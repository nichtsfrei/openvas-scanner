// Copyright (C) 2023 Greenbone Networks GmbH
//
// SPDX-License-Identifier: GPL-2.0-or-later

use std::{collections::HashMap, io};

use nasl_syntax::{
    AssignOrder, DeclareScope, IdentifierType, Statement, Statement::*, Token, TokenCategory,
};
use regex::Regex;
use storage::StorageError;

use crate::{
    context::{Context, ContextType, Register},
    lookup,
    lookup_keys::FC_ANON_ARGS,
    FunctionError, InterpretError, InterpretErrorKind, LoadError, NaslValue,
};

/// Used to interpret a Statement
pub struct Interpreter<'a, K> {
    pub(crate) registrat: &'a mut Register,
    pub(crate) ctxconfigs: &'a Context<'a, K>,
}

/// Interpreter always returns a NaslValue or an InterpretError
///
/// When a result does not contain a value than NaslValue::Null must be returned.
pub type InterpretResult = Result<NaslValue, InterpretError>;

fn prepare_array(idx: &NaslValue, left: NaslValue) -> (usize, Vec<NaslValue>) {
    let idx = i64::from(idx) as usize;
    let mut arr: Vec<NaslValue> = match left {
        NaslValue::Array(x) => x,
        _ => {
            vec![left.clone()]
        }
    };

    for _ in arr.len()..idx + 1 {
        arr.push(NaslValue::Null)
    }
    (idx, arr)
}

fn prepare_dict(left: NaslValue) -> HashMap<String, NaslValue> {
    match left {
        NaslValue::Array(x) => x
            .into_iter()
            .enumerate()
            .map(|(i, v)| (i.to_string(), v))
            .collect(),
        NaslValue::Dict(x) => x,
        NaslValue::Null => HashMap::new(),
        x => HashMap::from([("0".to_string(), x)]),
    }
}

fn as_i64(left: NaslValue, right: Option<NaslValue>) -> (i64, i64) {
    (
        i64::from(&left),
        right.map(|x| i64::from(&x)).unwrap_or_default(),
    )
}

macro_rules! expr {
    ($e:expr) => {
        $e
    };
}
macro_rules! num_expr {
    ($op:tt $left:ident $right:ident) => {
        {
        let (left, right) = as_i64($left, $right);
        let result = expr!(left $op right);
        Ok(NaslValue::Number(result as i64))
        }
    };
    ($op:expr => $left:ident $right:ident) => {
        {
        let (left, right) = as_i64($left, $right);
        let result = $op(left, right);
        Ok(NaslValue::Number(result as i64))
        }
    };
}

fn match_regex(a: NaslValue, matches: Option<NaslValue>) -> InterpretResult {
    let right = matches.map(|x| x.to_string()).unwrap_or_default();
    match Regex::new(&right) {
        Ok(c) => Ok(NaslValue::Boolean(c.is_match(&a.to_string()))),
        Err(_) => Err(InterpretError::unparse_regex(&right)),
    }
}

fn not_match_regex(a: NaslValue, matches: Option<NaslValue>) -> InterpretResult {
    let result = match_regex(a, matches)?;
    Ok(NaslValue::Boolean(!bool::from(result)))
}

impl<'a, K> Interpreter<'a, K>
where
    K: AsRef<str>,
{
    /// Creates a new Interpreter.
    pub fn new(register: &'a mut Register, ctxconfigs: &'a Context<K>) -> Self {
        Interpreter {
            registrat: register,
            ctxconfigs,
        }
    }

    fn save(&mut self, idx: usize, key: &str, value: NaslValue) {
        self.registrat
            .add_to_index(idx, key, ContextType::Value(value));
    }

    fn named_value(&self, key: &str) -> Result<(usize, NaslValue), InterpretError> {
        match self
            .registrat()
            .index_named(key)
            .unwrap_or((0, &ContextType::Value(NaslValue::Null)))
        {
            (_, ContextType::Function(_, _)) => Err(InterpretError::expected_value()),
            (idx, ContextType::Value(val)) => Ok((idx, val.clone())),
        }
    }
    #[allow(clippy::too_many_arguments)]
    fn handle_dict(
        &mut self,
        ridx: usize,
        key: &str,
        idx: String,
        left: NaslValue,
        right: &NaslValue,
        return_original: &AssignOrder,
        result: impl Fn(&NaslValue, &NaslValue) -> NaslValue,
    ) -> NaslValue {
        let mut dict = prepare_dict(left);
        match return_original {
            AssignOrder::ReturnAssign => {
                let original = dict.get(&idx).unwrap_or(&NaslValue::Null).clone();
                let result = result(&original, right);
                dict.insert(idx, result);
                self.save(ridx, key, NaslValue::Dict(dict));
                original
            }
            AssignOrder::AssignReturn => {
                let original = dict.get(&idx).unwrap_or(&NaslValue::Null);
                let result = result(original, right);
                dict.insert(idx, result.clone());
                self.save(ridx, key, NaslValue::Dict(dict));
                result
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    // TODO remove
    fn handle_array(
        &mut self,
        ridx: usize,
        key: &str,
        idx: &NaslValue,
        left: NaslValue,
        right: &NaslValue,
        return_original: &AssignOrder,
        result: impl Fn(&NaslValue, &NaslValue) -> NaslValue,
    ) -> NaslValue {
        let (idx, mut arr) = prepare_array(idx, left);
        match return_original {
            AssignOrder::ReturnAssign => {
                let orig = arr[idx].clone();
                let result = result(&orig, right);
                arr[idx] = result;
                self.save(ridx, key, NaslValue::Array(arr));
                orig
            }
            AssignOrder::AssignReturn => {
                let result = result(&arr[idx], right);
                arr[idx] = result.clone();
                self.save(ridx, key, NaslValue::Array(arr));
                result
            }
        }
    }

    fn store_return(
        &mut self,
        key: &str,
        lookup: Option<NaslValue>,
        right: &NaslValue,
        result: impl Fn(&NaslValue, &NaslValue) -> NaslValue,
    ) -> InterpretResult {
        self.dynamic_return(key, &AssignOrder::AssignReturn, lookup, right, result)
    }

    fn dynamic_return(
        &mut self,
        key: &str,
        order: &AssignOrder,
        lookup: Option<NaslValue>,
        right: &NaslValue,
        result: impl Fn(&NaslValue, &NaslValue) -> NaslValue,
    ) -> InterpretResult {
        let (ridx, left) = self.named_value(key)?;
        let result = match lookup {
            None => {
                let result = result(&left, right);
                self.save(ridx, key, result.clone());
                match order {
                    AssignOrder::AssignReturn => result,
                    AssignOrder::ReturnAssign => left,
                }
            }
            Some(idx) => match idx {
                NaslValue::String(idx) => {
                    self.handle_dict(ridx, key, idx, left, right, order, result)
                }
                NaslValue::Data(idx) => {
                    let idx = idx.into_iter().map(|x| x as char).collect();
                    self.handle_dict(ridx, key, idx, left, right, order, result)
                }
                _ => match left {
                    NaslValue::Dict(_) => {
                        self.handle_dict(ridx, key, idx.to_string(), left, right, order, result)
                    }
                    _ => self.handle_array(ridx, key, &idx, left, right, order, result),
                },
            },
        };
        Ok(result)
    }
    fn without_right(
        &mut self,
        order: &AssignOrder,
        key: &str,
        lookup: Option<NaslValue>,
        result: impl Fn(&NaslValue, &NaslValue) -> NaslValue,
    ) -> InterpretResult {
        self.dynamic_return(key, order, lookup, &NaslValue::Null, result)
    }

    pub(crate) fn identifier(token: &Token) -> Result<String, InterpretError> {
        match token.category() {
            TokenCategory::Identifier(IdentifierType::Undefined(x)) => Ok(x.to_owned()),
            cat => Err(InterpretError::wrong_category(cat)),
        }
    }

    /// Tries to interpret a statement and retries n times on a retry error
    ///
    /// When encountering a retrievable error:
    /// - LoadError(Retry(_))
    /// - StorageError(Retry(_))
    /// - IOError(Interrupted(_))
    ///
    /// then it retries the statement for a given max_attempts times.
    ///
    /// When max_attempts is set to 0 it will it execute it once.
    pub fn retry_resolve(&mut self, stmt: &Statement, max_attempts: usize) -> InterpretResult {
        match self.resolve(stmt) {
            Ok(x) => Ok(x),
            Err(e) => {
                if max_attempts > 0 {
                    match e.kind {
                        InterpretErrorKind::LoadError(LoadError::Retry(_))
                        | InterpretErrorKind::IOError(io::ErrorKind::Interrupted)
                        | InterpretErrorKind::StorageError(StorageError::Retry(_)) => {
                            self.retry_resolve(stmt, max_attempts - 1)
                        }
                        _ => Err(e),
                    }
                } else {
                    Err(e)
                }
            }
        }
    }

    fn include(&mut self, name: &Statement) -> InterpretResult {
        match self.resolve(name)? {
            NaslValue::String(key) => {
                let code = self.ctxconfigs.loader().load(&key)?;
                let mut inter = Interpreter::new(self.registrat, self.ctxconfigs);
                let result = nasl_syntax::parse(&code)
                    .map(|parsed| match parsed {
                        Ok(stmt) => inter.resolve(&stmt),
                        Err(err) => Err(InterpretError::include_syntax_error(&key, err)),
                    })
                    .find(|e| e.is_err());
                match result {
                    Some(e) => e,
                    None => Ok(NaslValue::Null),
                }
            }
            _ => Err(InterpretError::unsupported(name, "string")),
        }
    }

    fn assign(
        &mut self,
        category: &TokenCategory,
        order: &AssignOrder,
        left: &Statement,
        right: &Statement,
    ) -> InterpretResult {
        let (key, lookup) = {
            match left {
                Variable(ref token) => (Self::identifier(token)?, None),
                Array(ref token, Some(stmt)) => {
                    (Self::identifier(token)?, Some(self.resolve(stmt)?))
                }
                Array(ref token, None) => (Self::identifier(token)?, None),
                _ => return Err(InterpretError::unsupported(left, "Array or Variable")),
            }
        };
        let val = self.resolve(right)?;
        match category {
            TokenCategory::Equal => self.store_return(&key, lookup, &val, |_, right| right.clone()),
            TokenCategory::PlusEqual => self.store_return(&key, lookup, &val, |left, right| {
                NaslValue::Number(i64::from(left) + i64::from(right))
            }),
            TokenCategory::MinusEqual => self.store_return(&key, lookup, &val, |left, right| {
                NaslValue::Number(i64::from(left) - i64::from(right))
            }),
            TokenCategory::SlashEqual => self.store_return(&key, lookup, &val, |left, right| {
                NaslValue::Number(i64::from(left) / i64::from(right))
            }),
            TokenCategory::StarEqual => self.store_return(&key, lookup, &val, |left, right| {
                NaslValue::Number(i64::from(left) * i64::from(right))
            }),
            TokenCategory::GreaterGreaterEqual => {
                self.store_return(&key, lookup, &val, |left, right| {
                    NaslValue::Number(i64::from(left) >> i64::from(right))
                })
            }
            TokenCategory::LessLessEqual => self.store_return(&key, lookup, &val, |left, right| {
                NaslValue::Number(i64::from(left) << i64::from(right))
            }),
            TokenCategory::GreaterGreaterGreaterEqual => {
                self.store_return(&key, lookup, &val, |left, right| {
                    // get rid of minus sign
                    let left = i64::from(left) as u32;
                    let right = i64::from(right) as u32;
                    NaslValue::Number((left << right) as i64)
                })
            }
            TokenCategory::PercentEqual => self.store_return(&key, lookup, &val, |left, right| {
                NaslValue::Number(i64::from(left) % i64::from(right))
            }),
            TokenCategory::PlusPlus => self.without_right(order, &key, lookup, |left, _| {
                NaslValue::Number(i64::from(left) + 1)
            }),
            TokenCategory::MinusMinus => self.without_right(order, &key, lookup, |left, _| {
                NaslValue::Number(i64::from(left) - 1)
            }),

            cat => Err(InterpretError::wrong_category(cat)),
        }
    }

    fn for_loop(
        &mut self,
        assignment: &Statement,
        condition: &Statement,
        update: &Statement,
        body: &Statement,
    ) -> InterpretResult {
        // Resolve assignment
        self.resolve(assignment)?;

        loop {
            // Check condition statement
            if !bool::from(self.resolve(condition)?) {
                break;
            }

            // Execute loop body
            let ret = self.resolve(body)?;
            // Catch special values
            match ret {
                NaslValue::Break => break,
                NaslValue::Exit(code) => return Ok(NaslValue::Exit(code)),
                NaslValue::Return(val) => return Ok(NaslValue::Return(val)),
                _ => (),
            };

            // Execute update Statement
            self.resolve(update)?;
        }

        Ok(NaslValue::Null)
    }

    fn for_each_loop(
        &mut self,
        variable: &Token,
        iterable: &Statement,
        body: &Statement,
    ) -> InterpretResult {
        // Get name of the iteration variable
        let iter_name = match variable.category() {
            TokenCategory::Identifier(IdentifierType::Undefined(name)) => name,
            o => return Err(InterpretError::wrong_category(o)),
        };
        // Iterate through the iterable Statement
        for val in Vec::<NaslValue>::from(self.resolve(iterable)?) {
            // Change the value of the iteration variable after each iteration
            self.registrat.add_local(iter_name, ContextType::Value(val));

            // Execute loop body
            let ret = self.resolve(body)?;
            // Catch special values
            match ret {
                NaslValue::Break => break,
                NaslValue::Exit(code) => return Ok(NaslValue::Exit(code)),
                NaslValue::Return(val) => return Ok(NaslValue::Return(val)),
                _ => (),
            };
        }

        Ok(NaslValue::Null)
    }

    fn while_loop(&mut self, condition: &Statement, body: &Statement) -> InterpretResult {
        while bool::from(self.resolve(condition)?) {
            // Execute loop body
            let ret = self.resolve(body)?;
            // Catch special values
            match ret {
                NaslValue::Break => break,
                NaslValue::Exit(code) => return Ok(NaslValue::Exit(code)),
                NaslValue::Return(val) => return Ok(NaslValue::Return(val)),
                _ => (),
            };
        }

        Ok(NaslValue::Null)
    }

    fn repeat_loop(&mut self, body: &Statement, condition: &Statement) -> InterpretResult {
        loop {
            // Execute loop body
            let ret = self.resolve(body)?;
            // Catch special values
            match ret {
                NaslValue::Break => break,
                NaslValue::Exit(code) => return Ok(NaslValue::Exit(code)),
                NaslValue::Return(val) => return Ok(NaslValue::Return(val)),
                _ => (),
            };

            // Check condition statement
            if bool::from(self.resolve(condition)?) {
                break;
            }
        }

        Ok(NaslValue::Null)
    }

    fn call(&mut self, name: &Token, arguments: &[Statement]) -> InterpretResult {
        let name = &Self::identifier(name)?;
        // get the context
        let mut named = HashMap::new();
        let mut position = vec![];
        // TODO simplify
        for p in arguments {
            match p {
                NamedParameter(token, val) => {
                    let val = self.resolve(val)?;
                    let name = Self::identifier(token)?;
                    named.insert(name, ContextType::Value(val));
                }
                val => {
                    let val = self.resolve(val)?;
                    position.push(val);
                }
            }
        }
        named.insert(
            FC_ANON_ARGS.to_owned(),
            ContextType::Value(NaslValue::Array(position)),
        );
        self.registrat.create_root_child(named);
        let result = match lookup(name) {
            // Built-In Function
            Some(function) => function(self.registrat, self.ctxconfigs)
                .map_err(|x| FunctionError::new(name, x).into()),
            // Check for user defined function
            None => {
                let found = self
                    .registrat
                    .named(name)
                    .ok_or_else(|| InterpretError::not_found(name))?
                    .clone();
                match found {
                    ContextType::Function(params, stmt) => {
                        // prepare default values
                        for p in params {
                            match self.registrat.named(&p) {
                                None => {
                                    // add default NaslValue::Null for each defined params
                                    self.registrat
                                        .add_local(&p, ContextType::Value(NaslValue::Null));
                                }
                                Some(_) => {}
                            }
                        }
                        match self.resolve(&stmt)? {
                            NaslValue::Return(x) => Ok(*x),
                            a => Ok(a),
                        }
                    }
                    ContextType::Value(_) => Err(InterpretError::expected_function()),
                }
            }
        };
        self.registrat.drop_last();
        result
    }

    fn declare_function(
        &mut self,
        name: &Token,
        arguments: &[Statement],
        execution: &Statement,
    ) -> InterpretResult {
        let name = &Self::identifier(name)?;
        let mut names = vec![];
        for a in arguments {
            match a {
                Statement::Variable(token) => {
                    let param_name = &Self::identifier(token)?;
                    names.push(param_name.to_owned());
                }
                _ => return Err(InterpretError::unsupported(a, "variable")),
            }
        }
        self.registrat
            .add_global(name, ContextType::Function(names, execution.clone()));
        Ok(NaslValue::Null)
    }

    fn declare_variable(&mut self, scope: &DeclareScope, stmts: &[Statement]) -> InterpretResult {
        let mut add = |key: &str| {
            let value = ContextType::Value(NaslValue::Null);
            match scope {
                DeclareScope::Global => self.registrat.add_global(key, value),
                DeclareScope::Local => self.registrat.add_local(key, value),
            }
        };

        for stmt in stmts {
            if let Statement::Variable(ref token) = stmt {
                if let TokenCategory::Identifier(name) = token.category() {
                    add(&name.to_string());
                }
            };
        }
        Ok(NaslValue::Null)
    }

    fn execute(
        &mut self,
        stmts: &[Statement],
        result: impl Fn(NaslValue, Option<NaslValue>) -> InterpretResult,
    ) -> InterpretResult {
        // neither empty statements nor statements over 2 arguments should ever happen
        // because it is handled as a SyntaxError. Therefore we don't double check and
        // and let it run into a index out of bound panic to immediately escalate.
        let (left, right) = {
            let first = self.resolve(&stmts[0])?;
            if stmts.len() == 1 {
                (first, None)
            } else {
                (first, Some(self.resolve(&stmts[1])?))
            }
        };
        result(left, right)
    }

    fn operator(&mut self, category: &TokenCategory, stmts: &[Statement]) -> InterpretResult {
        match category {
            // number and string
            TokenCategory::Plus => self.execute(stmts, |a, b| match a {
                NaslValue::String(x) => {
                    let right = b.map(|x| x.to_string()).unwrap_or_default();
                    Ok(NaslValue::String(format!("{x}{right}")))
                }
                NaslValue::Data(x) => {
                    let right: String = b.map(|x| x.to_string()).unwrap_or_default();
                    let x: String = x.into_iter().map(|b| b as char).collect();
                    Ok(NaslValue::String(format!("{x}{right}")))
                }
                left => {
                    let right = b.map(|x| i64::from(&x)).unwrap_or_default();
                    Ok(NaslValue::Number(i64::from(&left) + right))
                }
            }),
            TokenCategory::Minus => self.execute(stmts, |a, b| match a {
                NaslValue::String(x) => {
                    let right: String = b.map(|x| x.to_string()).unwrap_or_default();
                    Ok(NaslValue::String(x.replacen(&right, "", 1)))
                }
                NaslValue::Data(x) => {
                    let right: String = b.map(|x| x.to_string()).unwrap_or_default();
                    let x: String = x.into_iter().map(|b| b as char).collect();
                    Ok(NaslValue::String(x.replacen(&right, "", 1)))
                }
                left => {
                    let result = match b {
                        Some(right) => i64::from(&left) - i64::from(&right),
                        None => -i64::from(&left),
                    };
                    Ok(NaslValue::Number(result))
                }
            }),
            // number
            TokenCategory::Star => self.execute(stmts, |a, b| num_expr!(* a b)),
            TokenCategory::Slash => self.execute(stmts, |a, b| num_expr!(/ a b)),
            TokenCategory::Percent => self.execute(stmts, |a, b| num_expr!(% a b)),
            TokenCategory::LessLess => self.execute(stmts, |a, b| num_expr!(|a, b| a << b => a b)),
            TokenCategory::GreaterGreater => {
                self.execute(stmts, |a, b| num_expr!(|a, b| a >> b => a b))
            }
            // let left_casted = left as u32; (left_casted >> right) as i64
            TokenCategory::GreaterGreaterGreater => self.execute(
                stmts,
                |a, b| num_expr!(|a, b| ((a as u32) >> b) as i32 => a b),
            ),
            TokenCategory::Ampersand => self.execute(stmts, |a, b| num_expr!(& a b)),
            TokenCategory::Pipe => self.execute(stmts, |a, b| num_expr!(| a b)),
            TokenCategory::Caret => self.execute(stmts, |a, b| num_expr!(^ a b)),
            TokenCategory::StarStar => self.execute(
                stmts,
                |a, b| num_expr!(|a, b| (a as u32).pow(b as u32) as i32 => a b),
            ),
            TokenCategory::Tilde => {
                self.execute(stmts, |a, b| num_expr!(|a: i64, _: i64| !a => a b))
            }
            // string
            TokenCategory::EqualTilde => self.execute(stmts, match_regex),
            TokenCategory::BangTilde => self.execute(stmts, not_match_regex),
            TokenCategory::GreaterLess => self.execute(stmts, |a, b| {
                let substr = b.map(|x| x.to_string()).unwrap_or_default();
                Ok(NaslValue::Boolean(a.to_string().contains(&substr)))
            }),
            TokenCategory::GreaterBangLess => self.execute(stmts, |a, b| {
                let substr = b.map(|x| x.to_string()).unwrap_or_default();
                Ok(NaslValue::Boolean(!a.to_string().contains(&substr)))
            }),
            // bool
            TokenCategory::Bang => {
                self.execute(stmts, |a, _| Ok(NaslValue::Boolean(!bool::from(a))))
            }
            TokenCategory::AmpersandAmpersand => self.execute(stmts, |a, b| {
                let right = b.map(bool::from).unwrap_or_default();
                Ok(NaslValue::Boolean(bool::from(a) && right))
            }),
            TokenCategory::PipePipe => self.execute(stmts, |a, b| {
                let right = b.map(bool::from).unwrap_or_default();
                Ok(NaslValue::Boolean(bool::from(a) || right))
            }),
            TokenCategory::EqualEqual => self.execute(stmts, |a, b| {
                let right = b.unwrap_or(NaslValue::Null);
                Ok(NaslValue::Boolean(a == right))
            }),
            TokenCategory::BangEqual => self.execute(stmts, |a, b| {
                let right = b.unwrap_or(NaslValue::Null);
                Ok(NaslValue::Boolean(a != right))
            }),
            TokenCategory::Greater => self.execute(stmts, |a, b| {
                let right = b.map(|x| i64::from(&x)).unwrap_or_default();
                Ok(NaslValue::Boolean(i64::from(&a) > right))
            }),
            TokenCategory::Less => self.execute(stmts, |a, b| {
                let right = b.map(|x| i64::from(&x)).unwrap_or_default();
                Ok(NaslValue::Boolean(i64::from(&a) < right))
            }),
            TokenCategory::GreaterEqual => self.execute(stmts, |a, b| {
                let right = b.map(|x| i64::from(&x)).unwrap_or_default();
                Ok(NaslValue::Boolean(i64::from(&a) >= right))
            }),
            TokenCategory::LessEqual => self.execute(stmts, |a, b| {
                let right = b.map(|x| i64::from(&x)).unwrap_or_default();
                Ok(NaslValue::Boolean(i64::from(&a) <= right))
            }),
            TokenCategory::X => {
                // neither empty statements nor statements over 2 arguments should ever happen
                // because it is handled as a SyntaxError. Therefore we don't double check and
                // and let it run into a index out of bound panic to immediately escalate.
                let repeat = {
                    let last = self.resolve(&stmts[1])?;
                    i64::from(&last)
                };
                if repeat == 0 {
                    // don't execute;
                    return Ok(NaslValue::Null);
                }
                let repeatable = &stmts[0];
                for _ in 1..repeat - 1 {
                    self.resolve(repeatable)?;
                }
                self.resolve(repeatable)
            }

            o => Err(InterpretError::wrong_category(o)),
        }
    }

    /// Interprets a Statement
    pub fn resolve(&mut self, statement: &Statement) -> InterpretResult {
        match statement {
            Array(name, position) => {
                let name = Self::identifier(name)?;
                let val = self
                    .registrat
                    .named(&name)
                    .unwrap_or(&ContextType::Value(NaslValue::Null));
                let val = val.clone();

                match (position, val) {
                    (None, ContextType::Value(v)) => Ok(v),
                    (Some(p), ContextType::Value(NaslValue::Array(x))) => {
                        let position = self.resolve(p)?;
                        let position = i64::from(&position) as usize;
                        let result = x.get(position).unwrap_or(&NaslValue::Null);
                        Ok(result.clone())
                    }
                    (Some(p), ContextType::Value(NaslValue::Dict(x))) => {
                        let position = self.resolve(p)?.to_string();
                        let result = x.get(&position).unwrap_or(&NaslValue::Null);
                        Ok(result.clone())
                    }
                    (Some(_), ContextType::Value(NaslValue::Null)) => Ok(NaslValue::Null),
                    (Some(p), _) => Err(InterpretError::unsupported(p, "array")),
                    (None, ContextType::Function(_, _)) => {
                        Err(InterpretError::unsupported(statement, "variable"))
                    }
                }
            }
            Exit(stmt) => {
                let rc = self.resolve(stmt)?;
                match rc {
                    NaslValue::Number(rc) => Ok(NaslValue::Exit(rc)),
                    _ => Err(InterpretError::unsupported(stmt, "numeric")),
                }
            }
            Return(stmt) => {
                let rc = self.resolve(stmt)?;
                Ok(NaslValue::Return(Box::new(rc)))
            }
            Include(inc) => self.include(inc),
            NamedParameter(_, _) => unreachable!("is handled in call"),
            For(assignment, condition, update, body) => {
                self.for_loop(assignment, condition, update, body)
            }
            While(condition, body) => self.while_loop(condition, body),
            Repeat(body, condition) => self.repeat_loop(body, condition),
            ForEach(variable, iterable, body) => self.for_each_loop(variable, iterable, body),
            FunctionDeclaration(name, args, exec) => self.declare_function(name, args, exec),
            Primitive(token) => TryFrom::try_from(token),
            Variable(token) => {
                let name: NaslValue = TryFrom::try_from(token)?;
                match self.registrat.named(&name.to_string()) {
                    Some(ContextType::Value(result)) => Ok(result.clone()),
                    None => Ok(NaslValue::Null),
                    Some(ContextType::Function(_, _)) => {
                        Err(InterpretError::unsupported(statement, "variable"))
                    }
                }
            }
            Call(name, arguments) => self.call(name, arguments),
            Declare(scope, stmts) => self.declare_variable(scope, stmts),
            // array creation
            Parameter(x) => {
                let mut result = vec![];
                for stmt in x {
                    let val = self.resolve(stmt)?;
                    result.push(val);
                }
                Ok(NaslValue::Array(result))
            }
            Assign(cat, order, left, right) => self.assign(cat, order, left, right),
            Operator(sign, stmts) => self.operator(sign, stmts),
            If(condition, if_block, else_block) => match self.resolve(condition) {
                Ok(value) => {
                    if bool::from(value) {
                        return self.resolve(if_block);
                    } else if let Some(else_block) = else_block {
                        return self.resolve(else_block.as_ref());
                    }
                    Ok(NaslValue::Null)
                }
                Err(err) => Err(err),
            },
            Block(blocks) => {
                self.registrat.create_child(HashMap::default());
                for stmt in blocks {
                    match self.resolve(stmt) {
                        Ok(x) => {
                            if matches!(
                                x,
                                NaslValue::Exit(_)
                                    | NaslValue::Return(_)
                                    | NaslValue::Break
                                    | NaslValue::Continue
                            ) {
                                self.registrat.drop_last();
                                return Ok(x);
                            }
                        }
                        Err(e) => return Err(e),
                    }
                }
                self.registrat.drop_last();
                // currently blocks don't return something
                Ok(NaslValue::Null)
            }
            NoOp(_) => Ok(NaslValue::Null),
            EoF => todo!(),
            AttackCategory(cat) => Ok(NaslValue::AttackCategory(*cat)),
            Continue => Ok(NaslValue::Continue),
            Break => Ok(NaslValue::Break),
        }
        .map_err(|e| {
            if e.origin.is_none() {
                InterpretError::from_statement(statement, e.kind)
            } else {
                e
            }
        })
    }

    pub(crate) fn registrat(&self) -> &Register {
        self.registrat
    }
}
