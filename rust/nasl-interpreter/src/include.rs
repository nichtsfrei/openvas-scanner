// Copyright (C) 2023 Greenbone Networks GmbH
//
// SPDX-License-Identifier: GPL-2.0-or-later

use nasl_syntax::{parse, Statement};

use crate::{error::InterpretError, interpreter::InterpretResult, Interpreter, NaslValue};

/// Is a trait to declare include functionality
pub(crate) trait IncludeExtension {
    fn include(&mut self, name: &Statement) -> InterpretResult;
}

impl<'a> IncludeExtension for Interpreter<'a> {
    fn include(&mut self, name: &Statement) -> InterpretResult {
        match self.resolve(name)? {
            NaslValue::String(key) => {
                let code = self.ctxconfigs.loader().load(&key)?;
                let mut inter = Interpreter::new(self.registrat, self.ctxconfigs);
                let result = parse(&code)
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
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use nasl_syntax::parse;
    use sink::DefaultSink;

    use crate::{
        context::Register, Context, DefaultLogger, Interpreter, LoadError, Loader, NaslValue
    };

    struct FakeInclude<'a> {
        plugins: &'a HashMap<String, String>,
    }

    impl<'a> Loader for FakeInclude<'a> {
        fn load(&self, key: &str) -> Result<String, LoadError> {
            self.plugins
                .get(key)
                .cloned()
                .ok_or_else(|| LoadError::NotFound(String::default()))
        }
    }

    #[test]
    fn function_variable() {
        let example = r#"
        a = 12;
        function test() {
            b['hello'] = 'world';
            return b;
        }
        "#
        .to_string();
        let plugins = HashMap::from([("example.inc".to_string(), example)]);
        let loader = &FakeInclude { plugins: &plugins };
        let code = r###"
        include("example.inc");
        a;
        test();
        "###;
        let mut register = Register::default();
        let storage = DefaultSink::new(false);
        let logger = DefaultLogger::new();
        let context = Context::new("1", &storage, loader, &logger);
        let mut interpreter = Interpreter::new(&mut register, &context);
        let mut interpreter = parse(code).map(|x| interpreter.resolve(&x.expect("expected")));
        assert_eq!(interpreter.next(), Some(Ok(NaslValue::Null)));
        assert_eq!(interpreter.next(), Some(Ok(12.into())));
        assert_eq!(
            interpreter.next(),
            Some(Ok(NaslValue::Dict(HashMap::from([(
                "hello".to_owned(),
                NaslValue::Data("world".as_bytes().into())
            )]))))
        );
    }
}