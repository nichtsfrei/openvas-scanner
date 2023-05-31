// Copyright (C) 2023 Greenbone Networks GmbH
//
// SPDX-License-Identifier: GPL-2.0-or-later

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use nasl_syntax::parse;

    use nasl_interpreter::{Register, DefaultContext, Interpreter, NaslValue};

    #[test]
    fn variables() {
        let code = r###"
        a = 12;
        a += 13;
        a -= 2;
        a /= 2;
        a *= 2;
        a >>= 2;
        a <<= 2;
        a >>>= 2;
        a %= 2;
        a++;
        ++a;
        a--;
        --a;
        "###;
        let mut register = Register::default();
        let binding = DefaultContext::default();
        let context = binding.as_context();
        let mut interpreter = Interpreter::new(&mut register, &context);
        let mut parser =
            parse(code).map(|x| interpreter.resolve(&x.expect("no parse error expected")));
        assert_eq!(parser.next(), Some(Ok(12.into())));
        assert_eq!(parser.next(), Some(Ok(25.into())));
        assert_eq!(parser.next(), Some(Ok(23.into())));
        assert_eq!(parser.next(), Some(Ok(11.into())));
        assert_eq!(parser.next(), Some(Ok(22.into())));
        assert_eq!(parser.next(), Some(Ok(5.into())));
        assert_eq!(parser.next(), Some(Ok(20.into())));
        assert_eq!(parser.next(), Some(Ok(80.into())));
        assert_eq!(parser.next(), Some(Ok(0.into())));
        assert_eq!(parser.next(), Some(Ok(0.into())));
        assert_eq!(parser.next(), Some(Ok(2.into())));
        assert_eq!(parser.next(), Some(Ok(2.into())));
        assert_eq!(parser.next(), Some(Ok(0.into())));
    }
    #[test]
    fn arrays() {
        let code = r###"
        a[0] = 12;
        a[0] += 13;
        a[0] -= 2;
        a[0] /= 2;
        a[0] *= 2;
        a[0] >>= 2;
        a[0] <<= 2;
        a[0] >>>= 2;
        a[0] %= 2;
        a[0]++;
        ++a[0];
        "###;
        let mut register = Register::default();
        let binding = DefaultContext::default();
        let context = binding.as_context();
        let mut interpreter = Interpreter::new(&mut register, &context);
        let mut parser =
            parse(code).map(|x| interpreter.resolve(&x.expect("no parse error expected")));
        assert_eq!(parser.next(), Some(Ok(12.into())));
        assert_eq!(parser.next(), Some(Ok(25.into())));
        assert_eq!(parser.next(), Some(Ok(23.into())));
        assert_eq!(parser.next(), Some(Ok(11.into())));
        assert_eq!(parser.next(), Some(Ok(22.into())));
        assert_eq!(parser.next(), Some(Ok(5.into())));
        assert_eq!(parser.next(), Some(Ok(20.into())));
        assert_eq!(parser.next(), Some(Ok(80.into())));
        assert_eq!(parser.next(), Some(Ok(0.into())));
        assert_eq!(parser.next(), Some(Ok(0.into())));
        assert_eq!(parser.next(), Some(Ok(2.into())));
    }
    #[test]
    fn implicit_extend() {
        let code = r###"
        a[2] = 12;
        a;
        "###;
        let mut register = Register::default();
        let binding = DefaultContext::default();
        let context = binding.as_context();
        let mut interpreter = Interpreter::new(&mut register, &context);
        let mut parser =
            parse(code).map(|x| interpreter.resolve(&x.expect("no parse error expected")));
        assert_eq!(parser.next(), Some(Ok(12.into())));
        assert_eq!(
            parser.next(),
            Some(Ok(NaslValue::Array(vec![
                NaslValue::Null,
                NaslValue::Null,
                12.into()
            ])))
        );
    }

    #[test]
    fn implicit_transformation() {
        let code = r###"
        a = 12;
        a;
        a[2] = 12;
        a;
        "###;
        let mut register = Register::default();
        let binding = DefaultContext::default();
        let context = binding.as_context();
        let mut interpreter = Interpreter::new(&mut register, &context);
        let mut parser =
            parse(code).map(|x| interpreter.resolve(&x.expect("no parse error expected")));
        assert_eq!(parser.next(), Some(Ok(12.into())));
        assert_eq!(parser.next(), Some(Ok(12.into())));
        assert_eq!(parser.next(), Some(Ok(12.into())));
        assert_eq!(
            parser.next(),
            Some(Ok(NaslValue::Array(vec![
                12.into(),
                NaslValue::Null,
                12.into()
            ])))
        );
    }

    #[test]
    fn dict() {
        let code = r###"
        a['hi'] = 12;
        a;
        a['hi'];
        "###;
        let mut register = Register::default();
        let binding = DefaultContext::default();
        let context = binding.as_context();
        let mut interpreter = Interpreter::new(&mut register, &context);
        let mut parser =
            parse(code).map(|x| interpreter.resolve(&x.expect("no parse error expected")));
        assert_eq!(parser.next(), Some(Ok(12.into())));
        assert_eq!(
            parser.next(),
            Some(Ok(NaslValue::Dict(HashMap::from([(
                "hi".to_owned(),
                12.into()
            )]))))
        );
        assert_eq!(parser.next(), Some(Ok(12.into())));
    }

    #[test]
    fn array_creation() {
        let code = r###"
        a = [1, 2, 3];
        "###;
        let mut register = Register::default();
        let binding = DefaultContext::default();
        let context = binding.as_context();
        let mut interpreter = Interpreter::new(&mut register, &context);
        let mut parser =
            parse(code).map(|x| interpreter.resolve(&x.expect("no parse error expected")));
        assert_eq!(
            parser.next(),
            Some(Ok(NaslValue::Array(vec![1.into(), 2.into(), 3.into()])))
        );
    }
}
