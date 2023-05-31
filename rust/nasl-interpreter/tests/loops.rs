// Copyright (C) 2023 Greenbone Networks GmbH
//
// SPDX-License-Identifier: GPL-2.0-or-later

#[cfg(test)]
mod tests {
    use nasl_syntax::parse;

    use crate::{DefaultContext, Interpreter, NaslValue, Register};

    #[test]
    fn for_loop_test() {
        let code = r###"
        a = 0;
        for ( i = 1; i < 5; i++) {
            a += i;
        }
        a;
        "###;
        let binding = DefaultContext::default();
        let context = binding.as_context();
        let mut register = Register::default();
        let mut interpreter = Interpreter::new(&mut register, &context);
        let mut interpreter =
            parse(code).map(|x| interpreter.resolve(&x.expect("unexpected parse error")));
        assert_eq!(interpreter.next(), Some(Ok(0.into())));
        assert_eq!(interpreter.next(), Some(Ok(NaslValue::Null)));
        assert_eq!(interpreter.next(), Some(Ok(10.into())));
    }

    #[test]
    fn for_loop_without_update() {
        let code = r###"
        a = 0;
        for (; a < 5; ) {
            a += 1;
        }
        a;
        "###;
        let mut register = Register::default();
        let binding = DefaultContext::default();
        let context = binding.as_context();
        let mut interpreter = Interpreter::new(&mut register, &context);
        let mut interpreter =
            parse(code).map(|x| interpreter.resolve(&x.expect("unexpected parse error")));
        assert_eq!(interpreter.next(), Some(Ok(0.into())));
        assert_eq!(interpreter.next(), Some(Ok(NaslValue::Null)));
        assert_eq!(interpreter.next(), Some(Ok(5.into())));
    }

    #[test]
    fn for_each_loop_test() {
        let code = r###"
        arr[0] = 3;
        arr[1] = 5;
        a = 0;
        foreach i (arr) {
            a += i;
        }
        a;
        "###;
        let mut register = Register::default();
        let binding = DefaultContext::default();
        let context = binding.as_context();
        let mut interpreter = Interpreter::new(&mut register, &context);
        let mut interpreter =
            parse(code).map(|x| interpreter.resolve(&x.expect("unexpected parse error")));
        assert_eq!(interpreter.next(), Some(Ok(3.into())));
        assert_eq!(interpreter.next(), Some(Ok(5.into())));
        assert_eq!(interpreter.next(), Some(Ok(0.into())));
        assert_eq!(interpreter.next(), Some(Ok(NaslValue::Null)));
        assert_eq!(interpreter.next(), Some(Ok(8.into())));
    }

    #[test]
    fn while_loop_test() {
        let code = r###"
        i = 4;
        a = 0;
        i > 0;
        while(i > 0) {
            a += i;
            i--;
        }
        a;
        i;
        "###;
        let mut register = Register::default();
        let binding = DefaultContext::default();
        let context = binding.as_context();
        let mut interpreter = Interpreter::new(&mut register, &context);
        let mut interpreter =
            parse(code).map(|x| interpreter.resolve(&x.expect("unexpected parse error")));
        assert_eq!(interpreter.next(), Some(Ok(4.into())));
        assert_eq!(interpreter.next(), Some(Ok(0.into())));
        assert_eq!(interpreter.next(), Some(Ok(NaslValue::Boolean(true))));

        assert_eq!(interpreter.next(), Some(Ok(NaslValue::Null)));
        assert_eq!(interpreter.next(), Some(Ok(10.into())));
        assert_eq!(interpreter.next(), Some(Ok(0.into())));
    }

    #[test]
    fn repeat_loop_test() {
        let code = r###"
        i = 10;
        a = 0;
        repeat {
            a += i;
            i--;
        } until (i > 0);
        a;
        i;
        "###;
        let mut register = Register::default();
        let binding = DefaultContext::default();
        let context = binding.as_context();
        let mut interpreter = Interpreter::new(&mut register, &context);
        let mut interpreter =
            parse(code).map(|x| interpreter.resolve(&x.expect("unexpected parse error")));
        assert_eq!(interpreter.next(), Some(Ok(10.into())));
        assert_eq!(interpreter.next(), Some(Ok(0.into())));
        assert_eq!(interpreter.next(), Some(Ok(NaslValue::Null)));
        assert_eq!(interpreter.next(), Some(Ok(10.into())));
        assert_eq!(interpreter.next(), Some(Ok(9.into())));
    }

    #[test]
    fn control_flow() {
        let code = r###"
        a = 0;
        i = 5;
        while(i > 0) {
            if(i == 4) {
                i--;
                continue;
            }
            if (i == 1) {
                break;
            }
            a += i;
            i--;
        }
        a;
        i;
        "###;
        let mut register = Register::default();
        let binding = DefaultContext::default();
        let context = binding.as_context();
        let mut interpreter = Interpreter::new(&mut register, &context);
        let mut interpreter =
            parse(code).map(|x| interpreter.resolve(&x.expect("unexpected parse error")));
        assert_eq!(interpreter.next(), Some(Ok(0.into())));
        assert_eq!(interpreter.next(), Some(Ok(5.into())));
        assert_eq!(interpreter.next(), Some(Ok(NaslValue::Null)));
        assert_eq!(interpreter.next(), Some(Ok(10.into())));
        assert_eq!(interpreter.next(), Some(Ok(1.into())));
    }
}
