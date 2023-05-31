// Copyright (C) 2023 Greenbone Networks GmbH
//
// SPDX-License-Identifier: GPL-2.0-or-later

#[cfg(test)]
mod tests {
    use nasl_syntax::parse;

    use nasl_interpreter::{DefaultContext, Register};
    use nasl_interpreter::{Interpreter, NaslValue};

    macro_rules! create_test {
        ($($name:tt: $code:expr => $result:expr),*) => {

        $(
            #[test]
            fn $name() {
                let mut register = Register::default();
                let binding = DefaultContext::default();
                let context = binding.as_context();
                let mut interpreter = Interpreter::new(&mut register, &context);
                let mut parser = parse($code).map(|x|
                    interpreter.resolve(&x.expect("unexpected parse error"))
                );
                assert_eq!(parser.next(), Some(Ok($result)));
            }
        )*
        };
    }
    create_test! {
        numeric_plus: "1+2;" => 3.into(),
        string_plus: "\"hello \" + \"world!\";" => "hello world!".into(),
        string_minus : "\"hello \" - 'o ';" => "hell".into(),
        data_plus: "'hello ' + 'world!';" => "hello world!".into(),
        data_minus: "'hello ' - 'o ';" => "hell".into(),
        numeric_minus : "1 - 2;" => NaslValue::Number(-1),
        multiplication: "1*2;" => 2.into(),
        division: "512/2;" => 256.into(),
        modulo: "512%2;" => 0.into(),
        left_shift: "512 << 2;" => 2048.into(),
        right_shift: "512 >> 2;" => 128.into(),
        unsigned_right_shift: "-2 >>> 2;" => 1073741823.into(),
        and: "-2 & 2;" => 2.into(),
        or: "-2 | 2;" => NaslValue::Number(-2),
        xor: "-2 ^ 2;" => NaslValue::Number(-4),
        pow: "2 ** 2;" => 4.into(),
        not: "~2;" => NaslValue::Number(-3),
        r_match: "'hello' =~ 'hell';" => NaslValue::Boolean(true),
        r_not_match: "'hello' !~ 'hell';" => NaslValue::Boolean(false),
        contains: "'hello' >< 'hell';" => NaslValue::Boolean(true),
        not_contains: "'hello' >!< 'hell';" => NaslValue::Boolean(false),
        bool_not: "!23;" => NaslValue::Boolean(false),
        bool_not_reverse: "!0;" => NaslValue::Boolean(true),
        bool_and: "1 && 1;" => NaslValue::Boolean(true),
        bool_or: "1 || 0;" => NaslValue::Boolean(true),
        equals_string: "'1' == '1';" => NaslValue::Boolean(true),
        equals_number: "1 == 1;" => NaslValue::Boolean(true),
        unequal: "1 != 1;" => NaslValue::Boolean(false),
        greater: "1 > 0;" => NaslValue::Boolean(true),
        less: "1 < 2;" => NaslValue::Boolean(true),
        greater_equal: "1 >= 1;" => NaslValue::Boolean(true),
        less_equal: "1 <= 1;" => NaslValue::Boolean(true),
        xxxgonna_give_it_to_ya: "script_oid('hi') x 200;" => NaslValue::Null,
        gonna_give_it_to_ya: "script_oid('hi') x 200;" => NaslValue::Null
    }
}
