#![cfg(test)]

use std::cmp::Ordering;

use crate::*;

struct Person<'a> {
    name: &'a str,
    age: u8,
}

fn test_cmp<T: ?Sized>(under_test: impl Comparator<T>, left: &T, right: &T, expected: Ordering) {
    assert_eq!(under_test.cmp(left, right), expected);
}

macro_rules! assert_comparator {
    ($comparator:expr, $compare_to:expr, ) => {
    };
    ($comparator:expr, $compare_to:expr, <, $eq:expr $(, $op:tt, $expr:expr)*) => {
        test_cmp($comparator, $eq, $compare_to, Ordering::Less);
        assert_comparator!($comparator, $compare_to, $($op, $expr),*);
    };
    ($comparator:expr, $compare_to:expr, =, $eq:expr $(, $op:tt, $expr:expr)*) => {
        test_cmp($comparator, $eq, $compare_to, Ordering::Equal);
        assert_comparator!($comparator, $compare_to, $($op, $expr),*);
    };
    ($comparator:expr, $compare_to:expr, >, $ne:expr $(, $op:tt, $expr:expr)*) => {
        test_cmp($comparator, $ne, $compare_to, Ordering::Greater);
        assert_comparator!($comparator, $compare_to, $($op, $expr),*);
    };
}

#[test]
fn test_natural_order() {
    assert_comparator!(natural_order(), &2, <, &1, =, &2, >, &3);
}

#[test]
fn test_reverse_order() {
    assert_comparator!(reverse_order(), &2, <, &3, =, &2, >, &1);
}

#[test]
fn test_comparing() {
    assert_comparator! {
        comparing(|v: &Person| v.age),
        &Person { name: "Foo", age: 32 },
        <, &Person { name: "Bar", age: 31 },
        =, &Person { name: "Bar", age: 32 },
        >, &Person { name: "Bar", age: 33 }
    }
}

#[test]
fn test_comparing_ref() {
    assert_comparator! {
        comparing_ref(|v: &Person| v.name),
        &Person { name: "Baz", age: 32 },
        <, &Person { name: "Bar", age: 32 },
        =, &Person { name: "Baz", age: 32 },
        >, &Person { name: "Foo", age: 32 }
    }
}

#[test]
fn test_comparing_with() {
    assert_comparator! {
        comparing_with(|v: &Person| v.age, reverse_order()),
        &Person { name: "Foo", age: 32 },
        <, &Person { name: "Bar", age: 33 },
        =, &Person { name: "Bar", age: 32 },
        >, &Person { name: "Bar", age: 31 }
    }
}

#[test]
fn test_comparing_ref_with() {
    assert_comparator! {
        comparing_ref_with(|v: &Person| v.name, reverse_order()),
        &Person { name: "Baz", age: 32 },
        <, &Person { name: "Foo", age: 32 },
        =, &Person { name: "Baz", age: 32 },
        >, &Person { name: "Bar", age: 32 }
    }
}

#[test]
fn test_partial_order_or() {
    assert_comparator! {
        partial_order_or(at_least(|f: &f64| f.is_nan())),
        &2_f64,
        <, &f64::NAN,
        <, &1_f64,
        =, &2_f64,
        >, &3_f64
    }
}

#[test]
fn test_at_least() {
    assert_comparator!(at_least(|f: &f64| f < &0_f64), &-1_f64, =, &-2_f64, >, &1_f64);
    assert_comparator!(at_least(|f: &f64| f < &0_f64), &1_f64, =, &2_f64, <, &-1_f64);
}

#[test]
fn test_at_greatest() {
    assert_comparator!(at_greatest(|f: &f64| f > &0_f64), &-1_f64, =, &-2_f64, >, &1_f64);
    assert_comparator!(at_greatest(|f: &f64| f > &0_f64), &1_f64, =, &2_f64, <, &-1_f64);
}

#[test]
fn test_comparing_reversed() {
    assert_comparator! {
        comparing(|v: &Person| v.age).reversed(),
        &Person { name: "Foo", age: 32 },
        <, &Person { name: "Bar", age: 33 },
        =, &Person { name: "Bar", age: 32 },
        >, &Person { name: "Bar", age: 31 }
    }
}

#[test]
fn test_comparing_then() {
    assert_comparator! {
        comparing(|v: &Person| v.name).then(comparing(|v: &Person| v.age)),
        &Person { name: "Bar", age: 32 },
        <, &Person { name: "Bar", age: 31 },
        =, &Person { name: "Bar", age: 32 },
        >, &Person { name: "Foo", age: 32 }
    }
}

#[test]
fn test_fn_comparator() {
    assert_comparator! {
        |left: &str, right: &str| left.to_ascii_uppercase().cmp(&right.to_ascii_uppercase()),
        "Baz",
        <, "BAR",
        <, "bar",
        =, "BAZ",
        =, "baz",
        >, "FOO",
        >, "foo"
    }
}

#[test]
fn test_max() {
    assert_eq!(reverse_order().max(&1, &2), &1);
}

#[test]
fn test_min() {
    assert_eq!(reverse_order().min(&1, &2), &2);
}

fn test_eq<T: ?Sized>(under_test: impl EqClass<T>, left: &T, right: &T, expected: bool) {
    assert_eq!(under_test.eq(left, right), expected);
}

macro_rules! assert_eq_class {
    ($eq_class:expr, $compare_to:expr, ) => {
    };
    ($eq_class:expr, $compare_to:expr, =, $eq:expr $(, $op:tt, $expr:expr)*) => {
        test_eq($eq_class, $eq, $compare_to, true);
        assert_eq_class!($eq_class, $compare_to, $($op, $expr),*);
    };
    ($eq_class:expr, $compare_to:expr, !, $ne:expr $(, $op:tt, $expr:expr)*) => {
        test_eq($eq_class, $ne, $compare_to, false);
        assert_eq_class!($eq_class, $compare_to, $($op, $expr),*);
    };
}

#[test]
fn test_natural_eq() {
    assert_eq_class!(natural_eq(), &2, =, &2, !, &3);
}

#[test]
fn test_partial_eq() {
    assert_eq_class!(partial_eq(), &f64::NAN, =, &f64::NAN, !, &1_f64);
    assert_eq_class!(partial_eq(), &1_f64, =, &1_f64, !, &f64::NAN);
}

#[test]
fn test_eq_by_hash() {
    assert_eq_class!(eq_by_hash(), &2, =, &2, !, &3);
}

#[test]
fn test_eq_by_cmp() {
    assert_eq_class!(
        eq_by_cmp(comparing(|s: &str| s.to_ascii_uppercase())),
        "Foo",
        =, "Foo",
        =, "foo",
        =, "FOO",
        !, "Bar"
    );
}

#[test]
fn test_eq_by() {
    assert_eq_class!(eq_by(|v| v % 6), &2, =, &2, =, &8, !, &9);
}

#[test]
fn test_eq_by_ref() {
    assert_eq_class! {
        eq_by_ref(|v: &Person| v.name),
        &Person { name: "Foo", age: 32 },
        =, &Person { name: "Foo", age: 33 },
        !, &Person { name: "Bar", age: 32 }
    }
}

#[test]
fn test_eq_by_with() {
    assert_eq_class! {
        eq_by_with(|v: &Person| v.age, eq_by(|v| v % 6)),
        &Person { name: "Foo", age: 32 },
        =, &Person { name: "Bar", age: 26 },
        !, &Person { name: "Foo", age: 28 }
    }
}

#[test]
fn test_eq_by_ref_with() {
    assert_eq_class! {
        eq_by_ref_with(|v: &Person| v.name, |left: &str, right: &str| left.eq_ignore_ascii_case(right)),
        &Person { name: "Foo", age: 32 },
        =, &Person { name: "foo", age: 33 },
        =, &Person { name: "FOO", age: 33 },
        !, &Person { name: "Bar", age: 32 }
    }
}

#[test]
fn test_eq_by_and() {
    assert_eq_class! {
        eq_by(|v: &Person| v.name).and(eq_by(|v: &Person| v.age)),
        &Person { name: "Foo", age: 32 },
        =, &Person { name: "Foo", age: 32 },
        !, &Person { name: "Foo", age: 33 },
        !, &Person { name: "Bar", age: 32 }
    }
}

#[test]
fn test_fn_eq_class() {
    assert_eq_class! {
        |left: &str, right: &str| left.eq_ignore_ascii_case(right),
        "Foo",
        =, "Foo",
        =, "FOO",
        =, "foo",
        !, "Bar"
    }
}
