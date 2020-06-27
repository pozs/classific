# Classific

A Rust library for classifications like comparators and equivalence classes.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
classific = "0.1"
```

## Examples

```rust
use classific::{Comparator, EqClass, comparing_with, reverse_order, eq_by};

#[derive(PartialEq, Eq, Debug)]
struct Person<'a> {
    name: &'a str,
    age: u8,
}

fn main() {
    let foo = Person {
        name: "Foo",
        age: 32,
    };
    let bar = Person {
        name: "Bar",
        age: 32,
    };

    assert!(eq_by(|p: &Person| p.age).eq(&foo, &bar));
    assert_eq!(comparing_with(|p: &Person| p.name, reverse_order()).max(&foo, &bar), &bar);
}
```
