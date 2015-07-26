owning-ref-rs
==============

[![Travis-CI Status](https://travis-ci.org/Kimundi/owning-ref-rs.png?branch=master)](https://travis-ci.org/Kimundi/owning-ref-rs)

A library for creating references that carry their owner with them.

For more details, see the [docs](http://kimundi.github.io/owning-ref-rs/owning_ref/index.html).

# Getting Started

[owning-ref-rs is available on crates.io](https://crates.io/crates/owning_ref).
Add the following dependency to your Cargo manifest to get the latest version of the 0.1 branch:
```
[dependencies]

owning_ref = "0.1.*"
```

To always get the latest version, add this git repository to your
Cargo manifest:

```
[dependencies.owning_ref]
git = "https://github.com/Kimundi/owning-ref-rs"
```
# Example

```rust
extern crate owning_ref;
use owning_ref::RcRef;

fn main() {
    // Let's create a few reference counted slices that point to the same memory:

    let rc: RcRef<[i32]> = RcRef::new(Rc::new([1, 2, 3, 4]) as Rc<[i32]>);
    assert_eq!(&*rc, &[1, 2, 3, 4]);

    let rc_a: RcRef<[i32]> = rc.clone().map(|s| &s[0..2]);
    let rc_b = rc.clone().map(|s| &s[1..3]);
    let rc_c = rc.clone().map(|s| &s[2..4]);
    assert_eq!(&*rc_a, &[1, 2]);
    assert_eq!(&*rc_b, &[2, 3]);
    assert_eq!(&*rc_c, &[3, 4]);
}
```
