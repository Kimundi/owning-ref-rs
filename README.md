owning-ref-rs
==============

[![Travis-CI Status](https://travis-ci.org/Kimundi/owning-ref-rs.png?branch=master)](https://travis-ci.org/Kimundi/owning-ref-rs)

A library for creating references that carry their owner with them.

Using this library, it is possible
Using this macro, it is possible to have `static`s that require code to be
executed at runtime in order to be initialized.
This includes anything requiring heap allocations, like vectors or hash maps,
as well as anything that requires function calls to be computed.

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

fn main() {

}
```
