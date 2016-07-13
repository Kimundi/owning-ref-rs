#![warn(missing_docs)]

/*!
# An owning reference.

This crate provides the _owning reference_ type `OwningRef` that enables it
to bundle a reference together with the owner of the data it points to.
This allows moving and dropping of a `OwningRef` without needing to recreate the reference.

It works by requiring owner types to dereference to stable memory locations and preventing mutable access, which in practice requires an heap allocation as
provided by `Box<T>`, `Rc<T>`, etc.

Also provided are typedefs for common owner type combinations,
which allows for less verbose type signatures. For example, `BoxRef<T>` instead of `OwningRef<Box<T>, T>`.

# Examples

## Basics

```
extern crate owning_ref;
use owning_ref::BoxRef;

fn main() {
    // Create an array owned by a Box.
    let arr = Box::new([1, 2, 3, 4]) as Box<[i32]>;

    // Transfer into a BoxRef.
    let arr: BoxRef<[i32]> = BoxRef::new(arr);
    assert_eq!(&*arr, &[1, 2, 3, 4]);

    // We can slice the array without losing ownership or changing type.
    let arr: BoxRef<[i32]> = arr.map(|arr| &arr[1..3]);
    assert_eq!(&*arr, &[2, 3]);

    // Also works for Arc, Rc, String and Vec!
}
```

## Caching a reference to a struct field

```
extern crate owning_ref;
use owning_ref::BoxRef;

fn main() {
    struct Foo {
        tag: u32,
        x: u16,
        y: u16,
        z: u16,
    }
    let foo = Foo { tag: 1, x: 100, y: 200, z: 300 };

    let or = BoxRef::new(Box::new(foo)).map(|foo| {
        match foo.tag {
            0 => &foo.x,
            1 => &foo.y,
            2 => &foo.z,
            _ => panic!(),
        }
    });

    assert_eq!(*or, 200);
}
```

## Caching a reference to an entry in a vector

```
extern crate owning_ref;
use owning_ref::VecRef;

fn main() {
    let v = VecRef::new(vec![1, 2, 3, 4, 5]).map(|v| &v[3]);
    assert_eq!(*v, 4);
}
```

## Caching a subslice of a String

```
extern crate owning_ref;
use owning_ref::StringRef;

fn main() {
    let s = StringRef::new("hello world".to_owned())
        .map(|s| s.split(' ').nth(1).unwrap());

    assert_eq!(&*s, "world");
}
```

## Reference counted slices that share ownership of the backing storage

```
extern crate owning_ref;
use owning_ref::RcRef;
use std::rc::Rc;

fn main() {
    let rc: RcRef<[i32]> = RcRef::new(Rc::new([1, 2, 3, 4]) as Rc<[i32]>);
    assert_eq!(&*rc, &[1, 2, 3, 4]);

    let rc_a: RcRef<[i32]> = rc.clone().map(|s| &s[0..2]);
    let rc_b = rc.clone().map(|s| &s[1..3]);
    let rc_c = rc.clone().map(|s| &s[2..4]);
    assert_eq!(&*rc_a, &[1, 2]);
    assert_eq!(&*rc_b, &[2, 3]);
    assert_eq!(&*rc_c, &[3, 4]);

    let rc_c_a = rc_c.clone().map(|s| &s[1]);
    assert_eq!(&*rc_c_a, &4);
}
```

## Atomic reference counted slices that share ownership of the backing storage

```
extern crate owning_ref;
use owning_ref::ArcRef;
use std::sync::Arc;

fn main() {
    use std::thread;

    fn par_sum(rc: ArcRef<[i32]>) -> i32 {
        if rc.len() == 0 {
            return 0;
        } else if rc.len() == 1 {
            return rc[0];
        }
        let mid = rc.len() / 2;
        let left = rc.clone().map(|s| &s[..mid]);
        let right = rc.map(|s| &s[mid..]);

        let left = thread::spawn(move || par_sum(left));
        let right = thread::spawn(move || par_sum(right));

        left.join().unwrap() + right.join().unwrap()
    }

    let rc: Arc<[i32]> = Arc::new([1, 2, 3, 4]);
    let rc: ArcRef<[i32]> = rc.into();

    assert_eq!(par_sum(rc), 10);
}
```

## References into RAII locks

```
extern crate owning_ref;
use owning_ref::RefRef;
use std::cell::{RefCell, Ref};

fn main() {
    let refcell = RefCell::new((1, 2, 3, 4));
    // Also works with Mutex and RwLock

    let refref = {
        let refref = RefRef::new(refcell.borrow()).map(|x| &x.3);
        assert_eq!(*refref, 4);

        // We move the RAII lock and the reference to one of
        // the subfields in the data it guards here:
        refref
    };

    assert_eq!(*refref, 4);

    drop(refref);

    assert_eq!(*refcell.borrow(), (1, 2, 3, 4));
}
```
*/

/// Marker trait for expressing that the memory address of the value
/// reachable via a dereference remains identical even if `self` gets moved.
pub unsafe trait StableAddress: Deref {}

/// Marker trait for expressing that the memory address of the value
/// reachable via a dereference remains identical even if `self` is a clone.
pub unsafe trait CloneStableAddress: StableAddress + Clone {}

/// An owning reference.
///
/// This wraps an owner `O` and a reference `&T` pointing
/// at something reachable from `O::Target` while keeping
/// the ability to move `self` around.
///
/// The owner is usually a pointer that points at some base type.
///
/// For more details and examples, see the module and method docs.
pub struct OwningRef<O, T: ?Sized> {
    owner: O,
    reference: *const T,
}

/// Helper trait for an erased concrete type an owner dereferences to.
/// This is used in form of a trait object for keeping
/// something around to (virtually) call the destructor.
pub trait Erased {}
impl<T> Erased for T {}

/// Helper trait for erasing the concrete type of what an owner derferences to,
/// for example `Box<T> -> Box<Erased>`. This would be unneeded with
/// higher kinded types support in the language.
pub unsafe trait IntoErased {
    /// Owner with the dereference type substituted to `Erased`.
    type Erased;
    /// Perform the type erasure.
    fn into_erased(self) -> Self::Erased;
}

/////////////////////////////////////////////////////////////////////////////
// inherent API
/////////////////////////////////////////////////////////////////////////////

impl<O, T: ?Sized> OwningRef<O, T> {
    /// Creates a new owning reference from a owner
    /// initialized to the direct dereference of it.
    ///
    /// # Example
    /// ```
    /// extern crate owning_ref;
    /// use owning_ref::OwningRef;
    ///
    /// fn main() {
    ///     let owning_ref = OwningRef::new(Box::new(42));
    ///     assert_eq!(*owning_ref, 42);
    /// }
    /// ```
    pub fn new(o: O) -> Self
        where O: StableAddress,
              O: Deref<Target = T>,
    {
        OwningRef {
            reference: &*o,
            owner: o,
        }
    }

    /// Converts `self` into a new owning reference that points at something reachable
    /// from the previous one.
    ///
    /// This can be a reference to a field of `U`, something reachable from a field of
    /// `U`, or even something unrelated with a `'static` lifetime.
    ///
    /// # Example
    /// ```
    /// extern crate owning_ref;
    /// use owning_ref::OwningRef;
    ///
    /// fn main() {
    ///     let owning_ref = OwningRef::new(Box::new([1, 2, 3, 4]));
    ///
    ///     // create a owning reference that points at the
    ///     // third element of the array.
    ///     let owning_ref = owning_ref.map(|array| &array[2]);
    ///     assert_eq!(*owning_ref, 3);
    /// }
    /// ```
    pub fn map<F, U: ?Sized>(self, f: F) -> OwningRef<O, U>
        where O: StableAddress,
              F: FnOnce(&T) -> &U
    {
        OwningRef {
            reference: f(&self),
            owner: self.owner,
        }
    }

    /// Erases the concrete base type of the owner with a trait object.
    ///
    /// This allows mixing of owned references with different owner base types.
    ///
    /// # Example
    /// ```
    /// extern crate owning_ref;
    /// use owning_ref::{OwningRef, Erased};
    ///
    /// fn main() {
    ///     // NB: Using the concrete types here for explicitnes.
    ///     // For less verbose code type aliases like `BoxRef` are provided.
    ///
    ///     let owning_ref_a: OwningRef<Box<[i32; 4]>, [i32; 4]>
    ///         = OwningRef::new(Box::new([1, 2, 3, 4]));
    ///
    ///     let owning_ref_b: OwningRef<Box<Vec<(i32, bool)>>, Vec<(i32, bool)>>
    ///         = OwningRef::new(Box::new(vec![(0, false), (1, true)]));
    ///
    ///     let owning_ref_a: OwningRef<Box<[i32; 4]>, i32>
    ///         = owning_ref_a.map(|a| &a[0]);
    ///
    ///     let owning_ref_b: OwningRef<Box<Vec<(i32, bool)>>, i32>
    ///         = owning_ref_b.map(|a| &a[1].0);
    ///
    ///     let owning_refs: [OwningRef<Box<Erased>, i32>; 2]
    ///         = [owning_ref_a.erase_owner(), owning_ref_b.erase_owner()];
    ///
    ///     assert_eq!(*owning_refs[0], 1);
    ///     assert_eq!(*owning_refs[1], 1);
    /// }
    /// ```
    pub fn erase_owner(self) -> OwningRef<O::Erased, T>
        where O: IntoErased,
    {
        OwningRef {
            reference: self.reference,
            owner: self.owner.into_erased(),
        }
    }

    // TODO: wrap_owner

    // FIXME: Naming convention?
    /// A getter for the underlying owner.
    pub fn owner(&self) -> &O {
        &self.owner
    }

    // FIXME: Naming convention?
    /// Discards the reference and retrieves the owner.
    pub fn into_inner(self) -> O {
        self.owner
    }
}

/////////////////////////////////////////////////////////////////////////////
// std traits
/////////////////////////////////////////////////////////////////////////////

use std::ops::Deref;
use std::convert::From;
use std::fmt::{self, Debug};
use std::marker::{Send, Sync};

impl<O, T: ?Sized> Deref for OwningRef<O, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe {
            &*self.reference
        }
    }
}

impl<O, T: ?Sized> AsRef<T> for OwningRef<O, T> {
    fn as_ref(&self) -> &T {
        &*self
    }
}

impl<O, T: ?Sized> From<O> for OwningRef<O, T>
    where O: StableAddress, O: Deref<Target = T>,
{
    fn from(owner: O) -> Self {
        OwningRef::new(owner)
    }
}

// ^ FIXME: Is a Into impl for calling into_inner() possible as well?

impl<O, T: ?Sized> Debug for OwningRef<O, T>
    where O: Debug, T: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "OwningRef {{ owner: {:?}, reference: {:?} }}",
               self.owner(), &**self)
    }
}

impl<O, T: ?Sized> Clone for OwningRef<O, T>
    where O: CloneStableAddress,
{
    fn clone(&self) -> Self {
        OwningRef {
            owner: self.owner.clone(),
            reference: self.reference,
        }
    }
}

unsafe impl<O: Send, T: ?Sized> Send for OwningRef<O, T> {}
unsafe impl<O: Sync, T: ?Sized> Sync for OwningRef<O, T> {}

impl Debug for Erased {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "<Erased>",)
    }
}

/////////////////////////////////////////////////////////////////////////////
// std types integration and convenience type defs
/////////////////////////////////////////////////////////////////////////////

use std::boxed::Box;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::{MutexGuard, RwLockReadGuard, RwLockWriteGuard};
use std::cell::{Ref, RefMut};

unsafe impl<T: ?Sized> StableAddress for Box<T> {}
unsafe impl<T> StableAddress for Vec<T> {}
unsafe impl StableAddress for String {}

unsafe impl<T: ?Sized> StableAddress for Rc<T> {}
unsafe impl<T: ?Sized> CloneStableAddress for Rc<T> {}
unsafe impl<T: ?Sized> StableAddress for Arc<T> {}
unsafe impl<T: ?Sized> CloneStableAddress for Arc<T> {}

unsafe impl<'a, T: ?Sized> StableAddress for Ref<'a, T> {}
unsafe impl<'a, T: ?Sized> StableAddress for RefMut<'a, T> {}
unsafe impl<'a, T: ?Sized> StableAddress for MutexGuard<'a, T> {}
unsafe impl<'a, T: ?Sized> StableAddress for RwLockReadGuard<'a, T> {}
unsafe impl<'a, T: ?Sized> StableAddress for RwLockWriteGuard<'a, T> {}

/// Typedef of a owning reference that uses a `Box` as the owner.
pub type BoxRef<T, U = T> = OwningRef<Box<T>, U>;
/// Typedef of a owning reference that uses a `Vec` as the owner.
pub type VecRef<T, U = T> = OwningRef<Vec<T>, U>;
/// Typedef of a owning reference that uses a `String` as the owner.
pub type StringRef = OwningRef<String, str>;

/// Typedef of a owning reference that uses a `Rc` as the owner.
pub type RcRef<T, U = T> = OwningRef<Rc<T>, U>;
/// Typedef of a owning reference that uses a `Arc` as the owner.
pub type ArcRef<T, U = T> = OwningRef<Arc<T>, U>;

/// Typedef of a owning reference that uses a `Ref` as the owner.
pub type RefRef<'a, T, U = T> = OwningRef<Ref<'a, T>, U>;
/// Typedef of a owning reference that uses a `RefMut` as the owner.
pub type RefMutRef<'a, T, U = T> = OwningRef<RefMut<'a, T>, U>;
/// Typedef of a owning reference that uses a `MutexGuard` as the owner.
pub type MutexGuardRef<'a, T, U = T> = OwningRef<MutexGuard<'a, T>, U>;
/// Typedef of a owning reference that uses a `RwLockReadGuard` as the owner.
pub type RwLockReadGuardRef<'a, T, U = T>
    = OwningRef<RwLockReadGuard<'a, T>, U>;
/// Typedef of a owning reference that uses a `RwLockWriteGuard` as the owner.
pub type RwLockWriteGuardRef<'a, T, U = T>
    = OwningRef<RwLockWriteGuard<'a, T>, U>;

unsafe impl<'a, T: 'a> IntoErased for Box<T> {
    type Erased = Box<Erased + 'a>;
    fn into_erased(self) -> Self::Erased { self }
}
unsafe impl<'a, T: 'a> IntoErased for Rc<T> {
    type Erased = Rc<Erased + 'a>;
    fn into_erased(self) -> Self::Erased { self }
}
unsafe impl<'a, T: 'a> IntoErased for Arc<T> {
    type Erased = Arc<Erased + 'a>;
    fn into_erased(self) -> Self::Erased { self }
}

/// Typedef of a owning reference that uses an erased `Box` as the owner.
pub type ErasedBoxRef<U> = OwningRef<Box<Erased>, U>;
/// Typedef of a owning reference that uses an erased `Rc` as the owner.
pub type ErasedRcRef<U> = OwningRef<Rc<Erased>, U>;
/// Typedef of a owning reference that uses an erased `Arc` as the owner.
pub type ErasedArcRef<U> = OwningRef<Arc<Erased>, U>;

/////////////////////////////////////////////////////////////////////////////
// aref
/////////////////////////////////////////////////////////////////////////////

type ARefStorage = [usize; 3];

// We can't call drop_in_place directly, see https://github.com/rust-lang/rust/issues/34123
unsafe fn aref_drop_wrapper<T>(t: *mut ARefStorage) {
    std::ptr::drop_in_place::<T>(t as *mut _ as *mut T);
}

/// This wraps a reference `&T` pointing
/// at something reachable from the owner, while keeping
/// the ability to move `self` around. Unlike OwningRef,
/// the owner is completely abstracted, and can't be extracted. 
///
/// The owner must be a pointer which is three usizes big or less,
/// (this size was chosen to make Vec, String, Ref etc fit).
pub struct ARef<U: ?Sized> {
    inner: OwningRef<(), U>,
    owner: ARefStorage,
    dropfn: unsafe fn (*mut ARefStorage)
}

impl<U: ?Sized> Drop for ARef<U> {
    fn drop(&mut self) {
        unsafe {
            (self.dropfn)(&mut self.owner);
        }
    }
}

impl<U: ?Sized> Deref for ARef<U> {
    type Target = U;

    fn deref(&self) -> &U {
        &*self.inner
    }
}

impl<U: ?Sized> AsRef<U> for ARef<U> {
    fn as_ref(&self) -> &U {
        &*self.inner
    }
}

impl<U: ?Sized> ARef<U> {
    /// Creates a new reference from an owner
    /// initialized to the direct dereference of it.
    ///
    /// # Example
    /// ```
    /// extern crate owning_ref;
    /// use owning_ref::ARef;
    ///
    /// fn main() {
    ///     let aref = ARef::new(Box::new(42));
    ///     assert_eq!(*aref, 42);
    /// }
    /// ```
    pub fn new<O>(o: O) -> Self
        where O: StableAddress,
              O: Deref<Target = U>,
    {
        OwningRef::new(o).into()
    }


    /// Converts `self` into a new reference that points at something reachable
    /// from the previous one.
    ///
    /// This can be a reference to a field of `T`, something reachable from a field of
    /// `T`, or even something unrelated with a `'static` lifetime.
    ///
    /// # Example
    /// ```
    /// extern crate owning_ref;
    /// use owning_ref::ARef;
    ///
    /// fn main() {
    ///     let aref = ARef::new(Box::new([1, 2, 3, 4]));
    ///
    ///     // create a owning reference that points at the
    ///     // third element of the array.
    ///     let aref = aref.map(|array| &array[2]);
    ///     assert_eq!(*aref, 3);
    /// }
    /// ```
    pub fn map<F, T: ?Sized>(self, f: F) -> ARef<T>
        where F: FnOnce(&U) -> &T
    {
        let newref: *const _ = f(&self);
        let owner = self.owner;
        let dropfn = self.dropfn;
        std::mem::forget(self);

        ARef {
            inner: OwningRef { reference: newref, owner: () },
            owner: owner,
            dropfn: dropfn,
        }
    }
}

impl<O, U: ?Sized> From<OwningRef<O, U>> for ARef<U>
{
    fn from(oref: OwningRef<O, U>) -> Self {
        assert!(std::mem::size_of::<O>() <= std::mem::size_of::<ARefStorage>());
        let OwningRef { owner, reference } = oref;
        unsafe {
            let mut storage: ARefStorage = std::mem::uninitialized();
            std::ptr::copy(&owner, &mut storage as *mut _ as *mut O, 1);
            std::mem::forget(owner);
            ARef {
                inner: OwningRef { owner: (), reference: reference },
                dropfn: aref_drop_wrapper::<O>,
                owner: storage,
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use super::{OwningRef, BoxRef, Erased, ErasedBoxRef};

    #[derive(Debug, PartialEq)]
    struct Example(u32, String, [u8; 3]);
    fn example() -> Example {
        Example(42, "hello world".to_string(), [1, 2, 3])
    }

    #[test]
    fn new_deref() {
        let or: OwningRef<Box<()>, ()> = OwningRef::new(Box::new(()));
        assert_eq!(&*or, &());
    }

    #[test]
    fn into() {
        let or: OwningRef<Box<()>, ()> = Box::new(()).into();
        assert_eq!(&*or, &());
    }

    #[test]
    fn map_offset_ref() {
        let or: BoxRef<Example> = Box::new(example()).into();
        let or: BoxRef<_, u32> = or.map(|x| &x.0);
        assert_eq!(&*or, &42);

        let or: BoxRef<Example> = Box::new(example()).into();
        let or: BoxRef<_, u8> = or.map(|x| &x.2[1]);
        assert_eq!(&*or, &2);
    }

    #[test]
    fn map_heap_ref() {
        let or: BoxRef<Example> = Box::new(example()).into();
        let or: BoxRef<_, str> = or.map(|x| &x.1[..5]);
        assert_eq!(&*or, "hello");
    }

    #[test]
    fn map_static_ref() {
        let or: BoxRef<()> = Box::new(()).into();
        let or: BoxRef<_, str> = or.map(|_| "hello");
        assert_eq!(&*or, "hello");
    }

    #[test]
    fn map_chained() {
        let or: BoxRef<String> = Box::new(example().1).into();
        let or: BoxRef<_, str> = or.map(|x| &x[1..5]);
        let or: BoxRef<_, str> = or.map(|x| &x[..2]);
        assert_eq!(&*or, "el");
    }

    #[test]
    fn map_chained_inference() {
        let or = BoxRef::new(Box::new(example().1))
            .map(|x| &x[..5])
            .map(|x| &x[1..3]);
        assert_eq!(&*or, "el");
    }

    #[test]
    fn owner() {
        let or: BoxRef<String> = Box::new(example().1).into();
        let or = or.map(|x| &x[..5]);
        assert_eq!(&*or, "hello");
        assert_eq!(&**or.owner(), "hello world");
    }

    #[test]
    fn into_inner() {
        let or: BoxRef<String> = Box::new(example().1).into();
        let or = or.map(|x| &x[..5]);
        assert_eq!(&*or, "hello");
        let s = *or.into_inner();
        assert_eq!(&s, "hello world");
    }

    #[test]
    fn fmt_debug() {
        let or: BoxRef<String> = Box::new(example().1).into();
        let or = or.map(|x| &x[..5]);
        let s = format!("{:?}", or);
        assert_eq!(&s, "OwningRef { owner: \"hello world\", reference: \"hello\" }");
    }

    #[test]
    fn erased_owner() {
        let o1: BoxRef<Example, str> = BoxRef::new(Box::new(example()))
            .map(|x| &x.1[..]);

        let o2: BoxRef<String, str> = BoxRef::new(Box::new(example().1))
            .map(|x| &x[..]);

        let os: Vec<ErasedBoxRef<str>> = vec![o1.erase_owner(), o2.erase_owner()];
        assert!(os.iter().all(|e| &e[..] == "hello world"));
    }

    #[test]
    fn non_static_erased_owner() {
        let foo = [413, 612];
        let bar = &foo;

        let o: BoxRef<&[i32; 2]> = Box::new(bar).into();
        let o: BoxRef<&[i32; 2], i32> = o.map(|a: &&[i32; 2]| &a[0]);
        let o: BoxRef<Erased, i32> = o.erase_owner();

        assert_eq!(*o, 413);
    }

    #[test]
    fn raii_locks() {
        use super::{RefRef, RefMutRef};
        use std::cell::RefCell;
        use super::{MutexGuardRef, RwLockReadGuardRef, RwLockWriteGuardRef};
        use std::sync::{Mutex, RwLock};

        {
            let a = RefCell::new(1);
            let a = {
                let a = RefRef::new(a.borrow());
                assert_eq!(*a, 1);
                a
            };
            assert_eq!(*a, 1);
            drop(a);
        }
        {
            let a = RefCell::new(1);
            let a = {
                let a = RefMutRef::new(a.borrow_mut());
                assert_eq!(*a, 1);
                a
            };
            assert_eq!(*a, 1);
            drop(a);
        }
        {
            let a = Mutex::new(1);
            let a = {
                let a = MutexGuardRef::new(a.lock().unwrap());
                assert_eq!(*a, 1);
                a
            };
            assert_eq!(*a, 1);
            drop(a);
        }
        {
            let a = RwLock::new(1);
            let a = {
                let a = RwLockReadGuardRef::new(a.read().unwrap());
                assert_eq!(*a, 1);
                a
            };
            assert_eq!(*a, 1);
            drop(a);
        }
        {
            let a = RwLock::new(1);
            let a = {
                let a = RwLockWriteGuardRef::new(a.write().unwrap());
                assert_eq!(*a, 1);
                a
            };
            assert_eq!(*a, 1);
            drop(a);
        }
    }

    #[test]
    fn aref_locks() {
        use super::{ARef, RefMutRef};
        use std::cell::RefCell;
        {
            let b = RefCell::new(1);
            let a = {
                let a = RefMutRef::new(b.borrow_mut());
                let a: ARef<_> = a.into();
                assert_eq!(*a, 1);
                a
            };
            assert_eq!(*a, 1);
            drop(a);
            assert_eq!(*b.borrow_mut(), 1);
        }
    }

    #[test]
    fn aref_map() {
        use super::{ARef, StringRef};

        let a: StringRef = String::from("Hello world").into();
        let a: ARef<str> = a.into();
        assert_eq!(&*a, "Hello world");
        let a = a.map(|s| {
            assert_eq!(s, "Hello world");
            &s[6..]
        });
        assert_eq!(&*a, "world");
    }

    #[test]
    fn aref_sizes() {
        use super::ARef;
        use std::sync::{Arc, Mutex, RwLock};
        use std::rc::Rc;
        use std::cell::RefCell;

        let a = Mutex::new(1);
        let _ = ARef::new(a.lock().unwrap());

        let a = RwLock::new(1);
        let _ = ARef::new(a.read().unwrap());
        let _ = ARef::new(a.write().unwrap());

        let a = RefCell::new(1);
        let _ = ARef::new(a.borrow());
        let _ = ARef::new(a.borrow_mut());

        let _ = ARef::new(Box::new(1));
        let _ = ARef::new(Rc::new(1));
        let _ = ARef::new(Arc::new(1));

        let _ = ARef::new(vec![1, 2, 3, 4]);
    }
}
