#![warn(missing_docs)]

//! # An owning reference.
//!
//! This crate provides the _owning reference_ types `OwningRef` and `OwningRefMut`
//! that enables it to bundle a reference together with the owner of the data it points to.
//! This allows moving and dropping of a `OwningRef` without needing to recreate the reference.
//!
//! It works by requiring owner types to dereference to stable memory locations
//! and preventing mutable access to root containers, which in practice requires heap allocation
//! as provided by `Box<T>`, `Rc<T>`, etc.
//!
//! Also provided are typedefs for common owner type combinations,
//! which allows for less verbose type signatures.
//! For example, `BoxRef<T>` instead of `OwningRef<Box<T>, T>`.
//!
//! # Examples
//!
//! ## Basics
//!
//! ```
//! extern crate owning_ref;
//! use owning_ref::BoxRef;
//!
//! fn main() {
//!     // Create an array owned by a Box.
//!     let arr = Box::new([1, 2, 3, 4]) as Box<[i32]>;
//!
//!     // Transfer into a BoxRef.
//!     let arr: BoxRef<[i32]> = BoxRef::new(arr);
//!     assert_eq!(&*arr, &[1, 2, 3, 4]);
//!
//!     // We can slice the array without losing ownership or changing type.
//!     let arr: BoxRef<[i32]> = arr.map(|arr| &arr[1..3]);
//!     assert_eq!(&*arr, &[2, 3]);
//!
//!     // Also works for Arc, Rc, String and Vec!
//! }
//! ```
//!
//! ## Caching a reference to a struct field
//!
//! ```
//! extern crate owning_ref;
//! use owning_ref::BoxRef;
//!
//! fn main() {
//!     struct Foo {
//!         tag: u32,
//!         x: u16,
//!         y: u16,
//!         z: u16,
//!     }
//!     let foo = Foo { tag: 1, x: 100, y: 200, z: 300 };
//!
//!     let or = BoxRef::new(Box::new(foo)).map(|foo| {
//!         match foo.tag {
//!             0 => &foo.x,
//!             1 => &foo.y,
//!             2 => &foo.z,
//!             _ => panic!(),
//!         }
//!     });
//!
//!     assert_eq!(*or, 200);
//! }
//! ```
//!
//! ## Caching a reference to an entry in a vector
//!
//! ```
//! extern crate owning_ref;
//! use owning_ref::VecRef;
//!
//! fn main() {
//!     let v = VecRef::new(vec![1, 2, 3, 4, 5]).map(|v| &v[3]);
//!     assert_eq!(*v, 4);
//! }
//! ```
//!
//! ## Caching a subslice of a String
//!
//! ```
//! extern crate owning_ref;
//! use owning_ref::StringRef;
//!
//! fn main() {
//!     let s = StringRef::new("hello world".to_owned())
//!         .map(|s| s.split(' ').nth(1).unwrap());
//!
//!     assert_eq!(&*s, "world");
//! }
//! ```
//!
//! ## Reference counted slices that share ownership of the backing storage
//!
//! ```
//! extern crate owning_ref;
//! use owning_ref::RcRef;
//! use std::rc::Rc;
//!
//! fn main() {
//!     let rc: RcRef<[i32]> = RcRef::new(Rc::new([1, 2, 3, 4]) as Rc<[i32]>);
//!     assert_eq!(&*rc, &[1, 2, 3, 4]);
//!
//!     let rc_a: RcRef<[i32]> = rc.clone().map(|s| &s[0..2]);
//!     let rc_b = rc.clone().map(|s| &s[1..3]);
//!     let rc_c = rc.clone().map(|s| &s[2..4]);
//!     assert_eq!(&*rc_a, &[1, 2]);
//!     assert_eq!(&*rc_b, &[2, 3]);
//!     assert_eq!(&*rc_c, &[3, 4]);
//!
//!     let rc_c_a = rc_c.clone().map(|s| &s[1]);
//!     assert_eq!(&*rc_c_a, &4);
//! }
//! ```
//!
//! ## Atomic reference counted slices that share ownership of the backing storage
//!
//! ```
//! extern crate owning_ref;
//! use owning_ref::ArcRef;
//! use std::sync::Arc;
//!
//! fn main() {
//!     use std::thread;
//!
//!     fn par_sum(rc: ArcRef<[i32]>) -> i32 {
//!         if rc.len() == 0 {
//!             return 0;
//!         } else if rc.len() == 1 {
//!             return rc[0];
//!         }
//!         let mid = rc.len() / 2;
//!         let left = rc.clone().map(|s| &s[..mid]);
//!         let right = rc.map(|s| &s[mid..]);
//!
//!         let left = thread::spawn(move || par_sum(left));
//!         let right = thread::spawn(move || par_sum(right));
//!
//!         left.join().unwrap() + right.join().unwrap()
//!     }
//!
//!     let rc: Arc<[i32]> = Arc::new([1, 2, 3, 4]);
//!     let rc: ArcRef<[i32]> = rc.into();
//!
//!     assert_eq!(par_sum(rc), 10);
//! }
//! ```
//!
//! ## References into RAII locks
//!
//! ```
//! extern crate owning_ref;
//! use owning_ref::RefRef;
//! use std::cell::{RefCell, Ref};
//!
//! fn main() {
//!     let refcell = RefCell::new((1, 2, 3, 4));
//!     // Also works with Mutex and RwLock
//!
//!     let refref = {
//!         let refref = RefRef::new(refcell.borrow()).map(|x| &x.3);
//!         assert_eq!(*refref, 4);
//!
//!         // We move the RAII lock and the reference to one of
//!         // the subfields in the data it guards here:
//!         refref
//!     };
//!
//!     assert_eq!(*refref, 4);
//!
//!     drop(refref);
//!
//!     assert_eq!(*refcell.borrow(), (1, 2, 3, 4));
//! }
//! ```
//!
//! ## Mutable reference
//!
//! When the owned container implements `DerefMut`, it is also possible to make
//! a _mutable owning reference_. (E.g. with `Box`, `RefMut`, `MutexGuard`)
//!
//! ```
//! extern crate owning_ref;
//! use owning_ref::RefMutRefMut;
//! use std::cell::{RefCell, RefMut};
//!
//! fn main() {
//!     let refcell = RefCell::new((1, 2, 3, 4));
//!
//!     let mut refmut_refmut = {
//!         let mut refmut_refmut = RefMutRefMut::new(refcell.borrow_mut()).map(|x| &mut x.3);
//!         assert_eq!(*refmut_refmut, 4);
//!         *refmut_refmut *= 2;
//!
//!         refmut_refmut
//!     };
//!
//!     assert_eq!(*refmut_refmut, 8);
//!     *refmut_refmut *= 2;
//!
//!     drop(refmut_refmut);
//!
//!     assert_eq!(*refcell.borrow(), (1, 2, 3, 16));
//! }
//! ```

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

/// A mutable owning reference.
///
/// This wraps an owner `O` and a reference `&mut T` pointing
/// at something reachable from `O::Target` while keeping
/// the ability to move `self` around.
///
/// The owner is usually a pointer that points at some base type.
///
/// For more details and examples, see the module and method docs.
pub struct OwningRefMut<O, T: ?Sized> {
    owner: O,
    reference: *mut T,
}

/// Helper trait for an erased concrete type an owner dereferences to.
/// This is used in form of a trait object for keeping
/// something around to (virtually) call the destructor.
pub trait Erased {}
impl<T> Erased for T {}

/// Helper trait for erasing the concrete type of what an owner derferences to,
/// for example `Box<T> -> Box<Erased>`. This would be unneeded with
/// higher kinded types support in the language.
pub unsafe trait IntoErased<'a> {
    /// Owner with the dereference type substituted to `Erased`.
    type Erased;
    /// Perform the type erasure.
    fn into_erased(self) -> Self::Erased;
}

// ############################################################################
// inherent API
// ############################################################################

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
              O: Deref<Target = T>
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

    /// Tries to convert `self` into a new owning reference that points
    /// at something reachable from the previous one.
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
    ///     let owning_ref = owning_ref.try_map(|array| {
    ///         if array[2] == 3 { Ok(&array[2]) } else { Err(()) }
    ///     });
    ///     assert_eq!(*owning_ref.unwrap(), 3);
    /// }
    /// ```
    pub fn try_map<F, U: ?Sized, E>(self, f: F) -> Result<OwningRef<O, U>, E>
        where O: StableAddress,
              F: FnOnce(&T) -> Result<&U, E>
    {
        f(&self).map(|it| it as *const _).map(move |it| {
            OwningRef {
                reference: it,
                owner: self.owner,
            }
        })
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
    pub fn erase_owner<'a>(self) -> OwningRef<O::Erased, T>
        where O: IntoErased<'a>
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

impl<O, T: ?Sized> OwningRefMut<O, T> {
    /// Creates a new mutable owning reference from a owner
    /// initialized to the direct dereference of it.
    ///
    /// # Example
    /// ```
    /// extern crate owning_ref;
    /// use owning_ref::OwningRefMut;
    ///
    /// fn main() {
    ///     let owning_ref_mut = OwningRefMut::new(Box::new(42));
    ///     assert_eq!(*owning_ref_mut, 42);
    /// }
    /// ```
    pub fn new(mut o: O) -> Self
        where O: StableAddress,
              O: DerefMut<Target = T>
    {
        OwningRefMut {
            reference: &mut *o,
            owner: o,
        }
    }

    /// Converts `self` into a new mutable owning reference that points
    /// at something reachable from the previous one.
    ///
    /// This can be a reference to a field of `U`, something reachable from a field of
    /// `U`, or even something unrelated with a `'static` lifetime.
    ///
    /// # Example
    /// ```
    /// extern crate owning_ref;
    /// use owning_ref::OwningRefMut;
    ///
    /// fn main() {
    ///     let owning_ref_mut = OwningRefMut::new(Box::new([1, 2, 3, 4]));
    ///
    ///     // create a owning reference that points at the
    ///     // third element of the array.
    ///     let owning_ref_mut = owning_ref_mut.map(|array| &mut array[2]);
    ///     assert_eq!(*owning_ref_mut, 3);
    /// }
    /// ```
    pub fn map<F, U: ?Sized>(mut self, f: F) -> OwningRefMut<O, U>
        where O: StableAddress,
              F: FnOnce(&mut T) -> &mut U
    {
        OwningRefMut {
            reference: f(&mut self),
            owner: self.owner,
        }
    }

    /// Tries to convert `self` into a new mutable owning reference that points
    /// at something reachable from the previous one.
    ///
    /// This can be a reference to a field of `U`, something reachable from a field of
    /// `U`, or even something unrelated with a `'static` lifetime.
    ///
    /// # Example
    /// ```
    /// extern crate owning_ref;
    /// use owning_ref::OwningRefMut;
    ///
    /// fn main() {
    ///     let owning_ref_mut = OwningRefMut::new(Box::new([1, 2, 3, 4]));
    ///
    ///     // create a owning reference that points at the
    ///     // third element of the array.
    ///     let owning_ref_mut = owning_ref_mut.try_map(|array| {
    ///         if array[2] == 3 { Ok(&mut array[2]) } else { Err(()) }
    ///     });
    ///     assert_eq!(*owning_ref_mut.unwrap(), 3);
    /// }
    /// ```
    pub fn try_map<F, U: ?Sized, E>(mut self, f: F) -> Result<OwningRefMut<O, U>, E>
        where O: StableAddress,
              F: FnOnce(&mut T) -> Result<&mut U, E>
    {
        f(&mut self).map(|it| it as *mut _).map(move |it| {
            OwningRefMut {
                reference: it,
                owner: self.owner,
            }
        })
    }

    /// Erases the concrete base type of the owner with a trait object.
    ///
    /// This allows mixing of owned references with different owner base types.
    ///
    /// # Example
    /// ```
    /// extern crate owning_ref;
    /// use owning_ref::{OwningRefMut, Erased};
    ///
    /// fn main() {
    ///     // NB: Using the concrete types here for explicitnes.
    ///     // For less verbose code type aliases like `BoxRef` are provided.
    ///
    ///     let owning_ref_mut_a: OwningRefMut<Box<[i32; 4]>, [i32; 4]>
    ///         = OwningRefMut::new(Box::new([1, 2, 3, 4]));
    ///
    ///     let owning_ref_mut_b: OwningRefMut<Box<Vec<(i32, bool)>>, Vec<(i32, bool)>>
    ///         = OwningRefMut::new(Box::new(vec![(0, false), (1, true)]));
    ///
    ///     let owning_ref_mut_a: OwningRefMut<Box<[i32; 4]>, i32>
    ///         = owning_ref_mut_a.map(|a| &mut a[0]);
    ///
    ///     let owning_ref_mut_b: OwningRefMut<Box<Vec<(i32, bool)>>, i32>
    ///         = owning_ref_mut_b.map(|a| &mut a[1].0);
    ///
    ///     let owning_refs_mut: [OwningRefMut<Box<Erased>, i32>; 2]
    ///         = [owning_ref_mut_a.erase_owner(), owning_ref_mut_b.erase_owner()];
    ///
    ///     assert_eq!(*owning_refs_mut[0], 1);
    ///     assert_eq!(*owning_refs_mut[1], 1);
    /// }
    /// ```
    pub fn erase_owner<'a>(self) -> OwningRefMut<O::Erased, T>
        where O: IntoErased<'a>
    {
        OwningRefMut {
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

// ############################################################################
// std traits
// ############################################################################

use std::ops::{Deref, DerefMut};
use std::convert::From;
use std::fmt::{self, Debug};
use std::marker::{Send, Sync};

impl<O, T: ?Sized> Deref for OwningRef<O, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.reference }
    }
}

impl<O, T: ?Sized> Deref for OwningRefMut<O, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.reference }
    }
}

impl<O, T: ?Sized> DerefMut for OwningRefMut<O, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.reference }
    }
}

impl<O, T: ?Sized> AsRef<T> for OwningRef<O, T> {
    fn as_ref(&self) -> &T {
        &*self
    }
}

impl<O, T: ?Sized> AsRef<T> for OwningRefMut<O, T> {
    fn as_ref(&self) -> &T {
        &*self
    }
}

impl<O, T: ?Sized> AsMut<T> for OwningRefMut<O, T> {
    fn as_mut(&mut self) -> &mut T {
        &mut *self
    }
}

impl<O, T: ?Sized> From<O> for OwningRef<O, T>
    where O: StableAddress,
          O: Deref<Target = T>
{
    fn from(owner: O) -> Self {
        OwningRef::new(owner)
    }
}

impl<O, T: ?Sized> From<O> for OwningRefMut<O, T>
    where O: StableAddress,
          O: DerefMut<Target = T>
{
    fn from(owner: O) -> Self {
        OwningRefMut::new(owner)
    }
}

impl<O, T: ?Sized> From<OwningRefMut<O, T>> for OwningRef<O, T>
    where O: StableAddress,
          O: DerefMut<Target = T>
{
    fn from(other: OwningRefMut<O, T>) -> Self {
        OwningRef {
            owner: other.owner,
            reference: other.reference,
        }
    }
}

// ^ FIXME: Is a Into impl for calling into_inner() possible as well?

impl<O, T: ?Sized> Debug for OwningRef<O, T>
    where O: Debug,
          T: Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f,
               "OwningRef {{ owner: {:?}, reference: {:?} }}",
               self.owner(),
               &**self)
    }
}

impl<O, T: ?Sized> Debug for OwningRefMut<O, T>
    where O: Debug,
          T: Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f,
               "OwningRefMut {{ owner: {:?}, reference: {:?} }}",
               self.owner(),
               &**self)
    }
}

impl<O, T: ?Sized> Clone for OwningRef<O, T>
    where O: CloneStableAddress
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
unsafe impl<O: Send, T: ?Sized> Send for OwningRefMut<O, T> {}
unsafe impl<O: Sync, T: ?Sized> Sync for OwningRefMut<O, T> {}

impl Debug for Erased {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "<Erased>",)
    }
}

// ############################################################################
// std types integration and convenience type defs
// ############################################################################

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
pub type RwLockReadGuardRef<'a, T, U = T> = OwningRef<RwLockReadGuard<'a, T>, U>;
/// Typedef of a owning reference that uses a `RwLockWriteGuard` as the owner.
pub type RwLockWriteGuardRef<'a, T, U = T> = OwningRef<RwLockWriteGuard<'a, T>, U>;

/// Typedef of a mutable owning reference that uses a `Box` as the owner.
pub type BoxRefMut<T, U = T> = OwningRefMut<Box<T>, U>;
/// Typedef of a mutable owning reference that uses a `Vec` as the owner.
pub type VecRefMut<T, U = T> = OwningRefMut<Vec<T>, U>;
/// Typedef of a mutable owning reference that uses a `String` as the owner.
pub type StringRefMut = OwningRefMut<String, str>;

/// Typedef of a mutable owning reference that uses a `RefMut` as the owner.
pub type RefMutRefMut<'a, T, U = T> = OwningRefMut<RefMut<'a, T>, U>;
/// Typedef of a mutable owning reference that uses a `MutexGuard` as the owner.
pub type MutexGuardRefMut<'a, T, U = T> = OwningRefMut<MutexGuard<'a, T>, U>;
/// Typedef of a mutable owning reference that uses a `RwLockWriteGuard` as the owner.
pub type RwLockWriteGuardRefMut<'a, T, U = T> = OwningRef<RwLockWriteGuard<'a, T>, U>;

unsafe impl<'a, T: 'a> IntoErased<'a> for Box<T> {
    type Erased = Box<Erased + 'a>;
    fn into_erased(self) -> Self::Erased {
        self
    }
}
unsafe impl<'a, T: 'a> IntoErased<'a> for Rc<T> {
    type Erased = Rc<Erased + 'a>;
    fn into_erased(self) -> Self::Erased {
        self
    }
}
unsafe impl<'a, T: 'a> IntoErased<'a> for Arc<T> {
    type Erased = Arc<Erased + 'a>;
    fn into_erased(self) -> Self::Erased {
        self
    }
}

/// Typedef of a owning reference that uses an erased `Box` as the owner.
pub type ErasedBoxRef<U> = OwningRef<Box<Erased>, U>;
/// Typedef of a owning reference that uses an erased `Rc` as the owner.
pub type ErasedRcRef<U> = OwningRef<Rc<Erased>, U>;
/// Typedef of a owning reference that uses an erased `Arc` as the owner.
pub type ErasedArcRef<U> = OwningRef<Arc<Erased>, U>;

/// Typedef of a mutable owning reference that uses an erased `Box` as the owner.
pub type ErasedBoxRefMut<U> = OwningRefMut<Box<Erased>, U>;

#[cfg(test)]
mod tests {
    mod owning_ref {
        use super::super::{OwningRef, BoxRef, Erased, ErasedBoxRef};

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
        fn try_map() {
            let or: BoxRef<String> = Box::new(example().1).into();
            let or: Result<BoxRef<_, str>, ()> = or.try_map(|x| Ok(&x[1..5]));
            assert_eq!(&*or.unwrap(), "ello");

            let or: BoxRef<String> = Box::new(example().1).into();
            let or: Result<BoxRef<_, str>, ()> = or.try_map(|_| Err(()));
            assert!(or.is_err());
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
            assert_eq!(&s,
                       "OwningRef { owner: \"hello world\", reference: \"hello\" }");
        }

        #[test]
        fn erased_owner() {
            let o1: BoxRef<Example, str> = BoxRef::new(Box::new(example())).map(|x| &x.1[..]);

            let o2: BoxRef<String, str> = BoxRef::new(Box::new(example().1)).map(|x| &x[..]);

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
            use super::super::{RefRef, RefMutRef};
            use std::cell::RefCell;
            use super::super::{MutexGuardRef, RwLockReadGuardRef, RwLockWriteGuardRef};
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
    }

    mod owning_ref_mut {
        use super::super::{OwningRefMut, BoxRefMut, Erased, ErasedBoxRefMut};

        #[derive(Debug, PartialEq)]
        struct Example(u32, String, [u8; 3]);
        fn example() -> Example {
            Example(42, "hello world".to_string(), [1, 2, 3])
        }

        #[test]
        fn new_deref() {
            let or: OwningRefMut<Box<()>, ()> = OwningRefMut::new(Box::new(()));
            assert_eq!(&*or, &());
        }

        #[test]
        fn new_deref_mut() {
            let mut or: OwningRefMut<Box<()>, ()> = OwningRefMut::new(Box::new(()));
            assert_eq!(&mut *or, &mut ());
        }

        #[test]
        fn mutate() {
            let mut or: OwningRefMut<Box<usize>, usize> = OwningRefMut::new(Box::new(0));
            assert_eq!(&*or, &0);
            *or = 1;
            assert_eq!(&*or, &1);
        }

        #[test]
        fn into() {
            let or: OwningRefMut<Box<()>, ()> = Box::new(()).into();
            assert_eq!(&*or, &());
        }

        #[test]
        fn map_offset_ref() {
            let or: BoxRefMut<Example> = Box::new(example()).into();
            let or: BoxRefMut<_, u32> = or.map(|x| &mut x.0);
            assert_eq!(&*or, &42);

            let or: BoxRefMut<Example> = Box::new(example()).into();
            let or: BoxRefMut<_, u8> = or.map(|x| &mut x.2[1]);
            assert_eq!(&*or, &2);
        }

        #[test]
        fn map_heap_ref() {
            let or: BoxRefMut<Example> = Box::new(example()).into();
            let or: BoxRefMut<_, str> = or.map(|x| &mut x.1[..5]);
            assert_eq!(&*or, "hello");
        }

        #[test]
        fn map_chained() {
            let or: BoxRefMut<String> = Box::new(example().1).into();
            let or: BoxRefMut<_, str> = or.map(|x| &mut x[1..5]);
            let or: BoxRefMut<_, str> = or.map(|x| &mut x[..2]);
            assert_eq!(&*or, "el");
        }

        #[test]
        fn map_chained_inference() {
            let or = BoxRefMut::new(Box::new(example().1))
                .map(|x| &mut x[..5])
                .map(|x| &mut x[1..3]);
            assert_eq!(&*or, "el");
        }

        #[test]
        fn try_map() {
            let or: BoxRefMut<String> = Box::new(example().1).into();
            let or: Result<BoxRefMut<_, str>, ()> = or.try_map(|x| Ok(&mut x[1..5]));
            assert_eq!(&*or.unwrap(), "ello");

            let or: BoxRefMut<String> = Box::new(example().1).into();
            let or: Result<BoxRefMut<_, str>, ()> = or.try_map(|_| Err(()));
            assert!(or.is_err());
        }

        #[test]
        fn owner() {
            let or: BoxRefMut<String> = Box::new(example().1).into();
            let or = or.map(|x| &mut x[..5]);
            assert_eq!(&*or, "hello");
            assert_eq!(&**or.owner(), "hello world");
        }

        #[test]
        fn into_inner() {
            let or: BoxRefMut<String> = Box::new(example().1).into();
            let or = or.map(|x| &mut x[..5]);
            assert_eq!(&*or, "hello");
            let s = *or.into_inner();
            assert_eq!(&s, "hello world");
        }

        #[test]
        fn fmt_debug() {
            let or: BoxRefMut<String> = Box::new(example().1).into();
            let or = or.map(|x| &mut x[..5]);
            let s = format!("{:?}", or);
            assert_eq!(&s,
                       "OwningRefMut { owner: \"hello world\", reference: \"hello\" }");
        }

        #[test]
        fn erased_owner() {
            let o1: BoxRefMut<Example, str> = BoxRefMut::new(Box::new(example()))
                .map(|x| &mut x.1[..]);

            let o2: BoxRefMut<String, str> = BoxRefMut::new(Box::new(example().1))
                .map(|x| &mut x[..]);

            let os: Vec<ErasedBoxRefMut<str>> = vec![o1.erase_owner(), o2.erase_owner()];
            assert!(os.iter().all(|e| &e[..] == "hello world"));
        }

        #[test]
        fn non_static_erased_owner() {
            let mut foo = [413, 612];
            let bar = &mut foo;

            let o: BoxRefMut<&mut [i32; 2]> = Box::new(bar).into();
            let o: BoxRefMut<&mut [i32; 2], i32> = o.map(|a: &mut &mut [i32; 2]| &mut a[0]);
            let o: BoxRefMut<Erased, i32> = o.erase_owner();

            assert_eq!(*o, 413);
        }

        #[test]
        fn raii_locks() {
            use super::super::RefMutRefMut;
            use std::cell::RefCell;
            use super::super::{MutexGuardRefMut, RwLockWriteGuardRefMut};
            use std::sync::{Mutex, RwLock};

            {
                let a = RefCell::new(1);
                let a = {
                    let a = RefMutRefMut::new(a.borrow_mut());
                    assert_eq!(*a, 1);
                    a
                };
                assert_eq!(*a, 1);
                drop(a);
            }
            {
                let a = Mutex::new(1);
                let a = {
                    let a = MutexGuardRefMut::new(a.lock().unwrap());
                    assert_eq!(*a, 1);
                    a
                };
                assert_eq!(*a, 1);
                drop(a);
            }
            {
                let a = RwLock::new(1);
                let a = {
                    let a = RwLockWriteGuardRefMut::new(a.write().unwrap());
                    assert_eq!(*a, 1);
                    a
                };
                assert_eq!(*a, 1);
                drop(a);
            }
        }

        #[test]
        fn into_owning_ref() {
            use super::super::BoxRef;

            let or: BoxRefMut<()> = Box::new(()).into();
            let or: BoxRef<()> = or.into();
            assert_eq!(&*or, &());
        }
    }
}
