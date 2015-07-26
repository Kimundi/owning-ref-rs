//#![warn(missing_docs)]

pub unsafe trait StableAddress: Deref {}
pub unsafe trait CloneStableAddress: StableAddress + Clone {}

pub struct OwningRef<O, T: ?Sized> {
    owner: O,
    reference: *const T,
}

pub trait Erased {}
impl<T> Erased for T {}

pub unsafe trait IntoErased {
    type Erased;
    fn into_erased(self) -> Self::Erased;
}

/////////////////////////////////////////////////////////////////////////////
// inherent API
/////////////////////////////////////////////////////////////////////////////

impl<O, T: ?Sized> OwningRef<O, T> {
    pub fn new(o: O) -> Self
        where O: StableAddress,
        O: Deref<Target = T>,
    {
        OwningRef {
            reference: &*o,
            owner: o,
        }
    }

    pub fn map<F, U: ?Sized>(self, f: F) -> OwningRef<O, U>
        where O: StableAddress,
              F: FnOnce(&T) -> &U
    {
        OwningRef {
            reference: f(&self),
            owner: self.owner,
        }
    }

    pub fn erase_owner(self) -> OwningRef<O::Erased, T>
        where O: IntoErased,
    {
        OwningRef {
            reference: self.reference,
            owner: self.owner.into_erased(),
        }
    }

    pub fn owner(&self) -> &O {
        &self.owner
    }

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

/////////////////////////////////////////////////////////////////////////////
// std types integration and convenience type defs
/////////////////////////////////////////////////////////////////////////////

use std::boxed::Box;
use std::rc::Rc;
use std::sync::Arc;

unsafe impl<T: ?Sized> StableAddress for Box<T> {}
unsafe impl<T> StableAddress for Vec<T> {}
unsafe impl StableAddress for String {}
#[cfg(feature = "nightly")]
unsafe impl<T: ?Sized> StableAddress for Rc<T> {}
#[cfg(feature = "nightly")]
unsafe impl<T: ?Sized> StableAddress for Arc<T> {}
#[cfg(not(feature = "nightly"))]
unsafe impl<T> StableAddress for Rc<T> {}
#[cfg(not(feature = "nightly"))]
unsafe impl<T> StableAddress for Arc<T> {}

#[cfg(feature = "nightly")]
unsafe impl<T: ?Sized> CloneStableAddress for Rc<T> {}
#[cfg(feature = "nightly")]
unsafe impl<T: ?Sized> CloneStableAddress for Arc<T> {}
#[cfg(not(feature = "nightly"))]
unsafe impl<T> CloneStableAddress for Rc<T> {}
#[cfg(not(feature = "nightly"))]
unsafe impl<T> CloneStableAddress for Arc<T> {}

pub type BoxRef<T, U = T> = OwningRef<Box<T>, U>;
pub type VecRef<T, U = T> = OwningRef<Vec<T>, U>;
pub type StringRef = OwningRef<String, str>;
pub type RcRef<T, U = T> = OwningRef<Rc<T>, U>;
pub type ArcRef<T, U = T> = OwningRef<Arc<T>, U>;

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

pub type ErasedBoxRef<U> = OwningRef<Box<Erased>, U>;
pub type ErasedRcRef<U> = OwningRef<Rc<Erased>, U>;
pub type ErasedArcRef<U> = OwningRef<Arc<Erased>, U>;

#[cfg(test)]
mod tests {
    use super::OwningRef;
    use super::{BoxRef, VecRef, StringRef, RcRef, ArcRef};
    use super::{Erased, ErasedBoxRef};

    use std::rc::Rc;
    use std::sync::Arc;

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

    /////////////////////////////////////////////////////////////////////////
    // Tests of example uses cases for each supported owner type:
    /////////////////////////////////////////////////////////////////////////

    #[test]
    fn box_ref() {
        // Caching a reference to a struct field

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
                _ => {
                    static INVALID: u16 = !0;
                    &INVALID
                }
            }
        });

        assert_eq!(*or, 200);
    }

    #[test]
    fn vec_ref() {
        // Cache a reference to an entry in a vector

        let v = VecRef::new(vec![1, 2, 3, 4, 5]).map(|v| &v[3]);
        assert_eq!(*v, 4);
    }

    #[test]
    fn string_ref() {
        // Caching a subslice of a String

        let s = StringRef::new("hello world".to_owned())
            .map(|s| s.split(' ').nth(1).unwrap());

        assert_eq!(&*s, "world");
    }

    #[test]
    #[cfg(feature = "nightly")]
    fn rc_ref() {
        // Creating many subslices that share ownership of the backing storage

        let rc: Rc<[i32]> = Rc::new([1, 2, 3, 4]);
        let rc: RcRef<[i32]> = rc.into();
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

    #[test]
    #[cfg(feature = "nightly")]
    fn arc_ref() {
        // Calculate the sum of a atomic shared slice in parallel

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

}
