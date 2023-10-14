#![allow(unused_imports)]

use core::{marker, mem, mem::MaybeUninit};

use builtin::*;
use builtin_macros::*;
use crate::*;
use crate::pervasive::*;
use crate::modes::*;
use crate::prelude::*;

verus!{

/// `PPtr<V>` (which stands for "permissioned pointer")
/// is a wrapper around a raw pointer to `V` on the heap.
///
/// Technically, it is a wrapper around `*mut mem::MaybeUninit<V>`, that is, the object
/// it points to may be uninitialized.
///
/// In order to access (read or write) the value behind the pointer, the user needs
/// a special _ghost permission token_, [`PointsTo<V>`](PointsTo). This object is `tracked`,
/// which means that it is "only a proof construct" that does not appear in code,
/// but its uses _are_ checked by the borrow-checker. This ensures memory safety,
/// data-race-freedom, prohibits use-after-free, etc.
///
/// ### PointsTo objects.
///
/// The [`PointsTo`] object represents both the ability to access the data behind the
/// pointer _and_ the ability to free it (return it to the memory allocator).
///
/// In particular:
///  * When the user owns a `PointsTo<V>` object associated to a given pointer,
///    they can either read or write its contents, or deallocate ("free") it.
///  * When the user has a shared borrow, `&PointsTo<V>`, they can read
///    the contents (i.e., obtained a shared borrow `&V`).
///
/// The `perm: PointsTo<V>` object tracks two pieces of data:
///  * `perm.pptr` is the pointer that the permission is associated to,
///     given by [`ptr.id()`](PPtr::id).
///  * `perm.value` tracks the data that is behind the pointer. Thereby:
///      * When the user uses the permission to _read_ a value, they always
///        read the value as given by the `perm.value`.
///      * When the user uses the permission to _write_ a value, the `perm.value`
///        data is updated.
///
/// For those familiar with separation logic, the `PointsTo` object plays a role
/// similar to that of the "points-to" operator, _ptr_ ↦ _value_.
///
/// ### Differences from `PCell`.
///
/// `PPtr` is similar to [`cell::PCell`], but has a few key differences:
///  * In `PCell<T>`, the type `T` is placed internally to the `PCell`, whereas with `PPtr`,
///    the type `T` is placed at some location on the heap.
///  * Since `PPtr` is just a pointer (represented by an integer), it can be `Copy`.
///  * The `ptr::PointsTo` token represents not just the permission to read/write
///    the contents, but also to deallocate.
///
/// ### Example (TODO)

// Notes about pointer provenance:
// 
// "Pointer provenance" is this complicated subject which is a necessary
// evil if you want to understand the abstract machine semantics of a language
// with pointers and what is or is not UB with int-to-pointer casts.
//
// See this series of blog posts for some introduction:
// https://www.ralfj.de/blog/2022/04/11/provenance-exposed.html
//
// Here in Verus, where code is forced to be verified, we want to tell
// a much simpler story, which is the following:
//
//   ***** VERUS POINTER MODEL *****
//    "Provenance" comes from the `tracked ghost` PointsTo object.
//   *******************************
// 
// Pretty simple, right?
//
// Of course, this trusted pointer library still needs to actually run and
// be sound in the Rust backend.
// Rust's abstract pointer model is unchanged, and it doesn't know anything
// about Verus's special ghost `PointsTo` object, which gets erased, anyway.
//
// Maybe someday the ghost PointsTo model will become a real
// memory model. That isn't true today.
// So we still need to know something about actual, real memory models that
// are used right now in order to implement this API soundly.
//
// Our goal is to allow the *user of Verus* to think in terms of the
// VERUS POINTER MODEL where provenance is tracked via the `PointsTo` object.
// The rest of this is just details for the trusted implementation of PPtr
// that will be sound in the Rust backend.
//
// In the "PNVI-ae-udi" model:
//  * A ptr->int cast "exposes" a pointer (adding it some global list in the 
//    abstract machine)
//  * An int->ptr cast acquires the provenance of that pointer only if it
//    was previously exposed.
//
// The "tower of weakenings", however,
// (see https://gankra.github.io/blah/tower-of-weakenings/)
// proposes a stricter model called "Strict Provenance".
// This basically forbids exposing and requires provenance to always be tracked.
//
// If possible, it would be nice to stick to this stricter model, but it isn't necessary.
//
// Unfortunately, it's not possible. The Strict Provenance requires "provenance" to be
// tracked through non-ghost pointers. We can't use our ghost objects to track provenance
// in general while staying consistent with Strict Provenance.
//
// We have two options:
//
//  1. Just forbid int->ptr conversions
//  2. Always "expose" every PPtr when it's created, in order to definitely be safe
//     under PNVI-ae-udi.
//
// However, int->ptr conversions ought to be allowed in the VERUS POINTER MODEL,
// so I'm going with (2) here.

// TODO implement: borrow_mut; figure out Drop, see if we can avoid leaking?

#[verifier(external_body)]
#[verifier::accept_recursive_types(V)]
pub struct PPtrSeq<V> {
    uptr: *mut MaybeUninit<V>,
}

// PPtr is always safe to Send/Sync. It's the PointsTo object where Send/Sync matters.
// It doesn't matter if you send the pointer to another thread if you can't access it.

#[verifier(external)]
unsafe impl<T> Sync for PPtrSeq<T> {}

#[verifier(external)]
unsafe impl<T> Send for PPtrSeq<T> {}

// TODO split up the "deallocation" permission and the "access" permission?

/// A `tracked` ghost object that gives the user permission to dereference a pointer
/// for reading or writing, or to free the memory at that pointer.
///
/// The meaning of a `PointsTo` object is given by the data in its
/// `View` object, [`PointsToData`].
///
/// See the [`PPtr`] documentation for more details.

#[verifier(external_body)]
#[verifier::reject_recursive_types_in_ground_variants(V)]
pub tracked struct PointsToSeq<V> {
    phantom: marker::PhantomData<V>,
    no_copy: NoCopy,
}

/// Represents the meaning of a [`PointsTo`] object.

pub ghost struct PointsToDataSeq<V> {
    /// Indicates that this token is for a pointer `ptr: PPtr<V>`
    /// such that [`ptr.id()`](PPtr::id) equal to this value.

    pub pptr: int,

    /// Indicates that this token gives the ability to read a value `V` from memory.
    /// When `None`, it indicates that the memory is uninitialized.

    pub value: Seq<Option<V>>,
}

impl<V> PointsToSeq<V> {
    pub spec fn view(self) -> PointsToDataSeq<V>;

    /// Any dereferenceable pointer must be non-null.
    /// (Note that null pointers _do_ exist and are representable by `PPtr`;
    /// however, it is not possible to obtain a `PointsTo` token for
    /// any such a pointer.)

    #[verifier(external_body)]
    pub proof fn is_nonnull(tracked &self)
        ensures self@.pptr != 0,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn leak_contents(tracked &mut self)
        ensures self@.pptr == old(self)@.pptr && self@.value == Seq::new(self@.value.len(), |i| Option::<V>::None),
    {
        unimplemented!();
    }
}

impl<V> PPtrSeq<V> {

    /// integer address of the pointer
    pub spec fn id(&self) -> int;
    
    #[inline(always)]
    #[verifier(external_body)]
    pub fn from_usize(u: usize) -> (p: Self) 
        ensures p.id() == u as int,
    {
        let uptr = u as *mut MaybeUninit<V>;
        PPtrSeq{uptr}
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn from_usize_assumed(u: usize, sz: usize) -> (pt: (PPtrSeq<V>, Tracked<PointsToSeq<V>>))
        ensures pt.1@@ === (PointsToDataSeq{ pptr: pt.0.id(), value: Seq::new(sz as nat, |i| Option::None) }),
        opens_invariants none
    {
        let uptr = u as *mut MaybeUninit<V>;
        let p = PPtrSeq{uptr};
        (p, Tracked::assume_new())
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn clone(&self) -> (pt: PPtrSeq<V>)
        ensures pt.id() === self.id(),
        opens_invariants none
    {
        PPtrSeq { uptr: self.uptr }
    }
    
    #[inline(always)]
    #[verifier(external_body)]
    pub fn write_offset(&self, Tracked(perm): Tracked<&mut PointsToSeq<V>>, v: V, index: usize) 
        requires
            self.id() === old(perm)@.pptr,
            index < old(perm)@.value.len(),
        ensures
            perm@.pptr === old(perm)@.pptr,
            perm@.value === old(perm)@.value.update(index as int, Some(v)),
            
    {
        unsafe {
            *(self.uptr.add(index)) = MaybeUninit::new(v);
        }
    }
    
    #[inline(always)]
    #[verifier(external_body)]
    pub fn borrow_offset<'a>(&self, Tracked(perm): Tracked<&mut PointsToSeq<V>>, index: usize) -> (v: &'a V)
        requires
            self.id() === old(perm)@.pptr,
            index < old(perm)@.value.len(),
            old(perm)@.value.index(index as int).is_Some(),
        ensures
            perm@.pptr == old(perm)@.pptr,
            *v === perm@.value.index(index as int).get_Some_0(),
        opens_invariants none
    {
        unsafe {
            (*self.uptr.add(index)).assume_init_ref()
        }
    }

}

}
