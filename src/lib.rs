//! Simplified allocations for no-std on stable Rust.
//!
//! All allocations require a `*Store` which gives them a `'static` lifetime.
//!
//! You can swap out alloc for faux_alloc and as long as the APIs are supported
//! it will work.

#![no_std]

use core::mem::ManuallyDrop;
use core::task::{RawWaker, RawWakerVTable, Waker};
use core::{
    borrow::{Borrow, BorrowMut},
    cell::UnsafeCell,
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    pin::Pin,
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
};

/// A pointer type for heap allocation.
pub struct Box<T>(*mut T);

impl<T> Box<T> {
    /// Construct `Box` from pointer
    #[inline]
    pub const unsafe fn from_raw(raw: *mut T) -> Self {
        Box(raw)
    }

    /// Convert box to a pointer
    #[inline]
    pub const fn into_raw(b: Self) -> *mut T {
        b.0
    }

    /// Leak the `Box`
    #[inline]
    pub fn leak<'a>(b: Self) -> &'a mut T {
        unsafe { &mut *b.0 }
    }

    /// Convert the `Box` into a pinned `Box`
    #[inline]
    pub fn into_pin(boxed: Self) -> Pin<Self> {
        unsafe { Pin::new_unchecked(boxed) }
    }
}

impl<T> Borrow<T> for Box<T> {
    #[inline]
    fn borrow(&self) -> &T {
        &*self
    }
}

impl<T> BorrowMut<T> for Box<T> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut T {
        &mut *self
    }
}

impl<T> AsRef<T> for Box<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &*self
    }
}

impl<T> AsMut<T> for Box<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut T {
        &mut *self
    }
}

impl<T> Deref for Box<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        unsafe { &*self.0 }
    }
}

impl<T> DerefMut for Box<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.0 }
    }
}

/// A place to store a fake "heap" that can allocate for one `Box`.
pub struct BoxStore<T>(UnsafeCell<MaybeUninit<T>>, AtomicBool);

unsafe impl<T> Sync for BoxStore<T> {}

impl<T> BoxStore<T> {
    /// Create a new `ArcStore`
    #[inline]
    pub const fn new() -> Self {
        Self(
            UnsafeCell::new(MaybeUninit::uninit()),
            AtomicBool::new(false),
        )
    }

    /// Allocate memory.
    #[inline]
    pub fn alloc(&'static self, value: T) -> Option<Box<T>> {
        if self.1.fetch_or(true, Ordering::SeqCst) {
            None
        } else {
            unsafe {
                let maybe_uninit = &mut *self.0.get();
                let pointer = maybe_uninit.write(value);
                Some(Box::from_raw(pointer))
            }
        }
    }

    /// De-allocate memory and drop.
    ///
    /// After this is called, the memory may be allocated again.
    ///
    /// May error if:
    ///  - Not the same `Box` that was allocated on this store.
    #[inline]
    pub fn dealloc(&'static self, ptr: Box<T>) -> Result<(), ()> {
        unsafe {
            let ptr = Box::into_raw(ptr);
            if (*self.0.get()).as_mut_ptr() == ptr {
                core::ptr::drop_in_place(ptr);
                self.1.store(false, Ordering::SeqCst);
                Ok(())
            } else {
                Err(())
            }
        }
    }
}

/// A place to store a fake "heap" that can allocate for one `Arc`.
pub struct ArcStore<T>(UnsafeCell<MaybeUninit<ArcInner<T>>>, AtomicBool);

unsafe impl<T> Sync for ArcStore<T> {}

impl<T> ArcStore<T> {
    /// Create a new `ArcStore`
    #[inline]
    pub fn new() -> Self {
        Self(
            UnsafeCell::new(MaybeUninit::uninit()),
            AtomicBool::new(false),
        )
    }

    /// Allocate memory.
    #[inline]
    pub fn alloc(&'static self, value: T) -> Option<Arc<T>> {
        if self.1.fetch_or(true, Ordering::SeqCst) {
            None
        } else {
            unsafe {
                let maybe_uninit = &mut *self.0.get();
                let pointer = maybe_uninit.write(ArcInner {
                    count: AtomicUsize::new(1),
                    data: UnsafeCell::new(value),
                });
                Some(Arc(pointer))
            }
        }
    }

    /// De-allocate memory and drop.
    ///
    /// After this is called, the memory may be allocated again.
    ///
    /// May error if:
    ///  - Not the same `Arc` that was allocated on this store.
    ///  - Reference count is not 1
    #[inline]
    pub fn dealloc(&'static self, ptr: Arc<T>) -> Result<(), ()> {
        unsafe {
            let count = Arc::count(&ptr);
            let ptr = Arc::into_raw(ptr);
            let ptr: *const ArcInner<T> = ptr.cast();
            if count == 1 && ptr == (*self.0.get()).as_ptr() {
                core::ptr::drop_in_place((*ptr).data.get());
                self.1.store(false, Ordering::SeqCst);
                Ok(())
            } else {
                Arc::<T>::decrement_count(ptr.cast());
                Err(())
            }
        }
    }
}

struct ArcInner<T: ?Sized> {
    count: AtomicUsize,
    data: UnsafeCell<T>,
}

/// Atomically reference-counted pointer
pub struct Arc<T>(*const ArcInner<T>);

impl<T> Arc<T> {
    /// Get the number of `Arc`s
    #[inline]
    #[must_use]
    pub fn count(this: &Self) -> usize {
        unsafe { (*this.0).count.load(Ordering::SeqCst) }
    }

    /// Check if two arcs point to the same location
    #[inline]
    #[must_use]
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.0 == other.0
    }

    /// Fake a `Clone` on a raw arc
    #[inline]
    pub unsafe fn increment_count(ptr: *const ()) {
        // Retain Arc, but don't touch refcount by wrapping in ManuallyDrop
        let arc = ManuallyDrop::new(Arc::<T>::from_raw(ptr));
        // Now increase refcount, but don't drop new refcount either
        let _arc_clone: ManuallyDrop<_> = arc.clone();
    }

    /// Fake a `Drop` on raw arc
    #[inline]
    pub unsafe fn decrement_count(ptr: *const ()) {
        core::mem::drop(Arc::<T>::from_raw(ptr));
    }

    /// Create arc from raw arc
    #[inline]
    pub unsafe fn from_raw(ptr: *const ()) -> Self {
        Self(ptr.cast())
    }

    /// Create raw arc from arc
    #[inline]
    pub fn into_raw(this: Self) -> *const () {
        let ptr = this.0;
        core::mem::forget(this);
        ptr.cast()
    }

    /// Leak the `Arc`
    #[inline]
    pub fn leak<'a>(this: Self) -> &'a T {
        unsafe { &*(*this.0).data.get() }
    }
}

impl<T> Borrow<T> for Arc<T> {
    #[inline]
    fn borrow(&self) -> &T {
        &*self
    }
}

impl<T> AsRef<T> for Arc<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &*self
    }
}

impl<T> Deref for Arc<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        unsafe { &*(*self.0).data.get() }
    }
}

impl<T> Clone for Arc<T> {
    #[inline]
    fn clone(&self) -> Arc<T> {
        const MAX: usize = (isize::MAX) as usize;

        if unsafe { (*self.0).count.fetch_add(1, Ordering::Relaxed) } > MAX {
            panic!();
        }

        Self(self.0)
    }
}

impl<T> Drop for Arc<T> {
    #[inline]
    fn drop(&mut self) {
        unsafe { (*self.0).count.fetch_sub(1, Ordering::Release) };
    }
}

/// Trait for safely implementing a [`Waker`]
pub trait Wake: Sized {
    /// Wake this task.
    fn wake(this: Arc<Self>);

    /// Wake this task without consuming the waker.
    fn wake_by_ref(this: &Arc<Self>) {
        Self::wake(this.clone());
    }
}

impl<W: Wake + Send + Sync + 'static> From<Arc<W>> for Waker {
    /// Create waker from `Arc<Wake>`
    fn from(waker: Arc<W>) -> Waker {
        unsafe { Waker::from_raw(raw_waker(waker)) }
    }
}

impl<W: Wake + Send + Sync + 'static> From<Arc<W>> for RawWaker {
    fn from(waker: Arc<W>) -> RawWaker {
        raw_waker(waker)
    }
}

#[inline(always)]
fn raw_waker<W: Wake + Send + Sync + 'static>(waker: Arc<W>) -> RawWaker {
    // Increment the reference count of the arc to clone it.
    unsafe fn clone_waker<W: Wake + Send + Sync + 'static>(waker: *const ()) -> RawWaker {
        Arc::<W>::increment_count(waker);
        RawWaker::new(
            waker as *const (),
            &RawWakerVTable::new(
                clone_waker::<W>,
                wake::<W>,
                wake_by_ref::<W>,
                drop_waker::<W>,
            ),
        )
    }

    // Wake by value, moving the Arc into the Wake::wake function
    unsafe fn wake<W: Wake + Send + Sync + 'static>(waker: *const ()) {
        let waker = Arc::<W>::from_raw(waker);
        <W as Wake>::wake(waker);
    }

    // Wake by reference, wrap the waker in ManuallyDrop to avoid dropping it
    unsafe fn wake_by_ref<W: Wake + Send + Sync + 'static>(waker: *const ()) {
        let waker = ManuallyDrop::new(Arc::from_raw(waker));
        <W as Wake>::wake_by_ref(&waker);
    }

    // Decrement the reference count of the Arc on drop
    unsafe fn drop_waker<W: Wake + Send + Sync + 'static>(waker: *const ()) {
        Arc::<W>::decrement_count(waker);
    }

    RawWaker::new(
        Arc::into_raw(waker) as *const (),
        &RawWakerVTable::new(
            clone_waker::<W>,
            wake::<W>,
            wake_by_ref::<W>,
            drop_waker::<W>,
        ),
    )
}

pub mod boxed {
    //! Emulating <https://doc.rust-lang.org/alloc/boxed/index.html>

    pub use crate::Box;
}

pub mod sync {
    //! Emulating <https://doc.rust-lang.org/alloc/sync/index.html>

    pub use crate::Arc;
}

pub mod task {
    //! Emulating <https://doc.rust-lang.org/alloc/task/index.html>

    pub use crate::Wake;
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
