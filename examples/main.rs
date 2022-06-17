//! No std + No alloc, create a `Box`, format and print it's contents.

#![no_std]
#![no_main]

use core::fmt::Write;

#[link(name = "c")]
extern "C" {
    fn puts(s: *const ()) -> i32;
}

#[panic_handler]
fn panic(_panic: &::core::panic::PanicInfo<'_>) -> ! {
    loop {}
}

static BOX_STORE: faux_alloc::BoxStore<u32> = faux_alloc::BoxStore::new();

struct CStringFormatter<const SIZE: usize>([u8; SIZE]);

impl<const SIZE: usize> CStringFormatter<SIZE> {
    fn new() -> Self {
        Self([b'\0'; SIZE])
    }
}

impl<const SIZE: usize> Write for CStringFormatter<SIZE> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for (src, dst) in s.bytes().zip(self.0.iter_mut()).take(SIZE - 1) {
            *dst = src;
        }
        Ok(())
    }
}

#[no_mangle]
pub extern "C" fn main() {
    let boxed = BOX_STORE.alloc(12).unwrap();
    let mut string = CStringFormatter::<3>::new();
    string.write_fmt(format_args!("{}", *boxed)).unwrap();
    unsafe { puts(string.0.as_ptr().cast()) };
}
