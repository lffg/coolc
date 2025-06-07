#![no_std]
#![no_main]

trait Foo {
    fn add(&self, a: i32, b: i32) -> i32;
}

struct PlusFactor(i32);

impl Foo for PlusFactor {
    fn add(&self, a: i32, b: i32) -> i32 {
        self.0 + a + b
    }
}

#[unsafe(no_mangle)]
fn foo(f: &dyn Foo) -> i32 {
    f.add(2, 3)
}

unsafe extern "C" {
    fn printf(...) -> i32;
}

#[unsafe(no_mangle)]
pub extern "C" fn main() -> i32 {
    let x = PlusFactor(13);
    let y: i32 = foo(&x);

    let f = c"Got [%d]\n".as_ptr();
    unsafe {
        printf(f, y);
    }
    return 0;
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}
