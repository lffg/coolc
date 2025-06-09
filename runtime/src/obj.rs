use std::alloc::{alloc, dealloc, Layout};
use std::ffi::c_void;
use std::ptr::NonNull;

// Type IDs
pub const OBJECT_TYPE_ID: u32 = 1;
pub const NO_TYPE_TYPE_ID: u32 = 2;
pub const STRING_TYPE_ID: u32 = 3;
pub const INT_TYPE_ID: u32 = 4;
pub const BOOL_TYPE_ID: u32 = 5;
pub const IO_TYPE_ID: u32 = 6;

#[repr(C)]
pub struct VTable {
    pub size: u32,
    pub type_id: u32,
    // ... functions (in the heap allocation)
}

impl VTable {
    #[cfg(test)]
    pub unsafe fn dummy() -> *mut VTable {
        Box::into_raw(Box::new(VTable {
            size: 8,
            type_id: NO_TYPE_TYPE_ID,
        }))
    }
}

#[repr(C)]
pub struct Object {
    pub size: u32,
    pub type_id: u32,
    pub vtable_ptr: NonNull<VTable>,
    // ... fields (in the heap allocation)
}

impl Object {
    pub fn fields(&self) -> u32 {
        self.size.checked_sub(Self::HEADER_SIZE).unwrap()
    }
}

#[repr(C)]
pub struct String {
    pub base: Object,
    pub len: usize,
    pub bytes: *mut u8,
}

#[repr(C)]
pub struct Int {
    pub base: Object,
    pub value: i64,
}

#[repr(C)]
pub struct Bool {
    pub base: Object,
    pub value: bool,
}

#[repr(C)]
pub struct IO {
    pub base: Object,
}

impl Object {
    /// size + type_id + vtable_ptr.
    pub const HEADER_SIZE: u32 = 16;

    /// Allocates a new object with the given TOTAL size (includes all the
    /// fields), type ID and vtable pointer.
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `size` >= [`Self::HEADER_SIZE`] (16 bytes minimum)
    /// - `size` is a multiple of 8 to maintain pointer alignment for trailing
    ///   fields
    /// - `type_id` accurately represents the intended object type that will be
    ///   stored
    /// - `vtable_ptr` points to a valid, properly initialized VTable that will
    ///   remain valid for the lifetime of this object
    /// - `vtable_ptr` is properly aligned for VTable
    /// - The caller will properly initialize any type-specific fields after
    ///   allocation
    /// - The returned object will be deallocated using [`Object::deallocate`]
    pub unsafe fn allocate(
        size: u32,
        type_id: u32,
        vtable_ptr: NonNull<VTable>,
    ) -> NonNull<Object> {
        assert!(
            size >= Self::HEADER_SIZE,
            "Size must be at least header size"
        );
        assert!(
            size % 8 == 0,
            "Size must be 8-byte aligned for pointer fields"
        );

        let layout = Layout::from_size_align_unchecked(size as usize, 8);
        let ptr = alloc(layout) as *mut Object;

        if ptr.is_null() {
            panic!("Allocation failed");
        }

        // Initialize header
        std::ptr::write(
            ptr,
            Object {
                size,
                type_id,
                vtable_ptr,
            },
        );

        // Zero-initialize the trailing fields
        let fields_size = size - Self::HEADER_SIZE;
        if fields_size > 0 {
            let fields_ptr = (ptr as *mut u8).add(Self::HEADER_SIZE as usize);
            std::ptr::write_bytes(fields_ptr, 0, fields_size as usize);
        }

        NonNull::new_unchecked(ptr)
    }

    /// Deallocates an object.
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `obj` was allocated using [`Object::allocate`]
    /// - `obj` has not been deallocated before
    /// - `obj.size` has not been corrupted since allocation
    /// - No references to this object or its fields exist after this call
    /// - The object is not accessed after deallocation
    pub unsafe fn deallocate(obj: NonNull<Object>) {
        let size = obj.as_ref().size;
        let layout = Layout::from_size_align_unchecked(size as usize, 8);
        dealloc(obj.as_ptr() as *mut u8, layout);
    }

    /// Returns the trailing dynamic part as (field_count, fields_ptr).
    ///
    /// Assumes trailing data consists of pointer-sized fields.
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `self` was properly allocated using [`Object::allocate`]
    /// - `self.size` has not been corrupted since allocation
    /// - The object's memory layout has not been corrupted
    /// - If `field_count > 0`, the trailing memory was intended as pointer
    ///   fields
    /// - The returned pointer is only used while `self` remains valid
    pub unsafe fn get_fields(&self) -> (usize, *mut *mut c_void) {
        let trailing_fields = self.fields();
        let field_size = std::mem::size_of::<*mut c_void>() as u32;
        let field_count = (trailing_fields / field_size) as usize;

        let fields_ptr = if field_count > 0 {
            let base_ptr = (self as *const Object) as *const u8;
            base_ptr.add(Self::HEADER_SIZE as usize) as *mut *mut c_void
        } else {
            std::ptr::null_mut()
        };

        (field_count, fields_ptr)
    }

    /// Returns a specific trailing field by index.
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `self` was properly allocated using [`Object::allocate`]
    /// - `self.size` and memory layout have not been corrupted
    /// - `index < field_count` (as returned by [`Object::get_fields`])
    /// - The trailing memory was allocated and initialized as pointer fields
    /// - The object remains valid for the duration of use
    pub unsafe fn get_field(&self, index: usize) -> *mut c_void {
        let (field_count, fields_ptr) = self.get_fields();
        assert!(index < field_count, "Field index out of bounds");
        *fields_ptr.add(index)
    }

    /// Sets a specific trailing field by index.
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `self` was properly allocated using [`Object::allocate`]
    /// - `self.size` and memory layout have not been corrupted
    /// - `index < field_count` (as returned by [`Object::get_fields`])
    /// - The trailing memory was allocated as pointer fields
    /// - `value` is a valid pointer or null (must not be a dangling pointer)
    /// - If `value` is non-null, it points to valid memory that will remain
    ///   valid
    /// - The object remains valid and won't be deallocated while field is in
    ///   use
    pub unsafe fn set_field(&mut self, index: usize, value: *mut c_void) {
        let (field_count, fields_ptr) = self.get_fields();
        assert!(index < field_count, "Field index out of bounds");
        *fields_ptr.add(index) = value;
    }

    /// Casts to String.
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `self` was originally allocated as a [`String`] object
    /// - The memory actually contains a valid [`String`] layout
    /// - `self.type_id` accurately reflects that this is a String object
    /// - The object remains valid for the lifetime of use
    pub unsafe fn as_string(&self) -> *mut String {
        self as *const Object as *mut String
    }

    /// Casts to Int.
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `self` was originally allocated as an [`Int`] object
    /// - The memory actually contains a valid [`Int`] layout
    /// - `self.type_id` accurately reflects that this is an Int object
    /// - The object remains valid for the lifetime of use
    pub unsafe fn as_int(&self) -> *mut Int {
        self as *const Object as *mut Int
    }

    /// Casts to Bool
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `self` was originally allocated as a [`Bool`] object
    /// - The memory actually contains a valid [`Bool`] layout
    /// - `self.type_id` accurately reflects that this is a Bool object
    /// - The object remains valid for the lifetime of use
    pub unsafe fn as_bool(&self) -> *mut Bool {
        self as *const Object as *mut Bool
    }

    /// Casts to IO.
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `self` was originally allocated as an [`IO`] object
    /// - The memory actually contains a valid [`IO`] layout
    /// - `self.type_id` accurately reflects that this is an IO object
    /// - The object remains valid for the lifetime of use
    pub unsafe fn as_io(&self) -> *mut IO {
        self as *const Object as *mut IO
    }
}

impl String {
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `vtable_ptr` points to a valid `VTable` for strings that will remain
    ///   valid
    /// - `bytes` is either null or points to at least `len` bytes of valid,
    ///   initialized memory
    /// - If `bytes` is non-null, the memory will remain valid for the object's
    ///   lifetime
    /// - `len` accurately represents the number of valid bytes at `bytes`
    /// - The caller will properly manage the lifetime of both the object and
    ///   the `bytes` memory
    pub unsafe fn new(vtable_ptr: NonNull<VTable>, len: usize, bytes: *mut u8) -> NonNull<String> {
        let size = std::mem::size_of::<String>() as u32;
        let obj = Object::allocate(size, STRING_TYPE_ID, vtable_ptr);

        let string_ptr = obj.as_ptr() as *mut String;
        (*string_ptr).len = len;
        (*string_ptr).bytes = bytes;

        NonNull::new_unchecked(string_ptr)
    }
}

impl Int {
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `vtable_ptr` points to a valid `VTable` for integers that will remain
    ///   valid
    /// - The caller will properly manage the lifetime of the returned object
    pub unsafe fn new(vtable_ptr: NonNull<VTable>, value: i64) -> NonNull<Int> {
        let size = std::mem::size_of::<Int>() as u32;
        let obj = Object::allocate(size, INT_TYPE_ID, vtable_ptr);

        let int_ptr = obj.as_ptr() as *mut Int;
        (*int_ptr).value = value;

        NonNull::new_unchecked(int_ptr)
    }
}

impl Bool {
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `vtable_ptr` points to a valid `VTable` for booleans that will remain
    ///   valid
    /// - The caller will properly manage the lifetime of the returned object
    pub unsafe fn new(vtable_ptr: NonNull<VTable>, value: bool) -> NonNull<Bool> {
        let size = std::mem::size_of::<Bool>() as u32;
        let obj = Object::allocate(size, BOOL_TYPE_ID, vtable_ptr);

        let bool_ptr = obj.as_ptr() as *mut Bool;
        (*bool_ptr).value = value;

        NonNull::new_unchecked(bool_ptr)
    }
}

impl IO {
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `vtable_ptr` points to a valid `VTable` for IO that will remain valid
    /// - The caller will properly manage the lifetime of the returned object
    pub unsafe fn new(vtable_ptr: NonNull<VTable>) -> NonNull<IO> {
        let size = std::mem::size_of::<IO>() as u32;
        let obj = Object::allocate(size, IO_TYPE_ID, vtable_ptr);

        NonNull::new_unchecked(obj.as_ptr() as *mut IO)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::{align_of, size_of};

    #[test]
    fn test_object_sizes() {
        assert_eq!(std::mem::size_of::<Object>(), 16);
        assert_eq!(Object::HEADER_SIZE, 16);

        assert_eq!(size_of::<String>(), 32);
        assert_eq!(size_of::<Int>(), 24);
        assert_eq!(size_of::<Bool>(), 24);
    }

    #[test]
    fn test_type_alignments() {
        const _: () = {
            assert!(align_of::<Object>() == 8);

            assert!(align_of::<String>() <= 8);
            assert!(align_of::<Int>() <= 8);
            assert!(align_of::<Bool>() <= 8);
        };

        assert!(align_of::<Object>() == 8);
        assert!(align_of::<String>() <= 8);
        assert!(align_of::<Int>() <= 8);
        assert!(align_of::<Bool>() <= 8);
    }

    #[test]
    fn test_trailing_fields() {
        unsafe {
            let dummy_vtable = VTable::dummy();
            let vtable_ptr = NonNull::new_unchecked(dummy_vtable);

            // Create object with 2 trailing pointer fields (16 + 16 = 32 bytes)
            let obj = Object::allocate(32, OBJECT_TYPE_ID, vtable_ptr);
            let obj_ref = obj.as_ref();

            let (field_count, _) = obj_ref.get_fields();
            assert_eq!(field_count, 2);

            Object::deallocate(obj);
            drop(Box::from_raw(dummy_vtable));
        }
    }

    #[test]
    fn test_type_casting() {
        unsafe {
            let dummy_vtable = VTable::dummy();
            let vtable_ptr = NonNull::new_unchecked(dummy_vtable);

            // Create an Int
            let int_obj = Int::new(vtable_ptr, 42);
            let obj_ref = &int_obj.as_ref().base;

            // Test casting - now returns raw pointers
            let int_ptr = obj_ref.as_int();
            assert_eq!((*int_ptr).value, 42);

            Object::deallocate(int_obj.cast());
            drop(Box::from_raw(dummy_vtable));
        }
    }
}
