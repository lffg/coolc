use std::{collections::HashMap, fmt, hash::Hash, marker::PhantomData, rc::Rc};

/// A handle to some interned value of type `T`. To retrieve a `&T`, use
/// [`Interner::get`].
pub struct Interned<T: ?Sized> {
    handle: u32,
    _ty: PhantomData<T>,
}

impl<T: ?Sized> Copy for Interned<T> {}

impl<T: ?Sized> Clone for Interned<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> PartialEq for Interned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.handle == other.handle
    }
}

impl<T: ?Sized> Eq for Interned<T> {}

impl<T: ?Sized> fmt::Debug for Interned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Interned({})", self.handle)
    }
}

impl<T: ?Sized> Interned<T> {
    const fn new(handle: u32) -> Self {
        Interned {
            handle,
            _ty: PhantomData,
        }
    }
}

pub struct Interner<T: ?Sized> {
    map: HashMap<Rc<T>, u32>,
    vec: Vec<Rc<T>>,
}

impl<T: ?Sized> Interner<T> {
    pub fn with_capacity(capacity: usize) -> Self {
        Interner {
            map: HashMap::with_capacity(capacity),
            vec: Vec::with_capacity(capacity),
        }
    }

    pub fn clear(&mut self) {
        self.map.clear();
        self.vec.clear();
    }

    /// Interns the provided value, returning a handle which can be used to
    /// retrieve it later.
    pub fn intern(&mut self, value: &T) -> Interned<T>
    where
        T: Eq + Hash,
        T: ToOwned,
        T::Owned: Into<Rc<T>>,
    {
        if let Some(handle) = self.map.get(value) {
            return Interned::new(*handle);
        }
        let key: Rc<T> = value.to_owned().into();
        let i: u32 = self.vec.len().try_into().expect("interned out of capacity");
        self.vec.push(Rc::clone(&key));
        self.map.insert(key, i);
        Interned::new(i)
    }

    /// Returns the corresponding value for the provided [`Interned`] handle.
    /// Panics if not found.
    pub fn get(&self, handle: impl Into<Interned<T>>) -> &T {
        let handle = handle.into().handle as usize;
        &self.vec[handle]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interner() {
        let mut i = Interner::<str>::with_capacity(3);

        let hello1 = i.intern("hello");
        let world1 = i.intern("world");
        let bang1 = i.intern("!");

        let hello2 = i.intern("hello");
        let world2 = i.intern("world");
        let bang2 = i.intern("!");

        assert_eq!(i.get(hello1), i.get(hello2));
        assert_eq!(i.get(world1), i.get(world2));
        assert_eq!(i.get(bang1), i.get(bang2));

        assert_eq!(hello1.handle, hello2.handle);
        assert_eq!(world1.handle, world2.handle);
        assert_eq!(bang1.handle, bang2.handle);
    }
}
