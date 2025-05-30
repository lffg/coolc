use std::{collections::HashMap, fmt, hash::Hash, marker::PhantomData, num::NonZeroU32, rc::Rc};

/// A handle to some interned value of type `T`. To retrieve a `&T`, use
/// [`Interner::get`].
pub struct Interned<T: ?Sized> {
    // Here we use a NonZeroU32 to leverage niche layout optimization.
    handle: NonZeroU32,
    _ty: PhantomData<T>,
}

impl<T: ?Sized> Interned<T> {
    pub(crate) const fn unchecked_new(handle: NonZeroU32) -> Self {
        Interned {
            handle,
            _ty: PhantomData,
        }
    }
}

impl<T: ?Sized> Copy for Interned<T> {}

impl<T: ?Sized> Clone for Interned<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Hash for Interned<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.handle.hash(state);
    }
}

impl<T: ?Sized> PartialEq for Interned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.handle == other.handle
    }
}

impl<T: ?Sized> Eq for Interned<T> {}

impl<T: ?Sized> PartialOrd for Interned<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: ?Sized> Ord for Interned<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.handle.cmp(&other.handle)
    }
}

impl<T: ?Sized> fmt::Debug for Interned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Interned({})", self.handle)
    }
}

impl<T: ?Sized> From<&Interned<T>> for Interned<T> {
    fn from(value: &Interned<T>) -> Self {
        *value
    }
}

pub struct Interner<T: ?Sized> {
    map: HashMap<Rc<T>, NonZeroU32>,
    vec: Vec<Rc<T>>,
}

impl fmt::Debug for Interner<str> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();
        for (i, interned) in self.vec.iter().enumerate() {
            let i = i + 1;
            map.entry(&i, &interned);
        }
        map.finish()
    }
}

impl<T: ?Sized> Interner<T> {
    pub fn with_capacity(capacity: usize) -> Self {
        Interner {
            map: HashMap::with_capacity(capacity),
            vec: Vec::with_capacity(capacity),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty() && self.vec.is_empty()
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
            return Interned::unchecked_new(*handle);
        }
        let key: Rc<T> = value.to_owned().into();
        let i = {
            let len = u32::try_from(self.vec.len()).expect("interned out of capacity");
            // SAFETY: This will never be zero due to the +1.
            unsafe { NonZeroU32::new_unchecked(len + 1) }
        };
        self.vec.push(Rc::clone(&key));
        self.map.insert(key, i);
        Interned::unchecked_new(i)
    }

    /// Returns the corresponding value for the provided [`Interned`] handle.
    /// Panics if not found.
    pub fn get(&self, handle: impl Into<Interned<T>>) -> &T {
        let handle: Interned<T> = handle.into();
        let handle = handle.handle.get() - 1;
        &self.vec[handle as usize]
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
