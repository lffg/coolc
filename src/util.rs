pub trait BreakableIteratorExt<I>: Iterator
where
    I: Iterator,
{
    fn up_to<P>(self, stop_predicate: P) -> Break<I, P>
    where
        P: FnMut(&I::Item) -> bool;
}

impl<I> BreakableIteratorExt<I> for I
where
    I: Iterator,
{
    fn up_to<P>(self, stop_predicate: P) -> Break<I, P>
    where
        P: FnMut(&I::Item) -> bool,
    {
        Break {
            iter: self,
            stop_predicate,
            finished: false,
        }
    }
}

pub struct Break<I, P> {
    iter: I,
    stop_predicate: P,
    finished: bool,
}

impl<I, P> Iterator for Break<I, P>
where
    I: Iterator,
    P: FnMut(&I::Item) -> bool,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        let next = self.iter.next()?;
        self.finished = (self.stop_predicate)(&next);
        Some(next)
    }
}

#[cfg(test)]
mod tests {
    use crate::util::BreakableIteratorExt;

    #[test]
    fn test_up_to() {
        let items: Vec<_> = (0..10).up_to(|x| *x == 5).collect();
        assert_eq!(items, [0, 1, 2, 3, 4, 5]);
    }
}
