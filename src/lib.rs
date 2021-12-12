#![warn(missing_docs)]
//!Ring buffer that uses a boxed array as backing storage. This guarantees that the buffers size is
//!always exactly at the compile-time constant value. There is no way to get fewer or more entries.
//!In addition, by having the array boxed, conversion from [`Vec`][std::vec::Vec] and to 
//![`VecDeque`][std::collections::VecDeque] are nearly free.
//!
//!This crate does not use any unsafe code (however the IntoIterator implementation does so
//!indirectly, as it internally uses a [`VecDeque`][std::collections::VecDeque]).
//!
//!Since the ring buffer has always a guaranteed number of elements, it must be initialized, either
//!from an iterator, a boxed slice (most collections can convert into a boxed slice at very low
//!cost), a [`Vec`], or at a value that implements [`Copy`][std::marker::Copy].
//!
//!# Examples
//!
//!A new ring buffer can only be created from a [`Vec`] or a [boxed][std::boxed::Box] [`slice`]
//!of the correct size (using [`TryFrom`][std::convert::TryFrom]/[`TryInto`][std::convert::TryInto]),
//!by taking the correct size from an iterator (using [`new()`][RingBuffer::new]),
//!or by initializing all entries in the ring buffer to the same [`Copy`][core::marker::Copy]able
//!value (using [`new_copy()`][RingBuffer::new_copy]).
//!```
//! # use boxed_array_ringbuffer::RingBuffer;
//!let buf : RingBuffer<_, 4> = vec![42,37,23,12].try_into().expect("Works, size matches.");
//!let wrong_size : Result<RingBuffer<_,3>, Vec<u8>> = vec![42,37,23,12].try_into();
//!assert!(wrong_size.is_err());
//!
//!let buf2 : RingBuffer<_,3> = RingBuffer::new(vec![42,37,23,12].into_iter())
//!    .expect("works, because iterator has enough elements - use by_ref() on iterator if \
//!    you need the remaining elements still.");
//!let not_enough : Result<RingBuffer<_,5>,_> = RingBuffer::new(vec![42,37,23,12].into_iter());
//!assert_eq!(not_enough.unwrap_err()[2],23);
//!
//!let buf3 : RingBuffer<_,3> = RingBuffer::new_copy(42);
//!assert_eq!(buf3[2],42);
//!```
//!
//!As you have seen above, accessing upcoming elements can be done with the [`Index`] or
//![`IndexMut`] syntax. Howver, if you are not absolutely certain that your index is within the
//!size of the ring buffer, you can also use the [`get()`][RingBuffer::get] or
//![`get_mut()`][RingBuffer::get_mut] methods. The indices are always relevant to the current
//!position within the RingBuffer.
//!```
//! # use boxed_array_ringbuffer::RingBuffer;
//!let buf : RingBuffer<_, 4> = vec![42,37,23,12].try_into().expect("Works, size matches.");
//!assert_eq!(buf[3], 12);
//!assert_eq!(buf.get(2), Some(&23));
//!let mut buf = buf;
//!assert_eq!(buf.get_mut(4), None);
//!let (buf, forty_two) = buf.push_pop(6);
//!assert_eq!(buf[3],6);
//!```
//!
//!In order to add a new element to the buffer and remove the oldest element from the buffer (after
//!all, the size of the RingBuffer has to be constant), you can use the
//![`push_pop()`][RingBuffer::push_pop()] method:
//!```
//! # use boxed_array_ringbuffer::RingBuffer;
//!let buf : RingBuffer<_, 4> = vec![42,37,23,12].try_into().expect("Works, size matches.");
//!let (buf, forty_two) = buf.push_pop(6);
//!assert_eq!(forty_two, 42);
//!assert_eq!(buf[0],37);
//!assert_eq!(buf[3],6);
//!```
//!
//!To iterate over the upcoming elements, you can either use the [`iter()`][RingBuffer::iter] or
//!the [`into_iter()][RingBuffer::into_iter] methods, the latter if you want the iterator to take
//!ownership of the data of the ring buffer.
//!```
//! # use boxed_array_ringbuffer::RingBuffer;
//!let buf : RingBuffer<_, 4> = vec![42,37,23,12].try_into().expect("Works, size matches.");
//!assert!(buf.iter().eq(vec![42,37,23,12].iter()));
//!assert!(buf.into_iter().eq(vec![42,37,23,12].into_iter()));
//!```
//!
//!And last, but not least, once you are done utilizing the ring buffer's guarantee that the amount
//!of items is constant, you can always convert it to a [`VecDeque`][`std::collections::VecDeque`]
//!without needing a reallocation.
//!```
//! # use boxed_array_ringbuffer::RingBuffer;
//!let buf : RingBuffer<_, 4> = vec![42,37,23,12].try_into().expect("Works, size matches.");
//!let (buf, _forty_two) = buf.push_pop(6);
//!let deque : std::collections::VecDeque<_> = buf.into();
//!assert!(deque.into_iter().eq(vec![37,23,12,6].into_iter()));

use std::ops::{Index, IndexMut};
use std::iter::Iterator;
///Ring buffer using a boxed array as backing storage. This has the adantage that conversions 
///from [`Vec`][std::vec::Vec] or to [`VecDeque`][std::collections::VecDeque] are nearly free.
///Main use case of this is as a replacement for `std::collection::VecDeque` in cases where the
///size is fixed at compile time and one really wants to make invalid states impossible.
///
///Due to this, the only way to put a new item into the buffer is to take an old item out.
///There is intentionally no way to temporary ownership of items. If you need such an API, you can
///use the [`get_mut()`][crate::RingBuffer::get_mut] method or the index operator to obtain a
///mutable reference, and then use either methods from [`std::mem`] to temporarily place another
///value there, or use internally unsafe solutions like the [`replace_with`](https://docs.rs/replace_with)
///crate.
///
///# Examples
///Whenever you [`push_pop()`][RingBuffer::push_pop], the buffer moves to the next element. You can get a reference to
///contained data using the index operator, or if you want a panic-free way, using the
///[`get()`][RingBuffer::get()] or [`get_mut()`][RingBuffer::get_mut()] methods.
///```
/// # use boxed_array_ringbuffer::RingBuffer;
///let input = [42,37,23,12];
///let buf : RingBuffer<&usize, 4> = RingBuffer::new(input.iter()).expect("Works, enough input.");
///assert_eq!(buf[0], &42);
///assert_eq!(buf[1], &37);
///assert_eq!(buf[2], &23);
///assert_eq!(buf[3], &12);
///assert_eq!(buf.get(3), Some(&&12));
///assert_eq!(buf.get(4), None);
///let (buf, forty_two) = buf.push_pop(&1);
///assert_eq!(forty_two, &42);
///assert_eq!(buf[0], &37);
///assert_eq!(buf[1], &23);
///assert_eq!(buf[2], &12);
///assert_eq!(buf[3], &1);
///let (buf, thirty_seven) = buf.push_pop(&2);
///assert_eq!(thirty_seven, &37);
///let (buf, twenty_three) = buf.push_pop(&3);
///assert_eq!(twenty_three, &23);
///let (buf, twelve) = buf.push_pop(&4);
///assert_eq!(twelve, &12);
///let (buf, one) = buf.push_pop(&5);
///assert_eq!(one, &1);
///assert_eq!(buf[0], &2);
///assert_eq!(buf[1], &3);
///assert_eq!(buf[2], &4);
///assert_eq!(buf[3], &5);
///```
#[derive(Debug, Clone)]
pub struct RingBuffer<T, const SIZE : usize>
{
    //storage is an array, because arrays _guarantee_ an initialized fixed size.
    //It's inside a box, because that way we can collect() into it without copying from heap to
    //stack.
    storage : Box<[T;SIZE]>,
    index : usize,
}

impl<T, const SIZE : usize> RingBuffer<T, SIZE> 
{
    ///Puts `new_entry` into the ring buffer at its current location, and returns the value that
    ///was there before. Then moves the ring buffer to the next location.
    ///
    ///# Examples
    ///```
    /// # use boxed_array_ringbuffer::RingBuffer;
    ///let input = [42,37,23,12];
    ///let buf : RingBuffer<&usize, 4> = RingBuffer::new(input.iter()).expect("Works, enough input.");
    ///assert_eq!(buf[0], &42);
    ///assert_eq!(buf[3], &12);
    ///let (buf, forty_two) = buf.push_pop(&1);
    ///assert_eq!(forty_two, &42);
    ///assert_eq!(buf[0], &37);
    ///assert_eq!(buf[3], &1);
    ///```
    pub fn push_pop(mut self,new_entry : T) -> (Self, T) {
        let old_value = std::mem::replace(&mut self.storage[self.index], new_entry);
        self.index = (self.index + 1) % SIZE;
        (self, old_value)
    }

    ///Creates a new RingBuffer from an [`Iterator`]. If the iterator does not supply enough
    ///elements, the elements that have already been taken from the iterator are instead returned
    ///in the [`Err`] variant as a boxed slice.
    ///
    ///# Warning
    ///Beware that it is *not* considered an error if the iterator would yield more elements. If you
    ///need the remaining data in the iterator, make sure to pass it
    ///[`by_ref()`][Iterator::by_ref].
    ///
    ///# Examples
    ///If the iterator has at least the required number of elements, a ring buffer is created.
    ///```
    /// # use boxed_array_ringbuffer::RingBuffer;
    ///let input = [42,37,23,12,8];
    ///let mut iter = input.iter();
    ///let buf : RingBuffer<&usize, 4> = RingBuffer::new(iter.by_ref()).expect("Works, enough input.");
    ///assert_eq!(iter.next(), Some(&8));
    ///assert_eq!(buf[0], &42);
    ///assert_eq!(buf[1], &37);
    ///assert_eq!(buf[2], &23);
    ///assert_eq!(buf[3], &12);
    ///assert_eq!(buf.get(4),None);
    ///```
    ///
    ///If the iterator does not yield enough elements, an error is returned, containing all
    ///elements taken from the iterator.
    ///```
    /// # use boxed_array_ringbuffer::RingBuffer;
    ///let input = ["lizard", "fish", "bird"];
    ///let buf : Result<RingBuffer<&str, 4>, _> = RingBuffer::new(input.iter().map(|x| *x));
    ///assert!(buf.is_err());
    ///assert_eq!(buf.unwrap_err()[1], "fish");
    ///```
    pub fn new<I>(input : I) -> Result<Self, Box<[T]>>
        where I : Iterator<Item=T>
    {
        let slice = input.take(SIZE).collect::<Box<[T]>>();
        let array = slice.try_into()?;
        Ok(RingBuffer { storage : array, index : 0 })
    }

    ///Initializes the ring buffer with copies of the same value.
    ///
    ///# Examples
    ///```
    /// # use boxed_array_ringbuffer::RingBuffer;
    ///let buf :RingBuffer<usize,4> = RingBuffer::new_copy(3);
    ///assert_eq!(buf[0], 3);
    ///assert_eq!(buf[1], 3);
    ///assert_eq!(buf[2], 3);
    ///assert_eq!(buf[3], 3);
    ///assert_eq!(buf.get(4), None);
    ///```
    pub fn new_copy(init : T) -> Self 
        where T : Copy 
    {
        RingBuffer { storage : Box::new([init;SIZE]), index : 0 }
    }

    ///Gets an immutable reference to the entry that's `index` elements in the future of the
    ///buffer. In other words `get(0)` returns an immutable reference to the next element that
    ///would be returned by [`push_pop()`][RingBuffer::push_pop], `get(1)` to the second-next and
    ///so on. Return value is wrapped in an option due to range checking. You can use the index
    ///operator `[]` instead if you are sure your index is valid.
    ///
    ///# Examples
    ///```
    /// # use boxed_array_ringbuffer::RingBuffer;
    ///let input = [42,37,23,12];
    ///let buf : RingBuffer<&usize, 4> = RingBuffer::new(input.iter()).expect("Works, enough input.");
    ///let (buf, _) = buf.push_pop(&7);
    ///assert_eq!(buf.get(0), Some(&&37));
    ///assert_eq!(buf.get(3), Some(&&7));
    ///assert_eq!(buf.get(4), None);
    ///```
    pub fn get(&self, index : usize) -> Option<&T> {
        if index >= SIZE {
            None
        }
        else {
            Some(&self.storage[self.get_arr_index_wrapped(index)])
        }
    }

    ///Similar to [`get()`][RingBuffer::get], but yields a mutable reference instead.
    ///
    ///# Examples
    ///```
    /// # use boxed_array_ringbuffer::RingBuffer;
    ///let input = [42,37,23,12];
    ///let mut buf : RingBuffer<&usize, 4> = RingBuffer::new(input.iter()).expect("Works, enough input.");
    ///match buf.get_mut(0) {
    ///    Some(x) => { 
    ///        assert_eq!(**x, 42);
    ///        *x = &1;
    ///    }
    ///    _ => {
    ///        unreachable!();
    ///    }
    ///}
    ///assert_eq!(buf.get(0), Some(&&1));
    ///```
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index >= SIZE {
            None
        }
        else {
            Some(&mut self.storage[self.get_arr_index_wrapped(index)])
        }
    }

    ///Returns an [`Iterator`] over references to the contained elements.
    ///
    ///# Examples
    ///```
    /// # use boxed_array_ringbuffer::RingBuffer;
    ///let input = [42,37,23,12];
    ///let buf : RingBuffer<&usize, 4> = RingBuffer::new(input.iter()).expect("Works, enough input");
    ///let (buf, forty_two) = buf.push_pop(&1);
    ///assert_eq!(forty_two, &42);
    ///assert!(buf.iter().map(|x| *x).eq([37,23,12,1].iter()));
    ///```
    pub fn iter(&self) -> RingBufferIterator<T,SIZE> {
        RingBufferIterator { ring_buffer : self, index : 0 }
    }

    fn get_arr_index_wrapped(&self, index : usize) -> usize {
        (self.index + index) % SIZE
    }
}

impl<T, const SIZE : usize> std::convert::TryFrom<Box<[T]>> for RingBuffer<T, SIZE> {
    type Error = Box<[T]>; 
    ///Conversion from a boxed slice. This works without a re-allocation. Returns the input as `Err`
    ///in case the size does not match. Opposed to the [`new()`][RingBuffer::new] method that takes an
    ///[`Iterator`] this conversion fails if the input has more elements than fit into the ring buffer.
    ///
    ///# Examples
    ///```
    /// # use boxed_array_ringbuffer::RingBuffer;
    ///let a : Box<[_]> = vec![42,37,23,12].into();
    ///let buf : RingBuffer<_, 4> = a.try_into().expect("Works, size matches.");
    ///assert_eq!(buf[0], 42);
    ///assert_eq!(buf[1], 37);
    ///assert_eq!(buf[2], 23);
    ///assert_eq!(buf[3], 12);
    ///assert_eq!(buf.get(4),None);
    ///
    ///let b : Box<[_]> = vec![42,37,23,12].into();
    ///let b_cpy = b.clone();
    ///let buf2 : Result<RingBuffer<_,3>,_> = b.try_into();
    ///assert_eq!(buf2.unwrap_err(), b_cpy);
    ///```
   fn try_from(slice: Box<[T]>) -> Result<Self, Self::Error> {
        let array = slice.try_into()?;
        Ok(RingBuffer { storage : array, index : 0 })
    }
}

impl<T, const SIZE : usize> std::convert::TryFrom<Vec<T>> for RingBuffer<T, SIZE> {
    type Error = Vec<T>;
    ///Conversion from a [`Vec`]. This works without re-allocation. Returns the input as `Err` in case
    ///the size does not match. Opposed to the [`new()`][RingBuffer::new] method that takes an
    ///[`Iterator`] this conversion fails if the input has more elements than fit into the ring buffer.
    ///
    ///# Examples
    ///```
    /// # use boxed_array_ringbuffer::RingBuffer;
    ///let a = vec![42,37,23,12];
    ///let buf : RingBuffer<_, 4> = a.try_into().expect("Works, size matches.");
    ///assert_eq!(buf[0], 42);
    ///assert_eq!(buf[1], 37);
    ///assert_eq!(buf[2], 23);
    ///assert_eq!(buf[3], 12);
    ///assert_eq!(buf.get(4),None);
    ///
    ///let b = vec![42,37,23,12];
    ///let b_cpy = b.clone();
    ///let buf2 : Result<RingBuffer<_,3>,_> = b.try_into();
    ///assert_eq!(buf2.unwrap_err(), b_cpy);
    ///```
    fn try_from(vector : Vec<T>) -> Result<Self, Self::Error> {
        let slice : Box<[T]> = vector.into();
        match slice.try_into() {
            Ok(array) => { Ok(RingBuffer{ storage : array, index : 0 }) }
            Err(slice) => { Err(slice.into()) }
        }
    }
}

impl<T, const SIZE : usize> std::convert::From<RingBuffer<T, SIZE>> for std::collections::VecDeque<T> {
    ///Conversion from a [`RingBuffer<T, const SIZE :usize>`][crate::RingBuffer] into a
    ///[`VecDeque<T>`][std::collections::VecDeque]. This works without re-allocations and cannot fail.
    ///
    ///# Examples
    ///```
    /// # use boxed_array_ringbuffer::RingBuffer;
    ///use std::collections::VecDeque;
    ///let a = vec![42,37,23,12];
    ///let buf : RingBuffer<_, 4> = a.try_into().expect("Works, size matches.");
    ///let (buf, _) = buf.push_pop(5);
    ///let deque : VecDeque<_> = buf.into();
    ///assert_eq!(deque[0], 37);
    ///assert_eq!(deque[3], 5);
    ///```
    fn from(buffer : RingBuffer<T, SIZE>) -> std::collections::VecDeque<T> {
        let slice = buffer.storage as Box<[T]>;
        let vec : Vec<T> = slice.into();
        let mut deque : std::collections::VecDeque<T> = vec.into();
        deque.rotate_left(buffer.index);
        deque
    }
}

impl<T, const SIZE : usize> Index<usize> for RingBuffer<T, SIZE> {
    type Output = T;
    ///Indexing operation in an immutable context. Internally uses [`get()`][RingBuffer::get].
    ///Indices start at the value that would be replaced/returned by the next call to
    ///[`push_pop()`][RingBuffer::push_pop].
    ///# Examples
    ///
    ///```
    /// # use boxed_array_ringbuffer::RingBuffer;
    ///let input = [42,37,23,12];
    ///let buf : RingBuffer<&usize, 4> = RingBuffer::new(input.iter()).unwrap();
    ///let (buf, _) = buf.push_pop(&123);
    ///assert_eq!(buf[0],&37);
    ///assert_eq!(buf[3],&123);
    ///```
    ///
    ///# Panics
    ///If the index is out of range (larger than or equal to `SIZE`), this panics. Use
    ///[`get()`][RingBuffer::get] if you want sane behaviour.
    fn index(&self, index : usize) -> &T {
        self.get(index).expect("Ring buffer index out of bounds")
    }
}

impl<T, const SIZE : usize> IndexMut<usize> for RingBuffer<T, SIZE> {
    ///Indexing operation in a mutable context. Internally uses [`get_mut()`][RingBuffer::get_mut].
    ///Indices start at the value that would be replaced/returned by the next call to
    ///[`push_pop()`][RingBuffer::push_pop].
    ///# Examples
    ///
    ///```
    /// # use boxed_array_ringbuffer::RingBuffer;
    ///let input = [42,37,23,12];
    ///let mut buf : RingBuffer<&usize, 4> = RingBuffer::new(input.iter()).unwrap();
    ///buf[1] = &0;
    ///assert_eq!(buf[1], &0);
    ///let (buf, forty_two) = buf.push_pop(&3);
    ///assert_eq!(forty_two, &42);
    ///let (buf, zero) = buf.push_pop(&4);
    ///assert_eq!(zero, &0);
    ///```
    ///
    ///# Panics
    ///If the index is out of range (larger than or equal to `SIZE`), this panics. Use
    ///[`get_mut()`][RingBuffer::get_mut] if you want sane behaviour.
fn index_mut(&mut self, index :usize) -> &mut T {
        self.get_mut(index).expect("Ring buffer index out of bounds")
    }
}

///[`Iterator`] type returned by [`RingBuffer::iter()`]. Holds a reference to the ring buffer. See
///[`RingBuffer::iter()`] for an example.
#[derive(Clone)]
pub struct RingBufferIterator<'a, T, const SIZE :usize> {
    ring_buffer : &'a RingBuffer<T, SIZE>,
    index : usize,
}

impl<'b, T, const SIZE : usize> Iterator for RingBufferIterator<'b, T, SIZE> {
    type Item = &'b T;
    fn next(&mut self) -> Option<&'b T> {
        let result = self.ring_buffer.get(self.index);
        if result.is_some() {
            self.index += 1;
        }
        result
    }
}

impl<T, const SIZE : usize> IntoIterator for RingBuffer<T, SIZE> {
    type Item = T;
    type IntoIter = std::collections::vec_deque::IntoIter<T>;

    ///Consumes the ring buffer into an [`Iterator`]. This conversion works without reallocation.
    ///
    ///# Example
    ///```
    /// # use boxed_array_ringbuffer::RingBuffer;
    ///let input = [42,37,23,12];
    ///let buf : RingBuffer<&usize, 4> = RingBuffer::new(input.iter()).unwrap();
    ///let (buf, forty_two) = buf.push_pop(&1);
    ///assert_eq!(forty_two, &42);
    ///assert!(buf.into_iter().eq([37,23,12,1].iter()));
    ///```
    fn into_iter(self) -> Self::IntoIter {
        let deque : std::collections::VecDeque<_> = self.into();
        deque.into_iter()
    }
}

impl<'b, T, const SIZE : usize> IntoIterator for &'b RingBuffer<T, SIZE> {
    type Item = &'b T;
    type IntoIter = RingBufferIterator<'b, T, SIZE>;

    ///Wrapper around the [`RingBuffer::iter()`] to enable for-loop compatibility for
    ///`&RingBuffer`.
    ///
    ///# Example
    ///```
    /// # use boxed_array_ringbuffer::RingBuffer;
    ///let input = [42,37,23,12];
    ///let buf : RingBuffer<&usize, 4> = RingBuffer::new(input.iter()).unwrap();
    ///let (buf, forty_two) = buf.push_pop(&1);
    ///assert_eq!(forty_two, &42);
    ///let reference = &buf;
    ///assert!(reference.into_iter().map(|x| *x).eq([37,23,12,1].iter()));
    ///```
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_from_box_slice_too_large() {
        let c : Box<[_]> = vec![42,37,23,12].into();
        let buf3 : Result<RingBuffer<_,5>,_> = c.try_into();
        assert!(buf3.is_err());
    }
    
    #[test]
    fn test_from_vec_too_large() {
        let c = vec![42,37,23,12];
        let buf3 : Result<RingBuffer<_,5>,_> = c.try_into();
        assert!(buf3.is_err());
    }
}
