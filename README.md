# boxed_array_ringbuffer
Rust Ring Buffer that uses a boxed array as backing storage, to guarantee a fixed size after initialization. Uses const generics.

This crate is useful in cases where one needs an as simple as possible queue of a fixed size, and wants that fixed size to be guaranteed.
The standard library offers a double ended queue of variable size, [`VecDeque`](https://doc.rust-lang.org/std/collections/struct.VecDeque.html),
but there might be cases in which one does not want the used queue to possibly ever grow or shrink, for instance to avoid bugs by making invaild
states unrepresentable.

Storage of the ring buffer is in the heap, because that way `Vec` or `Box<[_]>` can be converted into a `RingBuffer` without any re-allocations, and
a `RingBuffer` can be converted into a `VecDeque` without re-allocations too.

See the documentation on https://docs.rs/boxed_array_ringbuffer for details on how to use it.

This crate does not (directly) use any unsafe code, and only has the standard library as dependency.
