/* Given a non-empty vector whose elements satisfy that each element equals its index plus 2, returns the element at the specified index i. The returned value therefore equals i + 2. */
// [FAILED]

/* Given a non-empty vector whose elements satisfy that each element equals its index plus 2, returns the element at the specified index i. The returned value therefore equals i + 2. */

#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus!{

#[verifier::loop_isolation(false)]
spec fn f(seq: Seq<u64>, i: int) -> bool {
    seq[i] == i + 2
}

fn get_element_check_property(arr: Vec<u64>, i: usize) -> (ret: u64)
requires
arr.len() > 0,
i < arr.len(),
forall j: usize :: j < arr.len() ==> arr[j] == j as u64 + 2
ensures
ret == i as u64 + 2

{
    arr[i]
}
}
// Score: (0, 1)
// Safe: False