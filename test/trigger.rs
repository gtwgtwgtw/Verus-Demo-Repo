/* Given a non-empty vector whose elements satisfy that each element equals its index plus 2, returns the element at the specified index i. The returned value therefore equals i + 2. */

#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus!{
spec fn f(seq: Seq<u64>, i: int) -> bool {
    seq[i] == i + 2
}

fn get_element_check_property(arr: Vec<u64>, i: usize) -> (ret: u64)
// [Add Requires Clauses Here]
// [Add Ensures Clauses Here]

{
    arr[i]
}
}
