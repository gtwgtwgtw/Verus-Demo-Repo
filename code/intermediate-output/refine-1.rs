
use vstd::prelude::*;

verus!{
/*
  Finds and returns the index of the maximum element in a non-empty vector of integers.
*/
pub fn index_of_max(vec: &Vec<int>) -> (idx: usize)
    requires
        vec.len() > 0,
    ensures
        // The returned index is within bounds:
        idx < vec.len(),
        // The element at the returned index is at least as large as every other:
        forall|j: nat| j < vec.len() ==> vec@[idx as int] >= vec@[j as int],
{
    let mut max_idx = 0usize;
    let mut i = 1usize;

    while i < vec.len()
        invariant
            vec.len() > 0, // Repeating requires condition as an invariant
            vec.len() == vec.len(), // Loop invariant specifying the length of the array
            // max_idx is always strictly less than i:
            max_idx < i,
            // i will never exceed vec.len():
            i <= vec.len(),
            // The element at max_idx is at least as large as all elements before i:
            forall|k: nat| k < i ==> vec@[max_idx as int] >= vec@[k as int],
    {
        if vec@[i as int] > vec@[max_idx as int] {
            max_idx = i;
        }
        i = i + 1;
    }

    max_idx
}
}

fn main() {}
