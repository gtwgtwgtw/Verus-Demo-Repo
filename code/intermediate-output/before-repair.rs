/*
Performs binary search on a sorted vector to locate a given key.
Returns the index of the key within the vector.
*/


//This example is from Verus tutorial, Chpt 7.5
use vstd::prelude::*;
fn main() {}

verus!{
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
requires
v.len() > 0,
∀i, j: 0 ≤ i < j < v.len() ==> v[i] ≤ v[j],
∃i: i < v.len() && v[i] == k
ensures
r < v.len(),
v[r] == k
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;
    while i1 != i2
    {
        let ix = i1 + (i2 - i1) / 2;
        if v[ix] < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }
    }
    i1
}
}
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5