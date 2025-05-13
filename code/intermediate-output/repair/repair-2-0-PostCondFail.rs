
/*
Performs binary search on a sorted vector to locate a given key.
Returns the index of the key within the vector.
*/

//This example is from Verus tutorial, Chpt 7.5
use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        v.len() > 0,
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
        exists|idx: int| 0 <= idx < v.len() && v[idx] == k
    ensures
        r < v.len(),
        v[r as int] == k,
        forall|i: int| 0 <= i < r as int ==> v[i] < k
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;
    while i1 != i2
        invariant
            v.len() > 0,
            forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
            exists|idx: int| 0 <= idx < v.len() && v[idx] == k, // Key must be in the range
            i1 <= i2, // Ensure i1 is always less than or equal to i2
            i2 < v.len(), // Ensure i2 is within bounds of the array
            i1 < v.len(), // Ensure i1 is within bounds of the array
            i2 - i1 <= v.len(), // Prevent overflow in the subtraction (i2 - i1)
            forall|i: int| 0 <= i < i1 as int ==> v[i] < k, // Added invariant by AI
    {
        let ix = i1 + (i2 - i1) / 2;
        if v[ix] < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }
    }
    proof {
        assert(forall|i: int| 0 <= i < i1 as int ==> v[i] < k); // Added proof block by AI
    }
    i1
}
}


// failed this postcondition
//         forall|i: int| 0 <= i < r as int ==> v[i] < k
// at the end of the function body
//     i1
//   at the end of the function body: i1
//   failed this postcondition: forall|i: int| 0 <= i < r as int ==> v[i] < k

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True