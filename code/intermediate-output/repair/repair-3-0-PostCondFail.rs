
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
            exists|idx: int| 0 <= idx < v.len() && v[idx] == k,
            i1 <= i2,
            i2 < v.len(),
            i1 < v.len(),
            i2 - i1 <= v.len(),
            forall|i: int| 0 <= i < i1 as int ==> v[i] < k,
    {
        let ix = i1 + (i2 - i1) / 2;
        if v[ix] < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }
    }
    proof {
        assert(v[i1 as int] == k); // Added proof block by AI
    }
    i1
}
}


// failed this postcondition
//         v[r as int] == k,
// at the end of the function body
//     i1
//   at the end of the function body: i1
//   failed this postcondition: v[r as int] == k

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True