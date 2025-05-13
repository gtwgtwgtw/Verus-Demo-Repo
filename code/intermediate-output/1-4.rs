
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
        invariant
            // Bounds on indices
            i1 < v.len(),
            i2 < v.len(),
            i1 <= i2,
            
            // Key existence guarantee
            ∃i: i < v.len() && v[i] == k,
            
            // Range invariance
            ∀j: i1 <= j <= i2 ==> v[j] >= k,
            ∀j: 0 <= j < i1 ==> v[j] < k,
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

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 8