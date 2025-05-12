/* Returns the index of the first odd element in the given vector. The vector is assumed to contain at least one odd value. */
use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1
    ensures
        odd_index < v.len(),
        v[( odd_index ) as int] % 2 == 1,
        forall |i: int| 0 <= i < odd_index ==> v[i] % 2 == 0
{
    let mut j: usize = 0;
    while (j < v.len())
        invariant
            j <= v.len(),
            v.len() > 0,
            forall |i: int| 0 <= i < j ==> v[i] % 2 == 0,
    {
        if v[j] % 2 == 1 {
            return j;
        }
        j = j + 1;
    }
    j
}
}
// Score: (2, 0)
// Safe: False