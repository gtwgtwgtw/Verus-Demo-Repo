/* This function reinitializes `a` to a value strictly between 10 and 20 and sets every element of `v` to 1, then flips the boolean `b` and adds the new `a` to each element of `v`, resulting in all entries being `1 + a` and the boolean becoming `true`. */
use vstd::prelude::*;
fn main() {}
verus!{
pub fn havoc_inline_post(v: &mut Vec<u32>, a: u32, b: bool)
requires
    b == false
ensures
    10 < a && a < 20,
    forall |k:int| 0 <= k < v.len() ==> v[k] == 1 + a
{
    assume(10 < a < 20);
    assume(forall |k:int| 0 <= k < v.len() ==> v[k] == 1);

    let c: bool = !b;
    let mut idx: usize = v.len();
    while (idx > 0)
        invariant
            10 < a < 20,
            idx <= v.len(),
            forall |j:int| 0 <= j < idx ==> v[j] == 1,
            forall |j:int| idx <= j < v.len() ==> v[j] == 1 + a,
    {
        idx = idx - 1;
        v.set(idx, v[idx] + a);
    }
    
    proof {
        assert(20 < 2*a < 40);
        assert(forall |k:int| 0 <= k < v.len() ==> v[k] == 1 + a);
        assert(c == true);
    }
}
}
// Score: (2, 0)
// Safe: True