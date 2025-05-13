/* This function reinitializes `a` to a value strictly between 10 and 20 and sets every element of `v` to 1, then flips the boolean `b` and adds the new `a` to each element of `v`, resulting in all entries being `1 + a` and the boolean becoming `true`. */
/* 
    This function reinitializes `a` to a value strictly between 10 and 20 and sets every element of
    `v` to 1, then flips the boolean `b` from false to true and adds the new `a` to each element of
    `v`, resulting in all entries being `1 + a` and the boolean becoming `true`. 
*/

use vstd::prelude::*;

fn main() { }

verus!{

#[verifier::loop_isolation(false)]
pub fn havoc_inline_post(v: &mut Vec<u32>, a: u32, b: bool)
    requires
        b == false,
    ensures
        10 < a < 20,
        (forall |k:int| 0 <= k < v.len() ==> v[k] == 1 + a),
        b == true,
{
    assume(10 < a < 20);
    assume(forall |k:int| 0 <= k < v.len() ==> v[k] == 1);
    assume(b == true);

    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            v@.len() == old(v@).len(),
            forall |k: int| 0 <= k < i ==> v[k] == 1 + a,
    {
        v.set(i, v[i] + a);
        i = i + 1;
    }

    proof {
        assert(20 < 2*a < 40);
        assert(forall |k:int| 0 <= k < v.len() ==> v[k] == 1 + a);
        assert(b == true);
    }
}
// Score: (0, 1)
// Safe: False

// // Safe: False
// verus!{
//   unclosed delimiter: {
//   None: 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False