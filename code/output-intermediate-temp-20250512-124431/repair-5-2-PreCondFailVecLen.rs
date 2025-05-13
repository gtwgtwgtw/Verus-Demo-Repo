/* This function reinitializes `a` to a value strictly between 10 and 20 and sets every element of `v` to 1, then flips the boolean `b` and adds the new `a` to each element of `v`, resulting in all entries being `1 + a` and the boolean becoming `true`. */

use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
pub fn havoc_inline_post(v: &mut Vec<u32>, a: u32, b: bool)
requires
    b == false
ensures
    10 < a < 20,
    (forall |k:int| 0 <= k < v.len() ==> v[k] == 1 + a),
    b == true
{  
    // Variables a and v are havocked. Their values are randomly reset, but their new values follow the following assumptions.
    assume(10 < a < 20);
    assume(forall |k:int| 0 <= k < v.len() ==> v[k] == 1);

    let c: bool = !b;
    let mut idx: usize = v.len();
    while (idx > 0)
        invariant v.len() == old(v).len()
        invariant 0 <= idx <= v.len()
    {
        idx = idx - 1;
        v.set(idx, v[idx] + a);
    }
    
    proof {  // inline postcondition
        assert(20 < 2*a < 40);
        assert(forall |k:int| 0 <= k < v.len() ==> v[k] == 1 + a);
        assert(c == true);
    }
}
}
// Score: (0, 3)
// Safe: True

//         v.set(idx, v[idx] + a);
// failed precondition
//         i < vec.view().len(),
//   failed precondition: i < vec.view().len()
//   None: v[idx]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False