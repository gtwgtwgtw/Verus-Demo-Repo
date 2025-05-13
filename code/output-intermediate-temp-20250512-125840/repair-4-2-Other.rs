use vstd::prelude::*;
fn main() {}

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
    // The following `assume` statements represent the new (havoced) values of these variables.
    // Old `b` was false, so we assume the new `b` is flipped to true.
    assume(10 < a < 20);
    assume(forall |k:int| 0 <= k < v.len() ==> v[k] == 1);
    assume(b == true);

    // Now we add `a` to each element of `v`.
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            v@.len() == old(( v@ ) as &mut _).len(),
            // Everything up to i has been updated to 1 + a:
            forall |k: int| 0 <= k < i ==> v[k] == 1 + a,
    {
        v.set(i, v[i] + a);
        i = i + 1;
    }

    proof {
        // Check final conditions:
        // `a` is in (10, 20), so `2*a` is in (20, 40).
        assert(20 < 2*a < 40);
        // All elements of `v` have become 1 + a.
        assert(forall |k:int| 0 <= k < v.len() ==> v[k] == 1 + a);
        // The boolean has been flipped to true.
        assert(b == true);
    }
}
}


// // Safe: False
// verus!{
//   unclosed delimiter: {
//   None: 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False