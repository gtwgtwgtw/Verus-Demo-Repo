/* Adds 4 to each element of the vector in place, preserving its length. */
// [FAILED]

/* Adds 4 to each element of the vector in place, preserving its length. */

use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
pub fn myfun2(x: &mut Vec<i32>)
    requires
        // For each valid index i, the element x@[i] is at most i32::MAX - 4
        // (lifted to an int via "as int"), so adding 4 won't overflow:
        forall|i: int| 0 <= i && i < x@.len() ==> x@[i] <= i32::MAX as int - 4,
    ensures
        // The length of x does not change:
        x@.len() == old(( x@ ) as &mut _).len(),
        // Each element becomes the old value plus 4:
        forall|i: int| 0 <= i && i < x@.len() ==> x@[i] == old(( x@ ) as &mut _)[i] + 4
{
    let mut i: usize = 0;
    let xlen: usize = x.len();

    while i < xlen
        invariant
            // The length is preserved by the loop:
            x@.len() == old(x@).len(),
            // i must stay within [0, x@.len()]:
            0 <= i && i <= x@.len(),
            // Elements before i have already been incremented:
            forall|j: int|
                0 <= j && j < i ==>
                x@[j] == old(x@)[j] + 4,
            // Elements from i onward have not yet been changed:
            forall|j: int|
                i <= j && j < x@.len() ==>
                x@[j] == old(x@)[j],
        decreases xlen - i
    {
        let old_val = x[i];
        x.set(i, old_val + 4);
        i = i + 1;
    }
}
}
// Score: (0, 10)
// Safe: True



//         x@.len() == old(x@).len(),
//   expected `&mut _`, found `Seq<i32>`: x@
//   arguments to this function are incorrect: old

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 12
// Safe: False