use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
pub fn myfun2(x: &mut Vec<i32>)
    requires
        // For each valid index i, the element x@[i] is at most i32::MAX - 4:
        forall|i: int| 0 <= i && i < x@.len() ==> x@[i] <= i32::MAX as int - 4,
    ensures
        // The length is unchanged:
        x@.len() == pre_x.len(),
        // Each element is the old value plus 4:
        forall|i: int| 0 <= i && i < x@.len() ==> x@[i] == pre_x[i] + 4
{
    let ghost pre_x = x@; // Added by AI

    let mut i: usize = 0;
    let xlen: usize = x.len();

    while i < xlen
        invariant
            x@.len() == pre_x.len(),
            x@.len() == xlen,
            0 <= i && i <= x@.len(),
            // Repeat the precondition bound as an invariant:
            forall|j: int| 0 <= j && j < x@.len() ==> x@[j] <= i32::MAX as int - 4,
            forall|j: int| 0 <= j && j < i ==> x@[j] == pre_x[j] + 4,
            forall|j: int| i <= j && j < x@.len() ==> x@[j] == pre_x[j],
        decreases xlen - i
    {
        let old_val = x[i];
        x.set(i, old_val + 4);
        i += 1;
    }
}
}

//         forall|i: int| 0 <= i && i < x@.len() ==> x@[i] == pre_x[i] + 4
//   not found in this scope: pre_x

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False