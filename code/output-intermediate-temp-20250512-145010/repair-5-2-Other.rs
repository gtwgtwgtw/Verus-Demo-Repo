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
        x@.len() == old(x)@.len(),
        // Each element is the old value plus 4:
        forall|i: int| 0 <= i && i < x@.len() ==> x@[i] == old(x)@[i] + 4
{
    let mut i: usize = 0;
    let xlen: usize = x.len();

    while i < xlen
        invariant
            x@.len() == xlen,
            x@.len() == old(x)@.len(),
            0 <= i && i <= x@.len(),
            forall|j: int|
                0 <= j && j < i ==>
                x@[j] == old(x)@[j] + 4,
            forall|j: int|
                i <= j && j < x@.len() ==>
                x@[j] == old(x)@[j],
            forall|m: int| 0 <= m && m < x@.len() ==> x@[m] <= i32::MAX as int - 4,
        decreases xlen - i
    {
        let old_val = x[i];
        x.set(i, old_val + 4);
        i += 1;
    }
}
}

//                 x@[j] == old<Seq<int>>(x@)[j],
//   `Seq` defined here: 
//   None: Seq

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False