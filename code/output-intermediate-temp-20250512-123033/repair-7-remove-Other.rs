/*
For each index, computes and stores into the output vector either the average of the two input values if both condition flags are true, the first input value if only the first flag is true, or the second input value if only the second flag is true.  
The output vector is cleared and then filled to match the length of the input vectors.
*/
// [FAILED]

use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
fn conditional_average(
    vals_1: &Vec<u64>, 
    vals_2: &Vec<u64>, 
    conds_1: &Vec<bool>, 
    conds_2: &Vec<bool>, 
    avgs: &mut Vec<u64>
)
    requires
        vals_1@.len() == vals_2@.len(),
        vals_1@.len() == conds_1@.len(),
        vals_1@.len() == conds_2@.len(),
        forall|i: int| 
            0 <= i < vals_1@.len() ==>
            vals_1@[i] + vals_2@[i] <= u64::MAX,

    ensures
        avgs@.len() == vals_1@.len(),
        forall|i: int| 0 <= i < vals_1@.len() ==>
            avgs@[i]
            ==
            if conds_1@[i] && conds_2@[i] {
                (vals_1@[i] + vals_2@[i]) / 2
{
    let mut k: usize = 0;
    let common_len = vals_1.len();

    avgs.clear();

    while k < common_len
        invariant
            avgs@.len() == k as int,
            0 <= k as int <= vals_1@.len(),
            common_len == vals_1.len(),
            vals_2.len() == common_len,
            conds_1.len() == common_len,
            conds_2.len() == common_len,
            avgs.len() == k,
            forall|i: int| 0 <= i < vals_1@.len() ==> vals_1@[i] + vals_2@[i] <= u64::MAX, // vals_1, vals_2 are never changed in this loop (no .set calls)
            forall|i: int| 0 <= i < conds_1@.len() ==> true, // conds_1 is never changed in this loop (no .set calls)
            forall|i: int| 0 <= i < conds_2@.len() ==> true // conds_2 is never changed in this loop (no .set calls)
    {
        let new_avg: u64;
        if conds_1[k] && conds_2[k] {
            new_avg = (vals_1[k] + vals_2[k]) / 2;
        } else if conds_1[k] {
            new_avg = vals_1[k];
        } else {
            new_avg = vals_2[k];
        }

        avgs.push(new_avg);
        k = k + 1;
    }
}
}
// Score: (0, 1)
// Safe: True