/*
For each index, computes and stores into the output vector either the average of the two input values if both condition flags are true, the first input value if only the first flag is true, or the second input value if only the second flag is true.  
The output vector is cleared and then filled to match the length of the input vectors.
*/
// [FAILED]

/*
For each index, computes and stores into the output vector either the average of the two input values if both condition flags are true, the first input value if only the first flag is true, or the second input value if only the second flag is true.  
The output vector is cleared and then filled to match the length of the input vectors.
*/

use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn conditional_average(
    vals_1: &Vec<u64>, 
    vals_2: &Vec<u64>, 
    conds_1: &Vec<bool>, 
    conds_2: &Vec<bool>, 
    avgs: &mut Vec<u64>
) 
    requires
        vals_1.len() == vals_2.len(),
        vals_1.len() == conds_1.len(),
        vals_1.len() == conds_2.len(),
        // Ensures addition does not overflow:
        forall|i: usize| i < vals_1.len() ==> vals_1[( i ) as int] + vals_2[( i ) as int] <= u64::MAX,
    ensures
        // Output vector is the same length as inputs:
        avgs.len() == vals_1.len(),
        // For each index, handle the conditions as stated:
        forall|i: usize| i < vals_1.len() ==>
            avgs[( i ) as int] == (if conds_1[( i ) as int] && conds_2[( i ) as int] {
                (vals_1[( i ) as int] + vals_2[( i ) as int]) / 2
            } else if conds_1[( i ) as int] {
                vals_1[( i ) as int]
            } else {
                vals_2[( i ) as int]
            })
{
    let mut k: usize = 0;
    let common_len = vals_1.len();
    avgs.clear();
    while k < common_len
        invariant 
            avgs.len() == k,
            k <= common_len
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
// Score: (0, 11)
// Safe: True











//         forall|i: usize| i < vals_1.len() ==> vals_1[i] + vals_2[i] <= u64::MAX,
//   expected `int`, found `usize`: i
//   arguments to this method are incorrect: vals_1[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False