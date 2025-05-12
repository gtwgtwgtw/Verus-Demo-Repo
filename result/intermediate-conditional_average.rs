/*
For each index, computes and stores into the output vector either the average of the two input values if both condition flags are true, the first input value if only the first flag is true, or the second input value if only the second flag is true.  
The output vector is cleared and then filled to match the length of the input vectors.
*/

use vstd::prelude::*;
fn main() {}

verus!{
fn conditional_average(vals_1: &Vec<u64>, vals_2: &Vec<u64>, conds_1: &Vec<bool>, conds_2: &Vec<bool>, avgs: &mut Vec<u64>) 
requires
vals_1.len() == vals_2.len(),
vals_1.len() == conds_1.len(),
vals_1.len() == conds_2.len()
ensures
avgs.len() == vals_1.len(),
forall |i: usize| i < vals_1.len() ==>
    if conds_1[i] {
        if conds_2[i] {
            avgs[i] == (vals_1[i] + vals_2[i]) / 2
        } else {
            avgs[i] == vals_1[i]
        }
    } else {
        avgs[i] == vals_2[i]
    }
{
    let mut k: usize = 0;
    let common_len = vals_1.len();
    avgs.clear();
    while (k < common_len)
    {
        let mut new_avg: u64 = 0;
        if (conds_1[k]) {
            if (conds_2[k]) {
                new_avg = (vals_1[k] + vals_2[k]) / 2;
            }
            else {
                new_avg = vals_1[k];
            }
        }
        else {
            new_avg = vals_2[k];
        }
        avgs.push(new_avg);
        k = k + 1;
    }
}
}
