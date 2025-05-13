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
            } else if conds_1@[i] {
                vals_1@[i]
            } else {
                vals_2@[i]
            }
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
            forall|i: int| 0 <= i < vals_1@.len() ==> vals_1@[i] + vals_2@[i] <= u64::MAX,
            forall|i: int| 0 <= i < conds_1@.len() ==> true,
            forall|i: int| 0 <= i < conds_2@.len() ==> true
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

//             if conds_1@[i] && conds_2@[i] {
//                 (vals_1@[i] + vals_2@[i]) / 2
//             } else if conds_1@[i] {
//                 vals_1@[i]
//             } else {
//                 vals_2@[i]
//             }
//                 (vals_1@[i] + vals_2@[i]) / 2
//             } else if conds_1@[i] {
//                 vals_1@[i]
//             } else {
//                 vals_2@[i]
//             }
//   expected `int`, found `u64`: if conds_1@[i] {                 vals_1@[i]             } else {                 vals_2@[i]             }
//   expected because of this: (vals_1@[i] + vals_2@[i]) / 2
//   `if` and `else` have incompatible types: if conds_1@[i] && conds_2@[i] {                 (vals_1@[i] + vals_2@[i]) / 2             } else if conds_1@[i] {                 vals_1@[i]             } else {                 vals_2@[i]             }

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True