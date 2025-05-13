use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
requires
ensures {
    ∀ i in 0..result.len() ⇒ result[i] ≤ e,
    ∀ i in 0..v.len() ⇒ (v[i] ≤ e) ⇒ result.contains(v[i]),
    ∀ i, j in 0..v.len() ⇒ (i < j ∧ v[i] ≤ e ∧ v[j] ≤ e) ⇒ (result.index_of(v[i]) < result.index_of(v[j]))
}
{
    let mut i: usize = 0;
    let vlen = v.len();
    let mut result: Vec<i32> = vec![];
    while (i < v.len()) 
    {
        if (v[i] <= e) {
            result.push(v[i]);
        }
        i = i + 1;
    }
    result
}
}

// ∀ i in 0..result.len() ⇒ result[i] ≤ e,
//   None: in

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 15
// Safe: False