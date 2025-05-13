use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
requires
    true
ensures {
    forall|i: int| 0 <= i < result.len() ==> result[i] <= e,
    forall|i: int| 0 <= i < v.len() && v[i] <= e ==> result.contains(v[i]),
    forall|i: int, j: int| 0 <= i < j < v.len() && v[i] <= e && v[j] <= e ==> result.index_of(v[i]) < result.index_of(v[j])
}
{
    let mut i: usize = 0;
    let vlen = v.len();
    let mut result: Vec<i32> = vec![];
    while i < v.len() {
        if v[i] <= e {
            result.push(v[i]);
        }
        i += 1;
    }
    result
}
}

// ∀ i in 0..result.len() ⇒ result[i] ≤ e,
//   None: in

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False