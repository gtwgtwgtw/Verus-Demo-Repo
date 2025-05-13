use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i && i < result@.len() ==> result@[i] <= e,
        forall|i: int|
            0 <= i && i < v@.len() && v@[i] <= e ==> result@.contains(v@[i]),
        forall|i: int, j: int|
            0 <= i && i < j && j < v@.len()
            && v@[i] <= e && v@[j] <= e
            ==> result@.index_of(v@[i]) < result@.index_of(v@[j])
{
    let mut result = Vec::new();
    let mut i = 0usize;

    while i < v.len()
        invariant
            i <= v.len(),
    {
        if v[i] <= e {
            result.push(v[i]);
        }
        i += 1;
    }

    proof {
        let ghost final_seq = result@;
        assert forall|ii: int, jj: int|
            0 <= ii < jj < v@.len()
            && v@[ii] <= e
            && v@[jj] <= e
            implies final_seq.index_of(v@[ii]) < final_seq.index_of(v@[jj]) by {
                // Because we push elements in ascending index order,
                // any v@[ii] with ii < jj is pushed before v@[jj].
            };
    }

    result
}

}

//             implies final_seq.index_of(v@[ii]) < final_seq.index_of(v@[jj]) by {
//   assertion failed: final_seq.index_of(v@[ii]) < final_seq.index_of(v@[jj])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: True