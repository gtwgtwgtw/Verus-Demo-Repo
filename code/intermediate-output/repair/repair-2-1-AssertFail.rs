use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    ensures
        // 1) Every element in result is ≤ e 
        forall|i: int|
            0 <= i && i < result@.len() ==> result@[i] <= e,

        // 2) Every element ≤ e in v appears in result
        forall|i: int|
            0 <= i && i < v@.len() && v@[i] <= e ==> result@.contains(v@[i]),

        // 3) The relative order of elements ≤ e is preserved
        forall|i: int, j: int|
            0 <= i && i < j && j < v@.len()
            && v@[i] <= e && v@[j] <= e
            ==> result@.index_of(v@[i]) < result@.index_of(v@[j])
{
    let mut result = Vec::new();
    let mut i = 0usize;

    while i < v.len() {
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
                reveal(index_of);
            };
    }

    result
}

}

//             implies final_seq.index_of(v@[ii]) < final_seq.index_of(v@[jj]) by {
//   assertion failed: final_seq.index_of(v@[ii]) < final_seq.index_of(v@[jj])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True