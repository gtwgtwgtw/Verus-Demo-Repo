use vstd::prelude::*;
fn main() { }

verus! {

#[verifier::loop_isolation(false)]
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    ensures
        // 1) Every element in result is <= e
        forall|i: int|
            0 <= i && i < result@.len() ==> result@[i] <= e,
        // 2) Every element <= e in v appears in result
        forall|i: int|
            0 <= i && i < v@.len() && v@[i] <= e ==> result@.contains(v@[i]),
        // 3) The relative order of elements that are <= e is preserved
        forall|i: int, j: int|
            0 <= i && i < j && j < v@.len()
            && v@[i] <= e && v@[j] <= e
            ==> result@.index_of(v@[i]) < result@.index_of(v@[j])
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;

    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|r: int|
                0 <= r && r < result@.len() ==> result@[r] <= e,
            forall|k: int|
                0 <= k && k < v.len() && v@[k] <= e ==> result@.contains(v@[k]),
            forall|k1: int, k2: int|
                0 <= k1 && k1 < k2 && k2 < v.len()
                && v@[k1] <= e && v@[k2] <= e
                ==> result@.index_of(v@[k1]) < result@.index_of(v@[k2]),
    {
        if v[i] <= e {
            result.push(v[i]);
        }
        i += 1;
    }

    result
}

}

//     let mut result = Vec::new();
//                 0 <= r && r < result@.len() ==> result@[r] <= e,
//   type must be known at this point: result@[r]
//   None: mut result

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False