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
        assert(forall|x: int, y: int|
            0 <= x < y < v@.len()
            && v@[x] <= e
            && v@[y] <= e
            ==> result@.index_of(v@[x]) < result@.index_of(v@[y]));
    } // Added by AI

    result
}

}

//             forall|x: int, y: int|
//                 0 <= x < y < i
//                 && v@[x] <= e
//                 && v@[y] <= e
//                 ==> result@.index_of(v@[x]) < result@.index_of(v@[y]),
//   None: forall|x: int, y: int|                 0 <= x < y < i                 && v@[x] <= e                 && v@[y] <= e                 ==> result@.index_of(v@[x]) < result@.index_of(v@[y])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: True