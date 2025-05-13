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
            forall|x: int|
                0 <= x < i && v@[x] <= e
                ==> result@.contains(v@[x]),
            forall|x: int, y: int|
                0 <= x < y < i + 1
                && v@[x] <= e
                && v@[y] <= e
                ==> result@.index_of(v@[x]) < result@.index_of(v@[y]),
    {
        if v[i] <= e {
            result.push(v[i]);
            proof {
                assert(forall|x: int|
                    0 <= x < i && v@[x] <= e
                    ==> result@.index_of(v@[x]) < result@.len() - 1
                );
            }
        }
        i += 1;
    }

    proof {
        assert(forall|x: int, y: int|
            0 <= x < y < v@.len()
            && v@[x] <= e
            && v@[y] <= e
            ==> result@.index_of(v@[x]) < result@.index_of(v@[y]));
    }

    result
}

}

//                 assert(forall|x: int|
//                     0 <= x < i && v@[x] <= e
//                     ==> result@.index_of(v@[x]) < result@.len() - 1
//   assertion failed: forall|x: int|                     0 <= x < i && v@[x] <= e                     ==> result@.index_of(v@[x]) < result@.len() - 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: True