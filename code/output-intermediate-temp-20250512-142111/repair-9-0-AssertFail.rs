use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_index_of_before_push<T>(old_r: Seq<T>, new_r: Seq<T>, x: T, e: T)
    requires
        old_r.len() + 1 == new_r.len(),
        new_r =~= old_r.push(e),
        old_r.contains(x),
    ensures
        new_r.index_of(x) < new_r.len() - 1
{
    // Since x is in old_r, x is not the newly pushed element e
    // => x's index remains the same in new_r and is strictly less than new_r.len() - 1
}

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
            forall|x: int, y: int|
                0 <= x < y < i + 1
                && v@[x] <= e
                && v@[y] <= e
                ==> result@.index_of(v@[x]) < result@.index_of(v@[y]),
    {
        if v[i] <= e {
            let old_result = result@;
            result.push(v[i]);
            proof {
                assert(old_result.len() + 1 == result@.len());
                assert(result@ =~= old_result.push(v@[i as int]));
                assert(forall|x: int|
                    0 <= x < i && v@[x] <= e
                    ==> {
                        if old_result.contains(v@[x]) {
                            lemma_index_of_before_push(old_result, result@, v@[x], v@[i as int]);
                            result@.index_of(v@[x]) < result@.len() - 1
                        } else {
                            // If x wasn't in old_result, we don't need the assertion for it
                            true
                        }
                    }
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

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False