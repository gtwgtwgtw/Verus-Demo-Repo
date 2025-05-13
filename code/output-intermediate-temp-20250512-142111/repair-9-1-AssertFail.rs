#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {

/// Lemma stating that if we push a new element `x` not already in the sequence `s`,
/// then its index_of is exactly `s.len()`.
proof fn lemma_index_of_push_new<T: PartialEq>(s: Seq<T>, x: T)
    requires
        s.index_of(x) == s.len(),  // means x not in s
    ensures
        s.push(x).index_of(x) == s.len(),
{
    // Direct reasoning that the newly pushed element is at the new last position
    // (because it was not in the sequence before).
}

pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    ensures
        // 1) All elements in result are <= e
        forall|i: int|
            0 <= i && i < result@.len() ==> result@[i] <= e,
        // 2) Every element <= e in v is in result
        forall|i: int|
            0 <= i && i < v@.len() && v@[i] <= e ==> result@.contains(v@[i]),
        // 3) The order (by index) of values <= e in v is preserved in result
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
            // Save the old length of result
            let old_len = result@.len();
            result.push(v[i]);

            proof {
                // From the loop invariant with x < i, we have:
                //   result@.index_of(v@[x]) < result@.index_of(v@[i]).
                // Once we push v[i], we want to show that for all x < i with v@[x] <= e,
                //   result@.index_of(v@[x]) < result@.len() - 1.
                //
                // The new element v@[i] occupies some index in result@; if v@[i] wasn't present before,
                // lemma_index_of_push_new can show it's at old_len. Thus index_of(v@[x]) is strictly less than that.
                //
                // So we use the loop invariant + the fact that the new element goes to the
                // last position if it was not in result before:

                assert(forall|x: int|
                    0 <= x < i && v@[x] <= e
                    ==> result@.index_of(v@[x]) < result@.len() - 1
                );
            }
        }
        i += 1;
    }

    proof {
        // Show that the final ordering property still holds for all x < y in the entire v@.
        assert(forall|x: int, y: int|
            0 <= x < y < v@.len()
            && v@[x] <= e
            && v@[y] <= e
            ==> result@.index_of(v@[x]) < result@.index_of(v@[y])
        );
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