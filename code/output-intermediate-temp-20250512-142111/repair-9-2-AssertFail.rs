use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_order_before_new_push(
    v: Seq<int>,
    e: int,
    result_before: Seq<int>,
    i: int,
)
    requires
        0 <= i <= v.len(),
        // Invariant: for all x < y <= i, if v[x] <= e and v[y] <= e, then
        // the index_of v[x] in result_before is strictly less than the index_of v[y].
        forall |x: int, y: int| 
            0 <= x < y <= i
            && v[x] <= e
            && v[y] <= e
            ==> result_before.index_of(v[x]) < result_before.index_of(v[y]),
    ensures
        // For every x < i with v[x] <= e, index_of(v[x]) < result_before.len()
        // so that after pushing a new element at the end, they are each < new_len - 1.
        forall |x: int|
            0 <= x < i && v[x] <= e
            ==> result_before.index_of(v[x]) < result_before.len(),
{
    assert forall |x: int| 0 <= x < i && v[x] <= e implies result_before.index_of(v[x]) < result_before.len() by {
        if x < i {
            // pick y = i in the ordering invariant:
            // if v[i] <= e, then index_of(v[x]) < index_of(v[i])
            // otherwise, v[x] was inserted when x < i, so it must be in the current result with some valid index
            // less than result_before.len().
            // The main point is that previously added items must come before the new push index.
            // If v[i] <= e, then index_of(v[x]) < index_of(v[i]) <= result_before.len().
            // If v[i] > e, then v[x] was inserted strictly below the new push index anyway.
        }
    };
}

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
            result.push(v[i]);
            proof {
                lemma_order_before_new_push(v@, e, result@.subrange(0, result@.len() - 1), i as int);
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

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True