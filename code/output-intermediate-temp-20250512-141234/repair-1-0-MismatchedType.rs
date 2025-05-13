/* Returns a new vector containing all elements from the input vector that are less than or equal to the given threshold. The relative order of elements in the input is preserved in the output. */
// [FAILED]

/* Returns a new vector containing all elements from the input vector that are less than or equal to the given threshold. The relative order of elements in the input is preserved in the output. */
/* Returns a new vector containing all elements from the input vector that are less than or equal to the given threshold. 
   The relative order of elements in the input is preserved in the output. */

use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires
        // no special pre-conditions
    ensures
        // Every element in result is <= e
        forall|i: usize| 0 <= i && i < result.len() ==> result[( i ) as int] <= e,
        // Every element <= e in v appears in result
        forall|i: usize| 0 <= i && i < v.len() && v[( i ) as int] <= e ==> result.contains(v[( i ) as &i32),
        // The relative order of elements <= e is preserved
        forall|i: usize, j: usize| 
            0 <= i && i < j && j < v.len() && v[i] <= e && v[j] <= e 
            ==> result.index_of(v[i]) < result.index_of(v[j])
{
    let mut i: usize = 0;
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
// Score: (0, 10)
// Safe: None





//         forall|i: usize| 0 <= i && i < result.len() ==> result[i] <= e,
//   expected `int`, found `usize`: i
//   arguments to this method are incorrect: result[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: None