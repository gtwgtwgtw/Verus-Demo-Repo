/* Returns a new vector in which the given element is inserted before each element of the input vector, producing the sequence [elem, arr[0], elem, arr[1], …]. The resulting vector has twice as many items as the original. */

use vstd::prelude::*;

fn main() {}

verus! {

fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)
    ensures
        result@.len() == (2 * arr.len()),
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem,
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k],
{
    let mut result: Vec<i32> = Vec::new();
    let mut index = 0;

    while index < arr.len() {
        result.push(elem);
        result.push(arr[index]);
        index += 1;
    }
    result
}

} // verus!
