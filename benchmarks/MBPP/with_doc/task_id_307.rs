/* Deeply clones a vector of u64 by iterating over its elements and pushing them into a new vector. The resulting vector has the same length and contents as the original. */

use vstd::prelude::*;

fn main() {}

verus! {

fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)
    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
{
    let mut copied_array = Vec::with_capacity(arr.len());
    let mut index = 0;
    while index < arr.len() {
        copied_array.push(arr[index]);
        index += 1;
    }
    copied_array
}

} // verus!
