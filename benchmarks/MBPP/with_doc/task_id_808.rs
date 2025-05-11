/* Iterates through the vector to check for the presence of a given integer k. Returns true if k is found, false otherwise. */

use vstd::prelude::*;

fn main() {}

verus! {

fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
{
    let mut index = 0;
    while index < arr.len() {
        if (arr[index] == k) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
