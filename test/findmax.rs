/* Finds and returns the largest integer in a non-empty vector by iterating through its elements. */

#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
fn find_max(nums: Vec<i32>) -> (ret:i32)
// [Add Requires Clauses Here]
// [Add Ensures Clauses Here]
{
    let mut max = nums[0];
    let mut i = 1;
    while i < nums.len()
    {
        if nums[i] > max {
            max = nums[i];
        }
        i += 1;
    }
    max
}
}
