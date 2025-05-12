/*[Performs a linear search on the input vector `nums`, returning the index of the first matching element or -1 if the target is not found.]*/*

#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {
fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)
// [Add Requires Clauses Here]
// [Add Ensures Clauses Here]

{
    let mut i = 0;
    while i < nums.len()
    {
        if nums[i] == target {
            break;
        }
        i = i + 1;
    }
    if i == nums.len() {
        -1
    } else {
        i as i32
    }
}
}
