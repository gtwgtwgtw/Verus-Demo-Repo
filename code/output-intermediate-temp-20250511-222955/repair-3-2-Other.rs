/*[Performs a linear search on the input vector `nums`, returning the index of the first matching element or -1 if the target is not found.]*/
// [FAILED]

#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)
requires
    nums.len() <= 2147483647
ensures
    ret == -1 ==> (forall|i: usize| i < nums.len() ==> nums[( i ) as int] != target),
    ret != -1 ==> (
        0 <= ret < nums.len() as i32
        && nums[ret as int] == target
        && (forall|j: usize| j < (ret as usize) ==> nums[( j ) as int] != target)
    )
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
// Score: (0, 1)
// Safe: False




// /*[Performs a linear search on the input vector `nums`, returning the index of the first matching element or -1 if the target is not found.]*/*
//   expected item: *

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False