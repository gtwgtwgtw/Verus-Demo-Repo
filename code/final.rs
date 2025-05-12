/* Finds and returns the largest integer in a non-empty vector by iterating through its elements. */
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
fn find_max(nums: Vec<i32>) -> (ret:i32)
    requires
        nums.len() > 0
    ensures
        forall |j: usize| j < nums.len() ==> nums[( j ) as int] <= ret,
        exists |j: usize| j < nums.len() && nums[( j ) as int] == ret
{
    let mut max = nums[0];
    let mut i = 1;
    while i < nums.len()
        invariant
            nums.len() > 0,
            1 <= i <= nums.len(),
            forall |k: usize| k < i ==> nums[( k ) as int] <= max,
            exists |k: usize| k < i && nums[( k ) as int] == max,
    {
        if nums[i] > max {
            max = nums[i];
        }
        i += 1;
    }
    max
}
}
// Score: (2, 0)
// Safe: False