#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn find_max(nums: Vec<i32>) -> (ret:i32)
    requires
        nums.len() > 0
    ensures
        exists |j: usize| j < nums.len() && ret == nums[( j ) as int],
        forall |k: usize| k < nums.len() ==> ret >= nums[( k ) as int]
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



// forall(|k: usize| k < nums.len() ==> ret >= nums[k])
//   None: forall(|k: usize| k < nums.len() ==> ret >= nums[k])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False