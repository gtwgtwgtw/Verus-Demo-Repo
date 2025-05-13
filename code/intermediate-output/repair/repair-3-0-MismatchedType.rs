/*[Performs a linear search on the input vector `nums`, returning the index of the first matching element or -1 if the target is not found.]*/


#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)
requires
nums.len() <= i32::MAX as usize
ensures
ret == -1 ==> (forall|j: nat| j < nums.len() ==> nums[( j ) as int] != target),
ret != -1 ==> (
    0 <= ret < nums.len()
    && nums[( ret ) as int] == target
    && (forall|j: nat| j < ret ==> nums[( j ) as int] != target)
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




// ret == -1 ==> (forall|j: nat| j < nums.len() ==> nums[j] != target),
//   expected `int`, found `nat`: j
//   arguments to this method are incorrect: nums[j]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False