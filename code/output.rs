
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)
    requires
        nums.len() <= i32::MAX as usize,
    ensures
        // If `ret == -1`, no element in the vector equals `target`.
        ret == -1 ==> (
            forall |j: int|
                0 <= j < nums.len() as int
                ==> nums[j as int] != target
        ),
        // Otherwise, `ret` is a valid index, contains `target`, and no earlier index contains `target`.
        ret != -1 ==> (
            0 <= ret < nums.len() as i32
            && nums[ret as int] == target
            && (forall |j: int|
                0 <= j < ret as int
                ==> nums[j as int] != target
            )
        )
{
    let mut i = 0usize;
    while i < nums.len()
        invariant
            i <= nums.len(),
            nums.len() <= i32::MAX as usize, // Copied consistent bound
            (forall |j: int| 0 <= j < i as int ==> nums[j as int] != target),
        decreases nums.len() - i
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

// Score: (1, 0)
// Safe: False