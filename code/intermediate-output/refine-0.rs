
/*[Performs a linear search on the input vector `nums`, returning the index of the first matching element or -1 if the target is not found.]*/

#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)
    requires
        // We assume the length of the vector is within i32 range so that casting
        // its length to i32 is safe.
        nums.len() <= i32::MAX as usize,
    ensures
        // If `ret == -1`, then no element in the vector is equal to `target`.
        ret == -1 ==> (
            forall |j: int|
                0 <= j < nums.len() as int
                ==> nums.index(j) != target
        ),
        // Otherwise, `ret` must be within valid index range, the element at `ret`
        // is `target`, and no earlier index has an element equal to `target`.
        ret != -1 ==> (
            0 <= ret < nums.len() as i32
            && nums.index(ret as int) == target
            && (forall |j: int|
                0 <= j < ret
                ==> nums.index(j) != target
            )
        )
{
    let mut i = 0usize;
    while i < nums.len()
        invariant
            nums.len() <= i32::MAX as usize,
            i <= nums.len(),
            (forall |j: int| 0 <= j < i as int ==> nums.index(j) != target),
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
