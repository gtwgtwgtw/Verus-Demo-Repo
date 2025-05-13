/* Sorts the given vector of u32 in non-decreasing order using insertion sort.  
   The final sequence is a permutation of the original elements. */
// [FAILED]

/* Sorts the given vector of u32 in non-decreasing order using insertion sort.  
   The final sequence is a permutation of the original elements. */

use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
    spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
        forall |i: int, j:int|  from <= i < j < to ==> a[i] <= a[j]
    }
 
 
    spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
    &&& r.len() == s.len()
    &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
    &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
    &&& p =~= r.map_values(|i: int| s[i])
    }
 
    fn test1(nums: &mut Vec<u32>)
    requires
true
    ensures
sorted_between(nums@, 0, ( nums@.len() ) as int),
exists |r: Seq<int>| is_reorder_of(r, nums@, ( old(( nums@ ) as &mut _) ) as Seq<u32>)
    {
        let n = nums.len();
        if n == 0 {
            return;
        }
        for i in 1..n
        {
            let mut j = i;
            while j != 0
            {
                if nums[j - 1] > nums[j] {
                    let temp = nums[j - 1];
                    nums.set(j - 1, nums[j]);
                    nums.set(j, temp);
                }
                j -= 1;
            }
        }
    }
}
// Score: (0, 3)
// Safe: True




// sorted_between(nums@, 0, nums@.len()),
//   expected `int`, found `nat`: nums@.len()
//   arguments to this function are incorrect: sorted_between

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False