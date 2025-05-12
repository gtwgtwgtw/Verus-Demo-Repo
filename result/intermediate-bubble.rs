/* Sorts the given vector of u32 in non-decreasing order using insertion sort.  
   The final sequence is a permutation of the original elements. */

use vstd::prelude::*;
fn main() {}

verus! {
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

    ensures
exists |r: Seq<int>| is_reorder_of(r, nums@, old(nums@)),
sorted_between(nums@, 0, n as int)
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
