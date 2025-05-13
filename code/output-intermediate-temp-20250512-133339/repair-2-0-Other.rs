use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
    forall |i: int, j: int|
        from <= i < j < to ==> a[i] <= a[j]
}

spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
    &&& r.len() == s.len()
    &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
    &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
    &&& p =~= r.map_values(|idx: int| s[idx])
}

spec fn swap_seq<T>(s: Seq<T>, i: int, j: int) -> Seq<T>
    recommends 0 <= i < s.len(), 0 <= j < s.len()
{
    s.update(i, s[j]).update(j, s[i])
}

// Insertion sort
fn test1(nums: &mut Vec<u32>)
    requires
        true
    ensures
        sorted_between(nums@, 0, nums@.len() as int),
        exists |r: Seq<int>| is_reorder_of(r, nums@, old(nums)@)
{
    let n = nums.len();
    if n <= 1 {
        return;
    }

    let old_nums = nums@;

    proof {
        // We'll track a permutation of the original array in the ghost variable `perm`.
        let mut perm = Seq::from_fn(|i: int| i);

        // In each iteration, we make sure that the subarray [0..i) is sorted,
        // then we insert the element at index i into this subarray.
        for i in 1..n
            invariant
                0 <= i <= n,
                nums.len() == n,
                sorted_between(nums@, 0, i as int),
                is_reorder_of(perm, nums@, old_nums),
            decreases (n - i)
        {
            let mut j = i;
            while j > 0
                invariant
                    0 < j <= i,
                    nums.len() == n,
                    sorted_between(nums@, 0, i as int),
                    is_reorder_of(perm, nums@, old_nums),
                decreases j
            {
                assert(j - 1 < n);
                if nums[j - 1] > nums[j] {
                    let temp = nums[j - 1];
                    nums.set(j - 1, nums[j]);
                    nums.set(j, temp);
                    perm = swap_seq(perm, j as int - 1, j as int);
                    assert(is_reorder_of(perm, nums@, old_nums));
                } else {
                    break;
                }
                j -= 1;
            }
            assert(sorted_between(nums@, 0, i as int + 1));
        }
    }
}

}

// // Safe: False
// verus! {
//   unclosed delimiter: {
//   None: 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False