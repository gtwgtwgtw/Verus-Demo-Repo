#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len()
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

fn remove_duplicates(nums: Vec<i32>) -> (res: Vec<i32>)
    requires
        true,
    ensures
        // 1) Result vector has no duplicates
        res@.no_duplicates(),
        // 2) The set of numbers is the same
        nums@.to_set() == res@.to_set(),
        // 3) Order of first occurrences is preserved
        forall |i: int, j: int|
            0 <= i && i < j && j < res@.len()
            ==> nums@.index_of(res@[i]) < nums@.index_of(res@[j]),
{
    let mut res = Vec::new();
    let mut i = 0;

    while i < nums.len()
        invariant 0 <= i
        invariant i <= nums.len()
        invariant nums.len() == nums.len()
    {
        let mut found = false;
        let mut j = 0;
        while j < res.len()
            invariant 0 <= j
            invariant j <= res.len()
            invariant 0 <= i
            invariant i < nums.len()
            invariant nums.len() == nums.len()
            invariant res.len() == res.len()
        {
            if nums[i] == res[j] {
                found = true;
                break;
            }
            j += 1;
        }

        if !found {
            res.push(nums[i]);
        }
        i += 1;
    }
    res
}
}

fn main() {
    let dedup = remove_duplicates(vec![2, 1, 2, 3, 2, 4]);
    println!("{:?}", dedup);
}

//             if nums[i] == res[j] {
// failed precondition
//         i < vec.view().len(),
//   failed precondition: i < vec.view().len()
//   None: nums[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False