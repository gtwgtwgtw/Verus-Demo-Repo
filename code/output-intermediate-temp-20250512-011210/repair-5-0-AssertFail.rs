#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/****************************************************
 * 1) A spec function for converting a sequence
 *    to a set by recursion
 ****************************************************/
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len()
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

/****************************************************
 * 2) contains(v, x): returns true iff x is in v
 ****************************************************/
#[verifier::loop_isolation(false)]
fn contains(v: &Vec<i32>, x: i32) -> (result: bool)
    ensures
        result == v@.contains(x),
{
    let mut i = 0;
    let mut found = false;

    while i < v.len()
        invariant
            0 <= i <= v.len(),
            found ==> v@.contains(x),
            !found ==> !v@.subrange(0, i as int).contains(x),
        decreases v.len() - i
    {
        if v[i] == x {
            found = true;
        }
        i += 1;
    }

    found
}

/****************************************************
 * 3) A helper lemma: if an element does not appear
 *    in the first i elements of nums, then its
 *    index_of is exactly i
 ****************************************************/
proof fn lemma_index_of_is_i_if_not_in_0_to_i(nums: Seq<i32>, i: int)
    requires
        0 <= i < nums.len(),
        (forall|j: int| 0 <= j < i ==> nums[j] != nums[i]),
    ensures
        nums.index_of(nums[i]) == i
{
    // By definition, index_of finds the first j such that nums[j] == nums[i].
    // Since nums[i] is not found for j < i, j must be exactly i.
}

/****************************************************
 * 4) remove_duplicates(nums):
 *    - no duplicates in the result
 *    - same set of elements
 *    - order of first occurrences is preserved
 ****************************************************/
fn remove_duplicates(nums: Vec<i32>) -> (res: Vec<i32>)
    requires
        true,
    ensures
        res@.no_duplicates(),
        nums@.to_set() == res@.to_set(),
        forall|x: int, y: int|
            0 <= x && x < y && y < res@.len()
            ==> nums@.index_of(res@[x]) < nums@.index_of(res@[y]),
{
    let mut res = Vec::new();
    let mut i = 0;
    proof {
        assert(nums@.subrange(0, 0).to_set() == res@.to_set());
    }
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            res@.no_duplicates(),
            nums@.subrange(0, i as int).to_set() == res@.to_set(),
            forall|r: int|
                0 <= r < res@.len() ==> nums@.index_of(res@[r]) < i,
            forall|x: int, y: int|
                0 <= x && x < y && y < res@.len()
                ==> nums@.index_of(res@[x]) < nums@.index_of(res@[y]),
        decreases nums.len() - i
    {
        if !contains(&res, nums[i]) {
            res.push(nums[i]);
            proof {
                let new_index = res@.len() - 1;
                let new_elem = res@[new_index];
                // Show that new_elem was not in nums@.subrange(0, i) at all:
                assert(forall|j: int| 0 <= j < i ==> nums@[j] != new_elem);
                lemma_index_of_is_i_if_not_in_0_to_i(nums@, ( i ) as int);
                assert(nums@.index_of(new_elem) == i);

                assert(forall|x: int|
                    0 <= x < new_index
                    ==> nums@.index_of(res@[x]) < i
                );
                assert(forall|x: int|
                    0 <= x < new_index
                    ==> nums@.index_of(res@[x]) < nums@.index_of(res@[new_index])
                );
            }
        }
        i += 1;
        proof {
            // Preserve the ordering property in the loop
            assert(forall|x: int, y: int|
                0 <= x && x < y && y < res@.len()
                ==> nums@.index_of(res@[x]) < nums@.index_of(res@[y]));
        }
    }
    res
}

fn main() {
    let dedup = remove_duplicates(vec![2, 1, 2, 3, 2, 4]);
    println!("{:?}", dedup);
}
}


//                 assert(nums@.index_of(new_elem) == i);
//   assertion failed: nums@.index_of(new_elem) == i

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False