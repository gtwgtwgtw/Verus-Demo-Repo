use vstd::prelude::*;

fn main() {
    let dedup = remove_duplicates(vec![2, 1, 2, 3, 2, 4]);
    println!("{:?}", dedup);
}

verus! {

/****************************************************
 * 1) Recursively converts a sequence into a set
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
 * 3) remove_duplicates(nums):
 *    - no duplicates in the result
 *    - same set of elements
 *    - order of first occurrences is preserved
 ****************************************************/
fn remove_duplicates(nums: Vec<i32>) -> (res: Vec<i32>)
    ensures
        res@.no_duplicates(),
        nums@.to_set() == res@.to_set(),
        forall|i: int, j: int|
            0 <= i && i < j && j < res@.len()
            ==> nums@.index_of(res@[i]) < nums@.index_of(res@[j]),
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
                // Prove that new_elem is indeed first found at index i in nums@
                assert(forall|k: int| 0 <= k < i ==> nums@[k] != new_elem);
                assert(nums@[( i ) as int] == new_elem);
                assert(nums@.index_of(new_elem) == i);
            }
        }
        i += 1;
        proof {
            assert(forall|x: int, y: int|
                0 <= x && x < y && y < res@.len()
                ==> nums@.index_of(res@[x]) < nums@.index_of(res@[y]));
        }
    }

    res
}

}


//                 assert(nums@.index_of(new_elem) == i);
//   assertion failed: nums@.index_of(new_elem) == i

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False