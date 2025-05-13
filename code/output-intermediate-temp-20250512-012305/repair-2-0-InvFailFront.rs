#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]

spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len()
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

fn contains(v: &Vec<i32>, x: i32) -> (result: bool)
    ensures
        result == v@.contains(x),
{
    let mut i = 0;
    let mut found = false;

    while i < v.len()
        invariant
            0 <= i <= v.len(),
            found ==> v@.subrange(0, i as int).contains(x),
            !found ==> !v@.subrange(0, i as int).contains(x),
            v@.len() == v.len() as int,
            forall |k: int| #![trigger v@.index(k)] 0 <= k < v@.len() ==> true,
        decreases v.len() - i
    {
        if v[i] == x {
            found = true;
        }
        i += 1;
    }

    found
}

fn remove_duplicates(nums: Vec<i32>) -> (res: Vec<i32>)
    requires
        true,
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
        assert(nums@.subrange(0, i as int).to_set() == res@.to_set());
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
            nums@.len() == nums.len() as int,
            res@.len() == res.len() as int,
            forall |k: int| #![trigger nums@.index(k)] 0 <= k < nums@.len() ==> true,
        decreases nums.len() - i
    {
        if !contains(&res, nums[i]) {
            res.push(nums[i]);
            proof {
                let new_index = res@.len() - 1;
                let new_elem = res@[new_index];
                assert(nums@.index_of(new_elem) == i);
            }
        }
        i += 1;
        proof { }
    }

    res
}

}

fn main() {
    let dedup = remove_duplicates(vec![2, 1, 2, 3, 2, 4]);
    println!("{:?}", dedup);
}

//             nums@.subrange(0, i as int).to_set() == res@.to_set(),
//   None: nums@.subrange(0, i as int).to_set() == res@.to_set()

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: True