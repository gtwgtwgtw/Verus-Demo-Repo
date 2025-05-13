use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn contains(v: &Vec<i32>, x: i32) -> (result: bool)
    ensures
        result == v@.contains(x),
{
    let mut i = 0;
    while i < v.len()
        invariant
            v.len() == v.len(),
            forall|k: int| 0 <= k < v.len() ==> v[k] == v[k]
    {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
}

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
    } // Added by AI

    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            nums.len() == nums.len(),
            res.len() == res.len(),
            res@.len() <= i,
            res@.no_duplicates(),
            nums@.subrange(0, ( i ) as int).to_set() == res@.to_set(),
            forall|x: int, y: int|
                0 <= x && x < y && y < res@.len()
                ==> nums@.index_of(res@[x]) < nums@.index_of(res@[y]),
            forall|k: int| 0 <= k < nums.len() ==> nums[k] == nums[k],
            forall|k: int| 0 <= k < res.len() ==> res@[k] == res@[k],
        decreases nums.len() - i
    {
        if !contains(&res, nums[i]) {
            res.push(nums[i]);
            proof {
                assert(forall|x: int, y: int|
                    0 <= x && x < y && y < res@.len()
                    ==> nums@.index_of(res@[x]) < nums@.index_of(res@[y]));
            } // Added by AI
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

//             forall|x: int, y: int|
//                 0 <= x && x < y && y < res@.len()
//                 ==> nums@.index_of(res@[x]) < nums@.index_of(res@[y]),
//   None: forall|x: int, y: int|                 0 <= x && x < y && y < res@.len()                 ==> nums@.index_of(res@[x]) < nums@.index_of(res@[y])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False