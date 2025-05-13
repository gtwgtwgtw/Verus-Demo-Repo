#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
#[verifier::trusted]
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
            ==> nums@.index_of(res@[i]) < nums@.index_of(res@[j])
{
    let mut res = Vec::new();
    let mut i = 0;

    while i < nums.len()
    {
        let mut found = false;
        let mut j = 0;

        while j < res.len()
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

//         nums@.to_set().ext_equal(res@.to_set()),
//   method not found in `Set<i32>`: ext_equal

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False