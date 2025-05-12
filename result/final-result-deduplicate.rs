/*
Recursively converts a sequence into a set of its elements.
Removes duplicates from a vector of integers, preserving the order of first occurrences.
*/
// [FAILED]

/*
Recursively converts a sequence into a set of its elements.
Removes duplicates from a vector of integers, preserving the order of first occurrences.
*/
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

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


fn remove_duplicates(nums: Vec<i32>) -> (res: Vec<i32>)
requires

ensures
res@.no_duplicates(),
Set::ext_equal(seq_to_set_rec(nums@), res@.to_set())
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

#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

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
ensures
    res@.no_duplicates(),
    nums@.to_set().ext_equal(res@.to_set())
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
// Score: (0, 3)
// Safe: None