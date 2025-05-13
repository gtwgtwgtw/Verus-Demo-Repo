use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
/* Returns the index of the first odd element in the given vector. The vector is assumed to contain at least one odd value. */ 
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
requires
    exists |i: int| 0 <= i < v.len() && v[i] % 2 == 1
ensures
    0 <= odd_index < v.len(),
    v[odd_index] % 2 == 1,
    forall |k: int| 0 <= k < odd_index ==> v[k] % 2 == 0
{
    let mut j: usize = 0;
    while (j < v.len())
        invariant
            v.len() > 0,
            forall |k:int| 0 <= k < v.len() ==> true
    {
        if v[j] % 2 == 1 {
            return j;
        }
        j = j + 1;
    }
    j
}
}

use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd2(v: &Vec<u64>) -> (odd_index: usize)
    requires
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1
    ensures
        odd_index < v.len()
{
    let mut j: usize = 0;
    while (j < v.len())
        invariant
            v.len() > 0,
            forall |k:int| 0 <= k < v.len() ==> true
    {
        if v[j] % 2 == 1 {
            return j;
        }
        j = j + 1;
    }
    j
}
}

// fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
// requires
//     exists |i: int| 0 <= i < v.len() && v[i] % 2 == 1
// ensures
// ...
//     j
// }
// fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
//     requires    
//         exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1
//     ensures
// ...
//     j
// }
//   `choose_odd` redefined here: fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)     requires             exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1     ensures         odd_index < v.len() {     let mut j: usize = 0;     while (j < v.len())         invariant             v.len() > 0,             forall |k:int| 0 <= k < v.len() ==> true // v is never changed in this loop     {         if v[j] % 2 == 1 {             return j;         }         j = j + 1;     }     j }
//   previous definition of the value `choose_odd` here: fn choose_odd(v: &Vec<u64>) -> (odd_index: usize) requires     exists |i: int| 0 <= i < v.len() && v[i] % 2 == 1 ensures     0 <= odd_index < v.len(),     v[odd_index] % 2 == 1,     forall |k: int| 0 <= k < odd_index ==> v[k] % 2 == 0 {     let mut j: usize = 0;     while (j < v.len())         invariant             v.len() > 0,             forall |k:int| 0 <= k < v.len() ==> true // v is never changed in this loop     {         if v[j] % 2 == 1 {             return j;         }         j = j + 1;     }     j }

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False