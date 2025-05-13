use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
    requires
        (N as usize) <= a.len(),
    ensures
        forall|i: int| 0 <= i < N as int ==> a.index(i) <= 2,
        sum == seq!(a).subrange(0, N as int).sum(),
        forall|i: int| i >= N as int && i < old(a).len() ==> a.index(i) == old(a).index(i)
{
    let mut i: usize = 0;
    while i < N as usize
        invariant
            a.len() == old(a).len(),
            (N as usize) <= a.len()
    {
        if a[i] > 2 {
            a.set(i, 2);
        }
        i += 1;
    }

    i = 0;
    let mut sum: u32 = 0;
    while i < N as usize
        invariant
            a.len() == old(a).len(),
            (N as usize) <= a.len(),
            forall|k:int| 0 <= k < a.len() ==> a[k] == old(a)[k]
    {
        sum = sum + a[i];
        i += 1;
    }

    sum
}
}

//         forall|i: usize| i < N as usize ==> a[i] <= 2,
//   expected `int`, found `usize`: i
//   arguments to this method are incorrect: a[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False