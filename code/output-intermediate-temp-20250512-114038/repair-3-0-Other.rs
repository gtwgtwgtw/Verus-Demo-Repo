use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
    requires
        (N as int) <= a@.len(),
    ensures
        forall|i: int| 0 <= i < N ==> a@.index(i) <= 2,
        sum as int == a@.subrange(0, N).sum(),
        forall|i: int| N <= i < old(a)@.len() ==> a@.index(i) == old(a)@.index(i)
{
    let mut i: usize = 0;

    while i < N as usize
        invariant
            a@.len() == old(a)@.len(),
            (N as int) <= a@.len(),
            forall|k: int| 0 <= k < i as int ==> a@.index(k) <= 2,
            forall|k: int| i as int <= k < a@.len() ==> a@.index(k) == old(a)@.index(k)
        modifies(a)
        decreases (N - i as u32)
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
            a@.len() == old(a)@.len(),
            (N as int) <= a@.len(),
            forall|k: int| 0 <= k < a@.len() ==> a@.index(k) == old(a)@.index(k),
            sum as int == a@.subrange(0, i as int).sum()
        decreases (N - i as u32)
    {
        sum = sum + a[i];
        i += 1;
    }

    sum
}
}

//         modifies a
//   None: modifies

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False