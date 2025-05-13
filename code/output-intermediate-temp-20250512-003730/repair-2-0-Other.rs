use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
    requires
        // Require that N is no bigger than the length of 'a'
        (N as int) <= a@.len(),
    ensures
        // 1) For all i < N, each element is capped at most 2
        forall|i: int| 0 <= i < N ==> a@.index(i) <= 2,
        // 2) The returned sum equals the sum of the first N elements
        sum as int == a@.subrange(0, N).sum(),
        // 3) Elements beyond N remain unchanged
        forall|i: int| N <= i < old(a)@.len() ==> a@.index(i) == old(a)@.index(i)
{
    let mut i: usize = 0;

    // First loop caps any element at 2 for all indices < N.
    while i < N as usize
        invariant
            a@.len() == old(a)@.len(),
            (N as int) <= a@.len(),
            // Everything before i was capped
            forall|k: int| 0 <= k < i as int ==> a@.index(k) <= 2,
            // Everything from i onward is still the same as old(a)
            forall|k: int| i as int <= k < a@.len() ==> a@.index(k) == old(a)@.index(k)
        modifies(a)
    {
        if a[i] > 2 {
            a.set(i, 2);
        }
        i += 1;
    }

    // Second loop computes the sum of the first N elements.
    i = 0;
    let mut sum: u32 = 0;
    while i < N as usize
        invariant
            a@.len() == old(a)@.len(),
            (N as int) <= a@.len(),
            // The array does not change in this loop
            forall|k: int| 0 <= k < a@.len() ==> a@.index(k) == old(a)@.index(k),
            // The partial sum up to i matches the view of a from 0..i
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