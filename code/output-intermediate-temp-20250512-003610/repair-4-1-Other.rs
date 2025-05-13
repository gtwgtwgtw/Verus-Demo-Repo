use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
    requires
        (N as usize) <= a.len(),
    ensures
        forall|i: usize| i < N as usize ==> a[( i ) as int] <= 2,
        sum == a@.subrange(0, N as int).fold(0, |acc, x: u32| acc + x),
        forall|i: usize| i >= N as usize && i < old(a).len() ==> a[i] == old(a)[i]
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant a.len() == old(a).len()
    {
        if a[i] > 2 {
            a.set(i, 2);
        } 
        i = i + 1;
    }

    i = 0;
    let mut sum: u32 = 0;
	
    while (i < N as usize)
        invariant 
            a.len() == old(a).len(),
            forall|k:int| 0 <= k < a.len() ==> a[k] == old(a)[k]
    {
        sum = sum + a[i];
        i = i + 1;
    }

    sum
}
}


// sum == seq(a)[0..N as usize].sum(),
//   not a function: seq

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False