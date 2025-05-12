/*
Caps each element of `a` at 2 for the first `N` entries and then computes the sum of these possibly reduced values. 
Returns the total sum of the capped elements.
*/
// [FAILED]

/*
Caps each element of `a` at 2 for the first `N` entries and then computes the sum of these possibly reduced values. 
Returns the total sum of the capped elements.
*/

use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
requires
N <= a.len() as u32
ensures
forall |i: usize| i < N as usize ==> a[i] == if old(a)[i] > 2 { 2 } else { old(a)[i] },
forall |i: usize| N as usize <= i && i < a.len() ==> a[i] == old(a)[i],
sum == (0..N as usize).fold(0u32, |acc: u32, i| acc + (if old(a)[i] > 2 { 2 } else { old(a)[i] }))
{
    let mut i: usize = 0;
    while (i < N as usize)
    {
	if a[i] > 2 
        {
	    a.set(i, 2);
	} 
	i = i + 1;
    }

    i = 0;
    let mut sum: u32 = 0;
	
    while (i < N as usize)
    {
        sum = sum + a[i];
	i = i + 1;
    }

    sum
}
}
// Score: (0, 6)
// Safe: True