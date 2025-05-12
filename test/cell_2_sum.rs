/*
Caps each element of `a` at 2 for the first `N` entries and then computes the sum of these possibly reduced values. 
Returns the total sum of the capped elements.
*/

use vstd::prelude::*;
fn main() {}
verus!{

pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
// [Add Requires Clauses Here]
// [Add Ensures Clauses Here]
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
