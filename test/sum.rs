/* arith_sum_int returns the sum of the integers from 1 through i using recursion. compute_arith_sum iteratively computes this sum for a given n. */

#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

spec fn arith_sum_int(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { i + arith_sum_int( (i - 1) as nat) }
}

fn compute_arith_sum(n: u64) -> (sum: u64)
// [Add Requires Clauses Here]
// [Add Ensures Clauses Here]

{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;
    while i < n
    {
        i = i + 1;
        sum = sum + i;
    }
    sum
}


} // verus!
