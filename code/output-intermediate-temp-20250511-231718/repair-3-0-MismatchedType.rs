/* arith_sum_int returns the sum of the integers from 1 through i using recursion. compute_arith_sum iteratively computes this sum for a given n. */
// [FAILED]

/* arith_sum_int returns the sum of the integers from 1 through i using recursion. compute_arith_sum iteratively computes this sum for a given n. */

#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

// [Trusted]
spec fn arith_sum_nat(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { i + arith_sum_nat( (i - 1) as nat) }
}

fn compute_arith_sum(n: u64) -> (sum: u64)
requires
n <= 4294967295
ensures
sum == arith_sum_nat(( n ) as nat)

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
// Score: (0, 1)
// Safe: True


// sum == arith_sum_nat(n)
//   expected `nat`, found `u64`: n
//   arguments to this function are incorrect: arith_sum_nat

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False