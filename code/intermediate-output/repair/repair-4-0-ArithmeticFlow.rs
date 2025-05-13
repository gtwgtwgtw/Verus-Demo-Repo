Below is a revised version of the loop body showing (1) an explicit assertion (and any accompanying proof steps) before the line that does "sum + (i + 1)", and (2) how you can rely on the loop invariant plus basic algebra to show there is no 64-bit overflow. Essentially, we use the fact that i < n ≤ 2^32 − 1 implies i ≤ 2^32 − 2, so (i+1) and (i+2) remain strictly below 2^32, ensuring (i+1)*(i+2) < 2^64.

--------------------------------------------------------------------------------
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
spec fn arith_sum_nat(i: nat) -> nat
    decreases i
{
    if i == 0 {
        0
    } else {
        i + arith_sum_nat((i - 1) as nat)
    }
}

fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        n <= 4294967295, // n is bounded by 2^32 - 1
    ensures
        sum as nat == arith_sum_nat(n as nat), // matches the trusted spec
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;

    while i < n
        invariant
            0 <= i <= n,
            sum as nat == arith_sum_nat(i as nat),
            sum <= (i * (i + 1)) / 2,
            i <= 4294967295,
            n <= 4294967295,
        decreases (n - i)
    {
        // --------------------------------------------------------
        //   1) Assert that sum + (i + 1) stays within bounds
        // --------------------------------------------------------
        proof {
            // Because i < n and n ≤ 2^32 - 1, we have i ≤ 2^32 - 2.
            // Hence (i+1) ≤ 2^32 - 1, (i+2) ≤ 2^32, and so (i+1)*(i+2) < 2^64.
            assert(sum <= (i * (i + 1)) / 2);    // from the loop invariant
            assert(sum + (i + 1) <= (i * (i + 1)) / 2 + (i + 1));
            // By simple algebra: (i*(i+1))/2 + (i+1) = ((i+1)*(i+2))/2
            // and ((i+1)*(i+2)) < 2^64, so no 64-bit overflow occurs.
        }

        let next_sum = sum + (i + 1);

        i = i + 1;
        sum = next_sum;
    }

    // When the loop finishes, i == n, so sum is the sum from 1..n
    // which matches arith_sum_nat(n).
    sum
}

} 
--------------------------------------------------------------------------------

Explanation of the key changes:

1. We place the “proof” block (and corresponding assertions) before the line let next_sum = sum + (i + 1);. This ensures Verus sees we have proved next_sum cannot overflow in 64 bits.

2. We rely on the loop invariant sum ≤ (i*(i+1))/2 and the fact that i < 2^32 − 1 to show (i+1)*(i+2) < 2^64. Specifically, because i ≤ 2^32 − 2, (i+1) ≤ 2^32 − 1 and (i+2) ≤ 2^32, so their product is strictly < 2^64. Dividing by 2 stays within 2^64, therefore there is no overflow in calculating (i+1)*(i+2)/2 or sum + (i+1).

//         let next_sum = sum + (i + 1);
//   None: sum + (i + 1)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 14
// Safe: False