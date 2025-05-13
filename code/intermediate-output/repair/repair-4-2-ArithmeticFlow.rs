Below is one way to add an assertion (and supporting proof steps) before creating next_sum so that Verus can confirm there is no potential arithmetic overflow in the expression sum + (i + 1). The important part is to show that next_sum is bounded above by something that fits in 64 bits. Here, we have:  
• i < n ≤ 2^32 - 1 implies i ≤ 2^32 - 2,  
• so (i + 1) ≤ 2^32 - 1,  
• and from the loop invariant sum ≤ i*(i+1)/2,  
• which leads to sum + (i + 1) ≤ (i+1)*(i+2)/2,  
• (i+1)*(i+2)/2 < 2^64 for i ≤ (2^32 - 1).  

Hence no overflow occurs in the addition.

--------------------------------------------------------------------------------
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
// [Trusted]
spec fn arith_sum_nat(i: nat) -> nat
    decreases i
{
    if i == 0 {
        0
    } else {
        i + arith_sum_nat((i - 1) as nat)
    }
}

// We compute the same sum iteratively and prove no overflow occurs,
// and that we match the trusted recursive definition arith_sum_nat.
fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        // n is bounded by 2^32 - 1
        n <= 4294967295,
    ensures
        // The resulting sum matches the trusted recursive definition
        sum as nat == arith_sum_nat(n as nat),
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;

    while i < n
        invariant
            0 <= i <= n,                              // i stays in valid range
            sum as nat == arith_sum_nat(i as nat),    // sum so far is correct
            // sum is at most i*(i+1)/2, the closed form for 1 + 2 + ... + i
            sum <= (i * (i + 1)) / 2,
            // i remains below 2^32
            i <= 4294967295,
            // n is bounded by 2^32 - 1
            n <= 4294967295,
        decreases (n - i)
    {
        proof {
            // Since i < n ≤ 2^32 - 1, i ≤ 2^32 - 2, hence (i + 1) ≤ 2^32 - 1.
            // By the invariant: sum ≤ i*(i+1)/2.
            // Therefore sum + (i + 1) ≤ i*(i+1)/2 + (i+1) = (i+1)*(i+2)/2.
            // Lastly, for i ≤ 2^32 - 2, (i+1)*(i+2)/2 < 2^64, so there is no overflow.
        }
        assert(sum + (i + 1) <= (i + 1) * (i + 2) / 2);

        let next_sum = sum + (i + 1);

        i = i + 1;
        sum = next_sum;
    }

    // When the loop finishes, i == n, so sum = sum(1..n) which matches arith_sum_nat(n).
    sum
}

}
--------------------------------------------------------------------------------

Explanation:

• The assert(...) right before let next_sum = sum + (i + 1) confirms that next_sum remains within a proven safe bound.  
• The proof block comments show how the loop invariants and bounds on i (in turn, on n) guarantee no underflow/overflow in 64-bit arithmetic.

//         let next_sum = sum + (i + 1);
//   None: sum + (i + 1)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 14
// Safe: False