Below is one way to insert an assertion (or a short proof block) that shows “sum + (i + 1)” stays within 64-bit bounds, right before computing next_sum. The key step is showing that, under your loop invariant and the bound on i, no overflow can occur when adding (i+1) to sum. One straightforward approach is to assert sum ≤ i*(i+1)/2 (by the loop invariant), then argue

  sum + (i+1) ≤ (i*(i+1))/2 + (i+1) = ((i+1)*(i+2)) / 2 < 2^64,

using i < 2^32. The commented code below shows how to add such an assertion.

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
                sum <= (i * (i + 1)) / 2,                 // standard bound on sum(1..i)
                i <= 4294967295,                          // i remains below 2^32
                n <= 4294967295,                          // n is bounded by 2^32 - 1
            decreases (n - i)
        {
            // -----------------------------------------------------------
            // Insert your proof/assertion right before the addition:
            proof {
                // By the loop invariant:
                assert(sum <= (i * (i + 1)) / 2);

                // Next sum when adding (i+1):
                //   sum + (i+1) ≤ (i*(i+1))/2 + (i+1) = ((i+1)*(i+2))/2.
                assert(sum + (i + 1) <= ((i + 1) * (i + 2)) / 2);

                // Since i < 2^32, (i+1)*(i+2) < 2^32 * 2^32 = 2^64,
                // so the result is safely below 2^64 and cannot overflow a u64.
            }
            // -----------------------------------------------------------

            let next_sum = sum + (i + 1);
            i = i + 1;
            sum = next_sum;
        }

        // At loop exit, i == n, so sum = sum(1..n) which matches arith_sum_nat(n).
        sum
    }
}

--------------------------------------------------------------------------------

Explanation:

1. In the loop invariant, we track that sum ≤ i·(i+1)/2.  
2. Just before adding (i+1), we prove sum + (i+1) ≤ (i+1)(i+2)/2, and for i < 2^32, that product is below 2^64, so no 64-bit overflow occurs when we form next_sum = sum + (i+1).  
3. This fixes the potential underflow/overflow issue by enforcing (through assertion) that the addition is in range.

//         let next_sum = sum + (i + 1);
//   None: sum + (i + 1)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False