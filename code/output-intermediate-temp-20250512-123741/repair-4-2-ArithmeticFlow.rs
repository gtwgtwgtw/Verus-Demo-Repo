Below is one illustrative way to insert a proof‐side assertion (and, if desired, a monotonicity lemma) to prevent the verifier from complaining about possible overflow when computing “sum + (i + 1)”. The example shows both:

• How to assert explicitly that sum + (i + 1) stays within safe numeric bounds, using the loop invariant and basic arithmetic.  
• How to incorporate a “monotonicity lemma” on the recursive spec function (arith_sum_nat) if you want to show that sum + (i + 1) is ≤ arith_sum_nat(n) (which itself is bounded by 2^64 for n ≤ 2^32–1).

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
        i + arith_sum_nat(i - 1)
    }
}

// Optional: If you want to show that arith_sum_nat is monotonic 
proof fn lemma_arith_sum_nat_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        arith_sum_nat(i) <= arith_sum_nat(j),
    decreases j
{
    if i < j {
        lemma_arith_sum_nat_monotonic(i, j - 1);
        // from i <= j - 1 we have arith_sum_nat(i) ≤ arith_sum_nat(j - 1)
        // from j - 1 < j we know arith_sum_nat(j - 1) ≤ arith_sum_nat(j)
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
            0 <= i <= n,                               // i stays in valid range
            sum as nat == arith_sum_nat(i as nat),     // sum so far matches the spec function
            sum <= (i * (i + 1)) / 2,                  // sum is within the standard closed form for 1 + 2 + ... + i
            i <= 4294967295,                           // i remains below 2^32
            n <= 4294967295,                           // n is bounded by 2^32 - 1
        decreases (n - i)
    {
        // ---------------------------------------------------------------
        // 1) (Optional) Show sum + (i + 1) is still within the recursive spec’s upper bound:
        proof {
            lemma_arith_sum_nat_monotonic(i as nat, n as nat);
            // We know sum == arith_sum_nat(i),
            // so sum + (i + 1) = arith_sum_nat(i) + (i + 1) = arith_sum_nat(i + 1).
            // Because i < n, we get i + 1 <= n, so arith_sum_nat(i + 1) <= arith_sum_nat(n).
            // That implies sum + (i + 1) <= arith_sum_nat(n).
        }
        // ---------------------------------------------------------------
        // 2) Also show that no arithmetic overflow occurs in 64-bit, using the loop invariant:
        proof {
            assert(sum <= (i * (i + 1)) / 2);                   // from invariant
            assert(sum + (i + 1) <= (i * (i + 1)) / 2 + (i + 1));
            // arith: (i*(i + 1))/2 + (i + 1) = ((i + 1)*(i + 2))/2
            // and for i < 2^32, (i + 1)*(i + 2) < 2^64, so no overflow in sum + (i + 1).
        }
        // ---------------------------------------------------------------
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

1) Just before let next_sum = sum + (i + 1), we have two proof blocks:

   • (Optional) Monotonicity argument: By calling lemma_arith_sum_nat_monotonic(i, n), we show arith_sum_nat(i) ≤ arith_sum_nat(n). Since sum == arith_sum_nat(i) (per the loop invariant) and i + 1 ≤ n, we conclude sum + (i + 1) = arith_sum_nat(i + 1) ≤ arith_sum_nat(n).  
   • Arithmetic bound argument: We also show that sum + (i + 1) does not exceed 2^64 by leveraging the loop invariant sum ≤ i*(i+1)/2. A little algebra shows sum + (i + 1) ≤ ((i+1)*(i+2))/2, which remains within 64‐bit bounds when i ≤ 2^32–1.

2) Putting these pieces together assures Verus that the addition sum + (i + 1) is safe against both underflow (trivially not < 0) and overflow (within 64 bits), plus it remains consistent with the recursively defined specification arith_sum_nat.

//         let next_sum = sum + (i + 1);
//   None: sum + (i + 1)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 11
// Safe: False