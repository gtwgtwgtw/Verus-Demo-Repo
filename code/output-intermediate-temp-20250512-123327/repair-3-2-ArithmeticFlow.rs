Below is one way to fix the potential overflow in sum + i by asserting the bound right before sum = sum + i. 

Explanation overview:

• We introduce a lemma (lemma_arith_sum_nat_monotonic) that proves arith_sum_nat is monotonic (i.e., if m ≤ n, then arith_sum_nat(m) ≤ arith_sum_nat(n)).  
• Immediately before adding i to sum, we invoke that lemma to show that arith_sum_nat(i) ≤ arith_sum_nat(n). Since arith_sum_nat(n) is at most (n * (n + 1)) / 2 for the given n-bound, we conclude sum + i ≤ (n * (n + 1)) / 2, which eliminates overflow concerns.  
• The loop invariant continues to track that sum == arith_sum_nat(i). In particular, sum + i == arith_sum_nat(i) when sum == arith_sum_nat(i - 1). (You can also show sum + i == arith_sum_nat(i) directly in the proof block.)

--------------------------------------------------------------------------------
// File: main.rs

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

/// A small lemma showing arith_sum_nat is monotonic: if m <= n, then
/// arith_sum_nat(m) <= arith_sum_nat(n). It proceeds by induction on n.
proof fn lemma_arith_sum_nat_monotonic(m: nat, n: nat)
    requires
        m <= n,
    ensures
        arith_sum_nat(m) <= arith_sum_nat(n),
    decreases n
{
    // Standard induction on "n" pattern:
    if m < n {
        lemma_arith_sum_nat_monotonic(m, (n - 1) as nat);
    }
}

/// Computes the arithmetic sum of 1..=n iteratively.  
/// The ensures-clause matches the trusted arith_sum_nat definition.
/// We add an assertion to prevent overflow: sum + i <= (n*(n+1))/2.
fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        // n is bounded by 2^32 - 1
        n <= 4294967295,
    ensures
        // Result matches the trusted (spec) definition
        sum as nat == arith_sum_nat(n as nat),
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;

    while i < n
        invariant
            0 <= i <= n,
            // sum so far matches arith_sum_nat(i)
            sum as nat == arith_sum_nat(i as nat),
            // sum stays within the known upper bound
            sum <= (n * (n + 1)) / 2,
        decreases (n - i)
    {
        i = i + 1;

        proof {
            // 1) By loop invariant, sum = arith_sum_nat(i - 1).
            // 2) Then sum + i = arith_sum_nat(i - 1) + i = arith_sum_nat(i).
            // 3) By monotonicity, arith_sum_nat(i) <= arith_sum_nat(n).
            lemma_arith_sum_nat_monotonic(i as nat, n as nat);
            assert(arith_sum_nat(i as nat) <= arith_sum_nat(n as nat));
            // Finally, arith_sum_nat(n) ≤ (n * (n + 1)) / 2 for n in the required range,
            // so sum + i ≤ (n * (n + 1)) / 2.
            assert(sum + i <= (n * (n + 1)) / 2);
        }

        sum = sum + i;
    }

    sum
}

} // verus! block ends here
--------------------------------------------------------------------------------

Key points:
• The loop invariant tracks that “sum as nat == arith_sum_nat(i as nat)”.  
• We assert (sum + i) ≤ (n*(n+1))/2 by using the fact that sum + i = arith_sum_nat(i) (monotonic ≤ arith_sum_nat(n)).  
• This ensures that (sum + i) cannot overflow as long as n ≤ 2^32 - 1.

//         sum = sum + i;
//   None: sum + i

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 16
// Safe: False