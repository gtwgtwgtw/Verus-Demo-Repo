Below is one way to eliminate the overflow/underflow complaints by giving the verifier a proof argument that (1) your running sum is always equal to arith_sum_nat(i), and (2) arith_sum_nat(i) ≤ arith_sum_nat(n).  This allows you to assert that (sum + i) will never exceed arith_sum_nat(n), which in turn is within u64-range when n ≤ 4294967295.

--------------------------------------------------------------------------------
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

/// arith_sum_nat returns the sum of the integers from 1 through i (in nat).
spec fn arith_sum_nat(i: nat) -> nat
    decreases i
{
    if i == 0 { 
        0 
    } else { 
        i + arith_sum_nat((i - 1) as nat)
    }
}

/// A simple monotonicity lemma: if i ≤ j, then arith_sum_nat(i) ≤ arith_sum_nat(j).
proof fn lemma_arith_sum_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        arith_sum_nat(i) <= arith_sum_nat(j),
    decreases j
{
    if i < j {
        lemma_arith_sum_monotonic(i, (j - 1) as nat);
    }
}

/// compute_arith_sum iteratively computes the sum 1 + 2 + ... + n.
/// We show that (sum + i) never overflows by asserting it is bounded by arith_sum_nat(n).
fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        n <= 4294967295, // ensures upper bound large enough to keep sum in u64
    ensures
        (sum as nat) == arith_sum_nat(n as nat),
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;
    while i < n
        invariant
            i <= n,
            // Tracking that sum is always exactly the sum of 1..i
            sum == arith_sum_nat(i as nat),
            // Retaining the original requirement in the loop invariant
            n <= 4294967295,
    {
        i = i + 1;

        // Prove that sum + i will not overflow by showing sum + i ≤ arith_sum_nat(n).
        // We know sum == arith_sum_nat(i - 1) from the loop invariant (if i was just incremented),
        // thus sum + i == arith_sum_nat(i). And arith_sum_nat(i) ≤ arith_sum_nat(n) by monotonicity.
        assert(sum + i <= arith_sum_nat(n as nat)) by {
            lemma_arith_sum_monotonic(i as nat, n as nat);
        };

        sum = sum + i;
    }
    sum
}

} 
--------------------------------------------------------------------------------

Key details:
• We added a loop invariant sum == arith_sum_nat(i as nat).  
• We wrote lemma_arith_sum_monotonic(i, j) to help Verus see that arith_sum_nat(i) ≤ arith_sum_nat(j) if i ≤ j.  
• Right before sum = sum + i, we assert that sum + i ≤ arith_sum_nat(n), which forces the prover to check there is no overflow.

//         sum = sum + i;
//   None: sum + i

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 9
// Safe: False