Below is one way to add an assertion (using the existing monotonicity lemma) so that Verus can confirm that “sum + i” does not overflow. The main idea is:

• Right after you increment i (i = i + 1) and before sum = sum + i, prove that sum + i ≤ arith_sum_nat(n) (which is already known to fit into a u64).  
• We rely on the loop invariant sum as nat == arith_sum_nat(i as nat) (before increment) and the fact that arith_sum_nat is monotonic to show sum + i will stay within bounds.

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
        i + arith_sum_nat(( i - 1 ) as nat)
    }
}

// Monotonicity lemma (already defined):
proof fn lemma_arith_sum_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        arith_sum_nat(i) <= arith_sum_nat(j),
    decreases j
{
    if i < j {
        lemma_arith_sum_monotonic(i, (j - 1) as nat);
        assert(arith_sum_nat(j) == j + arith_sum_nat((j - 1) as nat));
    }
}

fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        // Ensures n is not so large that the sum won't fit into a u64.
        n <= 4294967295,
    ensures
        sum as nat == arith_sum_nat(n as nat),
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;

    while i < n
        invariant
            0 <= i <= n,
            n <= 4294967295,
            // sum exactly matches arith_sum_nat(i)
            sum as nat == arith_sum_nat(i as nat),
            // and never exceeds arith_sum_nat(n)
            sum as nat <= arith_sum_nat(n as nat),
        decreases (n - i)
    {
        proof {
            // ( i + 1 ) ≤ n  ==>  arith_sum_nat(i + 1) ≤ arith_sum_nat(n )
            lemma_arith_sum_monotonic((i + 1) as nat, n as nat);
        }

        i = i + 1;

        // -------------------------------------
        // Assertion to prevent overflow:
        // sum (which equals arith_sum_nat(i - 1)) + i ≤ arith_sum_nat(n).
        // -------------------------------------
        assert(sum as nat + i as nat <= arith_sum_nat(n as nat)) by {
            assert(sum as nat == arith_sum_nat((i - 1) as nat));
            // arith_sum_nat(i) = i + arith_sum_nat(i - 1)
            assert(arith_sum_nat(i as nat) == i as nat + arith_sum_nat((i - 1) as nat));
            // So (sum + i) = arith_sum_nat(i)
            // and arith_sum_nat(i) ≤ arith_sum_nat(n) by monotonicity.
        };

        sum = sum + i;
    }

    sum
}

}
--------------------------------------------------------------------------------

Explanation:

• Right after i is incremented, “sum” is still arith_sum_nat(i−1). Hence, (sum + i) = arith_sum_nat(i−1) + i.  
• By definition, arith_sum_nat(i) = i + arith_sum_nat(i−1). So sum + i = arith_sum_nat(i).  
• Because i ≤ n in the loop, arith_sum_nat(i) ≤ arith_sum_nat(n) (due to lemma_arith_sum_monotonic).  
• Therefore, sum + i ≤ arith_sum_nat(n), which in turn is ≤ 2^64 − 1 given n ≤ 2^32 − 1, so no overflow occurs.

//         sum = sum + i;
//   None: sum + i

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 22
// Safe: False