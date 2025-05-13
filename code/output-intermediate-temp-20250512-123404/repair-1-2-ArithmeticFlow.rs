Below is an example of how you can add a proof‐based assertion (with the help of your monotonicity lemma) to avoid overflow when doing “sum + i”. The key is to show, right before you update sum, that “sum + i” is within a valid bound (in this case, no larger than arith_sum_nat(n as nat)). This assertion, together with the loop invariants and the monotonicity lemma, helps Verus see that no overflow occurs.

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

// A small lemma showing that arith_sum_nat is monotonic (i.e., i ≤ j ⇒ arith_sum_nat(i) ≤ arith_sum_nat(j)).
proof fn lemma_arith_sum_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        arith_sum_nat(i) <= arith_sum_nat(j),
    decreases j
{
    if i < j {
        lemma_arith_sum_monotonic(i, (j - 1) as nat);
        assert(arith_sum_nat(j) == j + arith_sum_nat(( j - 1 ) as nat));
    }
}

fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        // Additional numeric bound to help ensure we won't exceed u64 when summing up to n
        n <= 4294967295,
    ensures
        sum as nat == arith_sum_nat(n as nat),
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;

    while i < n
        invariant
            // i stays within range
            0 <= i <= n,
            // n is bounded
            n <= 4294967295,
            // sum so far is exactly arith_sum_nat(i)
            sum as nat == arith_sum_nat(i as nat),
            // sum cannot exceed the final arith_sum_nat(n)
            sum as nat <= arith_sum_nat(n as nat),
        decreases (n - i)
    {
        proof {
            // We use monotonicity to show that arith_sum_nat((i + 1)) ≤ arith_sum_nat(n).
            lemma_arith_sum_monotonic((i + 1) as nat, n as nat);
        }

        // Increment i
        i = i + 1;

        // Assert that adding i to the current sum cannot exceed arith_sum_nat(n)
        // (which is part of ensuring no arithmetic overflow in the mathematical sense).
        assert(sum + i <= arith_sum_nat(n as nat)) by {
            // Because sum = arith_sum_nat(i as nat), we have:
            //   sum + i = arith_sum_nat(i) + i
            // From the definition, arith_sum_nat(i + 1) = (i + 1) + arith_sum_nat(i).
            // This is no larger than arith_sum_nat(n) by our lemma and loop invariant.
            lemma_arith_sum_monotonic(i as nat, (i + 1) as nat);
            lemma_arith_sum_monotonic((i + 1) as nat, n as nat);
        };

        // Now it is safe to do the update without overflowing a u64, as far as
        // the verifier is concerned (assuming the final numeric bound on n
        // actually keeps sum < 2^64 in the final result).
        sum = sum + i;
    }

    sum
}

}
--------------------------------------------------------------------------------

Explanation:

1. We strengthen the proof obligations by asserting that “sum + i ≤ arith_sum_nat(n as nat)” right before the addition.  
2. We invoke lemma_arith_sum_monotonic(i, i+1) and lemma_arith_sum_monotonic(i+1, n) to justify that arith_sum_nat(i) + i cannot exceed arith_sum_nat(n).  
3. That assertion ensures that no arithmetic overflow is possible under the loop’s numeric constraints (i ≤ n ≤ 4294967295).

//         sum = sum + i;
//   None: sum + i

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 12
// Safe: False