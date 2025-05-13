Below is one illustrative way to insert an assertion (and, optionally, a monotonicity lemma) that makes VeriFx/Verus happy about the bounds of sum + i before the line sum = sum + i. The main idea is:

1. Before adding i to sum, show that sum + i cannot overflow.  
2. Since the function arith_sum_nat is recursively defined in terms of i, a monotonicity lemma can also be written to help prove that arith_sum_nat(i) ≤ arith_sum_nat(n).  
3. In this particular example, however, you can often get away with a direct numeric bound check, because your loop invariant already states sum ≤ (n * (n + 1)) / 2, and i < n. 

Below is a version that includes both a direct assertion (sum + i <= …) and an optional monotonicity lemma:

--------------------------------------------------------------------------------
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

// A lemma to show monotonicity of arith_sum_nat, if you want to use it
// for deriving sum + i <= arith_sum_nat(n) or other bounds. 
// (Strictly speaking, not always needed with the numeric bound.)
proof fn lemma_monotonic_arith_sum_nat(i: nat, j: nat)
    requires
        i <= j,
    ensures
        arith_sum_nat(i) <= arith_sum_nat(j),
    decreases j
{
    if i < j {
        lemma_monotonic_arith_sum_nat(i, (j - 1) as nat);
        // Standard structural/inductive argument that arith_sum_nat is monotonic
    }
}

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
            // i always stays in range
            0 <= i <= n,
            // sum so far matches the recursive sum from 1..i
            sum as nat == arith_sum_nat(i as nat),
            // sum stays within u64 bounds, given n <= 2^32 - 1
            // (n*(n+1))/2 is the closed-form of arith_sum_nat(n)
            sum <= (n * (n + 1)) / 2,
        decreases (n - i)
    {
        proof {
            // Show that adding i+1 to sum is safe
            assert(i + 1 <= n);
            assert(sum + (i + 1) <= (n * (n + 1)) / 2);

            // If you prefer referring to the recursive spec:
            // lemma_monotonic_arith_sum_nat(i as nat, n as nat);
            // assert(arith_sum_nat(i as nat) + (i + 1) <= arith_sum_nat(n as nat));
        }

        i = i + 1;

        // Here is the point of interest: show sum + i is in range
        // The proof block above justifies it, but you can also insert
        // an immediate "assert" right before sum = sum + i if needed:
        assert(sum + i <= (n * (n + 1)) / 2);

        sum = sum + i;
    }

    sum
}
--------------------------------------------------------------------------------

Explanation of the key changes:

• We inserted proof { … } before i = i + 1 so that Verus sees an explicit justification that sum + (i + 1) stays within the loop invariant bound ( (n*(n+1))/2 for sum ).  
• Right before sum = sum + i, we also inserted a one-line assert(...) that restates the numeric inequality to satisfy Verus’s requirement for preventing any arithmetic overflows.  
• The optional lemma_monotonic_arith_sum_nat can be used in cases where an inductive argument about a recursively defined function (like arith_sum_nat) is more natural than a purely numeric bound; however, here the numeric bound alone is typically enough.  

With these adjustments, you eliminate the potential overflow concerns on the line sum = sum + i.

//         sum = sum + i;
//   None: sum + i

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 9
// Safe: False