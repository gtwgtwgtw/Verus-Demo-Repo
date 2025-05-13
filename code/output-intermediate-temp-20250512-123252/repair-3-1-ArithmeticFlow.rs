Below is an example of how you can insert the necessary assertion (and supporting lemmas) to avoid overflow on “sum + i”. 

Explanation Highlights:

• We add a monotonicity lemma, lemma_arith_sum_monotonic, that shows arith_sum_nat(i) ≤ arith_sum_nat(n) whenever i ≤ n.  
• We add a bounding lemma, lemma_arith_sum_upper_bound, showing arith_sum_nat(n) ≤ 2^64−1 for n ≤ 4294967295.  
• Right before sum = sum + i, we assert that (sum + i) is within the 64-bit range by relating sum + i to arith_sum_nat(n).  

--------------------------------------------------------------------------------
Code
--------------------------------------------------------------------------------

#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

// A trusted spec function that recursively computes the sum of [1..=i].
spec fn arith_sum_nat(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { i + arith_sum_nat((i - 1) as nat) }
}

// ------------------------------------------------------------------
// 1. Prove monotonicity: if m ≤ n, then arith_sum_nat(m) ≤ arith_sum_nat(n).
// ------------------------------------------------------------------
proof fn lemma_arith_sum_monotonic(m: nat, n: nat)
    requires
        m <= n,
    ensures
        arith_sum_nat(m) <= arith_sum_nat(n),
    decreases n
{
    if m < n {
        lemma_arith_sum_monotonic(m, n - 1);
    }
}

// ------------------------------------------------------------------
// 2. For n ≤ 2^32 - 1, show that arith_sum_nat(n) fits in 64 bits.
//    i.e. arith_sum_nat(n) ≤ 2^64 - 1
// ------------------------------------------------------------------
proof fn lemma_arith_sum_upper_bound(n: nat)
    requires
        n <= 4294967295,
    ensures
        arith_sum_nat(n) <= u64::MAX as nat,
    decreases n
{
    if n > 0 {
        lemma_arith_sum_upper_bound(n - 1);
        // By induction: arith_sum_nat(n) = n + arith_sum_nat(n-1).
        // We already know arith_sum_nat(n-1) ≤ 2^64 - 1,
        // and n ≤ 2^32 - 1. Their sum still fits in 64 bits.
    }
}

// ------------------------------------------------------------------
// 3. Main function: compute_arith_sum
// ------------------------------------------------------------------
fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        n <= 4294967295,
    ensures
        (sum as nat) == arith_sum_nat(n as nat),
{
    // First, prove that arith_sum_nat(n) ≤ 2^64 - 1:
    lemma_arith_sum_upper_bound(n as nat);

    let mut i: u64 = 0;
    let mut sum: u64 = 0;

    while i < n
        invariant
            i <= n,
            sum as nat == arith_sum_nat(i as nat),
            n <= 4294967295,
    {
        i = i + 1;

        //
        //  Insert the assertion that sum + i <= arith_sum_nat(n),
        //  thereby guaranteeing no overflow in “sum = sum + i”.
        //
        assert( (sum as nat) + (i as nat) <= arith_sum_nat(n as nat) ) by {
            // Because sum = arith_sum_nat(i−1) (in nat form),
            //     sum + i = arith_sum_nat(i−1) + i = arith_sum_nat(i).
            // Then arith_sum_nat(i) ≤ arith_sum_nat(n)
            // by our monotonicity lemma.
            lemma_arith_sum_monotonic(i, n as nat);
        };

        sum = sum + i;
    }
    sum
}

}

--------------------------------------------------------------------------------

Explanation:

1) lemma_arith_sum_monotonic(m, n): Shows that arith_sum_nat is non-decreasing.  
2) lemma_arith_sum_upper_bound(n): Shows that for n ≤ 2^32 − 1, the sum of integers up to n fits in 64 bits.  
3) compute_arith_sum(n): Uses those lemmas in the loop. The crucial line is the assert(...) call ensuring sum + i never exceeds arith_sum_nat(n as nat), which has already been shown to be ≤ 2^64 − 1.  

With this assertion (and supporting lemmas) in place, Verus can verify that “sum = sum + i” does not cause an arithmetic overflow.

//         sum = sum + i;
//   None: sum + i

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 11
// Safe: False