Below is one way you can insert a proof obligation (assert) right before computing next_fib to convince Verus that the addition does not overflow. The key is to relate fib[i - 1] + fib[i - 2] back to fibo(i) (your recursively defined spec) and use a monotonicity lemma for fibo, together with fibo_fits_i32(n - 1), to show that fibo(i) remains under 2³¹.

--------------------------------------------------------------------------------
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
// [Trusted]
spec fn fibo(n: int) -> nat
    decreases n
{
    if n <= 0 {
        0
    } else if n == 1 {
        1
    } else {
        fibo(n - 2) + fibo(n - 1)
    }
}

// A simple monotonicity lemma for fibo
proof fn lemma_fibo_monotonic(i: int, j: int)
    requires
        0 <= i <= j,
    ensures
        fibo(i) <= fibo(j),
    decreases (j - i)
{
    if i < j {
        lemma_fibo_monotonic(i, j - 1);
        assert(fibo(i) <= fibo(j));
    }
}

// [Trusted]
spec fn fibo_fits_i32(n: int) -> bool {
    // If fibo(n) < 2³¹, it "fits" into an i32 without overflow
    fibo(n) < 0x8000_0000
}

fn fibonacci(n: usize) -> (ret: Vec<i32>)
    requires
        n >= 2,
        fibo_fits_i32(n - 1),  // i.e., fibo(n - 1) < 2^31
    ensures
        ret.len() == n,
        forall|i: nat| i < n ==> ret[i as int] as int == fibo(i as int),
{
    let mut fib = Vec::new();
    fib.push(0);  // fib[0] == fibo(0) == 0
    fib.push(1);  // fib[1] == fibo(1) == 1

    let mut i = 2;
    while i < n
        invariant
            fib.len() == i,
            i >= 2,
            // Optionally, you can strengthen invariants if needed,
            // e.g. <= n, but for the overflow fix we just need the proof below.
    {
        // First, assert that fib[i - 1] + fib[i - 2] == fibo(i) by definition:
        assert(fib[i - 1] as int + fib[i - 2] as int == fibo((i - 1) as int) + fibo((i - 2) as int));
        assert(fib[i - 1] as int + fib[i - 2] as int == fibo(i as int));

        // Next, show fibo(i as int) < 2^31 (so that adding them won't overflow i32).
        assert(fibo(i as int) < 0x8000_0000) by {
            //  1. By lemma_fibo_monotonic, fibo(i) ≤ fibo(n - 1).
            lemma_fibo_monotonic(i as int, (n - 1) as int);
            //  2. We know fibo(n - 1) < 2^31 from fibo_fits_i32(n - 1).
        };

        let next_fib = fib[i - 1] + fib[i - 2];
        fib.push(next_fib);
        i += 1;
    }
    fib
}
--------------------------------------------------------------------------------

Explanation:

1) We define lemma_fibo_monotonic to show fibo(i) ≤ fibo(j) for i ≤ j ≥ 0.  
2) Right before let next_fib = ..., we assert that fib[i - 1] + fib[i - 2] equals fibo(i), then invoke the lemma to show fibo(i) ≤ fibo(n-1) < 2^31.  
3) Because fibo(n-1) < 2^31 by assumption (fibo_fits_i32(n - 1)), we conclude fibo(i) < 2^31 for all i up to n-1. Thus, the addition cannot overflow in a 32-bit signed integer.

//         let next_fib = fib[i - 1] + fib[i - 2];
//   None: fib[i - 1] + fib[i - 2]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False