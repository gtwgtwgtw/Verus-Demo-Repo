#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {

/* -------------------------------------------------------------------------
   Trusted spec functions for mathematical Fibonacci reasoning:
   fibo(n) returns the nth Fibonacci number (fibo(0) = 0, fibo(1) = 1),
   fibo_fits_i32(n) proves fibo(n) won't exceed i32::MAX.
------------------------------------------------------------------------- */

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

// [Trusted]
spec fn fibo_fits_i32(n: int) -> bool {
    fibo(n) < 0x8000_0000
}

/* -------------------------------------------------------------------------
   fibonacci(n) constructs a Vec<i32> of length n holding the Fibonacci
   numbers 0..fibo(n-1). We require:
     - n >= 2.
     - fibo_fits_i32(n - 1) so no overflow in computing fib(i).
   Postconditions:
     - The result has length n.
     - Each element matches fibo(i).
------------------------------------------------------------------------- */

fn fibonacci(n: usize) -> (ret: Vec<i32>)
    requires
        n >= 2,
        fibo_fits_i32(n - 1),
    ensures
        ret.len() == n,
        forall|j: nat| j < n ==> ret[j as int] as int == fibo(j as int),
{
    let mut fib = Vec::new();
    fib.push(0);
    fib.push(1);

    let mut i = 2usize;
    while i < n
        invariant
            n >= 2,
            fibo_fits_i32(n - 1),
            2 <= i as int <= n as int,
            fib.len() == i,
            // Each inserted element so far is correct
            forall|k: nat| k < i ==> fib[k as int] as int == fibo(k as int),
        decreases n - i
    {
        // Safe indexing because i >= 2 and fib.len() == i
        assert(i - 1 < fib.len());
        assert(i - 2 < fib.len());

        let next_fib = fib[i - 1] + fib[i - 2];

        // Prove that next_fib matches fibo(i)
        assert(next_fib as int == fib[i - 1] as int + fib[i - 2] as int);
        // From the invariant, these match fibo(i-1) and fibo(i-2) in spec
        assert(fib[i - 1] as int == fibo((i - 1) as int));
        assert(fib[i - 2] as int == fibo((i - 2) as int));
        reveal(fibo);
        assert(next_fib as int == fibo(i as int - 1) + fibo(i as int - 2));
        assert(next_fib as int == fibo(i as int));

        // Also show next_fib will not overflow i32, given fibo_fits_i32(n - 1) and i < n
        assert(fibo(i as int) <= fibo(n as int - 1));
        assert(fibo(n as int - 1) < 0x8000_0000);
        assert(next_fib >= 0 && next_fib < 0x8000_0000);

        fib.push(next_fib);
        i += 1;

        // Now fib.len() = old fib.len() + 1 = old i + 1 = new i
        assert(fib.len() == i);
    }

    fib
}

}

// Score: (0, 1)
// Safe: False

// // Safe: False
// verus! {
//   unclosed delimiter: {
//   None: 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False