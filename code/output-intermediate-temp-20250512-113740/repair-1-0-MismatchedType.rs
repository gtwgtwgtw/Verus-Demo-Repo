/* Generates a Vec<i32> of length n containing the Fibonacci sequence starting with 0 and 1. Each element beyond the first two is the sum of the two preceding elements. */
// [FAILED]

/* Generates a Vec<i32> of length n containing the Fibonacci sequence starting with 0 and 1. Each element beyond the first two is the sum of the two preceding elements. */
/* Generates a Vec<i32> of length n containing the Fibonacci sequence starting with 0 and 1.
   Each element beyond the first two is the sum of the two preceding elements. */

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

// [Trusted]
spec fn fibo_fits_i32(n: int) -> bool {
    fibo(n) < 0x8000_0000
}

fn fibonacci(n: usize) -> (ret: Vec<i32>)
    requires
        n >= 2,
        fibo_fits_i32(n - 1)
    ensures
        ret.len() == n,
        // Compare as nat to match fibo's return type (nat).
        forall|i: nat| i < n ==> ret[( i ) as int] as nat == fibo(i as int)
{
    let mut fib = Vec::new();
    fib.push(0);
    fib.push(1);

    let mut i = 2;
    while i < n {
        let next_fib = fib[i - 1] + fib[i - 2];
        fib.push(next_fib);
        i += 1;
    }
    fib
}
}
// Score: (0, 1)
// Safe: True


//         forall|i: nat| i < n ==> ret[i] as nat == fibo(i as int)
//   expected `int`, found `nat`: i
//   arguments to this method are incorrect: ret[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False