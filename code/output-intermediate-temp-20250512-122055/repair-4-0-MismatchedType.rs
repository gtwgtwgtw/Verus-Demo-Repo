/*[Returns the sum of integers from 1 to n (the triangular number). Includes both a simple recursive definition and a tail‐recursive implementation that accumulates the result.*/
// [FAILED]

/*[Returns the sum of integers from 1 to n (the triangular number). Includes both a simple recursive definition and a tail‐recursive implementation that accumulates the result.*/
/*[Returns the sum of integers from 1 to n (the triangular number). Includes both a simple recursive definition
  and a tail‐recursive implementation that accumulates the result.]*/
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
// [Trusted]
spec fn triangle(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        n + triangle(( n - 1 ) as nat)
    }
}

fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
    requires
        idx as nat <= n as nat,
        old(( sum@ ) as &mut _) + (triangle(n as nat) - triangle(idx as nat)) <= u32::MAX as nat,
    ensures
        sum@ == old(( sum@ ) as &mut _) + (triangle(n as nat) - triangle(idx as nat))
{
    if idx < n {
        let idx_new = idx + 1;
        *sum = *sum + idx_new;
        tail_triangle(n, idx_new, sum);
    }
}

}
// Score: (0, 5)
// Safe: True




//         n + triangle(n - 1)
//   expected `nat`, found `int`: n - 1
//   arguments to this function are incorrect: triangle

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False