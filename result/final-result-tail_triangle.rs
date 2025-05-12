/*[Returns the sum of integers from 1 to n (the triangular number). Includes both a simple recursive definition and a tail‐recursive implementation that accumulates the result.*/
// [FAILED]

/*[Returns the sum of integers from 1 to n (the triangular number). Includes both a simple recursive definition and a tail‐recursive implementation that accumulates the result.*/

//This is an example from Verus tutorial Chpt 4.2
//This is a rather complicated example

use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
     
spec fn triangle(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        n + triangle((n - 1) as nat)
    }
}

fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
requires
idx <= n,
*sum == triangle(idx) as u32
ensures
*sum == triangle(n) as u32

{
    if idx < n {
        let idx = idx + 1;
        *sum = *sum + idx;
        tail_triangle(n, idx, sum);
    }
}
}
// Score: (0, 2)
// Safe: True