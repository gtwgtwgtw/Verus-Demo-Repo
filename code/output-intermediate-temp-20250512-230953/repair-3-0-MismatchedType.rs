/* Adds 4 to each element of the vector in place, preserving its length. */
// [FAILED]

/* Adds 4 to each element of the vector in place, preserving its length. */
// [FAILED]

/* Adds 4 to each element of the vector in place, preserving its length. */

use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
pub fn myfun2(x: &mut Vec<i32>) 
requires
forall|i: usize| i < x.len() ==> x[( i ) as int] <= i32::MAX - 4
ensures
x.len() == old(x).len(),
forall|i: usize| i < x.len() ==> x[( i ) as int] == old(x)[( i ) as int] + 4

{
    let mut i: usize = 0;
    let xlen: usize = x.len();
    while (i < xlen) 
    { 
        x.set(i, x[i] + 4);  
        i = i + 1;
    }  
}
}
// Score: (0, 3)
// Safe: True




// forall|i: usize| i < x.len() ==> x[i] <= i32::MAX - 4
//   expected `int`, found `usize`: i
//   arguments to this method are incorrect: x[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False