
/* Adds 4 to each element of the vector in place, preserving its length. */

use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
pub fn myfun2(x: &mut Vec<i32>) 
requires
    true
ensures
    x.len() == old(x).len(),
    forall |i: usize| 0 <= i && i < x.len() ==> x[( i ) as int] == old(x[( i ) as &mut _) + 4
{
    let mut i: usize = 0;
    let xlen: usize = x.len();
    while i < xlen 
    invariant
        0 <= i <= xlen,
        x.len() == old(x).len(),
        forall |j: usize| 0 <= j && j < i ==> x[j] == old(x[j]) + 4
    { 
        x.set(i, x[i] + 4);  
        i = i + 1;
    }  
}

}





// `forall|i: usize| 0 <= i && i < x.len() ==> x[i] == old(x[i]) + 4`
//   None: `

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False