/* Adds 4 to each element of the vector in place, preserving its length. */

use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]

pub fn myfun2(x: &mut Vec<i32>) 
requires
    true
ensures
    // The final length is equal to the original length.
    x.len() == old(x).len(),
    // Every element now is 4 greater than it was initially.
    forall |i: usize| 0 <= i < old(x).len() ==> x[( i ) as int] == old(x)[( i ) as int] + 4
{
    // We use 'old(x)' in the specification to refer to the state of x at function entry.
    let mut i: usize = 0;
    // The loop iterates over the original length of x.
    while i < x.len()
    invariant
        // The index i never exceeds the original length.
        i <= old(x).len(),
        // The length of the vector remains constant.
        x.len() == old(x).len(),
        // For every index processed so far, the element has been increased by 4.
        forall |j: usize| 0 <= j && j < i ==> x[( j ) as int] == old(x)[( j ) as int] + 4,
    {
        x.set(i, x[i] + 4);  
        i = i + 1;
    }  
}
}





//     forall |i: usize| 0 <= i < old(x).len() ==> x[i] == old(x)[i] + 4
//   expected `int`, found `usize`: i
//   arguments to this method are incorrect: x[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False