/* Adds 4 to each element of the vector in place, preserving its length. */

use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun2(x: &mut Vec<i32>) 
// [Add Requires Clauses Here]
// [Add Ensures Clauses Here]

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
