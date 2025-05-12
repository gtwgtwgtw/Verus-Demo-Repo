/* Appends to y every element of x that is divisible by 3, preserving their original order. After execution, y contains exactly the multiples of 3 from x. */

use vstd::prelude::*;
fn main() {}

verus!{
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires
true
ensures
y@ == old(y@).append(x@.filter(|e: u64| e % 3 == 0))
{
    let mut i: usize = 0;
    let xlen = x.len();
    
    while (i < xlen) 
    { 
        if (x[i] % 3 == 0) {
            y.push(x[i]);            
        }
        i = i + 1;
    }
}
}
