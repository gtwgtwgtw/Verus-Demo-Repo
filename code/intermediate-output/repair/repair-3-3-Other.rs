
use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    ensures
        // x is not modified
        x@ == old(( x@ ) as &mut _),
        // y ends up equal to the old y concatenated with exactly those elements of x divisible by 3, in order
        y@ == old(y@) + x@.filter(|v: u64| v % 3 == 0),
{
    let mut i: usize = 0;
    let xlen = x.len();
    
    while i < xlen
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
        i = i + 1;
    }
}
}



//     ensures(x@ == old(x@));
//   None: ensures

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False