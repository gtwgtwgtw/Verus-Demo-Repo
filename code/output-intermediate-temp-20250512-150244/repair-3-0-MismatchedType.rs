/* Iterates through `x` and appends each element divisible by 3 into the initially empty vector `y`, preserving their order. */
// [FAILED]

/* Iterates through `x` and appends each element divisible by 3 into the initially empty vector `y`, preserving their order. */

use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    requires
        y@.len() == 0
    ensures
        // Every element of y is divisible by 3:
        forall|i: nat| i < y@.len() ==> y@[( i ) as int] % 3 == 0,
        // Every element of x divisible by 3 is present in y:
        forall|i: nat| i < x@.len() && x@[( i ) as int] % 3 == 0
            ==> exists|j: nat| j < y@.len() && y@[( j ) as int] == x@[( i ) as int],
        // The order of elements taken from x is preserved in y:
        forall|j1, j2: nat| j1 < j2 < y@.len() ==>
            exists|i1, i2: nat| i1 < i2 < x@.len() 
                && x@[i1] == y@[j1] 
                && x@[( i2 ) as int] == y@[( j2 ) as int]
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
// Score: (0, 6)
// Safe: True







//         forall|i: nat| i < y@.len() ==> y@[i] % 3 == 0,
//   expected `int`, found `nat`: i
//   arguments to this method are incorrect: y@[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False