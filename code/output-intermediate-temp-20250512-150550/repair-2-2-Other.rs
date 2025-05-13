use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
        requires
            old(y)@.len() == 0
        ensures
            forall |i: int| 0 <= i < y@.len() ==> y@[i] % 3 == 0,
            forall |i: int| 0 <= i < x@.len() && x@[i] % 3 == 0
                ==> exists |j: int| 0 <= j < y@.len() && y@[j] == x@[i],
            forall |j1: int, j2: int| 
                   0 <= j1 < j2 < y@.len() ==>
                   exists |i1: int, i2: int| 
                       0 <= i1 < i2 < x@.len()
                       && x@[i1] == y@[j1]
                       && x@[i2] == y@[j2]
    {
        let mut i: usize = 0;
        let xlen = x.len();
        
        while i < xlen {
            if x[i] % 3 == 0 {
                y.push(x[i]);
            }
            i = i + 1;
        }
    }
}

//             y@.len() == 0
//   None: y

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False