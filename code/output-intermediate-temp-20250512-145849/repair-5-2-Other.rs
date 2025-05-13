use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    requires
        y@.len() == 0,
    ensures
        forall i: nat :: i < y@.len() ==> y@[i] % 3 == 0,
    ensures
        forall i: nat :: i < x@.len() && x@[i] % 3 == 0 ==> exists j: nat :: j < y@.len() && y@[j] == x@[i],
    ensures
        forall j1, j2: nat :: j1 < j2 < y@.len() ==>
            exists i1, i2: nat :: i1 < i2 < x@.len() && x@[i1] == y@[j1] && x@[i2] == y@[j2]
{
    let mut i: usize = 0;
    let xlen = x.len();
    
    while i < xlen {
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
        i += 1;
    }
}
}

// forall i: nat, i < y@.len() ==> y@[i] % 3 == 0,
//   None: i

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False