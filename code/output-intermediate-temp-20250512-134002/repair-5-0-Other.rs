use vstd::prelude::*;
fn main() {}

verus!{

spec fn num_of(p: FnSpec(int) -> bool) -> int {
    0 // Added by AI
}

spec fn count(p: FnSpec(int) -> bool) -> int {
    num_of(|i: int| p(i))
}

spec fn nth(p: FnSpec(int) -> bool, i: int) -> int {
    choose |r: int| 
        p(r)
        && count(|k: int| 0 <= k < r && p(k)) == i
}

#[verifier::loop_isolation(false)]
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    requires
        old(y).len() == 0,
    ensures
        y.len() == count(|j: int| 0 <= j < x.len() && x[j] % 3 == 0),
        forall|i: int| 0 <= i < y.len() ==>
            y[i] == x[nth(|j: int| 0 <= j < x.len() && x[j] % 3 == 0, i)],
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

//         y.len() == 0,
//   None: y

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False