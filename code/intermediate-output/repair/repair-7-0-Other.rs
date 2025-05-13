use vstd::prelude::*;
fn main() {}

verus!{

pub open spec fn num_of(p: spec_fn(int) -> bool) -> int {
    0
}

pub open spec fn count(p: spec_fn(int) -> bool) -> int {
    num_of(|i: int| p(i))
}

pub open spec fn nth(p: spec_fn(int) -> bool, i: int) -> int {
    choose |r: int|
        #[trigger] p(r)
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

    while i < xlen
        invariant 
            0 <= i <= xlen,
            xlen == x.len(),
            y.len() == count(|j: int| 0 <= j < i && x[j] % 3 == 0),
            forall|j: int| 
                (0 <= j < y.len() ==> y[j] == x[nth(|k: int| 0 <= k < i && x[k] % 3 == 0, j)])
                && 
                (0 <= j < x.len() ==> x[j] == x[j])
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
        i = i + 1;
    }
}
}

//         && #[trigger] (count(|k: int| 0 <= k < r && p(k))) == i
//   None: |k: int| 0 <= k < r && p(k)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True