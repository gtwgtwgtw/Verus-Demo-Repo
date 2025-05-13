use vstd::prelude::*;
fn main() {}

verus! {

/**********************************************************
   We treat num_of, count, and nth as trusted specifications
   for "how many" and "which" elements satisfy a predicate.
   That way, the verification can use them in the specs
   without needing their internal proof details.
***********************************************************/

// [Trusted]
pub open spec fn num_of(p: spec_fn(int) -> bool) -> int {
    arbitrary()
}

// [Trusted]
pub open spec fn count(p: spec_fn(int) -> bool) -> int {
    num_of(p)
}

// [Trusted]
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
        forall|ii: int|
            0 <= ii < y.len() ==>
                y[ii] == x[nth(|j: int| 0 <= j < x.len() && x[j] % 3 == 0, ii)],
{
    let mut i: usize = 0;
    let xlen = x.len();

    while i < xlen
        invariant
            0 <= i <= xlen,
            x.len() == xlen,
            y.len() <= x.len(),
            y.len() == count(|j: int| 0 <= j < i && x[j] % 3 == 0),
            forall|jj: int|
                0 <= jj < y.len() ==>
                    y[jj] == x[nth(|k: int| 0 <= k < i && x[k] % 3 == 0, jj)],
            forall|k: int| 0 <= k < x.len() ==> x[k] == x[k]
    {
        let old_len = y.len();
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
        i = i + 1;

        assert(y.len() == count(|jj: int| 0 <= jj < i && x[jj] % 3 == 0));

        if x[i - 1] % 3 == 0 {
            assert(old_len == count(|j: int| 0 <= j < i - 1 && x[j] % 3 == 0));
            proof {
                let r = nth(|k: int| 0 <= k < i && x[k] % 3 == 0, old_len as int);
                assert(r == i - 1);
                assert(y[old_len as int] == x[r]);
            }
        }
    }
}
}

//             let r = nth(|k: int| 0 <= k < i && x[k] % 3 == 0, old_len);
//   expected `int`, found `usize`: old_len
//   None: nth

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False