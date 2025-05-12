/* Initializes a value at 5 and increments it in two loops of 10 iterations, resulting in 25. It then asserts that the result equals 25. */

use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd()
// [Add Requires Clauses Here]

{
    let mut idx: u64 = 0;
    let mut res: u64 = 5;
    while (idx < 10)
    {
        res = res + 1;
        idx = idx + 1;
    }
    idx = 0;
    while (idx < 10)
    {
        res = res + 1;
        idx = idx + 1;
    }
    assert(res == 25);
}
}
