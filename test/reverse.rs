/* Reverses the elements of the vector in place. Each element at index i is moved to index len - 1 - i. */

use vstd::prelude::*;
fn main() {}

verus!{
fn reverse(v: &mut Vec<u64>)
// [Add Requires Clauses Here]
// [Add Ensures Clauses Here]

{
    let length = v.len();
    let mut n: usize = 0;
    while n < length / 2
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);

        n = n + 1;
    }
}
}
