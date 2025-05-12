/*
Performs binary search on a sorted vector to locate a given key.
Returns the index of the key within the vector.
*/
use vstd::prelude::*;
fn main() {}

verus!{
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        v.len() > 0,
        forall |i: usize, j: usize| i < j && j < v.len() ==> v[( i ) as int] <= v[( j ) as int],
        exists |i: usize| i < v.len() && v[( i ) as int] == k
    ensures
        r < v.len(),
        v[( r ) as int] == k
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;
    while i1 != i2
        invariant
            0 <= i1,
            0 <= i2,
            i1 <= i2,
            i2 < v.len(),
            i1 < v.len(),
            forall |p: usize, q: usize| p < q && q < v.len() ==> v[( p ) as int] <= v[( q ) as int],
            exists |m: usize| i1 <= m <= i2 && v[( m ) as int] == k
    {
        let ix = i1 + (i2 - i1) / 2;
        if v[ix] < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }
    }
    i1
}
}
// Score: (2, 0)
// Safe: False