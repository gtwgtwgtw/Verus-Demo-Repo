use vstd::prelude::*;
fn main() {}

verus!{
fn reverse(v: &mut Vec<u64>)
requires
true
ensures
v.len() == old(v).len(),
forall|i: nat| i < v.len() ==> v[( i ) as int] == old(v)[v.len() - 1 - i]
{
    let length = v.len();
    let mut n: usize = 0;
    while n < length / 2
        invariant
            n <= length / 2,
            length == v.len(),
            forall |j: nat|
                j < n ==> (
                    v[( j ) as int] == old(v)[length - 1 - j]
                    && v[length - 1 - j] == old(v)[( j ) as int]
                ),
            forall |j: nat|
                n <= j && j < length - n ==> v[( j ) as int] == old(v)[( j ) as int],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
}
}





// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1