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
            v.len() == length,
            forall|i: nat| i < n ==> v[( i ) as int] == old(v)[length - 1 - i],
            forall|i: nat| i < n ==> v[length - 1 - i] == old(v)[( i ) as int],
            forall|i: nat| n <= i && i < length - n ==> v[( i ) as int] == old(v)[( i ) as int],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);

        n = n + 1;
    }
}
}
// Score: (2, 0)
// Safe: False