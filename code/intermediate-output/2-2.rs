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
            length == v.len(),
            n <= length / 2,
            forall |i: nat| i < n ==> 
                v[( i ) as int] == old(v)[length - 1 - i]
                && v[length - 1 - i] == old(v)[( i ) as int],
            forall |j: nat| n <= j <= length - 1 - n ==> 
                v[( j ) as int] == old(v)[( j ) as int],
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