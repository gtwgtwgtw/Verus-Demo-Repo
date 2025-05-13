use vstd::prelude::*;

fn main() {}

verus!{

#[verifier::spec]
fn sum_f(low: int, high: int, f: FnSpec(int) -> int) -> int
    decreases high - low
{
    if low >= high {
        ( 0 ) as int
    } else {
        f(low) + sum_f(low + 1, high, f)
    }
}

#[verifier::loop_isolation(false)]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: int) -> (sum: int)
    requires
        N >= 0,
        N <= a@.len(),
        N <= b@.len(),
    ensures
        forall|i: int| 0 <= i < N ==> a@[i] == b@[i] + 1 - i,
        sum == sum_f(0, N, |i: int| a@[i]),
        sum == sum_f(0, N, |i: int| b@[i] + 1 - i),
{
    let mut i: usize = 0;
    let mut s: i32 = 0;

    while i < N as usize {
        a.set(i, b[i] + 1);

        let mut j: usize = 0;
        while j < i {
            a.set(i, a[i] - 1);
            j = j + 1;
        }

        s = s + a[i];
        i = i + 1;
    }

    proof {
        let ghost ret = s as int;
        return ret;
    }
}
}


//     s as int
//   None: s as int

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False