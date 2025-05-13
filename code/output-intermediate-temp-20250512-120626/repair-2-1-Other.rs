use vstd::prelude::*;
fn main() {}

verus!{

spec fn seq_sum(seq: Seq<i32>) -> i32 {
    decreases seq.len();
    if seq.len() == 0 {
        0
    } else {
        seq.index(0) + seq_sum(seq.subrange(1, seq.len()))
    }
}

#[verifier::loop_isolation(false)]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        N >= 0,
        (N as nat) <= a@.len(),
        (N as nat) <= b@.len(),
    ensures
        forall|i: nat| i < (N as nat) ==> a@[i] == b@[i] + 1 - i,
        sum == seq_sum(a@.subrange(0, N as nat)),
        sum == seq_sum((0 .. N as nat).map(|i: nat| b@[i] + 1 - i)),
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;

    while i < N as usize {
        a.set(i, b[i] + 1);

        let mut j: usize = 0;
        while j < i {
            a.set(i, a[i] - 1);
            j = j + 1;
        }

        sum = sum + a[i];
        i = i + 1;
    }

    sum
}
}

//         sum == seq_sum((0 .. N as nat).map(|i: nat| b@[i] + 1 - i)),
//   not found in this scope: seq_sum

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False