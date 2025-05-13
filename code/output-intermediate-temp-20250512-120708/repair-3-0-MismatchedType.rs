/* For each index i < N, this function sets a[i] to b[i] + 1 and then decrements it i times. It returns the sum of all updated a elements. */
// [FAILED]

/* For each index i < N, this function sets a[i] to b[i] + 1 and then decrements it i times. It returns the sum of all updated a elements. */

use vstd::prelude::*;
use vstd::seq_lib::*;

fn main() {}

verus!{

#[verifier::loop_isolation(false)]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        N >= 0,
        (N as nat) <= a@.len(),
        (N as nat) <= b@.len(),
    ensures
        // For each i < N, the new a[i] is b[i] + 1 - i
        forall|i: nat| i < (N as nat) ==> a@[( i ) as int] == b@[( i ) as int] + 1 - i,
        // The returned sum is the sum of the updated a elements
        sum == a@.subrange(0, N as int).sum(),
        // And that sum matches the sum of b[i] + 1 - i
        sum == (0 .. N as nat).map(|i: nat| b@[( i ) as int] + 1 - i).sum(),
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
// Score: (0, 6)
// Safe: True





//         forall|i: nat| i < (N as nat) ==> a@[i] == b@[i] + 1 - i,
//   expected `int`, found `nat`: i
//   arguments to this method are incorrect: a@[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False