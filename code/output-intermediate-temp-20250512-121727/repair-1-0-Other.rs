use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
spec fn triangle(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        n + triangle((n - 1) as nat)
    }
}

fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
    requires
        idx as nat <= n as nat,
        (*old(sum) as nat) + (triangle(n as nat) - triangle(idx as nat)) <= u32::MAX as nat,
    ensures
        *sum as nat == (*old(sum)) as nat + (triangle(n as nat) - triangle(idx as nat))
{
    if idx < n {
        let idx = idx + 1;
        *sum = *sum + idx;
        tail_triangle(n, idx, sum);
    }
}

}

//         (*sum as nat) + (triangle(n as nat) - triangle(idx as nat)) <= u32::MAX as nat,
//   None: sum

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False