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
        n + triangle(( n - 1 ) as nat)
    }
}

fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
    requires
        idx as nat <= n as nat,
        old(( *sum ) as &mut _) as nat + (triangle(n as nat) - triangle(idx as nat)) <= u32::MAX as nat,
    ensures
        *sum as nat == old(*sum) as nat + (triangle(n as nat) - triangle(idx as nat))
{
    if idx < n {
        let idx_new = idx + 1;
        *sum = *sum + idx_new;
        tail_triangle(n, idx_new, sum);
    }
}

}


//         *sum as nat == old(sum) as nat + (triangle(n as nat) - triangle(idx as nat))
//   the trait `std::marker::Copy` is not implemented for `&mut u32`: old(sum) as nat

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False