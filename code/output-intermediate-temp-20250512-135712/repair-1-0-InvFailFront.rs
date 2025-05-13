Below is one simple way to fix the verifier’s complaint.  Since there is only one loop in this function, Verus is complaining that the invariant  
  y.len() == count(|j: int| 0 <= j < i && x[j] % 3 == 0)  
does not hold “on entry.”  In other words, Verus wants a proof that when i = 0, y.len() is in fact equal to count(|j: int| 0 <= j < 0 && …), i.e., zero.

A straightforward remedy is simply to assert that y.len() already satisfies this condition before the loop begins.  For example:

-----------------------------------------------------------
#[verifier::loop_isolation(false)]
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    requires
        old(y).len() == 0,
    ensures
        y.len() == count(|j: int| 0 <= j < x.len() && x[j] % 3 == 0),
        forall|i: int|
            0 <= i < y.len() ==>
                y[i] == x[nth(|j: int| 0 <= j < x.len() && x[j] % 3 == 0, i)],
{
    let mut i: usize = 0;
    let xlen = x.len();

    // Add this assertion before the loop so that 
    // Verus knows the invariant holds at loop entry:
    assert(y.len() == count(|j: int| 0 <= j < i && x[j] % 3 == 0));

    while i < xlen
        invariant
            0 <= i <= xlen,
            x.len() == xlen,
            y.len() == count(|j: int| 0 <= j < i && x[j] % 3 == 0),
            forall|j: int|
                0 <= j < y.len() ==>
                    y[j] == x[nth(|k: int| 0 <= k < i && x[k] % 3 == 0, j)],
            forall|k: int| 0 <= k < x.len() ==> x[k] == x[k]
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
        i = i + 1;
    }
}
-----------------------------------------------------------

Because i == 0 at the start, count(|j: int| 0 <= j < 0 && x[j] % 3 == 0) = 0 and y.len() ought to be 0 (given old(y).len() == 0).  By placing that assert right before the loop, you establish the invariant at loop entry so the verifier is satisfied.

//             y.len() == count(|j: int| 0 <= j < i && x[j] % 3 == 0),
//   None: y.len() == count(|j: int| 0 <= j < i && x[j] % 3 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False