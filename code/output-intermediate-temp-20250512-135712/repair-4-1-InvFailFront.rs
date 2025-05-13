Below is one straightforward way to fix the issue when there is only one loop.  
Because Verus complains that the invariant “y.len() == count(|j:int| 0 <= j < i && x[j] % 3 == 0)” does not hold right at the loop’s start, the simplest fix is to assert that fact immediately before the loop. That way, the verifier sees it proven as true at entry and permits its use as an invariant. For example:

----------------------------------------------------------------------
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

    // Add this assert so Verus knows the relationship is initialized correctly:
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
----------------------------------------------------------------------

Explanation:
• Verus needs to see that y.len() already equals the count of multiples of 3 among x[0..i], at the moment the loop first executes.  
• By adding assert(y.len() == count(|j:int| 0 <= j < i && x[j] % 3 == 0)) before the loop, we give Verus a proven fact that matches our invariant.  
• Because there is only one loop in the snippet, adding the assert is the easiest way to make the verification engine accept that invariant at loop entry.

//             y.len() == count(|j: int| 0 <= j < i && x[j] % 3 == 0),
//   None: y.len() == count(|j: int| 0 <= j < i && x[j] % 3 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False