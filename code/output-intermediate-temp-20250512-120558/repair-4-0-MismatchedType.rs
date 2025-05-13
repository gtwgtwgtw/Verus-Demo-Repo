/* For each index i < N, this function sets a[i] to b[i] + 1 and then decrements it i times. It returns the sum of all updated a elements. */
// [FAILED]

/* For each index i < N, this function sets a[i] to b[i] + 1 and then decrements it i times. It returns the sum of all updated a elements. */

use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
requires
N >= 0,
(N as usize) <= a.len(),
(N as usize) <= b.len()
ensures
forall|i: usize| i < (N as usize) ==> a[( i ) as int] == b[( i ) as int] + 1 - (i as i32),
sum == a[..(N as int].spec_sum(),
sum == (0 .. (N as usize)).fold(0, |acc, i| acc + (b[i] + 1 - (i as i32)))

{  
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize) 
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        sum = sum + a[i];
        i = i + 1;
    }  
    sum
}
}
// Score: (0, 4)
// Safe: True




// forall|i: usize| i < (N as usize) ==> a[i] == b[i] + 1 - (i as i32),
//   expected `int`, found `usize`: i
//   arguments to this method are incorrect: a[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False