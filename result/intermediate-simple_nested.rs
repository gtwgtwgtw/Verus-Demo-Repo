/* For each index i < N, this function sets a[i] to b[i] + 1 and then decrements it i times. It returns the sum of all updated a elements. */

use vstd::prelude::*;
fn main() {}
verus!{
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
requires
0 <= N,
(N as usize) <= a.len(),
(N as usize) <= b.len()
ensures
forall |i: int| 0 <= i && i < N
    ==> a[i as usize] == b[i as usize] + 1 - i,
sum == (0..N).map(|i| b[i as usize] + 1 - i).sum()

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
