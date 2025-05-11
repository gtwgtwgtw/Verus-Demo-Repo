/*
Checks whether one integer n is evenly divisible by a given divisor. 
Determines if an integer n >= 2 is prime by testing divisibility for all numbers from 2 up to n - 1.
*/

use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

fn prime_num(n: u64) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)),
{
    if n <= 1 {
        return false;
    }
    let mut index = 2;
    while index < n {
        if ((n % index) == 0) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
