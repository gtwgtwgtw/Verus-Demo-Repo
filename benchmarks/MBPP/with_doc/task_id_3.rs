/* Provides an is_divisible helper and a function is_non_prime that returns true if the input n has any divisor between 2 and n-1, indicating it is not prime. If no such divisor is found, it returns false. */
use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

fn is_non_prime(n: u64) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
{
    if n <= 1 {
        return true;
    }
    let mut index = 2;
    while index < n {
        if ((n % index) == 0) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!

use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

fn is_non_prime(n: u64) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
{
    if n <= 1 {
        return true;
    }
    let mut index = 2;
    while index < n {
        if ((n % index) == 0) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
