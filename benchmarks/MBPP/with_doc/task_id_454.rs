/*
Checks whether the input character vector contains the letter 'Z' in either uppercase or lowercase.
Returns true as soon as such a character is found, and false if none are present.
*/

use vstd::prelude::*;

fn main() {}

verus! {

fn contains_z(text: &Vec<char>) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 'Z' || text[i] == 'z')),
{
    let mut index = 0;
    while index < text.len() {
        if text[index] == 'Z' || text[index] == 'z' {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
