/* Returns a new vector containing all elements from the input vector that are less than or equal to the given threshold. The relative order of elements in the input is preserved in the output. */

use vstd::prelude::*;
fn main() {}
verus!{
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
// [Add Requires Clauses Here]
// [Add Ensures Clauses Here]

{  
    let mut i: usize = 0;
    let vlen = v.len();
    let mut result: Vec<i32> = vec![];
    while (i < v.len()) 
    {  
        if (v[i] <= e) { 
            result.push(v[i]); 
        }
        i = i + 1;
    }  
    result
}
}
