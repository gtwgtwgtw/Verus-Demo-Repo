use vstd::prelude::*;
fn main() {}
verus!{

/* Returns a new vector containing all elements from the input vector that are less than or equal to the given threshold. The relative order of elements in the input is preserved in the output. */
// [FAILED]

/* Returns a new vector containing all elements from the input vector that are less than or equal to the given threshold. The relative order of elements in the input is preserved in the output. */

#[verifier::loop_isolation(false)]
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires
    true,
    ensures
        forall|i: int| 0 <= i < result.len() ==> result[i] <= e,
        forall|i: int| 0 <= i < v.len() && v[i] <= e ==> result.contains(( v[i] ) as &i32),
        forall|i: int, j: int| 0 <= i < j < v.len() && v[i] <= e && v[j] <= e ==> result.index_of(v[i]) < result.index_of(v[j]),
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


// ∀ i in 0..result.len() ⇒ result[i] ≤ e,
//   None: in

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False