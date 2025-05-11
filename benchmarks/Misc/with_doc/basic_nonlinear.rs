/*[Ensures that for any two 16-bit unsigned integers x and y (each ≤ 0xffff), their product does not exceed 0x100000000 (2^32).]*/  

//from Verus tutorial

use vstd::prelude::*;
fn main() {}

verus!{
     
proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x*y <= 0x100000000,
{

}
}

//from Verus tutorial

use vstd::prelude::*;
fn main() {}

verus!{
     
proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x*y <= 0x100000000,
{

}
}
