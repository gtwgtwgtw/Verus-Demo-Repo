use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
	ensures
		forall |k:int| b[k] == 4*k*k + 4*k + 1,
{
	a.set(0, 8);
	b.set(0, 1);
	let mut i: usize = 1;
	while (i < N as usize)
	{
		a.set(i, a[i-1] + 8);
		i = i + 1;
	}

	i = 1;
	while (i < N as usize)
	{
		b.set(i, b[i-1] + a[i-1]);
		i = i + 1;
	}
}
}