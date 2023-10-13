use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;


verus! {

// Struct with flag indicating whether a 
// map should happen
#[derive(Structural, PartialEq, Eq)]
struct MyStruct<T> {
    x: Option<Box<T>>, // INTERESTING TO TALK ABOUT
    p: bool
}

// EXAMPLE: 1
fn adder(x: u32, y: u32) -> (res: u32) 
    requires
        x <= 0x7fffffff,
        y <= 0x7fffffff,
    ensures
        res == x + y
{
    return x + y;
}

// EXAMPLE 2
fn struct_map<T>(s: MyStruct<T>) -> (res: MyStruct<T>)
    requires
        s.p ==> s.x.is_some(),
{
    match s.x {
        Some(val) => MyStruct { x: Some(val), p: true},
        None => s
    }
}

fn main() {
}

}
