use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::ptr::*;
use vstd::cell::*;

// Potential aliasing of variable bindings in the presence of mutation 
// complicates verification - Bordiga 1995 . Might be encodable in SMT but requires
// moving away from "modular" verification ==> introduces scalability issues.

verus! {



fn main() {

    let (p, mut tracked) = PPtr::<[PCell<u8>; 128]>::empty();
    let perms: Tracked<Map<nat, PointsTo<PCell<u8>>>>;
    proof {
        
    }

}

}


// References:
// On the frame problem in procedure specifications - A.Bordiga et al 1995
