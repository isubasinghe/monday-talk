
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::ptr::*;
use vstd::seqptr;

// Potential aliasing of variable bindings in the presence of mutation 
// complicates verification - Bordiga 1995 . Might be encodable in SMT but requires
// moving away from "modular" verification ==> introduces scalability issues.

verus! {


fn increment(counter: PPtr<u64>, Tracked(perm) : Tracked<&mut PointsTo<u64>>) 
    requires
        counter.id() == old(perm)@.pptr,
{

}

fn start_thread(counter: PPtr<u64>, Tracked(perm): Tracked<PointsTo<u64>>) 
    requires
        counter.id() == perm@.pptr, perm@.value === None,
{
    let tracked mut perm: PointsTo<u64> = perm;
    counter.put(Tracked(&mut perm), 5);

    // WHAT THE HELL ARE THESE @ symbols?
    // Why is my equal sign having an extra '='
    //
    // Well what really is a PPtr?
    // Just a wrapper over MaybeUninit
    // There is nothing to encode here!
    // We need ghost state.
    //
    //
    // we want to talk about Ghost state
    //
    assert(perm@.value === Some(5));


}


fn raw_mem(addr: usize) {
    let (ptr, Tracked(mut perm)) = PPtr::<u8>::from_usize_assumed(addr);
    ptr.put(Tracked(&mut perm), 97);
    ptr.replace(Tracked(&mut perm), 97);
    assert(perm@.value === Some(97));
}

fn seq_raw_mem(addr: usize, sz: usize) {
    let (ptr, Tracked(mut perm)) = seqptr::PPtrSeq::<u8>::from_usize_assumed(addr, 4);
    ptr.write_offset(Tracked(&mut perm), 1, 0);
    ptr.write_offset(Tracked(&mut perm), 2, 1);
    ptr.write_offset(Tracked(&mut perm), 3, 2);
    ptr.write_offset(Tracked(&mut perm), 4, 3);
}


#[verifier(external_body)]
fn raw_addr() {
    let mut m: u8 = 2;
    let p_m: *mut u8 = &mut m;
    raw_mem(p_m as usize);
    println!("{}", m);


    let mut z: [u8; 4] = [0; 4];
    let p_z: *mut [u8; 4] = &mut z;
    seq_raw_mem(p_z as usize, 4);
    println!("{:?}", z);

}




fn main() {
    raw_addr();
}

}


// References:
// On the frame problem in procedure specifications - A.Bordiga et al 1995
