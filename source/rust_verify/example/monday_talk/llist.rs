
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::ptr::*;
use vstd::string::*;
use vstd::*;

// Potential aliasing of variable bindings in the presence of mutation 
// complicates verification - Bordiga 1995 . Might be encodable in SMT but requires
// moving away from "modular" verification ==> introduces scalability issues.


// Rust is infamous for being difficult to write a LinkedList in without the usage
// of unsafe.
//
// Writing 
//
// Let's take a step back and ask why?
//
// Rust enforces affine types - safe
// Unfortunately this makes mutation impossible without moving 
// For LL moving won't work - everything is chained together
// Rc would work -> do you really want to use reference counting?
//
// 

// The core idea here is to seperate data from permission
//

verus! {

#[verifier(external_body)]
proof fn lemma_usize_u64(x: u64)
    ensures
        x as usize as u64 == x,
{
    unimplemented!();
}


struct Node<V> {
    nxt: u64,
    v: V,
}


// How is this represented in our ghost state?
// A linkedList is just a sequence of things
//
// A->B->C->D
// [A,B,C,D]
// [perm A, perm B, perm C, perm D]
//
struct LList<V> {
    ptrs: Ghost<Seq<PPtr<Node<V>>>>, // Ghost state
    perms: Tracked<Map<nat, PointsTo<Node<V>>>>, // Zero sized type
    head: u64,
    tail: u64
}


impl<V> LList<V> {

    spec fn wf_perms(&self) -> bool {
        forall|i: nat| 0 <= i < self.ptrs@.len() ==> self.wf_perm(i)
    }

    spec fn wf_perm(&self, i: nat) -> bool 
        recommends i < self.ptrs@.len()
    {
        &&& self.perms@.dom().contains(i) // valid index
        &&& self.perms@[i].view().pptr == self.ptrs@[i as int].id() // the pointer the permission
                                                                    // points to is the same as the
                                                                    // pointer
        &&& 0 < self.ptrs@[i as int].id() // non null pointer
        &&& self.perms@[i].view().value.is_Some() // defined to be something <- MaybeUninit

    }

    spec fn wf_head(&self) -> bool {
        if self.ptrs@.len() == 0 {
            self.head == 0 
        }else {
            self.head == self.ptrs@[0].id()
        }
    }

    spec fn wf_tail(&self) -> bool {
        if self.ptrs@.len() == 0 {
            self.tail == 0
        }else {
            self.tail == self.ptrs@[self.ptrs@.len() -1].id()
        }
    }

    spec fn view(&self) -> Seq<V> 
        recommends self.wf()
    {
        Seq::<V>::new(self.ptrs@.len(), |i: int| {
            self.perms@[i as nat]@.value.get_Some_0().v
        })
    }

    spec fn wf(&self) -> bool {
        self.wf_perms() && self.wf_head() && self.wf_tail()
    }

    
    fn new() -> (s: Self) 
        ensures
            s.wf(),
            s@.len() == 0,
    {
        LList{
            ptrs: Ghost(Seq::empty()),
            perms: Tracked(Map:: tracked_empty()),
            head: 0,
            tail: 0
        }

    }
    
    fn push_empty_case(&mut self, v: V) 
        requires 
            old(self).wf(),
            old(self).ptrs@.len() == 0
        ensures
            self.wf(),
            self@ == old(self)@.push(v),
            self.ptrs@.len() == 1,
            self.perms@[0].view().pptr == self.ptrs@[0].id(),
    {
        let (ptr, perm) = PPtr::new(
            Node::<V> { nxt: 0, v }
        );

        proof {
            self.ptrs@ = self.ptrs@.push(ptr);
            let tracked perm = perm.get();
            (&perm).is_nonnull();
            (self.perms.borrow_mut())
                .tracked_insert((self.ptrs@.len() - 1 ) as nat, perm);
        }
        self.head = ptr.to_usize() as u64;
        self.tail = ptr.to_usize() as u64;
        
        assert(self@ =~= old(self)@.push(v));
        assert(self.ptrs@.len() == 1);
    }

    fn push(&mut self, v: V) 
        requires
            old(self).wf(),
            old(self).ptrs@.len() > 0
        ensures
            self.wf(),
            self@ == old(self)@.push(v)
    {
        let tail_ptr_u64 = self.tail;
        proof {
            lemma_usize_u64(tail_ptr_u64);
        }

        let (ptr, perm) = PPtr::new(
            Node::<V> { nxt: 0, v}
        );
        let new_ptr = ptr.to_usize() as u64;

        proof {
            (perm.borrow()).is_nonnull();
        }

        let tail_ptr = PPtr::<Node<V>>::from_usize(tail_ptr_u64 as usize);


        assert(self.ptrs@.len() > 0);
        assert(self.wf_perm((self.ptrs@.len() - 1) as nat));

        let tracked mut tail_perm: PointsTo<Node<V>> = 
            (self.perms.borrow_mut()).tracked_remove((self.ptrs@.len() -1) as nat);

        let mut tail_node = tail_ptr.take(Tracked(&mut tail_perm));
        tail_node.nxt = new_ptr;
        tail_ptr.put(Tracked(&mut tail_perm), tail_node);

        
        proof {
            (self.perms.borrow_mut()).tracked_insert((self.ptrs@.len() - 1) as nat, tail_perm);
            (self.perms.borrow_mut()).tracked_insert((self.ptrs@.len()), (perm).get());
            self.ptrs@ = self.ptrs@.push(ptr);
            assert(self.ptrs@[self.ptrs@.len() -1].id() == perm@.view().pptr);
            assert(self.ptrs@[self.ptrs@.len() -2].id() == tail_perm@.pptr);
        }

        self.tail = new_ptr;


        proof {
            assert(self.wf_perm((self.ptrs@.len() -1) as nat));
            assert(forall|i: nat| i < self.ptrs@.len() ==> 
                   old(self).wf_perm(i) ==> self.wf_perm(i));
            assert(self.wf_perms());
            assert(self.wf_head());
            assert(self.wf_tail());
            assert(self@[self.ptrs@.len() -1] == v); 
            assert forall|i: int| 0 <= i < self.ptrs@.len() - 1 implies old(self)@[i] == self@[i] by {
                assert(old(self).wf_perm(i as nat)); // trigger
            };

            assert(self@ =~= old(self)@.push(v));
        }

    }


}

fn main() {
    let mut llist = LList::<u32>::new();
    llist.push_empty_case(5);
    assert(llist@[0] == 5);
    llist.push(2);
    assert(llist@[1] == 2);
}


}


// References:
// On the frame problem in procedure specifications - A.Bordiga et al 1995
