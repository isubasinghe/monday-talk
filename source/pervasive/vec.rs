#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;

verus2! {

#[verifier(external_body)]
pub struct Vec<#[verifier(strictly_positive)] A> {
    pub vec: std::vec::Vec<A>,
}

impl<A> Vec<A> {
    pub spec fn view(&self) -> Seq<A>;

    #[verifier(external_body)]
    pub fn new() -> (v: Self)
        ensures
            v.view() === Seq::empty(),
    {
        Vec { vec: std::vec::Vec::new() }
    }
    
    pub fn empty() -> (v: Self)
        ensures
            v.view() === Seq::empty(),
    {
        Vec::new()
    }

    #[verifier(external_body)]
    pub fn push(&mut self, value: A)
        ensures
            self.view() === old(self).view().push(value),
    {
        self.vec.push(value);
    }

    #[verifier(external_body)]
    pub fn pop(&mut self) -> (value: A)
        requires
            old(self).len() > 0,
        ensures
            value === old(self).view()[old(self).view().len() as int - 1],
            self.view() === old(self).view().subrange(0, old(self).view().len() as int - 1),
    {
        unsafe {
            self.vec.pop().unwrap_unchecked()  // Safe to unwrap given the precondition above
        }
    }

    #[verifier(inline)]
    pub open spec fn spec_index(self, i: int) -> A {
        self.view()[i]
    }

    #[verifier(external_body)]
    #[verifier(autoview)]
    pub fn index(&self, i: usize) -> (r: &A)
        requires
            i < self.view().len(),
        ensures
            *r === self.view()[i as int],
    {
        &self.vec[i]
    }

    #[verifier(external_body)]
    pub fn set(&mut self, i: usize, a: A)
        requires
            i < old(self).view().len(),
        ensures
            self.view() === old(self).view().update(i as int, a),
    {
        self.vec[i] = a;
    }

    pub spec fn spec_len(&self) -> usize;

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_len))]
    #[verifier(autoview)]
    pub fn len(&self) -> (l: usize)
        ensures
            l == self.view().len(),
    {
        self.vec.len()
    }
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_spec_len<A>(v: Vec<A>)
    ensures
        #[trigger] v.spec_len() == v.view().len(),
{
}

} // verus!
