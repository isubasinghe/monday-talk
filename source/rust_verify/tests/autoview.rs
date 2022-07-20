#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        struct S {}

        impl S {
            spec fn f(&self) -> bool { true }

            // Note: it's a good idea for g and f to return the same value,
            // but, for testing purposes only, we have them return different values here.
            #[verifier(when_used_as_spec(f))]
            fn g(&self) -> bool { false }

            fn h(&self) {
                self.g(); // call g
                assert(self.g()); // in a spec, so call f, not g
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] fail_exec_false verus_code! {
        struct S {}

        impl S {
            spec fn f(&self) -> bool { true }

            #[verifier(when_used_as_spec(f))]
            fn g(&self) -> bool { false }

            fn h(&self) {
                let b = self.g();
                assert(b); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] fail_different_typarg verus_code! {
        struct S {}

        impl S {
            spec fn f<A>(&self, k: &A) -> bool { true }

            #[verifier(when_used_as_spec(f))]
            fn g<B>(&self, k: &B) -> bool { true }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] fail_different_arg verus_code! {
        struct S {}

        impl S {
            spec fn f(&self, k: int) -> bool { true }

            #[verifier(when_used_as_spec(f))]
            fn g(&self, k: u64) -> bool { true }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] fail_different_returns verus_code! {
        struct S {}

        impl S {
            spec fn f(&self) -> bool { true }

            #[verifier(when_used_as_spec(f))]
            fn g(&self) -> u8 { 0 }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] fail_not_exec verus_code! {
        struct S {}

        impl S {
            spec fn f(&self, k: u64) -> bool { true }

            #[verifier(when_used_as_spec(f))]
            proof fn g(&self, k: u64) -> bool { true }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] fail_not_spec verus_code! {
        struct S {}

        impl S {
            proof fn f(&self, k: u64) -> bool { true }

            #[verifier(when_used_as_spec(f))]
            fn g(&self, k: u64) -> bool { true }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] fail_missing verus_code! {
        struct S {}

        impl S {
            #[verifier(when_used_as_spec(f))]
            fn g(&self, k: u64) -> bool { true }
        }
    } => Err(err) => assert_vir_error(err)
}

/* TODO: remove this when autoview is removed
test_verify_one_file! {
    #[test] test1 code! {
        struct S {
        }

        struct V {
        }

        impl V {
            #[spec]
            fn mkint(self, _i: int) -> int {
                8
            }
        }

        impl S {
            #[proof]
            fn f(#[proof]&self, #[spec] x: int) {

            }

            #[verifier(autoview)]
            fn mkint(&self, _u: u64) -> u64 {
                7
            }

            #[spec]
            fn view(self) -> V {
                V {}
            }
        }

        fn test() {
            let s = S {};
            #[spec] let i: int = 10;
            s.f(s.mkint(i));
            assert(s.mkint(i) == s.mkint(i));
            #[spec] let x: u64 = s.mkint(10);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 code! {
        struct S {
        }

        struct V {
        }

        impl V {
            #[spec]
            fn mkint(self, _i: int) -> int {
                8
            }
        }

        impl S {
            #[verifier(autoview)]
            #[spec] // ERROR: autoview cannot be spec
            fn mkint(&self, _u: u64) -> u64 {
                7
            }

            #[spec]
            fn view(self) -> V {
                V {}
            }
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test1_fails2 code! {
        struct S {
        }

        struct V {
        }

        impl V {
            #[spec]
            fn mkint(self, _i: int) -> int {
                8
            }
        }

        impl S {
            #[verifier(autoview)]
            fn mkint(&self, _u: u64) -> u64 {
                7
            }

            #[spec]
            // ERROR: wrong signature for view
            fn view(self, foo: int) -> V {
                V {}
            }
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test1_fails3 code! {
        struct S {
        }

        struct V {
        }

        impl V {
            #[spec]
            fn mkint(self, _i: int) -> int {
                8
            }
        }

        impl S {
            #[verifier(autoview)]
            fn mkint(&self, _u: u64) -> u64 {
                7
            }

            // ERROR: view is missing
        }
    } => Err(_)
}
*/
