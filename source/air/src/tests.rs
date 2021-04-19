use crate::ast::{CommandX, ValidityResult};
#[allow(unused_imports)]
use crate::print_parse::{macro_push_node, nodes_to_commands};
#[allow(unused_imports)]
use sise::Node;

#[allow(dead_code)]
fn run_nodes_as_test(should_typecheck: bool, should_be_valid: bool, nodes: &[Node]) {
    let mut z3_config = z3::Config::new();
    z3_config.set_param_value("auto_config", "false");
    let z3_context = z3::Context::new(&z3_config);
    let z3_solver = z3::Solver::new(&z3_context);
    let mut air_context = crate::context::Context::new(&z3_context, &z3_solver);
    air_context.set_z3_param("air_recommended_options", "true");
    match nodes_to_commands(&nodes) {
        Ok(commands) => {
            for command in commands.iter() {
                let result = air_context.command(&command);
                match (&**command, should_typecheck, should_be_valid, result) {
                    (_, false, _, ValidityResult::TypeError(_)) => {}
                    (_, true, _, ValidityResult::TypeError(s)) => {
                        panic!("type error: {}", s);
                    }
                    (_, _, true, ValidityResult::Valid) => {}
                    (_, _, false, ValidityResult::Invalid(_)) => {}
                    (CommandX::CheckValid(_), _, _, _) => {
                        panic!("unexpected result");
                    }
                    _ => {}
                }
            }
        }
        Err(s) => {
            println!("{}", s);
            panic!();
        }
    }
}

#[allow(unused_macros)]
macro_rules! yes {
    ( $( $x:tt )* ) => {
       {
           let mut v = Vec::new();
           $(macro_push_node(&mut v, node!($x));)*
           run_nodes_as_test(true, true, &v)
       }
    };
}

#[allow(unused_macros)]
macro_rules! no {
    ( $( $x:tt )* ) => {
       {
           let mut v = Vec::new();
           $(macro_push_node(&mut v, node!($x));)*
           run_nodes_as_test(true, false, &v)
       }
    };
}

#[allow(unused_macros)]
macro_rules! untyped {
    ( $( $x:tt )* ) => {
       {
           let mut v = Vec::new();
           $(macro_push_node(&mut v, node!($x));)*
           run_nodes_as_test(false, false, &v)
       }
    };
}

#[test]
fn yes_true() {
    yes!(
        (check-valid
            (assert true)
        )
    );
}

#[test]
fn no_false() {
    no!(
        (check-valid
            (assert false)
        )
    );
}

#[test]
fn yes_int_const() {
    yes!(
        (check-valid
            (assert
                (= (+ 2 2) 4)
            )
        )
    );
}

#[test]
fn no_int_const() {
    no!(
        (check-valid
            (assert
                (= (+ 2 2) 5)
            )
        )
    );
}

#[test]
fn yes_int_vars() {
    yes!(
        (check-valid
            (declare-const x Int)
            (declare-const y Int)
            (declare-const z Int)
            (assert
                (= (+ x y z) (+ z y x))
            )
        )
    );
}

#[test]
fn no_int_vars() {
    no!(
        (check-valid
            (declare-const x Int)
            (declare-const y Int)
            (assert
                (= (+ x y) (+ y y))
            )
        )
    );
}

#[test]
fn yes_int_neg() {
    yes!(
        (check-valid
            (declare-const x Int)
            (assert
                (= (+ x (- 2)) (- x 2))
            )
        )
    );
}

#[test]
fn yes_int_axiom() {
    yes!(
        (check-valid
            (declare-const x Int)
            (axiom (> x 3))
            (assert
                (>= x 3)
            )
        )
    );
}

#[test]
fn no_int_axiom() {
    no!(
        (check-valid
            (declare-const x Int)
            (axiom (>= x 3))
            (assert
                (> x 3)
            )
        )
    );
}

#[test]
fn yes_test_block() {
    yes!(
        (check-valid
            (declare-const x Int)
            (block
                (assume (> x 3))
                (assert (>= x 3))
                (assume (> x 5))
                (assert (>= x 5))
            )
        )
    );
}

#[test]
fn no_test_block() {
    no!(
        (check-valid
            (declare-const x Int)
            (block
                (assume (> x 3))
                (assert (>= x 3))
                (assert (>= x 5))
                (assume (> x 5))
            )
        )
    );
}

#[test]
fn yes_test_block_nest() {
    yes!(
        (check-valid
            (declare-const x Int)
            (block
                (assume (> x 3))
                (block
                    (assert (>= x 3))
                    (assume (> x 5))
                )
                (assert (>= x 5))
            )
        )
    );
}

#[test]
fn yes_global() {
    yes!(
        (push)
            (axiom false)
            (check-valid
                (assert false)
            )
        (pop)
    );
}

#[test]
fn no_global() {
    no!(
        (push)
            (axiom false)
        (pop)
        (check-valid
            (assert false)
        )
    );
}

#[test]
fn yes_type() {
    yes!(
        (check-valid
            (declare-sort T)
            (declare-const x T)
            (assert
                (= x x)
            )
        )
    );
}

#[test]
fn no_type() {
    no!(
        (check-valid
            (declare-sort T)
            (declare-const x T)
            (declare-const y T)
            (assert
                (= x y)
            )
        )
    );
}

#[test]
fn yes_assign() {
    no!(
        (check-valid
            (declare-var x Int)
            (declare-var y Int)
            (block
                (assume (= x 100))
                (assume (= y 200))
                (assign x (+ x 1))
                (assign x (+ x 1))
                (assert (= x 102))
                (assert (= y 100))
            )
        )
    );
}

#[test]
fn no_assign() {
    no!(
        (check-valid
            (declare-var x Int)
            (declare-var y Int)
            (block
                (assume (= x 100))
                (assume (= y 200))
                (assign x (+ x 1))
                (assign x (+ x 1))
                (assert (not (= x 102)))
            )
        )
    );
}

#[test]
fn untyped_scope1() {
    untyped!(
        (declare-const x Int)
        (declare-const x Int) // error: x already in scope
    );
}

#[test]
fn untyped_scope2() {
    untyped!(
        (declare-const x Int)
        (push)
            (declare-const x Int) // error: x already in scope
        (pop)
    );
}

#[test]
fn untyped_scope3() {
    untyped!(
        (declare-const x Int)
        (check-valid
            (declare-const x Int) // error: x already in scope
            (assert true)
        )
    );
}

#[test]
fn untyped_scope4() {
    untyped!(
        (declare-const x Int)
        (check-valid
            (declare-var x Int) // error: x already in scope
            (assert true)
        )
    );
}

#[test]
fn untyped_scope5() {
    untyped!(
        (declare-const "x@0" Int)
        (check-valid
            (declare-var x Int) // error: x@0 already in scope
            (assert true)
        )
    );
}

#[test]
fn untyped_scope6() {
    untyped!(
        (declare-var x Int) // error: declare-var not allowed in global scope
    );
}

#[test]
fn untyped_scope7() {
    untyped!(
        (declare-const x Int)
        (declare-fun x (Int Int) Int) // error: x already in scope
    );
}

#[test]
fn yes_scope1() {
    yes!(
        (push)
            (declare-const x Int)
        (pop)
        (push)
            (declare-const x Int)
        (pop)
    );
}

#[test]
fn yes_scope2() {
    yes!(
        (push)
            (declare-const x Int)
        (pop)
        (declare-const x Int)
    );
}

#[test]
fn yes_scope3() {
    yes!(
        (push)
            (declare-const x Int)
        (pop)
        (check-valid
            (declare-var x Int)
            (assert true)
        )
    );
}

#[test]
fn yes_fun1() {
    yes!(
        (check-valid
            (declare-fun f (Int Bool) Bool)
            (block
                (assume (f 10 true))
                (assert (f 10 true))
            )
        )
    )
}

#[test]
fn no_fun1() {
    no!(
        (check-valid
            (declare-fun f (Int Bool) Bool)
            (block
                (assume (f 10 true))
                (assert (f 11 true))
            )
        )
    )
}

#[test]
fn no_typing1() {
    untyped!(
        (axiom 10)
    )
}

#[test]
fn no_typing2() {
    untyped!(
        (axiom b)
    )
}

#[test]
fn no_typing3() {
    untyped!(
        (declare-fun f (Int Bool) Bool)
        (axiom (f 10))
    )
}

#[test]
fn no_typing4() {
    untyped!(
        (declare-fun f (Int Bool) Bool)
        (axiom (f 10 20))
    )
}

#[test]
fn no_typing5() {
    untyped!(
        (check-valid
            (declare-var x Int)
            (assign x true)
        )
    )
}

#[test]
fn yes_let1() {
    yes!(
        (check-valid
            (assert (let ((x 10) (y 20)) (< x y)))
        )
    )
}

#[test]
fn yes_let2() {
    yes!(
        (check-valid
            (assert
                (let ((x 10) (y 20))
                    (=
                        40
                        (let ((x (+ x 10))) (+ x y)) // can shadow other let/forall bindings
                    )
                )
            )
        )
    )
}

#[test]
fn yes_let3() {
    yes!(
        (check-valid
            (assert
                (let ((x 10) (y 20))
                    (=
                        (let ((x (+ x 10))) (+ x y)) // can shadow other let/forall bindings
                        (+ x x y) // make sure old values are restored here
                    )
                )
            )
        )
    )
}

#[test]
fn yes_let4() {
    yes!(
        (check-valid
            (assert
                (let ((x true) (y 20))
                    (and
                        (=
                            (let ((x (+ y 10))) (+ x y))
                            50
                        )
                        x // make sure old type is restored here
                    )
                )
            )
        )
    )
}

#[test]
fn untyped_let1() {
    untyped!(
        (check-valid
            (assert (let ((x 10) (x 20)) true)) // no duplicates allowed in single let
        )
    )
}

#[test]
fn untyped_let2() {
    untyped!(
        (declare-const y Int)
        (check-valid
            (assert (let ((x 10) (y 20)) true)) // cannot shadow global name
        )
    )
}

#[test]
fn untyped_let3() {
    untyped!(
        (declare-fun y (Int) Int)
        (check-valid
            (assert (let ((x 10) (y 20)) true)) // cannot shadow global name
        )
    )
}

#[test]
fn untyped_let4() {
    untyped!(
        (declare-sort y)
        (check-valid
            (assert (let ((x 10) (y 20)) true)) // cannot shadow global name
        )
    )
}

#[test]
fn no_let1() {
    no!(
        (check-valid
            (assert
                (let ((x 10) (y 20))
                    (=
                        (let ((x (+ x 10))) (+ x y))
                        (+ x y) // make sure old values are restored here
                    )
                )
            )
        )
    )
}

#[test]
fn yes_forall1() {
    yes!(
        (check-valid
            (assert
                (forall ((i Int)) true)
            )
        )
    )
}

#[test]
fn yes_forall2() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (forall ((i Int) (j Int)) (f i j))
                    (f 10 20)
                )
            )
        )
    )
}

#[test]
fn yes_forall3() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (!
                        (forall ((i Int) (j Int)) (f i j))
                        ":pattern" ((f i j))
                    )
                    (f 10 20)
                )
            )
        )
    )
}

#[test]
fn yes_forall4() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (declare-fun g (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (!
                        (forall ((i Int) (j Int)) (f i j))
                        ":pattern" ((g i j))
                        ":pattern" ((f i j))
                    )
                    (f 10 20)
                )
            )
        )
    )
}

#[test]
fn yes_forall5() {
    yes!(
        (declare-fun f (Int) Bool)
        (declare-fun g (Int) Bool)
        (axiom
            (!
                (forall ((i Int) (j Int)) (=> (f i) (g j)))
                ":pattern" ((f i) (g j))
            )
        )
        (check-valid
            (assert
                (=> (f 10) (g 10))
            )
        )
    )
}

#[test]
fn no_forall1() {
    no!(
        (check-valid
            (assert
                (forall ((i Int)) false)
            )
        )
    )
}

#[test]
fn no_forall2() {
    no!(
        (declare-fun f (Int Int) Bool)
        (declare-fun g (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (!
                        (forall ((i Int) (j Int)) (f i j))
                        ":pattern" ((g i j))
                    )
                    (f 10 20) // doesn't match (g i j)
                )
            )
        )
    )
}

#[test]
fn untyped_forall1() {
    untyped!(
        (check-valid
            (assert
                (let
                    ((
                        x
                        (forall ((i Int)) i)
                    ))
                    true
                )
            )
        )
    )
}

#[test]
fn yes_exists1() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (f 10 20)
                    (!
                        (exists ((i Int) (j Int)) (f i j))
                        ":pattern" ((f i j))
                    )
                )
            )
        )
    )
}

#[test]
fn no_exists1() {
    no!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (!
                        (exists ((i Int) (j Int)) (f i j))
                        ":pattern" ((f i j))
                    )
                    (f 10 20)
                )
            )
        )
    )
}

#[test]
fn yes_ite1() {
    yes!(
        (check-valid
            (block
                (assert (= (ite true 10 20) 10))
                (assert (= (ite false 10 20) 20))
            )
        )
    )
}

#[test]
fn no_ite1() {
    no!(
        (check-valid
            (assert (= (ite true 10 20) 20))
        )
    )
}

#[test]
fn untyped_ite1() {
    untyped!(
        (check-valid
            (assert (= (ite 0 10 20) 20))
        )
    )
}

#[test]
fn untyped_ite2() {
    untyped!(
        (check-valid
            (assert (= (ite true 10 true) 20))
        )
    )
}