import {getZ3, Z3} from "./z3/Z3";

async function main() {
    console.log("getting Z3...");
    let z3: Z3 = await getZ3();
    console.log("got Z3");

    let cfg = z3.mk_config();
    let ctx = z3.mk_context(cfg);
    z3.set_error_handler(ctx, z3.errorHandler);
    z3.del_config(cfg);

    let smtlib = `(declare-const x00 Int)
(assert (and (<= 0 x00) (< x00 3)))
(declare-const x01 Int)
(assert (and (<= 0 x01) (< x01 3)))
(declare-const x02 Int)
(assert (and (<= 0 x02) (< x02 3)))
(assert (distinct x00 x01 x02))
(declare-const x10 Int)
(assert (and (<= 0 x10) (< x10 3)))
(declare-const x11 Int)
(assert (and (<= 0 x11) (< x11 3)))
(declare-const x12 Int)
(assert (and (<= 0 x12) (< x12 3)))
(assert (distinct x10 x11 x12))
(assert (or (distinct x02 0) (distinct x01 1) (distinct x00 2) (distinct x10 0) (distinct x11 1) (distinct x12 2)))
(check-sat)
(assert (! (< x02 x00) :named h0))
(assert (! (< x10 x12) :named h1))
(assert (! (= x00 x12) :named h2))
(assert (! (= x01 x11) :named h3))
(assert (! (or (and (= x11 (+ x10 1)) (= x11 (- x00 1))) (and (= x11 (+ x00 1)) (= x11 (- x10 1)))) :named h4))
(check-sat)`;

    let lines = smtlib.split(/\r?\n/);
    for (let line of lines) {
        let ret = z3.eval_smtlib2_string(ctx, line).trim();
        console.log(ret);
    }

    z3.del_context(ctx);
}

console.log("Output should be 'sat unsat', not 'unknown sat'");
main();