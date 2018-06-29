import * as Z3Em from "z3em";
import * as z3emWasm from "z3em/z3em.wasm";
import {memoizeSupplier} from "../function";

export const getZ3 = memoizeSupplier(() =>
    new Promise<Z3>((resolve, reject) => {
        const z3em = Z3Em({
            wasmBinaryFile: z3emWasm,
            onRuntimeInitialized: () => {
                const z3 = new Z3(z3em);
                alert("Z3 armed");
                resolve(z3);
            }
        });
    }));

export class Z3 {
    constructor(private z3em) {

    }

    mk_config = this.z3em.cwrap("Z3_mk_config", "number", []);
    mk_context = this.z3em.cwrap("Z3_mk_context", "number", ["number"]);
    del_config = this.z3em.cwrap("Z3_del_config", null, ["number"]);
    del_context = this.z3em.cwrap("Z3_del_context", null, ["number"]);
    eval_smtlib2_string = this.z3em.cwrap("Z3_eval_smtlib2_string", "string", ["number", "string"]);
}
