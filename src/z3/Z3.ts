// import * as Z3Factory from "./z3smt2w";
import * as Z3Em from "z3em";
// let z3emWasm = require("z3em/z3em.wasm") as string;
import * as z3emWasm from "z3em/z3em.wasm";

export let z3: Z3 | null = null;

var wasmURL = z3emWasm;
// var wasmXHR = new XMLHttpRequest();
// wasmXHR.open('GET', wasmURL, true);
// wasmXHR.responseType = 'arraybuffer';
// wasmXHR.onload = function() {

    var z3smt2 = Z3Em({
        // wasmBinary: wasmXHR.response,
        wasmBinaryFile: wasmURL,
        onRuntimeInitialized: () => {
            z3 = new Z3(z3smt2);
            alert("Z3 armed");
        }
    });
// };
// wasmXHR.send(null);

export class Z3 {
    constructor(private z3smt2) {

    }

    /*init = this.z3smt2.cwrap('smt2Init', 'number', []);
    setParam = this.z3smt2.cwrap('smt2SetParam', null, ['string', 'string']);
    ask = this.z3smt2.cwrap('smt2Ask', 'string', ['number', 'string']);
    destroy = this.z3smt2.cwrap('smt2Destroy', null, ['number']);*/

    mk_config = this.z3smt2.cwrap("Z3_mk_config", "number", []);
    mk_context = this.z3smt2.cwrap("Z3_mk_context", "number", ["number"]);
    del_config = this.z3smt2.cwrap("Z3_del_config", null, ["number"]);
    del_context = this.z3smt2.cwrap("Z3_del_context", null, ["number"]);
    eval_smtlib2_string = this.z3smt2.cwrap("Z3_eval_smtlib2_string", "string", ["number", "string"]);
}

