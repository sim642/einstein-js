import * as Z3Factory from "./z3smt2w";

export let z3: Z3 | null = null;

var wasmURL = 'z3smt2w.wasm';
var wasmXHR = new XMLHttpRequest();
wasmXHR.open('GET', wasmURL, true);
wasmXHR.responseType = 'arraybuffer';
wasmXHR.onload = function() {

    var z3smt2 = Z3Factory({
        wasmBinary: wasmXHR.response
    });

    z3 = new Z3(z3smt2);
};
wasmXHR.send(null);

export class Z3 {
    constructor(private z3smt2) {

    }

    init = this.z3smt2.cwrap('smt2Init', 'number', []);
    setParam = this.z3smt2.cwrap('smt2SetParam', null, ['string', 'string']);
    ask = this.z3smt2.cwrap('smt2Ask', 'string', ['number', 'string']);
    destroy = this.z3smt2.cwrap('smt2Destroy', null, ['number']);
}

