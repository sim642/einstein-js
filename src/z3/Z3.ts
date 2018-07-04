import * as Z3Em from "z3em";
import * as z3emWasm from "z3em/z3em.wasm";
import {memoizeSupplier} from "../function";
import {Wasm} from "../storage/Wasm";

class ResolveWrapper<T> {
    constructor(public value: T) {

    }
}

function createZ3Em(z3emOptions): Promise<ResolveWrapper<Z3Em>> {
    return new Promise((resolve, reject) => {
        const z3em = Z3Em({
            ...z3emOptions,
            onRuntimeInitialized: () => {
                resolve(new ResolveWrapper(z3em)); // TODO: unwrapped return freezes browser, WTF?
            }
            // TODO: handle failed
        });
    });
}

// for caching WASM in Chrome: chrome://flags/#enable-webassembly

export const getZ3 = memoizeSupplier(() =>
    Wasm.getCached(z3emWasm).then( module => {
        let z3emOptions;
        if (module !== undefined) {
            z3emOptions = {
                instantiateWasm: (importObject, receiveInstance) => {
                    console.debug("instantiateWasm");
                    WebAssembly.instantiate(module, importObject).then(instance =>
                        receiveInstance(instance, module)
                    );
                    return {}; // instantiateWasm is async
                }
            };
        }
        else {
            z3emOptions = {
                locateFile: () => z3emWasm,
                onReceiveInstance: (instance, module) => {
                    console.debug("onReceiveInstance");
                    Wasm.cache(z3emWasm, module);
                }
            };
        }

        console.debug("Z3 arming...");
        return createZ3Em(z3emOptions).then(resolveWrapper => {
            let z3em = resolveWrapper.value;

            const z3 = new Z3(z3em);
            console.log("Z3 armed");
            return z3;
        });
    })
);

export class Z3 {
    constructor(private z3em) {

    }

    errorHandler = this.z3em.addFunction(function (ctx, e) {
        console.error(`Z3 (${ctx}): ${e}`);
    }, "vii");

    mk_config = this.z3em.cwrap("Z3_mk_config", "number", []);
    mk_context = this.z3em.cwrap("Z3_mk_context", "number", ["number"]);
    del_config = this.z3em.cwrap("Z3_del_config", null, ["number"]);
    del_context = this.z3em.cwrap("Z3_del_context", null, ["number"]);
    eval_smtlib2_string = this.z3em.cwrap("Z3_eval_smtlib2_string", "string", ["number", "string"]);
    global_param_set = this.z3em.cwrap("Z3_global_param_set", null, ["string", "string"]);
    set_error_handler = this.z3em.cwrap("Z3_set_error_handler", null, ["number", "number"]);
}
