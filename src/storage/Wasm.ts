import {db} from "./db";

export interface WasmItem {
    url: string;
    module: WebAssembly.Module;
}

export namespace Wasm {
    export function getCached(url): Promise<WebAssembly.Module> {
        return db.wasm.get(url, wasmItem => {
            console.log("wasm from db:");
            console.debug(wasmItem);
            return wasmItem !== undefined ? wasmItem.module : undefined;
        });
    }

    export function cache(url: string, module: WebAssembly.Module) {
        let wasmItem = {
            url: url,
            module: module
        };
        console.log("wasm to db:");
        console.debug(wasmItem);
        db.transaction("rw", db.wasm, () =>
            db.wasm.clear().then(() =>
                db.wasm.put(wasmItem)
            )
        ).then(() => console.log("wasm cached"));
    }
}