declare module "z3em/z3em.wasm" {
    const filename: string;
    export = filename; // https://github.com/TypeStrong/ts-loader/issues/344
}