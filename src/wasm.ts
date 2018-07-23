export function isWasmSupported(): boolean {
    // https://stackoverflow.com/a/47880734/854540
    // TODO more thorough check
    return typeof WebAssembly === "object";
}