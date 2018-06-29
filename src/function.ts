export type Supplier<T> = () => T;

export function memoizeSupplier<T>(supplier: Supplier<T>): Supplier<T> {
    let p: T | null = null;

    return () => p === null ? (p = supplier()) : p;
}