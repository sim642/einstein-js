import {expect} from "chai";
import {ChiSq} from "./ChiSq";

export interface Distribution<T> {
    get(value: T): number | undefined;

    n: number;
    classes: number;

    mapFreqs(f: (freq: number, value: T) => number): Distribution<T>;
    map<U>(f: (freq: number, value: T) => U): U[];
    filter(p: (freq: number, value: T) => boolean): Distribution<T>;

    scale(targetN: number): Distribution<T>;
    scaleTo<U>(targetDist: Distribution<U>): Distribution<T>;

    random(): T;
}

export namespace Distribution {
    export function expectSame<T>(observed: Distribution<T>, expected: Distribution<T>, significanceLevel: number): void {
        let pValue = ChiSq.test(observed, expected);
        expect(pValue).to.not.be.lessThan(significanceLevel);
    }
}