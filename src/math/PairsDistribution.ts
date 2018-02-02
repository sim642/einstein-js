import * as _ from "lodash";
import {AbstractDistribution} from "./AbstractDistribution";

export type NumericPair<T> = [T, number];
export type NumericPairs<T> = NumericPair<T>[];

export class PairsDistribution<T> extends AbstractDistribution<T> {
    constructor(private readonly pairs: NumericPairs<T>) {
        super();
    }

    private find(value: T): NumericPair<T> | undefined {
        return PairsDistribution.find(this.pairs, value);
    }

    get(value: T): number | undefined {
        const pair = this.find(value);
        return pair !== undefined ? pair[1] : undefined;
    }

    get n(): number {
        return _.sumBy(this.pairs, pair => pair[1]);
    }

    get classes(): number {
        return this.pairs.length;
    }

    mapFreqs(f: (freq: number, value: T) => number): PairsDistribution<T> {
        return new PairsDistribution(this.map((freq, value) => [value, f(freq, value)]) as NumericPairs<T>);
    }

    map<U>(f: (freq: number, value: T) => U): U[] {
        return _.map(this.pairs, ([value, freq]) => f(freq, value));
    }

    filter(p: (freq: number, value: T) => boolean): PairsDistribution<T> {
        return new PairsDistribution<T>(_.filter(this.pairs, ([value, freq]) => p(freq, value)));
    }

    private static find<T>(pairs: NumericPairs<T>, value: T): NumericPair<T> | undefined {
        return _.find(pairs, pair => pair[0] === value);
    }

    static monteCarlo<T>(n: number, generator: () => T): PairsDistribution<T> {
        let observed: NumericPairs<T> = [];
        for (let i = 0; i < n; i++) {
            let value = generator();
            let pair = PairsDistribution.find(observed, value);
            if (pair === undefined) {
                pair = [value, 0];
                observed.push(pair);
            }
            pair[1]++;
        }
        return new PairsDistribution<T>(observed);
    }

    protected toPairs(): NumericPairs<T> {
        return this.pairs;
    }
}