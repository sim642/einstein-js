import * as _ from "lodash";
import {expect} from "chai";
import {ChiSq} from "./statistics";

export type Distribution<T> = [T, number][];

interface ObjectDistribution {
    [value: string]: number;
}

export namespace Distribution {
    export function fromObject(object: ObjectDistribution): Distribution<string> {
        return _.toPairs(object);
    }

    export function find<T>(dist: Distribution<T>, value: T): [T, number] | undefined {
        return _.find(dist, pair => pair[0] === value); // TODO optimize
    }

    export function get<T>(dist: Distribution<T>, value: T): number | undefined {
        let pair = find(dist, value);
        return pair !== undefined ? pair[1] : undefined;
    }

    export function monteCarlo<T>(n: number, generator: () => T): Distribution<T> {
        let observed: Distribution<T> = [];
        for (let i = 0; i < n; i++) {
            let value = generator();
            let pair = find(observed, value);
            if (pair === undefined) {
                pair = [value, 0];
                observed.push(pair);
            }
            pair[1]++;
        }
        return observed;
    }

    export function n<T>(dist: Distribution<T>): number {
        return _.sumBy(dist, pair => pair[1]);
    }

    export function classes<T>(dist: Distribution<T>): number {
        return _.size(dist);
    }

    export function scale<T>(dist: Distribution<T>, targetN: number): Distribution<T> {
        let sourceN = n(dist);
        return _.map(dist, ([value, freq]) => [value, freq / sourceN * targetN]) as Distribution<T>; // TODO type safe
    }

    export function scaleTo<T, U>(dist: Distribution<T>, targetDist: Distribution<U>): Distribution<T> {
        return scale(dist, n(targetDist));
    }

    export function expectSame<T>(observed: Distribution<T>, expected: Distribution<T>, significanceLevel: number): void {
        let pValue = ChiSq.test(observed, expected);
        expect(pValue).to.not.be.lessThan(significanceLevel);
    }
}