import * as _ from "lodash";
import {expect} from "chai";
import {ChiSq} from "./statistics";

export interface Distribution {
    [value: string]: number;
}

export namespace Distribution {
    export function monteCarlo(n: number, generator: () => string): Distribution {
        let observed: Distribution = {};
        for (let i = 0; i < n; i++) {
            let value = generator();
            if (!(value in observed))
                observed[value] = 0;
            observed[value]++;
        }
        return observed;
    }

    export function n(dist: Distribution): number {
        return _.sum(_.values(dist));
    }

    export function classes(dist: Distribution): number {
        return _.size(dist);
    }

    export function scale(dist: Distribution, targetN: number): Distribution {
        let sourceN = n(dist);
        return _.mapValues(dist, freq => freq / sourceN * targetN);
    }

    export function scaleTo(dist: Distribution, targetDist: Distribution): Distribution {
        return scale(dist, n(targetDist));
    }

    export function expectSame(observed: Distribution, expected: Distribution, significanceLevel: number): void {
        let pValue = ChiSq.test(observed, expected);
        expect(pValue).to.not.be.lessThan(significanceLevel);
    }
}