import * as _ from "lodash";
import {AbstractDistribution} from "./AbstractDistribution";

export type NumericObject = {
    [value: string]: number;
}

export class ObjectDistribution extends AbstractDistribution<string> {
    constructor(private readonly object: NumericObject) {
        super();
    }

    get n(): number {
        return _.sum(_.values(this.object));
    }

    get classes(): number {
        return _.size(this.object);
    }

    get(value: string): number | undefined {
        return this.object[value];
    }

    mapFreqs(f: (freq: number, value: string) => number): ObjectDistribution {
        return new ObjectDistribution(_.mapValues(this.object, f));
    }

    map<U>(f: (freq: number, value: string) => U): U[] {
        return _.map(this.object, f);
    }

    filter(p: (freq: number, value: string) => boolean): ObjectDistribution {
        return new ObjectDistribution(_.pickBy(this.object, p));
    }

    static monteCarlo(n: number, generator: () => string): ObjectDistribution {
        let observed: NumericObject = {};
        for (let i = 0; i < n; i++) {
            let value = generator();
            if (!(value in observed))
                observed[value] = 0;
            observed[value]++;
        }
        return new ObjectDistribution(observed);
    }
}