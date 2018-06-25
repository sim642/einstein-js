import * as _ from "lodash";
import {Distribution} from "./Distribution";
import * as chiSquared from "chi-squared";

export namespace ChiSq {
    export function testStatistic<T>(observed: Distribution<T>, expected: Distribution<T>): number {
        expected = expected.scaleTo(observed);
        return _.sum(expected.map((expectedFreq, value) => {
            let observedFreq = observed.get(value) || 0;
            return Math.pow(observedFreq - expectedFreq, 2) / expectedFreq;
        }));
    }

    export function test<T>(observed: Distribution<T>, expected: Distribution<T>): number {
        let statistic = testStatistic(observed, expected);
        let df = expected.classes - 1;
        return 1 - chiSquared.cdf(statistic, df);
    }
}