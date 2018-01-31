import * as _ from "lodash";
import {Distribution} from "./distribution";
import * as chiSquared from "chi-squared";

export module ChiSq {
    export function testStatistic<T>(observed: Distribution<T>, expected: Distribution<T>): number {
        expected = Distribution.scaleTo(expected, observed);
        return _.sumBy(expected, ([value, expectedFreq]) => {
            let observedFreq = Distribution.get(observed, value) || 0;
            return Math.pow(observedFreq - expectedFreq, 2) / expectedFreq;
        });
    }

    export function test<T>(observed: Distribution<T>, expected: Distribution<T>): number {
        let statistic = testStatistic(observed, expected);
        let df = Distribution.classes(expected) - 1;
        return 1 - chiSquared.cdf(statistic, df);
    }
}