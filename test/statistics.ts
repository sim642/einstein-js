import * as _ from "lodash";
import {Distribution} from "./distribution";
import * as chiSquared from "chi-squared";

export module ChiSq {
    export function testStatistic(observed: Distribution, expected: Distribution): number {
        expected = Distribution.scaleTo(expected, observed);
        return _.sum(_.values(_.mapValues(expected, (expectedFreq, value) => {
            let observedFreq = observed[value] || 0;
            return Math.pow(observedFreq - expectedFreq, 2) / expectedFreq;
        })));
    }

    export function test(observed: Distribution, expected: Distribution): number {
        let statistic = testStatistic(observed, expected);
        let df = Distribution.classes(expected) - 1;
        return 1 - chiSquared.cdf(statistic, df);
    }
}