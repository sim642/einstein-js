import * as _ from "lodash";
import {expect} from "chai";
import "mocha";
import {RandomHintFactory} from "../../src/puzzle/RandomHint";
import {SingleBoard} from "../../src/puzzle/board/SingleBoard";
import * as chi from "chi-squared";

interface HintDistribution {
    [hint: string]: number;
}

describe("RandomHintFactory", function () {
    const factory = new RandomHintFactory();

    describe("#random()", function () {
        it("should have original einstein 2.0 hint distribution", function () {
            const N = 100000;

            let observed: HintDistribution = {};
            let board = SingleBoard.random({rows: 6, cols: 6});
            for (let i = 0; i < N; i++) {
                let hint = factory.random(board);
                let name = (hint.constructor as any).name;
                if (!(name in observed))
                    observed[name] = 0;
                observed[name]++;
            }
            console.log(observed);

            let expected: HintDistribution = {
                AdjacentHint: 4,
                OpenHint: 1,
                SameColumnHint: 2,
                DirectionHint: 4,
                BetweenHint: 3
            };
            let sum = _.sum(_.values(expected));
            expected = _.mapValues(expected, freq => freq / sum * N);
            console.log(expected);

            let chiSq = _.sum(_.values(_.mapValues(expected, (expectedFreq, name) => {
                let observedFreq = observed[name] || 0;
                return Math.pow(observedFreq - expectedFreq, 2) / expectedFreq;
            })));
            console.log(chiSq);
            let df = _.size(expected) - 1;
            let p = 1 - chi.cdf(chiSq, df);
            // let p = chi.cdf(chiSq, df);
            console.log(p);
            // expect(p).to.be.lessThan(0.05);
            // expect(p).to.be.greaterThan(0.5);
            // expect(p < 0.05).to.be.false;
            expect(p).to.not.be.lessThan(0.05);
            // expect(p >= 0.05).to.be.true;
            // expect(p < 0.95).to.be.true;
            // expect(p > 0.95).to.be.false;
            // expect(p).to.be.at.most(0.95);
        });
    });
});