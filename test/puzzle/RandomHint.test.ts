import "mocha";
import {SingleBoard} from "../../src/puzzle/board/SingleBoard";
import {RandomHintFactory} from "../../src/puzzle/RandomHint";
import {Distribution} from "../../src/math/distribution";

describe("RandomHintFactory", function () {
    const factory = new RandomHintFactory();

    describe("#random()", function () {
        it("should have original einstein 2.0 hint distribution", function () {
            let board = SingleBoard.random({rows: 6, cols: 6});
            let observed: Distribution<string> = Distribution.monteCarlo(10000, () => {
                let hint = factory.random(board);
                return (hint.constructor as any).name; // TODO: don't use any
            });

            let expected: Distribution<string> = Distribution.fromObject({
                AdjacentHint: 4,
                OpenHint: 1,
                SameColumnHint: 2,
                DirectionHint: 4,
                BetweenHint: 3
            });

            Distribution.expectSame(observed, expected, 0.001);
        });
    });
});