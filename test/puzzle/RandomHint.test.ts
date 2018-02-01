import "mocha";
import {expect} from "chai";
import {ObjectDistribution} from "../../src/math/ObjectDistribution";
import {SingleBoard} from "../../src/puzzle/board/SingleBoard";
import {RandomHintFactory} from "../../src/puzzle/RandomHint";
import {Distribution} from "../../src/math/Distribution";
import {paramBoardOptionsExtra} from "./paramPuzzle";

describe("RandomHintFactory", function () {
    const factory = new RandomHintFactory();

    describe("#supports()", function () {
        context("large enough board", function () {
            paramBoardOptionsExtra([
                {rows: 1, cols: 2},
                {rows: 2, cols: 1},
                {rows: 1, cols: 1}
            ], function (options) {
                it("should return true", function () {
                    expect(factory.supports(options)).to.be.true;
                });
            });
        });

        // no too small boards
    });


    describe("#random()", function () {
        it("should have original einstein 2.0 hint distribution", function () {
            let board = SingleBoard.random({rows: 6, cols: 6});
            let observed: Distribution<string> = ObjectDistribution.monteCarlo(10000, () => {
                let hint = factory.random(board);
                return (hint.constructor as any).name; // TODO: don't use any
            });

            let expected: Distribution<string> = new ObjectDistribution({
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