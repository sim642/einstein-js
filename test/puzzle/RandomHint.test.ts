import "mocha";
import {expect} from "chai";
import {BoardOptions} from "../../src/puzzle/board/Board";
import {SingleBoard} from "../../src/puzzle/board/SingleBoard";
import {RandomHintFactory} from "../../src/puzzle/RandomHint";
import {Distribution, ObjectDistribution} from "../../src/math/distribution";
import {contextObject, param} from "../param";
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
        function testDistribution(options: BoardOptions, expectedObject: ObjectDistribution) {
            let board = SingleBoard.random(options);
            let observed: Distribution<string> = Distribution.monteCarlo(10000, () => {
                let hint = factory.random(board);
                return (hint.constructor as any).name; // TODO: don't use any
            });

            let expected: Distribution<string> = Distribution.fromObject(expectedObject);

            Distribution.expectSame(observed, expected, 0.001);
        }

        context("large enough board", function () {
            param<BoardOptions>([
                {rows: 6, cols: 6},
                {rows: 5, cols: 5},
                {rows: 4, cols: 4},
                {rows: 3, cols: 3},
            ], function (options) {
                it("should have original einstein 2.0 hint distribution", function () {
                    testDistribution(options, {
                        AdjacentHint: 4,
                        OpenHint: 1,
                        SameColumnHint: 2,
                        DirectionHint: 4,
                        BetweenHint: 3
                    });
                })
            });
        });

        context("too small board", function () {
            contextObject<BoardOptions>({rows: 2, cols: 2}, function (options) {
                it("should have original einstein 2.0 hint distribution without BetweenHint", function () {
                    testDistribution(options, {
                        AdjacentHint: 4,
                        OpenHint: 1,
                        SameColumnHint: 2,
                        DirectionHint: 4
                    });
                })
            });
        });
    });
});