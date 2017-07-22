import {expect} from "chai";
import * as _ from "lodash";
import "mocha";
import {MultiBoard} from "../../../src/puzzle/board/MultiBoard";
import {AdjacentHint} from "../../../src/puzzle/hint/AdjacentHint";
import {HintType} from "../../../src/puzzle/hint/Hint";

function equivalents(hint: AdjacentHint): AdjacentHint[] {
    return [
        new AdjacentHint(hint.row1, hint.variant1, hint.row2, hint.variant2),
        new AdjacentHint(hint.row2, hint.variant2, hint.row1, hint.variant1)
    ];
}

function param<T>(values: T[], callback: (value: T) => void): void {
    _.forEach(values, value => {
        context(JSON.stringify(value), function () {
            callback(value);
        });
    });
}

describe("AdjacentHint", function () {
    describe("#apply()", function () {
        let board: MultiBoard;
        beforeEach(function () {
            board = MultiBoard.full({rows: 3, cols: 3});
        });

        context("first column", function () {
            param(equivalents(new AdjacentHint(1, 0, 0, 2)), hint => {
                beforeEach(function () {
                    board.remove(0, 1, 2);
                });

                it("should remove variant if other variant cannot be adjacent", function () {
                    board.applyHint(hint);

                    expect(board.isPossible(1, 0, 0)).to.be.false;
                });

                it("should return true if variant is removed", function () {
                    let changed = board.applyHint(hint);

                    expect(changed).to.be.true;
                });
            });
        });

        context("last column", function () {
            param(equivalents(new AdjacentHint(1, 0, 0, 2)), hint => {
                beforeEach(function () {
                    board.remove(0, 1, 2);
                });

                it("should remove variant if other variant cannot be adjacent", function () {
                    board.applyHint(hint);

                    expect(board.isPossible(1, 2, 0)).to.be.false;
                });

                it("should return true if variant is removed", function () {
                    let changed = board.applyHint(hint);

                    expect(changed).to.be.true;
                });
            });
        });

        context("other column", function () {
            param(equivalents(new AdjacentHint(1, 0, 0, 2)), hint => {
                beforeEach(function () {
                    board.remove(0, 0, 2);
                    board.remove(0, 2, 2);
                });

                it("should remove variant if other variant cannot be adjacent", function () {
                    board.applyHint(hint);

                    expect(board.isPossible(1, 1, 0)).to.be.false;
                });

                it("should return true if variant is removed", function () {
                    let changed = board.applyHint(hint);

                    expect(changed).to.be.true;
                });
            });
        });

        it("should return false if variant is not removed", function () {
            let changed = board.applyHint(new AdjacentHint(1, 0, 0, 2));

            expect(changed).to.be.false;
        });
    });

    it("should have Horizontal type", function () {
        expect(new AdjacentHint(0, 1, 2, 3).getType()).to.equal(HintType.Horizontal);
    });
});