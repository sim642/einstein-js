import {expect} from "chai";
import "mocha";
import {MultiBoard} from "../../../src/puzzle/board/MultiBoard";
import {BetweenHint, BetweenHintFactory} from "../../../src/puzzle/hint/BetweenHint";
import {HintType} from "../../../src/puzzle/hint/Hint";
import {param} from "../../param";
import {BoardOptions} from "../../../src/puzzle/board/Board";
import {SingleBoard} from "../../../src/puzzle/board/SingleBoard";

function equivalents(hint: BetweenHint): BetweenHint[] {
    return [
        new BetweenHint(hint.row1, hint.variant1, hint.rowMiddle, hint.variantMiddle, hint.row2, hint.variant2),
        new BetweenHint(hint.row2, hint.variant2, hint.rowMiddle, hint.variantMiddle, hint.row1, hint.variant1)
    ];
}

const paramEquivalents = param.generate(equivalents);

describe("BetweenHint", function () {
    describe("#apply()", function () {
        let board: MultiBoard;
        beforeEach(function () {
            board = MultiBoard.full({rows: 5, cols: 5});
        });

        context("first column", function () {
            paramEquivalents(new BetweenHint(0, 1, 1, 2, 2, 3), hint => {
                it("should remove middle variant", function () {
                    board.applyHint(hint);

                    expect(board.isPossible(1, 0, 2)).to.be.false;
                });

                it("should remove one side variant if middle variant cannot be adjacent", function () {
                    board.remove(1, 1, 2);

                    board.applyHint(hint);

                    expect(board.isPossible(0, 0, 1)).to.be.false;
                });

                it("should remove one side variant if other side variant cannot be two columns away", function () {
                    board.remove(2, 2, 3);

                    board.applyHint(hint);

                    expect(board.isPossible(0, 0, 1)).to.be.false;
                });

                it("should return true if variant is removed", function () {
                    let changed = board.applyHint(hint);

                    expect(changed).to.be.true;
                });
            });
        });

        context("last column", function () {
            paramEquivalents(new BetweenHint(0, 1, 1, 2, 2, 3), hint => {
                it("should remove middle variant", function () {
                    board.applyHint(hint);

                    expect(board.isPossible(1, 4, 2)).to.be.false;
                });

                it("should remove one side variant if middle variant cannot be adjacent", function () {
                    board.remove(1, 3, 2);

                    board.applyHint(hint);

                    expect(board.isPossible(0, 4, 1)).to.be.false;
                });

                it("should remove one side variant if other side variant cannot be two columns away", function () {
                    board.remove(2, 2, 3);

                    board.applyHint(hint);

                    expect(board.isPossible(0, 4, 1)).to.be.false;
                });

                it("should return true if variant is removed", function () {
                    let changed = board.applyHint(hint);

                    expect(changed).to.be.true;
                });
            });
        });

        context("other column", function () {
            paramEquivalents(new BetweenHint(0, 1, 1, 2, 2, 3), hint => {
                it("should remove middle variant if side variant cannot be adjacent", function () {
                    board.remove(0, 1, 1);
                    board.remove(0, 3, 1);

                    board.applyHint(hint);

                    expect(board.isPossible(1, 2, 2)).to.be.false;
                });

                it("should remove one side variant if middle variant cannot be adjacent", function () {
                    board.remove(1, 1, 2);
                    board.remove(1, 3, 2);

                    board.applyHint(hint);

                    expect(board.isPossible(0, 2, 1)).to.be.false;
                });

                it("should remove one side variant if other side variant cannot be two columns away", function () {
                    board.remove(2, 0, 3);
                    board.remove(2, 4, 3);

                    board.applyHint(hint);

                    expect(board.isPossible(0, 2, 1)).to.be.false;
                });

                it("should return true if variant is removed", function () {
                    board.remove(0, 1, 1);
                    board.remove(0, 3, 1);

                    let changed = board.applyHint(hint);

                    expect(changed).to.be.true;
                });
            });
        });

        paramEquivalents(new BetweenHint(0, 1, 1, 2, 2, 3), hint => {
            it("should not remove more variants than necessary", function () {
                board.remove(0, 1, 1);
                board.remove(0, 3, 1);

                board.applyHint(hint);

                let expectedBoard = MultiBoard.full({rows: 5, cols: 5});
                expectedBoard.remove(0, 1, 1);
                expectedBoard.remove(0, 3, 1);
                expectedBoard.remove(1, 2, 2);
                expectedBoard.remove(1, 0, 2);
                expectedBoard.remove(1, 4, 2);
                expectedBoard.remove(2, 1, 3);
                expectedBoard.remove(2, 3, 3);
                expect(board).to.deep.equal(expectedBoard);
            });
        });

        it("should return false if variant is not removed", function () {
            board.remove(1, 0, 2);
            board.remove(1, 4, 2);

            let changed = board.applyHint(new BetweenHint(0, 1, 1, 2, 2, 3));

            expect(changed).to.be.false;
        });
    });

    it("should have Horizontal type", function () {
        expect(new BetweenHint(0, 1, 1, 2, 2, 3).getType()).to.equal(HintType.Horizontal);
    });
});

describe("BetweenHintFactory", function () {
    const factory = new BetweenHintFactory();

    describe("#supports()", function () {
        context("large enough board", function () {
            param<BoardOptions>([
                {rows: 6, cols: 6},
                {rows: 5, cols: 5},
                {rows: 4, cols: 4},
                {rows: 6, cols: 4},
                {rows: 3, cols: 3},
                // no 2×2
                {rows: 2, cols: 3},
                {rows: 1, cols: 3},
            ], function (options) {
                it("should return true", function () {
                    expect(factory.supports(options)).to.be.true;
                });
            });
        });

        context("too small board", function () {
            param<BoardOptions>([
                {rows: 1, cols: 1},
                {rows: 2, cols: 1},
                {rows: 2, cols: 2},
            ], function (options) {
                it("should return false", function () {
                    expect(factory.supports(options)).to.be.false;
                });
            });
        });
    });

    describe("#random()", function () {
        context("returned hint", function () {
            const options: BoardOptions = {rows: 6, cols: 6};
            const board = SingleBoard.random(options);

            param.repeat(100, () => factory.random(board), function (hint) {
                it("should have valid row1, rowMiddle, row2", function () {
                    expect(hint.row1).to.be.within(0, board.rows - 1);
                    expect(hint.rowMiddle).to.be.within(0, board.rows - 1);
                    expect(hint.row2).to.be.within(0, board.rows - 1);
                });

                it("should have side variants adjacent to middle variant on different sides", function () {
                    let col1 = board.getCol(hint.row1, hint.variant1);
                    let colMiddle = board.getCol(hint.rowMiddle, hint.variantMiddle);
                    let col2 = board.getCol(hint.row2, hint.variant2);

                    let col1Diff = col1 - colMiddle;
                    let col2Diff = col2 - colMiddle;

                    expect(col1).to.be.at.least(0);
                    expect(colMiddle).to.be.at.least(0);
                    expect(col2).to.be.at.least(0);
                    expect(col1Diff).to.be.oneOf([-1, 1]);
                    expect(col2Diff).to.be.oneOf([-1, 1]);
                    expect(col1Diff).to.not.equal(col2Diff);
                });
            });
        });
    });
});