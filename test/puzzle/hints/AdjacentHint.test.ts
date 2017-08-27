import {expect} from "chai";
import "mocha";
import {MultiBoard} from "../../../src/puzzle/board/MultiBoard";
import {AdjacentHint, AdjacentHintFactory} from "../../../src/puzzle/hint/AdjacentHint";
import {HintType} from "../../../src/puzzle/hint/Hint";
import {param} from "../../param";
import {BoardOptions} from "../../../src/puzzle/board/Board";
import {SingleBoard} from "../../../src/puzzle/board/SingleBoard";

function equivalents(hint: AdjacentHint): AdjacentHint[] {
    return [
        new AdjacentHint(hint.row1, hint.variant1, hint.row2, hint.variant2),
        new AdjacentHint(hint.row2, hint.variant2, hint.row1, hint.variant1)
    ];
}

const paramEquivalents = param.generate(equivalents);

describe("AdjacentHint", function () {
    describe("#apply()", function () {
        let board: MultiBoard;
        beforeEach(function () {
            board = MultiBoard.full({rows: 3, cols: 3});
        });

        context("first column", function () {
            paramEquivalents(new AdjacentHint(1, 0, 0, 2), hint => {
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
            paramEquivalents(new AdjacentHint(1, 0, 0, 2), hint => {
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
            paramEquivalents(new AdjacentHint(1, 0, 0, 2), hint => {
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

        paramEquivalents(new AdjacentHint(1, 0, 0, 2), hint => {
            it("should not remove more variants than necessary", function () {
                board.remove(0, 1, 2);

                board.applyHint(hint);

                let expectedBoard = MultiBoard.full({rows: 3, cols: 3});
                expectedBoard.remove(0, 1, 2);
                expectedBoard.remove(1, 0, 0);
                expectedBoard.remove(1, 2, 0);
                expect(board).to.deep.equal(expectedBoard);
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

describe("AdjacentHintFactory", function () {
    describe("#random()", function () {
        context("returned hint", function () {
            const options: BoardOptions = {rows: 6, cols: 6};
            const board = SingleBoard.random(options);
            const factory = new AdjacentHintFactory();

            param.repeat(100, () => factory.random(board), function (hint) {
                it("should have valid row1, row2", function () {
                    expect(hint.row1).to.be.within(0, board.rows - 1);
                    expect(hint.row2).to.be.within(0, board.rows - 1);
                });

                it("should have variants adjacent", function () {
                    let col1 = board.getCol(hint.row1, hint.variant1);
                    let col2 = board.getCol(hint.row2, hint.variant2);

                    expect(col1).to.be.at.least(0);
                    expect(col2).to.be.at.least(0);
                    expect(col1 - col2).to.be.oneOf([-1, 1]);
                });
            });
        });
    });
});