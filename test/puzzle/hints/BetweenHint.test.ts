import {expect} from "chai";
import "mocha";
import {MultiBoard} from "../../../src/puzzle/board/MultiBoard";
import {BetweenHint} from "../../../src/puzzle/hint/BetweenHint";
import {HintType} from "../../../src/puzzle/hint/Hint";
import {param} from "../../param";

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