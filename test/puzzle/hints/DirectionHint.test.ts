import {expect} from "chai";
import "mocha";
import {MultiBoard} from "../../../src/puzzle/board/MultiBoard";
import {DirectionHint, DirectionHintFactory} from "../../../src/puzzle/hint/DirectionHint";
import {HintType} from "../../../src/puzzle/hint/Hint";
import {BoardOptions} from "../../../src/puzzle/board/Board";
import {SingleBoard} from "../../../src/puzzle/board/SingleBoard";
import {param} from "../../param";

describe("DirectionHint", function () {
    describe("#apply()", function () {
        let board: MultiBoard;
        beforeEach(function () {
            board = MultiBoard.full({rows: 4, cols: 4});
        });

        context("leftward", function () {
            const hint = new DirectionHint(1, 2, 0, 3);

            beforeEach(function () {
                board.remove(1, 0, 2);
            });

            it("should remove right variant if left variant cannot be to the left", function () {
                board.applyHint(hint);

                expect(board.isPossible(0, 0, 3)).to.be.false;
                expect(board.isPossible(0, 1, 3)).to.be.false;
            });

            it("should return true if variant is removed", function () {
                let changed = board.applyHint(hint);

                expect(changed).to.be.true;
            });
        });

        context("rightward", function () {
            const hint = new DirectionHint(1, 2, 0, 3);

            beforeEach(function () {
                board.remove(0, 3, 3);
            });

            it("should remove left variant if right variant cannot be to the right", function () {
                board.applyHint(hint);

                expect(board.isPossible(1, 2, 2)).to.be.false;
                expect(board.isPossible(1, 3, 2)).to.be.false;
            });

            it("should return true if variant is removed", function () {
                let changed = board.applyHint(hint);

                expect(changed).to.be.true;
            });
        });

        it("should not remove more variants than necessary", function () {
            board.remove(0, 3, 3);
            board.remove(1, 0, 2);

            board.applyHint(new DirectionHint(1, 2, 0, 3));

            let expectedBoard = MultiBoard.full({rows: 4, cols: 4});
            expectedBoard.remove(0, 3, 3);
            expectedBoard.remove(1, 0, 2);
            expectedBoard.remove(0, 0, 3);
            expectedBoard.remove(1, 3, 2);
            expectedBoard.remove(0, 1, 3);
            expectedBoard.remove(1, 2, 2);
            expect(board).to.deep.equal(expectedBoard);
        });

        it("should return false if variant is not removed", function () {
            board.remove(0, 0, 3);
            board.remove(1, 3, 2);

            let changed = board.applyHint(new DirectionHint(1, 2, 0, 3));

            expect(changed).to.be.false;
        });
    });

    it("should have Horizontal type", function () {
        expect(new DirectionHint(0, 1, 2, 3).getType()).to.equal(HintType.Horizontal);
    });
});

describe("DirectionHintFactory", function () {
    describe("#random()", function () {
        context("returned hint", function () {
            const options: BoardOptions = {rows: 6, cols: 6};
            const board = SingleBoard.random(options);
            const factory = new DirectionHintFactory();

            param.repeat(100, () => factory.random(board), function (hint) {
                it("should have valid rowLeft, rowRight", function () {
                    expect(hint.rowLeft).to.be.within(0, board.rows - 1);
                    expect(hint.rowRight).to.be.within(0, board.rows - 1);
                });

                it("should have left and right variant in the correct order", function () {
                    let colLeft = board.getCol(hint.rowLeft, hint.variantLeft);
                    let colRight = board.getCol(hint.rowRight, hint.variantRight);

                    expect(colLeft).to.be.at.least(0);
                    expect(colRight).to.be.at.least(0);
                    expect(colLeft).to.be.lessThan(colRight);
                });
            });
        });
    });
});