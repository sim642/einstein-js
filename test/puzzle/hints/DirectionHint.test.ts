import {expect} from "chai";
import "mocha";
import {MultiBoard} from "../../../src/puzzle/board/MultiBoard";
import {DirectionHint} from "../../../src/puzzle/hint/DirectionHint";
import {HintType} from "../../../src/puzzle/hint/Hint";

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