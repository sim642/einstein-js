import {expect} from "chai";
import "mocha";
import {MultiBoard} from "../../../src/puzzle/board/MultiBoard";
import {OpenHint} from "../../../src/puzzle/hint/OpenHint";
import {HintType} from "../../../src/puzzle/hint/Hint";

describe("OpenHint", function () {
    describe("#apply()", function () {
        let board: MultiBoard;
        beforeEach(function () {
            board = MultiBoard.full({rows: 3, cols: 3});
        });

        it("should set cell variant", function () {
            board.applyHint(new OpenHint(0, 1, 2));

            expect(board.isSingle(0, 1)).to.be.true;
            expect(board.getSingle(0, 1)).to.equal(2);
        });

        it("should return true if variant is set", function () {
            let changed = board.applyHint(new OpenHint(0, 1, 2));

            expect(changed).to.be.true;
        });

        it("should not remove more variants than necessary", function () {
            board.applyHint(new OpenHint(0, 1, 2));

            let expectedBoard = MultiBoard.full({rows: 3, cols: 3});
            expectedBoard.set(0, 1, 2);
            expect(board).to.deep.equal(expectedBoard);
        });

        it("should return false if variant already set", function () {
            board.set(0, 1, 2);

            let changed = board.applyHint(new OpenHint(0, 1, 2));

            expect(changed).to.be.false;
        });
    });

    it("should have Start type", function () {
        expect(new OpenHint(0, 1, 2).getType()).to.equal(HintType.Start);
    });
});