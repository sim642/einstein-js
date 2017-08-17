import {expect} from "chai";
import "mocha";
import {MultiBoard} from "../../../src/puzzle/board/MultiBoard";
import {OpenHint, OpenHintFactory} from "../../../src/puzzle/hint/OpenHint";
import {HintType} from "../../../src/puzzle/hint/Hint";
import {BoardOptions} from "../../../src/puzzle/board/Board";
import {SingleBoard} from "../../../src/puzzle/board/SingleBoard";
import {param} from "../../param";

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

describe("OpenHintFactory", function () {
    describe("#random()", function () {
        context("returned hint", function () {
            const options: BoardOptions = {rows: 6, cols: 6};
            const board = SingleBoard.random(options);
            const factory = new OpenHintFactory();

            param.repeat(100, () => factory.random(board), function (hint) {
                it("should have valid row, col", function () {
                    expect(hint.row).to.be.within(0, board.rows - 1);
                    expect(hint.col).to.be.within(0, board.cols - 1);
                });

                it("should have correct variant", function () {
                    expect(hint.variant).to.equal(board.get(hint.row, hint.col));
                });
            });
        });
    });
});