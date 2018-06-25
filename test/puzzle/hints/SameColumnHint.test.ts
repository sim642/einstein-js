import {expect} from "chai";
import "mocha";
import {MultiBoard} from "../../../src/puzzle/board/MultiBoard";
import {HintType} from "../../../src/puzzle/hint/Hint";
import {SameColumnHint, SameColumnHintFactory} from "../../../src/puzzle/hint/SameColumnHint";
import {param} from "../../param";
import {BoardOptions} from "../../../src/puzzle/board/Board";
import {SingleBoard} from "../../../src/puzzle/board/SingleBoard";
import {paramBoardOptionsExtra} from "../paramPuzzle";

function equivalents(hint: SameColumnHint): SameColumnHint[] {
    return [
        new SameColumnHint(hint.row1, hint.variant1, hint.row2, hint.variant2),
        new SameColumnHint(hint.row2, hint.variant2, hint.row1, hint.variant1)
    ];
}

const paramEquivalents = param.generate(equivalents);

interface RowColVariant {
    row: number;
    col: number;
    variant: number;
}

describe("SameColumnHint", function () {
    describe("#apply()", function () {
        let board: MultiBoard;
        beforeEach(function () {
            board = MultiBoard.full({rows: 3, cols: 3});
        });

        param.swaps<RowColVariant>([
            {row: 0, col: 2, variant: 1},
            {row: 1, col: 2, variant: 2}
        ], ([remove, possible]) => {
            paramEquivalents(new SameColumnHint(0, 1, 1, 2), hint => {
                beforeEach(function () {
                    board.remove(remove.row, remove.col, remove.variant);
                });

                it("should remove variant if other variant cannot be in same column", function () {
                    board.applyHint(hint);

                    expect(board.isPossible(possible.row, possible.col, possible.variant)).to.be.false;
                });

                it("should return true if variant is removed", function () {
                    let changed = board.applyHint(hint);

                    expect(changed).to.be.true;
                });
            });
        });

        paramEquivalents(new SameColumnHint(0, 1, 1, 2), hint => {
            it("should not remove more variants than necessary", function () {
                board.remove(0, 0, 1);
                board.remove(1, 2, 2);

                board.applyHint(hint);

                let expectedBoard = MultiBoard.full({rows: 3, cols: 3});
                expectedBoard.remove(0, 0, 1);
                expectedBoard.remove(1, 2, 2);
                expectedBoard.remove(1, 0, 2);
                expectedBoard.remove(0, 2, 1);
                expect(board).to.deep.equal(expectedBoard);
            });
        });

        it("should return false if variant is not removed", function () {
            let changed = board.applyHint(new SameColumnHint(0, 1, 1, 2));

            expect(changed).to.be.false;
        });
    });

    it("should have Vertical type", function () {
        expect(new SameColumnHint(0, 1, 2, 3).getType()).to.equal(HintType.Vertical);
    });
});

describe("SameColumnHintFactory", function () {
    const factory = new SameColumnHintFactory();

    describe("#supports()", function () {
        context("large enough board", function () {
            paramBoardOptionsExtra([
                {rows: 2, cols: 1}
            ], function (options) {
                it("should return true", function () {
                    expect(factory.supports(options)).to.be.true;
                });
            });
        });

        context("too small board", function () {
            param<BoardOptions>([
                {rows: 1, cols: 1},
                {rows: 1, cols: 2},
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
                it("should have valid row1, row2", function () {
                    expect(hint.row1).to.be.within(0, board.rows - 1);
                    expect(hint.row2).to.be.within(0, board.rows - 1);
                });

                it("should have different rows", function () {
                    expect(hint.row1).to.not.eq(hint.row2);
                });

                it("should have variants from same column", function () {
                    let col1 = board.getCol(hint.row1, hint.variant1);
                    let col2 = board.getCol(hint.row2, hint.variant2);

                    expect(col1).to.be.at.least(0);
                    expect(col2).to.be.at.least(0);
                    expect(col1).to.equal(col2);
                });
            });
        });
    });
});