import {expect} from "chai";
import "mocha";
import {MultiBoard} from "../../../src/puzzle/board/MultiBoard";
import {HintType} from "../../../src/puzzle/hint/Hint";
import {SameColumnHint} from "../../../src/puzzle/hint/SameColumnHint";
import {param} from "../../param";

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