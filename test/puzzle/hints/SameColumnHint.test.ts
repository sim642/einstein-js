import {expect} from "chai";
import * as _ from "lodash";
import "mocha";
import {MultiBoard} from "../../../src/puzzle/board/MultiBoard";
import {HintType} from "../../../src/puzzle/hint/Hint";
import {SameColumnHint} from "../../../src/puzzle/hint/SameColumnHint";

function equivalents(hint: SameColumnHint): SameColumnHint[] {
    return [
        new SameColumnHint(hint.row1, hint.variant1, hint.row2, hint.variant2),
        new SameColumnHint(hint.row2, hint.variant2, hint.row1, hint.variant1)
    ];
}

function swaps<T>([first, second]: [T, T]): [T, T][] {
    return [
        [first, second],
        [second, first]
    ];
}

function param<T>(values: T[], callback: (value: T) => void): void {
    _.forEach(values, value => {
        context(JSON.stringify(value), function () {
            callback(value);
        });
    });
}

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

        param(swaps<RowColVariant>([
            {row: 0, col: 2, variant: 1},
            {row: 1, col: 2, variant: 2}
        ]), ([remove, possible]) => {
            param(equivalents(new SameColumnHint(0, 1, 1, 2)), hint => {
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

        it("should return false if variant is not removed", function () {
            let changed = board.applyHint(new SameColumnHint(0, 1, 1, 2));

            expect(changed).to.be.false;
        });
    });

    it("should have Vertical type", function () {
        expect(new SameColumnHint(0, 1, 2, 3).getType()).to.equal(HintType.Vertical);
    });
});