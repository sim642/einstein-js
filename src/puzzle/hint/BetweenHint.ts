import * as _ from "lodash";
import {BoardOptions} from "../board/Board";
import {MultiBoard} from "../board/MultiBoard";
import {SingleBoard} from "../board/SingleBoard";
import {Hint, HintFactory, HintType} from "./Hint";

export class BetweenHint implements Hint {
    constructor(public row1: number, public variant1: number, public rowMiddle: number, public variantMiddle: number, public row2: number, public variant2: number) {

    }

    applyTo(board: MultiBoard): boolean {
        let changed = false;

        if (board.isPossible(this.rowMiddle, 0, this.variantMiddle)) {
            board.remove(this.rowMiddle, 0, this.variantMiddle);
            changed = true;
        }

        if (board.isPossible(this.rowMiddle, board.cols - 1, this.variantMiddle)) {
            board.remove(this.rowMiddle, board.cols - 1, this.variantMiddle);
            changed = true;
        }

        let changed2;
        do {
            changed2 = false;

            for (let col = 1; col < board.cols - 1; col++) {
                if (board.isPossible(this.rowMiddle, col, this.variantMiddle) &&
                    !(board.isPossible(this.row1, col - 1, this.variant1) && board.isPossible(this.row2, col + 1, this.variant2) ||
                      board.isPossible(this.row2, col - 1, this.variant2) && board.isPossible(this.row1, col + 1, this.variant1))) {
                    board.remove(this.rowMiddle, col, this.variantMiddle);
                    changed2 = true;
                }
            }

            for (let col = 0; col < board.cols; col++) {
                if (board.isPossible(this.row1, col, this.variant1)) {
                    const leftPossible = col >= 2 ? board.isPossible(this.rowMiddle, col - 1, this.variantMiddle) && board.isPossible(this.row2, col - 2, this.variant2) : false;
                    const rightPossible = col < board.cols - 2 ? board.isPossible(this.rowMiddle, col + 1, this.variantMiddle) && board.isPossible(this.row2, col + 2, this.variant2) : false;
                    if (!leftPossible && !rightPossible) {
                        board.remove(this.row1, col, this.variant1);
                        changed2 = true;
                    }
                }

                if (board.isPossible(this.row2, col, this.variant2)) {
                    const leftPossible = col >= 2 ? board.isPossible(this.rowMiddle, col - 1, this.variantMiddle) && board.isPossible(this.row1, col - 2, this.variant1) : false;
                    const rightPossible = col < board.cols - 2 ? board.isPossible(this.rowMiddle, col + 1, this.variantMiddle) && board.isPossible(this.row1, col + 2, this.variant1) : false;
                    if (!leftPossible && !rightPossible) {
                        board.remove(this.row2, col, this.variant2);
                        changed2 = true;
                    }
                }
            }

            if (changed2)
                changed = true;
        } while (changed2);

        return changed;
    }

    getType(): HintType {
        return HintType.Horizontal;
    }
}

export class BetweenHintFactory implements HintFactory {
    supports(options: BoardOptions): boolean {
        return options.rows >= 1 && options.cols >= 3;
    }

    random(board: SingleBoard): BetweenHint {
        let row1 = _.random(0, board.rows - 1);
        let rowMiddle = _.random(0, board.rows - 1);
        let colMiddle = _.random(1, board.cols - 2);
        let row2 = _.random(0, board.rows - 1);
        let colDelta = _.random(0, 1) == 1 ? 1 : -1;
        let col1 = colMiddle + colDelta;
        let col2 = colMiddle - colDelta;
        return new BetweenHint(row1, board.get(row1, col1), rowMiddle, board.get(rowMiddle, colMiddle), row2, board.get(row2, col2));
    }
}