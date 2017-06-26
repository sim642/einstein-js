import * as _ from "lodash";
import {MultiBoard} from "../board/MultiBoard";
import {SingleBoard} from "../board/SingleBoard";
import {Hint, HintFactory, HintType} from "./Hint";

export class SameColumnHint implements Hint {
    constructor(public row1: number, public variant1: number, public row2: number, public variant2: number) {

    }

    applyTo(board: MultiBoard): boolean {
        let changed = false;

        for (let col = 0; col < board.cols; col++) {
            const possible1 = board.isPossible(this.row1, col, this.variant1);
            const possible2 = board.isPossible(this.row2, col, this.variant2);

            if (!possible1 && possible2) {
                board.remove(this.row2, col, this.variant2);
                changed = true;
            }
            else if (possible1 && !possible2) {
                board.remove(this.row1, col, this.variant1);
                changed = true;
            }
        }

        return changed;
    }

    getType(): HintType {
        return HintType.Vertical;
    }
}

export class SameColumnHintFactory implements HintFactory {
    random(board: SingleBoard): Hint {
        let col = _.random(0, board.cols - 1);
        let row1 = _.random(0, board.rows - 1);
        let row2;
        do {
            row2 = _.random(0, board.rows - 1);
        } while (row2 == row1);
        return new SameColumnHint(row1, board.get(row1, col), row2, board.get(row2, col));
    }
}