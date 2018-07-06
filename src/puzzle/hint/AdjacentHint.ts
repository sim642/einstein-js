import * as _ from "lodash";
import {BoardOptions} from "../board/Board";
import {MultiBoard} from "../board/MultiBoard";
import {SingleBoard} from "../board/SingleBoard";
import {Hint, HintClass, HintFactory, HintType} from "./Hint";

export class AdjacentHint implements Hint {
    class: HintClass = HintClass.Adjacent;

    constructor(public row1: number, public variant1: number, public row2: number, public variant2: number) {

    }

    applyTo(board: MultiBoard): boolean {
        let changed = false;

        let applyToCol = (col: number, thisRow: number, thisVariant: number, adjRow: number, adjVariant: number) => {
            const hasLeft = col >= 1 ? board.isPossible(adjRow, col - 1, adjVariant) : false;
            const hasRight = col < board.cols - 1 ? board.isPossible(adjRow, col + 1, adjVariant) : false;

            if (!hasLeft && !hasRight && board.isPossible(thisRow, col, thisVariant)) {
                board.remove(thisRow, col, thisVariant);
                changed = true;
            }
        };

        for (let col = 0; col < board.cols; col++) {
            applyToCol(col, this.row1, this.variant1, this.row2, this.variant2);
            applyToCol(col, this.row2, this.variant2, this.row1, this.variant1);
        }

        if (changed)
            this.applyTo(board);

        return changed;
    }

    getType(): HintType {
        return HintType.Horizontal;
    }
}

export class AdjacentHintFactory implements HintFactory {
    supports(options: BoardOptions): boolean {
        return options.rows >= 1 && options.cols >= 2;
    }

    random(board: SingleBoard): AdjacentHint {
        let row1 = _.random(0, board.rows - 1);
        let col1 = _.random(0, board.cols - 1);
        let row2 = _.random(0, board.rows - 1);
        let colDelta;
        if (col1 == 0)
            colDelta = 1;
        else if (col1 == board.cols - 1)
            colDelta = -1;
        else
            colDelta = _.random(0, 1) == 1 ? 1 : -1;
        let col2 = col1 + colDelta;
        return new AdjacentHint(row1, board.get(row1, col1), row2, board.get(row2, col2));
    }
}