import * as _ from "lodash";
import {BoardOptions} from "../board/Board";
import {MultiBoard} from "../board/MultiBoard";
import {SingleBoard} from "../board/SingleBoard";
import {Hint, HintClass, HintFactory, HintType} from "./Hint";

export class DirectionHint implements Hint {
    class: HintClass = HintClass.Direction;

    constructor(public rowLeft: number, public variantLeft: number, public rowRight: number, public variantRight: number) {

    }

    applyTo(board: MultiBoard): boolean {
        let changed = false;

        for (let col = 0; col < board.cols; col++) {
            if (board.isPossible(this.rowRight, col, this.variantRight)) {
                board.remove(this.rowRight, col, this.variantRight);
                changed = true;
            }
            if (board.isPossible(this.rowLeft, col, this.variantLeft))
                break;
        }

        for (let col = board.cols - 1; col >= 0; col--) {
            if (board.isPossible(this.rowLeft, col, this.variantLeft)) {
                board.remove(this.rowLeft, col, this.variantLeft);
                changed = true;
            }
            if (board.isPossible(this.rowRight, col, this.variantRight))
                break;
        }

        return changed;
    }

    getType(): HintType {
        return HintType.Horizontal;
    }
}

export class DirectionHintFactory implements HintFactory {
    supports(options: BoardOptions): boolean {
        return options.rows >= 1 && options.cols >= 2;
    }

    random(board: SingleBoard): DirectionHint {
        let rowLeft = _.random(0, board.rows - 1);
        let colLeft = _.random(0, board.cols - 2);
        let rowRight = _.random(0, board.rows - 1);
        let colRight = _.random(colLeft + 1, board.cols - 1);
        return new DirectionHint(rowLeft, board.get(rowLeft, colLeft), rowRight, board.get(rowRight, colRight));
    }
}