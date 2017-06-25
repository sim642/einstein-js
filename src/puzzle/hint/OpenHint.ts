import * as _ from "lodash";
import {MultiBoard} from "../board/MultiBoard";
import {SingleBoard} from "../board/SingleBoard";
import {Hint, HintFactory} from "./Hint";

export class OpenHint implements Hint {
    constructor(public row: number, public col: number, public variant: number) {

    }

    applyTo(board: MultiBoard): boolean {
        if (!board.isSingle(this.row, this.col)) {
            board.set(this.row, this.col, this.variant);
            return true;
        }
        else
            return false;
    }
}

export class OpenHintFactory implements HintFactory {
    random(board: SingleBoard): Hint {
        let row = _.random(0, board.rows - 1);
        let col = _.random(0, board.cols - 1);
        return new OpenHint(row, col, board.get(row, col));
    }
}