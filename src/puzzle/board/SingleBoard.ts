import * as _ from "lodash";
import {Hint} from "../hint/Hint";
import {Board, BoardOptions} from "./Board";
import {MultiBoard} from "./MultiBoard";

export class SingleBoard extends Board<number> {
    static random(options: BoardOptions): SingleBoard {
        return new SingleBoard(_.times(options.rows, row => _.shuffle(_.range(options.cols))), options);
    }

    isSolvable(hints: Hint[]) {
        let multiBoard = MultiBoard.full(this.options);
        multiBoard.applyHints(hints);
        return multiBoard.isSolved(this);
    }
}