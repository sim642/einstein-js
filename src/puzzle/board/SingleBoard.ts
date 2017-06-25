import * as _ from "lodash";
import {Hint} from "../hint/Hint";
import {Board} from "./Board";
import {MultiBoard} from "./MultiBoard";

export class SingleBoard extends Board<number> {
    static random(): SingleBoard {
        return new SingleBoard(_.times(Board.rows, row => _.shuffle(_.range(Board.cols))));
    }

    isSolvable(hints: Hint[]) {
        let multiBoard = MultiBoard.full();
        multiBoard.applyHints(hints);
        return multiBoard.isSolved(this);
    }
}