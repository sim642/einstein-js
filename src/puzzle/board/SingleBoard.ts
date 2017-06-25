import * as _ from "lodash";
import {Board} from "./Board";

export class SingleBoard extends Board<number> {
    static random(): SingleBoard {
        return new SingleBoard(_.times(Board.rows, row => _.shuffle(_.range(Board.cols))));
    }
}