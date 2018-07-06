import * as _ from "lodash";
import {setClass} from "../../object";
import {Hint} from "../hint/Hint";
import {Board, BoardOptions} from "./Board";
import {MultiBoard} from "./MultiBoard";

export class SingleBoard extends Board<number> {
    static random(options: BoardOptions): SingleBoard {
        return new SingleBoard(_.times(options.rows, row => _.shuffle(_.range(options.cols))), options);
    }

    static from(o: any): SingleBoard {
        setClass(o, SingleBoard);
        return o;
    }

    getCol(row: number, variant: number): number {
        for (let col = 0; col < this.cols; col++) {
            if (this.get(row, col) === variant)
                return col;
        }
        return -1;
    }

    isSolvable(hints: Hint[]) {
        let multiBoard = MultiBoard.full(this.options);
        multiBoard.applyHints(hints);
        return multiBoard.isSolved(this);
    }
}