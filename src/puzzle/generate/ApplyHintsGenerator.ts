import {SingleBoard} from "../board/SingleBoard";
import {Hint} from "../hint/Hint";
import {SolvableHintsGenerator} from "./HintsGenerator";

export class ApplyHintsGenerator extends SolvableHintsGenerator {
    isSolvable(board: SingleBoard, hints: Hint[]): boolean {
        return board.isSolvable(hints);
    }
}