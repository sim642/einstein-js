import {SingleBoard} from "../board/SingleBoard";
import {Hint} from "../hint/Hint";
import {SolvableHintsGenerator} from "./HintsGenerator";

export class ApplyHintsGenerator extends SolvableHintsGenerator {
    async isSolvable(board: SingleBoard, hints: Hint[]): Promise<boolean> {
        return board.isSolvable(hints);
    }
}