import {MultiBoard} from "../board/MultiBoard";
import {SingleBoard} from "../board/SingleBoard";

export interface Hint {
    applyTo(board: MultiBoard): boolean;
}

export interface HintFactory {
    random(board: SingleBoard): Hint;
}