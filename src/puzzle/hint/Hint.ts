import {BoardOptions} from "../board/Board";
import {MultiBoard} from "../board/MultiBoard";
import {SingleBoard} from "../board/SingleBoard";

export const enum HintType {
    Start,
    Horizontal,
    Vertical,
}

export interface Hint {
    applyTo(board: MultiBoard): boolean;
    getType(): HintType;
}

export interface HintFactory {
    supports(options: BoardOptions): boolean;
    random(board: SingleBoard): Hint;
}