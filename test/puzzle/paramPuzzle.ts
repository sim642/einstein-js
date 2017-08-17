import {param} from "../param";
import {BoardOptions} from "../../src/puzzle/board/Board";
import {PuzzleOptions} from "../../src/puzzle/Puzzle";

export function paramBoardOptions(callback: (options: BoardOptions) => void): void {
    param<BoardOptions>([
        {rows: 6, cols: 6},
        {rows: 5, cols: 5},
        {rows: 4, cols: 4},
        {rows: 6, cols: 4},
        {rows: 3, cols: 3}
    ], callback);
}

export function paramPuzzleOptions(callback: (options: PuzzleOptions) => void): void {
    param<PuzzleOptions>([
        {rows: 6, cols: 6},
        {rows: 5, cols: 5},
        {rows: 4, cols: 4},
        {rows: 6, cols: 4},
        {rows: 3, cols: 3}
    ], callback);
}