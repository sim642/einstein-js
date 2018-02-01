import * as _ from "lodash";
import {param} from "../param";
import {BoardOptions} from "../../src/puzzle/board/Board";
import {PuzzleOptions} from "../../src/puzzle/Puzzle";

const defaultBoardOptions = [
    {rows: 6, cols: 6},
    {rows: 5, cols: 5},
    {rows: 4, cols: 4},
    {rows: 6, cols: 4},
    {rows: 3, cols: 3},
    {rows: 2, cols: 2}
];

export function paramBoardOptions(callback: (options: BoardOptions) => void): void {
    param<BoardOptions>(defaultBoardOptions, callback);
}

export function paramBoardOptionsExtra(extraBoardOptions: BoardOptions[], callback: (options: BoardOptions) => void): void {
    param<BoardOptions>(_.concat(defaultBoardOptions, extraBoardOptions), callback);
}

export function paramPuzzleOptions(callback: (options: PuzzleOptions) => void): void {
    param<PuzzleOptions>([
        {rows: 6, cols: 6, extraHintsPercent: 0},
        {rows: 5, cols: 5, extraHintsPercent: 0},
        {rows: 4, cols: 4, extraHintsPercent: 0},
        {rows: 6, cols: 4, extraHintsPercent: 0},
        {rows: 3, cols: 3, extraHintsPercent: 0},
        {rows: 2, cols: 2, extraHintsPercent: 0},

        {rows: 6, cols: 6, extraHintsPercent: 25},
        {rows: 6, cols: 6, extraHintsPercent: 50},
        {rows: 6, cols: 6, extraHintsPercent: 100}
    ], callback);
}