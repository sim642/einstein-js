import * as _ from "lodash";
import {BoardOptions} from "./board/Board";
import {MultiBoard} from "./board/MultiBoard";
import {SingleBoard} from "./board/SingleBoard";
import {Hint, HintType} from "./hint/Hint";
import {mainPuzzleGenerator} from "./PuzzleGenerator";

export type Difficulty = "normal" | "hard";

export interface PuzzleOptions extends BoardOptions {
    readonly extraHintsPercent: number;
    readonly difficulty: Difficulty;
}

export class Puzzle {
    public multiBoard: MultiBoard;

    constructor(public singleBoard: SingleBoard, public hints: Hint[], public readonly options: PuzzleOptions) {
        this.multiBoard = MultiBoard.full(options);
        this.multiBoard.applyHints(_.filter(hints, hint => hint.getType() === HintType.Start));
    }

    isSolved(): boolean {
        return this.multiBoard.isSolved(this.singleBoard);
    }

    isOver(): boolean {
        return !this.multiBoard.contains(this.singleBoard);
    }

    applySingleHint(): boolean {
        return this.multiBoard.applySingleHint(_.filter(this.hints, hint => hint.getType() !== HintType.Start));
    }

    canApplySingleHint(): boolean {
        let tmpPuzzle: Puzzle = _.cloneDeep(this);
        return tmpPuzzle.applySingleHint();
    }

    static generate(options: PuzzleOptions): Promise<Puzzle> {
        return mainPuzzleGenerator.generate(options); // TODO: remove because usages should check supports before
    }
}