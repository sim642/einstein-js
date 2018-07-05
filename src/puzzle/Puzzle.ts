import * as _ from "lodash";
import {BoardOptions} from "./board/Board";
import {MultiBoard} from "./board/MultiBoard";
import {SingleBoard} from "./board/SingleBoard";
import {ApplyHintsGenerator} from "./generate/ApplyHintsGenerator";
import {DifficultyHintsGenerator} from "./generate/DifficultyHintsGenerator";
import {ExtraHintsGenerator} from "./generate/ExtraHintsGenerator";
import {NonApplyHintsGenerator} from "./generate/NonApplyHintsGenerator";
import {Z3HintsGenerator} from "./generate/Z3HintsGenerator";
import {Hint, HintType} from "./hint/Hint";

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

    static async generate(options: PuzzleOptions): Promise<Puzzle> {
        let board = SingleBoard.random(options);
        let hintsGenerator = new ExtraHintsGenerator(new DifficultyHintsGenerator({
            normal: new ApplyHintsGenerator(),
            hard: new NonApplyHintsGenerator(new Z3HintsGenerator())
        }));
        let start = _.now();
        let hints = await hintsGenerator.generate(options, board);
        let end = _.now();
        console.log(`${end - start}`);
        return new Puzzle(board, hints, options);
    }
}