import * as _ from "lodash";
import {BoardOptions} from "./board/Board";
import {MultiBoard} from "./board/MultiBoard";
import {SingleBoard} from "./board/SingleBoard";
import {Hint, HintFactory, HintType} from "./hint/Hint";
import {RandomHintFactory} from "./RandomHint";

export interface PuzzleOptions extends BoardOptions {

}

export class Puzzle {
    public multiBoard: MultiBoard;

    constructor(public singleBoard: SingleBoard, public hints: Hint[], private options: PuzzleOptions) {
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

    static generate(options: PuzzleOptions): Puzzle {
        let board = SingleBoard.random(options);
        return new Puzzle(board, Puzzle.pruneHints(board, Puzzle.generateHints(board)), options);
    }

    private static hintFactory: HintFactory = new RandomHintFactory();

    private static generateHints(board: SingleBoard): Hint[] {
        let hints: Hint[] = [];
        while (!board.isSolvable(hints)) {
            let hint = Puzzle.hintFactory.random(board);
            hints.push(hint);
        }
        return hints;
    }

    private static pruneHints(board: SingleBoard, hints: Hint[]): Hint[] {
        hints = _.clone(hints);
        console.debug(`Before pruneHints: ${hints.length}`);
        let changed: boolean;
        do {
            changed = false;
            for (let i = 0; i < hints.length; i++) {
                let hint = hints.splice(i, 1)[0];
                if (board.isSolvable(hints)) {
                    changed = true;
                    break;
                }
                else
                    hints.splice(i, 0, hint);
            }
        } while (changed);
        console.debug(`After pruneHints: ${hints.length}`);
        return hints;
    }
}