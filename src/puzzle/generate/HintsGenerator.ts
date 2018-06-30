import * as _ from "lodash";
import {SingleBoard} from "../board/SingleBoard";
import {Hint, HintFactory} from "../hint/Hint";
import {Puzzle, PuzzleOptions} from "../Puzzle";
import {RandomHintFactory} from "../RandomHint";

export interface HintsGenerator {
    generate(options: PuzzleOptions, board: SingleBoard): Promise<Hint[]>;
}

export abstract class DelegateHintsGenerator implements HintsGenerator {
    constructor(protected delegate: HintsGenerator) {

    }

    abstract generate(options: PuzzleOptions, board: SingleBoard): Promise<Hint[]>;
}

export abstract class SolvableHintsGenerator implements HintsGenerator {

    protected static hintFactory: HintFactory = new RandomHintFactory();

    async generate(options: PuzzleOptions, board: SingleBoard): Promise<Hint[]> {
        let hints = this.generateHints(board);
        return this.pruneHints(board, hints);
    }

    abstract isSolvable(board: SingleBoard, hints: Hint[]): boolean;

    protected generateHints(board: SingleBoard): Hint[] {
        let hints: Hint[] = [];
        while (!this.isSolvable(board, hints)) {
            let hint = SolvableHintsGenerator.hintFactory.random(board);
            hints.push(hint);
        }
        return hints;
    }

    protected pruneHints(board: SingleBoard, hints: Hint[]): Hint[] {
        hints = _.clone(hints);
        console.debug(`Before pruneHints: ${hints.length}`);
        for (let i = 0; i < hints.length;) { // no i++
            let hint = hints.splice(i, 1)[0];
            if (board.isSolvable(hints)) {
                // keep i which now points to next hint
            }
            else {
                hints.splice(i, 0, hint);
                i++;
            }
        }
        console.debug(`After pruneHints: ${hints.length}`);
        return hints;
    }
}