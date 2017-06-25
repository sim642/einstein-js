import * as _ from "lodash";
import {MultiBoard} from "./board/MultiBoard";
import {SingleBoard} from "./board/SingleBoard";
import {Hint} from "./hint/Hint";
import {OpenHintFactory} from "./hint/OpenHint";
import {SameColumnHintFactory} from "./hint/SameColumnHint";
import {AdjacentHintFactory} from "./hint/AdjacentHint";

export class Puzzle {
    public multiBoard: MultiBoard = MultiBoard.full();

    constructor(public singleBoard: SingleBoard, public hints: Hint[]) {

    }

    static generate(): Puzzle {
        let board = SingleBoard.random();
        return new Puzzle(board, Puzzle.pruneHints(board, Puzzle.generateHints(board)));
    }

    private static generateHints(board: SingleBoard): Hint[] {
        let hints: Hint[] = [];
        while (!board.isSolvable(hints)) {
            let hint = Puzzle.generateHint(board);
            hints.push(hint);
        }
        return hints;
    }

    private static generateHint(board: SingleBoard): Hint {
        let hintFactories = [new OpenHintFactory(), new SameColumnHintFactory(), new AdjacentHintFactory()];
        let hintFactory = hintFactories[_.random(0, hintFactories.length - 1)];
        return hintFactory.random(board);
    }

    private static pruneHints(board: SingleBoard, hints: Hint[]): Hint[] {
        hints = _.clone(hints);
        let changed: boolean;
        do {
            changed = false;
            for (let i = 0; i < hints.length; i++) {
                let newHints = _.pullAt(hints, [i]);
                if (board.isSolvable(newHints)) {
                    hints = newHints;
                    changed = true;
                    break;
                }
            }
        } while (changed);
        return hints;
    }
}