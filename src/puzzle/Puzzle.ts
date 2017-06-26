import * as _ from "lodash";
import {MultiBoard} from "./board/MultiBoard";
import {SingleBoard} from "./board/SingleBoard";
import {AdjacentHintFactory} from "./hint/AdjacentHint";
import {BetweenHintFactory} from "./hint/BetweenHint";
import {DirectionHintFactory} from "./hint/DirectionHint";
import {Hint, HintType} from "./hint/Hint";
import {OpenHintFactory} from "./hint/OpenHint";
import {SameColumnHintFactory} from "./hint/SameColumnHint";

export class Puzzle {
    public multiBoard: MultiBoard = MultiBoard.full();

    constructor(public singleBoard: SingleBoard, public hints: Hint[]) {
        this.multiBoard.applyHints(_.filter(hints, hint => hint.getType() === HintType.Start));
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
        let hintFactories = [new OpenHintFactory(), new SameColumnHintFactory(), new AdjacentHintFactory(), new DirectionHintFactory(), new BetweenHintFactory()];
        let hintFactory = hintFactories[_.random(0, hintFactories.length - 1)];
        return hintFactory.random(board);
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