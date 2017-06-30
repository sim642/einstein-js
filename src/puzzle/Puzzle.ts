import * as _ from "lodash";
import {MultiBoard} from "./board/MultiBoard";
import {SingleBoard} from "./board/SingleBoard";
import {AdjacentHintFactory} from "./hint/AdjacentHint";
import {BetweenHintFactory} from "./hint/BetweenHint";
import {DirectionHintFactory} from "./hint/DirectionHint";
import {Hint, HintFactory, HintType} from "./hint/Hint";
import {OpenHintFactory} from "./hint/OpenHint";
import {SameColumnHintFactory} from "./hint/SameColumnHint";

export class Puzzle {
    public multiBoard: MultiBoard = MultiBoard.full();

    constructor(public singleBoard: SingleBoard, public hints: Hint[]) {
        this.multiBoard.applyHints(_.filter(hints, hint => hint.getType() === HintType.Start));
    }

    isSolved(): boolean {
        return this.multiBoard.isSolved(this.singleBoard);
    }

    isOver(): boolean {
        return !this.multiBoard.contains(this.singleBoard);
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
        let hintFactory: HintFactory;
        // hint frequency distribution from original einstein 2.0
        switch (_.random(0, 14 - 1)) {
            case 0:
            case 1:
            case 2:
            case 3:
                hintFactory = new AdjacentHintFactory();
                break;

            case 4:
                hintFactory = new OpenHintFactory();
                break;

            case 5:
            case 6:
                hintFactory = new SameColumnHintFactory();
                break;

            case 7:
            case 8:
            case 9:
            case 10:
                hintFactory = new DirectionHintFactory();
                break;

            case 11:
            case 12:
            case 13:
                hintFactory = new BetweenHintFactory();
                break;

            default:
                throw new Error("Unhandled random HintFactory value");
        }
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