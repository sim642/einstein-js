import * as _ from "lodash";
import {SingleBoard} from "./board/SingleBoard";
import {AdjacentHintFactory} from "./hint/AdjacentHint";
import {BetweenHintFactory} from "./hint/BetweenHint";
import {DirectionHintFactory} from "./hint/DirectionHint";
import {Hint, HintFactory} from "./hint/Hint";
import {OpenHintFactory} from "./hint/OpenHint";
import {SameColumnHintFactory} from "./hint/SameColumnHint";

export class RandomHintFactory implements HintFactory {
    random(board: SingleBoard): Hint {
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

            // istanbul ignore next: impossible case
            default:
                throw new Error("Unhandled random HintFactory value");
        }
        return hintFactory.random(board);
    }
}