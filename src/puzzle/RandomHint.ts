import * as _ from "lodash";
import {Distribution} from "../math/distribution";
import {SingleBoard} from "./board/SingleBoard";
import {AdjacentHintFactory} from "./hint/AdjacentHint";
import {BetweenHintFactory} from "./hint/BetweenHint";
import {DirectionHintFactory} from "./hint/DirectionHint";
import {Hint, HintFactory} from "./hint/Hint";
import {OpenHintFactory} from "./hint/OpenHint";
import {SameColumnHintFactory} from "./hint/SameColumnHint";

export class RandomHintFactory implements HintFactory {
    // hint frequency distribution from original einstein 2.0
    private defaultDist: Distribution<HintFactory> = [
        [new AdjacentHintFactory(), 4],
        [new OpenHintFactory(), 1],
        [new SameColumnHintFactory(), 2],
        [new DirectionHintFactory(), 4],
        [new BetweenHintFactory(), 3]
    ];

    random(board: SingleBoard): Hint {
        let hintFactory: HintFactory = Distribution.random(this.defaultDist);
        return hintFactory.random(board);
    }
}