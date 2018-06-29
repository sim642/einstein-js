import * as _ from "lodash";
import {SingleBoard} from "../board/SingleBoard";
import {Hint, HintFactory} from "../hint/Hint";
import {PuzzleOptions} from "../Puzzle";
import {RandomHintFactory} from "../RandomHint";
import {DelegateHintsGenerator} from "./HintsGenerator";

export class ExtraHintsGenerator extends DelegateHintsGenerator {

    private static hintFactory: HintFactory = new RandomHintFactory();

    async generate(options: PuzzleOptions, board: SingleBoard): Promise<Hint[]> {
        let hints = await this.delegate.generate(options, board);
        return ExtraHintsGenerator.generateExtraHints(options, board, hints);
    }

    private static generateExtraHints(options: PuzzleOptions, board: SingleBoard, hints: Hint[]): Hint[] {
        hints = _.clone(hints);
        let extraHints = Math.round((options.extraHintsPercent / 100) * hints.length);
        console.debug(`Adding extra hints: ${extraHints}`);
        for (let i = 0; i < extraHints; i++) {
            let hint = ExtraHintsGenerator.hintFactory.random(board);
            hints.push(hint);
        }
        return hints;
    }
}