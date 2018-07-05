import {SingleBoard} from "../board/SingleBoard";
import {Hint} from "../hint/Hint";
import {PuzzleOptions} from "../Puzzle";
import {DelegateHintsGenerator} from "./HintsGenerator";

export class NonApplyHintsGenerator extends DelegateHintsGenerator {
    async generate(options: PuzzleOptions, board: SingleBoard): Promise<Hint[]> {
        let hints: Hint[];

        let i = 0;
        do {
            hints = await this.delegate.generate(options, board);
            i++;
        } while (board.isSolvable(hints));
        console.log(`${i} tries to non-apply`);

        return hints;
    }
}