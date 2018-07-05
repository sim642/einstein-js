import {SingleBoard} from "../board/SingleBoard";
import {Hint} from "../hint/Hint";
import {Difficulty, PuzzleOptions} from "../Puzzle";
import {HintsGenerator} from "./HintsGenerator";

export class DifficultyHintsGenerator implements HintsGenerator {
    constructor(private generators: Record<Difficulty, HintsGenerator>) {

    }

    supports(options: PuzzleOptions): boolean {
        return this.generators[options.difficulty].supports(options);
    }

    generate(options: PuzzleOptions, board: SingleBoard): Promise<Hint[]> {
        return this.generators[options.difficulty].generate(options, board);
    }
}