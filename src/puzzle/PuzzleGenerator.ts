import * as _ from "lodash";
import {SingleBoard} from "./board/SingleBoard";
import {ApplyHintsGenerator} from "./generate/ApplyHintsGenerator";
import {DifficultyHintsGenerator} from "./generate/DifficultyHintsGenerator";
import {ExtraHintsGenerator} from "./generate/ExtraHintsGenerator";
import {HintsGenerator} from "./generate/HintsGenerator";
import {NonApplyHintsGenerator} from "./generate/NonApplyHintsGenerator";
import {Z3HintsGenerator} from "./generate/Z3HintsGenerator";
import {Puzzle, PuzzleOptions} from "./Puzzle";

export interface PuzzleGenerator {
    supports(options: PuzzleOptions): boolean;
    generate(options: PuzzleOptions): Promise<Puzzle>;
}

export class HintsPuzzleGenerator implements PuzzleGenerator {
    constructor(private hintsGenerator: HintsGenerator) {

    }

    supports(options: PuzzleOptions): boolean {
        return this.hintsGenerator.supports(options);
    }

    async generate(options: PuzzleOptions): Promise<Puzzle> {
        let board = SingleBoard.random(options);
        let start = _.now();
        let hints = await this.hintsGenerator.generate(options, board);
        let end = _.now();
        console.log(`${end - start}`);
        return new Puzzle(board, hints, options);
    }
}

export let mainPuzzleGenerator: PuzzleGenerator = new HintsPuzzleGenerator(
    new ExtraHintsGenerator(new DifficultyHintsGenerator({
        normal: new ApplyHintsGenerator(),
        hard: new NonApplyHintsGenerator(new Z3HintsGenerator())
    }))
);