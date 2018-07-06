import {Puzzle, PuzzleOptions} from "./Puzzle";
import {mainPuzzleGenerator, PuzzleGenerator} from "./PuzzleGenerator";
import * as Worker from "./WorkerPuzzleGenerator.worker";

class WorkerMainPuzzleGenerator implements PuzzleGenerator {
    private worker = new (Worker as any)();

    supports(options: PuzzleOptions): boolean {
        return mainPuzzleGenerator.supports(options);
    }

    generate(options: PuzzleOptions): Promise<Puzzle> {
        return new Promise(resolve => {
            this.worker.onmessage = ev => {
                let puzzle: Puzzle = Puzzle.from(ev.data); // TODO: deserialize
                console.log(puzzle);
                resolve(puzzle);
            };

            this.worker.postMessage(options);
        });
    }
}

export let workerMainPuzzleGenerator: PuzzleGenerator = new WorkerMainPuzzleGenerator();