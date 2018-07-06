import {PuzzleOptions} from "./Puzzle";
import {mainPuzzleGenerator} from "./PuzzleGenerator";

const ctx: Worker = self as any;

ctx.onmessage = ev => {
    let options: PuzzleOptions = ev.data;
    console.log(options);

    mainPuzzleGenerator.generate(options).then(puzzle => {
        console.log(puzzle);
        ctx.postMessage(puzzle); // TODO: serialize
    });
};