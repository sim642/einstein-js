import {PuzzleOptions} from "../puzzle/Puzzle";

export function formatOptions(options: PuzzleOptions): string {
    let difficultyText = options.difficulty === "hard" ? "hard " : "";
    let extraHintsText = options.extraHintsPercent > 0 ? ` with ${options.extraHintsPercent}% extra hints` : "";
    return `${options.rows}×${options.cols} ${difficultyText}puzzle${extraHintsText}`;
}