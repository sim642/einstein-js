import {getZ3, Z3} from "../../z3/Z3";
import {SingleBoard} from "../board/SingleBoard";
import {AdjacentHint} from "../hint/AdjacentHint";
import {BetweenHint} from "../hint/BetweenHint";
import {DirectionHint} from "../hint/DirectionHint";
import {Hint} from "../hint/Hint";
import {OpenHint} from "../hint/OpenHint";
import {SameColumnHint} from "../hint/SameColumnHint";
import {PuzzleOptions} from "../Puzzle";
import {SolvableHintsGenerator} from "./HintsGenerator";

export class Z3HintsGenerator extends SolvableHintsGenerator {

    private z3: Z3;
    private ctx;

    async generate(options: PuzzleOptions, board: SingleBoard): Promise<Hint[]> {
        console.debug("getting Z3");
        this.z3 = await getZ3();
        this.makeContext();
        this.assertBoard(board);

        let hints = super.generate(options, board);

        this.deleteContext();
        return hints;
    }

    private makeContext() {
        console.debug("makeContext");
        let cfg = this.z3.mk_config();
        this.ctx = this.z3.mk_context(cfg);
        this.z3.del_config(cfg);
    }

    private ask(smtlib2: string): string {
        // console.debug(smtlib2);
        return this.z3.eval_smtlib2_string(this.ctx, smtlib2).trim();
    }

    private deleteContext() {
        console.debug("deleteContext");
        this.z3.del_context(this.ctx);
    }

    isSolvable(board: SingleBoard, hints: Hint[]): boolean {
        /*this.z3 = await getZ3();
        this.makeContext();
        this.assertBoard(board);*/

        console.debug("push");
        this.ask("(push)");

        this.assertHints(hints);
        let checkSat = this.ask("(check-sat)");
        let unique = checkSat == "unsat";

        console.debug("pop");
        this.ask("(pop)");
        // this.deleteContext();
        return unique;
    }

    private assertBoard(board: SingleBoard) {
        console.debug("assertBoard");
        for (let row = 0; row < board.rows; row++) {
            let xs = "";
            for (let variant = 0; variant < board.variants; variant++) {
                let x = `x${row}${variant}`;
                this.ask(`(declare-const ${x} Int)`);
                this.ask(`(assert (and (<= 0 ${x}) (< ${x} ${board.cols})))`);
                xs += " " + x;
            }

            this.ask(`(assert (distinct${xs}))`);
        }

        let ds = "";
        for (let row = 0; row < board.rows; row++) {
            for (let col = 0; col < board.cols; col++) {
                let variant = board.get(row, col);
                let x = `x${row}${variant}`;
                ds += ` (distinct ${x} ${col})`;
            }
        }
        this.ask(`(assert (or${ds}))`);
    }

    private assertHints(hints: Hint[]) {
        console.debug("assertHints");
        for (const hint of hints) {
            if (hint instanceof AdjacentHint) {
                let x1 = `x${hint.row1}${hint.variant1}`;
                let x2 = `x${hint.row2}${hint.variant2}`;
                this.ask(`(assert (or (= ${x1} (+ ${x2} 1)) (= ${x1} (- ${x2} 1))))`);
            }
            else if (hint instanceof BetweenHint) {
                let x1 = `x${hint.row1}${hint.variant1}`;
                let xMiddle = `x${hint.rowMiddle}${hint.variantMiddle}`;
                let x2 = `x${hint.row2}${hint.variant2}`;
                this.ask(`(assert (or (and (= ${xMiddle} (+ ${x1} 1)) (= ${xMiddle} (- ${x2} 1))) (and (= ${xMiddle} (+ ${x2} 1)) (= ${xMiddle} (- ${x1} 1)))))`);
            }
            else if (hint instanceof DirectionHint) {
                let xLeft = `x${hint.rowLeft}${hint.variantLeft}`;
                let xRight = `x${hint.rowRight}${hint.variantRight}`;
                this.ask(`(assert (< ${xLeft} ${xRight}))`);
            }
            else if (hint instanceof OpenHint) {
                let x = `x${hint.row}${hint.variant}`;
                this.ask(`(assert (= ${x} ${hint.col}))`);
            }
            else if (hint instanceof SameColumnHint) {
                let x1 = `x${hint.row1}${hint.variant1}`;
                let x2 = `x${hint.row2}${hint.variant2}`;
                this.ask(`(assert (= ${x1} ${x2}))`);
            }
        }
    }
}