import * as _ from "lodash";
import {getZ3, Z3} from "../../z3/Z3";
import {SingleBoard} from "../board/SingleBoard";
import {AdjacentHint} from "../hint/AdjacentHint";
import {BetweenHint} from "../hint/BetweenHint";
import {DirectionHint} from "../hint/DirectionHint";
import {Hint, HintFactory} from "../hint/Hint";
import {OpenHint} from "../hint/OpenHint";
import {SameColumnHint} from "../hint/SameColumnHint";
import {PuzzleOptions} from "../Puzzle";
import {RandomHintFactory} from "../RandomHint";
import {HintsGenerator} from "./HintsGenerator";

export class Z3HintsGenerator implements HintsGenerator {

    private static hintFactory: HintFactory = new RandomHintFactory();

    private z3: Z3;
    private ctx;

    async generate(options: PuzzleOptions, board: SingleBoard): Promise<Hint[]> {
        console.debug("getZ3");
        this.z3 = await getZ3();

        this.makeContext();
        // this.ask("(set-option :produce-unsat-cores true)"); // TODO: why parser error?
        this.assertBoard(board);

        let hints = this.generateHints(board);
        hints = this.pruneHints(board, hints);

        this.deleteContext();
        return hints;
    }

    private makeContext() {
        console.debug("makeContext");
        this.z3.global_param_set("unsat_core", "true");
        this.z3.global_param_set("smt.core.minimize", "true");

        let cfg = this.z3.mk_config();
        this.ctx = this.z3.mk_context(cfg);
        this.z3.set_error_handler(this.ctx, this.z3.errorHandler);
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

    protected generateHints(board: SingleBoard): Hint[] {
        let hints: Hint[] = [];
        while (!this.isUniqueSolvable()) {
            let hint = Z3HintsGenerator.hintFactory.random(board);
            hints.push(hint);

            let i = hints.length - 1;
            let constraint = Z3HintsGenerator.getHintConstraint(hint);
            this.ask(`(assert (! ${constraint} :named h${i}))`);
        }
        return hints;
    }

    protected pruneHints(board: SingleBoard, hints: Hint[]): Hint[] {
        console.debug(`Before pruneHints: ${hints.length}`);

        let getUnsatCore = this.ask("(get-unsat-core)");
        console.debug(getUnsatCore);
        let coreIs = _.map(getUnsatCore.match(/\d+/g), i => parseInt(i));
        hints = _.filter(hints, (hint, i) => _.includes(coreIs, i));

        console.debug(`After pruneHints: ${hints.length}`);
        return hints;
    }

    private isUniqueSolvable() {
        let checkSat = this.ask("(check-sat)");
        let unique = checkSat == "unsat";
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

    private static getHintConstraint(hint: Hint): string {
        if (hint instanceof AdjacentHint) {
            let x1 = `x${hint.row1}${hint.variant1}`;
            let x2 = `x${hint.row2}${hint.variant2}`;
            return `(or (= ${x1} (+ ${x2} 1)) (= ${x1} (- ${x2} 1)))`;
        }
        else if (hint instanceof BetweenHint) {
            let x1 = `x${hint.row1}${hint.variant1}`;
            let xMiddle = `x${hint.rowMiddle}${hint.variantMiddle}`;
            let x2 = `x${hint.row2}${hint.variant2}`;
            return `(or (and (= ${xMiddle} (+ ${x1} 1)) (= ${xMiddle} (- ${x2} 1))) (and (= ${xMiddle} (+ ${x2} 1)) (= ${xMiddle} (- ${x1} 1))))`;
        }
        else if (hint instanceof DirectionHint) {
            let xLeft = `x${hint.rowLeft}${hint.variantLeft}`;
            let xRight = `x${hint.rowRight}${hint.variantRight}`;
            return `(< ${xLeft} ${xRight})`;
        }
        else if (hint instanceof OpenHint) {
            let x = `x${hint.row}${hint.variant}`;
            return `(= ${x} ${hint.col})`;
        }
        else if (hint instanceof SameColumnHint) {
            let x1 = `x${hint.row1}${hint.variant1}`;
            let x2 = `x${hint.row2}${hint.variant2}`;
            return `(= ${x1} ${x2})`;
        }
        else
            throw new Error("Unsupported hint type");
    }
}