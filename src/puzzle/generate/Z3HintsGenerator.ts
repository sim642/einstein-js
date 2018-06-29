import {getZ3, Z3} from "../../z3/Z3";
import {SingleBoard} from "../board/SingleBoard";
import {AdjacentHint} from "../hint/AdjacentHint";
import {BetweenHint} from "../hint/BetweenHint";
import {DirectionHint} from "../hint/DirectionHint";
import {Hint} from "../hint/Hint";
import {OpenHint} from "../hint/OpenHint";
import {SameColumnHint} from "../hint/SameColumnHint";
import {SolvableHintsGenerator} from "./HintsGenerator";

export class Z3HintsGenerator extends SolvableHintsGenerator {
    async isSolvable(board: SingleBoard, hints: Hint[]): Promise<boolean> {
        const z3 = await getZ3();

        let cfg = z3.mk_config();
        let ctx = z3.mk_context(cfg);
        z3.del_config(cfg);

        // z3.setParam("model", "true");
        // z3.setParam("auto_config", "false");
        // z3.setParam("smtlib2_compliant", "false");

        let ss = "";
        let ask = s => {
            // console.log(s);
            ss += s + "\n";
            return z3.eval_smtlib2_string(ctx, s);
        };

        let setup = v => {
            for (let row = 0; row < board.rows; row++) {
                let xs = "";
                for (let variant = 0; variant < board.variants; variant++) {
                    let x = `${v}${row}${variant}`;
                    ask(`(declare-const ${x} Int)`);
                    ask(`(assert (and (<= 0 ${x}) (< ${x} ${board.cols})))`);
                    xs += " " + x;
                }

                ask(`(assert (distinct${xs}))`);
            }

            for (const hint of hints) {
                if (hint instanceof AdjacentHint) {
                    let x1 = `${v}${hint.row1}${hint.variant1}`;
                    let x2 = `${v}${hint.row2}${hint.variant2}`;
                    ask(`(assert (or (= ${x1} (+ ${x2} 1)) (= ${x1} (- ${x2} 1))))`);
                }
                else if (hint instanceof BetweenHint) {
                    let x1 = `${v}${hint.row1}${hint.variant1}`;
                    let xMiddle = `${v}${hint.rowMiddle}${hint.variantMiddle}`;
                    let x2 = `${v}${hint.row2}${hint.variant2}`;
                    ask(`(assert (or (and (= ${xMiddle} (+ ${x1} 1)) (= ${xMiddle} (- ${x2} 1))) (and (= ${xMiddle} (+ ${x2} 1)) (= ${xMiddle} (- ${x1} 1)))))`);
                }
                else if (hint instanceof DirectionHint) {
                    let xLeft = `${v}${hint.rowLeft}${hint.variantLeft}`;
                    let xRight = `${v}${hint.rowRight}${hint.variantRight}`;
                    ask(`(assert (< ${xLeft} ${xRight}))`);
                }
                else if (hint instanceof OpenHint) {
                    let x = `${v}${hint.row}${hint.variant}`;
                    ask(`(assert (= ${x} ${hint.col}))`);
                }
                else if (hint instanceof SameColumnHint) {
                    let x1 = `${v}${hint.row1}${hint.variant1}`;
                    let x2 = `${v}${hint.row2}${hint.variant2}`;
                    ask(`(assert (= ${x1} ${x2}))`);
                }
            }
        };

        setup("x");
        // let sat1 = ask("(check-sat)").trim();
        // let solvable = sat1 == "sat";

        let ds = "";
        for (let row = 0; row < board.rows; row++) {
            for (let col = 0; col < board.cols; col++) {
                let variant = board.get(row, col);
                let x = `x${row}${variant}`;
                ds += ` (distinct ${x} ${col})`;
            }
        }
        ask(`(assert (or${ds}))`);
        console.log(ss);
        let sat2 = ask("(check-sat)").trim();

        let unique = sat2 == "unsat";
        // alert(`${sat1} ${solvable}\n${sat2} ${unique}`);

        z3.del_context(ctx);

        // return solvable && unique;
        return unique;
    }
}