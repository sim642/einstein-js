import * as _ from "lodash";
import {AdjacentHint} from "../hint/AdjacentHint";
import {BetweenHint} from "../hint/BetweenHint";
import {DirectionHint} from "../hint/DirectionHint";
import {Hint} from "../hint/Hint";
import {OpenHint} from "../hint/OpenHint";
import {SameColumnHint} from "../hint/SameColumnHint";
import {Board, BoardOptions} from "./Board";
import {MultiBoard} from "./MultiBoard";
import {Z3, z3 as z} from "../../z3/Z3";

export class SingleBoard extends Board<number> {
    static random(options: BoardOptions): SingleBoard {
        return new SingleBoard(_.times(options.rows, row => _.shuffle(_.range(options.cols))), options);
    }

    getCol(row: number, variant: number): number {
        for (let col = 0; col < this.cols; col++) {
            if (this.get(row, col) === variant)
                return col;
        }
        return -1;
    }

    isSolvable(hints: Hint[]) {
        let z3 = z;
        if (z3 !== null) {
            let ctx = z3.init();

            z3.setParam("model", "true");
            z3.setParam("auto_config", "false");
            z3.setParam("smtlib2_compliant", "false");

            let ss = "";
            let ask = s => {
                // console.log(s);
                ss += s + "\n";
                return (z3 as Z3).ask(ctx, s);
            };

            let setup = v => {
                for (let row = 0; row < this.rows; row++) {
                    let xs = "";
                    for (let variant = 0; variant < this.variants; variant++) {
                        let x = `${v}${row}${variant}`;
                        ask(`(declare-const ${x} Int)`);
                        ask(`(assert (and (<= 0 ${x}) (< ${x} ${this.cols})))`);
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

            setup("y");
            let ds = "";
            for (let row = 0; row < this.rows; row++) {
                for (let variant = 0; variant < this.variants; variant++) {
                    let x = `x${row}${variant}`;
                    let y = `y${row}${variant}`;
                    ds += ` (distinct ${x} ${y})`;
                }
            }
            ask(`(assert (or${ds}))`);
            let sat2 = ask("(check-sat)").trim();
            let unique = sat2 == "unsat";

            console.log(ss);
            // alert(`${sat1} ${solvable}\n${sat2} ${unique}`);

            z3.destroy(ctx);

            // return solvable && unique;
            return unique;
        }
        else {
            // alert("crap");
            console.log("crap");
            let multiBoard = MultiBoard.full(this.options);
            multiBoard.applyHints(hints);
            return multiBoard.isSolved(this);
            // return false;
        }
    }
}