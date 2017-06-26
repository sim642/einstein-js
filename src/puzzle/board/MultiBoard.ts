import * as _ from 'lodash';
import {Board} from './Board';
import {Hint} from "../hint/Hint";
import {SingleBoard} from "./SingleBoard";

type Variants = boolean[];

export class MultiBoard extends Board<Variants> {
    static full(): MultiBoard {
        return new MultiBoard(_.times(Board.rows, row => _.times(Board.cols, col => _.times(Board.variants, _.constant(true)))));
    }

    remove(row: number, col: number, variant: number): void {
        if (this.get(row, col)[variant]) {
            this.get(row, col)[variant] = false;
            this.pruneSingles(row);
        }
    }

    set(row: number, col: number, variant: number): void {
        for (let variant = 0; variant < this.variants; variant++)
            this.get(row, col)[variant] = false;
        for (let col = 0; col < this.cols; col++)
            this.get(row, col)[variant] = false;
        this.get(row, col)[variant] = true;
        this.pruneSingles(row);
    }

    isPossible(row: number, col: number, variant: number): boolean {
        return this.get(row, col)[variant];
    }

    count(row: number, col: number): number {
        return _.sumBy(this.get(row, col), variant => variant ? 1 : 0);
    }

    isSingle(row: number, col: number): boolean {
        return this.count(row, col) == 1;
    }

    getSingle(row: number, col: number): number {
        return _.findIndex(this.get(row, col));
    }

    private pruneSingles(row: number): void {
        let colCnt = _.times(this.cols, _.constant(0));
        let variantCnt = _.times(this.variants, _.constant(0));
        let colVariant = _.times(this.cols, _.constant(0));
        let variantCol = _.times(this.variants, _.constant(0));

        for (let col = 0; col < this.cols; col++) {
            for (let variant = 0; variant < this.variants; variant++) {
                if (this.get(row, col)[variant]) {
                    colCnt[col]++;
                    variantCnt[variant]++;
                    colVariant[col] = variant;
                    variantCol[variant] = col;
                }
            }
        }

        let changed = false;

        for (let col = 0; col < this.cols; col++) {
            if (colCnt[col] == 1 && variantCnt[colVariant[col]] != 1) {
                const variant = colVariant[col];
                for (let col2 = 0; col2 < this.cols; col2++) {
                    if (col2 != col)
                        this.get(row, col2)[variant] = false;
                }
                changed = true;
            }
        }

        for (let variant = 0; variant < this.variants; variant++) {
            if (variantCnt[variant] == 1 && colCnt[variantCol[variant]] != 1) {
                const col = variantCol[variant];
                for (let variant2 = 0; variant2 < this.variants; variant2++) {
                    if (variant2 != variant)
                        this.get(row, col)[variant2] = false;
                }
                changed = true;
            }
        }

        if (changed)
            this.pruneSingles(row);
    }

    applyHint(hint: Hint): boolean {
        return hint.applyTo(this);
    }

    applyHints(hints: Hint[]): boolean {
        let changed : boolean;
        do {
            changed = false;
            for (let hint of hints) {
                if (this.applyHint(hint))
                    changed = true;
            }
        } while (changed);
        return changed;
    }

    isSolved(singleBoard: SingleBoard): boolean {
        return this.isSingleBoard() && this.contains(singleBoard);
    }

    isSingleBoard(): boolean {
        for (let row = 0; row < this.rows; row++) {
            for (let col = 0; col < this.cols; col++) {
                if (!this.isSingle(row, col))
                    return false;
            }
        }
        return true;
    }

    contains(singleBoard: SingleBoard): boolean {
        for (let row = 0; row < this.rows; row++) {
            for (let col = 0; col < this.cols; col++) {
                if (!this.isPossible(row, col, singleBoard.get(row, col)))
                    return false;
            }
        }
        return true;
    }
}