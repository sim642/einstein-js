export interface BoardOptions {
    readonly rows: number;
    readonly cols: number;
}

export abstract class Board<T> {
    constructor(private table: T[][], protected options: BoardOptions) {

    }

    readonly rows: number = this.options.rows;
    readonly cols: number = this.options.cols;
    readonly variants: number = this.options.cols;

    get(row: number, col: number): T {
        return this.table[row][col];
    }
}