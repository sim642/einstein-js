export interface BoardOptions {
    readonly rows: number;
    readonly cols: number;
}

export abstract class Board<T> {
    constructor(private table: T[][], public readonly options: BoardOptions = {
        rows: table.length,
        cols: table[0].length
    }) {

    }

    readonly rows: number = this.options.rows;
    readonly cols: number = this.options.cols;
    readonly variants: number = this.options.cols;

    get(row: number, col: number): T {
        return this.table[row][col];
    }
}