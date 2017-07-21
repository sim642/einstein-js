export interface BoardOptions {
    readonly rows: number;
    readonly cols: number;
}

export abstract class Board<T> {
    protected options: BoardOptions;
    readonly rows: number;
    readonly cols: number;
    readonly variants: number;

    constructor(private table: T[][], options?: BoardOptions) {
        if (!options) {
            options = {
                rows: table.length,
                cols: table[0].length // assuming table is rectangular
            };
        }
        this.options = options;

        this.rows = options.rows;
        this.cols = options.cols;
        this.variants = options.cols;
    }

    get(row: number, col: number): T {
        return this.table[row][col];
    }
}