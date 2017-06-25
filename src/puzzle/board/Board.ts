export abstract class Board<T> {
    public static readonly rows: number = 6;
    public static readonly cols: number = 6;
    public static readonly variants: number = Board.cols;

    constructor(private table: T[][]) {

    }

    readonly rows: number = this.table.length;
    readonly cols: number = this.table[0].length;
    readonly variants: number = this.cols;

    get(row: number, col: number): T {
        return this.table[row][col];
    }
}