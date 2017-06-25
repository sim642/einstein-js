export abstract class Board<T> {
    public static readonly rows: number = 6;
    public static readonly cols: number = 6;

    constructor(private table: T[][]) {

    }

    readonly rows: number = this.table.length;
    readonly cols: number = this.table[0].length;

    get(row: number, col: number): T {
        return this.table[row][col];
    }
}