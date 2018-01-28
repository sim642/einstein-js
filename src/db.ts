import {Dexie} from "dexie";
import {PuzzleOptions} from "./puzzle/Puzzle";

export interface TimesItem extends PuzzleOptions {
    time: number;
    date: Date;
}

class EinsteinDatabase extends Dexie {
    times: Dexie.Table<TimesItem, any>;

    constructor() {
        super("EinsteinDatabase");

        this.version(1).stores({
            times: "++, [rows+cols+extraHintsPercent]"
        });
    }
}

export let db = new EinsteinDatabase();