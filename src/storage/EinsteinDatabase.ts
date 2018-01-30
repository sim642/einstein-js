import Dexie from "dexie";
import {PuzzleOptions} from "../puzzle/Puzzle";
import {ConfigItem} from "./Config";
import {CountsItem} from "./Counts";
import {TimesItem} from "./Times";

export class EinsteinDatabase extends Dexie {
    times: Dexie.Table<TimesItem, any>;
    config: Dexie.Table<ConfigItem, string>;
    counts: Dexie.Table<CountsItem, PuzzleOptions>;

    constructor() {
        super("EinsteinDatabase");

        this.version(1).stores({
            times: "++, [rows+cols+extraHintsPercent]"
        });

        this.version(2).stores({
            config: "key"
        });

        this.version(3).stores({
            counts: "[rows+cols+extraHintsPercent]"
        });
    }
}