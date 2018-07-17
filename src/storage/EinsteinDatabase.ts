import Dexie from "dexie";
import {PuzzleOptions} from "../puzzle/Puzzle";
import {ConfigItem} from "./Config";
import {CountsItem} from "./Counts";
import {TimesItem} from "./Times";
import {WasmItem} from "./Wasm";

export class EinsteinDatabase extends Dexie {
    times: Dexie.Table<TimesItem, any>;
    config: Dexie.Table<ConfigItem, string>;
    counts: Dexie.Table<CountsItem, number>;
    wasm: Dexie.Table<WasmItem, string>;

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

        /*
        counts has puzzle options as primary key.
        Dexie can't upgrade primary key changes automatically: https://github.com/dfahlander/Dexie.js/issues/88#issuecomment-285384576
        Must use temporary table to recreate with additional auto-increment primary key.
        Must use separate versions for deletion for some reason: https://github.com/dfahlander/Dexie.js/issues/105#issuecomment-405670992
         */

        this.version(4).stores({
            countsTmp: "[rows+cols+extraHintsPercent]"
        }).upgrade(async tx => {
            let countsItems = await tx.table("counts").toArray();
            await tx.table("countsTmp").bulkAdd(countsItems);
        });

        this.version(5).stores({
            counts: null
        });

        this.version(6).stores({
            counts: "++id, [rows+cols+extraHintsPercent]"
        }).upgrade(async tx => {
            let countsItemsTmp = await tx.table("countsTmp").toArray();
            await tx.table("counts").bulkAdd(countsItemsTmp);
        });

        this.version(7).stores({
            countsTmp: null
        });

        this.version(8).stores({
            times: "++, [rows+cols+extraHintsPercent+difficulty]",
            counts: "++id, [rows+cols+extraHintsPercent+difficulty]"
        }).upgrade(tx =>
            Dexie.Promise.all([
                tx.table<TimesItem>("times").toCollection().modify({
                    difficulty: "normal"
                }),
                tx.table<ConfigItem, string>("config").update("options", {
                    "value.difficulty": "normal" // actual object is in value
                }),
                tx.table<CountsItem>("counts").toCollection().modify({
                    difficulty: "normal"
                }),
            ])
        );

        this.version(9).stores({
            wasm: "url"
        });
    }
}