import Dexie from "dexie";
import {PuzzleOptions} from "../puzzle/Puzzle";
import {ConfigItem} from "./Config";
import {CountsItem} from "./Counts";
import {TimesItem} from "./Times";

export class EinsteinDatabase extends Dexie {
    times: Dexie.Table<TimesItem, any>;
    config: Dexie.Table<ConfigItem, string>;
    counts: Dexie.Table<CountsItem, any>;

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

        this.version(4).stores({
            counts: null,
            countsTmp: "[rows+cols+extraHintsPercent]"
        }).upgrade(async tx => {
            let countsItems = await tx.table("counts").toArray();
            let countsTmpStore = tx.idbtrans.objectStore("countsTmp");
            countsItems.forEach(countsItem => countsTmpStore.put(countsItem));
        });

        this.version(5).stores({
            counts: "++, [rows+cols+extraHintsPercent]",
            countsTmp: null
        }).upgrade(async tx => {
            let countsItemsTmp = await new Promise<any[]>((resolve, reject) => {
                let request = tx.idbtrans.objectStore("countsTmp").getAll();
                request.onSuccess = () => resolve(request.result);
                request.onError = () => reject(request.error);
            });
            await tx.table("counts").bulkAdd(countsItemsTmp);
        });

        this.version(6).stores({
            times: "++, [rows+cols+extraHintsPercent+difficulty]",
            counts: "++, [rows+cols+extraHintsPercent+difficulty]"
        }).upgrade(tx =>
            Dexie.Promise.all([
                tx.table<TimesItem>("times").toCollection().modify({
                    difficulty: "normal"
                }),
                tx.table<ConfigItem, string>("config").update("options", {
                    difficulty: "normal"
                }),
                tx.table<CountsItem>("counts").toCollection().modify({
                    difficulty: "normal"
                }),
            ])
        );
    }
}