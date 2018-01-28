import Dexie from "dexie";
import {TimesItem} from "./Times";

export class EinsteinDatabase extends Dexie {
    times: Dexie.Table<TimesItem, any>;

    constructor() {
        super("EinsteinDatabase");

        this.version(1).stores({
            times: "++, [rows+cols+extraHintsPercent]"
        });
    }
}