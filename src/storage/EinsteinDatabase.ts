import Dexie from "dexie";
import {ConfigItem} from "./Config";
import {TimesItem} from "./Times";

export class EinsteinDatabase extends Dexie {
    times: Dexie.Table<TimesItem, any>;
    config: Dexie.Table<ConfigItem, string>;

    constructor() {
        super("EinsteinDatabase");

        this.version(1).stores({
            times: "++, [rows+cols+extraHintsPercent]"
        });

        this.version(2).stores({
            config: "key"
        });
    }
}