import * as _ from "lodash";
import {PuzzleOptions} from "../puzzle/Puzzle";
import {db} from "./db";

export interface TimesItem extends PuzzleOptions {
    time: number;
    date: Date;
}

export namespace Times {
    export function addItem(timesItem: TimesItem) {
        return db.times.add(timesItem);
    }

    export function add(options: PuzzleOptions, time: number) {
        let timesItem = {
            ...options,
            time: time,
            date: new Date()
        };
        return addItem(timesItem);
    }

    export function getTop10(options: PuzzleOptions): Promise<TimesItem[]> {
        return db.times.where({...options}).sortBy("time").then(timesItems =>
            _.take(timesItems, 10)
        );
    }
}