import * as _ from "lodash";
import {PuzzleOptions} from "../puzzle/Puzzle";
import {db} from "./db";

export interface TimesItem extends PuzzleOptions {
    time: number;
    date: Date;
    name?: string;
}

export namespace Times {
    export function addItem(timesItem: TimesItem) {
        return db.times.add(timesItem);
    }

    export function add(options: PuzzleOptions, time: number, name?: string) {
        let timesItem = {
            ...options,
            time: time,
            date: new Date(),
            name: name
        };
        return addItem(timesItem);
    }

    export function getSortedTimes(options: PuzzleOptions): Promise<TimesItem[]> {
        return db.times.where({...options}).sortBy("time");
    }

    export function getTop10(options: PuzzleOptions): Promise<TimesItem[]> {
        return getSortedTimes(options).then(timesItems =>
            _.take(timesItems, 10)
        );
    }

    export function isInTop10(options: PuzzleOptions, time: number): Promise<boolean> {
        return getSortedTimes(options).then(timesItems => {
            return timesItems.length < 10 || time < timesItems[10 - 1].time;
        });
    }
}