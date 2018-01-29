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

    export function isInTop10(options: PuzzleOptions, time: number): Promise<false | number> {
        return getSortedTimes(options).then(timesItems => {
            if (timesItems.length < 10 || time < timesItems[10 - 1].time)
                return _.sortedIndexBy(timesItems, {time: time}, timesItem => timesItem.time);
            else
                return false;
        });
    }

    export function hasTimes(options: PuzzleOptions): Promise<boolean> {
        return db.times.where({...options}).count(count => count > 0);
    }
}