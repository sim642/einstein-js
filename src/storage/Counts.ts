import * as _ from "lodash";
import {PuzzleOptions} from "../puzzle/Puzzle";
import {db} from "./db";

export interface Counts {
    solved: number;
    solvedCheated: number;
    over: number;
}

export interface CountsItem extends PuzzleOptions, Counts {

}

export namespace Counts {
    export function get(options: PuzzleOptions): Promise<CountsItem> {
        return db.counts.get(options, countsItem => {
            if (countsItem === undefined) {
                let defaultItem: CountsItem = {
                    ...options,
                    solved: 0,
                    solvedCheated: 0,
                    over: 0
                }; // extracted to have explicit type annotation
                return defaultItem;
            }
            else
                return countsItem;
        });
    }

    export function getTopCounts(): Promise<CountsItem[]> {
        return db.counts.toArray().then(countsItems =>
            _.orderBy(countsItems, countsItem =>
                countsItem.solved + countsItem.solvedCheated + countsItem.over,
                ["desc"])
        );
    }

    export function increase(options: PuzzleOptions, count: keyof Counts): Promise<PuzzleOptions> {
        return db.transaction("rw", db.counts, () =>
            get(options).then(countsItem => {
                let newCountsItem: CountsItem = _.merge(countsItem, {
                    [count]: countsItem[count] + 1
                });
                return db.counts.put(newCountsItem);
            })
        );
    }
}