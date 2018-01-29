import * as _ from "lodash";
import {PuzzleOptions} from "../puzzle/Puzzle";
import {db} from "./db";

export interface ConfigItem {
    key: string;
    value: any;
}

export interface Config {
    options?: PuzzleOptions;
    name?: string;
}

export namespace Config {
    export function getKey<V>(key: string): Promise<V | undefined> {
        return db.config.get(key, configItem => configItem !== undefined ? configItem.value : undefined);
    }

    export function get(): Promise<Config> {
        return db.config.toArray(configItems =>
            _.fromPairs(_.map(configItems, configItem => [configItem.key, configItem.value]))
        );
    }

    export function setKey<V>(key: string, value: V): Promise<string> {
        return db.config.put({
            key: key,
            value: value
        });
    }

    export function set(newConfig: Partial<Config>): Promise<string> {
        return db.config.bulkPut(_.map(_.toPairs(newConfig), pair => ({key: pair[0], value: pair[1]})));
    }
}