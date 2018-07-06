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
    export function getKey<K extends keyof Config>(key: K): Promise<Config[K] | undefined> {
        return db.config.get(key, configItem => configItem !== undefined ? configItem.value : undefined);
    }

    export function get(): Promise<Config> {
        return db.config.toArray(configItems =>
            _.fromPairs(_.map(configItems, configItem => [configItem.key, configItem.value]))
        );
    }

    export function setKey<K extends keyof Config>(key: K, value: Config[K]): Promise<K> {
        return db.config.put({
            key: key,
            value: value
        });
    }

    export function set(newConfig: Partial<Config>): Promise<string> {
        return db.config.bulkPut(_.map(_.toPairs(newConfig), pair => ({key: pair[0], value: pair[1]})));
    }
}