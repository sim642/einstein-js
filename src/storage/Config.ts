import {db} from "./db";

export interface ConfigItem {
    key: string;
    value: any;
}

export namespace Config {
    export function get<V>(key: string): Promise<V | undefined> {
        return db.config.get(key, configItem => configItem !== undefined ? configItem.value : undefined);
    }

    export function set<V>(key: string, value: V): Promise<string> {
        return db.config.put({
            key: key,
            value: value
        });
    }
}