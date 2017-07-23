import * as _ from "lodash";
import "mocha";

interface Callback<T> {
    (value: T): void;
}

export function param<T>(values: T[], callback: Callback<T>): void {
    _.forEach(values, value => {
        context(JSON.stringify(value), function () {
            callback(value);
        });
    });
}

export namespace param {
    interface Generator<T> {
        (value: T): T[];
    }

    interface GeneratedParam<T> {
        (value: T, callback: Callback<T>): void;
    }

    export function generate<T>(generator: Generator<T>): GeneratedParam<T> {
        return (value, callback) => {
            param(generator(value), callback);
        };
    }

    function swapsGenerator<T>([first, second]: [T, T]): [T, T][] {
        return [
            [first, second],
            [second, first]
        ];
    }

    export function swaps<T>(value: [T, T], callback: Callback<[T, T]>): void {
        generate(swapsGenerator)(value, callback);
    }
}

// export = param;