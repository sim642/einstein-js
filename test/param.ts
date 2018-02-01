import * as _ from "lodash";
import "mocha";

interface Callback<T> {
    (value: T): void;
}

export function contextObject<T>(value: T, callback: Callback<T>): void {
    context(JSON.stringify(value), function () {
        callback(value);
    });
}

export function param<T>(values: T[], callback: Callback<T>): void {
    _.forEach(values, value => {
        contextObject(value, callback);
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

    export function repeat<T>(count: number, generator: () => T, callback: Callback<T>): void {
        param(_.times(count, generator), callback);
    }
}

// export = param;