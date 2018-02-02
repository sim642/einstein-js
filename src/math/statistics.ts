import * as _ from "lodash";

export function mean(arr: number[]): number {
    return _.sum(arr) / arr.length;
}

export function variance(arr: number[], knownMean: number = mean(arr)): number {
    return _.sumBy(arr, x => Math.pow(x - knownMean, 2)) / arr.length;
}

export function stdDev(arr: number[], knownMean: number = mean(arr)): number {
    return Math.sqrt(variance(arr, knownMean));
}