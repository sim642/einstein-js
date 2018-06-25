export function median(arr: number[]): number {
    let n = arr.length;
    if (n % 2 === 0)
        return (arr[n / 2 - 1] + arr[n / 2]) / 2;
    else
        return arr[(n - 1) / 2];
}

// Tukey's hinges (include median) - https://en.wikipedia.org/wiki/Quartile#Method_2
export function lowerQuartile(arr: number[]): number {
    let n = arr.length;
    let end = n % 2 === 0 ? n / 2 : (n + 1) / 2;
    return median(arr.slice(0, end));
}

export function upperQuartile(arr: number[]): number {
    let n = arr.length;
    let start = n % 2 === 0 ? n / 2 : (n - 1) / 2;
    return median(arr.slice(start));
}