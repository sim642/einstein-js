import * as _ from "lodash";

export function formatDuration(start, end) {
    let diffMs = end - start;
    let diffSec = diffMs / 1000;
    let sec = Math.floor(diffSec) % 60;
    let min = Math.floor(diffSec / 60) % 60;
    let hr = Math.floor(diffSec / 60 / 60);

    return `${_.padStart(hr.toString(), 2, "0")}:${_.padStart(min.toString(), 2, "0")}:${_.padStart(sec.toString(), 2, "0")}`;
}