import * as _ from "lodash";

export class Timer {
    private totalTime: number;
    private startTime: number | null;

    constructor() {
        this.reset();
    }

    start(): void {
        if (this.startTime === null)
            this.startTime = _.now();
    }

    pause(): void {
        let runningTime = this.getRunningTime();
        if (runningTime !== null) {
            this.totalTime += runningTime;
            this.startTime = null;
        }
    }

    getRunningTime(): number | null {
        return this.startTime !== null ? _.now() - this.startTime : null;
    }

    getTotalTime(): number {
        return this.totalTime + (this.getRunningTime() || 0);
    }

    reset(): void {
        this.totalTime = 0;
        this.startTime = null;
    }
}