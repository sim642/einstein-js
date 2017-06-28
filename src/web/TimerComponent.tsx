import * as _ from "lodash";
import {Component, h} from "preact";

export interface TimerProps {
    start: number;
}

interface TimerState {
    now: number;
}

export class TimerComponent extends Component<TimerProps, TimerState> {
    private timer: number | null = null;

    constructor(props: TimerProps) {
        super();
        this.state = {
            now: props.start
        };
    }

    componentWillReceiveProps(nextProps: TimerProps) {
        this.setState(state => {
            return {
                now: nextProps.start
            };
        });
        this.setTimer();
    }

    componentDidMount() {
        this.setTimer();
    }

    componentWillUnmount() {
        this.clearTimer();
    }

    private clearTimer() {
        if (this.timer !== null)
            clearInterval(this.timer);
    }

    private setTimer() {
        this.clearTimer();

        this.timer = setInterval(() => {
            this.setState(state => {
                return {
                    now: _.now()
                };
            })
        }, 1000);
    }

    render(props: TimerProps, state: TimerState) {
        let diffMs = state.now - props.start;
        let diffSec = diffMs / 1000;
        let sec = Math.floor(diffSec) % 60;
        let min = Math.floor(diffSec / 60) % 60;
        let hr = Math.floor(diffSec / 60 / 60);

        return (
            <div>
                {_.padStart(hr.toString(), 2, "0")}
                :
                {_.padStart(min.toString(), 2, "0")}
                :
                {_.padStart(sec.toString(), 2, "0")}
            </div>
        )
    }
}