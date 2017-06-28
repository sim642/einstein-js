import * as _ from "lodash";
import {Component, h} from "preact";
import {formatDuration} from "../time";

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
        return (
            <div>
                {formatDuration(props.start, state.now)}
            </div>
        )
    }
}