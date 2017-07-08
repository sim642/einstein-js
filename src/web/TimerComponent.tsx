import {Component, h} from "preact";
import {formatDuration} from "../time";
import {Timer} from "../Timer";

export interface TimerProps {
    timer: Timer;
}

interface TimerState {
    time: number;
}

export class TimerComponent extends Component<TimerProps, TimerState> {
    private interval: number | null = null;

    constructor(props: TimerProps) {
        super();
        this.state = {
            time: props.timer.getTotalTime()
        };
    }

    componentWillReceiveProps(nextProps: TimerProps) {
        this.setState({
            time: nextProps.timer.getTotalTime()
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
        if (this.interval !== null)
            clearInterval(this.interval);
    }

    private setTimer() {
        this.clearTimer();

        setTimeout(() => {
            this.interval = setInterval(() => {
                this.setState({
                    time: this.props.timer.getTotalTime()
                });
            }, 1000);
        }, 0); // HACK: give enough delay to make interval fall between seconds and avoid second skipping
    }

    render(props: TimerProps, state: TimerState) {
        return (
            <div class="timer">
                {formatDuration(state.time)}
            </div>
        )
    }
}