import * as classNames from "classnames";
import * as _ from "lodash";
import * as Package from "package.json";
import {Component, h} from "preact";
import {Puzzle} from "../puzzle/Puzzle";
import {formatDuration} from "../time";
import {Timer} from "../Timer";
import "./app.less";
import {HintsComponent} from "./HintsComponent";
import {MultiBoardComponent} from "./MultiBoardComponent";
import {TimerComponent} from "./TimerComponent";

interface AppState {
    puzzle: Puzzle;
    paused: boolean;
}

export class AppComponent extends Component<{}, AppState> {
    private timer = new Timer();

    constructor() {
        super();
        this.state = {
            puzzle: Puzzle.generate(),
            paused: false
        };
    }

    componentDidMount() {
        this.timer.start();
    }

    private onClickNewGame = (e) => {
        this.setState({
            puzzle: Puzzle.generate(),
            paused: false
        });
        this.timer.reset();
        this.timer.start();
    };

    private onClickPause = (e) => {
        this.timer.pause();
        this.setState(state => _.merge(state, {
            paused: true
        }));
    };

    private onClickResume = (e) => {
        this.timer.start();
        this.setState(state => _.merge(state, {
            paused: false
        }));
    };

    private refresh = () => {
        let puzzle = this.state.puzzle;
        if (puzzle.isSolved()) {
            this.timer.pause();
            alert(`Solved in ${formatDuration(this.timer.getTotalTime())}!`);
            this.forceUpdate();
        }
        else if (puzzle.isOver()) {
            this.timer.pause();
            alert("Over!");
            this.forceUpdate();
        }
    };

    render(props, state: AppState) {
        return (
            <div class={classNames({
                "app": true,
                "paused": state.paused
            })}>
                <div class="app-top">
                    <div class="header">
                        <div class="brand">
                            <a href="http://einstein.sim642.eu" title={`einstein-js ${Package.version}`}>einstein-js</a> <small>by <a href="https://github.com/sim642/einstein-js">sim642</a></small>
                        </div>

                        <button onClick={this.onClickNewGame}>New game</button>
                        {
                            state.paused ?
                                <button class="button-highlight" onClick={this.onClickResume}>Resume</button> :
                                <button onClick={this.onClickPause}>Pause</button>
                        }
                        <TimerComponent timer={this.timer}/>
                    </div>
                    <MultiBoardComponent puzzle={state.puzzle} refresh={this.refresh}/>
                </div>
                <HintsComponent hints={state.puzzle.hints}/>
            </div>
        );
    }
}