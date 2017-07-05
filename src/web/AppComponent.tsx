import * as _ from "lodash";
import {Component, h} from "preact";
import {Puzzle} from "../puzzle/Puzzle";
import "./app.less";
import {HintsComponent} from "./HintsComponent";
import {MultiBoardComponent} from "./MultiBoardComponent";
import {TimerComponent} from "./TimerComponent";
import {formatDuration} from "../time";
import * as Package from "package.json";

interface AppState {
    puzzle: Puzzle;
    startTime: number;
}

export class AppComponent extends Component<{}, AppState> {
    constructor() {
        super();
        this.state = {
            puzzle: Puzzle.generate(),
            startTime: _.now()
        };
    }

    private onClickNewGame = (e) => {
        this.setState({
            puzzle: Puzzle.generate(),
            startTime: _.now()
        });
    };

    private refresh = () => {
        let puzzle = this.state.puzzle;
        if (puzzle.isSolved()) {
            let endTime = _.now();
            alert(`Solved in ${formatDuration(this.state.startTime, endTime)}!`);
            this.forceUpdate();
        }
        else if (puzzle.isOver()) {
            alert("Over!");
            this.forceUpdate();
        }
    };

    render(props, state: AppState) {
        return (
            <div class="app">
                <div class="app-top">
                    <div class="header">
                        <div class="brand">
                            <a href="http://einstein.sim642.eu" title={`einstein-js ${Package.version}`}>einstein-js</a> <small>by <a href="https://github.com/sim642/einstein-js">sim642</a></small>
                        </div>

                        <button onClick={this.onClickNewGame}>New game</button>
                        <TimerComponent start={state.startTime}/>
                    </div>
                    <MultiBoardComponent puzzle={state.puzzle} refresh={this.refresh}/>
                </div>
                <HintsComponent hints={state.puzzle.hints}/>
            </div>
        );
    }
}