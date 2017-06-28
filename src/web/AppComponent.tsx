import * as _ from "lodash";
import {Component, h} from "preact";
import {Puzzle} from "../puzzle/Puzzle";
import "./app.less";
import {HintsComponent} from "./HintsComponent";
import {MultiBoardComponent} from "./MultiBoardComponent";
import {TimerComponent} from "./TimerComponent";
import {formatDuration} from "../time";

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