import * as _ from "lodash";
import {Component, h} from "preact";
import {Puzzle} from "../puzzle/Puzzle";
import "./app.less";
import {HintsComponent} from "./HintsComponent";
import {MultiBoardComponent} from "./MultiBoardComponent";
import {TimerComponent} from "./TimerComponent";

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

    render(props, state: AppState) {
        return (
            <div class="app">
                <div class="app-top">
                    <div>
                        <button onClick={this.onClickNewGame}>New game</button>
                        <TimerComponent start={state.startTime}/>
                    </div>
                    <MultiBoardComponent puzzle={state.puzzle}/>
                </div>
                <HintsComponent hints={state.puzzle.hints}/>
            </div>
        );
    }
}