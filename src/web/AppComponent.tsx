import {Component, h} from "preact";
import {MultiBoardComponent} from "./MultiBoardComponent";
import {Puzzle} from "../puzzle/Puzzle";
import {HintsComponent} from "./HintsComponent";
import "./app.less";

interface AppState {
    puzzle: Puzzle;
}

export class AppComponent extends Component<{}, AppState> {
    constructor() {
        super();
        this.state = {
            puzzle: Puzzle.generate()
        };
    }

    private onClickNewGame = (e) => {
        this.setState({
            puzzle: Puzzle.generate()
        });
    };

    render(props, state: AppState) {
        return (
            <div class="app">
                <div class="app-top">
                    <div>
                        <button onClick={this.onClickNewGame}>New game</button>
                    </div>
                    <MultiBoardComponent puzzle={state.puzzle}/>
                </div>
                <HintsComponent hints={state.puzzle.hints}/>
            </div>
        );
    }
}