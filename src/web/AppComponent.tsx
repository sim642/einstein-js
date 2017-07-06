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
import {VisibilityChangeListener} from "./helper/VisibilityChangeListener";

export enum GameState {
    Playing,
    ManualPaused,
    AutoPaused,
    Solved,
    Over,
}

interface AppState {
    puzzle: Puzzle;
    gameState: GameState;
}

export class AppComponent extends Component<{}, AppState> {
    private timer = new Timer();
    private visibilityChange: VisibilityChangeListener;

    constructor() {
        super();
        this.state = {
            puzzle: Puzzle.generate(),
            gameState: GameState.Playing
        };
        this.visibilityChange = new VisibilityChangeListener(this.onVisibilityChange);
    }

    componentDidMount() {
        this.timer.start();
        this.visibilityChange.add();
    }

    componentWillUnmount() {
        this.visibilityChange.remove();
    }

    private onClickNewGame = (e) => {
        this.setState({
            puzzle: Puzzle.generate(),
            gameState: GameState.Playing
        });
        this.timer.reset();
        this.timer.start();
    };

    private onClickPause = (e) => {
        if (this.state.gameState === GameState.Playing) {
            this.timer.pause();
            this.setState(state => _.merge(state, {
                gameState: GameState.ManualPaused
            }));
        }
    };

    private onClickResume = (e) => {
        if (this.state.gameState === GameState.ManualPaused || this.state.gameState === GameState.AutoPaused) {
            this.timer.start();
            this.setState(state => _.merge(state, {
                gameState: GameState.Playing
            }));
        }
    };

    private onVisibilityChange = visible => {
        if (visible && this.state.gameState === GameState.AutoPaused) {
            this.timer.start();
            this.setState(state => _.merge(state, {
                gameState: GameState.Playing
            }));
        }
        else if (!visible && this.state.gameState === GameState.Playing) {
            this.timer.pause();
            this.setState(state => _.merge(state, {
                gameState: GameState.AutoPaused
            }));
        }
    };

    private refresh = () => {
        if (this.state.gameState === GameState.Playing) {
            let puzzle = this.state.puzzle;
            if (puzzle.isSolved()) {
                this.timer.pause();
                alert(`Solved in ${formatDuration(this.timer.getTotalTime())}!`);
                this.setState(state => _.merge(state, {
                    gameState: GameState.Solved
                }));
            }
            else if (puzzle.isOver()) {
                this.timer.pause();
                alert("Over!");
                puzzle.multiBoard.applySingleBoard(puzzle.singleBoard); // show correct solution
                this.setState(state => _.merge(state, {
                    gameState: GameState.Over
                }));
            }
        }
    };

    render(props, state: AppState) {
        return (
            <div class={classNames({
                "app": true,
                "paused": state.gameState === GameState.ManualPaused || state.gameState === GameState.AutoPaused,
                "solved": state.gameState === GameState.Solved,
                "over": state.gameState === GameState.Over,
            })}>
                <div class="app-top">
                    <div class="header">
                        <div class="brand">
                            <a href="http://einstein.sim642.eu" title={`einstein-js ${Package.version}`}>einstein-js</a> <small>by <a href="https://github.com/sim642/einstein-js">sim642</a></small>
                        </div>

                        <button onClick={this.onClickNewGame}>New game</button>
                        {
                            state.gameState === GameState.ManualPaused || state.gameState === GameState.AutoPaused ?
                                <button class="button-highlight" onClick={this.onClickResume}>Resume</button> :
                                <button disabled={state.gameState !== GameState.Playing} onClick={this.onClickPause}>Pause</button>
                        }
                        <TimerComponent timer={this.timer}/>
                    </div>
                    <MultiBoardComponent board={state.puzzle.multiBoard} refresh={this.refresh}/>
                </div>
                <HintsComponent hints={state.puzzle.hints}/>
            </div>
        );
    }
}