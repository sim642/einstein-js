import * as classNames from "classnames";
import * as _ from "lodash";
import * as Package from "package.json";
import {Component, h} from "preact";
import {Puzzle, PuzzleOptions} from "../puzzle/Puzzle";
import {formatDuration} from "../time";
import {Timer} from "../Timer";
import "./app.less";
import {HintsComponent} from "./HintsComponent";
import {MultiBoardComponent} from "./MultiBoardComponent";
import {TimerComponent} from "./TimerComponent";
import {VisibilityChangeListener} from "./helper/VisibilityChangeListener";
import {MessageUnloadListener} from "./helper/MessageUnloadListener";
import {BirthdayComponent} from "./BirthdayComponent";
import {OptionsComponent} from "./OptionsComponent";

export enum GameState {
    Options,
    Playing,
    ManualPaused,
    AutoPaused,
    Solved,
    Over,
}

interface AppState {
    options: PuzzleOptions;
    puzzle: Puzzle;
    gameState: GameState;
    cheated: number;
}

export class AppComponent extends Component<{}, AppState> {
    private timer = new Timer();
    private visibilityChange: VisibilityChangeListener;
    private messageUnload: MessageUnloadListener;

    constructor() {
        super();
        let options = {
            rows: 6,
            cols: 6
        };
        this.state = {
            options: options,
            puzzle: Puzzle.generate(options), // TODO: don't generate puzzle before setting options
            gameState: GameState.Options,
            cheated: 0
        };
        this.visibilityChange = new VisibilityChangeListener(this.onVisibilityChange);
        this.messageUnload = new MessageUnloadListener(this.onMessageUnload);
    }

    componentDidMount() {
        this.visibilityChange.add();
        this.messageUnload.add();
    }

    componentWillUnmount() {
        this.visibilityChange.remove();
        this.messageUnload.remove();
    }

    private onClickNewGame = (e) => {
        this.setState({
            gameState: GameState.Options,
            cheated: 0
        });
        this.timer.reset();
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

    private onClickCheat = (e) => {
        if (this.state.gameState === GameState.Playing) {
            this.setState((state: AppState) => {
                let changed = state.puzzle.applySingleHint();
                return _.merge(state, {
                    cheated: state.cheated + (changed ? 1 : 0)
                });
            }, this.refresh);
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

    private onMessageUnload = () => {
        switch (this.state.gameState) {
            case GameState.Playing:
            case GameState.ManualPaused:
            case GameState.AutoPaused:
                return "Are you sure you want to leave while the game is in progress?";

            default:
                return null;
        }
    };

    private submitOptions = (options: PuzzleOptions) => {
        this.setState({
            options: options,
            puzzle: Puzzle.generate(options),
            gameState: GameState.Playing,
            cheated: 0
        }, () => {
            this.timer.start();
        });
    };

    private refresh = () => {
        if (this.state.gameState === GameState.Playing) {
            let puzzle = this.state.puzzle;
            if (puzzle.isSolved()) {
                this.timer.pause();
                let time = this.timer.getTotalTime();
                this.setState(state => _.merge(state, {
                    gameState: GameState.Solved
                }), () => {
                    let cheated = this.state.cheated;
                    alert(`Solved in ${formatDuration(time)}${cheated > 0 ? ` by cheating ${cheated} times` : ""}!`);
                });
            }
            else if (puzzle.isOver()) {
                this.timer.pause();
                this.setState(state => _.merge(state, {
                    gameState: GameState.Over
                }), () => {
                    alert("Over!");
                });
            }
        }
    };

    render(props, state: AppState) {
        let solvedOrOver = state.gameState === GameState.Solved || state.gameState === GameState.Over;
        let showBoard = solvedOrOver ? state.puzzle.singleBoard : undefined;
        return (
            <div class={classNames({
                "app": true,
                "paused": state.gameState === GameState.ManualPaused || state.gameState === GameState.AutoPaused,
                "solved": state.gameState === GameState.Solved,
                "over": state.gameState === GameState.Over,
                "cheated": state.cheated > 0
            })}>
                <div class="app-top">
                    <div class="header">
                        <div class="brand">
                            <a href="http://einstein.sim642.eu" title={`einstein-js ${Package.version}`}>einstein-js</a> <small>by <a href="https://github.com/sim642/einstein-js">sim642</a></small>
                        </div>

                        <div class="buttons buttons-responsive">
                            <button onClick={this.onClickNewGame}>New game</button>
                            <button disabled={state.gameState !== GameState.Playing} onClick={this.onClickCheat}>
                                Cheat {
                                    state.cheated > 0 ?
                                        <span class="badge">{state.cheated}</span> :
                                        null
                                }
                            </button>
                            {
                                state.gameState === GameState.ManualPaused || state.gameState === GameState.AutoPaused ?
                                    <button class="button-highlight" onClick={this.onClickResume}>Resume</button> :
                                    <button disabled={state.gameState !== GameState.Playing} onClick={this.onClickPause}>Pause</button>
                            }
                        </div>

                        <TimerComponent timer={this.timer}/>
                    </div>
                    <BirthdayComponent month={10} day={22} name="Elisabeth"/>
                    {
                        state.gameState === GameState.Options ?
                            <OptionsComponent options={state.options} submit={this.submitOptions}/> :
                            <MultiBoardComponent board={state.puzzle.multiBoard} refresh={this.refresh} showBoard={showBoard}/>
                    }
                </div>
                {
                    state.gameState !== GameState.Options ?
                        <HintsComponent hints={state.puzzle.hints}/> :
                        null
                }
            </div>
        );
    }
}