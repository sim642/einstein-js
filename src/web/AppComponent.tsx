import * as classNames from "classnames";
import Dexie from "dexie";
import * as _ from "lodash";
import * as Package from "package.json";
import {Component, h} from "preact";
import {Puzzle, PuzzleOptions} from "../puzzle/Puzzle";
import {mainPuzzleGenerator, PuzzleGenerator} from "../puzzle/PuzzleGenerator";
import {Config} from "../storage/Config";
import {Counts} from "../storage/Counts";
import {Times} from "../storage/Times";
import {formatDuration} from "../time";
import {Timer} from "../Timer";
import "./app.less";
import {HighscoreComponent} from "./HighscoreComponent";
import {HintsComponent} from "./HintsComponent";
import {MultiBoardComponent} from "./MultiBoardComponent";
import {formatOptions} from "./PuzzleOptionsUtils";
import {TimerComponent} from "./TimerComponent";
import {VisibilityChangeListener} from "./helper/VisibilityChangeListener";
import {MessageUnloadListener} from "./helper/MessageUnloadListener";
import {BirthdayComponent} from "./BirthdayComponent";
import {OptionsComponent} from "./OptionsComponent";

export enum GameState {
    Options,
    Highscore,
    Generating,
    Playing,
    ManualPaused,
    AutoPaused,
    Solved,
    Over,
}

interface AppState {
    options: PuzzleOptions;
    puzzle?: Puzzle;
    gameState: GameState;
    cheated: number;
    defaultName?: string;
    canCheat?: boolean;
}

export class AppComponent extends Component<{}, AppState> {
    private timer = new Timer();
    private visibilityChange: VisibilityChangeListener;
    private messageUnload: MessageUnloadListener;
    private puzzleGenerator: PuzzleGenerator = mainPuzzleGenerator;

    private static readonly defaultOptions: PuzzleOptions = {
        rows: 6,
        cols: 6,
        extraHintsPercent: 0,
        difficulty: "normal"
    };

    constructor() {
        super();
        this.state = {
            options: AppComponent.defaultOptions,
            puzzle: undefined,
            gameState: GameState.Options,
            cheated: 0,
            canCheat: undefined
        };
        this.visibilityChange = new VisibilityChangeListener(this.onVisibilityChange);
        this.messageUnload = new MessageUnloadListener(this.onMessageUnload);

        Config.get().then(config => {
            this.setState(state => _.assignWith(state, {
                options: config.options,
                defaultName: config.name
            }, (stateValue, sourceValue) => _.isUndefined(sourceValue) ? stateValue : sourceValue));
        });
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
                let changed = state.puzzle!.applySingleHint();
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
        this.configOptions(options);
        this.setState({
            gameState: GameState.Generating
        }, () => {
            // this.forceUpdate(); // seems to make no difference

            requestAnimationFrame(time => { // request repaint, callback runs BEFORE
                setTimeout(async () => {
                    let puzzle = await this.puzzleGenerator.generate(options);
                    this.setState({
                        puzzle: puzzle,
                        gameState: GameState.Playing,
                        cheated: 0,
                        canCheat: true
                    }, () => {
                        this.timer.start();
                        this.refresh(); // check win in case everything opened on start
                    });
                }, 0); // timeout to start generation AFTER repaint (hopefully)
            });
        });
    };

    private highscoreOptions = (options: PuzzleOptions) => {
        this.configOptions(options);
        this.setState({
            gameState: GameState.Highscore
        });
    };

    private configOptions(options: PuzzleOptions) {
        this.setState({
            options: options
        });
        Config.set({
            options: options
        });
    }

    private configDefaultName(name: string): Promise<string> {
        return Dexie.Promise.all([
            new Dexie.Promise((resolve, reject) => {
                this.setState({
                    defaultName: name
                }, () => resolve(name));
            }),
            Config.set({
                name: name
            })
        ]).then(() => name);
    }

    private refresh = () => {
        if (this.state.gameState === GameState.Playing) {
            let puzzle = this.state.puzzle!;
            if (puzzle.isSolved()) {
                this.timer.pause();
                let time = this.timer.getTotalTime();
                this.setState(state => _.merge(state, {
                    gameState: GameState.Solved
                }), () => {
                    let options = puzzle.options;
                    let cheated = this.state.cheated;
                    Counts.increase(options, cheated ? "solvedCheated" : "solved");

                    let cheatedText = cheated > 0 ? ` by cheating ${cheated} times` : "";
                    alert(`Solved ${formatOptions(options)} in ${formatDuration(time)}${cheatedText}!`);

                    if (!cheated) {
                        Times.isInTop10(options, time).then<string | undefined>(isInTop10 => {
                            let name;
                            if (isInTop10 !== false &&
                                (name = prompt(`Enter name for ${isInTop10 + 1}. place in high scores:`, this.state.defaultName)) !== null)
                                return this.configDefaultName(name);
                            else
                                return undefined;
                        }).then(name =>
                            Times.add(options, time, name)
                        );
                    }
                });
            }
            else if (puzzle.isOver()) {
                this.timer.pause();
                this.setState(state => _.merge(state, {
                    gameState: GameState.Over
                }), () => {
                    Counts.increase(puzzle.options, "over");

                    alert("Over!");
                });
            }
            else {
                this.setState({
                    canCheat: puzzle.canApplySingleHint()
                });
            }
        }
    };

    render(props, state: AppState) {
        let solvedOrOver = state.gameState === GameState.Solved || state.gameState === GameState.Over;
        let showBoard = solvedOrOver ? state.puzzle!.singleBoard : undefined;
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
                            <button class={classNames({
                                "button-highlight": solvedOrOver || state.gameState === GameState.Highscore
                            })} disabled={state.gameState === GameState.Generating} onClick={this.onClickNewGame}>New game</button>
                            <button disabled={!(state.gameState === GameState.Playing && state.canCheat)} onClick={this.onClickCheat}>
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
                        state.gameState === GameState.Options || state.gameState === GameState.Generating ?
                            <OptionsComponent options={state.options} submit={this.submitOptions} highscore={this.highscoreOptions} defaultOptions={AppComponent.defaultOptions} puzzleGenerator={this.puzzleGenerator} generating={state.gameState === GameState.Generating}/> :
                            state.gameState === GameState.Highscore ?
                                <HighscoreComponent options={state.options}/> :
                                <MultiBoardComponent board={state.puzzle!.multiBoard} refresh={this.refresh} showBoard={showBoard}/>
                    }
                </div>
                {
                    state.gameState !== GameState.Options && state.gameState !== GameState.Highscore && state.gameState !== GameState.Generating ?
                        <HintsComponent hints={state.puzzle!.hints}/> :
                        null
                }
            </div>
        );
    }
}