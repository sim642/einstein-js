import * as _ from "lodash";
import {Component, h} from "preact";
import "./options.less";
import {PuzzleOptions} from "../puzzle/Puzzle";
import {PuzzleGenerator} from "../puzzle/PuzzleGenerator";
import {Config} from "../storage/Config";
import {Counts, CountsItem} from "../storage/Counts";
import {Times} from "../storage/Times";
import {formatOptions} from "./PuzzleOptionsUtils";

interface RangeProps {
    value: number;
    min: number;
    max: number;
    step?: number;
    onChange: (value: number) => void;
    id?: string;
    unit?: string;
}

class InputRangeComponent extends Component<RangeProps, {}> {
    private onChange = (e) => {
        e.preventDefault();

        let value = parseInt(e.target.value);
        this.props.onChange(value);
    };

    render(props: RangeProps) {
        let listId = `${props.id}-list`;
        return (
            <span class="input input-range">
                <input type="range" {...props} value={props.value.toString()} list={listId} onChange={this.onChange} onInput={this.onChange}/>
                <output for={props.id}>{props.value}{props.unit}</output>

                <datalist id={listId}>
                    {_.map(_.range(props.min, props.max + 1, props.step), value =>
                        <option value={value.toString()}/>
                    )}
                </datalist>
            </span>
        );
    }
}

interface ChoiceProps {
    choices: [string, string][];
    value: string;
    onChange: (value: string) => void;
    id?: string;
}

class RadioChoiceComponent extends Component<ChoiceProps, {}> {
    private onChange(value: string) {
        return (e) => {
            e.preventDefault();

            this.props.onChange(value);
        };
    }

    render(props: ChoiceProps) {
        return (
            // Chrome fieldsets don't flex: https://stackoverflow.com/q/28078681
            <div class="input input-choice">
                {_.map(props.choices, ([value, label]) =>
                    <span>
                        <input type="radio" id={`${props.id}-${value}`} name={props.id} checked={value === props.value} onChange={this.onChange(value)}/>
                        <label for={`${props.id}-${value}`}>{label}</label>
                    </span>
                )}
            </div>
        );
    }
}

interface TopOptionsProps {
    set: (PuzzleOptions) => void;
}

interface TopOptionsState {
    topCounts?: CountsItem[];
}

class TopOptionsComponent extends Component<TopOptionsProps, TopOptionsState> {
    constructor() {
        super();
        this.state = {
            topCounts: undefined
        };
        this.fetchTopCounts();
    }

    private fetchTopCounts() {
        Counts.getTopCounts().then(topCounts => {
            this.setState({
                topCounts: topCounts
            });
        });
    }

    private onClick(countsItem: CountsItem) {
        let options: PuzzleOptions = {
            rows: countsItem.rows,
            cols: countsItem.cols,
            extraHintsPercent: countsItem.extraHintsPercent,
            difficulty: countsItem.difficulty
        }; // options shouldn't contain Counts fields, breaks IndexedDB query

        return (e) => {
            e.preventDefault();
            this.props.set(options);
        };
    }

    render(props: TopOptionsProps, state: TopOptionsState) {
        if (state.topCounts !== undefined && state.topCounts.length > 0) {
            return (
                <div class="top-options">
                    <hr/>

                    <span class="options-title">Most played:</span>
                    <ol>
                        {
                            _.map(_.take(state.topCounts, 5), countsItem =>
                                <li>
                                    <a class="button" onClick={this.onClick(countsItem)}>
                                        {formatOptions(countsItem)} <small className="small-number">({countsItem.solved + countsItem.solvedCheated + countsItem.over})</small>
                                    </a>
                                </li>
                            )
                        }
                    </ol>
                </div>
            );
        }
        else
            return null;
    }
}

export interface OptionsProps {
    options: PuzzleOptions;
    submit: (PuzzleOptions) => void;
    highscore: (PuzzleOptions) => void;
    defaultOptions: PuzzleOptions;
    puzzleGenerator: PuzzleGenerator;
    generating: boolean;
}

interface OptionsState {
    options: PuzzleOptions;
    hasTimes: boolean;
}

export class OptionsComponent extends Component<OptionsProps, OptionsState> {
    constructor(props: OptionsProps) {
        super();
        this.state = {
            options: _.clone(props.options),
            hasTimes: false
        };
        this.fetchHasTimes(props.options);
    }

    componentWillReceiveProps(nextProps: OptionsProps) {
        if (!_.eq(this.props, nextProps)) {
            this.setState({
                options: _.clone(nextProps.options),
                hasTimes: false
            });
            this.fetchHasTimes(nextProps.options);
        }
    }

    private onChange<K extends keyof PuzzleOptions>(field: K) {
        return (value: PuzzleOptions[K]) => {
            this.setState(state => _.merge(state, {
                options: {
                    [field as string]: value // TODO: typecheck this,
                },
                hasTimes: false
            }));
            this.fetchHasTimes(this.state.options);
            Config.set({
                options: this.state.options
            });
        };
    }

    private fetchHasTimes(options: PuzzleOptions) {
        Times.hasTimes(options).then(hasTimes => {
            this.setState({
                hasTimes: hasTimes
            });
        })
    }

    private onSubmit = (e) => {
        e.preventDefault();
        this.props.submit(this.state.options);
    };

    // No onReset on <form>
    private onReset = (e) => {
        e.preventDefault();
        this.setState({
            options: _.clone(this.props.defaultOptions),
            hasTimes: false
        });
        this.fetchHasTimes(this.state.options);
        Config.set({
            options: this.state.options
        });
    };

    private onHighscore = (e) => {
        this.props.highscore(this.state.options);
    };

    private setOptions = (options: PuzzleOptions) => {
        this.setState({
            options: _.clone(options),
            hasTimes: false
        });
        this.fetchHasTimes(this.state.options);
        Config.set({
            options: this.state.options
        });
    };

    render(props: OptionsProps, state: OptionsState) {
        return (
            <form class="options" onSubmit={this.onSubmit}>
                <fieldset disabled={props.generating}>
                    <div class="form-group">
                        <label for="option-rows">Rows</label>
                        <InputRangeComponent id="option-rows" min={2} max={6} value={state.options.rows} onChange={this.onChange("rows")}/>
                    </div>
                    <div class="form-group">
                        <label for="option-cols">Columns</label>
                        <InputRangeComponent id="option-cols" min={2} max={6} value={state.options.cols} onChange={this.onChange("cols")}/>
                    </div>
                    <div class="form-group">
                        <label for="option-extra-hints">Extra hints</label>
                        <InputRangeComponent id="option-extra-hints" min={0} max={100} step={20} value={state.options.extraHintsPercent} onChange={this.onChange("extraHintsPercent")} unit="%"/>
                    </div>
                    <div class="form-group">
                        <label for="option-difficulty">Difficulty</label>
                        <RadioChoiceComponent id="option-difficulty" choices={[["normal", "Normal"], ["hard", "Hard"]]} value={state.options.difficulty} onChange={this.onChange("difficulty")}/>
                    </div>
                    <div class="form-group buttons">
                        <button type="reset" onClick={this.onReset}>Reset</button>
                        <button type="button" disabled={!state.hasTimes} onClick={this.onHighscore}>High scores</button>
                        <button class="button-highlight button-wide" type="submit" disabled={!props.puzzleGenerator.supports(state.options)}>Play</button>
                    </div>

                    <TopOptionsComponent set={this.setOptions}/>
                </fieldset>

                {
                    props.generating ?
                        <div class="loading-overlay">Loading...</div> :
                        null
                }
            </form>
        );
    }
}