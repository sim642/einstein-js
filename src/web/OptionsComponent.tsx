import * as _ from "lodash";
import {Component, h} from "preact";
import "./options.less";
import {PuzzleOptions} from "../puzzle/Puzzle";
import {Config} from "../storage/Config";
import {Times} from "../storage/Times";

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

export interface OptionsProps {
    options: PuzzleOptions;
    submit: (PuzzleOptions) => void;
    highscore: (PuzzleOptions) => void;
    defaultOptions: PuzzleOptions;
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

    private onChange(field: keyof PuzzleOptions) {
        return (value: number) => {
            this.setState(state => _.merge(state, {
                options: {
                    [field]: value // TODO: typecheck this,
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

    render(props: OptionsProps, state: OptionsState) {
        return (
            <form class="options" onSubmit={this.onSubmit}>
                <div class="form-group">
                    <label for="option-rows">Rows</label>
                    <InputRangeComponent id="option-rows" min={3} max={6} value={state.options.rows} onChange={this.onChange("rows")}/>
                </div>
                <div class="form-group">
                    <label for="option-cols">Columns</label>
                    <InputRangeComponent id="option-cols" min={3} max={6} value={state.options.cols} onChange={this.onChange("cols")}/>
                </div>
                <div class="form-group">
                    <label for="option-extra-hints">Extra hints</label>
                    <InputRangeComponent id="option-extra-hints" min={0} max={100} step={10} value={state.options.extraHintsPercent} onChange={this.onChange("extraHintsPercent")} unit="%"/>
                </div>
                <div class="form-group buttons">
                    <button type="reset" onClick={this.onReset}>Reset</button>
                    <button type="button" disabled={!state.hasTimes} onClick={this.onHighscore}>High scores</button>
                    <button class="button-highlight button-wide" type="submit">Play</button>
                </div>
            </form>
        );
    }
}