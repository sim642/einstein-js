import * as _ from "lodash";
import {Component, h} from "preact";
import "./options.less";
import {PuzzleOptions} from "../puzzle/Puzzle";

interface RangeProps {
    value: number;
    min: number;
    max: number;
    onChange: (value: number) => void;
    id?: string;
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
                <output for={props.id}>{props.value}</output>

                <datalist id={listId}>
                    {_.map(_.range(props.min, props.max + 1), value =>
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
}

interface OptionsState {
    options: PuzzleOptions;
}

export class OptionsComponent extends Component<OptionsProps, OptionsState> {
    constructor(props: OptionsProps) {
        super();
        this.state = {
            options: _.clone(props.options)
        };
    }

    private onChange(field: keyof PuzzleOptions) {
        return (value: number) => {
            this.setState(state => _.merge(state, {
                options: {
                    [field]: value // TODO: typecheck this
                }
            }));
        };
    }

    private onSubmit = (e) => {
        e.preventDefault();
        this.props.submit(this.state.options);
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
                <div class="form-group buttons">
                    <button class="button-highlight" type="submit">Play</button>
                </div>
            </form>
        );
    }
}