import * as _ from "lodash";
import {Component, h} from "preact";
import {PuzzleOptions} from "../puzzle/Puzzle";

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
        return (e) => {
            e.preventDefault();
            this.setState(state => _.merge(state, {
                options: {
                    [field]: parseInt(e.target.value) // TODO: typecheck this
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
                <input type="range" min="3" max="6" step="1" value={state.options.rows.toString()} onChange={this.onChange("rows")}/>
                <input type="range" min="3" max="6" step="1" value={state.options.cols.toString()} onChange={this.onChange("cols")}/>
                <input type="submit"/>
            </form>
        );
    }
}