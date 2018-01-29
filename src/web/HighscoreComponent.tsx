import * as _ from "lodash";
import {Component, h} from "preact";
import "./highscore.less";
import {Times, TimesItem} from "../storage/Times";
import {PuzzleOptions} from "../puzzle/Puzzle";
import {formatDuration} from "../time";
import {formatOptions} from "./PuzzleOptionsUtils";

interface HighscoreItemProps {
    i: number;
    item: TimesItem;
}

class HighscoreItemComponent extends Component<HighscoreItemProps, {}> {
    render(props: HighscoreItemProps) {
        return (
            <tr>
                <td class="highscore-i">{`${props.i + 1}.`}</td>
                <td class="highscore-name" title={props.item.date.toISOString()}>{props.item.name}</td>
                <td class="highscore-time">{formatDuration(props.item.time)}</td>
            </tr>
        )
    }
}

export interface HighscoreProps {
    options: PuzzleOptions;
}

interface HighscoreState {
    top10?: TimesItem[];
}

export class HighscoreComponent extends Component<HighscoreProps, HighscoreState> {
    constructor(props: HighscoreProps) {
        super();
        this.state = {
            top10: undefined
        };
        this.fetchTop10(props);
    }

    componentWillReceiveProps(nextProps: HighscoreProps) {
        if (this.props.options !== nextProps.options) {
            this.fetchTop10(nextProps);
        }
    }

    private fetchTop10(props: HighscoreProps) {
        Times.getTop10(props.options).then(top10 => {
            this.setState({
                top10: top10
            });
        });
    }

    render(props: HighscoreProps, state: HighscoreState) {
        return (
            <div class="highscore-outer">
                <div class="highscore-title">
                    {formatOptions(props.options)}
                </div>
                <table class="highscore">
                    <thead>
                        <tr>
                            <th class="highscore-i">#&nbsp;</th>
                            <th class="highscore-name">Name</th>
                            <th class="highscore-time">Time</th>
                        </tr>
                    </thead>

                    <tbody>
                        {
                            state.top10 !== undefined && state.top10.length > 0 ?
                                _.map(state.top10, (timesItem, i) =>
                                    <HighscoreItemComponent i={i} item={timesItem}/>
                                ) :
                                <tr class="highscore-text">
                                    <td colSpan={3}>
                                        {
                                            state.top10 !== undefined ?
                                                "No times" :
                                                "Loading..."
                                        }
                                    </td>
                                </tr>
                        }
                    </tbody>
                </table>
            </div>
        );
    }
}