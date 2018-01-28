import * as _ from "lodash";
import {Component, h} from "preact";
import "./highscore.less";
import {db} from "../db";
import {TimesItem} from "../EinsteinDatabase";
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
                <td class="highscore-name">{props.item.date.toISOString()}</td>
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
        db.times.where({...props.options}).sortBy("time").then(timesItems => {
            let top10 = _.take(timesItems, 10);
            this.setState({
                top10: top10
            });
        });
    }

    render(props: HighscoreProps, state: HighscoreState) {
        return (
            <table class="highscore">
                <thead>
                    <tr class="highscore-title">
                        <th colSpan={3}>
                            {`High scores for ${formatOptions(props.options)}`}
                        </th>
                    </tr>
                    <tr>
                        <th class="highscore-i">#</th>
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
        );
    }
}