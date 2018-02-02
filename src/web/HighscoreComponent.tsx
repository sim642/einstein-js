import * as _ from "lodash";
import {Component, h} from "preact";
import "./highscore.less";
import {Times, TimesItem} from "../storage/Times";
import {PuzzleOptions} from "../puzzle/Puzzle";
import {formatDuration} from "../time";
import {formatOptions} from "./PuzzleOptionsUtils";
import * as statistics from "../math/statistics";
import * as sortedStatistics from "../math/sortedStatistics";

interface HighscoreItemProps {
    i: number;
    item: TimesItem;
}

class HighscoreItemComponent extends Component<HighscoreItemProps, {}> {
    render(props: HighscoreItemProps) {
        return (
            <tr>
                <td class="highscore-i">{`${props.i + 1}.`}</td>
                <td class="highscore-name" title={props.item.date.toString()}>{props.item.name}</td>
                <td class="highscore-time">{formatDuration(props.item.time)}</td>
            </tr>
        )
    }
}


interface HighscoreTableProps {
    top10?: TimesItem[];
}

class HighscoreTableComponent extends Component<HighscoreTableProps, {}> {
    render(props: HighscoreTableProps) {
        return (
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
                    props.top10 !== undefined && props.top10.length > 0 ?
                        _.map(props.top10, (timesItem, i) =>
                            <HighscoreItemComponent i={i} item={timesItem}/>
                        ) :
                        <tr class="highscore-text">
                            <td colSpan={3}>
                                {
                                    props.top10 !== undefined ?
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


interface Stats {
    count: number;
    mean: number;
    median: number;
    lowerQuartile: number;
    upperQuartile: number;
    stdDev: number;
}

interface StatsProps {
    stats?: Stats;
}

class StatsComponent extends Component<StatsProps, {}> {
    render(props: StatsProps) {
        return (
            props.stats !== undefined ?
                // TODO nice design
                <ul style={{
                    paddingLeft: 0,
                    listStylePosition: "inside"
                }}>
                    {_.map({...props.stats}, (value, key) =>
                        <li>{key}: {key !== "count" ? formatDuration(Math.round(value)) : value}</li>
                    )}
                </ul> :
                null
        );
    }
}


export interface HighscoreProps {
    options: PuzzleOptions;
}

interface HighscoreState {
    top10?: TimesItem[];
    stats?: Stats;
}

export class HighscoreComponent extends Component<HighscoreProps, HighscoreState> {
    constructor(props: HighscoreProps) {
        super();
        this.state = {
            top10: undefined,
            stats: undefined
        };
        this.fetchTimes(props);
    }

    componentWillReceiveProps(nextProps: HighscoreProps) {
        if (this.props.options !== nextProps.options) {
            this.fetchTimes(nextProps);
        }
    }

    private static calculateStats(timesItems: TimesItem[]): Stats {
        let sortedTimes: number[] = _.map(timesItems, "time");
        let mean = statistics.mean(sortedTimes);
        return {
            count: sortedTimes.length,
            mean: mean,
            median: sortedStatistics.median(sortedTimes),
            lowerQuartile: sortedStatistics.lowerQuartile(sortedTimes),
            upperQuartile: sortedStatistics.upperQuartile(sortedTimes),
            stdDev: statistics.stdDev(sortedTimes, mean)
        };
    }

    private fetchTimes(props: HighscoreProps) {
        Times.getSortedTimes(props.options).then(timesItems => {
            this.setState({
                top10: _.take(timesItems, 10),
                stats: HighscoreComponent.calculateStats(timesItems)
            });
        });
    }

    render(props: HighscoreProps, state: HighscoreState) {
        return (
            <div class="highscore-outer">
                <div class="highscore-title">
                    {formatOptions(props.options)}
                </div>

                <HighscoreTableComponent top10={state.top10}/>
                <StatsComponent stats={state.stats}/>
            </div>
        );
    }
}