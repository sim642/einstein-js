import * as _ from "lodash";
import {Component, h} from "preact";
import "./highscore.less";
import "./spinner.less";
import {Counts} from "../storage/Counts";
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
    stdDev: number;
    lowerQuartile: number;
    median: number;
    upperQuartile: number;
    max: number;
}

interface StatsProps {
    options: PuzzleOptions;
    stats?: Stats;
}

interface StatsState {
    counts?: Counts;
}

class StatsComponent extends Component<StatsProps, StatsState> {
    constructor(props: StatsProps) {
        super();
        this.state = {
            counts: undefined
        };
        this.fetchCounts(props);
    }

    componentWillReceiveProps(nextProps: StatsProps) {
        if (this.props.options !== nextProps.options) {
            this.fetchCounts(nextProps);
        }
    }

    private fetchCounts(props: StatsProps) {
        Counts.get(props.options).then(countsItem => {
            this.setState({
                counts: countsItem
            });
        });
    }

    render(props: StatsProps, state: StatsState) {
        const stats = props.stats;
        const counts = state.counts;

        if (stats !== undefined && counts !== undefined) {
            let total = counts.solved + counts.solvedCheated + counts.over;

            let countWithPercentage = (count) => {
                let percentage = count / total * 100;
                return (
                    <dd>{count} <small class="small-number">({percentage.toFixed(0)}%)</small></dd>
                );
            };

            return (
                <div class="stats">
                    <dl>
                        <div>
                            <dt>Games played</dt>
                            <dd>{total}</dd>
                        </div>
                        <dl>
                            <div>
                                <dt>Solved</dt>
                                {countWithPercentage(counts.solved)}
                            </div>
                            <div>
                                <dt>Solved <small>w/</small> cheats</dt>
                                {countWithPercentage(counts.solvedCheated)}
                            </div>
                            <div>
                                <dt>Over</dt>
                                {countWithPercentage(counts.over)}
                            </div>
                        </dl>

                        <div>
                            <dt>Time average</dt>
                            <dd>{formatDuration(stats.mean)}</dd>
                        </div>
                        <dl>
                            <div>
                                <dt>Std. dev.</dt>
                                <dd>{formatDuration(stats.stdDev)}</dd>
                            </div>
                        </dl>

                        <div>
                            <dt>Time quartiles</dt>
                        </div>
                        <dl>
                            <div>
                                <dt>Lower <small>(25%)</small></dt>
                                <dd>{formatDuration(stats.lowerQuartile)}</dd>
                            </div>
                            <div>
                                <dt>Median <small>(50%)</small></dt>
                                <dd>{formatDuration(stats.median)}</dd>
                            </div>
                            <div>
                                <dt>Upper <small>(75%)</small></dt>
                                <dd>{formatDuration(stats.upperQuartile)}</dd>
                            </div>
                            <div>
                                <dt>Max</dt>
                                <dd>{formatDuration(stats.max)}</dd>
                            </div>
                        </dl>
                    </dl>
                </div>
            );
        } else
            return null;
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
            stdDev: statistics.stdDev(sortedTimes, mean),
            lowerQuartile: sortedStatistics.lowerQuartile(sortedTimes),
            median: sortedStatistics.median(sortedTimes),
            upperQuartile: sortedStatistics.upperQuartile(sortedTimes),
            max: _.max(sortedTimes) as number // never undefined because always has times
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
                <hr/>
                <StatsComponent options={props.options} stats={state.stats}/>
            </div>
        );
    }
}