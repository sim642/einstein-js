import * as classNames from "classnames";
import * as _ from "lodash";
import {Component, h} from "preact";
import {AdjacentHint} from "../puzzle/hint/AdjacentHint";
import {BetweenHint} from "../puzzle/hint/BetweenHint";
import {DirectionHint} from "../puzzle/hint/DirectionHint";
import {Hint, HintType} from "../puzzle/hint/Hint";
import {SameColumnHint} from "../puzzle/hint/SameColumnHint";
import {LongTouchContextMenuHandler} from "./helper/LongTouchContextMenuHandler";
import "./hints.less";
import {IconComponent, LargeVariantIconComponent} from "./IconComponents";

interface VisibilityState {
    visible: boolean;
}

interface HintProps {
    hint: Hint;
}

class HintComponent extends Component<HintProps, VisibilityState> {
    private contextMenuHandler = new LongTouchContextMenuHandler(() => this.onToggle());

    constructor() {
        super();
        this.state = {
            visible: true
        };
    }

    componentWillReceiveProps(nextProps: HintProps) {
        if (this.props.hint !== nextProps.hint) {
            this.setState({
                visible: true
            });
        }
    }

    private onToggle = () => {
        this.setState(state => {
            return {
                visible: !state.visible
            };
        });
    };

    private renderTbody(props: HintProps) {
        let hint = props.hint;
        if (hint instanceof AdjacentHint) {
            return (
                <tbody>
                    <tr>
                        <td>
                            <LargeVariantIconComponent row={hint.row1} variant={hint.variant1}/>
                        </td>
                        <td>
                            <IconComponent name="hint-adjacent"/>
                        </td>
                        <td>
                            <LargeVariantIconComponent row={hint.row2} variant={hint.variant2}/>
                        </td>
                    </tr>
                </tbody>
            );
        }
        else if (hint instanceof BetweenHint) {
            return (
                <tbody>
                    <tr>
                        <td>
                            <LargeVariantIconComponent row={hint.row1} variant={hint.variant1}/>
                        </td>
                        <td>
                            <LargeVariantIconComponent row={hint.rowMiddle} variant={hint.variantMiddle}/>
                            <div class="hint-between">
                                <IconComponent name="hint-between"/>
                            </div>
                        </td>
                        <td>
                            <LargeVariantIconComponent row={hint.row2} variant={hint.variant2}/>
                        </td>
                    </tr>
                </tbody>
            );
        }
        else if (hint instanceof DirectionHint) {
            return (
                <tbody>
                    <tr>
                        <td>
                            <LargeVariantIconComponent row={hint.rowLeft} variant={hint.variantLeft}/>
                        </td>
                        <td>
                            <IconComponent name="hint-direction"/>
                        </td>
                        <td>
                            <LargeVariantIconComponent row={hint.rowRight} variant={hint.variantRight}/>
                        </td>
                    </tr>
                </tbody>
            );
        }
        else if (hint instanceof SameColumnHint) {
            return (
                <tbody>
                    <tr>
                        <td>
                            <LargeVariantIconComponent row={hint.row1} variant={hint.variant1}/>
                        </td>
                    </tr>
                    <tr>
                        <td>
                            <LargeVariantIconComponent row={hint.row2} variant={hint.variant2}/>
                        </td>
                    </tr>
                </tbody>
            );
        }
        else
            throw new Error("Unsupported hint type");
    }

    render(props: HintProps, state: VisibilityState) {
        return (
            <div class={classNames({
                "hint-outer": true,
                "hint-visible": state.visible,
                "hint-hidden": !state.visible
            })} {...this.contextMenuHandler}>
                <table class="hint">
                    {this.renderTbody(props)}
                </table>
            </div>
        );
    }
}

export interface HintsProps {
    hints: Hint[];
}

export class HintsComponent extends Component<HintsProps, VisibilityState> {
    constructor() {
        super();
        this.state = {
            visible: true
        };
    }

    componentWillReceiveProps(nextProps: HintsProps) {
        if (this.props.hints !== nextProps.hints) {
            this.setState({
                visible: true
            });
        }
    }

    private onToggle = (e) => {
        this.setState(state => {
            return {
                visible: !state.visible
            };
        });
    };

    render(props: HintsProps, state: VisibilityState) {
        return (
            <div class="hints">
                <button class="button-toggle" onClick={this.onToggle}>Toggle</button>
                <div class={classNames({
                    "hints-horizontal": true,
                    "hints-visible": state.visible,
                    "hints-hidden": !state.visible
                })}>
                    {_.map(_.filter(props.hints, hint => hint.getType() === HintType.Horizontal), hint =>
                        <HintComponent hint={hint}/>
                    )}
                    {/*<div class="hints-vertical">*/}
                        {_.map(_.filter(props.hints, hint => hint.getType() === HintType.Vertical), hint =>
                            <HintComponent hint={hint}/>
                        )}
                    {/*</div>*/}
                </div>
            </div>
        );
    }
}