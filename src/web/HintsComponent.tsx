import * as $ from "jquery";
import * as _ from "lodash";
import {Component, h} from "preact";
import {AdjacentHint} from "../puzzle/hint/AdjacentHint";
import {BetweenHint} from "../puzzle/hint/BetweenHint";
import {DirectionHint} from "../puzzle/hint/DirectionHint";
import {Hint, HintType} from "../puzzle/hint/Hint";
import {SameColumnHint} from "../puzzle/hint/SameColumnHint";
import {IconComponent, LargeVariantIconComponent} from "./IconComponents";

interface HintProps {
    hint: Hint;
}

class HintComponent extends Component<HintProps, any> {
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

    private onRightClick(e) {
        e.preventDefault();
        $(this).hide();
    }

    render(props: HintProps) {
        return (
            <div class="hint-outer" onContextMenu={this.onRightClick}>
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

export class HintsComponent extends Component<HintsProps, any> {
    private onToggle(e) {
        $(".hint-outer").toggle();
    }

    render(props: HintsProps) {
        return (
            <div class="hints">
                <button onClick={this.onToggle}>Toggle</button>
                <div class="hints-horizontal">
                    {_.map(_.filter(props.hints, hint => hint.getType() === HintType.Horizontal), hint =>
                        <HintComponent hint={hint}/>
                    )}
                </div>
                <div class="hints-horizontal">
                    {_.map(_.filter(props.hints, hint => hint.getType() === HintType.Vertical), hint =>
                        <HintComponent hint={hint}/>
                    )}
                </div>
            </div>
        );
    }
}