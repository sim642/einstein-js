import * as $ from "jquery";
import * as _ from "lodash";
import {AdjacentHint} from "../puzzle/hint/AdjacentHint";
import {BetweenHint} from "../puzzle/hint/BetweenHint";
import {DirectionHint} from "../puzzle/hint/DirectionHint";
import {Hint, HintType} from "../puzzle/hint/Hint";
import {OpenHint} from "../puzzle/hint/OpenHint";
import {SameColumnHint} from "../puzzle/hint/SameColumnHint";
import {IconWidget, LargeVariantIconWidget} from "./IconWidgets";
import {$Element, Widget} from "./Widget";

class HintWidget extends Widget {
    constructor(private hint: Hint) {
        super();
    }

    private renderTbody(): Element {
        if (this.hint instanceof AdjacentHint) {
            return (
                <tbody>
                    <tr>
                        <td>
                            {new LargeVariantIconWidget(this.hint.row1, this.hint.variant1).create2()}
                        </td>
                        <td>
                            {new IconWidget("hint-adjacent").create2()}
                        </td>
                        <td>
                            {new LargeVariantIconWidget(this.hint.row2, this.hint.variant2).create2()}
                        </td>
                    </tr>
                </tbody>
            );
        }
        else if (this.hint instanceof BetweenHint) {
            return (
                <tbody>
                    <tr>
                        <td>
                            {new LargeVariantIconWidget(this.hint.row1, this.hint.variant1).create2()}
                        </td>
                        <td>
                            {new LargeVariantIconWidget(this.hint.rowMiddle, this.hint.variantMiddle).create2()}
                            {new IconWidget("hint-between").create()
                                .addClass("hint-between")[0]}
                        </td>
                        <td>
                            {new LargeVariantIconWidget(this.hint.row2, this.hint.variant2).create2()}
                        </td>
                    </tr>
                </tbody>
            );
        }
        else if (this.hint instanceof DirectionHint) {
            return (
                <tbody>
                    <tr>
                        <td>
                            {new LargeVariantIconWidget(this.hint.rowLeft, this.hint.variantLeft).create2()}
                        </td>
                        <td>
                            {new IconWidget("hint-direction").create2()}
                        </td>
                        <td>
                            {new LargeVariantIconWidget(this.hint.rowRight, this.hint.variantRight).create2()}
                        </td>
                    </tr>
                </tbody>
            );
        }
        else if (this.hint instanceof SameColumnHint) {
            return (
                <tbody>
                    <tr>
                        <td>
                            {new LargeVariantIconWidget(this.hint.row1, this.hint.variant1).create2()}
                        </td>
                    </tr>
                    <tr>
                        <td>
                            {new LargeVariantIconWidget(this.hint.row2, this.hint.variant2).create2()}
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

    render(): $Element {
        return $(
            <div class="hint-outer" oncontextmenu={this.onRightClick}>
                <table class="hint">
                    {this.renderTbody()}
                </table>
            </div>
        );
    }
}

export class HintsWidget extends Widget {
    constructor(private hints: Hint[]) {
        super();
    }

    private onToggle(e) {
        $(".hint-outer").toggle();
    }

    render(): $Element {
        return $(
            <div class="hints">
                <button onclick={this.onToggle}>Toggle</button>
                <div class="hints-horizontal">
                    {_.map(_.filter(this.hints, hint => hint.getType() === HintType.Horizontal), hint =>
                        new HintWidget(hint).create2()
                    )}
                </div>
                <div class="hints-horizontal">
                    {_.map(_.filter(this.hints, hint => hint.getType() === HintType.Vertical), hint =>
                        new HintWidget(hint).create2()
                    )}
                </div>
            </div>
        );
    }
}