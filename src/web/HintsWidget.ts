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

    private renderTbody(): $Element {
        if (this.hint instanceof AdjacentHint) {
            return $("<tbody></tbody>")
                .append($("<tr></tr>")
                    .append($("<td></td>")
                        .append(new LargeVariantIconWidget(this.hint.row1, this.hint.variant1).create())
                    )
                    .append($("<td></td>")
                        .append(new IconWidget("hint-adjacent").create())
                    )
                    .append($("<td></td>")
                        .append(new LargeVariantIconWidget(this.hint.row2, this.hint.variant2).create())
                    )
                )
        }
        else if (this.hint instanceof BetweenHint) {
            return $("<tbody></tbody>")
                .append($("<tr></tr>")
                    .append($("<td></td>")
                        .append(new LargeVariantIconWidget(this.hint.row1, this.hint.variant1).create())
                    )
                    .append($("<td></td>")
                        .append(new LargeVariantIconWidget(this.hint.rowMiddle, this.hint.variantMiddle).create())
                        .append(new IconWidget("hint-between").create()
                            .addClass("hint-between")
                        )
                    )
                    .append($("<td></td>")
                        .append(new LargeVariantIconWidget(this.hint.row2, this.hint.variant2).create())
                    )
                )
        }
        else if (this.hint instanceof DirectionHint) {
            return $("<tbody></tbody>")
                .append($("<tr></tr>")
                    .append($("<td></td>")
                        .append(new LargeVariantIconWidget(this.hint.rowLeft, this.hint.variantLeft).create())
                    )
                    .append($("<td></td>")
                        .append(new IconWidget("hint-direction").create())
                    )
                    .append($("<td></td>")
                        .append(new LargeVariantIconWidget(this.hint.rowRight, this.hint.variantRight).create())
                    )
                )
        }
        else if (this.hint instanceof SameColumnHint) {
            return $("<tbody></tbody>")
                .append($("<tr></tr>")
                    .append($("<td></td>")
                        .append(new LargeVariantIconWidget(this.hint.row1, this.hint.variant1).create())
                    )
                )
                .append($("<tr></tr>")
                    .append($("<td></td>")
                        .append(new LargeVariantIconWidget(this.hint.row2, this.hint.variant2).create())
                    )
                )
        }
        else if (this.hint instanceof OpenHint) {
            return $("<tbody></tbody>")
                .append($("<tr></tr>")
                    .append($("<td></td>")
                        .append(new LargeVariantIconWidget(this.hint.row, this.hint.variant).create()
                            .attr("alt", this.hint.col)
                        )
                    )
                )
        }
        else
            throw new Error("Unknown hint type");
    }

    render(): $Element {
        return $("<div></div>")
            .addClass("hint-outer")
            .append($("<table></table>")
                .addClass("hint")
                .append(this.renderTbody())
            )
    }
}

export class HintsWidget extends Widget {
    constructor(private hints: Hint[]) {
        super();
    }

    render(): $Element {
        return $("<div></div>")
            .addClass("hints")
            .append($("<div></div>")
                .addClass("hints-horizontal")
                .append(...
                    _.map(_.filter(this.hints, hint => hint.getType() === HintType.Horizontal), hint =>
                        new HintWidget(hint).create()
                    )
                )
            )
            .append($("<div></div>")
                .addClass("hints-vertical")
                .append(...
                    _.map(_.filter(this.hints, hint => hint.getType() === HintType.Vertical), hint =>
                        new HintWidget(hint).create()
                    )
                )
            )
    }
}