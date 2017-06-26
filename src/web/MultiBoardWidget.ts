import * as $ from "jquery";
import * as _ from "lodash";
import {MultiBoard} from "../puzzle/board/MultiBoard";
import {Puzzle} from "../puzzle/Puzzle";
import {$Element, Widget} from "./Widget";
import {LargeVariantIconWidget, SmallVariantIconWidget} from "./IconWidgets";

type RefreshCb = () => void;

class CellWidget extends Widget {
    constructor(private board: MultiBoard, private row: number, private col: number, private refreshCb: RefreshCb) {
        super();
    }

    private onClickVariant(variant: number) {
        return e => {
            this.board.set(this.row, this.col, variant);
            this.refreshCb();
        }
    }

    private onRightClickVariant(variant: number) {
        return e => {
            e.preventDefault();
            this.board.remove(this.row, this.col, variant);
            this.refreshCb();
        }
    }

    render(): $Element {
        let $td = $("<td></td>");
        if (this.board.isSingle(this.row, this.col)) {
            let variant = this.board.getSingle(this.row, this.col);
            $td.append(
                new LargeVariantIconWidget(this.row, variant).create()
                    .addClass("cell-single")
            );
        }
        else {
            $td.append(
                $("<div></div>")
                    .addClass("cell-multi")
                    .append(...
                        _.times(this.board.variants, variant =>
                            this.board.isPossible(this.row, this.col, variant) ?
                                new SmallVariantIconWidget(this.row, variant).create()
                                    .addClass("cell-multi-variant")
                                    .click(this.onClickVariant(variant))
                                    .contextmenu(this.onRightClickVariant(variant))
                            :
                                $("<div></div>")
                                    .addClass("cell-multi-empty")
                        )
                    )
            );
        }
        return $td;
    }
}

class RowWidget extends Widget {
    constructor(private board: MultiBoard, private row: number, private refreshCb: RefreshCb) {
        super();
    }

    private refresh: RefreshCb = () => {
        this.recreate();
        this.refreshCb();
    };

    render(): $Element {
        return $("<tr></tr>")
            .append(...
                _.times(this.board.cols, col =>
                    new CellWidget(this.board, this.row, col, this.refresh).create()
                )
            )
    }
}

export class MultiBoardWidget extends Widget {
    private board: MultiBoard;

    constructor(private puzzle: Puzzle) {
        super();
        this.board = puzzle.multiBoard;
    }

    private refresh: RefreshCb = () => {
        if (this.puzzle.isSolved()) {
            alert("Solved!");
            this.$.addClass("solved");
        }
        else if (this.puzzle.isOver()) {
            alert("Over!");
            this.$.addClass("over");
        }
    };

    render(): $Element {
        return $("<table></table>")
            .addClass("multiboard")
            .append(...
                _.times(this.board.rows, row =>
                    new RowWidget(this.board, row, this.refresh).create()
                )
            )
    }
}