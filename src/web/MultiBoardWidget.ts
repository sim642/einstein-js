import * as $ from "jquery";
import * as _ from "lodash";
import {MultiBoard} from "../puzzle/board/MultiBoard";
import {Puzzle} from "../puzzle/Puzzle";
import {$Element, Widget} from "./Widget";

class ColWidget extends Widget {
    constructor(private board: MultiBoard, private row: number, private col: number, private rowWidget: RowWidget) {
        super();
    }

    private onClickVariant(variant: number) {
        this.board.set(this.row, this.col, variant);
        this.rowWidget.recreate();
    }

    private onRightClickVariant(variant: number) {
        this.board.remove(this.row, this.col, variant);
        this.rowWidget.recreate();
    }

    render(): $Element {
        return $("<td></td>").append(...
            _.times(this.board.variants, variant =>
                this.board.isPossible(this.row, this.col, variant) ?
                    $("<span></span>").text(variant).click(e => this.onClickVariant(variant)).contextmenu(e => {
                        e.preventDefault();
                        this.onRightClickVariant(variant)
                    }) :
                    $("<span></span>")
            )
        );
    }
}

class RowWidget extends Widget {
    constructor(private board: MultiBoard, private row: number) {
        super();
    }

    render(): $Element {
        return $("<tr></tr>").append(...
            _.times(this.board.cols, col =>
                new ColWidget(this.board, this.row, col, this).create()
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

    render(): $Element {
        return $("<table></table>").append(...
            _.times(this.board.rows, row =>
                new RowWidget(this.board, row).create()
            )
        )
    }
}