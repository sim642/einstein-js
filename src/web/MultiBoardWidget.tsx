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
        let el;
        if (this.board.isSingle(this.row, this.col)) {
            let variant = this.board.getSingle(this.row, this.col);
            el = new LargeVariantIconWidget(this.row, variant).create()
                .addClass("cell-single")[0];
        }
        else {
            let variantCols = Math.ceil(Math.sqrt(this.board.variants));
            let variantRows = Math.ceil(this.board.variants / variantCols);
            el = (
                <table class="cell-multi">
                    {_.times(variantRows, variantRow => (
                            <tr>
                                {_.times(variantCols, variantCol => {
                                        let variant = variantRow * variantCols + variantCol;
                                        let el;
                                        if (variant < this.board.variants && this.board.isPossible(this.row, this.col, variant)) {
                                            el = new SmallVariantIconWidget(this.row, variant).create()
                                                .addClass("cell-multi-variant")
                                                .click(this.onClickVariant(variant))
                                                .contextmenu(this.onRightClickVariant(variant))[0];
                                        }
                                        else {
                                            el = (
                                                <div class="cell-multi-empty square"/>
                                            )
                                        }
                                        return (
                                            <td>
                                                {el}
                                            </td>
                                        );
                                    }
                                )}
                            </tr>
                        )
                    )}
                </table>
            );
        }

        return (
            <td>
                <div class="square">
                    {el}
                </div>
            </td>
        )
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
        return $(
            <table class="multiboard">
                {_.times(this.board.rows, row =>
                    new RowWidget(this.board, row, this.refresh).create2()
                )}
            </table>
        );
    }
}