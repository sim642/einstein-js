import * as classNames from "classnames";
import * as _ from "lodash";
import {Component, h} from "preact";
import {MultiBoard} from "../puzzle/board/MultiBoard";
import {Puzzle} from "../puzzle/Puzzle";
import {LongTouchContextMenuHandler} from "./helper/LongTouchContextMenuHandler";
import {LargeVariantIconComponent, SmallVariantIconComponent} from "./IconComponents";
import "./multiboard.less";

type Refresh = () => void;

class SingleCellComponent extends Component<CellProps, any> {
    render(props: CellProps) {
        let variant = props.board.getSingle(props.row, props.col);
        return (
            <div class="cell-single">
                <LargeVariantIconComponent row={props.row} variant={variant}/>
            </div>
        );
    }
}

class VariantVariantMultiCellComponent extends Component<VariantProps, any> {
    private contextMenuHandler = new LongTouchContextMenuHandler(() => this.remove());

    private set() {
        this.props.board.set(this.props.row, this.props.col, this.props.variant);
        this.props.refresh();
    }

    private remove() {
        this.props.board.remove(this.props.row, this.props.col, this.props.variant);
        this.props.refresh();
    }

    private onClick = (e) => {
        this.set();
    };

    render(props: VariantProps) {
        return (
            <div class="cell-multi-variant" onClick={this.onClick} {...this.contextMenuHandler}>
                <SmallVariantIconComponent row={props.row} variant={props.variant}/>
            </div>
        );
    }
}

class EmptyVariantMultiCellComponent extends Component<VariantProps, any> {
    render(props: VariantProps) {
        return (
            <div class="cell-multi-empty"/>
        );
    }
}

interface VariantProps extends CellProps {
    variant: number;
}

class VariantMultiCellComponent extends Component<VariantProps, any> {
    render(props: VariantProps) {
        if (props.variant < props.board.variants &&
            props.board.isPossible(props.row, props.col, props.variant))
            return <VariantVariantMultiCellComponent {...props}/>;
        else
            return <EmptyVariantMultiCellComponent {...props}/>;
    }
}

class MultiCellComponent extends Component<CellProps, any> {
    render(props: CellProps) {
        let variantCols = Math.ceil(Math.sqrt(props.board.variants));
        let variantRows = Math.ceil(props.board.variants / variantCols);
        return (
            <table class="cell-multi">
                {_.times(variantRows, variantRow =>
                    <tr>
                        {_.times(variantCols, variantCol =>
                            <td>
                                <VariantMultiCellComponent {...props} variant={variantRow * variantCols + variantCol}/>
                            </td>
                        )}
                    </tr>
                )}
            </table>
        )
    }
}

interface CellProps extends RowProps {
    col: number;
}

class CellComponent extends Component<CellProps, any> {
    private onContextMenu = (e) => {
        e.preventDefault();
    };

    render(props: CellProps) {
        return (
            <td>
                <div class="cell" onContextMenu={this.onContextMenu}>
                    {
                        props.board.isSingle(props.row, props.col) ?
                            <SingleCellComponent {...props}/> :
                            <MultiCellComponent {...props}/>
                    }
                </div>
            </td>
        )
    }
}

interface RowProps {
    board: MultiBoard;
    row: number;
    refresh: Refresh;
}

class RowComponent extends Component<RowProps, any> {
    private refresh: Refresh = () => {
        this.forceUpdate();
        this.props.refresh();
    };

    render(props: RowProps) {
        return (
            <tr>
                {_.times(props.board.cols, col =>
                    <CellComponent {...props} col={col} refresh={this.refresh}/>
                )}
            </tr>
        );
    }
}

export interface MultiBoardProps {
    puzzle: Puzzle;
    refresh: Refresh;
}

export class MultiBoardComponent extends Component<MultiBoardProps, any> {
    render(props: MultiBoardProps) {
        let board = props.puzzle.multiBoard;
        return (
            <div class="multiboard-outer">
                <table class={classNames({
                    "multiboard": true,
                    "solved": props.puzzle.isSolved(),
                    "over": props.puzzle.isOver()
                })}>
                    {_.times(board.rows, row =>
                        <RowComponent board={board} row={row} refresh={props.refresh}/>
                    )}
                </table>
            </div>
        );
    }
}