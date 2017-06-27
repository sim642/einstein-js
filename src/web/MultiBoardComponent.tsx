import * as _ from "lodash";
import {Component, h} from "preact";
import {MultiBoard} from "../puzzle/board/MultiBoard";
import {Puzzle} from "../puzzle/Puzzle";
import {LargeVariantIconComponent, SmallVariantIconComponent} from "./IconComponents";

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
    private onClick(e) {
        this.props.board.set(this.props.row, this.props.col, this.props.variant);
        this.props.refresh();
    }

    private onRightClick(e) {
        e.preventDefault();
        this.props.board.remove(this.props.row, this.props.col, this.props.variant);
        this.props.refresh();
    }

    render(props: VariantProps) {
        return (
            <div class="cell-multi-variant" onClick={this.onClick} onContextMenu={this.onRightClick}>
                <SmallVariantIconComponent row={props.row} variant={props.variant}/>
            </div>
        );
    }
}

class EmptyVariantMultiCellComponent extends Component<VariantProps, any> {
    render(props: VariantProps) {
        return (
            <div class="cell-multi-empty square"/>
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
    refresh: Refresh;
}

class CellComponent extends Component<CellProps, any> {

    render(props: CellProps) {
        return (
            <td>
                <div class="square">
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
}

class RowComponent extends Component<RowProps, MultiBoard> {
    constructor(props: RowProps) {
        super();
        this.state = props.board;
    }

    private refresh() {
        this.forceUpdate();
    }

    render(props: RowProps, state: MultiBoard) {
        return (
            <tr>
                {_.times(state.cols, col =>
                    <CellComponent board={state} row={props.row} col={col} refresh={this.refresh}/>
                )}
            </tr>
        );
    }
}

export interface MultiBoardProps {
    puzzle: Puzzle;
}

export class MultiBoardComponent extends Component<MultiBoardProps, MultiBoard> {
    constructor(props: MultiBoardProps) {
        super();
        this.state = props.puzzle.multiBoard;
    }

    /*private refresh: Refresh = () => {
        if (this.puzzle.isSolved()) {
            alert("Solved!");
            this.$.addClass("solved");
        }
        else if (this.puzzle.isOver()) {
            alert("Over!");
            this.$.addClass("over");
        }
    };*/

    render(props: MultiBoardProps, state: MultiBoard) {
        return (
            <table class="multiboard">
                {_.times(state.rows, row =>
                    <RowComponent board={state} row={row}/>
                )}
            </table>
        );
    }
}