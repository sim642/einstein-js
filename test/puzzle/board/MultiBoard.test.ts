import {expect} from "chai";
import * as _ from "lodash";
import "mocha";
import {BoardOptions} from "../../../src/puzzle/board/Board";
import {MultiBoard} from "../../../src/puzzle/board/MultiBoard";

describe("MultiBoard", function () {
    describe("#full()", function () {
        _.forEach([
            {rows: 6, cols: 6},
            {rows: 5, cols: 5},
            {rows: 4, cols: 4},
            {rows: 6, cols: 4}
        ], (options: BoardOptions) => {
            context(`with ${options.rows} rows, ${options.cols} cols`, function () {
                it("should return correct size board", function () {
                    let board = MultiBoard.full(options);

                    expect(board.rows).to.equal(options.rows);
                    expect(board.cols).to.equal(options.cols);

                    _.forEach(_.range(0, options.rows), row => {
                        _.forEach(_.range(0, options.cols), col => {
                            expect(board.get(row, col)).to.be.an("Array");
                        });
                    });
                });

                it("should return board with all variants", function () {
                    let board = MultiBoard.full(options);

                    expect(board.variants).to.equal(options.cols);

                    const allVariants = _.times(options.cols, _.constant(true));
                    _.forEach(_.range(0, options.rows), row => {
                        _.forEach(_.range(0, options.cols), col => {
                            expect(board.get(row, col)).to.deep.equal(allVariants);
                        });
                    });
                });
            });
        });
    });

    describe("#remove()", function () {
        it("should remove variant from cell", function () {
            let board = MultiBoard.full({rows: 3, cols: 3});

            board.remove(0, 1, 2);

            expect(board.isPossible(0, 1, 2)).to.be.false;
        });

        it("should prune singles");
    });
});