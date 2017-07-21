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

    let board3: MultiBoard;
    beforeEach(function () {
        board3 = MultiBoard.full({rows: 3, cols: 3});
    });

    describe("#remove()", function () {
        it("should remove variant from cell", function () {
            board3.remove(0, 1, 2);

            expect(board3.isPossible(0, 1, 2)).to.be.false;
        });

        it("should prune singles");
    });

    describe("#set()", function () {
        it("should only keep variant in cell", function () {
            board3.set(0, 1, 2);

            expect(board3.isPossible(0, 1, 2)).to.be.true;
            expect(board3.isSingle(0, 1)).to.be.true;
        });

        it("should remove variant from other cells in row", function () {
            board3.set(0, 1, 2);

            expect(board3.isPossible(0, 0, 2)).to.be.false;
            expect(board3.isPossible(0, 2, 2)).to.be.false;
        });

        it("should prune singles");
    });

    let board12: MultiBoard;
    beforeEach(function () {
        board12 = new MultiBoard([
            [[true, false], [true, true]]
        ], {rows: 1, cols: 2});
    });

    describe("#isPossible()", function () {
        it("should return variant possibility in cell", function () {
            expect(board12.isPossible(0, 0, 0)).to.be.true;
            expect(board12.isPossible(0, 0, 1)).to.be.false;
            expect(board12.isPossible(0, 1, 0)).to.be.true;
            expect(board12.isPossible(0, 1, 1)).to.be.true;
        })
    });

    describe("#count()", function () {
        it("should return variant count in cell", function () {
            expect(board12.count(0, 0)).to.equal(1);
            expect(board12.count(0, 1)).to.equal(2);
        });
    });

    describe("#isSingle()", function () {
        it("should return true for cells with one variant", function () {
            expect(board12.isSingle(0, 0)).to.be.true;
        });

        it("should return false for cells with multiple variant", function () {
            expect(board12.isSingle(0, 1)).to.be.false;
        });
    });
});