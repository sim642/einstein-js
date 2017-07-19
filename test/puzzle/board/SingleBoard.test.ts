import {expect} from "chai";
import * as _ from "lodash";
import "mocha";
import {BoardOptions} from "../../../src/puzzle/board/Board";
import {SingleBoard} from "../../../src/puzzle/board/SingleBoard";

describe("SingleBoard", function () {
    describe("#random()", function () {
        _.forEach([
            {rows: 6, cols: 6},
            {rows: 5, cols: 5},
            {rows: 4, cols: 4},
            {rows: 6, cols: 4}
        ], (options: BoardOptions) => {
            context(`with ${options.rows} rows, ${options.cols} cols`, function () {
                it("should return correct size board", function () {
                    let board = SingleBoard.random(options);

                    expect(board.rows).to.equal(options.rows);
                    expect(board.cols).to.equal(options.cols);

                    _.forEach(_.range(0, options.rows), row => {
                        _.forEach(_.range(0, options.cols), col => {
                            expect(board.get(row, col)).to.be.a("number");
                        });
                    });
                });

                it("should return board with permutations as rows", function () {
                    let board = SingleBoard.random(options);

                    expect(board.variants).to.equal(options.cols);

                    _.forEach(_.range(0, options.rows), row => {
                        let rowValues = _.map(_.range(0, options.cols), col => board.get(row, col));
                        expect(rowValues).to.have.members(_.range(0, options.cols));
                    });
                });
            });
        });
    });
});