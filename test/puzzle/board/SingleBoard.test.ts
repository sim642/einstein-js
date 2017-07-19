import {expect} from "chai";
import * as _ from "lodash";
import "mocha";
import {BoardOptions} from "../../../src/puzzle/board/Board";
import {SingleBoard} from "../../../src/puzzle/board/SingleBoard";

describe("SingleBoard", function () {
    describe("#random()", function () {
        const options: BoardOptions = {
            rows: 6,
            cols: 6
        };

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