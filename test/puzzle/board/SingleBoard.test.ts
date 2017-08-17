import {expect} from "chai";
import * as _ from "lodash";
import "mocha";
import {SingleBoard} from "../../../src/puzzle/board/SingleBoard";
import {OpenHint} from "../../../src/puzzle/hint/OpenHint";
import {SameColumnHint} from "../../../src/puzzle/hint/SameColumnHint";
import {paramBoardOptions} from "../paramPuzzle";

describe("SingleBoard", function () {
    describe("#random()", function () {
        paramBoardOptions(function (options) {
            const board = SingleBoard.random(options);

            it("should return correct size board", function () {
                expect(board.rows).to.equal(options.rows);
                expect(board.cols).to.equal(options.cols);

                _.forEach(_.range(0, options.rows), row => {
                    _.forEach(_.range(0, options.cols), col => {
                        expect(board.get(row, col)).to.be.a("number");
                    });
                });
            });

            it("should return board with permutations as rows", function () {
                expect(board.variants).to.equal(options.cols);

                _.forEach(_.range(0, options.rows), row => {
                    let rowValues = _.map(_.range(0, options.cols), col => board.get(row, col));
                    expect(rowValues).to.have.members(_.range(0, options.cols));
                });
            });
        });
    });

    describe("#isSolvable()", function () {
        const board = new SingleBoard([
            [0, 1],
            [1, 0]
        ]);

        it("should return true if board is solvable using hints", function () {
            let hints = [
                new SameColumnHint(0, 1, 1, 0),
                new OpenHint(0, 0, 0)
            ];

            let solvable = board.isSolvable(hints);

            expect(solvable).to.be.true;
        });

        it("should return false if board is not solvable using hints", function () {
            let hints = [
                new OpenHint(0, 0, 0)
            ];

            let solvable = board.isSolvable(hints);

            expect(solvable).to.be.false;
        });
    });
});