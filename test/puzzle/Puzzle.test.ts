import {expect} from "chai";
import * as _ from "lodash";
import "mocha";
import {Puzzle, PuzzleOptions} from "../../src/puzzle/Puzzle";
import {SingleBoard} from "../../src/puzzle/board/SingleBoard";
import {MultiBoard} from "../../src/puzzle/board/MultiBoard";
import {OpenHint} from "../../src/puzzle/hint/OpenHint";
import {SameColumnHint} from "../../src/puzzle/hint/SameColumnHint";

describe("Puzzle", function () {
    const options: PuzzleOptions = {
        rows: 3,
        cols: 3
    };
    const singleBoard: SingleBoard = new SingleBoard([
        [0, 1, 2],
        [1, 2, 0],
        [2, 0, 1]
    ]);

    describe("#constructor()", function () {

        it("should initialize full multiboard", function () {
            let puzzle = new Puzzle(singleBoard, [], options);

            let expectedBoard = MultiBoard.full(options);
            expect(puzzle.multiBoard).to.deep.equal(expectedBoard);
        });

        it("should apply hints with Start type", function () {
            let hints = [
                new OpenHint(0, 0, 0),
                new SameColumnHint(0, 0, 1, 1)
            ];

            let puzzle = new Puzzle(singleBoard, hints, options);

            let expectedBoard = MultiBoard.full(options);
            expectedBoard.set(0, 0, 0);
            expect(puzzle.multiBoard).to.deep.equal(expectedBoard);
        });
    });

    describe("#isSolved()", function () {
        it("should return true if multiboard is solved", function () {
            let puzzle = new Puzzle(singleBoard, [], options);
            puzzle.multiBoard.applySingleBoard(singleBoard);

            expect(puzzle.isSolved()).to.be.true;
        });

        it("should return false if multiboard is not solved", function () {
            let puzzle = new Puzzle(singleBoard, [], options);

            expect(puzzle.isSolved()).to.be.false;
        });
    });

    describe("#isOver()", function () {
        it("should return true if multiboard can not be solved", function () {
            let puzzle = new Puzzle(singleBoard, [], options);
            puzzle.multiBoard.remove(0, 0, 0);

            expect(puzzle.isOver()).to.be.true;
        });

        it("should return false if multiboard can be solved", function () {
            let puzzle = new Puzzle(singleBoard, [], options);

            expect(puzzle.isOver()).to.be.false;
        });
    });

    describe("#generate()", function () {
        _.forEach([
            {rows: 6, cols: 6},
            {rows: 5, cols: 5},
            {rows: 4, cols: 4},
            {rows: 6, cols: 4}
        ], (options: PuzzleOptions) => {
            context(`with ${options.rows} rows, ${options.cols} cols`, function () {
                const puzzle = Puzzle.generate(options);

                it("should return puzzle with correct size boards", function () {
                    // singleboard
                    expect(puzzle.singleBoard.rows).to.equal(options.rows);
                    expect(puzzle.singleBoard.cols).to.equal(options.cols);
                    // multiboard
                    expect(puzzle.multiBoard.rows).to.equal(options.rows);
                    expect(puzzle.multiBoard.cols).to.equal(options.cols);
                });

                it("should return puzzle which is solvable", function () {
                    let solvable = puzzle.singleBoard.isSolvable(puzzle.hints);

                    expect(solvable).to.be.true;
                });
            });
        });
    });
});