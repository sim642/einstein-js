import {expect} from "chai";
import "mocha";
import {MultiBoard} from "../../src/puzzle/board/MultiBoard";
import {SingleBoard} from "../../src/puzzle/board/SingleBoard";
import {OpenHint} from "../../src/puzzle/hint/OpenHint";
import {SameColumnHint} from "../../src/puzzle/hint/SameColumnHint";
import {Puzzle, PuzzleOptions} from "../../src/puzzle/Puzzle";
import {paramPuzzleOptions} from "./paramPuzzle";
import {param} from "../param";

describe("Puzzle", function () {
    const options: PuzzleOptions = {
        rows: 3,
        cols: 3,
        extraHintsPercent: 0
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
        context("returned puzzle", function () {
            paramPuzzleOptions(function (options) {
                param.repeat(20, () => Puzzle.generate(options), function (puzzlePromise) {
                    it("should have correct size boards", async function () {
                        let puzzle = await puzzlePromise;

                        // singleboard
                        expect(puzzle.singleBoard.rows).to.equal(options.rows);
                        expect(puzzle.singleBoard.cols).to.equal(options.cols);
                        // multiboard
                        expect(puzzle.multiBoard.rows).to.equal(options.rows);
                        expect(puzzle.multiBoard.cols).to.equal(options.cols);
                    });

                    it("should be solvable", async function () {
                        let puzzle = await puzzlePromise;

                        let solvable = puzzle.singleBoard.isSolvable(puzzle.hints);

                        expect(solvable).to.be.true;
                    });
                });
            });
        });
    });
});