import "mocha";
import {assert} from "chai";
import {SingleBoard} from "../src/puzzle/board/SingleBoard";

describe("Test", function () {
    it("should succeed", function () {
        assert(true);
    });

    it("should fail", function () {
        // assert(false);
    });
});

describe("Board", function () {
    it("should work", function () {
        SingleBoard.random({rows: 6, cols: 6});
    });
});