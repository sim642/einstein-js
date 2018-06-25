import {expect} from "chai";
import "mocha";
import {lowerQuartile, median, upperQuartile} from "../../src/math/sortedStatistics";

describe("sortedStatistics", function () {
    const example1 = [6, 7, 15, 36, 39, 40, 41, 42, 43, 47, 49]; // https://en.wikipedia.org/wiki/Quartile#Example_1
    const example2 = [7, 15, 36, 39, 40, 41]; // https://en.wikipedia.org/wiki/Quartile#Example_2

    describe("median()", function () {
        context("odd length", function () {
            it("should return middle element", function () {
                expect(median(example1)).to.equal(40);
            });
        });

        context("even length", function () {
            it("should return the average of middle elements", function () {
                expect(median(example2)).to.equal(37.5);
            });
        });
    });

    describe("lowerQuartile()", function () {
        context("odd length", function () {
            it("should return the median of lower half, including median", function () {
                expect(lowerQuartile(example1)).to.equal(25.5);
            });
        });

        context("even length", function () {
            it("should return the median of lower half", function () {
                expect(lowerQuartile(example2)).to.equal(15);
            });
        });
    });

    describe("upperQuartile()", function () {
        context("odd length", function () {
            it("should return the median of upper half, including median", function () {
                expect(upperQuartile(example1)).to.equal(42.5);
            });
        });

        context("even length", function () {
            it("should return the median of upper half", function () {
                expect(upperQuartile(example2)).to.equal(40);
            });
        });
    });
});