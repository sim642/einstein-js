import {expect} from "chai";
import "mocha";
import {mean, stdDev, variance} from "../../src/math/statistics";

describe("statistics", function () {
    const exampleStudents = [2, 4, 4, 4, 5, 5, 7, 9]; // https://en.wikipedia.org/wiki/Standard_deviation#Population_standard_deviation_of_grades_of_eight_students

    describe("mean()", function () {
        it("should return the arithmetic mean", function () {
            expect(mean(exampleStudents)).to.equal(5);
        });
    });

    describe("variance()", function () {
        it("should return the variance", function () {
            expect(variance(exampleStudents)).to.equal(4);
        });
    });

    describe("stdDev()", function () {
        it("should return square root of the variance", function () {
            expect(stdDev(exampleStudents)).to.equal(2);
        });
    });
});