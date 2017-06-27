import {Component, h, render} from "preact";
import {Puzzle} from "./puzzle/Puzzle";
import {AppComponent} from "./web/AppComponent";

let puzzle = Puzzle.generate();
console.debug(puzzle);
render(<AppComponent puzzle={puzzle}/>, document.body);
