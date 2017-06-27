import {Component, h, render} from "preact";
import {Puzzle} from "./puzzle/Puzzle";
import {AppComponent} from "./web/AppComponent";
import "./index.less";

let puzzle = Puzzle.generate();
console.debug(puzzle);
render(<AppComponent puzzle={puzzle}/>, document.body);
