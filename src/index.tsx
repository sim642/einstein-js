import {Component, h, render} from "preact";
import {Puzzle} from "./puzzle/Puzzle";
import {AppComponent} from "./web/AppComponent";

let puzzle = Puzzle.generate();
console.debug(puzzle);
render(<AppComponent puzzle={puzzle}/>, document.body);

/*var width = (window.innerWidth > 0) ? window.innerWidth : screen.width;
alert(width);*/
