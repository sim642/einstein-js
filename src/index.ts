import {Puzzle} from "./puzzle/Puzzle";
import * as $ from "jquery";
import {MultiBoardWidget} from "./web/MultiBoardWidget";
import {HintsWidget} from "./web/HintsWidget";

let puzzle = Puzzle.generate();
console.debug(puzzle);
let multiBoardWidget = new MultiBoardWidget(puzzle);
let hintsWidget = new HintsWidget(puzzle.hints);
$("body").append(multiBoardWidget.create());
$("body").append(hintsWidget.create());