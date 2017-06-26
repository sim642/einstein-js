import {Puzzle} from "./puzzle/Puzzle";
import * as $ from "jquery";
import {MultiBoardWidget} from "./web/MultiBoardWidget";

let puzzle = Puzzle.generate();
let multiBoardWidget = new MultiBoardWidget(puzzle);
$("body").append(multiBoardWidget.create());