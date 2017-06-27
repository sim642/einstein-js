import * as $ from "jquery";
import {Puzzle} from "./puzzle/Puzzle";
import {HintsWidget} from "./web/HintsWidget";
import {MultiBoardWidget} from "./web/MultiBoardWidget";

let puzzle = Puzzle.generate();
console.debug(puzzle);
let multiBoardWidget = new MultiBoardWidget(puzzle);
let hintsWidget = new HintsWidget(puzzle.hints);
$("body").append(multiBoardWidget.create());
$("body").append(hintsWidget.create());

document.body.appendChild(
    <div>
        Foo!
    </div>
);