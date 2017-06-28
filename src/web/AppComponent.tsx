import {Component, h} from "preact";
import {MultiBoardComponent} from "./MultiBoardComponent";
import {Puzzle} from "../puzzle/Puzzle";
import {HintsComponent} from "./HintsComponent";
import "./app.less";

export interface AppProps {
    puzzle: Puzzle;
}

export class AppComponent extends Component<AppProps, any> {
    render(props: AppProps) {
        return (
            <div class="app">
                <MultiBoardComponent puzzle={props.puzzle}/>
                <HintsComponent hints={props.puzzle.hints}/>
            </div>
        );
    }
}