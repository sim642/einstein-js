import {setClass} from "../../object";
import {BoardOptions} from "../board/Board";
import {MultiBoard} from "../board/MultiBoard";
import {SingleBoard} from "../board/SingleBoard";
import {AdjacentHint} from "./AdjacentHint";
import {BetweenHint} from "./BetweenHint";
import {DirectionHint} from "./DirectionHint";
import {OpenHint} from "./OpenHint";
import {SameColumnHint} from "./SameColumnHint";

export const enum HintType {
    Start,
    Horizontal,
    Vertical,
}

export const enum HintClass {
    Adjacent,
    Between,
    Direction,
    Open,
    SameColumn
}

export interface Hint {
    class: HintClass;
    applyTo(board: MultiBoard): boolean;
    getType(): HintType;
}

export interface HintFactory {
    supports(options: BoardOptions): boolean;
    random(board: SingleBoard): Hint;
}

export namespace Hint {
    export function hydrate(o: Hint): void {
        switch (o.class) {
            case HintClass.Adjacent:
                setClass(o, AdjacentHint);
                break;

            case HintClass.Between:
                setClass(o, BetweenHint);
                break;

            case HintClass.Direction:
                setClass(o, DirectionHint);
                break;

            case HintClass.Open:
                setClass(o, OpenHint);
                break;

            case HintClass.SameColumn:
                setClass(o, SameColumnHint);
                break;
        }
    }
}