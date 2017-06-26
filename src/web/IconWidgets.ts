import * as $ from "jquery";
import {$Element, Widget} from "./Widget";

export class IconWidget extends Widget {
    constructor(private name: string) {
        super();
    }

    render(): $Element {
        return $("<img>")
            .attr("src", `./icons/original/${this.name}.png`);
    }
}

export class LargeVariantIconWidget extends IconWidget {
    constructor(row: number, variant: number) {
        super(`large/large-${(row + 10).toString(16)}${variant + 1}`)
    }
}

export class SmallVariantIconWidget extends IconWidget {
    constructor(row: number, variant: number) {
        super(`small/small-${(row + 10).toString(16)}${variant + 1}`)
    }
}