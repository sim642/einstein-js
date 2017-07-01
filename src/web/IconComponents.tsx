import {Component, h} from "preact";
import "./icons.less";

// https://webpack.js.org/guides/dependency-management/#context-module-api
let cache = {};

function importAll (r) {
    r.keys().forEach(key => cache[key] = r(key));
}

importAll(require.context('./', true, /\.png$/));


export interface IconProps {
    name: string;
}

export class IconComponent extends Component<IconProps, any> {
    render(props: IconProps) {
        return (
            <img class="icon" src={cache[`./icons/original/${props.name}.png`]}/>
        );
    }
}

export interface VariantIconProps {
    row: number;
    variant: number;
}

export class LargeVariantIconComponent extends Component<VariantIconProps, any> {
    render(props: VariantIconProps) {
        return (
            <IconComponent name={`large/large-${(props.row + 10).toString(16)}${props.variant + 1}`}/>
        );
    }
}

export class SmallVariantIconComponent extends Component<VariantIconProps, any> {
    render(props: VariantIconProps) {
        return (
            <IconComponent name={`small/small-${(props.row + 10).toString(16)}${props.variant + 1}`}/>
        );
    }
}