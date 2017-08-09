import {Component, h} from "preact";
import "./birthday.less";

export interface BirthdayProps {
    month: number;
    day: number;
    name: string;
}

export class BirthdayComponent extends Component<BirthdayProps, any> {
    render(props: BirthdayProps) {
        let now = new Date();
        if (now.getMonth() + 1 == props.month && now.getDate() == props.day) { // JS month is 0-indexed, date is 1-indexed
            return (
                <div class="birthday">
                    <p>
                        Happy birthday, {props.name}!
                    </p>
                </div>
            );
        }
        else
            return null;
    }
}