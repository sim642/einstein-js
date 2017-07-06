import {Listener} from "./Listener";

declare global {
    interface Document {
        readonly mozHidden: boolean;
        readonly webkitHidden: boolean;
        readonly msHidden: boolean;
        onfocusin;
        onfocusout;
    }
}

export class VisibilityChangeListener implements Listener {
    private visible: boolean = true;

    constructor(public callback: (visible: boolean) => void) {

    }

    private focused = () => {
        // console.debug(`focused ${document.visibilityState}`);
        if (!this.visible)
            this.callback(this.visible = true);
    };

    private unfocused = () => {
        // console.debug(`unfocused ${document.visibilityState}`);
        if (this.visible)
            this.callback(this.visible = false);
    };

    add(): void {
        // https://stackoverflow.com/a/38710376

        // Standards:
        if ('hidden' in document) {
            document.addEventListener('visibilitychange',
                () => {(document.hidden ? this.unfocused : this.focused)()});
        }
        if ('mozHidden' in document) {
            document.addEventListener('mozvisibilitychange',
                () => {(document.mozHidden ? this.unfocused : this.focused)()});
        }
        if ('webkitHidden' in document) {
            document.addEventListener('webkitvisibilitychange',
                () => {(document.webkitHidden ? this.unfocused : this.focused)()});
        }
        if ('msHidden' in document) {
            document.addEventListener('msvisibilitychange',
                () => {(document.msHidden ? this.unfocused : this.focused)()});
        }
        // IE 9 and lower:
        if ('onfocusin' in document) {
            document.onfocusin = this.focused;
            document.onfocusout = this.unfocused;
        }
        // All others:
        window.onpageshow = window.onfocus = this.focused;
        window.onpagehide = window.onblur = this.unfocused;

        // TODO: initial visibility check like https://stackoverflow.com/a/1060034
    }

    remove(): void {
        // TODO: remove listeners
    }
}