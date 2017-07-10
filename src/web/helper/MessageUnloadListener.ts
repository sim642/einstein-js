import {Listener} from "./Listener";

export class MessageUnloadListener implements Listener {
    constructor(public callback: () => string | null) {

    }

    private onBeforeUnload = (e) => {
        let message = this.callback();
        if (message !== null)
            return e.returnValue = message;
        else
            return undefined;
    };

    add(): void {
        window.addEventListener("beforeunload", this.onBeforeUnload);
    }

    remove(): void {
        window.removeEventListener("beforeunload", this.onBeforeUnload);
    }
}