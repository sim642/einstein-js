export interface TouchHandler {
    onTouchStart(e: TouchEvent): void;
    onTouchMove(e: TouchEvent): void;
    onTouchEnd(e: TouchEvent): void;
    onTouchCancel(e: TouchEvent): void;
}

export class LongTouchHandler implements TouchHandler {
    private timeout: number;

    constructor(public callback: () => void) {

    }

    // iOS long touch workaround
    // https://stackoverflow.com/a/33778163
    // https://jsfiddle.net/gianlucaguarini/56Szw/
    // https://stackoverflow.com/a/33303261

    onTouchStart = (e) => {
        console.debug("touchstart");
        this.timeout = setTimeout(() => {
            console.log("longtouch");
            this.callback();
        }, 500);
    };

    onTouchMove = (e) => {
        console.debug("touchmove");
        clearTimeout(this.timeout);
    };

    onTouchEnd = (e) => {
        console.debug("touchend");
        clearTimeout(this.timeout);
    };

    onTouchCancel = (e) => {
        console.debug("touchcancel");
        clearTimeout(this.timeout);
    };
}