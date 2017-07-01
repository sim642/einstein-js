import {TouchContextMenuHandler} from "./Handler";

export class LongTouchContextMenuHandler implements TouchContextMenuHandler {
    private timeout: number;

    private static touching: boolean = false;
    private static readonly longTouchTime = 500;

    constructor(public callback: () => void) {

    }

    // iOS long touch workaround
    // https://stackoverflow.com/a/33778163
    // https://jsfiddle.net/gianlucaguarini/56Szw/
    // https://stackoverflow.com/a/33303261

    onTouchStart = (e) => {
        // console.debug("touchstart");
        LongTouchContextMenuHandler.touching = true;
        this.timeout = setTimeout(() => {
            console.log("longtouch");
            this.callback();
        }, LongTouchContextMenuHandler.longTouchTime);
    };

    onTouchMove = (e) => {
        // console.debug("touchmove");
        clearTimeout(this.timeout);
    };

    onTouchEnd = (e) => {
        // console.debug("touchend");
        LongTouchContextMenuHandler.touching = false;
        clearTimeout(this.timeout);
    };

    onTouchCancel = (e) => {
        // console.debug("touchcancel");
        LongTouchContextMenuHandler.touching = false;
        clearTimeout(this.timeout);
    };

    onContextMenu = (e) => {
        e.preventDefault();
        if (!LongTouchContextMenuHandler.touching) // prevent double-triggering if context menu opens after long touch
            this.callback();
    };
}