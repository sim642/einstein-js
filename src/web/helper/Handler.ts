export interface TouchHandler {
    onTouchStart(e: TouchEvent): void;
    onTouchMove(e: TouchEvent): void;
    onTouchEnd(e: TouchEvent): void;
    onTouchCancel(e: TouchEvent): void;
}

export interface ContextMenuHandler {
    onContextMenu(e: MouseEvent): void;
}

export type TouchContextMenuHandler = TouchHandler & ContextMenuHandler;