export function setClass(o, cls) {
    Object.setPrototypeOf(o, cls.prototype);
}