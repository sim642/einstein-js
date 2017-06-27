export type $Element = JQuery<HTMLElement>;

export abstract class Widget {
    abstract render(): $Element;

    protected $: $Element;

    create(): $Element {
        return this.$ = this.render();
    }

    create2(): HTMLElement {
        return this.create()[0];
    }

    recreate(): $Element {
        let $new = this.render();
        this.$.replaceWith($new);
        return this.$ = $new;
    }
}