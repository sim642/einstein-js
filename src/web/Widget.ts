export type $Element = JQuery<HTMLElement>;

export abstract class Widget {
    abstract render(): $Element;

    protected $: $Element;

    create(): $Element {
        return this.$ = this.render();
    }

    recreate(): $Element {
        let $new = this.render();
        this.$.replaceWith($new);
        return this.$ = $new;
    }
}