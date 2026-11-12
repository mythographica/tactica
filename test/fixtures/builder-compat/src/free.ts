import { define } from 'mnemonica';

export interface WidgetShape { w: number; meta: { deep: { x: number } } }
export interface GadgetShape { g: string }

export const Widget = define('Widget', function (this: WidgetShape, data: { w: number; meta: { deep: { x: number } } }) {
	this.w = data.w;
	this.meta = data.meta;
});

define('Gadget', function (this: GadgetShape, g: string) {
	this.g = g;
});
