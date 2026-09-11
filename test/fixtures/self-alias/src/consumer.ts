import { define } from 'mnemonica';
import type { TWidgetInstance } from './widget-instance';

// the self-referencing root ctor annotation (field-recommended pattern):
// the handler's `this` is annotated with the generated instance alias, so
// `new Widget(args)` is directly assignable to the instance type at call
// sites — zero casts. Tactica must tolerate the self-reference: the
// annotation drives property extraction only and never lands in the
// emitted type, so no circularity can form.
export const Widget = define('Widget', function (this: TWidgetInstance, data: { label: string; size: number }) {
	this.label = data.label;
	this.size = data.size;
});
