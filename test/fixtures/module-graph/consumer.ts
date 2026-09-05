import { makeThing, Thing, RenamedShape } from './barrel';
import DefaultWidget from './classmod';
import * as defs from './defs';

export function runConsumer (): string {
	const widget = new DefaultWidget();
	const thing: RenamedShape = new Thing();
	return makeThing() + defs.thingValue + widget.size + thing.name;
}
