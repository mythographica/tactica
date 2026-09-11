import { define } from 'mnemonica';
import { Widget } from './models';

export const WidgetPack = define('WidgetPack', function (this: WidgetPack, data: Widget) {
	this.unit = data;
});
