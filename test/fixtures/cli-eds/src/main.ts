import { define } from 'mnemonica';
import { wrap } from '@mnemonica/dive';

export const Widget = define('Widget', function (this: { id: string }, data: { id: string }) {
	this.id = data.id;
});

export function makeWrapped (): () => string {
	const widget = new Widget({ id : 'w1' });
	const wrapped = wrap(() => {
		const result = widget.id;
		return result;
	}, widget, 'demo:wrap');
	return wrapped;
}
