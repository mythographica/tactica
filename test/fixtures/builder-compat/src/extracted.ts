import { define } from 'mnemonica';

define('InlineRest', function (this: { name: string; values: number[] }, data: { name: string }, ...values: number[]) {
	this.name = data.name;
	this.values = values;
});

define('InlineKlass', class {
	k: number;
	label = 'inline';
	constructor (k: number) {
		this.k = k;
	}
});

define('Bare');
