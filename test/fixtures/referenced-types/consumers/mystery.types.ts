import { define } from 'mnemonica';

export const Mystery = define('Mystery', function (
	this: Mystery,
	thing: NotImportedAnywhere
) {
	this.thing = thing;
});
