import { define } from 'mnemonica';
import type { TShelfArgs, TShelfInstance } from './shelf.types';

export const Shelf = define('Shelf', function (this: TShelfInstance, data: TShelfArgs) {
	this.label = data.label;
});
