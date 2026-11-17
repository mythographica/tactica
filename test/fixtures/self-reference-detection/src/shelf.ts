import { mnemonica } from 'mnemonica';
import type { TShelfArgs, TShelfInstance } from './shelf.types';

export const Shelf = mnemonica.define('Shelf', function (this: TShelfInstance, data: TShelfArgs) {
	this.label = data.label;
});
