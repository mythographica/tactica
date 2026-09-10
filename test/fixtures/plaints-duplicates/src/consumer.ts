import { define } from 'mnemonica';

// SharedShape is declared in both a.ts and b.ts and this file imports
// neither — the reference is ambiguous and tactica must hard-fail with
// every declaration site printed
export const Crate = define('Crate', function (this: Crate, data: SharedShape) {
	this.item = data;
});
