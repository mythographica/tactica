import { define } from 'mnemonica';
import { SharedShape } from './a';

// the duplicate declaration in b.ts does not matter: this file's own
// import anchors the name, so the reference resolves to a.ts and the
// run is not fatal
export const Crate = define('Crate', function (this: Crate, data: SharedShape) {
	this.item = data;
});
