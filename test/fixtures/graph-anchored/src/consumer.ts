import { define } from 'mnemonica';
import { Token } from './defs';

// Crate is a root: its parent chain and the root tier say nothing about
// `Token` — only this file's import anchors the reference to Holder.Token
export const Crate = define('Crate', function (this: Crate, data: Token) {
	this.item = data;
});
