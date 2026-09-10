import { define } from 'mnemonica';

// Crate is a root: its parent chain and the root tier say nothing about
// `Token`, and this file imports nothing. Two Tokens live in the graph
// (Holder.Token and Other.Token), so the bare reference is ambiguous and
// tactica must hard-fail with every location printed
export const Crate = define('Crate', function (this: Crate, data: Token) {
	this.item = data;
});
