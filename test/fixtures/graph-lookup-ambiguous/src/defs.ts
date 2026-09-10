import { define } from 'mnemonica';

export const Holder = define('Holder', function (this: Holder) {
	this.kind = 'holder';
});

// exported binding: `Token` denotes Holder.Token for every importer
export const Token = Holder.define('Token', function (this: Token, data: { mark: string }) {
	this.mark = data.mark;
});
