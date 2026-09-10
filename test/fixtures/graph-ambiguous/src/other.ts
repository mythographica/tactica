import { define } from 'mnemonica';

export const Other = define('Other', function (this: Other) {
	this.kind = 'other';
});

// a second Token elsewhere in the graph: bare references to `Token` are
// ambiguous unless a file's own import anchors them
Other.define('Token', function (this: Token, data: { hue: string }) {
	this.hue = data.hue;
});
