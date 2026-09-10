import { define } from 'mnemonica';

export const Parent = define('Parent', function (this: Parent) {
	this.kind = 'parent';
});

// the same parent declares Twin twice: another ALREADY_DECLARED case
// (same-parent same-child), both sites must be reported
Parent.define('Twin', function (this: Twin) {
	this.slot = 1;
});

Parent.define('Twin', function (this: Twin) {
	this.slot = 2;
});
