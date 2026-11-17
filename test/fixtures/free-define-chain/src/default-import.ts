import mn from 'mnemonica';

// mnemonica has no default export: a default import is the module
// itself, and its `define` is the free define
export const Lever = mn.define('Lever', function (this: { force: number }) {
	this.force = 3;
});
export const Arm = Lever.define('Arm', function (this: { span: number }) {
	this.span = 4;
});
