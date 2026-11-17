import { define, lookup } from 'mnemonica';

// Exported values on chains that start at the free define()/lookup(): each
// carries the global TypeRegistry, so none may enter the registry through
// RegistryOf (it would be TypeRegistry's own base)

// a free root, an exported subtype on it, and one more hop
export const Widget = define('Widget', function (this: { size: number }) {
	this.size = 1;
});
export const Part = Widget.define('Part', function (this: { label: string }, data: { label: string }) {
	this.label = data.label;
});
export const Bolt = Part.define('Bolt', function (this: { torque: number }) {
	this.torque = 3;
});

// an inline chain on the free define
export const Right = define('Left', function (this: { l: number }) {
	this.l = 1;
}).define('Right', function (this: { r: number }) {
	this.r = 2;
});

// a subtype defined on a free lookup
define('Frame', function (this: { f: number }) {
	this.f = 1;
});
export const Panel = lookup('Frame').define('Panel', function (this: { p: number }) {
	this.p = 1;
});
