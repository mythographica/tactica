import * as ns from 'mnemonica';

// A namespace import's `define` is the free define: a free chain
export const Gear = ns.define('Gear', function (this: { teeth: number }) {
	this.teeth = 12;
});
export const Cog = Gear.define('Cog', function (this: { pitch: number }) {
	this.pitch = 2;
});

// the builder object reached through the namespace stays a builder
export const Belt = ns.mnemonica.define('Belt', function (this: { length: number }) {
	this.length = 1;
});
