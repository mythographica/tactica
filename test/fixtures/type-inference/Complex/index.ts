'use strict';

export type ComplexData = {
	label: string;
	count: number;
	active: boolean;
};

export function ComplexHandler (
	this: Record<string, unknown>,
	data: ComplexData,
	tag: string,
	score: number,
	enabled: boolean,
	items: string[],
	_options: { ref: LocalClass; flag: any; mode: string | number },
	_classInstance: LocalClass
) {
	Object.assign(this, data);
	this.tag = tag;
	this.score = score;
	this.enabled = enabled;
	this.items = items;
	this.createdAt = new Date();
	this.mapData = new Map();
	this.setData = new Set();
	this.regexp = new RegExp('test');
	this.arrData = new Array();
	this.timestamp = Date.now();
	this.parsed = parseInt('42');
	this.parsed2 = parseFloat('3.14');
	this.str = String(score);
	this.num = Number(tag);
	this.flag = Boolean(score);
	this.nullProp = null;
	this.undefinedProp = undefined;
	this.arrLiteral = [];
	this.objLiteral = {};
	this.sum = score + 1;
	this.instance = new LocalClass();
	this.callResult = customFunc(score);
	this.floorVal = Math.floor(score);
}

class LocalClass {}
function customFunc (_n: number) { return 'x'; }
