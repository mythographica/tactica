'use strict';

import { define } from 'mnemonica';

export const Types = define('Types', function (this: { createdAt: number }) {
	this.createdAt = Date.now();
});

export const TypeEntry = Types.define('TypeEntry', function (
	this: { id: string; name: string; fullPath: string; parent?: string; properties: Map<string, string> },
	data: { id: string; name: string; fullPath: string; parent?: string; properties: Map<string, string> }
) {
	this.id = data.id;
	this.name = data.name;
	this.fullPath = data.fullPath;
	this.parent = data.parent;
	this.properties = data.properties;
});

export default Types;
