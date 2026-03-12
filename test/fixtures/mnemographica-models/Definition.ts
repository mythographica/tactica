'use strict';

import { define } from 'mnemonica';

export const Definition = define('Definition', function (
	this: { id: string; name: string; fullPath: string; properties: Map<string, { type: string; optional?: boolean }> },
	data: { id: string; name: string; fullPath: string; properties: Map<string, { type: string; optional?: boolean }> }
) {
	this.id = data.id;
	this.name = data.name;
	this.fullPath = data.fullPath;
	this.properties = data.properties;
});

export const Link = Definition.define('Link', function (
	this: { source: unknown; target: unknown; relation: 'extends' | 'implements' | 'contains' },
	data: { source: unknown; target: unknown; relation: 'extends' | 'implements' | 'contains' }
) {
	this.source = data.source;
	this.target = data.target;
	this.relation = data.relation;
});

export default Definition;
