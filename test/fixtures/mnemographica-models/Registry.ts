'use strict';

import { define } from 'mnemonica';

export const Registry = define('Registry', function (this: { createdAt: number }) {
	this.createdAt = Date.now();
});

export const DefinitionEntry = Registry.define('DefinitionEntry', function (
	this: { id: string; name: string; filePath: string; line: number; column: number },
	data: { id: string; name: string; filePath: string; line: number; column: number }
) {
	this.id = data.id;
	this.name = data.name;
	this.filePath = data.filePath;
	this.line = data.line;
	this.column = data.column;
});

export default Registry;
