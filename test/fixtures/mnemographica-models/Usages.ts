'use strict';

import { define } from 'mnemonica';

export type usage = {
	id: string;
	typeName: string;
	filePath: string;
	line: number;
	column: number;
	context: string
};

export type usageEntry = InstanceType<typeof UsageEntry>;

export const Usages = define('Usages', class {
	createdAt: number;
	private map: Map<string, object[]>;
	constructor() {
		this.createdAt = Date.now();
		this.map = new Map();
	}
	has (name: string) {
		return this.map.has(name);
	}
	set (name: string, entry: usageEntry[]) {
		this.map.set(name, entry);
	}
	values () {
		return this.map.values();
	}
	get size () {
		return this.map.size;
	}
});

const setProps = (to: object, from: object) => {
	Object.defineProperties(to, Object.getOwnPropertyDescriptors(from));
}

export const UsageEntry = Usages.define('UsageEntry', function (
	this: usage,
	data: usage
) {
	setProps(this, data);
});

export default Usages;
