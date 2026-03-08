'use strict';

/**
 * Memory type handler - TypeScript version
 */

export function MemoryHandler (
	this: { content?: string; timestamp?: number },
	data: { content?: string; timestamp?: number }
) {
	Object.assign(this, data);
	this.content = data.content || '';
	this.timestamp = data.timestamp || Date.now();
}
