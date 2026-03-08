'use strict';

/**
 * Curiosity type handler - TypeScript version
 */

export function CuriosityHandler (
	this: { topic?: string; active?: boolean },
	data: { topic?: string }
) {
	Object.assign(this, data);
	this.topic = data.topic || 'general';
	this.active = true;
}
