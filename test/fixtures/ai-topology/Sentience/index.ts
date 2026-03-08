'use strict';

/**
 * Sentience type handler - TypeScript version
 */

export function SentienceHandler (this: { purpose?: string }, data: { purpose?: string }) {
	Object.assign(this, data);
	this.purpose = data.purpose || 'AI Sentience';
}
