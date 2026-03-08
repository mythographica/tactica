'use strict';

/**
 * Consciousness type handler - TypeScript version
 */

export function ConsciousnessHandler (
	this: { level?: number; aware?: boolean },
	data: { level?: number }
) {
	Object.assign(this, data);
	this.level = data.level || 1;
	this.aware = true;
}
