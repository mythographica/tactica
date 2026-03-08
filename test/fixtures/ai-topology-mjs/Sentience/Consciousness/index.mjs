/**
 * Consciousness type handler - ESM version
 */

export function ConsciousnessHandler (data) {
	Object.assign(this, data);
	this.level = data.level || 1;
	this.aware = true;
}
