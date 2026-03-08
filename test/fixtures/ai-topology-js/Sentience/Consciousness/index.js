'use strict';

/**
 * Consciousness type handler - JavaScript version
 */

function ConsciousnessHandler (data) {
	Object.assign(this, data);
	this.level = data.level || 1;
	this.aware = true;
}

module.exports = { ConsciousnessHandler };
