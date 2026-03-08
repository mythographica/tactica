'use strict';

/**
 * Sentience type handler - JavaScript version
 */

function SentienceHandler (data) {
	Object.assign(this, data);
	this.purpose = data.purpose || 'AI Sentience';
}

module.exports = { SentienceHandler };
