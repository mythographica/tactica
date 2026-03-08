/**
 * Sentience type handler - ESM version
 */

export function SentienceHandler (data) {
	Object.assign(this, data);
	this.purpose = data.purpose || 'AI Sentience';
}
