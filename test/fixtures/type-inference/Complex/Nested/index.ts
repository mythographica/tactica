'use strict';

export function NestedHandler (
	this: Record<string, unknown>,
	data: { id: number; label: string; active?: boolean }
) {
	Object.assign(this, data);
	Object.assign(this, { extra: 'literal', count: 42 });
	const ctx = {};
	Object.assign(ctx, { x: 1 });
	Array.isArray([]);
	this.conditional = data.active ? 'yes' : 'no';
	this.ored = data.label || 'default';
}
