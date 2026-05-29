'use strict';

export const ArrowTypeHandler = function (
	this: Record<string, unknown>,
	data: { label: string; value: number }
) {
	Object.assign(this, data);
	this.computed = data.value * 2;
};
