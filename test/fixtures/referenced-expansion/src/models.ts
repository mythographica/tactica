// F13 fixture models: classes with heritage, interface chains, and
// typeof-const field types. Synthetic identifiers only.

export class HolderBase {
	baseField: string;
}

export class HolderDto extends HolderBase {
	ownField: number;
}

// child shadowing: the derived declaration overrides the base field
export class TaggedBase {
	tag: string;
}
export class TaggedDto extends TaggedBase {
	tag: number;
}

// interface heritage chain
export interface ShapeBase {
	baseProp: string;
}
export interface ShapeDto extends ShapeBase {
	ownProp: number;
}

// module-level NON-exported const + a field typed by a typeof query:
// the literal union must be emitted, never a bare `typeof statusList`
const statusList = [ 'active', 'closed' ] as const;

export class Crate {
	item: string;
	status?: typeof statusList[number];
}

// value use so the const is not type-only (lint) — the analyzer tracks
// the array literal itself for the typeof expansion above
export const [ firstStatus ] = statusList;

// non-literal typeof source: elements are not statically visible
export function makeCode (): string {
	return 'x';
}
const dynamicList = [ makeCode() ];

export class Bin {
	state?: typeof dynamicList[number];
}

export const [ firstDynamic ] = dynamicList;

// non-array typeof source
const configObject = { mode : 'manual' };

export class Silo {
	settings?: typeof configObject;
}

export const currentMode = configObject.mode;
