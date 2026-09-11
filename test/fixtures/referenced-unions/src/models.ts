// F15/F16/F17 fixture: typeof const-array literal-union expansion edge
// cases. Synthetic identifiers only.

// as const form — the union must be emitted with NO [number] suffix (F15)
const statusList = [ 'active', 'not_active', 'hold' ] as const;
export const [ firstStatus ] = statusList;

// angle-bracket assertion form — same tracking as the `as const` form (F17)
const tierList = <const>[ 'low', 'high' ];
export const [ firstTier ] = tierList;

// unary-minus numeric literals stay signed in the union (F16)
const mixList = [ -1, 1 ] as const;
export const [ firstLevel ] = mixList;

// not statically visible: the whole indexed access degrades to `unknown`,
// never `unknown[number]` (F17 invariant)
const ghostList = buildGhostList();
export const [ firstGhost ] = ghostList;

export function buildGhostList (): string[] {
	return [ 'x' ];
}

export class Widget {
	status: typeof statusList[number];
	tier: typeof tierList[number];
	level: typeof mixList[number];
	ghost: typeof ghostList[number];
	// non-typeof unresolved targets must not carry a suffix either
	broken: MissingType[number];
	keyed: MissingType['key'];
}
