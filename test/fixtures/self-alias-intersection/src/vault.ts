import { define } from 'mnemonica';
import type { TVaultGeneratedInstance } from './generated-standin';

// the field's recommended root pattern (F21): the root ctor's `this` is
// an INTERSECTION alias over the generated root type
type TEntryArgs = { code: string; amount: number };
type TVaultInstance = TEntryArgs & TVaultGeneratedInstance;

export const VaultRoot = define('VaultRoot', function (this: TVaultInstance, args: TEntryArgs) {
	Object.assign(this, args);
});

// a child branching DIRECTLY off the intersection-alias-annotated root
// must statically see the root's arg fields (runtime has them via the
// prototype chain)
export const FailedUnlock = VaultRoot.define('FailedUnlock', function (this: FailedUnlock, reason: string) {
	this.reason = reason;
});
