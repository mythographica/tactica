import { define } from 'mnemonica';

// a second DupRoot in the same (default) namespace: the mnemonica runtime
// rejects this with ALREADY_DECLARED — tactica must hard-fail and report
// both definition sites
export const Second = define('DupRoot', function (this: DupRoot) {
	this.from = 'b';
});
