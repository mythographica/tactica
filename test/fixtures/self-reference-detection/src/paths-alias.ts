import { define } from 'mnemonica';
// the generated type through a tsconfig `paths` alias; .tactica is not
// written yet, as on a fresh clone
import type { Courier as TGeneratedCourier } from '~tactica/types';

type TCourierArgs = { maxAttempts: number; baseMs: number };

export const Courier = define('Courier', function (
	this: TGeneratedCourier & TCourierArgs,
	data: TCourierArgs
) {
	this.maxAttempts = data.maxAttempts;
	this.baseMs = data.baseMs;
});

// a subtype of a self-referencing root stays extracted with it
export const Attempt = Courier.define('Attempt', function (this: { reason: string }, reason: string) {
	this.reason = reason;
});
