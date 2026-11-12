import { define } from 'mnemonica';
import type { User } from '../.tactica/types';

export const ParameterType = define('Parameter', function (this: { value: string }, owner: User) {
	this.value = owner.name;
});

export const Chained = ParameterType.define('Chained', function (
	this: { value: string; reason: string },
	data: { reason: string }
) {
	this.value = 'chained';
	this.reason = data.reason;
});
