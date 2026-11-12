import { define } from 'mnemonica';
// generated with --output ./generated: no `.tactica` in the specifier
import type { Crate as TGeneratedCrate } from '../generated/types';

type TCrateArgs = { size: number };

export const Crate = define('Crate', function (this: TGeneratedCrate & TCrateArgs, data: TCrateArgs) {
	this.size = data.size;
});
