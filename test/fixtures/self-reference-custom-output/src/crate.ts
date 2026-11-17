import { mnemonica } from 'mnemonica';
// generated with --output ./generated: no `.tactica` in the specifier
import type { Crate as TGeneratedCrate } from '../generated/types';

type TCrateArgs = { size: number };

export const Crate = mnemonica.define('Crate', function (this: TGeneratedCrate & TCrateArgs, data: TCrateArgs) {
	this.size = data.size;
});
