import { lookup } from 'mnemonica';

const T2 = lookup('Thing');

export function makeViaLookup (): unknown {
	const inst = new T2();
	return inst;
}
