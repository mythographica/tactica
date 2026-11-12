import { define } from 'mnemonica';
import type { Mirror } from '../.tactica/types';

export const MirrorType = define('Mirror', function (this: Mirror, data: { m: number }) {
	Object.assign(this, data);
});
