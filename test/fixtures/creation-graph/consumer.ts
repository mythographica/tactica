import { makeThing } from './barrel';

export function run (): unknown {
	const made = makeThing();
	return made;
}
