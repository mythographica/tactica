import { createInCycle, pingA } from './cyc-a';

export function pingB (): unknown {
	pingA();
	const made = createInCycle();
	return made;
}
