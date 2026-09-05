import { Thing } from './entities';
import { pingB } from './cyc-b';

export function createInCycle (): unknown {
	const made = new Thing();
	return made;
}

export function pingA (): unknown {
	const pong = pingB();
	return pong;
}
