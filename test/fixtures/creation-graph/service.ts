import { Thing } from './entities';

export function makeThing (): unknown {
	const thing = new Thing();
	return thing;
}

export function reassignThing (): unknown {
	let current = new Thing();
	current = null;
	return current;
}
