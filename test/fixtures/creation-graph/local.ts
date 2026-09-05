import { Thing } from './entities';

function buildLocal (): unknown {
	const local = new Thing();
	return local;
}

export function entry (): unknown {
	const built = buildLocal();
	return built;
}
