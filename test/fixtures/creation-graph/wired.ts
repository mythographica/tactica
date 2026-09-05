import { Thing } from './entities';

export class WiredMaker {
	make (): unknown {
		const made = new Thing();
		return made;
	}
}

// Framework-style registration: the class is handed over as a VALUE —
// the module scope references it, nobody "calls" the module itself
export const registry = [ WiredMaker ];
