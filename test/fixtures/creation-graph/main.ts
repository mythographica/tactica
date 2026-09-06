import { run } from './consumer';
import { entry } from './local';
import { pingB } from './cyc-b';
import { makeViaLookup } from './lookup-alias';
import { reassignThing } from './service';
import * as svc from './service';
import { registry } from './wired';

run();
entry();
pingB();
makeViaLookup();
reassignThing();

const viaNamespace = (): unknown => {
	const made = svc.reassignThing();
	return made;
};

viaNamespace();

// Used the way a framework bootstrap receives the root module: the
// registration object crosses the module boundary as a VALUE, not a call
void registry;
