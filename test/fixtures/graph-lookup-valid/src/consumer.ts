import { lookup } from 'mnemonica';
import { Holder } from './defs';

// dotted absolute path and receiver-relative lookup both resolve — exit 0
const ByPath = lookup('Holder.Token');
const ByReceiver = Holder.lookup('Token');
export const a = new ByPath({ mark : 'x' });
export const b = new ByReceiver({ mark : 'y' });
