import { lookup } from 'mnemonica';

// Two Tokens live in the graph (Holder.Token and Other.Token) and none at
// root: the runtime answers `undefined` for this lookup and the TypeError
// arrives at the `new` below — tactica must hard-fail instead
const TokenCtor = lookup('Token');
export const instance = new TokenCtor({ mark : 'x' });
