import { define } from 'mnemonica';

// Two flows with the same subtree shape: each Gadget has its own Fault
export const Alpha = define('Alpha', function (this: { a: number }) { this.a = 1; });
const AlphaGadget = Alpha.define('Gadget', function (this: { g: number }) { this.g = 1; });
AlphaGadget.define('Fault', function (this: { f: number }) { this.f = 1; });

export const Beta = define('Beta', function (this: { b: number }) { this.b = 2; });
const BetaGadget = Beta.define('Gadget', function (this: { g: number }) { this.g = 2; });
BetaGadget.define('Fault', function (this: { f: number }) { this.f = 2; });
