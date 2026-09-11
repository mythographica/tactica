import { define } from 'mnemonica';

const TrunkRoot = define('TrunkRoot', function (this: TrunkRoot) {
	this.kind = 'root';
});

// F18: multi-hop initializer — Branch must bind the LAST hop
// (TrunkRoot.Limb.Joint), because define() returns the defined type's
// constructor; children of Branch land under Joint, one level BELOW
// where the old first-hop binding placed them
const Branch = TrunkRoot.define('Limb', function (this: Limb) {
	this.part = 'limb';
}).define('Joint', function (this: Joint) {
	this.part = 'joint';
});

// single-hop control — the const binds the only hop
const Solo = TrunkRoot.define('Solo', function (this: Solo) {
	this.part = 'solo';
});

Branch.define('Tip', function (this: Tip) {
	this.part = 'tip';
});
Solo.define('Cap', function (this: Cap) {
	this.part = 'cap';
});

// F19 law pin: the root's own arg fields must reach nested instance
// types through the ProtoFlat chain (direct child AND deeper levels)
export const PaymentRoot = define('PaymentRoot', function (this: PaymentRoot, data: { uuid: string }) {
	this.uuid = data.uuid;
});

PaymentRoot.define('GatheredContext', function (this: GatheredContext, data: { gathered: string }) {
	this.gathered = data.gathered;
});

PaymentRoot.lookup('GatheredContext').define('DeepLeaf', function (this: DeepLeaf, data: { leaf: string }) {
	this.leaf = data.leaf;
});
