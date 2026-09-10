import { define } from 'mnemonica';
import * as barrel from '../shape-a/nested/gadget-barrel';

export const GadgetUser = define('GadgetUser', function (
	this: GadgetUser,
	gadget: barrel.Deep.Gadget
) {
	this.gadget = gadget;
});
