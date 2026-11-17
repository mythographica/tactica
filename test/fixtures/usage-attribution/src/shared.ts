import type { AnyGadget } from './gadget-types';

// Shared by both flows: the parent arrives as a parameter typed through
// an alias declared in another file
export const makeFault = function (gadget: AnyGadget) {
	const fault = new gadget.Fault();
	return fault;
};
