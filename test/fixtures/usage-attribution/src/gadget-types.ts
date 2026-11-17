// The union of the two generated Gadget types, one imported under a
// local name
import type { Alpha_Gadget, Beta_Gadget as SecondGadget } from '../.tactica/types';

export type AnyGadget = Alpha_Gadget | SecondGadget;
