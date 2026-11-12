// the alias over the generated type lives in its own file, reached
// through the `paths` alias; the instance interface names it only
// through its `extends` clause
import type { Shelf as TGeneratedShelf } from '~tactica/types';

export type TShelfArgs = { label: string };

type TShelfBase = TShelfArgs & TGeneratedShelf;

export interface TShelfInstance extends TShelfBase {
	label: string;
}
