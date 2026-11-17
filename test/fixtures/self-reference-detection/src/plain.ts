import { mnemonica } from 'mnemonica';

// no generated type anywhere: stays derived
type TPlainArgs = { size: number };
type TPlainInstance = TPlainArgs;

export const Plain = mnemonica.define('Plain', function (this: TPlainInstance, data: TPlainArgs) {
	this.size = data.size;
});
