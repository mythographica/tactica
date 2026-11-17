import { mnemonica } from 'mnemonica';
import type { Ledger as TGeneratedLedger } from '../.tactica/types';

type TLedgerArgs = { code: string; amount: number };

// the generated type is reached only through this local alias
export type TLedgerInstance = {
	code: string;
	amount: number;
} & TGeneratedLedger;

export const Ledger = mnemonica.define('Ledger', function (this: TLedgerInstance, data: TLedgerArgs) {
	this.code = data.code;
	this.amount = data.amount;
});
