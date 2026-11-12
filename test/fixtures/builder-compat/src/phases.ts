import { createTypesCollection } from 'mnemonica';

const Data = {
	Prepare : { step : 1 },
	Produce : { step : 2 },
};

type PhaseName = keyof typeof Data;

const holder = <D extends object>() => {
	const handler = function (this: D, data: D) {
		Object.assign(this, data);
	};
	return handler;
};

export const collection = createTypesCollection();
export const Run = collection.define('Run', holder<{ id: string }>());

const definePhase = (name: PhaseName) => {
	const result = Run.define(name, holder<typeof Data[typeof name]>());
	return result;
};

export const Phase = new Map<PhaseName, ReturnType<typeof definePhase>>();
const isPhaseName = (key: string): key is PhaseName => {
	const result = Object.prototype.hasOwnProperty.call(Data, key);
	return result;
};

for (const key of Object.keys(Data)) {
	if (isPhaseName(key)) {
		Phase.set(key, definePhase(key));
	}
}
