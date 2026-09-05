export function makeThing (): string {
	return 'thing';
}

export class Thing {
	name = 'thing';
}

export const thingValue = 42;

export interface ThingShape {
	name: string;
}

export type ThingId = string;
