export namespace Inner {
	export interface Crate {
		slot: number;
		tag: string;
	}
}

export namespace Outer {
	export interface Crate {
		bay: string;
		level: number;
	}
}
