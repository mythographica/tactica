// F14 fixture models: the referenced declarations behind the named
// constructor params. Synthetic identifiers only.

export interface PackHeader {
	title: string;
}

export interface PackFiles {
	header: PackHeader | null;
	info: Record<string, unknown>;
}

export type PackMeta = {
	note: string;
	weight: number;
};
