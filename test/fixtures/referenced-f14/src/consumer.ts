import { define } from 'mnemonica';
import { PackFiles, PackMeta } from './models';

interface PackData {
	data?: Record<string, unknown>;
}

// the F14 field pattern: explicit this.x = param.y assignments from a
// NAMED alias/interface param (not an inline literal)
export const Pack = define('Pack', function (this: PackData, pageFiles: PackFiles, meta: PackMeta) {
	this.header = pageFiles.header;
	this.info = pageFiles.info;
	this.note = meta.note;
	this.weight = meta.weight;
	// unknown-bearing inference must not clobber the annotated optional field
	this.data = pageFiles.missing;
});
