import { define } from 'mnemonica';
import { SharedShape } from '../shape-a/models/shared-shape.model';

export const PrimaryType = define('PrimaryType', function (
	this: PrimaryType,
	record: SharedShape
) {
	this.record = record;
});
