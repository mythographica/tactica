import { define } from 'mnemonica';
import { SharedShape as SharedShapeAlias } from '../shape-a/models/shared-shape.model';

export const AliasedType = define('AliasedType', function (
	this: AliasedType,
	record: SharedShapeAlias
) {
	this.record = record;
});
