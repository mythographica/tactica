import { define } from 'mnemonica';
import { SharedShape } from '../shape-a/models/shared-shape.model';

type SharedShape = {
	localOnly: string;
};

export const LocalShadow = define('LocalShadow', function (
	this: LocalShadow,
	record: SharedShape
) {
	this.record = record;
});
