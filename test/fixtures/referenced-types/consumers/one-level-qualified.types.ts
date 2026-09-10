import { define } from 'mnemonica';
import * as models from '../shape-a/models/shared-shape.model';

export const QualifiedUser = define('QualifiedUser', function (
	this: QualifiedUser,
	record: models.SharedShape
) {
	this.record = record;
});
