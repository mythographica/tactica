import { define } from 'mnemonica';
import * as holders from '../shape-a/nested/crate-holder';

export const InnerCrateUser = define('InnerCrateUser', function (
	this: InnerCrateUser,
	crate: holders.Inner.Crate
) {
	this.crate = crate;
});

export const OuterCrateUser = define('OuterCrateUser', function (
	this: OuterCrateUser,
	crate: holders.Outer.Crate
) {
	this.crate = crate;
});
