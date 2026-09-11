import { define } from 'mnemonica';
import { HolderDto, TaggedDto, ShapeDto, Crate, Bin, Silo } from './models';

export const Holder = define('Holder', function (this: Holder, data: HolderDto) {
	this.payload = data;
});
export const Tagged = define('Tagged', function (this: Tagged, data: TaggedDto) {
	this.payload = data;
});
export const Shaped = define('Shaped', function (this: Shaped, data: ShapeDto) {
	this.payload = data;
});
export const Crated = define('Crated', function (this: Crated, data: Crate) {
	this.payload = data;
});
export const Binned = define('Binned', function (this: Binned, data: Bin) {
	this.payload = data;
});
export const Siloed = define('Siloed', function (this: Siloed, data: Silo) {
	this.payload = data;
});
