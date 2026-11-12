import { decorate } from 'mnemonica';

@decorate()
export class Robot {
	serial: string;
	constructor (serial: string) {
		this.serial = serial;
	}
}
