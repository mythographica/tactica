import { mnemonica } from 'mnemonica';

export interface UserShape { name: string; tags: string[] }
export interface AdminShape { role: 'root' | 'ops'; level: number }
export interface SessionShape { token: string }

export const App = mnemonica
	.define('User', function (this: UserShape, data: { name: string }, ...tags: string[]) {
		this.name = data.name;
		this.tags = tags;
	})
	.define('Admin', function (this: AdminShape, data: { role: 'root' | 'ops' }, level?: number) {
		this.role = data.role;
		this.level = level ?? 0;
	});

export const Sessions = App.lookup('User').define('Session', async function (this: SessionShape, token: string) {
	this.token = token;
	return this;
});

export const Klass = mnemonica.define('Klass', class {
	k: number;
	label = 'klass';
	constructor (k: number) {
		this.k = k;
	}
});
