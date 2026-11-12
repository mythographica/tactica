import { Sessions } from './app';
import type { User } from '../.tactica/types';

export const Notes = Sessions.lookup('User').define('Note', function (this: { text: string }, author: User) {
	this.text = author.name;
});

export const AsyncNotes = Notes.lookup('User').define('AsyncNote', async function (this: { text: string }, author: User) {
	this.text = author.name;
	return this;
});
