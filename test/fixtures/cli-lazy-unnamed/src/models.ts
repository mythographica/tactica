import { define } from 'mnemonica';

export const Parent = define('Parent', function (this: { id: string }) {
	this.id = '';
});

// the unnamed form: the runtime throws TYPENAME_MUST_BE_A_STRING here,
// so tactica warns and generates no type for it
export const Bad = Parent.lazy(() => class Bad {
	value: number = 1;
});

export const Good = Parent.lazy('Good', () => class Good {
	name: string = '';
});
