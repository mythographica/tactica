import { lookup } from 'mnemonica';
import { ParameterType as BuilderParameter, Chained as BuilderChained } from './parameter-ref';
import { AsyncNotes } from './notes';
import type { InlineKlass, Bare, Parameter, Parameter_Chained, User, User_Note, User_AsyncNote } from '../.tactica/types';

type Mutual<A, B> = [ A ] extends [ B ] ? [ B ] extends [ A ] ? true : false : false;
type ChainedMember<T> = T extends { Chained: infer Member } ? Member : undefined;
type NoteMember<T> = T extends { Note: infer Member } ? Member : undefined;
type NotAConstructor<T> = T extends new (...args: never[]) => unknown ? false : true;

const TInlineRest = lookup('InlineRest');
const tInlineRest = new TInlineRest({ name : 'rest' }, 1, 2, 3);
const TInlineKlass = lookup('InlineKlass');
const tInlineKlass = new TInlineKlass(1);
const TBare = lookup('Bare');
const tBare = new TBare(1, 'two');
const TUser = lookup('User');
const tUser = new TUser({ name : 'owner' }, 'a', 'b');
const TParameter = lookup('Parameter');
const tParameter = new TParameter(tUser);
const TChained = lookup('Parameter.Chained');
const tChained = new TChained({ reason : 'transitive' });
declare const builderChained: InstanceType<typeof BuilderChained>;
const BuilderUserWithNotes = AsyncNotes.lookup('User');
const builderUserWithNote = new BuilderUserWithNotes({ name : 'note owner' }, 'a', 'b');
const builderNote = new builderUserWithNote.Note(tUser);
const tNote = new tUser.Note(tUser);
const builderAsyncNote = new builderUserWithNote.AsyncNote(tUser);
const tAsyncNote = new tUser.AsyncNote(tUser);

export const inlineRestArgs: Mutual<ConstructorParameters<typeof TInlineRest>, [data: { name: string }, ...values: number[]]> = true;
export const inlineRestName: string = tInlineRest.name;
export const inlineRestValues: number[] = tInlineRest.values;
export const inlineKlassInstance: Mutual<typeof tInlineKlass, InlineKlass> = true;
export const tacticaInlineKlassLabel: string = tInlineKlass.label;
export const bareInstance: Mutual<typeof tBare, Bare> = true;
export const parameterInstance: Mutual<typeof tParameter, Parameter> = true;
export const chainedInstance: Mutual<typeof tChained, Parameter_Chained> = true;
export const chainedReason: string = tChained.reason;
export const chainedParentValue: string = tChained.value;

export const parameterToBuilder: InstanceType<typeof BuilderParameter> = tParameter;
export const chainedToTactica: Parameter_Chained = builderChained;
export const chainedToBuilder: typeof builderChained = tChained;
export const tacticaChainedIsNotConstructor: NotAConstructor<ChainedMember<Parameter_Chained>> = true;
export const builderChainedIsNotConstructor: NotAConstructor<ChainedMember<typeof builderChained>> = true;

export const noteParentToTactica: User = builderUserWithNote;
export const noteParentToBuilder: typeof builderUserWithNote = tUser;
export const noteToTactica: User_Note = builderNote;
export const noteToBuilder: typeof builderNote = tNote;
export const tacticaNoteIsNotConstructor: NotAConstructor<NoteMember<User_Note>> = true;
export const builderNoteIsNotConstructor: NotAConstructor<NoteMember<typeof builderNote>> = true;

export const asyncNoteParentToTactica: User = builderUserWithNote;
export const asyncNoteParentToBuilder: typeof builderUserWithNote = tUser;
export const asyncNotePendingToTactica: Promise<User_AsyncNote> = builderAsyncNote;
export const asyncNotePendingToBuilder: typeof builderAsyncNote = tAsyncNote;
const crossAsyncNotes = async () => {
	const builder = await builderAsyncNote;
	const tactica = await tAsyncNote;
	const toTactica: User_AsyncNote = builder;
	const toBuilder: typeof builder = tactica;
	return [ toTactica, toBuilder ];
};
export const asyncNoteCrossing = crossAsyncNotes();

export const parameterHook = TParameter.registerHook('postCreation', (opts) => {
	const { value } = opts.inheritedInstance;
	void value;
});

void tBare;
void tParameter;
