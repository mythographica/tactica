import { lookup } from 'mnemonica';
import { Klass as BuilderKlass } from './app';
import { AsyncNotes } from './notes';
import { Widget as BuilderWidget, type GadgetShape } from './free';
import { Robot as BuilderRobot } from './decorated';
import { MirrorType as BuilderMirror } from './selfref';
import type {
	User,
	User_Admin,
	User_Session,
	Klass,
	Widget,
	Gadget,
	Robot,
	Mirror,
} from '../.tactica/types';

type Mutual<A, B> = [ A ] extends [ B ] ? [ B ] extends [ A ] ? true : false : false;
type GadgetExpectedConstructor = new (g: string) => GadgetShape;

// Constructors through the builder and through tactica's registry.
const BUser = AsyncNotes.lookup('User');
const bUser = new BUser({ name : 'Ada' }, 'a', 'b');
const bAdmin = new bUser.Admin({ role : 'root' }, 2);
const bSession = new bUser.Session('t');
const bKlass = new BuilderKlass(1);
const bWidget = new BuilderWidget({ w : 1, meta : { deep : { x : 1 } } });
const bRobot = new BuilderRobot('r');
const bMirror = new BuilderMirror({ m : 1 });

const TUser = lookup('User');
const tUser = new TUser({ name : 'Ada' }, 'a', 'b');
const tAdmin = new tUser.Admin({ role : 'root' }, 2);
const tSession = new tUser.Session('t');
const TKlass = lookup('Klass');
const tKlass = new TKlass(1);
const TWidget = lookup('Widget');
const tWidget = new TWidget({ w : 1, meta : { deep : { x : 1 } } });
const TGadget = lookup('Gadget');
const tGadget = new TGadget('g');
const TRobot = lookup('Robot');
const tRobot = new TRobot('r');
const TMirror = lookup('Mirror');
const tMirror = new TMirror({ m : 1 });

// Constructor parameters.
export const userArgs: Mutual<ConstructorParameters<typeof BUser>, ConstructorParameters<typeof TUser>> = true;
export const adminArgs: Mutual<ConstructorParameters<typeof bUser.Admin>, ConstructorParameters<typeof tUser.Admin>> = true;
export const sessionArgs: Mutual<ConstructorParameters<typeof bUser.Session>, ConstructorParameters<typeof tUser.Session>> = true;
export const klassArgs: Mutual<ConstructorParameters<typeof BuilderKlass>, ConstructorParameters<typeof TKlass>> = true;
export const widgetArgs: Mutual<ConstructorParameters<typeof BuilderWidget>, ConstructorParameters<typeof TWidget>> = true;
export const gadgetArgs: Mutual<ConstructorParameters<GadgetExpectedConstructor>, ConstructorParameters<typeof TGadget>> = true;
export const robotArgs: Mutual<ConstructorParameters<typeof BuilderRobot>, ConstructorParameters<typeof TRobot>> = true;
export const mirrorArgs: Mutual<ConstructorParameters<typeof BuilderMirror>, ConstructorParameters<typeof TMirror>> = true;

// Instance types and async results.
export const userInstance: Mutual<typeof bUser, User> = true;
export const adminInstance: Mutual<typeof bAdmin, User_Admin> = true;
export const sessionResult: Mutual<typeof bSession, Promise<User_Session>> = true;
export const klassInstance: Mutual<typeof bKlass, Klass> = true;
export const widgetInstance: Mutual<typeof bWidget, Widget> = true;
export const gadgetInstance: Mutual<GadgetShape, Gadget> = true;
export const robotInstance: Mutual<BuilderRobot, Robot> = true;
export const mirrorInstance: Mutual<typeof bMirror, Mirror> = true;

// Instances passed across in both directions.
export const userToTactica: User = bUser;
export const userToBuilder: typeof bUser = tUser;
export const adminToTactica: User_Admin = bAdmin;
export const adminToBuilder: typeof bAdmin = tAdmin;
export const sessionToTactica: Promise<User_Session> = bSession;
export const sessionToBuilder: typeof bSession = tSession;
export const klassToTactica: Klass = bKlass;
export const klassToBuilder: typeof bKlass = tKlass;
export const widgetToTactica: Widget = bWidget;
export const widgetToBuilder: typeof bWidget = tWidget;
export const gadgetToTactica: Gadget = { g : 'expected' };
export const gadgetToBuilder: GadgetShape = tGadget;
export const robotToTactica: Robot = bRobot;
export const robotToBuilder: BuilderRobot = tRobot;
export const mirrorToTactica: Mirror = bMirror;
export const mirrorToBuilder: typeof bMirror = tMirror;

// Subtypes from instances and inherited fields.
export const builderSubtypeRole: 'root' | 'ops' = bAdmin.role;
export const tacticaSubtypeRole: 'root' | 'ops' = tAdmin.role;
export const builderSubtypeParentName: string = bAdmin.name;
export const tacticaSubtypeParentName: string = tAdmin.name;
const readBuilderToken = async () => {
	const session = await bSession;
	const result = session.token;
	return result;
};
const readTacticaToken = async () => {
	const session = await tSession;
	const result = session.token;
	return result;
};
export const builderAsyncToken: Promise<string> = readBuilderToken();
export const tacticaAsyncToken: Promise<string> = readTacticaToken();

// Extracted field details.
export const builderKlassLabel: string = bKlass.label;
export const tacticaKlassLabel: string = tKlass.label;
export const builderWidgetDeep: number = bWidget.meta.deep.x;
export const tacticaWidgetDeep: number = tWidget.meta.deep.x;
export const tacticaGadgetField: string = tGadget.g;
export const builderRobotSerial: string = bRobot.serial;
export const tacticaRobotSerial: string = tRobot.serial;
export const builderMirrorField: number = bMirror.m;
export const tacticaMirrorField: number = tMirror.m;

// Hooks on derived and plain-signature entries.
export const builderUserHook = BUser.registerHook('postCreation', (opts) => {
	const { name } = opts.inheritedInstance;
	const { existentInstance: parent } = opts;
	void name;
	void parent;
});
export const tacticaUserHook = TUser.registerHook('postCreation', (opts) => {
	const { name } = opts.inheritedInstance;
	const { existentInstance: parent } = opts;
	void name;
	void parent;
});
export const tacticaGadgetHook = TGadget.registerHook('postCreation', (opts) => {
	const field: string = opts.inheritedInstance.g;
	void field;
});
export const tacticaRobotHook = TRobot.registerHook('postCreation', (opts) => {
	const { serial } = opts.inheritedInstance;
	void serial;
});
