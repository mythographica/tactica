import { expect } from 'chai';
import * as path from 'path';
import { MnemonicaAnalyzer } from '../src/analyzer';

describe('MnemonicaAnalyzer - EDS Tracking', () => {
	let analyzer: MnemonicaAnalyzer;

	beforeEach(() => {
		analyzer = new MnemonicaAnalyzer();
	});

	describe('wrap() detection', () => {
		it('should detect wrap() call', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const MyType = define('MyType', function () {
					this.value = 1;
				});

				const instance = new MyType();
				const wrapped = wrap(instance.process.bind(instance));
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			expect(eds.size).to.be.greaterThan(0);
			const entries = Array.from(eds.values()).flat();
			const wrapEntry = entries.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.code).to.include('wrap(');
		});

		it('should detect wrapConstructorArg() call', () => {
			const source = `
				import { wrapConstructorArg } from '@mnemonica/dive';
				const wrapped = wrapConstructorArg(someFn, parent);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const wrapEntry = entries.find(e => e.kind === 'wrap' && e.code.includes('wrapConstructorArg'));
			expect(wrapEntry).to.exist;
		});

		it('should detect upgradeConstructorArg() call', () => {
			const source = `
				import { upgradeConstructorArg } from '@mnemonica/dive';
				upgradeConstructorArg(arg, instance);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const wrapEntry = entries.find(e => e.kind === 'wrap' && e.code.includes('upgradeConstructorArg'));
			expect(wrapEntry).to.exist;
		});

		it('should detect wrapInstanceMethods() call', () => {
			const source = `
				import { wrapInstanceMethods } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const MyType = define('MyType', function () {
					this.value = 1;
				});

				const instance = new MyType();
				wrapInstanceMethods(instance);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const wrapEntry = entries.find(e => e.kind === 'wrap' && e.code.includes('wrapInstanceMethods'));
			expect(wrapEntry).to.exist;
		});
	});

	describe('contextConsume detection', () => {
		it('should detect current() call', () => {
			const source = `
				import { current } from '@mnemonica/dive';
				const ctx = current();
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const ctxEntry = entries.find(e => e.kind === 'contextConsume' && e.code.includes('current'));
			expect(ctxEntry).to.exist;
		});

		it('should detect getFlow() call', () => {
			const source = `
				import { getFlow } from '@mnemonica/dive';
				const flow = getFlow(err);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const ctxEntry = entries.find(e => e.kind === 'contextConsume' && e.code.includes('getFlow'));
			expect(ctxEntry).to.exist;
		});

		it('should detect getErrorInstance() call', () => {
			const source = `
				import { getErrorInstance } from '@mnemonica/dive';
				const inst = getErrorInstance(err);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const ctxEntry = entries.find(e => e.kind === 'contextConsume' && e.code.includes('getErrorInstance'));
			expect(ctxEntry).to.exist;
		});
	});

	describe('hookAttach detection', () => {
		it('should detect attachHooks() with single type', () => {
			const source = `
				import { attachHooks } from '@mnemonica/otel';
				import { defaultTypes } from 'mnemonica';

				attachHooks(defaultTypes);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const hookEntry = entries.find(e => e.kind === 'hookAttach');
			expect(hookEntry).to.exist;
			expect(hookEntry!.code).to.include('attachHooks(');
		});

		it('should detect attachHooks() with array of types', () => {
			const source = `
				import { attachHooks } from '@mnemonica/otel';
				import { define } from 'mnemonica';

				const TypeA = define('TypeA', function () { this.a = 1; });
				const TypeB = define('TypeB', function () { this.b = 2; });

				attachHooks([TypeA, TypeB]);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			// Should have entries for both TypeA and TypeB
			const entries = Array.from(eds.values()).flat();
			const hookEntries = entries.filter(e => e.kind === 'hookAttach');
			expect(hookEntries.length).to.be.at.least(2);
		});
	});

	describe('duplicate prevention', () => {
		it('should not duplicate identical EDS entries', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				const w1 = wrap(fn);
				const w2 = wrap(fn);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const wrapEntries = entries.filter(e => e.kind === 'wrap');
			// Two wrap calls on different lines should both be recorded
			expect(wrapEntries.length).to.equal(2);
		});
	});

	describe('type resolution', () => {
		it('should resolve type from variable for wrap()', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const MyType = define('MyType', function () {
					this.value = 1;
				});

				const instance = new MyType();
				wrap(instance.doWork.bind(instance));
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			// Should have an entry with targetType pointing to MyType or unknown
			const entries = Array.from(eds.values()).flat();
			const wrapEntry = entries.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
		});
	});

	describe('scope keying', () => {
		it('should key wrap() inside a define() handler by the type path', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const MyType = define('MyType', function () {
					this.process = wrap(function () { return 1; });
				});
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const scoped = eds.get('MyType');
			expect(scoped).to.exist;
			const wrapEntry = scoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.scope).to.equal('MyType');
		});

		it('should key wrap() inside a nested define() handler by the full path', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const MyType = define('MyType', function () {
					this.value = 1;
				});

				const SubType = MyType.define('SubType', function () {
					this.process = wrap(function () { return 2; });
				});
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const scoped = eds.get('MyType.SubType');
			expect(scoped).to.exist;
			const wrapEntry = scoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.scope).to.equal('MyType.SubType');
		});

		it('should key wrap() inside a @decorate()-ed class method by the class type', () => {
			const source = `
				import { decorate } from 'mnemonica';
				import { wrap } from '@mnemonica/dive';

				@decorate()
				class MyClass {
					doWork () {
						return wrap(function () { return 3; });
					}
				}
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const scoped = eds.get('MyClass');
			expect(scoped).to.exist;
			const wrapEntry = scoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.scope).to.equal('MyClass');
		});

		it('should keep the unknown key for wrap() outside any type scope', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				const wrapped = wrap(function () { return 4; });
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const unscoped = eds.get('unknown');
			expect(unscoped).to.exist;
			const wrapEntry = unscoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.scope).to.be.undefined;
		});

		it('should key current() inside a define() handler by the type path', () => {
			const source = `
				import { current } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const MyType = define('MyType', function () {
					this.ctx = current();
				});
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const scoped = eds.get('MyType');
			expect(scoped).to.exist;
			const ctxEntry = scoped!.find(e => e.kind === 'contextConsume');
			expect(ctxEntry).to.exist;
			expect(ctxEntry!.scope).to.equal('MyType');
		});
	});

	describe('wrapped body analysis', () => {
		it('should record a function-valued return as a nested wrap with via', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';

				const fn = function () {
					return () => 42;
				};
				const w = wrap(fn);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const rootEntry = entries.find(e => e.code.includes('wrap(fn)'));
			expect(rootEntry).to.exist;
			const nested = entries.find(e => e.via === rootEntry!.location);
			expect(nested).to.exist;
			expect(nested!.kind).to.equal('wrap');
		});

		it('should chain via through nested returns (fn -> g -> h)', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';

				const h = () => 1;
				const g = function () { return h; };
				const fn = function () { return g; };
				wrap(fn);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const rootEntry = entries.find(e => e.code.includes('wrap(fn)'));
			expect(rootEntry).to.exist;
			const midEntry = entries.find(e => e.via === rootEntry!.location);
			expect(midEntry).to.exist;
			const leafEntry = entries.find(e => e.via === midEntry!.location);
			expect(leafEntry).to.exist;
		});

		it('should record mnemonica instances created in the wrapped body as createsTypes', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const MyType = define('MyType', function () {
					this.value = 1;
				});

				const fn = function () {
					const inst = new MyType();
					return inst;
				};
				wrap(fn);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const rootEntry = entries.find(e => e.code.includes('wrap(fn)'));
			expect(rootEntry).to.exist;
			expect(rootEntry!.createsTypes).to.include('MyType');
		});

		it('should back-patch via onto a lexically nested wrap call', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';

				const outer = function () {
					const inner = wrap(function () { return 1; });
					return inner;
				};
				wrap(outer);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const rootEntry = entries.find(e => e.code.includes('wrap(outer)'));
			expect(rootEntry).to.exist;
			// the nested wrap call was visited BEFORE wrap(outer), so its
			// via arrives through the back-patch path
			const nestedCall = entries.find(e => e.code.includes('wrap(function'));
			expect(nestedCall).to.exist;
			expect(nestedCall!.via).to.equal(rootEntry!.location);
		});

		it('should survive a function returning itself (cycle guard)', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';

				const fn = function () {
					return fn;
				};
				wrap(fn);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const rootEntry = entries.find(e => e.code.includes('wrap(fn)'));
			expect(rootEntry).to.exist;
			// fn returns fn: exactly one nested entry, no infinite recursion
			const nested = entries.filter(e => e.via === rootEntry!.location);
			expect(nested.length).to.equal(1);
		});
	});

	describe('wrap fn field (engine knot join)', () => {
		it('should record fn for each wrap-family call', () => {
			const source = `
				import { wrap, wrapConstructorArg, upgradeConstructorArg, wrapInstanceMethods } from '@mnemonica/dive';

				const a = wrap(function () { return 1; });
				const b = wrapConstructorArg(function () { return 2; }, parent);
				const c = upgradeConstructorArg(arg, inst);
				const d = wrapInstanceMethods(inst);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat()
				.filter(e => e.kind === 'wrap');
			const byCode = (needle: string) => entries.find(e => e.code.startsWith(needle));
			expect(byCode('wrap(function')!.fn).to.equal('wrap');
			expect(byCode('wrapConstructorArg(')!.fn).to.equal('wrapConstructorArg');
			expect(byCode('upgradeConstructorArg(')!.fn).to.equal('upgradeConstructorArg');
			expect(byCode('wrapInstanceMethods(')!.fn).to.equal('wrapInstanceMethods');
		});

		it('should mark return-chain nested wraps as fn wrap', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';

				const fn = function () {
					return () => 42;
				};
				wrap(fn);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const rootEntry = entries.find(e => e.code.includes('wrap(fn)'));
			const nested = entries.find(e => e.via === rootEntry!.location);
			expect(nested).to.exist;
			expect(nested!.fn).to.equal('wrap');
		});
	});

	describe('wrap() join fields', () => {
		it('should record the label of wrap(fn, label) and no instanceArg', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';

				const w = wrap(function () { return 1; }, 'job:run');
			`;

			analyzer.analyzeSource(source);
			const entries = Array.from(analyzer.getEDSUsages().values()).flat();
			const wrapEntry = entries.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.label).to.equal('job:run');
			expect(wrapEntry!.instanceArg).to.be.undefined;
		});

		it('should record both instanceArg and label of wrap(fn, instance, label)', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';

				const user = { name : 'ada' };
				const w = wrap(function () { return 1; }, user, 'job:run');
			`;

			analyzer.analyzeSource(source);
			const entries = Array.from(analyzer.getEDSUsages().values()).flat();
			const wrapEntry = entries.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.instanceArg).to.equal('user');
			expect(wrapEntry!.label).to.equal('job:run');
		});

		it('should treat wrapConstructorArg(fn, context) second arg as the instance', () => {
			const source = `
				import { wrapConstructorArg } from '@mnemonica/dive';
				const wrapped = wrapConstructorArg(someFn, parent);
			`;

			analyzer.analyzeSource(source);
			const entries = Array.from(analyzer.getEDSUsages().values()).flat();
			const wrapEntry = entries.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.instanceArg).to.equal('parent');
			expect(wrapEntry!.label).to.be.undefined;
		});

		it('should treat wrapInstanceMethods(instance) first arg as the instance', () => {
			const source = `
				import { wrapInstanceMethods } from '@mnemonica/dive';

				const instance = { work () { return 1; } };
				wrapInstanceMethods(instance);
			`;

			analyzer.analyzeSource(source);
			const entries = Array.from(analyzer.getEDSUsages().values()).flat();
			const wrapEntry = entries.find(e => e.kind === 'wrap' && e.code.includes('wrapInstanceMethods'));
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.instanceArg).to.equal('instance');
			expect(wrapEntry!.callbackScopeId).to.be.undefined;
		});

		it('should record callbackScopeId at the wrapped callback start', () => {
			const source = [
				'import { wrap } from \'@mnemonica/dive\';',
				'',
				'const w = wrap(() => {',
				'\treturn 1;',
				'});',
			].join('\n');

			analyzer.analyzeSource(source, 'test.ts');
			const entries = Array.from(analyzer.getEDSUsages().values()).flat();
			const wrapEntry = entries.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.callbackScopeId).to.exist;
			expect(wrapEntry!.callbackScopeId!.startsWith(path.resolve('test.ts'))).to.be.true;

			// The recorded coordinates point at the arrow's parameter list:
			// line 3, and the character there is the opening '(' of '() => {'
			const match = /:(\d+):(\d+)$/.exec(wrapEntry!.callbackScopeId!);
			expect(match).to.exist;
			const [ , lineText, colText ] = match!;
			expect(Number(lineText)).to.equal(3);
			const [ , , sourceLine ] = source.split('\n');
			expect(sourceLine[ Number(colText) - 1 ]).to.equal('(');
		});
	});

	describe('scope attribution through wrappers', () => {
		it('should attribute a module-level wrap() through a tracked instance assignment', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const Holder = define('Holder', function (this: Holder) {
					this.kind = 'holder';
				});

				const holder = new Holder();
				const w = wrap(function () { return 1; }, holder, 'job:run');
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const scoped = eds.get('Holder');
			expect(scoped).to.exist;
			const wrapEntry = scoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.scope).to.equal('Holder');
			expect(wrapEntry!.instanceArg).to.equal('holder');
		});

		it('should attribute a wrap() in a wire-up helper through the parameter annotation', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const Holder = define('Holder', function (this: Holder) {
					this.kind = 'holder';
				});

				function wire (holder: Holder) {
					return wrap(function () { return 2; }, holder);
				}
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const scoped = eds.get('Holder');
			expect(scoped).to.exist;
			const wrapEntry = scoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.scope).to.equal('Holder');
			expect(wrapEntry!.instanceArg).to.equal('holder');
		});

		it('should attribute a wrap() through a let with an explicit type annotation (F20 cheap tier)', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const LedgerUpdate = define('LedgerUpdate', function (this: LedgerUpdate) {
					this.kind = 'ledger';
				});

				export function processUpdate (committed: { id: string }) {
					let updateCommitted: LedgerUpdate;
					try {
						updateCommitted = Object.assign(new LedgerUpdate(), committed);
						return wrap(function () { return committed.id; }, updateCommitted);
					} catch (error) {
						return undefined;
					}
				}
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const scoped = eds.get('LedgerUpdate');
			expect(scoped).to.exist;
			const wrapEntry = scoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.scope).to.equal('LedgerUpdate');
			expect(wrapEntry!.instanceArg).to.equal('updateCommitted');
		});

		it('should attribute a wrap() through a let annotated with a GENERATED nested-type alias (F24)', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const UpdatePay = define('UpdatePay', function (this: UpdatePay) {
					this.kind = 'pay';
				});
				UpdatePay.define('SomeTerminal', function (this: SomeTerminal, data: { code: string }) {
					this.code = data.code;
				});

				export async function updateSomething (updatePay: UpdatePay, payload: { code: string }) {
					let updateCommitted: UpdatePay_SomeTerminal;
					try {
						updateCommitted = new updatePay.SomeTerminal({ code: payload.code });
					} catch (error) {
						throw error;
					}
					return wrap(function () { return payload.code; }, updateCommitted);
				}
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const scoped = eds.get('UpdatePay.SomeTerminal');
			expect(scoped).to.exist;
			const wrapEntry = scoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.scope).to.equal('UpdatePay.SomeTerminal');
			expect(wrapEntry!.instanceArg).to.equal('updateCommitted');
		});

		it('should attribute a wrap() through a let assigned inside a try (catch-guard pattern, let-in-try)', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const ReportTerminal = define('ReportTerminal', function (this: ReportTerminal, data: { channel: string }) {
					this.channel = data.channel;
				});

				export async function wireReport (context: { raw: string }) {
					let sendReport;
					try {
						sendReport = new ReportTerminal({ channel: 'main' });
					} catch (error) {
						return;
					}
					return wrap(sendReport, context);
				}
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const scoped = eds.get('ReportTerminal');
			expect(scoped).to.exist;
			const wrapEntry = scoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.targetType).to.equal('ReportTerminal');
		});

		it('should attribute the const-at-declaration control the same way (the field workaround)', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const ReportTerminal = define('ReportTerminal', function (this: ReportTerminal, data: { channel: string }) {
					this.channel = data.channel;
				});

				export function wireConst (context: { raw: string }) {
					const sendReport = new ReportTerminal({ channel: 'alt' });
					return wrap(sendReport, context);
				}
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const scoped = eds.get('ReportTerminal');
			expect(scoped).to.exist;
			const wrapEntry = scoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.targetType).to.equal('ReportTerminal');
		});

		it('should NOT attribute a let assigned only inside a nested closure (scope boundary)', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const ReportTerminal = define('ReportTerminal', function (this: ReportTerminal, data: { channel: string }) {
					this.channel = data.channel;
				});

				export function wireClosure (context: { raw: string }, defer: (fn: () => void) => void) {
					let sendReport;
					defer(() => {
						sendReport = new ReportTerminal({ channel: 'inner' });
					});
					return wrap(sendReport, context);
				}
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			expect(eds.get('ReportTerminal')?.filter(e => e.kind === 'wrap')).to.be.undefined;
			const unscoped = eds.get('unknown');
			expect(unscoped).to.exist;
			const wrapEntry = unscoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
		});

		it('should NOT attribute a let that is never assigned in scope', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const ReportTerminal = define('ReportTerminal', function (this: ReportTerminal, data: { channel: string }) {
					this.channel = data.channel;
				});

				export function wireUnassigned (context: { raw: string }) {
					let sendReport;
					return wrap(sendReport, context);
				}
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			expect(eds.get('ReportTerminal')?.filter(e => e.kind === 'wrap')).to.be.undefined;
			const unscoped = eds.get('unknown');
			expect(unscoped).to.exist;
		});

		it('should attribute a wrap() callee through its explicit annotation when the assignment is untrackable (annotation fallback)', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const ReportTerminal = define('ReportTerminal', function (this: ReportTerminal, data: { channel: string }) {
					this.channel = data.channel;
				});

				export async function wireAnnotated (context: { raw: string }) {
					let sendReport: ReportTerminal;
					try {
						sendReport = makeSender();
					} catch (error) {
						return;
					}
					return wrap(sendReport, context);
				}
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const scoped = eds.get('ReportTerminal');
			expect(scoped).to.exist;
			const wrapEntry = scoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.targetType).to.equal('ReportTerminal');
		});

		it('should prefer a resolvable assignment over the annotation claim (constructed subtype is the more specific truth)', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const ReportTerminal = define('ReportTerminal', function (this: ReportTerminal, data: { channel: string }) {
					this.channel = data.channel;
				});
				const LedgerRoot = define('LedgerRoot', function (this: LedgerRoot, data: { code: string }) {
					this.code = data.code;
				});

				export function wirePrecedence (context: { raw: string }) {
					let sendReport: ReportTerminal;
					try {
						sendReport = new LedgerRoot({ code: 'x' });
					} catch (error) {
						return;
					}
					return wrap(sendReport, context);
				}
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			// the assignment constructs a LedgerRoot — runtime truth beats
			// the annotation claim even though the annotation named another type
			const scoped = eds.get('LedgerRoot');
			expect(scoped).to.exist;
			const wrapEntry = scoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(eds.get('ReportTerminal')?.filter(e => e.kind === 'wrap')).to.be.undefined;
		});

		it('should attribute a wrap() callee arriving as an annotated function parameter', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const ReportTerminal = define('ReportTerminal', function (this: ReportTerminal, data: { channel: string }) {
					this.channel = data.channel;
				});

				export function wireParam (sendReport: ReportTerminal, context: { raw: string }) {
					return wrap(sendReport, context);
				}
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const scoped = eds.get('ReportTerminal');
			expect(scoped).to.exist;
			const wrapEntry = scoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.targetType).to.equal('ReportTerminal');
		});

		it('should keep an unannotated let with an untrackable assignment unknown (honest negative)', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const ReportTerminal = define('ReportTerminal', function (this: ReportTerminal, data: { channel: string }) {
					this.channel = data.channel;
				});

				export function wireUntrackable (context: { raw: string }) {
					let sendReport;
					try {
						sendReport = makeSender();
					} catch (error) {
						return;
					}
					return wrap(sendReport, context);
				}
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			expect(eds.get('ReportTerminal')?.filter(e => e.kind === 'wrap')).to.be.undefined;
			const unscoped = eds.get('unknown');
			expect(unscoped).to.exist;
			const wrapEntry = unscoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
		});

		it('should keep the unknown bucket for an UNANNOTATED let (documented F20 boundary)', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const LedgerUpdate = define('LedgerUpdate', function (this: LedgerUpdate) {
					this.kind = 'ledger';
				});

				export function processUpdate (makeIt: () => LedgerUpdate) {
					let updateCommitted;
					try {
						updateCommitted = makeIt();
						return wrap(function () { return 1; }, updateCommitted);
					} catch (error) {
						return undefined;
					}
				}
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			expect(eds.get('LedgerUpdate')?.filter(e => e.kind === 'wrap')).to.be.undefined;
			const unscoped = eds.get('unknown');
			expect(unscoped).to.exist;
			const wrapEntry = unscoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.scope).to.be.undefined;
			expect(wrapEntry!.instanceArg).to.equal('updateCommitted');
		});

		it('should keep the unknown key when neither a handler nor the instance arg attributes the site', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				const w = wrap(function () { return 3; }, untracked);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const unscoped = eds.get('unknown');
			expect(unscoped).to.exist;
			const wrapEntry = unscoped!.find(e => e.kind === 'wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.scope).to.be.undefined;
		});

		it('should inherit the causing wrap site\'s scope for a function-valued return declared outside any handler', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const helper = function () {
					return () => 3;
				};

				const MyService = define('MyService', function (this: MyService) {
					const fn = function () {
						return helper;
					};
					this.process = wrap(fn);
				});
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const scoped = eds.get('MyService');
			expect(scoped).to.exist;
			const rootEntry = scoped!.find(e => e.code.includes('wrap(fn)'));
			expect(rootEntry).to.exist;
			expect(rootEntry!.scope).to.equal('MyService');
			// helper (and its returned arrow) live at module level — the
			// generation chain is their only holder
			const nested = scoped!.filter(e => e.via === rootEntry!.location);
			expect(nested.length).to.be.greaterThan(0);
			for (const entry of nested) {
				expect(entry.scope).to.equal('MyService');
			}
		});

		it('should back-patch the causing site\'s scope onto a lexically nested wrap', () => {
			const source = `
				import { wrap } from '@mnemonica/dive';
				import { define } from 'mnemonica';

				const outer = function () {
					const inner = wrap(function () { return 1; });
					return inner;
				};

				const MyType = define('MyType', function (this: MyType) {
					this.process = wrap(outer);
				});
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const scoped = eds.get('MyType');
			expect(scoped).to.exist;
			const rootEntry = scoped!.find(e => e.code.includes('wrap(outer)'));
			expect(rootEntry).to.exist;
			const nestedCall = Array.from(eds.values()).flat()
				.find(e => e.code.includes('wrap(function'));
			expect(nestedCall).to.exist;
			expect(nestedCall!.via).to.equal(rootEntry!.location);
			expect(nestedCall!.scope).to.equal('MyType');
		});
	});
});
