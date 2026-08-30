import { expect } from 'chai';
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
				import { attachHooks } from '@mnemonica/nestjs';
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
				import { attachHooks } from '@mnemonica/nestjs';
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
});
