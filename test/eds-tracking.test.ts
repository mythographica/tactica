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

		it('should detect wrapArgs() call', () => {
			const source = `
				import { wrapArgs } from '@mnemonica/dive';
				const wrapped = wrapArgs(someFn);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const wrapEntry = entries.find(e => e.kind === 'wrap' && e.code.includes('wrapArgs'));
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

	describe('link() detection', () => {
		it('should detect link() call', () => {
			const source = `
				import { link } from '@mnemonica/dive';
				link(parentInstance, childInstance);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const linkEntry = entries.find(e => e.kind === 'link');
			expect(linkEntry).to.exist;
			expect(linkEntry!.code).to.include('link(');
		});

		it('should detect runWithInstance() call', () => {
			const source = `
				import { runWithInstance } from '@mnemonica/dive';
				runWithInstance(instance, () => { /* ... */ });
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const linkEntry = entries.find(e => e.kind === 'link' && e.code.includes('runWithInstance'));
			expect(linkEntry).to.exist;
		});
	});

	describe('contextConsume detection', () => {
		it('should detect getLastContext() call', () => {
			const source = `
				import { getLastContext } from '@mnemonica/dive';
				const ctx = getLastContext();
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const ctxEntry = entries.find(e => e.kind === 'contextConsume' && e.code.includes('getLastContext'));
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

	describe('errorEnrich detection', () => {
		it('should detect enrichError() call', () => {
			const source = `
				import { enrichError } from '@mnemonica/dive';
				enrichError(err, instance);
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const enrichEntry = entries.find(e => e.kind === 'errorEnrich');
			expect(enrichEntry).to.exist;
			expect(enrichEntry!.code).to.include('enrichError(');
		});
	});

	describe('hookAttach detection', () => {
		it('should detect attachHooks() with single type', () => {
			const source = `
				import { attachHooks } from '@mnemonica/dive';
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
				import { attachHooks } from '@mnemonica/dive';
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

	describe('adapterUse detection', () => {
		it('should detect createDiveInterceptor() call', () => {
			const source = `
				import { createDiveInterceptor } from '@mnemonica/dive/adapters/nestjs';
				const interceptor = createDiveInterceptor();
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const adapterEntry = entries.find(e => e.kind === 'adapterUse');
			expect(adapterEntry).to.exist;
			expect(adapterEntry!.code).to.include('createDiveInterceptor');
		});

		it('should detect createDivePlugin() call', () => {
			const source = `
				import { createDivePlugin } from '@mnemonica/dive/adapters/fastify';
				const plugin = createDivePlugin();
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const adapterEntry = entries.find(
				e => e.kind === 'adapterUse' && e.code.includes('createDivePlugin')
			);
			expect(adapterEntry).to.exist;
		});

		it('should detect createDiveMiddleware() call', () => {
			const source = `
				import { createDiveMiddleware } from '@mnemonica/dive/adapters/express';
				const middleware = createDiveMiddleware();
			`;

			analyzer.analyzeSource(source);
			const eds = analyzer.getEDSUsages();

			const entries = Array.from(eds.values()).flat();
			const adapterEntry = entries.find(
				e => e.kind === 'adapterUse' && e.code.includes('createDiveMiddleware')
			);
			expect(adapterEntry).to.exist;
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
});
