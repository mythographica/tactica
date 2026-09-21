'use strict';

import { expect } from 'chai';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import * as ts from 'typescript';
import { parseArgs, run } from '../src/cli';

describe('parseArgs()', () => {
	it('should return empty options for empty args', () => {
		const opts = parseArgs([]);
		expect(opts).to.deep.equal({});
	});

	it('should parse --watch flag', () => {
		expect(parseArgs([ '--watch' ]).watch).to.be.true;
		expect(parseArgs([ '-w' ]).watch).to.be.true;
	});

	it('should parse --project flag', () => {
		const opts = parseArgs([ '--project', './tsconfig.json' ]);
		expect(opts.project).to.equal('./tsconfig.json');
	});

	it('should parse -p shorthand for project', () => {
		const opts = parseArgs([ '-p', './custom.tsconfig.json' ]);
		expect(opts.project).to.equal('./custom.tsconfig.json');
	});

	it('should parse --output flag', () => {
		const opts = parseArgs([ '--output', '.out' ]);
		expect(opts.outputDir).to.equal('.out');
	});

	it('should parse -o shorthand for output', () => {
		const opts = parseArgs([ '-o', './dist/types' ]);
		expect(opts.outputDir).to.equal('./dist/types');
	});

	it('should parse --include as comma-separated patterns', () => {
		const opts = parseArgs([ '--include', 'src/**,lib/**' ]);
		expect(opts.include).to.deep.equal([ 'src/**', 'lib/**' ]);
	});

	it('should parse -i shorthand and accumulate multiple --include flags', () => {
		const opts = parseArgs([ '-i', 'src/**', '-i', 'lib/**' ]);
		expect(opts.include).to.include('src/**');
		expect(opts.include).to.include('lib/**');
	});

	it('should parse --exclude flag', () => {
		const opts = parseArgs([ '--exclude', 'node_modules/**,dist/**' ]);
		expect(opts.exclude).to.deep.equal([ 'node_modules/**', 'dist/**' ]);
	});

	it('should parse -e shorthand for exclude', () => {
		const opts = parseArgs([ '-e', '**/*.spec.ts' ]);
		expect(opts.exclude).to.deep.equal([ '**/*.spec.ts' ]);
	});

	it('should parse --module-augmentation as globalAugmentation:false', () => {
		const opts = parseArgs([ '--module-augmentation' ]);
		expect(opts.globalAugmentation).to.be.false;
	});

	it('should parse -m shorthand for module-augmentation', () => {
		const opts = parseArgs([ '-m' ]);
		expect(opts.globalAugmentation).to.be.false;
	});

	it('should parse --verbose flag', () => {
		expect(parseArgs([ '--verbose' ]).verbose).to.be.true;
		expect(parseArgs([ '-v' ]).verbose).to.be.true;
	});

	it('should parse --topologica as comma-separated dirs', () => {
		const opts = parseArgs([ '--topologica', 'src/ai-types,src/types' ]);
		expect(opts.topologicaDirs).to.deep.equal([ 'src/ai-types', 'src/types' ]);
	});

	it('should parse -t shorthand for topologica', () => {
		const opts = parseArgs([ '-t', 'ai-types' ]);
		expect(opts.topologicaDirs).to.deep.equal([ 'ai-types' ]);
	});

	it('should parse --esm flag', () => {
		expect(parseArgs([ '--esm' ]).esm).to.be.true;
	});

	it('should parse --eds flag', () => {
		expect(parseArgs([ '--eds' ]).eds).to.be.true;
	});

	it('should parse --no-eds flag', () => {
		expect(parseArgs([ '--no-eds' ]).eds).to.be.false;
	});

	it('should parse --help flag', () => {
		expect(parseArgs([ '--help' ]).help).to.be.true;
		expect(parseArgs([ '-h' ]).help).to.be.true;
	});

	it('should parse multiple flags together', () => {
		const opts = parseArgs([ '--watch', '--verbose', '--esm', '--output', '.out' ]);
		expect(opts.watch).to.be.true;
		expect(opts.verbose).to.be.true;
		expect(opts.esm).to.be.true;
		expect(opts.outputDir).to.equal('.out');
	});
});

describe('run() exclusion', () => {
	// The fixture tsconfig deliberately includes ".tactica/*.ts" (the real-world
	// trap: the tactica-nestjs example does this). The conventional project
	// .tactica dir must be excluded anyway, even when --output points elsewhere.
	const fixtureDir = path.join(__dirname, 'fixtures', 'cli-exclusion');

	it('should always exclude the project-conventional .tactica directory', () => {
		const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-cli-exclusion-'));
		try {
			run({
				project : path.join(fixtureDir, 'tsconfig.json'),
				outputDir,
			});

			const modulesJson = JSON.parse(
				fs.readFileSync(path.join(outputDir, 'modules.json'), 'utf-8')
			);
			const keys = Object.keys(modulesJson.modules);
			expect(keys.filter(k => k.includes(`${path.sep}.tactica${path.sep}`))).to.deep.equal([]);
			expect(keys.some(k => k.endsWith(path.join('src', 'main.ts')))).to.be.true;
		} finally {
			fs.rmSync(outputDir, { recursive : true, force : true });
		}
	});
});

describe('run() deprecated compiler options', () => {
	// Tactica bundles its own TypeScript (6.x), newer than the compiler many
	// user tsconfigs were written for. A TS5-era config carrying `baseUrl`
	// is a deprecation ERROR under TS6 (TS5101); analysis never emits user
	// code, so loadProgram silences deprecations instead of failing.
	const fixtureDir = path.join(__dirname, 'fixtures', 'cli-baseurl');

	it('should analyze a TS5-era tsconfig with baseUrl without failing', () => {
		const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-cli-baseurl-'));
		try {
			run({
				project : path.join(fixtureDir, 'tsconfig.json'),
				outputDir,
			});

			const modulesJson = JSON.parse(
				fs.readFileSync(path.join(outputDir, 'modules.json'), 'utf-8')
			);
			const keys = Object.keys(modulesJson.modules);
			expect(keys.some(k => k.endsWith(path.join('src', 'main.ts')))).to.be.true;
		} finally {
			fs.rmSync(outputDir, { recursive : true, force : true });
		}
	});
});

describe('run() custom collections (Option B)', () => {
	// The CLI usages pass re-analyzes every file after resetUsages(); the
	// collection id minted for a collection variable must stay stable across
	// both passes. A re-minted id re-registers every collection type under a
	// second `collectionId::` prefix and the generator then emits each entry
	// twice — the generated types.ts/registry.ts fail with TS2300.
	//
	// The output goes to the fixture-local .tactica (the conventional project
	// layout) so the generated files resolve 'mnemonica' by plain node_modules
	// walk-up and `declare module '../src/models'` lands on the fixture source;
	// afterEach removes it again.
	const fixtureDir = path.join(__dirname, 'fixtures', 'cli-collections');
	const outputDir = path.join(fixtureDir, '.tactica');

	afterEach(() => {
		fs.rmSync(outputDir, { recursive : true, force : true });
	});

	it('should emit each collection type exactly once', () => {
		const exitCode = run({
			project : path.join(fixtureDir, 'tsconfig.json'),
			outputDir,
		});
		expect(exitCode).to.equal(0);

		const typesTs = fs.readFileSync(path.join(outputDir, 'types.ts'), 'utf-8');
		const registryTs = fs.readFileSync(path.join(outputDir, 'registry.ts'), 'utf-8');

		expect(typesTs.split('export type ShopRegistry_Product =')).to.have.length(2);
		expect(typesTs.split('export type ShopRegistry_Product_Category =')).to.have.length(2);
		expect(registryTs.split('\'Product\':')).to.have.length(2);
		expect(registryTs.split('\'Product.Category\':')).to.have.length(2);

		const definitionsJson = JSON.parse(
			fs.readFileSync(path.join(outputDir, 'definitions.json'), 'utf-8')
		);
		expect(Object.keys(definitionsJson.definitions)).to.have.length(2);
	});

	it('should resolve collection lookups and compile against the generated types', () => {
		const exitCode = run({
			project : path.join(fixtureDir, 'tsconfig.json'),
			outputDir,
		});
		expect(exitCode).to.equal(0);

		const usagesJson = JSON.parse(
			fs.readFileSync(path.join(outputDir, 'usages.json'), 'utf-8')
		);
		const usageKeys = Object.keys(usagesJson.usages);
		const categoryKey = usageKeys.find(k => k.endsWith('::Product.Category'));
		expect(categoryKey).to.exist;
		const relativeLookup = (usagesJson.usages[ categoryKey! ] as Array<{ code: string }>)
			.find(u => u.code.includes('ProductCtor.lookup'));
		expect(relativeLookup).to.exist;

		// End-to-end acceptance: the generated types/registry, the fixture
		// models, and the strict consumer (including its @ts-expect-error
		// negatives) compile with zero diagnostics under tactica's bundled
		// TypeScript.
		const configPath = path.join(fixtureDir, 'tsconfig.json');
		const configFile = ts.readConfigFile(configPath, ts.sys.readFile);
		const parsed = ts.parseJsonConfigFileContent(configFile.config, ts.sys, fixtureDir);
		const program = ts.createProgram(parsed.fileNames, parsed.options);
		const diagnostics = ts.getPreEmitDiagnostics(program);
		const messages = diagnostics.map(d =>
			`${d.file ? `${d.file.fileName}:${d.start} — ` : ''}${ts.flattenDiagnosticMessageText(d.messageText, '\n')}`
		);
		expect(messages).to.deep.equal([]);
	});
});

describe('run() plugin config', () => {
	// Framework instrumentation vocabulary arrives via plugins: a
	// .tactica.js config next to the fixture tsconfig loads one plugin by
	// string specifier and one inline. Without a config file, the analyzer
	// stays framework-blind.
	const fixtureDir = path.join(__dirname, 'fixtures', 'cli-plugin');

	it('should load plugins from the project .tactica.js config', () => {
		const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-cli-plugin-'));
		try {
			run({
				project : path.join(fixtureDir, 'tsconfig.json'),
				outputDir,
			});

			const instrumentationJson = JSON.parse(
				fs.readFileSync(path.join(outputDir, 'instrumentation.json'), 'utf-8')
			);
			const points = instrumentationJson.points as Array<Record<string, unknown>>;

			// String-loaded plugin: heritage interface match
			const stringPoint = points.find(p => p.className === 'FixtureGuard' && p.scope === 'module');
			expect(stringPoint).to.exist;
			expect(stringPoint!.kind).to.equal('guard');

			// Inline plugin: heritage interface match
			const inlinePoint = points.find(p => p.className === 'InlineGuard');
			expect(inlinePoint).to.exist;

			// Inline plugin: provider-token registration, global scope
			const tokenPoint = points.find(p => p.scope === 'global');
			expect(tokenPoint).to.exist;
			expect(tokenPoint!.className).to.equal('FixtureGuard');
		} finally {
			fs.rmSync(outputDir, { recursive : true, force : true });
		}
	});

	it('should emit empty points without a config file or programmatic plugins', () => {
		const exclusionFixture = path.join(__dirname, 'fixtures', 'cli-exclusion');
		const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-cli-noplugin-'));
		try {
			run({
				project : path.join(exclusionFixture, 'tsconfig.json'),
				outputDir,
			});

			const instrumentationJson = JSON.parse(
				fs.readFileSync(path.join(outputDir, 'instrumentation.json'), 'utf-8')
			);
			expect(instrumentationJson.points).to.deep.equal([]);
		} finally {
			fs.rmSync(outputDir, { recursive : true, force : true });
		}
	});
});

describe('run() EDS join data', () => {
	// Wrap entries carry the join data mnemographica's wrappers layer needs:
	// the holder scope of the call site (scopeId) and the mnemonica type of
	// the wrapped instance argument (wrapsTypePath), resolved through the
	// scope-variable chain.
	const fixtureDir = path.join(__dirname, 'fixtures', 'cli-eds');

	it('should pin wrap entries to holder scopes and resolve wrapped instance types', () => {
		const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-cli-eds-'));
		try {
			run({
				project : path.join(fixtureDir, 'tsconfig.json'),
				outputDir,
				eds     : true,
			});

			const edsJson = JSON.parse(
				fs.readFileSync(path.join(outputDir, 'eds.json'), 'utf-8')
			);
			const entries = Object.values(edsJson.eds).flat() as Array<Record<string, unknown>>;
			const wrapEntry = entries.find(e => e.kind === 'wrap' && e.label === 'demo:wrap');
			expect(wrapEntry).to.exist;
			expect(wrapEntry!.instanceArg).to.equal('widget');
			expect(wrapEntry!.wrapsTypePath).to.equal('Widget');
			expect(wrapEntry!.callbackScopeId).to.be.a('string').and.include('main.ts');
			expect(wrapEntry!.scopeId).to.be.a('string').and.include('main.ts');
			// The holder scope of the wrap call is makeWrapped's function scope,
			// not the module scope (module scope ids are the bare file path)
			expect(String(wrapEntry!.scopeId)).to.match(/main\.ts:\d+:\d+$/);
		} finally {
			fs.rmSync(outputDir, { recursive : true, force : true });
		}
	});
});
