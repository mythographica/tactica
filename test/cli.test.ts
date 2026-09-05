'use strict';

import { expect } from 'chai';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
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
	// trap: the nestjs example does this). The conventional project .tactica
	// dir must be excluded anyway, even when --output points elsewhere.
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
