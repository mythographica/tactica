'use strict';

import { expect } from 'chai';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import { MnemonicaAnalyzer } from '../src/analyzer';
import { run } from '../src/cli';
import { TypesGenerator } from '../src/generator';

/**
 * Graph identity law (F10 follow-up): references to mnemonica graph types
 * resolve path-aware — relative-first up the anchor's parent chain, then
 * the anchor's collection roots, then a program-wide search that must be
 * unique. File-local value bindings and import anchors disambiguate first.
 * Same-namespace duplicate definitions (ALREADY_DECLARED at runtime) and
 * graph references that stay ambiguous or unresolved are fatal: the CLI
 * prints every location, exits non-zero, and writes no .tactica output.
 */
describe('Graph identity law (F10 follow-up)', () => {

	describe('path-aware resolution in the analyzer', () => {
		it('resolves same-named subtypes relative-first: each Order gets its own Leaf', () => {
			const analyzer = new MnemonicaAnalyzer();
			const file = path.join(__dirname, 'fixtures', 'graph-anchored', 'src', 'unit-inline.ts');
			analyzer.analyzeSource(`
import { define } from 'mnemonica';

export const Alpha = define('Alpha', function (this: Alpha) {
	this.tone = 'a';
});
export const Gamma = define('Gamma', function (this: Gamma) {
	this.shade = 'g';
});
Alpha.define('Leaf', function (this: Leaf, data: { tone: string }) {
	this.tone = data.tone;
});
Gamma.define('Leaf', function (this: Leaf, data: { shade: string }) {
	this.shade = data.shade;
});
Alpha.define('Order', function (this: Order, data: Leaf) {
	this.leaf = data;
});
Gamma.define('Order', function (this: Order, data: Leaf) {
	this.leaf = data;
});
`, file);

			const generator = new TypesGenerator(analyzer.getGraph());
			const generated = generator.generateTypesFile();

			// the old first-match scan emitted Alpha_Leaf for both Orders
			expect(generated.content).to.include('leaf: Alpha_Leaf');
			expect(generated.content).to.include('leaf: Gamma_Leaf');
			expect(generated.content.split('leaf: Alpha_Leaf').length - 1).to.equal(1);
			// every reference resolved — nothing is fatal
			expect(analyzer.getResolutionErrors()).to.deep.equal([]);
		});
	});

	describe('lookup() path validation', () => {
		it('hard-fails an unresolved lookup with did-you-mean candidates', () => {
			const analyzer = new MnemonicaAnalyzer();
			analyzer.analyzeSource(`
import { define, lookup } from 'mnemonica';

const Holder = define('Holder', function (this: Holder) {});
Holder.define('Token', function (this: Token, data: { mark: string }) {
	this.mark = data.mark;
});
const Other = define('Other', function (this: Other) {});
Other.define('Token', function (this: Token, data: { hue: string }) {
	this.hue = data.hue;
});
const TokenCtor = lookup('Token');
new TokenCtor({ mark: 'x' });
`, path.join(__dirname, 'fixtures', 'graph-lookup-ambiguous', 'src', 'unit-inline.ts'));

			const errors = analyzer.getResolutionErrors();
			expect(errors).to.have.length(1);
			expect(errors[ 0 ].message).to.include('Unresolved lookup of mnemonica type \'Token\'');
			expect(errors[ 0 ].message).to.include('Holder.Token');
			expect(errors[ 0 ].message).to.include('Other.Token');
			// idempotent: a second call must not double-record
			expect(analyzer.getResolutionErrors()).to.have.length(1);
		});

		it('hard-fails a lookup matching nothing, without candidates', () => {
			const analyzer = new MnemonicaAnalyzer();
			analyzer.analyzeSource(`
import { define, lookup } from 'mnemonica';

const Holder = define('Holder', function (this: Holder) {});
const Ghost = lookup('Ghost');
`, path.join(__dirname, 'fixtures', 'graph-lookup-ambiguous', 'src', 'unit-inline.ts'));

			const errors = analyzer.getResolutionErrors();
			expect(errors).to.have.length(1);
			expect(errors[ 0 ].message).to.include('no type at that path');
		});

		it('accepts dotted and receiver-relative lookups', () => {
			const analyzer = new MnemonicaAnalyzer();
			analyzer.analyzeSource(`
import { define, lookup } from 'mnemonica';

const Holder = define('Holder', function (this: Holder) {});
Holder.define('Token', function (this: Token, data: { mark: string }) {
	this.mark = data.mark;
});
const ByPath = lookup('Holder.Token');
const ByReceiver = Holder.lookup('Token');
new ByPath({ mark: 'x' });
new ByReceiver({ mark: 'y' });
`, path.join(__dirname, 'fixtures', 'graph-lookup-valid', 'src', 'unit-inline.ts'));

			expect(analyzer.getResolutionErrors()).to.deep.equal([]);
		});
	});

	describe('CLI hard-fail', () => {
		const fixtureRoot = path.join(__dirname, 'fixtures');

		const runCapturingErrors = (options: Parameters<typeof run>[0]): { code: number; errors: string } => {
			const originalError = console.error;
			let captured = '';
			console.error = (...args: unknown[]): void => {
				captured += `${args.map(String).join(' ')  }\n`;
			};
			let code = 0;
			try {
				code = run(options);
			} finally {
				console.error = originalError;
			}
			const result = { code, errors : captured };
			return result;
		};

		it('resolves an import-anchored reference and exits 0', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-graph-anchored-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'graph-anchored', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(0);
				expect(errors).to.equal('');
				const types = fs.readFileSync(path.join(outputDir, 'types.ts'), 'utf8');
				expect(types).to.include('item: Holder_Token');
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});

		it('hard-fails on an ambiguous graph reference and writes no output', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-graph-ambiguous-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'graph-ambiguous', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(1);
				expect(errors).to.include('Ambiguous reference');
				expect(errors).to.include('Token');
				// the whole point of the hard fail: no partial output
				expect(fs.existsSync(path.join(outputDir, 'types.ts'))).to.be.false;
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});

		it('hard-fails on an unresolved lookup path and writes no output', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-lookup-ambiguous-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'graph-lookup-ambiguous', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(1);
				expect(errors).to.include('Unresolved lookup');
				expect(errors).to.include('Token');
				expect(errors).to.include('Holder.Token');
				expect(errors).to.include('would return undefined');
				expect(fs.existsSync(path.join(outputDir, 'types.ts'))).to.be.false;
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});

		it('accepts dotted and receiver-relative lookups and exits 0', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-lookup-valid-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'graph-lookup-valid', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(0);
				expect(errors).to.equal('');
				expect(fs.existsSync(path.join(outputDir, 'types.ts'))).to.be.true;
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});

		it('hard-fails on an ambiguous plain-TS reference and writes no output', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-plaints-duplicates-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'plaints-duplicates', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(1);
				expect(errors).to.include('Ambiguous reference to type \'SharedShape\'');
				expect(errors).to.include('no import disambiguates');
				expect(errors).to.include('import the one you mean');
				// the reference site plus EVERY declaration site
				expect(errors).to.include(path.join('src', 'consumer.ts'));
				expect(errors).to.include(path.join('src', 'a.ts'));
				expect(errors).to.include(path.join('src', 'b.ts'));
				// the whole point of the hard fail: no partial output
				expect(fs.existsSync(path.join(outputDir, 'types.ts'))).to.be.false;
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});

		it('resolves an import-anchored plain-TS duplicate and exits 0', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-plaints-anchored-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'plaints-anchored', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(0);
				expect(errors).to.equal('');
				const types = fs.readFileSync(path.join(outputDir, 'types.ts'), 'utf8');
				expect(types).to.include('item: { a: string }');
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});

		it('hard-fails on same-namespace duplicates, reporting every site', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-graph-duplicates-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'graph-duplicates', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(1);
				expect(errors).to.include('Duplicate definition');
				expect(errors).to.include('ALREADY_DECLARED');
				expect(errors).to.include(path.join('src', 'dup-a.ts'));
				expect(errors).to.include(path.join('src', 'dup-b.ts'));
				expect(errors).to.include('Twin');
				expect(fs.existsSync(path.join(outputDir, 'types.ts'))).to.be.false;
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});
	});
});
