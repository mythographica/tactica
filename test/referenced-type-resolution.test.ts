'use strict';

import { expect } from 'chai';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import * as ts from 'typescript';
import { MnemonicaAnalyzer } from '../src/analyzer';
import { run } from '../src/cli';
import { TypesGenerator } from '../src/generator';
import { GeneratedTypes } from '../src/types';
import { TypesWriter } from '../src/writer';

/**
 * F10: referenced types in mnemonica constructor signatures resolve through
 * the importing file's own import statements — never through a program-wide
 * same-name lookup. Unresolvable references emit `unknown`, never a bare
 * unresolvable name (types.ts carries no imports). Ambiguity is split by
 * tier: an unanchored name declared in several project-source files is
 * FATAL (the plain-TS tier of the graph identity law — the CLI prints every
 * site and writes no output); absence (ghost names) and external collisions
 * stay soft `unknown`; same-file interface merging is not ambiguity.
 */
describe('Referenced type resolution (F10)', () => {
	const fixtureRoot = path.join(__dirname, 'fixtures', 'referenced-types');
	const importedDeclFile = path.join(fixtureRoot, 'shape-a', 'models', 'shared-shape.model.ts');
	const unrelatedFile = path.join(fixtureRoot, 'shape-b', 'unrelated-store.ts');
	const expectedExpansion = 'record: { id: string; code: string; amount: number }';

	const analyzeFiles = (analyzer: MnemonicaAnalyzer, ...files: string[]): void => {
		for (const file of files) {
			analyzer.analyzeSource(fs.readFileSync(file, 'utf8'), file);
		}
	};

	const generateTypes = (analyzer: MnemonicaAnalyzer): GeneratedTypes => {
		const generator = new TypesGenerator(analyzer.getGraph());
		const generated = generator.generateTypesFile();
		return generated;
	};

	const generateTypesContent = (analyzer: MnemonicaAnalyzer): string => {
		const generated = generateTypes(analyzer);
		return generated.content;
	};

	it('expands the imported declaration, not a same-named unrelated one', () => {
		const analyzer = new MnemonicaAnalyzer();
		analyzeFiles(
			analyzer,
			importedDeclFile,
			unrelatedFile,
			path.join(fixtureRoot, 'consumers', 'primary.types.ts')
		);

		const content = generateTypesContent(analyzer);

		// the imported declaration's fields win
		expect(content).to.include(expectedExpansion);
		// the unrelated same-named type's fields stay out
		expect(content).to.not.include('fieldOne');
		expect(content).to.not.include('createdAt: Date');
		// an import anchors the name — no ambiguity, nothing fatal
		expect(analyzer.getResolutionErrors()).to.deep.equal([]);
	});

	it('writes the same expansion into .tactica/types.ts on disk', () => {
		const analyzer = new MnemonicaAnalyzer();
		analyzeFiles(
			analyzer,
			importedDeclFile,
			unrelatedFile,
			path.join(fixtureRoot, 'consumers', 'primary.types.ts')
		);

		const outputDir = path.join(__dirname, '.test-f10-output');
		try {
			const writer = new TypesWriter(outputDir);
			writer.writeTypesFile(generateTypes(analyzer));
			const written = fs.readFileSync(path.join(outputDir, 'types.ts'), 'utf8');
			expect(written).to.include(expectedExpansion);
			expect(written).to.not.include('fieldOne');
		} finally {
			fs.rmSync(outputDir, { recursive : true, force : true });
		}
	});

	it('does not let a same-named in-scope local declaration shadow the import', () => {
		const analyzer = new MnemonicaAnalyzer();
		analyzeFiles(
			analyzer,
			importedDeclFile,
			unrelatedFile,
			path.join(fixtureRoot, 'consumers', 'local-shadow.types.ts')
		);

		const content = generateTypesContent(analyzer);
		expect(content).to.include(expectedExpansion);
		expect(content).to.not.include('localOnly');
	});

	it('resolves aliased imports through the original exported name', () => {
		const analyzer = new MnemonicaAnalyzer();
		analyzeFiles(
			analyzer,
			importedDeclFile,
			unrelatedFile,
			path.join(fixtureRoot, 'consumers', 'aliased-import.types.ts')
		);

		const content = generateTypesContent(analyzer);
		expect(content).to.include(expectedExpansion);
		// the alias must not leak as a bare unresolvable name
		expect(content).to.not.include('SharedShapeAlias');
	});

	it('emits unknown for a genuinely unresolvable reference, not a bare name', () => {
		const analyzer = new MnemonicaAnalyzer();
		analyzeFiles(
			analyzer,
			importedDeclFile,
			unrelatedFile,
			path.join(fixtureRoot, 'consumers', 'mystery.types.ts')
		);

		const content = generateTypesContent(analyzer);
		expect(content).to.include('thing: unknown');
		expect(content).to.not.include('NotImportedAnywhere');
		// a ghost name declares nowhere — absence stays soft, not fatal
		expect(analyzer.getResolutionErrors()).to.deep.equal([]);
	});

	it('is FATAL when same-named declarations are ambiguous with no import to disambiguate', () => {
		const analyzer = new MnemonicaAnalyzer();
		const ambiguousSource = `
import { define } from 'mnemonica';

export const Ambiguous = define('Ambiguous', function (
	this: Ambiguous,
	record: SharedShape
) {
	this.record = record;
});
`;
		// SharedShape exists in two files and this file imports neither
		analyzeFiles(analyzer, importedDeclFile, unrelatedFile);
		analyzer.analyzeSource(ambiguousSource, path.join(fixtureRoot, 'consumers', 'ambiguous.types.ts'));

		const content = generateTypesContent(analyzer);
		expect(content).to.include('record: unknown');

		const errors = analyzer.getResolutionErrors();
		expect(errors).to.have.length(1);
		expect(errors[ 0 ].message).to.include('Ambiguous reference to type \'SharedShape\'');
		expect(errors[ 0 ].message).to.include('no import disambiguates');
		expect(errors[ 0 ].message).to.include('import the one you mean');
		// the reference site plus EVERY declaration site
		expect(errors[ 0 ].locations).to.have.length(3);
		expect(errors[ 0 ].locations[ 0 ]).to.include('ambiguous.types.ts');
		expect(errors[ 0 ].locations.join(' ')).to.include(importedDeclFile);
		expect(errors[ 0 ].locations.join(' ')).to.include(unrelatedFile);
		// idempotent: a second call must not double-record
		expect(analyzer.getResolutionErrors()).to.have.length(1);
	});

	it('does not fatal when a package-declared same-named type collides with a user-local one', () => {
		const analyzer = new MnemonicaAnalyzer();
		// the user-local declaration — analyzed project source
		analyzeFiles(analyzer, importedDeclFile);
		// a node_modules .d.ts declaring the same name: the CLI never
		// analyzes these, but a programmatic caller could feed one — it
		// must not create fatality and the local declaration wins
		analyzer.analyzeSource(
			'export interface SharedShape { externalOnly: boolean; }',
			path.join(fixtureRoot, 'node_modules', 'some-pkg', 'index.d.ts')
		);
		analyzer.analyzeSource(`
import { define } from 'mnemonica';

export const LocalWins = define('LocalWins', function (this: LocalWins, record: SharedShape) {
	this.record = record;
});
`, path.join(fixtureRoot, 'consumers', 'local-wins.types.ts'));

		expect(analyzer.getResolutionErrors()).to.deep.equal([]);
		const content = generateTypesContent(analyzer);
		expect(content).to.include(expectedExpansion);
		expect(content).to.not.include('externalOnly');
	});

	it('does not fatal on same-file interface merging (last declaration wins)', () => {
		const analyzer = new MnemonicaAnalyzer();
		// two same-named interfaces in ONE module are legal TypeScript
		// merging, not ambiguity — tactica keeps one declaration per name
		// per file (last wins; documented known limitation)
		analyzer.analyzeSource(`
export interface SharedShape { a: string; }
export interface SharedShape { b: number; }
`, path.join(fixtureRoot, 'shape-c', 'merged-shape.ts'));
		analyzer.analyzeSource(`
import { define } from 'mnemonica';

export const Merged = define('Merged', function (this: Merged, record: SharedShape) {
	this.record = record;
});
`, path.join(fixtureRoot, 'consumers', 'merged.types.ts'));

		expect(analyzer.getResolutionErrors()).to.deep.equal([]);
		const content = generateTypesContent(analyzer);
		expect(content).to.include('record: { b: number }');
	});

	describe('qualified references through namespace imports', () => {
		const nestedDeclFile = path.join(fixtureRoot, 'shape-a', 'nested', 'crate-holder.ts');
		const nestTargetFile = path.join(fixtureRoot, 'shape-a', 'nested', 'gadget-nest.ts');
		const reExportFile = path.join(fixtureRoot, 'shape-a', 'nested', 'gadget-barrel.ts');

		it('expands a one-level qualified reference (models.SharedShape)', () => {
			const analyzer = new MnemonicaAnalyzer();
			analyzeFiles(
				analyzer,
				importedDeclFile,
				path.join(fixtureRoot, 'consumers', 'one-level-qualified.types.ts')
			);

			const content = generateTypesContent(analyzer);
			expect(content).to.include(expectedExpansion);
		});

		it('expands namespace-nested references precisely (holders.Inner.Crate vs holders.Outer.Crate)', () => {
			const analyzer = new MnemonicaAnalyzer();
			analyzeFiles(
				analyzer,
				nestedDeclFile,
				path.join(fixtureRoot, 'consumers', 'nested-qualified.types.ts')
			);

			const content = generateTypesContent(analyzer);
			// each consumer gets its own namespace's Crate — the middle
			// segment disambiguates; the qualified name never leaks bare
			expect(content).to.include('crate: { slot: number; tag: string }');
			expect(content).to.include('crate: { bay: string; level: number }');
			expect(content).to.not.include('holders.Inner.Crate');
			expect(content).to.not.include('Inner.Crate');
		});

		it('expands a reference behind an export * as ns barrel (barrel.Deep.Gadget)', () => {
			const analyzer = new MnemonicaAnalyzer();
			analyzeFiles(
				analyzer,
				nestTargetFile,
				reExportFile,
				path.join(fixtureRoot, 'consumers', 'namespace-reexport.types.ts')
			);

			const content = generateTypesContent(analyzer);
			expect(content).to.include('gadget: { power: number }');
			expect(content).to.not.include('Deep.Gadget');
		});
	});
});
/**
 * F13: import-anchored referenced-type expansion fidelity.
 * A — inherited members: class/interface extends chains are walked
 * (depth-capped, cycle-guarded) and parent fields merge into the
 * expansion, the declaration's own fields overriding on name clash.
 * B — `typeof` over a module-level non-exported const: a visible
 * array literal expands to its element literal union; anything else
 * degrades the field to `unknown`. A bare `typeof name` is never
 * emitted into generated types.ts (the file carries no imports).
 */
describe('Referenced type expansion fidelity (F13)', () => {
	const fixtureRoot = path.join(__dirname, 'fixtures', 'referenced-expansion');
	const modelsFile = path.join(fixtureRoot, 'src', 'models.ts');
	const consumerFile = path.join(fixtureRoot, 'src', 'consumer.ts');

	const analyzeFixture = (): MnemonicaAnalyzer => {
		const analyzer = new MnemonicaAnalyzer();
		analyzer.analyzeSource(fs.readFileSync(modelsFile, 'utf8'), modelsFile);
		analyzer.analyzeSource(fs.readFileSync(consumerFile, 'utf8'), consumerFile);
		return analyzer;
	};

	const generateContent = (analyzer: MnemonicaAnalyzer): string => {
		const generator = new TypesGenerator(analyzer.getGraph());
		const generated = generator.generateTypesFile();
		return generated.content;
	};

	it('expands inherited class members: parent fields merge, child shadow wins', () => {
		const analyzer = analyzeFixture();
		const content = generateContent(analyzer);

		// both the base's and the derived declaration's own fields
		expect(content).to.include('payload: { baseField: string; ownField: number }');
		// name clash: the derived declaration's field type wins
		expect(content).to.include('payload: { tag: number }');
		expect(content).to.not.include('tag: string');
	});

	it('expands interface extends chains the same way', () => {
		const analyzer = analyzeFixture();
		const content = generateContent(analyzer);

		expect(content).to.include('payload: { baseProp: string; ownProp: number }');
	});

	it('expands typeof over a non-exported const array to the literal union', () => {
		const analyzer = analyzeFixture();
		const content = generateContent(analyzer);

		expect(content).to.include('status?: \'active\' | \'closed\'');
		// the bare query must not leak anywhere in the generated file
		expect(content).to.not.include('typeof statusList');
		expect(content).to.not.include('statusList');
	});

	it('degrades non-literal and non-array typeof sources to unknown, never a bare query', () => {
		const analyzer = analyzeFixture();
		const content = generateContent(analyzer);

		expect(content).to.include('state?: unknown');
		expect(content).to.include('settings?: unknown');
		expect(content).to.not.include('typeof dynamicList');
		expect(content).to.not.include('typeof configObject');
		expect(content).to.not.include('dynamicList');
		expect(content).to.not.include('configObject');
	});

	describe('CLI end-to-end (tsc-clean generated output is the bar)', () => {
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

		it('runs the fixture, exits 0, and the generated types.ts compiles clean', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-referenced-expansion-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(0);
				expect(errors).to.equal('');

				const typesPath = path.join(outputDir, 'types.ts');
				const content = fs.readFileSync(typesPath, 'utf8');
				expect(content).to.include('payload: { baseField: string; ownField: number }');
				expect(content).to.include('status?: \'active\' | \'closed\'');
				expect(content).to.not.include('typeof');
				expect(content).to.not.include('statusList');
				expect(content).to.not.include('dynamicList');
				expect(content).to.not.include('configObject');

				// compile the generated file for real — the field report was
				// downstream TS errors from the bare typeof leak
				const mnemonicaTypes = path.join(__dirname, '..', 'node_modules', 'mnemonica', 'build', 'index.d.ts');
				const program = ts.createProgram([ typesPath ], {
					strict           : true,
					noEmit           : true,
					target           : ts.ScriptTarget.ES2020,
					module           : ts.ModuleKind.ES2020,
					moduleResolution : ts.ModuleResolutionKind.Bundler,
					baseUrl          : outputDir,
					paths            : { mnemonica : [ mnemonicaTypes ] },
				});
				const diagnostics = ts.getPreEmitDiagnostics(program);
				const compileErrors = diagnostics
					.filter(d => d.category === ts.DiagnosticCategory.Error)
					.map(d => `TS${d.code}: ${ts.flattenDiagnosticMessageText(d.messageText, ' ')}`);

				expect(compileErrors).to.deep.equal([]);
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		}).timeout(20000);
	});
});

/**
 * F14 regression: named-alias constructor params and the annotation
 * merge guard. Field pattern (six consumer apps, 0.1.9 → 0.3.7):
 *   interface PackFiles { header: PackHeader | null; info: Record<string, unknown> }
 *   define('Pack', function (this: PackData, pageFiles: PackFiles) {
 *       this.header = pageFiles.header;
 *       this.info   = pageFiles.info;
 *   });
 * 0.3.7 emitted `header: unknown; info: unknown`. Two root causes:
 *   1. buildDataTypeMap only decomposed INLINE type literals, so
 *      `this.x = param.y` never resolved per-property types for a named
 *      alias/interface param — now routed through the import-aware
 *      declaration machinery (F10) including the heritage walk (F13).
 *   2. the don't-clobber guard treated `Record<string, unknown>` (a good
 *      annotation) as unknown-bearing via a substring match, so inferred
 *      `unknown` overwrote it together with the optionality modifier —
 *      the guard now fires only when the existing type IS `unknown`
 *      (exact whole-type match), and a known overwrite keeps optionality.
 */
describe('Named-parameter property inference regression (F14)', () => {
	const fixtureRoot = path.join(__dirname, 'fixtures', 'referenced-f14');
	const modelsFile = path.join(fixtureRoot, 'src', 'models.ts');
	const consumerFile = path.join(fixtureRoot, 'src', 'consumer.ts');

	it('extracts Object.assign(this, data) fields from the data param\'s type (F21)', () => {
		const analyzer = new MnemonicaAnalyzer();
		analyzer.analyzeSource(`
import { define } from 'mnemonica';

export const Vault = define('Vault', function (this: Vault, args: { code: string; amount: number }) {
	Object.assign(this, args);
});
`, path.join(__dirname, 'fixtures', 'referenced-types', 'consumers', 'assign-identifier.types.ts'));

		const generator = new TypesGenerator(analyzer.getGraph());
		const { content } = generator.generateTypesFile();
		expect(content).to.include('code: string;');
		expect(content).to.include('amount: number;');
	});

	const analyzeFixture = (): MnemonicaAnalyzer => {
		const analyzer = new MnemonicaAnalyzer();
		analyzer.analyzeSource(fs.readFileSync(modelsFile, 'utf8'), modelsFile);
		analyzer.analyzeSource(fs.readFileSync(consumerFile, 'utf8'), consumerFile);
		return analyzer;
	};

	const generateContent = (analyzer: MnemonicaAnalyzer): string => {
		const generator = new TypesGenerator(analyzer.getGraph());
		const generated = generator.generateTypesFile();
		return generated.content;
	};

	it('resolves this.x = param.y per-property types through named alias/interface params', () => {
		const analyzer = analyzeFixture();
		const content = generateContent(analyzer);

		// interface param: named members resolve through the import-aware
		// machinery — no `unknown`, no bare names
		expect(content).to.include('header: { title: string } | null');
		expect(content).to.include('info: Record<string, unknown>');
		expect(content).to.not.include('header: unknown');
		expect(content).to.not.include('info: unknown');
		// alias param decomposes the same way
		expect(content).to.include('note: string');
		expect(content).to.include('weight: number');
		// bare names never leak into the generated file
		expect(content).to.not.include('pageFiles');
		expect(content).to.not.include('PackHeader');
		expect(content).to.not.include('PackFiles');
		expect(content).to.not.include('PackMeta');
	});

	it('keeps the annotated Record<string, unknown> field and its optionality', () => {
		const analyzer = analyzeFixture();
		const content = generateContent(analyzer);

		// unknown-bearing inference must not clobber the good annotation,
		// and the `?` modifier must survive
		expect(content).to.include('data?: Record<string, unknown>');
		expect(content).to.not.include('data: unknown');
		expect(analyzer.getResolutionErrors()).to.deep.equal([]);
	});

	describe('CLI end-to-end (resolved types + optionality in generated output)', () => {
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

		it('runs the fixture, exits 0, and the generated types.ts compiles clean', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-referenced-f14-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(0);
				expect(errors).to.equal('');

				const typesPath = path.join(outputDir, 'types.ts');
				const content = fs.readFileSync(typesPath, 'utf8');
				expect(content).to.include('header: { title: string } | null');
				expect(content).to.include('info: Record<string, unknown>');
				expect(content).to.include('data?: Record<string, unknown>');
				expect(content).to.not.include('unknown;');

				// compile the generated file for real — the field regression
				// was downstream consumer TS errors
				const mnemonicaTypes = path.join(__dirname, '..', 'node_modules', 'mnemonica', 'build', 'index.d.ts');
				const program = ts.createProgram([ typesPath ], {
					strict           : true,
					noEmit           : true,
					target           : ts.ScriptTarget.ES2020,
					module           : ts.ModuleKind.ES2020,
					moduleResolution : ts.ModuleResolutionKind.Bundler,
					baseUrl          : outputDir,
					paths            : { mnemonica : [ mnemonicaTypes ] },
				});
				const diagnostics = ts.getPreEmitDiagnostics(program);
				const compileErrors = diagnostics
					.filter(d => d.category === ts.DiagnosticCategory.Error)
					.map(d => `TS${d.code}: ${ts.flattenDiagnosticMessageText(d.messageText, ' ')}`);

				expect(compileErrors).to.deep.equal([]);
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		}).timeout(20000);
	});
});

/**
 * F15/F16/F17: typeof const-array literal-union expansion edge cases.
 *   F15 — the union consumes the index suffix entirely: `typeof arr[number]`
 *         emits exactly `'a' | 'b'`, never `'a' | 'b'[number]` (the suffix
 *         would degrade the last member to `string`).
 *   F16 — unary-minus/plus numeric literals keep their sign: `-1 | 1`.
 *   F17 — the angle-bracket `<const>[…]` spelling is tracked like
 *         `[…] as const`; and the emission invariant: an index suffix is
 *         NEVER glued onto an unresolved/fallback target — `unknown[number]`
 *         is invalid TypeScript, so the whole indexed access degrades to
 *         `unknown`.
 */
describe('typeof const-array union edge cases (F15/F16/F17)', () => {
	const fixtureRoot = path.join(__dirname, 'fixtures', 'referenced-unions');
	const modelsFile = path.join(fixtureRoot, 'src', 'models.ts');
	const consumerFile = path.join(fixtureRoot, 'src', 'consumer.ts');

	const analyzeFixture = (): MnemonicaAnalyzer => {
		const analyzer = new MnemonicaAnalyzer();
		analyzer.analyzeSource(fs.readFileSync(modelsFile, 'utf8'), modelsFile);
		analyzer.analyzeSource(fs.readFileSync(consumerFile, 'utf8'), consumerFile);
		return analyzer;
	};

	const generateContent = (analyzer: MnemonicaAnalyzer): string => {
		const generator = new TypesGenerator(analyzer.getGraph());
		const generated = generator.generateTypesFile();
		return generated.content;
	};

	it('emits the as-const union consuming the index suffix entirely (F15)', () => {
		const analyzer = analyzeFixture();
		const content = generateContent(analyzer);

		expect(content).to.include('status: \'active\' | \'not_active\' | \'hold\'');
		expect(content).to.not.include('\'hold\'[number]');
		expect(content).to.not.include('statusList');
	});

	it('tracks the angle-bracket <const>[…] spelling like as const (F17)', () => {
		const analyzer = analyzeFixture();
		const content = generateContent(analyzer);

		expect(content).to.include('tier: \'low\' | \'high\'');
		expect(content).to.not.include('tierList');
	});

	it('preserves unary-minus numeric literals in the union (F16)', () => {
		const analyzer = analyzeFixture();
		const content = generateContent(analyzer);

		expect(content).to.include('level: -1 | 1');
		expect(content).to.not.include('unknown | 1');
	});

	it('degrades unresolved indexed-access targets to unknown, never unknown[number] (F17)', () => {
		const analyzer = analyzeFixture();
		const content = generateContent(analyzer);

		expect(content).to.include('ghost: unknown');
		expect(content).to.include('broken: unknown');
		expect(content).to.include('keyed: unknown');
		// the invariant: no index suffix may survive on a fallback type
		expect(content).to.not.include('unknown[');
		expect(analyzer.getResolutionErrors()).to.deep.equal([]);
	});

	describe('CLI end-to-end (valid generated TypeScript is the bar)', () => {
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

		it('runs the fixture, exits 0, and the generated types.ts compiles clean', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-referenced-unions-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(0);
				expect(errors).to.equal('');

				const typesPath = path.join(outputDir, 'types.ts');
				const content = fs.readFileSync(typesPath, 'utf8');
				expect(content).to.include('status: \'active\' | \'not_active\' | \'hold\'');
				expect(content).to.include('tier: \'low\' | \'high\'');
				expect(content).to.include('level: -1 | 1');
				expect(content).to.not.include('unknown[');

				// compile the generated file for real — `unknown[number]`
				// was a hard compile break for every consumer (F17)
				const mnemonicaTypes = path.join(__dirname, '..', 'node_modules', 'mnemonica', 'build', 'index.d.ts');
				const program = ts.createProgram([ typesPath ], {
					strict           : true,
					noEmit           : true,
					target           : ts.ScriptTarget.ES2020,
					module           : ts.ModuleKind.ES2020,
					moduleResolution : ts.ModuleResolutionKind.Bundler,
					baseUrl          : outputDir,
					paths            : { mnemonica : [ mnemonicaTypes ] },
				});
				const diagnostics = ts.getPreEmitDiagnostics(program);
				const compileErrors = diagnostics
					.filter(d => d.category === ts.DiagnosticCategory.Error)
					.map(d => `TS${d.code}: ${ts.flattenDiagnosticMessageText(d.messageText, ' ')}`);

				expect(compileErrors).to.deep.equal([]);
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		}).timeout(20000);
	});
});
