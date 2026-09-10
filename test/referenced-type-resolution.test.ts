'use strict';

import { expect } from 'chai';
import * as fs from 'fs';
import * as path from 'path';
import { MnemonicaAnalyzer } from '../src/analyzer';
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
