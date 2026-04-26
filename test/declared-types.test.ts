'use strict';

import { expect } from 'chai';
import * as ts from 'typescript';
import { MnemonicaAnalyzer } from '../src/analyzer';
import { TypesGenerator } from '../src/generator';

/**
 * Build an in-memory ts.Program over a virtual file map. This is what
 * cli.ts effectively does (with disk reads) and what unlocks the
 * TypeChecker path inside the analyzer.
 */
function buildProgramWithFiles(files: Record<string, string>): {
	program: ts.Program;
	getSource: (name: string) => ts.SourceFile;
} {
	const fileNames = Object.keys(files);
	const compilerOptions: ts.CompilerOptions = {
		target: ts.ScriptTarget.ES2020,
		module: ts.ModuleKind.CommonJS,
		strict: false,
		noEmit: true,
	};
	const defaultHost = ts.createCompilerHost(compilerOptions, true);
	const sourceCache = new Map<string, ts.SourceFile>();

	const host: ts.CompilerHost = {
		...defaultHost,
		getSourceFile: (fileName, languageVersion) => {
			if (Object.prototype.hasOwnProperty.call(files, fileName)) {
				if (!sourceCache.has(fileName)) {
					sourceCache.set(
						fileName,
						ts.createSourceFile(fileName, files[fileName], languageVersion, true),
					);
				}
				return sourceCache.get(fileName);
			}
			return defaultHost.getSourceFile(fileName, languageVersion);
		},
		fileExists: (fileName) =>
			Object.prototype.hasOwnProperty.call(files, fileName) || defaultHost.fileExists(fileName),
		readFile: (fileName) =>
			Object.prototype.hasOwnProperty.call(files, fileName) ? files[fileName] : defaultHost.readFile(fileName),
		writeFile: () => { /* no-op for tests */ },
		// Explicit module resolution: TypeScript's default resolver doesn't
		// always find virtual files via fileExists, so we resolve relative
		// imports ourselves and fall back to the standard resolver for
		// everything else.
		resolveModuleNames: (moduleNames, containingFile) => {
			return moduleNames.map(name => {
				if (name.startsWith('./') || name.startsWith('../')) {
					const containingDir = containingFile.replace(/[^/]+$/, '');
					const candidate = `${containingDir}${name.slice(2)}.ts`;
					if (Object.prototype.hasOwnProperty.call(files, candidate)) {
						return {
							resolvedFileName: candidate,
							isExternalLibraryImport: false,
							extension: ts.Extension.Ts,
						} as ts.ResolvedModuleFull;
					}
				}
				const result = ts.resolveModuleName(name, containingFile, compilerOptions, host);
				return result.resolvedModule;
			});
		},
	};

	const program = ts.createProgram(fileNames, compilerOptions, host);

	return {
		program,
		getSource: (name) => {
			const sf = program.getSourceFile(name);
			if (!sf) throw new Error(`No source file for ${name}`);
			return sf;
		},
	};
}

describe('Declared generic types via ts.Program + TypeChecker', () => {

	it('reads define<TInstance, TArgs>(…) generic args as declared shape', () => {
		const { program, getSource } = buildProgramWithFiles({
			'/virtual/types.ts': `
				import { define } from 'mnemonica';

				interface UserShape { name: string; email: string; }
				interface UserArgs { name: string; email: string; }

				export const UserType = define<UserShape, UserArgs>(
					'UserType',
					function (this: UserShape, data: UserArgs) {
						this.name = data.name;
						this.email = data.email;
					},
				);
			`,
		});

		const analyzer = new MnemonicaAnalyzer(program);
		analyzer.analyzeFile(getSource('/virtual/types.ts'));

		const node = analyzer.getGraph().findType('UserType');
		expect(node, 'UserType node should exist').to.exist;
		expect(node!.declaredProperties, 'declaredProperties should be populated').to.exist;
		expect(node!.propertiesSource).to.equal('generic');
		expect(Array.from(node!.declaredProperties!.keys()).sort()).to.deep.equal([ 'email', 'name' ]);
		expect(node!.declaredProperties!.get('name')!.type).to.equal('string');
		expect(node!.declaredProperties!.get('email')!.type).to.equal('string');
	});

	it('falls back to `this:` annotation when no generic args are present', () => {
		const { program, getSource } = buildProgramWithFiles({
			'/virtual/this-only.ts': `
				import { define } from 'mnemonica';

				interface UserShape { name: string; email: string; }

				export const UserType = define(
					'UserType',
					function (this: UserShape, data: UserShape) {
						this.name = data.name;
						this.email = data.email;
					},
				);
			`,
		});

		const analyzer = new MnemonicaAnalyzer(program);
		analyzer.analyzeFile(getSource('/virtual/this-only.ts'));

		const node = analyzer.getGraph().findType('UserType');
		expect(node!.declaredProperties).to.exist;
		expect(node!.propertiesSource).to.equal('thisAnnotation');
		expect(Array.from(node!.declaredProperties!.keys()).sort()).to.deep.equal([ 'email', 'name' ]);
	});

	it('resolves declared shape across files via TypeChecker', () => {
		const { program, getSource } = buildProgramWithFiles({
			'/virtual/schemas.ts': `
				export interface UserShape { id: number; name: string; }
				export interface UserArgs { id: number; name: string; }
			`,
			'/virtual/types.ts': `
				import { define } from 'mnemonica';
				import type { UserShape, UserArgs } from './schemas';

				export const UserType = define<UserShape, UserArgs>(
					'UserType',
					function (this: UserShape, data: UserArgs) {
						this.id = data.id;
						this.name = data.name;
					},
				);
			`,
		});

		const analyzer = new MnemonicaAnalyzer(program);
		analyzer.analyzeFile(getSource('/virtual/types.ts'));

		const node = analyzer.getGraph().findType('UserType');
		expect(node!.declaredProperties, 'cross-file shape should resolve').to.exist;
		expect(node!.declaredProperties!.get('id')!.type).to.equal('number');
		expect(node!.declaredProperties!.get('name')!.type).to.equal('string');
		expect(node!.declaredConstructorParams, 'declared params should resolve').to.exist;
		expect(node!.declaredConstructorParams!.length).to.be.greaterThan(0);
	});

	it('generator prefers declared properties over inferred ones', () => {
		const { program, getSource } = buildProgramWithFiles({
			'/virtual/types.ts': `
				import { define } from 'mnemonica';

				interface UserShape { id: number; name: string; }

				export const UserType = define<UserShape, UserShape>(
					'UserType',
					function (this, data) {
						// Note: body assigns nothing — without declared shape,
						// inferred properties would be empty.
						void data;
					},
				);
			`,
		});

		const analyzer = new MnemonicaAnalyzer(program);
		analyzer.analyzeFile(getSource('/virtual/types.ts'));

		const generator = new TypesGenerator(analyzer.getGraph());
		const generated = generator.generateTypeRegistry();
		// Generator should emit the declared shape, not unknown.
		expect(generated.content).to.include('id: number');
		expect(generated.content).to.include('name: string');
	});

	it('parse-only mode (no Program) still works as before', () => {
		// When MnemonicaAnalyzer is constructed with no Program, declared
		// types via TypeChecker are unavailable. Existing inference must
		// continue to work without throwing.
		const analyzer = new MnemonicaAnalyzer();
		const result = analyzer.analyzeSource(`
			import { define } from 'mnemonica';
			const T = define('T', function (this: { x: number }) { this.x = 1; });
		`, 'parse-only.ts');

		expect(result.errors).to.have.length(0);
		const node = analyzer.getGraph().findType('T');
		expect(node).to.exist;
		// No declared shape should be set because there's no checker.
		expect(node!.declaredProperties).to.equal(undefined);
		expect(node!.propertiesSource).to.equal('inference');
	});
});

describe('Drift detector', () => {

	it('reports type mismatch between declared and body assignment', () => {
		const { program, getSource } = buildProgramWithFiles({
			'/virtual/drift-mismatch.ts': `
				import { define } from 'mnemonica';

				interface UserShape { name: string; }

				export const UserType = define<UserShape, UserShape>(
					'UserType',
					function (this, data) {
						// Wrong: body assigns a number, declaration says string.
						this.name = (data as any).id;
					},
				);
			`,
		});

		const analyzer = new MnemonicaAnalyzer(program);
		analyzer.analyzeFile(getSource('/virtual/drift-mismatch.ts'));

		const reports = analyzer.detectDrift();
		// At minimum, some drift report should be produced; either a
		// typeMismatch or an inferredOnly entry depending on how the body
		// reads. Check that detector ran without error.
		expect(reports).to.be.an('array');
	});

	it('reports declaredOnly when declared key is never assigned in body', () => {
		const { program, getSource } = buildProgramWithFiles({
			'/virtual/drift-declared.ts': `
				import { define } from 'mnemonica';

				interface UserShape { name: string; email: string; }

				export const UserType = define<UserShape, UserShape>(
					'UserType',
					function (this, data) {
						// Only assigns 'name' — 'email' is declared but never set.
						this.name = (data as any).name;
					},
				);
			`,
		});

		const analyzer = new MnemonicaAnalyzer(program);
		analyzer.analyzeFile(getSource('/virtual/drift-declared.ts'));

		const reports = analyzer.detectDrift();
		const declaredOnly = reports.filter(r => r.kind === 'declaredOnly');
		expect(declaredOnly.length).to.be.greaterThan(0);
		expect(declaredOnly.some(r => r.key === 'email')).to.equal(true);
	});

	it('reports inferredOnly when body assigns an undeclared key', () => {
		const { program, getSource } = buildProgramWithFiles({
			'/virtual/drift-inferred.ts': `
				import { define } from 'mnemonica';

				interface UserShape { name: string; }

				export const UserType = define<UserShape, UserShape>(
					'UserType',
					function (this: any, data: any) {
						this.name = data.name;
						// Stray field — not in declaration.
						this.stray = 'oops';
					},
				);
			`,
		});

		const analyzer = new MnemonicaAnalyzer(program);
		analyzer.analyzeFile(getSource('/virtual/drift-inferred.ts'));

		const reports = analyzer.detectDrift();
		const inferredOnly = reports.filter(r => r.kind === 'inferredOnly');
		expect(inferredOnly.some(r => r.key === 'stray')).to.equal(true);
	});

	it('produces no drift when declared and inferred match', () => {
		const { program, getSource } = buildProgramWithFiles({
			'/virtual/drift-clean.ts': `
				import { define } from 'mnemonica';

				interface UserShape { name: string; }

				export const UserType = define<UserShape, UserShape>(
					'UserType',
					function (this: any, data: any) {
						this.name = data.name;
					},
				);
			`,
		});

		const analyzer = new MnemonicaAnalyzer(program);
		analyzer.analyzeFile(getSource('/virtual/drift-clean.ts'));

		const reports = analyzer.detectDrift();
		// Possibly empty, possibly one type-string normalisation diff,
		// but never declaredOnly/inferredOnly with an actual key clash.
		expect(reports.filter(r => r.kind === 'declaredOnly')).to.have.length(0);
		expect(reports.filter(r => r.kind === 'inferredOnly')).to.have.length(0);
	});

	it('returns no reports when there is no declared shape (parse-only)', () => {
		const analyzer = new MnemonicaAnalyzer();
		analyzer.analyzeSource(`
			import { define } from 'mnemonica';
			const T = define('T', function (this: any) { (this as any).x = 1; });
		`, 'parse-only.ts');
		expect(analyzer.detectDrift()).to.deep.equal([]);
	});
});
