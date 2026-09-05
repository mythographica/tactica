'use strict';

import { expect } from 'chai';
import * as path from 'path';
import * as ts from 'typescript';
import { ModuleGraphBuilder } from '../src/module-graph';
import { ModuleGraph, ModuleInfo } from '../src/types';

/**
 * Module-scope walker (Phase 1 of the instrumentation walker plan).
 * Fixtures live in test/fixtures/module-graph and are loaded through a real
 * tsconfig.json so module resolution (incl. the @app/* paths alias) matches
 * the CLI's behavior.
 */
describe('ModuleGraphBuilder', () => {
	const fixturesDir = path.join(__dirname, 'fixtures', 'module-graph');

	const fixturePath = (name: string): string => {
		const result = path.join(fixturesDir, name);
		return result;
	};

	let graph: ModuleGraph;

	const getModule = (name: string): ModuleInfo => {
		const moduleInfo = graph.modules.get(fixturePath(name));
		expect(moduleInfo, `module ${name} should be tracked`).to.exist;
		const result = moduleInfo as ModuleInfo;
		return result;
	};

	before(() => {
		const tsconfigPath = fixturePath('tsconfig.json');
		const configFile = ts.readConfigFile(tsconfigPath, ts.sys.readFile);
		const parsed = ts.parseJsonConfigFileContent(configFile.config, ts.sys, fixturesDir);
		const program = ts.createProgram({
			rootNames : parsed.fileNames,
			options   : parsed.options,
		});

		const builder = new ModuleGraphBuilder(program);
		for (const sourceFile of program.getSourceFiles()) {
			if (sourceFile.isDeclarationFile) {
				continue;
			}
			if (!path.resolve(sourceFile.fileName).startsWith(fixturesDir + path.sep)) {
				continue;
			}
			builder.addFile(sourceFile);
		}

		const definedTypesByFile = new Map<string, string[]>([
			[ fixturePath('defs.ts'), [ 'Thing', 'Thing.Admin' ] ],
		]);
		graph = builder.build(definedTypesByFile);
	});

	describe('module tracking', () => {
		it('should track all fixture modules', () => {
			const names = [
				'defs.ts', 'extra.ts', 'barrel.ts', 'classmod.ts',
				'consumer.ts', 'consumer-star.ts', 'circular-a.ts', 'circular-b.ts',
				'aliased.ts', 'cjs.js', 'broken.ts', 'builtins.ts',
			];
			for (const name of names) {
				getModule(name);
			}
		});

		it('should attach definedTypes from the definitions map', () => {
			const defs = getModule('defs.ts');
			expect(defs.definedTypes).to.deep.equal([ 'Thing', 'Thing.Admin' ]);
		});
	});

	describe('export kinds', () => {
		it('should classify exported functions, classes, consts and types', () => {
			const defs = getModule('defs.ts');
			const byName = new Map(defs.exportedBindings.map(b => [ b.name, b ]));

			expect(byName.get('makeThing')?.kind).to.equal('function');
			expect(byName.get('Thing')?.kind).to.equal('class');
			expect(byName.get('thingValue')?.kind).to.equal('const');
			expect(byName.get('ThingShape')?.kind).to.equal('type');
			expect(byName.get('ThingId')?.kind).to.equal('type');
		});

		it('should mark local exports with the module itself as sourceModule', () => {
			const defs = getModule('defs.ts');
			for (const binding of defs.exportedBindings) {
				expect(binding.isReExport).to.be.false;
				expect(binding.sourceModule).to.equal(fixturePath('defs.ts'));
			}
		});

		it('should record default exports under the name "default"', () => {
			const classmod = getModule('classmod.ts');
			const defaultExport = classmod.exportedBindings.find(b => b.name === 'default');
			expect(defaultExport).to.exist;
			expect(defaultExport?.kind).to.equal('class');
			expect(defaultExport?.importAlias).to.equal('DefaultWidget');
		});
	});

	describe('imports', () => {
		it('should record named imports with resolved absolute sourceModule', () => {
			const barrel = getModule('barrel.ts');
			const makeThing = barrel.importedBindings.find(b => b.name === 'makeThing');
			expect(makeThing).to.exist;
			expect(makeThing?.importKind).to.equal('named');
			expect(makeThing?.sourceModule).to.equal(fixturePath('defs.ts'));
		});

		it('should record default imports', () => {
			const consumer = getModule('consumer.ts');
			const widget = consumer.importedBindings.find(b => b.name === 'DefaultWidget');
			expect(widget).to.exist;
			expect(widget?.importKind).to.equal('default');
			expect(widget?.sourceModule).to.equal(fixturePath('classmod.ts'));
		});

		it('should backfill import kinds from the origin module', () => {
			const consumer = getModule('consumer.ts');
			const widget = consumer.importedBindings.find(b => b.name === 'DefaultWidget');
			expect(widget?.kind).to.equal('class');

			const thing = consumer.importedBindings.find(b => b.name === 'Thing');
			expect(thing?.kind).to.equal('class');
		});

		it('should record namespace imports', () => {
			const consumer = getModule('consumer.ts');
			const ns = consumer.importedBindings.find(b => b.importKind === 'namespace');
			expect(ns).to.exist;
			expect(ns?.name).to.equal('defs');
			expect(ns?.sourceModule).to.equal(fixturePath('defs.ts'));
		});

		it('should record aliased named imports with importAlias', () => {
			const barrel = getModule('barrel.ts');
			const renamed = barrel.importedBindings.find(b => b.name === 'RenamedShape');
			expect(renamed).to.exist;
			expect(renamed?.importAlias).to.equal('ThingShape');
		});

		it('should record require() calls with importKind require', () => {
			const cjs = getModule('cjs.js');
			const required = cjs.importedBindings.find(b => b.name === 'defs');
			expect(required).to.exist;
			expect(required?.importKind).to.equal('require');
			expect(required?.sourceModule).to.equal(fixturePath('defs.ts'));
		});
	});

	describe('re-exports (barrels)', () => {
		it('should mark re-exports with isReExport in both binding lists', () => {
			const barrel = getModule('barrel.ts');
			const exported = barrel.exportedBindings.find(b => b.name === 'Thing');
			const imported = barrel.importedBindings.find(b => b.name === 'Thing');
			expect(exported?.isReExport).to.be.true;
			expect(imported?.isReExport).to.be.true;
			expect(exported?.sourceModule).to.equal(fixturePath('defs.ts'));
		});

		it('should record `export * from` as a namespace re-export', () => {
			const barrel = getModule('barrel.ts');
			const star = barrel.exportedBindings.find(b => b.name === '*');
			expect(star).to.exist;
			expect(star?.importKind).to.equal('namespace');
			expect(star?.isReExport).to.be.true;
			expect(star?.sourceModule).to.equal(fixturePath('extra.ts'));
		});

		it('should chase re-export chains to the origin module for edges', () => {
			const consumerPath = fixturePath('consumer.ts');
			const defsPath = fixturePath('defs.ts');
			const edge = graph.edges.find(e =>
				e.usageModule === consumerPath && e.typePath === 'Thing');
			expect(edge).to.exist;
			expect(edge?.definitionModule).to.equal(defsPath);
			expect(edge?.usageLocation.startsWith(consumerPath)).to.be.true;
		});

		it('should chase through `export *` barrels', () => {
			const extraPath = fixturePath('extra.ts');
			const consumer = getModule('consumer-star.ts');
			const extraValue = consumer.importedBindings.find(b => b.name === 'extraValue');
			expect(extraValue?.kind).to.equal('const');

			const barrel = getModule('barrel.ts');
			expect(barrel.dependencies).to.include(extraPath);
			expect(consumer.dependencies).to.include(fixturePath('barrel.ts'));
		});
	});

	describe('module resolution', () => {
		it('should resolve tsconfig paths aliases (@app/*)', () => {
			const aliased = getModule('aliased.ts');
			const makeThing = aliased.importedBindings.find(b => b.name === 'makeThing');
			expect(makeThing).to.exist;
			expect(makeThing?.sourceModule).to.equal(fixturePath('defs.ts'));
			expect(makeThing?.kind).to.equal('function');
			expect(aliased.dependencies).to.include(fixturePath('defs.ts'));
		});

		it('should record unresolvable specifiers without failing', () => {
			const broken = getModule('broken.ts');
			expect(broken.unresolvedSpecifiers).to.deep.equal([ './does-not-exist' ]);
			const nothing = broken.importedBindings.find(b => b.name === 'nothing');
			expect(nothing?.sourceModule).to.equal('./does-not-exist');
		});

		it('should keep dependencies project-internal only', () => {
			const consumer = getModule('consumer.ts');
			expect(consumer.dependencies).to.include(fixturePath('barrel.ts'));
			expect(consumer.dependencies).to.include(fixturePath('classmod.ts'));
			expect(consumer.dependencies).to.include(fixturePath('defs.ts'));
			for (const dep of consumer.dependencies) {
				expect(dep.startsWith(fixturesDir)).to.be.true;
			}
		});
	});

	describe('node builtins and external packages', () => {
		it('should record node builtins in builtinSpecifiers only', () => {
			const builtins = getModule('builtins.ts');
			expect(builtins.builtinSpecifiers).to.deep.equal([ 'path', 'node:fs' ]);
			expect(builtins.unresolvedSpecifiers).to.deep.equal([]);
			// Builtins produce no bindings at all
			expect(builtins.importedBindings.find(b => b.name === 'path')).to.not.exist;
			expect(builtins.importedBindings.find(b => b.name === 'readFileSync')).to.not.exist;
			expect(builtins.dependencies).to.deep.equal([]);
		});

		it('should mark node_modules-resolved bindings as external', () => {
			const builtins = getModule('builtins.ts');
			const defineBinding = builtins.importedBindings.find(b => b.name === 'define');
			expect(defineBinding).to.exist;
			expect(defineBinding?.external).to.be.true;
			expect(defineBinding?.sourceModule).to.include('node_modules');
			// Externals never enter dependencies
			for (const dep of builtins.dependencies) {
				expect(dep).to.not.include('node_modules');
			}
		});
	});

	describe('circular imports', () => {
		it('should record the circular pair as a cycle, not an error', () => {
			const aPath = fixturePath('circular-a.ts');
			const bPath = fixturePath('circular-b.ts');

			const cycle = graph.cycles.find(c => c.includes(aPath) && c.includes(bPath));
			expect(cycle, 'cycle containing circular-a and circular-b').to.exist;
		});

		it('should still record dependencies both ways', () => {
			expect(getModule('circular-a.ts').dependencies).to.include(fixturePath('circular-b.ts'));
			expect(getModule('circular-b.ts').dependencies).to.include(fixturePath('circular-a.ts'));
		});
	});

	describe('re-adding files', () => {
		it('should replace a module record when the file is added again', () => {
			const builder = new ModuleGraphBuilder();
			const code = 'export const x = 1;\n';
			const fileName = fixturePath('virtual.ts');

			const first = ts.createSourceFile(fileName, code, ts.ScriptTarget.Latest, true);
			builder.addFile(first);
			const second = ts.createSourceFile(fileName, code + code, ts.ScriptTarget.Latest, true);
			builder.addFile(second);

			const built = builder.build();
			const moduleInfo = built.modules.get(path.resolve(fileName));
			// 2 = the second file's own two declarations; 3 would mean the
			// first add's record leaked into the second
			expect(moduleInfo?.exportedBindings.filter(b => b.name === 'x')).to.have.length(2);
		});
	});

	describe('inline sources (no program, no tsconfig)', () => {
		// Virtual files are not on disk, so specifiers never resolve here:
		// these tests cover binding collection and the unresolved path.
		const buildInline = (files: Record<string, string>): ModuleGraph => {
			const builder = new ModuleGraphBuilder(undefined, { module : ts.ModuleKind.CommonJS });
			for (const [ name, code ] of Object.entries(files)) {
				const sourceFile = ts.createSourceFile(fixturePath(name), code, ts.ScriptTarget.Latest, true);
				builder.addFile(sourceFile);
			}
			const result = builder.build();
			return result;
		};

		it('should classify every exported declaration kind from inline source', () => {
			const code = [
				'export function makeThing (): string { return \'x\'; }',
				'export class Thing {}',
				'export const answer = 42;',
				'export const handler = (): number => 1;',
				'export const Widget = class {};',
				'export interface Shape { name: string; }',
				'export type Id = string;',
				'export default class DefaultThing {}',
				'',
			].join('\n');

			const built = buildInline({ 'inline-defs.ts' : code });
			const moduleInfo = built.modules.get(fixturePath('inline-defs.ts'));
			const byName = new Map(moduleInfo?.exportedBindings.map(b => [ b.name, b ]));

			expect(byName.get('makeThing')?.kind).to.equal('function');
			expect(byName.get('Thing')?.kind).to.equal('class');
			expect(byName.get('answer')?.kind).to.equal('const');
			expect(byName.get('handler')?.kind).to.equal('function');
			expect(byName.get('Widget')?.kind).to.equal('class');
			expect(byName.get('Shape')?.kind).to.equal('type');
			expect(byName.get('Id')?.kind).to.equal('type');
			expect(byName.get('default')?.kind).to.equal('class');
			expect(byName.get('default')?.importAlias).to.equal('DefaultThing');
		});

		it('should record import bindings and keep raw specifiers when unresolvable', () => {
			const code = [
				'import DefaultThing, { makeThing as mk, Shape } from \'./inline-defs\';',
				'import * as helpers from \'./inline-defs\';',
				'',
				'void DefaultThing; void mk; void helpers;',
				'const shape: Shape = { name: \'s\' };',
				'export const consumed = shape;',
				'',
			].join('\n');

			const built = buildInline({ 'inline-consumer.ts' : code });
			const moduleInfo = built.modules.get(fixturePath('inline-consumer.ts'));

			expect(moduleInfo?.unresolvedSpecifiers).to.deep.equal([ './inline-defs' ]);

			const mk = moduleInfo?.importedBindings.find(b => b.name === 'mk');
			expect(mk?.importKind).to.equal('named');
			expect(mk?.importAlias).to.equal('makeThing');
			// No resolution → raw specifier kept, kind stays unknown
			expect(mk?.sourceModule).to.equal('./inline-defs');
			expect(mk?.kind).to.equal('unknown');

			const def = moduleInfo?.importedBindings.find(b => b.name === 'DefaultThing');
			expect(def?.importKind).to.equal('default');

			const ns = moduleInfo?.importedBindings.find(b => b.name === 'helpers');
			expect(ns?.importKind).to.equal('namespace');

			expect(moduleInfo?.dependencies).to.deep.equal([]);
		});
	});
});
