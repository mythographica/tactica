'use strict';

import { expect } from 'chai';
import * as path from 'path';
import * as ts from 'typescript';
import { MnemonicaAnalyzer } from '../src/analyzer';
import { ModuleGraphBuilder } from '../src/module-graph';
import { LocalScopeWalker, ScopeTypeResolver } from '../src/scopes';
import { CreationGraphBuilder } from '../src/creation-graph';
import {
	CreationGraph, ModuleGraph, ScopeAnalysis, UsageInfo
} from '../src/types';

/**
 * Inside-out creation walker (Phase 3 of the instrumentation walker plan).
 * The fixture program is loaded through a real tsconfig.json so module
 * resolution matches the CLI; the pipeline mirrors cli.ts run(): definitions
 * pass, usages pass, scopes build, holderScopeId attachment, module graph,
 * then the creation walk.
 */
describe('CreationGraphBuilder', () => {
	const fixturesDir = path.join(__dirname, 'fixtures', 'creation-graph');

	const fixturePath = (name: string): string => {
		const result = path.join(fixturesDir, name);
		return result;
	};

	let graph: CreationGraph;
	let scopeAnalysis: ScopeAnalysis;
	let moduleGraph: ModuleGraph;

	const findNode = (scopeId: string) => {
		const result = graph.nodes.find(node => node.scopeId === scopeId);
		return result;
	};

	const hasEdge = (caller: string, callee: string): boolean => {
		const result = graph.edges.some(edge => edge.caller === caller && edge.callee === callee);
		return result;
	};

	const findAnchor = (location: string) => {
		const result = graph.anchors.find(anchor => anchor.location === location);
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

		const sourceFiles: ts.SourceFile[] = [];
		for (const sourceFile of program.getSourceFiles()) {
			if (sourceFile.isDeclarationFile) {
				continue;
			}
			if (!path.resolve(sourceFile.fileName).startsWith(fixturesDir + path.sep)) {
				continue;
			}
			sourceFiles.push(sourceFile);
		}

		const analyzer = new MnemonicaAnalyzer(program);
		const moduleGraphBuilder = new ModuleGraphBuilder(program);
		for (const sourceFile of sourceFiles) {
			analyzer.analyzeFile(sourceFile);
			moduleGraphBuilder.addFile(sourceFile);
		}
		analyzer.resetUsages();
		for (const sourceFile of sourceFiles) {
			analyzer.analyzeFile(sourceFile);
		}

		const definitions = new Map(analyzer.getDefinitions());
		const usages = new Map(analyzer.getUsages());

		const scopeWalker = new LocalScopeWalker();
		for (const sourceFile of sourceFiles) {
			scopeWalker.addFile(sourceFile);
		}
		const scopeResolver: ScopeTypeResolver = {
			resolveByName : (name: string): string | undefined => {
				if (definitions.has(name)) {
					return name;
				}
				let found: string | undefined;
				for (const [ fullPath, definition ] of definitions) {
					if (definition.name !== name) {
						continue;
					}
					if (found) {
						return undefined;
					}
					found = fullPath;
				}
				return found;
			},
			hasPath : (fullPath: string): boolean => {
				const result = definitions.has(fullPath);
				return result;
			},
		};
		scopeAnalysis = scopeWalker.build(scopeResolver);
		LocalScopeWalker.attachHolderScopeIds(usages, scopeWalker);

		const definedTypesByFile = new Map<string, string[]>();
		for (const [ fullPath, definition ] of definitions) {
			const { location } = definition;
			const lastColon = location.lastIndexOf(':');
			const prevColon = location.lastIndexOf(':', lastColon - 1);
			const file = path.resolve(location.slice(0, prevColon));
			const list = definedTypesByFile.get(file) ?? [];
			list.push(fullPath);
			definedTypesByFile.set(file, list);
		}
		moduleGraph = moduleGraphBuilder.build(definedTypesByFile);

		const sourceFilesByPath = new Map<string, ts.SourceFile>();
		for (const sourceFile of sourceFiles) {
			sourceFilesByPath.set(path.resolve(sourceFile.fileName), sourceFile);
		}

		const builder = new CreationGraphBuilder(moduleGraph, scopeAnalysis, scopeWalker, sourceFilesByPath);
		graph = builder.build(usages);
	});

	describe('anchors (one per instantiation usage)', () => {
		it('should anchor every fixture creation site to its holder scope', () => {
			expect(graph.anchors).to.have.length(7);
			for (const anchor of graph.anchors) {
				expect(anchor.typePath).to.equal('Thing');
			}
		});

		it('should record the constructor expression text used at each site (decision 1)', () => {
			expect(findAnchor(fixturePath('service.ts:4:16'))?.constructorText).to.equal('Thing');
			// lookup alias: the alias name is the constructor actually used
			expect(findAnchor(fixturePath('lookup-alias.ts:6:15'))?.constructorText).to.equal('T2');
			// value-registered class: the method body is the creation site
			expect(findAnchor(fixturePath('wired.ts:5:16'))?.constructorText).to.equal('Thing');
		});

		it('should bind anchors to the same-line variable (documented heuristic)', () => {
			expect(findAnchor(fixturePath('service.ts:4:16'))?.variable).to.equal('thing');
			expect(findAnchor(fixturePath('local.ts:4:16'))?.variable).to.equal('local');
		});
	});

	describe('the inside-out walk', () => {
		it('should walk cross-file through a re-export barrel to the caller', () => {
			// consumer.ts imports makeThing through barrel.ts (export … from)
			expect(hasEdge(fixturePath('consumer.ts:3:1'), fixturePath('service.ts:3:1'))).to.be.true;
			expect(findNode(fixturePath('service.ts:3:1'))?.name).to.equal('makeThing');
			expect(findNode(fixturePath('consumer.ts:3:1'))?.name).to.equal('run');
		});

		it('should walk same-file callers of a non-exported holder', () => {
			// buildLocal is not exported; entry() calls it inside local.ts
			expect(hasEdge(fixturePath('local.ts:8:1'), fixturePath('local.ts:3:1'))).to.be.true;
		});

		it('should reach main.ts as a starter (the plan\'s PoC criterion)', () => {
			const mainModule = findNode(fixturePath('main.ts'));
			expect(mainModule).to.exist;
			expect(mainModule?.kind).to.equal('module');
			expect(mainModule?.starter).to.be.true;
			// main calls run/entry/pingB/makeViaLookup/reassignThing at top level
			expect(hasEdge(fixturePath('main.ts'), fixturePath('consumer.ts:3:1'))).to.be.true;
			expect(hasEdge(fixturePath('main.ts'), fixturePath('local.ts:8:1'))).to.be.true;
			expect(hasEdge(fixturePath('main.ts'), fixturePath('cyc-b.ts:3:1'))).to.be.true;
			expect(hasEdge(fixturePath('main.ts'), fixturePath('lookup-alias.ts:5:1'))).to.be.true;
			expect(hasEdge(fixturePath('main.ts'), fixturePath('service.ts:8:1'))).to.be.true;
		});

		it('should mark only caller-less nodes as starters', () => {
			const starters = graph.nodes.filter(node => node.starter).map(node => node.scopeId);
			expect(starters.sort()).to.deep.equal([ fixturePath('main.ts'), fixturePath('rooted.ts') ].sort());
		});

		it('should label module-scope creations as rooted instances', () => {
			const rooted = findAnchor(fixturePath('rooted.ts:3:28'));
			expect(rooted).to.exist;
			expect(rooted?.rooted).to.be.true;
			expect(rooted?.holderScopeId).to.equal(fixturePath('rooted.ts'));
		});

		it('should terminate on import cycles and record both directions', () => {
			// pingA (cyc-a) calls pingB (cyc-b) and vice versa — the walk ends
			expect(hasEdge(fixturePath('cyc-a.ts:9:1'), fixturePath('cyc-b.ts:3:1'))).to.be.true;
			expect(hasEdge(fixturePath('cyc-b.ts:3:1'), fixturePath('cyc-a.ts:9:1'))).to.be.true;
			// createInCycle's caller across the cycle boundary
			expect(hasEdge(fixturePath('cyc-b.ts:3:1'), fixturePath('cyc-a.ts:4:1'))).to.be.true;
			const cycleModules = moduleGraph.cycles.flat().map(file => path.basename(file));
			expect(cycleModules).to.include.members([ 'cyc-a.ts', 'cyc-b.ts' ]);
		});

		it('should follow namespace imports as an approximation: any alias reference counts', () => {
			const viaNamespace = fixturePath('main.ts:15:22');
			expect(findNode(viaNamespace)?.name).to.equal('viaNamespace');
			// svc.reassignThing() reaches reassignThing…
			expect(hasEdge(viaNamespace, fixturePath('service.ts:8:1'))).to.be.true;
			// …and the approximation also links makeThing, exported by the same module
			expect(hasEdge(viaNamespace, fixturePath('service.ts:3:1'))).to.be.true;
			expect(hasEdge(fixturePath('main.ts'), viaNamespace)).to.be.true;
		});

		it('should bridge terminal modules to their importers (exports-and-usage)', () => {
			// wired.ts registers WiredMaker at module level — a VALUE handoff,
			// the way NestJS hands classes to the framework; no call connects
			// main.ts to the module, only the import relation does
			const wiredModule = findNode(fixturePath('wired.ts'));
			expect(wiredModule).to.exist;
			expect(wiredModule?.kind).to.equal('module');
			// the module scope calls the holder (the registry array reference)
			const makerMethod = graph.nodes.find(node => node.name === 'WiredMaker.make');
			expect(makerMethod).to.exist;
			expect(hasEdge(fixturePath('wired.ts'), makerMethod?.scopeId ?? '')).to.be.true;
			// the bridge: main.ts imports from wired.ts → main.ts is its caller
			expect(hasEdge(fixturePath('main.ts'), fixturePath('wired.ts'))).to.be.true;
			expect(wiredModule?.starter).to.be.false;
			// unimported terminal modules stay starters (rooted.ts: nobody imports it)
			expect(findNode(fixturePath('rooted.ts'))?.starter).to.be.true;
		});
	});

	describe('lookup() aliases', () => {
		it('should resolve the aliased instantiation to the looked-up typePath', () => {
			const anchor = findAnchor(fixturePath('lookup-alias.ts:6:15'));
			expect(anchor).to.exist;
			expect(anchor?.typePath).to.equal('Thing');
			expect(anchor?.variable).to.equal('inst');
		});

		it('should resolve lookup() variables in the scope analysis', () => {
			const t2 = scopeAnalysis.variables.get(`${fixturePath('lookup-alias.ts')}#T2`);
			expect(t2).to.exist;
			expect(t2?.typePath).to.equal('Thing');
		});
	});

	describe('reassignment termination (decision 6)', () => {
		it('should point terminatedAt at the variable\'s first reassignment site', () => {
			const anchor = findAnchor(fixturePath('service.ts:9:16'));
			expect(anchor).to.exist;
			expect(anchor?.variable).to.equal('current');
			expect(anchor?.terminatedAt).to.equal(fixturePath('service.ts:10:2'));
		});
	});

	describe('inline sources', () => {
		const virtualPath = (name: string): string => {
			const result = path.join('/virtual', name);
			return result;
		};

		const buildInline = (code: string, usages: Map<string, UsageInfo[]>): CreationGraph => {
			const sourceFile = ts.createSourceFile(virtualPath('inline.ts'), code, ts.ScriptTarget.Latest, true);
			const walker = new LocalScopeWalker();
			walker.addFile(sourceFile);
			const moduleGraphBuilder = new ModuleGraphBuilder();
			moduleGraphBuilder.addFile(sourceFile);
			const inlineModuleGraph = moduleGraphBuilder.build();
			const analysis = walker.build();
			LocalScopeWalker.attachHolderScopeIds(usages, walker);
			const sourceFilesByPath = new Map<string, ts.SourceFile>([
				[ virtualPath('inline.ts'), sourceFile ],
			]);
			const builder = new CreationGraphBuilder(inlineModuleGraph, analysis, walker, sourceFilesByPath);
			const result = builder.build(usages);
			return result;
		};

		it('should bind method scopes to their class name for the caller search', () => {
			// Line numbers in assertions below are 1-based in source order
			const code = [
				'class Greeter {',
				'\tmake (): unknown {',
				'\t\tconst thing = new Thing();',
				'\t\treturn thing;',
				'\t}',
				'}',
				'',
				'function boot (): unknown {',
				'\tconst greeter = new Greeter();',
				'\tconst made = greeter.make();',
				'\treturn made;',
				'}',
				'',
			].join('\n');
			const usages = new Map<string, UsageInfo[]>([
				[ 'Thing', [ {
					location : `${virtualPath('inline.ts')}:3:17`,
					kind     : 'instantiation',
					code     : 'new Thing()',
				} ] ],
			]);

			const inlineGraph = buildInline(code, usages);
			const methodNode = inlineGraph.nodes.find(node => node.kind === 'method');
			expect(methodNode?.name).to.equal('Greeter.make');
			const bootNode = inlineGraph.nodes.find(node => node.name === 'boot');
			expect(bootNode).to.exist;
			// boot references the class (`new Greeter()`), so boot calls Greeter.make
			expect(inlineGraph.edges.some(edge =>
				edge.caller === bootNode?.scopeId && edge.callee === methodNode?.scopeId)).to.be.true;
			expect(bootNode?.starter).to.be.true;
		});

		it('should treat anonymous holders as terminals (file:line labels, never referenced)', () => {
			const code = [
				'setTimeout(() => {',
				'\tconst thing = new Thing();',
				'\tvoid thing;',
				'});',
				'',
			].join('\n');
			const usages = new Map<string, UsageInfo[]>([
				[ 'Thing', [ {
					location : `${virtualPath('inline.ts')}:2:17`,
					kind     : 'instantiation',
					code     : 'new Thing()',
				} ] ],
			]);

			const inlineGraph = buildInline(code, usages);
			expect(inlineGraph.nodes).to.have.length(1);
			const [ holder ] = inlineGraph.nodes;
			expect(holder.kind).to.equal('arrow');
			expect(holder.name).to.equal(`${virtualPath('inline.ts')}:1`);
			expect(holder.starter).to.be.true;
			expect(inlineGraph.edges).to.have.length(0);
		});

		it('should not count import/export wiring or declaration positions as caller references', () => {
			// Line numbers in assertions below are 1-based in source order
			const code = [
				'import DefaultThing from \'./elsewhere\';',
				'import { other as aliased } from \'./elsewhere\';',
				'import * as ns from \'./elsewhere\';',
				'import eq = require(\'./elsewhere\');',
				'',
				'function makeThing (): unknown {',
				'\tconst thing = new Thing();',
				'\treturn thing;',
				'}',
				'',
				'function boot (): unknown {',
				'\tconst made = makeThing();',
				'\tconst { x: renamed } = made;',
				'\tconst obj = { made, key: renamed };',
				'\treturn obj;',
				'}',
				'',
				'export { makeThing as reExported };',
				'export default boot;',
				'',
			].join('\n');
			const usages = new Map<string, UsageInfo[]>([
				[ 'Thing', [ {
					location : `${virtualPath('inline.ts')}:7:17`,
					kind     : 'instantiation',
					code     : 'new Thing()',
				} ] ],
			]);

			const inlineGraph = buildInline(code, usages);
			const makeThingNode = inlineGraph.nodes.find(node => node.name === 'makeThing');
			const bootNode = inlineGraph.nodes.find(node => node.name === 'boot');
			expect(makeThingNode).to.exist;
			expect(bootNode).to.exist;

			// Only boot's genuine call counts: the `export { makeThing as … }`
			// specifier is wiring, not a caller
			const callersOfMakeThing = inlineGraph.edges.filter(edge => edge.callee === makeThingNode?.scopeId);
			expect(callersOfMakeThing).to.have.length(1);
			expect(callersOfMakeThing[ 0 ].caller).to.equal(bootNode?.scopeId);

			// `export default boot` is wiring too — boot keeps starter status
			const callersOfBoot = inlineGraph.edges.filter(edge => edge.callee === bootNode?.scopeId);
			expect(callersOfBoot).to.have.length(0);
			expect(bootNode?.starter).to.be.true;
		});

		it('should return an empty graph when nothing instantiates a tracked type', () => {
			const code = [
				'function idle (): number {',
				'\treturn 1;',
				'}',
				'',
			].join('\n');
			const usages = new Map<string, UsageInfo[]>([
				[ 'Thing', [ {
					location : `${virtualPath('inline.ts')}:1:1`,
					kind     : 'reference',
					code     : 'Thing',
				} ] ],
			]);

			const inlineGraph = buildInline(code, usages);
			expect(inlineGraph.nodes).to.have.length(0);
			expect(inlineGraph.edges).to.have.length(0);
			expect(inlineGraph.anchors).to.have.length(0);
		});
	});
});
