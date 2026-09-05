'use strict';

import * as path from 'path';
import * as ts from 'typescript';
import { LocalScopeWalker } from './scopes';
import {
	CreationAnchor, CreationGraph, CreationGraphEdge, CreationGraphNode, ModuleBinding, ModuleGraph, ModuleInfo,
	ScopeAnalysis, ScopeInfo, ScopeVariable, UsageInfo
} from './types';

/**
 * Inside-out creation walker (instrumentation walker plan, Phase 3).
 *
 * Starts at the certain points — instantiation usages carrying a
 * holderScopeId — then walks OUTWARD: who invokes or references the holder,
 * crossing files through the module graph (barrels chased the same way
 * ModuleGraphBuilder.resolveOrigin does), until no callers remain. Terminals
 * are the starters (application entry points). The walk never assumes a
 * linear Trie (decision 1: strictChain:false permits cycles/out-of-order
 * construction), so traversal is cycle-guarded DFS, and every anchor records
 * which constructor expression was actually used.
 *
 * Deliberate approximations (no getTypeChecker(), name-based only):
 * - Namespace imports (`import * as ns`): when the namespace's source module
 *   exposes the holder's export, ANY reference to the alias counts as a
 *   caller reference.
 * - Method scopes bind to their CLASS name (callers reference the class);
 *   instance-method call sites (`obj.method()`) are not distinguishable
 *   without the checker.
 * - Any non-declaration identifier counts as a reference (invocations,
 *   pass-as-arg, rebinding); type-position references are not filtered.
 * - Module scopes end the invocation walk, but a terminal module still
 *   gains its IMPORTERS as callers: entry modules hand classes to the
 *   framework as values (`NestFactory.create(AppModule)`), which no
 *   call-walk can see — the import relation bridges them to the center.
 */
export class CreationGraphBuilder {
	private moduleGraph: ModuleGraph;
	private scopeAnalysis: ScopeAnalysis;
	private scopeWalker: LocalScopeWalker;
	/** Keyed by path.resolve(sourceFile.fileName), matching scopeIds */
	private sourceFiles: Map<string, ts.SourceFile>;
	/** filePath -> (identifier text -> reference locations), built lazily per file */
	private referencesByFile = new Map<string, Map<string, string[]>>();

	constructor (
		moduleGraph: ModuleGraph,
		scopeAnalysis: ScopeAnalysis,
		scopeWalker: LocalScopeWalker,
		sourceFiles: Map<string, ts.SourceFile>
	) {
		this.moduleGraph = moduleGraph;
		this.scopeAnalysis = scopeAnalysis;
		this.scopeWalker = scopeWalker;
		this.sourceFiles = sourceFiles;
	}

	/**
	 * Build the creation graph from the analyzer's usages (holderScopeId
	 * already attached). Always returns a graph, empty arrays when nothing
	 * creates mnemonica instances.
	 */
	build (usages: Map<string, UsageInfo[]>): CreationGraph {
		const anchors = this.collectAnchors(usages);

		const nodes = new Map<string, CreationGraphNode>();
		const edges: CreationGraphEdge[] = [];
		const seenEdges = new Set<string>();
		// scopeIds with at least one caller — everyone else is a starter
		const called = new Set<string>();
		const visited = new Set<string>();
		const work: string[] = anchors.map(anchor => anchor.holderScopeId);

		const addEdge = (caller: string, callee: string): void => {
			const key = `${caller}\n${callee}`;
			if (seenEdges.has(key)) {
				return;
			}
			seenEdges.add(key);
			edges.push({ caller, callee });
			called.add(callee);
		};

		while (work.length > 0) {
			const scopeId = work.pop();
			if (!scopeId || visited.has(scopeId)) {
				continue;
			}
			visited.add(scopeId);
			const scope = this.scopeAnalysis.scopes.get(scopeId);
			if (!scope) {
				continue;
			}
			nodes.set(scopeId, CreationGraphBuilder.nodeOf(scope));

			if (scope.kind === 'module') {
				// Module scopes END the invocation walk — nobody invokes a
				// module (a module-scope creation is labeled rooted on the
				// anchor instead). But entry modules hand their classes to
				// the framework as VALUES (`NestFactory.create(AppModule)`,
				// `@Module({ controllers: [...] })`), invisible to
				// call-walking — so a terminal module still gains its
				// IMPORTERS as callers: main.ts importing AppModule yields
				// the main.ts → app.module edge the pure call graph misses.
				for (const importer of this.importersOf(scope.filePath)) {
					addEdge(importer, scopeId);
					if (!visited.has(importer)) {
						work.push(importer);
					}
				}
				continue;
			}

			const bindingName = CreationGraphBuilder.bindingNameOf(scope);
			if (!bindingName) {
				// Anonymous holder (file:line label): never referenced by name
				continue;
			}

			// Plan-sketch refinement: same-file references are followed for
			// EVERY holder, exported or not — an exported function can also be
			// called from its own module, and both paths lead outward.
			const sameFileCallers = this.callersOf(scope.filePath, bindingName);
			const crossFileCallers = this.findCrossFileCallers(scope, bindingName);
			for (const caller of [ ...sameFileCallers, ...crossFileCallers ]) {
				// Direct recursion (f calls f) adds no outward information
				if (caller === scopeId) {
					continue;
				}
				addEdge(caller, scopeId);
				if (!visited.has(caller)) {
					work.push(caller);
				}
			}
		}

		for (const node of nodes.values()) {
			node.starter = !called.has(node.scopeId);
		}

		const result: CreationGraph = {
			nodes : Array.from(nodes.values()),
			edges,
			anchors,
		};
		return result;
	}

	/**
	 * One anchor per instantiation usage with a known holder scope.
	 */
	private collectAnchors (usages: Map<string, UsageInfo[]>): CreationAnchor[] {
		const anchors: CreationAnchor[] = [];
		for (const [ typePath, usageList ] of usages) {
			for (const usage of usageList) {
				if (usage.kind !== 'instantiation' || !usage.holderScopeId) {
					continue;
				}
				const holderScope = this.scopeAnalysis.scopes.get(usage.holderScopeId);
				if (!holderScope) {
					continue;
				}
				const anchor: CreationAnchor = {
					location      : usage.location,
					holderScopeId : usage.holderScopeId,
					typePath,
				};
				if (usage.constructorText) {
					anchor.constructorText = usage.constructorText;
				}
				if (holderScope.kind === 'module') {
					// Plan: module-scope creation is a rooted instance —
					// legitimate root or developer error; labeled, not policed
					anchor.rooted = true;
				}
				const variable = this.matchAnchorVariable(usage, typePath, holderScope);
				if (variable) {
					anchor.variable = variable.name;
					const [ terminatedAt ] = variable.reassignments;
					if (terminatedAt) {
						anchor.terminatedAt = terminatedAt;
					}
				}
				anchors.push(anchor);
			}
		}
		return anchors;
	}

	/**
	 * Same-line heuristic for the anchor's variable: the variable declared in
	 * the holder scope on the same line as the creation, whose typePath (when
	 * known) matches the created type.
	 */
	private matchAnchorVariable (
		usage: UsageInfo,
		typePath: string,
		holderScope: ScopeInfo
	): ScopeVariable | undefined {
		const usageLine = CreationGraphBuilder.lineOf(usage.location);
		if (usageLine === undefined) {
			return undefined;
		}
		for (const variable of this.scopeAnalysis.variables.values()) {
			if (variable.scopeId !== holderScope.scopeId) {
				continue;
			}
			if (CreationGraphBuilder.lineOf(variable.declaration) !== usageLine) {
				continue;
			}
			if (variable.typePath && variable.typePath !== typePath) {
				continue;
			}
			return variable;
		}
		return undefined;
	}

	/**
	 * Parse the 1-based line out of a file.ts:Line:Col location string.
	 */
	private static lineOf (location: string): number | undefined {
		const lastColon = location.lastIndexOf(':');
		const prevColon = location.lastIndexOf(':', lastColon - 1);
		if (lastColon < 0 || prevColon < 0) {
			return undefined;
		}
		const line = Number(location.slice(prevColon + 1, lastColon));
		const result = Number.isFinite(line) ? line : undefined;
		return result;
	}

	private static nodeOf (scope: ScopeInfo): CreationGraphNode {
		const node: CreationGraphNode = {
			scopeId  : scope.scopeId,
			name     : scope.name,
			kind     : scope.kind,
			filePath : scope.filePath,
			location : scope.location,
			starter  : false,
		};
		return node;
	}

	/**
	 * The name a scope is reachable by: functions/arrows take their scope
	 * name; methods take their class (the part before '.') — that is what
	 * callers reference. Anonymous holders (file:line labels) and module
	 * scopes have no binding name.
	 */
	private static bindingNameOf (scope: ScopeInfo): string | undefined {
		if (scope.kind === 'module') {
			return undefined;
		}
		// Anonymous label is `${filePath}:${line}` — a name can never contain '/'
		if (scope.name.startsWith(`${scope.filePath}:`)) {
			return undefined;
		}
		if (scope.kind === 'method') {
			const dotIndex = scope.name.indexOf('.');
			if (dotIndex < 0) {
				// Method of an anonymous class — no binding name
				return undefined;
			}
			const result = scope.name.slice(0, dotIndex);
			return result;
		}
		return scope.name;
	}

	/**
	 * Scope ids referencing `bindingName` inside one file (invocations,
	 * pass-as-arg, rebindings — any non-declaration identifier).
	 */
	private callersOf (filePath: string, bindingName: string): string[] {
		const references = this.referencesIn(filePath, bindingName);
		const callers: string[] = [];
		for (const location of references) {
			const callerScopeId = this.scopeWalker.findHolderScopeId(location);
			if (callerScopeId) {
				callers.push(callerScopeId);
			}
		}
		return callers;
	}

	/**
	 * Callers in OTHER modules, followed through the module graph when the
	 * holder's binding is exported (the plan's "if f is exported" branch,
	 * including the barrel chase).
	 */
	private findCrossFileCallers (scope: ScopeInfo, bindingName: string): string[] {
		const holderModule = this.moduleGraph.modules.get(scope.filePath);
		if (!holderModule) {
			return [];
		}
		// The exported binding whose LOCAL name is the scope's binding name.
		// Plain exports present under their own name; `export { X as Y }` and
		// `export default X` carry the local name in importAlias.
		const exported = holderModule.exportedBindings.find(binding =>
			!binding.isReExport && (binding.importAlias ?? binding.name) === bindingName);
		if (!exported) {
			return [];
		}

		const callers: string[] = [];
		for (const importer of this.moduleGraph.modules.values()) {
			if (importer.filePath === scope.filePath) {
				continue;
			}
			for (const imported of importer.importedBindings) {
				// Re-exports create no local identifier to reference; external
				// packages (node_modules) are never walked
				if (imported.isReExport || imported.external) {
					continue;
				}
				const localName = this.importReferencesHolder(imported, exported, scope.filePath);
				if (!localName) {
					continue;
				}
				const importerCallers = this.callersOf(importer.filePath, localName);
				callers.push(...importerCallers);
			}
		}
		return callers;
	}

	/**
	 * Modules importing bindings whose ORIGIN is `filePath` — the
	 * exports-and-usage bridge for terminal module scopes. Any binding kind
	 * counts (named, default, re-export): resolveImportOrigin chases barrels
	 * to the declaring module; namespace imports and external packages never
	 * resolve, so neither connects. Returned as module-scope scopeIds — a
	 * module's scopeId IS its resolved filePath.
	 */
	private importersOf (filePath: string): string[] {
		const importers: string[] = [];
		for (const importer of this.moduleGraph.modules.values()) {
			if (importer.filePath === filePath) {
				continue;
			}
			const depends = importer.importedBindings.some(imported => {
				const origin = this.resolveImportOrigin(imported);
				const result = origin !== undefined && origin.module.filePath === filePath;
				return result;
			});
			if (depends) {
				importers.push(importer.filePath);
			}
		}
		return importers;
	}

	/**
	 * The local identifier an import binding presents for reference search,
	 * when the binding resolves to the holder's export — undefined otherwise.
	 */
	private importReferencesHolder (
		imported: ModuleBinding,
		holderExport: ModuleBinding,
		holderFilePath: string
	): string | undefined {
		if (imported.importKind === 'namespace') {
			// Namespace approximation: when the alias's source module exposes
			// the holder's export, any reference to the alias counts
			const exposes = this.namespaceExposes(imported.sourceModule, holderExport.name, holderFilePath);
			const result = exposes ? imported.name : undefined;
			return result;
		}
		const origin = this.resolveImportOrigin(imported);
		if (!origin) {
			return undefined;
		}
		if (origin.module.filePath !== holderFilePath || origin.binding.name !== holderExport.name) {
			return undefined;
		}
		return imported.name;
	}

	/**
	 * True when a namespace import's source module exposes `exportedName`
	 * whose origin is the holder's module. Expressed as resolving a synthetic
	 * named binding, so star barrels and named re-exports are chased by the
	 * same machinery as plain imports.
	 */
	private namespaceExposes (sourceModule: string, exportedName: string, holderFilePath: string): boolean {
		const synthetic: ModuleBinding = {
			name       : exportedName,
			kind       : 'unknown',
			sourceModule,
			isReExport : true,
		};
		const origin = this.resolveImportOrigin(synthetic);
		if (!origin) {
			return false;
		}
		const result = origin.module.filePath === holderFilePath && origin.binding.name === exportedName;
		return result;
	}

	/**
	 * Chase an import binding to the module that actually declares it,
	 * following re-export chains (barrels). Same shape as
	 * ModuleGraphBuilder.resolveOrigin, run here over the BUILT graph
	 * (sourceModule values are already resolved absolute paths).
	 * Cycle-guarded; undefined when the origin is external or the chain loops.
	 */
	private resolveImportOrigin (
		binding: ModuleBinding,
		visited = new Set<string>()
	): { module: ModuleInfo; binding: ModuleBinding } | undefined {
		const sourcePath = path.resolve(binding.sourceModule);
		if (visited.has(sourcePath)) {
			return undefined;
		}
		visited.add(sourcePath);

		const sourceModuleInfo = this.moduleGraph.modules.get(sourcePath);
		if (!sourceModuleInfo) {
			return undefined;
		}

		// The name to look up in the source module's export list
		const lookupKey = binding.importKind === 'default'
			? 'default'
			: binding.importAlias ?? binding.name;

		for (const exported of sourceModuleInfo.exportedBindings) {
			if (exported.name !== lookupKey) {
				continue;
			}
			if (!exported.isReExport) {
				const result = { module : sourceModuleInfo, binding : exported };
				return result;
			}
			const chased = this.resolveImportOrigin(exported, visited);
			return chased;
		}

		// `export * from './y'` barrels: the name may live behind a star
		for (const exported of sourceModuleInfo.exportedBindings) {
			if (!exported.isReExport || exported.importKind !== 'namespace' || exported.name !== '*') {
				continue;
			}
			const chased = this.resolveImportOrigin({
				name         : lookupKey,
				kind         : 'unknown',
				sourceModule : exported.sourceModule,
				isReExport   : true,
			}, visited);
			if (chased) {
				return chased;
			}
		}

		return undefined;
	}

	/**
	 * All references to `name` in a file as location strings. The per-file
	 * index is built lazily in ONE pass (every identifier bucketed by text)
	 * and cached.
	 */
	private referencesIn (filePath: string, name: string): string[] {
		let byName = this.referencesByFile.get(filePath);
		if (!byName) {
			byName = new Map<string, string[]>();
			const sourceFile = this.sourceFiles.get(filePath);
			if (sourceFile) {
				CreationGraphBuilder.collectReferences(sourceFile, byName);
			}
			this.referencesByFile.set(filePath, byName);
		}
		const result = byName.get(name) ?? [];
		return result;
	}

	/**
	 * Bucket every identifier reference by name. Declaration and wiring
	 * positions are NOT references: import/export specifiers, declaration
	 * names, property-access `.name`, and property-assignment keys go into a
	 * skip set of NODES — program files can be unbound, so parent-pointer
	 * checks are impossible (the scopes walker precedent, Phase 2).
	 * ShorthandPropertyAssignment names DO count: `{ foo }` is a genuine
	 * reference to foo.
	 */
	private static collectReferences (sourceFile: ts.SourceFile, byName: Map<string, string[]>): void {
		const skip = new Set<ts.Node>();
		const filePath = path.resolve(sourceFile.fileName);

		const visit = (node: ts.Node): void => {
			CreationGraphBuilder.registerSkips(node, skip);
			if (ts.isIdentifier(node) && !skip.has(node)) {
				const list = byName.get(node.text) ?? [];
				if (list.length === 0) {
					byName.set(node.text, list);
				}
				const { line, character } = sourceFile.getLineAndCharacterOfPosition(node.getStart(sourceFile));
				list.push(`${filePath}:${line + 1}:${character + 1}`);
			}
			ts.forEachChild(node, visit);
		};
		visit(sourceFile);
	}

	/**
	 * Register the identifier nodes that must NOT count as references when
	 * `node` is a wiring/declaration construct. Runs on the parent before
	 * descending, so the skip set is populated before the identifier nodes
	 * themselves are visited.
	 */
	private static registerSkips (node: ts.Node, skip: Set<ts.Node>): void {
		// import … from './x'
		if (ts.isImportDeclaration(node)) {
			const { importClause } = node;
			if (!importClause) {
				return;
			}
			if (importClause.name) {
				skip.add(importClause.name);
			}
			const { namedBindings } = importClause;
			if (namedBindings && ts.isNamedImports(namedBindings)) {
				for (const element of namedBindings.elements) {
					if (element.propertyName) {
						skip.add(element.propertyName);
					}
					skip.add(element.name);
				}
			}
			if (namedBindings && ts.isNamespaceImport(namedBindings)) {
				skip.add(namedBindings.name);
			}
			return;
		}
		// import x = require('./y')
		if (ts.isImportEqualsDeclaration(node)) {
			skip.add(node.name);
			return;
		}
		// export { X } [from './y'] / export * as ns from './y' — export wiring
		// alone is not a caller; an importer's usage creates the edge instead
		if (ts.isExportDeclaration(node)) {
			const { exportClause } = node;
			if (exportClause && ts.isNamedExports(exportClause)) {
				for (const element of exportClause.elements) {
					if (element.propertyName) {
						skip.add(element.propertyName);
					}
					skip.add(element.name);
				}
			}
			if (exportClause && ts.isNamespaceExport(exportClause)) {
				skip.add(exportClause.name);
			}
			return;
		}
		// export default foo — same export-wiring rule
		if (ts.isExportAssignment(node) && ts.isIdentifier(node.expression)) {
			skip.add(node.expression);
			return;
		}
		// obj.name — the `.name` part is property wiring, not a reference
		if (ts.isPropertyAccessExpression(node)) {
			skip.add(node.name);
			return;
		}
		// { name: value } — the key is not a reference. Shorthand `{ name }`
		// IS a reference: ShorthandPropertyAssignment never matches here.
		if (ts.isPropertyAssignment(node) && ts.isIdentifier(node.name)) {
			skip.add(node.name);
			return;
		}
		if (ts.isShorthandPropertyAssignment(node)) {
			return;
		}
		// { x: a } destructuring — `x` is property wiring (`a` is the declared
		// name, skipped by the generic declaration branch below)
		if (ts.isBindingElement(node) && node.propertyName && ts.isIdentifier(node.propertyName)) {
			skip.add(node.propertyName);
		}
		// Declaration names: `function f`, `class C`, `const x`, parameters,
		// methods, enum members… — being declared is not being referenced
		const named = node as ts.NamedDeclaration;
		if ('name' in node && named.name && ts.isIdentifier(named.name)) {
			skip.add(named.name);
		}
	}
}
