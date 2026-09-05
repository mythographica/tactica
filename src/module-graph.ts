'use strict';

import { builtinModules } from 'module';
import * as path from 'path';
import * as ts from 'typescript';
import {
	ModuleBinding, ModuleBindingKind, ModuleGraph, ModuleInfo, CrossModuleUsage
} from './types';

/**
 * Internal record of one import/export site: the specifier as written, its
 * location, and the binding objects it produced (shared by reference with
 * ModuleInfo, so build()-time resolution rewrites them in place).
 */
interface ImportSite {
	specifier: string;
	location: string;
	bindings: ModuleBinding[];
}

/**
 * Result of resolving one specifier: the absolute path (undefined when
 * unresolvable) and whether it landed in node_modules.
 */
interface ModuleResolution {
	resolvedPath?: string;
	isExternal: boolean;
}

// Bare builtin names from node:module; both 'path' and 'node:path' accepted
const BUILTIN_MODULES = new Set(builtinModules);

/**
 * Module-scope walker (instrumentation walker plan, Phase 1).
 *
 * Builds the cross-file module graph: every export/import binding (functions,
 * classes, consts, types — not only mnemonica types), resolved with
 * `ts.resolveModuleName` driven by the program's compilerOptions (tsconfig
 * `paths`, extensionless imports, index files). This is module resolution,
 * NOT the type checker — the no-`getTypeChecker()` precedent stays intact.
 *
 * Usage: addFile() per source file during the definitions pass, then
 * build(definedTypesByFile) once definitions are known.
 */
export class ModuleGraphBuilder {
	private compilerOptions: ts.CompilerOptions;
	private modules = new Map<string, ModuleInfo>();
	// filePath -> (local name -> kind) for every named top-level declaration
	private localDecls = new Map<string, Map<string, ModuleBindingKind>>();
	// filePath -> import/export specifier sites, for build()-time resolution
	private importSites = new Map<string, ImportSite[]>();
	// `${filePath}\n${specifier}` -> resolution (undefined = failed)
	private resolutionCache = new Map<string, ModuleResolution | undefined>();

	constructor (program?: ts.Program, compilerOptions?: ts.CompilerOptions) {
		const options = compilerOptions ?? program?.getCompilerOptions() ?? {};
		this.compilerOptions = options;
	}

	/**
	 * Track one source file. Re-adding the same file replaces its record,
	 * so a builder may safely be reused across passes.
	 */
	addFile (sourceFile: ts.SourceFile): ModuleInfo {
		const filePath = path.resolve(sourceFile.fileName);

		const moduleInfo: ModuleInfo = {
			filePath,
			definedTypes         : [],
			exportedBindings     : [],
			importedBindings     : [],
			dependencies         : [],
			unresolvedSpecifiers : [],
			builtinSpecifiers    : [],
		};
		const decls = new Map<string, ModuleBindingKind>();
		const sites: ImportSite[] = [];

		this.modules.set(filePath, moduleInfo);
		this.localDecls.set(filePath, decls);
		this.importSites.set(filePath, sites);

		// Pass 1: collect every named top-level declaration, so later
		// `export { X }` statements can be classified regardless of order
		for (const statement of sourceFile.statements) {
			this.collectLocalDecl(statement, decls);
		}

		// Pass 2: process imports, exports, and exported declarations
		for (const statement of sourceFile.statements) {
			this.processStatement(statement, sourceFile, moduleInfo, decls, sites);
		}

		return moduleInfo;
	}

	/**
	 * Resolve all specifiers, backfill binding kinds from origin modules,
	 * derive dependencies, cross-module mnemonica-type edges, and cycles.
	 * `definedTypesByFile` maps absolute file path -> mnemonica type fullPaths
	 * defined there (from the analyzer's definitions).
	 */
	build (definedTypesByFile?: Map<string, string[]>): ModuleGraph {
		if (definedTypesByFile) {
			for (const [ file, types ] of definedTypesByFile) {
				const moduleInfo = this.modules.get(path.resolve(file));
				if (moduleInfo) {
					moduleInfo.definedTypes = types;
				}
			}
		}

		// Resolution pass: rewrite sourceModule to the resolved absolute path
		for (const [ filePath, sites ] of this.importSites) {
			const moduleInfo = this.modules.get(filePath);
			if (!moduleInfo) {
				continue;
			}
			for (const site of sites) {
				const resolution = this.resolveModule(site.specifier, filePath);
				if (!resolution?.resolvedPath) {
					if (!moduleInfo.unresolvedSpecifiers.includes(site.specifier)) {
						moduleInfo.unresolvedSpecifiers.push(site.specifier);
					}
					continue;
				}
				const { resolvedPath, isExternal } = resolution;
				for (const binding of site.bindings) {
					binding.sourceModule = resolvedPath;
					if (isExternal) {
						binding.external = true;
					}
				}
				// Dependencies stay project-internal: external (node_modules)
				// modules are never addFile()'d, so modules.has() gates them out
				if (this.modules.has(resolvedPath) && !moduleInfo.dependencies.includes(resolvedPath)) {
					moduleInfo.dependencies.push(resolvedPath);
				}
			}
		}

		// Kind backfill + edge collection
		const edges: CrossModuleUsage[] = [];
		for (const [ filePath, sites ] of this.importSites) {
			const moduleInfo = this.modules.get(filePath);
			if (!moduleInfo) {
				continue;
			}
			for (const site of sites) {
				for (const binding of site.bindings) {
					const origin = this.resolveOrigin(binding);
					if (origin && binding.kind === 'unknown') {
						binding.kind = origin.binding.kind;
					}
					if (!origin || origin.module.filePath === filePath) {
						continue;
					}
					const typePath = this.matchDefinedType(origin.module, binding);
					if (typePath) {
						edges.push({
							typePath,
							definitionModule : origin.module.filePath,
							usageModule      : filePath,
							usageLocation    : site.location,
						});
					}
				}
			}
		}

		const cycles = this.detectCycles();

		const graph: ModuleGraph = {
			modules : this.modules,
			edges,
			cycles,
		};
		return graph;
	}

	/**
	 * Resolve a specifier to an absolute file path via ts.resolveModuleName
	 * with the program's compilerOptions. Returns undefined on failure.
	 */
	private resolveModule (specifier: string, fromFile: string): ModuleResolution | undefined {
		const cacheKey = `${fromFile}\n${specifier}`;
		if (this.resolutionCache.has(cacheKey)) {
			const cached = this.resolutionCache.get(cacheKey);
			return cached;
		}

		const result = ts.resolveModuleName(specifier, fromFile, this.compilerOptions, ts.sys);
		const resolution: ModuleResolution | undefined = result.resolvedModule
			? {
				resolvedPath : path.resolve(result.resolvedModule.resolvedFileName),
				isExternal   : result.resolvedModule.isExternalLibraryImport === true,
			}
			: undefined;
		this.resolutionCache.set(cacheKey, resolution);
		return resolution;
	}

	/**
	 * True for Node.js builtins in both bare and `node:`-prefixed forms
	 * ('path', 'node:path', 'fs/promises', 'node:fs/promises', …).
	 */
	private static isBuiltinSpecifier (specifier: string): boolean {
		const bare = specifier.startsWith('node:') ? specifier.slice('node:'.length) : specifier;
		const result = BUILTIN_MODULES.has(bare);
		return result;
	}

	/**
	 * Record a builtin import on the module (honesty marker) and skip it
	 * entirely: no bindings, no site, no dependency, no edge.
	 * Returns true when the specifier was a builtin (caller must return early).
	 */
	private static skipBuiltin (moduleInfo: ModuleInfo, specifier: string): boolean {
		if (!ModuleGraphBuilder.isBuiltinSpecifier(specifier)) {
			return false;
		}
		if (!moduleInfo.builtinSpecifiers.includes(specifier)) {
			moduleInfo.builtinSpecifiers.push(specifier);
		}
		return true;
	}

	/**
	 * Chase a binding to the module that actually declares it, following
	 * re-export chains (barrels). Cycle-guarded. Returns undefined when the
	 * origin is external or the chain loops.
	 */
	private resolveOrigin (
		binding: ModuleBinding,
		visited = new Set<string>()
	): { module: ModuleInfo; binding: ModuleBinding } | undefined {
		const sourcePath = path.resolve(binding.sourceModule);
		if (visited.has(sourcePath)) {
			return undefined;
		}
		visited.add(sourcePath);

		const sourceModuleInfo = this.modules.get(sourcePath);
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
			const chased = this.resolveOrigin(exported, visited);
			return chased;
		}

		// `export * from './y'` barrels: the name may live behind a star
		for (const exported of sourceModuleInfo.exportedBindings) {
			if (!exported.isReExport || exported.importKind !== 'namespace' || exported.name !== '*') {
				continue;
			}
			const chased = this.resolveOrigin({
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
	 * Match a binding against a module's defined mnemonica types.
	 * Returns the matched fullPath, or undefined when the binding is not a
	 * mnemonica type of that module.
	 */
	private matchDefinedType (moduleInfo: ModuleInfo, binding: ModuleBinding): string | undefined {
		const candidate = binding.importAlias ?? binding.name;
		for (const definedType of moduleInfo.definedTypes) {
			// Custom-collection types are keyed `collectionId::Path`
			const bare = definedType.includes('::')
				? definedType.slice(definedType.indexOf('::') + 2)
				: definedType;
			if (bare === candidate || bare.startsWith(`${candidate  }.`)) {
				return definedType;
			}
		}
		return undefined;
	}

	/**
	 * Three-color DFS over project-internal dependencies. Cycles are recorded
	 * (mnemonica strictChain:false permits non-linear construction), never
	 * treated as errors.
	 */
	private detectCycles (): string[][] {
		const cycles: string[][] = [];
		const seenCycles = new Set<string>();
		// 1 = on the current stack, 2 = fully explored
		const state = new Map<string, number>();

		const visit = (filePath: string, stack: string[]): void => {
			state.set(filePath, 1);
			stack.push(filePath);

			const moduleInfo = this.modules.get(filePath);
			for (const dep of moduleInfo?.dependencies ?? []) {
				if (state.get(dep) === 1) {
					const cycle = stack.slice(stack.indexOf(dep));
					const key = ModuleGraphBuilder.cycleKey(cycle);
					if (!seenCycles.has(key)) {
						seenCycles.add(key);
						cycles.push(cycle);
					}
					continue;
				}
				if (!state.get(dep)) {
					visit(dep, stack);
				}
			}

			stack.pop();
			state.set(filePath, 2);
		};

		for (const filePath of this.modules.keys()) {
			if (!state.get(filePath)) {
				visit(filePath, []);
			}
		}

		return cycles;
	}

	/**
	 * Rotation-independent cycle key: smallest path first.
	 */
	private static cycleKey (cycle: string[]): string {
		let minIndex = 0;
		for (let i = 1; i < cycle.length; i++) {
			if (cycle[ i ] < cycle[ minIndex ]) {
				minIndex = i;
			}
		}
		const rotated = cycle.slice(minIndex).concat(cycle.slice(0, minIndex));
		const key = rotated.join('\n');
		return key;
	}

	/**
	 * Pass 1: record every named top-level declaration's kind.
	 */
	private collectLocalDecl (statement: ts.Statement, decls: Map<string, ModuleBindingKind>): void {
		if (ts.isFunctionDeclaration(statement) && statement.name) {
			decls.set(statement.name.text, 'function');
			return;
		}
		if (ts.isClassDeclaration(statement) && statement.name) {
			decls.set(statement.name.text, 'class');
			return;
		}
		if (ts.isInterfaceDeclaration(statement) || ts.isTypeAliasDeclaration(statement)) {
			decls.set(statement.name.text, 'type');
			return;
		}
		if (ts.isEnumDeclaration(statement)) {
			decls.set(statement.name.text, 'type');
			return;
		}
		if (ts.isVariableStatement(statement)) {
			for (const decl of statement.declarationList.declarations) {
				if (ts.isIdentifier(decl.name)) {
					decls.set(decl.name.text, ModuleGraphBuilder.variableKind(decl));
				}
			}
		}
	}

	/**
	 * Classify a variable declaration: arrow/function initializers are
	 * 'function' (holder functions the walker follows), class expressions
	 * are 'class', everything else is 'const'.
	 */
	private static variableKind (decl: ts.VariableDeclaration): ModuleBindingKind {
		const { initializer } = decl;
		if (initializer && (ts.isArrowFunction(initializer) || ts.isFunctionExpression(initializer))) {
			return 'function';
		}
		if (initializer && ts.isClassExpression(initializer)) {
			return 'class';
		}
		return 'const';
	}

	/**
	 * Pass 2: imports, exports, requires, exported declarations.
	 */
	private processStatement (
		statement: ts.Statement,
		sourceFile: ts.SourceFile,
		moduleInfo: ModuleInfo,
		decls: Map<string, ModuleBindingKind>,
		sites: ImportSite[]
	): void {
		if (ts.isImportDeclaration(statement)) {
			this.processImport(statement, sourceFile, moduleInfo, sites);
			return;
		}
		if (ts.isExportDeclaration(statement)) {
			this.processExportDeclaration(statement, sourceFile, moduleInfo, decls, sites);
			return;
		}
		if (ts.isImportEqualsDeclaration(statement)) {
			this.processImportEquals(statement, sourceFile, moduleInfo, sites);
			return;
		}
		if (ts.isExportAssignment(statement)) {
			this.processExportAssignment(statement, moduleInfo, decls);
			return;
		}
		this.processMaybeExportedDecl(statement, moduleInfo, decls);
		this.processRequireCall(statement, sourceFile, moduleInfo, sites);
	}

	private processImport (
		importDecl: ts.ImportDeclaration,
		sourceFile: ts.SourceFile,
		moduleInfo: ModuleInfo,
		sites: ImportSite[]
	): void {
		const { moduleSpecifier } = importDecl;
		if (!ts.isStringLiteral(moduleSpecifier)) {
			return;
		}
		if (ModuleGraphBuilder.skipBuiltin(moduleInfo, moduleSpecifier.text)) {
			return;
		}

		const site: ImportSite = {
			specifier : moduleSpecifier.text,
			location  : this.locationOf(moduleSpecifier, sourceFile),
			bindings  : [],
		};
		sites.push(site);

		const { importClause } = importDecl;
		if (!importClause) {
			// Side-effect import: dependency only, no bindings
			return;
		}

		// Default import: import Type from './module'
		if (importClause.name) {
			const binding: ModuleBinding = {
				name         : importClause.name.text,
				kind         : 'unknown',
				sourceModule : site.specifier,
				importKind   : 'default',
				isReExport   : false,
			};
			moduleInfo.importedBindings.push(binding);
			site.bindings.push(binding);
		}

		const { namedBindings } = importClause;
		if (namedBindings && ts.isNamedImports(namedBindings)) {
			for (const element of namedBindings.elements) {
				const originalName = element.propertyName?.text;
				const binding: ModuleBinding = {
					name         : element.name.text,
					kind         : 'unknown',
					sourceModule : site.specifier,
					importKind   : 'named',
					isReExport   : false,
				};
				if (originalName) {
					binding.importAlias = originalName;
				}
				moduleInfo.importedBindings.push(binding);
				site.bindings.push(binding);
			}
			return;
		}

		// Namespace import: import * as Types from './module'
		if (namedBindings && ts.isNamespaceImport(namedBindings)) {
			const binding: ModuleBinding = {
				name         : namedBindings.name.text,
				kind         : 'unknown',
				sourceModule : site.specifier,
				importKind   : 'namespace',
				isReExport   : false,
			};
			moduleInfo.importedBindings.push(binding);
			site.bindings.push(binding);
		}
	}

	private processExportDeclaration (
		exportDecl: ts.ExportDeclaration,
		sourceFile: ts.SourceFile,
		moduleInfo: ModuleInfo,
		decls: Map<string, ModuleBindingKind>,
		sites: ImportSite[]
	): void {
		const { moduleSpecifier } = exportDecl;
		const { exportClause } = exportDecl;

		// Re-export forms carry a module specifier: `export … from './y'`
		if (moduleSpecifier && ts.isStringLiteral(moduleSpecifier)) {
			if (ModuleGraphBuilder.skipBuiltin(moduleInfo, moduleSpecifier.text)) {
				return;
			}

			const site: ImportSite = {
				specifier : moduleSpecifier.text,
				location  : this.locationOf(moduleSpecifier, sourceFile),
				bindings  : [],
			};
			sites.push(site);

			if (!exportClause) {
				// `export * from './y'`
				const binding: ModuleBinding = {
					name         : '*',
					kind         : 'unknown',
					sourceModule : site.specifier,
					importKind   : 'namespace',
					isReExport   : true,
				};
				moduleInfo.exportedBindings.push(binding);
				moduleInfo.importedBindings.push(binding);
				site.bindings.push(binding);
				return;
			}

			if (ts.isNamespaceExport(exportClause)) {
				// `export * as ns from './y'`
				const binding: ModuleBinding = {
					name         : exportClause.name.text,
					kind         : 'unknown',
					sourceModule : site.specifier,
					importKind   : 'namespace',
					isReExport   : true,
				};
				moduleInfo.exportedBindings.push(binding);
				moduleInfo.importedBindings.push(binding);
				site.bindings.push(binding);
				return;
			}

			// `export { X, Y as Z } from './y'`
			for (const element of exportClause.elements) {
				const originalName = element.propertyName?.text;
				const binding: ModuleBinding = {
					name         : element.name.text,
					kind         : 'unknown',
					sourceModule : site.specifier,
					importKind   : 'named',
					isReExport   : true,
				};
				if (originalName) {
					binding.importAlias = originalName;
				}
				moduleInfo.exportedBindings.push(binding);
				moduleInfo.importedBindings.push(binding);
				site.bindings.push(binding);
			}
			return;
		}

		// Plain `export { X, Y as Z }` — local declarations
		if (exportClause && ts.isNamedExports(exportClause)) {
			for (const element of exportClause.elements) {
				const originalName = element.propertyName?.text ?? element.name.text;
				const binding: ModuleBinding = {
					name         : element.name.text,
					kind         : decls.get(originalName) ?? 'unknown',
					sourceModule : moduleInfo.filePath,
					isReExport   : false,
				};
				if (element.propertyName) {
					binding.importAlias = element.propertyName.text;
				}
				moduleInfo.exportedBindings.push(binding);
			}
		}
	}

	/**
	 * `import foo = require('./y')`
	 */
	private processImportEquals (
		importDecl: ts.ImportEqualsDeclaration,
		sourceFile: ts.SourceFile,
		moduleInfo: ModuleInfo,
		sites: ImportSite[]
	): void {
		const { moduleReference } = importDecl;
		if (!ts.isExternalModuleReference(moduleReference)) {
			return;
		}
		const { expression } = moduleReference;
		if (!ts.isStringLiteral(expression)) {
			return;
		}
		if (ModuleGraphBuilder.skipBuiltin(moduleInfo, expression.text)) {
			return;
		}

		const binding: ModuleBinding = {
			name         : importDecl.name.text,
			kind         : 'unknown',
			sourceModule : expression.text,
			importKind   : 'require',
			isReExport   : false,
		};
		moduleInfo.importedBindings.push(binding);
		sites.push({
			specifier : expression.text,
			location  : this.locationOf(expression, sourceFile),
			bindings  : [ binding ],
		});
	}

	/**
	 * `export default <expression>`
	 */
	private processExportAssignment (
		statement: ts.ExportAssignment,
		moduleInfo: ModuleInfo,
		decls: Map<string, ModuleBindingKind>
	): void {
		const { expression } = statement;
		const kind = ts.isIdentifier(expression)
			? decls.get(expression.text) ?? 'unknown'
			: 'unknown';
		const binding: ModuleBinding = {
			name         : 'default',
			kind,
			sourceModule : moduleInfo.filePath,
			importKind   : 'default',
			isReExport   : false,
		};
		if (ts.isIdentifier(expression)) {
			binding.importAlias = expression.text;
		}
		moduleInfo.exportedBindings.push(binding);
	}

	/**
	 * `export function/class/const/interface/type …` declarations.
	 */
	private processMaybeExportedDecl (
		statement: ts.Statement,
		moduleInfo: ModuleInfo,
		decls: Map<string, ModuleBindingKind>
	): void {
		const modifiers = ts.canHaveModifiers(statement) ? ts.getModifiers(statement) : undefined;
		const hasExport = modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword) ?? false;
		const hasDefault = modifiers?.some(m => m.kind === ts.SyntaxKind.DefaultKeyword) ?? false;
		if (!hasExport) {
			return;
		}

		const addExport = (localName: string | undefined, kind: ModuleBindingKind): void => {
			const binding: ModuleBinding = {
				name         : hasDefault ? 'default' : localName ?? 'default',
				kind,
				sourceModule : moduleInfo.filePath,
				isReExport   : false,
			};
			if (hasDefault) {
				binding.importKind = 'default';
				if (localName) {
					binding.importAlias = localName;
				}
			}
			moduleInfo.exportedBindings.push(binding);
		};

		if (ts.isFunctionDeclaration(statement)) {
			addExport(statement.name?.text, 'function');
			return;
		}
		if (ts.isClassDeclaration(statement)) {
			addExport(statement.name?.text, 'class');
			return;
		}
		if (ts.isInterfaceDeclaration(statement) || ts.isTypeAliasDeclaration(statement)) {
			addExport(statement.name.text, 'type');
			return;
		}
		if (ts.isEnumDeclaration(statement)) {
			addExport(statement.name.text, 'type');
			return;
		}
		if (ts.isVariableStatement(statement)) {
			for (const decl of statement.declarationList.declarations) {
				if (ts.isIdentifier(decl.name)) {
					addExport(decl.name.text, decls.get(decl.name.text) ?? 'const');
				}
			}
		}
	}

	/**
	 * CommonJS `const x = require('./y')` (JS sources with allowJs).
	 */
	private processRequireCall (
		statement: ts.Statement,
		sourceFile: ts.SourceFile,
		moduleInfo: ModuleInfo,
		sites: ImportSite[]
	): void {
		if (!ts.isVariableStatement(statement)) {
			return;
		}
		for (const decl of statement.declarationList.declarations) {
			const { initializer } = decl;
			if (!initializer || !ts.isCallExpression(initializer)) {
				continue;
			}
			if (!ts.isIdentifier(initializer.expression) || initializer.expression.text !== 'require') {
				continue;
			}
			const [ firstArg ] = initializer.arguments;
			if (!firstArg || !ts.isStringLiteral(firstArg)) {
				continue;
			}
			if (ModuleGraphBuilder.skipBuiltin(moduleInfo, firstArg.text)) {
				continue;
			}
			const localName = ts.isIdentifier(decl.name) ? decl.name.text : decl.name.getText();
			const binding: ModuleBinding = {
				name         : localName,
				kind         : 'unknown',
				sourceModule : firstArg.text,
				importKind   : 'require',
				isReExport   : false,
			};
			moduleInfo.importedBindings.push(binding);
			sites.push({
				specifier : firstArg.text,
				location  : this.locationOf(firstArg, sourceFile),
				bindings  : [ binding ],
			});
		}
	}

	/**
	 * Format a node's position as file.ts:Line:Col (1-based), matching the
	 * location format of the other .tactica outputs.
	 */
	private locationOf (node: ts.Node, sourceFile: ts.SourceFile): string {
		const position = sourceFile.getLineAndCharacterOfPosition(node.getStart(sourceFile));
		const location = `${path.resolve(sourceFile.fileName)}:${position.line + 1}:${position.character + 1}`;
		return location;
	}
}
