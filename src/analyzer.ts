'use strict';

import * as nodePath from 'path';
import * as ts from 'typescript';
import {
	TypeNode, PropertyInfo, AnalyzeResult, AnalyzeError,
	DefinitionInfo, UsageInfo, ConstructorParamInfo,
	EDSInfo, FlowInfo, InstrumentationKind, InstrumentationPoint,
	InstrumentationScope, ResolutionError
} from './types';
import {
	TypeGraphImpl, resolveGraphTypeReference, GraphTypeReferenceResult 
} from './graph';
import {
	InstrumentationVocabulary, TacticaPlugin, mergeTacticaPlugins
} from './plugins';

interface CollectionInfo {
	variableName: string;
	sourceFile: string;
	registryInterfaceName?: string;
}

/**
 * Location/code captured at a class declaration, used to resolve
 * instrumentation registration sites to the declared class
 */
interface InstrumentationClassDecl {
	kind?: InstrumentationKind;
	location: string;
	code: string;
}

/**
 * Raw registration site (decorator, APP_* provider, consumer.apply).
 * Location/code are the site's own; getInstrumentationPoints() rewrites
 * them to the class declaration when the class is declared in-project.
 */
interface InstrumentationSite {
	kind: InstrumentationKind;
	className: string;
	location: string;
	code: string;
	scope: InstrumentationScope;
	targets: string[];
}

/**
 * A named referenced-type declaration (type alias, class, or interface)
 * recorded per file, so references can be resolved through the importing
 * file's own imports instead of a program-wide last-wins name map (F10).
 */
interface ReferencedTypeDeclaration {
	kind: 'alias' | 'class' | 'interface';
	node: ts.TypeAliasDeclaration | ts.ClassDeclaration | ts.InterfaceDeclaration;
	/** file that declares the type — nested references resolve against it */
	file: string;
}

/**
 * One import binding of a referenced type: the local name under which the
 * file knows it, the original exported name in the source module, and the
 * specifier it came from.
 */
interface ReferencedTypeImport {
	originalName: string;
	specifier: string;
	isNamespace: boolean;
}

/**
 * Result of resolving one module specifier from one containing file.
 */
interface ReferencedTypeResolution {
	resolvedPath: string;
	isExternal: boolean;
}

/**
 * Global/builtin type names that are safe to emit bare into generated files
 * — they resolve in any TypeScript compilation without an import.
 */
const KNOWN_GLOBAL_TYPES = new Set([
	'Date', 'RegExp', 'Error', 'EvalError', 'RangeError', 'ReferenceError',
	'SyntaxError', 'TypeError', 'URIError', 'AggregateError',
	'Map', 'Set', 'WeakMap', 'WeakSet', 'WeakRef', 'FinalizationRegistry',
	'Promise', 'Array', 'ReadonlyArray', 'Record', 'Partial', 'Required',
	'Readonly', 'Pick', 'Omit', 'Exclude', 'Extract', 'NonNullable',
	'ReturnType', 'InstanceType', 'Parameters', 'ConstructorParameters',
	'ThisType', 'ThisParameterType', 'OmitThisParameter',
	'Uppercase', 'Lowercase', 'Capitalize', 'Uncapitalize',
	'String', 'Number', 'Boolean', 'Symbol', 'BigInt', 'Object', 'Function',
	'Iterable', 'Iterator', 'Generator', 'AsyncIterable', 'AsyncIterator',
	'AsyncGenerator', 'IterableIterator', 'AsyncIterableIterator',
	'PropertyKey', 'ArrayBuffer', 'SharedArrayBuffer', 'DataView',
	'Int8Array', 'Uint8Array', 'Uint8ClampedArray', 'Int16Array',
	'Uint16Array', 'Int32Array', 'Uint32Array', 'Float32Array',
	'Float64Array', 'BigInt64Array', 'BigUint64Array', 'Intl'
]);

// Bound for chasing re-export barrels (export { X } from '…', export * from '…')
const MAX_REEXPORT_CHASE_DEPTH = 5;
// Bound for walking class/interface extends chains during referenced-type
// expansion (inherited members merge into the expanded fields)
const MAX_HERITAGE_DEPTH = 8;

/**
 * AST Analyzer for finding Mnemonica define() and decorate() calls
 *
 * Framework-blind by construction: instrumentation detection vocabulary
 * (interface names, decorator names, provider tokens, middleware wiring)
 * comes entirely from plugins — with none loaded, zero points are collected.
 */
export class MnemonicaAnalyzer {
	private errors: AnalyzeError[] = [];
	private graph = new TypeGraphImpl();
	private definitions = new Map<string, DefinitionInfo>();
	private usages = new Map<string, UsageInfo[]>();
	private edsUsages = new Map<string, EDSInfo[]>();
	private flowUsages = new Map<string, FlowInfo[]>();
	// Enclosing mnemonica scope for EDS keying: define()/lazy() call node
	// or @decorate()-ed class declaration -> fullPath of the type it owns.
	// Populated on the definitions pass; AST nodes persist across passes,
	// so entries stay valid after resetUsages().
	private edsScopeByNode = new Map<ts.Node, string>();
	// Same-file function bindings (`fileName#name` -> function node) for
	// resolving wrap(fn) arguments syntactically — the checker stays unused
	private functionBindings = new Map<string, ts.FunctionLikeDeclaration>();
	// wrap call node -> location of the enclosing wrap site (plus that
	// site's scope attribution), so nested wrap() calls inside a wrapped
	// body carry the `via` link — and inherit the scope when they have
	// none of their own
	private nestedWrapVia = new Map<ts.Node, { via: string; scope?: string }>();
	// wrap call node -> its collected entry, so a lexically nested wrap
	// (visited BEFORE the outer wrap call, per source order) gets its
	// `via` back-patched when the outer body is analysed
	private wrapEntryByNode = new Map<ts.Node, EDSInfo>();
	// Track variable assignments: variableName -> fullPath of the type it holds
	private variableToTypeMap = new Map<string, string>();
	// Track mnemonica module-object variables (e.g., import { mnemonica } from 'mnemonica'; const m = mnemonica)
	private moduleObjectVariables = new Set<string>();
	// file -> (local name -> imported name) for named imports from
	// 'mnemonica' — import-awareness for the construction-function
	// recognition (call/apply/bind) and the utils forms (merge/fork):
	// userland functions with those names must never match
	private mnemonicaNamedImports = new Map<string, Map<string, string>>();
	// Track imported aliases of createTypesCollection (e.g., import { createTypesCollection as ctc })
	private createTypesCollectionVariables = new Set<string>();
	// Track custom collection variables: variableName -> collectionId
	private collectionVariables = new Map<string, string>();
	// Track custom collection metadata for Option B registry emission
	private collectionInfo = new Map<string, CollectionInfo>();
	private collectionCounter = 0;
	// Instrumentation collection (syntactic only — no type checker):
	// every named class declaration by simple name, for resolving
	// registration sites to declaration locations (best effort, last wins)
	private instrumentationClassDecls = new Map<string, InstrumentationClassDecl>();
	// Registration sites: decorator applications, provider-token object
	// literals, consumer.apply() middleware wiring
	private instrumentationSites: InstrumentationSite[] = [];
	// Merged plugin vocabulary for instrumentation detection (empty when
	// no plugins were passed — the analyzer then collects no points)
	private instrumentationVocabulary: InstrumentationVocabulary;
	// Referenced-type resolution (F10): per-file declarations and imports.
	// A type name used in file X resolves through X's own import statements
	// first (relative + tsconfig-paths, via ts.resolveModuleName), then
	// X's local declarations, then — only when nothing imports or declares
	// the name — the unique same-named declaration across scanned files.
	// Genuine ambiguity or an unresolvable reference yields `unknown`, never
	// a bare emitted name: generated types.ts carries no imports of its own.
	private referencedTypeDecls = new Map<string, Map<string, ReferencedTypeDeclaration>>();
	private referencedTypeImports = new Map<string, Map<string, ReferencedTypeImport>>();
	// file -> (exported name -> re-export specifier) for `export { X } from '…'`
	private referencedTypeReExports = new Map<string, Map<string, string>>();
	// file -> specifiers of `export * from '…'`
	private referencedTypeExportStars = new Map<string, string[]>();
	// file -> (exported name -> local name) for `export { X as Y }`
	private referencedTypeExportAliases = new Map<string, Map<string, string>>();
	// file -> (namespace name -> namespace declaration) — middle segments
	// of qualified references (models.Inner.Crate) descend through these
	private referencedTypeNamespaces = new Map<string, Map<string, ts.ModuleDeclaration>>();
	// file -> (namespace name -> specifier) for `export * as ns from '…'`
	// barrels — a nested module namespace one segment deep
	private referencedTypeNamespaceStars = new Map<string, Map<string, string>>();
	// `${containingFile}::${specifier}` -> resolution (undefined = failed)
	private referencedTypeResolutionCache = new Map<string, ReferencedTypeResolution | undefined>();
	// file -> (const name -> array literal) for consts with array-literal
	// initializers (`as const` / `satisfies` unwrapped), so a
	// `typeof statusList[number]` field type expands to the element literal
	// union instead of leaking a bare unresolvable `typeof` query into the
	// generated file. Declarations persist across passes — entries stay
	// valid after resetUsages(), same as referencedTypeDecls
	private referencedTypeConstArrays = new Map<string, Map<string, ts.ArrayLiteralExpression>>();
	private referencedTypeCompilerOptions: ts.CompilerOptions;
	// File whose AST is currently being visited; references resolve against it
	private currentReferencedTypeFile = '';
	// Alias names currently being expanded (cycle guard)
	private expandingReferencedAliases = new Set<string>();
	// Mnemonica-graph identity law (hard fail): every define()/lazy()/
	// @decorate() site keyed by its runtime namespace (collection roots:
	// `<collection>::<name>`; subtypes: `<parentFullPath>.<name>`). Two
	// sites in one namespace are a same-namespace duplicate — the runtime
	// throws ALREADY_DECLARED — and must abort generation.
	private defineSites = new Map<string, string[]>();
	// Mnemonica-graph references that stayed ambiguous after path-aware
	// resolution or resolved to nothing (hard-fail class 2)
	private graphReferenceErrors: ResolutionError[] = [];
	// Guards lookup()-path validation so it runs once per usages pass
	// (getResolutionErrors may be called repeatedly); resetUsages re-arms it
	private lookupReferencesValidated = false;
	// Literal lookup() call sites with their resolved paths. Kept apart from
	// the usages map on purpose: addUsage drops paths the graph does not
	// know (usages.json indexes references to KNOWN types), but an unknown
	// lookup path is exactly the hard-fail case — the runtime returns
	// undefined there and the TypeError arrives one line later
	private lookupReferences: { path: string; location: string }[] = [];
	// Guards plain-TS reference validation so it runs once per usages pass
	// (getResolutionErrors may be called repeatedly); resetUsages re-arms it
	private plainTypeReferencesValidated = false;
	// Plain-TS type reference sites whose resolution fell through imports,
	// locals, the program-wide scan, and the graph to a soft `unknown`.
	// Validated lazily from getResolutionErrors against the complete
	// declaration map: a name several project-source files declare — with
	// no import in the referencing file to anchor it — is the plain-TS
	// ambiguity hard-fail class (one tier below the graph identity law);
	// absence (ghost names) stays soft. Recording happens on every pass,
	// the verdict only here — pass 1 sees an incomplete declaration map,
	// so only the usages pass is authoritative (mirrors lookup references)
	private plainTypeReferences: { name: string; location: string; file: string }[] = [];
	// Per-file top-level variable -> mnemonica fullPath bindings (value
	// scope): `const Address = User.define('Address', …)` makes `Address`
	// denote User.Address wherever that file's references are resolved
	private fileGraphBindings = new Map<string, Map<string, string>>();
	// The graph type whose constructor is currently being extracted;
	// anchors relative-first graph reference resolution
	private currentGraphAnchor: TypeNode | undefined;
	// define()/lazy() calls already extracted this pass. The CLI re-analyzes
	// every file after resetUsages(); clearing the set lets the second pass
	// re-extract every constructor against the COMPLETE graph — pass 1 sees
	// forward references as `none` (soft unknown) because later files have
	// not been visited yet, so only pass-2 resolution is authoritative for
	// the hard-fail identity law. The stamp lives here rather than on the
	// AST node so it can actually be cleared. (Chained calls visit the same
	// node twice within one pass; the in-pass dedup below stays.)
	private processedCalls = new Set<ts.CallExpression>();

	constructor (program?: ts.Program, plugins: TacticaPlugin[] = []) {
		// Compiler options drive ts.resolveModuleName for import-aware
		// referenced-type resolution (tsconfig `paths`, extensionless
		// imports); the type checker itself stays unused.
		this.referencedTypeCompilerOptions = program?.getCompilerOptions() ?? {};
		this.instrumentationVocabulary = mergeTacticaPlugins(plugins);
	}

	/**
	 * Reset usage-related state for a fresh pass.
	 * Call before the usage-collection pass to avoid duplicates from definition pass.
	 */
	resetUsages (): void {
		this.usages.clear();
		this.edsUsages.clear();
		this.flowUsages.clear();
		this.variableToTypeMap.clear();
		// EDS entry references go stale with edsUsages; via links are
		// re-derived on the next pass
		this.wrapEntryByNode.clear();
		this.nestedWrapVia.clear();
		// Note: moduleObjectVariables and collectionVariables intentionally persist
		// across definition and usage passes.
		// Re-extraction in the usages pass is what makes graph reference
		// resolution authoritative: pass 1 resolves against an incomplete
		// graph (forward references read as `none`), pass 2 against all of it.
		this.processedCalls.clear();
		// lookup()-path validation runs against the recorded sites; a fresh
		// pass must re-record and re-validate (pass-1 results would be
		// premature — the graph is still incomplete)
		this.lookupReferencesValidated = false;
		this.lookupReferences = [];
		this.plainTypeReferencesValidated = false;
		this.plainTypeReferences = [];
	}

	/**
	 * Analyze a source file for Mnemonica type definitions
	 */
	analyzeFile (sourceFile: ts.SourceFile): AnalyzeResult {
		this.errors = [];
		// Referenced-type names in this file resolve against its own imports
		this.currentReferencedTypeFile = nodePath.resolve(sourceFile.fileName);
		// Ensure parent nodes are set for AST traversal
		this.setParentNodesInSourceFile(sourceFile);
		this.visitNode(sourceFile, sourceFile);

		return {
			types  : this.graph.getAllTypes(),
			errors : this.errors,
		};
	}

	/**
	 * Analyze source code string
	 */
	analyzeSource (sourceCode: string, fileName = 'temp.ts'): AnalyzeResult {
		const sourceFile = ts.createSourceFile(
			fileName,
			sourceCode,
			ts.ScriptTarget.Latest,
			true
		);
		return this.analyzeFile(sourceFile);
	}

	/**
	 * Get the type graph
	 */
	getGraph (): TypeGraphImpl {
		return this.graph;
	}

	/**
	 * Get collected definitions
	 */
	getDefinitions (): Map<string, DefinitionInfo> {
		return this.definitions;
	}

	/**
	 * Get collected usages
	 */
	getUsages (): Map<string, UsageInfo[]> {
		return this.usages;
	}

	/**
	 * Get collected EDS usages
	 */
	getEDSUsages (): Map<string, EDSInfo[]> {
		return this.edsUsages;
	}

	/**
	 * Get collected flow usages
	 */
	getFlowUsages (): Map<string, FlowInfo[]> {
		return this.flowUsages;
	}

	/**
	 * Get collected instrumentation points.
	 * Registration sites referencing a class declared in the same project
	 * resolve to the class declaration's location/code; external classes
	 * (e.g., a framework-builtin implementation from node_modules) keep
	 * the registration site.
	 * Deduped by kind+className+location+scope with targets merged — a
	 * class detected by heritage AND by a decorator site yields separate
	 * entries with distinct scopes (see InstrumentationPoint in types.ts).
	 */
	getInstrumentationPoints (): InstrumentationPoint[] {
		const points = new Map<string, InstrumentationPoint>();

		const addPoint = (point: InstrumentationPoint): void => {
			const key = `${point.kind}|${point.className}|${point.location}|${point.scope}`;
			const existing = points.get(key);
			if (existing) {
				const merged = new Set([ ...existing.targets, ...point.targets ]);
				existing.targets = Array.from(merged);
				return;
			}
			points.set(key, point);
		};

		for (const site of this.instrumentationSites) {
			const decl = this.instrumentationClassDecls.get(site.className);
			const point: InstrumentationPoint = {
				kind      : site.kind,
				className : site.className,
				location  : decl ? decl.location : site.location,
				code      : decl ? decl.code : site.code,
				scope     : site.scope,
				targets   : site.targets,
			};
			addPoint(point);
		}

		// Heritage-declared classes always emit a declaration point with
		// scope 'module' (attachment statically unknown); registration
		// sites above carry the narrower scopes as separate entries
		for (const [ className, decl ] of this.instrumentationClassDecls) {
			if (!decl.kind) {
				continue;
			}
			const point: InstrumentationPoint = {
				kind      : decl.kind,
				className : className,
				location  : decl.location,
				code      : decl.code,
				scope     : 'module',
				targets   : [],
			};
			addPoint(point);
		}

		const result = Array.from(points.values());
		return result;
	}

	/**
	 * Add a topologica type to the analyzer for usage tracking.
	 * This allows the analyzer to recognize topologica types when collecting usages.
	 */
	addTopologicaType (fullPath: string, node: import('./types').TypeNode): void {
		// Skip if already exists
		if (this.graph.allTypes.has(fullPath)) {
			return;
		}

		// Add to graph so it can be found during usage collection
		if (node.parent) {
			// Add as child of parent
			this.graph.addChild(node.parent, node);
		} else {
			// Add as root
			this.graph.addRoot(node);
		}

		// Also add to definitions so it's recognized as a known type
		const definition: DefinitionInfo = {
			name        : node.name,
			location    : `${node.sourceFile}:${node.line}:${node.column}`,
			kind        : 'define',
			parent      : node.parent ? node.parent.fullPath : null,
			strictChain : true,
			blockErrors : false
		};
		this.definitions.set(fullPath, definition);
	}

	/**
	 * Set parent nodes in a source file to enable AST traversal up
	 */
	private setParentNodesInSourceFile (sourceFile: ts.SourceFile): void {
		const setParent = (node: ts.Node, parent?: ts.Node) => {
			// TypeScript doesn't expose parent as writable, but we need it
			// eslint-disable-next-line @typescript-eslint/no-explicit-any
			(node as any).parent = parent;
			ts.forEachChild(node, child => setParent(child, node));
		};
		setParent(sourceFile);
	}

	/**
	 * Visit a node in the AST
	 */
	private visitNode (node: ts.Node, sourceFile: ts.SourceFile, currentClass?: ts.ClassDeclaration): void {
		// Track mnemonica module-object aliases and custom collection variables
		// before processing define()/lookup() calls so source resolution works.
		this.trackImports(node);
		this.trackModuleObjectAliases(node);
		this.trackCollectionAliases(node, sourceFile);

		// Check for define() calls
		if (this.isDefineCall(node)) {
			this.processDefineCall(node as ts.CallExpression, sourceFile);
		}

		// Check for lazy() calls
		if (this.isLazyCall(node)) {
			this.processLazyCall(node as ts.CallExpression, sourceFile);
		}

		// Check for decorate() decorator
		if (this.isDecorateDecorator(node)) {
			this.processDecorateDecorator(node as ts.Decorator, sourceFile, currentClass);
		}

		// Check for type usages (new Type(), type annotations, etc.)
		this.collectUsage(node, sourceFile);

		// Check for EDS patterns (wrap, current, getFlow, etc.)
		this.collectEDS(node, sourceFile);

		// Check for native flow patterns (property access, method calls, etc.)
		this.collectFlow(node, sourceFile);

		// Check for framework instrumentation points (vocabulary supplied
		// by plugins; syntactic only — no type checker)
		this.collectInstrumentation(node, sourceFile);

		// Collect referenced-type declarations (aliases, classes, interfaces)
		// per file, and the file's import wiring, for import-aware resolution
		this.trackReferencedTypeDeclaration(node);
		this.trackReferencedTypeImport(node);
		this.trackReferencedTypeReExport(node);
		this.trackReferencedTypeConstArray(node);

		// Track same-file function bindings so EDS can resolve wrap(fn)
		// arguments without the type checker (best effort, last wins)
		if (ts.isFunctionDeclaration(node) && node.name) {
			const key = `${sourceFile.fileName}#${node.name.text}`;
			this.functionBindings.set(key, node);
		}
		if (
			ts.isVariableDeclaration(node) &&
			ts.isIdentifier(node.name) &&
			node.initializer &&
			(ts.isArrowFunction(node.initializer) || ts.isFunctionExpression(node.initializer))
		) {
			const key = `${sourceFile.fileName}#${node.name.text}`;
			this.functionBindings.set(key, node.initializer);
		}

		// Track class declarations for decorator parent lookup
		if (ts.isClassDeclaration(node)) {
			// Visit children with this class as the current context
			ts.forEachChild(node, child => this.visitNode(child, sourceFile, node));
		} else {
			// Recursively visit children
			ts.forEachChild(node, child => this.visitNode(child, sourceFile, currentClass));
		}
	}

	/**
	 * Track imports from 'mnemonica' so aliases of the module object and
	 * createTypesCollection are recognized without relying on the type checker.
	 */
	private trackImports (node: ts.Node): void {
		if (!ts.isImportDeclaration(node)) {
			return;
		}

		const { moduleSpecifier } = node;
		if (!ts.isStringLiteral(moduleSpecifier) || moduleSpecifier.text !== 'mnemonica') {
			return;
		}

		const clause = node.importClause;
		if (!clause) {
			return;
		}

		// import { mnemonica, createTypesCollection } from 'mnemonica'
		if (clause.namedBindings && ts.isNamedImports(clause.namedBindings)) {
			for (const element of clause.namedBindings.elements) {
				const localName = element.name.text;
				const importedName = element.propertyName
					? element.propertyName.text
					: localName;
				if (importedName === 'mnemonica') {
					this.moduleObjectVariables.add(localName);
				}
				if (importedName === 'createTypesCollection') {
					this.createTypesCollectionVariables.add(localName);
				}
				let fileImports = this.mnemonicaNamedImports.get(this.currentReferencedTypeFile);
				if (!fileImports) {
					fileImports = new Map<string, string>();
					this.mnemonicaNamedImports.set(this.currentReferencedTypeFile, fileImports);
				}
				fileImports.set(localName, importedName);
			}
		}

		// import * as mnemonica from 'mnemonica'
		if (clause.namedBindings && ts.isNamespaceImport(clause.namedBindings)) {
			this.moduleObjectVariables.add(clause.namedBindings.name.text);
		}

		// import mnemonica from 'mnemonica' (default import) — treat as module object too
		if (clause.name) {
			this.moduleObjectVariables.add(clause.name.text);
		}
	}

	/**
	 * Record a named referenced-type declaration (type alias, class, or
	 * interface) for the file currently being visited.
	 */
	private trackReferencedTypeDeclaration (node: ts.Node): void {
		// Namespaces are the middle segments of qualified references
		// (models.Inner.Crate) — recorded separately from the plain-name
		// declaration table (string-named `module '…'` declarations are
		// ambient externals and stay out)
		if (ts.isModuleDeclaration(node) && ts.isIdentifier(node.name) &&
			node.body && ts.isModuleBlock(node.body)) {
			const namespaceFilePath = this.currentReferencedTypeFile;
			let namespaces = this.referencedTypeNamespaces.get(namespaceFilePath);
			if (!namespaces) {
				namespaces = new Map<string, ts.ModuleDeclaration>();
				this.referencedTypeNamespaces.set(namespaceFilePath, namespaces);
			}
			namespaces.set(node.name.text, node);
			return;
		}

		let name = '';
		let kind: ReferencedTypeDeclaration['kind'] | undefined;
		let declNode: ReferencedTypeDeclaration['node'] | undefined;

		if (ts.isTypeAliasDeclaration(node) && ts.isIdentifier(node.name)) {
			name = node.name.text;
			kind = 'alias';
			declNode = node;
		} else if (ts.isClassDeclaration(node) && node.name) {
			name = node.name.text;
			kind = 'class';
			declNode = node;
		} else if (ts.isInterfaceDeclaration(node) && ts.isIdentifier(node.name)) {
			name = node.name.text;
			kind = 'interface';
			declNode = node;
		}

		if (!kind || !declNode || !name) {
			return;
		}

		const filePath = this.currentReferencedTypeFile;
		let decls = this.referencedTypeDecls.get(filePath);
		if (!decls) {
			decls = new Map<string, ReferencedTypeDeclaration>();
			this.referencedTypeDecls.set(filePath, decls);
		}
		const entry: ReferencedTypeDeclaration = { kind, node : declNode, file : filePath };
		decls.set(name, entry);

		// `export default class Foo {}` is also reachable under the 'default'
		// binding for default importers
		if (kind === 'class') {
			const classNode = declNode as ts.ClassDeclaration;
			const isExported = classNode.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword) ?? false;
			const isDefault = classNode.modifiers?.some(m => m.kind === ts.SyntaxKind.DefaultKeyword) ?? false;
			if (isExported && isDefault) {
				decls.set('default', entry);
			}
		}
	}

	/**
	 * Record consts initialized with an array literal (optionally wrapped in
	 * `as const` / `satisfies`), so a `typeof statusList[number]` field type
	 * expands to the element literal union — the generated file carries no
	 * imports, so emitting the bare `typeof statusList` query would be an
	 * unresolvable name downstream. First binding wins: a nested shadow
	 * must not replace the module-level const the typeof refers to.
	 */
	private trackReferencedTypeConstArray (node: ts.Node): void {
		if (!ts.isVariableDeclaration(node) || !ts.isIdentifier(node.name) || !node.initializer) {
			return;
		}
		const { initializer: rawInitializer } = node;
		let initializer: ts.Expression = rawInitializer;
		while (
			ts.isAsExpression(initializer) ||
			ts.isSatisfiesExpression(initializer) ||
			// the angle-bracket assertion spelling (`<const>[…]`) is the
			// same const-array marker as the `as const` form (F17)
			ts.isTypeAssertionExpression(initializer)
		) {
			initializer = initializer.expression;
		}
		if (!ts.isArrayLiteralExpression(initializer)) {
			return;
		}
		const filePath = this.currentReferencedTypeFile;
		let consts = this.referencedTypeConstArrays.get(filePath);
		if (!consts) {
			consts = new Map<string, ts.ArrayLiteralExpression>();
			this.referencedTypeConstArrays.set(filePath, consts);
		}
		if (!consts.has(node.name.text)) {
			consts.set(node.name.text, initializer);
		}
	}

	/**
	 * Find the array literal behind a module const referenced through
	 * `typeof`: the declaring file's own consts first (the F13 case is a
	 * NON-exported const in the same module as the expanded class), then —
	 * when the file imports the name — the imported module's consts.
	 * External modules are never analyzed, so those yield nothing.
	 */
	private findReferencedConstArray (
		name: string,
		fromFile: string
	): ts.ArrayLiteralExpression | undefined {
		const local = this.referencedTypeConstArrays.get(fromFile)?.get(name);
		if (local) {
			return local;
		}
		const imported = this.referencedTypeImports.get(fromFile)?.get(name);
		if (!imported || imported.isNamespace) {
			return undefined;
		}
		const resolution = this.resolveReferencedTypeModule(imported.specifier, fromFile);
		if (!resolution || resolution.isExternal) {
			return undefined;
		}
		const found = this.referencedTypeConstArrays.get(resolution.resolvedPath)?.get(imported.originalName);
		return found;
	}

	/**
	 * Element literal types of a tracked const array: every element must be
	 * a plain literal (optionally wrapped in `as const` / `satisfies` /
	 * `<const>` assertions) — string, numeric (unary `-`/`+` preserved),
	 * boolean, or null. Spreads, identifiers, and nested arrays mean the
	 * union is not statically visible and yield undefined, so the caller
	 * degrades the field to `unknown` rather than guessing.
	 */
	private literalTypesOfArray (arrayLiteral: ts.ArrayLiteralExpression): string[] | undefined {
		const literals: string[] = [];
		for (const element of arrayLiteral.elements) {
			if (ts.isSpreadElement(element)) {
				return undefined;
			}
			const literal = this.literalTypeOfExpression(element);
			if (literal === undefined) {
				return undefined;
			}
			literals.push(literal);
		}
		if (literals.length === 0) {
			return undefined;
		}
		const result = literals;
		return result;
	}

	/**
	 * The literal type of one array element: a plain literal (optionally
	 * wrapped in `as const` / `satisfies` / assertion expressions) —
	 * string, numeric (unary `-`/`+` preserved), boolean, or null.
	 * Anything else yields undefined.
	 */
	private literalTypeOfExpression (expr: ts.Expression): string | undefined {
		let inner: ts.Expression = expr;
		while (ts.isAsExpression(inner) || ts.isSatisfiesExpression(inner) || ts.isTypeAssertionExpression(inner)) {
			inner = inner.expression;
		}
		if (ts.isStringLiteral(inner) || ts.isNoSubstitutionTemplateLiteral(inner)) {
			const literal = `'${inner.text}'`;
			return literal;
		}
		if (ts.isPrefixUnaryExpression(inner) && ts.isNumericLiteral(inner.operand)) {
			if (inner.operator === ts.SyntaxKind.MinusToken) {
				const negative = `-${inner.operand.text}`;
				return negative;
			}
			if (inner.operator === ts.SyntaxKind.PlusToken) {
				return inner.operand.text;
			}
			return undefined;
		}
		if (ts.isNumericLiteral(inner)) {
			return inner.text;
		}
		if (inner.kind === ts.SyntaxKind.TrueKeyword) {
			return 'true';
		}
		if (inner.kind === ts.SyntaxKind.FalseKeyword) {
			return 'false';
		}
		if (inner.kind === ts.SyntaxKind.NullKeyword) {
			return 'null';
		}
		return undefined;
	}

	/**
	 * F22: the const-assertion check shared by the value-level and
	 * declaration-level paths — `expr as const` and `<const>expr` parse
	 * identically (a TypeReferenceNode named 'const'). General `<T>expr`
	 * assertions never match.
	 */
	private isConstAssertionType (type: ts.TypeNode): boolean {
		const constAssertion = ts.isTypeReferenceNode(type) &&
			ts.isIdentifier(type.typeName) &&
			type.typeName.text === 'const';
		return constAssertion;
	}

	/**
	 * The array literal behind a value-level element access: inline
	 * (`(<const>[…])[0]`, `([…] as const)[1]`), parenthesized, or a
	 * tracked module const array (`const x = <const>[…]` / `x[0]`, F17
	 * tracking). Only const assertions are unwrapped — general
	 * assertions stay unknown (F22 scope boundary).
	 */
	private constArrayLiteralOf (expr: ts.Expression): ts.ArrayLiteralExpression | undefined {
		let current: ts.Expression = expr;
		while (ts.isParenthesizedExpression(current)) {
			current = current.expression;
		}
		if (ts.isArrayLiteralExpression(current)) {
			return current;
		}
		if ((ts.isAsExpression(current) || ts.isTypeAssertionExpression(current)) &&
			this.isConstAssertionType(current.type)) {
			const inner = current.expression;
			const literal = ts.isArrayLiteralExpression(inner) ? inner : undefined;
			return literal;
		}
		if (ts.isIdentifier(current)) {
			const tracked = this.referencedTypeConstArrays.get(this.currentReferencedTypeFile)?.get(current.text);
			return tracked;
		}
		return undefined;
	}

	/**
	 * Emit-type for `typeof name` when `name` is a tracked const array: the
	 * union of its element literal types (`'active' | 'closed'`). Every
	 * other typeof source — non-array consts, functions, classes, names not
	 * tracked at all — yields undefined, so the caller degrades the field
	 * to `unknown`: a bare `typeof name` emitted into types.ts has no
	 * import to resolve against downstream.
	 */
	private typeOfConstArrayUnion (name: string, fromFile: string): string | undefined {
		const arrayLiteral = this.findReferencedConstArray(name, fromFile);
		if (!arrayLiteral) {
			return undefined;
		}
		const literals = this.literalTypesOfArray(arrayLiteral);
		if (!literals) {
			return undefined;
		}
		const union = literals.join(' | ');
		return union;
	}

	/**
	 * Record the importing file's named/namespace/default import bindings so
	 * referenced-type names resolve through the file's own import statements
	 * (F10) rather than a program-wide name map.
	 */
	private trackReferencedTypeImport (node: ts.Node): void {
		if (!ts.isImportDeclaration(node)) {
			return;
		}
		const { moduleSpecifier } = node;
		if (!ts.isStringLiteral(moduleSpecifier)) {
			return;
		}
		const clause = node.importClause;
		if (!clause) {
			return;
		}

		const filePath = this.currentReferencedTypeFile;
		let imports = this.referencedTypeImports.get(filePath);
		if (!imports) {
			imports = new Map<string, ReferencedTypeImport>();
			this.referencedTypeImports.set(filePath, imports);
		}

		// import { SharedShape } from '…' / import { SharedShape as S } from '…'
		if (clause.namedBindings && ts.isNamedImports(clause.namedBindings)) {
			for (const element of clause.namedBindings.elements) {
				const localName = element.name.text;
				const originalName = element.propertyName ? element.propertyName.text : localName;
				imports.set(localName, {
					originalName,
					specifier   : moduleSpecifier.text,
					isNamespace : false
				});
			}
		}

		// import * as models from '…' — resolved when a qualified name
		// (models.SharedShape) is encountered
		if (clause.namedBindings && ts.isNamespaceImport(clause.namedBindings)) {
			imports.set(clause.namedBindings.name.text, {
				originalName : '',
				specifier    : moduleSpecifier.text,
				isNamespace  : true
			});
		}

		// import SharedShape from '…' (default import)
		if (clause.name) {
			imports.set(clause.name.text, {
				originalName : 'default',
				specifier    : moduleSpecifier.text,
				isNamespace  : false
			});
		}
	}

	/**
	 * Record re-export wiring (`export { X } from '…'`, `export * from '…'`,
	 * `export { X as Y }`) so resolution can chase barrels to the origin
	 * module. Mirrors ModuleGraphBuilder.resolveOrigin, name-based only.
	 */
	private trackReferencedTypeReExport (node: ts.Node): void {
		if (!ts.isExportDeclaration(node)) {
			return;
		}
		const filePath = this.currentReferencedTypeFile;
		const { moduleSpecifier } = node;
		const specifierText = moduleSpecifier && ts.isStringLiteral(moduleSpecifier)
			? moduleSpecifier.text
			: undefined;

		if (node.exportClause && ts.isNamedExports(node.exportClause)) {
			for (const element of node.exportClause.elements) {
				const exportedName = element.name.text;
				const localName = element.propertyName ? element.propertyName.text : exportedName;
				if (specifierText) {
					// export { X } from '…' / export { X as Y } from '…'
					let reExports = this.referencedTypeReExports.get(filePath);
					if (!reExports) {
						reExports = new Map<string, string>();
						this.referencedTypeReExports.set(filePath, reExports);
					}
					reExports.set(exportedName, specifierText);
				} else if (localName !== exportedName) {
					// export { X as Y } — same-file alias of a local declaration
					let aliases = this.referencedTypeExportAliases.get(filePath);
					if (!aliases) {
						aliases = new Map<string, string>();
						this.referencedTypeExportAliases.set(filePath, aliases);
					}
					aliases.set(exportedName, localName);
				}
			}
			return;
		}

		if (node.exportClause && ts.isNamespaceExport(node.exportClause)) {
			// `export * as ns from '…'` — a nested module namespace; middle
			// segments of qualified references (barrel.Deep.Gadget) chase it
			if (specifierText) {
				let stars = this.referencedTypeNamespaceStars.get(filePath);
				if (!stars) {
					stars = new Map<string, string>();
					this.referencedTypeNamespaceStars.set(filePath, stars);
				}
				stars.set(node.exportClause.name.text, specifierText);
			}
			return;
		}

		if (!node.exportClause && specifierText) {
			// export * from '…'
			let stars = this.referencedTypeExportStars.get(filePath);
			if (!stars) {
				stars = [];
				this.referencedTypeExportStars.set(filePath, stars);
			}
			stars.push(specifierText);
		}
	}

	/**
	 * Resolve a module specifier from a containing file with the program's
	 * compilerOptions (tsconfig `paths`, extensionless imports, index files).
	 * Module resolution only — the no-getTypeChecker() precedent stays.
	 */
	private resolveReferencedTypeModule (specifier: string, containingFile: string):
		ReferencedTypeResolution | undefined {
		const cacheKey = `${containingFile}::${specifier}`;
		if (this.referencedTypeResolutionCache.has(cacheKey)) {
			const cached = this.referencedTypeResolutionCache.get(cacheKey);
			return cached === undefined ? undefined : cached;
		}

		const resolution = ts.resolveModuleName(
			specifier,
			containingFile,
			this.referencedTypeCompilerOptions,
			ts.sys
		).resolvedModule;

		const result: ReferencedTypeResolution | undefined = resolution
			? {
				resolvedPath : nodePath.resolve(resolution.resolvedFileName),
				isExternal   : !!resolution.isExternalLibraryImport
			}
			: undefined;

		this.referencedTypeResolutionCache.set(cacheKey, result);
		const finalResult = result;
		return finalResult;
	}

	/**
	 * Look up a name in one resolved module, chasing re-export barrels with a
	 * bounded depth. External (node_modules) modules hold no in-project
	 * declarations and stop the chase.
	 */
	private findReferencedTypeInModule (
		modulePath: string,
		name: string,
		depth: number
	): ReferencedTypeDeclaration | undefined {
		if (depth > MAX_REEXPORT_CHASE_DEPTH) {
			return undefined;
		}

		const decls = this.referencedTypeDecls.get(modulePath);
		const direct = decls?.get(name);
		if (direct) {
			return direct;
		}
		// export { X as Y } — resolve through the local name
		const localAlias = this.referencedTypeExportAliases.get(modulePath)?.get(name);
		if (localAlias) {
			const aliased = decls?.get(localAlias);
			if (aliased) {
				return aliased;
			}
		}

		const reExports = this.referencedTypeReExports.get(modulePath);
		const reExportSpecifier = reExports?.get(name);
		if (reExportSpecifier) {
			const nextResolution = this.resolveReferencedTypeModule(reExportSpecifier, modulePath);
			if (nextResolution && !nextResolution.isExternal) {
				const found = this.findReferencedTypeInModule(nextResolution.resolvedPath, name, depth + 1);
				if (found) {
					return found;
				}
			}
		}

		const stars = this.referencedTypeExportStars.get(modulePath);
		if (stars) {
			for (const starSpecifier of stars) {
				const nextResolution = this.resolveReferencedTypeModule(starSpecifier, modulePath);
				if (!nextResolution || nextResolution.isExternal) {
					continue;
				}
				const found = this.findReferencedTypeInModule(nextResolution.resolvedPath, name, depth + 1);
				if (found) {
					return found;
				}
			}
		}

		return undefined;
	}

	/**
	 * Resolve a referenced type name as used in fromFile, import-aware:
	 *   1. the file's own import statements (relative + tsconfig paths,
	 *      chased through re-export barrels),
	 *   2. the file's local declarations,
	 *   3. the unique same-named declaration across scanned files.
	 * Returns undefined when nothing matches (or the match is ambiguous),
	 * in which case the caller falls back to `unknown`.
	 */
	private resolveReferencedTypeDeclaration (
		name: string,
		fromFile: string
	): ReferencedTypeDeclaration | undefined {
		// 1. the file's own imports win — an import is never shadowed by a
		// same-named local declaration elsewhere in the program (F10)
		const imported = this.referencedTypeImports.get(fromFile)?.get(name);
		if (imported && !imported.isNamespace) {
			const resolution = this.resolveReferencedTypeModule(imported.specifier, fromFile);
			if (resolution && !resolution.isExternal) {
				const found = this.findReferencedTypeInModule(resolution.resolvedPath, imported.originalName, 0);
				if (found) {
					return found;
				}
			}
		}

		// 2. local declaration in the referencing file itself
		const local = this.referencedTypeDecls.get(fromFile)?.get(name);
		if (local) {
			return local;
		}

		// 3. program-wide fallback, unique declaration only — ambiguity and
		// absence both yield undefined (the caller emits `unknown`).
		// External/ambient declarations (.d.ts, node_modules) do not
		// participate: a user-local declaration always wins over a
		// package-declared same-named type (the plain-TS tier of the
		// identity law; ambiguity among the remaining declarations is
		// validated separately as a hard fail)
		let unique: ReferencedTypeDeclaration | undefined;
		let count = 0;
		for (const [ filePath, decls ] of this.referencedTypeDecls) {
			if (this.isExternalDeclFile(filePath)) {
				continue;
			}
			const candidate = decls.get(name);
			if (candidate) {
				count++;
				unique = candidate;
				if (count > 1) {
					return undefined;
				}
			}
		}

		const result = count === 1 ? unique : undefined;
		return result;
	}

	/**
	 * External/ambient declaration files (.d.ts, anything under
	 * node_modules) never participate in plain-TS referenced-type
	 * resolution or the ambiguity law: they are not project source, the
	 * CLI never analyzes them, and a user-local declaration always wins
	 * over a package-declared same-named type.
	 */
	private isExternalDeclFile (file: string): boolean {
		const external = file.endsWith('.d.ts') ||
			file.includes(`${nodePath.sep}node_modules${nodePath.sep}`);
		return external;
	}

	/**
	 * Properties of a referenced class/interface/alias-of-literal declaration,
	 * shared by `this:`-parameter expansion and inline type emission.
	 * Inherited members are included: the extends chain is walked
	 * (depth-capped, cycle-guarded) and parent fields merge first, the
	 * declaration's own fields overriding on name clash.
	 */
	private referencedDeclarationProperties (decl: ReferencedTypeDeclaration):
		Map<string, PropertyInfo> {
		const visited = new Set<string>();
		const properties = this.referencedDeclarationPropertiesInner(decl, visited, 0);
		return properties;
	}

	private referencedDeclarationPropertiesInner (
		decl: ReferencedTypeDeclaration,
		visited: Set<string>,
		depth: number
	): Map<string, PropertyInfo> {
		const ownProperties = new Map<string, PropertyInfo>();
		const declNode = decl.node as ts.ClassDeclaration | ts.InterfaceDeclaration;
		const declName = declNode.name && ts.isIdentifier(declNode.name) ? declNode.name.text : '';
		const visitKey = `${decl.kind}:${decl.file}:${declName}`;
		if (depth > MAX_HERITAGE_DEPTH || visited.has(visitKey)) {
			return ownProperties;
		}
		visited.add(visitKey);

		if (decl.kind === 'class') {
			const classProps = this.extractClassProperties(decl.node as ts.ClassDeclaration);
			for (const [ name, info ] of classProps) {
				ownProperties.set(name, info);
			}
		} else if (decl.kind === 'interface') {
			const iface = decl.node as ts.InterfaceDeclaration;
			this.collectTypeElementProperties([ ...iface.members ], ownProperties);
		} else {
			const aliasType = (decl.node as ts.TypeAliasDeclaration).type;
			if (ts.isTypeLiteralNode(aliasType)) {
				this.collectTypeElementProperties([ ...aliasType.members ], ownProperties);
			} else {
				return ownProperties;
			}
		}

		// heritage merges parent fields first; the declaration's own fields
		// override on name clash (later bases override earlier ones)
		const merged = new Map<string, PropertyInfo>();
		for (const baseDecl of this.resolveHeritageDeclarations(decl)) {
			const baseProps = this.referencedDeclarationPropertiesInner(baseDecl, visited, depth + 1);
			for (const [ name, info ] of baseProps) {
				merged.set(name, info);
			}
		}
		for (const [ name, info ] of ownProperties) {
			merged.set(name, info);
		}
		return merged;
	}

	/**
	 * Property signatures of interface/alias type-literal members, into
	 * the given map.
	 */
	private collectTypeElementProperties (
		members: readonly ts.TypeElement[],
		properties: Map<string, PropertyInfo>
	): void {
		for (const member of members) {
			if (ts.isPropertySignature(member) && ts.isIdentifier(member.name)) {
				const propName = member.name.text;
				const type = this.inferType(member.type);
				properties.set(propName, {
					name     : propName,
					type,
					optional : !!member.questionToken,
				});
			}
		}
	}

	/**
	 * Resolve the heritage clause of a class (`extends Base`) or interface
	 * (`extends A, B`) to referenced-type declarations through the SAME
	 * import-aware machinery as plain references (the declaring file's own
	 * imports first, then its locals, then the unique program-wide
	 * declaration). Unresolvable or external bases yield nothing — their
	 * inherited fields simply stay absent, same as before this walk
	 * existed. Mixin calls (`extends mixin(X)`) and namespace access are
	 * not followed.
	 */
	private resolveHeritageDeclarations (decl: ReferencedTypeDeclaration): ReferencedTypeDeclaration[] {
		const { heritageClauses } = (decl.node as ts.ClassDeclaration | ts.InterfaceDeclaration);
		if (!heritageClauses) {
			return [];
		}
		const bases: ReferencedTypeDeclaration[] = [];
		for (const clause of heritageClauses) {
			if (clause.token !== ts.SyntaxKind.ExtendsKeyword) {
				continue;
			}
			for (const heritageType of clause.types) {
				if (!ts.isIdentifier(heritageType.expression)) {
					continue;
				}
				const baseName = heritageType.expression.text;
				const baseDecl = this.resolveReferencedTypeDeclaration(baseName, decl.file);
				if (baseDecl) {
					bases.push(baseDecl);
				}
			}
		}
		const result = bases;
		return result;
	}

	/**
	 * Expand a referenced-type declaration to a self-contained type string
	 * for emission into generated files: type aliases through inferType,
	 * classes and interfaces through their (public, non-method) fields.
	 * Nested references resolve against the declaring file while expanding.
	 */
	private expandReferencedTypeDeclaration (decl: ReferencedTypeDeclaration): string | undefined {
		const referencingFile = this.currentReferencedTypeFile;
		this.currentReferencedTypeFile = decl.file;
		try {
			const result = this.expandReferencedTypeDeclarationInner(decl);
			return result;
		} finally {
			this.currentReferencedTypeFile = referencingFile;
		}
	}

	private expandReferencedTypeDeclarationInner (decl: ReferencedTypeDeclaration): string | undefined {
		if (decl.kind === 'alias') {
			const aliasNode = decl.node as ts.TypeAliasDeclaration;
			const aliasName = ts.isIdentifier(aliasNode.name) ? aliasNode.name.text : '';
			if (aliasName && this.expandingReferencedAliases.has(aliasName)) {
				// Self-referential alias chain — bail out
				return 'unknown';
			}
			if (aliasName) {
				this.expandingReferencedAliases.add(aliasName);
			}
			const expanded = this.inferType(aliasNode.type);
			if (aliasName) {
				this.expandingReferencedAliases.delete(aliasName);
			}
			return expanded;
		}

		const declProperties = this.referencedDeclarationProperties(decl);
		const props = Array.from(declProperties.entries()).map(([ propName, info ]) => {
			const optional = info.optional ? '?' : '';
			return `${propName}${optional}: ${info.type}`;
		});

		const result = `{ ${props.join('; ')} }`;
		return result;
	}

	/**
	 * Resolve a simple (non-qualified) type reference: import-aware
	 * declaration expansion first, then the InstanceType<typeof X> pattern,
	 * then mnemonica graph types; known globals keep their bare name and
	 * anything else falls back to `unknown` so generated files never carry
	 * an unresolvable bare name. Returns undefined when the caller should
	 * keep the generic spelling (handled separately).
	 */
	private resolveSimpleTypeReference (
		typeName: string,
		typeArgs?: ts.NodeArray<ts.TypeNode>,
		refNode?: ts.Node
	): string | undefined {
		// Import-aware referenced-type declaration (F10)
		const decl = this.resolveReferencedTypeDeclaration(typeName, this.currentReferencedTypeFile);
		if (decl) {
			const expanded = this.expandReferencedTypeDeclaration(decl);
			if (expanded !== undefined) {
				return expanded;
			}
			const unknownResult = 'unknown';
			return unknownResult;
		}

		// Mnemonica-graph identity law: path-aware resolution (value scope,
		// imports, nearest-chain, root, program-wide). Ambiguity between
		// real graph types is a hard failure; a name no graph type carries
		// stays in the plain-TS soft scope and falls to `unknown`.
		const graphResult = this.resolveGraphTypeName(typeName);
		if (graphResult.status === 'unique') {
			// Handle InstanceType<typeof X> pattern -> convert to Parent_X
			if (typeName === 'InstanceType' && typeArgs && typeArgs.length === 1) {
				const [ arg ] = typeArgs;
				if (arg.kind === ts.SyntaxKind.TypeQuery) {
					const typeQuery = arg as ts.TypeQueryNode;
					if (ts.isIdentifier(typeQuery.exprName)) {
						const queryResult = this.resolveGraphTypeName(typeQuery.exprName.text);
						if (queryResult.status === 'unique') {
							// Convert full path with dots to underscores: Usages.UsageEntry -> Usages_UsageEntry
							return queryResult.node.fullPath.replace(/\./g, '_');
						}
						if (queryResult.status === 'ambiguous') {
							this.recordGraphReferenceError(typeQuery.exprName.text, typeQuery, queryResult);
						}
						// Not a known mnemonica type — no bare emission
						return 'unknown';
					}
				}
			}
			if (!typeArgs || typeArgs.length === 0) {
				// Convert full path with dots to underscores: Usages.UsageEntry -> Usages_UsageEntry
				return graphResult.node.fullPath.replace(/\./g, '_');
			}
			// Generic use of a graph type keeps its simple name; the
			// generator upgrades it to the full-path instance type name
			return `${typeName}<${typeArgs.map(a => this.inferType(a)).join(', ')}>`;
		}
		if (graphResult.status === 'ambiguous') {
			this.recordGraphReferenceError(typeName, refNode ?? this.currentReferencedTypeFile, graphResult);
		}

		if (typeArgs && typeArgs.length > 0) {
			if (KNOWN_GLOBAL_TYPES.has(typeName)) {
				const genericResult = `${typeName}<${typeArgs.map(a => this.inferType(a)).join(', ')}>`;
				return genericResult;
			}
			// Generic reference to a non-global, non-graph type cannot be
			// emitted bare into the generated file
			if (refNode) {
				this.recordPlainTypeReferenceSite(typeName, refNode);
			}
			return 'unknown';
		}

		const fallbackResult = this.unresolvedTypeReferenceFallback(typeName, refNode);
		return fallbackResult;
	}

	/**
	 * Resolve a qualified type reference (models.Inner.Crate) through the
	 * current file's namespace imports. The chain's head must be a namespace
	 * import; middle segments descend through namespace declarations, named
	 * re-exports of namespaces, and `export * as ns from '…'` barrels (each
	 * segment consumed exactly once, so the walk cannot cycle); the final
	 * segment resolves to a declaration which is expanded inline. When the
	 * precise walk finds nothing, the legacy rightmost-name lookup in the
	 * head module keeps one-level forms (models.Type) working — nested
	 * declarations are recorded by plain name there too. Returns undefined
	 * when the head is not a namespace import or nothing resolves.
	 */
	private inferQualifiedTypeReference (typeRef: ts.TypeReferenceNode): string | undefined {
		if (!ts.isQualifiedName(typeRef.typeName)) {
			return undefined;
		}

		// flatten the qualified name chain: models.Inner.Crate → ['models', 'Inner', 'Crate']
		const segments: string[] = [];
		let chain: ts.EntityName = typeRef.typeName;
		while (ts.isQualifiedName(chain)) {
			segments.unshift(chain.right.text);
			chain = chain.left;
		}
		segments.unshift(chain.text);

		const namespaceImport = this.referencedTypeImports.get(this.currentReferencedTypeFile)?.get(segments[ 0 ]);
		if (!namespaceImport || !namespaceImport.isNamespace) {
			return undefined;
		}

		const resolution = this.resolveReferencedTypeModule(namespaceImport.specifier, this.currentReferencedTypeFile);
		if (!resolution || resolution.isExternal) {
			return undefined;
		}

		// descend the middle segments: a module context resolves the segment
		// as a namespace declaration / namespace re-export; a namespace-block
		// context resolves it as a nested namespace declaration
		let qualifier: { modulePath: string; block?: ts.ModuleBlock } | undefined = {
			modulePath : resolution.resolvedPath
		};
		for (let i = 1; i < segments.length - 1 && qualifier; i++) {
			const segment = segments[ i ];
			if (qualifier.block) {
				const nested = this.findNamespaceInBlock(qualifier.block, segment);
				if (nested?.body && ts.isModuleBlock(nested.body)) {
					qualifier = { modulePath : qualifier.modulePath, block : nested.body };
					continue;
				}
				qualifier = undefined;
				break;
			}
			const namespaceDecl: ts.ModuleDeclaration | undefined =
				this.referencedTypeNamespaces.get(qualifier.modulePath)?.get(segment);
			if (namespaceDecl?.body && ts.isModuleBlock(namespaceDecl.body)) {
				qualifier = { modulePath : qualifier.modulePath, block : namespaceDecl.body };
				continue;
			}
			const starSpecifier = this.referencedTypeNamespaceStars.get(qualifier.modulePath)?.get(segment);
			if (starSpecifier) {
				const nextResolution = this.resolveReferencedTypeModule(starSpecifier, qualifier.modulePath);
				if (nextResolution && !nextResolution.isExternal) {
					qualifier = { modulePath : nextResolution.resolvedPath };
					continue;
				}
			}
			const reExportSpecifier = this.referencedTypeReExports.get(qualifier.modulePath)?.get(segment);
			if (reExportSpecifier) {
				const nextResolution = this.resolveReferencedTypeModule(reExportSpecifier, qualifier.modulePath);
				const reExported: ts.ModuleDeclaration | undefined =
					nextResolution && !nextResolution.isExternal
						? this.referencedTypeNamespaces.get(nextResolution.resolvedPath)?.get(segment)
						: undefined;
				if (reExported?.body && ts.isModuleBlock(reExported.body)) {
					qualifier = { modulePath : nextResolution!.resolvedPath, block : reExported.body };
					continue;
				}
			}
			qualifier = undefined;
		}

		const finalName = segments[ segments.length - 1 ];
		let decl: ReferencedTypeDeclaration | undefined;
		if (qualifier?.block) {
			decl = this.findReferencedTypeInBlock(qualifier.block, qualifier.modulePath, finalName);
		} else if (qualifier) {
			decl = this.findReferencedTypeInModule(qualifier.modulePath, finalName, 0);
		}
		// legacy fallback: rightmost name anywhere in the head module
		// (namespace-nested declarations are also recorded by plain name)
		if (!decl) {
			decl = this.findReferencedTypeInModule(resolution.resolvedPath, finalName, 0);
		}
		if (!decl) {
			return undefined;
		}

		const expanded = this.expandReferencedTypeDeclaration(decl);
		return expanded;
	}

	/**
	 * Find a namespace declaration by name directly inside a module block.
	 */
	private findNamespaceInBlock (block: ts.ModuleBlock, name: string): ts.ModuleDeclaration | undefined {
		for (const statement of block.statements) {
			if (ts.isModuleDeclaration(statement) && ts.isIdentifier(statement.name) &&
				statement.name.text === name) {
				const result = statement;
				return result;
			}
		}
		return undefined;
	}

	/**
	 * Find a named type declaration (alias, class, interface) directly inside
	 * a namespace block — the final segment of a descended qualified chain.
	 */
	private findReferencedTypeInBlock (
		block: ts.ModuleBlock,
		filePath: string,
		name: string
	): ReferencedTypeDeclaration | undefined {
		for (const statement of block.statements) {
			if (ts.isTypeAliasDeclaration(statement) && ts.isIdentifier(statement.name) &&
				statement.name.text === name) {
				const result: ReferencedTypeDeclaration = { kind : 'alias', node : statement, file : filePath };
				return result;
			}
			if (ts.isClassDeclaration(statement) && statement.name && statement.name.text === name) {
				const result: ReferencedTypeDeclaration = { kind : 'class', node : statement, file : filePath };
				return result;
			}
			if (ts.isInterfaceDeclaration(statement) && ts.isIdentifier(statement.name) &&
				statement.name.text === name) {
				const result: ReferencedTypeDeclaration = { kind : 'interface', node : statement, file : filePath };
				return result;
			}
		}
		return undefined;
	}

	/**
	 * Fallback for a type-reference name that resolves to no declaration and
	 * no graph type: known globals keep their bare name (they resolve without
	 * an import); everything else becomes `unknown` so generated types.ts
	 * never carries an unresolvable bare name (README's documented behavior)
	 * and the site is recorded for the plain-TS ambiguity validation.
	 */
	private unresolvedTypeReferenceFallback (typeName: string, refNode?: ts.Node): string {
		if (KNOWN_GLOBAL_TYPES.has(typeName)) {
			return typeName;
		}
		if (refNode) {
			this.recordPlainTypeReferenceSite(typeName, refNode);
		}
		const result = 'unknown';
		return result;
	}

	/**
	 * Record one define()/lazy()/@decorate() site under its runtime
	 * namespace key. Two sites in one namespace are a same-namespace
	 * duplicate (the runtime throws ALREADY_DECLARED); every site is kept
	 * so the failure can report all locations.
	 */
	private recordDefineSite (namespaceKey: string, location: string): void {
		let sites = this.defineSites.get(namespaceKey);
		if (!sites) {
			sites = [];
			this.defineSites.set(namespaceKey, sites);
		}
		if (!sites.includes(location)) {
			sites.push(location);
		}
	}

	/**
	 * Fatal resolution failures (hard-fail law): same-namespace duplicate
	 * mnemonica definitions plus ambiguous/unresolved mnemonica-graph
	 * references. The CLI prints every location and writes no output.
	 */
	getResolutionErrors (): ResolutionError[] {
		this.validateLookupReferences();
		this.validatePlainTypeReferences();
		const errors: ResolutionError[] = [];
		for (const [ namespaceKey, sites ] of this.defineSites) {
			if (sites.length < 2) {
				continue;
			}
			const displayName = namespaceKey.replace(/^[^:]+::/, '');
			const message = `Duplicate definition of '${displayName}' in one namespace — ` +
				'the mnemonica runtime would throw ALREADY_DECLARED';
			errors.push({ message, locations : [ ...sites ] });
		}
		for (const error of this.graphReferenceErrors) {
			errors.push(error);
		}
		const result = errors;
		return result;
	}

	/**
	 * Resolve a reference to a mnemonica graph type name, import-aware and
	 * path-aware (the hard-fail identity law, mirroring the runtime):
	 *   1. value scope — a tracked top-level binding in the referencing file
	 *      (`const Address = User.define('Address', …)`),
	 *   2. import scope — a binding exported from a module this file imports
	 *      (barrels chased),
	 *   3. nearest-chain — the anchor type's own subtypes first, then each
	 *      ancestor level (relative-first),
	 *   4. root — roots of the anchor's collection,
	 *   5. program-wide — only when exactly one type carries the name.
	 * Ambiguity (several candidates and nothing disambiguates) and absence
	 * are both returned as such — the caller records a hard failure; a bare
	 * first-match name is never emitted.
	 */
	private resolveGraphTypeName (name: string): GraphTypeReferenceResult {
		// 1. value scope in the referencing file itself
		const localBinding = this.fileGraphBindings.get(this.currentReferencedTypeFile)?.get(name);
		if (localBinding) {
			const node = this.graph.findType(localBinding);
			if (node) {
				const valueResult: GraphTypeReferenceResult = { status : 'unique', node };
				return valueResult;
			}
		}

		// 2. import scope — the imported module's exported binding
		const imported = this.referencedTypeImports.get(this.currentReferencedTypeFile)?.get(name);
		if (imported && !imported.isNamespace) {
			const resolution = this.resolveReferencedTypeModule(imported.specifier, this.currentReferencedTypeFile);
			if (resolution && !resolution.isExternal) {
				const fullPath = this.findGraphBindingInModule(resolution.resolvedPath, imported.originalName, 0);
				if (fullPath) {
					const node = this.graph.findType(fullPath);
					if (node) {
						const importResult: GraphTypeReferenceResult = { status : 'unique', node };
						return importResult;
					}
				}
			}
		}

		// 3-5. chain / root / program-wide tiers
		const result = resolveGraphTypeReference(this.graph, name, this.currentGraphAnchor);
		return result;
	}

	/**
	 * Find a graph constructor binding exported by a resolved module,
	 * chasing re-export barrels with a bounded depth.
	 */
	private findGraphBindingInModule (modulePath: string, name: string, depth: number): string | undefined {
		if (depth > MAX_REEXPORT_CHASE_DEPTH) {
			return undefined;
		}

		const direct = this.fileGraphBindings.get(modulePath)?.get(name);
		if (direct) {
			return direct;
		}

		const reExports = this.referencedTypeReExports.get(modulePath);
		const reExportSpecifier = reExports?.get(name);
		if (reExportSpecifier) {
			const nextResolution = this.resolveReferencedTypeModule(reExportSpecifier, modulePath);
			if (nextResolution && !nextResolution.isExternal) {
				const found = this.findGraphBindingInModule(nextResolution.resolvedPath, name, depth + 1);
				if (found) {
					return found;
				}
			}
		}

		const stars = this.referencedTypeExportStars.get(modulePath);
		if (stars) {
			for (const starSpecifier of stars) {
				const nextResolution = this.resolveReferencedTypeModule(starSpecifier, modulePath);
				if (!nextResolution || nextResolution.isExternal) {
					continue;
				}
				const found = this.findGraphBindingInModule(nextResolution.resolvedPath, name, depth + 1);
				if (found) {
					return found;
				}
			}
		}

		return undefined;
	}

	/**
	 * Validate literal lookup() paths recorded during the usages pass
	 * against the complete graph. A lookup path matching no type is what the
	 * runtime answers with `undefined` — the TypeError arrives one line
	 * later at the `new` — so it joins the hard-fail law. The relative-first
	 * step already ran inside resolveLookupPath; whatever was recorded is
	 * the root-resolution result, so a plain findType check is the exact
	 * runtime law. Same-named types elsewhere in the graph are listed as
	 * did-you-mean candidates. Runs once per usages pass (re-armed by
	 * resetUsages); non-literal lookup arguments are never recorded and
	 * stay best-effort.
	 */
	private validateLookupReferences (): void {
		if (this.lookupReferencesValidated) {
			return;
		}
		this.lookupReferencesValidated = true;
		// group sites by path: every failing site of the same path is listed
		const sitesByPath = new Map<string, string[]>();
		for (const ref of this.lookupReferences) {
			const sites = sitesByPath.get(ref.path) ?? [];
			sites.push(ref.location);
			sitesByPath.set(ref.path, sites);
		}
		for (const [ typePath, sites ] of sitesByPath) {
			if (this.graph.findType(typePath)) {
				continue;
			}
			// did-you-mean: types carrying the same name anywhere in the
			// graph (never a first-match pick — the full list only)
			const unprefixed = typePath.replace(/^[^:]+::/, '');
			const lastSegment = unprefixed.split('.').pop() ?? unprefixed;
			const candidates = this.graph.getAllTypes().filter(t => t.name === lastSegment);
			if (candidates.length === 0) {
				const noneError: ResolutionError = {
					message : `Unresolved lookup of mnemonica type '${typePath}': no type at that path — ` +
						'the runtime would return undefined',
					locations : sites,
				};
				this.graphReferenceErrors.push(noneError);
				continue;
			}
			const candidateLocations = candidates.map(n => `${n.sourceFile}:${n.line}:${n.column}`);
			const candidatePaths = candidates.map(n => n.fullPath).join(', ');
			const ambiguousError: ResolutionError = {
				message : `Unresolved lookup of mnemonica type '${typePath}': the runtime would return ` +
					`undefined — ${candidates.length} graph type(s) carry the name ` +
					`off-root (${candidatePaths}); use the full dotted path`,
				locations : [ ...sites, ...candidateLocations ],
			};
			this.graphReferenceErrors.push(ambiguousError);
		}
	}

	/**
	 * Record a plain-TS type reference site that resolved to nothing and
	 * fell back to `unknown`, for the lazily-run ambiguity validation.
	 * Deduped by (name, location): inferType can visit the same node more
	 * than once per pass (constructor params + property inference).
	 */
	private recordPlainTypeReferenceSite (name: string, refNode: ts.Node): void {
		const location = this.nodeLocation(refNode);
		const file = this.currentReferencedTypeFile;
		const already = this.plainTypeReferences.some((ref) => ref.name === name && ref.location === location);
		if (already) {
			return;
		}
		this.plainTypeReferences.push({ name, location, file });
	}

	/**
	 * Project-source declaration files carrying `name` — one entry per
	 * file, so same-file interface merging counts once (not ambiguous).
	 * External/ambient declarations (.d.ts, anything under node_modules)
	 * never count: a user-local declaration always wins over a package-
	 * declared same-named type, so an external collision stays soft.
	 */
	private plainTypeDeclarationFiles (name: string): string[] {
		const files: string[] = [];
		for (const [ file, decls ] of this.referencedTypeDecls) {
			if (!this.isExternalDeclFile(file) && decls.has(name)) {
				files.push(file);
			}
		}
		return files;
	}

	/**
	 * Validate plain-TS type reference sites recorded during the usages
	 * pass against the complete declaration map. A name declared in
	 * several project-source files — with no import in the referencing
	 * file to anchor it — is ambiguous: silently emitting `unknown` would
	 * hide a real type the author meant, so it joins the hard-fail law
	 * (the plain-TS tier of the same identity law as graph references).
	 * Absence (ghost names) and external collisions stay soft `unknown`.
	 * Runs once per usages pass (re-armed by resetUsages), mirroring
	 * validateLookupReferences: recording happens on every pass, but only
	 * the usages pass sees the complete declaration map.
	 */
	private validatePlainTypeReferences (): void {
		if (this.plainTypeReferencesValidated) {
			return;
		}
		this.plainTypeReferencesValidated = true;
		const sitesByName = new Map<string, { name: string; location: string; file: string }[]>();
		for (const ref of this.plainTypeReferences) {
			const sites = sitesByName.get(ref.name) ?? [];
			sites.push(ref);
			sitesByName.set(ref.name, sites);
		}
		for (const [ name, sites ] of sitesByName) {
			// an import binding in the referencing file anchors the name —
			// the author already disambiguated (the import may just point
			// at an unanalyzable external module, which stays soft)
			const unanchored = sites.filter((site) => !this.referencedTypeImports.get(site.file)?.has(name));
			if (unanchored.length === 0) {
				continue;
			}
			const declFiles = this.plainTypeDeclarationFiles(name);
			if (declFiles.length < 2) {
				continue;
			}
			const message = `Ambiguous reference to type '${name}': ${declFiles.length} declarations ` +
				'share the name and no import disambiguates — import the one you mean';
			const declLocations = declFiles.map((file) => this.plainDeclLocation(file, name));
			const error: ResolutionError = {
				message,
				locations : [ ...unanchored.map((site) => site.location), ...declLocations ]
			};
			this.graphReferenceErrors.push(error);
		}
	}

	/**
	 * `file:line:column` of a recorded declaration, for the ambiguity
	 * report. Nodes recorded during traversal keep their positions; a
	 * synthetic/unpositioned node falls back to the file itself.
	 */
	private plainDeclLocation (file: string, name: string): string {
		const decl = this.referencedTypeDecls.get(file)?.get(name);
		const node = decl?.node;
		let location = `${file}:1:1`;
		if (node && node.pos >= 0) {
			const sourceFile = node.getSourceFile();
			const line = sourceFile.getLineAndCharacterOfPosition(node.getStart()).line + 1;
			const column = sourceFile.getLineAndCharacterOfPosition(node.getStart()).character + 1;
			location = `${file}:${line}:${column}`;
		}
		const result = location;
		return result;
	}

	/**
	 * Record a hard-fail graph reference error with the reference site and
	 * every candidate location.
	 */
	private recordGraphReferenceError (
		name: string,
		refNode: ts.Node | string,
		result: Extract<GraphTypeReferenceResult, { status: 'ambiguous' | 'none' }>
	): void {
		const location = typeof refNode === 'string' ? refNode : this.nodeLocation(refNode);
		if (result.status === 'ambiguous') {
			const candidateLocations = result.candidates.map(n => `${n.sourceFile}:${n.line}:${n.column}`);
			const ambiguousMessage = `Ambiguous reference to mnemonica type '${name}': ` +
				`${result.candidates.length} types share the name and neither the parent chain ` +
				'nor the imports disambiguate';
			const ambiguousError: ResolutionError = {
				message   : ambiguousMessage,
				locations : [ location, ...candidateLocations ],
			};
			this.graphReferenceErrors.push(ambiguousError);
			return;
		}
		const unresolvedMessage = `Unresolved reference to mnemonica type '${name}': no type matches ` +
			'by value scope, imports, parent chain, or root path';
		const unresolvedError: ResolutionError = { message : unresolvedMessage, locations : [ location ] };
		this.graphReferenceErrors.push(unresolvedError);
	}

	/**
	 * Location (`file:line:column`) of an AST node, derived without parent
	 * pointers when necessary.
	 */
	private nodeLocation (node: ts.Node): string {
		let current: ts.Node | undefined = node;
		while (current && !ts.isSourceFile(current)) {
			current = current.parent;
		}
		if (!current) {
			const fallback = this.currentReferencedTypeFile;
			return fallback;
		}
		const start = node.getStart(current);
		const { line, character } = ts.getLineAndCharacterOfPosition(current, start);
		const location = `${current.fileName}:${line + 1}:${character + 1}`;
		return location;
	}

	/**
	 * Track aliases of the mnemonica module object, e.g.:
	 *   const m = mnemonica;
	 *   const App = m;
	 */
	private trackModuleObjectAliases (node: ts.Node): void {
		if (!ts.isVariableDeclaration(node) || !ts.isIdentifier(node.name)) {
			return;
		}

		const { initializer } = node;
		if (!initializer) {
			return;
		}

		if (ts.isIdentifier(initializer) && this.moduleObjectVariables.has(initializer.text)) {
			this.moduleObjectVariables.add(node.name.text);
		}
	}

	/**
	 * Track custom collection variables, e.g.:
	 *   const MyCollection = createTypesCollection();
	 *   const Other = MyCollection;
	 *
	 * Also detects Option B user-provided registry interfaces:
	 *   export interface MyCollectionRegistry {}
	 *   const MyCollection = createTypesCollection<MyCollectionRegistry>();
	 */
	private trackCollectionAliases (node: ts.Node, sourceFile: ts.SourceFile): void {
		if (!ts.isVariableDeclaration(node) || !ts.isIdentifier(node.name)) {
			return;
		}

		const { initializer } = node;
		if (!initializer) {
			return;
		}

		// Direct createTypesCollection() call
		if (this.isCreateTypesCollectionCall(initializer)) {
			const collectionId = this.nextCollectionId();
			this.collectionVariables.set(node.name.text, collectionId);

			const registryInterfaceName = this.extractRegistryInterfaceName(
				initializer as ts.CallExpression,
				sourceFile
			);
			this.collectionInfo.set(collectionId, {
				variableName          : node.name.text,
				sourceFile            : sourceFile.fileName,
				registryInterfaceName : registryInterfaceName
			});
			return;
		}

		// Alias of another collection variable
		if (ts.isIdentifier(initializer)) {
			const existing = this.collectionVariables.get(initializer.text);
			if (existing) {
				this.collectionVariables.set(node.name.text, existing);
			}
		}
	}

	/**
	 * Extract the registry interface name from createTypesCollection<Registry>()
	 * when the interface is declared in the same source file.
	 */
	private extractRegistryInterfaceName (
		call: ts.CallExpression,
		sourceFile: ts.SourceFile
	): string | undefined {
		const typeArgs = call.typeArguments;
		if (!typeArgs || typeArgs.length === 0) {
			return undefined;
		}

		const [ firstTypeArg ] = typeArgs;
		if (!ts.isTypeReferenceNode(firstTypeArg) || !ts.isIdentifier(firstTypeArg.typeName)) {
			return undefined;
		}

		const name = firstTypeArg.typeName.text;

		// Confirm the interface exists in the same source file.
		for (const statement of sourceFile.statements) {
			if (
				ts.isInterfaceDeclaration(statement) &&
				statement.name.text === name
			) {
				return name;
			}
		}

		return undefined;
	}

	/**
	 * Get the registry interface name for a collection id.
	 */
	private getRegistryInterfaceName (collectionId?: string): string | undefined {
		if (!collectionId) {
			return undefined;
		}
		return this.collectionInfo.get(collectionId)?.registryInterfaceName;
	}

	/**
	 * Check if an expression is a createTypesCollection() call.
	 * Handles:
	 *   createTypesCollection()
	 *   ctc() // aliased import
	 *   mnemonica.createTypesCollection() // module object method
	 *   m.createTypesCollection() // aliased module object
	 */
	private isCreateTypesCollectionCall (node: ts.Node): node is ts.CallExpression {
		if (!ts.isCallExpression(node)) {
			return false;
		}
		const expr = node.expression;

		// Direct call or aliased import: createTypesCollection() / ctc()
		if (ts.isIdentifier(expr)) {
			return expr.text === 'createTypesCollection' ||
				this.createTypesCollectionVariables.has(expr.text);
		}

		// Module object method: mnemonica.createTypesCollection()
		if (
			ts.isPropertyAccessExpression(expr) &&
			expr.name.text === 'createTypesCollection' &&
			ts.isIdentifier(expr.expression) &&
			this.moduleObjectVariables.has(expr.expression.text)
		) {
			return true;
		}

		return false;
	}

	/**
	 * Generate a unique collection identifier.
	 */
	private nextCollectionId (): string {
		this.collectionCounter++;
		const result = `collection_${this.collectionCounter}`;
		return result;
	}

	/**
	 * Check if a node is a define() call
	 */
	private isDefineCall (node: ts.Node): node is ts.CallExpression {
		if (!ts.isCallExpression(node)) {
			return false;
		}

		const { expression } = node;

		// Check for direct call: define('TypeName', ...)
		if (ts.isIdentifier(expression) && expression.text === 'define') {
			return true;
		}

		// Check for method call: SomeType.define('SubType', ...)
		if (ts.isPropertyAccessExpression(expression)) {
			return expression.name?.text === 'define';
		}

		return false;
	}

	/**
	 * Check if a node is a lazy() call
	 */
	private isLazyCall (node: ts.Node): node is ts.CallExpression {
		if (!ts.isCallExpression(node)) {
			return false;
		}

		const { expression } = node;

		// Check for direct call: lazy('TypeName', getter, ...)
		if (ts.isIdentifier(expression) && expression.text === 'lazy') {
			return true;
		}

		// Check for method call: SomeType.lazy('SubType', getter, ...)
		if (ts.isPropertyAccessExpression(expression)) {
			return expression.name?.text === 'lazy';
		}

		return false;
	}

	/**
		* Extract config options from an object literal
		*/
	private extractConfigFromObjectLiteral (configArg: ts.ObjectLiteralExpression):
		{ strictChain?: boolean; blockErrors?: boolean } {
		const config: { strictChain?: boolean; blockErrors?: boolean } = {};

		for (const prop of configArg.properties) {
			if (ts.isPropertyAssignment(prop) && ts.isIdentifier(prop.name)) {
				const propName = prop.name.text;
				if (propName === 'strictChain' && prop.initializer.kind === ts.SyntaxKind.TrueKeyword) {
					config.strictChain = true;
				} else if (propName === 'strictChain' && prop.initializer.kind === ts.SyntaxKind.FalseKeyword) {
					config.strictChain = false;
				} else if (propName === 'blockErrors' && prop.initializer.kind === ts.SyntaxKind.TrueKeyword) {
					config.blockErrors = true;
				} else if (propName === 'blockErrors' && prop.initializer.kind === ts.SyntaxKind.FalseKeyword) {
					config.blockErrors = false;
				}
			}
		}

		return config;
	}

	/**
		* Extract config options from define() call
		*/
	private extractConfig (call: ts.CallExpression): { strictChain?: boolean; blockErrors?: boolean } {
		// Config is the third argument: define('Name', handler, config)
		const [ , , configArg ] = call.arguments;
		if (!configArg || !ts.isObjectLiteralExpression(configArg)) {
			return {};
		}

		const configResult = this.extractConfigFromObjectLiteral(configArg);
		return configResult;
	}

	/**
		* Check if a node is a @decorate() decorator
		*/
	private isDecorateDecorator (node: ts.Node): node is ts.Decorator {
		if (!ts.isDecorator(node)) {
			return false;
		}

		const { expression } = node;

		// Check for @decorate
		if (ts.isIdentifier(expression) && expression.text === 'decorate') {
			return true;
		}

		// Check for @decorate() or @decorate(ParentType)
		if (ts.isCallExpression(expression)) {
			const fnName = expression.expression;
			if (ts.isIdentifier(fnName) && fnName.text === 'decorate') {
				return true;
			}

			// Check for @MyCollection.decorate() where MyCollection is a custom collection
			if (
				ts.isPropertyAccessExpression(fnName) &&
				fnName.name.text === 'decorate' &&
				ts.isIdentifier(fnName.expression) &&
				this.collectionVariables.has(fnName.expression.text)
			) {
				return true;
			}
		}

		return false;
	}

	/**
	 * Mark a call expression as processed and return whether it already was.
	 */
	private markProcessed (call: ts.CallExpression): boolean {
		if (this.processedCalls.has(call)) {
			return true;
		}
		this.processedCalls.add(call);
		return false;
	}

	/**
	 * Process a define() call
	 */
	private processDefineCall (call: ts.CallExpression, sourceFile: ts.SourceFile): void {
		// Check if this exact call has already been processed (prevents duplicates from chained calls)
		if (this.markProcessed(call)) {
			return;
		}

		// Get the type name and source context from arguments
		const defineContext = this.extractDefineContext(call);

		// For chained calls like define('A').define('B'), we want the position of the .define('B') part
		// not the start of the entire expression
		let positionNode: ts.Node = call;

		// If this is a chained call, get the position of the property access expression
		// which is the .define part
		if (ts.isPropertyAccessExpression(call.expression)) {
			// The expression is the property access: (define('RootAsync', ...)).define
			// We want the position of just the .define part
			// This is the 'define' identifier
			positionNode = call.expression.name;
		}

		const startPos = positionNode.getStart(sourceFile);
		const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, startPos);

		if (!defineContext.typeName) {
			this.errors.push({
				message : 'Could not extract type name from define() call',
				file    : sourceFile.fileName,
				line    : line + 1,
				column  : character + 1,
			});
			return;
		}

		const { typeName } = defineContext;

		// Determine parent type and collection based on the call source.
		const parentNode = defineContext.parentType;
		const { collectionId } = defineContext;

		// Extract config options
		const config = this.extractConfig(call);

		// Create type node first so its internal fullPath (including any collection prefix) is resolved.
		const node = TypeGraphImpl.createNode(
			typeName,
			parentNode,
			sourceFile.fileName,
			line + 1,
			character + 1,
			collectionId
		);
		node.registryInterfaceName = this.getRegistryInterfaceName(collectionId);

		// Same-namespace duplicate detection (hard-fail law): key by the
		// runtime namespace — collection roots `<collection>::<name>`, or
		// `<parentFullPath>.<name>` for subtypes
		this.recordDefineSite(
			parentNode ? `${parentNode.fullPath}.${typeName}` : `${collectionId ?? 'default'}::${typeName}`,
			`${sourceFile.fileName}:${line + 1}:${character + 1}`
		);

		// Extract properties from constructor function — the new node anchors
		// relative-first graph reference resolution while its own signature
		// is being read
		const previousAnchor = this.currentGraphAnchor;
		this.currentGraphAnchor = node;
		try {
			node.properties = this.extractProperties(call);

			// Extract constructor parameters for TypeRegistry signature
			node.constructorParams = this.extractConstructorParams(call);
		} finally {
			this.currentGraphAnchor = previousAnchor;
		}

		// Add to graph
		if (parentNode) {
			this.graph.addChild(parentNode, node);
		} else {
			this.graph.addRoot(node);
		}

		// Create definition info using the node's resolved fullPath
		const definition: DefinitionInfo = {
			name        : typeName,
			location    : `${sourceFile.fileName}:${line + 1}:${character + 1}`,
			kind        : 'define',
			parent      : parentNode ? parentNode.fullPath : null,
			strictChain : config.strictChain ?? true,
			blockErrors : config.blockErrors ?? false,
		};
		this.definitions.set(node.fullPath, definition);
		this.edsScopeByNode.set(call, node.fullPath);

		// Track variable assignment: const User = define('UserEntity', ...) -> map "User" to "UserEntity"
		// A multi-hop initializer binds the LAST hop: define() returns the
		// defined type's constructor (F18)
		this.trackVariableAssignment(call, parentNode, node.fullPath);
	}

	/**
	 * Process a lazy() call
	 */
	private processLazyCall (call: ts.CallExpression, sourceFile: ts.SourceFile): void {
		// Check if this exact call has already been processed (prevents duplicates from chained calls)
		if (this.markProcessed(call)) {
			return;
		}

		// Get the type name and source context from arguments
		const lazyContext = this.extractLazyContext(call, sourceFile);

		// For chained calls like define('A').lazy('B'), we want the position of the .lazy('B') part
		// not the start of the entire expression
		let positionNode: ts.Node = call;

		// If this is a chained call, get the position of the property access expression
		// which is the .lazy part
		if (ts.isPropertyAccessExpression(call.expression)) {
			// The expression is the property access: (define('RootAsync', ...)).lazy
			// We want the position of just the .lazy part
			// This is the 'lazy' identifier
			positionNode = call.expression.name;
		}

		const startPos = positionNode.getStart(sourceFile);
		const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, startPos);

		if (!lazyContext.typeName) {
			this.errors.push({
				message : 'Could not extract type name from lazy() call',
				file    : sourceFile.fileName,
				line    : line + 1,
				column  : character + 1,
			});
			return;
		}

		const { typeName } = lazyContext;

		// Determine parent type and collection based on the call source.
		const parentNode = lazyContext.parentType;
		const { collectionId } = lazyContext;

		// Extract config options
		const config = this.extractLazyConfig(call);

		// Create type node first so its internal fullPath (including any collection prefix) is resolved.
		const node = TypeGraphImpl.createNode(
			typeName,
			parentNode,
			sourceFile.fileName,
			line + 1,
			character + 1,
			collectionId
		);
		node.registryInterfaceName = this.getRegistryInterfaceName(collectionId);

		// Same-namespace duplicate detection (hard-fail law)
		this.recordDefineSite(
			parentNode ? `${parentNode.fullPath}.${typeName}` : `${collectionId ?? 'default'}::${typeName}`,
			`${sourceFile.fileName}:${line + 1}:${character + 1}`
		);

		// Extract properties from the constructor returned by the lazy getter
		// — the new node anchors relative-first graph reference resolution
		const previousAnchor = this.currentGraphAnchor;
		this.currentGraphAnchor = node;
		try {
			node.properties = this.extractProperties(call);

			// Extract constructor parameters for TypeRegistry signature
			node.constructorParams = this.extractConstructorParams(call);
		} finally {
			this.currentGraphAnchor = previousAnchor;
		}

		// Add to graph
		if (parentNode) {
			this.graph.addChild(parentNode, node);
		} else {
			this.graph.addRoot(node);
		}

		// Create definition info using the node's resolved fullPath
		const definition: DefinitionInfo = {
			name        : typeName,
			location    : `${sourceFile.fileName}:${line + 1}:${character + 1}`,
			kind        : 'define',
			parent      : parentNode ? parentNode.fullPath : null,
			strictChain : config.strictChain ?? true,
			blockErrors : config.blockErrors ?? false,
		};
		this.definitions.set(node.fullPath, definition);
		this.edsScopeByNode.set(call, node.fullPath);

		// Track variable assignment: const LazyType = lazy('LazyType', ...) -> map "LazyType" -> "LazyType"
		// For chained calls like const X = lazy('A').define('B'), we want to map X -> A (the root)
		this.trackVariableAssignment(call, parentNode, node.fullPath);
	}

	/**
	 * Extract lazy() call arguments into a normalized shape.
	 * Handles named/unnamed and explicit-source forms, both as free calls
	 * and as method calls.
	 */
	private extractLazyCallArgs (call: ts.CallExpression): {
		source?: ts.Expression;
		name?: string;
		getter: ts.Expression;
		config?: ts.Expression;
	} | undefined {
		const args = call.arguments;
		const isMethodCall = ts.isPropertyAccessExpression(call.expression);

		if (isMethodCall) {
			// Source is the object of the property access: Type.lazy(...)
			const source = call.expression.expression;
			if (args.length === 0) {
				return undefined;
			}
			const [ methodFirstArg ] = args;
			if (ts.isStringLiteral(methodFirstArg)) {
				// Type.lazy('Name', getter, config?)
				if (args.length < 2) {
					return undefined;
				}
				return {
					source,
					name   : methodFirstArg.text,
					getter : args[ 1 ],
					config : args[ 2 ],
				};
			}
			// Type.lazy(getter, config?)
			return {
				source,
				getter : methodFirstArg,
				config : args[ 1 ],
			};
		}

		// Free call: lazy(...)
		if (args.length === 0) {
			return undefined;
		}

		const [ firstArg ] = args;

		// Explicit-source form: lazy(source, 'Name', getter, config?)
		// or lazy(source, getter, config?)
		if (args.length >= 2 && ts.isIdentifier(firstArg)) {
			const [ , secondArg ] = args;
			if (ts.isStringLiteral(secondArg)) {
				// lazy(source, 'Name', getter, config?)
				if (args.length < 3) {
					return undefined;
				}
				return {
					source : firstArg,
					name   : secondArg.text,
					getter : args[ 2 ],
					config : args[ 3 ],
				};
			}
			// lazy(source, getter, config?)
			return {
				source : firstArg,
				getter : secondArg,
				config : args[ 2 ],
			};
		}

		// Named root form: lazy('Name', getter, config?)
		if (ts.isStringLiteral(firstArg)) {
			if (args.length < 2) {
				return undefined;
			}
			return {
				name   : firstArg.text,
				getter : args[ 1 ],
				config : args[ 2 ],
			};
		}

		// Unnamed root form: lazy(getter, config?)
		return {
			getter : firstArg,
			config : args[ 1 ],
		};
	}

	/**
	 * Unwrap the constructor returned by a lazy getter.
	 * Supports:
	 *   () => class Name {}
	 *   () => function Name() {}
	 *   () => { return class Name {}; }
	 *   function () { return function Name() {}; }
	 */
	private unwrapLazyGetter (getterExpr: ts.Expression): ts.Expression | undefined {
		if (ts.isArrowFunction(getterExpr)) {
			const { body } = getterExpr;
			if (!ts.isBlock(body)) {
				return body;
			}
			for (const stmt of body.statements) {
				if (ts.isReturnStatement(stmt) && stmt.expression) {
					return stmt.expression;
				}
			}
			return undefined;
		}

		if (ts.isFunctionExpression(getterExpr)) {
			const { body } = getterExpr;
			for (const stmt of body.statements) {
				if (ts.isReturnStatement(stmt) && stmt.expression) {
					return stmt.expression;
				}
			}
			return undefined;
		}

		// Not a recognized getter pattern
		return undefined;
	}

	/**
	 * Extract a constructor name from a class expression, class declaration,
	 * or named function expression.
	 */
	private extractConstructorName (constructorExpr: ts.Expression): string | undefined {
		if (ts.isClassExpression(constructorExpr) && constructorExpr.name) {
			return constructorExpr.name.text;
		}
		if (ts.isClassDeclaration(constructorExpr) && constructorExpr.name) {
			return constructorExpr.name.text;
		}
		if (ts.isFunctionExpression(constructorExpr) && constructorExpr.name) {
			return constructorExpr.name.text;
		}
		return undefined;
	}

	/**
	 * Extract the type name from either a define() or lazy() call.
	 */
	private extractMnemonicaTypeName (call: ts.CallExpression): string | undefined {
		if (this.isDefineCall(call)) {
			return this.extractTypeName(call);
		}
		if (this.isLazyCall(call)) {
			const args = this.extractLazyCallArgs(call);
			if (!args) {
				return undefined;
			}
			if (args.name) {
				return args.name;
			}
			const constructorExpr = this.unwrapLazyGetter(args.getter);
			if (constructorExpr) {
				return this.extractConstructorName(constructorExpr);
			}
		}
		return undefined;
	}

	/**
	 * Extract the full lazy() call context: type name, parent type, and collection.
	 * Handles direct calls, property-access calls, chained calls, and the
	 * explicit-source form `lazy(source, 'TypeName', getter)`.
	 */
	private extractLazyContext (call: ts.CallExpression, sourceFile: ts.SourceFile): {
		typeName?: string;
		parentType?: TypeNode;
		collectionId?: string;
	} {
		const args = this.extractLazyCallArgs(call);
		if (!args) {
			return {};
		}

		let typeName: string | undefined = args.name;
		if (!typeName) {
			const constructorExpr = this.unwrapLazyGetter(args.getter);
			if (constructorExpr) {
				typeName = this.extractConstructorName(constructorExpr);
			}
		}
		if (!typeName) {
			return {};
		}

		const { expression } = call;

		// Direct call: lazy('TypeName', ...) or lazy(source, 'TypeName', getter)
		if (ts.isIdentifier(expression) && expression.text === 'lazy') {
			if (args.source && ts.isIdentifier(args.source)) {
				const sourceContext = this.resolveDefineSource(args.source.text);
				return {
					typeName,
					parentType   : sourceContext.parentType,
					collectionId : sourceContext.collectionId,
				};
			}
			// Plain root lazy in default collection
			return { typeName };
		}

		// Property access: X.lazy('TypeName', ...)
		if (ts.isPropertyAccessExpression(expression) && expression.name.text === 'lazy') {
			const obj = expression.expression;

			if (ts.isIdentifier(obj)) {
				const sourceContext = this.resolveDefineSource(obj.text);
				return {
					typeName,
					parentType   : sourceContext.parentType,
					collectionId : sourceContext.collectionId,
				};
			}

			if (ts.isPropertyAccessExpression(obj)) {
				// Nested access: instance.Type.lazy - try to resolve
				const chain = this.getPropertyChain(obj);
				if (chain.length > 0) {
					const parentNode = this.graph.findType(chain.join('.'));
					return { typeName, parentType : parentNode };
				}
			}

			if (ts.isCallExpression(obj)) {
				// Determine the collection context from the root of the chain so that
				// custom-collection types do not get confused with default-collection types.
				const rootId = this.getRootIdentifier(obj.expression);
				const expectedCollectionId = rootId
					? this.resolveDefineSource(rootId.text).collectionId
					: undefined;

				// Chained call: define('A').lazy('B') or lazy('A').lazy('B')
				if (this.isDefineCall(obj)) {
					this.processDefineCall(obj, sourceFile);
					const parentTypeName = this.extractMnemonicaTypeName(obj);
					if (parentTypeName) {
						const parentNode = this.findParentTypeByName(parentTypeName, expectedCollectionId);
						return { typeName, parentType : parentNode, collectionId : parentNode?.collectionId };
					}
				}

				if (this.isLazyCall(obj)) {
					this.processLazyCall(obj, sourceFile);
					const parentTypeName = this.extractMnemonicaTypeName(obj);
					if (parentTypeName) {
						const parentNode = this.findParentTypeByName(parentTypeName, expectedCollectionId);
						return { typeName, parentType : parentNode, collectionId : parentNode?.collectionId };
					}
				}

				// Builder lookup chain: App.lookup('User').lazy('Admin')
				if (this.isLookupCall(obj)) {
					const lookedUpPath = this.resolveLookupPath(obj);
					if (lookedUpPath) {
						const parentNode = this.graph.findType(lookedUpPath);
						if (parentNode) {
							return { typeName, parentType : parentNode, collectionId : parentNode.collectionId };
						}
					}
				}
			}
		}

		return { typeName };
	}

	/**
	 * Extract config options from lazy() call
	 */
	private extractLazyConfig (call: ts.CallExpression): { strictChain?: boolean; blockErrors?: boolean } {
		const args = this.extractLazyCallArgs(call);
		if (!args || !args.config || !ts.isObjectLiteralExpression(args.config)) {
			return {};
		}

		const configResult = this.extractConfigFromObjectLiteral(args.config);
		return configResult;
	}

	/**
		* Track variable assignments that capture define() results
		* e.g., const User = define('UserEntity', ...) maps "User" -> "UserEntity"
		* For chained calls like const X = define('A').define('B'), we map X -> A (the root type)
		*/
	private trackVariableAssignment (
		call: ts.CallExpression,
		parentNode: TypeNode | undefined,
		fullPath: string
	): void {
		// Check if this call is the right-hand side of a variable declaration
		// Walk up the tree to find VariableDeclaration
		let current: ts.Node | undefined = call.parent;
		while (current) {
			if (ts.isVariableDeclaration(current)) {
				// Found: const X = define(...)
				if (ts.isIdentifier(current.name)) {
					const varName = current.name.text;
					// F18: define() returns the DEFINED type's constructor,
					// so a const holding a multi-hop initializer
					// (`const X = A.define('B').define('C')`) binds the LAST
					// hop — a deeper hop must not bind, and the outermost
					// hop binds unconditionally (visit-order independent)
					if (this.isDeeperDefineHop(call)) {
						return;
					}
					// For chained lazy calls like const X = define('A').lazy('B'),
					// the first call in the chain sets the mapping (lazy hop
					// keeps it — pinned behavior)
					if (parentNode && this.variableToTypeMap.has(varName)) {
						return;
					}
					this.variableToTypeMap.set(varName, fullPath);
					this.trackFileGraphBinding(varName, fullPath);
				}
				return;
			}
			current = current.parent;
		}
	}

	/**
	 * A `.define(...)` hop wrapped by another `.define(...)` call is not
	 * the value its const ends up holding — the OUTERMOST hop of the
	 * initializer chain is (define() returns the defined type's
	 * constructor). Only the outermost hop may bind the variable.
	 */
	private isDeeperDefineHop (call: ts.CallExpression): boolean {
		const { parent } = call;
		const deeper = !!parent &&
			ts.isPropertyAccessExpression(parent) &&
			parent.name.text === 'define' &&
			ts.isCallExpression(parent.parent) &&
			parent.parent.expression === parent;
		return deeper;
	}

	/**
	 * Mirror a variable -> mnemonica fullPath binding into the per-file
	 * value-scope map (graph identity law: `typeof X` and bare references
	 * resolve through the file's own bindings first).
	 */
	private trackFileGraphBinding (varName: string, fullPath: string): void {
		const filePath = this.currentReferencedTypeFile;
		let bindings = this.fileGraphBindings.get(filePath);
		if (!bindings) {
			bindings = new Map<string, string>();
			this.fileGraphBindings.set(filePath, bindings);
		}
		bindings.set(varName, fullPath);
	}
	
	/**
		* Track variable assignments from lookup() calls
		* e.g., const SentienceConstructor = lookup('Sentience') maps "SentienceConstructor" -> "Sentience"
		*/
	private trackLookupAssignment (call: ts.CallExpression, typePath: string): void {
		this.bindResultVariable(call, typePath);
	}

	/**
		* Track variable assignments from new Type() calls
		* e.g., const user = new UserType() maps "user" -> "UserType"
		*/
	private trackNewAssignment (newExpr: ts.NewExpression, typePath: string): void {
		let effectivePath = typePath;
		let current: ts.Node | undefined = newExpr.parent;
		// Chain-form construction: new R().A().B() — the result variable
		// holds the OUTERMOST tip's instance (await-transparent), not the
		// inner new's type. Walk the chain, keeping the last resolvable tip.
		while (current) {
			if (ts.isPropertyAccessExpression(current) &&
				ts.isCallExpression(current.parent) &&
				current.parent.expression === current) {
				const tip = this.resolveChainTipTypePath(current.parent);
				if (tip) {
					effectivePath = tip;
				}
				current = current.parent.parent;
				continue;
			}
			break;
		}
		this.bindResultVariable(newExpr, effectivePath);
	}

	/**
	 * Bind the nearest enclosing `const/let/var X = …` to a mnemonica
	 * fullPath — the shared result-variable walker behind new/lookup/
	 * chain/fork/merge/call tracking (value scope: downstream references
	 * and `this.x = x` assignments resolve through the same binding).
	 */
	private bindResultVariable (from: ts.Node, typePath: string): void {
		let current: ts.Node | undefined = from.parent;
		while (current) {
			if (ts.isVariableDeclaration(current)) {
				// Found: const X = <construction>
				if (ts.isIdentifier(current.name)) {
					const varName = current.name.text;
					this.variableToTypeMap.set(varName, typePath);
					this.trackFileGraphBinding(varName, typePath);
				}
				return;
			}
			current = current.parent;
		}
	}

	/**
	 * Record an `instantiation` usage for a construction-shape call
	 * (chain tip / call / apply / fork / clone / merge —
	 * byte-indistinguishable from `new` until the deferred
	 * mechanism-kind revision). `constructorText` defaults to the callee
	 * expression text so the site stays readable without new fields;
	 * call/apply override it with the Ctor argument text.
	 */
	private recordConstructionUsage (
		call: ts.CallExpression,
		typePath: string,
		sourceFile: ts.SourceFile,
		constructorText?: string
	): void {
		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			call.getStart(sourceFile)
		);
		const ctorText = constructorText ?? call.expression.getText(sourceFile);
		this.addUsage(typePath, {
			location        : `${sourceFile.fileName}:${line + 1}:${character + 1}`,
			kind            : 'instantiation',
			code            : call.getText(sourceFile).slice(0, 100),
			constructorText : ctorText.slice(0, 100),
		});
	}

	/**
	 * Resolve the type a construction-chain tip call constructs:
	 * `new R(...).A(...)` constructs R.A; `await new R(...).A(...).B(...)`
	 * constructs R.A.B. The receiver is the nested chain (NewExpression
	 * base, then tip calls); exact fullPath first, and only when the root
	 * itself is unknown does the prop-name fallback law apply (so plain
	 * method calls on fresh instances never record a construction).
	 */
	private resolveChainTipTypePath (call: ts.CallExpression): string | undefined {
		if (!ts.isPropertyAccessExpression(call.expression)) {
			return undefined;
		}
		const receiver = call.expression;
		let rootPath: string | undefined;
		if (ts.isNewExpression(receiver.expression)) {
			const inner = receiver.expression;
			rootPath = ts.isPropertyAccessExpression(inner.expression)
				? this.resolveTypePath(inner.expression)
				: this.getTypeNameFromExpression(inner.expression);
		} else if (ts.isCallExpression(receiver.expression)) {
			rootPath = this.resolveChainTipTypePath(receiver.expression);
		} else {
			return undefined;
		}
		if (!rootPath) {
			return undefined;
		}
		const candidate = `${rootPath}.${receiver.name.text}`;
		if (this.definitions.has(candidate)) {
			return candidate;
		}
		if (!this.definitions.has(rootPath)) {
			return this.resolveTypePath(receiver);
		}
		return undefined;
	}

	/**
	 * True when `expr` denotes a construction function imported from
	 * 'mnemonica' — the named-import form (`import { call } from
	 * 'mnemonica'`, aliases included) or a member of a tracked
	 * module-object alias (`mnemonica.call`). Userland call/apply/bind
	 * functions never match.
	 */
	private isMnemonicaConstructionFn (expr: ts.Expression, fn: 'call' | 'apply' | 'bind'): boolean {
		if (ts.isIdentifier(expr)) {
			const imported = this.mnemonicaNamedImports.get(this.currentReferencedTypeFile)?.get(expr.text);
			const matched = imported === fn;
			return matched;
		}
		if (ts.isPropertyAccessExpression(expr) && expr.name.text === fn) {
			const matched = ts.isIdentifier(expr.expression) &&
				this.moduleObjectVariables.has(expr.expression.text);
			return matched;
		}
		return false;
	}

	/**
	 * mnemonica call/apply(entity, Ctor, ...) / bind(entity, Ctor):
	 * resolve the Ctor argument (arg 1) to a graph fullPath through the
	 * same tiers as the `new` branch (value scope for identifiers,
	 * chain resolution for property accesses).
	 */
	private resolveConstructionFnTypePath (call: ts.CallExpression): string | undefined {
		const callee = call.expression;
		const isCallOrApply = this.isMnemonicaConstructionFn(callee, 'call') ||
			this.isMnemonicaConstructionFn(callee, 'apply');
		const isBind = this.isMnemonicaConstructionFn(callee, 'bind');
		if (!isCallOrApply && !isBind) {
			return undefined;
		}
		if (call.arguments.length < 2) {
			return undefined;
		}
		const [ , ctorArg ] = call.arguments;
		let resolved: string | undefined;
		if (ts.isPropertyAccessExpression(ctorArg)) {
			resolved = this.resolveTypePath(ctorArg);
		} else if (ts.isIdentifier(ctorArg)) {
			const bound = this.variableToTypeMap.get(ctorArg.text);
			if (bound) {
				resolved = bound;
			} else {
				const graphResult = this.resolveGraphTypeName(ctorArg.text);
				if (graphResult.status === 'unique') {
					resolved = graphResult.node.fullPath;
				}
			}
		}
		const known = resolved && this.definitions.has(resolved) ? resolved : undefined;
		return known;
	}

	/**
	 * instance.fork(...) / instance.clone(...) on a tracked variable —
	 * runtime returns `this`, so the result carries the source type.
	 */
	private resolveForkLikeTypePath (call: ts.CallExpression): string | undefined {
		if (!ts.isPropertyAccessExpression(call.expression)) {
			return undefined;
		}
		const method = call.expression.name.text;
		if (method !== 'fork' && method !== 'clone') {
			return undefined;
		}
		const receiver = call.expression.expression;
		if (!ts.isIdentifier(receiver)) {
			return undefined;
		}
		const result = this.variableToTypeMap.get(receiver.text);
		return result;
	}

	/**
	 * Free utils forms: utils.merge(a, b, ...) (also the direct named
	 * import `merge(a, b)`) and the curried utils.fork(instance)(...).
	 * The result binds to arg 0's type — runtime returns a's lineage over
	 * b's context; a's fullPath is the honest approximation within the
	 * output contract (documented in README).
	 */
	private resolveUtilsFnTypePath (call: ts.CallExpression): string | undefined {
		const callee = call.expression;
		const isUtilsOwner = (owner: ts.Expression): boolean => {
			if (ts.isIdentifier(owner)) {
				const imported = this.mnemonicaNamedImports.get(this.currentReferencedTypeFile)?.get(owner.text);
				return imported === 'utils';
			}
			const matched = ts.isPropertyAccessExpression(owner) && owner.name.text === 'utils' &&
				ts.isIdentifier(owner.expression) && this.moduleObjectVariables.has(owner.expression.text);
			return matched;
		};
		let subjectArg: ts.Expression | undefined;
		if (ts.isPropertyAccessExpression(callee) && isUtilsOwner(callee.expression) &&
			(callee.name.text === 'merge' || callee.name.text === 'fork')) {
			const [ firstArg ] = call.arguments;
			subjectArg = firstArg;
		} else if (ts.isIdentifier(callee)) {
			const imported = this.mnemonicaNamedImports.get(this.currentReferencedTypeFile)?.get(callee.text);
			if (imported === 'merge' || imported === 'fork') {
				const [ firstArg ] = call.arguments;
				subjectArg = firstArg;
			}
		} else if (ts.isCallExpression(callee) && ts.isPropertyAccessExpression(callee.expression) &&
			callee.expression.name.text === 'fork' && isUtilsOwner(callee.expression.expression)) {
			// utils.fork(instance)(...args) — the curried form
			const [ firstArg ] = callee.arguments;
			subjectArg = firstArg;
		}
		if (!subjectArg || !ts.isIdentifier(subjectArg)) {
			return undefined;
		}
		const result = this.variableToTypeMap.get(subjectArg.text);
		return result;
	}


	/**
		* Process a @decorate() decorator
	 */
	private processDecorateDecorator (
		decorator: ts.Decorator,
		sourceFile: ts.SourceFile,
		classDeclParam?: ts.ClassDeclaration
	): void {
		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			decorator.getStart(sourceFile)
		);

		// Get the class declaration - use the passed context if parent is not set
		const classDecl = decorator.parent as ts.ClassDeclaration | undefined || classDeclParam;
		if (!classDecl || !classDecl.name) {
			this.errors.push({
				message : 'Decorated class has no name',
				file    : sourceFile.fileName,
				line    : line + 1,
				column  : character + 1,
			});
			return;
		}

		const typeName = classDecl.name.text;
		if (!typeName) {
			this.errors.push({
				message : 'Decorated class has no name',
				file    : sourceFile.fileName,
				line    : line + 1,
				column  : character + 1,
			});
			return;
		}

		// Parse decorator arguments: @decorate(), @decorate(Parent),
		// @decorate({ ... }), @decorate(Parent, { ... }),
		// @MyCollection.decorate(), @MyCollection.decorate({ ... })
		let parentNode: TypeNode | undefined;
		let parentFullPath: string | null = null;
		let collectionId: string | undefined;
		let decoratorConfig: { strictChain?: boolean; blockErrors?: boolean } = {};

		if (ts.isCallExpression(decorator.expression)) {
			const callExpr = decorator.expression;
			const callee = callExpr.expression;

			// Check for @MyCollection.decorate() where MyCollection is a custom collection.
			// The decorated class becomes a root type in that collection.
			if (
				ts.isPropertyAccessExpression(callee) &&
				callee.name.text === 'decorate' &&
				ts.isIdentifier(callee.expression) &&
				this.collectionVariables.has(callee.expression.text)
			) {
				collectionId = this.collectionVariables.get(callee.expression.text);
				if (callExpr.arguments.length === 1 && ts.isObjectLiteralExpression(callExpr.arguments[ 0 ])) {
					decoratorConfig = this.extractConfigFromObjectLiteral(callExpr.arguments[ 0 ]);
				}
			} else {
				const args = callExpr.arguments;
				let parentArg: ts.Identifier | undefined;
				let configArg: ts.ObjectLiteralExpression | undefined;

				for (const arg of args) {
					if (ts.isIdentifier(arg)) {
						if (parentArg) {
							this.errors.push({
								message : '@decorate() accepts only one parent reference',
								file    : sourceFile.fileName,
								line    : line + 1,
								column  : character + 1,
							});
						} else {
							parentArg = arg;
						}
					} else if (ts.isObjectLiteralExpression(arg)) {
						if (configArg) {
							this.errors.push({
								message : '@decorate() accepts only one config object',
								file    : sourceFile.fileName,
								line    : line + 1,
								column  : character + 1,
							});
						} else {
							configArg = arg;
						}
					}
				}

				if (parentArg) {
					parentNode = this.findParentTypeByIdentifier(parentArg.text);
					if (parentNode) {
						parentFullPath = parentNode.fullPath;
					}
				}

				if (configArg) {
					decoratorConfig = this.extractConfigFromObjectLiteral(configArg);
				}
			}
		}

		// Build full path
		const fullPath = parentNode ? `${parentNode.fullPath}.${typeName}` : typeName;

		// Create definition info for decorate
		const definition: DefinitionInfo = {
			name        : typeName,
			location    : `${sourceFile.fileName}:${line + 1}:${character + 1}`,
			kind        : 'decorate',
			parent      : parentFullPath,
			strictChain : decoratorConfig.strictChain ?? true,
			blockErrors : decoratorConfig.blockErrors ?? false,
		};
		this.definitions.set(fullPath, definition);
		this.edsScopeByNode.set(classDecl, fullPath);

		// Create type node
		const node = TypeGraphImpl.createNode(
			typeName,
			parentNode,
			sourceFile.fileName,
			line + 1,
			character + 1,
			collectionId
		);
		node.registryInterfaceName = this.getRegistryInterfaceName(node.collectionId);

		// Same-namespace duplicate detection (hard-fail law)
		this.recordDefineSite(
			parentNode ? `${parentNode.fullPath}.${typeName}` : `${collectionId ?? 'default'}::${typeName}`,
			`${sourceFile.fileName}:${line + 1}:${character + 1}`
		);

		// Extract properties and constructor parameters from class members —
		// the new node anchors relative-first graph reference resolution
		const previousAnchor = this.currentGraphAnchor;
		this.currentGraphAnchor = node;
		try {
			node.properties = this.extractClassProperties(classDecl);
			node.constructorParams = this.extractClassConstructorParams(classDecl);
		} finally {
			this.currentGraphAnchor = previousAnchor;
		}

		// Add to graph
		if (parentNode) {
			this.graph.addChild(parentNode, node);
		} else {
			this.graph.addRoot(node);
		}
	}

	/**
	 * Extract type name from define() call arguments.
	 * Handles:
	 *   define('TypeName', handler)
	 *   define(source, 'TypeName', handler)   // explicit-source form
	 *   define(function TypeName() {})
	 *   define(() => class TypeName {})
	 */
	private extractTypeName (call: ts.CallExpression): string | undefined {
		const args = call.arguments;

		if (args.length === 0) {
			return undefined;
		}

		const [ firstArg ] = args;

		// Explicit-source form: define(source, 'TypeName', handler)
		if (args.length >= 2 && ts.isIdentifier(firstArg) && ts.isStringLiteral(args[ 1 ])) {
			return args[ 1 ].text;
		}

		// String literal: define('TypeName', ...)
		if (ts.isStringLiteral(firstArg)) {
			return firstArg.text;
		}

		// Function with name: define(function TypeName() {})
		if (ts.isFunctionExpression(firstArg) && firstArg.name) {
			return firstArg.name.text;
		}

		// Arrow function returning class: define(() => class TypeName {})
		if (ts.isArrowFunction(firstArg)) {
			const { body } = firstArg;
			if (ts.isClassExpression(body) && body.name) {
				return body.name.text;
			}
		}

		return undefined;
	}

	/**
	 * Extract the full define() call context: type name, parent type, and collection.
	 * Handles direct calls, property-access calls, chained calls, and the
	 * explicit-source form `define(source, 'TypeName', handler)`.
	 */
	private extractDefineContext (call: ts.CallExpression): {
		typeName?: string;
		parentType?: TypeNode;
		collectionId?: string;
	} {
		const typeName = this.extractTypeName(call);
		if (!typeName) {
			return {};
		}

		const { expression } = call;

		// Direct call: define('TypeName', ...) or define(source, 'TypeName', handler)
		if (ts.isIdentifier(expression) && expression.text === 'define') {
			// Explicit-source form: define(source, 'TypeName', handler)
			if (call.arguments.length >= 2 && ts.isIdentifier(call.arguments[ 0 ])) {
				const sourceName = call.arguments[ 0 ].text;
				const sourceContext = this.resolveDefineSource(sourceName);
				return {
					typeName,
					parentType   : sourceContext.parentType,
					collectionId : sourceContext.collectionId,
				};
			}

			// Plain root define in default collection
			return { typeName };
		}

		// Property access: X.define('TypeName', ...)
		if (ts.isPropertyAccessExpression(expression) && expression.name.text === 'define') {
			const obj = expression.expression;

			if (ts.isIdentifier(obj)) {
				const sourceContext = this.resolveDefineSource(obj.text);
				return {
					typeName,
					parentType   : sourceContext.parentType,
					collectionId : sourceContext.collectionId,
				};
			}

			if (ts.isPropertyAccessExpression(obj)) {
				// Nested access: instance.Type.define - try to resolve
				const chain = this.getPropertyChain(obj);
				if (chain.length > 0) {
					const parentNode = this.graph.findType(chain.join('.'));
					return { typeName, parentType : parentNode };
				}
			}

			if (ts.isCallExpression(obj)) {
				// Determine the collection context from the root of the chain so that
				// custom-collection types do not get confused with default-collection types.
				const rootId = this.getRootIdentifier(obj.expression);
				const expectedCollectionId = rootId
					? this.resolveDefineSource(rootId.text).collectionId
					: undefined;

				// Chained call: define('A').define('B') or mnemonica.define('A').define('B')
				if (this.isDefineCall(obj)) {
					this.processDefineCall(obj, call.getSourceFile());
					const parentTypeName = this.extractTypeName(obj);
					if (parentTypeName) {
						const parentNode = this.findParentTypeByName(parentTypeName, expectedCollectionId);
						// Inherit collection from the parent type (if any)
						return { typeName, parentType : parentNode, collectionId : parentNode?.collectionId };
					}
				}

				// Chained lazy call: lazy('A').define('B') or Type.lazy('A').define('B')
				if (this.isLazyCall(obj)) {
					this.processLazyCall(obj, call.getSourceFile());
					const parentTypeName = this.extractMnemonicaTypeName(obj);
					if (parentTypeName) {
						const parentNode = this.findParentTypeByName(parentTypeName, expectedCollectionId);
						return { typeName, parentType : parentNode, collectionId : parentNode?.collectionId };
					}
				}

				// Builder lookup chain: App.lookup('User').define('Admin')
				if (this.isLookupCall(obj)) {
					const lookedUpPath = this.resolveLookupPath(obj);
					if (lookedUpPath) {
						const parentNode = this.graph.findType(lookedUpPath);
						if (parentNode) {
							return { typeName, parentType : parentNode, collectionId : parentNode.collectionId };
						}
					}
				}
			}
		}

		return { typeName };
	}

	/**
	 * Prefix a dotted type path with a collection identifier so custom-collection
	 * types do not collide with default-collection types in the graph.
	 */
	private prefixCollectionPath (path: string, collectionId: string): string {
		return `${collectionId}::${path}`;
	}

	/**
	 * Resolve a define() source identifier to either a parent type, a collection,
	 * or the default (module object) collection.
	 */
	private resolveDefineSource (sourceName: string): {
		parentType?: TypeNode;
		collectionId?: string;
	} {
		// Module object aliases -> root in default collection
		if (this.moduleObjectVariables.has(sourceName)) {
			return {};
		}

		// Collection variables -> root in that collection
		const collectionId = this.collectionVariables.get(sourceName);
		if (collectionId) {
			return { collectionId };
		}

		// Otherwise treat as a type variable reference
		const parentNode = this.findParentTypeByIdentifier(sourceName);
		return { parentType : parentNode, collectionId : parentNode?.collectionId };
	}

	/**
	 * Check if a call expression is a lookup() call.
	 */
	private isLookupCall (node: ts.CallExpression): boolean {
		const expr = node.expression;
		if (ts.isIdentifier(expr) && expr.text === 'lookup') {
			return true;
		}
		if (ts.isPropertyAccessExpression(expr) && expr.name.text === 'lookup') {
			return true;
		}
		return false;
	}

	/**
	 * Resolve a lookup() call to a dotted type path (best effort).
	 * Handles:
	 *   lookup('User')
	 *   lookup(source, 'User')
	 *   App.lookup('User')
	 *   collection.lookup('User.Admin')
	 */
	private resolveLookupPath (call: ts.CallExpression): string | undefined {
		const args = call.arguments;
		if (args.length === 0) {
			return undefined;
		}

		// Single-arg lookup: lookup('User') or App.lookup('User')
		if (args.length === 1) {
			const [ arg ] = args;
			if (ts.isStringLiteral(arg) || ts.isNoSubstitutionTemplateLiteral(arg)) {
				const path = arg.text;
				// If this is a method call on a source, resolve relative to that source.
				if (ts.isPropertyAccessExpression(call.expression)) {
					const sourceExpr = call.expression.expression;
					if (ts.isIdentifier(sourceExpr)) {
						const sourceName = sourceExpr.text;
						const sourceContext = this.resolveDefineSource(sourceName);
						if (sourceContext.collectionId) {
							// Collection lookup: prefix path with the collection id
							return this.prefixCollectionPath(path, sourceContext.collectionId);
						}
						if (sourceContext.parentType) {
							// Type lookup: relative first, then root fallback
							const relativePath = `${sourceContext.parentType.fullPath}.${path}`;
							if (this.graph.findType(relativePath)) {
								return relativePath;
							}
							return path;
						}
					}
				}
				return path;
			}
			return undefined;
		}

		// Two-arg lookup: lookup(source, 'User')
		if (args.length >= 2) {
			const [ sourceArg, pathArg ] = args;
			if (!ts.isIdentifier(sourceArg) || !ts.isStringLiteral(pathArg)) {
				return undefined;
			}
			const sourceName = sourceArg.text;
			const path = pathArg.text;
			const sourceContext = this.resolveDefineSource(sourceName);
			if (sourceContext.collectionId) {
				return this.prefixCollectionPath(path, sourceContext.collectionId);
			}
			if (sourceContext.parentType) {
				const relativePath = `${sourceContext.parentType.fullPath}.${path}`;
				if (this.graph.findType(relativePath)) {
					return relativePath;
				}
				return path;
			}
			return path;
		}

		return undefined;
	}

	/**
	 * Lookup-law delegate for the local-scope walker (scopes.json typePath
	 * metadata): resolve a lookup() initializer call through exactly the
	 * tiers the usages pass resolved it against (same source resolution,
	 * same complete graph). The walker runs its own scope-chain value-scope
	 * tier before delegating; everything above value scope lands here, so
	 * scopes.json never disagrees with the hard-fail-law verdicts.
	 */
	resolveLookupCallPath (call: ts.CallExpression): string | undefined {
		const result = this.resolveLookupPath(call);
		return result;
	}

	/**
		* Find a parent type by its name, searching in the graph.
		* When collectionId is provided, only types from that collection are considered.
		*/
	private findParentTypeByName (
		name: string,
		collectionId?: string
	): TypeNode | undefined {
		const matchesCollection = (type: TypeNode): boolean => {
			if (collectionId === undefined) {
				return type.collectionId === undefined;
			}
			return type.collectionId === collectionId;
		};

		// First try exact match (default-collection types use the plain dotted path)
		const exact = this.graph.findType(name);
		if (exact && matchesCollection(exact)) {
			return exact;
		}

		// Then search through all types for one with matching name and collection
		for (const type of this.graph.getAllTypes()) {
			if (type.name === name && matchesCollection(type)) {
				return type;
			}
		}

		return undefined;
	}

	/**
		* Find a parent type from an identifier reference.
		* Handles both aliased variables (const User = define('UserEntity', ...))
		* and direct class/type names.
		*/
	private findParentTypeByIdentifier (name: string): TypeNode | undefined {
		// First check variable mapping: const User = define('UserEntity', ...)
		const mappedFullPath = this.variableToTypeMap.get(name);
		if (mappedFullPath) {
			const mappedNode = this.graph.findType(mappedFullPath);
			if (mappedNode) return mappedNode;
		}

		const parentNode = this.findParentTypeByName(name);
		return parentNode;
	}

	/**
	 * Get the leftmost identifier of a property-access chain.
	 * For `App.define('User').define('Admin')` this returns the `App` identifier.
	 */
	private getRootIdentifier (expr: ts.Expression): ts.Identifier | undefined {
		let current: ts.Expression = expr;
		while (ts.isPropertyAccessExpression(current)) {
			current = current.expression;
		}
		if (ts.isIdentifier(current)) {
			return current;
		}
		return undefined;
	}

	/**
		* Get property chain from nested access
		*/
	private getPropertyChain (expr: ts.PropertyAccessExpression | ts.Identifier): string[] {
		const chain: string[] = [];

		let current: ts.Expression = expr;
		while (ts.isPropertyAccessExpression(current)) {
			if (current.name) {
				chain.unshift(current.name.text);
			}
			current = current.expression;
		}

		if (ts.isIdentifier(current)) {
			chain.unshift(current.text);
		}

		return chain;
	}

	/**
	 * Determine the constructor expression for either a define() or lazy() call.
	 * For define() this is the construct handler; for lazy() it is the value
	 * returned by the lazy getter.
	 */
	private extractConstructorExpression (call: ts.CallExpression): ts.Expression | undefined {
		const expr = call.expression;
		const name = ts.isIdentifier(expr)
			? expr.text
			: ts.isPropertyAccessExpression(expr)
				? expr.name.text
				: '';

		if (name === 'lazy') {
			const lazyArgs = this.extractLazyCallArgs(call);
			if (!lazyArgs) {
				return undefined;
			}
			return this.unwrapLazyGetter(lazyArgs.getter);
		}

		// define() call
		const args = call.arguments;
		if (args.length === 0) {
			return undefined;
		}

		// Modern form: define('Name', handler, config?)
		if (ts.isStringLiteral(args[ 0 ])) {
			return args[ 1 ];
		}

		// Legacy form: define(function Name() {}) or define(() => class Name {})
		return args[ 0 ];
	}

	/**
	 * Extract properties from constructor function
	 */
	private extractProperties (call: ts.CallExpression): Map<string, PropertyInfo> {
		const constructorExpr = this.extractConstructorExpression(call);
		if (!constructorExpr) {
			return new Map<string, PropertyInfo>();
		}
		const result = this.extractPropertiesFromConstructor(constructorExpr);
		return result;
	}

	/**
	 * Extract properties from a constructor expression (function, arrow, or class).
	 */
	private extractPropertiesFromConstructor (constructorExpr: ts.Expression): Map<string, PropertyInfo> {
		const properties = new Map<string, PropertyInfo>();

		// Build type map from data parameter (for this.x = data.x patterns)
		const dataTypeMap = this.buildDataTypeMap(constructorExpr);

		// Handle function expression
		if (ts.isFunctionExpression(constructorExpr) || ts.isArrowFunction(constructorExpr)) {
			const { body } = constructorExpr;

			// First, extract properties from `this` parameter type annotation
			// This handles patterns like: function(this: SomeType, data: SomeType) { }
			const thisParamProperties = this.extractThisParamProperties(constructorExpr);
			for (const [ name, propInfo ] of thisParamProperties) {
				properties.set(name, propInfo);
			}

			// Function body with statements
			if (ts.isBlock(body)) {
				for (const stmt of body.statements) {
					if (ts.isExpressionStatement(stmt)) {
						this.extractPropertyFromStatement(stmt.expression, properties, dataTypeMap);
					}
				}
			}
		}

		// Handle class expression
		if (ts.isClassExpression(constructorExpr)) {
			// First pass: collect all property types for method inference
			const classPropertyTypes = this.extractClassPropertyTypes(constructorExpr);

			for (const member of constructorExpr.members) {
				// Handle property declarations
				if (ts.isPropertyDeclaration(member) && member.name) {
					// Skip private and protected properties
					if (member.modifiers) {
						const hasPrivateOrProtected = member.modifiers.some(m => {
							return m.kind === ts.SyntaxKind.PrivateKeyword ||
								m.kind === ts.SyntaxKind.ProtectedKeyword;
						});
						if (hasPrivateOrProtected) {
							continue;
						}
					}

					const name = ts.isIdentifier(member.name) ? member.name.text : '';
					if (name) {
						properties.set(name, {
							name,
							type     : this.inferType(member.type),
							optional : !!member.questionToken,
						});
					}
				}

				// Handle method declarations
				if (ts.isMethodDeclaration(member) && member.name && ts.isIdentifier(member.name)) {
					// Skip private and protected methods
					if (member.modifiers) {
						const hasPrivateOrProtected = member.modifiers.some(m => {
							return m.kind === ts.SyntaxKind.PrivateKeyword ||
								m.kind === ts.SyntaxKind.ProtectedKeyword;
						});
						if (hasPrivateOrProtected) {
							continue;
						}
					}

					const name = member.name.text;
					const type = this.inferMethodType(member, classPropertyTypes);
					properties.set(name, {
						name,
						type,
						optional : false,
					});
				}

				// Handle getter declarations
				if (ts.isGetAccessor(member) && member.name && ts.isIdentifier(member.name)) {
					// Skip private and protected getters
					if (member.modifiers) {
						const hasPrivateOrProtected = member.modifiers.some(m => {
							return m.kind === ts.SyntaxKind.PrivateKeyword ||
								m.kind === ts.SyntaxKind.ProtectedKeyword;
						});
						if (hasPrivateOrProtected) {
							continue;
						}
					}

					const name = member.name.text;
					// First try explicit type annotation, then infer from getter body
					let type = this.inferType(member.type);
					if (type === 'unknown' && member.body) {
						type = this.inferReturnTypeFromBody(member.body, classPropertyTypes);
					}
					properties.set(name, {
						name,
						type,
						optional : false,
						readonly : true,
					});
				}
			}
		}

		return properties;
	}

	/**
	 * Build a type map from all parameters with inline object type annotations
	 * Returns a map of "paramName.propertyName" -> type
	 */
	private buildDataTypeMap (handlerArg: ts.Expression): Map<string, string> {
		const typeMap = new Map<string, string>();

		if (!ts.isFunctionExpression(handlerArg) && !ts.isArrowFunction(handlerArg)) {
			return typeMap;
		}

		// Iterate over ALL parameters
		for (const param of handlerArg.parameters) {
			if (!param.name || !param.type) continue;

			// Get parameter name
			let paramName = '';
			if (ts.isIdentifier(param.name)) {
				paramName = param.name.text;
			} else {
				// Skip destructured parameters for now
				continue;
			}

			// Check if it's an inline object type literal
			if (ts.isTypeLiteralNode(param.type)) {
				for (const member of param.type.members) {
					if (ts.isPropertySignature(member) && ts.isIdentifier(member.name)) {
						const propName = member.name.text;
						const type = this.inferType(member.type);
						typeMap.set(`${paramName}.${propName}`, type);
					}
				}
			} else {
				// Named type reference (alias/interface/class, imported or
				// local — F14): decompose the resolved declaration into
				// per-property entries through the same import-aware
				// machinery as constructor signatures (F10), including the
				// heritage walk (F13). Without this, `this.x = param.y`
				// read `unknown` for named params — only inline literals
				// were decomposed. Unresolvable → whole-param fallback
				// below; a bare name is never emitted either way
				let namedDecl: ReferencedTypeDeclaration | undefined;
				if (ts.isTypeReferenceNode(param.type) && ts.isIdentifier(param.type.typeName)) {
					const paramTypeName = param.type.typeName.text;
					namedDecl = this.resolveReferencedTypeDeclaration(paramTypeName, this.currentReferencedTypeFile);
				}
				if (namedDecl) {
					// member types resolve against the DECLARING file
					const referencingFile = this.currentReferencedTypeFile;
					this.currentReferencedTypeFile = namedDecl.file;
					try {
						const declProperties = this.referencedDeclarationProperties(namedDecl);
						for (const [ propName, info ] of declProperties) {
							typeMap.set(`${paramName}.${propName}`, info.type);
						}
					} finally {
						this.currentReferencedTypeFile = referencingFile;
					}
					// keep the whole-param entry too: `this.x = data` (the
					// bare parameter) assigns the full expanded shape —
					// the same string constructor-signature emission uses
					const wholeType = this.expandReferencedTypeDeclaration(namedDecl);
					if (wholeType && wholeType !== 'unknown') {
						typeMap.set(paramName, wholeType);
					}
				} else {
					// Store simple parameter types like `decorateValue: string`
					const type = this.inferType(param.type);
					if (type !== 'unknown') {
						typeMap.set(paramName, type);
					}
				}
			}
		}

		return typeMap;
	}

	/**
	 * Extract property access chain (e.g., "dataRenamed.id" from dataRenamed.id)
	 * Handles fallbacks like: data.permissions || []
	 */
	private getPropertyAccessChain (expr: ts.Expression): string | undefined {
		// Handle identifier: data
		if (ts.isIdentifier(expr)) {
			return expr.text;
		}
		// Handle property access: data.permissions
		if (ts.isPropertyAccessExpression(expr)) {
			const base = this.getPropertyAccessChain(expr.expression);
			if (base) {
				return `${base}.${expr.name.text}`;
			}
		}
		// Handle fallback pattern: data.permissions || []
		if (ts.isBinaryExpression(expr) &&
			expr.operatorToken.kind === ts.SyntaxKind.BarBarToken) {
			// Return the left side of || operator
			return this.getPropertyAccessChain(expr.left);
		}
		return undefined;
	}

	/**
	 * Extract property assignment from statement
	 */
	private extractPropertyFromStatement (
		expr: ts.Expression,
		properties: Map<string, PropertyInfo>,
		dataTypeMap: Map<string, string> = new Map()
	): void {
		// Handle: this.property = value
		if (ts.isBinaryExpression(expr) &&
			expr.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
			const { left } = expr;

			if (ts.isPropertyAccessExpression(left)) {
				// Check if accessing 'this' (ThisKeyword)
				if (left.expression.kind === ts.SyntaxKind.ThisKeyword) {
					const name = left.name?.text;
					if (name) {
						// Try to get type from dataTypeMap using full access chain (e.g., "dataRenamed.id")
						const accessChain = this.getPropertyAccessChain(expr.right);
						let type = accessChain ? dataTypeMap.get(accessChain) : undefined;
						// If not found and RHS is a simple identifier, try looking it up directly
						if (!type && ts.isIdentifier(expr.right)) {
							type = dataTypeMap.get(expr.right.text);
						}
						// a bound construction result (new/lookup/chain/fork/
						// merge/call): the value scope binding supplies the
						// graph type — emitted by its instance-type name
						if (!type && ts.isIdentifier(expr.right)) {
							const bound = this.variableToTypeMap.get(expr.right.text);
							if (bound) {
								type = bound.replace(/\./g, '_');
							}
						}
						if (!type) {
							type = this.inferTypeFromInitializer(expr.right, dataTypeMap);
						}
						// Don't overwrite a known type from a `this` annotation
						// with an unknown-bearing inference: an empty-array
						// initializer infers 'Array<unknown>', which must not
						// clobber an annotated 'Array<{ id: number }>' either.
						// "Known" on the EXISTING side means the whole type IS
						// `unknown` (exact match) — a substring match treats
						// `Record<string, unknown>` as unknown-bearing and let
						// inference clobber a good annotation (F14)
						const existing = properties.get(name);
						const typeHasUnknown = !type || type.includes('unknown');
						const existingIsKnown = existing ? existing.type.trim() !== 'unknown' : false;
						if (existingIsKnown && typeHasUnknown) {
							// Keep the better type from explicit annotation
						} else {
							properties.set(name, {
								name,
								type,
								optional : existing ? existing.optional : false,
							});
						}
					}
				}
			}
		}

		// Handle: Object.assign(this, { prop: value })
		if (ts.isCallExpression(expr)) {
			const fn = expr.expression;
			if (ts.isPropertyAccessExpression(fn) &&
				fn.name?.text === 'assign' &&
				ts.isIdentifier(fn.expression) &&
				fn.expression.text === 'Object') {
				const args = expr.arguments;
				if (args.length >= 2 && args[ 0 ].kind === ts.SyntaxKind.ThisKeyword) {
					// Extract properties from the second argument
					const [ , propsArg ] = args;
					if (ts.isObjectLiteralExpression(propsArg)) {
						for (const prop of propsArg.properties) {
							if (ts.isPropertyAssignment(prop) && ts.isIdentifier(prop.name)) {
								const name = prop.name.text;
								properties.set(name, {
									name,
									type     : this.inferTypeFromInitializer(prop.initializer),
									optional : false,
								});
							}
						}
					} else if (ts.isIdentifier(propsArg)) {
						// Object.assign(this, data) — the identifier form: every
						// per-property entry the data parameter contributed to
						// the type map becomes an own property. This is what
						// carries the fields for the self-referencing
						// intersection-alias root pattern (F21): the this-alias
						// is ergonomic-only and its intersection members are
						// never expanded, so the assign is where the root's
						// fields must come from
						const paramName = propsArg.text;
						for (const [ key, type ] of dataTypeMap) {
							if (!key.startsWith(`${paramName}.`)) {
								continue;
							}
							const name = key.slice(paramName.length + 1);
							properties.set(name, {
								name,
								type,
								optional : false,
							});
						}
					}
				}
			}
		}
	}

	/**
	 * Extract properties from class declaration (including methods and getters)
	 */
	private extractClassProperties (classDecl: ts.ClassDeclaration): Map<string, PropertyInfo> {
		const properties = new Map<string, PropertyInfo>();

		for (const member of classDecl.members) {
			// Handle property declarations
			if (ts.isPropertyDeclaration(member) && member.name) {
				// Skip private and protected properties
				if (member.modifiers) {
					const hasPrivateOrProtected = member.modifiers.some(m => m.kind === ts.SyntaxKind.PrivateKeyword ||
						     m.kind === ts.SyntaxKind.ProtectedKeyword);
					if (hasPrivateOrProtected) {
						continue;
					}
				}

				const name = ts.isIdentifier(member.name) ? member.name.text : '';
				if (name) {
					// If no explicit type but has initializer, infer from initializer
					let type = this.inferType(member.type);
					if (type === 'unknown' && member.initializer) {
						type = this.inferTypeFromInitializer(member.initializer);
					}
					properties.set(name, {
						name,
						type,
						optional : !!member.questionToken,
					});
				}
			}

			// Handle method declarations
			if (ts.isMethodDeclaration(member) && member.name && ts.isIdentifier(member.name)) {
				// Skip private and protected methods
				if (member.modifiers) {
					const hasPrivateOrProtected = member.modifiers.some(m => m.kind === ts.SyntaxKind.PrivateKeyword ||
						     m.kind === ts.SyntaxKind.ProtectedKeyword);
					if (hasPrivateOrProtected) {
						continue;
					}
				}

				const name = member.name.text;
				const type = this.inferMethodType(member);
				properties.set(name, {
					name,
					type,
					optional : false,
				});
			}

			// Handle getter declarations
			if (ts.isGetAccessor(member) && member.name && ts.isIdentifier(member.name)) {
				// Skip private and protected getters
				if (member.modifiers) {
					const hasPrivateOrProtected = member.modifiers.some(m => m.kind === ts.SyntaxKind.PrivateKeyword ||
						     m.kind === ts.SyntaxKind.ProtectedKeyword);
					if (hasPrivateOrProtected) {
						continue;
					}
				}

				const name = member.name.text;
				// First try explicit type annotation, then infer from getter body
				let type = this.inferType(member.type);
				if (type === 'unknown' && member.body) {
					type = this.inferReturnTypeFromBody(member.body);
				}
				properties.set(name, {
					name,
					type,
					optional : false,
					readonly : true,
				});
			}
		}

		return properties;
	}

	/**
	 * Extract class property types for method return type inference
	 * Maps property names to their TypeScript type strings
	 * Note: Includes private/protected properties for method inference
	 */
	private extractClassPropertyTypes (classDecl: ts.ClassExpression): Map<string, string> {
		const propertyTypes = new Map<string, string>();

		for (const member of classDecl.members) {
			if (ts.isPropertyDeclaration(member) && member.name && ts.isIdentifier(member.name)) {
				// Include ALL properties (even private) for method return type inference
				// The visibility check is done when adding to output properties
				const name = member.name.text;
				if (member.type) {
					propertyTypes.set(name, this.inferType(member.type));
				}
			}
		}

		return propertyTypes;
	}

	/**
	 * Infer method type from method declaration
	 */
	private inferMethodType (method: ts.MethodDeclaration, classPropertyTypes?: Map<string, string>): string {
		const params = method.parameters.map(param => {
			const paramName = ts.isIdentifier(param.name) ? param.name.text : 'arg';
			const paramType = this.inferType(param.type);
			return `${paramName}: ${paramType}`;
		}).join(', ');

		const returnType = this.inferReturnType(method, classPropertyTypes);

		if (params) {
			return `(${params}) => ${returnType}`;
		}
		return `() => ${returnType}`;
	}

	/**
		* Extract properties from `this` parameter type annotation
		* Handles patterns like: function(this: SomeType, data: SomeType) { }
		*/
	private extractThisParamProperties (handlerArg: ts.FunctionExpression | ts.ArrowFunction):
		Map<string, PropertyInfo> {
		const properties = new Map<string, PropertyInfo>();

		// Find the `this` parameter (if any)
		for (const param of handlerArg.parameters) {
			if (param.name && ts.isIdentifier(param.name) && param.name.text === 'this' && param.type) {
				// Check if it's a type reference (e.g., `this: usage`)
				if (ts.isTypeReferenceNode(param.type)) {
					const typeName = ts.isIdentifier(param.type.typeName)
						? param.type.typeName.text
						: '';

					// Resolve through the referencing file's own imports first (F10)
					const decl = typeName
						? this.resolveReferencedTypeDeclaration(typeName, this.currentReferencedTypeFile)
						: undefined;
					if (decl) {
						const declProperties = this.referencedDeclarationProperties(decl);
						for (const [ propName, info ] of declProperties) {
							properties.set(propName, info);
						}
					}
				}
				// Check if it's directly an inline type literal (e.g., `this: { id: string }`)
				else if (ts.isTypeLiteralNode(param.type)) {
					for (const member of param.type.members) {
						if (ts.isPropertySignature(member) && ts.isIdentifier(member.name)) {
							const propName = member.name.text;
							const type = this.inferType(member.type);
							properties.set(propName, {
								name     : propName,
								type,
								optional : !!member.questionToken,
							});
						}
					}
				}
				// Found the `this` parameter, no need to continue
				break;
			}
		}

		return properties;
	}

	/**
		* Infer TypeScript type from type node
		*/
	/**
	 * Infer TypeScript type from type node
	 */
	private inferType (typeNode?: ts.TypeNode): string {
		if (!typeNode) {
			return 'unknown';
		}

		switch (typeNode.kind) {
		case ts.SyntaxKind.StringKeyword:
			return 'string';
		case ts.SyntaxKind.NumberKeyword:
			return 'number';
		case ts.SyntaxKind.BooleanKeyword:
			return 'boolean';
		case ts.SyntaxKind.UndefinedKeyword:
			return 'undefined';
		case ts.SyntaxKind.NullKeyword:
			return 'null';
		case ts.SyntaxKind.AnyKeyword:
			return 'any';
		case ts.SyntaxKind.UnknownKeyword:
			return 'unknown';
		case ts.SyntaxKind.VoidKeyword:
			return 'void';
		case ts.SyntaxKind.ArrayType:
			return `Array<${  this.inferType((typeNode as ts.ArrayTypeNode).elementType)  }>`;
		case ts.SyntaxKind.TypeLiteral: {
			// Inline-expand type literals instead of collapsing to 'object'
			const typeLit = typeNode as ts.TypeLiteralNode;
			const props: string[] = [];
			for (const member of typeLit.members) {
				if (ts.isPropertySignature(member) && ts.isIdentifier(member.name)) {
					const propName = member.name.text;
					const optional = member.questionToken ? '?' : '';
					const type = this.inferType(member.type);
					props.push(`${propName}${optional}: ${type}`);
				}
			}
			return `{ ${props.join('; ')} }`;
		}
		case ts.SyntaxKind.LiteralType: {
			// Handle string literal types like 'user', 'admin', etc.
			const { literal } = (typeNode as ts.LiteralTypeNode);
			if (ts.isStringLiteral(literal)) {
				// Return the actual literal value (e.g., 'user' instead of string)
				return `'${literal.text}'`;
			}
			if (ts.isNumericLiteral(literal)) {
				return literal.text;
			}
			if (literal.kind === ts.SyntaxKind.TrueKeyword) {
				return 'true';
			}
			if (literal.kind === ts.SyntaxKind.FalseKeyword) {
				return 'false';
			}
			if (literal.kind === ts.SyntaxKind.NullKeyword) {
				return 'null';
			}
			return 'unknown';
		}
		case ts.SyntaxKind.TypeReference: {
			// Handle type references like Map<string, number>, PropertyInfo, etc.
			const typeRef = typeNode as ts.TypeReferenceNode;

			// Qualified names (Namespace.Type): resolve through namespace imports
			if (ts.isQualifiedName(typeRef.typeName)) {
				const resolvedQualified = this.inferQualifiedTypeReference(typeRef);
				if (resolvedQualified !== undefined) {
					return resolvedQualified;
				}
				// unresolved qualified references must not leak a bare name
				return 'unknown';
			}

			const typeName = ts.isIdentifier(typeRef.typeName) ? typeRef.typeName.text : 'unknown';

			// Import-aware referenced-type resolution (F10): a declaration
			// reached through the current file's own imports (or its locals,
			// or a unique program-wide declaration) expands inline
			const simpleRef = this.resolveSimpleTypeReference(typeName, typeRef.typeArguments, typeRef);
			if (simpleRef !== undefined) {
				return simpleRef;
			}

			// Build generic type arguments
			const typeArgs = (typeRef.typeArguments ?? []).map(arg => this.inferType(arg));
			return `${typeName}<${typeArgs.join(', ')}>`;
		}
		case ts.SyntaxKind.UnionType: {
			// Handle union types like 'a' | 'b' | 'c'
			const unionType = typeNode as ts.UnionTypeNode;
			const types = unionType.types.map(t => this.inferType(t));
			return types.join(' | ');
		}
		case ts.SyntaxKind.IntersectionType: {
			// Handle intersection types like TypeA & TypeB
			const intersectionType = typeNode as ts.IntersectionTypeNode;
			const types = intersectionType.types.map(t => this.inferType(t));
			return types.join(' & ');
		}
		case ts.SyntaxKind.TupleType: {
			// Handle tuple types like [string, number]
			const tupleType = typeNode as ts.TupleTypeNode;
			const elements = tupleType.elements.map(elem => this.inferType(elem as ts.TypeNode));
			return `[${elements.join(', ')}]`;
		}
		case ts.SyntaxKind.OptionalType: {
			// Handle optional element in tuple: string?
			const optionalType = typeNode as ts.OptionalTypeNode;
			return `${this.inferType(optionalType.type)  }?`;
		}
		case ts.SyntaxKind.RestType: {
			// Handle rest element: ...T
			const restType = typeNode as ts.RestTypeNode;
			return `...${  this.inferType(restType.type)}`;
		}
		case ts.SyntaxKind.ParenthesizedType: {
			// Handle parenthesized types: (A | B)
			return this.inferType((typeNode as ts.ParenthesizedTypeNode).type);
		}
		case ts.SyntaxKind.IndexedAccessType: {
			// Handle indexed access: T[K]
			const indexed = typeNode as ts.IndexedAccessTypeNode;
			// F23: unwrap parentheses around the object — `(typeof
			// list)[number]` must take the typeof branch like the bare
			// spelling; otherwise the general path infers the union and
			// glues the suffix onto the LAST member
			// (`'a' | 'b'[number]`)
			let objectNode: ts.TypeNode = indexed.objectType;
			while (ts.isParenthesizedTypeNode(objectNode)) {
				objectNode = objectNode.type;
			}
			// `typeof constArray[K]` — element type of a tracked const array:
			// emit the element literal union directly (assembling
			// `union[K]` text would misread precedence, and when the const
			// is not statically visible the honest answer is `unknown`,
			// never a bare `typeof name` query)
			if (ts.isTypeQueryNode(objectNode) && ts.isIdentifier(objectNode.exprName)) {
				const queryName = objectNode.exprName.text;
				const arrayLiteral = this.findReferencedConstArray(queryName, this.currentReferencedTypeFile);
				const literals = arrayLiteral ? this.literalTypesOfArray(arrayLiteral) : undefined;
				if (!literals) {
					return 'unknown';
				}
				if (ts.isLiteralTypeNode(indexed.indexType) && ts.isNumericLiteral(indexed.indexType.literal)) {
					const elementIndex = parseInt(indexed.indexType.literal.text, 10);
					const element = literals[ elementIndex ];
					const elementResult = element === undefined ? 'unknown' : element;
					return elementResult;
				}
				const unionResult = literals.join(' | ');
				return unionResult;
			}
			let objectType = this.inferType(objectNode);
			const indexType = this.inferType(indexed.indexType);
			// If objectType is 'object', try to resolve the underlying referenced type
			if (objectType === 'object' && ts.isTypeReferenceNode(objectNode)) {
				const refName = ts.isIdentifier(objectNode.typeName) ? objectNode.typeName.text : '';
				if (refName) {
					const decl = this.resolveReferencedTypeDeclaration(refName, this.currentReferencedTypeFile);
					if (decl) {
						const expanded = this.expandReferencedTypeDeclaration(decl);
						if (expanded) {
							objectType = expanded;
						}
					}
				}
			}
			// Invariant: an index suffix must NEVER be glued onto an
			// unresolved/fallback target — `unknown[number]` / `object[K]`
			// are invalid TypeScript in the generated file (hard compile
			// break, F17). When either side did not resolve, the WHOLE
			// indexed access degrades to `unknown`.
			const targetUnresolved = objectType === 'unknown' || objectType === 'object';
			const indexUnresolved = indexType === 'unknown';
			if (targetUnresolved || indexUnresolved) {
				return 'unknown';
			}
			return `${objectType}[${indexType}]`;
		}
		case ts.SyntaxKind.TypeOperator: {
			// Handle keyof, readonly, unique operators
			const typeOp = typeNode as ts.TypeOperatorNode;
			const operator = ts.SyntaxKind[ typeOp.operator ];
			return `${operator} ${this.inferType(typeOp.type)}`;
		}
		case ts.SyntaxKind.TypeQuery: {
			// `typeof x` as a FIELD TYPE: the generated file has no imports,
			// so a bare `typeof x` would be an unresolvable name downstream.
			// When x is a tracked const array, emit its element literal
			// union; otherwise degrade to `unknown`. (InstanceType<typeof X>
			// graph types are handled in resolveSimpleTypeReference before
			// inferType runs.)
			const typeQuery = typeNode as ts.TypeQueryNode;
			if (ts.isIdentifier(typeQuery.exprName)) {
				const union = this.typeOfConstArrayUnion(typeQuery.exprName.text, this.currentReferencedTypeFile);
				if (union) {
					return union;
				}
			}
			return 'unknown';
		}
		default:
			// For complex types, return the text representation
			return 'unknown';
		}
	}

	/**
		* Infer return type from a method declaration
		* Uses explicit return type annotation or infers from return statements
		*/
	private inferReturnType (method: ts.MethodDeclaration, classPropertyTypes?: Map<string, string>): string {
		// If method has explicit return type annotation, use it
		if (method.type) {
			return this.inferType(method.type);
		}

		// Otherwise, try to infer from return statements in the method body
		if (method.body) {
			return this.inferReturnTypeFromBody(method.body, classPropertyTypes);
		}

		return 'unknown';
	}

	/**
		* Infer return type by analyzing return statements in the method body
		*/
	private inferReturnTypeFromBody (body: ts.Block, classPropertyTypes?: Map<string, string>): string {
		const returnTypes = new Set<string>();

		const visit = (node: ts.Node): void => {
			if (ts.isReturnStatement(node) && node.expression) {
				const type = this.inferTypeFromInitializer(node.expression, undefined, classPropertyTypes);
				if (type !== 'unknown') {
					returnTypes.add(type);
				}
			}
			ts.forEachChild(node, visit);
		};

		visit(body);

		if (returnTypes.size === 0) {
			return 'void';
		}
		if (returnTypes.size === 1) {
			return Array.from(returnTypes)[ 0 ];
		}
		return Array.from(returnTypes).join(' | ');
	}

	/**
	 * Infer type from initializer
	 */
	private inferTypeFromInitializer (
		initializer: ts.Expression,
		dataTypeMap?: Map<string, string>,
		classPropertyTypes?: Map<string, string>
	): string {
		switch (initializer.kind) {
		case ts.SyntaxKind.StringLiteral:
			return 'string';
		case ts.SyntaxKind.NumericLiteral:
			return 'number';
		case ts.SyntaxKind.TrueKeyword:
		case ts.SyntaxKind.FalseKeyword:
			return 'boolean';
		case ts.SyntaxKind.NullKeyword:
			return 'null';
		case ts.SyntaxKind.UndefinedKeyword:
			return 'undefined';
		case ts.SyntaxKind.ArrayLiteralExpression:
			return 'Array<unknown>';
		case ts.SyntaxKind.ObjectLiteralExpression:
			return 'object';
		case ts.SyntaxKind.NewExpression: {
			// Handle new Date(), new Map(), etc.
			const newExpr = initializer as ts.NewExpression;
			if (ts.isIdentifier(newExpr.expression)) {
				return newExpr.expression.text;
			}
			return 'object';
		}
		case ts.SyntaxKind.BinaryExpression: {
			// Handle arithmetic operations: a * b, a + b, a - b, a / b
			const binaryExpr = initializer as ts.BinaryExpression;
			const leftType = this.inferTypeFromInitializer(binaryExpr.left, dataTypeMap, classPropertyTypes);
			const rightType = this.inferTypeFromInitializer(binaryExpr.right, dataTypeMap, classPropertyTypes);
				
			// Check if it's an arithmetic operator
			const operator = binaryExpr.operatorToken.kind;
			if (operator === ts.SyntaxKind.AsteriskToken ||
				    operator === ts.SyntaxKind.SlashToken ||
				    operator === ts.SyntaxKind.MinusToken ||
				    operator === ts.SyntaxKind.PercentToken) {
				// Arithmetic operations on numbers produce numbers
				if ((leftType === 'number' || leftType === 'unknown') &&
					    (rightType === 'number' || rightType === 'unknown')) {
					return 'number';
				}
			}
			if (operator === ts.SyntaxKind.PlusToken) {
				// Plus can be addition or string concatenation
				if (leftType === 'string' || rightType === 'string') {
					return 'string';
				}
				if (leftType === 'number' && rightType === 'number') {
					return 'number';
				}
			}
			return 'unknown';
		}
		case ts.SyntaxKind.PropertyAccessExpression: {
			// Handle property access like data.value, data.id
			if (dataTypeMap) {
				const accessChain = this.getPropertyAccessChain(initializer);
				if (accessChain) {
					const type = dataTypeMap.get(accessChain);
					if (type) {
						return type;
					}
				}
			}
			// Handle this.map.size pattern (Map.size returns number)
			const propAccess = initializer as ts.PropertyAccessExpression;
			if (ts.isPropertyAccessExpression(propAccess.expression)) {
				const outerProp = propAccess.expression;
				// Check for this.map pattern
				let innerName = '';
				if (outerProp.expression.kind === ts.SyntaxKind.ThisKeyword) {
					innerName = 'this';
				} else if (ts.isIdentifier(outerProp.expression)) {
					innerName = outerProp.expression.text;
				}
				const mapProp = outerProp.name.text;
				const finalProp = propAccess.name.text;
				// this.map.size -> number
				if (innerName === 'this' && mapProp === 'map' && finalProp === 'size') {
					return 'number';
				}
			}
			return 'unknown';
		}
		case ts.SyntaxKind.Identifier: {
			// Handle identifier references if in dataTypeMap
			if (dataTypeMap) {
				const name = (initializer as ts.Identifier).text;
				const type = dataTypeMap.get(name);
				if (type) {
					return type;
				}
			}
			return 'unknown';
		}
		case ts.SyntaxKind.ElementAccessExpression: {
			// F22: value-level element access over a const-asserted
			// literal array — `(<const>[…])[0]`, `([…] as const)[1]`, or
			// a tracked module const (`const x = <const>[…]`; `x[0]`) —
			// infers the element's literal type, the value-level twin of
			// the typeof-path union. Non-numeric indexes, non-literal
			// elements, and general assertions stay `unknown`.
			const elementAccess = initializer as ts.ElementAccessExpression;
			const argument = elementAccess.argumentExpression;
			if (!argument || !ts.isNumericLiteral(argument)) {
				return 'unknown';
			}
			const arrayLiteral = this.constArrayLiteralOf(elementAccess.expression);
			if (!arrayLiteral) {
				return 'unknown';
			}
			const element = arrayLiteral.elements[ parseInt(argument.text, 10) ];
			if (!element || ts.isSpreadElement(element)) {
				return 'unknown';
			}
			const literal = this.literalTypeOfExpression(element);
			const elementResult = literal ?? 'unknown';
			return elementResult;
		}
		case ts.SyntaxKind.CallExpression: {
			// Handle function calls like Date.now(), parseInt(), etc.
			const callExpr = initializer as ts.CallExpression;
			if (ts.isPropertyAccessExpression(callExpr.expression)) {
				const methodName = callExpr.expression.name.text;
				const objName = ts.isIdentifier(callExpr.expression.expression)
					? callExpr.expression.expression.text
					: '';
					
				// Date.now() -> number
				if (objName === 'Date' && methodName === 'now') {
					return 'number';
				}
				// String methods that return string
				if (methodName === 'toString' || methodName === 'valueOf') {
					return 'string';
				}
				// Handle Map property access on class instances (this.map.*)
				if (ts.isPropertyAccessExpression(callExpr.expression.expression)) {
					const outerProp = callExpr.expression.expression;
					// Handle both 'this' keyword and identifier patterns
					let innerName = '';
					if (outerProp.expression.kind === ts.SyntaxKind.ThisKeyword) {
						innerName = 'this';
					} else if (ts.isIdentifier(outerProp.expression)) {
						innerName = outerProp.expression.text;
					}
					const mapProp = outerProp.name.text;
					// this.map.X() patterns
					if (innerName === 'this' && mapProp === 'map') {
						// Try to get the Map's value type from class properties
						let mapValueType = 'unknown';
						if (classPropertyTypes) {
							const mapType = classPropertyTypes.get('map');
							if (mapType && mapType.startsWith('Map<')) {
								// Parse Map<K, V> to get V
								const match = mapType.match(/Map<[^,]+,\s*(.+)>$/);
								if (match) {
									[ , mapValueType ] = match;
								}
							}
						}
						if (methodName === 'has') return 'boolean';
						if (methodName === 'set') return 'this';
						if (methodName === 'get') return mapValueType;
						if (methodName === 'delete') return 'boolean';
						if (methodName === 'clear') return 'void';
						if (methodName === 'values') return `IterableIterator<${mapValueType}>`;
						if (methodName === 'keys') return 'IterableIterator<string>';
						if (methodName === 'entries') return `IterableIterator<[string, ${mapValueType}]>`;
					}
				}
				// Direct map.X() calls
				if (objName === 'map' || objName === 'obj') {
					if (methodName === 'has') return 'boolean';
					if (methodName === 'set') return 'this';
					if (methodName === 'get') return 'unknown';
					if (methodName === 'delete') return 'boolean';
					if (methodName === 'clear') return 'void';
					if (methodName === 'values') return 'IterableIterator<unknown>';
					if (methodName === 'keys') return 'IterableIterator<string>';
					if (methodName === 'entries') return 'IterableIterator<[string, unknown]>';
				}
			}
			// parseInt, parseFloat -> number
			if (ts.isIdentifier(callExpr.expression)) {
				const fnName = callExpr.expression.text;
				if (fnName === 'parseInt' || fnName === 'parseFloat') {
					return 'number';
				}
				if (fnName === 'String') {
					return 'string';
				}
				if (fnName === 'Number') {
					return 'number';
				}
				if (fnName === 'Boolean') {
					return 'boolean';
				}
			}
			return 'unknown';
		}
		case ts.SyntaxKind.TemplateExpression:
		case ts.SyntaxKind.NoSubstitutionTemplateLiteral: {
			// Template literals like `${baseValue}-${extra}` always produce strings
			return 'string';
		}
		default:
			return 'unknown';
		}
	}
	
	/**
			* Collect usage information for type references
			*/
	private collectUsage (node: ts.Node, sourceFile: ts.SourceFile): void {
		// Check for new Type() instantiation
		if (ts.isNewExpression(node) && node.expression) {
			let typeName: string | undefined;
			if (ts.isPropertyAccessExpression(node.expression)) {
				typeName = this.resolveTypePath(node.expression);
			} else {
				typeName = this.getTypeNameFromExpression(node.expression);
			}
			if (typeName) {
				const { line, character } = ts.getLineAndCharacterOfPosition(
					sourceFile,
					node.getStart(sourceFile)
				);
				this.addUsage(typeName, {
					location        : `${sourceFile.fileName}:${line + 1}:${character + 1}`,
					kind            : 'instantiation',
					code            : node.getText(sourceFile).slice(0, 100),
					// Constructor expression text ('Thing', 'user.AdminEntity',
					// a lookup alias) — CreationAnchor.constructorText (Phase 3)
					constructorText : node.expression.getText(sourceFile).slice(0, 100),
				});
				// Track variable assignment from new Type() for flow analysis
				this.trackNewAssignment(node, typeName);
				// Also record as flow event
				this.addFlow(typeName, {
					location : `${sourceFile.fileName}:${line + 1}:${character + 1}`,
					kind     : 'instantiation',
					code     : node.getText(sourceFile).slice(0, 100),
					context  : 'new expression',
				});
			}
		}
	
		// Check for property access on instances (user.AdminType)
		if (ts.isPropertyAccessExpression(node)) {
			const propName = node.name.text;
			// instance.clone — the PROPERTY form (core types it
			// `readonly clone: this`): the result variable binds to the
			// source instance's type, same as the fork()/clone() call
			// forms (await-transparent). The call form's recording happens
			// in the CallExpression branch; the property branch skips it
			// to avoid a duplicate entry at the same site
			if (propName === 'clone' && ts.isIdentifier(node.expression)) {
				const clonedPath = this.variableToTypeMap.get(node.expression.text);
				const isCallForm = ts.isCallExpression(node.parent) && node.parent.expression === node;
				if (clonedPath) {
					if (!isCallForm) {
						const { line, character } = ts.getLineAndCharacterOfPosition(
							sourceFile,
							node.getStart(sourceFile)
						);
						this.addUsage(clonedPath, {
							location        : `${sourceFile.fileName}:${line + 1}:${character + 1}`,
							kind            : 'instantiation',
							code            : node.getText(sourceFile).slice(0, 100),
							constructorText : node.getText(sourceFile).slice(0, 100),
						});
					}
					this.bindResultVariable(node, clonedPath);
				}
			}
			// Check if this looks like a type access pattern
			if (propName && this.isLikelyTypeName(propName)) {
				const { line, character } = ts.getLineAndCharacterOfPosition(
					sourceFile,
					node.getStart(sourceFile)
				);
					// Try to resolve full path
				const fullPath = this.resolveTypePath(node);
				if (fullPath) {
					this.addUsage(fullPath, {
						location : `${sourceFile.fileName}:${line + 1}:${character + 1}`,
						kind     : 'propertyAccess',
						code     : node.getText(sourceFile).slice(0, 100),
					});
				}
			}
		}
	
		// Check for lookup('TypeName') or lookup(source, 'TypeName') calls
		if (ts.isCallExpression(node) && node.expression) {
			const funcName = this.getFunctionName(node.expression);
			if (funcName === 'lookup' && node.arguments.length > 0) {
				const typePath = this.resolveLookupPath(node);
				if (typePath) {
					const { line, character } = ts.getLineAndCharacterOfPosition(
						sourceFile,
						node.getStart(sourceFile)
					);
					const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
					this.addUsage(typePath, {
						location,
						kind : 'lookup',
						code : node.getText(sourceFile).slice(0, 100),
					});
					// Track variable assignment from lookup for instantiation tracking
					this.trackLookupAssignment(node, typePath);
					// Record for the hard-fail law even when addUsage dropped
					// the path (unknown paths are exactly the failure class)
					this.lookupReferences.push({ path : typePath, location });
				}
			}

			// Chain-form construction: `new R(...).A(...)` / the awaited
			// single-chain `await new R(...).A(...).B(...)` — the call on
			// the fresh instance constructs the chain TIP (await is
			// transparent; the NewExpression branch already recorded the
			// inner root). The result variable binds to the tip, not the
			// root (trackNewAssignment resolves the same tip)
			const chainTip = this.resolveChainTipTypePath(node);
			if (chainTip) {
				this.recordConstructionUsage(node, chainTip, sourceFile);
				const { line, character } = ts.getLineAndCharacterOfPosition(
					sourceFile,
					node.getStart(sourceFile)
				);
				this.addFlow(chainTip, {
					location : `${sourceFile.fileName}:${line + 1}:${character + 1}`,
					kind     : 'instantiation',
					code     : node.getText(sourceFile).slice(0, 100),
					context  : 'chained construction',
				});
			}

			// mnemonica call/apply(entity, Ctor, ...) / bind(entity, Ctor) —
			// typed construction without `new`: the Ctor argument (arg 1) is
			// the constructed type. Import-aware: only identifiers actually
			// imported from 'mnemonica' (or members of a tracked
			// module-object alias) match — userland call/apply/bind never
			// do. call/apply record the construction; bind() constructs
			// nothing — it only binds the result variable to the Ctor's
			// type (runtime InstanceResult<Merge<E,T>> approximated by T
			// within the output contract)
			const constructionPath = this.resolveConstructionFnTypePath(node);
			if (constructionPath) {
				const isBindForm = this.isMnemonicaConstructionFn(node.expression, 'bind');
				if (!isBindForm) {
					const ctorArgText = node.arguments[ 1 ]?.getText(sourceFile);
					this.recordConstructionUsage(node, constructionPath, sourceFile, ctorArgText);
					const { line, character } = ts.getLineAndCharacterOfPosition(
						sourceFile,
						node.getStart(sourceFile)
					);
					this.addFlow(constructionPath, {
						location : `${sourceFile.fileName}:${line + 1}:${character + 1}`,
						kind     : 'instantiation',
						code     : node.getText(sourceFile).slice(0, 100),
						context  : 'call/apply construction',
					});
				}
				this.bindResultVariable(node, constructionPath);
			}

			// instance.fork()/clone() — runtime re-runs construction (hooks
			// fire, a distinct instance on a distinct line), so an
			// `instantiation` usage records the site IN ADDITION to the
			// result-var binding and the generic methodCall flow (the entry
			// is byte-indistinguishable from `new` until the deferred
			// mechanism-kind revision — the owner's explicit call). Free
			// utils.merge(a, b, ...) / utils.fork(instance)(...) are
			// construction of a's type too (merge = fork(a) over b's
			// context); the result binding keeps the documented arg-0
			// approximation
			const forkLikePath = this.resolveForkLikeTypePath(node);
			if (forkLikePath) {
				this.recordConstructionUsage(node, forkLikePath, sourceFile);
				this.bindResultVariable(node, forkLikePath);
			}
			const utilsPath = this.resolveUtilsFnTypePath(node);
			if (utilsPath) {
				this.recordConstructionUsage(node, utilsPath, sourceFile);
				this.bindResultVariable(node, utilsPath);
			}
		}
	}
	
	/**
			* Get function name from expression (identifier or property access)
			*/
	private getFunctionName (expr: ts.Expression): string | undefined {
		if (ts.isIdentifier(expr)) {
			return expr.text;
		}
		if (ts.isPropertyAccessExpression(expr)) {
			return expr.name.text;
		}
		return undefined;
	}
	
	/**
			* Add a usage to the collection
			*/
	private addUsage (typePath: string, usage: UsageInfo): void {
		// Only track usages of mnemonica-defined types
		if (!this.definitions.has(typePath)) {
			return;
		}
		if (!this.usages.has(typePath)) {
			this.usages.set(typePath, []);
		}

		// Check for duplicates based on location, code, and kind
		const existingUsages = this.usages.get(typePath)!;
		const isDuplicate = existingUsages.some(existing =>
			existing.location === usage.location &&
				existing.code === usage.code &&
				existing.kind === usage.kind);

		if (!isDuplicate) {
			existingUsages.push(usage);
		}
	}

	/**
	 * Collect EDS (Execution Data Storage) usage information
	 */
	private collectEDS (node: ts.Node, sourceFile: ts.SourceFile): void {
		if (!ts.isCallExpression(node) || !node.expression) {
			return;
		}

		const funcName = this.getFunctionName(node.expression);
		if (!funcName) {
			return;
		}

		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			node.getStart(sourceFile)
		);
		const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
		const code = node.getText(sourceFile).slice(0, 100);
		// Enclosing mnemonica type path — wrap args are usually local
		// functions, so the owning define()/lazy() handler or decorated
		// class is what eds.json consumers (GraphBuilder) can join on.
		const scope = this.resolveEDSScope(node);

		// wrap(fn), wrapConstructorArg(fn, parent), upgradeConstructorArg(arg, inst), wrapInstanceMethods(obj)
		if (
			funcName === 'wrap' ||
			funcName === 'wrapConstructorArg' ||
			funcName === 'upgradeConstructorArg' ||
			funcName === 'wrapInstanceMethods'
		) {
			const targetType = this.resolveEDSArgumentType(node.arguments[ 0 ]);
			// dive's wrap-family signatures (dive/src/index.ts):
			//   wrap(fn, label?) | wrap(fn, context?, label?)
			//   wrapConstructorArg(fn, context)
			//   upgradeConstructorArg(arg, instance)
			//   wrapInstanceMethods(instance)
			// …so the instance/context arg sits at args[1] (args[0] for
			// wrapInstanceMethods) and a string literal in args[1..2] is the label
			const instanceArgNode = funcName === 'wrapInstanceMethods'
				? node.arguments[ 0 ]
				: node.arguments[ 1 ];
			// Fire-and-forget wrappers (wire-up helpers, registration
			// functions) sit outside any define()/lazy() handler, so the
			// lexical scope is absent — attribute through the instance/context
			// argument instead: a tracked assignment, else the enclosing
			// function's parameter annotation resolved through the graph law
			const instanceTypePath = instanceArgNode
				? this.resolveWrapInstanceTypePath(instanceArgNode)
				: undefined;
			const effectiveScope = scope ?? instanceTypePath;
			const info: EDSInfo = {
				location,
				kind       : 'wrap',
				code,
				targetType : targetType || undefined,
				scope      : effectiveScope,
				fn         : funcName,
			};
			if (instanceArgNode && ts.isIdentifier(instanceArgNode)) {
				info.instanceArg = instanceArgNode.text;
			}
			for (const extraArg of [ node.arguments[ 1 ], node.arguments[ 2 ] ]) {
				if (extraArg && ts.isStringLiteral(extraArg)) {
					info.label = extraArg.text;
					break;
				}
			}
			// A wrap() call nested inside another wrapped body carries the
			// link to the site whose runtime wrapping caused it — and, when
			// the nested site has no scope of its own, the causing site's
			// scope attribution travels with the link
			const viaLink = this.nestedWrapVia.get(node);
			if (viaLink) {
				info.via = viaLink.via;
				if (info.scope === undefined) {
					info.scope = viaLink.scope;
				}
			}
			// dive wraps returned functions too, and any mnemonica instance
			// created inside the wrapped body is a guaranteed path hit —
			// both are calculable AoT, so record them
			const wrapped = this.resolveFunctionArgument(node.arguments[ 0 ], sourceFile);
			if (wrapped) {
				// The wrapped callback gets its own scope in scopes.json keyed by
				// its start position — record that scopeId so graph consumers can
				// join a wrap entry to the callback's creation node
				const callbackPos = ts.getLineAndCharacterOfPosition(
					sourceFile,
					wrapped.getStart(sourceFile)
				);
				const callbackFile = nodePath.resolve(sourceFile.fileName);
				info.callbackScopeId = `${callbackFile}:${callbackPos.line + 1}:${callbackPos.character + 1}`;
				const createsTypes = new Set<string>();
				this.analyzeWrappedBody(wrapped, location, sourceFile, 0, new Set(), createsTypes, effectiveScope);
				if (createsTypes.size > 0) {
					info.createsTypes = Array.from(createsTypes);
				}
			}
			const stored = this.addEDS(targetType || effectiveScope || 'unknown', info);
			this.wrapEntryByNode.set(node, stored);
			return;
		}

		// current(), getErrorInstance(err), getFlow(target?)
		if (funcName === 'current' || funcName === 'getErrorInstance' || funcName === 'getFlow') {
			this.addEDS(scope || 'unknown', {
				location,
				kind : 'contextConsume',
				code,
				scope,
			});
			return;
		}

		// attachHooks(collection) — from @mnemonica/otel, wires a
		// TypesCollection to dive's lifecycle tracing
		if (funcName === 'attachHooks' && node.arguments.length > 0) {
			const [ arg ] = node.arguments;
			if (ts.isArrayLiteralExpression(arg)) {
				for (const element of arg.elements) {
					const targetType = this.resolveEDSArgumentType(element);
					this.addEDS(targetType || scope || 'unknown', {
						location,
						kind       : 'hookAttach',
						code,
						targetType : targetType || undefined,
						scope,
					});
				}
			} else {
				const targetType = this.resolveEDSArgumentType(arg);
				this.addEDS(targetType || scope || 'unknown', {
					location,
					kind       : 'hookAttach',
					code,
					targetType : targetType || undefined,
					scope,
				});
			}
			return;
		}
	}

	/**
	 * Resolve type from EDS call argument (best effort)
	 */
	private resolveEDSArgumentType (arg: ts.Expression | undefined): string | undefined {
		if (!arg) {
			return undefined;
		}

		// Identifier: variable name
		if (ts.isIdentifier(arg)) {
			const mapped = this.variableToTypeMap.get(arg.text);
			if (mapped) {
				return mapped;
			}
			// Maybe it's a type name directly
			if (this.definitions.has(arg.text)) {
				return arg.text;
			}
			// let-in-try: a let/var binding declared without a tracked
			// initializer and assigned later in the SAME scope (the
			// fire-and-forget catch-guard pattern: `let fn; try { fn =
			// … } catch { return } wrap(fn, …)`) — follow the first
			// statically-visible in-scope assignment. No flow analysis:
			// function/class boundaries are not crossed, a
			// never-assigned binding stays unknown (F20 discipline).
			// When the assignment resolves, its evidence WINS over any
			// declaration annotation (the constructed subtype is the more
			// specific truth); an unresolvable RHS (a userland call, say)
			// falls through to the annotation claim below.
			const assigned = this.followScopeAssignment(arg.text, arg);
			if (assigned) {
				const resolved = this.resolveEDSArgumentType(assigned);
				if (resolved) {
					return resolved;
				}
			}
			// Annotation fallback — the F20 discipline one argument over:
			// an explicit declaration or parameter annotation is a user
			// claim written in the AST, not flow analysis. Parameter
			// first: it shadows an outer let, same as the context-arg path.
			const annotated = this.resolveParameterAnnotationTypePath(arg.text, arg) ??
				this.resolveVariableAnnotationTypePath(arg.text, arg);
			return annotated;
		}

		// NewExpression: the constructed type — reachable directly
		// (wrap(new T(), …)) or through a followed assignment
		if (ts.isNewExpression(arg)) {
			const ctorExpr = arg.expression;
			const name = ts.isPropertyAccessExpression(ctorExpr)
				? this.resolveTypePath(ctorExpr)
				: this.getTypeNameFromExpression(ctorExpr);
			const known = name && this.definitions.has(name) ? name : undefined;
			return known;
		}

		// Property access: obj.prop
		if (ts.isPropertyAccessExpression(arg)) {
			return this.resolveTypePath(arg);
		}

		// This expression: this.something
		if (ts.isPropertyAccessExpression(arg) && ts.isIdentifier(arg.expression) && arg.expression.text === 'this') {
			return undefined;
		}

		return undefined;
	}

	/**
	 * let-in-try: find the RIGHT-HAND SIDE of the first statically-visible
	 * assignment to `name` in the scope that declares it. The declaring
	 * container is found innermost-out (blocks, case clauses, the source
	 * file — the F20 walk); the scan recurses into nested blocks (try/
	 * catch/finally, if/else, loops, switch cases) but NEVER crosses
	 * function or class boundaries — an assignment inside a closure does
	 * not attribute. Returns undefined when the binding is declared but
	 * never assigned in scope (and stops there: an inner declaration
	 * shadows any outer binding).
	 */
	private followScopeAssignment (name: string, from: ts.Node): ts.Expression | undefined {
		let current: ts.Node | undefined = from;
		while (current) {
			const statements: ts.NodeArray<ts.Statement> | undefined =
				ts.isBlock(current) || ts.isModuleBlock(current) || ts.isSourceFile(current)
					? current.statements
					: ts.isCaseClause(current) || ts.isDefaultClause(current)
						? current.statements
						: undefined;
			if (statements && this.statementsDeclareVariable(statements, name)) {
				const rhs = this.findAssignmentRhsInStatements(statements, name);
				return rhs;
			}
			current = current.parent;
		}
		return undefined;
	}

	/**
	 * True when the statement list contains a `let`/`var`/`const`
	 * declaration for `name` (any initializer form).
	 */
	private statementsDeclareVariable (statements: readonly ts.Statement[], name: string): boolean {
		for (const statement of statements) {
			if (!ts.isVariableStatement(statement)) {
				continue;
			}
			for (const declaration of statement.declarationList.declarations) {
				if (ts.isIdentifier(declaration.name) && declaration.name.text === name) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * First `name = rhs` assignment in the statement list, recursing
	 * into nested in-scope blocks. Function and class bodies are
	 * boundaries and are not entered.
	 */
	private findAssignmentRhsInStatements (
		statements: readonly ts.Statement[],
		name: string
	): ts.Expression | undefined {
		for (const statement of statements) {
			const direct = this.directAssignmentRhs(statement, name);
			if (direct) {
				return direct;
			}
			for (const nested of this.nestedScopeBlocks(statement)) {
				const found = this.findAssignmentRhsInStatements(nested, name);
				if (found) {
					return found;
				}
			}
		}
		return undefined;
	}

	/**
	 * `name = rhs` as a direct expression statement.
	 */
	private directAssignmentRhs (statement: ts.Statement, name: string): ts.Expression | undefined {
		if (!ts.isExpressionStatement(statement)) {
			return undefined;
		}
		const expr = statement.expression;
		if (!ts.isBinaryExpression(expr) || expr.operatorToken.kind !== ts.SyntaxKind.EqualsToken) {
			return undefined;
		}
		if (!ts.isIdentifier(expr.left) || expr.left.text !== name) {
			return undefined;
		}
		const rhs = expr.right;
		return rhs;
	}

	/**
	 * Statement lists of the nested blocks that stay INSIDE the current
	 * scope — try/catch/finally, if/else, loops, switch cases, nested
	 * blocks, labeled statements. Function-like and class bodies are
	 * scope boundaries and yield nothing.
	 */
	private nestedScopeBlocks (statement: ts.Statement): readonly (readonly ts.Statement[])[] {
		const blocks: ts.Statement[][] = [];
		const push = (node: ts.Statement | undefined): void => {
			if (node && ts.isBlock(node)) {
				blocks.push([ ...node.statements ]);
			}
		};
		if (ts.isBlock(statement)) {
			blocks.push([ ...statement.statements ]);
		} else if (ts.isTryStatement(statement)) {
			push(statement.tryBlock);
			if (statement.catchClause) {
				push(statement.catchClause.block);
			}
			push(statement.finallyBlock);
		} else if (ts.isIfStatement(statement)) {
			push(statement.thenStatement);
			push(statement.elseStatement);
		} else if (ts.isForStatement(statement) || ts.isForInStatement(statement) ||
			ts.isForOfStatement(statement) || ts.isWhileStatement(statement) ||
			ts.isDoStatement(statement) || ts.isWithStatement(statement)) {
			push(statement.statement);
		} else if (ts.isSwitchStatement(statement)) {
			for (const clause of statement.caseBlock.clauses) {
				blocks.push([ ...clause.statements ]);
			}
		} else if (ts.isLabeledStatement(statement)) {
			const nested = this.nestedScopeBlocks(statement.statement);
			for (const block of nested) {
				blocks.push([ ...block ]);
			}
		}
		const result = blocks;
		return result;
	}

	/**
	 * Resolve the enclosing mnemonica scope of an EDS call site by walking
	 * up the parent chain: nearest define()/lazy() call whose handler holds
	 * the node, or nearest @decorate()-ed class declaration. Best effort —
	 * returns undefined for calls outside any type scope (module top level).
	 */
	private resolveEDSScope (node: ts.Node): string | undefined {
		let current: ts.Node | undefined = node.parent;
		while (current) {
			const scopePath = this.edsScopeByNode.get(current);
			if (scopePath) {
				return scopePath;
			}
			current = current.parent;
		}
		return undefined;
	}

	/**
	 * Resolve a wrap site's instance/context argument to a mnemonica type
	 * path — the fire-and-forget-wrapper attribution fallback when the call
	 * sits outside any define()/lazy() handler: a tracked assignment
	 * (`const holder = new Holder(...)`), else the root identifier's
	 * (property-access roots included) parameter annotation resolved
	 * through the graph law. Ambiguity or absence stays silent — this is a
	 * metadata heuristic, not the identity-law surface.
	 */
	private resolveWrapInstanceTypePath (arg: ts.Expression): string | undefined {
		const fromBinding = (name: string, from: ts.Node): string | undefined => {
			const mapped = this.variableToTypeMap.get(name);
			if (mapped) {
				return mapped;
			}
			const annotationType = this.resolveParameterAnnotationTypePath(name, from) ??
				// F20 cheap tier: the identifier is bound to a let/var/const
				// with an EXPLICIT type annotation — resolve the annotation
				// through the graph law. No flow-sensitive assignment
				// tracking: an UNANNOTATED let still buckets unknown
				this.resolveVariableAnnotationTypePath(name, from);
			return annotationType;
		};

		if (ts.isIdentifier(arg)) {
			const result = fromBinding(arg.text, arg);
			return result;
		}
		if (ts.isPropertyAccessExpression(arg)) {
			const root = this.getRootIdentifier(arg);
			if (root) {
				const result = fromBinding(root.text, arg);
				return result;
			}
		}
		return undefined;
	}

	/**
	 * F24: resolve a bare-identifier annotation to a graph fullPath. The
	 * annotation may name the type directly (`LedgerUpdate`) or carry
	 * the GENERATED instance alias of a nested type
	 * (`UpdatePay_SomeTerminal`, imported from the generated types file
	 * via tsconfig paths) — not a graph node NAME. The name is tried
	 * as-is first, then its underscore→dotted form (the generated alias
	 * naming law; the same mapping scopes.json uses for annotations).
	 * Ambiguity and absence yield undefined.
	 */
	private resolveAnnotationTypePath (name: string): string | undefined {
		const direct = this.resolveGraphTypeName(name);
		if (direct.status === 'unique') {
			const result = direct.node.fullPath;
			return result;
		}
		if (!name.includes('_')) {
			return undefined;
		}
		const aliased = this.resolveGraphTypeName(name.replace(/_/g, '.'));
		if (aliased.status === 'unique') {
			const result = aliased.node.fullPath;
			return result;
		}
		return undefined;
	}

	/**
	 * Resolve a bare-identifier type annotation of the nearest enclosing
	 * function's parameter through the mnemonica-graph tiers (value scope,
	 * imports, roots, program-wide-unique). Non-identifier and generic
	 * annotations are not graph references; ambiguity and absence yield
	 * undefined.
	 */
	private resolveParameterAnnotationTypePath (name: string, from: ts.Node): string | undefined {
		let current: ts.Node | undefined = from.parent;
		while (current) {
			if (ts.isFunctionLike(current)) {
				for (const param of current.parameters ?? []) {
					if (!ts.isIdentifier(param.name) || param.name.text !== name || !param.type ||
						!ts.isTypeReferenceNode(param.type) ||
						!ts.isIdentifier(param.type.typeName) ||
						(param.type.typeArguments?.length ?? 0) > 0) {
						continue;
					}
					const resolved = this.resolveAnnotationTypePath(param.type.typeName.text);
					if (resolved) {
						return resolved;
					}
				}
				return undefined;
			}
			current = current.parent;
		}
		return undefined;
	}

	/**
	 * F20 cheap tier: the wrap argument is an identifier declared with an
	 * EXPLICIT type annotation (`let updateCommitted: LedgerUpdate;`
	 * assigned later in a flow the analyzer does not track). The
	 * annotation resolves through the same graph tiers as parameter
	 * annotations. Deliberately NOT flow-sensitive: an UNANNOTATED
	 * let/var still buckets unknown, and a const with an analyzable
	 * initializer stays the recommended discipline. The lookup walks the
	 * enclosing statement containers innermost-out, so a shadowing inner
	 * declaration wins.
	 */
	private resolveVariableAnnotationTypePath (name: string, from: ts.Node): string | undefined {
		let current: ts.Node | undefined = from;
		while (current) {
			const statements: ts.NodeArray<ts.Statement> | undefined =
				ts.isBlock(current) || ts.isModuleBlock(current) || ts.isSourceFile(current)
					? current.statements
					: ts.isCaseClause(current) || ts.isDefaultClause(current)
						? current.statements
						: undefined;
			if (statements) {
				const resolved = this.findAnnotatedVariableTypePath(statements, name);
				if (resolved) {
					return resolved;
				}
			}
			current = current.parent;
		}
		return undefined;
	}

	/**
	 * First variable declaration carrying an explicit bare-identifier type
	 * annotation for `name` in the given statement list, resolved through
	 * the graph law.
	 */
	private findAnnotatedVariableTypePath (
		statements: readonly ts.Statement[],
		name: string
	): string | undefined {
		for (const statement of statements) {
			if (!ts.isVariableStatement(statement)) {
				continue;
			}
			for (const declaration of statement.declarationList.declarations) {
				if (!ts.isIdentifier(declaration.name) || declaration.name.text !== name ||
					!declaration.type ||
					!ts.isTypeReferenceNode(declaration.type) ||
					!ts.isIdentifier(declaration.type.typeName) ||
					(declaration.type.typeArguments?.length ?? 0) > 0) {
					continue;
				}
				const resolved = this.resolveAnnotationTypePath(declaration.type.typeName.text);
				if (resolved) {
					return resolved;
				}
			}
		}
		return undefined;
	}

	/**
	 * Resolve a wrap() argument to its function node without the type
	 * checker: direct function expressions/arrows, or same-file bindings
	 * (`const fn = () => ...`, `function fn() ...`). Best effort — method
	 * references, .bind() products and cross-file identifiers stay
	 * unresolved; the callsite entry itself is still recorded.
	 */
	private resolveFunctionArgument (
		arg: ts.Expression | undefined,
		sourceFile: ts.SourceFile
	): ts.FunctionLikeDeclaration | undefined {
		if (!arg) {
			return undefined;
		}
		if (ts.isArrowFunction(arg) || ts.isFunctionExpression(arg)) {
			return arg;
		}
		if (ts.isIdentifier(arg)) {
			const key = `${sourceFile.fileName}#${arg.text}`;
			const bound = this.functionBindings.get(key);
			if (bound) {
				return bound;
			}
		}
		return undefined;
	}

	/**
	 * Analyse a wrapped function's body for guaranteed runtime paths:
	 * dive wraps returned functions as well (recursively), so each
	 * function-valued return is a nested wrap site, and each `new Type()`
	 * inside the body means the path hits that type's constructor (which
	 * attachHooks wraps too). Both facts are 100% ensured, so they are
	 * recorded AoT. Nested function bodies are NOT walked here — they
	 * belong to their own wrap analysis, reached via the return chain.
	 * Depth-capped and cycle-guarded.
	 */
	private analyzeWrappedBody (
		fn: ts.FunctionLikeDeclaration,
		viaLocation: string,
		sourceFile: ts.SourceFile,
		depth: number,
		visited: Set<ts.Node>,
		createsTypes: Set<string>,
		fallbackScope?: string
	): void {
		if (depth > 5 || visited.has(fn) || !fn.body) {
			return;
		}
		visited.add(fn);

		// Arrow with expression body: implicit return
		if (ts.isArrowFunction(fn) && !ts.isBlock(fn.body)) {
			this.recordWrappedReturn(fn.body, viaLocation, sourceFile, depth, visited, fallbackScope);
			return;
		}

		const walk = (node: ts.Node): void => {
			if (node !== fn.body && (
				ts.isFunctionExpression(node) ||
				ts.isArrowFunction(node) ||
				ts.isFunctionDeclaration(node) ||
				ts.isMethodDeclaration(node)
			)) {
				// nested function bodies are analysed through the return chain
				return;
			}
			if (ts.isReturnStatement(node) && node.expression) {
				this.recordWrappedReturn(node.expression, viaLocation, sourceFile, depth, visited, fallbackScope);
			}
			if (ts.isNewExpression(node)) {
				const created = this.resolveExpressionType(node.expression) ||
					(ts.isIdentifier(node.expression) && this.definitions.has(node.expression.text)
						? node.expression.text
						: undefined);
				if (created) {
					createsTypes.add(created);
				}
			}
			if (ts.isCallExpression(node)) {
				const nestedName = this.getFunctionName(node.expression);
				if (
					nestedName === 'wrap' ||
					nestedName === 'wrapConstructorArg' ||
					nestedName === 'upgradeConstructorArg' ||
					nestedName === 'wrapInstanceMethods'
				) {
					// the nested call may already be collected (visited
					// before this outer wrap site) — back-patch its entry,
					// otherwise leave the link (with this site's scope) for
					// collectEDS to pick up
					const nestedEntry = this.wrapEntryByNode.get(node);
					if (nestedEntry) {
						nestedEntry.via = viaLocation;
						if (nestedEntry.scope === undefined) {
							nestedEntry.scope = fallbackScope;
						}
					} else {
						this.nestedWrapVia.set(node, { via : viaLocation, scope : fallbackScope });
					}
				}
			}
			ts.forEachChild(node, walk);
		};
		walk(fn.body);
	}

	/**
	 * Record one function-valued return of a wrapped body as a nested wrap
	 * site (`via` = the site whose wrapping caused it) and recurse into
	 * its own returns. Returns through identifiers resolve through the
	 * same-file bindings table; unresolvable returns are simply skipped.
	 * A return declared outside any type scope inherits the causing wrap
	 * site's scope attribution (the generation chain is the only holder).
	 */
	private recordWrappedReturn (
		expr: ts.Expression,
		viaLocation: string,
		sourceFile: ts.SourceFile,
		depth: number,
		visited: Set<ts.Node>,
		fallbackScope?: string
	): void {
		const returned = this.resolveFunctionArgument(expr, sourceFile);
		if (!returned) {
			return;
		}
		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			returned.getStart(sourceFile)
		);
		const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
		const code = returned.getText(sourceFile).slice(0, 100);
		const scope = this.resolveEDSScope(returned) ?? fallbackScope;
		const entry = this.addEDS(scope || 'unknown', {
			location,
			kind : 'wrap',
			code,
			scope,
			via  : viaLocation,
			// dive wraps returned functions through the same wrap machinery
			fn   : 'wrap',
		});
		// the returned function's own returns are wrapped in turn; `via`
		// chains to this nested entry's location
		const nestedCreates = new Set<string>();
		this.analyzeWrappedBody(returned, location, sourceFile, depth + 1, visited, nestedCreates, scope);
		if (nestedCreates.size > 0) {
			entry.createsTypes = Array.from(nestedCreates);
		}
	}

	/**
	 * Add an EDS usage to the collection
	 * Returns the stored entry (the existing one when this is a duplicate),
	 * so callers can enrich it after nested body analysis.
	 */
	private addEDS (typePath: string, info: EDSInfo): EDSInfo {
		if (!this.edsUsages.has(typePath)) {
			this.edsUsages.set(typePath, []);
		}

		const existing = this.edsUsages.get(typePath)!;
		const duplicate = existing.find(e => {
			return e.location === info.location &&
				e.kind === info.kind &&
				e.code === info.code;
		});

		if (duplicate) {
			return duplicate;
		}
		existing.push(info);
		return info;
	}

	/**
	 * Collect native flow patterns (instance usage after creation)
	 * Phase 1: property access, method calls, arguments, return, destructuring, etc.
	 */
	private collectFlow (node: ts.Node, sourceFile: ts.SourceFile): void {
		// Property read: user.name or user?.name
		if (ts.isPropertyAccessExpression(node)) {
			this.collectFlowPropertyAccess(node, sourceFile);
			return;
		}

		// Element access: user['name']
		if (ts.isElementAccessExpression(node)) {
			this.collectFlowElementAccess(node, sourceFile);
			return;
		}

		// Property write: user.name = value
		if (ts.isBinaryExpression(node) && node.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
			this.collectFlowAssignment(node, sourceFile);
			return;
		}

		// Method call: user.validate()  AND  argument passing: processUser(user)
		if (ts.isCallExpression(node) && node.expression) {
			this.collectFlowMethodCall(node, sourceFile);
			this.collectFlowArgumentPass(node, sourceFile);
			return;
		}

		// Destructure read: const { name } = user
		if (ts.isVariableDeclaration(node) && node.initializer) {
			this.collectFlowDestructure(node, sourceFile);
			return;
		}

		// Return instance: return user
		if (ts.isReturnStatement(node) && node.expression) {
			this.collectFlowReturn(node, sourceFile);
			return;
		}

		// Spread: { ...user }
		if (ts.isSpreadElement(node)) {
			this.collectFlowSpread(node, sourceFile);
			return;
		}
	}

	/**
	 * Collect property access flow (read or conditional)
	 */
	private collectFlowPropertyAccess (node: ts.PropertyAccessExpression, sourceFile: ts.SourceFile): void {
		const objectType = this.resolveExpressionType(node.expression);
		if (!objectType) { return; }

		const propName = node.name.text;
		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			node.getStart(sourceFile)
		);
		const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
		const code = node.getText(sourceFile).slice(0, 100);

		// Skip if this is a type constructor access (e.g., UserType.define)
		if (propName === 'define' || propName === 'lazy') { return; }

		this.addFlow(objectType, {
			location,
			kind         : 'propertyRead',
			code,
			propertyName : propName,
			targetType   : objectType
		});
	}

	/**
	 * Collect element access flow: user['name']
	 */
	private collectFlowElementAccess (node: ts.ElementAccessExpression, sourceFile: ts.SourceFile): void {
		const objectType = this.resolveExpressionType(node.expression);
		if (!objectType) { return; }

		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			node.getStart(sourceFile)
		);
		const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
		const code = node.getText(sourceFile).slice(0, 100);

		this.addFlow(objectType, {
			location,
			kind       : 'elementAccess',
			code,
			targetType : objectType
		});
	}

	/**
	 * Collect assignment flow: user.name = value or user = other
	 */
	private collectFlowAssignment (node: ts.BinaryExpression, sourceFile: ts.SourceFile): void {
		// Property write: user.name = value
		if (ts.isPropertyAccessExpression(node.left)) {
			const objectType = this.resolveExpressionType(node.left.expression);
			if (!objectType) { return; }

			const propName = node.left.name.text;
			const { line, character } = ts.getLineAndCharacterOfPosition(
				sourceFile,
				node.getStart(sourceFile)
			);
			const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
			const code = node.getText(sourceFile).slice(0, 100);

			this.addFlow(objectType, {
				location,
				kind         : 'propertyWrite',
				code,
				propertyName : propName,
				targetType   : objectType
			});
			return;
		}

		// Variable reassignment: user = other
		if (ts.isIdentifier(node.left)) {
			const varName = node.left.text;
			const mappedType = this.variableToTypeMap.get(varName);
			if (!mappedType) { return; }

			const { line, character } = ts.getLineAndCharacterOfPosition(
				sourceFile,
				node.getStart(sourceFile)
			);
			const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
			const code = node.getText(sourceFile).slice(0, 100);

			this.addFlow(mappedType, {
				location,
				kind       : 'reassignment',
				code,
				targetType : mappedType
			});
		}
	}

	/**
	 * Collect method call flow: user.validate()
	 */
	private collectFlowMethodCall (node: ts.CallExpression, sourceFile: ts.SourceFile): void {
		if (!ts.isPropertyAccessExpression(node.expression)) { return; }

		const objectType = this.resolveExpressionType(node.expression.expression);
		if (!objectType) { return; }

		const methodName = node.expression.name.text;
		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			node.getStart(sourceFile)
		);
		const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
		const code = node.getText(sourceFile).slice(0, 100);

		// Skip if this is a type constructor call (e.g., new UserType())
		if (methodName === 'define' || methodName === 'lazy') { return; }

		this.addFlow(objectType, {
			location,
			kind         : 'methodCall',
			code,
			propertyName : methodName,
			targetType   : objectType
		});
	}

	/**
	 * Collect argument passing flow: processUser(user)
	 */
	private collectFlowArgumentPass (node: ts.CallExpression, sourceFile: ts.SourceFile): void {
		for (let i = 0; i < node.arguments.length; i++) {
			const arg = node.arguments[ i ];
			const argType = this.resolveExpressionType(arg);
			if (!argType) { continue; }

			const funcName = this.getFunctionName(node.expression) || 'anonymous';
			const { line, character } = ts.getLineAndCharacterOfPosition(
				sourceFile,
				node.getStart(sourceFile)
			);
			const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
			const code = node.getText(sourceFile).slice(0, 100);

			this.addFlow(argType, {
				location,
				kind       : 'passAsArg',
				code,
				targetType : argType,
				context    : `arg ${i} to ${funcName}`
			});
		}
	}

	/**
	 * Collect destructuring flow: const { name } = user
	 */
	private collectFlowDestructure (node: ts.VariableDeclaration, sourceFile: ts.SourceFile): void {
		if (!ts.isObjectBindingPattern(node.name)) { return; }

		const sourceType = this.resolveExpressionType(node.initializer!);
		if (!sourceType) { return; }

		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			node.getStart(sourceFile)
		);
		const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
		const code = node.getText(sourceFile).slice(0, 100);

		// Extract destructured property names
		const props: string[] = [];
		for (const element of node.name.elements) {
			if (ts.isIdentifier(element.name)) {
				props.push(element.name.text);
			}
		}

		this.addFlow(sourceType, {
			location,
			kind       : 'destructureRead',
			code,
			targetType : sourceType,
			context    : props.join(', ')
		});
	}

	/**
	 * Collect return flow: return user
	 */
	private collectFlowReturn (node: ts.ReturnStatement, sourceFile: ts.SourceFile): void {
		const returnType = this.resolveExpressionType(node.expression!);
		if (!returnType) { return; }

		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			node.getStart(sourceFile)
		);
		const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
		const code = node.getText(sourceFile).slice(0, 100);

		this.addFlow(returnType, {
			location,
			kind       : 'return',
			code,
			targetType : returnType
		});
	}

	/**
	 * Collect spread flow: { ...user }
	 */
	private collectFlowSpread (node: ts.SpreadElement, sourceFile: ts.SourceFile): void {
		const spreadType = this.resolveExpressionType(node.expression);
		if (!spreadType) { return; }

		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			node.getStart(sourceFile)
		);
		const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
		const code = node.getText(sourceFile).slice(0, 100);

		this.addFlow(spreadType, {
			location,
			kind       : 'spread',
			code,
			targetType : spreadType
		});
	}

	/**
	 * Resolve type from an expression (identifier, property access, etc.)
	 */
	private resolveExpressionType (expr: ts.Expression): string | undefined {
		// Identifier: user
		if (ts.isIdentifier(expr)) {
			return this.variableToTypeMap.get(expr.text);
		}

		// Property access: user.name (return object type, not property type)
		if (ts.isPropertyAccessExpression(expr)) {
			return this.resolveExpressionType(expr.expression);
		}

		// Element access: user['name']
		if (ts.isElementAccessExpression(expr)) {
			return this.resolveExpressionType(expr.expression);
		}

		// This expression: this (if in a method, we can't resolve without more context)
		if (expr.kind === ts.SyntaxKind.ThisKeyword) {
			return undefined;
		}

		return undefined;
	}

	/**
	 * Add a flow usage to the collection
	 */
	private addFlow (typePath: string, info: FlowInfo): void {
		if (!this.flowUsages.has(typePath)) {
			this.flowUsages.set(typePath, []);
		}

		const existing = this.flowUsages.get(typePath)!;
		const isDuplicate = existing.some(e => {
			return e.location === info.location &&
				e.kind === info.kind &&
				e.code === info.code;
		});

		if (!isDuplicate) {
			existing.push(info);
		}
	}

	/**
			* Get type name from expression (identifier or property access)
			*/
	private getTypeNameFromExpression (expr: ts.Expression): string | undefined {
		if (ts.isIdentifier(expr)) {
			const name = expr.text;
			// Check if this identifier is a variable mapped to a type (e.g., from lookup)
			const mappedType = this.variableToTypeMap.get(name);
			if (mappedType) {
				return mappedType;
			}
			return name;
		}
		if (ts.isPropertyAccessExpression(expr)) {
			const chain = this.getPropertyChain(expr);
			return chain.join('.');
		}
		return undefined;
	}
	
	/**
			* Resolve full type path from property access
			*/
	private resolveTypePath (expr: ts.PropertyAccessExpression): string | undefined {
		const chain = this.getPropertyChain(expr);
		if (chain.length === 0) return undefined;
	
		// Check if this chain matches a known type
		const fullPath = chain.join('.');
		if (this.definitions.has(fullPath)) {
			return fullPath;
		}
	
		// Try just the property name
		const propName = chain[ chain.length - 1 ];
		for (const [ path ] of this.definitions) {
			if (path.endsWith(`.${propName}`) || path === propName) {
				return path;
			}
		}
	
		return fullPath;
	}
	
	/**
			 * Check if a name looks like a type (starts with uppercase)
			 */
	private isLikelyTypeName (name: string): boolean {
		return name[ 0 ] >= 'A' && name[ 0 ] <= 'Z';
	}
	
	/**
			 * Resolve a constructor parameter type, expanding inline object literals
			 * and type aliases where possible.
			 */
	private resolveConstructorParamType (typeNode: ts.TypeNode | undefined): string | undefined {
		if (!typeNode) return undefined;

		// Direct inline type literal: { prop: type }
		if (ts.isTypeLiteralNode(typeNode)) {
			const props: string[] = [];
			for (const member of typeNode.members) {
				if (ts.isPropertySignature(member) && ts.isIdentifier(member.name)) {
					const propName = member.name.text;
					const optional = member.questionToken ? '?' : '';
					const type = this.inferType(member.type);
					props.push(`${propName}${optional}: ${type}`);
				}
			}
			return `{ ${props.join('; ')} }`;
		}

		// Type reference: usage, UserData, etc. - resolve import-aware and
		// expand the referenced declaration where possible (F10)
		if (ts.isTypeReferenceNode(typeNode) && ts.isIdentifier(typeNode.typeName)) {
			const typeName = typeNode.typeName.text;
			const decl = this.resolveReferencedTypeDeclaration(typeName, this.currentReferencedTypeFile);
			if (decl) {
				const expanded = this.expandReferencedTypeDeclaration(decl);
				if (expanded) return expanded;
			}
			// mnemonica graph types keep their simple name — the generator
			// upgrades them to full-path instance type names. Resolution is
			// path-aware (hard-fail law): ambiguity between real graph types
			// records a fatal error instead of silently picking one.
			const graphResult = this.resolveGraphTypeName(typeName);
			if (graphResult.status === 'unique') {
				const simpleResult = typeName;
				return simpleResult;
			}
			if (graphResult.status === 'ambiguous') {
				this.recordGraphReferenceError(typeName, typeNode, graphResult);
				const unknownGraphResult = 'unknown';
				return unknownGraphResult;
			}
			// If not an object type alias, return the type name with args
			if (typeNode.typeArguments && typeNode.typeArguments.length > 0) {
				if (KNOWN_GLOBAL_TYPES.has(typeName)) {
					const args = typeNode.typeArguments.map(arg => this.inferType(arg));
					return `${typeName  }<${  args.join(', ')  }>`;
				}
				// generic reference to a non-global, non-graph type cannot be
				// emitted bare into the generated file
				this.recordPlainTypeReferenceSite(typeName, typeNode);
				const unknownGenericResult = 'unknown';
				return unknownGenericResult;
			}
			const fallbackResult = this.unresolvedTypeReferenceFallback(typeName, typeNode);
			return fallbackResult;
		}

		return undefined;
	}

	/**
			 * Extract constructor parameters from a class-like node.
			 */
	private extractClassConstructorParams (classLike: ts.ClassDeclaration | ts.ClassExpression):
		ConstructorParamInfo[] {
		const params: ConstructorParamInfo[] = [];

		for (const member of classLike.members) {
			if (!ts.isConstructorDeclaration(member)) {
				continue;
			}

			for (const param of member.parameters) {
				if (!param.name || !ts.isIdentifier(param.name)) continue;
				if (!param.type) continue;

				const paramName = param.name.text;
				const expandedType = this.resolveConstructorParamType(param.type) || this.inferType(param.type);

				params.push({
					name     : paramName,
					type     : expandedType,
					optional : !!param.questionToken || !!param.initializer
				});
			}
			// Only process first constructor
			break;
		}

		return params;
	}

	/**
			 * Extract constructor parameters from define() call
			 * This is used for TypeRegistry constructor signatures
			 * Preserves parameter names and expands object types to their structure
			 */
	private extractConstructorParams (call: ts.CallExpression): ConstructorParamInfo[] {
		const constructorExpr = this.extractConstructorExpression(call);
		if (!constructorExpr) {
			return [];
		}
		const result = this.extractConstructorParamsFromConstructor(constructorExpr);
		return result;
	}

	/**
			 * Extract constructor parameters from a constructor expression.
			 */
	private extractConstructorParamsFromConstructor (constructorExpr: ts.Expression): ConstructorParamInfo[] {
		const params: ConstructorParamInfo[] = [];
	
		// Handle function expression or arrow function
		if (ts.isFunctionExpression(constructorExpr) || ts.isArrowFunction(constructorExpr)) {
			// Look for constructor parameters (second param after `this`)
			// Patterns: function(this: Type, data: { ... }) or (this: Type, data: { ... }) =>
			for (let i = 0; i < constructorExpr.parameters.length; i++) {
				const param = constructorExpr.parameters[ i ];
				if (!param.type) continue;
	
				// Skip `this` parameter (first param)
				if (
					i === 0 &&
					param.name.kind === ts.SyntaxKind.Identifier &&
					(param.name as ts.Identifier).text === 'this'
				) {
					continue;
				}
	
				// Get parameter name and expand its type
				const paramName = ts.isIdentifier(param.name) ? param.name.text : 'arg';
				const expandedType = this.resolveConstructorParamType(param.type) || this.inferType(param.type);
					
				params.push({
					name     : paramName,
					type     : expandedType,
					optional : !!param.questionToken || !!param.initializer
				});
			}
		}
	
		// Handle class expression - check constructor method
		if (ts.isClassExpression(constructorExpr)) {
			const classParams = this.extractClassConstructorParams(constructorExpr);
			for (const param of classParams) {
				params.push(param);
			}
		}

		return params;
	}

	/**
	 * Collect framework instrumentation points. Purely syntactic: heritage
	 * clauses, decorator application sites, provider-token object literals
	 * and consumer.apply().forRoutes() wiring. The vocabulary comes from
	 * plugins; identifier text is matched as-is — no import resolution,
	 * the type checker stays unused.
	 */
	private collectInstrumentation (node: ts.Node, sourceFile: ts.SourceFile): void {
		if (ts.isClassDeclaration(node) && node.name) {
			this.collectInstrumentationClass(node, sourceFile);
		}
		if (ts.isDecorator(node)) {
			this.collectInstrumentationDecorator(node, sourceFile);
		}
		if (ts.isObjectLiteralExpression(node)) {
			this.collectInstrumentationProvider(node, sourceFile);
		}
		if (ts.isCallExpression(node)) {
			this.collectInstrumentationMiddleware(node, sourceFile);
		}
	}

	/**
	 * Record a named class declaration for instrumentation site resolution
	 * and detect heritage-based kinds (`implements <plugin interface>`)
	 */
	private collectInstrumentationClass (node: ts.ClassDeclaration, sourceFile: ts.SourceFile): void {
		if (!node.name) {
			return;
		}
		const className = node.name.text;
		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			node.name.getStart(sourceFile)
		);
		const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
		// First line of the declaration, like EDS `code` snippets
		const code = node.getText(sourceFile).split('\n')[ 0 ].slice(0, 100);

		let kind: InstrumentationKind | undefined;
		if (node.heritageClauses) {
			for (const clause of node.heritageClauses) {
				if (clause.token !== ts.SyntaxKind.ImplementsKeyword) {
					continue;
				}
				for (const type of clause.types) {
					if (!ts.isIdentifier(type.expression)) {
						continue;
					}
					const matched = this.instrumentationVocabulary.interfaces[ type.expression.text ];
					if (matched) {
						kind = matched;
					}
				}
			}
		}

		const decl: InstrumentationClassDecl = {
			location,
			code,
		};
		if (kind) {
			decl.kind = kind;
		}
		this.instrumentationClassDecls.set(className, decl);
	}

	/**
	 * Detect decorator application sites: plugin-listed decorators applied
	 * with class arguments on a class or one of its methods. One site per
	 * referenced class identifier.
	 */
	private collectInstrumentationDecorator (node: ts.Decorator, sourceFile: ts.SourceFile): void {
		const { expression } = node;
		if (!ts.isCallExpression(expression) || !ts.isIdentifier(expression.expression)) {
			return;
		}
		const kind = this.instrumentationVocabulary.useDecorators[ expression.expression.text ];
		if (!kind) {
			return;
		}

		// The decorator's parent is the decorated node: a controller class,
		// one of its methods, or one of its method parameters
		// (@Body(mvp.forType(Dto)) on a handler argument)
		const decorated = node.parent;
		let scope: InstrumentationScope;
		let targets: string[];
		if (ts.isClassDeclaration(decorated) && decorated.name) {
			scope = `controller:${decorated.name.text}`;
			targets = [ decorated.name.text ];
		} else if (
			ts.isMethodDeclaration(decorated) &&
			ts.isIdentifier(decorated.name) &&
			ts.isClassDeclaration(decorated.parent) &&
			decorated.parent.name
		) {
			const className = decorated.parent.name.text;
			scope = `method:${className}.${decorated.name.text}`;
			targets = [ className ];
		} else if (ts.isParameter(decorated)) {
			// Parameter decorators take the enclosing method's scope — the
			// attachment point is the handler, not the argument name; the
			// same method:Class.method form as method-level sites. Params of
			// constructors, functions, and unnameable hosts stay silent, the
			// same convention as other unresolvable decorator parents
			const host = decorated.parent;
			if (
				host &&
				ts.isMethodDeclaration(host) &&
				ts.isIdentifier(host.name) &&
				ts.isClassDeclaration(host.parent) &&
				host.parent.name
			) {
				const className = host.parent.name.text;
				scope = `method:${className}.${host.name.text}`;
				targets = [ className ];
			} else {
				return;
			}
		} else {
			return;
		}

		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			node.getStart(sourceFile)
		);
		const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
		const code = node.getText(sourceFile).slice(0, 100);

		for (const arg of expression.arguments) {
			// Class reference: @Register(Impl) or an inline instance:
			// @Register(new Impl({ ...options }))
			let className: string | undefined;
			// per-arg kind: factory-call args carry their own configured
			// kind, everything else takes the decorator's
			let argKind = kind;
			if (ts.isIdentifier(arg)) {
				className = arg.text;
			} else if (ts.isNewExpression(arg) && ts.isIdentifier(arg.expression)) {
				className = arg.expression.text;
			} else if (ts.isCallExpression(arg) && ts.isPropertyAccessExpression(arg.expression)) {
				// Pipe-factory shape: @UsePipes(mvp.forType(Dto)) — the
				// call's method name is plugin-listed, the target class sits
				// in the configured argument position (default 0)
				const factory = this.instrumentationVocabulary.decoratorArgFactories[ arg.expression.name.text ];
				if (factory) {
					const targetArg = arg.arguments[ factory.targetArg ?? 0 ];
					if (targetArg && ts.isIdentifier(targetArg)) {
						className = targetArg.text;
						argKind = factory.kind;
					}
				}
			}
			if (!className) {
				continue;
			}
			this.instrumentationSites.push({
				kind : argKind,
				className,
				location,
				code,
				scope,
				targets,
			});
		}
	}

	/**
	 * Detect global registrations: object literals shaped like
	 * `{ provide: <plugin-listed token>, useClass: X }`.
	 * useExisting/useFactory without a useClass identifier are not
	 * statically obvious — skipped rather than guessed.
	 */
	private collectInstrumentationProvider (node: ts.ObjectLiteralExpression, sourceFile: ts.SourceFile): void {
		let kind: InstrumentationKind | undefined;
		let useClassName: string | undefined;

		for (const prop of node.properties) {
			if (
				!ts.isPropertyAssignment(prop) ||
				!ts.isIdentifier(prop.name) ||
				!ts.isIdentifier(prop.initializer)
			) {
				continue;
			}
			if (prop.name.text === 'provide') {
				kind = this.instrumentationVocabulary.appTokens[ prop.initializer.text ];
			}
			if (prop.name.text === 'useClass') {
				useClassName = prop.initializer.text;
			}
		}

		if (!kind || !useClassName) {
			return;
		}

		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			node.getStart(sourceFile)
		);
		const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
		const code = node.getText(sourceFile).slice(0, 100);

		this.instrumentationSites.push({
			kind,
			className : useClassName,
			location,
			code,
			scope     : 'global',
			targets   : [],
		});
	}

	/**
	 * Detect middleware wiring: `consumer.apply(Mw1, Mw2).forRoutes(...)`
	 * inside a class's configure() method. Targets come from forRoutes
	 * arguments when statically readable (string routes or controller
	 * identifiers), else []. Shape-based, so a plugin must opt in via
	 * `middlewareWiring: true`.
	 */
	private collectInstrumentationMiddleware (node: ts.CallExpression, sourceFile: ts.SourceFile): void {
		if (!this.instrumentationVocabulary.middlewareWiring) {
			return;
		}
		if (
			!ts.isPropertyAccessExpression(node.expression) ||
			node.expression.name.text !== 'forRoutes'
		) {
			return;
		}
		const applyCall = node.expression.expression;
		if (
			!ts.isCallExpression(applyCall) ||
			!ts.isPropertyAccessExpression(applyCall.expression) ||
			applyCall.expression.name.text !== 'apply'
		) {
			return;
		}
		if (!this.isInsideConfigureMethod(node)) {
			return;
		}

		const targets: string[] = [];
		for (const arg of node.arguments) {
			if (ts.isIdentifier(arg) || ts.isStringLiteral(arg)) {
				targets.push(arg.text);
			}
		}

		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			applyCall.getStart(sourceFile)
		);
		const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
		const code = node.getText(sourceFile).slice(0, 100);

		for (const arg of applyCall.arguments) {
			if (!ts.isIdentifier(arg)) {
				continue;
			}
			this.instrumentationSites.push({
				kind      : 'middleware',
				className : arg.text,
				location,
				code,
				scope     : 'module',
				targets,
			});
		}
	}

	/**
	 * Walk up the parent chain looking for an enclosing configure() method
	 */
	private isInsideConfigureMethod (node: ts.Node): boolean {
		let current: ts.Node | undefined = node.parent;
		while (current) {
			if (
				ts.isMethodDeclaration(current) &&
				ts.isIdentifier(current.name) &&
				current.name.text === 'configure'
			) {
				return true;
			}
			current = current.parent;
		}
		return false;
	}
}
