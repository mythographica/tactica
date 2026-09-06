'use strict';

import * as nodePath from 'path';
import * as ts from 'typescript';
import {
	TypeNode, PropertyInfo, AnalyzeResult, AnalyzeError,
	DefinitionInfo, UsageInfo, ConstructorParamInfo,
	EDSInfo, FlowInfo, InstrumentationKind, InstrumentationPoint,
	InstrumentationScope
} from './types';
import { TypeGraphImpl } from './graph';
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
	// wrap call node -> location of the enclosing wrap site, so nested
	// wrap() calls inside a wrapped body carry the `via` link
	private nestedWrapVia = new Map<ts.Node, string>();
	// wrap call node -> its collected entry, so a lexically nested wrap
	// (visited BEFORE the outer wrap call, per source order) gets its
	// `via` back-patched when the outer body is analysed
	private wrapEntryByNode = new Map<ts.Node, EDSInfo>();
	private typeAliases = new Map<string, ts.TypeNode>();
	// Track variable assignments: variableName -> fullPath of the type it holds
	private variableToTypeMap = new Map<string, string>();
	// Track mnemonica module-object variables (e.g., import { mnemonica } from 'mnemonica'; const m = mnemonica)
	private moduleObjectVariables = new Set<string>();
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

	constructor (program?: ts.Program, plugins: TacticaPlugin[] = []) {
		// Store program for future use (currently unused but kept for extensibility)
		void program;
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
	}

	/**
	 * Analyze a source file for Mnemonica type definitions
	 */
	analyzeFile (sourceFile: ts.SourceFile): AnalyzeResult {
		this.errors = [];
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

		// Collect type aliases for resolving type references
		if (ts.isTypeAliasDeclaration(node) && ts.isIdentifier(node.name)) {
			this.typeAliases.set(node.name.text, node.type);
		}

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
		const marked = call as unknown as { __tactica_processed?: boolean };
		if (marked.__tactica_processed) {
			return true;
		}
		marked.__tactica_processed = true;
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

		// Extract properties from constructor function
		node.properties = this.extractProperties(call);

		// Extract constructor parameters for TypeRegistry signature
		node.constructorParams = this.extractConstructorParams(call);

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
		// For chained calls like const X = define('A').define('B'), we want to map X -> A (the root)
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

		// Extract properties from the constructor returned by the lazy getter
		node.properties = this.extractProperties(call);

		// Extract constructor parameters for TypeRegistry signature
		node.constructorParams = this.extractConstructorParams(call);

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
					// If this is a chained call (has parent), don't overwrite existing mapping
					// The first define in the chain sets the mapping to the root type
					if (parentNode && this.variableToTypeMap.has(varName)) {
						return;
					}
					this.variableToTypeMap.set(varName, fullPath);
				}
				return;
			}
			current = current.parent;
		}
	}
	
	/**
		* Track variable assignments from lookup() calls
		* e.g., const SentienceConstructor = lookup('Sentience') maps "SentienceConstructor" -> "Sentience"
		*/
	private trackLookupAssignment (call: ts.CallExpression, typePath: string): void {
		// Walk up the tree to find VariableDeclaration
		let current: ts.Node | undefined = call.parent;
		while (current) {
			if (ts.isVariableDeclaration(current)) {
				// Found: const X = lookup(...)
				if (ts.isIdentifier(current.name)) {
					const varName = current.name.text;
					this.variableToTypeMap.set(varName, typePath);
				}
				return;
			}
			current = current.parent;
		}
	}

	/**
		* Track variable assignments from new Type() calls
		* e.g., const user = new UserType() maps "user" -> "UserType"
		*/
	private trackNewAssignment (newExpr: ts.NewExpression, typePath: string): void {
		// Walk up the tree to find VariableDeclaration
		let current: ts.Node | undefined = newExpr.parent;
		while (current) {
			if (ts.isVariableDeclaration(current)) {
				// Found: const X = new Type(...)
				if (ts.isIdentifier(current.name)) {
					const varName = current.name.text;
					this.variableToTypeMap.set(varName, typePath);
				}
				return;
			}
			current = current.parent;
		}
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

		// Extract properties and constructor parameters from class members
		node.properties = this.extractClassProperties(classDecl);
		node.constructorParams = this.extractClassConstructorParams(classDecl);

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
				// Store simple parameter types like `decorateValue: string`
				const type = this.inferType(param.type);
				if (type !== 'unknown') {
					typeMap.set(paramName, type);
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
						if (!type) {
							type = this.inferTypeFromInitializer(expr.right, dataTypeMap);
						}
						// Don't overwrite a known type from a `this` annotation
						// with an unknown-bearing inference: an empty-array
						// initializer infers 'Array<unknown>', which must not
						// clobber an annotated 'Array<{ id: number }>' either
						const existing = properties.get(name);
						const typeHasUnknown = !type || type.includes('unknown');
						const existingIsKnown = existing ? !existing.type.includes('unknown') : false;
						if (existingIsKnown && typeHasUnknown) {
							// Keep the better type from explicit annotation
						} else {
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

					// Look up the type alias in our collected type aliases
					const aliasedType = this.typeAliases.get(typeName);
					if (aliasedType && ts.isTypeLiteralNode(aliasedType)) {
						// Extract properties from the type literal
						for (const member of aliasedType.members) {
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
			const typeName = ts.isIdentifier(typeRef.typeName)
				? typeRef.typeName.text
				: ts.isQualifiedName(typeRef.typeName)
					? this.getQualifiedNameText(typeRef.typeName)
					: 'unknown';

			// Check if this is a type alias we can resolve
			const aliasedType = this.typeAliases.get(typeName);
			if (aliasedType) {
				// Resolve the type alias
				return this.inferType(aliasedType);
			}

			// Handle InstanceType<typeof X> pattern -> convert to Parent_X
			if (typeName === 'InstanceType' && typeRef.typeArguments && typeRef.typeArguments.length === 1) {
				const [ arg ] = typeRef.typeArguments;
				if (arg.kind === ts.SyntaxKind.TypeQuery) {
					const typeQuery = arg as ts.TypeQueryNode;
					if (ts.isIdentifier(typeQuery.exprName)) {
						const queryTypeName = typeQuery.exprName.text;
						// Look up the type in the graph to get full path
						const matchedType = this.graph.findTypeByName(queryTypeName);
						if (matchedType) {
							// Convert full path with dots to underscores: Usages.UsageEntry -> Usages_UsageEntry
							return matchedType.fullPath.replace(/\./g, '_');
						}
						// Fallback: just use the type name if not found in graph
						return queryTypeName;
					}
				}
			}

			if (!typeRef.typeArguments || typeRef.typeArguments.length === 0) {
				// Check if this type exists in our graph - convert to full path format
				const matchedType = this.graph.findTypeByName(typeName);
				if (matchedType) {
					// Convert full path with dots to underscores: Usages.UsageEntry -> Usages_UsageEntry
					return matchedType.fullPath.replace(/\./g, '_');
				}
				return typeName;
			}

			// Build generic type arguments
			const typeArgs = typeRef.typeArguments.map(arg => this.inferType(arg));
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
			let objectType = this.inferType(indexed.objectType);
			const indexType = this.inferType(indexed.indexType);
			// If objectType is 'object', try to resolve the underlying type alias
			if (objectType === 'object' && ts.isTypeReferenceNode(indexed.objectType)) {
				const refName = ts.isIdentifier(indexed.objectType.typeName) ? indexed.objectType.typeName.text : '';
				const aliased = this.typeAliases.get(refName);
				if (aliased) {
					objectType = this.inferType(aliased);
				}
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
			// Handle typeof expressions like `typeof UsageEntry`
			const typeQuery = typeNode as ts.TypeQueryNode;
			if (ts.isIdentifier(typeQuery.exprName)) {
				return `typeof ${typeQuery.exprName.text}`;
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
		* Get full text from a qualified name (e.g., Namespace.Type)
		*/
	private getQualifiedNameText (qualifiedName: ts.QualifiedName): string {
		const parts: string[] = [];
		let current: ts.QualifiedName | ts.Identifier = qualifiedName;

		while (ts.isQualifiedName(current)) {
			parts.unshift(current.right.text);
			current = current.left;
		}
		parts.unshift(current.text);

		return parts.join('.');
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
					this.addUsage(typePath, {
						location : `${sourceFile.fileName}:${line + 1}:${character + 1}`,
						kind     : 'lookup',
						code     : node.getText(sourceFile).slice(0, 100),
					});
					// Track variable assignment from lookup for instantiation tracking
					this.trackLookupAssignment(node, typePath);
				}
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
			const info: EDSInfo = {
				location,
				kind       : 'wrap',
				code,
				targetType : targetType || undefined,
				scope,
				fn         : funcName,
			};
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
			// link to the site whose runtime wrapping caused it
			const via = this.nestedWrapVia.get(node);
			if (via) {
				info.via = via;
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
				this.analyzeWrappedBody(wrapped, location, sourceFile, 0, new Set(), createsTypes);
				if (createsTypes.size > 0) {
					info.createsTypes = Array.from(createsTypes);
				}
			}
			const stored = this.addEDS(targetType || scope || 'unknown', info);
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
			return undefined;
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
		createsTypes: Set<string>
	): void {
		if (depth > 5 || visited.has(fn) || !fn.body) {
			return;
		}
		visited.add(fn);

		// Arrow with expression body: implicit return
		if (ts.isArrowFunction(fn) && !ts.isBlock(fn.body)) {
			this.recordWrappedReturn(fn.body, viaLocation, sourceFile, depth, visited);
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
				this.recordWrappedReturn(node.expression, viaLocation, sourceFile, depth, visited);
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
					// otherwise leave the link for collectEDS to pick up
					const nestedEntry = this.wrapEntryByNode.get(node);
					if (nestedEntry) {
						nestedEntry.via = viaLocation;
					} else {
						this.nestedWrapVia.set(node, viaLocation);
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
	 */
	private recordWrappedReturn (
		expr: ts.Expression,
		viaLocation: string,
		sourceFile: ts.SourceFile,
		depth: number,
		visited: Set<ts.Node>
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
		const scope = this.resolveEDSScope(returned);
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
		this.analyzeWrappedBody(returned, location, sourceFile, depth + 1, visited, nestedCreates);
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

		// Type reference: usage, UserData, etc. - recursively expand
		if (ts.isTypeReferenceNode(typeNode) && ts.isIdentifier(typeNode.typeName)) {
			const typeName = typeNode.typeName.text;
			const aliasedType = this.typeAliases.get(typeName);
			if (aliasedType) {
				const expanded = this.resolveConstructorParamType(aliasedType);
				if (expanded) return expanded;
			}
			// If not an object type alias, return the type name with args
			if (typeNode.typeArguments && typeNode.typeArguments.length > 0) {
				const args = typeNode.typeArguments.map(arg => this.inferType(arg));
				return `${typeName  }<${  args.join(', ')  }>`;
			}
			return typeName;
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

		// The decorator's parent is the decorated node: a controller class
		// or one of its methods
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
			if (ts.isIdentifier(arg)) {
				className = arg.text;
			} else if (ts.isNewExpression(arg) && ts.isIdentifier(arg.expression)) {
				className = arg.expression.text;
			}
			if (!className) {
				continue;
			}
			this.instrumentationSites.push({
				kind,
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
