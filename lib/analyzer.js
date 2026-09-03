'use strict';
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.MnemonicaAnalyzer = void 0;
const ts = __importStar(require("typescript"));
const graph_1 = require("./graph");
/** NestJS interface identifier -> instrumentation kind (matched by simple name only) */
const INSTRUMENTATION_INTERFACE_KINDS = {
    NestInterceptor: 'interceptor',
    CanActivate: 'guard',
    PipeTransform: 'pipe',
    ExceptionFilter: 'filter',
    NestMiddleware: 'middleware',
};
/** @UseXxx decorator identifier -> instrumentation kind */
const USE_DECORATOR_KINDS = {
    UseGuards: 'guard',
    UseInterceptors: 'interceptor',
    UsePipes: 'pipe',
};
/** APP_* provider token identifier -> instrumentation kind */
const APP_TOKEN_KINDS = {
    APP_GUARD: 'guard',
    APP_PIPE: 'pipe',
    APP_INTERCEPTOR: 'interceptor',
    APP_FILTER: 'filter',
};
/**
 * AST Analyzer for finding Mnemonica define() and decorate() calls
 */
class MnemonicaAnalyzer {
    constructor(program) {
        this.errors = [];
        this.graph = new graph_1.TypeGraphImpl();
        this.definitions = new Map();
        this.usages = new Map();
        this.edsUsages = new Map();
        this.flowUsages = new Map();
        // Enclosing mnemonica scope for EDS keying: define()/lazy() call node
        // or @decorate()-ed class declaration -> fullPath of the type it owns.
        // Populated on the definitions pass; AST nodes persist across passes,
        // so entries stay valid after resetUsages().
        this.edsScopeByNode = new Map();
        // Same-file function bindings (`fileName#name` -> function node) for
        // resolving wrap(fn) arguments syntactically — the checker stays unused
        this.functionBindings = new Map();
        // wrap call node -> location of the enclosing wrap site, so nested
        // wrap() calls inside a wrapped body carry the `via` link
        this.nestedWrapVia = new Map();
        // wrap call node -> its collected entry, so a lexically nested wrap
        // (visited BEFORE the outer wrap call, per source order) gets its
        // `via` back-patched when the outer body is analysed
        this.wrapEntryByNode = new Map();
        this.typeAliases = new Map();
        // Track variable assignments: variableName -> fullPath of the type it holds
        this.variableToTypeMap = new Map();
        // Track mnemonica module-object variables (e.g., import { mnemonica } from 'mnemonica'; const m = mnemonica)
        this.moduleObjectVariables = new Set();
        // Track imported aliases of createTypesCollection (e.g., import { createTypesCollection as ctc })
        this.createTypesCollectionVariables = new Set();
        // Track custom collection variables: variableName -> collectionId
        this.collectionVariables = new Map();
        // Track custom collection metadata for Option B registry emission
        this.collectionInfo = new Map();
        this.collectionCounter = 0;
        // Instrumentation collection (syntactic only — no type checker):
        // every named class declaration by simple name, for resolving
        // registration sites to declaration locations (best effort, last wins)
        this.instrumentationClassDecls = new Map();
        // Registration sites: decorator applications, APP_* providers,
        // consumer.apply() middleware wiring
        this.instrumentationSites = [];
        // Store program for future use (currently unused but kept for extensibility)
        void program;
    }
    /**
     * Reset usage-related state for a fresh pass.
     * Call before the usage-collection pass to avoid duplicates from definition pass.
     */
    resetUsages() {
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
    analyzeFile(sourceFile) {
        this.errors = [];
        // Ensure parent nodes are set for AST traversal
        this.setParentNodesInSourceFile(sourceFile);
        this.visitNode(sourceFile, sourceFile);
        return {
            types: this.graph.getAllTypes(),
            errors: this.errors,
        };
    }
    /**
     * Analyze source code string
     */
    analyzeSource(sourceCode, fileName = 'temp.ts') {
        const sourceFile = ts.createSourceFile(fileName, sourceCode, ts.ScriptTarget.Latest, true);
        return this.analyzeFile(sourceFile);
    }
    /**
     * Get the type graph
     */
    getGraph() {
        return this.graph;
    }
    /**
     * Get collected definitions
     */
    getDefinitions() {
        return this.definitions;
    }
    /**
     * Get collected usages
     */
    getUsages() {
        return this.usages;
    }
    /**
     * Get collected EDS usages
     */
    getEDSUsages() {
        return this.edsUsages;
    }
    /**
     * Get collected flow usages
     */
    getFlowUsages() {
        return this.flowUsages;
    }
    /**
     * Get collected instrumentation points.
     * Registration sites referencing a class declared in the same project
     * resolve to the class declaration's location/code; external classes
     * (e.g., ValidationPipe from node_modules) keep the registration site.
     * Deduped by kind+className+location+scope with targets merged — a
     * class detected by heritage AND by a decorator site yields separate
     * entries with distinct scopes (see InstrumentationPoint in types.ts).
     */
    getInstrumentationPoints() {
        const points = new Map();
        const addPoint = (point) => {
            const key = `${point.kind}|${point.className}|${point.location}|${point.scope}`;
            const existing = points.get(key);
            if (existing) {
                const merged = new Set([...existing.targets, ...point.targets]);
                existing.targets = Array.from(merged);
                return;
            }
            points.set(key, point);
        };
        for (const site of this.instrumentationSites) {
            const decl = this.instrumentationClassDecls.get(site.className);
            const point = {
                kind: site.kind,
                className: site.className,
                location: decl ? decl.location : site.location,
                code: decl ? decl.code : site.code,
                scope: site.scope,
                targets: site.targets,
            };
            addPoint(point);
        }
        // Heritage-declared classes always emit a declaration point with
        // scope 'module' (attachment statically unknown); registration
        // sites above carry the narrower scopes as separate entries
        for (const [className, decl] of this.instrumentationClassDecls) {
            if (!decl.kind) {
                continue;
            }
            const point = {
                kind: decl.kind,
                className: className,
                location: decl.location,
                code: decl.code,
                scope: 'module',
                targets: [],
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
    addTopologicaType(fullPath, node) {
        // Skip if already exists
        if (this.graph.allTypes.has(fullPath)) {
            return;
        }
        // Add to graph so it can be found during usage collection
        if (node.parent) {
            // Add as child of parent
            this.graph.addChild(node.parent, node);
        }
        else {
            // Add as root
            this.graph.addRoot(node);
        }
        // Also add to definitions so it's recognized as a known type
        const definition = {
            name: node.name,
            location: `${node.sourceFile}:${node.line}:${node.column}`,
            kind: 'define',
            parent: node.parent ? node.parent.fullPath : null,
            strictChain: true,
            blockErrors: false
        };
        this.definitions.set(fullPath, definition);
    }
    /**
     * Set parent nodes in a source file to enable AST traversal up
     */
    setParentNodesInSourceFile(sourceFile) {
        const setParent = (node, parent) => {
            // TypeScript doesn't expose parent as writable, but we need it
            // eslint-disable-next-line @typescript-eslint/no-explicit-any
            node.parent = parent;
            ts.forEachChild(node, child => setParent(child, node));
        };
        setParent(sourceFile);
    }
    /**
     * Visit a node in the AST
     */
    visitNode(node, sourceFile, currentClass) {
        // Track mnemonica module-object aliases and custom collection variables
        // before processing define()/lookup() calls so source resolution works.
        this.trackImports(node);
        this.trackModuleObjectAliases(node);
        this.trackCollectionAliases(node, sourceFile);
        // Check for define() calls
        if (this.isDefineCall(node)) {
            this.processDefineCall(node, sourceFile);
        }
        // Check for lazy() calls
        if (this.isLazyCall(node)) {
            this.processLazyCall(node, sourceFile);
        }
        // Check for decorate() decorator
        if (this.isDecorateDecorator(node)) {
            this.processDecorateDecorator(node, sourceFile, currentClass);
        }
        // Check for type usages (new Type(), type annotations, etc.)
        this.collectUsage(node, sourceFile);
        // Check for EDS patterns (wrap, current, getFlow, etc.)
        this.collectEDS(node, sourceFile);
        // Check for native flow patterns (property access, method calls, etc.)
        this.collectFlow(node, sourceFile);
        // Check for NestJS instrumentation points (interceptors, guards,
        // pipes, filters, middleware) — syntactic only
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
        if (ts.isVariableDeclaration(node) &&
            ts.isIdentifier(node.name) &&
            node.initializer &&
            (ts.isArrowFunction(node.initializer) || ts.isFunctionExpression(node.initializer))) {
            const key = `${sourceFile.fileName}#${node.name.text}`;
            this.functionBindings.set(key, node.initializer);
        }
        // Track class declarations for decorator parent lookup
        if (ts.isClassDeclaration(node)) {
            // Visit children with this class as the current context
            ts.forEachChild(node, child => this.visitNode(child, sourceFile, node));
        }
        else {
            // Recursively visit children
            ts.forEachChild(node, child => this.visitNode(child, sourceFile, currentClass));
        }
    }
    /**
     * Track imports from 'mnemonica' so aliases of the module object and
     * createTypesCollection are recognized without relying on the type checker.
     */
    trackImports(node) {
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
    trackModuleObjectAliases(node) {
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
    trackCollectionAliases(node, sourceFile) {
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
            const registryInterfaceName = this.extractRegistryInterfaceName(initializer, sourceFile);
            this.collectionInfo.set(collectionId, {
                variableName: node.name.text,
                sourceFile: sourceFile.fileName,
                registryInterfaceName: registryInterfaceName
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
    extractRegistryInterfaceName(call, sourceFile) {
        const typeArgs = call.typeArguments;
        if (!typeArgs || typeArgs.length === 0) {
            return undefined;
        }
        const firstTypeArg = typeArgs[0];
        if (!ts.isTypeReferenceNode(firstTypeArg) || !ts.isIdentifier(firstTypeArg.typeName)) {
            return undefined;
        }
        const name = firstTypeArg.typeName.text;
        // Confirm the interface exists in the same source file.
        for (const statement of sourceFile.statements) {
            if (ts.isInterfaceDeclaration(statement) &&
                statement.name.text === name) {
                return name;
            }
        }
        return undefined;
    }
    /**
     * Get the registry interface name for a collection id.
     */
    getRegistryInterfaceName(collectionId) {
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
    isCreateTypesCollectionCall(node) {
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
        if (ts.isPropertyAccessExpression(expr) &&
            expr.name.text === 'createTypesCollection' &&
            ts.isIdentifier(expr.expression) &&
            this.moduleObjectVariables.has(expr.expression.text)) {
            return true;
        }
        return false;
    }
    /**
     * Generate a unique collection identifier.
     */
    nextCollectionId() {
        this.collectionCounter++;
        const result = `collection_${this.collectionCounter}`;
        return result;
    }
    /**
     * Check if a node is a define() call
     */
    isDefineCall(node) {
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
    isLazyCall(node) {
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
    extractConfigFromObjectLiteral(configArg) {
        const config = {};
        for (const prop of configArg.properties) {
            if (ts.isPropertyAssignment(prop) && ts.isIdentifier(prop.name)) {
                const propName = prop.name.text;
                if (propName === 'strictChain' && prop.initializer.kind === ts.SyntaxKind.TrueKeyword) {
                    config.strictChain = true;
                }
                else if (propName === 'strictChain' && prop.initializer.kind === ts.SyntaxKind.FalseKeyword) {
                    config.strictChain = false;
                }
                else if (propName === 'blockErrors' && prop.initializer.kind === ts.SyntaxKind.TrueKeyword) {
                    config.blockErrors = true;
                }
                else if (propName === 'blockErrors' && prop.initializer.kind === ts.SyntaxKind.FalseKeyword) {
                    config.blockErrors = false;
                }
            }
        }
        return config;
    }
    /**
        * Extract config options from define() call
        */
    extractConfig(call) {
        // Config is the third argument: define('Name', handler, config)
        const configArg = call.arguments[2];
        if (!configArg || !ts.isObjectLiteralExpression(configArg)) {
            return {};
        }
        const configResult = this.extractConfigFromObjectLiteral(configArg);
        return configResult;
    }
    /**
        * Check if a node is a @decorate() decorator
        */
    isDecorateDecorator(node) {
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
            if (ts.isPropertyAccessExpression(fnName) &&
                fnName.name.text === 'decorate' &&
                ts.isIdentifier(fnName.expression) &&
                this.collectionVariables.has(fnName.expression.text)) {
                return true;
            }
        }
        return false;
    }
    /**
     * Mark a call expression as processed and return whether it already was.
     */
    markProcessed(call) {
        const marked = call;
        if (marked.__tactica_processed) {
            return true;
        }
        marked.__tactica_processed = true;
        return false;
    }
    /**
     * Process a define() call
     */
    processDefineCall(call, sourceFile) {
        // Check if this exact call has already been processed (prevents duplicates from chained calls)
        if (this.markProcessed(call)) {
            return;
        }
        // Get the type name and source context from arguments
        const defineContext = this.extractDefineContext(call);
        // For chained calls like define('A').define('B'), we want the position of the .define('B') part
        // not the start of the entire expression
        let positionNode = call;
        // If this is a chained call, get the position of the property access expression
        // which is the .define part
        if (ts.isPropertyAccessExpression(call.expression)) {
            // The expression is the property access: (define('RootAsync', ...)).define
            // We want the position of just the .define part
            positionNode = call.expression.name; // This is the 'define' identifier
        }
        const startPos = positionNode.getStart(sourceFile);
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, startPos);
        if (!defineContext.typeName) {
            this.errors.push({
                message: 'Could not extract type name from define() call',
                file: sourceFile.fileName,
                line: line + 1,
                column: character + 1,
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
        const node = graph_1.TypeGraphImpl.createNode(typeName, parentNode, sourceFile.fileName, line + 1, character + 1, collectionId);
        node.registryInterfaceName = this.getRegistryInterfaceName(collectionId);
        // Extract properties from constructor function
        node.properties = this.extractProperties(call);
        // Extract constructor parameters for TypeRegistry signature
        node.constructorParams = this.extractConstructorParams(call);
        // Add to graph
        if (parentNode) {
            this.graph.addChild(parentNode, node);
        }
        else {
            this.graph.addRoot(node);
        }
        // Create definition info using the node's resolved fullPath
        const definition = {
            name: typeName,
            location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
            kind: 'define',
            parent: parentNode ? parentNode.fullPath : null,
            strictChain: config.strictChain ?? true,
            blockErrors: config.blockErrors ?? false,
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
    processLazyCall(call, sourceFile) {
        // Check if this exact call has already been processed (prevents duplicates from chained calls)
        if (this.markProcessed(call)) {
            return;
        }
        // Get the type name and source context from arguments
        const lazyContext = this.extractLazyContext(call, sourceFile);
        // For chained calls like define('A').lazy('B'), we want the position of the .lazy('B') part
        // not the start of the entire expression
        let positionNode = call;
        // If this is a chained call, get the position of the property access expression
        // which is the .lazy part
        if (ts.isPropertyAccessExpression(call.expression)) {
            // The expression is the property access: (define('RootAsync', ...)).lazy
            // We want the position of just the .lazy part
            positionNode = call.expression.name; // This is the 'lazy' identifier
        }
        const startPos = positionNode.getStart(sourceFile);
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, startPos);
        if (!lazyContext.typeName) {
            this.errors.push({
                message: 'Could not extract type name from lazy() call',
                file: sourceFile.fileName,
                line: line + 1,
                column: character + 1,
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
        const node = graph_1.TypeGraphImpl.createNode(typeName, parentNode, sourceFile.fileName, line + 1, character + 1, collectionId);
        node.registryInterfaceName = this.getRegistryInterfaceName(collectionId);
        // Extract properties from the constructor returned by the lazy getter
        node.properties = this.extractProperties(call);
        // Extract constructor parameters for TypeRegistry signature
        node.constructorParams = this.extractConstructorParams(call);
        // Add to graph
        if (parentNode) {
            this.graph.addChild(parentNode, node);
        }
        else {
            this.graph.addRoot(node);
        }
        // Create definition info using the node's resolved fullPath
        const definition = {
            name: typeName,
            location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
            kind: 'define',
            parent: parentNode ? parentNode.fullPath : null,
            strictChain: config.strictChain ?? true,
            blockErrors: config.blockErrors ?? false,
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
    extractLazyCallArgs(call) {
        const args = call.arguments;
        const isMethodCall = ts.isPropertyAccessExpression(call.expression);
        if (isMethodCall) {
            // Source is the object of the property access: Type.lazy(...)
            const source = call.expression.expression;
            if (args.length === 0) {
                return undefined;
            }
            const methodFirstArg = args[0];
            if (ts.isStringLiteral(methodFirstArg)) {
                // Type.lazy('Name', getter, config?)
                if (args.length < 2) {
                    return undefined;
                }
                return {
                    source,
                    name: methodFirstArg.text,
                    getter: args[1],
                    config: args[2],
                };
            }
            // Type.lazy(getter, config?)
            return {
                source,
                getter: methodFirstArg,
                config: args[1],
            };
        }
        // Free call: lazy(...)
        if (args.length === 0) {
            return undefined;
        }
        const firstArg = args[0];
        // Explicit-source form: lazy(source, 'Name', getter, config?)
        // or lazy(source, getter, config?)
        if (args.length >= 2 && ts.isIdentifier(firstArg)) {
            const secondArg = args[1];
            if (ts.isStringLiteral(secondArg)) {
                // lazy(source, 'Name', getter, config?)
                if (args.length < 3) {
                    return undefined;
                }
                return {
                    source: firstArg,
                    name: secondArg.text,
                    getter: args[2],
                    config: args[3],
                };
            }
            // lazy(source, getter, config?)
            return {
                source: firstArg,
                getter: secondArg,
                config: args[2],
            };
        }
        // Named root form: lazy('Name', getter, config?)
        if (ts.isStringLiteral(firstArg)) {
            if (args.length < 2) {
                return undefined;
            }
            return {
                name: firstArg.text,
                getter: args[1],
                config: args[2],
            };
        }
        // Unnamed root form: lazy(getter, config?)
        return {
            getter: firstArg,
            config: args[1],
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
    unwrapLazyGetter(getterExpr) {
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
    extractConstructorName(constructorExpr) {
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
    extractMnemonicaTypeName(call) {
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
    extractLazyContext(call, sourceFile) {
        const args = this.extractLazyCallArgs(call);
        if (!args) {
            return {};
        }
        let typeName = args.name;
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
                    parentType: sourceContext.parentType,
                    collectionId: sourceContext.collectionId,
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
                    parentType: sourceContext.parentType,
                    collectionId: sourceContext.collectionId,
                };
            }
            if (ts.isPropertyAccessExpression(obj)) {
                // Nested access: instance.Type.lazy - try to resolve
                const chain = this.getPropertyChain(obj);
                if (chain.length > 0) {
                    const parentNode = this.graph.findType(chain.join('.'));
                    return { typeName, parentType: parentNode };
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
                        return { typeName, parentType: parentNode, collectionId: parentNode?.collectionId };
                    }
                }
                if (this.isLazyCall(obj)) {
                    this.processLazyCall(obj, sourceFile);
                    const parentTypeName = this.extractMnemonicaTypeName(obj);
                    if (parentTypeName) {
                        const parentNode = this.findParentTypeByName(parentTypeName, expectedCollectionId);
                        return { typeName, parentType: parentNode, collectionId: parentNode?.collectionId };
                    }
                }
                // Builder lookup chain: App.lookup('User').lazy('Admin')
                if (this.isLookupCall(obj)) {
                    const lookedUpPath = this.resolveLookupPath(obj);
                    if (lookedUpPath) {
                        const parentNode = this.graph.findType(lookedUpPath);
                        if (parentNode) {
                            return { typeName, parentType: parentNode, collectionId: parentNode.collectionId };
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
    extractLazyConfig(call) {
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
    trackVariableAssignment(call, parentNode, fullPath) {
        // Check if this call is the right-hand side of a variable declaration
        // Walk up the tree to find VariableDeclaration
        let current = call.parent;
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
    trackLookupAssignment(call, typePath) {
        // Walk up the tree to find VariableDeclaration
        let current = call.parent;
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
    trackNewAssignment(newExpr, typePath) {
        // Walk up the tree to find VariableDeclaration
        let current = newExpr.parent;
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
    processDecorateDecorator(decorator, sourceFile, classDeclParam) {
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, decorator.getStart(sourceFile));
        // Get the class declaration - use the passed context if parent is not set
        const classDecl = decorator.parent || classDeclParam;
        if (!classDecl || !classDecl.name) {
            this.errors.push({
                message: 'Decorated class has no name',
                file: sourceFile.fileName,
                line: line + 1,
                column: character + 1,
            });
            return;
        }
        const typeName = classDecl.name.text;
        if (!typeName) {
            this.errors.push({
                message: 'Decorated class has no name',
                file: sourceFile.fileName,
                line: line + 1,
                column: character + 1,
            });
            return;
        }
        // Parse decorator arguments: @decorate(), @decorate(Parent),
        // @decorate({ ... }), @decorate(Parent, { ... }),
        // @MyCollection.decorate(), @MyCollection.decorate({ ... })
        let parentNode;
        let parentFullPath = null;
        let collectionId;
        let decoratorConfig = {};
        if (ts.isCallExpression(decorator.expression)) {
            const callExpr = decorator.expression;
            const callee = callExpr.expression;
            // Check for @MyCollection.decorate() where MyCollection is a custom collection.
            // The decorated class becomes a root type in that collection.
            if (ts.isPropertyAccessExpression(callee) &&
                callee.name.text === 'decorate' &&
                ts.isIdentifier(callee.expression) &&
                this.collectionVariables.has(callee.expression.text)) {
                collectionId = this.collectionVariables.get(callee.expression.text);
                if (callExpr.arguments.length === 1 && ts.isObjectLiteralExpression(callExpr.arguments[0])) {
                    decoratorConfig = this.extractConfigFromObjectLiteral(callExpr.arguments[0]);
                }
            }
            else {
                const args = callExpr.arguments;
                let parentArg;
                let configArg;
                for (const arg of args) {
                    if (ts.isIdentifier(arg)) {
                        if (parentArg) {
                            this.errors.push({
                                message: '@decorate() accepts only one parent reference',
                                file: sourceFile.fileName,
                                line: line + 1,
                                column: character + 1,
                            });
                        }
                        else {
                            parentArg = arg;
                        }
                    }
                    else if (ts.isObjectLiteralExpression(arg)) {
                        if (configArg) {
                            this.errors.push({
                                message: '@decorate() accepts only one config object',
                                file: sourceFile.fileName,
                                line: line + 1,
                                column: character + 1,
                            });
                        }
                        else {
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
        const definition = {
            name: typeName,
            location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
            kind: 'decorate',
            parent: parentFullPath,
            strictChain: decoratorConfig.strictChain ?? true,
            blockErrors: decoratorConfig.blockErrors ?? false,
        };
        this.definitions.set(fullPath, definition);
        this.edsScopeByNode.set(classDecl, fullPath);
        // Create type node
        const node = graph_1.TypeGraphImpl.createNode(typeName, parentNode, sourceFile.fileName, line + 1, character + 1, collectionId);
        node.registryInterfaceName = this.getRegistryInterfaceName(node.collectionId);
        // Extract properties and constructor parameters from class members
        node.properties = this.extractClassProperties(classDecl);
        node.constructorParams = this.extractClassConstructorParams(classDecl);
        // Add to graph
        if (parentNode) {
            this.graph.addChild(parentNode, node);
        }
        else {
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
    extractTypeName(call) {
        const args = call.arguments;
        if (args.length === 0) {
            return undefined;
        }
        const firstArg = args[0];
        // Explicit-source form: define(source, 'TypeName', handler)
        if (args.length >= 2 && ts.isIdentifier(firstArg) && ts.isStringLiteral(args[1])) {
            return args[1].text;
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
    extractDefineContext(call) {
        const typeName = this.extractTypeName(call);
        if (!typeName) {
            return {};
        }
        const { expression } = call;
        // Direct call: define('TypeName', ...) or define(source, 'TypeName', handler)
        if (ts.isIdentifier(expression) && expression.text === 'define') {
            // Explicit-source form: define(source, 'TypeName', handler)
            if (call.arguments.length >= 2 && ts.isIdentifier(call.arguments[0])) {
                const sourceName = call.arguments[0].text;
                const sourceContext = this.resolveDefineSource(sourceName);
                return {
                    typeName,
                    parentType: sourceContext.parentType,
                    collectionId: sourceContext.collectionId,
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
                    parentType: sourceContext.parentType,
                    collectionId: sourceContext.collectionId,
                };
            }
            if (ts.isPropertyAccessExpression(obj)) {
                // Nested access: instance.Type.define - try to resolve
                const chain = this.getPropertyChain(obj);
                if (chain.length > 0) {
                    const parentNode = this.graph.findType(chain.join('.'));
                    return { typeName, parentType: parentNode };
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
                        return { typeName, parentType: parentNode, collectionId: parentNode?.collectionId };
                    }
                }
                // Chained lazy call: lazy('A').define('B') or Type.lazy('A').define('B')
                if (this.isLazyCall(obj)) {
                    this.processLazyCall(obj, call.getSourceFile());
                    const parentTypeName = this.extractMnemonicaTypeName(obj);
                    if (parentTypeName) {
                        const parentNode = this.findParentTypeByName(parentTypeName, expectedCollectionId);
                        return { typeName, parentType: parentNode, collectionId: parentNode?.collectionId };
                    }
                }
                // Builder lookup chain: App.lookup('User').define('Admin')
                if (this.isLookupCall(obj)) {
                    const lookedUpPath = this.resolveLookupPath(obj);
                    if (lookedUpPath) {
                        const parentNode = this.graph.findType(lookedUpPath);
                        if (parentNode) {
                            return { typeName, parentType: parentNode, collectionId: parentNode.collectionId };
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
    prefixCollectionPath(path, collectionId) {
        return `${collectionId}::${path}`;
    }
    /**
     * Resolve a define() source identifier to either a parent type, a collection,
     * or the default (module object) collection.
     */
    resolveDefineSource(sourceName) {
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
        return { parentType: parentNode, collectionId: parentNode?.collectionId };
    }
    /**
     * Check if a call expression is a lookup() call.
     */
    isLookupCall(node) {
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
    resolveLookupPath(call) {
        const args = call.arguments;
        if (args.length === 0) {
            return undefined;
        }
        // Single-arg lookup: lookup('User') or App.lookup('User')
        if (args.length === 1) {
            const arg = args[0];
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
            const sourceArg = args[0];
            const pathArg = args[1];
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
    findParentTypeByName(name, collectionId) {
        const matchesCollection = (type) => {
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
    findParentTypeByIdentifier(name) {
        // First check variable mapping: const User = define('UserEntity', ...)
        const mappedFullPath = this.variableToTypeMap.get(name);
        if (mappedFullPath) {
            const mappedNode = this.graph.findType(mappedFullPath);
            if (mappedNode)
                return mappedNode;
        }
        const parentNode = this.findParentTypeByName(name);
        return parentNode;
    }
    /**
     * Get the leftmost identifier of a property-access chain.
     * For `App.define('User').define('Admin')` this returns the `App` identifier.
     */
    getRootIdentifier(expr) {
        let current = expr;
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
    getPropertyChain(expr) {
        const chain = [];
        let current = expr;
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
    extractConstructorExpression(call) {
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
        if (ts.isStringLiteral(args[0])) {
            return args[1];
        }
        // Legacy form: define(function Name() {}) or define(() => class Name {})
        return args[0];
    }
    /**
     * Extract properties from constructor function
     */
    extractProperties(call) {
        const constructorExpr = this.extractConstructorExpression(call);
        if (!constructorExpr) {
            return new Map();
        }
        const result = this.extractPropertiesFromConstructor(constructorExpr);
        return result;
    }
    /**
     * Extract properties from a constructor expression (function, arrow, or class).
     */
    extractPropertiesFromConstructor(constructorExpr) {
        const properties = new Map();
        // Build type map from data parameter (for this.x = data.x patterns)
        const dataTypeMap = this.buildDataTypeMap(constructorExpr);
        // Handle function expression
        if (ts.isFunctionExpression(constructorExpr) || ts.isArrowFunction(constructorExpr)) {
            const { body } = constructorExpr;
            // First, extract properties from `this` parameter type annotation
            // This handles patterns like: function(this: SomeType, data: SomeType) { }
            const thisParamProperties = this.extractThisParamProperties(constructorExpr);
            for (const [name, propInfo] of thisParamProperties) {
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
                            type: this.inferType(member.type),
                            optional: !!member.questionToken,
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
                        optional: false,
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
                        optional: false,
                        readonly: true,
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
    buildDataTypeMap(handlerArg) {
        const typeMap = new Map();
        if (!ts.isFunctionExpression(handlerArg) && !ts.isArrowFunction(handlerArg)) {
            return typeMap;
        }
        // Iterate over ALL parameters
        for (const param of handlerArg.parameters) {
            if (!param.name || !param.type)
                continue;
            // Get parameter name
            let paramName = '';
            if (ts.isIdentifier(param.name)) {
                paramName = param.name.text;
            }
            else {
                continue; // Skip destructured parameters for now
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
            }
            else {
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
    getPropertyAccessChain(expr) {
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
    extractPropertyFromStatement(expr, properties, dataTypeMap = new Map()) {
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
                        }
                        else {
                            properties.set(name, {
                                name,
                                type,
                                optional: false,
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
                if (args.length >= 2 && args[0].kind === ts.SyntaxKind.ThisKeyword) {
                    // Extract properties from the second argument
                    const propsArg = args[1];
                    if (ts.isObjectLiteralExpression(propsArg)) {
                        for (const prop of propsArg.properties) {
                            if (ts.isPropertyAssignment(prop) && ts.isIdentifier(prop.name)) {
                                const name = prop.name.text;
                                properties.set(name, {
                                    name,
                                    type: this.inferTypeFromInitializer(prop.initializer),
                                    optional: false,
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
    extractClassProperties(classDecl) {
        const properties = new Map();
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
                        optional: !!member.questionToken,
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
                    optional: false,
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
                    optional: false,
                    readonly: true,
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
    extractClassPropertyTypes(classDecl) {
        const propertyTypes = new Map();
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
    inferMethodType(method, classPropertyTypes) {
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
    extractThisParamProperties(handlerArg) {
        const properties = new Map();
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
                                    name: propName,
                                    type,
                                    optional: !!member.questionToken,
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
                                name: propName,
                                type,
                                optional: !!member.questionToken,
                            });
                        }
                    }
                }
                break; // Found the `this` parameter, no need to continue
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
    inferType(typeNode) {
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
                return `Array<${this.inferType(typeNode.elementType)}>`;
            case ts.SyntaxKind.TypeLiteral: {
                // Inline-expand type literals instead of collapsing to 'object'
                const typeLit = typeNode;
                const props = [];
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
                const { literal } = typeNode;
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
                const typeRef = typeNode;
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
                    const arg = typeRef.typeArguments[0];
                    if (arg.kind === ts.SyntaxKind.TypeQuery) {
                        const typeQuery = arg;
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
                const unionType = typeNode;
                const types = unionType.types.map(t => this.inferType(t));
                return types.join(' | ');
            }
            case ts.SyntaxKind.IntersectionType: {
                // Handle intersection types like TypeA & TypeB
                const intersectionType = typeNode;
                const types = intersectionType.types.map(t => this.inferType(t));
                return types.join(' & ');
            }
            case ts.SyntaxKind.TupleType: {
                // Handle tuple types like [string, number]
                const tupleType = typeNode;
                const elements = tupleType.elements.map(elem => this.inferType(elem));
                return `[${elements.join(', ')}]`;
            }
            case ts.SyntaxKind.OptionalType: {
                // Handle optional element in tuple: string?
                const optionalType = typeNode;
                return `${this.inferType(optionalType.type)}?`;
            }
            case ts.SyntaxKind.RestType: {
                // Handle rest element: ...T
                const restType = typeNode;
                return `...${this.inferType(restType.type)}`;
            }
            case ts.SyntaxKind.ParenthesizedType: {
                // Handle parenthesized types: (A | B)
                return this.inferType(typeNode.type);
            }
            case ts.SyntaxKind.IndexedAccessType: {
                // Handle indexed access: T[K]
                const indexed = typeNode;
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
                const typeOp = typeNode;
                const operator = ts.SyntaxKind[typeOp.operator];
                return `${operator} ${this.inferType(typeOp.type)}`;
            }
            case ts.SyntaxKind.TypeQuery: {
                // Handle typeof expressions like `typeof UsageEntry`
                const typeQuery = typeNode;
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
    inferReturnType(method, classPropertyTypes) {
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
    inferReturnTypeFromBody(body, classPropertyTypes) {
        const returnTypes = new Set();
        const visit = (node) => {
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
            return Array.from(returnTypes)[0];
        }
        return Array.from(returnTypes).join(' | ');
    }
    /**
        * Get full text from a qualified name (e.g., Namespace.Type)
        */
    getQualifiedNameText(qualifiedName) {
        const parts = [];
        let current = qualifiedName;
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
    inferTypeFromInitializer(initializer, dataTypeMap, classPropertyTypes) {
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
                const newExpr = initializer;
                if (ts.isIdentifier(newExpr.expression)) {
                    return newExpr.expression.text;
                }
                return 'object';
            }
            case ts.SyntaxKind.BinaryExpression: {
                // Handle arithmetic operations: a * b, a + b, a - b, a / b
                const binaryExpr = initializer;
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
                const propAccess = initializer;
                if (ts.isPropertyAccessExpression(propAccess.expression)) {
                    const outerProp = propAccess.expression;
                    // Check for this.map pattern
                    let innerName = '';
                    if (outerProp.expression.kind === ts.SyntaxKind.ThisKeyword) {
                        innerName = 'this';
                    }
                    else if (ts.isIdentifier(outerProp.expression)) {
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
                    const name = initializer.text;
                    const type = dataTypeMap.get(name);
                    if (type) {
                        return type;
                    }
                }
                return 'unknown';
            }
            case ts.SyntaxKind.CallExpression: {
                // Handle function calls like Date.now(), parseInt(), etc.
                const callExpr = initializer;
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
                        }
                        else if (ts.isIdentifier(outerProp.expression)) {
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
                                        mapValueType = match[1];
                                    }
                                }
                            }
                            if (methodName === 'has')
                                return 'boolean';
                            if (methodName === 'set')
                                return 'this';
                            if (methodName === 'get')
                                return mapValueType;
                            if (methodName === 'delete')
                                return 'boolean';
                            if (methodName === 'clear')
                                return 'void';
                            if (methodName === 'values')
                                return `IterableIterator<${mapValueType}>`;
                            if (methodName === 'keys')
                                return 'IterableIterator<string>';
                            if (methodName === 'entries')
                                return `IterableIterator<[string, ${mapValueType}]>`;
                        }
                    }
                    // Direct map.X() calls
                    if (objName === 'map' || objName === 'obj') {
                        if (methodName === 'has')
                            return 'boolean';
                        if (methodName === 'set')
                            return 'this';
                        if (methodName === 'get')
                            return 'unknown';
                        if (methodName === 'delete')
                            return 'boolean';
                        if (methodName === 'clear')
                            return 'void';
                        if (methodName === 'values')
                            return 'IterableIterator<unknown>';
                        if (methodName === 'keys')
                            return 'IterableIterator<string>';
                        if (methodName === 'entries')
                            return 'IterableIterator<[string, unknown]>';
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
    collectUsage(node, sourceFile) {
        // Check for new Type() instantiation
        if (ts.isNewExpression(node) && node.expression) {
            let typeName;
            if (ts.isPropertyAccessExpression(node.expression)) {
                typeName = this.resolveTypePath(node.expression);
            }
            else {
                typeName = this.getTypeNameFromExpression(node.expression);
            }
            if (typeName) {
                const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                this.addUsage(typeName, {
                    location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
                    kind: 'instantiation',
                    code: node.getText(sourceFile).slice(0, 100),
                });
                // Track variable assignment from new Type() for flow analysis
                this.trackNewAssignment(node, typeName);
                // Also record as flow event
                this.addFlow(typeName, {
                    location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
                    kind: 'instantiation',
                    code: node.getText(sourceFile).slice(0, 100),
                    context: 'new expression',
                });
            }
        }
        // Check for property access on instances (user.AdminType)
        if (ts.isPropertyAccessExpression(node)) {
            const propName = node.name.text;
            // Check if this looks like a type access pattern
            if (propName && this.isLikelyTypeName(propName)) {
                const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                // Try to resolve full path
                const fullPath = this.resolveTypePath(node);
                if (fullPath) {
                    this.addUsage(fullPath, {
                        location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
                        kind: 'propertyAccess',
                        code: node.getText(sourceFile).slice(0, 100),
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
                    const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                    this.addUsage(typePath, {
                        location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
                        kind: 'lookup',
                        code: node.getText(sourceFile).slice(0, 100),
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
    getFunctionName(expr) {
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
    addUsage(typePath, usage) {
        // Only track usages of mnemonica-defined types
        if (!this.definitions.has(typePath)) {
            return;
        }
        if (!this.usages.has(typePath)) {
            this.usages.set(typePath, []);
        }
        // Check for duplicates based on location, code, and kind
        const existingUsages = this.usages.get(typePath);
        const isDuplicate = existingUsages.some(existing => existing.location === usage.location &&
            existing.code === usage.code &&
            existing.kind === usage.kind);
        if (!isDuplicate) {
            existingUsages.push(usage);
        }
    }
    /**
     * Collect EDS (Execution Data Storage) usage information
     */
    collectEDS(node, sourceFile) {
        if (!ts.isCallExpression(node) || !node.expression) {
            return;
        }
        const funcName = this.getFunctionName(node.expression);
        if (!funcName) {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        // Enclosing mnemonica type path — wrap args are usually local
        // functions, so the owning define()/lazy() handler or decorated
        // class is what eds.json consumers (GraphBuilder) can join on.
        const scope = this.resolveEDSScope(node);
        // wrap(fn), wrapConstructorArg(fn, parent), upgradeConstructorArg(arg, inst), wrapInstanceMethods(obj)
        if (funcName === 'wrap' ||
            funcName === 'wrapConstructorArg' ||
            funcName === 'upgradeConstructorArg' ||
            funcName === 'wrapInstanceMethods') {
            const targetType = this.resolveEDSArgumentType(node.arguments[0]);
            const info = {
                location,
                kind: 'wrap',
                code,
                targetType: targetType || undefined,
                scope,
            };
            // A wrap() call nested inside another wrapped body carries the
            // link to the site whose runtime wrapping caused it
            const via = this.nestedWrapVia.get(node);
            if (via) {
                info.via = via;
            }
            // dive wraps returned functions too, and any mnemonica instance
            // created inside the wrapped body is a guaranteed path hit —
            // both are calculable AoT, so record them
            const wrapped = this.resolveFunctionArgument(node.arguments[0], sourceFile);
            if (wrapped) {
                const createsTypes = new Set();
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
                kind: 'contextConsume',
                code,
                scope,
            });
            return;
        }
        // attachHooks(collection) — from @mnemonica/nestjs, wires a
        // TypesCollection to dive's lifecycle tracing
        if (funcName === 'attachHooks' && node.arguments.length > 0) {
            const arg = node.arguments[0];
            if (ts.isArrayLiteralExpression(arg)) {
                for (const element of arg.elements) {
                    const targetType = this.resolveEDSArgumentType(element);
                    this.addEDS(targetType || scope || 'unknown', {
                        location,
                        kind: 'hookAttach',
                        code,
                        targetType: targetType || undefined,
                        scope,
                    });
                }
            }
            else {
                const targetType = this.resolveEDSArgumentType(arg);
                this.addEDS(targetType || scope || 'unknown', {
                    location,
                    kind: 'hookAttach',
                    code,
                    targetType: targetType || undefined,
                    scope,
                });
            }
            return;
        }
    }
    /**
     * Resolve type from EDS call argument (best effort)
     */
    resolveEDSArgumentType(arg) {
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
    resolveEDSScope(node) {
        let current = node.parent;
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
    resolveFunctionArgument(arg, sourceFile) {
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
    analyzeWrappedBody(fn, viaLocation, sourceFile, depth, visited, createsTypes) {
        if (depth > 5 || visited.has(fn) || !fn.body) {
            return;
        }
        visited.add(fn);
        // Arrow with expression body: implicit return
        if (ts.isArrowFunction(fn) && !ts.isBlock(fn.body)) {
            this.recordWrappedReturn(fn.body, viaLocation, sourceFile, depth, visited);
            return;
        }
        const walk = (node) => {
            if (node !== fn.body && (ts.isFunctionExpression(node) ||
                ts.isArrowFunction(node) ||
                ts.isFunctionDeclaration(node) ||
                ts.isMethodDeclaration(node))) {
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
                if (nestedName === 'wrap' ||
                    nestedName === 'wrapConstructorArg' ||
                    nestedName === 'upgradeConstructorArg' ||
                    nestedName === 'wrapInstanceMethods') {
                    // the nested call may already be collected (visited
                    // before this outer wrap site) — back-patch its entry,
                    // otherwise leave the link for collectEDS to pick up
                    const nestedEntry = this.wrapEntryByNode.get(node);
                    if (nestedEntry) {
                        nestedEntry.via = viaLocation;
                    }
                    else {
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
    recordWrappedReturn(expr, viaLocation, sourceFile, depth, visited) {
        const returned = this.resolveFunctionArgument(expr, sourceFile);
        if (!returned) {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, returned.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = returned.getText(sourceFile).slice(0, 100);
        const scope = this.resolveEDSScope(returned);
        const entry = this.addEDS(scope || 'unknown', {
            location,
            kind: 'wrap',
            code,
            scope,
            via: viaLocation,
        });
        // the returned function's own returns are wrapped in turn; `via`
        // chains to this nested entry's location
        const nestedCreates = new Set();
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
    addEDS(typePath, info) {
        if (!this.edsUsages.has(typePath)) {
            this.edsUsages.set(typePath, []);
        }
        const existing = this.edsUsages.get(typePath);
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
    collectFlow(node, sourceFile) {
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
    collectFlowPropertyAccess(node, sourceFile) {
        const objectType = this.resolveExpressionType(node.expression);
        if (!objectType) {
            return;
        }
        const propName = node.name.text;
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        // Skip if this is a type constructor access (e.g., UserType.define)
        if (propName === 'define' || propName === 'lazy') {
            return;
        }
        this.addFlow(objectType, {
            location,
            kind: 'propertyRead',
            code,
            propertyName: propName,
            targetType: objectType
        });
    }
    /**
     * Collect element access flow: user['name']
     */
    collectFlowElementAccess(node, sourceFile) {
        const objectType = this.resolveExpressionType(node.expression);
        if (!objectType) {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        this.addFlow(objectType, {
            location,
            kind: 'elementAccess',
            code,
            targetType: objectType
        });
    }
    /**
     * Collect assignment flow: user.name = value or user = other
     */
    collectFlowAssignment(node, sourceFile) {
        // Property write: user.name = value
        if (ts.isPropertyAccessExpression(node.left)) {
            const objectType = this.resolveExpressionType(node.left.expression);
            if (!objectType) {
                return;
            }
            const propName = node.left.name.text;
            const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
            const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
            const code = node.getText(sourceFile).slice(0, 100);
            this.addFlow(objectType, {
                location,
                kind: 'propertyWrite',
                code,
                propertyName: propName,
                targetType: objectType
            });
            return;
        }
        // Variable reassignment: user = other
        if (ts.isIdentifier(node.left)) {
            const varName = node.left.text;
            const mappedType = this.variableToTypeMap.get(varName);
            if (!mappedType) {
                return;
            }
            const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
            const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
            const code = node.getText(sourceFile).slice(0, 100);
            this.addFlow(mappedType, {
                location,
                kind: 'reassignment',
                code,
                targetType: mappedType
            });
        }
    }
    /**
     * Collect method call flow: user.validate()
     */
    collectFlowMethodCall(node, sourceFile) {
        if (!ts.isPropertyAccessExpression(node.expression)) {
            return;
        }
        const objectType = this.resolveExpressionType(node.expression.expression);
        if (!objectType) {
            return;
        }
        const methodName = node.expression.name.text;
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        // Skip if this is a type constructor call (e.g., new UserType())
        if (methodName === 'define' || methodName === 'lazy') {
            return;
        }
        this.addFlow(objectType, {
            location,
            kind: 'methodCall',
            code,
            propertyName: methodName,
            targetType: objectType
        });
    }
    /**
     * Collect argument passing flow: processUser(user)
     */
    collectFlowArgumentPass(node, sourceFile) {
        for (let i = 0; i < node.arguments.length; i++) {
            const arg = node.arguments[i];
            const argType = this.resolveExpressionType(arg);
            if (!argType) {
                continue;
            }
            const funcName = this.getFunctionName(node.expression) || 'anonymous';
            const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
            const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
            const code = node.getText(sourceFile).slice(0, 100);
            this.addFlow(argType, {
                location,
                kind: 'passAsArg',
                code,
                targetType: argType,
                context: `arg ${i} to ${funcName}`
            });
        }
    }
    /**
     * Collect destructuring flow: const { name } = user
     */
    collectFlowDestructure(node, sourceFile) {
        if (!ts.isObjectBindingPattern(node.name)) {
            return;
        }
        const sourceType = this.resolveExpressionType(node.initializer);
        if (!sourceType) {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        // Extract destructured property names
        const props = [];
        for (const element of node.name.elements) {
            if (ts.isIdentifier(element.name)) {
                props.push(element.name.text);
            }
        }
        this.addFlow(sourceType, {
            location,
            kind: 'destructureRead',
            code,
            targetType: sourceType,
            context: props.join(', ')
        });
    }
    /**
     * Collect return flow: return user
     */
    collectFlowReturn(node, sourceFile) {
        const returnType = this.resolveExpressionType(node.expression);
        if (!returnType) {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        this.addFlow(returnType, {
            location,
            kind: 'return',
            code,
            targetType: returnType
        });
    }
    /**
     * Collect spread flow: { ...user }
     */
    collectFlowSpread(node, sourceFile) {
        const spreadType = this.resolveExpressionType(node.expression);
        if (!spreadType) {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        this.addFlow(spreadType, {
            location,
            kind: 'spread',
            code,
            targetType: spreadType
        });
    }
    /**
     * Resolve type from an expression (identifier, property access, etc.)
     */
    resolveExpressionType(expr) {
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
    addFlow(typePath, info) {
        if (!this.flowUsages.has(typePath)) {
            this.flowUsages.set(typePath, []);
        }
        const existing = this.flowUsages.get(typePath);
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
    getTypeNameFromExpression(expr) {
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
    resolveTypePath(expr) {
        const chain = this.getPropertyChain(expr);
        if (chain.length === 0)
            return undefined;
        // Check if this chain matches a known type
        const fullPath = chain.join('.');
        if (this.definitions.has(fullPath)) {
            return fullPath;
        }
        // Try just the property name
        const propName = chain[chain.length - 1];
        for (const [path] of this.definitions) {
            if (path.endsWith(`.${propName}`) || path === propName) {
                return path;
            }
        }
        return fullPath;
    }
    /**
             * Check if a name looks like a type (starts with uppercase)
             */
    isLikelyTypeName(name) {
        return name[0] >= 'A' && name[0] <= 'Z';
    }
    /**
             * Resolve a constructor parameter type, expanding inline object literals
             * and type aliases where possible.
             */
    resolveConstructorParamType(typeNode) {
        if (!typeNode)
            return undefined;
        // Direct inline type literal: { prop: type }
        if (ts.isTypeLiteralNode(typeNode)) {
            const props = [];
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
                if (expanded)
                    return expanded;
            }
            // If not an object type alias, return the type name with args
            if (typeNode.typeArguments && typeNode.typeArguments.length > 0) {
                const args = typeNode.typeArguments.map(arg => this.inferType(arg));
                return `${typeName}<${args.join(', ')}>`;
            }
            return typeName;
        }
        return undefined;
    }
    /**
             * Extract constructor parameters from a class-like node.
             */
    extractClassConstructorParams(classLike) {
        const params = [];
        for (const member of classLike.members) {
            if (!ts.isConstructorDeclaration(member)) {
                continue;
            }
            for (const param of member.parameters) {
                if (!param.name || !ts.isIdentifier(param.name))
                    continue;
                if (!param.type)
                    continue;
                const paramName = param.name.text;
                const expandedType = this.resolveConstructorParamType(param.type) || this.inferType(param.type);
                params.push({
                    name: paramName,
                    type: expandedType,
                    optional: !!param.questionToken || !!param.initializer
                });
            }
            break; // Only process first constructor
        }
        return params;
    }
    /**
             * Extract constructor parameters from define() call
             * This is used for TypeRegistry constructor signatures
             * Preserves parameter names and expands object types to their structure
             */
    extractConstructorParams(call) {
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
    extractConstructorParamsFromConstructor(constructorExpr) {
        const params = [];
        // Handle function expression or arrow function
        if (ts.isFunctionExpression(constructorExpr) || ts.isArrowFunction(constructorExpr)) {
            // Look for constructor parameters (second param after `this`)
            // Patterns: function(this: Type, data: { ... }) or (this: Type, data: { ... }) =>
            for (let i = 0; i < constructorExpr.parameters.length; i++) {
                const param = constructorExpr.parameters[i];
                if (!param.type)
                    continue;
                // Skip `this` parameter (first param)
                if (i === 0 &&
                    param.name.kind === ts.SyntaxKind.Identifier &&
                    param.name.text === 'this') {
                    continue;
                }
                // Get parameter name and expand its type
                const paramName = ts.isIdentifier(param.name) ? param.name.text : 'arg';
                const expandedType = this.resolveConstructorParamType(param.type) || this.inferType(param.type);
                params.push({
                    name: paramName,
                    type: expandedType,
                    optional: !!param.questionToken || !!param.initializer
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
     * Collect NestJS instrumentation points (interceptors, guards, pipes,
     * filters, middleware). Purely syntactic: heritage clauses, decorator
     * application sites, APP_* provider object literals and
     * consumer.apply().forRoutes() wiring. No import resolution beyond the
     * identifier text — the type checker stays unused.
     */
    collectInstrumentation(node, sourceFile) {
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
     * and detect heritage-based kinds (`implements NestInterceptor`, etc.)
     */
    collectInstrumentationClass(node, sourceFile) {
        if (!node.name) {
            return;
        }
        const className = node.name.text;
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.name.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        // First line of the declaration, like EDS `code` snippets
        const code = node.getText(sourceFile).split('\n')[0].slice(0, 100);
        let kind;
        if (node.heritageClauses) {
            for (const clause of node.heritageClauses) {
                if (clause.token !== ts.SyntaxKind.ImplementsKeyword) {
                    continue;
                }
                for (const type of clause.types) {
                    if (!ts.isIdentifier(type.expression)) {
                        continue;
                    }
                    const matched = INSTRUMENTATION_INTERFACE_KINDS[type.expression.text];
                    if (matched) {
                        kind = matched;
                    }
                }
            }
        }
        const decl = {
            location,
            code,
        };
        if (kind) {
            decl.kind = kind;
        }
        this.instrumentationClassDecls.set(className, decl);
    }
    /**
     * Detect decorator application sites: @UseGuards(X), @UseInterceptors(X),
     * @UsePipes(X) on a controller class or one of its methods. One site per
     * referenced class identifier.
     */
    collectInstrumentationDecorator(node, sourceFile) {
        const { expression } = node;
        if (!ts.isCallExpression(expression) || !ts.isIdentifier(expression.expression)) {
            return;
        }
        const kind = USE_DECORATOR_KINDS[expression.expression.text];
        if (!kind) {
            return;
        }
        // The decorator's parent is the decorated node: a controller class
        // or one of its methods
        const decorated = node.parent;
        let scope;
        let targets;
        if (ts.isClassDeclaration(decorated) && decorated.name) {
            scope = `controller:${decorated.name.text}`;
            targets = [decorated.name.text];
        }
        else if (ts.isMethodDeclaration(decorated) &&
            ts.isIdentifier(decorated.name) &&
            ts.isClassDeclaration(decorated.parent) &&
            decorated.parent.name) {
            const className = decorated.parent.name.text;
            scope = `method:${className}.${decorated.name.text}`;
            targets = [className];
        }
        else {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        for (const arg of expression.arguments) {
            // Class reference: @UseGuards(AuthGuard) or an inline instance:
            // @UsePipes(new ValidationPipe({ transform: true }))
            let className;
            if (ts.isIdentifier(arg)) {
                className = arg.text;
            }
            else if (ts.isNewExpression(arg) && ts.isIdentifier(arg.expression)) {
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
     * `{ provide: APP_GUARD | APP_PIPE | APP_INTERCEPTOR | APP_FILTER, useClass: X }`.
     * useExisting/useFactory without a useClass identifier are not
     * statically obvious — skipped rather than guessed.
     */
    collectInstrumentationProvider(node, sourceFile) {
        let kind;
        let useClassName;
        for (const prop of node.properties) {
            if (!ts.isPropertyAssignment(prop) ||
                !ts.isIdentifier(prop.name) ||
                !ts.isIdentifier(prop.initializer)) {
                continue;
            }
            if (prop.name.text === 'provide') {
                kind = APP_TOKEN_KINDS[prop.initializer.text];
            }
            if (prop.name.text === 'useClass') {
                useClassName = prop.initializer.text;
            }
        }
        if (!kind || !useClassName) {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        this.instrumentationSites.push({
            kind,
            className: useClassName,
            location,
            code,
            scope: 'global',
            targets: [],
        });
    }
    /**
     * Detect middleware wiring: `consumer.apply(Mw1, Mw2).forRoutes(...)`
     * inside a class's configure() method. Targets come from forRoutes
     * arguments when statically readable (string routes or controller
     * identifiers), else [].
     */
    collectInstrumentationMiddleware(node, sourceFile) {
        if (!ts.isPropertyAccessExpression(node.expression) ||
            node.expression.name.text !== 'forRoutes') {
            return;
        }
        const applyCall = node.expression.expression;
        if (!ts.isCallExpression(applyCall) ||
            !ts.isPropertyAccessExpression(applyCall.expression) ||
            applyCall.expression.name.text !== 'apply') {
            return;
        }
        if (!this.isInsideConfigureMethod(node)) {
            return;
        }
        const targets = [];
        for (const arg of node.arguments) {
            if (ts.isIdentifier(arg) || ts.isStringLiteral(arg)) {
                targets.push(arg.text);
            }
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, applyCall.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        for (const arg of applyCall.arguments) {
            if (!ts.isIdentifier(arg)) {
                continue;
            }
            this.instrumentationSites.push({
                kind: 'middleware',
                className: arg.text,
                location,
                code,
                scope: 'module',
                targets,
            });
        }
    }
    /**
     * Walk up the parent chain looking for an enclosing configure() method
     */
    isInsideConfigureMethod(node) {
        let current = node.parent;
        while (current) {
            if (ts.isMethodDeclaration(current) &&
                ts.isIdentifier(current.name) &&
                current.name.text === 'configure') {
                return true;
            }
            current = current.parent;
        }
        return false;
    }
}
exports.MnemonicaAnalyzer = MnemonicaAnalyzer;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYW5hbHl6ZXIuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvYW5hbHl6ZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFFYiwrQ0FBaUM7QUFPakMsbUNBQXdDO0FBZ0N4Qyx3RkFBd0Y7QUFDeEYsTUFBTSwrQkFBK0IsR0FBd0M7SUFDNUUsZUFBZSxFQUFHLGFBQWE7SUFDL0IsV0FBVyxFQUFPLE9BQU87SUFDekIsYUFBYSxFQUFLLE1BQU07SUFDeEIsZUFBZSxFQUFHLFFBQVE7SUFDMUIsY0FBYyxFQUFJLFlBQVk7Q0FDOUIsQ0FBQztBQUVGLDJEQUEyRDtBQUMzRCxNQUFNLG1CQUFtQixHQUF3QztJQUNoRSxTQUFTLEVBQVMsT0FBTztJQUN6QixlQUFlLEVBQUcsYUFBYTtJQUMvQixRQUFRLEVBQVUsTUFBTTtDQUN4QixDQUFDO0FBRUYsOERBQThEO0FBQzlELE1BQU0sZUFBZSxHQUF3QztJQUM1RCxTQUFTLEVBQVMsT0FBTztJQUN6QixRQUFRLEVBQVUsTUFBTTtJQUN4QixlQUFlLEVBQUcsYUFBYTtJQUMvQixVQUFVLEVBQVEsUUFBUTtDQUMxQixDQUFDO0FBRUY7O0dBRUc7QUFDSCxNQUFhLGlCQUFpQjtJQTBDN0IsWUFBYSxPQUFvQjtRQXpDekIsV0FBTSxHQUFtQixFQUFFLENBQUM7UUFDNUIsVUFBSyxHQUFHLElBQUkscUJBQWEsRUFBRSxDQUFDO1FBQzVCLGdCQUFXLEdBQUcsSUFBSSxHQUFHLEVBQTBCLENBQUM7UUFDaEQsV0FBTSxHQUFHLElBQUksR0FBRyxFQUF1QixDQUFDO1FBQ3hDLGNBQVMsR0FBRyxJQUFJLEdBQUcsRUFBcUIsQ0FBQztRQUN6QyxlQUFVLEdBQUcsSUFBSSxHQUFHLEVBQXNCLENBQUM7UUFDbkQsc0VBQXNFO1FBQ3RFLHVFQUF1RTtRQUN2RSxzRUFBc0U7UUFDdEUsNkNBQTZDO1FBQ3JDLG1CQUFjLEdB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O0lBRUQ7O09BRUc7SUFDSyx1QkFBdUIsQ0FBRSxJQUFhO1FBQzdDLElBQUksT0FBTyxHQUF3QixJQUFJLENBQUMsTUFBTSxDQUFDO1FBQy9DLE9BQU8sT0FBTyxFQUFFLENBQUM7WUFDaEIsSUFDQyxFQUFFLENBQUMsbUJBQW1CLENBQUMsT0FBTyxDQUFDO2dCQUMvQixFQUFFLENBQUMsWUFBWSxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUM7Z0JBQzdCLE9BQU8sQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLFdBQVcsRUFDaEMsQ0FBQztnQkFDRixPQUFPLElBQUksQ0FBQztZQUNiLENBQUM7WUFDRCxPQUFPLEdBQUcsT0FBTyxDQUFDLE1BQU0sQ0FBQztRQUMxQixDQUFDO1FBQ0QsT0FBTyxLQUFLLENBQUM7SUFDZCxDQUFDO0NBQ0Q7QUEvcUhELDhDQStxSEMiLCJzb3VyY2VzQ29udGVudCI6WyIndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIHRzIGZyb20gJ3R5cGVzY3JpcHQnO1xuaW1wb3J0IHtcblx0VHlwZU5vZGUsIFByb3BlcnR5SW5mbywgQW5hbHl6ZVJlc3VsdCwgQW5hbHl6ZUVycm9yLFxuXHREZWZpbml0aW9uSW5mbywgVXNhZ2VJbmZvLCBDb25zdHJ1Y3RvclBhcmFtSW5mbyxcblx0RURTSW5mbywgRmxvd0luZm8sIEluc3RydW1lbnRhdGlvbktpbmQsIEluc3RydW1lbnRhdGlvblBvaW50LFxuXHRJbnN0cnVtZW50YXRpb25TY29wZVxufSBmcm9tICcuL3R5cGVzJztcbmltcG9ydCB7IFR5cGVHcmFwaEltcGwgfSBmcm9tICcuL2dyYXBoJztcblxuaW50ZXJmYWNlIENvbGxlY3Rpb25JbmZvIHtcblx0dmFyaWFibGVOYW1lOiBzdHJpbmc7XG5cdHNvdXJjZUZpbGU6IHN0cmluZztcblx0cmVnaXN0cnlJbnRlcmZhY2VOYW1lPzogc3RyaW5nO1xufVxuXG4vKipcbiAqIExvY2F0aW9uL2NvZGUgY2FwdHVyZWQgYXQgYSBjbGFzcyBkZWNsYXJhdGlvbiwgdXNlZCB0byByZXNvbHZlXG4gKiBpbnN0cnVtZW50YXRpb24gcmVnaXN0cmF0aW9uIHNpdGVzIHRvIHRoZSBkZWNsYXJlZCBjbGFzc1xuICovXG5pbnRlcmZhY2UgSW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNsIHtcblx0a2luZD86IEluc3RydW1lbnRhdGlvbktpbmQ7XG5cdGxvY2F0aW9uOiBzdHJpbmc7XG5cdGNvZGU6IHN0cmluZztcbn1cblxuLyoqXG4gKiBSYXcgcmVnaXN0cmF0aW9uIHNpdGUgKGRlY29yYXRvciwgQVBQXyogcHJvdmlkZXIsIGNvbnN1bWVyLmFwcGx5KS5cbiAqIExvY2F0aW9uL2NvZGUgYXJlIHRoZSBzaXRlJ3Mgb3duOyBnZXRJbnN0cnVtZW50YXRpb25Qb2ludHMoKSByZXdyaXRlc1xuICogdGhlbSB0byB0aGUgY2xhc3MgZGVjbGFyYXRpb24gd2hlbiB0aGUgY2xhc3MgaXMgZGVjbGFyZWQgaW4tcHJvamVjdC5cbiAqL1xuaW50ZXJmYWNlIEluc3RydW1lbnRhdGlvblNpdGUge1xuXHRraW5kOiBJbnN0cnVtZW50YXRpb25LaW5kO1xuXHRjbGFzc05hbWU6IHN0cmluZztcblx0bG9jYXRpb246IHN0cmluZztcblx0Y29kZTogc3RyaW5nO1xuXHRzY29wZTogSW5zdHJ1bWVudGF0aW9uU2NvcGU7XG5cdHRhcmdldHM6IHN0cmluZ1tdO1xufVxuXG4vKiogTmVzdEpTIGludGVyZmFjZSBpZGVudGlmaWVyIC0+IGluc3RydW1lbnRhdGlvbiBraW5kIChtYXRjaGVkIGJ5IHNpbXBsZSBuYW1lIG9ubHkpICovXG5jb25zdCBJTlNUUlVNRU5UQVRJT05fSU5URVJGQUNFX0tJTkRTOiBSZWNvcmQ8c3RyaW5nLCBJbnN0cnVtZW50YXRpb25LaW5kPiA9IHtcblx0TmVzdEludGVyY2VwdG9yIDogJ2ludGVyY2VwdG9yJyxcblx0Q2FuQWN0aXZhdGUgICAgIDogJ2d1YXJkJyxcblx0UGlwZVRyYW5zZm9ybSAgIDogJ3BpcGUnLFxuXHRFeGNlcHRpb25GaWx0ZXIgOiAnZmlsdGVyJyxcblx0TmVzdE1pZGRsZXdhcmUgIDogJ21pZGRsZXdhcmUnLFxufTtcblxuLyoqIEBVc2VYeHggZGVjb3JhdG9yIGlkZW50aWZpZXIgLT4gaW5zdHJ1bWVudGF0aW9uIGtpbmQgKi9cbmNvbnN0IFVTRV9ERUNPUkFUT1JfS0lORFM6IFJlY29yZDxzdHJpbmcsIEluc3RydW1lbnRhdGlvbktpbmQ+ID0ge1xuXHRVc2VHdWFyZHMgICAgICAgOiAnZ3VhcmQnLFxuXHRVc2VJbnRlcmNlcHRvcnMgOiAnaW50ZXJjZXB0b3InLFxuXHRVc2VQaXBlcyAgICAgICAgOiAncGlwZScsXG59O1xuXG4vKiogQVBQXyogcHJvdmlkZXIgdG9rZW4gaWRlbnRpZmllciAtPiBpbnN0cnVtZW50YXRpb24ga2luZCAqL1xuY29uc3QgQVBQX1RPS0VOX0tJTkRTOiBSZWNvcmQ8c3RyaW5nLCBJbnN0cnVtZW50YXRpb25LaW5kPiA9IHtcblx0QVBQX0dVQVJEICAgICAgIDogJ2d1YXJkJyxcblx0QVBQX1BJUEUgICAgICAgIDogJ3BpcGUnLFxuXHRBUFBfSU5URVJDRVBUT1IgOiAnaW50ZXJjZXB0b3InLFxuXHRBUFBfRklMVEVSICAgICAgOiAnZmlsdGVyJyxcbn07XG5cbi8qKlxuICogQVNUIEFuYWx5emVyIGZvciBmaW5kaW5nIE1uZW1vbmljYSBkZWZpbmUoKSBhbmQgZGVjb3JhdGUoKSBjYWxsc1xuICovXG5leHBvcnQgY2xhc3MgTW5lbW9uaWNhQW5hbHl6ZXIge1xuXHRwcml2YXRlIGVycm9yczogQW5hbHl6ZUVycm9yW10gPSBbXTtcblx0cHJpdmF0ZSBncmFwaCA9IG5ldyBUeXBlR3JhcGhJbXBsKCk7XG5cdHByaXZhdGUgZGVmaW5pdGlvbnMgPSBuZXcgTWFwPHN0cmluZywgRGVmaW5pdGlvbkluZm8+KCk7XG5cdHByaXZhdGUgdXNhZ2VzID0gbmV3IE1hcDxzdHJpbmcsIFVzYWdlSW5mb1tdPigpO1xuXHRwcml2YXRlIGVkc1VzYWdlcyA9IG5ldyBNYXA8c3RyaW5nLCBFRFNJbmZvW10+KCk7XG5cdHByaXZhdGUgZmxvd1VzYWdlcyA9IG5ldyBNYXA8c3RyaW5nLCBGbG93SW5mb1tdPigpO1xuXHQvLyBFbmNsb3NpbmcgbW5lbW9uaWNhIHNjb3BlIGZvciBFRFMga2V5aW5nOiBkZWZpbmUoKS9sYXp5KCkgY2FsbCBub2RlXG5cdC8vIG9yIEBkZWNvcmF0ZSgpLWVkIGNsYXNzIGRlY2xhcmF0aW9uIC0+IGZ1bGxQYXRoIG9mIHRoZSB0eXBlIGl0IG93bnMuXG5cdC8vIFBvcHVsYXRlZCBvbiB0aGUgZGVmaW5pdGlvbnMgcGFzczsgQVNUIG5vZGVzIHBlcnNpc3QgYWNyb3NzIHBhc3Nlcyxcblx0Ly8gc28gZW50cmllcyBzdGF5IHZhbGlkIGFmdGVyIHJlc2V0VXNhZ2VzKCkuXG5cdHByaXZhdGUgZWRzU2NvcGVCeU5vZGUgPSBuZXcgTWFwPHRzLk5vZGUsIHN0cmluZz4oKTtcblx0Ly8gU2FtZS1maWxlIGZ1bmN0aW9uIGJpbmRpbmdzIChgZmlsZU5hbWUjbmFtZWAgLT4gZnVuY3Rpb24gbm9kZSkgZm9yXG5cdC8vIHJlc29sdmluZyB3cmFwKGZuKSBhcmd1bWVudHMgc3ludGFjdGljYWxseSDigJQgdGhlIGNoZWNrZXIgc3RheXMgdW51c2VkXG5cdHByaXZhdGUgZnVuY3Rpb25CaW5kaW5ncyA9IG5ldyBNYXA8c3RyaW5nLCB0cy5GdW5jdGlvbkxpa2VEZWNsYXJhdGlvbj4oKTtcblx0Ly8gd3JhcCBjYWxsIG5vZGUgLT4gbG9jYXRpb24gb2YgdGhlIGVuY2xvc2luZyB3cmFwIHNpdGUsIHNvIG5lc3RlZFxuXHQvLyB3cmFwKCkgY2FsbHMgaW5zaWRlIGEgd3JhcHBlZCBib2R5IGNhcnJ5IHRoZSBgdmlhYCBsaW5rXG5cdHByaXZhdGUgbmVzdGVkV3JhcFZpYSA9IG5ldyBNYXA8dHMuTm9kZSwgc3RyaW5nPigpO1xuXHQvLyB3cmFwIGNhbGwgbm9kZSAtPiBpdHMgY29sbGVjdGVkIGVudHJ5LCBzbyBhIGxleGljYWxseSBuZXN0ZWQgd3JhcFxuXHQvLyAodmlzaXRlZCBCRUZPUkUgdGhlIG91dGVyIHdyYXAgY2FsbCwgcGVyIHNvdXJjZSBvcmRlcikgZ2V0cyBpdHNcblx0Ly8gYHZpYWAgYmFjay1wYXRjaGVkIHdoZW4gdGhlIG91dGVyIGJvZHkgaXMgYW5hbHlzZWRcblx0cHJpdmF0ZSB3cmFwRW50cnlCeU5vZGUgPSBuZXcgTWFwPHRzLk5vZGUsIEVEU0luZm8+KCk7XG5cdHByaXZhdGUgdHlwZUFsaWFzZXMgPSBuZXcgTWFwPHN0cmluZywgdHMuVHlwZU5vZGU+KCk7XG5cdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnRzOiB2YXJpYWJsZU5hbWUgLT4gZnVsbFBhdGggb2YgdGhlIHR5cGUgaXQgaG9sZHNcblx0cHJpdmF0ZSB2YXJpYWJsZVRvVHlwZU1hcCA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdC8vIFRyYWNrIG1uZW1vbmljYSBtb2R1bGUtb2JqZWN0IHZhcmlhYmxlcyAoZS5nLiwgaW1wb3J0IHsgbW5lbW9uaWNhIH0gZnJvbSAnbW5lbW9uaWNhJzsgY29uc3QgbSA9IG1uZW1vbmljYSlcblx0cHJpdmF0ZSBtb2R1bGVPYmplY3RWYXJpYWJsZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0Ly8gVHJhY2sgaW1wb3J0ZWQgYWxpYXNlcyBvZiBjcmVhdGVUeXBlc0NvbGxlY3Rpb24gKGUuZy4sIGltcG9ydCB7IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbiBhcyBjdGMgfSlcblx0cHJpdmF0ZSBjcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0Ly8gVHJhY2sgY3VzdG9tIGNvbGxlY3Rpb24gdmFyaWFibGVzOiB2YXJpYWJsZU5hbWUgLT4gY29sbGVjdGlvbklkXG5cdHByaXZhdGUgY29sbGVjdGlvblZhcmlhYmxlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdC8vIFRyYWNrIGN1c3RvbSBjb2xsZWN0aW9uIG1ldGFkYXRhIGZvciBPcHRpb24gQiByZWdpc3RyeSBlbWlzc2lvblxuXHRwcml2YXRlIGNvbGxlY3Rpb25JbmZvID0gbmV3IE1hcDxzdHJpbmcsIENvbGxlY3Rpb25JbmZvPigpO1xuXHRwcml2YXRlIGNvbGxlY3Rpb25Db3VudGVyID0gMDtcblx0Ly8gSW5zdHJ1bWVudGF0aW9uIGNvbGxlY3Rpb24gKHN5bnRhY3RpYyBvbmx5IOKAlCBubyB0eXBlIGNoZWNrZXIpOlxuXHQvLyBldmVyeSBuYW1lZCBjbGFzcyBkZWNsYXJhdGlvbiBieSBzaW1wbGUgbmFtZSwgZm9yIHJlc29sdmluZ1xuXHQvLyByZWdpc3RyYXRpb24gc2l0ZXMgdG8gZGVjbGFyYXRpb24gbG9jYXRpb25zIChiZXN0IGVmZm9ydCwgbGFzdCB3aW5zKVxuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMgPSBuZXcgTWFwPHN0cmluZywgSW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNsPigpO1xuXHQvLyBSZWdpc3RyYXRpb24gc2l0ZXM6IGRlY29yYXRvciBhcHBsaWNhdGlvbnMsIEFQUF8qIHByb3ZpZGVycyxcblx0Ly8gY29uc3VtZXIuYXBwbHkoKSBtaWRkbGV3YXJlIHdpcmluZ1xuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvblNpdGVzOiBJbnN0cnVtZW50YXRpb25TaXRlW10gPSBbXTtcblxuXHRjb25zdHJ1Y3RvciAocHJvZ3JhbT86IHRzLlByb2dyYW0pIHtcblx0XHQvLyBTdG9yZSBwcm9ncmFtIGZvciBmdXR1cmUgdXNlIChjdXJyZW50bHkgdW51c2VkIGJ1dCBrZXB0IGZvciBleHRlbnNpYmlsaXR5KVxuXHRcdHZvaWQgcHJvZ3JhbTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNldCB1c2FnZS1yZWxhdGVkIHN0YXRlIGZvciBhIGZyZXNoIHBhc3MuXG5cdCAqIENhbGwgYmVmb3JlIHRoZSB1c2FnZS1jb2xsZWN0aW9uIHBhc3MgdG8gYXZvaWQgZHVwbGljYXRlcyBmcm9tIGRlZmluaXRpb24gcGFzcy5cblx0ICovXG5cdHJlc2V0VXNhZ2VzICgpOiB2b2lkIHtcblx0XHR0aGlzLnVzYWdlcy5jbGVhcigpO1xuXHRcdHRoaXMuZWRzVXNhZ2VzLmNsZWFyKCk7XG5cdFx0dGhpcy5mbG93VXNhZ2VzLmNsZWFyKCk7XG5cdFx0dGhpcy52YXJpYWJsZVRvVHlwZU1hcC5jbGVhcigpO1xuXHRcdC8vIEVEUyBlbnRyeSByZWZlcmVuY2VzIGdvIHN0YWxlIHdpdGggZWRzVXNhZ2VzOyB2aWEgbGlua3MgYXJlXG5cdFx0Ly8gcmUtZGVyaXZlZCBvbiB0aGUgbmV4dCBwYXNzXG5cdFx0dGhpcy53cmFwRW50cnlCeU5vZGUuY2xlYXIoKTtcblx0XHR0aGlzLm5lc3RlZFdyYXBWaWEuY2xlYXIoKTtcblx0XHQvLyBOb3RlOiBtb2R1bGVPYmplY3RWYXJpYWJsZXMgYW5kIGNvbGxlY3Rpb25WYXJpYWJsZXMgaW50ZW50aW9uYWxseSBwZXJzaXN0XG5cdFx0Ly8gYWNyb3NzIGRlZmluaXRpb24gYW5kIHVzYWdlIHBhc3Nlcy5cblx0fVxuXG5cdC8qKlxuXHQgKiBBbmFseXplIGEgc291cmNlIGZpbGUgZm9yIE1uZW1vbmljYSB0eXBlIGRlZmluaXRpb25zXG5cdCAqL1xuXHRhbmFseXplRmlsZSAoc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IEFuYWx5emVSZXN1bHQge1xuXHRcdHRoaXMuZXJyb3JzID0gW107XG5cdFx0Ly8gRW5zdXJlIHBhcmVudCBub2RlcyBhcmUgc2V0IGZvciBBU1QgdHJhdmVyc2FsXG5cdFx0dGhpcy5zZXRQYXJlbnROb2Rlc0luU291cmNlRmlsZShzb3VyY2VGaWxlKTtcblx0XHR0aGlzLnZpc2l0Tm9kZShzb3VyY2VGaWxlLCBzb3VyY2VGaWxlKTtcblxuXHRcdHJldHVybiB7XG5cdFx0XHR0eXBlcyAgOiB0aGlzLmdyYXBoLmdldEFsbFR5cGVzKCksXG5cdFx0XHRlcnJvcnMgOiB0aGlzLmVycm9ycyxcblx0XHR9O1xuXHR9XG5cblx0LyoqXG5cdCAqIEFuYWx5emUgc291cmNlIGNvZGUgc3RyaW5nXG5cdCAqL1xuXHRhbmFseXplU291cmNlIChzb3VyY2VDb2RlOiBzdHJpbmcsIGZpbGVOYW1lID0gJ3RlbXAudHMnKTogQW5hbHl6ZVJlc3VsdCB7XG5cdFx0Y29uc3Qgc291cmNlRmlsZSA9IHRzLmNyZWF0ZVNvdXJjZUZpbGUoXG5cdFx0XHRmaWxlTmFtZSxcblx0XHRcdHNvdXJjZUNvZGUsXG5cdFx0XHR0cy5TY3JpcHRUYXJnZXQuTGF0ZXN0LFxuXHRcdFx0dHJ1ZVxuXHRcdCk7XG5cdFx0cmV0dXJuIHRoaXMuYW5hbHl6ZUZpbGUoc291cmNlRmlsZSk7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IHRoZSB0eXBlIGdyYXBoXG5cdCAqL1xuXHRnZXRHcmFwaCAoKTogVHlwZUdyYXBoSW1wbCB7XG5cdFx0cmV0dXJuIHRoaXMuZ3JhcGg7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBkZWZpbml0aW9uc1xuXHQgKi9cblx0Z2V0RGVmaW5pdGlvbnMgKCk6IE1hcDxzdHJpbmcsIERlZmluaXRpb25JbmZvPiB7XG5cdFx0cmV0dXJuIHRoaXMuZGVmaW5pdGlvbnM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCB1c2FnZXNcblx0ICovXG5cdGdldFVzYWdlcyAoKTogTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+IHtcblx0XHRyZXR1cm4gdGhpcy51c2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBFRFMgdXNhZ2VzXG5cdCAqL1xuXHRnZXRFRFNVc2FnZXMgKCk6IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4ge1xuXHRcdHJldHVybiB0aGlzLmVkc1VzYWdlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGZsb3cgdXNhZ2VzXG5cdCAqL1xuXHRnZXRGbG93VXNhZ2VzICgpOiBNYXA8c3RyaW5nLCBGbG93SW5mb1tdPiB7XG5cdFx0cmV0dXJuIHRoaXMuZmxvd1VzYWdlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGluc3RydW1lbnRhdGlvbiBwb2ludHMuXG5cdCAqIFJlZ2lzdHJhdGlvbiBzaXRlcyByZWZlcmVuY2luZyBhIGNsYXNzIGRlY2xhcmVkIGluIHRoZSBzYW1lIHByb2plY3Rcblx0ICogcmVzb2x2ZSB0byB0aGUgY2xhc3MgZGVjbGFyYXRpb24ncyBsb2NhdGlvbi9jb2RlOyBleHRlcm5hbCBjbGFzc2VzXG5cdCAqIChlLmcuLCBWYWxpZGF0aW9uUGlwZSBmcm9tIG5vZGVfbW9kdWxlcykga2VlcCB0aGUgcmVnaXN0cmF0aW9uIHNpdGUuXG5cdCAqIERlZHVwZWQgYnkga2luZCtjbGFzc05hbWUrbG9jYXRpb24rc2NvcGUgd2l0aCB0YXJnZXRzIG1lcmdlZCDigJQgYVxuXHQgKiBjbGFzcyBkZXRlY3RlZCBieSBoZXJpdGFnZSBBTkQgYnkgYSBkZWNvcmF0b3Igc2l0ZSB5aWVsZHMgc2VwYXJhdGVcblx0ICogZW50cmllcyB3aXRoIGRpc3RpbmN0IHNjb3BlcyAoc2VlIEluc3RydW1lbnRhdGlvblBvaW50IGluIHR5cGVzLnRzKS5cblx0ICovXG5cdGdldEluc3RydW1lbnRhdGlvblBvaW50cyAoKTogSW5zdHJ1bWVudGF0aW9uUG9pbnRbXSB7XG5cdFx0Y29uc3QgcG9pbnRzID0gbmV3IE1hcDxzdHJpbmcsIEluc3RydW1lbnRhdGlvblBvaW50PigpO1xuXG5cdFx0Y29uc3QgYWRkUG9pbnQgPSAocG9pbnQ6IEluc3RydW1lbnRhdGlvblBvaW50KTogdm9pZCA9PiB7XG5cdFx0XHRjb25zdCBrZXkgPSBgJHtwb2ludC5raW5kfXwke3BvaW50LmNsYXNzTmFtZX18JHtwb2ludC5sb2NhdGlvbn18JHtwb2ludC5zY29wZX1gO1xuXHRcdFx0Y29uc3QgZXhpc3RpbmcgPSBwb2ludHMuZ2V0KGtleSk7XG5cdFx0XHRpZiAoZXhpc3RpbmcpIHtcblx0XHRcdFx0Y29uc3QgbWVyZ2VkID0gbmV3IFNldChbIC4uLmV4aXN0aW5nLnRhcmdldHMsIC4uLnBvaW50LnRhcmdldHMgXSk7XG5cdFx0XHRcdGV4aXN0aW5nLnRhcmdldHMgPSBBcnJheS5mcm9tKG1lcmdlZCk7XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdHBvaW50cy5zZXQoa2V5LCBwb2ludCk7XG5cdFx0fTtcblxuXHRcdGZvciAoY29uc3Qgc2l0ZSBvZiB0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzKSB7XG5cdFx0XHRjb25zdCBkZWNsID0gdGhpcy5pbnN0cnVtZW50YXRpb25DbGFzc0RlY2xzLmdldChzaXRlLmNsYXNzTmFtZSk7XG5cdFx0XHRjb25zdCBwb2ludDogSW5zdHJ1bWVudGF0aW9uUG9pbnQgPSB7XG5cdFx0XHRcdGtpbmQgICAgICA6IHNpdGUua2luZCxcblx0XHRcdFx0Y2xhc3NOYW1lIDogc2l0ZS5jbGFzc05hbWUsXG5cdFx0XHRcdGxvY2F0aW9uICA6IGRlY2wgPyBkZWNsLmxvY2F0aW9uIDogc2l0ZS5sb2NhdGlvbixcblx0XHRcdFx0Y29kZSAgICAgIDogZGVjbCA/IGRlY2wuY29kZSA6IHNpdGUuY29kZSxcblx0XHRcdFx0c2NvcGUgICAgIDogc2l0ZS5zY29wZSxcblx0XHRcdFx0dGFyZ2V0cyAgIDogc2l0ZS50YXJnZXRzLFxuXHRcdFx0fTtcblx0XHRcdGFkZFBvaW50KHBvaW50KTtcblx0XHR9XG5cblx0XHQvLyBIZXJpdGFnZS1kZWNsYXJlZCBjbGFzc2VzIGFsd2F5cyBlbWl0IGEgZGVjbGFyYXRpb24gcG9pbnQgd2l0aFxuXHRcdC8vIHNjb3BlICdtb2R1bGUnIChhdHRhY2htZW50IHN0YXRpY2FsbHkgdW5rbm93bik7IHJlZ2lzdHJhdGlvblxuXHRcdC8vIHNpdGVzIGFib3ZlIGNhcnJ5IHRoZSBuYXJyb3dlciBzY29wZXMgYXMgc2VwYXJhdGUgZW50cmllc1xuXHRcdGZvciAoY29uc3QgWyBjbGFzc05hbWUsIGRlY2wgXSBvZiB0aGlzLmluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMpIHtcblx0XHRcdGlmICghZGVjbC5raW5kKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgcG9pbnQ6IEluc3RydW1lbnRhdGlvblBvaW50ID0ge1xuXHRcdFx0XHRraW5kICAgICAgOiBkZWNsLmtpbmQsXG5cdFx0XHRcdGNsYXNzTmFtZSA6IGNsYXNzTmFtZSxcblx0XHRcdFx0bG9jYXRpb24gIDogZGVjbC5sb2NhdGlvbixcblx0XHRcdFx0Y29kZSAgICAgIDogZGVjbC5jb2RlLFxuXHRcdFx0XHRzY29wZSAgICAgOiAnbW9kdWxlJyxcblx0XHRcdFx0dGFyZ2V0cyAgIDogW10sXG5cdFx0XHR9O1xuXHRcdFx0YWRkUG9pbnQocG9pbnQpO1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlc3VsdCA9IEFycmF5LmZyb20ocG9pbnRzLnZhbHVlcygpKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhIHRvcG9sb2dpY2EgdHlwZSB0byB0aGUgYW5hbHl6ZXIgZm9yIHVzYWdlIHRyYWNraW5nLlxuXHQgKiBUaGlzIGFsbG93cyB0aGUgYW5hbHl6ZXIgdG8gcmVjb2duaXplIHRvcG9sb2dpY2EgdHlwZXMgd2hlbiBjb2xsZWN0aW5nIHVzYWdlcy5cblx0ICovXG5cdGFkZFRvcG9sb2dpY2FUeXBlIChmdWxsUGF0aDogc3RyaW5nLCBub2RlOiBpbXBvcnQoJy4vdHlwZXMnKS5UeXBlTm9kZSk6IHZvaWQge1xuXHRcdC8vIFNraXAgaWYgYWxyZWFkeSBleGlzdHNcblx0XHRpZiAodGhpcy5ncmFwaC5hbGxUeXBlcy5oYXMoZnVsbFBhdGgpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoIHNvIGl0IGNhbiBiZSBmb3VuZCBkdXJpbmcgdXNhZ2UgY29sbGVjdGlvblxuXHRcdGlmIChub2RlLnBhcmVudCkge1xuXHRcdFx0Ly8gQWRkIGFzIGNoaWxkIG9mIHBhcmVudFxuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChub2RlLnBhcmVudCwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdC8vIEFkZCBhcyByb290XG5cdFx0XHR0aGlzLmdyYXBoLmFkZFJvb3Qobm9kZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQWxzbyBhZGQgdG8gZGVmaW5pdGlvbnMgc28gaXQncyByZWNvZ25pemVkIGFzIGEga25vd24gdHlwZVxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiBub2RlLm5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke25vZGUuc291cmNlRmlsZX06JHtub2RlLmxpbmV9OiR7bm9kZS5jb2x1bW59YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlZmluZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IG5vZGUucGFyZW50ID8gbm9kZS5wYXJlbnQuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBmYWxzZVxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQoZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFNldCBwYXJlbnQgbm9kZXMgaW4gYSBzb3VyY2UgZmlsZSB0byBlbmFibGUgQVNUIHRyYXZlcnNhbCB1cFxuXHQgKi9cblx0cHJpdmF0ZSBzZXRQYXJlbnROb2Rlc0luU291cmNlRmlsZSAoc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHNldFBhcmVudCA9IChub2RlOiB0cy5Ob2RlLCBwYXJlbnQ/OiB0cy5Ob2RlKSA9PiB7XG5cdFx0XHQvLyBUeXBlU2NyaXB0IGRvZXNuJ3QgZXhwb3NlIHBhcmVudCBhcyB3cml0YWJsZSwgYnV0IHdlIG5lZWQgaXRcblx0XHRcdC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBAdHlwZXNjcmlwdC1lc2xpbnQvbm8tZXhwbGljaXQtYW55XG5cdFx0XHQobm9kZSBhcyBhbnkpLnBhcmVudCA9IHBhcmVudDtcblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCBjaGlsZCA9PiBzZXRQYXJlbnQoY2hpbGQsIG5vZGUpKTtcblx0XHR9O1xuXHRcdHNldFBhcmVudChzb3VyY2VGaWxlKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBWaXNpdCBhIG5vZGUgaW4gdGhlIEFTVFxuXHQgKi9cblx0cHJpdmF0ZSB2aXNpdE5vZGUgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsIGN1cnJlbnRDbGFzcz86IHRzLkNsYXNzRGVjbGFyYXRpb24pOiB2b2lkIHtcblx0XHQvLyBUcmFjayBtbmVtb25pY2EgbW9kdWxlLW9iamVjdCBhbGlhc2VzIGFuZCBjdXN0b20gY29sbGVjdGlvbiB2YXJpYWJsZXNcblx0XHQvLyBiZWZvcmUgcHJvY2Vzc2luZyBkZWZpbmUoKS9sb29rdXAoKSBjYWxscyBzbyBzb3VyY2UgcmVzb2x1dGlvbiB3b3Jrcy5cblx0XHR0aGlzLnRyYWNrSW1wb3J0cyhub2RlKTtcblx0XHR0aGlzLnRyYWNrTW9kdWxlT2JqZWN0QWxpYXNlcyhub2RlKTtcblx0XHR0aGlzLnRyYWNrQ29sbGVjdGlvbkFsaWFzZXMobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgZGVmaW5lKCkgY2FsbHNcblx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0RlZmluZUNhbGwobm9kZSBhcyB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIGxhenkoKSBjYWxsc1xuXHRcdGlmICh0aGlzLmlzTGF6eUNhbGwobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0xhenlDYWxsKG5vZGUgYXMgdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGUpO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHRcdGlmICh0aGlzLmlzRGVjb3JhdGVEZWNvcmF0b3Iobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0RlY29yYXRlRGVjb3JhdG9yKG5vZGUgYXMgdHMuRGVjb3JhdG9yLCBzb3VyY2VGaWxlLCBjdXJyZW50Q2xhc3MpO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciB0eXBlIHVzYWdlcyAobmV3IFR5cGUoKSwgdHlwZSBhbm5vdGF0aW9ucywgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RVc2FnZShub2RlLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIENoZWNrIGZvciBFRFMgcGF0dGVybnMgKHdyYXAsIGN1cnJlbnQsIGdldEZsb3csIGV0Yy4pXG5cdFx0dGhpcy5jb2xsZWN0RURTKG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIG5hdGl2ZSBmbG93IHBhdHRlcm5zIChwcm9wZXJ0eSBhY2Nlc3MsIG1ldGhvZCBjYWxscywgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RGbG93KG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIE5lc3RKUyBpbnN0cnVtZW50YXRpb24gcG9pbnRzIChpbnRlcmNlcHRvcnMsIGd1YXJkcyxcblx0XHQvLyBwaXBlcywgZmlsdGVycywgbWlkZGxld2FyZSkg4oCUIHN5bnRhY3RpYyBvbmx5XG5cdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uKG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ29sbGVjdCB0eXBlIGFsaWFzZXMgZm9yIHJlc29sdmluZyB0eXBlIHJlZmVyZW5jZXNcblx0XHRpZiAodHMuaXNUeXBlQWxpYXNEZWNsYXJhdGlvbihub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSkge1xuXHRcdFx0dGhpcy50eXBlQWxpYXNlcy5zZXQobm9kZS5uYW1lLnRleHQsIG5vZGUudHlwZSk7XG5cdFx0fVxuXG5cdFx0Ly8gVHJhY2sgc2FtZS1maWxlIGZ1bmN0aW9uIGJpbmRpbmdzIHNvIEVEUyBjYW4gcmVzb2x2ZSB3cmFwKGZuKVxuXHRcdC8vIGFyZ3VtZW50cyB3aXRob3V0IHRoZSB0eXBlIGNoZWNrZXIgKGJlc3QgZWZmb3J0LCBsYXN0IHdpbnMpXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9IyR7bm9kZS5uYW1lLnRleHR9YDtcblx0XHRcdHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5zZXQoa2V5LCBub2RlKTtcblx0XHR9XG5cdFx0aWYgKFxuXHRcdFx0dHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSAmJlxuXHRcdFx0bm9kZS5pbml0aWFsaXplciAmJlxuXHRcdFx0KHRzLmlzQXJyb3dGdW5jdGlvbihub2RlLmluaXRpYWxpemVyKSB8fCB0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihub2RlLmluaXRpYWxpemVyKSlcblx0XHQpIHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9IyR7bm9kZS5uYW1lLnRleHR9YDtcblx0XHRcdHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5zZXQoa2V5LCBub2RlLmluaXRpYWxpemVyKTtcblx0XHR9XG5cblx0XHQvLyBUcmFjayBjbGFzcyBkZWNsYXJhdGlvbnMgZm9yIGRlY29yYXRvciBwYXJlbnQgbG9va3VwXG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0Ly8gVmlzaXQgY2hpbGRyZW4gd2l0aCB0aGlzIGNsYXNzIGFzIHRoZSBjdXJyZW50IGNvbnRleHRcblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCBjaGlsZCA9PiB0aGlzLnZpc2l0Tm9kZShjaGlsZCwgc291cmNlRmlsZSwgbm9kZSkpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHQvLyBSZWN1cnNpdmVseSB2aXNpdCBjaGlsZHJlblxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHRoaXMudmlzaXROb2RlKGNoaWxkLCBzb3VyY2VGaWxlLCBjdXJyZW50Q2xhc3MpKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgaW1wb3J0cyBmcm9tICdtbmVtb25pY2EnIHNvIGFsaWFzZXMgb2YgdGhlIG1vZHVsZSBvYmplY3QgYW5kXG5cdCAqIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbiBhcmUgcmVjb2duaXplZCB3aXRob3V0IHJlbHlpbmcgb24gdGhlIHR5cGUgY2hlY2tlci5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tJbXBvcnRzIChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc0ltcG9ydERlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBtb2R1bGVTcGVjaWZpZXIgfSA9IG5vZGU7XG5cdFx0aWYgKCF0cy5pc1N0cmluZ0xpdGVyYWwobW9kdWxlU3BlY2lmaWVyKSB8fCBtb2R1bGVTcGVjaWZpZXIudGV4dCAhPT0gJ21uZW1vbmljYScpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCBjbGF1c2UgPSBub2RlLmltcG9ydENsYXVzZTtcblx0XHRpZiAoIWNsYXVzZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGltcG9ydCB7IG1uZW1vbmljYSwgY3JlYXRlVHlwZXNDb2xsZWN0aW9uIH0gZnJvbSAnbW5lbW9uaWNhJ1xuXHRcdGlmIChjbGF1c2UubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVkSW1wb3J0cyhjbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBjbGF1c2UubmFtZWRCaW5kaW5ncy5lbGVtZW50cykge1xuXHRcdFx0XHRjb25zdCBsb2NhbE5hbWUgPSBlbGVtZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgaW1wb3J0ZWROYW1lID0gZWxlbWVudC5wcm9wZXJ0eU5hbWVcblx0XHRcdFx0XHQ/IGVsZW1lbnQucHJvcGVydHlOYW1lLnRleHRcblx0XHRcdFx0XHQ6IGxvY2FsTmFtZTtcblx0XHRcdFx0aWYgKGltcG9ydGVkTmFtZSA9PT0gJ21uZW1vbmljYScpIHtcblx0XHRcdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQobG9jYWxOYW1lKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoaW1wb3J0ZWROYW1lID09PSAnY3JlYXRlVHlwZXNDb2xsZWN0aW9uJykge1xuXHRcdFx0XHRcdHRoaXMuY3JlYXRlVHlwZXNDb2xsZWN0aW9uVmFyaWFibGVzLmFkZChsb2NhbE5hbWUpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0ICogYXMgbW5lbW9uaWNhIGZyb20gJ21uZW1vbmljYSdcblx0XHRpZiAoY2xhdXNlLm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lc3BhY2VJbXBvcnQoY2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQoY2xhdXNlLm5hbWVkQmluZGluZ3MubmFtZS50ZXh0KTtcblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgbW5lbW9uaWNhIGZyb20gJ21uZW1vbmljYScgKGRlZmF1bHQgaW1wb3J0KSDigJQgdHJlYXQgYXMgbW9kdWxlIG9iamVjdCB0b29cblx0XHRpZiAoY2xhdXNlLm5hbWUpIHtcblx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChjbGF1c2UubmFtZS50ZXh0KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgYWxpYXNlcyBvZiB0aGUgbW5lbW9uaWNhIG1vZHVsZSBvYmplY3QsIGUuZy46XG5cdCAqICAgY29uc3QgbSA9IG1uZW1vbmljYTtcblx0ICogICBjb25zdCBBcHAgPSBtO1xuXHQgKi9cblx0cHJpdmF0ZSB0cmFja01vZHVsZU9iamVjdEFsaWFzZXMgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSB8fCAhdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGluaXRpYWxpemVyIH0gPSBub2RlO1xuXHRcdGlmICghaW5pdGlhbGl6ZXIpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGluaXRpYWxpemVyKSAmJiB0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoaW5pdGlhbGl6ZXIudGV4dCkpIHtcblx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChub2RlLm5hbWUudGV4dCk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFRyYWNrIGN1c3RvbSBjb2xsZWN0aW9uIHZhcmlhYmxlcywgZS5nLjpcblx0ICogICBjb25zdCBNeUNvbGxlY3Rpb24gPSBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKTtcblx0ICogICBjb25zdCBPdGhlciA9IE15Q29sbGVjdGlvbjtcblx0ICpcblx0ICogQWxzbyBkZXRlY3RzIE9wdGlvbiBCIHVzZXItcHJvdmlkZWQgcmVnaXN0cnkgaW50ZXJmYWNlczpcblx0ICogICBleHBvcnQgaW50ZXJmYWNlIE15Q29sbGVjdGlvblJlZ2lzdHJ5IHt9XG5cdCAqICAgY29uc3QgTXlDb2xsZWN0aW9uID0gY3JlYXRlVHlwZXNDb2xsZWN0aW9uPE15Q29sbGVjdGlvblJlZ2lzdHJ5PigpO1xuXHQgKi9cblx0cHJpdmF0ZSB0cmFja0NvbGxlY3Rpb25BbGlhc2VzIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgfHwgIXRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBpbml0aWFsaXplciB9ID0gbm9kZTtcblx0XHRpZiAoIWluaXRpYWxpemVyKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRGlyZWN0IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIGNhbGxcblx0XHRpZiAodGhpcy5pc0NyZWF0ZVR5cGVzQ29sbGVjdGlvbkNhbGwoaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRjb25zdCBjb2xsZWN0aW9uSWQgPSB0aGlzLm5leHRDb2xsZWN0aW9uSWQoKTtcblx0XHRcdHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5zZXQobm9kZS5uYW1lLnRleHQsIGNvbGxlY3Rpb25JZCk7XG5cblx0XHRcdGNvbnN0IHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA9IHRoaXMuZXh0cmFjdFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZShcblx0XHRcdFx0aW5pdGlhbGl6ZXIgYXMgdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0XHRcdHNvdXJjZUZpbGVcblx0XHRcdCk7XG5cdFx0XHR0aGlzLmNvbGxlY3Rpb25JbmZvLnNldChjb2xsZWN0aW9uSWQsIHtcblx0XHRcdFx0dmFyaWFibGVOYW1lICAgICAgICAgIDogbm9kZS5uYW1lLnRleHQsXG5cdFx0XHRcdHNvdXJjZUZpbGUgICAgICAgICAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA6IHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZVxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gQWxpYXMgb2YgYW5vdGhlciBjb2xsZWN0aW9uIHZhcmlhYmxlXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihpbml0aWFsaXplcikpIHtcblx0XHRcdGNvbnN0IGV4aXN0aW5nID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChpbml0aWFsaXplci50ZXh0KTtcblx0XHRcdGlmIChleGlzdGluZykge1xuXHRcdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuc2V0KG5vZGUubmFtZS50ZXh0LCBleGlzdGluZyk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdGhlIHJlZ2lzdHJ5IGludGVyZmFjZSBuYW1lIGZyb20gY3JlYXRlVHlwZXNDb2xsZWN0aW9uPFJlZ2lzdHJ5PigpXG5cdCAqIHdoZW4gdGhlIGludGVyZmFjZSBpcyBkZWNsYXJlZCBpbiB0aGUgc2FtZSBzb3VyY2UgZmlsZS5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSAoXG5cdFx0Y2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZVxuXHQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IHR5cGVBcmdzID0gY2FsbC50eXBlQXJndW1lbnRzO1xuXHRcdGlmICghdHlwZUFyZ3MgfHwgdHlwZUFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZpcnN0VHlwZUFyZyA9IHR5cGVBcmdzWyAwIF07XG5cdFx0aWYgKCF0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKGZpcnN0VHlwZUFyZykgfHwgIXRzLmlzSWRlbnRpZmllcihmaXJzdFR5cGVBcmcudHlwZU5hbWUpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IG5hbWUgPSBmaXJzdFR5cGVBcmcudHlwZU5hbWUudGV4dDtcblxuXHRcdC8vIENvbmZpcm0gdGhlIGludGVyZmFjZSBleGlzdHMgaW4gdGhlIHNhbWUgc291cmNlIGZpbGUuXG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc291cmNlRmlsZS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzSW50ZXJmYWNlRGVjbGFyYXRpb24oc3RhdGVtZW50KSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIG5hbWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgdGhlIHJlZ2lzdHJ5IGludGVyZmFjZSBuYW1lIGZvciBhIGNvbGxlY3Rpb24gaWQuXG5cdCAqL1xuXHRwcml2YXRlIGdldFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSAoY29sbGVjdGlvbklkPzogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIWNvbGxlY3Rpb25JZCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0cmV0dXJuIHRoaXMuY29sbGVjdGlvbkluZm8uZ2V0KGNvbGxlY3Rpb25JZCk/LnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhbiBleHByZXNzaW9uIGlzIGEgY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgY2FsbC5cblx0ICogSGFuZGxlczpcblx0ICogICBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKVxuXHQgKiAgIGN0YygpIC8vIGFsaWFzZWQgaW1wb3J0XG5cdCAqICAgbW5lbW9uaWNhLmNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIC8vIG1vZHVsZSBvYmplY3QgbWV0aG9kXG5cdCAqICAgbS5jcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSAvLyBhbGlhc2VkIG1vZHVsZSBvYmplY3Rcblx0ICovXG5cdHByaXZhdGUgaXNDcmVhdGVUeXBlc0NvbGxlY3Rpb25DYWxsIChub2RlOiB0cy5Ob2RlKTogbm9kZSBpcyB0cy5DYWxsRXhwcmVzc2lvbiB7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXHRcdGNvbnN0IGV4cHIgPSBub2RlLmV4cHJlc3Npb247XG5cblx0XHQvLyBEaXJlY3QgY2FsbCBvciBhbGlhc2VkIGltcG9ydDogY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgLyBjdGMoKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLnRleHQgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nIHx8XG5cdFx0XHRcdHRoaXMuY3JlYXRlVHlwZXNDb2xsZWN0aW9uVmFyaWFibGVzLmhhcyhleHByLnRleHQpO1xuXHRcdH1cblxuXHRcdC8vIE1vZHVsZSBvYmplY3QgbWV0aG9kOiBtbmVtb25pY2EuY3JlYXRlVHlwZXNDb2xsZWN0aW9uKClcblx0XHRpZiAoXG5cdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSAmJlxuXHRcdFx0ZXhwci5uYW1lLnRleHQgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIoZXhwci5leHByZXNzaW9uKSAmJlxuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuaGFzKGV4cHIuZXhwcmVzc2lvbi50ZXh0KVxuXHRcdCkge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdlbmVyYXRlIGEgdW5pcXVlIGNvbGxlY3Rpb24gaWRlbnRpZmllci5cblx0ICovXG5cdHByaXZhdGUgbmV4dENvbGxlY3Rpb25JZCAoKTogc3RyaW5nIHtcblx0XHR0aGlzLmNvbGxlY3Rpb25Db3VudGVyKys7XG5cdFx0Y29uc3QgcmVzdWx0ID0gYGNvbGxlY3Rpb25fJHt0aGlzLmNvbGxlY3Rpb25Db3VudGVyfWA7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhIG5vZGUgaXMgYSBkZWZpbmUoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGlzRGVmaW5lQ2FsbCAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuQ2FsbEV4cHJlc3Npb24ge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBkaXJlY3QgY2FsbDogZGVmaW5lKCdUeXBlTmFtZScsIC4uLilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2RlZmluZScpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBtZXRob2QgY2FsbDogU29tZVR5cGUuZGVmaW5lKCdTdWJUeXBlJywgLi4uKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuIGV4cHJlc3Npb24ubmFtZT8udGV4dCA9PT0gJ2RlZmluZSc7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGEgbm9kZSBpcyBhIGxhenkoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGlzTGF6eUNhbGwgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkNhbGxFeHByZXNzaW9uIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IG5vZGU7XG5cblx0XHQvLyBDaGVjayBmb3IgZGlyZWN0IGNhbGw6IGxhenkoJ1R5cGVOYW1lJywgZ2V0dGVyLCAuLi4pXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLnRleHQgPT09ICdsYXp5Jykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIG1ldGhvZCBjYWxsOiBTb21lVHlwZS5sYXp5KCdTdWJUeXBlJywgZ2V0dGVyLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gZXhwcmVzc2lvbi5uYW1lPy50ZXh0ID09PSAnbGF6eSc7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IGNvbmZpZyBvcHRpb25zIGZyb20gYW4gb2JqZWN0IGxpdGVyYWxcblx0XHQqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbCAoY29uZmlnQXJnOiB0cy5PYmplY3RMaXRlcmFsRXhwcmVzc2lvbik6XG5cdFx0eyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9IHtcblx0XHRjb25zdCBjb25maWc6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSA9IHt9O1xuXG5cdFx0Zm9yIChjb25zdCBwcm9wIG9mIGNvbmZpZ0FyZy5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFzc2lnbm1lbnQocHJvcCkgJiYgdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBwcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0aWYgKHByb3BOYW1lID09PSAnc3RyaWN0Q2hhaW4nICYmIHByb3AuaW5pdGlhbGl6ZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5zdHJpY3RDaGFpbiA9IHRydWU7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdzdHJpY3RDaGFpbicgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5zdHJpY3RDaGFpbiA9IGZhbHNlO1xuXHRcdFx0XHR9IGVsc2UgaWYgKHByb3BOYW1lID09PSAnYmxvY2tFcnJvcnMnICYmIHByb3AuaW5pdGlhbGl6ZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5ibG9ja0Vycm9ycyA9IHRydWU7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdibG9ja0Vycm9ycycgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5ibG9ja0Vycm9ycyA9IGZhbHNlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGNvbmZpZztcblx0fVxuXG5cdC8qKlxuXHRcdCogRXh0cmFjdCBjb25maWcgb3B0aW9ucyBmcm9tIGRlZmluZSgpIGNhbGxcblx0XHQqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25maWcgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogeyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9IHtcblx0XHQvLyBDb25maWcgaXMgdGhlIHRoaXJkIGFyZ3VtZW50OiBkZWZpbmUoJ05hbWUnLCBoYW5kbGVyLCBjb25maWcpXG5cdFx0Y29uc3QgY29uZmlnQXJnID0gY2FsbC5hcmd1bWVudHNbIDIgXTtcblx0XHRpZiAoIWNvbmZpZ0FyZyB8fCAhdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihjb25maWdBcmcpKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgY29uZmlnUmVzdWx0ID0gdGhpcy5leHRyYWN0Q29uZmlnRnJvbU9iamVjdExpdGVyYWwoY29uZmlnQXJnKTtcblx0XHRyZXR1cm4gY29uZmlnUmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0KiBDaGVjayBpZiBhIG5vZGUgaXMgYSBAZGVjb3JhdGUoKSBkZWNvcmF0b3Jcblx0XHQqL1xuXHRwcml2YXRlIGlzRGVjb3JhdGVEZWNvcmF0b3IgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkRlY29yYXRvciB7XG5cdFx0aWYgKCF0cy5pc0RlY29yYXRvcihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBAZGVjb3JhdGVcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2RlY29yYXRlJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIEBkZWNvcmF0ZSgpIG9yIEBkZWNvcmF0ZShQYXJlbnRUeXBlKVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRjb25zdCBmbk5hbWUgPSBleHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGZuTmFtZSkgJiYgZm5OYW1lLnRleHQgPT09ICdkZWNvcmF0ZScpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cblx0XHRcdC8vIENoZWNrIGZvciBATXlDb2xsZWN0aW9uLmRlY29yYXRlKCkgd2hlcmUgTXlDb2xsZWN0aW9uIGlzIGEgY3VzdG9tIGNvbGxlY3Rpb25cblx0XHRcdGlmIChcblx0XHRcdFx0dHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZm5OYW1lKSAmJlxuXHRcdFx0XHRmbk5hbWUubmFtZS50ZXh0ID09PSAnZGVjb3JhdGUnICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihmbk5hbWUuZXhwcmVzc2lvbikgJiZcblx0XHRcdFx0dGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmhhcyhmbk5hbWUuZXhwcmVzc2lvbi50ZXh0KVxuXHRcdFx0KSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBNYXJrIGEgY2FsbCBleHByZXNzaW9uIGFzIHByb2Nlc3NlZCBhbmQgcmV0dXJuIHdoZXRoZXIgaXQgYWxyZWFkeSB3YXMuXG5cdCAqL1xuXHRwcml2YXRlIG1hcmtQcm9jZXNzZWQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgbWFya2VkID0gY2FsbCBhcyB1bmtub3duIGFzIHsgX190YWN0aWNhX3Byb2Nlc3NlZD86IGJvb2xlYW4gfTtcblx0XHRpZiAobWFya2VkLl9fdGFjdGljYV9wcm9jZXNzZWQpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHRtYXJrZWQuX190YWN0aWNhX3Byb2Nlc3NlZCA9IHRydWU7XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb2Nlc3MgYSBkZWZpbmUoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NEZWZpbmVDYWxsIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGlmIHRoaXMgZXhhY3QgY2FsbCBoYXMgYWxyZWFkeSBiZWVuIHByb2Nlc3NlZCAocHJldmVudHMgZHVwbGljYXRlcyBmcm9tIGNoYWluZWQgY2FsbHMpXG5cdFx0aWYgKHRoaXMubWFya1Byb2Nlc3NlZChjYWxsKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEdldCB0aGUgdHlwZSBuYW1lIGFuZCBzb3VyY2UgY29udGV4dCBmcm9tIGFyZ3VtZW50c1xuXHRcdGNvbnN0IGRlZmluZUNvbnRleHQgPSB0aGlzLmV4dHJhY3REZWZpbmVDb250ZXh0KGNhbGwpO1xuXG5cdFx0Ly8gRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBkZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKSwgd2Ugd2FudCB0aGUgcG9zaXRpb24gb2YgdGhlIC5kZWZpbmUoJ0InKSBwYXJ0XG5cdFx0Ly8gbm90IHRoZSBzdGFydCBvZiB0aGUgZW50aXJlIGV4cHJlc3Npb25cblx0XHRsZXQgcG9zaXRpb25Ob2RlOiB0cy5Ob2RlID0gY2FsbDtcblxuXHRcdC8vIElmIHRoaXMgaXMgYSBjaGFpbmVkIGNhbGwsIGdldCB0aGUgcG9zaXRpb24gb2YgdGhlIHByb3BlcnR5IGFjY2VzcyBleHByZXNzaW9uXG5cdFx0Ly8gd2hpY2ggaXMgdGhlIC5kZWZpbmUgcGFydFxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHQvLyBUaGUgZXhwcmVzc2lvbiBpcyB0aGUgcHJvcGVydHkgYWNjZXNzOiAoZGVmaW5lKCdSb290QXN5bmMnLCAuLi4pKS5kZWZpbmVcblx0XHRcdC8vIFdlIHdhbnQgdGhlIHBvc2l0aW9uIG9mIGp1c3QgdGhlIC5kZWZpbmUgcGFydFxuXHRcdFx0cG9zaXRpb25Ob2RlID0gY2FsbC5leHByZXNzaW9uLm5hbWU7IC8vIFRoaXMgaXMgdGhlICdkZWZpbmUnIGlkZW50aWZpZXJcblx0XHR9XG5cblx0XHRjb25zdCBzdGFydFBvcyA9IHBvc2l0aW9uTm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKTtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oc291cmNlRmlsZSwgc3RhcnRQb3MpO1xuXG5cdFx0aWYgKCFkZWZpbmVDb250ZXh0LnR5cGVOYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdDb3VsZCBub3QgZXh0cmFjdCB0eXBlIG5hbWUgZnJvbSBkZWZpbmUoKSBjYWxsJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IHR5cGVOYW1lIH0gPSBkZWZpbmVDb250ZXh0O1xuXG5cdFx0Ly8gRGV0ZXJtaW5lIHBhcmVudCB0eXBlIGFuZCBjb2xsZWN0aW9uIGJhc2VkIG9uIHRoZSBjYWxsIHNvdXJjZS5cblx0XHRjb25zdCBwYXJlbnROb2RlID0gZGVmaW5lQ29udGV4dC5wYXJlbnRUeXBlO1xuXHRcdGNvbnN0IHsgY29sbGVjdGlvbklkIH0gPSBkZWZpbmVDb250ZXh0O1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25maWcgb3B0aW9uc1xuXHRcdGNvbnN0IGNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZyhjYWxsKTtcblxuXHRcdC8vIENyZWF0ZSB0eXBlIG5vZGUgZmlyc3Qgc28gaXRzIGludGVybmFsIGZ1bGxQYXRoIChpbmNsdWRpbmcgYW55IGNvbGxlY3Rpb24gcHJlZml4KSBpcyByZXNvbHZlZC5cblx0XHRjb25zdCBub2RlID0gVHlwZUdyYXBoSW1wbC5jcmVhdGVOb2RlKFxuXHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRwYXJlbnROb2RlLFxuXHRcdFx0c291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdGxpbmUgKyAxLFxuXHRcdFx0Y2hhcmFjdGVyICsgMSxcblx0XHRcdGNvbGxlY3Rpb25JZFxuXHRcdCk7XG5cdFx0bm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWUgPSB0aGlzLmdldFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZShjb2xsZWN0aW9uSWQpO1xuXG5cdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gY29uc3RydWN0b3IgZnVuY3Rpb25cblx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzKGNhbGwpO1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZvciBUeXBlUmVnaXN0cnkgc2lnbmF0dXJlXG5cdFx0bm9kZS5jb25zdHJ1Y3RvclBhcmFtcyA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zKGNhbGwpO1xuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoXG5cdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkQ2hpbGQocGFyZW50Tm9kZSwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cblx0XHQvLyBDcmVhdGUgZGVmaW5pdGlvbiBpbmZvIHVzaW5nIHRoZSBub2RlJ3MgcmVzb2x2ZWQgZnVsbFBhdGhcblx0XHRjb25zdCBkZWZpbml0aW9uOiBEZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogcGFyZW50Tm9kZSA/IHBhcmVudE5vZGUuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiBjb25maWcuc3RyaWN0Q2hhaW4gPz8gdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogY29uZmlnLmJsb2NrRXJyb3JzID8/IGZhbHNlLFxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQobm9kZS5mdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdFx0dGhpcy5lZHNTY29wZUJ5Tm9kZS5zZXQoY2FsbCwgbm9kZS5mdWxsUGF0aCk7XG5cblx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50OiBjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKSAtPiBtYXAgXCJVc2VyXCIgdG8gXCJVc2VyRW50aXR5XCJcblx0XHQvLyBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGNvbnN0IFggPSBkZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKSwgd2Ugd2FudCB0byBtYXAgWCAtPiBBICh0aGUgcm9vdClcblx0XHR0aGlzLnRyYWNrVmFyaWFibGVBc3NpZ25tZW50KGNhbGwsIHBhcmVudE5vZGUsIG5vZGUuZnVsbFBhdGgpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb2Nlc3MgYSBsYXp5KCkgY2FsbFxuXHQgKi9cblx0cHJpdmF0ZSBwcm9jZXNzTGF6eUNhbGwgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBleGFjdCBjYWxsIGhhcyBhbHJlYWR5IGJlZW4gcHJvY2Vzc2VkIChwcmV2ZW50cyBkdXBsaWNhdGVzIGZyb20gY2hhaW5lZCBjYWxscylcblx0XHRpZiAodGhpcy5tYXJrUHJvY2Vzc2VkKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gR2V0IHRoZSB0eXBlIG5hbWUgYW5kIHNvdXJjZSBjb250ZXh0IGZyb20gYXJndW1lbnRzXG5cdFx0Y29uc3QgbGF6eUNvbnRleHQgPSB0aGlzLmV4dHJhY3RMYXp5Q29udGV4dChjYWxsLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIEZvciBjaGFpbmVkIGNhbGxzIGxpa2UgZGVmaW5lKCdBJykubGF6eSgnQicpLCB3ZSB3YW50IHRoZSBwb3NpdGlvbiBvZiB0aGUgLmxhenkoJ0InKSBwYXJ0XG5cdFx0Ly8gbm90IHRoZSBzdGFydCBvZiB0aGUgZW50aXJlIGV4cHJlc3Npb25cblx0XHRsZXQgcG9zaXRpb25Ob2RlOiB0cy5Ob2RlID0gY2FsbDtcblxuXHRcdC8vIElmIHRoaXMgaXMgYSBjaGFpbmVkIGNhbGwsIGdldCB0aGUgcG9zaXRpb24gb2YgdGhlIHByb3BlcnR5IGFjY2VzcyBleHByZXNzaW9uXG5cdFx0Ly8gd2hpY2ggaXMgdGhlIC5sYXp5IHBhcnRcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0Ly8gVGhlIGV4cHJlc3Npb24gaXMgdGhlIHByb3BlcnR5IGFjY2VzczogKGRlZmluZSgnUm9vdEFzeW5jJywgLi4uKSkubGF6eVxuXHRcdFx0Ly8gV2Ugd2FudCB0aGUgcG9zaXRpb24gb2YganVzdCB0aGUgLmxhenkgcGFydFxuXHRcdFx0cG9zaXRpb25Ob2RlID0gY2FsbC5leHByZXNzaW9uLm5hbWU7IC8vIFRoaXMgaXMgdGhlICdsYXp5JyBpZGVudGlmaWVyXG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnRQb3MgPSBwb3NpdGlvbk5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSk7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKHNvdXJjZUZpbGUsIHN0YXJ0UG9zKTtcblxuXHRcdGlmICghbGF6eUNvbnRleHQudHlwZU5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0NvdWxkIG5vdCBleHRyYWN0IHR5cGUgbmFtZSBmcm9tIGxhenkoKSBjYWxsJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IHR5cGVOYW1lIH0gPSBsYXp5Q29udGV4dDtcblxuXHRcdC8vIERldGVybWluZSBwYXJlbnQgdHlwZSBhbmQgY29sbGVjdGlvbiBiYXNlZCBvbiB0aGUgY2FsbCBzb3VyY2UuXG5cdFx0Y29uc3QgcGFyZW50Tm9kZSA9IGxhenlDb250ZXh0LnBhcmVudFR5cGU7XG5cdFx0Y29uc3QgeyBjb2xsZWN0aW9uSWQgfSA9IGxhenlDb250ZXh0O1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25maWcgb3B0aW9uc1xuXHRcdGNvbnN0IGNvbmZpZyA9IHRoaXMuZXh0cmFjdExhenlDb25maWcoY2FsbCk7XG5cblx0XHQvLyBDcmVhdGUgdHlwZSBub2RlIGZpcnN0IHNvIGl0cyBpbnRlcm5hbCBmdWxsUGF0aCAoaW5jbHVkaW5nIGFueSBjb2xsZWN0aW9uIHByZWZpeCkgaXMgcmVzb2x2ZWQuXG5cdFx0Y29uc3Qgbm9kZSA9IFR5cGVHcmFwaEltcGwuY3JlYXRlTm9kZShcblx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0cGFyZW50Tm9kZSxcblx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRsaW5lICsgMSxcblx0XHRcdGNoYXJhY3RlciArIDEsXG5cdFx0XHRjb2xsZWN0aW9uSWRcblx0XHQpO1xuXHRcdG5vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lID0gdGhpcy5nZXRSZWdpc3RyeUludGVyZmFjZU5hbWUoY29sbGVjdGlvbklkKTtcblxuXHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIHRoZSBjb25zdHJ1Y3RvciByZXR1cm5lZCBieSB0aGUgbGF6eSBnZXR0ZXJcblx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzKGNhbGwpO1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZvciBUeXBlUmVnaXN0cnkgc2lnbmF0dXJlXG5cdFx0bm9kZS5jb25zdHJ1Y3RvclBhcmFtcyA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zKGNhbGwpO1xuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoXG5cdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkQ2hpbGQocGFyZW50Tm9kZSwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cblx0XHQvLyBDcmVhdGUgZGVmaW5pdGlvbiBpbmZvIHVzaW5nIHRoZSBub2RlJ3MgcmVzb2x2ZWQgZnVsbFBhdGhcblx0XHRjb25zdCBkZWZpbml0aW9uOiBEZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogcGFyZW50Tm9kZSA/IHBhcmVudE5vZGUuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiBjb25maWcuc3RyaWN0Q2hhaW4gPz8gdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogY29uZmlnLmJsb2NrRXJyb3JzID8/IGZhbHNlLFxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQobm9kZS5mdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdFx0dGhpcy5lZHNTY29wZUJ5Tm9kZS5zZXQoY2FsbCwgbm9kZS5mdWxsUGF0aCk7XG5cblx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50OiBjb25zdCBMYXp5VHlwZSA9IGxhenkoJ0xhenlUeXBlJywgLi4uKSAtPiBtYXAgXCJMYXp5VHlwZVwiIC0+IFwiTGF6eVR5cGVcIlxuXHRcdC8vIEZvciBjaGFpbmVkIGNhbGxzIGxpa2UgY29uc3QgWCA9IGxhenkoJ0EnKS5kZWZpbmUoJ0InKSwgd2Ugd2FudCB0byBtYXAgWCAtPiBBICh0aGUgcm9vdClcblx0XHR0aGlzLnRyYWNrVmFyaWFibGVBc3NpZ25tZW50KGNhbGwsIHBhcmVudE5vZGUsIG5vZGUuZnVsbFBhdGgpO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgbGF6eSgpIGNhbGwgYXJndW1lbnRzIGludG8gYSBub3JtYWxpemVkIHNoYXBlLlxuXHQgKiBIYW5kbGVzIG5hbWVkL3VubmFtZWQgYW5kIGV4cGxpY2l0LXNvdXJjZSBmb3JtcywgYm90aCBhcyBmcmVlIGNhbGxzXG5cdCAqIGFuZCBhcyBtZXRob2QgY2FsbHMuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q2FsbEFyZ3MgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKToge1xuXHRcdHNvdXJjZT86IHRzLkV4cHJlc3Npb247XG5cdFx0bmFtZT86IHN0cmluZztcblx0XHRnZXR0ZXI6IHRzLkV4cHJlc3Npb247XG5cdFx0Y29uZmlnPzogdHMuRXhwcmVzc2lvbjtcblx0fSB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGNvbnN0IGlzTWV0aG9kQ2FsbCA9IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbik7XG5cblx0XHRpZiAoaXNNZXRob2RDYWxsKSB7XG5cdFx0XHQvLyBTb3VyY2UgaXMgdGhlIG9iamVjdCBvZiB0aGUgcHJvcGVydHkgYWNjZXNzOiBUeXBlLmxhenkoLi4uKVxuXHRcdFx0Y29uc3Qgc291cmNlID0gY2FsbC5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IG1ldGhvZEZpcnN0QXJnID0gYXJnc1sgMCBdO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChtZXRob2RGaXJzdEFyZykpIHtcblx0XHRcdFx0Ly8gVHlwZS5sYXp5KCdOYW1lJywgZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0XHRpZiAoYXJncy5sZW5ndGggPCAyKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHNvdXJjZSxcblx0XHRcdFx0XHRuYW1lICAgOiBtZXRob2RGaXJzdEFyZy50ZXh0LFxuXHRcdFx0XHRcdGdldHRlciA6IGFyZ3NbIDEgXSxcblx0XHRcdFx0XHRjb25maWcgOiBhcmdzWyAyIF0sXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cdFx0XHQvLyBUeXBlLmxhenkoZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0c291cmNlLFxuXHRcdFx0XHRnZXR0ZXIgOiBtZXRob2RGaXJzdEFyZyxcblx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMSBdLFxuXHRcdFx0fTtcblx0XHR9XG5cblx0XHQvLyBGcmVlIGNhbGw6IGxhenkoLi4uKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBmaXJzdEFyZyA9IGFyZ3NbIDAgXTtcblxuXHRcdC8vIEV4cGxpY2l0LXNvdXJjZSBmb3JtOiBsYXp5KHNvdXJjZSwgJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0Ly8gb3IgbGF6eShzb3VyY2UsIGdldHRlciwgY29uZmlnPylcblx0XHRpZiAoYXJncy5sZW5ndGggPj0gMiAmJiB0cy5pc0lkZW50aWZpZXIoZmlyc3RBcmcpKSB7XG5cdFx0XHRjb25zdCBzZWNvbmRBcmcgPSBhcmdzWyAxIF07XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKHNlY29uZEFyZykpIHtcblx0XHRcdFx0Ly8gbGF6eShzb3VyY2UsICdOYW1lJywgZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0XHRpZiAoYXJncy5sZW5ndGggPCAzKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHNvdXJjZSA6IGZpcnN0QXJnLFxuXHRcdFx0XHRcdG5hbWUgICA6IHNlY29uZEFyZy50ZXh0LFxuXHRcdFx0XHRcdGdldHRlciA6IGFyZ3NbIDIgXSxcblx0XHRcdFx0XHRjb25maWcgOiBhcmdzWyAzIF0sXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cdFx0XHQvLyBsYXp5KHNvdXJjZSwgZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0c291cmNlIDogZmlyc3RBcmcsXG5cdFx0XHRcdGdldHRlciA6IHNlY29uZEFyZyxcblx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMiBdLFxuXHRcdFx0fTtcblx0XHR9XG5cblx0XHQvLyBOYW1lZCByb290IGZvcm06IGxhenkoJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChmaXJzdEFyZykpIHtcblx0XHRcdGlmIChhcmdzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB7XG5cdFx0XHRcdG5hbWUgICA6IGZpcnN0QXJnLnRleHQsXG5cdFx0XHRcdGdldHRlciA6IGFyZ3NbIDEgXSxcblx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMiBdLFxuXHRcdFx0fTtcblx0XHR9XG5cblx0XHQvLyBVbm5hbWVkIHJvb3QgZm9ybTogbGF6eShnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0cmV0dXJuIHtcblx0XHRcdGdldHRlciA6IGZpcnN0QXJnLFxuXHRcdFx0Y29uZmlnIDogYXJnc1sgMSBdLFxuXHRcdH07XG5cdH1cblxuXHQvKipcblx0ICogVW53cmFwIHRoZSBjb25zdHJ1Y3RvciByZXR1cm5lZCBieSBhIGxhenkgZ2V0dGVyLlxuXHQgKiBTdXBwb3J0czpcblx0ICogICAoKSA9PiBjbGFzcyBOYW1lIHt9XG5cdCAqICAgKCkgPT4gZnVuY3Rpb24gTmFtZSgpIHt9XG5cdCAqICAgKCkgPT4geyByZXR1cm4gY2xhc3MgTmFtZSB7fTsgfVxuXHQgKiAgIGZ1bmN0aW9uICgpIHsgcmV0dXJuIGZ1bmN0aW9uIE5hbWUoKSB7fTsgfVxuXHQgKi9cblx0cHJpdmF0ZSB1bndyYXBMYXp5R2V0dGVyIChnZXR0ZXJFeHByOiB0cy5FeHByZXNzaW9uKTogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihnZXR0ZXJFeHByKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBnZXR0ZXJFeHByO1xuXHRcdFx0aWYgKCF0cy5pc0Jsb2NrKGJvZHkpKSB7XG5cdFx0XHRcdHJldHVybiBib2R5O1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBzdG10IG9mIGJvZHkuc3RhdGVtZW50cykge1xuXHRcdFx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQoc3RtdCkgJiYgc3RtdC5leHByZXNzaW9uKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHN0bXQuZXhwcmVzc2lvbjtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oZ2V0dGVyRXhwcikpIHtcblx0XHRcdGNvbnN0IHsgYm9keSB9ID0gZ2V0dGVyRXhwcjtcblx0XHRcdGZvciAoY29uc3Qgc3RtdCBvZiBib2R5LnN0YXRlbWVudHMpIHtcblx0XHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KHN0bXQpICYmIHN0bXQuZXhwcmVzc2lvbikge1xuXHRcdFx0XHRcdHJldHVybiBzdG10LmV4cHJlc3Npb247XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gTm90IGEgcmVjb2duaXplZCBnZXR0ZXIgcGF0dGVyblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBhIGNvbnN0cnVjdG9yIG5hbWUgZnJvbSBhIGNsYXNzIGV4cHJlc3Npb24sIGNsYXNzIGRlY2xhcmF0aW9uLFxuXHQgKiBvciBuYW1lZCBmdW5jdGlvbiBleHByZXNzaW9uLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JOYW1lIChjb25zdHJ1Y3RvckV4cHI6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc0NsYXNzRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpICYmIGNvbnN0cnVjdG9yRXhwci5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gY29uc3RydWN0b3JFeHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihjb25zdHJ1Y3RvckV4cHIpICYmIGNvbnN0cnVjdG9yRXhwci5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gY29uc3RydWN0b3JFeHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikgJiYgY29uc3RydWN0b3JFeHByLm5hbWUpIHtcblx0XHRcdHJldHVybiBjb25zdHJ1Y3RvckV4cHIubmFtZS50ZXh0O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdGhlIHR5cGUgbmFtZSBmcm9tIGVpdGhlciBhIGRlZmluZSgpIG9yIGxhenkoKSBjYWxsLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0TW5lbW9uaWNhVHlwZU5hbWUgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwoY2FsbCkpIHtcblx0XHRcdHJldHVybiB0aGlzLmV4dHJhY3RUeXBlTmFtZShjYWxsKTtcblx0XHR9XG5cdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChjYWxsKSkge1xuXHRcdFx0Y29uc3QgYXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRcdGlmICghYXJncykge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGFyZ3MubmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gYXJncy5uYW1lO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy51bndyYXBMYXp5R2V0dGVyKGFyZ3MuZ2V0dGVyKTtcblx0XHRcdGlmIChjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdFx0cmV0dXJuIHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yTmFtZShjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdGhlIGZ1bGwgbGF6eSgpIGNhbGwgY29udGV4dDogdHlwZSBuYW1lLCBwYXJlbnQgdHlwZSwgYW5kIGNvbGxlY3Rpb24uXG5cdCAqIEhhbmRsZXMgZGlyZWN0IGNhbGxzLCBwcm9wZXJ0eS1hY2Nlc3MgY2FsbHMsIGNoYWluZWQgY2FsbHMsIGFuZCB0aGVcblx0ICogZXhwbGljaXQtc291cmNlIGZvcm0gYGxhenkoc291cmNlLCAnVHlwZU5hbWUnLCBnZXR0ZXIpYC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdExhenlDb250ZXh0IChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHtcblx0XHR0eXBlTmFtZT86IHN0cmluZztcblx0XHRwYXJlbnRUeXBlPzogVHlwZU5vZGU7XG5cdFx0Y29sbGVjdGlvbklkPzogc3RyaW5nO1xuXHR9IHtcblx0XHRjb25zdCBhcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdGlmICghYXJncykge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGxldCB0eXBlTmFtZTogc3RyaW5nIHwgdW5kZWZpbmVkID0gYXJncy5uYW1lO1xuXHRcdGlmICghdHlwZU5hbWUpIHtcblx0XHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMudW53cmFwTGF6eUdldHRlcihhcmdzLmdldHRlcik7XG5cdFx0XHRpZiAoY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRcdHR5cGVOYW1lID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JOYW1lKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGlmICghdHlwZU5hbWUpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IGNhbGw7XG5cblx0XHQvLyBEaXJlY3QgY2FsbDogbGF6eSgnVHlwZU5hbWUnLCAuLi4pIG9yIGxhenkoc291cmNlLCAnVHlwZU5hbWUnLCBnZXR0ZXIpXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLnRleHQgPT09ICdsYXp5Jykge1xuXHRcdFx0aWYgKGFyZ3Muc291cmNlICYmIHRzLmlzSWRlbnRpZmllcihhcmdzLnNvdXJjZSkpIHtcblx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShhcmdzLnNvdXJjZS50ZXh0KTtcblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHR0eXBlTmFtZSxcblx0XHRcdFx0XHRwYXJlbnRUeXBlICAgOiBzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUsXG5cdFx0XHRcdFx0Y29sbGVjdGlvbklkIDogc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQsXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cdFx0XHQvLyBQbGFpbiByb290IGxhenkgaW4gZGVmYXVsdCBjb2xsZWN0aW9uXG5cdFx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2VzczogWC5sYXp5KCdUeXBlTmFtZScsIC4uLilcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi5uYW1lLnRleHQgPT09ICdsYXp5Jykge1xuXHRcdFx0Y29uc3Qgb2JqID0gZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG9iaikpIHtcblx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShvYmoudGV4dCk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBOZXN0ZWQgYWNjZXNzOiBpbnN0YW5jZS5UeXBlLmxhenkgLSB0cnkgdG8gcmVzb2x2ZVxuXHRcdFx0XHRjb25zdCBjaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlDaGFpbihvYmopO1xuXHRcdFx0XHRpZiAoY2hhaW4ubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGNoYWluLmpvaW4oJy4nKSk7XG5cdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlIH07XG5cdFx0XHRcdH1cblx0XHRcdH1cblxuXHRcdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBEZXRlcm1pbmUgdGhlIGNvbGxlY3Rpb24gY29udGV4dCBmcm9tIHRoZSByb290IG9mIHRoZSBjaGFpbiBzbyB0aGF0XG5cdFx0XHRcdC8vIGN1c3RvbS1jb2xsZWN0aW9uIHR5cGVzIGRvIG5vdCBnZXQgY29uZnVzZWQgd2l0aCBkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMuXG5cdFx0XHRcdGNvbnN0IHJvb3RJZCA9IHRoaXMuZ2V0Um9vdElkZW50aWZpZXIob2JqLmV4cHJlc3Npb24pO1xuXHRcdFx0XHRjb25zdCBleHBlY3RlZENvbGxlY3Rpb25JZCA9IHJvb3RJZFxuXHRcdFx0XHRcdD8gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKHJvb3RJZC50ZXh0KS5jb2xsZWN0aW9uSWRcblx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblxuXHRcdFx0XHQvLyBDaGFpbmVkIGNhbGw6IGRlZmluZSgnQScpLmxhenkoJ0InKSBvciBsYXp5KCdBJykubGF6eSgnQicpXG5cdFx0XHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ2FsbChvYmosIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudFR5cGVOYW1lID0gdGhpcy5leHRyYWN0TW5lbW9uaWNhVHlwZU5hbWUob2JqKTtcblx0XHRcdFx0XHRpZiAocGFyZW50VHlwZU5hbWUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKHBhcmVudFR5cGVOYW1lLCBleHBlY3RlZENvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGlmICh0aGlzLmlzTGF6eUNhbGwob2JqKSkge1xuXHRcdFx0XHRcdHRoaXMucHJvY2Vzc0xhenlDYWxsKG9iaiwgc291cmNlRmlsZSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gQnVpbGRlciBsb29rdXAgY2hhaW46IEFwcC5sb29rdXAoJ1VzZXInKS5sYXp5KCdBZG1pbicpXG5cdFx0XHRcdGlmICh0aGlzLmlzTG9va3VwQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0Y29uc3QgbG9va2VkVXBQYXRoID0gdGhpcy5yZXNvbHZlTG9va3VwUGF0aChvYmopO1xuXHRcdFx0XHRcdGlmIChsb29rZWRVcFBhdGgpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGxvb2tlZFVwUGF0aCk7XG5cdFx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGUuY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHsgdHlwZU5hbWUgfTtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGNvbmZpZyBvcHRpb25zIGZyb20gbGF6eSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdExhenlDb25maWcgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogeyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9IHtcblx0XHRjb25zdCBhcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdGlmICghYXJncyB8fCAhYXJncy5jb25maWcgfHwgIXRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24oYXJncy5jb25maWcpKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgY29uZmlnUmVzdWx0ID0gdGhpcy5leHRyYWN0Q29uZmlnRnJvbU9iamVjdExpdGVyYWwoYXJncy5jb25maWcpO1xuXHRcdHJldHVybiBjb25maWdSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHQqIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnRzIHRoYXQgY2FwdHVyZSBkZWZpbmUoKSByZXN1bHRzXG5cdFx0KiBlLmcuLCBjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKSBtYXBzIFwiVXNlclwiIC0+IFwiVXNlckVudGl0eVwiXG5cdFx0KiBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGNvbnN0IFggPSBkZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKSwgd2UgbWFwIFggLT4gQSAodGhlIHJvb3QgdHlwZSlcblx0XHQqL1xuXHRwcml2YXRlIHRyYWNrVmFyaWFibGVBc3NpZ25tZW50IChcblx0XHRjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHRwYXJlbnROb2RlOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCxcblx0XHRmdWxsUGF0aDogc3RyaW5nXG5cdCk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGlmIHRoaXMgY2FsbCBpcyB0aGUgcmlnaHQtaGFuZCBzaWRlIG9mIGEgdmFyaWFibGUgZGVjbGFyYXRpb25cblx0XHQvLyBXYWxrIHVwIHRoZSB0cmVlIHRvIGZpbmQgVmFyaWFibGVEZWNsYXJhdGlvblxuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gY2FsbC5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24oY3VycmVudCkpIHtcblx0XHRcdFx0Ly8gRm91bmQ6IGNvbnN0IFggPSBkZWZpbmUoLi4uKVxuXHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCB2YXJOYW1lID0gY3VycmVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Ly8gSWYgdGhpcyBpcyBhIGNoYWluZWQgY2FsbCAoaGFzIHBhcmVudCksIGRvbid0IG92ZXJ3cml0ZSBleGlzdGluZyBtYXBwaW5nXG5cdFx0XHRcdFx0Ly8gVGhlIGZpcnN0IGRlZmluZSBpbiB0aGUgY2hhaW4gc2V0cyB0aGUgbWFwcGluZyB0byB0aGUgcm9vdCB0eXBlXG5cdFx0XHRcdFx0aWYgKHBhcmVudE5vZGUgJiYgdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5oYXModmFyTmFtZSkpIHtcblx0XHRcdFx0XHRcdHJldHVybjtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0dGhpcy52YXJpYWJsZVRvVHlwZU1hcC5zZXQodmFyTmFtZSwgZnVsbFBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdH1cblx0XG5cdC8qKlxuXHRcdCogVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHMgZnJvbSBsb29rdXAoKSBjYWxsc1xuXHRcdCogZS5nLiwgY29uc3QgU2VudGllbmNlQ29uc3RydWN0b3IgPSBsb29rdXAoJ1NlbnRpZW5jZScpIG1hcHMgXCJTZW50aWVuY2VDb25zdHJ1Y3RvclwiIC0+IFwiU2VudGllbmNlXCJcblx0XHQqL1xuXHRwcml2YXRlIHRyYWNrTG9va3VwQXNzaWdubWVudCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHR5cGVQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHQvLyBXYWxrIHVwIHRoZSB0cmVlIHRvIGZpbmQgVmFyaWFibGVEZWNsYXJhdGlvblxuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gY2FsbC5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24oY3VycmVudCkpIHtcblx0XHRcdFx0Ly8gRm91bmQ6IGNvbnN0IFggPSBsb29rdXAoLi4uKVxuXHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCB2YXJOYW1lID0gY3VycmVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0dGhpcy52YXJpYWJsZVRvVHlwZU1hcC5zZXQodmFyTmFtZSwgdHlwZVBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHQqIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnRzIGZyb20gbmV3IFR5cGUoKSBjYWxsc1xuXHRcdCogZS5nLiwgY29uc3QgdXNlciA9IG5ldyBVc2VyVHlwZSgpIG1hcHMgXCJ1c2VyXCIgLT4gXCJVc2VyVHlwZVwiXG5cdFx0Ki9cblx0cHJpdmF0ZSB0cmFja05ld0Fzc2lnbm1lbnQgKG5ld0V4cHI6IHRzLk5ld0V4cHJlc3Npb24sIHR5cGVQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHQvLyBXYWxrIHVwIHRoZSB0cmVlIHRvIGZpbmQgVmFyaWFibGVEZWNsYXJhdGlvblxuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbmV3RXhwci5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24oY3VycmVudCkpIHtcblx0XHRcdFx0Ly8gRm91bmQ6IGNvbnN0IFggPSBuZXcgVHlwZSguLi4pXG5cdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudC5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHZhck5hbWUgPSBjdXJyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0XHR0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLnNldCh2YXJOYW1lLCB0eXBlUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdCogUHJvY2VzcyBhIEBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHQgKi9cblx0cHJpdmF0ZSBwcm9jZXNzRGVjb3JhdGVEZWNvcmF0b3IgKFxuXHRcdGRlY29yYXRvcjogdHMuRGVjb3JhdG9yLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0Y2xhc3NEZWNsUGFyYW0/OiB0cy5DbGFzc0RlY2xhcmF0aW9uXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRkZWNvcmF0b3IuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXG5cdFx0Ly8gR2V0IHRoZSBjbGFzcyBkZWNsYXJhdGlvbiAtIHVzZSB0aGUgcGFzc2VkIGNvbnRleHQgaWYgcGFyZW50IGlzIG5vdCBzZXRcblx0XHRjb25zdCBjbGFzc0RlY2wgPSBkZWNvcmF0b3IucGFyZW50IGFzIHRzLkNsYXNzRGVjbGFyYXRpb24gfCB1bmRlZmluZWQgfHwgY2xhc3NEZWNsUGFyYW07XG5cdFx0aWYgKCFjbGFzc0RlY2wgfHwgIWNsYXNzRGVjbC5uYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdEZWNvcmF0ZWQgY2xhc3MgaGFzIG5vIG5hbWUnLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHR5cGVOYW1lID0gY2xhc3NEZWNsLm5hbWUudGV4dDtcblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdEZWNvcmF0ZWQgY2xhc3MgaGFzIG5vIG5hbWUnLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFBhcnNlIGRlY29yYXRvciBhcmd1bWVudHM6IEBkZWNvcmF0ZSgpLCBAZGVjb3JhdGUoUGFyZW50KSxcblx0XHQvLyBAZGVjb3JhdGUoeyAuLi4gfSksIEBkZWNvcmF0ZShQYXJlbnQsIHsgLi4uIH0pLFxuXHRcdC8vIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSwgQE15Q29sbGVjdGlvbi5kZWNvcmF0ZSh7IC4uLiB9KVxuXHRcdGxldCBwYXJlbnROb2RlOiBUeXBlTm9kZSB8IHVuZGVmaW5lZDtcblx0XHRsZXQgcGFyZW50RnVsbFBhdGg6IHN0cmluZyB8IG51bGwgPSBudWxsO1xuXHRcdGxldCBjb2xsZWN0aW9uSWQ6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRsZXQgZGVjb3JhdG9yQ29uZmlnOiB7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0gPSB7fTtcblxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGRlY29yYXRvci5leHByZXNzaW9uKSkge1xuXHRcdFx0Y29uc3QgY2FsbEV4cHIgPSBkZWNvcmF0b3IuZXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IGNhbGxlZSA9IGNhbGxFeHByLmV4cHJlc3Npb247XG5cblx0XHRcdC8vIENoZWNrIGZvciBATXlDb2xsZWN0aW9uLmRlY29yYXRlKCkgd2hlcmUgTXlDb2xsZWN0aW9uIGlzIGEgY3VzdG9tIGNvbGxlY3Rpb24uXG5cdFx0XHQvLyBUaGUgZGVjb3JhdGVkIGNsYXNzIGJlY29tZXMgYSByb290IHR5cGUgaW4gdGhhdCBjb2xsZWN0aW9uLlxuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsZWUpICYmXG5cdFx0XHRcdGNhbGxlZS5uYW1lLnRleHQgPT09ICdkZWNvcmF0ZScgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGNhbGxlZS5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGNhbGxlZS5leHByZXNzaW9uLnRleHQpXG5cdFx0XHQpIHtcblx0XHRcdFx0Y29sbGVjdGlvbklkID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChjYWxsZWUuZXhwcmVzc2lvbi50ZXh0KTtcblx0XHRcdFx0aWYgKGNhbGxFeHByLmFyZ3VtZW50cy5sZW5ndGggPT09IDEgJiYgdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihjYWxsRXhwci5hcmd1bWVudHNbIDAgXSkpIHtcblx0XHRcdFx0XHRkZWNvcmF0b3JDb25maWcgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjYWxsRXhwci5hcmd1bWVudHNbIDAgXSk7XG5cdFx0XHRcdH1cblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGNvbnN0IGFyZ3MgPSBjYWxsRXhwci5hcmd1bWVudHM7XG5cdFx0XHRcdGxldCBwYXJlbnRBcmc6IHRzLklkZW50aWZpZXIgfCB1bmRlZmluZWQ7XG5cdFx0XHRcdGxldCBjb25maWdBcmc6IHRzLk9iamVjdExpdGVyYWxFeHByZXNzaW9uIHwgdW5kZWZpbmVkO1xuXG5cdFx0XHRcdGZvciAoY29uc3QgYXJnIG9mIGFyZ3MpIHtcblx0XHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdFx0XHRcdGlmIChwYXJlbnRBcmcpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdFx0XHRcdFx0bWVzc2FnZSA6ICdAZGVjb3JhdGUoKSBhY2NlcHRzIG9ubHkgb25lIHBhcmVudCByZWZlcmVuY2UnLFxuXHRcdFx0XHRcdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0XHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0XHRwYXJlbnRBcmcgPSBhcmc7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdFx0XHRcdGlmIChjb25maWdBcmcpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdFx0XHRcdFx0bWVzc2FnZSA6ICdAZGVjb3JhdGUoKSBhY2NlcHRzIG9ubHkgb25lIGNvbmZpZyBvYmplY3QnLFxuXHRcdFx0XHRcdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0XHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0XHRjb25maWdBcmcgPSBhcmc7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0aWYgKHBhcmVudEFyZykge1xuXHRcdFx0XHRcdHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlJZGVudGlmaWVyKHBhcmVudEFyZy50ZXh0KTtcblx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0XHRcdFx0cGFyZW50RnVsbFBhdGggPSBwYXJlbnROb2RlLmZ1bGxQYXRoO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGlmIChjb25maWdBcmcpIHtcblx0XHRcdFx0XHRkZWNvcmF0b3JDb25maWcgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjb25maWdBcmcpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gQnVpbGQgZnVsbCBwYXRoXG5cdFx0Y29uc3QgZnVsbFBhdGggPSBwYXJlbnROb2RlID8gYCR7cGFyZW50Tm9kZS5mdWxsUGF0aH0uJHt0eXBlTmFtZX1gIDogdHlwZU5hbWU7XG5cblx0XHQvLyBDcmVhdGUgZGVmaW5pdGlvbiBpbmZvIGZvciBkZWNvcmF0ZVxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWNvcmF0ZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IHBhcmVudEZ1bGxQYXRoLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiBkZWNvcmF0b3JDb25maWcuc3RyaWN0Q2hhaW4gPz8gdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogZGVjb3JhdG9yQ29uZmlnLmJsb2NrRXJyb3JzID8/IGZhbHNlLFxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQoZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXHRcdHRoaXMuZWRzU2NvcGVCeU5vZGUuc2V0KGNsYXNzRGVjbCwgZnVsbFBhdGgpO1xuXG5cdFx0Ly8gQ3JlYXRlIHR5cGUgbm9kZVxuXHRcdGNvbnN0IG5vZGUgPSBUeXBlR3JhcGhJbXBsLmNyZWF0ZU5vZGUoXG5cdFx0XHR0eXBlTmFtZSxcblx0XHRcdHBhcmVudE5vZGUsXG5cdFx0XHRzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0bGluZSArIDEsXG5cdFx0XHRjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0Y29sbGVjdGlvbklkXG5cdFx0KTtcblx0XHRub2RlLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA9IHRoaXMuZ2V0UmVnaXN0cnlJbnRlcmZhY2VOYW1lKG5vZGUuY29sbGVjdGlvbklkKTtcblxuXHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBhbmQgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGNsYXNzIG1lbWJlcnNcblx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RDbGFzc1Byb3BlcnRpZXMoY2xhc3NEZWNsKTtcblx0XHRub2RlLmNvbnN0cnVjdG9yUGFyYW1zID0gdGhpcy5leHRyYWN0Q2xhc3NDb25zdHJ1Y3RvclBhcmFtcyhjbGFzc0RlY2wpO1xuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoXG5cdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkQ2hpbGQocGFyZW50Tm9kZSwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0eXBlIG5hbWUgZnJvbSBkZWZpbmUoKSBjYWxsIGFyZ3VtZW50cy5cblx0ICogSGFuZGxlczpcblx0ICogICBkZWZpbmUoJ1R5cGVOYW1lJywgaGFuZGxlcilcblx0ICogICBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKSAgIC8vIGV4cGxpY2l0LXNvdXJjZSBmb3JtXG5cdCAqICAgZGVmaW5lKGZ1bmN0aW9uIFR5cGVOYW1lKCkge30pXG5cdCAqICAgZGVmaW5lKCgpID0+IGNsYXNzIFR5cGVOYW1lIHt9KVxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0VHlwZU5hbWUgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBhcmdzID0gY2FsbC5hcmd1bWVudHM7XG5cblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmlyc3RBcmcgPSBhcmdzWyAwIF07XG5cblx0XHQvLyBFeHBsaWNpdC1zb3VyY2UgZm9ybTogZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilcblx0XHRpZiAoYXJncy5sZW5ndGggPj0gMiAmJiB0cy5pc0lkZW50aWZpZXIoZmlyc3RBcmcpICYmIHRzLmlzU3RyaW5nTGl0ZXJhbChhcmdzWyAxIF0pKSB7XG5cdFx0XHRyZXR1cm4gYXJnc1sgMSBdLnRleHQ7XG5cdFx0fVxuXG5cdFx0Ly8gU3RyaW5nIGxpdGVyYWw6IGRlZmluZSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChmaXJzdEFyZykpIHtcblx0XHRcdHJldHVybiBmaXJzdEFyZy50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIEZ1bmN0aW9uIHdpdGggbmFtZTogZGVmaW5lKGZ1bmN0aW9uIFR5cGVOYW1lKCkge30pXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGZpcnN0QXJnKSAmJiBmaXJzdEFyZy5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gZmlyc3RBcmcubmFtZS50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIEFycm93IGZ1bmN0aW9uIHJldHVybmluZyBjbGFzczogZGVmaW5lKCgpID0+IGNsYXNzIFR5cGVOYW1lIHt9KVxuXHRcdGlmICh0cy5pc0Fycm93RnVuY3Rpb24oZmlyc3RBcmcpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGZpcnN0QXJnO1xuXHRcdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGJvZHkpICYmIGJvZHkubmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gYm9keS5uYW1lLnRleHQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSBmdWxsIGRlZmluZSgpIGNhbGwgY29udGV4dDogdHlwZSBuYW1lLCBwYXJlbnQgdHlwZSwgYW5kIGNvbGxlY3Rpb24uXG5cdCAqIEhhbmRsZXMgZGlyZWN0IGNhbGxzLCBwcm9wZXJ0eS1hY2Nlc3MgY2FsbHMsIGNoYWluZWQgY2FsbHMsIGFuZCB0aGVcblx0ICogZXhwbGljaXQtc291cmNlIGZvcm0gYGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpYC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdERlZmluZUNvbnRleHQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKToge1xuXHRcdHR5cGVOYW1lPzogc3RyaW5nO1xuXHRcdHBhcmVudFR5cGU/OiBUeXBlTm9kZTtcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmc7XG5cdH0ge1xuXHRcdGNvbnN0IHR5cGVOYW1lID0gdGhpcy5leHRyYWN0VHlwZU5hbWUoY2FsbCk7XG5cdFx0aWYgKCF0eXBlTmFtZSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gY2FsbDtcblxuXHRcdC8vIERpcmVjdCBjYWxsOiBkZWZpbmUoJ1R5cGVOYW1lJywgLi4uKSBvciBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0Ly8gRXhwbGljaXQtc291cmNlIGZvcm06IGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdFx0XHRpZiAoY2FsbC5hcmd1bWVudHMubGVuZ3RoID49IDIgJiYgdHMuaXNJZGVudGlmaWVyKGNhbGwuYXJndW1lbnRzWyAwIF0pKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZU5hbWUgPSBjYWxsLmFyZ3VtZW50c1sgMCBdLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBQbGFpbiByb290IGRlZmluZSBpbiBkZWZhdWx0IGNvbGxlY3Rpb25cblx0XHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiBYLmRlZmluZSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0Y29uc3Qgb2JqID0gZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG9iaikpIHtcblx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShvYmoudGV4dCk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBOZXN0ZWQgYWNjZXNzOiBpbnN0YW5jZS5UeXBlLmRlZmluZSAtIHRyeSB0byByZXNvbHZlXG5cdFx0XHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKG9iaik7XG5cdFx0XHRcdGlmIChjaGFpbi5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoY2hhaW4uam9pbignLicpKTtcblx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUgfTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihvYmopKSB7XG5cdFx0XHRcdC8vIERldGVybWluZSB0aGUgY29sbGVjdGlvbiBjb250ZXh0IGZyb20gdGhlIHJvb3Qgb2YgdGhlIGNoYWluIHNvIHRoYXRcblx0XHRcdFx0Ly8gY3VzdG9tLWNvbGxlY3Rpb24gdHlwZXMgZG8gbm90IGdldCBjb25mdXNlZCB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcy5cblx0XHRcdFx0Y29uc3Qgcm9vdElkID0gdGhpcy5nZXRSb290SWRlbnRpZmllcihvYmouZXhwcmVzc2lvbik7XG5cdFx0XHRcdGNvbnN0IGV4cGVjdGVkQ29sbGVjdGlvbklkID0gcm9vdElkXG5cdFx0XHRcdFx0PyB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uocm9vdElkLnRleHQpLmNvbGxlY3Rpb25JZFxuXHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXG5cdFx0XHRcdC8vIENoYWluZWQgY2FsbDogZGVmaW5lKCdBJykuZGVmaW5lKCdCJykgb3IgbW5lbW9uaWNhLmRlZmluZSgnQScpLmRlZmluZSgnQicpXG5cdFx0XHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ2FsbChvYmosIGNhbGwuZ2V0U291cmNlRmlsZSgpKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdFR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0Ly8gSW5oZXJpdCBjb2xsZWN0aW9uIGZyb20gdGhlIHBhcmVudCB0eXBlIChpZiBhbnkpXG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIENoYWluZWQgbGF6eSBjYWxsOiBsYXp5KCdBJykuZGVmaW5lKCdCJykgb3IgVHlwZS5sYXp5KCdBJykuZGVmaW5lKCdCJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzTGF6eUNhbGwob2JqLCBjYWxsLmdldFNvdXJjZUZpbGUoKSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gQnVpbGRlciBsb29rdXAgY2hhaW46IEFwcC5sb29rdXAoJ1VzZXInKS5kZWZpbmUoJ0FkbWluJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMb29rdXBDYWxsKG9iaikpIHtcblx0XHRcdFx0XHRjb25zdCBsb29rZWRVcFBhdGggPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKG9iaik7XG5cdFx0XHRcdFx0aWYgKGxvb2tlZFVwUGF0aCkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUobG9va2VkVXBQYXRoKTtcblx0XHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZS5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHR9XG5cblx0LyoqXG5cdCAqIFByZWZpeCBhIGRvdHRlZCB0eXBlIHBhdGggd2l0aCBhIGNvbGxlY3Rpb24gaWRlbnRpZmllciBzbyBjdXN0b20tY29sbGVjdGlvblxuXHQgKiB0eXBlcyBkbyBub3QgY29sbGlkZSB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcyBpbiB0aGUgZ3JhcGguXG5cdCAqL1xuXHRwcml2YXRlIHByZWZpeENvbGxlY3Rpb25QYXRoIChwYXRoOiBzdHJpbmcsIGNvbGxlY3Rpb25JZDogc3RyaW5nKTogc3RyaW5nIHtcblx0XHRyZXR1cm4gYCR7Y29sbGVjdGlvbklkfTo6JHtwYXRofWA7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGRlZmluZSgpIHNvdXJjZSBpZGVudGlmaWVyIHRvIGVpdGhlciBhIHBhcmVudCB0eXBlLCBhIGNvbGxlY3Rpb24sXG5cdCAqIG9yIHRoZSBkZWZhdWx0IChtb2R1bGUgb2JqZWN0KSBjb2xsZWN0aW9uLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRGVmaW5lU291cmNlIChzb3VyY2VOYW1lOiBzdHJpbmcpOiB7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Ly8gTW9kdWxlIG9iamVjdCBhbGlhc2VzIC0+IHJvb3QgaW4gZGVmYXVsdCBjb2xsZWN0aW9uXG5cdFx0aWYgKHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhzb3VyY2VOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdC8vIENvbGxlY3Rpb24gdmFyaWFibGVzIC0+IHJvb3QgaW4gdGhhdCBjb2xsZWN0aW9uXG5cdFx0Y29uc3QgY29sbGVjdGlvbklkID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChzb3VyY2VOYW1lKTtcblx0XHRpZiAoY29sbGVjdGlvbklkKSB7XG5cdFx0XHRyZXR1cm4geyBjb2xsZWN0aW9uSWQgfTtcblx0XHR9XG5cblx0XHQvLyBPdGhlcndpc2UgdHJlYXQgYXMgYSB0eXBlIHZhcmlhYmxlIHJlZmVyZW5jZVxuXHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlJZGVudGlmaWVyKHNvdXJjZU5hbWUpO1xuXHRcdHJldHVybiB7IHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhIGNhbGwgZXhwcmVzc2lvbiBpcyBhIGxvb2t1cCgpIGNhbGwuXG5cdCAqL1xuXHRwcml2YXRlIGlzTG9va3VwQ2FsbCAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24pOiBib29sZWFuIHtcblx0XHRjb25zdCBleHByID0gbm9kZS5leHByZXNzaW9uO1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikgJiYgZXhwci50ZXh0ID09PSAnbG9va3VwJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSAmJiBleHByLm5hbWUudGV4dCA9PT0gJ2xvb2t1cCcpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGxvb2t1cCgpIGNhbGwgdG8gYSBkb3R0ZWQgdHlwZSBwYXRoIChiZXN0IGVmZm9ydCkuXG5cdCAqIEhhbmRsZXM6XG5cdCAqICAgbG9va3VwKCdVc2VyJylcblx0ICogICBsb29rdXAoc291cmNlLCAnVXNlcicpXG5cdCAqICAgQXBwLmxvb2t1cCgnVXNlcicpXG5cdCAqICAgY29sbGVjdGlvbi5sb29rdXAoJ1VzZXIuQWRtaW4nKVxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlTG9va3VwUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGFyZ3MgPSBjYWxsLmFyZ3VtZW50cztcblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gU2luZ2xlLWFyZyBsb29rdXA6IGxvb2t1cCgnVXNlcicpIG9yIEFwcC5sb29rdXAoJ1VzZXInKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMSkge1xuXHRcdFx0Y29uc3QgYXJnID0gYXJnc1sgMCBdO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChhcmcpIHx8IHRzLmlzTm9TdWJzdGl0dXRpb25UZW1wbGF0ZUxpdGVyYWwoYXJnKSkge1xuXHRcdFx0XHRjb25zdCBwYXRoID0gYXJnLnRleHQ7XG5cdFx0XHRcdC8vIElmIHRoaXMgaXMgYSBtZXRob2QgY2FsbCBvbiBhIHNvdXJjZSwgcmVzb2x2ZSByZWxhdGl2ZSB0byB0aGF0IHNvdXJjZS5cblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRjb25zdCBzb3VyY2VFeHByID0gY2FsbC5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihzb3VyY2VFeHByKSkge1xuXHRcdFx0XHRcdFx0Y29uc3Qgc291cmNlTmFtZSA9IHNvdXJjZUV4cHIudGV4dDtcblx0XHRcdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRcdFx0XHRpZiAoc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQpIHtcblx0XHRcdFx0XHRcdFx0Ly8gQ29sbGVjdGlvbiBsb29rdXA6IHByZWZpeCBwYXRoIHdpdGggdGhlIGNvbGxlY3Rpb24gaWRcblx0XHRcdFx0XHRcdFx0cmV0dXJuIHRoaXMucHJlZml4Q29sbGVjdGlvblBhdGgocGF0aCwgc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSkge1xuXHRcdFx0XHRcdFx0XHQvLyBUeXBlIGxvb2t1cDogcmVsYXRpdmUgZmlyc3QsIHRoZW4gcm9vdCBmYWxsYmFja1xuXHRcdFx0XHRcdFx0XHRjb25zdCByZWxhdGl2ZVBhdGggPSBgJHtzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUuZnVsbFBhdGh9LiR7cGF0aH1gO1xuXHRcdFx0XHRcdFx0XHRpZiAodGhpcy5ncmFwaC5maW5kVHlwZShyZWxhdGl2ZVBhdGgpKSB7XG5cdFx0XHRcdFx0XHRcdFx0cmV0dXJuIHJlbGF0aXZlUGF0aDtcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHBhdGg7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIFR3by1hcmcgbG9va3VwOiBsb29rdXAoc291cmNlLCAnVXNlcicpXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIpIHtcblx0XHRcdGNvbnN0IHNvdXJjZUFyZyA9IGFyZ3NbIDAgXTtcblx0XHRcdGNvbnN0IHBhdGhBcmcgPSBhcmdzWyAxIF07XG5cdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihzb3VyY2VBcmcpIHx8ICF0cy5pc1N0cmluZ0xpdGVyYWwocGF0aEFyZykpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHNvdXJjZU5hbWUgPSBzb3VyY2VBcmcudGV4dDtcblx0XHRcdGNvbnN0IHBhdGggPSBwYXRoQXJnLnRleHQ7XG5cdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKHNvdXJjZU5hbWUpO1xuXHRcdFx0aWYgKHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKSB7XG5cdFx0XHRcdHJldHVybiB0aGlzLnByZWZpeENvbGxlY3Rpb25QYXRoKHBhdGgsIHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKTtcblx0XHRcdH1cblx0XHRcdGlmIChzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUpIHtcblx0XHRcdFx0Y29uc3QgcmVsYXRpdmVQYXRoID0gYCR7c291cmNlQ29udGV4dC5wYXJlbnRUeXBlLmZ1bGxQYXRofS4ke3BhdGh9YDtcblx0XHRcdFx0aWYgKHRoaXMuZ3JhcGguZmluZFR5cGUocmVsYXRpdmVQYXRoKSkge1xuXHRcdFx0XHRcdHJldHVybiByZWxhdGl2ZVBhdGg7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHBhdGg7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gcGF0aDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBGaW5kIGEgcGFyZW50IHR5cGUgYnkgaXRzIG5hbWUsIHNlYXJjaGluZyBpbiB0aGUgZ3JhcGguXG5cdFx0KiBXaGVuIGNvbGxlY3Rpb25JZCBpcyBwcm92aWRlZCwgb25seSB0eXBlcyBmcm9tIHRoYXQgY29sbGVjdGlvbiBhcmUgY29uc2lkZXJlZC5cblx0XHQqL1xuXHRwcml2YXRlIGZpbmRQYXJlbnRUeXBlQnlOYW1lIChcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0Y29sbGVjdGlvbklkPzogc3RyaW5nXG5cdCk6IFR5cGVOb2RlIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBtYXRjaGVzQ29sbGVjdGlvbiA9ICh0eXBlOiBUeXBlTm9kZSk6IGJvb2xlYW4gPT4ge1xuXHRcdFx0aWYgKGNvbGxlY3Rpb25JZCA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdHJldHVybiB0eXBlLmNvbGxlY3Rpb25JZCA9PT0gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHR5cGUuY29sbGVjdGlvbklkID09PSBjb2xsZWN0aW9uSWQ7XG5cdFx0fTtcblxuXHRcdC8vIEZpcnN0IHRyeSBleGFjdCBtYXRjaCAoZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzIHVzZSB0aGUgcGxhaW4gZG90dGVkIHBhdGgpXG5cdFx0Y29uc3QgZXhhY3QgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKG5hbWUpO1xuXHRcdGlmIChleGFjdCAmJiBtYXRjaGVzQ29sbGVjdGlvbihleGFjdCkpIHtcblx0XHRcdHJldHVybiBleGFjdDtcblx0XHR9XG5cblx0XHQvLyBUaGVuIHNlYXJjaCB0aHJvdWdoIGFsbCB0eXBlcyBmb3Igb25lIHdpdGggbWF0Y2hpbmcgbmFtZSBhbmQgY29sbGVjdGlvblxuXHRcdGZvciAoY29uc3QgdHlwZSBvZiB0aGlzLmdyYXBoLmdldEFsbFR5cGVzKCkpIHtcblx0XHRcdGlmICh0eXBlLm5hbWUgPT09IG5hbWUgJiYgbWF0Y2hlc0NvbGxlY3Rpb24odHlwZSkpIHtcblx0XHRcdFx0cmV0dXJuIHR5cGU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHRcdCogRmluZCBhIHBhcmVudCB0eXBlIGZyb20gYW4gaWRlbnRpZmllciByZWZlcmVuY2UuXG5cdFx0KiBIYW5kbGVzIGJvdGggYWxpYXNlZCB2YXJpYWJsZXMgKGNvbnN0IFVzZXIgPSBkZWZpbmUoJ1VzZXJFbnRpdHknLCAuLi4pKVxuXHRcdCogYW5kIGRpcmVjdCBjbGFzcy90eXBlIG5hbWVzLlxuXHRcdCovXG5cdHByaXZhdGUgZmluZFBhcmVudFR5cGVCeUlkZW50aWZpZXIgKG5hbWU6IHN0cmluZyk6IFR5cGVOb2RlIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBGaXJzdCBjaGVjayB2YXJpYWJsZSBtYXBwaW5nOiBjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKVxuXHRcdGNvbnN0IG1hcHBlZEZ1bGxQYXRoID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0aWYgKG1hcHBlZEZ1bGxQYXRoKSB7XG5cdFx0XHRjb25zdCBtYXBwZWROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShtYXBwZWRGdWxsUGF0aCk7XG5cdFx0XHRpZiAobWFwcGVkTm9kZSkgcmV0dXJuIG1hcHBlZE5vZGU7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUobmFtZSk7XG5cdFx0cmV0dXJuIHBhcmVudE5vZGU7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IHRoZSBsZWZ0bW9zdCBpZGVudGlmaWVyIG9mIGEgcHJvcGVydHktYWNjZXNzIGNoYWluLlxuXHQgKiBGb3IgYEFwcC5kZWZpbmUoJ1VzZXInKS5kZWZpbmUoJ0FkbWluJylgIHRoaXMgcmV0dXJucyB0aGUgYEFwcGAgaWRlbnRpZmllci5cblx0ICovXG5cdHByaXZhdGUgZ2V0Um9vdElkZW50aWZpZXIgKGV4cHI6IHRzLkV4cHJlc3Npb24pOiB0cy5JZGVudGlmaWVyIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuRXhwcmVzc2lvbiA9IGV4cHI7XG5cdFx0d2hpbGUgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5leHByZXNzaW9uO1xuXHRcdH1cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQpKSB7XG5cdFx0XHRyZXR1cm4gY3VycmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHRcdCogR2V0IHByb3BlcnR5IGNoYWluIGZyb20gbmVzdGVkIGFjY2Vzc1xuXHRcdCovXG5cdHByaXZhdGUgZ2V0UHJvcGVydHlDaGFpbiAoZXhwcjogdHMuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uIHwgdHMuSWRlbnRpZmllcik6IHN0cmluZ1tdIHtcblx0XHRjb25zdCBjaGFpbjogc3RyaW5nW10gPSBbXTtcblxuXHRcdGxldCBjdXJyZW50OiB0cy5FeHByZXNzaW9uID0gZXhwcjtcblx0XHR3aGlsZSAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY3VycmVudCkpIHtcblx0XHRcdGlmIChjdXJyZW50Lm5hbWUpIHtcblx0XHRcdFx0Y2hhaW4udW5zaGlmdChjdXJyZW50Lm5hbWUudGV4dCk7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5leHByZXNzaW9uO1xuXHRcdH1cblxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudCkpIHtcblx0XHRcdGNoYWluLnVuc2hpZnQoY3VycmVudC50ZXh0KTtcblx0XHR9XG5cblx0XHRyZXR1cm4gY2hhaW47XG5cdH1cblxuXHQvKipcblx0ICogRGV0ZXJtaW5lIHRoZSBjb25zdHJ1Y3RvciBleHByZXNzaW9uIGZvciBlaXRoZXIgYSBkZWZpbmUoKSBvciBsYXp5KCkgY2FsbC5cblx0ICogRm9yIGRlZmluZSgpIHRoaXMgaXMgdGhlIGNvbnN0cnVjdCBoYW5kbGVyOyBmb3IgbGF6eSgpIGl0IGlzIHRoZSB2YWx1ZVxuXHQgKiByZXR1cm5lZCBieSB0aGUgbGF6eSBnZXR0ZXIuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24gKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgZXhwciA9IGNhbGwuZXhwcmVzc2lvbjtcblx0XHRjb25zdCBuYW1lID0gdHMuaXNJZGVudGlmaWVyKGV4cHIpXG5cdFx0XHQ/IGV4cHIudGV4dFxuXHRcdFx0OiB0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKVxuXHRcdFx0XHQ/IGV4cHIubmFtZS50ZXh0XG5cdFx0XHRcdDogJyc7XG5cblx0XHRpZiAobmFtZSA9PT0gJ2xhenknKSB7XG5cdFx0XHRjb25zdCBsYXp5QXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRcdGlmICghbGF6eUFyZ3MpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB0aGlzLnVud3JhcExhenlHZXR0ZXIobGF6eUFyZ3MuZ2V0dGVyKTtcblx0XHR9XG5cblx0XHQvLyBkZWZpbmUoKSBjYWxsXG5cdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBNb2Rlcm4gZm9ybTogZGVmaW5lKCdOYW1lJywgaGFuZGxlciwgY29uZmlnPylcblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGFyZ3NbIDAgXSkpIHtcblx0XHRcdHJldHVybiBhcmdzWyAxIF07XG5cdFx0fVxuXG5cdFx0Ly8gTGVnYWN5IGZvcm06IGRlZmluZShmdW5jdGlvbiBOYW1lKCkge30pIG9yIGRlZmluZSgoKSA9PiBjbGFzcyBOYW1lIHt9KVxuXHRcdHJldHVybiBhcmdzWyAwIF07XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gY29uc3RydWN0b3IgZnVuY3Rpb25cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFByb3BlcnRpZXMgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpO1xuXHRcdGlmICghY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRyZXR1cm4gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5leHRyYWN0UHJvcGVydGllc0Zyb21Db25zdHJ1Y3Rvcihjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gYSBjb25zdHJ1Y3RvciBleHByZXNzaW9uIChmdW5jdGlvbiwgYXJyb3csIG9yIGNsYXNzKS5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFByb3BlcnRpZXNGcm9tQ29uc3RydWN0b3IgKGNvbnN0cnVjdG9yRXhwcjogdHMuRXhwcmVzc2lvbik6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Ly8gQnVpbGQgdHlwZSBtYXAgZnJvbSBkYXRhIHBhcmFtZXRlciAoZm9yIHRoaXMueCA9IGRhdGEueCBwYXR0ZXJucylcblx0XHRjb25zdCBkYXRhVHlwZU1hcCA9IHRoaXMuYnVpbGREYXRhVHlwZU1hcChjb25zdHJ1Y3RvckV4cHIpO1xuXG5cdFx0Ly8gSGFuZGxlIGZ1bmN0aW9uIGV4cHJlc3Npb25cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSB8fCB0cy5pc0Fycm93RnVuY3Rpb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBjb25zdHJ1Y3RvckV4cHI7XG5cblx0XHRcdC8vIEZpcnN0LCBleHRyYWN0IHByb3BlcnRpZXMgZnJvbSBgdGhpc2AgcGFyYW1ldGVyIHR5cGUgYW5ub3RhdGlvblxuXHRcdFx0Ly8gVGhpcyBoYW5kbGVzIHBhdHRlcm5zIGxpa2U6IGZ1bmN0aW9uKHRoaXM6IFNvbWVUeXBlLCBkYXRhOiBTb21lVHlwZSkgeyB9XG5cdFx0XHRjb25zdCB0aGlzUGFyYW1Qcm9wZXJ0aWVzID0gdGhpcy5leHRyYWN0VGhpc1BhcmFtUHJvcGVydGllcyhjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0Zm9yIChjb25zdCBbIG5hbWUsIHByb3BJbmZvIF0gb2YgdGhpc1BhcmFtUHJvcGVydGllcykge1xuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCBwcm9wSW5mbyk7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEZ1bmN0aW9uIGJvZHkgd2l0aCBzdGF0ZW1lbnRzXG5cdFx0XHRpZiAodHMuaXNCbG9jayhib2R5KSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IHN0bXQgb2YgYm9keS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdFx0aWYgKHRzLmlzRXhwcmVzc2lvblN0YXRlbWVudChzdG10KSkge1xuXHRcdFx0XHRcdFx0dGhpcy5leHRyYWN0UHJvcGVydHlGcm9tU3RhdGVtZW50KHN0bXQuZXhwcmVzc2lvbiwgcHJvcGVydGllcywgZGF0YVR5cGVNYXApO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIEhhbmRsZSBjbGFzcyBleHByZXNzaW9uXG5cdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikpIHtcblx0XHRcdC8vIEZpcnN0IHBhc3M6IGNvbGxlY3QgYWxsIHByb3BlcnR5IHR5cGVzIGZvciBtZXRob2QgaW5mZXJlbmNlXG5cdFx0XHRjb25zdCBjbGFzc1Byb3BlcnR5VHlwZXMgPSB0aGlzLmV4dHJhY3RDbGFzc1Byb3BlcnR5VHlwZXMoY29uc3RydWN0b3JFeHByKTtcblxuXHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgY29uc3RydWN0b3JFeHByLm1lbWJlcnMpIHtcblx0XHRcdFx0Ly8gSGFuZGxlIHByb3BlcnR5IGRlY2xhcmF0aW9uc1xuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eURlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUpIHtcblx0XHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBwcm9wZXJ0aWVzXG5cdFx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0XHRcdG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkO1xuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblxuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpID8gbWVtYmVyLm5hbWUudGV4dCA6ICcnO1xuXHRcdFx0XHRcdGlmIChuYW1lKSB7XG5cdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHRcdHR5cGUgICAgIDogdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpLFxuXHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBIYW5kbGUgbWV0aG9kIGRlY2xhcmF0aW9uc1xuXHRcdFx0XHRpZiAodHMuaXNNZXRob2REZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBtZXRob2RzXG5cdFx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0XHRcdG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkO1xuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblxuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyTWV0aG9kVHlwZShtZW1iZXIsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gSGFuZGxlIGdldHRlciBkZWNsYXJhdGlvbnNcblx0XHRcdFx0aWYgKHRzLmlzR2V0QWNjZXNzb3IobWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgZ2V0dGVyc1xuXHRcdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdFx0XHRtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZDtcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cblx0XHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHQvLyBGaXJzdCB0cnkgZXhwbGljaXQgdHlwZSBhbm5vdGF0aW9uLCB0aGVuIGluZmVyIGZyb20gZ2V0dGVyIGJvZHlcblx0XHRcdFx0XHRsZXQgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRpZiAodHlwZSA9PT0gJ3Vua25vd24nICYmIG1lbWJlci5ib2R5KSB7XG5cdFx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclJldHVyblR5cGVGcm9tQm9keShtZW1iZXIuYm9keSwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0cmVhZG9ubHkgOiB0cnVlLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHQvKipcblx0ICogQnVpbGQgYSB0eXBlIG1hcCBmcm9tIGFsbCBwYXJhbWV0ZXJzIHdpdGggaW5saW5lIG9iamVjdCB0eXBlIGFubm90YXRpb25zXG5cdCAqIFJldHVybnMgYSBtYXAgb2YgXCJwYXJhbU5hbWUucHJvcGVydHlOYW1lXCIgLT4gdHlwZVxuXHQgKi9cblx0cHJpdmF0ZSBidWlsZERhdGFUeXBlTWFwIChoYW5kbGVyQXJnOiB0cy5FeHByZXNzaW9uKTogTWFwPHN0cmluZywgc3RyaW5nPiB7XG5cdFx0Y29uc3QgdHlwZU1hcCA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cblx0XHRpZiAoIXRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGhhbmRsZXJBcmcpICYmICF0cy5pc0Fycm93RnVuY3Rpb24oaGFuZGxlckFyZykpIHtcblx0XHRcdHJldHVybiB0eXBlTWFwO1xuXHRcdH1cblxuXHRcdC8vIEl0ZXJhdGUgb3ZlciBBTEwgcGFyYW1ldGVyc1xuXHRcdGZvciAoY29uc3QgcGFyYW0gb2YgaGFuZGxlckFyZy5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRpZiAoIXBhcmFtLm5hbWUgfHwgIXBhcmFtLnR5cGUpIGNvbnRpbnVlO1xuXG5cdFx0XHQvLyBHZXQgcGFyYW1ldGVyIG5hbWVcblx0XHRcdGxldCBwYXJhbU5hbWUgPSAnJztcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkpIHtcblx0XHRcdFx0cGFyYW1OYW1lID0gcGFyYW0ubmFtZS50ZXh0O1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29udGludWU7IC8vIFNraXAgZGVzdHJ1Y3R1cmVkIHBhcmFtZXRlcnMgZm9yIG5vd1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBDaGVjayBpZiBpdCdzIGFuIGlubGluZSBvYmplY3QgdHlwZSBsaXRlcmFsXG5cdFx0XHRpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUocGFyYW0udHlwZSkpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgcGFyYW0udHlwZS5tZW1iZXJzKSB7XG5cdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQoYCR7cGFyYW1OYW1lfS4ke3Byb3BOYW1lfWAsIHR5cGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Ly8gU3RvcmUgc2ltcGxlIHBhcmFtZXRlciB0eXBlcyBsaWtlIGBkZWNvcmF0ZVZhbHVlOiBzdHJpbmdgXG5cdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblx0XHRcdFx0aWYgKHR5cGUgIT09ICd1bmtub3duJykge1xuXHRcdFx0XHRcdHR5cGVNYXAuc2V0KHBhcmFtTmFtZSwgdHlwZSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdHlwZU1hcDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnR5IGFjY2VzcyBjaGFpbiAoZS5nLiwgXCJkYXRhUmVuYW1lZC5pZFwiIGZyb20gZGF0YVJlbmFtZWQuaWQpXG5cdCAqIEhhbmRsZXMgZmFsbGJhY2tzIGxpa2U6IGRhdGEucGVybWlzc2lvbnMgfHwgW11cblx0ICovXG5cdHByaXZhdGUgZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbiAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gSGFuZGxlIGlkZW50aWZpZXI6IGRhdGFcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci50ZXh0O1xuXHRcdH1cblx0XHQvLyBIYW5kbGUgcHJvcGVydHkgYWNjZXNzOiBkYXRhLnBlcm1pc3Npb25zXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBiYXNlID0gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGV4cHIuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoYmFzZSkge1xuXHRcdFx0XHRyZXR1cm4gYCR7YmFzZX0uJHtleHByLm5hbWUudGV4dH1gO1xuXHRcdFx0fVxuXHRcdH1cblx0XHQvLyBIYW5kbGUgZmFsbGJhY2sgcGF0dGVybjogZGF0YS5wZXJtaXNzaW9ucyB8fCBbXVxuXHRcdGlmICh0cy5pc0JpbmFyeUV4cHJlc3Npb24oZXhwcikgJiZcblx0XHRcdGV4cHIub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkJhckJhclRva2VuKSB7XG5cdFx0XHQvLyBSZXR1cm4gdGhlIGxlZnQgc2lkZSBvZiB8fCBvcGVyYXRvclxuXHRcdFx0cmV0dXJuIHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihleHByLmxlZnQpO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydHkgYXNzaWdubWVudCBmcm9tIHN0YXRlbWVudFxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UHJvcGVydHlGcm9tU3RhdGVtZW50IChcblx0XHRleHByOiB0cy5FeHByZXNzaW9uLFxuXHRcdHByb3BlcnRpZXM6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4sXG5cdFx0ZGF0YVR5cGVNYXA6IE1hcDxzdHJpbmcsIHN0cmluZz4gPSBuZXcgTWFwKClcblx0KTogdm9pZCB7XG5cdFx0Ly8gSGFuZGxlOiB0aGlzLnByb3BlcnR5ID0gdmFsdWVcblx0XHRpZiAodHMuaXNCaW5hcnlFeHByZXNzaW9uKGV4cHIpICYmXG5cdFx0XHRleHByLm9wZXJhdG9yVG9rZW4ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbikge1xuXHRcdFx0Y29uc3QgeyBsZWZ0IH0gPSBleHByO1xuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obGVmdCkpIHtcblx0XHRcdFx0Ly8gQ2hlY2sgaWYgYWNjZXNzaW5nICd0aGlzJyAoVGhpc0tleXdvcmQpXG5cdFx0XHRcdGlmIChsZWZ0LmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBsZWZ0Lm5hbWU/LnRleHQ7XG5cdFx0XHRcdFx0aWYgKG5hbWUpIHtcblx0XHRcdFx0XHRcdC8vIFRyeSB0byBnZXQgdHlwZSBmcm9tIGRhdGFUeXBlTWFwIHVzaW5nIGZ1bGwgYWNjZXNzIGNoYWluIChlLmcuLCBcImRhdGFSZW5hbWVkLmlkXCIpXG5cdFx0XHRcdFx0XHRjb25zdCBhY2Nlc3NDaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihleHByLnJpZ2h0KTtcblx0XHRcdFx0XHRcdGxldCB0eXBlID0gYWNjZXNzQ2hhaW4gPyBkYXRhVHlwZU1hcC5nZXQoYWNjZXNzQ2hhaW4pIDogdW5kZWZpbmVkO1xuXHRcdFx0XHRcdFx0Ly8gSWYgbm90IGZvdW5kIGFuZCBSSFMgaXMgYSBzaW1wbGUgaWRlbnRpZmllciwgdHJ5IGxvb2tpbmcgaXQgdXAgZGlyZWN0bHlcblx0XHRcdFx0XHRcdGlmICghdHlwZSAmJiB0cy5pc0lkZW50aWZpZXIoZXhwci5yaWdodCkpIHtcblx0XHRcdFx0XHRcdFx0dHlwZSA9IGRhdGFUeXBlTWFwLmdldChleHByLnJpZ2h0LnRleHQpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKCF0eXBlKSB7XG5cdFx0XHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihleHByLnJpZ2h0LCBkYXRhVHlwZU1hcCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHQvLyBEb24ndCBvdmVyd3JpdGUgYSBrbm93biB0eXBlIGZyb20gYSBgdGhpc2AgYW5ub3RhdGlvblxuXHRcdFx0XHRcdFx0Ly8gd2l0aCBhbiB1bmtub3duLWJlYXJpbmcgaW5mZXJlbmNlOiBhbiBlbXB0eS1hcnJheVxuXHRcdFx0XHRcdFx0Ly8gaW5pdGlhbGl6ZXIgaW5mZXJzICdBcnJheTx1bmtub3duPicsIHdoaWNoIG11c3Qgbm90XG5cdFx0XHRcdFx0XHQvLyBjbG9iYmVyIGFuIGFubm90YXRlZCAnQXJyYXk8eyBpZDogbnVtYmVyIH0+JyBlaXRoZXJcblx0XHRcdFx0XHRcdGNvbnN0IGV4aXN0aW5nID0gcHJvcGVydGllcy5nZXQobmFtZSk7XG5cdFx0XHRcdFx0XHRjb25zdCB0eXBlSGFzVW5rbm93biA9ICF0eXBlIHx8IHR5cGUuaW5jbHVkZXMoJ3Vua25vd24nKTtcblx0XHRcdFx0XHRcdGNvbnN0IGV4aXN0aW5nSXNLbm93biA9IGV4aXN0aW5nID8gIWV4aXN0aW5nLnR5cGUuaW5jbHVkZXMoJ3Vua25vd24nKSA6IGZhbHNlO1xuXHRcdFx0XHRcdFx0aWYgKGV4aXN0aW5nSXNLbm93biAmJiB0eXBlSGFzVW5rbm93bikge1xuXHRcdFx0XHRcdFx0XHQvLyBLZWVwIHRoZSBiZXR0ZXIgdHlwZSBmcm9tIGV4cGxpY2l0IGFubm90YXRpb25cblx0XHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gSGFuZGxlOiBPYmplY3QuYXNzaWduKHRoaXMsIHsgcHJvcDogdmFsdWUgfSlcblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0Y29uc3QgZm4gPSBleHByLmV4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZm4pICYmXG5cdFx0XHRcdGZuLm5hbWU/LnRleHQgPT09ICdhc3NpZ24nICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihmbi5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHRmbi5leHByZXNzaW9uLnRleHQgPT09ICdPYmplY3QnKSB7XG5cdFx0XHRcdGNvbnN0IGFyZ3MgPSBleHByLmFyZ3VtZW50cztcblx0XHRcdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIgJiYgYXJnc1sgMCBdLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdFx0XHQvLyBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSB0aGUgc2Vjb25kIGFyZ3VtZW50XG5cdFx0XHRcdFx0Y29uc3QgcHJvcHNBcmcgPSBhcmdzWyAxIF07XG5cdFx0XHRcdFx0aWYgKHRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24ocHJvcHNBcmcpKSB7XG5cdFx0XHRcdFx0XHRmb3IgKGNvbnN0IHByb3Agb2YgcHJvcHNBcmcucHJvcGVydGllcykge1xuXHRcdFx0XHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFzc2lnbm1lbnQocHJvcCkgJiYgdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkpIHtcblx0XHRcdFx0XHRcdFx0XHRjb25zdCBuYW1lID0gcHJvcC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdFx0XHRcdHR5cGUgICAgIDogdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIocHJvcC5pbml0aWFsaXplciksXG5cdFx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGNsYXNzIGRlY2xhcmF0aW9uIChpbmNsdWRpbmcgbWV0aG9kcyBhbmQgZ2V0dGVycylcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENsYXNzUHJvcGVydGllcyAoY2xhc3NEZWNsOiB0cy5DbGFzc0RlY2xhcmF0aW9uKTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjbGFzc0RlY2wubWVtYmVycykge1xuXHRcdFx0Ly8gSGFuZGxlIHByb3BlcnR5IGRlY2xhcmF0aW9uc1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlEZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lKSB7XG5cdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIHByb3BlcnRpZXNcblx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdCAgICAgbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQpO1xuXHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpID8gbWVtYmVyLm5hbWUudGV4dCA6ICcnO1xuXHRcdFx0XHRpZiAobmFtZSkge1xuXHRcdFx0XHRcdC8vIElmIG5vIGV4cGxpY2l0IHR5cGUgYnV0IGhhcyBpbml0aWFsaXplciwgaW5mZXIgZnJvbSBpbml0aWFsaXplclxuXHRcdFx0XHRcdGxldCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdGlmICh0eXBlID09PSAndW5rbm93bicgJiYgbWVtYmVyLmluaXRpYWxpemVyKSB7XG5cdFx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIobWVtYmVyLmluaXRpYWxpemVyKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblxuXHRcdFx0Ly8gSGFuZGxlIG1ldGhvZCBkZWNsYXJhdGlvbnNcblx0XHRcdGlmICh0cy5pc01ldGhvZERlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBtZXRob2RzXG5cdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHQgICAgIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkKTtcblx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJNZXRob2RUeXBlKG1lbWJlcik7XG5cdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEhhbmRsZSBnZXR0ZXIgZGVjbGFyYXRpb25zXG5cdFx0XHRpZiAodHMuaXNHZXRBY2Nlc3NvcihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgZ2V0dGVyc1xuXHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0ICAgICBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZCk7XG5cdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdC8vIEZpcnN0IHRyeSBleHBsaWNpdCB0eXBlIGFubm90YXRpb24sIHRoZW4gaW5mZXIgZnJvbSBnZXR0ZXIgYm9keVxuXHRcdFx0XHRsZXQgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0aWYgKHR5cGUgPT09ICd1bmtub3duJyAmJiBtZW1iZXIuYm9keSkge1xuXHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyUmV0dXJuVHlwZUZyb21Cb2R5KG1lbWJlci5ib2R5KTtcblx0XHRcdFx0fVxuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0cmVhZG9ubHkgOiB0cnVlLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGNsYXNzIHByb3BlcnR5IHR5cGVzIGZvciBtZXRob2QgcmV0dXJuIHR5cGUgaW5mZXJlbmNlXG5cdCAqIE1hcHMgcHJvcGVydHkgbmFtZXMgdG8gdGhlaXIgVHlwZVNjcmlwdCB0eXBlIHN0cmluZ3Ncblx0ICogTm90ZTogSW5jbHVkZXMgcHJpdmF0ZS9wcm90ZWN0ZWQgcHJvcGVydGllcyBmb3IgbWV0aG9kIGluZmVyZW5jZVxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q2xhc3NQcm9wZXJ0eVR5cGVzIChjbGFzc0RlY2w6IHRzLkNsYXNzRXhwcmVzc2lvbik6IE1hcDxzdHJpbmcsIHN0cmluZz4ge1xuXHRcdGNvbnN0IHByb3BlcnR5VHlwZXMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXG5cdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgY2xhc3NEZWNsLm1lbWJlcnMpIHtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5RGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdC8vIEluY2x1ZGUgQUxMIHByb3BlcnRpZXMgKGV2ZW4gcHJpdmF0ZSkgZm9yIG1ldGhvZCByZXR1cm4gdHlwZSBpbmZlcmVuY2Vcblx0XHRcdFx0Ly8gVGhlIHZpc2liaWxpdHkgY2hlY2sgaXMgZG9uZSB3aGVuIGFkZGluZyB0byBvdXRwdXQgcHJvcGVydGllc1xuXHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0aWYgKG1lbWJlci50eXBlKSB7XG5cdFx0XHRcdFx0cHJvcGVydHlUeXBlcy5zZXQobmFtZSwgdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBwcm9wZXJ0eVR5cGVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEluZmVyIG1ldGhvZCB0eXBlIGZyb20gbWV0aG9kIGRlY2xhcmF0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGluZmVyTWV0aG9kVHlwZSAobWV0aG9kOiB0cy5NZXRob2REZWNsYXJhdGlvbiwgY2xhc3NQcm9wZXJ0eVR5cGVzPzogTWFwPHN0cmluZywgc3RyaW5nPik6IHN0cmluZyB7XG5cdFx0Y29uc3QgcGFyYW1zID0gbWV0aG9kLnBhcmFtZXRlcnMubWFwKHBhcmFtID0+IHtcblx0XHRcdGNvbnN0IHBhcmFtTmFtZSA9IHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSA/IHBhcmFtLm5hbWUudGV4dCA6ICdhcmcnO1xuXHRcdFx0Y29uc3QgcGFyYW1UeXBlID0gdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cdFx0XHRyZXR1cm4gYCR7cGFyYW1OYW1lfTogJHtwYXJhbVR5cGV9YDtcblx0XHR9KS5qb2luKCcsICcpO1xuXG5cdFx0Y29uc3QgcmV0dXJuVHlwZSA9IHRoaXMuaW5mZXJSZXR1cm5UeXBlKG1ldGhvZCwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblxuXHRcdGlmIChwYXJhbXMpIHtcblx0XHRcdHJldHVybiBgKCR7cGFyYW1zfSkgPT4gJHtyZXR1cm5UeXBlfWA7XG5cdFx0fVxuXHRcdHJldHVybiBgKCkgPT4gJHtyZXR1cm5UeXBlfWA7XG5cdH1cblxuXHQvKipcblx0XHQqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGB0aGlzYCBwYXJhbWV0ZXIgdHlwZSBhbm5vdGF0aW9uXG5cdFx0KiBIYW5kbGVzIHBhdHRlcm5zIGxpa2U6IGZ1bmN0aW9uKHRoaXM6IFNvbWVUeXBlLCBkYXRhOiBTb21lVHlwZSkgeyB9XG5cdFx0Ki9cblx0cHJpdmF0ZSBleHRyYWN0VGhpc1BhcmFtUHJvcGVydGllcyAoaGFuZGxlckFyZzogdHMuRnVuY3Rpb25FeHByZXNzaW9uIHwgdHMuQXJyb3dGdW5jdGlvbik6XG5cdFx0TWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cblx0XHQvLyBGaW5kIHRoZSBgdGhpc2AgcGFyYW1ldGVyIChpZiBhbnkpXG5cdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBoYW5kbGVyQXJnLnBhcmFtZXRlcnMpIHtcblx0XHRcdGlmIChwYXJhbS5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSAmJiBwYXJhbS5uYW1lLnRleHQgPT09ICd0aGlzJyAmJiBwYXJhbS50eXBlKSB7XG5cdFx0XHRcdC8vIENoZWNrIGlmIGl0J3MgYSB0eXBlIHJlZmVyZW5jZSAoZS5nLiwgYHRoaXM6IHVzYWdlYClcblx0XHRcdFx0aWYgKHRzLmlzVHlwZVJlZmVyZW5jZU5vZGUocGFyYW0udHlwZSkpIHtcblx0XHRcdFx0XHRjb25zdCB0eXBlTmFtZSA9IHRzLmlzSWRlbnRpZmllcihwYXJhbS50eXBlLnR5cGVOYW1lKVxuXHRcdFx0XHRcdFx0PyBwYXJhbS50eXBlLnR5cGVOYW1lLnRleHRcblx0XHRcdFx0XHRcdDogJyc7XG5cblx0XHRcdFx0XHQvLyBMb29rIHVwIHRoZSB0eXBlIGFsaWFzIGluIG91ciBjb2xsZWN0ZWQgdHlwZSBhbGlhc2VzXG5cdFx0XHRcdFx0Y29uc3QgYWxpYXNlZFR5cGUgPSB0aGlzLnR5cGVBbGlhc2VzLmdldCh0eXBlTmFtZSk7XG5cdFx0XHRcdFx0aWYgKGFsaWFzZWRUeXBlICYmIHRzLmlzVHlwZUxpdGVyYWxOb2RlKGFsaWFzZWRUeXBlKSkge1xuXHRcdFx0XHRcdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gdGhlIHR5cGUgbGl0ZXJhbFxuXHRcdFx0XHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgYWxpYXNlZFR5cGUubWVtYmVycykge1xuXHRcdFx0XHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChwcm9wTmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdFx0bmFtZSAgICAgOiBwcm9wTmFtZSxcblx0XHRcdFx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gQ2hlY2sgaWYgaXQncyBkaXJlY3RseSBhbiBpbmxpbmUgdHlwZSBsaXRlcmFsIChlLmcuLCBgdGhpczogeyBpZDogc3RyaW5nIH1gKVxuXHRcdFx0XHRlbHNlIGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZShwYXJhbS50eXBlKSkge1xuXHRcdFx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIHBhcmFtLnR5cGUubWVtYmVycykge1xuXHRcdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQocHJvcE5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRuYW1lICAgICA6IHByb3BOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0YnJlYWs7IC8vIEZvdW5kIHRoZSBgdGhpc2AgcGFyYW1ldGVyLCBubyBuZWVkIHRvIGNvbnRpbnVlXG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHQvKipcblx0XHQqIEluZmVyIFR5cGVTY3JpcHQgdHlwZSBmcm9tIHR5cGUgbm9kZVxuXHRcdCovXG5cdC8qKlxuXHQgKiBJbmZlciBUeXBlU2NyaXB0IHR5cGUgZnJvbSB0eXBlIG5vZGVcblx0ICovXG5cdHByaXZhdGUgaW5mZXJUeXBlICh0eXBlTm9kZT86IHRzLlR5cGVOb2RlKTogc3RyaW5nIHtcblx0XHRpZiAoIXR5cGVOb2RlKSB7XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblxuXHRcdHN3aXRjaCAodHlwZU5vZGUua2luZCkge1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5TdHJpbmdLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdW1iZXJLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Cb29sZWFuS2V5d29yZDpcblx0XHRcdHJldHVybiAnYm9vbGVhbic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVuZGVmaW5lZEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3VuZGVmaW5lZCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bGxLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdudWxsJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQW55S2V5d29yZDpcblx0XHRcdHJldHVybiAnYW55Jztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5rbm93bktleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Wb2lkS2V5d29yZDpcblx0XHRcdHJldHVybiAndm9pZCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkFycmF5VHlwZTpcblx0XHRcdHJldHVybiBgQXJyYXk8JHsgIHRoaXMuaW5mZXJUeXBlKCh0eXBlTm9kZSBhcyB0cy5BcnJheVR5cGVOb2RlKS5lbGVtZW50VHlwZSkgIH0+YDtcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZUxpdGVyYWw6IHtcblx0XHRcdC8vIElubGluZS1leHBhbmQgdHlwZSBsaXRlcmFscyBpbnN0ZWFkIG9mIGNvbGxhcHNpbmcgdG8gJ29iamVjdCdcblx0XHRcdGNvbnN0IHR5cGVMaXQgPSB0eXBlTm9kZSBhcyB0cy5UeXBlTGl0ZXJhbE5vZGU7XG5cdFx0XHRjb25zdCBwcm9wczogc3RyaW5nW10gPSBbXTtcblx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIHR5cGVMaXQubWVtYmVycykge1xuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Y29uc3Qgb3B0aW9uYWwgPSBtZW1iZXIucXVlc3Rpb25Ub2tlbiA/ICc/JyA6ICcnO1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0cHJvcHMucHVzaChgJHtwcm9wTmFtZX0ke29wdGlvbmFsfTogJHt0eXBlfWApO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gYHsgJHtwcm9wcy5qb2luKCc7ICcpfSB9YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkxpdGVyYWxUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgc3RyaW5nIGxpdGVyYWwgdHlwZXMgbGlrZSAndXNlcicsICdhZG1pbicsIGV0Yy5cblx0XHRcdGNvbnN0IHsgbGl0ZXJhbCB9ID0gKHR5cGVOb2RlIGFzIHRzLkxpdGVyYWxUeXBlTm9kZSk7XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGxpdGVyYWwpKSB7XG5cdFx0XHRcdC8vIFJldHVybiB0aGUgYWN0dWFsIGxpdGVyYWwgdmFsdWUgKGUuZy4sICd1c2VyJyBpbnN0ZWFkIG9mIHN0cmluZylcblx0XHRcdFx0cmV0dXJuIGAnJHtsaXRlcmFsLnRleHR9J2A7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNOdW1lcmljTGl0ZXJhbChsaXRlcmFsKSkge1xuXHRcdFx0XHRyZXR1cm4gbGl0ZXJhbC50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0aWYgKGxpdGVyYWwua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCkge1xuXHRcdFx0XHRyZXR1cm4gJ3RydWUnO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGxpdGVyYWwua2luZCA9PT0gdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQpIHtcblx0XHRcdFx0cmV0dXJuICdmYWxzZSc7XG5cdFx0XHR9XG5cdFx0XHRpZiAobGl0ZXJhbC5raW5kID09PSB0cy5TeW50YXhLaW5kLk51bGxLZXl3b3JkKSB7XG5cdFx0XHRcdHJldHVybiAnbnVsbCc7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZVJlZmVyZW5jZToge1xuXHRcdFx0Ly8gSGFuZGxlIHR5cGUgcmVmZXJlbmNlcyBsaWtlIE1hcDxzdHJpbmcsIG51bWJlcj4sIFByb3BlcnR5SW5mbywgZXRjLlxuXHRcdFx0Y29uc3QgdHlwZVJlZiA9IHR5cGVOb2RlIGFzIHRzLlR5cGVSZWZlcmVuY2VOb2RlO1xuXHRcdFx0Y29uc3QgdHlwZU5hbWUgPSB0cy5pc0lkZW50aWZpZXIodHlwZVJlZi50eXBlTmFtZSlcblx0XHRcdFx0PyB0eXBlUmVmLnR5cGVOYW1lLnRleHRcblx0XHRcdFx0OiB0cy5pc1F1YWxpZmllZE5hbWUodHlwZVJlZi50eXBlTmFtZSlcblx0XHRcdFx0XHQ/IHRoaXMuZ2V0UXVhbGlmaWVkTmFtZVRleHQodHlwZVJlZi50eXBlTmFtZSlcblx0XHRcdFx0XHQ6ICd1bmtub3duJztcblxuXHRcdFx0Ly8gQ2hlY2sgaWYgdGhpcyBpcyBhIHR5cGUgYWxpYXMgd2UgY2FuIHJlc29sdmVcblx0XHRcdGNvbnN0IGFsaWFzZWRUeXBlID0gdGhpcy50eXBlQWxpYXNlcy5nZXQodHlwZU5hbWUpO1xuXHRcdFx0aWYgKGFsaWFzZWRUeXBlKSB7XG5cdFx0XHRcdC8vIFJlc29sdmUgdGhlIHR5cGUgYWxpYXNcblx0XHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJUeXBlKGFsaWFzZWRUeXBlKTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gSGFuZGxlIEluc3RhbmNlVHlwZTx0eXBlb2YgWD4gcGF0dGVybiAtPiBjb252ZXJ0IHRvIFBhcmVudF9YXG5cdFx0XHRpZiAodHlwZU5hbWUgPT09ICdJbnN0YW5jZVR5cGUnICYmIHR5cGVSZWYudHlwZUFyZ3VtZW50cyAmJiB0eXBlUmVmLnR5cGVBcmd1bWVudHMubGVuZ3RoID09PSAxKSB7XG5cdFx0XHRcdGNvbnN0IGFyZyA9IHR5cGVSZWYudHlwZUFyZ3VtZW50c1sgMCBdO1xuXHRcdFx0XHRpZiAoYXJnLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVHlwZVF1ZXJ5KSB7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZVF1ZXJ5ID0gYXJnIGFzIHRzLlR5cGVRdWVyeU5vZGU7XG5cdFx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcih0eXBlUXVlcnkuZXhwck5hbWUpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBxdWVyeVR5cGVOYW1lID0gdHlwZVF1ZXJ5LmV4cHJOYW1lLnRleHQ7XG5cdFx0XHRcdFx0XHQvLyBMb29rIHVwIHRoZSB0eXBlIGluIHRoZSBncmFwaCB0byBnZXQgZnVsbCBwYXRoXG5cdFx0XHRcdFx0XHRjb25zdCBtYXRjaGVkVHlwZSA9IHRoaXMuZ3JhcGguZmluZFR5cGVCeU5hbWUocXVlcnlUeXBlTmFtZSk7XG5cdFx0XHRcdFx0XHRpZiAobWF0Y2hlZFR5cGUpIHtcblx0XHRcdFx0XHRcdFx0Ly8gQ29udmVydCBmdWxsIHBhdGggd2l0aCBkb3RzIHRvIHVuZGVyc2NvcmVzOiBVc2FnZXMuVXNhZ2VFbnRyeSAtPiBVc2FnZXNfVXNhZ2VFbnRyeVxuXHRcdFx0XHRcdFx0XHRyZXR1cm4gbWF0Y2hlZFR5cGUuZnVsbFBhdGgucmVwbGFjZSgvXFwuL2csICdfJyk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHQvLyBGYWxsYmFjazoganVzdCB1c2UgdGhlIHR5cGUgbmFtZSBpZiBub3QgZm91bmQgaW4gZ3JhcGhcblx0XHRcdFx0XHRcdHJldHVybiBxdWVyeVR5cGVOYW1lO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHRpZiAoIXR5cGVSZWYudHlwZUFyZ3VtZW50cyB8fCB0eXBlUmVmLnR5cGVBcmd1bWVudHMubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRcdC8vIENoZWNrIGlmIHRoaXMgdHlwZSBleGlzdHMgaW4gb3VyIGdyYXBoIC0gY29udmVydCB0byBmdWxsIHBhdGggZm9ybWF0XG5cdFx0XHRcdGNvbnN0IG1hdGNoZWRUeXBlID0gdGhpcy5ncmFwaC5maW5kVHlwZUJ5TmFtZSh0eXBlTmFtZSk7XG5cdFx0XHRcdGlmIChtYXRjaGVkVHlwZSkge1xuXHRcdFx0XHRcdC8vIENvbnZlcnQgZnVsbCBwYXRoIHdpdGggZG90cyB0byB1bmRlcnNjb3JlczogVXNhZ2VzLlVzYWdlRW50cnkgLT4gVXNhZ2VzX1VzYWdlRW50cnlcblx0XHRcdFx0XHRyZXR1cm4gbWF0Y2hlZFR5cGUuZnVsbFBhdGgucmVwbGFjZSgvXFwuL2csICdfJyk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHR5cGVOYW1lO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBCdWlsZCBnZW5lcmljIHR5cGUgYXJndW1lbnRzXG5cdFx0XHRjb25zdCB0eXBlQXJncyA9IHR5cGVSZWYudHlwZUFyZ3VtZW50cy5tYXAoYXJnID0+IHRoaXMuaW5mZXJUeXBlKGFyZykpO1xuXHRcdFx0cmV0dXJuIGAke3R5cGVOYW1lfTwke3R5cGVBcmdzLmpvaW4oJywgJyl9PmA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5VbmlvblR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSB1bmlvbiB0eXBlcyBsaWtlICdhJyB8ICdiJyB8ICdjJ1xuXHRcdFx0Y29uc3QgdW5pb25UeXBlID0gdHlwZU5vZGUgYXMgdHMuVW5pb25UeXBlTm9kZTtcblx0XHRcdGNvbnN0IHR5cGVzID0gdW5pb25UeXBlLnR5cGVzLm1hcCh0ID0+IHRoaXMuaW5mZXJUeXBlKHQpKTtcblx0XHRcdHJldHVybiB0eXBlcy5qb2luKCcgfCAnKTtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkludGVyc2VjdGlvblR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBpbnRlcnNlY3Rpb24gdHlwZXMgbGlrZSBUeXBlQSAmIFR5cGVCXG5cdFx0XHRjb25zdCBpbnRlcnNlY3Rpb25UeXBlID0gdHlwZU5vZGUgYXMgdHMuSW50ZXJzZWN0aW9uVHlwZU5vZGU7XG5cdFx0XHRjb25zdCB0eXBlcyA9IGludGVyc2VjdGlvblR5cGUudHlwZXMubWFwKHQgPT4gdGhpcy5pbmZlclR5cGUodCkpO1xuXHRcdFx0cmV0dXJuIHR5cGVzLmpvaW4oJyAmICcpO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHVwbGVUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgdHVwbGUgdHlwZXMgbGlrZSBbc3RyaW5nLCBudW1iZXJdXG5cdFx0XHRjb25zdCB0dXBsZVR5cGUgPSB0eXBlTm9kZSBhcyB0cy5UdXBsZVR5cGVOb2RlO1xuXHRcdFx0Y29uc3QgZWxlbWVudHMgPSB0dXBsZVR5cGUuZWxlbWVudHMubWFwKGVsZW0gPT4gdGhpcy5pbmZlclR5cGUoZWxlbSBhcyB0cy5UeXBlTm9kZSkpO1xuXHRcdFx0cmV0dXJuIGBbJHtlbGVtZW50cy5qb2luKCcsICcpfV1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuT3B0aW9uYWxUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgb3B0aW9uYWwgZWxlbWVudCBpbiB0dXBsZTogc3RyaW5nP1xuXHRcdFx0Y29uc3Qgb3B0aW9uYWxUeXBlID0gdHlwZU5vZGUgYXMgdHMuT3B0aW9uYWxUeXBlTm9kZTtcblx0XHRcdHJldHVybiBgJHt0aGlzLmluZmVyVHlwZShvcHRpb25hbFR5cGUudHlwZSkgIH0/YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlJlc3RUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgcmVzdCBlbGVtZW50OiAuLi5UXG5cdFx0XHRjb25zdCByZXN0VHlwZSA9IHR5cGVOb2RlIGFzIHRzLlJlc3RUeXBlTm9kZTtcblx0XHRcdHJldHVybiBgLi4uJHsgIHRoaXMuaW5mZXJUeXBlKHJlc3RUeXBlLnR5cGUpfWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5QYXJlbnRoZXNpemVkVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHBhcmVudGhlc2l6ZWQgdHlwZXM6IChBIHwgQilcblx0XHRcdHJldHVybiB0aGlzLmluZmVyVHlwZSgodHlwZU5vZGUgYXMgdHMuUGFyZW50aGVzaXplZFR5cGVOb2RlKS50eXBlKTtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkluZGV4ZWRBY2Nlc3NUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgaW5kZXhlZCBhY2Nlc3M6IFRbS11cblx0XHRcdGNvbnN0IGluZGV4ZWQgPSB0eXBlTm9kZSBhcyB0cy5JbmRleGVkQWNjZXNzVHlwZU5vZGU7XG5cdFx0XHRsZXQgb2JqZWN0VHlwZSA9IHRoaXMuaW5mZXJUeXBlKGluZGV4ZWQub2JqZWN0VHlwZSk7XG5cdFx0XHRjb25zdCBpbmRleFR5cGUgPSB0aGlzLmluZmVyVHlwZShpbmRleGVkLmluZGV4VHlwZSk7XG5cdFx0XHQvLyBJZiBvYmplY3RUeXBlIGlzICdvYmplY3QnLCB0cnkgdG8gcmVzb2x2ZSB0aGUgdW5kZXJseWluZyB0eXBlIGFsaWFzXG5cdFx0XHRpZiAob2JqZWN0VHlwZSA9PT0gJ29iamVjdCcgJiYgdHMuaXNUeXBlUmVmZXJlbmNlTm9kZShpbmRleGVkLm9iamVjdFR5cGUpKSB7XG5cdFx0XHRcdGNvbnN0IHJlZk5hbWUgPSB0cy5pc0lkZW50aWZpZXIoaW5kZXhlZC5vYmplY3RUeXBlLnR5cGVOYW1lKSA/IGluZGV4ZWQub2JqZWN0VHlwZS50eXBlTmFtZS50ZXh0IDogJyc7XG5cdFx0XHRcdGNvbnN0IGFsaWFzZWQgPSB0aGlzLnR5cGVBbGlhc2VzLmdldChyZWZOYW1lKTtcblx0XHRcdFx0aWYgKGFsaWFzZWQpIHtcblx0XHRcdFx0XHRvYmplY3RUeXBlID0gdGhpcy5pbmZlclR5cGUoYWxpYXNlZCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiBgJHtvYmplY3RUeXBlfVske2luZGV4VHlwZX1dYDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR5cGVPcGVyYXRvcjoge1xuXHRcdFx0Ly8gSGFuZGxlIGtleW9mLCByZWFkb25seSwgdW5pcXVlIG9wZXJhdG9yc1xuXHRcdFx0Y29uc3QgdHlwZU9wID0gdHlwZU5vZGUgYXMgdHMuVHlwZU9wZXJhdG9yTm9kZTtcblx0XHRcdGNvbnN0IG9wZXJhdG9yID0gdHMuU3ludGF4S2luZFsgdHlwZU9wLm9wZXJhdG9yIF07XG5cdFx0XHRyZXR1cm4gYCR7b3BlcmF0b3J9ICR7dGhpcy5pbmZlclR5cGUodHlwZU9wLnR5cGUpfWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlUXVlcnk6IHtcblx0XHRcdC8vIEhhbmRsZSB0eXBlb2YgZXhwcmVzc2lvbnMgbGlrZSBgdHlwZW9mIFVzYWdlRW50cnlgXG5cdFx0XHRjb25zdCB0eXBlUXVlcnkgPSB0eXBlTm9kZSBhcyB0cy5UeXBlUXVlcnlOb2RlO1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcih0eXBlUXVlcnkuZXhwck5hbWUpKSB7XG5cdFx0XHRcdHJldHVybiBgdHlwZW9mICR7dHlwZVF1ZXJ5LmV4cHJOYW1lLnRleHR9YDtcblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGRlZmF1bHQ6XG5cdFx0XHQvLyBGb3IgY29tcGxleCB0eXBlcywgcmV0dXJuIHRoZSB0ZXh0IHJlcHJlc2VudGF0aW9uXG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdCogSW5mZXIgcmV0dXJuIHR5cGUgZnJvbSBhIG1ldGhvZCBkZWNsYXJhdGlvblxuXHRcdCogVXNlcyBleHBsaWNpdCByZXR1cm4gdHlwZSBhbm5vdGF0aW9uIG9yIGluZmVycyBmcm9tIHJldHVybiBzdGF0ZW1lbnRzXG5cdFx0Ki9cblx0cHJpdmF0ZSBpbmZlclJldHVyblR5cGUgKG1ldGhvZDogdHMuTWV0aG9kRGVjbGFyYXRpb24sIGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz4pOiBzdHJpbmcge1xuXHRcdC8vIElmIG1ldGhvZCBoYXMgZXhwbGljaXQgcmV0dXJuIHR5cGUgYW5ub3RhdGlvbiwgdXNlIGl0XG5cdFx0aWYgKG1ldGhvZC50eXBlKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclR5cGUobWV0aG9kLnR5cGUpO1xuXHRcdH1cblxuXHRcdC8vIE90aGVyd2lzZSwgdHJ5IHRvIGluZmVyIGZyb20gcmV0dXJuIHN0YXRlbWVudHMgaW4gdGhlIG1ldGhvZCBib2R5XG5cdFx0aWYgKG1ldGhvZC5ib2R5KSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclJldHVyblR5cGVGcm9tQm9keShtZXRob2QuYm9keSwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHR9XG5cblx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBJbmZlciByZXR1cm4gdHlwZSBieSBhbmFseXppbmcgcmV0dXJuIHN0YXRlbWVudHMgaW4gdGhlIG1ldGhvZCBib2R5XG5cdFx0Ki9cblx0cHJpdmF0ZSBpbmZlclJldHVyblR5cGVGcm9tQm9keSAoYm9keTogdHMuQmxvY2ssIGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz4pOiBzdHJpbmcge1xuXHRcdGNvbnN0IHJldHVyblR5cGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cblx0XHRjb25zdCB2aXNpdCA9IChub2RlOiB0cy5Ob2RlKTogdm9pZCA9PiB7XG5cdFx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQobm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihub2RlLmV4cHJlc3Npb24sIHVuZGVmaW5lZCwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0aWYgKHR5cGUgIT09ICd1bmtub3duJykge1xuXHRcdFx0XHRcdHJldHVyblR5cGVzLmFkZCh0eXBlKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIHZpc2l0KTtcblx0XHR9O1xuXG5cdFx0dmlzaXQoYm9keSk7XG5cblx0XHRpZiAocmV0dXJuVHlwZXMuc2l6ZSA9PT0gMCkge1xuXHRcdFx0cmV0dXJuICd2b2lkJztcblx0XHR9XG5cdFx0aWYgKHJldHVyblR5cGVzLnNpemUgPT09IDEpIHtcblx0XHRcdHJldHVybiBBcnJheS5mcm9tKHJldHVyblR5cGVzKVsgMCBdO1xuXHRcdH1cblx0XHRyZXR1cm4gQXJyYXkuZnJvbShyZXR1cm5UeXBlcykuam9pbignIHwgJyk7XG5cdH1cblxuXHQvKipcblx0XHQqIEdldCBmdWxsIHRleHQgZnJvbSBhIHF1YWxpZmllZCBuYW1lIChlLmcuLCBOYW1lc3BhY2UuVHlwZSlcblx0XHQqL1xuXHRwcml2YXRlIGdldFF1YWxpZmllZE5hbWVUZXh0IChxdWFsaWZpZWROYW1lOiB0cy5RdWFsaWZpZWROYW1lKTogc3RyaW5nIHtcblx0XHRjb25zdCBwYXJ0czogc3RyaW5nW10gPSBbXTtcblx0XHRsZXQgY3VycmVudDogdHMuUXVhbGlmaWVkTmFtZSB8IHRzLklkZW50aWZpZXIgPSBxdWFsaWZpZWROYW1lO1xuXG5cdFx0d2hpbGUgKHRzLmlzUXVhbGlmaWVkTmFtZShjdXJyZW50KSkge1xuXHRcdFx0cGFydHMudW5zaGlmdChjdXJyZW50LnJpZ2h0LnRleHQpO1xuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQubGVmdDtcblx0XHR9XG5cdFx0cGFydHMudW5zaGlmdChjdXJyZW50LnRleHQpO1xuXG5cdFx0cmV0dXJuIHBhcnRzLmpvaW4oJy4nKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBJbmZlciB0eXBlIGZyb20gaW5pdGlhbGl6ZXJcblx0ICovXG5cdHByaXZhdGUgaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyIChcblx0XHRpbml0aWFsaXplcjogdHMuRXhwcmVzc2lvbixcblx0XHRkYXRhVHlwZU1hcD86IE1hcDxzdHJpbmcsIHN0cmluZz4sXG5cdFx0Y2xhc3NQcm9wZXJ0eVR5cGVzPzogTWFwPHN0cmluZywgc3RyaW5nPlxuXHQpOiBzdHJpbmcge1xuXHRcdHN3aXRjaCAoaW5pdGlhbGl6ZXIua2luZCkge1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5TdHJpbmdMaXRlcmFsOlxuXHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdW1lcmljTGl0ZXJhbDpcblx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHJ1ZUtleXdvcmQ6XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZDpcblx0XHRcdHJldHVybiAnYm9vbGVhbic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bGxLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdudWxsJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5kZWZpbmVkS2V5d29yZDpcblx0XHRcdHJldHVybiAndW5kZWZpbmVkJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbjpcblx0XHRcdHJldHVybiAnQXJyYXk8dW5rbm93bj4nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5PYmplY3RMaXRlcmFsRXhwcmVzc2lvbjpcblx0XHRcdHJldHVybiAnb2JqZWN0Jztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTmV3RXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gSGFuZGxlIG5ldyBEYXRlKCksIG5ldyBNYXAoKSwgZXRjLlxuXHRcdFx0Y29uc3QgbmV3RXhwciA9IGluaXRpYWxpemVyIGFzIHRzLk5ld0V4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG5ld0V4cHIuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0cmV0dXJuIG5ld0V4cHIuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICdvYmplY3QnO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQmluYXJ5RXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gSGFuZGxlIGFyaXRobWV0aWMgb3BlcmF0aW9uczogYSAqIGIsIGEgKyBiLCBhIC0gYiwgYSAvIGJcblx0XHRcdGNvbnN0IGJpbmFyeUV4cHIgPSBpbml0aWFsaXplciBhcyB0cy5CaW5hcnlFeHByZXNzaW9uO1xuXHRcdFx0Y29uc3QgbGVmdFR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihiaW5hcnlFeHByLmxlZnQsIGRhdGFUeXBlTWFwLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0Y29uc3QgcmlnaHRUeXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIoYmluYXJ5RXhwci5yaWdodCwgZGF0YVR5cGVNYXAsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdFxuXHRcdFx0Ly8gQ2hlY2sgaWYgaXQncyBhbiBhcml0aG1ldGljIG9wZXJhdG9yXG5cdFx0XHRjb25zdCBvcGVyYXRvciA9IGJpbmFyeUV4cHIub3BlcmF0b3JUb2tlbi5raW5kO1xuXHRcdFx0aWYgKG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLkFzdGVyaXNrVG9rZW4gfHxcblx0XHRcdFx0ICAgIG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLlNsYXNoVG9rZW4gfHxcblx0XHRcdFx0ICAgIG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLk1pbnVzVG9rZW4gfHxcblx0XHRcdFx0ICAgIG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLlBlcmNlbnRUb2tlbikge1xuXHRcdFx0XHQvLyBBcml0aG1ldGljIG9wZXJhdGlvbnMgb24gbnVtYmVycyBwcm9kdWNlIG51bWJlcnNcblx0XHRcdFx0aWYgKChsZWZ0VHlwZSA9PT0gJ251bWJlcicgfHwgbGVmdFR5cGUgPT09ICd1bmtub3duJykgJiZcblx0XHRcdFx0XHQgICAgKHJpZ2h0VHlwZSA9PT0gJ251bWJlcicgfHwgcmlnaHRUeXBlID09PSAndW5rbm93bicpKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAob3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuUGx1c1Rva2VuKSB7XG5cdFx0XHRcdC8vIFBsdXMgY2FuIGJlIGFkZGl0aW9uIG9yIHN0cmluZyBjb25jYXRlbmF0aW9uXG5cdFx0XHRcdGlmIChsZWZ0VHlwZSA9PT0gJ3N0cmluZycgfHwgcmlnaHRUeXBlID09PSAnc3RyaW5nJykge1xuXHRcdFx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAobGVmdFR5cGUgPT09ICdudW1iZXInICYmIHJpZ2h0VHlwZSA9PT0gJ251bWJlcicpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb246IHtcblx0XHRcdC8vIEhhbmRsZSBwcm9wZXJ0eSBhY2Nlc3MgbGlrZSBkYXRhLnZhbHVlLCBkYXRhLmlkXG5cdFx0XHRpZiAoZGF0YVR5cGVNYXApIHtcblx0XHRcdFx0Y29uc3QgYWNjZXNzQ2hhaW4gPSB0aGlzLmdldFByb3BlcnR5QWNjZXNzQ2hhaW4oaW5pdGlhbGl6ZXIpO1xuXHRcdFx0XHRpZiAoYWNjZXNzQ2hhaW4pIHtcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gZGF0YVR5cGVNYXAuZ2V0KGFjY2Vzc0NoYWluKTtcblx0XHRcdFx0XHRpZiAodHlwZSkge1xuXHRcdFx0XHRcdFx0cmV0dXJuIHR5cGU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBIYW5kbGUgdGhpcy5tYXAuc2l6ZSBwYXR0ZXJuIChNYXAuc2l6ZSByZXR1cm5zIG51bWJlcilcblx0XHRcdGNvbnN0IHByb3BBY2Nlc3MgPSBpbml0aWFsaXplciBhcyB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ocHJvcEFjY2Vzcy5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBvdXRlclByb3AgPSBwcm9wQWNjZXNzLmV4cHJlc3Npb247XG5cdFx0XHRcdC8vIENoZWNrIGZvciB0aGlzLm1hcCBwYXR0ZXJuXG5cdFx0XHRcdGxldCBpbm5lck5hbWUgPSAnJztcblx0XHRcdFx0aWYgKG91dGVyUHJvcC5leHByZXNzaW9uLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdFx0XHRpbm5lck5hbWUgPSAndGhpcyc7XG5cdFx0XHRcdH0gZWxzZSBpZiAodHMuaXNJZGVudGlmaWVyKG91dGVyUHJvcC5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdGlubmVyTmFtZSA9IG91dGVyUHJvcC5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgbWFwUHJvcCA9IG91dGVyUHJvcC5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IGZpbmFsUHJvcCA9IHByb3BBY2Nlc3MubmFtZS50ZXh0O1xuXHRcdFx0XHQvLyB0aGlzLm1hcC5zaXplIC0+IG51bWJlclxuXHRcdFx0XHRpZiAoaW5uZXJOYW1lID09PSAndGhpcycgJiYgbWFwUHJvcCA9PT0gJ21hcCcgJiYgZmluYWxQcm9wID09PSAnc2l6ZScpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5JZGVudGlmaWVyOiB7XG5cdFx0XHQvLyBIYW5kbGUgaWRlbnRpZmllciByZWZlcmVuY2VzIGlmIGluIGRhdGFUeXBlTWFwXG5cdFx0XHRpZiAoZGF0YVR5cGVNYXApIHtcblx0XHRcdFx0Y29uc3QgbmFtZSA9IChpbml0aWFsaXplciBhcyB0cy5JZGVudGlmaWVyKS50ZXh0O1xuXHRcdFx0XHRjb25zdCB0eXBlID0gZGF0YVR5cGVNYXAuZ2V0KG5hbWUpO1xuXHRcdFx0XHRpZiAodHlwZSkge1xuXHRcdFx0XHRcdHJldHVybiB0eXBlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQ2FsbEV4cHJlc3Npb246IHtcblx0XHRcdC8vIEhhbmRsZSBmdW5jdGlvbiBjYWxscyBsaWtlIERhdGUubm93KCksIHBhcnNlSW50KCksIGV0Yy5cblx0XHRcdGNvbnN0IGNhbGxFeHByID0gaW5pdGlhbGl6ZXIgYXMgdHMuQ2FsbEV4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbEV4cHIuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y29uc3QgbWV0aG9kTmFtZSA9IGNhbGxFeHByLmV4cHJlc3Npb24ubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBvYmpOYW1lID0gdHMuaXNJZGVudGlmaWVyKGNhbGxFeHByLmV4cHJlc3Npb24uZXhwcmVzc2lvbilcblx0XHRcdFx0XHQ/IGNhbGxFeHByLmV4cHJlc3Npb24uZXhwcmVzc2lvbi50ZXh0XG5cdFx0XHRcdFx0OiAnJztcblx0XHRcdFx0XHRcblx0XHRcdFx0Ly8gRGF0ZS5ub3coKSAtPiBudW1iZXJcblx0XHRcdFx0aWYgKG9iak5hbWUgPT09ICdEYXRlJyAmJiBtZXRob2ROYW1lID09PSAnbm93Jykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBTdHJpbmcgbWV0aG9kcyB0aGF0IHJldHVybiBzdHJpbmdcblx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICd0b1N0cmluZycgfHwgbWV0aG9kTmFtZSA9PT0gJ3ZhbHVlT2YnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIEhhbmRsZSBNYXAgcHJvcGVydHkgYWNjZXNzIG9uIGNsYXNzIGluc3RhbmNlcyAodGhpcy5tYXAuKilcblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxFeHByLmV4cHJlc3Npb24uZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRjb25zdCBvdXRlclByb3AgPSBjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRcdFx0Ly8gSGFuZGxlIGJvdGggJ3RoaXMnIGtleXdvcmQgYW5kIGlkZW50aWZpZXIgcGF0dGVybnNcblx0XHRcdFx0XHRsZXQgaW5uZXJOYW1lID0gJyc7XG5cdFx0XHRcdFx0aWYgKG91dGVyUHJvcC5leHByZXNzaW9uLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdFx0XHRcdGlubmVyTmFtZSA9ICd0aGlzJztcblx0XHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihvdXRlclByb3AuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRcdGlubmVyTmFtZSA9IG91dGVyUHJvcC5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdGNvbnN0IG1hcFByb3AgPSBvdXRlclByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRcdC8vIHRoaXMubWFwLlgoKSBwYXR0ZXJuc1xuXHRcdFx0XHRcdGlmIChpbm5lck5hbWUgPT09ICd0aGlzJyAmJiBtYXBQcm9wID09PSAnbWFwJykge1xuXHRcdFx0XHRcdFx0Ly8gVHJ5IHRvIGdldCB0aGUgTWFwJ3MgdmFsdWUgdHlwZSBmcm9tIGNsYXNzIHByb3BlcnRpZXNcblx0XHRcdFx0XHRcdGxldCBtYXBWYWx1ZVR5cGUgPSAndW5rbm93bic7XG5cdFx0XHRcdFx0XHRpZiAoY2xhc3NQcm9wZXJ0eVR5cGVzKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnN0IG1hcFR5cGUgPSBjbGFzc1Byb3BlcnR5VHlwZXMuZ2V0KCdtYXAnKTtcblx0XHRcdFx0XHRcdFx0aWYgKG1hcFR5cGUgJiYgbWFwVHlwZS5zdGFydHNXaXRoKCdNYXA8JykpIHtcblx0XHRcdFx0XHRcdFx0XHQvLyBQYXJzZSBNYXA8SywgVj4gdG8gZ2V0IFZcblx0XHRcdFx0XHRcdFx0XHRjb25zdCBtYXRjaCA9IG1hcFR5cGUubWF0Y2goL01hcDxbXixdKyxcXHMqKC4rKT4kLyk7XG5cdFx0XHRcdFx0XHRcdFx0aWYgKG1hdGNoKSB7XG5cdFx0XHRcdFx0XHRcdFx0XHRtYXBWYWx1ZVR5cGUgPSBtYXRjaFsgMSBdO1xuXHRcdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdoYXMnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdzZXQnKSByZXR1cm4gJ3RoaXMnO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdnZXQnKSByZXR1cm4gbWFwVmFsdWVUeXBlO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdkZWxldGUnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdjbGVhcicpIHJldHVybiAndm9pZCc7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3ZhbHVlcycpIHJldHVybiBgSXRlcmFibGVJdGVyYXRvcjwke21hcFZhbHVlVHlwZX0+YDtcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAna2V5cycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjxzdHJpbmc+Jztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZW50cmllcycpIHJldHVybiBgSXRlcmFibGVJdGVyYXRvcjxbc3RyaW5nLCAke21hcFZhbHVlVHlwZX1dPmA7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIERpcmVjdCBtYXAuWCgpIGNhbGxzXG5cdFx0XHRcdGlmIChvYmpOYW1lID09PSAnbWFwJyB8fCBvYmpOYW1lID09PSAnb2JqJykge1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnaGFzJykgcmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3NldCcpIHJldHVybiAndGhpcyc7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdnZXQnKSByZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZGVsZXRlJykgcmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2NsZWFyJykgcmV0dXJuICd2b2lkJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3ZhbHVlcycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjx1bmtub3duPic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdrZXlzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPHN0cmluZz4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZW50cmllcycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjxbc3RyaW5nLCB1bmtub3duXT4nO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBwYXJzZUludCwgcGFyc2VGbG9hdCAtPiBudW1iZXJcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY2FsbEV4cHIuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y29uc3QgZm5OYW1lID0gY2FsbEV4cHIuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHRpZiAoZm5OYW1lID09PSAncGFyc2VJbnQnIHx8IGZuTmFtZSA9PT0gJ3BhcnNlRmxvYXQnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdTdHJpbmcnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdOdW1iZXInKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdCb29sZWFuJykge1xuXHRcdFx0XHRcdHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UZW1wbGF0ZUV4cHJlc3Npb246XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk5vU3Vic3RpdHV0aW9uVGVtcGxhdGVMaXRlcmFsOiB7XG5cdFx0XHQvLyBUZW1wbGF0ZSBsaXRlcmFscyBsaWtlIGAke2Jhc2VWYWx1ZX0tJHtleHRyYX1gIGFsd2F5cyBwcm9kdWNlIHN0cmluZ3Ncblx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHR9XG5cdFx0ZGVmYXVsdDpcblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHR9XG5cdFxuXHQvKipcblx0XHRcdCogQ29sbGVjdCB1c2FnZSBpbmZvcm1hdGlvbiBmb3IgdHlwZSByZWZlcmVuY2VzXG5cdFx0XHQqL1xuXHRwcml2YXRlIGNvbGxlY3RVc2FnZSAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGZvciBuZXcgVHlwZSgpIGluc3RhbnRpYXRpb25cblx0XHRpZiAodHMuaXNOZXdFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0bGV0IHR5cGVOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obm9kZS5leHByZXNzaW9uKSkge1xuXHRcdFx0XHR0eXBlTmFtZSA9IHRoaXMucmVzb2x2ZVR5cGVQYXRoKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHR0eXBlTmFtZSA9IHRoaXMuZ2V0VHlwZU5hbWVGcm9tRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHR5cGVOYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0dGhpcy5hZGRVc2FnZSh0eXBlTmFtZSwge1xuXHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0a2luZCAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0fSk7XG5cdFx0XHRcdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnQgZnJvbSBuZXcgVHlwZSgpIGZvciBmbG93IGFuYWx5c2lzXG5cdFx0XHRcdHRoaXMudHJhY2tOZXdBc3NpZ25tZW50KG5vZGUsIHR5cGVOYW1lKTtcblx0XHRcdFx0Ly8gQWxzbyByZWNvcmQgYXMgZmxvdyBldmVudFxuXHRcdFx0XHR0aGlzLmFkZEZsb3codHlwZU5hbWUsIHtcblx0XHRcdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdGtpbmQgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0XHRcdGNvZGUgICAgIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0Y29udGV4dCAgOiAnbmV3IGV4cHJlc3Npb24nLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cdFxuXHRcdC8vIENoZWNrIGZvciBwcm9wZXJ0eSBhY2Nlc3Mgb24gaW5zdGFuY2VzICh1c2VyLkFkbWluVHlwZSlcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdGNvbnN0IHByb3BOYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0XHQvLyBDaGVjayBpZiB0aGlzIGxvb2tzIGxpa2UgYSB0eXBlIGFjY2VzcyBwYXR0ZXJuXG5cdFx0XHRpZiAocHJvcE5hbWUgJiYgdGhpcy5pc0xpa2VseVR5cGVOYW1lKHByb3BOYW1lKSkge1xuXHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdCk7XG5cdFx0XHRcdFx0Ly8gVHJ5IHRvIHJlc29sdmUgZnVsbCBwYXRoXG5cdFx0XHRcdGNvbnN0IGZ1bGxQYXRoID0gdGhpcy5yZXNvbHZlVHlwZVBhdGgobm9kZSk7XG5cdFx0XHRcdGlmIChmdWxsUGF0aCkge1xuXHRcdFx0XHRcdHRoaXMuYWRkVXNhZ2UoZnVsbFBhdGgsIHtcblx0XHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0XHRraW5kICAgICA6ICdwcm9wZXJ0eUFjY2VzcycsXG5cdFx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcblx0XHQvLyBDaGVjayBmb3IgbG9va3VwKCdUeXBlTmFtZScpIG9yIGxvb2t1cChzb3VyY2UsICdUeXBlTmFtZScpIGNhbGxzXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRjb25zdCBmdW5jTmFtZSA9IHRoaXMuZ2V0RnVuY3Rpb25OYW1lKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoZnVuY05hbWUgPT09ICdsb29rdXAnICYmIG5vZGUuYXJndW1lbnRzLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0Y29uc3QgdHlwZVBhdGggPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKG5vZGUpO1xuXHRcdFx0XHRpZiAodHlwZVBhdGgpIHtcblx0XHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHRcdCk7XG5cdFx0XHRcdFx0dGhpcy5hZGRVc2FnZSh0eXBlUGF0aCwge1xuXHRcdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRcdGtpbmQgICAgIDogJ2xvb2t1cCcsXG5cdFx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnQgZnJvbSBsb29rdXAgZm9yIGluc3RhbnRpYXRpb24gdHJhY2tpbmdcblx0XHRcdFx0XHR0aGlzLnRyYWNrTG9va3VwQXNzaWdubWVudChub2RlLCB0eXBlUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0KiBHZXQgZnVuY3Rpb24gbmFtZSBmcm9tIGV4cHJlc3Npb24gKGlkZW50aWZpZXIgb3IgcHJvcGVydHkgYWNjZXNzKVxuXHRcdFx0Ki9cblx0cHJpdmF0ZSBnZXRGdW5jdGlvbk5hbWUgKGV4cHI6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLnRleHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0cmV0dXJuIGV4cHIubmFtZS50ZXh0O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cdFxuXHQvKipcblx0XHRcdCogQWRkIGEgdXNhZ2UgdG8gdGhlIGNvbGxlY3Rpb25cblx0XHRcdCovXG5cdHByaXZhdGUgYWRkVXNhZ2UgKHR5cGVQYXRoOiBzdHJpbmcsIHVzYWdlOiBVc2FnZUluZm8pOiB2b2lkIHtcblx0XHQvLyBPbmx5IHRyYWNrIHVzYWdlcyBvZiBtbmVtb25pY2EtZGVmaW5lZCB0eXBlc1xuXHRcdGlmICghdGhpcy5kZWZpbml0aW9ucy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGlmICghdGhpcy51c2FnZXMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0dGhpcy51c2FnZXMuc2V0KHR5cGVQYXRoLCBbXSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIGR1cGxpY2F0ZXMgYmFzZWQgb24gbG9jYXRpb24sIGNvZGUsIGFuZCBraW5kXG5cdFx0Y29uc3QgZXhpc3RpbmdVc2FnZXMgPSB0aGlzLnVzYWdlcy5nZXQodHlwZVBhdGgpITtcblx0XHRjb25zdCBpc0R1cGxpY2F0ZSA9IGV4aXN0aW5nVXNhZ2VzLnNvbWUoZXhpc3RpbmcgPT5cblx0XHRcdGV4aXN0aW5nLmxvY2F0aW9uID09PSB1c2FnZS5sb2NhdGlvbiAmJlxuXHRcdFx0XHRleGlzdGluZy5jb2RlID09PSB1c2FnZS5jb2RlICYmXG5cdFx0XHRcdGV4aXN0aW5nLmtpbmQgPT09IHVzYWdlLmtpbmQpO1xuXG5cdFx0aWYgKCFpc0R1cGxpY2F0ZSkge1xuXHRcdFx0ZXhpc3RpbmdVc2FnZXMucHVzaCh1c2FnZSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgRURTIChFeGVjdXRpb24gRGF0YSBTdG9yYWdlKSB1c2FnZSBpbmZvcm1hdGlvblxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0RURTIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpIHx8ICFub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCBmdW5jTmFtZSA9IHRoaXMuZ2V0RnVuY3Rpb25OYW1lKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0aWYgKCFmdW5jTmFtZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblx0XHQvLyBFbmNsb3NpbmcgbW5lbW9uaWNhIHR5cGUgcGF0aCDigJQgd3JhcCBhcmdzIGFyZSB1c3VhbGx5IGxvY2FsXG5cdFx0Ly8gZnVuY3Rpb25zLCBzbyB0aGUgb3duaW5nIGRlZmluZSgpL2xhenkoKSBoYW5kbGVyIG9yIGRlY29yYXRlZFxuXHRcdC8vIGNsYXNzIGlzIHdoYXQgZWRzLmpzb24gY29uc3VtZXJzIChHcmFwaEJ1aWxkZXIpIGNhbiBqb2luIG9uLlxuXHRcdGNvbnN0IHNjb3BlID0gdGhpcy5yZXNvbHZlRURTU2NvcGUobm9kZSk7XG5cblx0XHQvLyB3cmFwKGZuKSwgd3JhcENvbnN0cnVjdG9yQXJnKGZuLCBwYXJlbnQpLCB1cGdyYWRlQ29uc3RydWN0b3JBcmcoYXJnLCBpbnN0KSwgd3JhcEluc3RhbmNlTWV0aG9kcyhvYmopXG5cdFx0aWYgKFxuXHRcdFx0ZnVuY05hbWUgPT09ICd3cmFwJyB8fFxuXHRcdFx0ZnVuY05hbWUgPT09ICd3cmFwQ29uc3RydWN0b3JBcmcnIHx8XG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3VwZ3JhZGVDb25zdHJ1Y3RvckFyZycgfHxcblx0XHRcdGZ1bmNOYW1lID09PSAnd3JhcEluc3RhbmNlTWV0aG9kcydcblx0XHQpIHtcblx0XHRcdGNvbnN0IHRhcmdldFR5cGUgPSB0aGlzLnJlc29sdmVFRFNBcmd1bWVudFR5cGUobm9kZS5hcmd1bWVudHNbIDAgXSk7XG5cdFx0XHRjb25zdCBpbmZvOiBFRFNJbmZvID0ge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCAgICAgICA6ICd3cmFwJyxcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSA6IHRhcmdldFR5cGUgfHwgdW5kZWZpbmVkLFxuXHRcdFx0XHRzY29wZSxcblx0XHRcdH07XG5cdFx0XHQvLyBBIHdyYXAoKSBjYWxsIG5lc3RlZCBpbnNpZGUgYW5vdGhlciB3cmFwcGVkIGJvZHkgY2FycmllcyB0aGVcblx0XHRcdC8vIGxpbmsgdG8gdGhlIHNpdGUgd2hvc2UgcnVudGltZSB3cmFwcGluZyBjYXVzZWQgaXRcblx0XHRcdGNvbnN0IHZpYSA9IHRoaXMubmVzdGVkV3JhcFZpYS5nZXQobm9kZSk7XG5cdFx0XHRpZiAodmlhKSB7XG5cdFx0XHRcdGluZm8udmlhID0gdmlhO1xuXHRcdFx0fVxuXHRcdFx0Ly8gZGl2ZSB3cmFwcyByZXR1cm5lZCBmdW5jdGlvbnMgdG9vLCBhbmQgYW55IG1uZW1vbmljYSBpbnN0YW5jZVxuXHRcdFx0Ly8gY3JlYXRlZCBpbnNpZGUgdGhlIHdyYXBwZWQgYm9keSBpcyBhIGd1YXJhbnRlZWQgcGF0aCBoaXQg4oCUXG5cdFx0XHQvLyBib3RoIGFyZSBjYWxjdWxhYmxlIEFvVCwgc28gcmVjb3JkIHRoZW1cblx0XHRcdGNvbnN0IHdyYXBwZWQgPSB0aGlzLnJlc29sdmVGdW5jdGlvbkFyZ3VtZW50KG5vZGUuYXJndW1lbnRzWyAwIF0sIHNvdXJjZUZpbGUpO1xuXHRcdFx0aWYgKHdyYXBwZWQpIHtcblx0XHRcdFx0Y29uc3QgY3JlYXRlc1R5cGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0XHRcdHRoaXMuYW5hbHl6ZVdyYXBwZWRCb2R5KHdyYXBwZWQsIGxvY2F0aW9uLCBzb3VyY2VGaWxlLCAwLCBuZXcgU2V0KCksIGNyZWF0ZXNUeXBlcyk7XG5cdFx0XHRcdGlmIChjcmVhdGVzVHlwZXMuc2l6ZSA+IDApIHtcblx0XHRcdFx0XHRpbmZvLmNyZWF0ZXNUeXBlcyA9IEFycmF5LmZyb20oY3JlYXRlc1R5cGVzKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgc3RvcmVkID0gdGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCBzY29wZSB8fCAndW5rbm93bicsIGluZm8pO1xuXHRcdFx0dGhpcy53cmFwRW50cnlCeU5vZGUuc2V0KG5vZGUsIHN0b3JlZCk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gY3VycmVudCgpLCBnZXRFcnJvckluc3RhbmNlKGVyciksIGdldEZsb3codGFyZ2V0Pylcblx0XHRpZiAoZnVuY05hbWUgPT09ICdjdXJyZW50JyB8fCBmdW5jTmFtZSA9PT0gJ2dldEVycm9ySW5zdGFuY2UnIHx8IGZ1bmNOYW1lID09PSAnZ2V0RmxvdycpIHtcblx0XHRcdHRoaXMuYWRkRURTKHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCA6ICdjb250ZXh0Q29uc3VtZScsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHNjb3BlLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gYXR0YWNoSG9va3MoY29sbGVjdGlvbikg4oCUIGZyb20gQG1uZW1vbmljYS9uZXN0anMsIHdpcmVzIGFcblx0XHQvLyBUeXBlc0NvbGxlY3Rpb24gdG8gZGl2ZSdzIGxpZmVjeWNsZSB0cmFjaW5nXG5cdFx0aWYgKGZ1bmNOYW1lID09PSAnYXR0YWNoSG9va3MnICYmIG5vZGUuYXJndW1lbnRzLmxlbmd0aCA+IDApIHtcblx0XHRcdGNvbnN0IGFyZyA9IG5vZGUuYXJndW1lbnRzWyAwIF07XG5cdFx0XHRpZiAodHMuaXNBcnJheUxpdGVyYWxFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGFyZy5lbGVtZW50cykge1xuXHRcdFx0XHRcdGNvbnN0IHRhcmdldFR5cGUgPSB0aGlzLnJlc29sdmVFRFNBcmd1bWVudFR5cGUoZWxlbWVudCk7XG5cdFx0XHRcdFx0dGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCBzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRcdFx0a2luZCAgICAgICA6ICdob29rQXR0YWNoJyxcblx0XHRcdFx0XHRcdGNvZGUsXG5cdFx0XHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdFx0XHRzY29wZSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgdGFyZ2V0VHlwZSA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShhcmcpO1xuXHRcdFx0XHR0aGlzLmFkZEVEUyh0YXJnZXRUeXBlIHx8IHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRcdGtpbmQgICAgICAgOiAnaG9va0F0dGFjaCcsXG5cdFx0XHRcdFx0Y29kZSxcblx0XHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdFx0c2NvcGUsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHR5cGUgZnJvbSBFRFMgY2FsbCBhcmd1bWVudCAoYmVzdCBlZmZvcnQpXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVFRFNBcmd1bWVudFR5cGUgKGFyZzogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCFhcmcpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gSWRlbnRpZmllcjogdmFyaWFibGUgbmFtZVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0Y29uc3QgbWFwcGVkID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQoYXJnLnRleHQpO1xuXHRcdFx0aWYgKG1hcHBlZCkge1xuXHRcdFx0XHRyZXR1cm4gbWFwcGVkO1xuXHRcdFx0fVxuXHRcdFx0Ly8gTWF5YmUgaXQncyBhIHR5cGUgbmFtZSBkaXJlY3RseVxuXHRcdFx0aWYgKHRoaXMuZGVmaW5pdGlvbnMuaGFzKGFyZy50ZXh0KSkge1xuXHRcdFx0XHRyZXR1cm4gYXJnLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2Vzczogb2JqLnByb3Bcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMucmVzb2x2ZVR5cGVQYXRoKGFyZyk7XG5cdFx0fVxuXG5cdFx0Ly8gVGhpcyBleHByZXNzaW9uOiB0aGlzLnNvbWV0aGluZ1xuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcmcpICYmIHRzLmlzSWRlbnRpZmllcihhcmcuZXhwcmVzc2lvbikgJiYgYXJnLmV4cHJlc3Npb24udGV4dCA9PT0gJ3RoaXMnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0aGUgZW5jbG9zaW5nIG1uZW1vbmljYSBzY29wZSBvZiBhbiBFRFMgY2FsbCBzaXRlIGJ5IHdhbGtpbmdcblx0ICogdXAgdGhlIHBhcmVudCBjaGFpbjogbmVhcmVzdCBkZWZpbmUoKS9sYXp5KCkgY2FsbCB3aG9zZSBoYW5kbGVyIGhvbGRzXG5cdCAqIHRoZSBub2RlLCBvciBuZWFyZXN0IEBkZWNvcmF0ZSgpLWVkIGNsYXNzIGRlY2xhcmF0aW9uLiBCZXN0IGVmZm9ydCDigJRcblx0ICogcmV0dXJucyB1bmRlZmluZWQgZm9yIGNhbGxzIG91dHNpZGUgYW55IHR5cGUgc2NvcGUgKG1vZHVsZSB0b3AgbGV2ZWwpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRURTU2NvcGUgKG5vZGU6IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbm9kZS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGNvbnN0IHNjb3BlUGF0aCA9IHRoaXMuZWRzU2NvcGVCeU5vZGUuZ2V0KGN1cnJlbnQpO1xuXHRcdFx0aWYgKHNjb3BlUGF0aCkge1xuXHRcdFx0XHRyZXR1cm4gc2NvcGVQYXRoO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSB3cmFwKCkgYXJndW1lbnQgdG8gaXRzIGZ1bmN0aW9uIG5vZGUgd2l0aG91dCB0aGUgdHlwZVxuXHQgKiBjaGVja2VyOiBkaXJlY3QgZnVuY3Rpb24gZXhwcmVzc2lvbnMvYXJyb3dzLCBvciBzYW1lLWZpbGUgYmluZGluZ3Ncblx0ICogKGBjb25zdCBmbiA9ICgpID0+IC4uLmAsIGBmdW5jdGlvbiBmbigpIC4uLmApLiBCZXN0IGVmZm9ydCDigJQgbWV0aG9kXG5cdCAqIHJlZmVyZW5jZXMsIC5iaW5kKCkgcHJvZHVjdHMgYW5kIGNyb3NzLWZpbGUgaWRlbnRpZmllcnMgc3RheVxuXHQgKiB1bnJlc29sdmVkOyB0aGUgY2FsbHNpdGUgZW50cnkgaXRzZWxmIGlzIHN0aWxsIHJlY29yZGVkLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRnVuY3Rpb25Bcmd1bWVudCAoXG5cdFx0YXJnOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGVcblx0KTogdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGlmICghYXJnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGFyZykgfHwgdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0cmV0dXJuIGFyZztcblx0XHR9XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihhcmcpKSB7XG5cdFx0XHRjb25zdCBrZXkgPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfSMke2FyZy50ZXh0fWA7XG5cdFx0XHRjb25zdCBib3VuZCA9IHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5nZXQoa2V5KTtcblx0XHRcdGlmIChib3VuZCkge1xuXHRcdFx0XHRyZXR1cm4gYm91bmQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogQW5hbHlzZSBhIHdyYXBwZWQgZnVuY3Rpb24ncyBib2R5IGZvciBndWFyYW50ZWVkIHJ1bnRpbWUgcGF0aHM6XG5cdCAqIGRpdmUgd3JhcHMgcmV0dXJuZWQgZnVuY3Rpb25zIGFzIHdlbGwgKHJlY3Vyc2l2ZWx5KSwgc28gZWFjaFxuXHQgKiBmdW5jdGlvbi12YWx1ZWQgcmV0dXJuIGlzIGEgbmVzdGVkIHdyYXAgc2l0ZSwgYW5kIGVhY2ggYG5ldyBUeXBlKClgXG5cdCAqIGluc2lkZSB0aGUgYm9keSBtZWFucyB0aGUgcGF0aCBoaXRzIHRoYXQgdHlwZSdzIGNvbnN0cnVjdG9yICh3aGljaFxuXHQgKiBhdHRhY2hIb29rcyB3cmFwcyB0b28pLiBCb3RoIGZhY3RzIGFyZSAxMDAlIGVuc3VyZWQsIHNvIHRoZXkgYXJlXG5cdCAqIHJlY29yZGVkIEFvVC4gTmVzdGVkIGZ1bmN0aW9uIGJvZGllcyBhcmUgTk9UIHdhbGtlZCBoZXJlIOKAlCB0aGV5XG5cdCAqIGJlbG9uZyB0byB0aGVpciBvd24gd3JhcCBhbmFseXNpcywgcmVhY2hlZCB2aWEgdGhlIHJldHVybiBjaGFpbi5cblx0ICogRGVwdGgtY2FwcGVkIGFuZCBjeWNsZS1ndWFyZGVkLlxuXHQgKi9cblx0cHJpdmF0ZSBhbmFseXplV3JhcHBlZEJvZHkgKFxuXHRcdGZuOiB0cy5GdW5jdGlvbkxpa2VEZWNsYXJhdGlvbixcblx0XHR2aWFMb2NhdGlvbjogc3RyaW5nLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0ZGVwdGg6IG51bWJlcixcblx0XHR2aXNpdGVkOiBTZXQ8dHMuTm9kZT4sXG5cdFx0Y3JlYXRlc1R5cGVzOiBTZXQ8c3RyaW5nPlxuXHQpOiB2b2lkIHtcblx0XHRpZiAoZGVwdGggPiA1IHx8IHZpc2l0ZWQuaGFzKGZuKSB8fCAhZm4uYm9keSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR2aXNpdGVkLmFkZChmbik7XG5cblx0XHQvLyBBcnJvdyB3aXRoIGV4cHJlc3Npb24gYm9keTogaW1wbGljaXQgcmV0dXJuXG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihmbikgJiYgIXRzLmlzQmxvY2soZm4uYm9keSkpIHtcblx0XHRcdHRoaXMucmVjb3JkV3JhcHBlZFJldHVybihmbi5ib2R5LCB2aWFMb2NhdGlvbiwgc291cmNlRmlsZSwgZGVwdGgsIHZpc2l0ZWQpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHdhbGsgPSAobm9kZTogdHMuTm9kZSk6IHZvaWQgPT4ge1xuXHRcdFx0aWYgKG5vZGUgIT09IGZuLmJvZHkgJiYgKFxuXHRcdFx0XHR0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihub2RlKSB8fFxuXHRcdFx0XHR0cy5pc0Fycm93RnVuY3Rpb24obm9kZSkgfHxcblx0XHRcdFx0dHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKG5vZGUpIHx8XG5cdFx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24obm9kZSlcblx0XHRcdCkpIHtcblx0XHRcdFx0Ly8gbmVzdGVkIGZ1bmN0aW9uIGJvZGllcyBhcmUgYW5hbHlzZWQgdGhyb3VnaCB0aGUgcmV0dXJuIGNoYWluXG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRXcmFwcGVkUmV0dXJuKG5vZGUuZXhwcmVzc2lvbiwgdmlhTG9jYXRpb24sIHNvdXJjZUZpbGUsIGRlcHRoLCB2aXNpdGVkKTtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc05ld0V4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdFx0Y29uc3QgY3JlYXRlZCA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbikgfHxcblx0XHRcdFx0XHQodHMuaXNJZGVudGlmaWVyKG5vZGUuZXhwcmVzc2lvbikgJiYgdGhpcy5kZWZpbml0aW9ucy5oYXMobm9kZS5leHByZXNzaW9uLnRleHQpXG5cdFx0XHRcdFx0XHQ/IG5vZGUuZXhwcmVzc2lvbi50ZXh0XG5cdFx0XHRcdFx0XHQ6IHVuZGVmaW5lZCk7XG5cdFx0XHRcdGlmIChjcmVhdGVkKSB7XG5cdFx0XHRcdFx0Y3JlYXRlc1R5cGVzLmFkZChjcmVhdGVkKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdFx0Y29uc3QgbmVzdGVkTmFtZSA9IHRoaXMuZ2V0RnVuY3Rpb25OYW1lKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHRcdGlmIChcblx0XHRcdFx0XHRuZXN0ZWROYW1lID09PSAnd3JhcCcgfHxcblx0XHRcdFx0XHRuZXN0ZWROYW1lID09PSAnd3JhcENvbnN0cnVjdG9yQXJnJyB8fFxuXHRcdFx0XHRcdG5lc3RlZE5hbWUgPT09ICd1cGdyYWRlQ29uc3RydWN0b3JBcmcnIHx8XG5cdFx0XHRcdFx0bmVzdGVkTmFtZSA9PT0gJ3dyYXBJbnN0YW5jZU1ldGhvZHMnXG5cdFx0XHRcdCkge1xuXHRcdFx0XHRcdC8vIHRoZSBuZXN0ZWQgY2FsbCBtYXkgYWxyZWFkeSBiZSBjb2xsZWN0ZWQgKHZpc2l0ZWRcblx0XHRcdFx0XHQvLyBiZWZvcmUgdGhpcyBvdXRlciB3cmFwIHNpdGUpIOKAlCBiYWNrLXBhdGNoIGl0cyBlbnRyeSxcblx0XHRcdFx0XHQvLyBvdGhlcndpc2UgbGVhdmUgdGhlIGxpbmsgZm9yIGNvbGxlY3RFRFMgdG8gcGljayB1cFxuXHRcdFx0XHRcdGNvbnN0IG5lc3RlZEVudHJ5ID0gdGhpcy53cmFwRW50cnlCeU5vZGUuZ2V0KG5vZGUpO1xuXHRcdFx0XHRcdGlmIChuZXN0ZWRFbnRyeSkge1xuXHRcdFx0XHRcdFx0bmVzdGVkRW50cnkudmlhID0gdmlhTG9jYXRpb247XG5cdFx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHRcdHRoaXMubmVzdGVkV3JhcFZpYS5zZXQobm9kZSwgdmlhTG9jYXRpb24pO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIHdhbGspO1xuXHRcdH07XG5cdFx0d2Fsayhmbi5ib2R5KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgb25lIGZ1bmN0aW9uLXZhbHVlZCByZXR1cm4gb2YgYSB3cmFwcGVkIGJvZHkgYXMgYSBuZXN0ZWQgd3JhcFxuXHQgKiBzaXRlIChgdmlhYCA9IHRoZSBzaXRlIHdob3NlIHdyYXBwaW5nIGNhdXNlZCBpdCkgYW5kIHJlY3Vyc2UgaW50b1xuXHQgKiBpdHMgb3duIHJldHVybnMuIFJldHVybnMgdGhyb3VnaCBpZGVudGlmaWVycyByZXNvbHZlIHRocm91Z2ggdGhlXG5cdCAqIHNhbWUtZmlsZSBiaW5kaW5ncyB0YWJsZTsgdW5yZXNvbHZhYmxlIHJldHVybnMgYXJlIHNpbXBseSBza2lwcGVkLlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmRXcmFwcGVkUmV0dXJuIChcblx0XHRleHByOiB0cy5FeHByZXNzaW9uLFxuXHRcdHZpYUxvY2F0aW9uOiBzdHJpbmcsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRkZXB0aDogbnVtYmVyLFxuXHRcdHZpc2l0ZWQ6IFNldDx0cy5Ob2RlPlxuXHQpOiB2b2lkIHtcblx0XHRjb25zdCByZXR1cm5lZCA9IHRoaXMucmVzb2x2ZUZ1bmN0aW9uQXJndW1lbnQoZXhwciwgc291cmNlRmlsZSk7XG5cdFx0aWYgKCFyZXR1cm5lZCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0cmV0dXJuZWQuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IHJldHVybmVkLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblx0XHRjb25zdCBzY29wZSA9IHRoaXMucmVzb2x2ZUVEU1Njb3BlKHJldHVybmVkKTtcblx0XHRjb25zdCBlbnRyeSA9IHRoaXMuYWRkRURTKHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kIDogJ3dyYXAnLFxuXHRcdFx0Y29kZSxcblx0XHRcdHNjb3BlLFxuXHRcdFx0dmlhICA6IHZpYUxvY2F0aW9uLFxuXHRcdH0pO1xuXHRcdC8vIHRoZSByZXR1cm5lZCBmdW5jdGlvbidzIG93biByZXR1cm5zIGFyZSB3cmFwcGVkIGluIHR1cm47IGB2aWFgXG5cdFx0Ly8gY2hhaW5zIHRvIHRoaXMgbmVzdGVkIGVudHJ5J3MgbG9jYXRpb25cblx0XHRjb25zdCBuZXN0ZWRDcmVhdGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0dGhpcy5hbmFseXplV3JhcHBlZEJvZHkocmV0dXJuZWQsIGxvY2F0aW9uLCBzb3VyY2VGaWxlLCBkZXB0aCArIDEsIHZpc2l0ZWQsIG5lc3RlZENyZWF0ZXMpO1xuXHRcdGlmIChuZXN0ZWRDcmVhdGVzLnNpemUgPiAwKSB7XG5cdFx0XHRlbnRyeS5jcmVhdGVzVHlwZXMgPSBBcnJheS5mcm9tKG5lc3RlZENyZWF0ZXMpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBBZGQgYW4gRURTIHVzYWdlIHRvIHRoZSBjb2xsZWN0aW9uXG5cdCAqIFJldHVybnMgdGhlIHN0b3JlZCBlbnRyeSAodGhlIGV4aXN0aW5nIG9uZSB3aGVuIHRoaXMgaXMgYSBkdXBsaWNhdGUpLFxuXHQgKiBzbyBjYWxsZXJzIGNhbiBlbnJpY2ggaXQgYWZ0ZXIgbmVzdGVkIGJvZHkgYW5hbHlzaXMuXG5cdCAqL1xuXHRwcml2YXRlIGFkZEVEUyAodHlwZVBhdGg6IHN0cmluZywgaW5mbzogRURTSW5mbyk6IEVEU0luZm8ge1xuXHRcdGlmICghdGhpcy5lZHNVc2FnZXMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0dGhpcy5lZHNVc2FnZXMuc2V0KHR5cGVQYXRoLCBbXSk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZXhpc3RpbmcgPSB0aGlzLmVkc1VzYWdlcy5nZXQodHlwZVBhdGgpITtcblx0XHRjb25zdCBkdXBsaWNhdGUgPSBleGlzdGluZy5maW5kKGUgPT4ge1xuXHRcdFx0cmV0dXJuIGUubG9jYXRpb24gPT09IGluZm8ubG9jYXRpb24gJiZcblx0XHRcdFx0ZS5raW5kID09PSBpbmZvLmtpbmQgJiZcblx0XHRcdFx0ZS5jb2RlID09PSBpbmZvLmNvZGU7XG5cdFx0fSk7XG5cblx0XHRpZiAoZHVwbGljYXRlKSB7XG5cdFx0XHRyZXR1cm4gZHVwbGljYXRlO1xuXHRcdH1cblx0XHRleGlzdGluZy5wdXNoKGluZm8pO1xuXHRcdHJldHVybiBpbmZvO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgbmF0aXZlIGZsb3cgcGF0dGVybnMgKGluc3RhbmNlIHVzYWdlIGFmdGVyIGNyZWF0aW9uKVxuXHQgKiBQaGFzZSAxOiBwcm9wZXJ0eSBhY2Nlc3MsIG1ldGhvZCBjYWxscywgYXJndW1lbnRzLCByZXR1cm4sIGRlc3RydWN0dXJpbmcsIGV0Yy5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3cgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHQvLyBQcm9wZXJ0eSByZWFkOiB1c2VyLm5hbWUgb3IgdXNlcj8ubmFtZVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd1Byb3BlcnR5QWNjZXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEVsZW1lbnQgYWNjZXNzOiB1c2VyWyduYW1lJ11cblx0XHRpZiAodHMuaXNFbGVtZW50QWNjZXNzRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0VsZW1lbnRBY2Nlc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgd3JpdGU6IHVzZXIubmFtZSA9IHZhbHVlXG5cdFx0aWYgKHRzLmlzQmluYXJ5RXhwcmVzc2lvbihub2RlKSAmJiBub2RlLm9wZXJhdG9yVG9rZW4ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0Fzc2lnbm1lbnQobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gTWV0aG9kIGNhbGw6IHVzZXIudmFsaWRhdGUoKSAgQU5EICBhcmd1bWVudCBwYXNzaW5nOiBwcm9jZXNzVXNlcih1c2VyKVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd01ldGhvZENhbGwobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93QXJndW1lbnRQYXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIERlc3RydWN0dXJlIHJlYWQ6IGNvbnN0IHsgbmFtZSB9ID0gdXNlclxuXHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgJiYgbm9kZS5pbml0aWFsaXplcikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0Rlc3RydWN0dXJlKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFJldHVybiBpbnN0YW5jZTogcmV0dXJuIHVzZXJcblx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQobm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93UmV0dXJuKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFNwcmVhZDogeyAuLi51c2VyIH1cblx0XHRpZiAodHMuaXNTcHJlYWRFbGVtZW50KG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93U3ByZWFkKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IHByb3BlcnR5IGFjY2VzcyBmbG93IChyZWFkIG9yIGNvbmRpdGlvbmFsKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd1Byb3BlcnR5QWNjZXNzIChub2RlOiB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBwcm9wTmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIFNraXAgaWYgdGhpcyBpcyBhIHR5cGUgY29uc3RydWN0b3IgYWNjZXNzIChlLmcuLCBVc2VyVHlwZS5kZWZpbmUpXG5cdFx0aWYgKHByb3BOYW1lID09PSAnZGVmaW5lJyB8fCBwcm9wTmFtZSA9PT0gJ2xhenknKSB7IHJldHVybjsgfVxuXG5cdFx0dGhpcy5hZGRGbG93KG9iamVjdFR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICAgIDogJ3Byb3BlcnR5UmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0cHJvcGVydHlOYW1lIDogcHJvcE5hbWUsXG5cdFx0XHR0YXJnZXRUeXBlICAgOiBvYmplY3RUeXBlXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBlbGVtZW50IGFjY2VzcyBmbG93OiB1c2VyWyduYW1lJ11cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dFbGVtZW50QWNjZXNzIChub2RlOiB0cy5FbGVtZW50QWNjZXNzRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnZWxlbWVudEFjY2VzcycsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGFzc2lnbm1lbnQgZmxvdzogdXNlci5uYW1lID0gdmFsdWUgb3IgdXNlciA9IG90aGVyXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93QXNzaWdubWVudCAobm9kZTogdHMuQmluYXJ5RXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIFByb3BlcnR5IHdyaXRlOiB1c2VyLm5hbWUgPSB2YWx1ZVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmxlZnQpKSB7XG5cdFx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5sZWZ0LmV4cHJlc3Npb24pO1xuXHRcdFx0aWYgKCFvYmplY3RUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0XHRjb25zdCBwcm9wTmFtZSA9IG5vZGUubGVmdC5uYW1lLnRleHQ7XG5cdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdCk7XG5cdFx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCAgICAgICAgIDogJ3Byb3BlcnR5V3JpdGUnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRwcm9wZXJ0eU5hbWUgOiBwcm9wTmFtZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSAgIDogb2JqZWN0VHlwZVxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gVmFyaWFibGUgcmVhc3NpZ25tZW50OiB1c2VyID0gb3RoZXJcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG5vZGUubGVmdCkpIHtcblx0XHRcdGNvbnN0IHZhck5hbWUgPSBub2RlLmxlZnQudGV4dDtcblx0XHRcdGNvbnN0IG1hcHBlZFR5cGUgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldCh2YXJOYW1lKTtcblx0XHRcdGlmICghbWFwcGVkVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHQpO1xuXHRcdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdFx0dGhpcy5hZGRGbG93KG1hcHBlZFR5cGUsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAncmVhc3NpZ25tZW50Jyxcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSA6IG1hcHBlZFR5cGVcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IG1ldGhvZCBjYWxsIGZsb3c6IHVzZXIudmFsaWRhdGUoKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd01ldGhvZENhbGwgKG5vZGU6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3Qgb2JqZWN0VHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbi5leHByZXNzaW9uKTtcblx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBtZXRob2ROYW1lID0gbm9kZS5leHByZXNzaW9uLm5hbWUudGV4dDtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHQvLyBTa2lwIGlmIHRoaXMgaXMgYSB0eXBlIGNvbnN0cnVjdG9yIGNhbGwgKGUuZy4sIG5ldyBVc2VyVHlwZSgpKVxuXHRcdGlmIChtZXRob2ROYW1lID09PSAnZGVmaW5lJyB8fCBtZXRob2ROYW1lID09PSAnbGF6eScpIHsgcmV0dXJuOyB9XG5cblx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgICAgOiAnbWV0aG9kQ2FsbCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0cHJvcGVydHlOYW1lIDogbWV0aG9kTmFtZSxcblx0XHRcdHRhcmdldFR5cGUgICA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGFyZ3VtZW50IHBhc3NpbmcgZmxvdzogcHJvY2Vzc1VzZXIodXNlcilcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dBcmd1bWVudFBhc3MgKG5vZGU6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuXHRcdFx0Y29uc3QgYXJnID0gbm9kZS5hcmd1bWVudHNbIGkgXTtcblx0XHRcdGNvbnN0IGFyZ1R5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShhcmcpO1xuXHRcdFx0aWYgKCFhcmdUeXBlKSB7IGNvbnRpbnVlOyB9XG5cblx0XHRcdGNvbnN0IGZ1bmNOYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKSB8fCAnYW5vbnltb3VzJztcblx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0KTtcblx0XHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRcdHRoaXMuYWRkRmxvdyhhcmdUeXBlLCB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgIDogJ3Bhc3NBc0FyZycsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHRhcmdldFR5cGUgOiBhcmdUeXBlLFxuXHRcdFx0XHRjb250ZXh0ICAgIDogYGFyZyAke2l9IHRvICR7ZnVuY05hbWV9YFxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgZGVzdHJ1Y3R1cmluZyBmbG93OiBjb25zdCB7IG5hbWUgfSA9IHVzZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dEZXN0cnVjdHVyZSAobm9kZTogdHMuVmFyaWFibGVEZWNsYXJhdGlvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNPYmplY3RCaW5kaW5nUGF0dGVybihub2RlLm5hbWUpKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3Qgc291cmNlVHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuaW5pdGlhbGl6ZXIhKTtcblx0XHRpZiAoIXNvdXJjZVR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHQvLyBFeHRyYWN0IGRlc3RydWN0dXJlZCBwcm9wZXJ0eSBuYW1lc1xuXHRcdGNvbnN0IHByb3BzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBub2RlLm5hbWUuZWxlbWVudHMpIHtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZWxlbWVudC5uYW1lKSkge1xuXHRcdFx0XHRwcm9wcy5wdXNoKGVsZW1lbnQubmFtZS50ZXh0KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHR0aGlzLmFkZEZsb3coc291cmNlVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ2Rlc3RydWN0dXJlUmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHNvdXJjZVR5cGUsXG5cdFx0XHRjb250ZXh0ICAgIDogcHJvcHMuam9pbignLCAnKVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgcmV0dXJuIGZsb3c6IHJldHVybiB1c2VyXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93UmV0dXJuIChub2RlOiB0cy5SZXR1cm5TdGF0ZW1lbnQsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCByZXR1cm5UeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uISk7XG5cdFx0aWYgKCFyZXR1cm5UeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0dGhpcy5hZGRGbG93KHJldHVyblR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICA6ICdyZXR1cm4nLFxuXHRcdFx0Y29kZSxcblx0XHRcdHRhcmdldFR5cGUgOiByZXR1cm5UeXBlXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBzcHJlYWQgZmxvdzogeyAuLi51c2VyIH1cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dTcHJlYWQgKG5vZGU6IHRzLlNwcmVhZEVsZW1lbnQsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCBzcHJlYWRUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIXNwcmVhZFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHR0aGlzLmFkZEZsb3coc3ByZWFkVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ3NwcmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHNwcmVhZFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHR5cGUgZnJvbSBhbiBleHByZXNzaW9uIChpZGVudGlmaWVyLCBwcm9wZXJ0eSBhY2Nlc3MsIGV0Yy4pXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVFeHByZXNzaW9uVHlwZSAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gSWRlbnRpZmllcjogdXNlclxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChleHByLnRleHQpO1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2VzczogdXNlci5uYW1lIChyZXR1cm4gb2JqZWN0IHR5cGUsIG5vdCBwcm9wZXJ0eSB0eXBlKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKGV4cHIuZXhwcmVzc2lvbik7XG5cdFx0fVxuXG5cdFx0Ly8gRWxlbWVudCBhY2Nlc3M6IHVzZXJbJ25hbWUnXVxuXHRcdGlmICh0cy5pc0VsZW1lbnRBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUoZXhwci5leHByZXNzaW9uKTtcblx0XHR9XG5cblx0XHQvLyBUaGlzIGV4cHJlc3Npb246IHRoaXMgKGlmIGluIGEgbWV0aG9kLCB3ZSBjYW4ndCByZXNvbHZlIHdpdGhvdXQgbW9yZSBjb250ZXh0KVxuXHRcdGlmIChleHByLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBBZGQgYSBmbG93IHVzYWdlIHRvIHRoZSBjb2xsZWN0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGFkZEZsb3cgKHR5cGVQYXRoOiBzdHJpbmcsIGluZm86IEZsb3dJbmZvKTogdm9pZCB7XG5cdFx0aWYgKCF0aGlzLmZsb3dVc2FnZXMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0dGhpcy5mbG93VXNhZ2VzLnNldCh0eXBlUGF0aCwgW10pO1xuXHRcdH1cblxuXHRcdGNvbnN0IGV4aXN0aW5nID0gdGhpcy5mbG93VXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGlzRHVwbGljYXRlID0gZXhpc3Rpbmcuc29tZShlID0+IHtcblx0XHRcdHJldHVybiBlLmxvY2F0aW9uID09PSBpbmZvLmxvY2F0aW9uICYmXG5cdFx0XHRcdGUua2luZCA9PT0gaW5mby5raW5kICYmXG5cdFx0XHRcdGUuY29kZSA9PT0gaW5mby5jb2RlO1xuXHRcdH0pO1xuXG5cdFx0aWYgKCFpc0R1cGxpY2F0ZSkge1xuXHRcdFx0ZXhpc3RpbmcucHVzaChpbmZvKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHRcdCogR2V0IHR5cGUgbmFtZSBmcm9tIGV4cHJlc3Npb24gKGlkZW50aWZpZXIgb3IgcHJvcGVydHkgYWNjZXNzKVxuXHRcdFx0Ki9cblx0cHJpdmF0ZSBnZXRUeXBlTmFtZUZyb21FeHByZXNzaW9uIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBuYW1lID0gZXhwci50ZXh0O1xuXHRcdFx0Ly8gQ2hlY2sgaWYgdGhpcyBpZGVudGlmaWVyIGlzIGEgdmFyaWFibGUgbWFwcGVkIHRvIGEgdHlwZSAoZS5nLiwgZnJvbSBsb29rdXApXG5cdFx0XHRjb25zdCBtYXBwZWRUeXBlID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0XHRpZiAobWFwcGVkVHlwZSkge1xuXHRcdFx0XHRyZXR1cm4gbWFwcGVkVHlwZTtcblx0XHRcdH1cblx0XHRcdHJldHVybiBuYW1lO1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKGV4cHIpO1xuXHRcdFx0cmV0dXJuIGNoYWluLmpvaW4oJy4nKTtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIFJlc29sdmUgZnVsbCB0eXBlIHBhdGggZnJvbSBwcm9wZXJ0eSBhY2Nlc3Ncblx0XHRcdCovXG5cdHByaXZhdGUgcmVzb2x2ZVR5cGVQYXRoIChleHByOiB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKGV4cHIpO1xuXHRcdGlmIChjaGFpbi5sZW5ndGggPT09IDApIHJldHVybiB1bmRlZmluZWQ7XG5cdFxuXHRcdC8vIENoZWNrIGlmIHRoaXMgY2hhaW4gbWF0Y2hlcyBhIGtub3duIHR5cGVcblx0XHRjb25zdCBmdWxsUGF0aCA9IGNoYWluLmpvaW4oJy4nKTtcblx0XHRpZiAodGhpcy5kZWZpbml0aW9ucy5oYXMoZnVsbFBhdGgpKSB7XG5cdFx0XHRyZXR1cm4gZnVsbFBhdGg7XG5cdFx0fVxuXHRcblx0XHQvLyBUcnkganVzdCB0aGUgcHJvcGVydHkgbmFtZVxuXHRcdGNvbnN0IHByb3BOYW1lID0gY2hhaW5bIGNoYWluLmxlbmd0aCAtIDEgXTtcblx0XHRmb3IgKGNvbnN0IFsgcGF0aCBdIG9mIHRoaXMuZGVmaW5pdGlvbnMpIHtcblx0XHRcdGlmIChwYXRoLmVuZHNXaXRoKGAuJHtwcm9wTmFtZX1gKSB8fCBwYXRoID09PSBwcm9wTmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdH1cblx0XHR9XG5cdFxuXHRcdHJldHVybiBmdWxsUGF0aDtcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQgKiBDaGVjayBpZiBhIG5hbWUgbG9va3MgbGlrZSBhIHR5cGUgKHN0YXJ0cyB3aXRoIHVwcGVyY2FzZSlcblx0XHRcdCAqL1xuXHRwcml2YXRlIGlzTGlrZWx5VHlwZU5hbWUgKG5hbWU6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRcdHJldHVybiBuYW1lWyAwIF0gPj0gJ0EnICYmIG5hbWVbIDAgXSA8PSAnWic7XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0ICogUmVzb2x2ZSBhIGNvbnN0cnVjdG9yIHBhcmFtZXRlciB0eXBlLCBleHBhbmRpbmcgaW5saW5lIG9iamVjdCBsaXRlcmFsc1xuXHRcdFx0ICogYW5kIHR5cGUgYWxpYXNlcyB3aGVyZSBwb3NzaWJsZS5cblx0XHRcdCAqL1xuXHRwcml2YXRlIHJlc29sdmVDb25zdHJ1Y3RvclBhcmFtVHlwZSAodHlwZU5vZGU6IHRzLlR5cGVOb2RlIHwgdW5kZWZpbmVkKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIXR5cGVOb2RlKSByZXR1cm4gdW5kZWZpbmVkO1xuXG5cdFx0Ly8gRGlyZWN0IGlubGluZSB0eXBlIGxpdGVyYWw6IHsgcHJvcDogdHlwZSB9XG5cdFx0aWYgKHRzLmlzVHlwZUxpdGVyYWxOb2RlKHR5cGVOb2RlKSkge1xuXHRcdFx0Y29uc3QgcHJvcHM6IHN0cmluZ1tdID0gW107XG5cdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiB0eXBlTm9kZS5tZW1iZXJzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRjb25zdCBvcHRpb25hbCA9IG1lbWJlci5xdWVzdGlvblRva2VuID8gJz8nIDogJyc7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRwcm9wcy5wdXNoKGAke3Byb3BOYW1lfSR7b3B0aW9uYWx9OiAke3R5cGV9YCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiBgeyAke3Byb3BzLmpvaW4oJzsgJyl9IH1gO1xuXHRcdH1cblxuXHRcdC8vIFR5cGUgcmVmZXJlbmNlOiB1c2FnZSwgVXNlckRhdGEsIGV0Yy4gLSByZWN1cnNpdmVseSBleHBhbmRcblx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZSh0eXBlTm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKHR5cGVOb2RlLnR5cGVOYW1lKSkge1xuXHRcdFx0Y29uc3QgdHlwZU5hbWUgPSB0eXBlTm9kZS50eXBlTmFtZS50ZXh0O1xuXHRcdFx0Y29uc3QgYWxpYXNlZFR5cGUgPSB0aGlzLnR5cGVBbGlhc2VzLmdldCh0eXBlTmFtZSk7XG5cdFx0XHRpZiAoYWxpYXNlZFR5cGUpIHtcblx0XHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLnJlc29sdmVDb25zdHJ1Y3RvclBhcmFtVHlwZShhbGlhc2VkVHlwZSk7XG5cdFx0XHRcdGlmIChleHBhbmRlZCkgcmV0dXJuIGV4cGFuZGVkO1xuXHRcdFx0fVxuXHRcdFx0Ly8gSWYgbm90IGFuIG9iamVjdCB0eXBlIGFsaWFzLCByZXR1cm4gdGhlIHR5cGUgbmFtZSB3aXRoIGFyZ3Ncblx0XHRcdGlmICh0eXBlTm9kZS50eXBlQXJndW1lbnRzICYmIHR5cGVOb2RlLnR5cGVBcmd1bWVudHMubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRjb25zdCBhcmdzID0gdHlwZU5vZGUudHlwZUFyZ3VtZW50cy5tYXAoYXJnID0+IHRoaXMuaW5mZXJUeXBlKGFyZykpO1xuXHRcdFx0XHRyZXR1cm4gYCR7dHlwZU5hbWUgIH08JHsgIGFyZ3Muam9pbignLCAnKSAgfT5gO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHR5cGVOYW1lO1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0XHRcdCAqIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGEgY2xhc3MtbGlrZSBub2RlLlxuXHRcdFx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENsYXNzQ29uc3RydWN0b3JQYXJhbXMgKGNsYXNzTGlrZTogdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHRzLkNsYXNzRXhwcmVzc2lvbik6XG5cdFx0Q29uc3RydWN0b3JQYXJhbUluZm9bXSB7XG5cdFx0Y29uc3QgcGFyYW1zOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdID0gW107XG5cblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjbGFzc0xpa2UubWVtYmVycykge1xuXHRcdFx0aWYgKCF0cy5pc0NvbnN0cnVjdG9yRGVjbGFyYXRpb24obWVtYmVyKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblxuXHRcdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBtZW1iZXIucGFyYW1ldGVycykge1xuXHRcdFx0XHRpZiAoIXBhcmFtLm5hbWUgfHwgIXRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSkgY29udGludWU7XG5cdFx0XHRcdGlmICghcGFyYW0udHlwZSkgY29udGludWU7XG5cblx0XHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gcGFyYW0ubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBleHBhbmRlZFR5cGUgPSB0aGlzLnJlc29sdmVDb25zdHJ1Y3RvclBhcmFtVHlwZShwYXJhbS50eXBlKSB8fCB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblxuXHRcdFx0XHRwYXJhbXMucHVzaCh7XG5cdFx0XHRcdFx0bmFtZSAgICAgOiBwYXJhbU5hbWUsXG5cdFx0XHRcdFx0dHlwZSAgICAgOiBleHBhbmRlZFR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiAhIXBhcmFtLnF1ZXN0aW9uVG9rZW4gfHwgISFwYXJhbS5pbml0aWFsaXplclxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHRcdGJyZWFrOyAvLyBPbmx5IHByb2Nlc3MgZmlyc3QgY29uc3RydWN0b3Jcblx0XHR9XG5cblx0XHRyZXR1cm4gcGFyYW1zO1xuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBkZWZpbmUoKSBjYWxsXG5cdFx0XHQgKiBUaGlzIGlzIHVzZWQgZm9yIFR5cGVSZWdpc3RyeSBjb25zdHJ1Y3RvciBzaWduYXR1cmVzXG5cdFx0XHQgKiBQcmVzZXJ2ZXMgcGFyYW1ldGVyIG5hbWVzIGFuZCBleHBhbmRzIG9iamVjdCB0eXBlcyB0byB0aGVpciBzdHJ1Y3R1cmVcblx0XHRcdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdIHtcblx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCk7XG5cdFx0aWYgKCFjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdHJldHVybiBbXTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JQYXJhbXNGcm9tQ29uc3RydWN0b3IoY29uc3RydWN0b3JFeHByKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBhIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24uXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JQYXJhbXNGcm9tQ29uc3RydWN0b3IgKGNvbnN0cnVjdG9yRXhwcjogdHMuRXhwcmVzc2lvbik6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10ge1xuXHRcdGNvbnN0IHBhcmFtczogQ29uc3RydWN0b3JQYXJhbUluZm9bXSA9IFtdO1xuXHRcblx0XHQvLyBIYW5kbGUgZnVuY3Rpb24gZXhwcmVzc2lvbiBvciBhcnJvdyBmdW5jdGlvblxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzQXJyb3dGdW5jdGlvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHQvLyBMb29rIGZvciBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIChzZWNvbmQgcGFyYW0gYWZ0ZXIgYHRoaXNgKVxuXHRcdFx0Ly8gUGF0dGVybnM6IGZ1bmN0aW9uKHRoaXM6IFR5cGUsIGRhdGE6IHsgLi4uIH0pIG9yICh0aGlzOiBUeXBlLCBkYXRhOiB7IC4uLiB9KSA9PlxuXHRcdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBjb25zdHJ1Y3RvckV4cHIucGFyYW1ldGVycy5sZW5ndGg7IGkrKykge1xuXHRcdFx0XHRjb25zdCBwYXJhbSA9IGNvbnN0cnVjdG9yRXhwci5wYXJhbWV0ZXJzWyBpIF07XG5cdFx0XHRcdGlmICghcGFyYW0udHlwZSkgY29udGludWU7XG5cdFxuXHRcdFx0XHQvLyBTa2lwIGB0aGlzYCBwYXJhbWV0ZXIgKGZpcnN0IHBhcmFtKVxuXHRcdFx0XHRpZiAoXG5cdFx0XHRcdFx0aSA9PT0gMCAmJlxuXHRcdFx0XHRcdHBhcmFtLm5hbWUua2luZCA9PT0gdHMuU3ludGF4S2luZC5JZGVudGlmaWVyICYmXG5cdFx0XHRcdFx0KHBhcmFtLm5hbWUgYXMgdHMuSWRlbnRpZmllcikudGV4dCA9PT0gJ3RoaXMnXG5cdFx0XHRcdCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFxuXHRcdFx0XHQvLyBHZXQgcGFyYW1ldGVyIG5hbWUgYW5kIGV4cGFuZCBpdHMgdHlwZVxuXHRcdFx0XHRjb25zdCBwYXJhbU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgPyBwYXJhbS5uYW1lLnRleHQgOiAnYXJnJztcblx0XHRcdFx0Y29uc3QgZXhwYW5kZWRUeXBlID0gdGhpcy5yZXNvbHZlQ29uc3RydWN0b3JQYXJhbVR5cGUocGFyYW0udHlwZSkgfHwgdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cdFx0XHRcdFx0XG5cdFx0XHRcdHBhcmFtcy5wdXNoKHtcblx0XHRcdFx0XHRuYW1lICAgICA6IHBhcmFtTmFtZSxcblx0XHRcdFx0XHR0eXBlICAgICA6IGV4cGFuZGVkVHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6ICEhcGFyYW0ucXVlc3Rpb25Ub2tlbiB8fCAhIXBhcmFtLmluaXRpYWxpemVyXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0Ly8gSGFuZGxlIGNsYXNzIGV4cHJlc3Npb24gLSBjaGVjayBjb25zdHJ1Y3RvciBtZXRob2Rcblx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Y29uc3QgY2xhc3NQYXJhbXMgPSB0aGlzLmV4dHJhY3RDbGFzc0NvbnN0cnVjdG9yUGFyYW1zKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGNsYXNzUGFyYW1zKSB7XG5cdFx0XHRcdHBhcmFtcy5wdXNoKHBhcmFtKTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcGFyYW1zO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgTmVzdEpTIGluc3RydW1lbnRhdGlvbiBwb2ludHMgKGludGVyY2VwdG9ycywgZ3VhcmRzLCBwaXBlcyxcblx0ICogZmlsdGVycywgbWlkZGxld2FyZSkuIFB1cmVseSBzeW50YWN0aWM6IGhlcml0YWdlIGNsYXVzZXMsIGRlY29yYXRvclxuXHQgKiBhcHBsaWNhdGlvbiBzaXRlcywgQVBQXyogcHJvdmlkZXIgb2JqZWN0IGxpdGVyYWxzIGFuZFxuXHQgKiBjb25zdW1lci5hcHBseSgpLmZvclJvdXRlcygpIHdpcmluZy4gTm8gaW1wb3J0IHJlc29sdXRpb24gYmV5b25kIHRoZVxuXHQgKiBpZGVudGlmaWVyIHRleHQg4oCUIHRoZSB0eXBlIGNoZWNrZXIgc3RheXMgdW51c2VkLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0SW5zdHJ1bWVudGF0aW9uIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbkNsYXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0XHRpZiAodHMuaXNEZWNvcmF0b3Iobm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbkRlY29yYXRvcihub2RlLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cdFx0aWYgKHRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvblByb3ZpZGVyKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uTWlkZGxld2FyZShub2RlLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGEgbmFtZWQgY2xhc3MgZGVjbGFyYXRpb24gZm9yIGluc3RydW1lbnRhdGlvbiBzaXRlIHJlc29sdXRpb25cblx0ICogYW5kIGRldGVjdCBoZXJpdGFnZS1iYXNlZCBraW5kcyAoYGltcGxlbWVudHMgTmVzdEludGVyY2VwdG9yYCwgZXRjLilcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEluc3RydW1lbnRhdGlvbkNsYXNzIChub2RlOiB0cy5DbGFzc0RlY2xhcmF0aW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCFub2RlLm5hbWUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgY2xhc3NOYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUubmFtZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHQvLyBGaXJzdCBsaW5lIG9mIHRoZSBkZWNsYXJhdGlvbiwgbGlrZSBFRFMgYGNvZGVgIHNuaXBwZXRzXG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zcGxpdCgnXFxuJylbIDAgXS5zbGljZSgwLCAxMDApO1xuXG5cdFx0bGV0IGtpbmQ6IEluc3RydW1lbnRhdGlvbktpbmQgfCB1bmRlZmluZWQ7XG5cdFx0aWYgKG5vZGUuaGVyaXRhZ2VDbGF1c2VzKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGNsYXVzZSBvZiBub2RlLmhlcml0YWdlQ2xhdXNlcykge1xuXHRcdFx0XHRpZiAoY2xhdXNlLnRva2VuICE9PSB0cy5TeW50YXhLaW5kLkltcGxlbWVudHNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Zm9yIChjb25zdCB0eXBlIG9mIGNsYXVzZS50eXBlcykge1xuXHRcdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHR5cGUuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCBtYXRjaGVkID0gSU5TVFJVTUVOVEFUSU9OX0lOVEVSRkFDRV9LSU5EU1sgdHlwZS5leHByZXNzaW9uLnRleHQgXTtcblx0XHRcdFx0XHRpZiAobWF0Y2hlZCkge1xuXHRcdFx0XHRcdFx0a2luZCA9IG1hdGNoZWQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGVjbDogSW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNsID0ge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRjb2RlLFxuXHRcdH07XG5cdFx0aWYgKGtpbmQpIHtcblx0XHRcdGRlY2wua2luZCA9IGtpbmQ7XG5cdFx0fVxuXHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNscy5zZXQoY2xhc3NOYW1lLCBkZWNsKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgZGVjb3JhdG9yIGFwcGxpY2F0aW9uIHNpdGVzOiBAVXNlR3VhcmRzKFgpLCBAVXNlSW50ZXJjZXB0b3JzKFgpLFxuXHQgKiBAVXNlUGlwZXMoWCkgb24gYSBjb250cm9sbGVyIGNsYXNzIG9yIG9uZSBvZiBpdHMgbWV0aG9kcy4gT25lIHNpdGUgcGVyXG5cdCAqIHJlZmVyZW5jZWQgY2xhc3MgaWRlbnRpZmllci5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEluc3RydW1lbnRhdGlvbkRlY29yYXRvciAobm9kZTogdHMuRGVjb3JhdG9yLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihleHByZXNzaW9uKSB8fCAhdHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24uZXhwcmVzc2lvbikpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3Qga2luZCA9IFVTRV9ERUNPUkFUT1JfS0lORFNbIGV4cHJlc3Npb24uZXhwcmVzc2lvbi50ZXh0IF07XG5cdFx0aWYgKCFraW5kKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gVGhlIGRlY29yYXRvcidzIHBhcmVudCBpcyB0aGUgZGVjb3JhdGVkIG5vZGU6IGEgY29udHJvbGxlciBjbGFzc1xuXHRcdC8vIG9yIG9uZSBvZiBpdHMgbWV0aG9kc1xuXHRcdGNvbnN0IGRlY29yYXRlZCA9IG5vZGUucGFyZW50O1xuXHRcdGxldCBzY29wZTogSW5zdHJ1bWVudGF0aW9uU2NvcGU7XG5cdFx0bGV0IHRhcmdldHM6IHN0cmluZ1tdO1xuXHRcdGlmICh0cy5pc0NsYXNzRGVjbGFyYXRpb24oZGVjb3JhdGVkKSAmJiBkZWNvcmF0ZWQubmFtZSkge1xuXHRcdFx0c2NvcGUgPSBgY29udHJvbGxlcjoke2RlY29yYXRlZC5uYW1lLnRleHR9YDtcblx0XHRcdHRhcmdldHMgPSBbIGRlY29yYXRlZC5uYW1lLnRleHQgXTtcblx0XHR9IGVsc2UgaWYgKFxuXHRcdFx0dHMuaXNNZXRob2REZWNsYXJhdGlvbihkZWNvcmF0ZWQpICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIoZGVjb3JhdGVkLm5hbWUpICYmXG5cdFx0XHR0cy5pc0NsYXNzRGVjbGFyYXRpb24oZGVjb3JhdGVkLnBhcmVudCkgJiZcblx0XHRcdGRlY29yYXRlZC5wYXJlbnQubmFtZVxuXHRcdCkge1xuXHRcdFx0Y29uc3QgY2xhc3NOYW1lID0gZGVjb3JhdGVkLnBhcmVudC5uYW1lLnRleHQ7XG5cdFx0XHRzY29wZSA9IGBtZXRob2Q6JHtjbGFzc05hbWV9LiR7ZGVjb3JhdGVkLm5hbWUudGV4dH1gO1xuXHRcdFx0dGFyZ2V0cyA9IFsgY2xhc3NOYW1lIF07XG5cdFx0fSBlbHNlIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRmb3IgKGNvbnN0IGFyZyBvZiBleHByZXNzaW9uLmFyZ3VtZW50cykge1xuXHRcdFx0Ly8gQ2xhc3MgcmVmZXJlbmNlOiBAVXNlR3VhcmRzKEF1dGhHdWFyZCkgb3IgYW4gaW5saW5lIGluc3RhbmNlOlxuXHRcdFx0Ly8gQFVzZVBpcGVzKG5ldyBWYWxpZGF0aW9uUGlwZSh7IHRyYW5zZm9ybTogdHJ1ZSB9KSlcblx0XHRcdGxldCBjbGFzc05hbWU6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0XHRjbGFzc05hbWUgPSBhcmcudGV4dDtcblx0XHRcdH0gZWxzZSBpZiAodHMuaXNOZXdFeHByZXNzaW9uKGFyZykgJiYgdHMuaXNJZGVudGlmaWVyKGFyZy5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjbGFzc05hbWUgPSBhcmcuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0aWYgKCFjbGFzc05hbWUpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHR0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzLnB1c2goe1xuXHRcdFx0XHRraW5kLFxuXHRcdFx0XHRjbGFzc05hbWUsXG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRzY29wZSxcblx0XHRcdFx0dGFyZ2V0cyxcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgZ2xvYmFsIHJlZ2lzdHJhdGlvbnM6IG9iamVjdCBsaXRlcmFscyBzaGFwZWQgbGlrZVxuXHQgKiBgeyBwcm92aWRlOiBBUFBfR1VBUkQgfCBBUFBfUElQRSB8IEFQUF9JTlRFUkNFUFRPUiB8IEFQUF9GSUxURVIsIHVzZUNsYXNzOiBYIH1gLlxuXHQgKiB1c2VFeGlzdGluZy91c2VGYWN0b3J5IHdpdGhvdXQgYSB1c2VDbGFzcyBpZGVudGlmaWVyIGFyZSBub3Rcblx0ICogc3RhdGljYWxseSBvYnZpb3VzIOKAlCBza2lwcGVkIHJhdGhlciB0aGFuIGd1ZXNzZWQuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25Qcm92aWRlciAobm9kZTogdHMuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRsZXQga2luZDogSW5zdHJ1bWVudGF0aW9uS2luZCB8IHVuZGVmaW5lZDtcblx0XHRsZXQgdXNlQ2xhc3NOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cblx0XHRmb3IgKGNvbnN0IHByb3Agb2Ygbm9kZS5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdCF0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSB8fFxuXHRcdFx0XHQhdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkgfHxcblx0XHRcdFx0IXRzLmlzSWRlbnRpZmllcihwcm9wLmluaXRpYWxpemVyKVxuXHRcdFx0KSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHByb3AubmFtZS50ZXh0ID09PSAncHJvdmlkZScpIHtcblx0XHRcdFx0a2luZCA9IEFQUF9UT0tFTl9LSU5EU1sgcHJvcC5pbml0aWFsaXplci50ZXh0IF07XG5cdFx0XHR9XG5cdFx0XHRpZiAocHJvcC5uYW1lLnRleHQgPT09ICd1c2VDbGFzcycpIHtcblx0XHRcdFx0dXNlQ2xhc3NOYW1lID0gcHJvcC5pbml0aWFsaXplci50ZXh0O1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGlmICgha2luZCB8fCAhdXNlQ2xhc3NOYW1lKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0dGhpcy5pbnN0cnVtZW50YXRpb25TaXRlcy5wdXNoKHtcblx0XHRcdGtpbmQsXG5cdFx0XHRjbGFzc05hbWUgOiB1c2VDbGFzc05hbWUsXG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGNvZGUsXG5cdFx0XHRzY29wZSAgICAgOiAnZ2xvYmFsJyxcblx0XHRcdHRhcmdldHMgICA6IFtdLFxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIERldGVjdCBtaWRkbGV3YXJlIHdpcmluZzogYGNvbnN1bWVyLmFwcGx5KE13MSwgTXcyKS5mb3JSb3V0ZXMoLi4uKWBcblx0ICogaW5zaWRlIGEgY2xhc3MncyBjb25maWd1cmUoKSBtZXRob2QuIFRhcmdldHMgY29tZSBmcm9tIGZvclJvdXRlc1xuXHQgKiBhcmd1bWVudHMgd2hlbiBzdGF0aWNhbGx5IHJlYWRhYmxlIChzdHJpbmcgcm91dGVzIG9yIGNvbnRyb2xsZXJcblx0ICogaWRlbnRpZmllcnMpLCBlbHNlIFtdLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0SW5zdHJ1bWVudGF0aW9uTWlkZGxld2FyZSAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoXG5cdFx0XHQhdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obm9kZS5leHByZXNzaW9uKSB8fFxuXHRcdFx0bm9kZS5leHByZXNzaW9uLm5hbWUudGV4dCAhPT0gJ2ZvclJvdXRlcydcblx0XHQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgYXBwbHlDYWxsID0gbm9kZS5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0aWYgKFxuXHRcdFx0IXRzLmlzQ2FsbEV4cHJlc3Npb24oYXBwbHlDYWxsKSB8fFxuXHRcdFx0IXRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFwcGx5Q2FsbC5leHByZXNzaW9uKSB8fFxuXHRcdFx0YXBwbHlDYWxsLmV4cHJlc3Npb24ubmFtZS50ZXh0ICE9PSAnYXBwbHknXG5cdFx0KSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGlmICghdGhpcy5pc0luc2lkZUNvbmZpZ3VyZU1ldGhvZChub2RlKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHRhcmdldHM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBhcmcgb2Ygbm9kZS5hcmd1bWVudHMpIHtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSB8fCB0cy5pc1N0cmluZ0xpdGVyYWwoYXJnKSkge1xuXHRcdFx0XHR0YXJnZXRzLnB1c2goYXJnLnRleHQpO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRhcHBseUNhbGwuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0Zm9yIChjb25zdCBhcmcgb2YgYXBwbHlDYWxsLmFyZ3VtZW50cykge1xuXHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uU2l0ZXMucHVzaCh7XG5cdFx0XHRcdGtpbmQgICAgICA6ICdtaWRkbGV3YXJlJyxcblx0XHRcdFx0Y2xhc3NOYW1lIDogYXJnLnRleHQsXG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRzY29wZSAgICAgOiAnbW9kdWxlJyxcblx0XHRcdFx0dGFyZ2V0cyxcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBXYWxrIHVwIHRoZSBwYXJlbnQgY2hhaW4gbG9va2luZyBmb3IgYW4gZW5jbG9zaW5nIGNvbmZpZ3VyZSgpIG1ldGhvZFxuXHQgKi9cblx0cHJpdmF0ZSBpc0luc2lkZUNvbmZpZ3VyZU1ldGhvZCAobm9kZTogdHMuTm9kZSk6IGJvb2xlYW4ge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbm9kZS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmIChcblx0XHRcdFx0dHMuaXNNZXRob2REZWNsYXJhdGlvbihjdXJyZW50KSAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoY3VycmVudC5uYW1lKSAmJlxuXHRcdFx0XHRjdXJyZW50Lm5hbWUudGV4dCA9PT0gJ2NvbmZpZ3VyZSdcblx0XHRcdCkge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG59XG4iXX0=