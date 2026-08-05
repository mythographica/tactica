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
        // Check for EDS patterns (wrap, link, getLastContext, etc.)
        this.collectEDS(node, sourceFile);
        // Check for native flow patterns (property access, method calls, etc.)
        this.collectFlow(node, sourceFile);
        // Collect type aliases for resolving type references
        if (ts.isTypeAliasDeclaration(node) && ts.isIdentifier(node.name)) {
            this.typeAliases.set(node.name.text, node.type);
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
                        // Don't overwrite a known type from `this` annotation with unknown
                        const existing = properties.get(name);
                        if (existing && existing.type !== 'unknown' && type === 'unknown') {
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
        // wrap(fn), wrapArgs(fn), wrapInstanceMethods(obj)
        if (funcName === 'wrap' || funcName === 'wrapArgs' || funcName === 'wrapInstanceMethods') {
            const targetType = this.resolveEDSArgumentType(node.arguments[0]);
            this.addEDS(targetType || 'unknown', {
                location,
                kind: 'wrap',
                code,
                targetType: targetType || undefined,
            });
            return;
        }
        // link(parent, child), runWithInstance(instance, fn)
        if (funcName === 'link' || funcName === 'runWithInstance') {
            const targetType = this.resolveEDSArgumentType(node.arguments[0]);
            this.addEDS(targetType || 'unknown', {
                location,
                kind: 'link',
                code,
                targetType: targetType || undefined,
            });
            return;
        }
        // getLastContext(), getErrorInstance(err)
        if (funcName === 'getLastContext' || funcName === 'getErrorInstance') {
            this.addEDS('unknown', {
                location,
                kind: 'contextConsume',
                code,
            });
            return;
        }
        // enrichError(err, instance)
        if (funcName === 'enrichError') {
            const targetType = node.arguments.length > 1
                ? this.resolveEDSArgumentType(node.arguments[1])
                : undefined;
            this.addEDS(targetType || 'unknown', {
                location,
                kind: 'errorEnrich',
                code,
                targetType: targetType || undefined,
            });
            return;
        }
        // attachHooks(types), attachHooks([A, B])
        if (funcName === 'attachHooks' && node.arguments.length > 0) {
            const arg = node.arguments[0];
            if (ts.isArrayLiteralExpression(arg)) {
                for (const element of arg.elements) {
                    const targetType = this.resolveEDSArgumentType(element);
                    this.addEDS(targetType || 'unknown', {
                        location,
                        kind: 'hookAttach',
                        code,
                        targetType: targetType || undefined,
                    });
                }
            }
            else {
                const targetType = this.resolveEDSArgumentType(arg);
                this.addEDS(targetType || 'unknown', {
                    location,
                    kind: 'hookAttach',
                    code,
                    targetType: targetType || undefined,
                });
            }
            return;
        }
        // Adapters: createDiveInterceptor, createDivePlugin, createDiveMiddleware
        if (funcName === 'createDiveInterceptor' ||
            funcName === 'createDivePlugin' ||
            funcName === 'createDiveMiddleware') {
            this.addEDS('unknown', {
                location,
                kind: 'adapterUse',
                code,
            });
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
     * Add an EDS usage to the collection
     */
    addEDS(typePath, info) {
        if (!this.edsUsages.has(typePath)) {
            this.edsUsages.set(typePath, []);
        }
        const existing = this.edsUsages.get(typePath);
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
}
exports.MnemonicaAnalyzer = MnemonicaAnalyzer;
//# sourceMappingURL=analyzer.js.map