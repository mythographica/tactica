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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYW5hbHl6ZXIuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvYW5hbHl6ZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFFYiwrQ0FBaUM7QUFNakMsbUNBQXdDO0FBUXhDOztHQUVHO0FBQ0gsTUFBYSxpQkFBaUI7SUFvQjdCLFlBQWEsT0FBb0I7UUFuQnpCLFdBQU0sR0FBbUIsRUFBRSxDQUFDO1FBQzVCLFVBQUssR0FBRyxJQUFJLHFCQUFhLEVBQUUsQ0FBQztRQUM1QixnQkFBVyxHQUFHLElBQUksR0FBRyxFQUEwQixDQUFDO1FBQ2hELFdBQU0sR0FBRyxJQUFJLEdBQUcsRUFBdUIsQ0FBQztRQUN4QyxjQUFTLEdBQUcsSUFBSSxHQUFHLEVBQXFCLENBQUM7UUFDekMsZUFBVSxHQUFHLElBQUksR0FBRyxFQUFzQixDQUFDO1FBQzNDLGdCQUFXLEdBQUcsSUFBSSxHQUFHLEVBQXVCLENBQUM7UUFDckQsNEVBQTRFO1FBQ3BFLHNCQUFpQixHQUFHLElBQUksR0FBRyxFQUFrQixDQUFDO1FBQ3RELDZHQUE2RztRQUNyRywwQkFBcUIsR0FBRyxJQUFJLEdBQUcsRUFBVSxDQUFDO1FBQ2xELGtHQUFrRztRQUMxRixtQ0FBOEIsR0FBRyxJQUFJLEdBQUcsRUFBVSxDQUFDO1FBQzNELGtFQUFrRTtRQUMxRCx3QkFBbUIsR0FBRyxJQUFJLEdBQUcsRUFBa0IsQ0FBQztRQUN4RCxrRUFBa0U7UUFDMUQsbUJBQWMsR0FBRyxJQUFJLEdBQUcsRUFBMEIsQ0FBQztRQUNuRCxzQkFBaUIsR0FBRyxDQUFDLENBQUM7UUFHN0IsNkVBQTZFO1FBQzdFLEtBQUssT0FBTyxDQUFDO0lBQ2QsQ0FBQztJQUVEOzs7T0FHRztJQUNILFdBQVc7UUFDVixJQUFJLENBQUMsTUFBTSxDQUFDLEtBQUssRUFBRSxDQUFDO1FBQ3BCLElBQUksQ0FBQyxTQUFTLENBQUMsS0FB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dHJpY3QnO1xuXG5pbXBvcnQgKiBhcyB0cyBmcm9tICd0eXBlc2NyaXB0JztcbmltcG9ydCB7XG5cdFR5cGVOb2RlLCBQcm9wZXJ0eUluZm8sIEFuYWx5emVSZXN1bHQsIEFuYWx5emVFcnJvcixcblx0RGVmaW5pdGlvbkluZm8sIFVzYWdlSW5mbywgQ29uc3RydWN0b3JQYXJhbUluZm8sXG5cdEVEU0luZm8sIEZsb3dJbmZvXG59IGZyb20gJy4vdHlwZXMnO1xuaW1wb3J0IHsgVHlwZUdyYXBoSW1wbCB9IGZyb20gJy4vZ3JhcGgnO1xuXG5pbnRlcmZhY2UgQ29sbGVjdGlvbkluZm8ge1xuXHR2YXJpYWJsZU5hbWU6IHN0cmluZztcblx0c291cmNlRmlsZTogc3RyaW5nO1xuXHRyZWdpc3RyeUludGVyZmFjZU5hbWU/OiBzdHJpbmc7XG59XG5cbi8qKlxuICogQVNUIEFuYWx5emVyIGZvciBmaW5kaW5nIE1uZW1vbmljYSBkZWZpbmUoKSBhbmQgZGVjb3JhdGUoKSBjYWxsc1xuICovXG5leHBvcnQgY2xhc3MgTW5lbW9uaWNhQW5hbHl6ZXIge1xuXHRwcml2YXRlIGVycm9yczogQW5hbHl6ZUVycm9yW10gPSBbXTtcblx0cHJpdmF0ZSBncmFwaCA9IG5ldyBUeXBlR3JhcGhJbXBsKCk7XG5cdHByaXZhdGUgZGVmaW5pdGlvbnMgPSBuZXcgTWFwPHN0cmluZywgRGVmaW5pdGlvbkluZm8+KCk7XG5cdHByaXZhdGUgdXNhZ2VzID0gbmV3IE1hcDxzdHJpbmcsIFVzYWdlSW5mb1tdPigpO1xuXHRwcml2YXRlIGVkc1VzYWdlcyA9IG5ldyBNYXA8c3RyaW5nLCBFRFNJbmZvW10+KCk7XG5cdHByaXZhdGUgZmxvd1VzYWdlcyA9IG5ldyBNYXA8c3RyaW5nLCBGbG93SW5mb1tdPigpO1xuXHRwcml2YXRlIHR5cGVBbGlhc2VzID0gbmV3IE1hcDxzdHJpbmcsIHRzLlR5cGVOb2RlPigpO1xuXHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50czogdmFyaWFibGVOYW1lIC0+IGZ1bGxQYXRoIG9mIHRoZSB0eXBlIGl0IGhvbGRzXG5cdHByaXZhdGUgdmFyaWFibGVUb1R5cGVNYXAgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHQvLyBUcmFjayBtbmVtb25pY2EgbW9kdWxlLW9iamVjdCB2YXJpYWJsZXMgKGUuZy4sIGltcG9ydCB7IG1uZW1vbmljYSB9IGZyb20gJ21uZW1vbmljYSc7IGNvbnN0IG0gPSBtbmVtb25pY2EpXG5cdHByaXZhdGUgbW9kdWxlT2JqZWN0VmFyaWFibGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdC8vIFRyYWNrIGltcG9ydGVkIGFsaWFzZXMgb2YgY3JlYXRlVHlwZXNDb2xsZWN0aW9uIChlLmcuLCBpbXBvcnQgeyBjcmVhdGVUeXBlc0NvbGxlY3Rpb24gYXMgY3RjIH0pXG5cdHByaXZhdGUgY3JlYXRlVHlwZXNDb2xsZWN0aW9uVmFyaWFibGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdC8vIFRyYWNrIGN1c3RvbSBjb2xsZWN0aW9uIHZhcmlhYmxlczogdmFyaWFibGVOYW1lIC0+IGNvbGxlY3Rpb25JZFxuXHRwcml2YXRlIGNvbGxlY3Rpb25WYXJpYWJsZXMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHQvLyBUcmFjayBjdXN0b20gY29sbGVjdGlvbiBtZXRhZGF0YSBmb3IgT3B0aW9uIEIgcmVnaXN0cnkgZW1pc3Npb25cblx0cHJpdmF0ZSBjb2xsZWN0aW9uSW5mbyA9IG5ldyBNYXA8c3RyaW5nLCBDb2xsZWN0aW9uSW5mbz4oKTtcblx0cHJpdmF0ZSBjb2xsZWN0aW9uQ291bnRlciA9IDA7XG5cblx0Y29uc3RydWN0b3IgKHByb2dyYW0/OiB0cy5Qcm9ncmFtKSB7XG5cdFx0Ly8gU3RvcmUgcHJvZ3JhbSBmb3IgZnV0dXJlIHVzZSAoY3VycmVudGx5IHVudXNlZCBidXQga2VwdCBmb3IgZXh0ZW5zaWJpbGl0eSlcblx0XHR2b2lkIHByb2dyYW07XG5cdH1cblxuXHQvKipcblx0ICogUmVzZXQgdXNhZ2UtcmVsYXRlZCBzdGF0ZSBmb3IgYSBmcmVzaCBwYXNzLlxuXHQgKiBDYWxsIGJlZm9yZSB0aGUgdXNhZ2UtY29sbGVjdGlvbiBwYXNzIHRvIGF2b2lkIGR1cGxpY2F0ZXMgZnJvbSBkZWZpbml0aW9uIHBhc3MuXG5cdCAqL1xuXHRyZXNldFVzYWdlcyAoKTogdm9pZCB7XG5cdFx0dGhpcy51c2FnZXMuY2xlYXIoKTtcblx0XHR0aGlzLmVkc1VzYWdlcy5jbGVhcigpO1xuXHRcdHRoaXMuZmxvd1VzYWdlcy5jbGVhcigpO1xuXHRcdHRoaXMudmFyaWFibGVUb1R5cGVNYXAuY2xlYXIoKTtcblx0XHQvLyBOb3RlOiBtb2R1bGVPYmplY3RWYXJpYWJsZXMgYW5kIGNvbGxlY3Rpb25WYXJpYWJsZXMgaW50ZW50aW9uYWxseSBwZXJzaXN0XG5cdFx0Ly8gYWNyb3NzIGRlZmluaXRpb24gYW5kIHVzYWdlIHBhc3Nlcy5cblx0fVxuXG5cdC8qKlxuXHQgKiBBbmFseXplIGEgc291cmNlIGZpbGUgZm9yIE1uZW1vbmljYSB0eXBlIGRlZmluaXRpb25zXG5cdCAqL1xuXHRhbmFseXplRmlsZSAoc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IEFuYWx5emVSZXN1bHQge1xuXHRcdHRoaXMuZXJyb3JzID0gW107XG5cdFx0Ly8gRW5zdXJlIHBhcmVudCBub2RlcyBhcmUgc2V0IGZvciBBU1QgdHJhdmVyc2FsXG5cdFx0dGhpcy5zZXRQYXJlbnROb2Rlc0luU291cmNlRmlsZShzb3VyY2VGaWxlKTtcblx0XHR0aGlzLnZpc2l0Tm9kZShzb3VyY2VGaWxlLCBzb3VyY2VGaWxlKTtcblxuXHRcdHJldHVybiB7XG5cdFx0XHR0eXBlcyAgOiB0aGlzLmdyYXBoLmdldEFsbFR5cGVzKCksXG5cdFx0XHRlcnJvcnMgOiB0aGlzLmVycm9ycyxcblx0XHR9O1xuXHR9XG5cblx0LyoqXG5cdCAqIEFuYWx5emUgc291cmNlIGNvZGUgc3RyaW5nXG5cdCAqL1xuXHRhbmFseXplU291cmNlIChzb3VyY2VDb2RlOiBzdHJpbmcsIGZpbGVOYW1lID0gJ3RlbXAudHMnKTogQW5hbHl6ZVJlc3VsdCB7XG5cdFx0Y29uc3Qgc291cmNlRmlsZSA9IHRzLmNyZWF0ZVNvdXJjZUZpbGUoXG5cdFx0XHRmaWxlTmFtZSxcblx0XHRcdHNvdXJjZUNvZGUsXG5cdFx0XHR0cy5TY3JpcHRUYXJnZXQuTGF0ZXN0LFxuXHRcdFx0dHJ1ZVxuXHRcdCk7XG5cdFx0cmV0dXJuIHRoaXMuYW5hbHl6ZUZpbGUoc291cmNlRmlsZSk7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IHRoZSB0eXBlIGdyYXBoXG5cdCAqL1xuXHRnZXRHcmFwaCAoKTogVHlwZUdyYXBoSW1wbCB7XG5cdFx0cmV0dXJuIHRoaXMuZ3JhcGg7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBkZWZpbml0aW9uc1xuXHQgKi9cblx0Z2V0RGVmaW5pdGlvbnMgKCk6IE1hcDxzdHJpbmcsIERlZmluaXRpb25JbmZvPiB7XG5cdFx0cmV0dXJuIHRoaXMuZGVmaW5pdGlvbnM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCB1c2FnZXNcblx0ICovXG5cdGdldFVzYWdlcyAoKTogTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+IHtcblx0XHRyZXR1cm4gdGhpcy51c2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBFRFMgdXNhZ2VzXG5cdCAqL1xuXHRnZXRFRFNVc2FnZXMgKCk6IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4ge1xuXHRcdHJldHVybiB0aGlzLmVkc1VzYWdlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGZsb3cgdXNhZ2VzXG5cdCAqL1xuXHRnZXRGbG93VXNhZ2VzICgpOiBNYXA8c3RyaW5nLCBGbG93SW5mb1tdPiB7XG5cdFx0cmV0dXJuIHRoaXMuZmxvd1VzYWdlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBBZGQgYSB0b3BvbG9naWNhIHR5cGUgdG8gdGhlIGFuYWx5emVyIGZvciB1c2FnZSB0cmFja2luZy5cblx0ICogVGhpcyBhbGxvd3MgdGhlIGFuYWx5emVyIHRvIHJlY29nbml6ZSB0b3BvbG9naWNhIHR5cGVzIHdoZW4gY29sbGVjdGluZyB1c2FnZXMuXG5cdCAqL1xuXHRhZGRUb3BvbG9naWNhVHlwZSAoZnVsbFBhdGg6IHN0cmluZywgbm9kZTogaW1wb3J0KCcuL3R5cGVzJykuVHlwZU5vZGUpOiB2b2lkIHtcblx0XHQvLyBTa2lwIGlmIGFscmVhZHkgZXhpc3RzXG5cdFx0aWYgKHRoaXMuZ3JhcGguYWxsVHlwZXMuaGFzKGZ1bGxQYXRoKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEFkZCB0byBncmFwaCBzbyBpdCBjYW4gYmUgZm91bmQgZHVyaW5nIHVzYWdlIGNvbGxlY3Rpb25cblx0XHRpZiAobm9kZS5wYXJlbnQpIHtcblx0XHRcdC8vIEFkZCBhcyBjaGlsZCBvZiBwYXJlbnRcblx0XHRcdHRoaXMuZ3JhcGguYWRkQ2hpbGQobm9kZS5wYXJlbnQsIG5vZGUpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHQvLyBBZGQgYXMgcm9vdFxuXHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KG5vZGUpO1xuXHRcdH1cblxuXHRcdC8vIEFsc28gYWRkIHRvIGRlZmluaXRpb25zIHNvIGl0J3MgcmVjb2duaXplZCBhcyBhIGtub3duIHR5cGVcblx0XHRjb25zdCBkZWZpbml0aW9uOiBEZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogbm9kZS5uYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHtub2RlLnNvdXJjZUZpbGV9OiR7bm9kZS5saW5lfToke25vZGUuY29sdW1ufWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiBub2RlLnBhcmVudCA/IG5vZGUucGFyZW50LmZ1bGxQYXRoIDogbnVsbCxcblx0XHRcdHN0cmljdENoYWluIDogdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogZmFsc2Vcblx0XHR9O1xuXHRcdHRoaXMuZGVmaW5pdGlvbnMuc2V0KGZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBTZXQgcGFyZW50IG5vZGVzIGluIGEgc291cmNlIGZpbGUgdG8gZW5hYmxlIEFTVCB0cmF2ZXJzYWwgdXBcblx0ICovXG5cdHByaXZhdGUgc2V0UGFyZW50Tm9kZXNJblNvdXJjZUZpbGUgKHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCBzZXRQYXJlbnQgPSAobm9kZTogdHMuTm9kZSwgcGFyZW50PzogdHMuTm9kZSkgPT4ge1xuXHRcdFx0Ly8gVHlwZVNjcmlwdCBkb2Vzbid0IGV4cG9zZSBwYXJlbnQgYXMgd3JpdGFibGUsIGJ1dCB3ZSBuZWVkIGl0XG5cdFx0XHQvLyBlc2xpbnQtZGlzYWJsZS1uZXh0LWxpbmUgQHR5cGVzY3JpcHQtZXNsaW50L25vLWV4cGxpY2l0LWFueVxuXHRcdFx0KG5vZGUgYXMgYW55KS5wYXJlbnQgPSBwYXJlbnQ7XG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgY2hpbGQgPT4gc2V0UGFyZW50KGNoaWxkLCBub2RlKSk7XG5cdFx0fTtcblx0XHRzZXRQYXJlbnQoc291cmNlRmlsZSk7XG5cdH1cblxuXHQvKipcblx0ICogVmlzaXQgYSBub2RlIGluIHRoZSBBU1Rcblx0ICovXG5cdHByaXZhdGUgdmlzaXROb2RlIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLCBjdXJyZW50Q2xhc3M/OiB0cy5DbGFzc0RlY2xhcmF0aW9uKTogdm9pZCB7XG5cdFx0Ly8gVHJhY2sgbW5lbW9uaWNhIG1vZHVsZS1vYmplY3QgYWxpYXNlcyBhbmQgY3VzdG9tIGNvbGxlY3Rpb24gdmFyaWFibGVzXG5cdFx0Ly8gYmVmb3JlIHByb2Nlc3NpbmcgZGVmaW5lKCkvbG9va3VwKCkgY2FsbHMgc28gc291cmNlIHJlc29sdXRpb24gd29ya3MuXG5cdFx0dGhpcy50cmFja0ltcG9ydHMobm9kZSk7XG5cdFx0dGhpcy50cmFja01vZHVsZU9iamVjdEFsaWFzZXMobm9kZSk7XG5cdFx0dGhpcy50cmFja0NvbGxlY3Rpb25BbGlhc2VzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIGRlZmluZSgpIGNhbGxzXG5cdFx0aWYgKHRoaXMuaXNEZWZpbmVDYWxsKG5vZGUpKSB7XG5cdFx0XHR0aGlzLnByb2Nlc3NEZWZpbmVDYWxsKG5vZGUgYXMgdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGUpO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBsYXp5KCkgY2FsbHNcblx0XHRpZiAodGhpcy5pc0xhenlDYWxsKG5vZGUpKSB7XG5cdFx0XHR0aGlzLnByb2Nlc3NMYXp5Q2FsbChub2RlIGFzIHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgZGVjb3JhdGUoKSBkZWNvcmF0b3Jcblx0XHRpZiAodGhpcy5pc0RlY29yYXRlRGVjb3JhdG9yKG5vZGUpKSB7XG5cdFx0XHR0aGlzLnByb2Nlc3NEZWNvcmF0ZURlY29yYXRvcihub2RlIGFzIHRzLkRlY29yYXRvciwgc291cmNlRmlsZSwgY3VycmVudENsYXNzKTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgdHlwZSB1c2FnZXMgKG5ldyBUeXBlKCksIHR5cGUgYW5ub3RhdGlvbnMsIGV0Yy4pXG5cdFx0dGhpcy5jb2xsZWN0VXNhZ2Uobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgRURTIHBhdHRlcm5zICh3cmFwLCBsaW5rLCBnZXRMYXN0Q29udGV4dCwgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RFRFMobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgbmF0aXZlIGZsb3cgcGF0dGVybnMgKHByb3BlcnR5IGFjY2VzcywgbWV0aG9kIGNhbGxzLCBldGMuKVxuXHRcdHRoaXMuY29sbGVjdEZsb3cobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDb2xsZWN0IHR5cGUgYWxpYXNlcyBmb3IgcmVzb2x2aW5nIHR5cGUgcmVmZXJlbmNlc1xuXHRcdGlmICh0cy5pc1R5cGVBbGlhc0RlY2xhcmF0aW9uKG5vZGUpICYmIHRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpKSB7XG5cdFx0XHR0aGlzLnR5cGVBbGlhc2VzLnNldChub2RlLm5hbWUudGV4dCwgbm9kZS50eXBlKTtcblx0XHR9XG5cblx0XHQvLyBUcmFjayBjbGFzcyBkZWNsYXJhdGlvbnMgZm9yIGRlY29yYXRvciBwYXJlbnQgbG9va3VwXG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0Ly8gVmlzaXQgY2hpbGRyZW4gd2l0aCB0aGlzIGNsYXNzIGFzIHRoZSBjdXJyZW50IGNvbnRleHRcblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCBjaGlsZCA9PiB0aGlzLnZpc2l0Tm9kZShjaGlsZCwgc291cmNlRmlsZSwgbm9kZSkpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHQvLyBSZWN1cnNpdmVseSB2aXNpdCBjaGlsZHJlblxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHRoaXMudmlzaXROb2RlKGNoaWxkLCBzb3VyY2VGaWxlLCBjdXJyZW50Q2xhc3MpKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgaW1wb3J0cyBmcm9tICdtbmVtb25pY2EnIHNvIGFsaWFzZXMgb2YgdGhlIG1vZHVsZSBvYmplY3QgYW5kXG5cdCAqIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbiBhcmUgcmVjb2duaXplZCB3aXRob3V0IHJlbHlpbmcgb24gdGhlIHR5cGUgY2hlY2tlci5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tJbXBvcnRzIChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc0ltcG9ydERlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBtb2R1bGVTcGVjaWZpZXIgfSA9IG5vZGU7XG5cdFx0aWYgKCF0cy5pc1N0cmluZ0xpdGVyYWwobW9kdWxlU3BlY2lmaWVyKSB8fCBtb2R1bGVTcGVjaWZpZXIudGV4dCAhPT0gJ21uZW1vbmljYScpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCBjbGF1c2UgPSBub2RlLmltcG9ydENsYXVzZTtcblx0XHRpZiAoIWNsYXVzZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGltcG9ydCB7IG1uZW1vbmljYSwgY3JlYXRlVHlwZXNDb2xsZWN0aW9uIH0gZnJvbSAnbW5lbW9uaWNhJ1xuXHRcdGlmIChjbGF1c2UubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVkSW1wb3J0cyhjbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBjbGF1c2UubmFtZWRCaW5kaW5ncy5lbGVtZW50cykge1xuXHRcdFx0XHRjb25zdCBsb2NhbE5hbWUgPSBlbGVtZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgaW1wb3J0ZWROYW1lID0gZWxlbWVudC5wcm9wZXJ0eU5hbWVcblx0XHRcdFx0XHQ/IGVsZW1lbnQucHJvcGVydHlOYW1lLnRleHRcblx0XHRcdFx0XHQ6IGxvY2FsTmFtZTtcblx0XHRcdFx0aWYgKGltcG9ydGVkTmFtZSA9PT0gJ21uZW1vbmljYScpIHtcblx0XHRcdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQobG9jYWxOYW1lKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoaW1wb3J0ZWROYW1lID09PSAnY3JlYXRlVHlwZXNDb2xsZWN0aW9uJykge1xuXHRcdFx0XHRcdHRoaXMuY3JlYXRlVHlwZXNDb2xsZWN0aW9uVmFyaWFibGVzLmFkZChsb2NhbE5hbWUpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0ICogYXMgbW5lbW9uaWNhIGZyb20gJ21uZW1vbmljYSdcblx0XHRpZiAoY2xhdXNlLm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lc3BhY2VJbXBvcnQoY2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQoY2xhdXNlLm5hbWVkQmluZGluZ3MubmFtZS50ZXh0KTtcblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgbW5lbW9uaWNhIGZyb20gJ21uZW1vbmljYScgKGRlZmF1bHQgaW1wb3J0KSDigJQgdHJlYXQgYXMgbW9kdWxlIG9iamVjdCB0b29cblx0XHRpZiAoY2xhdXNlLm5hbWUpIHtcblx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChjbGF1c2UubmFtZS50ZXh0KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgYWxpYXNlcyBvZiB0aGUgbW5lbW9uaWNhIG1vZHVsZSBvYmplY3QsIGUuZy46XG5cdCAqICAgY29uc3QgbSA9IG1uZW1vbmljYTtcblx0ICogICBjb25zdCBBcHAgPSBtO1xuXHQgKi9cblx0cHJpdmF0ZSB0cmFja01vZHVsZU9iamVjdEFsaWFzZXMgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSB8fCAhdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGluaXRpYWxpemVyIH0gPSBub2RlO1xuXHRcdGlmICghaW5pdGlhbGl6ZXIpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGluaXRpYWxpemVyKSAmJiB0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoaW5pdGlhbGl6ZXIudGV4dCkpIHtcblx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChub2RlLm5hbWUudGV4dCk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFRyYWNrIGN1c3RvbSBjb2xsZWN0aW9uIHZhcmlhYmxlcywgZS5nLjpcblx0ICogICBjb25zdCBNeUNvbGxlY3Rpb24gPSBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKTtcblx0ICogICBjb25zdCBPdGhlciA9IE15Q29sbGVjdGlvbjtcblx0ICpcblx0ICogQWxzbyBkZXRlY3RzIE9wdGlvbiBCIHVzZXItcHJvdmlkZWQgcmVnaXN0cnkgaW50ZXJmYWNlczpcblx0ICogICBleHBvcnQgaW50ZXJmYWNlIE15Q29sbGVjdGlvblJlZ2lzdHJ5IHt9XG5cdCAqICAgY29uc3QgTXlDb2xsZWN0aW9uID0gY3JlYXRlVHlwZXNDb2xsZWN0aW9uPE15Q29sbGVjdGlvblJlZ2lzdHJ5PigpO1xuXHQgKi9cblx0cHJpdmF0ZSB0cmFja0NvbGxlY3Rpb25BbGlhc2VzIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgfHwgIXRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBpbml0aWFsaXplciB9ID0gbm9kZTtcblx0XHRpZiAoIWluaXRpYWxpemVyKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRGlyZWN0IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIGNhbGxcblx0XHRpZiAodGhpcy5pc0NyZWF0ZVR5cGVzQ29sbGVjdGlvbkNhbGwoaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRjb25zdCBjb2xsZWN0aW9uSWQgPSB0aGlzLm5leHRDb2xsZWN0aW9uSWQoKTtcblx0XHRcdHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5zZXQobm9kZS5uYW1lLnRleHQsIGNvbGxlY3Rpb25JZCk7XG5cblx0XHRcdGNvbnN0IHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA9IHRoaXMuZXh0cmFjdFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZShcblx0XHRcdFx0aW5pdGlhbGl6ZXIgYXMgdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0XHRcdHNvdXJjZUZpbGVcblx0XHRcdCk7XG5cdFx0XHR0aGlzLmNvbGxlY3Rpb25JbmZvLnNldChjb2xsZWN0aW9uSWQsIHtcblx0XHRcdFx0dmFyaWFibGVOYW1lICAgICAgICAgIDogbm9kZS5uYW1lLnRleHQsXG5cdFx0XHRcdHNvdXJjZUZpbGUgICAgICAgICAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA6IHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZVxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gQWxpYXMgb2YgYW5vdGhlciBjb2xsZWN0aW9uIHZhcmlhYmxlXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihpbml0aWFsaXplcikpIHtcblx0XHRcdGNvbnN0IGV4aXN0aW5nID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChpbml0aWFsaXplci50ZXh0KTtcblx0XHRcdGlmIChleGlzdGluZykge1xuXHRcdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuc2V0KG5vZGUubmFtZS50ZXh0LCBleGlzdGluZyk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdGhlIHJlZ2lzdHJ5IGludGVyZmFjZSBuYW1lIGZyb20gY3JlYXRlVHlwZXNDb2xsZWN0aW9uPFJlZ2lzdHJ5PigpXG5cdCAqIHdoZW4gdGhlIGludGVyZmFjZSBpcyBkZWNsYXJlZCBpbiB0aGUgc2FtZSBzb3VyY2UgZmlsZS5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSAoXG5cdFx0Y2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZVxuXHQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IHR5cGVBcmdzID0gY2FsbC50eXBlQXJndW1lbnRzO1xuXHRcdGlmICghdHlwZUFyZ3MgfHwgdHlwZUFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZpcnN0VHlwZUFyZyA9IHR5cGVBcmdzWyAwIF07XG5cdFx0aWYgKCF0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKGZpcnN0VHlwZUFyZykgfHwgIXRzLmlzSWRlbnRpZmllcihmaXJzdFR5cGVBcmcudHlwZU5hbWUpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IG5hbWUgPSBmaXJzdFR5cGVBcmcudHlwZU5hbWUudGV4dDtcblxuXHRcdC8vIENvbmZpcm0gdGhlIGludGVyZmFjZSBleGlzdHMgaW4gdGhlIHNhbWUgc291cmNlIGZpbGUuXG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc291cmNlRmlsZS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzSW50ZXJmYWNlRGVjbGFyYXRpb24oc3RhdGVtZW50KSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIG5hbWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgdGhlIHJlZ2lzdHJ5IGludGVyZmFjZSBuYW1lIGZvciBhIGNvbGxlY3Rpb24gaWQuXG5cdCAqL1xuXHRwcml2YXRlIGdldFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSAoY29sbGVjdGlvbklkPzogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIWNvbGxlY3Rpb25JZCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0cmV0dXJuIHRoaXMuY29sbGVjdGlvbkluZm8uZ2V0KGNvbGxlY3Rpb25JZCk/LnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhbiBleHByZXNzaW9uIGlzIGEgY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgY2FsbC5cblx0ICogSGFuZGxlczpcblx0ICogICBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKVxuXHQgKiAgIGN0YygpIC8vIGFsaWFzZWQgaW1wb3J0XG5cdCAqICAgbW5lbW9uaWNhLmNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIC8vIG1vZHVsZSBvYmplY3QgbWV0aG9kXG5cdCAqICAgbS5jcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSAvLyBhbGlhc2VkIG1vZHVsZSBvYmplY3Rcblx0ICovXG5cdHByaXZhdGUgaXNDcmVhdGVUeXBlc0NvbGxlY3Rpb25DYWxsIChub2RlOiB0cy5Ob2RlKTogbm9kZSBpcyB0cy5DYWxsRXhwcmVzc2lvbiB7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXHRcdGNvbnN0IGV4cHIgPSBub2RlLmV4cHJlc3Npb247XG5cblx0XHQvLyBEaXJlY3QgY2FsbCBvciBhbGlhc2VkIGltcG9ydDogY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgLyBjdGMoKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLnRleHQgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nIHx8XG5cdFx0XHRcdHRoaXMuY3JlYXRlVHlwZXNDb2xsZWN0aW9uVmFyaWFibGVzLmhhcyhleHByLnRleHQpO1xuXHRcdH1cblxuXHRcdC8vIE1vZHVsZSBvYmplY3QgbWV0aG9kOiBtbmVtb25pY2EuY3JlYXRlVHlwZXNDb2xsZWN0aW9uKClcblx0XHRpZiAoXG5cdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSAmJlxuXHRcdFx0ZXhwci5uYW1lLnRleHQgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIoZXhwci5leHByZXNzaW9uKSAmJlxuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuaGFzKGV4cHIuZXhwcmVzc2lvbi50ZXh0KVxuXHRcdCkge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdlbmVyYXRlIGEgdW5pcXVlIGNvbGxlY3Rpb24gaWRlbnRpZmllci5cblx0ICovXG5cdHByaXZhdGUgbmV4dENvbGxlY3Rpb25JZCAoKTogc3RyaW5nIHtcblx0XHR0aGlzLmNvbGxlY3Rpb25Db3VudGVyKys7XG5cdFx0Y29uc3QgcmVzdWx0ID0gYGNvbGxlY3Rpb25fJHt0aGlzLmNvbGxlY3Rpb25Db3VudGVyfWA7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhIG5vZGUgaXMgYSBkZWZpbmUoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGlzRGVmaW5lQ2FsbCAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuQ2FsbEV4cHJlc3Npb24ge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBkaXJlY3QgY2FsbDogZGVmaW5lKCdUeXBlTmFtZScsIC4uLilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2RlZmluZScpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBtZXRob2QgY2FsbDogU29tZVR5cGUuZGVmaW5lKCdTdWJUeXBlJywgLi4uKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuIGV4cHJlc3Npb24ubmFtZT8udGV4dCA9PT0gJ2RlZmluZSc7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGEgbm9kZSBpcyBhIGxhenkoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGlzTGF6eUNhbGwgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkNhbGxFeHByZXNzaW9uIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IG5vZGU7XG5cblx0XHQvLyBDaGVjayBmb3IgZGlyZWN0IGNhbGw6IGxhenkoJ1R5cGVOYW1lJywgZ2V0dGVyLCAuLi4pXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLnRleHQgPT09ICdsYXp5Jykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIG1ldGhvZCBjYWxsOiBTb21lVHlwZS5sYXp5KCdTdWJUeXBlJywgZ2V0dGVyLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gZXhwcmVzc2lvbi5uYW1lPy50ZXh0ID09PSAnbGF6eSc7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IGNvbmZpZyBvcHRpb25zIGZyb20gYW4gb2JqZWN0IGxpdGVyYWxcblx0XHQqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbCAoY29uZmlnQXJnOiB0cy5PYmplY3RMaXRlcmFsRXhwcmVzc2lvbik6XG5cdFx0eyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9IHtcblx0XHRjb25zdCBjb25maWc6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSA9IHt9O1xuXG5cdFx0Zm9yIChjb25zdCBwcm9wIG9mIGNvbmZpZ0FyZy5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFzc2lnbm1lbnQocHJvcCkgJiYgdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBwcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0aWYgKHByb3BOYW1lID09PSAnc3RyaWN0Q2hhaW4nICYmIHByb3AuaW5pdGlhbGl6ZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5zdHJpY3RDaGFpbiA9IHRydWU7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdzdHJpY3RDaGFpbicgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5zdHJpY3RDaGFpbiA9IGZhbHNlO1xuXHRcdFx0XHR9IGVsc2UgaWYgKHByb3BOYW1lID09PSAnYmxvY2tFcnJvcnMnICYmIHByb3AuaW5pdGlhbGl6ZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5ibG9ja0Vycm9ycyA9IHRydWU7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdibG9ja0Vycm9ycycgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5ibG9ja0Vycm9ycyA9IGZhbHNlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGNvbmZpZztcblx0fVxuXG5cdC8qKlxuXHRcdCogRXh0cmFjdCBjb25maWcgb3B0aW9ucyBmcm9tIGRlZmluZSgpIGNhbGxcblx0XHQqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25maWcgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogeyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9IHtcblx0XHQvLyBDb25maWcgaXMgdGhlIHRoaXJkIGFyZ3VtZW50OiBkZWZpbmUoJ05hbWUnLCBoYW5kbGVyLCBjb25maWcpXG5cdFx0Y29uc3QgY29uZmlnQXJnID0gY2FsbC5hcmd1bWVudHNbIDIgXTtcblx0XHRpZiAoIWNvbmZpZ0FyZyB8fCAhdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihjb25maWdBcmcpKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgY29uZmlnUmVzdWx0ID0gdGhpcy5leHRyYWN0Q29uZmlnRnJvbU9iamVjdExpdGVyYWwoY29uZmlnQXJnKTtcblx0XHRyZXR1cm4gY29uZmlnUmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0KiBDaGVjayBpZiBhIG5vZGUgaXMgYSBAZGVjb3JhdGUoKSBkZWNvcmF0b3Jcblx0XHQqL1xuXHRwcml2YXRlIGlzRGVjb3JhdGVEZWNvcmF0b3IgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkRlY29yYXRvciB7XG5cdFx0aWYgKCF0cy5pc0RlY29yYXRvcihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBAZGVjb3JhdGVcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2RlY29yYXRlJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIEBkZWNvcmF0ZSgpIG9yIEBkZWNvcmF0ZShQYXJlbnRUeXBlKVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRjb25zdCBmbk5hbWUgPSBleHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGZuTmFtZSkgJiYgZm5OYW1lLnRleHQgPT09ICdkZWNvcmF0ZScpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cblx0XHRcdC8vIENoZWNrIGZvciBATXlDb2xsZWN0aW9uLmRlY29yYXRlKCkgd2hlcmUgTXlDb2xsZWN0aW9uIGlzIGEgY3VzdG9tIGNvbGxlY3Rpb25cblx0XHRcdGlmIChcblx0XHRcdFx0dHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZm5OYW1lKSAmJlxuXHRcdFx0XHRmbk5hbWUubmFtZS50ZXh0ID09PSAnZGVjb3JhdGUnICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihmbk5hbWUuZXhwcmVzc2lvbikgJiZcblx0XHRcdFx0dGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmhhcyhmbk5hbWUuZXhwcmVzc2lvbi50ZXh0KVxuXHRcdFx0KSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBNYXJrIGEgY2FsbCBleHByZXNzaW9uIGFzIHByb2Nlc3NlZCBhbmQgcmV0dXJuIHdoZXRoZXIgaXQgYWxyZWFkeSB3YXMuXG5cdCAqL1xuXHRwcml2YXRlIG1hcmtQcm9jZXNzZWQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgbWFya2VkID0gY2FsbCBhcyB1bmtub3duIGFzIHsgX190YWN0aWNhX3Byb2Nlc3NlZD86IGJvb2xlYW4gfTtcblx0XHRpZiAobWFya2VkLl9fdGFjdGljYV9wcm9jZXNzZWQpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHRtYXJrZWQuX190YWN0aWNhX3Byb2Nlc3NlZCA9IHRydWU7XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb2Nlc3MgYSBkZWZpbmUoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NEZWZpbmVDYWxsIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGlmIHRoaXMgZXhhY3QgY2FsbCBoYXMgYWxyZWFkeSBiZWVuIHByb2Nlc3NlZCAocHJldmVudHMgZHVwbGljYXRlcyBmcm9tIGNoYWluZWQgY2FsbHMpXG5cdFx0aWYgKHRoaXMubWFya1Byb2Nlc3NlZChjYWxsKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEdldCB0aGUgdHlwZSBuYW1lIGFuZCBzb3VyY2UgY29udGV4dCBmcm9tIGFyZ3VtZW50c1xuXHRcdGNvbnN0IGRlZmluZUNvbnRleHQgPSB0aGlzLmV4dHJhY3REZWZpbmVDb250ZXh0KGNhbGwpO1xuXG5cdFx0Ly8gRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBkZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKSwgd2Ugd2FudCB0aGUgcG9zaXRpb24gb2YgdGhlIC5kZWZpbmUoJ0InKSBwYXJ0XG5cdFx0Ly8gbm90IHRoZSBzdGFydCBvZiB0aGUgZW50aXJlIGV4cHJlc3Npb25cblx0XHRsZXQgcG9zaXRpb25Ob2RlOiB0cy5Ob2RlID0gY2FsbDtcblxuXHRcdC8vIElmIHRoaXMgaXMgYSBjaGFpbmVkIGNhbGwsIGdldCB0aGUgcG9zaXRpb24gb2YgdGhlIHByb3BlcnR5IGFjY2VzcyBleHByZXNzaW9uXG5cdFx0Ly8gd2hpY2ggaXMgdGhlIC5kZWZpbmUgcGFydFxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHQvLyBUaGUgZXhwcmVzc2lvbiBpcyB0aGUgcHJvcGVydHkgYWNjZXNzOiAoZGVmaW5lKCdSb290QXN5bmMnLCAuLi4pKS5kZWZpbmVcblx0XHRcdC8vIFdlIHdhbnQgdGhlIHBvc2l0aW9uIG9mIGp1c3QgdGhlIC5kZWZpbmUgcGFydFxuXHRcdFx0cG9zaXRpb25Ob2RlID0gY2FsbC5leHByZXNzaW9uLm5hbWU7IC8vIFRoaXMgaXMgdGhlICdkZWZpbmUnIGlkZW50aWZpZXJcblx0XHR9XG5cblx0XHRjb25zdCBzdGFydFBvcyA9IHBvc2l0aW9uTm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKTtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oc291cmNlRmlsZSwgc3RhcnRQb3MpO1xuXG5cdFx0aWYgKCFkZWZpbmVDb250ZXh0LnR5cGVOYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdDb3VsZCBub3QgZXh0cmFjdCB0eXBlIG5hbWUgZnJvbSBkZWZpbmUoKSBjYWxsJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IHR5cGVOYW1lIH0gPSBkZWZpbmVDb250ZXh0O1xuXG5cdFx0Ly8gRGV0ZXJtaW5lIHBhcmVudCB0eXBlIGFuZCBjb2xsZWN0aW9uIGJhc2VkIG9uIHRoZSBjYWxsIHNvdXJjZS5cblx0XHRjb25zdCBwYXJlbnROb2RlID0gZGVmaW5lQ29udGV4dC5wYXJlbnRUeXBlO1xuXHRcdGNvbnN0IHsgY29sbGVjdGlvbklkIH0gPSBkZWZpbmVDb250ZXh0O1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25maWcgb3B0aW9uc1xuXHRcdGNvbnN0IGNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZyhjYWxsKTtcblxuXHRcdC8vIENyZWF0ZSB0eXBlIG5vZGUgZmlyc3Qgc28gaXRzIGludGVybmFsIGZ1bGxQYXRoIChpbmNsdWRpbmcgYW55IGNvbGxlY3Rpb24gcHJlZml4KSBpcyByZXNvbHZlZC5cblx0XHRjb25zdCBub2RlID0gVHlwZUdyYXBoSW1wbC5jcmVhdGVOb2RlKFxuXHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRwYXJlbnROb2RlLFxuXHRcdFx0c291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdGxpbmUgKyAxLFxuXHRcdFx0Y2hhcmFjdGVyICsgMSxcblx0XHRcdGNvbGxlY3Rpb25JZFxuXHRcdCk7XG5cdFx0bm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWUgPSB0aGlzLmdldFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZShjb2xsZWN0aW9uSWQpO1xuXG5cdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gY29uc3RydWN0b3IgZnVuY3Rpb25cblx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzKGNhbGwpO1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZvciBUeXBlUmVnaXN0cnkgc2lnbmF0dXJlXG5cdFx0bm9kZS5jb25zdHJ1Y3RvclBhcmFtcyA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zKGNhbGwpO1xuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoXG5cdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkQ2hpbGQocGFyZW50Tm9kZSwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cblx0XHQvLyBDcmVhdGUgZGVmaW5pdGlvbiBpbmZvIHVzaW5nIHRoZSBub2RlJ3MgcmVzb2x2ZWQgZnVsbFBhdGhcblx0XHRjb25zdCBkZWZpbml0aW9uOiBEZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogcGFyZW50Tm9kZSA/IHBhcmVudE5vZGUuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiBjb25maWcuc3RyaWN0Q2hhaW4gPz8gdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogY29uZmlnLmJsb2NrRXJyb3JzID8/IGZhbHNlLFxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQobm9kZS5mdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cblx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50OiBjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKSAtPiBtYXAgXCJVc2VyXCIgdG8gXCJVc2VyRW50aXR5XCJcblx0XHQvLyBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGNvbnN0IFggPSBkZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKSwgd2Ugd2FudCB0byBtYXAgWCAtPiBBICh0aGUgcm9vdClcblx0XHR0aGlzLnRyYWNrVmFyaWFibGVBc3NpZ25tZW50KGNhbGwsIHBhcmVudE5vZGUsIG5vZGUuZnVsbFBhdGgpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb2Nlc3MgYSBsYXp5KCkgY2FsbFxuXHQgKi9cblx0cHJpdmF0ZSBwcm9jZXNzTGF6eUNhbGwgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBleGFjdCBjYWxsIGhhcyBhbHJlYWR5IGJlZW4gcHJvY2Vzc2VkIChwcmV2ZW50cyBkdXBsaWNhdGVzIGZyb20gY2hhaW5lZCBjYWxscylcblx0XHRpZiAodGhpcy5tYXJrUHJvY2Vzc2VkKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gR2V0IHRoZSB0eXBlIG5hbWUgYW5kIHNvdXJjZSBjb250ZXh0IGZyb20gYXJndW1lbnRzXG5cdFx0Y29uc3QgbGF6eUNvbnRleHQgPSB0aGlzLmV4dHJhY3RMYXp5Q29udGV4dChjYWxsLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIEZvciBjaGFpbmVkIGNhbGxzIGxpa2UgZGVmaW5lKCdBJykubGF6eSgnQicpLCB3ZSB3YW50IHRoZSBwb3NpdGlvbiBvZiB0aGUgLmxhenkoJ0InKSBwYXJ0XG5cdFx0Ly8gbm90IHRoZSBzdGFydCBvZiB0aGUgZW50aXJlIGV4cHJlc3Npb25cblx0XHRsZXQgcG9zaXRpb25Ob2RlOiB0cy5Ob2RlID0gY2FsbDtcblxuXHRcdC8vIElmIHRoaXMgaXMgYSBjaGFpbmVkIGNhbGwsIGdldCB0aGUgcG9zaXRpb24gb2YgdGhlIHByb3BlcnR5IGFjY2VzcyBleHByZXNzaW9uXG5cdFx0Ly8gd2hpY2ggaXMgdGhlIC5sYXp5IHBhcnRcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0Ly8gVGhlIGV4cHJlc3Npb24gaXMgdGhlIHByb3BlcnR5IGFjY2VzczogKGRlZmluZSgnUm9vdEFzeW5jJywgLi4uKSkubGF6eVxuXHRcdFx0Ly8gV2Ugd2FudCB0aGUgcG9zaXRpb24gb2YganVzdCB0aGUgLmxhenkgcGFydFxuXHRcdFx0cG9zaXRpb25Ob2RlID0gY2FsbC5leHByZXNzaW9uLm5hbWU7IC8vIFRoaXMgaXMgdGhlICdsYXp5JyBpZGVudGlmaWVyXG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnRQb3MgPSBwb3NpdGlvbk5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSk7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKHNvdXJjZUZpbGUsIHN0YXJ0UG9zKTtcblxuXHRcdGlmICghbGF6eUNvbnRleHQudHlwZU5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0NvdWxkIG5vdCBleHRyYWN0IHR5cGUgbmFtZSBmcm9tIGxhenkoKSBjYWxsJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IHR5cGVOYW1lIH0gPSBsYXp5Q29udGV4dDtcblxuXHRcdC8vIERldGVybWluZSBwYXJlbnQgdHlwZSBhbmQgY29sbGVjdGlvbiBiYXNlZCBvbiB0aGUgY2FsbCBzb3VyY2UuXG5cdFx0Y29uc3QgcGFyZW50Tm9kZSA9IGxhenlDb250ZXh0LnBhcmVudFR5cGU7XG5cdFx0Y29uc3QgeyBjb2xsZWN0aW9uSWQgfSA9IGxhenlDb250ZXh0O1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25maWcgb3B0aW9uc1xuXHRcdGNvbnN0IGNvbmZpZyA9IHRoaXMuZXh0cmFjdExhenlDb25maWcoY2FsbCk7XG5cblx0XHQvLyBDcmVhdGUgdHlwZSBub2RlIGZpcnN0IHNvIGl0cyBpbnRlcm5hbCBmdWxsUGF0aCAoaW5jbHVkaW5nIGFueSBjb2xsZWN0aW9uIHByZWZpeCkgaXMgcmVzb2x2ZWQuXG5cdFx0Y29uc3Qgbm9kZSA9IFR5cGVHcmFwaEltcGwuY3JlYXRlTm9kZShcblx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0cGFyZW50Tm9kZSxcblx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRsaW5lICsgMSxcblx0XHRcdGNoYXJhY3RlciArIDEsXG5cdFx0XHRjb2xsZWN0aW9uSWRcblx0XHQpO1xuXHRcdG5vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lID0gdGhpcy5nZXRSZWdpc3RyeUludGVyZmFjZU5hbWUoY29sbGVjdGlvbklkKTtcblxuXHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIHRoZSBjb25zdHJ1Y3RvciByZXR1cm5lZCBieSB0aGUgbGF6eSBnZXR0ZXJcblx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzKGNhbGwpO1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZvciBUeXBlUmVnaXN0cnkgc2lnbmF0dXJlXG5cdFx0bm9kZS5jb25zdHJ1Y3RvclBhcmFtcyA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zKGNhbGwpO1xuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoXG5cdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkQ2hpbGQocGFyZW50Tm9kZSwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cblx0XHQvLyBDcmVhdGUgZGVmaW5pdGlvbiBpbmZvIHVzaW5nIHRoZSBub2RlJ3MgcmVzb2x2ZWQgZnVsbFBhdGhcblx0XHRjb25zdCBkZWZpbml0aW9uOiBEZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogcGFyZW50Tm9kZSA/IHBhcmVudE5vZGUuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiBjb25maWcuc3RyaWN0Q2hhaW4gPz8gdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogY29uZmlnLmJsb2NrRXJyb3JzID8/IGZhbHNlLFxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQobm9kZS5mdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cblx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50OiBjb25zdCBMYXp5VHlwZSA9IGxhenkoJ0xhenlUeXBlJywgLi4uKSAtPiBtYXAgXCJMYXp5VHlwZVwiIC0+IFwiTGF6eVR5cGVcIlxuXHRcdC8vIEZvciBjaGFpbmVkIGNhbGxzIGxpa2UgY29uc3QgWCA9IGxhenkoJ0EnKS5kZWZpbmUoJ0InKSwgd2Ugd2FudCB0byBtYXAgWCAtPiBBICh0aGUgcm9vdClcblx0XHR0aGlzLnRyYWNrVmFyaWFibGVBc3NpZ25tZW50KGNhbGwsIHBhcmVudE5vZGUsIG5vZGUuZnVsbFBhdGgpO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgbGF6eSgpIGNhbGwgYXJndW1lbnRzIGludG8gYSBub3JtYWxpemVkIHNoYXBlLlxuXHQgKiBIYW5kbGVzIG5hbWVkL3VubmFtZWQgYW5kIGV4cGxpY2l0LXNvdXJjZSBmb3JtcywgYm90aCBhcyBmcmVlIGNhbGxzXG5cdCAqIGFuZCBhcyBtZXRob2QgY2FsbHMuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q2FsbEFyZ3MgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKToge1xuXHRcdHNvdXJjZT86IHRzLkV4cHJlc3Npb247XG5cdFx0bmFtZT86IHN0cmluZztcblx0XHRnZXR0ZXI6IHRzLkV4cHJlc3Npb247XG5cdFx0Y29uZmlnPzogdHMuRXhwcmVzc2lvbjtcblx0fSB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGNvbnN0IGlzTWV0aG9kQ2FsbCA9IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbik7XG5cblx0XHRpZiAoaXNNZXRob2RDYWxsKSB7XG5cdFx0XHQvLyBTb3VyY2UgaXMgdGhlIG9iamVjdCBvZiB0aGUgcHJvcGVydHkgYWNjZXNzOiBUeXBlLmxhenkoLi4uKVxuXHRcdFx0Y29uc3Qgc291cmNlID0gY2FsbC5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IG1ldGhvZEZpcnN0QXJnID0gYXJnc1sgMCBdO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChtZXRob2RGaXJzdEFyZykpIHtcblx0XHRcdFx0Ly8gVHlwZS5sYXp5KCdOYW1lJywgZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0XHRpZiAoYXJncy5sZW5ndGggPCAyKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHNvdXJjZSxcblx0XHRcdFx0XHRuYW1lICAgOiBtZXRob2RGaXJzdEFyZy50ZXh0LFxuXHRcdFx0XHRcdGdldHRlciA6IGFyZ3NbIDEgXSxcblx0XHRcdFx0XHRjb25maWcgOiBhcmdzWyAyIF0sXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cdFx0XHQvLyBUeXBlLmxhenkoZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0c291cmNlLFxuXHRcdFx0XHRnZXR0ZXIgOiBtZXRob2RGaXJzdEFyZyxcblx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMSBdLFxuXHRcdFx0fTtcblx0XHR9XG5cblx0XHQvLyBGcmVlIGNhbGw6IGxhenkoLi4uKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBmaXJzdEFyZyA9IGFyZ3NbIDAgXTtcblxuXHRcdC8vIEV4cGxpY2l0LXNvdXJjZSBmb3JtOiBsYXp5KHNvdXJjZSwgJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0Ly8gb3IgbGF6eShzb3VyY2UsIGdldHRlciwgY29uZmlnPylcblx0XHRpZiAoYXJncy5sZW5ndGggPj0gMiAmJiB0cy5pc0lkZW50aWZpZXIoZmlyc3RBcmcpKSB7XG5cdFx0XHRjb25zdCBzZWNvbmRBcmcgPSBhcmdzWyAxIF07XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKHNlY29uZEFyZykpIHtcblx0XHRcdFx0Ly8gbGF6eShzb3VyY2UsICdOYW1lJywgZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0XHRpZiAoYXJncy5sZW5ndGggPCAzKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHNvdXJjZSA6IGZpcnN0QXJnLFxuXHRcdFx0XHRcdG5hbWUgICA6IHNlY29uZEFyZy50ZXh0LFxuXHRcdFx0XHRcdGdldHRlciA6IGFyZ3NbIDIgXSxcblx0XHRcdFx0XHRjb25maWcgOiBhcmdzWyAzIF0sXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cdFx0XHQvLyBsYXp5KHNvdXJjZSwgZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0c291cmNlIDogZmlyc3RBcmcsXG5cdFx0XHRcdGdldHRlciA6IHNlY29uZEFyZyxcblx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMiBdLFxuXHRcdFx0fTtcblx0XHR9XG5cblx0XHQvLyBOYW1lZCByb290IGZvcm06IGxhenkoJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChmaXJzdEFyZykpIHtcblx0XHRcdGlmIChhcmdzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB7XG5cdFx0XHRcdG5hbWUgICA6IGZpcnN0QXJnLnRleHQsXG5cdFx0XHRcdGdldHRlciA6IGFyZ3NbIDEgXSxcblx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMiBdLFxuXHRcdFx0fTtcblx0XHR9XG5cblx0XHQvLyBVbm5hbWVkIHJvb3QgZm9ybTogbGF6eShnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0cmV0dXJuIHtcblx0XHRcdGdldHRlciA6IGZpcnN0QXJnLFxuXHRcdFx0Y29uZmlnIDogYXJnc1sgMSBdLFxuXHRcdH07XG5cdH1cblxuXHQvKipcblx0ICogVW53cmFwIHRoZSBjb25zdHJ1Y3RvciByZXR1cm5lZCBieSBhIGxhenkgZ2V0dGVyLlxuXHQgKiBTdXBwb3J0czpcblx0ICogICAoKSA9PiBjbGFzcyBOYW1lIHt9XG5cdCAqICAgKCkgPT4gZnVuY3Rpb24gTmFtZSgpIHt9XG5cdCAqICAgKCkgPT4geyByZXR1cm4gY2xhc3MgTmFtZSB7fTsgfVxuXHQgKiAgIGZ1bmN0aW9uICgpIHsgcmV0dXJuIGZ1bmN0aW9uIE5hbWUoKSB7fTsgfVxuXHQgKi9cblx0cHJpdmF0ZSB1bndyYXBMYXp5R2V0dGVyIChnZXR0ZXJFeHByOiB0cy5FeHByZXNzaW9uKTogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihnZXR0ZXJFeHByKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBnZXR0ZXJFeHByO1xuXHRcdFx0aWYgKCF0cy5pc0Jsb2NrKGJvZHkpKSB7XG5cdFx0XHRcdHJldHVybiBib2R5O1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBzdG10IG9mIGJvZHkuc3RhdGVtZW50cykge1xuXHRcdFx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQoc3RtdCkgJiYgc3RtdC5leHByZXNzaW9uKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHN0bXQuZXhwcmVzc2lvbjtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oZ2V0dGVyRXhwcikpIHtcblx0XHRcdGNvbnN0IHsgYm9keSB9ID0gZ2V0dGVyRXhwcjtcblx0XHRcdGZvciAoY29uc3Qgc3RtdCBvZiBib2R5LnN0YXRlbWVudHMpIHtcblx0XHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KHN0bXQpICYmIHN0bXQuZXhwcmVzc2lvbikge1xuXHRcdFx0XHRcdHJldHVybiBzdG10LmV4cHJlc3Npb247XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gTm90IGEgcmVjb2duaXplZCBnZXR0ZXIgcGF0dGVyblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBhIGNvbnN0cnVjdG9yIG5hbWUgZnJvbSBhIGNsYXNzIGV4cHJlc3Npb24sIGNsYXNzIGRlY2xhcmF0aW9uLFxuXHQgKiBvciBuYW1lZCBmdW5jdGlvbiBleHByZXNzaW9uLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JOYW1lIChjb25zdHJ1Y3RvckV4cHI6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc0NsYXNzRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpICYmIGNvbnN0cnVjdG9yRXhwci5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gY29uc3RydWN0b3JFeHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihjb25zdHJ1Y3RvckV4cHIpICYmIGNvbnN0cnVjdG9yRXhwci5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gY29uc3RydWN0b3JFeHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikgJiYgY29uc3RydWN0b3JFeHByLm5hbWUpIHtcblx0XHRcdHJldHVybiBjb25zdHJ1Y3RvckV4cHIubmFtZS50ZXh0O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdGhlIHR5cGUgbmFtZSBmcm9tIGVpdGhlciBhIGRlZmluZSgpIG9yIGxhenkoKSBjYWxsLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0TW5lbW9uaWNhVHlwZU5hbWUgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwoY2FsbCkpIHtcblx0XHRcdHJldHVybiB0aGlzLmV4dHJhY3RUeXBlTmFtZShjYWxsKTtcblx0XHR9XG5cdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChjYWxsKSkge1xuXHRcdFx0Y29uc3QgYXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRcdGlmICghYXJncykge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGFyZ3MubmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gYXJncy5uYW1lO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy51bndyYXBMYXp5R2V0dGVyKGFyZ3MuZ2V0dGVyKTtcblx0XHRcdGlmIChjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdFx0cmV0dXJuIHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yTmFtZShjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdGhlIGZ1bGwgbGF6eSgpIGNhbGwgY29udGV4dDogdHlwZSBuYW1lLCBwYXJlbnQgdHlwZSwgYW5kIGNvbGxlY3Rpb24uXG5cdCAqIEhhbmRsZXMgZGlyZWN0IGNhbGxzLCBwcm9wZXJ0eS1hY2Nlc3MgY2FsbHMsIGNoYWluZWQgY2FsbHMsIGFuZCB0aGVcblx0ICogZXhwbGljaXQtc291cmNlIGZvcm0gYGxhenkoc291cmNlLCAnVHlwZU5hbWUnLCBnZXR0ZXIpYC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdExhenlDb250ZXh0IChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHtcblx0XHR0eXBlTmFtZT86IHN0cmluZztcblx0XHRwYXJlbnRUeXBlPzogVHlwZU5vZGU7XG5cdFx0Y29sbGVjdGlvbklkPzogc3RyaW5nO1xuXHR9IHtcblx0XHRjb25zdCBhcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdGlmICghYXJncykge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGxldCB0eXBlTmFtZTogc3RyaW5nIHwgdW5kZWZpbmVkID0gYXJncy5uYW1lO1xuXHRcdGlmICghdHlwZU5hbWUpIHtcblx0XHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMudW53cmFwTGF6eUdldHRlcihhcmdzLmdldHRlcik7XG5cdFx0XHRpZiAoY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRcdHR5cGVOYW1lID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JOYW1lKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGlmICghdHlwZU5hbWUpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IGNhbGw7XG5cblx0XHQvLyBEaXJlY3QgY2FsbDogbGF6eSgnVHlwZU5hbWUnLCAuLi4pIG9yIGxhenkoc291cmNlLCAnVHlwZU5hbWUnLCBnZXR0ZXIpXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLnRleHQgPT09ICdsYXp5Jykge1xuXHRcdFx0aWYgKGFyZ3Muc291cmNlICYmIHRzLmlzSWRlbnRpZmllcihhcmdzLnNvdXJjZSkpIHtcblx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShhcmdzLnNvdXJjZS50ZXh0KTtcblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHR0eXBlTmFtZSxcblx0XHRcdFx0XHRwYXJlbnRUeXBlICAgOiBzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUsXG5cdFx0XHRcdFx0Y29sbGVjdGlvbklkIDogc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQsXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cdFx0XHQvLyBQbGFpbiByb290IGxhenkgaW4gZGVmYXVsdCBjb2xsZWN0aW9uXG5cdFx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2VzczogWC5sYXp5KCdUeXBlTmFtZScsIC4uLilcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi5uYW1lLnRleHQgPT09ICdsYXp5Jykge1xuXHRcdFx0Y29uc3Qgb2JqID0gZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG9iaikpIHtcblx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShvYmoudGV4dCk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBOZXN0ZWQgYWNjZXNzOiBpbnN0YW5jZS5UeXBlLmxhenkgLSB0cnkgdG8gcmVzb2x2ZVxuXHRcdFx0XHRjb25zdCBjaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlDaGFpbihvYmopO1xuXHRcdFx0XHRpZiAoY2hhaW4ubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGNoYWluLmpvaW4oJy4nKSk7XG5cdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlIH07XG5cdFx0XHRcdH1cblx0XHRcdH1cblxuXHRcdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBEZXRlcm1pbmUgdGhlIGNvbGxlY3Rpb24gY29udGV4dCBmcm9tIHRoZSByb290IG9mIHRoZSBjaGFpbiBzbyB0aGF0XG5cdFx0XHRcdC8vIGN1c3RvbS1jb2xsZWN0aW9uIHR5cGVzIGRvIG5vdCBnZXQgY29uZnVzZWQgd2l0aCBkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMuXG5cdFx0XHRcdGNvbnN0IHJvb3RJZCA9IHRoaXMuZ2V0Um9vdElkZW50aWZpZXIob2JqLmV4cHJlc3Npb24pO1xuXHRcdFx0XHRjb25zdCBleHBlY3RlZENvbGxlY3Rpb25JZCA9IHJvb3RJZFxuXHRcdFx0XHRcdD8gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKHJvb3RJZC50ZXh0KS5jb2xsZWN0aW9uSWRcblx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblxuXHRcdFx0XHQvLyBDaGFpbmVkIGNhbGw6IGRlZmluZSgnQScpLmxhenkoJ0InKSBvciBsYXp5KCdBJykubGF6eSgnQicpXG5cdFx0XHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ2FsbChvYmosIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudFR5cGVOYW1lID0gdGhpcy5leHRyYWN0TW5lbW9uaWNhVHlwZU5hbWUob2JqKTtcblx0XHRcdFx0XHRpZiAocGFyZW50VHlwZU5hbWUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKHBhcmVudFR5cGVOYW1lLCBleHBlY3RlZENvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGlmICh0aGlzLmlzTGF6eUNhbGwob2JqKSkge1xuXHRcdFx0XHRcdHRoaXMucHJvY2Vzc0xhenlDYWxsKG9iaiwgc291cmNlRmlsZSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gQnVpbGRlciBsb29rdXAgY2hhaW46IEFwcC5sb29rdXAoJ1VzZXInKS5sYXp5KCdBZG1pbicpXG5cdFx0XHRcdGlmICh0aGlzLmlzTG9va3VwQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0Y29uc3QgbG9va2VkVXBQYXRoID0gdGhpcy5yZXNvbHZlTG9va3VwUGF0aChvYmopO1xuXHRcdFx0XHRcdGlmIChsb29rZWRVcFBhdGgpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGxvb2tlZFVwUGF0aCk7XG5cdFx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGUuY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHsgdHlwZU5hbWUgfTtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGNvbmZpZyBvcHRpb25zIGZyb20gbGF6eSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdExhenlDb25maWcgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogeyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9IHtcblx0XHRjb25zdCBhcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdGlmICghYXJncyB8fCAhYXJncy5jb25maWcgfHwgIXRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24oYXJncy5jb25maWcpKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgY29uZmlnUmVzdWx0ID0gdGhpcy5leHRyYWN0Q29uZmlnRnJvbU9iamVjdExpdGVyYWwoYXJncy5jb25maWcpO1xuXHRcdHJldHVybiBjb25maWdSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHQqIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnRzIHRoYXQgY2FwdHVyZSBkZWZpbmUoKSByZXN1bHRzXG5cdFx0KiBlLmcuLCBjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKSBtYXBzIFwiVXNlclwiIC0+IFwiVXNlckVudGl0eVwiXG5cdFx0KiBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGNvbnN0IFggPSBkZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKSwgd2UgbWFwIFggLT4gQSAodGhlIHJvb3QgdHlwZSlcblx0XHQqL1xuXHRwcml2YXRlIHRyYWNrVmFyaWFibGVBc3NpZ25tZW50IChcblx0XHRjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHRwYXJlbnROb2RlOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCxcblx0XHRmdWxsUGF0aDogc3RyaW5nXG5cdCk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGlmIHRoaXMgY2FsbCBpcyB0aGUgcmlnaHQtaGFuZCBzaWRlIG9mIGEgdmFyaWFibGUgZGVjbGFyYXRpb25cblx0XHQvLyBXYWxrIHVwIHRoZSB0cmVlIHRvIGZpbmQgVmFyaWFibGVEZWNsYXJhdGlvblxuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gY2FsbC5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24oY3VycmVudCkpIHtcblx0XHRcdFx0Ly8gRm91bmQ6IGNvbnN0IFggPSBkZWZpbmUoLi4uKVxuXHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCB2YXJOYW1lID0gY3VycmVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Ly8gSWYgdGhpcyBpcyBhIGNoYWluZWQgY2FsbCAoaGFzIHBhcmVudCksIGRvbid0IG92ZXJ3cml0ZSBleGlzdGluZyBtYXBwaW5nXG5cdFx0XHRcdFx0Ly8gVGhlIGZpcnN0IGRlZmluZSBpbiB0aGUgY2hhaW4gc2V0cyB0aGUgbWFwcGluZyB0byB0aGUgcm9vdCB0eXBlXG5cdFx0XHRcdFx0aWYgKHBhcmVudE5vZGUgJiYgdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5oYXModmFyTmFtZSkpIHtcblx0XHRcdFx0XHRcdHJldHVybjtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0dGhpcy52YXJpYWJsZVRvVHlwZU1hcC5zZXQodmFyTmFtZSwgZnVsbFBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdH1cblx0XG5cdC8qKlxuXHRcdCogVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHMgZnJvbSBsb29rdXAoKSBjYWxsc1xuXHRcdCogZS5nLiwgY29uc3QgU2VudGllbmNlQ29uc3RydWN0b3IgPSBsb29rdXAoJ1NlbnRpZW5jZScpIG1hcHMgXCJTZW50aWVuY2VDb25zdHJ1Y3RvclwiIC0+IFwiU2VudGllbmNlXCJcblx0XHQqL1xuXHRwcml2YXRlIHRyYWNrTG9va3VwQXNzaWdubWVudCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHR5cGVQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHQvLyBXYWxrIHVwIHRoZSB0cmVlIHRvIGZpbmQgVmFyaWFibGVEZWNsYXJhdGlvblxuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gY2FsbC5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24oY3VycmVudCkpIHtcblx0XHRcdFx0Ly8gRm91bmQ6IGNvbnN0IFggPSBsb29rdXAoLi4uKVxuXHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCB2YXJOYW1lID0gY3VycmVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0dGhpcy52YXJpYWJsZVRvVHlwZU1hcC5zZXQodmFyTmFtZSwgdHlwZVBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHQqIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnRzIGZyb20gbmV3IFR5cGUoKSBjYWxsc1xuXHRcdCogZS5nLiwgY29uc3QgdXNlciA9IG5ldyBVc2VyVHlwZSgpIG1hcHMgXCJ1c2VyXCIgLT4gXCJVc2VyVHlwZVwiXG5cdFx0Ki9cblx0cHJpdmF0ZSB0cmFja05ld0Fzc2lnbm1lbnQgKG5ld0V4cHI6IHRzLk5ld0V4cHJlc3Npb24sIHR5cGVQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHQvLyBXYWxrIHVwIHRoZSB0cmVlIHRvIGZpbmQgVmFyaWFibGVEZWNsYXJhdGlvblxuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbmV3RXhwci5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24oY3VycmVudCkpIHtcblx0XHRcdFx0Ly8gRm91bmQ6IGNvbnN0IFggPSBuZXcgVHlwZSguLi4pXG5cdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudC5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHZhck5hbWUgPSBjdXJyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0XHR0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLnNldCh2YXJOYW1lLCB0eXBlUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdCogUHJvY2VzcyBhIEBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHQgKi9cblx0cHJpdmF0ZSBwcm9jZXNzRGVjb3JhdGVEZWNvcmF0b3IgKFxuXHRcdGRlY29yYXRvcjogdHMuRGVjb3JhdG9yLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0Y2xhc3NEZWNsUGFyYW0/OiB0cy5DbGFzc0RlY2xhcmF0aW9uXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRkZWNvcmF0b3IuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXG5cdFx0Ly8gR2V0IHRoZSBjbGFzcyBkZWNsYXJhdGlvbiAtIHVzZSB0aGUgcGFzc2VkIGNvbnRleHQgaWYgcGFyZW50IGlzIG5vdCBzZXRcblx0XHRjb25zdCBjbGFzc0RlY2wgPSBkZWNvcmF0b3IucGFyZW50IGFzIHRzLkNsYXNzRGVjbGFyYXRpb24gfCB1bmRlZmluZWQgfHwgY2xhc3NEZWNsUGFyYW07XG5cdFx0aWYgKCFjbGFzc0RlY2wgfHwgIWNsYXNzRGVjbC5uYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdEZWNvcmF0ZWQgY2xhc3MgaGFzIG5vIG5hbWUnLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHR5cGVOYW1lID0gY2xhc3NEZWNsLm5hbWUudGV4dDtcblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdEZWNvcmF0ZWQgY2xhc3MgaGFzIG5vIG5hbWUnLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFBhcnNlIGRlY29yYXRvciBhcmd1bWVudHM6IEBkZWNvcmF0ZSgpLCBAZGVjb3JhdGUoUGFyZW50KSxcblx0XHQvLyBAZGVjb3JhdGUoeyAuLi4gfSksIEBkZWNvcmF0ZShQYXJlbnQsIHsgLi4uIH0pLFxuXHRcdC8vIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSwgQE15Q29sbGVjdGlvbi5kZWNvcmF0ZSh7IC4uLiB9KVxuXHRcdGxldCBwYXJlbnROb2RlOiBUeXBlTm9kZSB8IHVuZGVmaW5lZDtcblx0XHRsZXQgcGFyZW50RnVsbFBhdGg6IHN0cmluZyB8IG51bGwgPSBudWxsO1xuXHRcdGxldCBjb2xsZWN0aW9uSWQ6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRsZXQgZGVjb3JhdG9yQ29uZmlnOiB7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0gPSB7fTtcblxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGRlY29yYXRvci5leHByZXNzaW9uKSkge1xuXHRcdFx0Y29uc3QgY2FsbEV4cHIgPSBkZWNvcmF0b3IuZXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IGNhbGxlZSA9IGNhbGxFeHByLmV4cHJlc3Npb247XG5cblx0XHRcdC8vIENoZWNrIGZvciBATXlDb2xsZWN0aW9uLmRlY29yYXRlKCkgd2hlcmUgTXlDb2xsZWN0aW9uIGlzIGEgY3VzdG9tIGNvbGxlY3Rpb24uXG5cdFx0XHQvLyBUaGUgZGVjb3JhdGVkIGNsYXNzIGJlY29tZXMgYSByb290IHR5cGUgaW4gdGhhdCBjb2xsZWN0aW9uLlxuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsZWUpICYmXG5cdFx0XHRcdGNhbGxlZS5uYW1lLnRleHQgPT09ICdkZWNvcmF0ZScgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGNhbGxlZS5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGNhbGxlZS5leHByZXNzaW9uLnRleHQpXG5cdFx0XHQpIHtcblx0XHRcdFx0Y29sbGVjdGlvbklkID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChjYWxsZWUuZXhwcmVzc2lvbi50ZXh0KTtcblx0XHRcdFx0aWYgKGNhbGxFeHByLmFyZ3VtZW50cy5sZW5ndGggPT09IDEgJiYgdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihjYWxsRXhwci5hcmd1bWVudHNbIDAgXSkpIHtcblx0XHRcdFx0XHRkZWNvcmF0b3JDb25maWcgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjYWxsRXhwci5hcmd1bWVudHNbIDAgXSk7XG5cdFx0XHRcdH1cblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGNvbnN0IGFyZ3MgPSBjYWxsRXhwci5hcmd1bWVudHM7XG5cdFx0XHRcdGxldCBwYXJlbnRBcmc6IHRzLklkZW50aWZpZXIgfCB1bmRlZmluZWQ7XG5cdFx0XHRcdGxldCBjb25maWdBcmc6IHRzLk9iamVjdExpdGVyYWxFeHByZXNzaW9uIHwgdW5kZWZpbmVkO1xuXG5cdFx0XHRcdGZvciAoY29uc3QgYXJnIG9mIGFyZ3MpIHtcblx0XHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdFx0XHRcdGlmIChwYXJlbnRBcmcpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdFx0XHRcdFx0bWVzc2FnZSA6ICdAZGVjb3JhdGUoKSBhY2NlcHRzIG9ubHkgb25lIHBhcmVudCByZWZlcmVuY2UnLFxuXHRcdFx0XHRcdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0XHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0XHRwYXJlbnRBcmcgPSBhcmc7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdFx0XHRcdGlmIChjb25maWdBcmcpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdFx0XHRcdFx0bWVzc2FnZSA6ICdAZGVjb3JhdGUoKSBhY2NlcHRzIG9ubHkgb25lIGNvbmZpZyBvYmplY3QnLFxuXHRcdFx0XHRcdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0XHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0XHRjb25maWdBcmcgPSBhcmc7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0aWYgKHBhcmVudEFyZykge1xuXHRcdFx0XHRcdHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlJZGVudGlmaWVyKHBhcmVudEFyZy50ZXh0KTtcblx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0XHRcdFx0cGFyZW50RnVsbFBhdGggPSBwYXJlbnROb2RlLmZ1bGxQYXRoO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGlmIChjb25maWdBcmcpIHtcblx0XHRcdFx0XHRkZWNvcmF0b3JDb25maWcgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjb25maWdBcmcpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gQnVpbGQgZnVsbCBwYXRoXG5cdFx0Y29uc3QgZnVsbFBhdGggPSBwYXJlbnROb2RlID8gYCR7cGFyZW50Tm9kZS5mdWxsUGF0aH0uJHt0eXBlTmFtZX1gIDogdHlwZU5hbWU7XG5cblx0XHQvLyBDcmVhdGUgZGVmaW5pdGlvbiBpbmZvIGZvciBkZWNvcmF0ZVxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWNvcmF0ZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IHBhcmVudEZ1bGxQYXRoLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiBkZWNvcmF0b3JDb25maWcuc3RyaWN0Q2hhaW4gPz8gdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogZGVjb3JhdG9yQ29uZmlnLmJsb2NrRXJyb3JzID8/IGZhbHNlLFxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQoZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXG5cdFx0Ly8gQ3JlYXRlIHR5cGUgbm9kZVxuXHRcdGNvbnN0IG5vZGUgPSBUeXBlR3JhcGhJbXBsLmNyZWF0ZU5vZGUoXG5cdFx0XHR0eXBlTmFtZSxcblx0XHRcdHBhcmVudE5vZGUsXG5cdFx0XHRzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0bGluZSArIDEsXG5cdFx0XHRjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0Y29sbGVjdGlvbklkXG5cdFx0KTtcblx0XHRub2RlLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA9IHRoaXMuZ2V0UmVnaXN0cnlJbnRlcmZhY2VOYW1lKG5vZGUuY29sbGVjdGlvbklkKTtcblxuXHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBhbmQgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGNsYXNzIG1lbWJlcnNcblx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RDbGFzc1Byb3BlcnRpZXMoY2xhc3NEZWNsKTtcblx0XHRub2RlLmNvbnN0cnVjdG9yUGFyYW1zID0gdGhpcy5leHRyYWN0Q2xhc3NDb25zdHJ1Y3RvclBhcmFtcyhjbGFzc0RlY2wpO1xuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoXG5cdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkQ2hpbGQocGFyZW50Tm9kZSwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0eXBlIG5hbWUgZnJvbSBkZWZpbmUoKSBjYWxsIGFyZ3VtZW50cy5cblx0ICogSGFuZGxlczpcblx0ICogICBkZWZpbmUoJ1R5cGVOYW1lJywgaGFuZGxlcilcblx0ICogICBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKSAgIC8vIGV4cGxpY2l0LXNvdXJjZSBmb3JtXG5cdCAqICAgZGVmaW5lKGZ1bmN0aW9uIFR5cGVOYW1lKCkge30pXG5cdCAqICAgZGVmaW5lKCgpID0+IGNsYXNzIFR5cGVOYW1lIHt9KVxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0VHlwZU5hbWUgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBhcmdzID0gY2FsbC5hcmd1bWVudHM7XG5cblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmlyc3RBcmcgPSBhcmdzWyAwIF07XG5cblx0XHQvLyBFeHBsaWNpdC1zb3VyY2UgZm9ybTogZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilcblx0XHRpZiAoYXJncy5sZW5ndGggPj0gMiAmJiB0cy5pc0lkZW50aWZpZXIoZmlyc3RBcmcpICYmIHRzLmlzU3RyaW5nTGl0ZXJhbChhcmdzWyAxIF0pKSB7XG5cdFx0XHRyZXR1cm4gYXJnc1sgMSBdLnRleHQ7XG5cdFx0fVxuXG5cdFx0Ly8gU3RyaW5nIGxpdGVyYWw6IGRlZmluZSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChmaXJzdEFyZykpIHtcblx0XHRcdHJldHVybiBmaXJzdEFyZy50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIEZ1bmN0aW9uIHdpdGggbmFtZTogZGVmaW5lKGZ1bmN0aW9uIFR5cGVOYW1lKCkge30pXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGZpcnN0QXJnKSAmJiBmaXJzdEFyZy5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gZmlyc3RBcmcubmFtZS50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIEFycm93IGZ1bmN0aW9uIHJldHVybmluZyBjbGFzczogZGVmaW5lKCgpID0+IGNsYXNzIFR5cGVOYW1lIHt9KVxuXHRcdGlmICh0cy5pc0Fycm93RnVuY3Rpb24oZmlyc3RBcmcpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGZpcnN0QXJnO1xuXHRcdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGJvZHkpICYmIGJvZHkubmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gYm9keS5uYW1lLnRleHQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSBmdWxsIGRlZmluZSgpIGNhbGwgY29udGV4dDogdHlwZSBuYW1lLCBwYXJlbnQgdHlwZSwgYW5kIGNvbGxlY3Rpb24uXG5cdCAqIEhhbmRsZXMgZGlyZWN0IGNhbGxzLCBwcm9wZXJ0eS1hY2Nlc3MgY2FsbHMsIGNoYWluZWQgY2FsbHMsIGFuZCB0aGVcblx0ICogZXhwbGljaXQtc291cmNlIGZvcm0gYGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpYC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdERlZmluZUNvbnRleHQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKToge1xuXHRcdHR5cGVOYW1lPzogc3RyaW5nO1xuXHRcdHBhcmVudFR5cGU/OiBUeXBlTm9kZTtcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmc7XG5cdH0ge1xuXHRcdGNvbnN0IHR5cGVOYW1lID0gdGhpcy5leHRyYWN0VHlwZU5hbWUoY2FsbCk7XG5cdFx0aWYgKCF0eXBlTmFtZSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gY2FsbDtcblxuXHRcdC8vIERpcmVjdCBjYWxsOiBkZWZpbmUoJ1R5cGVOYW1lJywgLi4uKSBvciBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0Ly8gRXhwbGljaXQtc291cmNlIGZvcm06IGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdFx0XHRpZiAoY2FsbC5hcmd1bWVudHMubGVuZ3RoID49IDIgJiYgdHMuaXNJZGVudGlmaWVyKGNhbGwuYXJndW1lbnRzWyAwIF0pKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZU5hbWUgPSBjYWxsLmFyZ3VtZW50c1sgMCBdLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBQbGFpbiByb290IGRlZmluZSBpbiBkZWZhdWx0IGNvbGxlY3Rpb25cblx0XHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiBYLmRlZmluZSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0Y29uc3Qgb2JqID0gZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG9iaikpIHtcblx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShvYmoudGV4dCk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBOZXN0ZWQgYWNjZXNzOiBpbnN0YW5jZS5UeXBlLmRlZmluZSAtIHRyeSB0byByZXNvbHZlXG5cdFx0XHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKG9iaik7XG5cdFx0XHRcdGlmIChjaGFpbi5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoY2hhaW4uam9pbignLicpKTtcblx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUgfTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihvYmopKSB7XG5cdFx0XHRcdC8vIERldGVybWluZSB0aGUgY29sbGVjdGlvbiBjb250ZXh0IGZyb20gdGhlIHJvb3Qgb2YgdGhlIGNoYWluIHNvIHRoYXRcblx0XHRcdFx0Ly8gY3VzdG9tLWNvbGxlY3Rpb24gdHlwZXMgZG8gbm90IGdldCBjb25mdXNlZCB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcy5cblx0XHRcdFx0Y29uc3Qgcm9vdElkID0gdGhpcy5nZXRSb290SWRlbnRpZmllcihvYmouZXhwcmVzc2lvbik7XG5cdFx0XHRcdGNvbnN0IGV4cGVjdGVkQ29sbGVjdGlvbklkID0gcm9vdElkXG5cdFx0XHRcdFx0PyB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uocm9vdElkLnRleHQpLmNvbGxlY3Rpb25JZFxuXHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXG5cdFx0XHRcdC8vIENoYWluZWQgY2FsbDogZGVmaW5lKCdBJykuZGVmaW5lKCdCJykgb3IgbW5lbW9uaWNhLmRlZmluZSgnQScpLmRlZmluZSgnQicpXG5cdFx0XHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ2FsbChvYmosIGNhbGwuZ2V0U291cmNlRmlsZSgpKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdFR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0Ly8gSW5oZXJpdCBjb2xsZWN0aW9uIGZyb20gdGhlIHBhcmVudCB0eXBlIChpZiBhbnkpXG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIENoYWluZWQgbGF6eSBjYWxsOiBsYXp5KCdBJykuZGVmaW5lKCdCJykgb3IgVHlwZS5sYXp5KCdBJykuZGVmaW5lKCdCJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzTGF6eUNhbGwob2JqLCBjYWxsLmdldFNvdXJjZUZpbGUoKSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gQnVpbGRlciBsb29rdXAgY2hhaW46IEFwcC5sb29rdXAoJ1VzZXInKS5kZWZpbmUoJ0FkbWluJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMb29rdXBDYWxsKG9iaikpIHtcblx0XHRcdFx0XHRjb25zdCBsb29rZWRVcFBhdGggPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKG9iaik7XG5cdFx0XHRcdFx0aWYgKGxvb2tlZFVwUGF0aCkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUobG9va2VkVXBQYXRoKTtcblx0XHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZS5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHR9XG5cblx0LyoqXG5cdCAqIFByZWZpeCBhIGRvdHRlZCB0eXBlIHBhdGggd2l0aCBhIGNvbGxlY3Rpb24gaWRlbnRpZmllciBzbyBjdXN0b20tY29sbGVjdGlvblxuXHQgKiB0eXBlcyBkbyBub3QgY29sbGlkZSB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcyBpbiB0aGUgZ3JhcGguXG5cdCAqL1xuXHRwcml2YXRlIHByZWZpeENvbGxlY3Rpb25QYXRoIChwYXRoOiBzdHJpbmcsIGNvbGxlY3Rpb25JZDogc3RyaW5nKTogc3RyaW5nIHtcblx0XHRyZXR1cm4gYCR7Y29sbGVjdGlvbklkfTo6JHtwYXRofWA7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGRlZmluZSgpIHNvdXJjZSBpZGVudGlmaWVyIHRvIGVpdGhlciBhIHBhcmVudCB0eXBlLCBhIGNvbGxlY3Rpb24sXG5cdCAqIG9yIHRoZSBkZWZhdWx0IChtb2R1bGUgb2JqZWN0KSBjb2xsZWN0aW9uLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRGVmaW5lU291cmNlIChzb3VyY2VOYW1lOiBzdHJpbmcpOiB7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Ly8gTW9kdWxlIG9iamVjdCBhbGlhc2VzIC0+IHJvb3QgaW4gZGVmYXVsdCBjb2xsZWN0aW9uXG5cdFx0aWYgKHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhzb3VyY2VOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdC8vIENvbGxlY3Rpb24gdmFyaWFibGVzIC0+IHJvb3QgaW4gdGhhdCBjb2xsZWN0aW9uXG5cdFx0Y29uc3QgY29sbGVjdGlvbklkID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChzb3VyY2VOYW1lKTtcblx0XHRpZiAoY29sbGVjdGlvbklkKSB7XG5cdFx0XHRyZXR1cm4geyBjb2xsZWN0aW9uSWQgfTtcblx0XHR9XG5cblx0XHQvLyBPdGhlcndpc2UgdHJlYXQgYXMgYSB0eXBlIHZhcmlhYmxlIHJlZmVyZW5jZVxuXHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlJZGVudGlmaWVyKHNvdXJjZU5hbWUpO1xuXHRcdHJldHVybiB7IHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhIGNhbGwgZXhwcmVzc2lvbiBpcyBhIGxvb2t1cCgpIGNhbGwuXG5cdCAqL1xuXHRwcml2YXRlIGlzTG9va3VwQ2FsbCAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24pOiBib29sZWFuIHtcblx0XHRjb25zdCBleHByID0gbm9kZS5leHByZXNzaW9uO1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikgJiYgZXhwci50ZXh0ID09PSAnbG9va3VwJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSAmJiBleHByLm5hbWUudGV4dCA9PT0gJ2xvb2t1cCcpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGxvb2t1cCgpIGNhbGwgdG8gYSBkb3R0ZWQgdHlwZSBwYXRoIChiZXN0IGVmZm9ydCkuXG5cdCAqIEhhbmRsZXM6XG5cdCAqICAgbG9va3VwKCdVc2VyJylcblx0ICogICBsb29rdXAoc291cmNlLCAnVXNlcicpXG5cdCAqICAgQXBwLmxvb2t1cCgnVXNlcicpXG5cdCAqICAgY29sbGVjdGlvbi5sb29rdXAoJ1VzZXIuQWRtaW4nKVxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlTG9va3VwUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGFyZ3MgPSBjYWxsLmFyZ3VtZW50cztcblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gU2luZ2xlLWFyZyBsb29rdXA6IGxvb2t1cCgnVXNlcicpIG9yIEFwcC5sb29rdXAoJ1VzZXInKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMSkge1xuXHRcdFx0Y29uc3QgYXJnID0gYXJnc1sgMCBdO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChhcmcpIHx8IHRzLmlzTm9TdWJzdGl0dXRpb25UZW1wbGF0ZUxpdGVyYWwoYXJnKSkge1xuXHRcdFx0XHRjb25zdCBwYXRoID0gYXJnLnRleHQ7XG5cdFx0XHRcdC8vIElmIHRoaXMgaXMgYSBtZXRob2QgY2FsbCBvbiBhIHNvdXJjZSwgcmVzb2x2ZSByZWxhdGl2ZSB0byB0aGF0IHNvdXJjZS5cblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRjb25zdCBzb3VyY2VFeHByID0gY2FsbC5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihzb3VyY2VFeHByKSkge1xuXHRcdFx0XHRcdFx0Y29uc3Qgc291cmNlTmFtZSA9IHNvdXJjZUV4cHIudGV4dDtcblx0XHRcdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRcdFx0XHRpZiAoc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQpIHtcblx0XHRcdFx0XHRcdFx0Ly8gQ29sbGVjdGlvbiBsb29rdXA6IHByZWZpeCBwYXRoIHdpdGggdGhlIGNvbGxlY3Rpb24gaWRcblx0XHRcdFx0XHRcdFx0cmV0dXJuIHRoaXMucHJlZml4Q29sbGVjdGlvblBhdGgocGF0aCwgc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSkge1xuXHRcdFx0XHRcdFx0XHQvLyBUeXBlIGxvb2t1cDogcmVsYXRpdmUgZmlyc3QsIHRoZW4gcm9vdCBmYWxsYmFja1xuXHRcdFx0XHRcdFx0XHRjb25zdCByZWxhdGl2ZVBhdGggPSBgJHtzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUuZnVsbFBhdGh9LiR7cGF0aH1gO1xuXHRcdFx0XHRcdFx0XHRpZiAodGhpcy5ncmFwaC5maW5kVHlwZShyZWxhdGl2ZVBhdGgpKSB7XG5cdFx0XHRcdFx0XHRcdFx0cmV0dXJuIHJlbGF0aXZlUGF0aDtcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHBhdGg7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIFR3by1hcmcgbG9va3VwOiBsb29rdXAoc291cmNlLCAnVXNlcicpXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIpIHtcblx0XHRcdGNvbnN0IHNvdXJjZUFyZyA9IGFyZ3NbIDAgXTtcblx0XHRcdGNvbnN0IHBhdGhBcmcgPSBhcmdzWyAxIF07XG5cdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihzb3VyY2VBcmcpIHx8ICF0cy5pc1N0cmluZ0xpdGVyYWwocGF0aEFyZykpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHNvdXJjZU5hbWUgPSBzb3VyY2VBcmcudGV4dDtcblx0XHRcdGNvbnN0IHBhdGggPSBwYXRoQXJnLnRleHQ7XG5cdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKHNvdXJjZU5hbWUpO1xuXHRcdFx0aWYgKHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKSB7XG5cdFx0XHRcdHJldHVybiB0aGlzLnByZWZpeENvbGxlY3Rpb25QYXRoKHBhdGgsIHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKTtcblx0XHRcdH1cblx0XHRcdGlmIChzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUpIHtcblx0XHRcdFx0Y29uc3QgcmVsYXRpdmVQYXRoID0gYCR7c291cmNlQ29udGV4dC5wYXJlbnRUeXBlLmZ1bGxQYXRofS4ke3BhdGh9YDtcblx0XHRcdFx0aWYgKHRoaXMuZ3JhcGguZmluZFR5cGUocmVsYXRpdmVQYXRoKSkge1xuXHRcdFx0XHRcdHJldHVybiByZWxhdGl2ZVBhdGg7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHBhdGg7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gcGF0aDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBGaW5kIGEgcGFyZW50IHR5cGUgYnkgaXRzIG5hbWUsIHNlYXJjaGluZyBpbiB0aGUgZ3JhcGguXG5cdFx0KiBXaGVuIGNvbGxlY3Rpb25JZCBpcyBwcm92aWRlZCwgb25seSB0eXBlcyBmcm9tIHRoYXQgY29sbGVjdGlvbiBhcmUgY29uc2lkZXJlZC5cblx0XHQqL1xuXHRwcml2YXRlIGZpbmRQYXJlbnRUeXBlQnlOYW1lIChcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0Y29sbGVjdGlvbklkPzogc3RyaW5nXG5cdCk6IFR5cGVOb2RlIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBtYXRjaGVzQ29sbGVjdGlvbiA9ICh0eXBlOiBUeXBlTm9kZSk6IGJvb2xlYW4gPT4ge1xuXHRcdFx0aWYgKGNvbGxlY3Rpb25JZCA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdHJldHVybiB0eXBlLmNvbGxlY3Rpb25JZCA9PT0gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHR5cGUuY29sbGVjdGlvbklkID09PSBjb2xsZWN0aW9uSWQ7XG5cdFx0fTtcblxuXHRcdC8vIEZpcnN0IHRyeSBleGFjdCBtYXRjaCAoZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzIHVzZSB0aGUgcGxhaW4gZG90dGVkIHBhdGgpXG5cdFx0Y29uc3QgZXhhY3QgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKG5hbWUpO1xuXHRcdGlmIChleGFjdCAmJiBtYXRjaGVzQ29sbGVjdGlvbihleGFjdCkpIHtcblx0XHRcdHJldHVybiBleGFjdDtcblx0XHR9XG5cblx0XHQvLyBUaGVuIHNlYXJjaCB0aHJvdWdoIGFsbCB0eXBlcyBmb3Igb25lIHdpdGggbWF0Y2hpbmcgbmFtZSBhbmQgY29sbGVjdGlvblxuXHRcdGZvciAoY29uc3QgdHlwZSBvZiB0aGlzLmdyYXBoLmdldEFsbFR5cGVzKCkpIHtcblx0XHRcdGlmICh0eXBlLm5hbWUgPT09IG5hbWUgJiYgbWF0Y2hlc0NvbGxlY3Rpb24odHlwZSkpIHtcblx0XHRcdFx0cmV0dXJuIHR5cGU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHRcdCogRmluZCBhIHBhcmVudCB0eXBlIGZyb20gYW4gaWRlbnRpZmllciByZWZlcmVuY2UuXG5cdFx0KiBIYW5kbGVzIGJvdGggYWxpYXNlZCB2YXJpYWJsZXMgKGNvbnN0IFVzZXIgPSBkZWZpbmUoJ1VzZXJFbnRpdHknLCAuLi4pKVxuXHRcdCogYW5kIGRpcmVjdCBjbGFzcy90eXBlIG5hbWVzLlxuXHRcdCovXG5cdHByaXZhdGUgZmluZFBhcmVudFR5cGVCeUlkZW50aWZpZXIgKG5hbWU6IHN0cmluZyk6IFR5cGVOb2RlIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBGaXJzdCBjaGVjayB2YXJpYWJsZSBtYXBwaW5nOiBjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKVxuXHRcdGNvbnN0IG1hcHBlZEZ1bGxQYXRoID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0aWYgKG1hcHBlZEZ1bGxQYXRoKSB7XG5cdFx0XHRjb25zdCBtYXBwZWROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShtYXBwZWRGdWxsUGF0aCk7XG5cdFx0XHRpZiAobWFwcGVkTm9kZSkgcmV0dXJuIG1hcHBlZE5vZGU7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUobmFtZSk7XG5cdFx0cmV0dXJuIHBhcmVudE5vZGU7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IHRoZSBsZWZ0bW9zdCBpZGVudGlmaWVyIG9mIGEgcHJvcGVydHktYWNjZXNzIGNoYWluLlxuXHQgKiBGb3IgYEFwcC5kZWZpbmUoJ1VzZXInKS5kZWZpbmUoJ0FkbWluJylgIHRoaXMgcmV0dXJucyB0aGUgYEFwcGAgaWRlbnRpZmllci5cblx0ICovXG5cdHByaXZhdGUgZ2V0Um9vdElkZW50aWZpZXIgKGV4cHI6IHRzLkV4cHJlc3Npb24pOiB0cy5JZGVudGlmaWVyIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuRXhwcmVzc2lvbiA9IGV4cHI7XG5cdFx0d2hpbGUgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5leHByZXNzaW9uO1xuXHRcdH1cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQpKSB7XG5cdFx0XHRyZXR1cm4gY3VycmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHRcdCogR2V0IHByb3BlcnR5IGNoYWluIGZyb20gbmVzdGVkIGFjY2Vzc1xuXHRcdCovXG5cdHByaXZhdGUgZ2V0UHJvcGVydHlDaGFpbiAoZXhwcjogdHMuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uIHwgdHMuSWRlbnRpZmllcik6IHN0cmluZ1tdIHtcblx0XHRjb25zdCBjaGFpbjogc3RyaW5nW10gPSBbXTtcblxuXHRcdGxldCBjdXJyZW50OiB0cy5FeHByZXNzaW9uID0gZXhwcjtcblx0XHR3aGlsZSAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY3VycmVudCkpIHtcblx0XHRcdGlmIChjdXJyZW50Lm5hbWUpIHtcblx0XHRcdFx0Y2hhaW4udW5zaGlmdChjdXJyZW50Lm5hbWUudGV4dCk7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5leHByZXNzaW9uO1xuXHRcdH1cblxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudCkpIHtcblx0XHRcdGNoYWluLnVuc2hpZnQoY3VycmVudC50ZXh0KTtcblx0XHR9XG5cblx0XHRyZXR1cm4gY2hhaW47XG5cdH1cblxuXHQvKipcblx0ICogRGV0ZXJtaW5lIHRoZSBjb25zdHJ1Y3RvciBleHByZXNzaW9uIGZvciBlaXRoZXIgYSBkZWZpbmUoKSBvciBsYXp5KCkgY2FsbC5cblx0ICogRm9yIGRlZmluZSgpIHRoaXMgaXMgdGhlIGNvbnN0cnVjdCBoYW5kbGVyOyBmb3IgbGF6eSgpIGl0IGlzIHRoZSB2YWx1ZVxuXHQgKiByZXR1cm5lZCBieSB0aGUgbGF6eSBnZXR0ZXIuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24gKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgZXhwciA9IGNhbGwuZXhwcmVzc2lvbjtcblx0XHRjb25zdCBuYW1lID0gdHMuaXNJZGVudGlmaWVyKGV4cHIpXG5cdFx0XHQ/IGV4cHIudGV4dFxuXHRcdFx0OiB0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKVxuXHRcdFx0XHQ/IGV4cHIubmFtZS50ZXh0XG5cdFx0XHRcdDogJyc7XG5cblx0XHRpZiAobmFtZSA9PT0gJ2xhenknKSB7XG5cdFx0XHRjb25zdCBsYXp5QXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRcdGlmICghbGF6eUFyZ3MpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB0aGlzLnVud3JhcExhenlHZXR0ZXIobGF6eUFyZ3MuZ2V0dGVyKTtcblx0XHR9XG5cblx0XHQvLyBkZWZpbmUoKSBjYWxsXG5cdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBNb2Rlcm4gZm9ybTogZGVmaW5lKCdOYW1lJywgaGFuZGxlciwgY29uZmlnPylcblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGFyZ3NbIDAgXSkpIHtcblx0XHRcdHJldHVybiBhcmdzWyAxIF07XG5cdFx0fVxuXG5cdFx0Ly8gTGVnYWN5IGZvcm06IGRlZmluZShmdW5jdGlvbiBOYW1lKCkge30pIG9yIGRlZmluZSgoKSA9PiBjbGFzcyBOYW1lIHt9KVxuXHRcdHJldHVybiBhcmdzWyAwIF07XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gY29uc3RydWN0b3IgZnVuY3Rpb25cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFByb3BlcnRpZXMgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpO1xuXHRcdGlmICghY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRyZXR1cm4gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5leHRyYWN0UHJvcGVydGllc0Zyb21Db25zdHJ1Y3Rvcihjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gYSBjb25zdHJ1Y3RvciBleHByZXNzaW9uIChmdW5jdGlvbiwgYXJyb3csIG9yIGNsYXNzKS5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFByb3BlcnRpZXNGcm9tQ29uc3RydWN0b3IgKGNvbnN0cnVjdG9yRXhwcjogdHMuRXhwcmVzc2lvbik6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Ly8gQnVpbGQgdHlwZSBtYXAgZnJvbSBkYXRhIHBhcmFtZXRlciAoZm9yIHRoaXMueCA9IGRhdGEueCBwYXR0ZXJucylcblx0XHRjb25zdCBkYXRhVHlwZU1hcCA9IHRoaXMuYnVpbGREYXRhVHlwZU1hcChjb25zdHJ1Y3RvckV4cHIpO1xuXG5cdFx0Ly8gSGFuZGxlIGZ1bmN0aW9uIGV4cHJlc3Npb25cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSB8fCB0cy5pc0Fycm93RnVuY3Rpb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBjb25zdHJ1Y3RvckV4cHI7XG5cblx0XHRcdC8vIEZpcnN0LCBleHRyYWN0IHByb3BlcnRpZXMgZnJvbSBgdGhpc2AgcGFyYW1ldGVyIHR5cGUgYW5ub3RhdGlvblxuXHRcdFx0Ly8gVGhpcyBoYW5kbGVzIHBhdHRlcm5zIGxpa2U6IGZ1bmN0aW9uKHRoaXM6IFNvbWVUeXBlLCBkYXRhOiBTb21lVHlwZSkgeyB9XG5cdFx0XHRjb25zdCB0aGlzUGFyYW1Qcm9wZXJ0aWVzID0gdGhpcy5leHRyYWN0VGhpc1BhcmFtUHJvcGVydGllcyhjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0Zm9yIChjb25zdCBbIG5hbWUsIHByb3BJbmZvIF0gb2YgdGhpc1BhcmFtUHJvcGVydGllcykge1xuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCBwcm9wSW5mbyk7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEZ1bmN0aW9uIGJvZHkgd2l0aCBzdGF0ZW1lbnRzXG5cdFx0XHRpZiAodHMuaXNCbG9jayhib2R5KSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IHN0bXQgb2YgYm9keS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdFx0aWYgKHRzLmlzRXhwcmVzc2lvblN0YXRlbWVudChzdG10KSkge1xuXHRcdFx0XHRcdFx0dGhpcy5leHRyYWN0UHJvcGVydHlGcm9tU3RhdGVtZW50KHN0bXQuZXhwcmVzc2lvbiwgcHJvcGVydGllcywgZGF0YVR5cGVNYXApO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIEhhbmRsZSBjbGFzcyBleHByZXNzaW9uXG5cdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikpIHtcblx0XHRcdC8vIEZpcnN0IHBhc3M6IGNvbGxlY3QgYWxsIHByb3BlcnR5IHR5cGVzIGZvciBtZXRob2QgaW5mZXJlbmNlXG5cdFx0XHRjb25zdCBjbGFzc1Byb3BlcnR5VHlwZXMgPSB0aGlzLmV4dHJhY3RDbGFzc1Byb3BlcnR5VHlwZXMoY29uc3RydWN0b3JFeHByKTtcblxuXHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgY29uc3RydWN0b3JFeHByLm1lbWJlcnMpIHtcblx0XHRcdFx0Ly8gSGFuZGxlIHByb3BlcnR5IGRlY2xhcmF0aW9uc1xuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eURlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUpIHtcblx0XHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBwcm9wZXJ0aWVzXG5cdFx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0XHRcdG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkO1xuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblxuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpID8gbWVtYmVyLm5hbWUudGV4dCA6ICcnO1xuXHRcdFx0XHRcdGlmIChuYW1lKSB7XG5cdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHRcdHR5cGUgICAgIDogdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpLFxuXHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBIYW5kbGUgbWV0aG9kIGRlY2xhcmF0aW9uc1xuXHRcdFx0XHRpZiAodHMuaXNNZXRob2REZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBtZXRob2RzXG5cdFx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0XHRcdG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkO1xuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblxuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyTWV0aG9kVHlwZShtZW1iZXIsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gSGFuZGxlIGdldHRlciBkZWNsYXJhdGlvbnNcblx0XHRcdFx0aWYgKHRzLmlzR2V0QWNjZXNzb3IobWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgZ2V0dGVyc1xuXHRcdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdFx0XHRtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZDtcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cblx0XHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHQvLyBGaXJzdCB0cnkgZXhwbGljaXQgdHlwZSBhbm5vdGF0aW9uLCB0aGVuIGluZmVyIGZyb20gZ2V0dGVyIGJvZHlcblx0XHRcdFx0XHRsZXQgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRpZiAodHlwZSA9PT0gJ3Vua25vd24nICYmIG1lbWJlci5ib2R5KSB7XG5cdFx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclJldHVyblR5cGVGcm9tQm9keShtZW1iZXIuYm9keSwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0cmVhZG9ubHkgOiB0cnVlLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHQvKipcblx0ICogQnVpbGQgYSB0eXBlIG1hcCBmcm9tIGFsbCBwYXJhbWV0ZXJzIHdpdGggaW5saW5lIG9iamVjdCB0eXBlIGFubm90YXRpb25zXG5cdCAqIFJldHVybnMgYSBtYXAgb2YgXCJwYXJhbU5hbWUucHJvcGVydHlOYW1lXCIgLT4gdHlwZVxuXHQgKi9cblx0cHJpdmF0ZSBidWlsZERhdGFUeXBlTWFwIChoYW5kbGVyQXJnOiB0cy5FeHByZXNzaW9uKTogTWFwPHN0cmluZywgc3RyaW5nPiB7XG5cdFx0Y29uc3QgdHlwZU1hcCA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cblx0XHRpZiAoIXRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGhhbmRsZXJBcmcpICYmICF0cy5pc0Fycm93RnVuY3Rpb24oaGFuZGxlckFyZykpIHtcblx0XHRcdHJldHVybiB0eXBlTWFwO1xuXHRcdH1cblxuXHRcdC8vIEl0ZXJhdGUgb3ZlciBBTEwgcGFyYW1ldGVyc1xuXHRcdGZvciAoY29uc3QgcGFyYW0gb2YgaGFuZGxlckFyZy5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRpZiAoIXBhcmFtLm5hbWUgfHwgIXBhcmFtLnR5cGUpIGNvbnRpbnVlO1xuXG5cdFx0XHQvLyBHZXQgcGFyYW1ldGVyIG5hbWVcblx0XHRcdGxldCBwYXJhbU5hbWUgPSAnJztcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkpIHtcblx0XHRcdFx0cGFyYW1OYW1lID0gcGFyYW0ubmFtZS50ZXh0O1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29udGludWU7IC8vIFNraXAgZGVzdHJ1Y3R1cmVkIHBhcmFtZXRlcnMgZm9yIG5vd1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBDaGVjayBpZiBpdCdzIGFuIGlubGluZSBvYmplY3QgdHlwZSBsaXRlcmFsXG5cdFx0XHRpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUocGFyYW0udHlwZSkpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgcGFyYW0udHlwZS5tZW1iZXJzKSB7XG5cdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQoYCR7cGFyYW1OYW1lfS4ke3Byb3BOYW1lfWAsIHR5cGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Ly8gU3RvcmUgc2ltcGxlIHBhcmFtZXRlciB0eXBlcyBsaWtlIGBkZWNvcmF0ZVZhbHVlOiBzdHJpbmdgXG5cdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblx0XHRcdFx0aWYgKHR5cGUgIT09ICd1bmtub3duJykge1xuXHRcdFx0XHRcdHR5cGVNYXAuc2V0KHBhcmFtTmFtZSwgdHlwZSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdHlwZU1hcDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnR5IGFjY2VzcyBjaGFpbiAoZS5nLiwgXCJkYXRhUmVuYW1lZC5pZFwiIGZyb20gZGF0YVJlbmFtZWQuaWQpXG5cdCAqIEhhbmRsZXMgZmFsbGJhY2tzIGxpa2U6IGRhdGEucGVybWlzc2lvbnMgfHwgW11cblx0ICovXG5cdHByaXZhdGUgZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbiAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gSGFuZGxlIGlkZW50aWZpZXI6IGRhdGFcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci50ZXh0O1xuXHRcdH1cblx0XHQvLyBIYW5kbGUgcHJvcGVydHkgYWNjZXNzOiBkYXRhLnBlcm1pc3Npb25zXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBiYXNlID0gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGV4cHIuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoYmFzZSkge1xuXHRcdFx0XHRyZXR1cm4gYCR7YmFzZX0uJHtleHByLm5hbWUudGV4dH1gO1xuXHRcdFx0fVxuXHRcdH1cblx0XHQvLyBIYW5kbGUgZmFsbGJhY2sgcGF0dGVybjogZGF0YS5wZXJtaXNzaW9ucyB8fCBbXVxuXHRcdGlmICh0cy5pc0JpbmFyeUV4cHJlc3Npb24oZXhwcikgJiZcblx0XHRcdGV4cHIub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkJhckJhclRva2VuKSB7XG5cdFx0XHQvLyBSZXR1cm4gdGhlIGxlZnQgc2lkZSBvZiB8fCBvcGVyYXRvclxuXHRcdFx0cmV0dXJuIHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihleHByLmxlZnQpO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydHkgYXNzaWdubWVudCBmcm9tIHN0YXRlbWVudFxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UHJvcGVydHlGcm9tU3RhdGVtZW50IChcblx0XHRleHByOiB0cy5FeHByZXNzaW9uLFxuXHRcdHByb3BlcnRpZXM6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4sXG5cdFx0ZGF0YVR5cGVNYXA6IE1hcDxzdHJpbmcsIHN0cmluZz4gPSBuZXcgTWFwKClcblx0KTogdm9pZCB7XG5cdFx0Ly8gSGFuZGxlOiB0aGlzLnByb3BlcnR5ID0gdmFsdWVcblx0XHRpZiAodHMuaXNCaW5hcnlFeHByZXNzaW9uKGV4cHIpICYmXG5cdFx0XHRleHByLm9wZXJhdG9yVG9rZW4ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbikge1xuXHRcdFx0Y29uc3QgeyBsZWZ0IH0gPSBleHByO1xuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obGVmdCkpIHtcblx0XHRcdFx0Ly8gQ2hlY2sgaWYgYWNjZXNzaW5nICd0aGlzJyAoVGhpc0tleXdvcmQpXG5cdFx0XHRcdGlmIChsZWZ0LmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBsZWZ0Lm5hbWU/LnRleHQ7XG5cdFx0XHRcdFx0aWYgKG5hbWUpIHtcblx0XHRcdFx0XHRcdC8vIFRyeSB0byBnZXQgdHlwZSBmcm9tIGRhdGFUeXBlTWFwIHVzaW5nIGZ1bGwgYWNjZXNzIGNoYWluIChlLmcuLCBcImRhdGFSZW5hbWVkLmlkXCIpXG5cdFx0XHRcdFx0XHRjb25zdCBhY2Nlc3NDaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihleHByLnJpZ2h0KTtcblx0XHRcdFx0XHRcdGxldCB0eXBlID0gYWNjZXNzQ2hhaW4gPyBkYXRhVHlwZU1hcC5nZXQoYWNjZXNzQ2hhaW4pIDogdW5kZWZpbmVkO1xuXHRcdFx0XHRcdFx0Ly8gSWYgbm90IGZvdW5kIGFuZCBSSFMgaXMgYSBzaW1wbGUgaWRlbnRpZmllciwgdHJ5IGxvb2tpbmcgaXQgdXAgZGlyZWN0bHlcblx0XHRcdFx0XHRcdGlmICghdHlwZSAmJiB0cy5pc0lkZW50aWZpZXIoZXhwci5yaWdodCkpIHtcblx0XHRcdFx0XHRcdFx0dHlwZSA9IGRhdGFUeXBlTWFwLmdldChleHByLnJpZ2h0LnRleHQpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKCF0eXBlKSB7XG5cdFx0XHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihleHByLnJpZ2h0LCBkYXRhVHlwZU1hcCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHQvLyBEb24ndCBvdmVyd3JpdGUgYSBrbm93biB0eXBlIGZyb20gYHRoaXNgIGFubm90YXRpb24gd2l0aCB1bmtub3duXG5cdFx0XHRcdFx0XHRjb25zdCBleGlzdGluZyA9IHByb3BlcnRpZXMuZ2V0KG5hbWUpO1xuXHRcdFx0XHRcdFx0aWYgKGV4aXN0aW5nICYmIGV4aXN0aW5nLnR5cGUgIT09ICd1bmtub3duJyAmJiB0eXBlID09PSAndW5rbm93bicpIHtcblx0XHRcdFx0XHRcdFx0Ly8gS2VlcCB0aGUgYmV0dGVyIHR5cGUgZnJvbSBleHBsaWNpdCBhbm5vdGF0aW9uXG5cdFx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIEhhbmRsZTogT2JqZWN0LmFzc2lnbih0aGlzLCB7IHByb3A6IHZhbHVlIH0pXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdGNvbnN0IGZuID0gZXhwci5leHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGZuKSAmJlxuXHRcdFx0XHRmbi5uYW1lPy50ZXh0ID09PSAnYXNzaWduJyAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoZm4uZXhwcmVzc2lvbikgJiZcblx0XHRcdFx0Zm4uZXhwcmVzc2lvbi50ZXh0ID09PSAnT2JqZWN0Jykge1xuXHRcdFx0XHRjb25zdCBhcmdzID0gZXhwci5hcmd1bWVudHM7XG5cdFx0XHRcdGlmIChhcmdzLmxlbmd0aCA+PSAyICYmIGFyZ3NbIDAgXS5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gdGhlIHNlY29uZCBhcmd1bWVudFxuXHRcdFx0XHRcdGNvbnN0IHByb3BzQXJnID0gYXJnc1sgMSBdO1xuXHRcdFx0XHRcdGlmICh0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKHByb3BzQXJnKSkge1xuXHRcdFx0XHRcdFx0Zm9yIChjb25zdCBwcm9wIG9mIHByb3BzQXJnLnByb3BlcnRpZXMpIHtcblx0XHRcdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBc3NpZ25tZW50KHByb3ApICYmIHRzLmlzSWRlbnRpZmllcihwcm9wLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRcdFx0Y29uc3QgbmFtZSA9IHByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0XHR0eXBlICAgICA6IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKHByb3AuaW5pdGlhbGl6ZXIpLFxuXHRcdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBjbGFzcyBkZWNsYXJhdGlvbiAoaW5jbHVkaW5nIG1ldGhvZHMgYW5kIGdldHRlcnMpXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDbGFzc1Byb3BlcnRpZXMgKGNsYXNzRGVjbDogdHMuQ2xhc3NEZWNsYXJhdGlvbik6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgY2xhc3NEZWNsLm1lbWJlcnMpIHtcblx0XHRcdC8vIEhhbmRsZSBwcm9wZXJ0eSBkZWNsYXJhdGlvbnNcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5RGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSkge1xuXHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBwcm9wZXJ0aWVzXG5cdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHQgICAgIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkKTtcblx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRjb25zdCBuYW1lID0gdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSA/IG1lbWJlci5uYW1lLnRleHQgOiAnJztcblx0XHRcdFx0aWYgKG5hbWUpIHtcblx0XHRcdFx0XHQvLyBJZiBubyBleHBsaWNpdCB0eXBlIGJ1dCBoYXMgaW5pdGlhbGl6ZXIsIGluZmVyIGZyb20gaW5pdGlhbGl6ZXJcblx0XHRcdFx0XHRsZXQgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRpZiAodHlwZSA9PT0gJ3Vua25vd24nICYmIG1lbWJlci5pbml0aWFsaXplcikge1xuXHRcdFx0XHRcdFx0dHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKG1lbWJlci5pbml0aWFsaXplcik7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdC8vIEhhbmRsZSBtZXRob2QgZGVjbGFyYXRpb25zXG5cdFx0XHRpZiAodHMuaXNNZXRob2REZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgbWV0aG9kc1xuXHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0ICAgICBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZCk7XG5cdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyTWV0aG9kVHlwZShtZW1iZXIpO1xuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBIYW5kbGUgZ2V0dGVyIGRlY2xhcmF0aW9uc1xuXHRcdFx0aWYgKHRzLmlzR2V0QWNjZXNzb3IobWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIGdldHRlcnNcblx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdCAgICAgbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQpO1xuXHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHQvLyBGaXJzdCB0cnkgZXhwbGljaXQgdHlwZSBhbm5vdGF0aW9uLCB0aGVuIGluZmVyIGZyb20gZ2V0dGVyIGJvZHlcblx0XHRcdFx0bGV0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdGlmICh0eXBlID09PSAndW5rbm93bicgJiYgbWVtYmVyLmJvZHkpIHtcblx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclJldHVyblR5cGVGcm9tQm9keShtZW1iZXIuYm9keSk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdHJlYWRvbmx5IDogdHJ1ZSxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBjbGFzcyBwcm9wZXJ0eSB0eXBlcyBmb3IgbWV0aG9kIHJldHVybiB0eXBlIGluZmVyZW5jZVxuXHQgKiBNYXBzIHByb3BlcnR5IG5hbWVzIHRvIHRoZWlyIFR5cGVTY3JpcHQgdHlwZSBzdHJpbmdzXG5cdCAqIE5vdGU6IEluY2x1ZGVzIHByaXZhdGUvcHJvdGVjdGVkIHByb3BlcnRpZXMgZm9yIG1ldGhvZCBpbmZlcmVuY2Vcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENsYXNzUHJvcGVydHlUeXBlcyAoY2xhc3NEZWNsOiB0cy5DbGFzc0V4cHJlc3Npb24pOiBNYXA8c3RyaW5nLCBzdHJpbmc+IHtcblx0XHRjb25zdCBwcm9wZXJ0eVR5cGVzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblxuXHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGNsYXNzRGVjbC5tZW1iZXJzKSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eURlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHQvLyBJbmNsdWRlIEFMTCBwcm9wZXJ0aWVzIChldmVuIHByaXZhdGUpIGZvciBtZXRob2QgcmV0dXJuIHR5cGUgaW5mZXJlbmNlXG5cdFx0XHRcdC8vIFRoZSB2aXNpYmlsaXR5IGNoZWNrIGlzIGRvbmUgd2hlbiBhZGRpbmcgdG8gb3V0cHV0IHByb3BlcnRpZXNcblx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdGlmIChtZW1iZXIudHlwZSkge1xuXHRcdFx0XHRcdHByb3BlcnR5VHlwZXMuc2V0KG5hbWUsIHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydHlUeXBlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBJbmZlciBtZXRob2QgdHlwZSBmcm9tIG1ldGhvZCBkZWNsYXJhdGlvblxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlck1ldGhvZFR5cGUgKG1ldGhvZDogdHMuTWV0aG9kRGVjbGFyYXRpb24sIGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz4pOiBzdHJpbmcge1xuXHRcdGNvbnN0IHBhcmFtcyA9IG1ldGhvZC5wYXJhbWV0ZXJzLm1hcChwYXJhbSA9PiB7XG5cdFx0XHRjb25zdCBwYXJhbU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgPyBwYXJhbS5uYW1lLnRleHQgOiAnYXJnJztcblx0XHRcdGNvbnN0IHBhcmFtVHlwZSA9IHRoaXMuaW5mZXJUeXBlKHBhcmFtLnR5cGUpO1xuXHRcdFx0cmV0dXJuIGAke3BhcmFtTmFtZX06ICR7cGFyYW1UeXBlfWA7XG5cdFx0fSkuam9pbignLCAnKTtcblxuXHRcdGNvbnN0IHJldHVyblR5cGUgPSB0aGlzLmluZmVyUmV0dXJuVHlwZShtZXRob2QsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cblx0XHRpZiAocGFyYW1zKSB7XG5cdFx0XHRyZXR1cm4gYCgke3BhcmFtc30pID0+ICR7cmV0dXJuVHlwZX1gO1xuXHRcdH1cblx0XHRyZXR1cm4gYCgpID0+ICR7cmV0dXJuVHlwZX1gO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBgdGhpc2AgcGFyYW1ldGVyIHR5cGUgYW5ub3RhdGlvblxuXHRcdCogSGFuZGxlcyBwYXR0ZXJucyBsaWtlOiBmdW5jdGlvbih0aGlzOiBTb21lVHlwZSwgZGF0YTogU29tZVR5cGUpIHsgfVxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdFRoaXNQYXJhbVByb3BlcnRpZXMgKGhhbmRsZXJBcmc6IHRzLkZ1bmN0aW9uRXhwcmVzc2lvbiB8IHRzLkFycm93RnVuY3Rpb24pOlxuXHRcdE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Ly8gRmluZCB0aGUgYHRoaXNgIHBhcmFtZXRlciAoaWYgYW55KVxuXHRcdGZvciAoY29uc3QgcGFyYW0gb2YgaGFuZGxlckFyZy5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRpZiAocGFyYW0ubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgJiYgcGFyYW0ubmFtZS50ZXh0ID09PSAndGhpcycgJiYgcGFyYW0udHlwZSkge1xuXHRcdFx0XHQvLyBDaGVjayBpZiBpdCdzIGEgdHlwZSByZWZlcmVuY2UgKGUuZy4sIGB0aGlzOiB1c2FnZWApXG5cdFx0XHRcdGlmICh0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHBhcmFtLnR5cGUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSlcblx0XHRcdFx0XHRcdD8gcGFyYW0udHlwZS50eXBlTmFtZS50ZXh0XG5cdFx0XHRcdFx0XHQ6ICcnO1xuXG5cdFx0XHRcdFx0Ly8gTG9vayB1cCB0aGUgdHlwZSBhbGlhcyBpbiBvdXIgY29sbGVjdGVkIHR5cGUgYWxpYXNlc1xuXHRcdFx0XHRcdGNvbnN0IGFsaWFzZWRUeXBlID0gdGhpcy50eXBlQWxpYXNlcy5nZXQodHlwZU5hbWUpO1xuXHRcdFx0XHRcdGlmIChhbGlhc2VkVHlwZSAmJiB0cy5pc1R5cGVMaXRlcmFsTm9kZShhbGlhc2VkVHlwZSkpIHtcblx0XHRcdFx0XHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIHRoZSB0eXBlIGxpdGVyYWxcblx0XHRcdFx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGFsaWFzZWRUeXBlLm1lbWJlcnMpIHtcblx0XHRcdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQocHJvcE5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRcdG5hbWUgICAgIDogcHJvcE5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIENoZWNrIGlmIGl0J3MgZGlyZWN0bHkgYW4gaW5saW5lIHR5cGUgbGl0ZXJhbCAoZS5nLiwgYHRoaXM6IHsgaWQ6IHN0cmluZyB9YClcblx0XHRcdFx0ZWxzZSBpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUocGFyYW0udHlwZSkpIHtcblx0XHRcdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBwYXJhbS50eXBlLm1lbWJlcnMpIHtcblx0XHRcdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KHByb3BOYW1lLCB7XG5cdFx0XHRcdFx0XHRcdFx0bmFtZSAgICAgOiBwcm9wTmFtZSxcblx0XHRcdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogISFtZW1iZXIucXVlc3Rpb25Ub2tlbixcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHRcdGJyZWFrOyAvLyBGb3VuZCB0aGUgYHRoaXNgIHBhcmFtZXRlciwgbm8gbmVlZCB0byBjb250aW51ZVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBwcm9wZXJ0aWVzO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBJbmZlciBUeXBlU2NyaXB0IHR5cGUgZnJvbSB0eXBlIG5vZGVcblx0XHQqL1xuXHQvKipcblx0ICogSW5mZXIgVHlwZVNjcmlwdCB0eXBlIGZyb20gdHlwZSBub2RlXG5cdCAqL1xuXHRwcml2YXRlIGluZmVyVHlwZSAodHlwZU5vZGU/OiB0cy5UeXBlTm9kZSk6IHN0cmluZyB7XG5cdFx0aWYgKCF0eXBlTm9kZSkge1xuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cblx0XHRzd2l0Y2ggKHR5cGVOb2RlLmtpbmQpIHtcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuU3RyaW5nS2V5d29yZDpcblx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVtYmVyS2V5d29yZDpcblx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQm9vbGVhbktleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5VbmRlZmluZWRLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICd1bmRlZmluZWQnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdWxsS2V5d29yZDpcblx0XHRcdHJldHVybiAnbnVsbCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkFueUtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ2FueSc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVua25vd25LZXl3b3JkOlxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVm9pZEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3ZvaWQnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5BcnJheVR5cGU6XG5cdFx0XHRyZXR1cm4gYEFycmF5PCR7ICB0aGlzLmluZmVyVHlwZSgodHlwZU5vZGUgYXMgdHMuQXJyYXlUeXBlTm9kZSkuZWxlbWVudFR5cGUpICB9PmA7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR5cGVMaXRlcmFsOiB7XG5cdFx0XHQvLyBJbmxpbmUtZXhwYW5kIHR5cGUgbGl0ZXJhbHMgaW5zdGVhZCBvZiBjb2xsYXBzaW5nIHRvICdvYmplY3QnXG5cdFx0XHRjb25zdCB0eXBlTGl0ID0gdHlwZU5vZGUgYXMgdHMuVHlwZUxpdGVyYWxOb2RlO1xuXHRcdFx0Y29uc3QgcHJvcHM6IHN0cmluZ1tdID0gW107XG5cdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiB0eXBlTGl0Lm1lbWJlcnMpIHtcblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdGNvbnN0IG9wdGlvbmFsID0gbWVtYmVyLnF1ZXN0aW9uVG9rZW4gPyAnPycgOiAnJztcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdHByb3BzLnB1c2goYCR7cHJvcE5hbWV9JHtvcHRpb25hbH06ICR7dHlwZX1gKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGB7ICR7cHJvcHMuam9pbignOyAnKX0gfWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5MaXRlcmFsVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHN0cmluZyBsaXRlcmFsIHR5cGVzIGxpa2UgJ3VzZXInLCAnYWRtaW4nLCBldGMuXG5cdFx0XHRjb25zdCB7IGxpdGVyYWwgfSA9ICh0eXBlTm9kZSBhcyB0cy5MaXRlcmFsVHlwZU5vZGUpO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChsaXRlcmFsKSkge1xuXHRcdFx0XHQvLyBSZXR1cm4gdGhlIGFjdHVhbCBsaXRlcmFsIHZhbHVlIChlLmcuLCAndXNlcicgaW5zdGVhZCBvZiBzdHJpbmcpXG5cdFx0XHRcdHJldHVybiBgJyR7bGl0ZXJhbC50ZXh0fSdgO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzTnVtZXJpY0xpdGVyYWwobGl0ZXJhbCkpIHtcblx0XHRcdFx0cmV0dXJuIGxpdGVyYWwudGV4dDtcblx0XHRcdH1cblx0XHRcdGlmIChsaXRlcmFsLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVHJ1ZUtleXdvcmQpIHtcblx0XHRcdFx0cmV0dXJuICd0cnVlJztcblx0XHRcdH1cblx0XHRcdGlmIChsaXRlcmFsLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkKSB7XG5cdFx0XHRcdHJldHVybiAnZmFsc2UnO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGxpdGVyYWwua2luZCA9PT0gdHMuU3ludGF4S2luZC5OdWxsS2V5d29yZCkge1xuXHRcdFx0XHRyZXR1cm4gJ251bGwnO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR5cGVSZWZlcmVuY2U6IHtcblx0XHRcdC8vIEhhbmRsZSB0eXBlIHJlZmVyZW5jZXMgbGlrZSBNYXA8c3RyaW5nLCBudW1iZXI+LCBQcm9wZXJ0eUluZm8sIGV0Yy5cblx0XHRcdGNvbnN0IHR5cGVSZWYgPSB0eXBlTm9kZSBhcyB0cy5UeXBlUmVmZXJlbmNlTm9kZTtcblx0XHRcdGNvbnN0IHR5cGVOYW1lID0gdHMuaXNJZGVudGlmaWVyKHR5cGVSZWYudHlwZU5hbWUpXG5cdFx0XHRcdD8gdHlwZVJlZi50eXBlTmFtZS50ZXh0XG5cdFx0XHRcdDogdHMuaXNRdWFsaWZpZWROYW1lKHR5cGVSZWYudHlwZU5hbWUpXG5cdFx0XHRcdFx0PyB0aGlzLmdldFF1YWxpZmllZE5hbWVUZXh0KHR5cGVSZWYudHlwZU5hbWUpXG5cdFx0XHRcdFx0OiAndW5rbm93bic7XG5cblx0XHRcdC8vIENoZWNrIGlmIHRoaXMgaXMgYSB0eXBlIGFsaWFzIHdlIGNhbiByZXNvbHZlXG5cdFx0XHRjb25zdCBhbGlhc2VkVHlwZSA9IHRoaXMudHlwZUFsaWFzZXMuZ2V0KHR5cGVOYW1lKTtcblx0XHRcdGlmIChhbGlhc2VkVHlwZSkge1xuXHRcdFx0XHQvLyBSZXNvbHZlIHRoZSB0eXBlIGFsaWFzXG5cdFx0XHRcdHJldHVybiB0aGlzLmluZmVyVHlwZShhbGlhc2VkVHlwZSk7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEhhbmRsZSBJbnN0YW5jZVR5cGU8dHlwZW9mIFg+IHBhdHRlcm4gLT4gY29udmVydCB0byBQYXJlbnRfWFxuXHRcdFx0aWYgKHR5cGVOYW1lID09PSAnSW5zdGFuY2VUeXBlJyAmJiB0eXBlUmVmLnR5cGVBcmd1bWVudHMgJiYgdHlwZVJlZi50eXBlQXJndW1lbnRzLmxlbmd0aCA9PT0gMSkge1xuXHRcdFx0XHRjb25zdCBhcmcgPSB0eXBlUmVmLnR5cGVBcmd1bWVudHNbIDAgXTtcblx0XHRcdFx0aWYgKGFyZy5raW5kID09PSB0cy5TeW50YXhLaW5kLlR5cGVRdWVyeSkge1xuXHRcdFx0XHRcdGNvbnN0IHR5cGVRdWVyeSA9IGFyZyBhcyB0cy5UeXBlUXVlcnlOb2RlO1xuXHRcdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIodHlwZVF1ZXJ5LmV4cHJOYW1lKSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcXVlcnlUeXBlTmFtZSA9IHR5cGVRdWVyeS5leHByTmFtZS50ZXh0O1xuXHRcdFx0XHRcdFx0Ly8gTG9vayB1cCB0aGUgdHlwZSBpbiB0aGUgZ3JhcGggdG8gZ2V0IGZ1bGwgcGF0aFxuXHRcdFx0XHRcdFx0Y29uc3QgbWF0Y2hlZFR5cGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlQnlOYW1lKHF1ZXJ5VHlwZU5hbWUpO1xuXHRcdFx0XHRcdFx0aWYgKG1hdGNoZWRUeXBlKSB7XG5cdFx0XHRcdFx0XHRcdC8vIENvbnZlcnQgZnVsbCBwYXRoIHdpdGggZG90cyB0byB1bmRlcnNjb3JlczogVXNhZ2VzLlVzYWdlRW50cnkgLT4gVXNhZ2VzX1VzYWdlRW50cnlcblx0XHRcdFx0XHRcdFx0cmV0dXJuIG1hdGNoZWRUeXBlLmZ1bGxQYXRoLnJlcGxhY2UoL1xcLi9nLCAnXycpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0Ly8gRmFsbGJhY2s6IGp1c3QgdXNlIHRoZSB0eXBlIG5hbWUgaWYgbm90IGZvdW5kIGluIGdyYXBoXG5cdFx0XHRcdFx0XHRyZXR1cm4gcXVlcnlUeXBlTmFtZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblxuXHRcdFx0aWYgKCF0eXBlUmVmLnR5cGVBcmd1bWVudHMgfHwgdHlwZVJlZi50eXBlQXJndW1lbnRzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHQvLyBDaGVjayBpZiB0aGlzIHR5cGUgZXhpc3RzIGluIG91ciBncmFwaCAtIGNvbnZlcnQgdG8gZnVsbCBwYXRoIGZvcm1hdFxuXHRcdFx0XHRjb25zdCBtYXRjaGVkVHlwZSA9IHRoaXMuZ3JhcGguZmluZFR5cGVCeU5hbWUodHlwZU5hbWUpO1xuXHRcdFx0XHRpZiAobWF0Y2hlZFR5cGUpIHtcblx0XHRcdFx0XHQvLyBDb252ZXJ0IGZ1bGwgcGF0aCB3aXRoIGRvdHMgdG8gdW5kZXJzY29yZXM6IFVzYWdlcy5Vc2FnZUVudHJ5IC0+IFVzYWdlc19Vc2FnZUVudHJ5XG5cdFx0XHRcdFx0cmV0dXJuIG1hdGNoZWRUeXBlLmZ1bGxQYXRoLnJlcGxhY2UoL1xcLi9nLCAnXycpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiB0eXBlTmFtZTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gQnVpbGQgZ2VuZXJpYyB0eXBlIGFyZ3VtZW50c1xuXHRcdFx0Y29uc3QgdHlwZUFyZ3MgPSB0eXBlUmVmLnR5cGVBcmd1bWVudHMubWFwKGFyZyA9PiB0aGlzLmluZmVyVHlwZShhcmcpKTtcblx0XHRcdHJldHVybiBgJHt0eXBlTmFtZX08JHt0eXBlQXJncy5qb2luKCcsICcpfT5gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5pb25UeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgdW5pb24gdHlwZXMgbGlrZSAnYScgfCAnYicgfCAnYydcblx0XHRcdGNvbnN0IHVuaW9uVHlwZSA9IHR5cGVOb2RlIGFzIHRzLlVuaW9uVHlwZU5vZGU7XG5cdFx0XHRjb25zdCB0eXBlcyA9IHVuaW9uVHlwZS50eXBlcy5tYXAodCA9PiB0aGlzLmluZmVyVHlwZSh0KSk7XG5cdFx0XHRyZXR1cm4gdHlwZXMuam9pbignIHwgJyk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5JbnRlcnNlY3Rpb25UeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgaW50ZXJzZWN0aW9uIHR5cGVzIGxpa2UgVHlwZUEgJiBUeXBlQlxuXHRcdFx0Y29uc3QgaW50ZXJzZWN0aW9uVHlwZSA9IHR5cGVOb2RlIGFzIHRzLkludGVyc2VjdGlvblR5cGVOb2RlO1xuXHRcdFx0Y29uc3QgdHlwZXMgPSBpbnRlcnNlY3Rpb25UeXBlLnR5cGVzLm1hcCh0ID0+IHRoaXMuaW5mZXJUeXBlKHQpKTtcblx0XHRcdHJldHVybiB0eXBlcy5qb2luKCcgJiAnKTtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR1cGxlVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHR1cGxlIHR5cGVzIGxpa2UgW3N0cmluZywgbnVtYmVyXVxuXHRcdFx0Y29uc3QgdHVwbGVUeXBlID0gdHlwZU5vZGUgYXMgdHMuVHVwbGVUeXBlTm9kZTtcblx0XHRcdGNvbnN0IGVsZW1lbnRzID0gdHVwbGVUeXBlLmVsZW1lbnRzLm1hcChlbGVtID0+IHRoaXMuaW5mZXJUeXBlKGVsZW0gYXMgdHMuVHlwZU5vZGUpKTtcblx0XHRcdHJldHVybiBgWyR7ZWxlbWVudHMuam9pbignLCAnKX1dYDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk9wdGlvbmFsVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIG9wdGlvbmFsIGVsZW1lbnQgaW4gdHVwbGU6IHN0cmluZz9cblx0XHRcdGNvbnN0IG9wdGlvbmFsVHlwZSA9IHR5cGVOb2RlIGFzIHRzLk9wdGlvbmFsVHlwZU5vZGU7XG5cdFx0XHRyZXR1cm4gYCR7dGhpcy5pbmZlclR5cGUob3B0aW9uYWxUeXBlLnR5cGUpICB9P2A7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5SZXN0VHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHJlc3QgZWxlbWVudDogLi4uVFxuXHRcdFx0Y29uc3QgcmVzdFR5cGUgPSB0eXBlTm9kZSBhcyB0cy5SZXN0VHlwZU5vZGU7XG5cdFx0XHRyZXR1cm4gYC4uLiR7ICB0aGlzLmluZmVyVHlwZShyZXN0VHlwZS50eXBlKX1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuUGFyZW50aGVzaXplZFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBwYXJlbnRoZXNpemVkIHR5cGVzOiAoQSB8IEIpXG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclR5cGUoKHR5cGVOb2RlIGFzIHRzLlBhcmVudGhlc2l6ZWRUeXBlTm9kZSkudHlwZSk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5JbmRleGVkQWNjZXNzVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIGluZGV4ZWQgYWNjZXNzOiBUW0tdXG5cdFx0XHRjb25zdCBpbmRleGVkID0gdHlwZU5vZGUgYXMgdHMuSW5kZXhlZEFjY2Vzc1R5cGVOb2RlO1xuXHRcdFx0bGV0IG9iamVjdFR5cGUgPSB0aGlzLmluZmVyVHlwZShpbmRleGVkLm9iamVjdFR5cGUpO1xuXHRcdFx0Y29uc3QgaW5kZXhUeXBlID0gdGhpcy5pbmZlclR5cGUoaW5kZXhlZC5pbmRleFR5cGUpO1xuXHRcdFx0Ly8gSWYgb2JqZWN0VHlwZSBpcyAnb2JqZWN0JywgdHJ5IHRvIHJlc29sdmUgdGhlIHVuZGVybHlpbmcgdHlwZSBhbGlhc1xuXHRcdFx0aWYgKG9iamVjdFR5cGUgPT09ICdvYmplY3QnICYmIHRzLmlzVHlwZVJlZmVyZW5jZU5vZGUoaW5kZXhlZC5vYmplY3RUeXBlKSkge1xuXHRcdFx0XHRjb25zdCByZWZOYW1lID0gdHMuaXNJZGVudGlmaWVyKGluZGV4ZWQub2JqZWN0VHlwZS50eXBlTmFtZSkgPyBpbmRleGVkLm9iamVjdFR5cGUudHlwZU5hbWUudGV4dCA6ICcnO1xuXHRcdFx0XHRjb25zdCBhbGlhc2VkID0gdGhpcy50eXBlQWxpYXNlcy5nZXQocmVmTmFtZSk7XG5cdFx0XHRcdGlmIChhbGlhc2VkKSB7XG5cdFx0XHRcdFx0b2JqZWN0VHlwZSA9IHRoaXMuaW5mZXJUeXBlKGFsaWFzZWQpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gYCR7b2JqZWN0VHlwZX1bJHtpbmRleFR5cGV9XWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlT3BlcmF0b3I6IHtcblx0XHRcdC8vIEhhbmRsZSBrZXlvZiwgcmVhZG9ubHksIHVuaXF1ZSBvcGVyYXRvcnNcblx0XHRcdGNvbnN0IHR5cGVPcCA9IHR5cGVOb2RlIGFzIHRzLlR5cGVPcGVyYXRvck5vZGU7XG5cdFx0XHRjb25zdCBvcGVyYXRvciA9IHRzLlN5bnRheEtpbmRbIHR5cGVPcC5vcGVyYXRvciBdO1xuXHRcdFx0cmV0dXJuIGAke29wZXJhdG9yfSAke3RoaXMuaW5mZXJUeXBlKHR5cGVPcC50eXBlKX1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZVF1ZXJ5OiB7XG5cdFx0XHQvLyBIYW5kbGUgdHlwZW9mIGV4cHJlc3Npb25zIGxpa2UgYHR5cGVvZiBVc2FnZUVudHJ5YFxuXHRcdFx0Y29uc3QgdHlwZVF1ZXJ5ID0gdHlwZU5vZGUgYXMgdHMuVHlwZVF1ZXJ5Tm9kZTtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIodHlwZVF1ZXJ5LmV4cHJOYW1lKSkge1xuXHRcdFx0XHRyZXR1cm4gYHR5cGVvZiAke3R5cGVRdWVyeS5leHByTmFtZS50ZXh0fWA7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRkZWZhdWx0OlxuXHRcdFx0Ly8gRm9yIGNvbXBsZXggdHlwZXMsIHJldHVybiB0aGUgdGV4dCByZXByZXNlbnRhdGlvblxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHQqIEluZmVyIHJldHVybiB0eXBlIGZyb20gYSBtZXRob2QgZGVjbGFyYXRpb25cblx0XHQqIFVzZXMgZXhwbGljaXQgcmV0dXJuIHR5cGUgYW5ub3RhdGlvbiBvciBpbmZlcnMgZnJvbSByZXR1cm4gc3RhdGVtZW50c1xuXHRcdCovXG5cdHByaXZhdGUgaW5mZXJSZXR1cm5UeXBlIChtZXRob2Q6IHRzLk1ldGhvZERlY2xhcmF0aW9uLCBjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+KTogc3RyaW5nIHtcblx0XHQvLyBJZiBtZXRob2QgaGFzIGV4cGxpY2l0IHJldHVybiB0eXBlIGFubm90YXRpb24sIHVzZSBpdFxuXHRcdGlmIChtZXRob2QudHlwZSkge1xuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJUeXBlKG1ldGhvZC50eXBlKTtcblx0XHR9XG5cblx0XHQvLyBPdGhlcndpc2UsIHRyeSB0byBpbmZlciBmcm9tIHJldHVybiBzdGF0ZW1lbnRzIGluIHRoZSBtZXRob2QgYm9keVxuXHRcdGlmIChtZXRob2QuYm9keSkge1xuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJSZXR1cm5UeXBlRnJvbUJvZHkobWV0aG9kLmJvZHksIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0fVxuXG5cdFx0cmV0dXJuICd1bmtub3duJztcblx0fVxuXG5cdC8qKlxuXHRcdCogSW5mZXIgcmV0dXJuIHR5cGUgYnkgYW5hbHl6aW5nIHJldHVybiBzdGF0ZW1lbnRzIGluIHRoZSBtZXRob2QgYm9keVxuXHRcdCovXG5cdHByaXZhdGUgaW5mZXJSZXR1cm5UeXBlRnJvbUJvZHkgKGJvZHk6IHRzLkJsb2NrLCBjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+KTogc3RyaW5nIHtcblx0XHRjb25zdCByZXR1cm5UeXBlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXG5cdFx0Y29uc3QgdmlzaXQgPSAobm9kZTogdHMuTm9kZSk6IHZvaWQgPT4ge1xuXHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIobm9kZS5leHByZXNzaW9uLCB1bmRlZmluZWQsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdGlmICh0eXBlICE9PSAndW5rbm93bicpIHtcblx0XHRcdFx0XHRyZXR1cm5UeXBlcy5hZGQodHlwZSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCB2aXNpdCk7XG5cdFx0fTtcblxuXHRcdHZpc2l0KGJvZHkpO1xuXG5cdFx0aWYgKHJldHVyblR5cGVzLnNpemUgPT09IDApIHtcblx0XHRcdHJldHVybiAndm9pZCc7XG5cdFx0fVxuXHRcdGlmIChyZXR1cm5UeXBlcy5zaXplID09PSAxKSB7XG5cdFx0XHRyZXR1cm4gQXJyYXkuZnJvbShyZXR1cm5UeXBlcylbIDAgXTtcblx0XHR9XG5cdFx0cmV0dXJuIEFycmF5LmZyb20ocmV0dXJuVHlwZXMpLmpvaW4oJyB8ICcpO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBHZXQgZnVsbCB0ZXh0IGZyb20gYSBxdWFsaWZpZWQgbmFtZSAoZS5nLiwgTmFtZXNwYWNlLlR5cGUpXG5cdFx0Ki9cblx0cHJpdmF0ZSBnZXRRdWFsaWZpZWROYW1lVGV4dCAocXVhbGlmaWVkTmFtZTogdHMuUXVhbGlmaWVkTmFtZSk6IHN0cmluZyB7XG5cdFx0Y29uc3QgcGFydHM6IHN0cmluZ1tdID0gW107XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLlF1YWxpZmllZE5hbWUgfCB0cy5JZGVudGlmaWVyID0gcXVhbGlmaWVkTmFtZTtcblxuXHRcdHdoaWxlICh0cy5pc1F1YWxpZmllZE5hbWUoY3VycmVudCkpIHtcblx0XHRcdHBhcnRzLnVuc2hpZnQoY3VycmVudC5yaWdodC50ZXh0KTtcblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LmxlZnQ7XG5cdFx0fVxuXHRcdHBhcnRzLnVuc2hpZnQoY3VycmVudC50ZXh0KTtcblxuXHRcdHJldHVybiBwYXJ0cy5qb2luKCcuJyk7XG5cdH1cblxuXHQvKipcblx0ICogSW5mZXIgdHlwZSBmcm9tIGluaXRpYWxpemVyXG5cdCAqL1xuXHRwcml2YXRlIGluZmVyVHlwZUZyb21Jbml0aWFsaXplciAoXG5cdFx0aW5pdGlhbGl6ZXI6IHRzLkV4cHJlc3Npb24sXG5cdFx0ZGF0YVR5cGVNYXA/OiBNYXA8c3RyaW5nLCBzdHJpbmc+LFxuXHRcdGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz5cblx0KTogc3RyaW5nIHtcblx0XHRzd2l0Y2ggKGluaXRpYWxpemVyLmtpbmQpIHtcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuU3RyaW5nTGl0ZXJhbDpcblx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVtZXJpY0xpdGVyYWw6XG5cdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkOlxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdWxsS2V5d29yZDpcblx0XHRcdHJldHVybiAnbnVsbCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVuZGVmaW5lZEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3VuZGVmaW5lZCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkFycmF5TGl0ZXJhbEV4cHJlc3Npb246XG5cdFx0XHRyZXR1cm4gJ0FycmF5PHVua25vd24+Jztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb246XG5cdFx0XHRyZXR1cm4gJ29iamVjdCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk5ld0V4cHJlc3Npb246IHtcblx0XHRcdC8vIEhhbmRsZSBuZXcgRGF0ZSgpLCBuZXcgTWFwKCksIGV0Yy5cblx0XHRcdGNvbnN0IG5ld0V4cHIgPSBpbml0aWFsaXplciBhcyB0cy5OZXdFeHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihuZXdFeHByLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdHJldHVybiBuZXdFeHByLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdH1cblx0XHRcdHJldHVybiAnb2JqZWN0Jztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkJpbmFyeUV4cHJlc3Npb246IHtcblx0XHRcdC8vIEhhbmRsZSBhcml0aG1ldGljIG9wZXJhdGlvbnM6IGEgKiBiLCBhICsgYiwgYSAtIGIsIGEgLyBiXG5cdFx0XHRjb25zdCBiaW5hcnlFeHByID0gaW5pdGlhbGl6ZXIgYXMgdHMuQmluYXJ5RXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IGxlZnRUeXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIoYmluYXJ5RXhwci5sZWZ0LCBkYXRhVHlwZU1hcCwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdGNvbnN0IHJpZ2h0VHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKGJpbmFyeUV4cHIucmlnaHQsIGRhdGFUeXBlTWFwLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0XHRcblx0XHRcdC8vIENoZWNrIGlmIGl0J3MgYW4gYXJpdGhtZXRpYyBvcGVyYXRvclxuXHRcdFx0Y29uc3Qgb3BlcmF0b3IgPSBiaW5hcnlFeHByLm9wZXJhdG9yVG9rZW4ua2luZDtcblx0XHRcdGlmIChvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5Bc3Rlcmlza1Rva2VuIHx8XG5cdFx0XHRcdCAgICBvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5TbGFzaFRva2VuIHx8XG5cdFx0XHRcdCAgICBvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5NaW51c1Rva2VuIHx8XG5cdFx0XHRcdCAgICBvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5QZXJjZW50VG9rZW4pIHtcblx0XHRcdFx0Ly8gQXJpdGhtZXRpYyBvcGVyYXRpb25zIG9uIG51bWJlcnMgcHJvZHVjZSBudW1iZXJzXG5cdFx0XHRcdGlmICgobGVmdFR5cGUgPT09ICdudW1iZXInIHx8IGxlZnRUeXBlID09PSAndW5rbm93bicpICYmXG5cdFx0XHRcdFx0ICAgIChyaWdodFR5cGUgPT09ICdudW1iZXInIHx8IHJpZ2h0VHlwZSA9PT0gJ3Vua25vd24nKSkge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLlBsdXNUb2tlbikge1xuXHRcdFx0XHQvLyBQbHVzIGNhbiBiZSBhZGRpdGlvbiBvciBzdHJpbmcgY29uY2F0ZW5hdGlvblxuXHRcdFx0XHRpZiAobGVmdFR5cGUgPT09ICdzdHJpbmcnIHx8IHJpZ2h0VHlwZSA9PT0gJ3N0cmluZycpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGxlZnRUeXBlID09PSAnbnVtYmVyJyAmJiByaWdodFR5cGUgPT09ICdudW1iZXInKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgcHJvcGVydHkgYWNjZXNzIGxpa2UgZGF0YS52YWx1ZSwgZGF0YS5pZFxuXHRcdFx0aWYgKGRhdGFUeXBlTWFwKSB7XG5cdFx0XHRcdGNvbnN0IGFjY2Vzc0NoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGluaXRpYWxpemVyKTtcblx0XHRcdFx0aWYgKGFjY2Vzc0NoYWluKSB7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IGRhdGFUeXBlTWFwLmdldChhY2Nlc3NDaGFpbik7XG5cdFx0XHRcdFx0aWYgKHR5cGUpIHtcblx0XHRcdFx0XHRcdHJldHVybiB0eXBlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gSGFuZGxlIHRoaXMubWFwLnNpemUgcGF0dGVybiAoTWFwLnNpemUgcmV0dXJucyBudW1iZXIpXG5cdFx0XHRjb25zdCBwcm9wQWNjZXNzID0gaW5pdGlhbGl6ZXIgYXMgdHMuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKHByb3BBY2Nlc3MuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y29uc3Qgb3V0ZXJQcm9wID0gcHJvcEFjY2Vzcy5leHByZXNzaW9uO1xuXHRcdFx0XHQvLyBDaGVjayBmb3IgdGhpcy5tYXAgcGF0dGVyblxuXHRcdFx0XHRsZXQgaW5uZXJOYW1lID0gJyc7XG5cdFx0XHRcdGlmIChvdXRlclByb3AuZXhwcmVzc2lvbi5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0aW5uZXJOYW1lID0gJ3RoaXMnO1xuXHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihvdXRlclByb3AuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRpbm5lck5hbWUgPSBvdXRlclByb3AuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IG1hcFByb3AgPSBvdXRlclByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBmaW5hbFByb3AgPSBwcm9wQWNjZXNzLm5hbWUudGV4dDtcblx0XHRcdFx0Ly8gdGhpcy5tYXAuc2l6ZSAtPiBudW1iZXJcblx0XHRcdFx0aWYgKGlubmVyTmFtZSA9PT0gJ3RoaXMnICYmIG1hcFByb3AgPT09ICdtYXAnICYmIGZpbmFsUHJvcCA9PT0gJ3NpemUnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuSWRlbnRpZmllcjoge1xuXHRcdFx0Ly8gSGFuZGxlIGlkZW50aWZpZXIgcmVmZXJlbmNlcyBpZiBpbiBkYXRhVHlwZU1hcFxuXHRcdFx0aWYgKGRhdGFUeXBlTWFwKSB7XG5cdFx0XHRcdGNvbnN0IG5hbWUgPSAoaW5pdGlhbGl6ZXIgYXMgdHMuSWRlbnRpZmllcikudGV4dDtcblx0XHRcdFx0Y29uc3QgdHlwZSA9IGRhdGFUeXBlTWFwLmdldChuYW1lKTtcblx0XHRcdFx0aWYgKHR5cGUpIHtcblx0XHRcdFx0XHRyZXR1cm4gdHlwZTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkNhbGxFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgZnVuY3Rpb24gY2FsbHMgbGlrZSBEYXRlLm5vdygpLCBwYXJzZUludCgpLCBldGMuXG5cdFx0XHRjb25zdCBjYWxsRXhwciA9IGluaXRpYWxpemVyIGFzIHRzLkNhbGxFeHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxFeHByLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IG1ldGhvZE5hbWUgPSBjYWxsRXhwci5leHByZXNzaW9uLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3Qgb2JqTmFtZSA9IHRzLmlzSWRlbnRpZmllcihjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb24pXG5cdFx0XHRcdFx0PyBjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb24udGV4dFxuXHRcdFx0XHRcdDogJyc7XG5cdFx0XHRcdFx0XG5cdFx0XHRcdC8vIERhdGUubm93KCkgLT4gbnVtYmVyXG5cdFx0XHRcdGlmIChvYmpOYW1lID09PSAnRGF0ZScgJiYgbWV0aG9kTmFtZSA9PT0gJ25vdycpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gU3RyaW5nIG1ldGhvZHMgdGhhdCByZXR1cm4gc3RyaW5nXG5cdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAndG9TdHJpbmcnIHx8IG1ldGhvZE5hbWUgPT09ICd2YWx1ZU9mJykge1xuXHRcdFx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBIYW5kbGUgTWFwIHByb3BlcnR5IGFjY2VzcyBvbiBjbGFzcyBpbnN0YW5jZXMgKHRoaXMubWFwLiopXG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0Y29uc3Qgb3V0ZXJQcm9wID0gY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdFx0XHRcdC8vIEhhbmRsZSBib3RoICd0aGlzJyBrZXl3b3JkIGFuZCBpZGVudGlmaWVyIHBhdHRlcm5zXG5cdFx0XHRcdFx0bGV0IGlubmVyTmFtZSA9ICcnO1xuXHRcdFx0XHRcdGlmIChvdXRlclByb3AuZXhwcmVzc2lvbi5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0XHRpbm5lck5hbWUgPSAndGhpcyc7XG5cdFx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc0lkZW50aWZpZXIob3V0ZXJQcm9wLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0XHRpbm5lck5hbWUgPSBvdXRlclByb3AuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCBtYXBQcm9wID0gb3V0ZXJQcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0XHQvLyB0aGlzLm1hcC5YKCkgcGF0dGVybnNcblx0XHRcdFx0XHRpZiAoaW5uZXJOYW1lID09PSAndGhpcycgJiYgbWFwUHJvcCA9PT0gJ21hcCcpIHtcblx0XHRcdFx0XHRcdC8vIFRyeSB0byBnZXQgdGhlIE1hcCdzIHZhbHVlIHR5cGUgZnJvbSBjbGFzcyBwcm9wZXJ0aWVzXG5cdFx0XHRcdFx0XHRsZXQgbWFwVmFsdWVUeXBlID0gJ3Vua25vd24nO1xuXHRcdFx0XHRcdFx0aWYgKGNsYXNzUHJvcGVydHlUeXBlcykge1xuXHRcdFx0XHRcdFx0XHRjb25zdCBtYXBUeXBlID0gY2xhc3NQcm9wZXJ0eVR5cGVzLmdldCgnbWFwJyk7XG5cdFx0XHRcdFx0XHRcdGlmIChtYXBUeXBlICYmIG1hcFR5cGUuc3RhcnRzV2l0aCgnTWFwPCcpKSB7XG5cdFx0XHRcdFx0XHRcdFx0Ly8gUGFyc2UgTWFwPEssIFY+IHRvIGdldCBWXG5cdFx0XHRcdFx0XHRcdFx0Y29uc3QgbWF0Y2ggPSBtYXBUeXBlLm1hdGNoKC9NYXA8W14sXSssXFxzKiguKyk+JC8pO1xuXHRcdFx0XHRcdFx0XHRcdGlmIChtYXRjaCkge1xuXHRcdFx0XHRcdFx0XHRcdFx0bWFwVmFsdWVUeXBlID0gbWF0Y2hbIDEgXTtcblx0XHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnaGFzJykgcmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnc2V0JykgcmV0dXJuICd0aGlzJztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZ2V0JykgcmV0dXJuIG1hcFZhbHVlVHlwZTtcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZGVsZXRlJykgcmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnY2xlYXInKSByZXR1cm4gJ3ZvaWQnO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICd2YWx1ZXMnKSByZXR1cm4gYEl0ZXJhYmxlSXRlcmF0b3I8JHttYXBWYWx1ZVR5cGV9PmA7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2tleXMnKSByZXR1cm4gJ0l0ZXJhYmxlSXRlcmF0b3I8c3RyaW5nPic7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2VudHJpZXMnKSByZXR1cm4gYEl0ZXJhYmxlSXRlcmF0b3I8W3N0cmluZywgJHttYXBWYWx1ZVR5cGV9XT5gO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBEaXJlY3QgbWFwLlgoKSBjYWxsc1xuXHRcdFx0XHRpZiAob2JqTmFtZSA9PT0gJ21hcCcgfHwgb2JqTmFtZSA9PT0gJ29iaicpIHtcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2hhcycpIHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdzZXQnKSByZXR1cm4gJ3RoaXMnO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZ2V0JykgcmV0dXJuICd1bmtub3duJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2RlbGV0ZScpIHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdjbGVhcicpIHJldHVybiAndm9pZCc7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICd2YWx1ZXMnKSByZXR1cm4gJ0l0ZXJhYmxlSXRlcmF0b3I8dW5rbm93bj4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAna2V5cycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjxzdHJpbmc+Jztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2VudHJpZXMnKSByZXR1cm4gJ0l0ZXJhYmxlSXRlcmF0b3I8W3N0cmluZywgdW5rbm93bl0+Jztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gcGFyc2VJbnQsIHBhcnNlRmxvYXQgLT4gbnVtYmVyXG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGNhbGxFeHByLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IGZuTmFtZSA9IGNhbGxFeHByLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ3BhcnNlSW50JyB8fCBmbk5hbWUgPT09ICdwYXJzZUZsb2F0Jykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoZm5OYW1lID09PSAnU3RyaW5nJykge1xuXHRcdFx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoZm5OYW1lID09PSAnTnVtYmVyJykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoZm5OYW1lID09PSAnQm9vbGVhbicpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVGVtcGxhdGVFeHByZXNzaW9uOlxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Ob1N1YnN0aXR1dGlvblRlbXBsYXRlTGl0ZXJhbDoge1xuXHRcdFx0Ly8gVGVtcGxhdGUgbGl0ZXJhbHMgbGlrZSBgJHtiYXNlVmFsdWV9LSR7ZXh0cmF9YCBhbHdheXMgcHJvZHVjZSBzdHJpbmdzXG5cdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0fVxuXHRcdGRlZmF1bHQ6XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIENvbGxlY3QgdXNhZ2UgaW5mb3JtYXRpb24gZm9yIHR5cGUgcmVmZXJlbmNlc1xuXHRcdFx0Ki9cblx0cHJpdmF0ZSBjb2xsZWN0VXNhZ2UgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHQvLyBDaGVjayBmb3IgbmV3IFR5cGUoKSBpbnN0YW50aWF0aW9uXG5cdFx0aWYgKHRzLmlzTmV3RXhwcmVzc2lvbihub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdGxldCB0eXBlTmFtZTogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0dHlwZU5hbWUgPSB0aGlzLnJlc29sdmVUeXBlUGF0aChub2RlLmV4cHJlc3Npb24pO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0dHlwZU5hbWUgPSB0aGlzLmdldFR5cGVOYW1lRnJvbUV4cHJlc3Npb24obm9kZS5leHByZXNzaW9uKTtcblx0XHRcdH1cblx0XHRcdGlmICh0eXBlTmFtZSkge1xuXHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdCk7XG5cdFx0XHRcdHRoaXMuYWRkVXNhZ2UodHlwZU5hbWUsIHtcblx0XHRcdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdGtpbmQgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0XHRcdGNvZGUgICAgIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdH0pO1xuXHRcdFx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50IGZyb20gbmV3IFR5cGUoKSBmb3IgZmxvdyBhbmFseXNpc1xuXHRcdFx0XHR0aGlzLnRyYWNrTmV3QXNzaWdubWVudChub2RlLCB0eXBlTmFtZSk7XG5cdFx0XHRcdC8vIEFsc28gcmVjb3JkIGFzIGZsb3cgZXZlbnRcblx0XHRcdFx0dGhpcy5hZGRGbG93KHR5cGVOYW1lLCB7XG5cdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRraW5kICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdGNvbnRleHQgIDogJ25ldyBleHByZXNzaW9uJyxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcblx0XHQvLyBDaGVjayBmb3IgcHJvcGVydHkgYWNjZXNzIG9uIGluc3RhbmNlcyAodXNlci5BZG1pblR5cGUpXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRjb25zdCBwcm9wTmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0Ly8gQ2hlY2sgaWYgdGhpcyBsb29rcyBsaWtlIGEgdHlwZSBhY2Nlc3MgcGF0dGVyblxuXHRcdFx0aWYgKHByb3BOYW1lICYmIHRoaXMuaXNMaWtlbHlUeXBlTmFtZShwcm9wTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHQpO1xuXHRcdFx0XHRcdC8vIFRyeSB0byByZXNvbHZlIGZ1bGwgcGF0aFxuXHRcdFx0XHRjb25zdCBmdWxsUGF0aCA9IHRoaXMucmVzb2x2ZVR5cGVQYXRoKG5vZGUpO1xuXHRcdFx0XHRpZiAoZnVsbFBhdGgpIHtcblx0XHRcdFx0XHR0aGlzLmFkZFVzYWdlKGZ1bGxQYXRoLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdFx0a2luZCAgICAgOiAncHJvcGVydHlBY2Nlc3MnLFxuXHRcdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0Ly8gQ2hlY2sgZm9yIGxvb2t1cCgnVHlwZU5hbWUnKSBvciBsb29rdXAoc291cmNlLCAnVHlwZU5hbWUnKSBjYWxsc1xuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0Y29uc3QgZnVuY05hbWUgPSB0aGlzLmdldEZ1bmN0aW9uTmFtZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdFx0aWYgKGZ1bmNOYW1lID09PSAnbG9va3VwJyAmJiBub2RlLmFyZ3VtZW50cy5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdGNvbnN0IHR5cGVQYXRoID0gdGhpcy5yZXNvbHZlTG9va3VwUGF0aChub2RlKTtcblx0XHRcdFx0aWYgKHR5cGVQYXRoKSB7XG5cdFx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0XHQpO1xuXHRcdFx0XHRcdHRoaXMuYWRkVXNhZ2UodHlwZVBhdGgsIHtcblx0XHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0XHRraW5kICAgICA6ICdsb29rdXAnLFxuXHRcdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50IGZyb20gbG9va3VwIGZvciBpbnN0YW50aWF0aW9uIHRyYWNraW5nXG5cdFx0XHRcdFx0dGhpcy50cmFja0xvb2t1cEFzc2lnbm1lbnQobm9kZSwgdHlwZVBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cdFxuXHQvKipcblx0XHRcdCogR2V0IGZ1bmN0aW9uIG5hbWUgZnJvbSBleHByZXNzaW9uIChpZGVudGlmaWVyIG9yIHByb3BlcnR5IGFjY2Vzcylcblx0XHRcdCovXG5cdHByaXZhdGUgZ2V0RnVuY3Rpb25OYW1lIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci50ZXh0O1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIEFkZCBhIHVzYWdlIHRvIHRoZSBjb2xsZWN0aW9uXG5cdFx0XHQqL1xuXHRwcml2YXRlIGFkZFVzYWdlICh0eXBlUGF0aDogc3RyaW5nLCB1c2FnZTogVXNhZ2VJbmZvKTogdm9pZCB7XG5cdFx0Ly8gT25seSB0cmFjayB1c2FnZXMgb2YgbW5lbW9uaWNhLWRlZmluZWQgdHlwZXNcblx0XHRpZiAoIXRoaXMuZGVmaW5pdGlvbnMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAoIXRoaXMudXNhZ2VzLmhhcyh0eXBlUGF0aCkpIHtcblx0XHRcdHRoaXMudXNhZ2VzLnNldCh0eXBlUGF0aCwgW10pO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBkdXBsaWNhdGVzIGJhc2VkIG9uIGxvY2F0aW9uLCBjb2RlLCBhbmQga2luZFxuXHRcdGNvbnN0IGV4aXN0aW5nVXNhZ2VzID0gdGhpcy51c2FnZXMuZ2V0KHR5cGVQYXRoKSE7XG5cdFx0Y29uc3QgaXNEdXBsaWNhdGUgPSBleGlzdGluZ1VzYWdlcy5zb21lKGV4aXN0aW5nID0+XG5cdFx0XHRleGlzdGluZy5sb2NhdGlvbiA9PT0gdXNhZ2UubG9jYXRpb24gJiZcblx0XHRcdFx0ZXhpc3RpbmcuY29kZSA9PT0gdXNhZ2UuY29kZSAmJlxuXHRcdFx0XHRleGlzdGluZy5raW5kID09PSB1c2FnZS5raW5kKTtcblxuXHRcdGlmICghaXNEdXBsaWNhdGUpIHtcblx0XHRcdGV4aXN0aW5nVXNhZ2VzLnB1c2godXNhZ2UpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IEVEUyAoRXhlY3V0aW9uIERhdGEgU3RvcmFnZSkgdXNhZ2UgaW5mb3JtYXRpb25cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEVEUyAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSB8fCAhbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgZnVuY05hbWUgPSB0aGlzLmdldEZ1bmN0aW9uTmFtZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghZnVuY05hbWUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHQvLyB3cmFwKGZuKSwgd3JhcEFyZ3MoZm4pLCB3cmFwSW5zdGFuY2VNZXRob2RzKG9iailcblx0XHRpZiAoZnVuY05hbWUgPT09ICd3cmFwJyB8fCBmdW5jTmFtZSA9PT0gJ3dyYXBBcmdzJyB8fCBmdW5jTmFtZSA9PT0gJ3dyYXBJbnN0YW5jZU1ldGhvZHMnKSB7XG5cdFx0XHRjb25zdCB0YXJnZXRUeXBlID0gdGhpcy5yZXNvbHZlRURTQXJndW1lbnRUeXBlKG5vZGUuYXJndW1lbnRzWyAwIF0pO1xuXHRcdFx0dGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAnd3JhcCcsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHRhcmdldFR5cGUgOiB0YXJnZXRUeXBlIHx8IHVuZGVmaW5lZCxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGxpbmsocGFyZW50LCBjaGlsZCksIHJ1bldpdGhJbnN0YW5jZShpbnN0YW5jZSwgZm4pXG5cdFx0aWYgKGZ1bmNOYW1lID09PSAnbGluaycgfHwgZnVuY05hbWUgPT09ICdydW5XaXRoSW5zdGFuY2UnKSB7XG5cdFx0XHRjb25zdCB0YXJnZXRUeXBlID0gdGhpcy5yZXNvbHZlRURTQXJndW1lbnRUeXBlKG5vZGUuYXJndW1lbnRzWyAwIF0pO1xuXHRcdFx0dGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAnbGluaycsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHRhcmdldFR5cGUgOiB0YXJnZXRUeXBlIHx8IHVuZGVmaW5lZCxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGdldExhc3RDb250ZXh0KCksIGdldEVycm9ySW5zdGFuY2UoZXJyKVxuXHRcdGlmIChmdW5jTmFtZSA9PT0gJ2dldExhc3RDb250ZXh0JyB8fCBmdW5jTmFtZSA9PT0gJ2dldEVycm9ySW5zdGFuY2UnKSB7XG5cdFx0XHR0aGlzLmFkZEVEUygndW5rbm93bicsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgOiAnY29udGV4dENvbnN1bWUnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gZW5yaWNoRXJyb3IoZXJyLCBpbnN0YW5jZSlcblx0XHRpZiAoZnVuY05hbWUgPT09ICdlbnJpY2hFcnJvcicpIHtcblx0XHRcdGNvbnN0IHRhcmdldFR5cGUgPSBub2RlLmFyZ3VtZW50cy5sZW5ndGggPiAxXG5cdFx0XHRcdD8gdGhpcy5yZXNvbHZlRURTQXJndW1lbnRUeXBlKG5vZGUuYXJndW1lbnRzWyAxIF0pXG5cdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0dGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAnZXJyb3JFbnJpY2gnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBhdHRhY2hIb29rcyh0eXBlcyksIGF0dGFjaEhvb2tzKFtBLCBCXSlcblx0XHRpZiAoZnVuY05hbWUgPT09ICdhdHRhY2hIb29rcycgJiYgbm9kZS5hcmd1bWVudHMubGVuZ3RoID4gMCkge1xuXHRcdFx0Y29uc3QgYXJnID0gbm9kZS5hcmd1bWVudHNbIDAgXTtcblx0XHRcdGlmICh0cy5pc0FycmF5TGl0ZXJhbEV4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2YgYXJnLmVsZW1lbnRzKSB7XG5cdFx0XHRcdFx0Y29uc3QgdGFyZ2V0VHlwZSA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShlbGVtZW50KTtcblx0XHRcdFx0XHR0aGlzLmFkZEVEUyh0YXJnZXRUeXBlIHx8ICd1bmtub3duJywge1xuXHRcdFx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdFx0XHRraW5kICAgICAgIDogJ2hvb2tBdHRhY2gnLFxuXHRcdFx0XHRcdFx0Y29kZSxcblx0XHRcdFx0XHRcdHRhcmdldFR5cGUgOiB0YXJnZXRUeXBlIHx8IHVuZGVmaW5lZCxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgdGFyZ2V0VHlwZSA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShhcmcpO1xuXHRcdFx0XHR0aGlzLmFkZEVEUyh0YXJnZXRUeXBlIHx8ICd1bmtub3duJywge1xuXHRcdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRcdGtpbmQgICAgICAgOiAnaG9va0F0dGFjaCcsXG5cdFx0XHRcdFx0Y29kZSxcblx0XHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEFkYXB0ZXJzOiBjcmVhdGVEaXZlSW50ZXJjZXB0b3IsIGNyZWF0ZURpdmVQbHVnaW4sIGNyZWF0ZURpdmVNaWRkbGV3YXJlXG5cdFx0aWYgKFxuXHRcdFx0ZnVuY05hbWUgPT09ICdjcmVhdGVEaXZlSW50ZXJjZXB0b3InIHx8XG5cdFx0XHRmdW5jTmFtZSA9PT0gJ2NyZWF0ZURpdmVQbHVnaW4nIHx8XG5cdFx0XHRmdW5jTmFtZSA9PT0gJ2NyZWF0ZURpdmVNaWRkbGV3YXJlJ1xuXHRcdCkge1xuXHRcdFx0dGhpcy5hZGRFRFMoJ3Vua25vd24nLCB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kIDogJ2FkYXB0ZXJVc2UnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgdHlwZSBmcm9tIEVEUyBjYWxsIGFyZ3VtZW50IChiZXN0IGVmZm9ydClcblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUVEU0FyZ3VtZW50VHlwZSAoYXJnOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIWFyZykge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBJZGVudGlmaWVyOiB2YXJpYWJsZSBuYW1lXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihhcmcpKSB7XG5cdFx0XHRjb25zdCBtYXBwZWQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChhcmcudGV4dCk7XG5cdFx0XHRpZiAobWFwcGVkKSB7XG5cdFx0XHRcdHJldHVybiBtYXBwZWQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBNYXliZSBpdCdzIGEgdHlwZSBuYW1lIGRpcmVjdGx5XG5cdFx0XHRpZiAodGhpcy5kZWZpbml0aW9ucy5oYXMoYXJnLnRleHQpKSB7XG5cdFx0XHRcdHJldHVybiBhcmcudGV4dDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiBvYmoucHJvcFxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcmcpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5yZXNvbHZlVHlwZVBhdGgoYXJnKTtcblx0XHR9XG5cblx0XHQvLyBUaGlzIGV4cHJlc3Npb246IHRoaXMuc29tZXRoaW5nXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFyZykgJiYgdHMuaXNJZGVudGlmaWVyKGFyZy5leHByZXNzaW9uKSAmJiBhcmcuZXhwcmVzc2lvbi50ZXh0ID09PSAndGhpcycpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBBZGQgYW4gRURTIHVzYWdlIHRvIHRoZSBjb2xsZWN0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGFkZEVEUyAodHlwZVBhdGg6IHN0cmluZywgaW5mbzogRURTSW5mbyk6IHZvaWQge1xuXHRcdGlmICghdGhpcy5lZHNVc2FnZXMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0dGhpcy5lZHNVc2FnZXMuc2V0KHR5cGVQYXRoLCBbXSk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZXhpc3RpbmcgPSB0aGlzLmVkc1VzYWdlcy5nZXQodHlwZVBhdGgpITtcblx0XHRjb25zdCBpc0R1cGxpY2F0ZSA9IGV4aXN0aW5nLnNvbWUoZSA9PiB7XG5cdFx0XHRyZXR1cm4gZS5sb2NhdGlvbiA9PT0gaW5mby5sb2NhdGlvbiAmJlxuXHRcdFx0XHRlLmtpbmQgPT09IGluZm8ua2luZCAmJlxuXHRcdFx0XHRlLmNvZGUgPT09IGluZm8uY29kZTtcblx0XHR9KTtcblxuXHRcdGlmICghaXNEdXBsaWNhdGUpIHtcblx0XHRcdGV4aXN0aW5nLnB1c2goaW5mbyk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgbmF0aXZlIGZsb3cgcGF0dGVybnMgKGluc3RhbmNlIHVzYWdlIGFmdGVyIGNyZWF0aW9uKVxuXHQgKiBQaGFzZSAxOiBwcm9wZXJ0eSBhY2Nlc3MsIG1ldGhvZCBjYWxscywgYXJndW1lbnRzLCByZXR1cm4sIGRlc3RydWN0dXJpbmcsIGV0Yy5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3cgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHQvLyBQcm9wZXJ0eSByZWFkOiB1c2VyLm5hbWUgb3IgdXNlcj8ubmFtZVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd1Byb3BlcnR5QWNjZXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEVsZW1lbnQgYWNjZXNzOiB1c2VyWyduYW1lJ11cblx0XHRpZiAodHMuaXNFbGVtZW50QWNjZXNzRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0VsZW1lbnRBY2Nlc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgd3JpdGU6IHVzZXIubmFtZSA9IHZhbHVlXG5cdFx0aWYgKHRzLmlzQmluYXJ5RXhwcmVzc2lvbihub2RlKSAmJiBub2RlLm9wZXJhdG9yVG9rZW4ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0Fzc2lnbm1lbnQobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gTWV0aG9kIGNhbGw6IHVzZXIudmFsaWRhdGUoKSAgQU5EICBhcmd1bWVudCBwYXNzaW5nOiBwcm9jZXNzVXNlcih1c2VyKVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd01ldGhvZENhbGwobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93QXJndW1lbnRQYXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIERlc3RydWN0dXJlIHJlYWQ6IGNvbnN0IHsgbmFtZSB9ID0gdXNlclxuXHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgJiYgbm9kZS5pbml0aWFsaXplcikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0Rlc3RydWN0dXJlKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFJldHVybiBpbnN0YW5jZTogcmV0dXJuIHVzZXJcblx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQobm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93UmV0dXJuKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFNwcmVhZDogeyAuLi51c2VyIH1cblx0XHRpZiAodHMuaXNTcHJlYWRFbGVtZW50KG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93U3ByZWFkKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IHByb3BlcnR5IGFjY2VzcyBmbG93IChyZWFkIG9yIGNvbmRpdGlvbmFsKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd1Byb3BlcnR5QWNjZXNzIChub2RlOiB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBwcm9wTmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIFNraXAgaWYgdGhpcyBpcyBhIHR5cGUgY29uc3RydWN0b3IgYWNjZXNzIChlLmcuLCBVc2VyVHlwZS5kZWZpbmUpXG5cdFx0aWYgKHByb3BOYW1lID09PSAnZGVmaW5lJyB8fCBwcm9wTmFtZSA9PT0gJ2xhenknKSB7IHJldHVybjsgfVxuXG5cdFx0dGhpcy5hZGRGbG93KG9iamVjdFR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICAgIDogJ3Byb3BlcnR5UmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0cHJvcGVydHlOYW1lIDogcHJvcE5hbWUsXG5cdFx0XHR0YXJnZXRUeXBlICAgOiBvYmplY3RUeXBlXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBlbGVtZW50IGFjY2VzcyBmbG93OiB1c2VyWyduYW1lJ11cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dFbGVtZW50QWNjZXNzIChub2RlOiB0cy5FbGVtZW50QWNjZXNzRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnZWxlbWVudEFjY2VzcycsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGFzc2lnbm1lbnQgZmxvdzogdXNlci5uYW1lID0gdmFsdWUgb3IgdXNlciA9IG90aGVyXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93QXNzaWdubWVudCAobm9kZTogdHMuQmluYXJ5RXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIFByb3BlcnR5IHdyaXRlOiB1c2VyLm5hbWUgPSB2YWx1ZVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmxlZnQpKSB7XG5cdFx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5sZWZ0LmV4cHJlc3Npb24pO1xuXHRcdFx0aWYgKCFvYmplY3RUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0XHRjb25zdCBwcm9wTmFtZSA9IG5vZGUubGVmdC5uYW1lLnRleHQ7XG5cdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdCk7XG5cdFx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCAgICAgICAgIDogJ3Byb3BlcnR5V3JpdGUnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRwcm9wZXJ0eU5hbWUgOiBwcm9wTmFtZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSAgIDogb2JqZWN0VHlwZVxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gVmFyaWFibGUgcmVhc3NpZ25tZW50OiB1c2VyID0gb3RoZXJcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG5vZGUubGVmdCkpIHtcblx0XHRcdGNvbnN0IHZhck5hbWUgPSBub2RlLmxlZnQudGV4dDtcblx0XHRcdGNvbnN0IG1hcHBlZFR5cGUgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldCh2YXJOYW1lKTtcblx0XHRcdGlmICghbWFwcGVkVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHQpO1xuXHRcdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdFx0dGhpcy5hZGRGbG93KG1hcHBlZFR5cGUsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAncmVhc3NpZ25tZW50Jyxcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSA6IG1hcHBlZFR5cGVcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IG1ldGhvZCBjYWxsIGZsb3c6IHVzZXIudmFsaWRhdGUoKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd01ldGhvZENhbGwgKG5vZGU6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3Qgb2JqZWN0VHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbi5leHByZXNzaW9uKTtcblx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBtZXRob2ROYW1lID0gbm9kZS5leHByZXNzaW9uLm5hbWUudGV4dDtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHQvLyBTa2lwIGlmIHRoaXMgaXMgYSB0eXBlIGNvbnN0cnVjdG9yIGNhbGwgKGUuZy4sIG5ldyBVc2VyVHlwZSgpKVxuXHRcdGlmIChtZXRob2ROYW1lID09PSAnZGVmaW5lJyB8fCBtZXRob2ROYW1lID09PSAnbGF6eScpIHsgcmV0dXJuOyB9XG5cblx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgICAgOiAnbWV0aG9kQ2FsbCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0cHJvcGVydHlOYW1lIDogbWV0aG9kTmFtZSxcblx0XHRcdHRhcmdldFR5cGUgICA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGFyZ3VtZW50IHBhc3NpbmcgZmxvdzogcHJvY2Vzc1VzZXIodXNlcilcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dBcmd1bWVudFBhc3MgKG5vZGU6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuXHRcdFx0Y29uc3QgYXJnID0gbm9kZS5hcmd1bWVudHNbIGkgXTtcblx0XHRcdGNvbnN0IGFyZ1R5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShhcmcpO1xuXHRcdFx0aWYgKCFhcmdUeXBlKSB7IGNvbnRpbnVlOyB9XG5cblx0XHRcdGNvbnN0IGZ1bmNOYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKSB8fCAnYW5vbnltb3VzJztcblx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0KTtcblx0XHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRcdHRoaXMuYWRkRmxvdyhhcmdUeXBlLCB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgIDogJ3Bhc3NBc0FyZycsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHRhcmdldFR5cGUgOiBhcmdUeXBlLFxuXHRcdFx0XHRjb250ZXh0ICAgIDogYGFyZyAke2l9IHRvICR7ZnVuY05hbWV9YFxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgZGVzdHJ1Y3R1cmluZyBmbG93OiBjb25zdCB7IG5hbWUgfSA9IHVzZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dEZXN0cnVjdHVyZSAobm9kZTogdHMuVmFyaWFibGVEZWNsYXJhdGlvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNPYmplY3RCaW5kaW5nUGF0dGVybihub2RlLm5hbWUpKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3Qgc291cmNlVHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuaW5pdGlhbGl6ZXIhKTtcblx0XHRpZiAoIXNvdXJjZVR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHQvLyBFeHRyYWN0IGRlc3RydWN0dXJlZCBwcm9wZXJ0eSBuYW1lc1xuXHRcdGNvbnN0IHByb3BzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBub2RlLm5hbWUuZWxlbWVudHMpIHtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZWxlbWVudC5uYW1lKSkge1xuXHRcdFx0XHRwcm9wcy5wdXNoKGVsZW1lbnQubmFtZS50ZXh0KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHR0aGlzLmFkZEZsb3coc291cmNlVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ2Rlc3RydWN0dXJlUmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHNvdXJjZVR5cGUsXG5cdFx0XHRjb250ZXh0ICAgIDogcHJvcHMuam9pbignLCAnKVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgcmV0dXJuIGZsb3c6IHJldHVybiB1c2VyXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93UmV0dXJuIChub2RlOiB0cy5SZXR1cm5TdGF0ZW1lbnQsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCByZXR1cm5UeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uISk7XG5cdFx0aWYgKCFyZXR1cm5UeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0dGhpcy5hZGRGbG93KHJldHVyblR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICA6ICdyZXR1cm4nLFxuXHRcdFx0Y29kZSxcblx0XHRcdHRhcmdldFR5cGUgOiByZXR1cm5UeXBlXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBzcHJlYWQgZmxvdzogeyAuLi51c2VyIH1cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dTcHJlYWQgKG5vZGU6IHRzLlNwcmVhZEVsZW1lbnQsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCBzcHJlYWRUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIXNwcmVhZFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHR0aGlzLmFkZEZsb3coc3ByZWFkVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ3NwcmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHNwcmVhZFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHR5cGUgZnJvbSBhbiBleHByZXNzaW9uIChpZGVudGlmaWVyLCBwcm9wZXJ0eSBhY2Nlc3MsIGV0Yy4pXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVFeHByZXNzaW9uVHlwZSAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gSWRlbnRpZmllcjogdXNlclxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChleHByLnRleHQpO1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2VzczogdXNlci5uYW1lIChyZXR1cm4gb2JqZWN0IHR5cGUsIG5vdCBwcm9wZXJ0eSB0eXBlKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKGV4cHIuZXhwcmVzc2lvbik7XG5cdFx0fVxuXG5cdFx0Ly8gRWxlbWVudCBhY2Nlc3M6IHVzZXJbJ25hbWUnXVxuXHRcdGlmICh0cy5pc0VsZW1lbnRBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUoZXhwci5leHByZXNzaW9uKTtcblx0XHR9XG5cblx0XHQvLyBUaGlzIGV4cHJlc3Npb246IHRoaXMgKGlmIGluIGEgbWV0aG9kLCB3ZSBjYW4ndCByZXNvbHZlIHdpdGhvdXQgbW9yZSBjb250ZXh0KVxuXHRcdGlmIChleHByLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBBZGQgYSBmbG93IHVzYWdlIHRvIHRoZSBjb2xsZWN0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGFkZEZsb3cgKHR5cGVQYXRoOiBzdHJpbmcsIGluZm86IEZsb3dJbmZvKTogdm9pZCB7XG5cdFx0aWYgKCF0aGlzLmZsb3dVc2FnZXMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0dGhpcy5mbG93VXNhZ2VzLnNldCh0eXBlUGF0aCwgW10pO1xuXHRcdH1cblxuXHRcdGNvbnN0IGV4aXN0aW5nID0gdGhpcy5mbG93VXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGlzRHVwbGljYXRlID0gZXhpc3Rpbmcuc29tZShlID0+IHtcblx0XHRcdHJldHVybiBlLmxvY2F0aW9uID09PSBpbmZvLmxvY2F0aW9uICYmXG5cdFx0XHRcdGUua2luZCA9PT0gaW5mby5raW5kICYmXG5cdFx0XHRcdGUuY29kZSA9PT0gaW5mby5jb2RlO1xuXHRcdH0pO1xuXG5cdFx0aWYgKCFpc0R1cGxpY2F0ZSkge1xuXHRcdFx0ZXhpc3RpbmcucHVzaChpbmZvKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHRcdCogR2V0IHR5cGUgbmFtZSBmcm9tIGV4cHJlc3Npb24gKGlkZW50aWZpZXIgb3IgcHJvcGVydHkgYWNjZXNzKVxuXHRcdFx0Ki9cblx0cHJpdmF0ZSBnZXRUeXBlTmFtZUZyb21FeHByZXNzaW9uIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBuYW1lID0gZXhwci50ZXh0O1xuXHRcdFx0Ly8gQ2hlY2sgaWYgdGhpcyBpZGVudGlmaWVyIGlzIGEgdmFyaWFibGUgbWFwcGVkIHRvIGEgdHlwZSAoZS5nLiwgZnJvbSBsb29rdXApXG5cdFx0XHRjb25zdCBtYXBwZWRUeXBlID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0XHRpZiAobWFwcGVkVHlwZSkge1xuXHRcdFx0XHRyZXR1cm4gbWFwcGVkVHlwZTtcblx0XHRcdH1cblx0XHRcdHJldHVybiBuYW1lO1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKGV4cHIpO1xuXHRcdFx0cmV0dXJuIGNoYWluLmpvaW4oJy4nKTtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIFJlc29sdmUgZnVsbCB0eXBlIHBhdGggZnJvbSBwcm9wZXJ0eSBhY2Nlc3Ncblx0XHRcdCovXG5cdHByaXZhdGUgcmVzb2x2ZVR5cGVQYXRoIChleHByOiB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKGV4cHIpO1xuXHRcdGlmIChjaGFpbi5sZW5ndGggPT09IDApIHJldHVybiB1bmRlZmluZWQ7XG5cdFxuXHRcdC8vIENoZWNrIGlmIHRoaXMgY2hhaW4gbWF0Y2hlcyBhIGtub3duIHR5cGVcblx0XHRjb25zdCBmdWxsUGF0aCA9IGNoYWluLmpvaW4oJy4nKTtcblx0XHRpZiAodGhpcy5kZWZpbml0aW9ucy5oYXMoZnVsbFBhdGgpKSB7XG5cdFx0XHRyZXR1cm4gZnVsbFBhdGg7XG5cdFx0fVxuXHRcblx0XHQvLyBUcnkganVzdCB0aGUgcHJvcGVydHkgbmFtZVxuXHRcdGNvbnN0IHByb3BOYW1lID0gY2hhaW5bIGNoYWluLmxlbmd0aCAtIDEgXTtcblx0XHRmb3IgKGNvbnN0IFsgcGF0aCBdIG9mIHRoaXMuZGVmaW5pdGlvbnMpIHtcblx0XHRcdGlmIChwYXRoLmVuZHNXaXRoKGAuJHtwcm9wTmFtZX1gKSB8fCBwYXRoID09PSBwcm9wTmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdH1cblx0XHR9XG5cdFxuXHRcdHJldHVybiBmdWxsUGF0aDtcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQgKiBDaGVjayBpZiBhIG5hbWUgbG9va3MgbGlrZSBhIHR5cGUgKHN0YXJ0cyB3aXRoIHVwcGVyY2FzZSlcblx0XHRcdCAqL1xuXHRwcml2YXRlIGlzTGlrZWx5VHlwZU5hbWUgKG5hbWU6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRcdHJldHVybiBuYW1lWyAwIF0gPj0gJ0EnICYmIG5hbWVbIDAgXSA8PSAnWic7XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0ICogUmVzb2x2ZSBhIGNvbnN0cnVjdG9yIHBhcmFtZXRlciB0eXBlLCBleHBhbmRpbmcgaW5saW5lIG9iamVjdCBsaXRlcmFsc1xuXHRcdFx0ICogYW5kIHR5cGUgYWxpYXNlcyB3aGVyZSBwb3NzaWJsZS5cblx0XHRcdCAqL1xuXHRwcml2YXRlIHJlc29sdmVDb25zdHJ1Y3RvclBhcmFtVHlwZSAodHlwZU5vZGU6IHRzLlR5cGVOb2RlIHwgdW5kZWZpbmVkKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIXR5cGVOb2RlKSByZXR1cm4gdW5kZWZpbmVkO1xuXG5cdFx0Ly8gRGlyZWN0IGlubGluZSB0eXBlIGxpdGVyYWw6IHsgcHJvcDogdHlwZSB9XG5cdFx0aWYgKHRzLmlzVHlwZUxpdGVyYWxOb2RlKHR5cGVOb2RlKSkge1xuXHRcdFx0Y29uc3QgcHJvcHM6IHN0cmluZ1tdID0gW107XG5cdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiB0eXBlTm9kZS5tZW1iZXJzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRjb25zdCBvcHRpb25hbCA9IG1lbWJlci5xdWVzdGlvblRva2VuID8gJz8nIDogJyc7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRwcm9wcy5wdXNoKGAke3Byb3BOYW1lfSR7b3B0aW9uYWx9OiAke3R5cGV9YCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiBgeyAke3Byb3BzLmpvaW4oJzsgJyl9IH1gO1xuXHRcdH1cblxuXHRcdC8vIFR5cGUgcmVmZXJlbmNlOiB1c2FnZSwgVXNlckRhdGEsIGV0Yy4gLSByZWN1cnNpdmVseSBleHBhbmRcblx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZSh0eXBlTm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKHR5cGVOb2RlLnR5cGVOYW1lKSkge1xuXHRcdFx0Y29uc3QgdHlwZU5hbWUgPSB0eXBlTm9kZS50eXBlTmFtZS50ZXh0O1xuXHRcdFx0Y29uc3QgYWxpYXNlZFR5cGUgPSB0aGlzLnR5cGVBbGlhc2VzLmdldCh0eXBlTmFtZSk7XG5cdFx0XHRpZiAoYWxpYXNlZFR5cGUpIHtcblx0XHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLnJlc29sdmVDb25zdHJ1Y3RvclBhcmFtVHlwZShhbGlhc2VkVHlwZSk7XG5cdFx0XHRcdGlmIChleHBhbmRlZCkgcmV0dXJuIGV4cGFuZGVkO1xuXHRcdFx0fVxuXHRcdFx0Ly8gSWYgbm90IGFuIG9iamVjdCB0eXBlIGFsaWFzLCByZXR1cm4gdGhlIHR5cGUgbmFtZSB3aXRoIGFyZ3Ncblx0XHRcdGlmICh0eXBlTm9kZS50eXBlQXJndW1lbnRzICYmIHR5cGVOb2RlLnR5cGVBcmd1bWVudHMubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRjb25zdCBhcmdzID0gdHlwZU5vZGUudHlwZUFyZ3VtZW50cy5tYXAoYXJnID0+IHRoaXMuaW5mZXJUeXBlKGFyZykpO1xuXHRcdFx0XHRyZXR1cm4gYCR7dHlwZU5hbWUgIH08JHsgIGFyZ3Muam9pbignLCAnKSAgfT5gO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHR5cGVOYW1lO1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0XHRcdCAqIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGEgY2xhc3MtbGlrZSBub2RlLlxuXHRcdFx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENsYXNzQ29uc3RydWN0b3JQYXJhbXMgKGNsYXNzTGlrZTogdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHRzLkNsYXNzRXhwcmVzc2lvbik6XG5cdFx0Q29uc3RydWN0b3JQYXJhbUluZm9bXSB7XG5cdFx0Y29uc3QgcGFyYW1zOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdID0gW107XG5cblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjbGFzc0xpa2UubWVtYmVycykge1xuXHRcdFx0aWYgKCF0cy5pc0NvbnN0cnVjdG9yRGVjbGFyYXRpb24obWVtYmVyKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblxuXHRcdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBtZW1iZXIucGFyYW1ldGVycykge1xuXHRcdFx0XHRpZiAoIXBhcmFtLm5hbWUgfHwgIXRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSkgY29udGludWU7XG5cdFx0XHRcdGlmICghcGFyYW0udHlwZSkgY29udGludWU7XG5cblx0XHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gcGFyYW0ubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBleHBhbmRlZFR5cGUgPSB0aGlzLnJlc29sdmVDb25zdHJ1Y3RvclBhcmFtVHlwZShwYXJhbS50eXBlKSB8fCB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblxuXHRcdFx0XHRwYXJhbXMucHVzaCh7XG5cdFx0XHRcdFx0bmFtZSAgICAgOiBwYXJhbU5hbWUsXG5cdFx0XHRcdFx0dHlwZSAgICAgOiBleHBhbmRlZFR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiAhIXBhcmFtLnF1ZXN0aW9uVG9rZW4gfHwgISFwYXJhbS5pbml0aWFsaXplclxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHRcdGJyZWFrOyAvLyBPbmx5IHByb2Nlc3MgZmlyc3QgY29uc3RydWN0b3Jcblx0XHR9XG5cblx0XHRyZXR1cm4gcGFyYW1zO1xuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBkZWZpbmUoKSBjYWxsXG5cdFx0XHQgKiBUaGlzIGlzIHVzZWQgZm9yIFR5cGVSZWdpc3RyeSBjb25zdHJ1Y3RvciBzaWduYXR1cmVzXG5cdFx0XHQgKiBQcmVzZXJ2ZXMgcGFyYW1ldGVyIG5hbWVzIGFuZCBleHBhbmRzIG9iamVjdCB0eXBlcyB0byB0aGVpciBzdHJ1Y3R1cmVcblx0XHRcdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdIHtcblx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCk7XG5cdFx0aWYgKCFjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdHJldHVybiBbXTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JQYXJhbXNGcm9tQ29uc3RydWN0b3IoY29uc3RydWN0b3JFeHByKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBhIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24uXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JQYXJhbXNGcm9tQ29uc3RydWN0b3IgKGNvbnN0cnVjdG9yRXhwcjogdHMuRXhwcmVzc2lvbik6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10ge1xuXHRcdGNvbnN0IHBhcmFtczogQ29uc3RydWN0b3JQYXJhbUluZm9bXSA9IFtdO1xuXHRcblx0XHQvLyBIYW5kbGUgZnVuY3Rpb24gZXhwcmVzc2lvbiBvciBhcnJvdyBmdW5jdGlvblxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzQXJyb3dGdW5jdGlvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHQvLyBMb29rIGZvciBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIChzZWNvbmQgcGFyYW0gYWZ0ZXIgYHRoaXNgKVxuXHRcdFx0Ly8gUGF0dGVybnM6IGZ1bmN0aW9uKHRoaXM6IFR5cGUsIGRhdGE6IHsgLi4uIH0pIG9yICh0aGlzOiBUeXBlLCBkYXRhOiB7IC4uLiB9KSA9PlxuXHRcdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBjb25zdHJ1Y3RvckV4cHIucGFyYW1ldGVycy5sZW5ndGg7IGkrKykge1xuXHRcdFx0XHRjb25zdCBwYXJhbSA9IGNvbnN0cnVjdG9yRXhwci5wYXJhbWV0ZXJzWyBpIF07XG5cdFx0XHRcdGlmICghcGFyYW0udHlwZSkgY29udGludWU7XG5cdFxuXHRcdFx0XHQvLyBTa2lwIGB0aGlzYCBwYXJhbWV0ZXIgKGZpcnN0IHBhcmFtKVxuXHRcdFx0XHRpZiAoXG5cdFx0XHRcdFx0aSA9PT0gMCAmJlxuXHRcdFx0XHRcdHBhcmFtLm5hbWUua2luZCA9PT0gdHMuU3ludGF4S2luZC5JZGVudGlmaWVyICYmXG5cdFx0XHRcdFx0KHBhcmFtLm5hbWUgYXMgdHMuSWRlbnRpZmllcikudGV4dCA9PT0gJ3RoaXMnXG5cdFx0XHRcdCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFxuXHRcdFx0XHQvLyBHZXQgcGFyYW1ldGVyIG5hbWUgYW5kIGV4cGFuZCBpdHMgdHlwZVxuXHRcdFx0XHRjb25zdCBwYXJhbU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgPyBwYXJhbS5uYW1lLnRleHQgOiAnYXJnJztcblx0XHRcdFx0Y29uc3QgZXhwYW5kZWRUeXBlID0gdGhpcy5yZXNvbHZlQ29uc3RydWN0b3JQYXJhbVR5cGUocGFyYW0udHlwZSkgfHwgdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cdFx0XHRcdFx0XG5cdFx0XHRcdHBhcmFtcy5wdXNoKHtcblx0XHRcdFx0XHRuYW1lICAgICA6IHBhcmFtTmFtZSxcblx0XHRcdFx0XHR0eXBlICAgICA6IGV4cGFuZGVkVHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6ICEhcGFyYW0ucXVlc3Rpb25Ub2tlbiB8fCAhIXBhcmFtLmluaXRpYWxpemVyXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0Ly8gSGFuZGxlIGNsYXNzIGV4cHJlc3Npb24gLSBjaGVjayBjb25zdHJ1Y3RvciBtZXRob2Rcblx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Y29uc3QgY2xhc3NQYXJhbXMgPSB0aGlzLmV4dHJhY3RDbGFzc0NvbnN0cnVjdG9yUGFyYW1zKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGNsYXNzUGFyYW1zKSB7XG5cdFx0XHRcdHBhcmFtcy5wdXNoKHBhcmFtKTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcGFyYW1zO1xuXHR9XG59XG4iXX0=