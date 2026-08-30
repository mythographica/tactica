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
        // Enclosing mnemonica scope for EDS keying: define()/lazy() call node
        // or @decorate()-ed class declaration -> fullPath of the type it owns.
        // Populated on the definitions pass; AST nodes persist across passes,
        // so entries stay valid after resetUsages().
        this.edsScopeByNode = new Map();
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
        // Check for EDS patterns (wrap, current, getFlow, etc.)
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
            this.addEDS(targetType || scope || 'unknown', {
                location,
                kind: 'wrap',
                code,
                targetType: targetType || undefined,
                scope,
            });
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYW5hbHl6ZXIuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvYW5hbHl6ZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFFYiwrQ0FBaUM7QUFNakMsbUNBQXdDO0FBUXhDOztHQUVHO0FBQ0gsTUFBYSxpQkFBaUI7SUF5QjdCLFlBQWEsT0FBb0I7UUF4QnpCLFdBQU0sR0FBbUIsRUFBRSxDQUFDO1FBQzVCLFVBQUssR0FBRyxJQUFJLHFCQUFhLEVBQUUsQ0FBQztRQUM1QixnQkFBVyxHQUFHLElBQUksR0FBRyxFQUEwQixDQUFDO1FBQ2hELFdBQU0sR0FBRyxJQUFJLEdBQUcsRUFBdUIsQ0FBQztRQUN4QyxjQUFTLEdBQUcsSUFBSSxHQUFHLEVBQXFCLENBQUM7UUFDekMsZUFBVSxHQUFHLElBQUksR0FBRyxFQUFzQixDQUFDO1FBQ25ELHNFQUFzRTtRQUN0RSx1RUFBdUU7UUFDdkUsc0VBQXNFO1FBQ3RFLDZDQUE2QztRQUNyQyxtQkFBYyxHQUFHLElBQUksR0FBRyxFQUFtQixDQUFDO1FBQzVDLGdCQUFXLEdBQUcsSUFBSSxHQUFHLEVBQXVCLENBQUM7UUFDckQsNEVBQTRFO1FBQ3BFLHNCQUFpQixHQUFHLElBQUksR0FBRyxFQUFrQixDQUFDO1FBQ3RELDZHQUE2RztRQUNyRywwQkFBcUIsR0FBRyxJQUFJLEdBQUcsRUFBVSxDQUFDO1FBQ2xELGtHQUFrRztRQUMxRixtQ0FBOEIsR0FBRyxJQUFJLEdBQUcsRUFBVSxDQUFDO1FBQzNELGtFQUFrRTtRQUMxRCx3QkFBbUIsR0FBRyxJQUFJLEdBQUcsRUFBa0IsQ0FBQztRQUN4RCxrRUFBa0U7UUFDMUQsbUJBQWMsR0FBRyxJQUFJLEdBQUcsRUFBMEIsQ0FBQztRQUNuRCxzQkFBaUIsR0FBRyxDQUFDLENBQUM7UUFHN0IsNkVBQTZFO1FBQzdFLEtBQUssT0FBTyxDQUFDO0lBQ2QsQ0FBQztJ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QyxNQUFNLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxDQUFDO1lBQ3BCLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0NBQ0Q7QUEzcUdELDhDQTJxR0MiLCJzb3VyY2VzQ29udGVudCI6WyIndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIHRzIGZyb20gJ3R5cGVzY3JpcHQnO1xuaW1wb3J0IHtcblx0VHlwZU5vZGUsIFByb3BlcnR5SW5mbywgQW5hbHl6ZVJlc3VsdCwgQW5hbHl6ZUVycm9yLFxuXHREZWZpbml0aW9uSW5mbywgVXNhZ2VJbmZvLCBDb25zdHJ1Y3RvclBhcmFtSW5mbyxcblx0RURTSW5mbywgRmxvd0luZm9cbn0gZnJvbSAnLi90eXBlcyc7XG5pbXBvcnQgeyBUeXBlR3JhcGhJbXBsIH0gZnJvbSAnLi9ncmFwaCc7XG5cbmludGVyZmFjZSBDb2xsZWN0aW9uSW5mbyB7XG5cdHZhcmlhYmxlTmFtZTogc3RyaW5nO1xuXHRzb3VyY2VGaWxlOiBzdHJpbmc7XG5cdHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZT86IHN0cmluZztcbn1cblxuLyoqXG4gKiBBU1QgQW5hbHl6ZXIgZm9yIGZpbmRpbmcgTW5lbW9uaWNhIGRlZmluZSgpIGFuZCBkZWNvcmF0ZSgpIGNhbGxzXG4gKi9cbmV4cG9ydCBjbGFzcyBNbmVtb25pY2FBbmFseXplciB7XG5cdHByaXZhdGUgZXJyb3JzOiBBbmFseXplRXJyb3JbXSA9IFtdO1xuXHRwcml2YXRlIGdyYXBoID0gbmV3IFR5cGVHcmFwaEltcGwoKTtcblx0cHJpdmF0ZSBkZWZpbml0aW9ucyA9IG5ldyBNYXA8c3RyaW5nLCBEZWZpbml0aW9uSW5mbz4oKTtcblx0cHJpdmF0ZSB1c2FnZXMgPSBuZXcgTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+KCk7XG5cdHByaXZhdGUgZWRzVXNhZ2VzID0gbmV3IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4oKTtcblx0cHJpdmF0ZSBmbG93VXNhZ2VzID0gbmV3IE1hcDxzdHJpbmcsIEZsb3dJbmZvW10+KCk7XG5cdC8vIEVuY2xvc2luZyBtbmVtb25pY2Egc2NvcGUgZm9yIEVEUyBrZXlpbmc6IGRlZmluZSgpL2xhenkoKSBjYWxsIG5vZGVcblx0Ly8gb3IgQGRlY29yYXRlKCktZWQgY2xhc3MgZGVjbGFyYXRpb24gLT4gZnVsbFBhdGggb2YgdGhlIHR5cGUgaXQgb3ducy5cblx0Ly8gUG9wdWxhdGVkIG9uIHRoZSBkZWZpbml0aW9ucyBwYXNzOyBBU1Qgbm9kZXMgcGVyc2lzdCBhY3Jvc3MgcGFzc2VzLFxuXHQvLyBzbyBlbnRyaWVzIHN0YXkgdmFsaWQgYWZ0ZXIgcmVzZXRVc2FnZXMoKS5cblx0cHJpdmF0ZSBlZHNTY29wZUJ5Tm9kZSA9IG5ldyBNYXA8dHMuTm9kZSwgc3RyaW5nPigpO1xuXHRwcml2YXRlIHR5cGVBbGlhc2VzID0gbmV3IE1hcDxzdHJpbmcsIHRzLlR5cGVOb2RlPigpO1xuXHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50czogdmFyaWFibGVOYW1lIC0+IGZ1bGxQYXRoIG9mIHRoZSB0eXBlIGl0IGhvbGRzXG5cdHByaXZhdGUgdmFyaWFibGVUb1R5cGVNYXAgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHQvLyBUcmFjayBtbmVtb25pY2EgbW9kdWxlLW9iamVjdCB2YXJpYWJsZXMgKGUuZy4sIGltcG9ydCB7IG1uZW1vbmljYSB9IGZyb20gJ21uZW1vbmljYSc7IGNvbnN0IG0gPSBtbmVtb25pY2EpXG5cdHByaXZhdGUgbW9kdWxlT2JqZWN0VmFyaWFibGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdC8vIFRyYWNrIGltcG9ydGVkIGFsaWFzZXMgb2YgY3JlYXRlVHlwZXNDb2xsZWN0aW9uIChlLmcuLCBpbXBvcnQgeyBjcmVhdGVUeXBlc0NvbGxlY3Rpb24gYXMgY3RjIH0pXG5cdHByaXZhdGUgY3JlYXRlVHlwZXNDb2xsZWN0aW9uVmFyaWFibGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdC8vIFRyYWNrIGN1c3RvbSBjb2xsZWN0aW9uIHZhcmlhYmxlczogdmFyaWFibGVOYW1lIC0+IGNvbGxlY3Rpb25JZFxuXHRwcml2YXRlIGNvbGxlY3Rpb25WYXJpYWJsZXMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHQvLyBUcmFjayBjdXN0b20gY29sbGVjdGlvbiBtZXRhZGF0YSBmb3IgT3B0aW9uIEIgcmVnaXN0cnkgZW1pc3Npb25cblx0cHJpdmF0ZSBjb2xsZWN0aW9uSW5mbyA9IG5ldyBNYXA8c3RyaW5nLCBDb2xsZWN0aW9uSW5mbz4oKTtcblx0cHJpdmF0ZSBjb2xsZWN0aW9uQ291bnRlciA9IDA7XG5cblx0Y29uc3RydWN0b3IgKHByb2dyYW0/OiB0cy5Qcm9ncmFtKSB7XG5cdFx0Ly8gU3RvcmUgcHJvZ3JhbSBmb3IgZnV0dXJlIHVzZSAoY3VycmVudGx5IHVudXNlZCBidXQga2VwdCBmb3IgZXh0ZW5zaWJpbGl0eSlcblx0XHR2b2lkIHByb2dyYW07XG5cdH1cblxuXHQvKipcblx0ICogUmVzZXQgdXNhZ2UtcmVsYXRlZCBzdGF0ZSBmb3IgYSBmcmVzaCBwYXNzLlxuXHQgKiBDYWxsIGJlZm9yZSB0aGUgdXNhZ2UtY29sbGVjdGlvbiBwYXNzIHRvIGF2b2lkIGR1cGxpY2F0ZXMgZnJvbSBkZWZpbml0aW9uIHBhc3MuXG5cdCAqL1xuXHRyZXNldFVzYWdlcyAoKTogdm9pZCB7XG5cdFx0dGhpcy51c2FnZXMuY2xlYXIoKTtcblx0XHR0aGlzLmVkc1VzYWdlcy5jbGVhcigpO1xuXHRcdHRoaXMuZmxvd1VzYWdlcy5jbGVhcigpO1xuXHRcdHRoaXMudmFyaWFibGVUb1R5cGVNYXAuY2xlYXIoKTtcblx0XHQvLyBOb3RlOiBtb2R1bGVPYmplY3RWYXJpYWJsZXMgYW5kIGNvbGxlY3Rpb25WYXJpYWJsZXMgaW50ZW50aW9uYWxseSBwZXJzaXN0XG5cdFx0Ly8gYWNyb3NzIGRlZmluaXRpb24gYW5kIHVzYWdlIHBhc3Nlcy5cblx0fVxuXG5cdC8qKlxuXHQgKiBBbmFseXplIGEgc291cmNlIGZpbGUgZm9yIE1uZW1vbmljYSB0eXBlIGRlZmluaXRpb25zXG5cdCAqL1xuXHRhbmFseXplRmlsZSAoc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IEFuYWx5emVSZXN1bHQge1xuXHRcdHRoaXMuZXJyb3JzID0gW107XG5cdFx0Ly8gRW5zdXJlIHBhcmVudCBub2RlcyBhcmUgc2V0IGZvciBBU1QgdHJhdmVyc2FsXG5cdFx0dGhpcy5zZXRQYXJlbnROb2Rlc0luU291cmNlRmlsZShzb3VyY2VGaWxlKTtcblx0XHR0aGlzLnZpc2l0Tm9kZShzb3VyY2VGaWxlLCBzb3VyY2VGaWxlKTtcblxuXHRcdHJldHVybiB7XG5cdFx0XHR0eXBlcyAgOiB0aGlzLmdyYXBoLmdldEFsbFR5cGVzKCksXG5cdFx0XHRlcnJvcnMgOiB0aGlzLmVycm9ycyxcblx0XHR9O1xuXHR9XG5cblx0LyoqXG5cdCAqIEFuYWx5emUgc291cmNlIGNvZGUgc3RyaW5nXG5cdCAqL1xuXHRhbmFseXplU291cmNlIChzb3VyY2VDb2RlOiBzdHJpbmcsIGZpbGVOYW1lID0gJ3RlbXAudHMnKTogQW5hbHl6ZVJlc3VsdCB7XG5cdFx0Y29uc3Qgc291cmNlRmlsZSA9IHRzLmNyZWF0ZVNvdXJjZUZpbGUoXG5cdFx0XHRmaWxlTmFtZSxcblx0XHRcdHNvdXJjZUNvZGUsXG5cdFx0XHR0cy5TY3JpcHRUYXJnZXQuTGF0ZXN0LFxuXHRcdFx0dHJ1ZVxuXHRcdCk7XG5cdFx0cmV0dXJuIHRoaXMuYW5hbHl6ZUZpbGUoc291cmNlRmlsZSk7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IHRoZSB0eXBlIGdyYXBoXG5cdCAqL1xuXHRnZXRHcmFwaCAoKTogVHlwZUdyYXBoSW1wbCB7XG5cdFx0cmV0dXJuIHRoaXMuZ3JhcGg7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBkZWZpbml0aW9uc1xuXHQgKi9cblx0Z2V0RGVmaW5pdGlvbnMgKCk6IE1hcDxzdHJpbmcsIERlZmluaXRpb25JbmZvPiB7XG5cdFx0cmV0dXJuIHRoaXMuZGVmaW5pdGlvbnM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCB1c2FnZXNcblx0ICovXG5cdGdldFVzYWdlcyAoKTogTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+IHtcblx0XHRyZXR1cm4gdGhpcy51c2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBFRFMgdXNhZ2VzXG5cdCAqL1xuXHRnZXRFRFNVc2FnZXMgKCk6IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4ge1xuXHRcdHJldHVybiB0aGlzLmVkc1VzYWdlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGZsb3cgdXNhZ2VzXG5cdCAqL1xuXHRnZXRGbG93VXNhZ2VzICgpOiBNYXA8c3RyaW5nLCBGbG93SW5mb1tdPiB7XG5cdFx0cmV0dXJuIHRoaXMuZmxvd1VzYWdlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBBZGQgYSB0b3BvbG9naWNhIHR5cGUgdG8gdGhlIGFuYWx5emVyIGZvciB1c2FnZSB0cmFja2luZy5cblx0ICogVGhpcyBhbGxvd3MgdGhlIGFuYWx5emVyIHRvIHJlY29nbml6ZSB0b3BvbG9naWNhIHR5cGVzIHdoZW4gY29sbGVjdGluZyB1c2FnZXMuXG5cdCAqL1xuXHRhZGRUb3BvbG9naWNhVHlwZSAoZnVsbFBhdGg6IHN0cmluZywgbm9kZTogaW1wb3J0KCcuL3R5cGVzJykuVHlwZU5vZGUpOiB2b2lkIHtcblx0XHQvLyBTa2lwIGlmIGFscmVhZHkgZXhpc3RzXG5cdFx0aWYgKHRoaXMuZ3JhcGguYWxsVHlwZXMuaGFzKGZ1bGxQYXRoKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEFkZCB0byBncmFwaCBzbyBpdCBjYW4gYmUgZm91bmQgZHVyaW5nIHVzYWdlIGNvbGxlY3Rpb25cblx0XHRpZiAobm9kZS5wYXJlbnQpIHtcblx0XHRcdC8vIEFkZCBhcyBjaGlsZCBvZiBwYXJlbnRcblx0XHRcdHRoaXMuZ3JhcGguYWRkQ2hpbGQobm9kZS5wYXJlbnQsIG5vZGUpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHQvLyBBZGQgYXMgcm9vdFxuXHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KG5vZGUpO1xuXHRcdH1cblxuXHRcdC8vIEFsc28gYWRkIHRvIGRlZmluaXRpb25zIHNvIGl0J3MgcmVjb2duaXplZCBhcyBhIGtub3duIHR5cGVcblx0XHRjb25zdCBkZWZpbml0aW9uOiBEZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogbm9kZS5uYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHtub2RlLnNvdXJjZUZpbGV9OiR7bm9kZS5saW5lfToke25vZGUuY29sdW1ufWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiBub2RlLnBhcmVudCA/IG5vZGUucGFyZW50LmZ1bGxQYXRoIDogbnVsbCxcblx0XHRcdHN0cmljdENoYWluIDogdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogZmFsc2Vcblx0XHR9O1xuXHRcdHRoaXMuZGVmaW5pdGlvbnMuc2V0KGZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBTZXQgcGFyZW50IG5vZGVzIGluIGEgc291cmNlIGZpbGUgdG8gZW5hYmxlIEFTVCB0cmF2ZXJzYWwgdXBcblx0ICovXG5cdHByaXZhdGUgc2V0UGFyZW50Tm9kZXNJblNvdXJjZUZpbGUgKHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCBzZXRQYXJlbnQgPSAobm9kZTogdHMuTm9kZSwgcGFyZW50PzogdHMuTm9kZSkgPT4ge1xuXHRcdFx0Ly8gVHlwZVNjcmlwdCBkb2Vzbid0IGV4cG9zZSBwYXJlbnQgYXMgd3JpdGFibGUsIGJ1dCB3ZSBuZWVkIGl0XG5cdFx0XHQvLyBlc2xpbnQtZGlzYWJsZS1uZXh0LWxpbmUgQHR5cGVzY3JpcHQtZXNsaW50L25vLWV4cGxpY2l0LWFueVxuXHRcdFx0KG5vZGUgYXMgYW55KS5wYXJlbnQgPSBwYXJlbnQ7XG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgY2hpbGQgPT4gc2V0UGFyZW50KGNoaWxkLCBub2RlKSk7XG5cdFx0fTtcblx0XHRzZXRQYXJlbnQoc291cmNlRmlsZSk7XG5cdH1cblxuXHQvKipcblx0ICogVmlzaXQgYSBub2RlIGluIHRoZSBBU1Rcblx0ICovXG5cdHByaXZhdGUgdmlzaXROb2RlIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLCBjdXJyZW50Q2xhc3M/OiB0cy5DbGFzc0RlY2xhcmF0aW9uKTogdm9pZCB7XG5cdFx0Ly8gVHJhY2sgbW5lbW9uaWNhIG1vZHVsZS1vYmplY3QgYWxpYXNlcyBhbmQgY3VzdG9tIGNvbGxlY3Rpb24gdmFyaWFibGVzXG5cdFx0Ly8gYmVmb3JlIHByb2Nlc3NpbmcgZGVmaW5lKCkvbG9va3VwKCkgY2FsbHMgc28gc291cmNlIHJlc29sdXRpb24gd29ya3MuXG5cdFx0dGhpcy50cmFja0ltcG9ydHMobm9kZSk7XG5cdFx0dGhpcy50cmFja01vZHVsZU9iamVjdEFsaWFzZXMobm9kZSk7XG5cdFx0dGhpcy50cmFja0NvbGxlY3Rpb25BbGlhc2VzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIGRlZmluZSgpIGNhbGxzXG5cdFx0aWYgKHRoaXMuaXNEZWZpbmVDYWxsKG5vZGUpKSB7XG5cdFx0XHR0aGlzLnByb2Nlc3NEZWZpbmVDYWxsKG5vZGUgYXMgdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGUpO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBsYXp5KCkgY2FsbHNcblx0XHRpZiAodGhpcy5pc0xhenlDYWxsKG5vZGUpKSB7XG5cdFx0XHR0aGlzLnByb2Nlc3NMYXp5Q2FsbChub2RlIGFzIHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgZGVjb3JhdGUoKSBkZWNvcmF0b3Jcblx0XHRpZiAodGhpcy5pc0RlY29yYXRlRGVjb3JhdG9yKG5vZGUpKSB7XG5cdFx0XHR0aGlzLnByb2Nlc3NEZWNvcmF0ZURlY29yYXRvcihub2RlIGFzIHRzLkRlY29yYXRvciwgc291cmNlRmlsZSwgY3VycmVudENsYXNzKTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgdHlwZSB1c2FnZXMgKG5ldyBUeXBlKCksIHR5cGUgYW5ub3RhdGlvbnMsIGV0Yy4pXG5cdFx0dGhpcy5jb2xsZWN0VXNhZ2Uobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgRURTIHBhdHRlcm5zICh3cmFwLCBjdXJyZW50LCBnZXRGbG93LCBldGMuKVxuXHRcdHRoaXMuY29sbGVjdEVEUyhub2RlLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIENoZWNrIGZvciBuYXRpdmUgZmxvdyBwYXR0ZXJucyAocHJvcGVydHkgYWNjZXNzLCBtZXRob2QgY2FsbHMsIGV0Yy4pXG5cdFx0dGhpcy5jb2xsZWN0Rmxvdyhub2RlLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIENvbGxlY3QgdHlwZSBhbGlhc2VzIGZvciByZXNvbHZpbmcgdHlwZSByZWZlcmVuY2VzXG5cdFx0aWYgKHRzLmlzVHlwZUFsaWFzRGVjbGFyYXRpb24obm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdHRoaXMudHlwZUFsaWFzZXMuc2V0KG5vZGUubmFtZS50ZXh0LCBub2RlLnR5cGUpO1xuXHRcdH1cblxuXHRcdC8vIFRyYWNrIGNsYXNzIGRlY2xhcmF0aW9ucyBmb3IgZGVjb3JhdG9yIHBhcmVudCBsb29rdXBcblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHQvLyBWaXNpdCBjaGlsZHJlbiB3aXRoIHRoaXMgY2xhc3MgYXMgdGhlIGN1cnJlbnQgY29udGV4dFxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHRoaXMudmlzaXROb2RlKGNoaWxkLCBzb3VyY2VGaWxlLCBub2RlKSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdC8vIFJlY3Vyc2l2ZWx5IHZpc2l0IGNoaWxkcmVuXG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgY2hpbGQgPT4gdGhpcy52aXNpdE5vZGUoY2hpbGQsIHNvdXJjZUZpbGUsIGN1cnJlbnRDbGFzcykpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBUcmFjayBpbXBvcnRzIGZyb20gJ21uZW1vbmljYScgc28gYWxpYXNlcyBvZiB0aGUgbW9kdWxlIG9iamVjdCBhbmRcblx0ICogY3JlYXRlVHlwZXNDb2xsZWN0aW9uIGFyZSByZWNvZ25pemVkIHdpdGhvdXQgcmVseWluZyBvbiB0aGUgdHlwZSBjaGVja2VyLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja0ltcG9ydHMgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzSW1wb3J0RGVjbGFyYXRpb24obm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IG1vZHVsZVNwZWNpZmllciB9ID0gbm9kZTtcblx0XHRpZiAoIXRzLmlzU3RyaW5nTGl0ZXJhbChtb2R1bGVTcGVjaWZpZXIpIHx8IG1vZHVsZVNwZWNpZmllci50ZXh0ICE9PSAnbW5lbW9uaWNhJykge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IGNsYXVzZSA9IG5vZGUuaW1wb3J0Q2xhdXNlO1xuXHRcdGlmICghY2xhdXNlKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0IHsgbW5lbW9uaWNhLCBjcmVhdGVUeXBlc0NvbGxlY3Rpb24gfSBmcm9tICdtbmVtb25pY2EnXG5cdFx0aWYgKGNsYXVzZS5uYW1lZEJpbmRpbmdzICYmIHRzLmlzTmFtZWRJbXBvcnRzKGNsYXVzZS5uYW1lZEJpbmRpbmdzKSkge1xuXHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGNsYXVzZS5uYW1lZEJpbmRpbmdzLmVsZW1lbnRzKSB7XG5cdFx0XHRcdGNvbnN0IGxvY2FsTmFtZSA9IGVsZW1lbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBpbXBvcnRlZE5hbWUgPSBlbGVtZW50LnByb3BlcnR5TmFtZVxuXHRcdFx0XHRcdD8gZWxlbWVudC5wcm9wZXJ0eU5hbWUudGV4dFxuXHRcdFx0XHRcdDogbG9jYWxOYW1lO1xuXHRcdFx0XHRpZiAoaW1wb3J0ZWROYW1lID09PSAnbW5lbW9uaWNhJykge1xuXHRcdFx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChsb2NhbE5hbWUpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChpbXBvcnRlZE5hbWUgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nKSB7XG5cdFx0XHRcdFx0dGhpcy5jcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMuYWRkKGxvY2FsTmFtZSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgKiBhcyBtbmVtb25pY2EgZnJvbSAnbW5lbW9uaWNhJ1xuXHRcdGlmIChjbGF1c2UubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVzcGFjZUltcG9ydChjbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChjbGF1c2UubmFtZWRCaW5kaW5ncy5uYW1lLnRleHQpO1xuXHRcdH1cblxuXHRcdC8vIGltcG9ydCBtbmVtb25pY2EgZnJvbSAnbW5lbW9uaWNhJyAoZGVmYXVsdCBpbXBvcnQpIOKAlCB0cmVhdCBhcyBtb2R1bGUgb2JqZWN0IHRvb1xuXHRcdGlmIChjbGF1c2UubmFtZSkge1xuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuYWRkKGNsYXVzZS5uYW1lLnRleHQpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBUcmFjayBhbGlhc2VzIG9mIHRoZSBtbmVtb25pY2EgbW9kdWxlIG9iamVjdCwgZS5nLjpcblx0ICogICBjb25zdCBtID0gbW5lbW9uaWNhO1xuXHQgKiAgIGNvbnN0IEFwcCA9IG07XG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrTW9kdWxlT2JqZWN0QWxpYXNlcyAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpIHx8ICF0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgaW5pdGlhbGl6ZXIgfSA9IG5vZGU7XG5cdFx0aWYgKCFpbml0aWFsaXplcikge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoaW5pdGlhbGl6ZXIpICYmIHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhpbml0aWFsaXplci50ZXh0KSkge1xuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuYWRkKG5vZGUubmFtZS50ZXh0KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgY3VzdG9tIGNvbGxlY3Rpb24gdmFyaWFibGVzLCBlLmcuOlxuXHQgKiAgIGNvbnN0IE15Q29sbGVjdGlvbiA9IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpO1xuXHQgKiAgIGNvbnN0IE90aGVyID0gTXlDb2xsZWN0aW9uO1xuXHQgKlxuXHQgKiBBbHNvIGRldGVjdHMgT3B0aW9uIEIgdXNlci1wcm92aWRlZCByZWdpc3RyeSBpbnRlcmZhY2VzOlxuXHQgKiAgIGV4cG9ydCBpbnRlcmZhY2UgTXlDb2xsZWN0aW9uUmVnaXN0cnkge31cblx0ICogICBjb25zdCBNeUNvbGxlY3Rpb24gPSBjcmVhdGVUeXBlc0NvbGxlY3Rpb248TXlDb2xsZWN0aW9uUmVnaXN0cnk+KCk7XG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrQ29sbGVjdGlvbkFsaWFzZXMgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSB8fCAhdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGluaXRpYWxpemVyIH0gPSBub2RlO1xuXHRcdGlmICghaW5pdGlhbGl6ZXIpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBEaXJlY3QgY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgY2FsbFxuXHRcdGlmICh0aGlzLmlzQ3JlYXRlVHlwZXNDb2xsZWN0aW9uQ2FsbChpbml0aWFsaXplcikpIHtcblx0XHRcdGNvbnN0IGNvbGxlY3Rpb25JZCA9IHRoaXMubmV4dENvbGxlY3Rpb25JZCgpO1xuXHRcdFx0dGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLnNldChub2RlLm5hbWUudGV4dCwgY29sbGVjdGlvbklkKTtcblxuXHRcdFx0Y29uc3QgcmVnaXN0cnlJbnRlcmZhY2VOYW1lID0gdGhpcy5leHRyYWN0UmVnaXN0cnlJbnRlcmZhY2VOYW1lKFxuXHRcdFx0XHRpbml0aWFsaXplciBhcyB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHRcdFx0c291cmNlRmlsZVxuXHRcdFx0KTtcblx0XHRcdHRoaXMuY29sbGVjdGlvbkluZm8uc2V0KGNvbGxlY3Rpb25JZCwge1xuXHRcdFx0XHR2YXJpYWJsZU5hbWUgICAgICAgICAgOiBub2RlLm5hbWUudGV4dCxcblx0XHRcdFx0c291cmNlRmlsZSAgICAgICAgICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0cmVnaXN0cnlJbnRlcmZhY2VOYW1lIDogcmVnaXN0cnlJbnRlcmZhY2VOYW1lXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBBbGlhcyBvZiBhbm90aGVyIGNvbGxlY3Rpb24gdmFyaWFibGVcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGluaXRpYWxpemVyKSkge1xuXHRcdFx0Y29uc3QgZXhpc3RpbmcgPSB0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuZ2V0KGluaXRpYWxpemVyLnRleHQpO1xuXHRcdFx0aWYgKGV4aXN0aW5nKSB7XG5cdFx0XHRcdHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5zZXQobm9kZS5uYW1lLnRleHQsIGV4aXN0aW5nKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0aGUgcmVnaXN0cnkgaW50ZXJmYWNlIG5hbWUgZnJvbSBjcmVhdGVUeXBlc0NvbGxlY3Rpb248UmVnaXN0cnk+KClcblx0ICogd2hlbiB0aGUgaW50ZXJmYWNlIGlzIGRlY2xhcmVkIGluIHRoZSBzYW1lIHNvdXJjZSBmaWxlLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UmVnaXN0cnlJbnRlcmZhY2VOYW1lIChcblx0XHRjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlXG5cdCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgdHlwZUFyZ3MgPSBjYWxsLnR5cGVBcmd1bWVudHM7XG5cdFx0aWYgKCF0eXBlQXJncyB8fCB0eXBlQXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmlyc3RUeXBlQXJnID0gdHlwZUFyZ3NbIDAgXTtcblx0XHRpZiAoIXRzLmlzVHlwZVJlZmVyZW5jZU5vZGUoZmlyc3RUeXBlQXJnKSB8fCAhdHMuaXNJZGVudGlmaWVyKGZpcnN0VHlwZUFyZy50eXBlTmFtZSkpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgbmFtZSA9IGZpcnN0VHlwZUFyZy50eXBlTmFtZS50ZXh0O1xuXG5cdFx0Ly8gQ29uZmlybSB0aGUgaW50ZXJmYWNlIGV4aXN0cyBpbiB0aGUgc2FtZSBzb3VyY2UgZmlsZS5cblx0XHRmb3IgKGNvbnN0IHN0YXRlbWVudCBvZiBzb3VyY2VGaWxlLnN0YXRlbWVudHMpIHtcblx0XHRcdGlmIChcblx0XHRcdFx0dHMuaXNJbnRlcmZhY2VEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmXG5cdFx0XHRcdHN0YXRlbWVudC5uYW1lLnRleHQgPT09IG5hbWVcblx0XHRcdCkge1xuXHRcdFx0XHRyZXR1cm4gbmFtZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCB0aGUgcmVnaXN0cnkgaW50ZXJmYWNlIG5hbWUgZm9yIGEgY29sbGVjdGlvbiBpZC5cblx0ICovXG5cdHByaXZhdGUgZ2V0UmVnaXN0cnlJbnRlcmZhY2VOYW1lIChjb2xsZWN0aW9uSWQ/OiBzdHJpbmcpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghY29sbGVjdGlvbklkKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRyZXR1cm4gdGhpcy5jb2xsZWN0aW9uSW5mby5nZXQoY29sbGVjdGlvbklkKT8ucmVnaXN0cnlJbnRlcmZhY2VOYW1lO1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGFuIGV4cHJlc3Npb24gaXMgYSBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSBjYWxsLlxuXHQgKiBIYW5kbGVzOlxuXHQgKiAgIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpXG5cdCAqICAgY3RjKCkgLy8gYWxpYXNlZCBpbXBvcnRcblx0ICogICBtbmVtb25pY2EuY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgLy8gbW9kdWxlIG9iamVjdCBtZXRob2Rcblx0ICogICBtLmNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIC8vIGFsaWFzZWQgbW9kdWxlIG9iamVjdFxuXHQgKi9cblx0cHJpdmF0ZSBpc0NyZWF0ZVR5cGVzQ29sbGVjdGlvbkNhbGwgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkNhbGxFeHByZXNzaW9uIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Y29uc3QgZXhwciA9IG5vZGUuZXhwcmVzc2lvbjtcblxuXHRcdC8vIERpcmVjdCBjYWxsIG9yIGFsaWFzZWQgaW1wb3J0OiBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSAvIGN0YygpXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIGV4cHIudGV4dCA9PT0gJ2NyZWF0ZVR5cGVzQ29sbGVjdGlvbicgfHxcblx0XHRcdFx0dGhpcy5jcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGV4cHIudGV4dCk7XG5cdFx0fVxuXG5cdFx0Ly8gTW9kdWxlIG9iamVjdCBtZXRob2Q6IG1uZW1vbmljYS5jcmVhdGVUeXBlc0NvbGxlY3Rpb24oKVxuXHRcdGlmIChcblx0XHRcdHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpICYmXG5cdFx0XHRleHByLm5hbWUudGV4dCA9PT0gJ2NyZWF0ZVR5cGVzQ29sbGVjdGlvbicgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcihleHByLmV4cHJlc3Npb24pICYmXG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoZXhwci5leHByZXNzaW9uLnRleHQpXG5cdFx0KSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogR2VuZXJhdGUgYSB1bmlxdWUgY29sbGVjdGlvbiBpZGVudGlmaWVyLlxuXHQgKi9cblx0cHJpdmF0ZSBuZXh0Q29sbGVjdGlvbklkICgpOiBzdHJpbmcge1xuXHRcdHRoaXMuY29sbGVjdGlvbkNvdW50ZXIrKztcblx0XHRjb25zdCByZXN1bHQgPSBgY29sbGVjdGlvbl8ke3RoaXMuY29sbGVjdGlvbkNvdW50ZXJ9YDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGEgbm9kZSBpcyBhIGRlZmluZSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgaXNEZWZpbmVDYWxsIChub2RlOiB0cy5Ob2RlKTogbm9kZSBpcyB0cy5DYWxsRXhwcmVzc2lvbiB7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIGRpcmVjdCBjYWxsOiBkZWZpbmUoJ1R5cGVOYW1lJywgLi4uKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIG1ldGhvZCBjYWxsOiBTb21lVHlwZS5kZWZpbmUoJ1N1YlR5cGUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gZXhwcmVzc2lvbi5uYW1lPy50ZXh0ID09PSAnZGVmaW5lJztcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogQ2hlY2sgaWYgYSBub2RlIGlzIGEgbGF6eSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgaXNMYXp5Q2FsbCAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuQ2FsbEV4cHJlc3Npb24ge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBkaXJlY3QgY2FsbDogbGF6eSgnVHlwZU5hbWUnLCBnZXR0ZXIsIC4uLilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2xhenknKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgbWV0aG9kIGNhbGw6IFNvbWVUeXBlLmxhenkoJ1N1YlR5cGUnLCBnZXR0ZXIsIC4uLilcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcmVzc2lvbikpIHtcblx0XHRcdHJldHVybiBleHByZXNzaW9uLm5hbWU/LnRleHQgPT09ICdsYXp5Jztcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0XHQqIEV4dHJhY3QgY29uZmlnIG9wdGlvbnMgZnJvbSBhbiBvYmplY3QgbGl0ZXJhbFxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsIChjb25maWdBcmc6IHRzLk9iamVjdExpdGVyYWxFeHByZXNzaW9uKTpcblx0XHR7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0ge1xuXHRcdGNvbnN0IGNvbmZpZzogeyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9ID0ge307XG5cblx0XHRmb3IgKGNvbnN0IHByb3Agb2YgY29uZmlnQXJnLnByb3BlcnRpZXMpIHtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSAmJiB0cy5pc0lkZW50aWZpZXIocHJvcC5uYW1lKSkge1xuXHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IHByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRpZiAocHJvcE5hbWUgPT09ICdzdHJpY3RDaGFpbicgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLnN0cmljdENoYWluID0gdHJ1ZTtcblx0XHRcdFx0fSBlbHNlIGlmIChwcm9wTmFtZSA9PT0gJ3N0cmljdENoYWluJyAmJiBwcm9wLmluaXRpYWxpemVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLnN0cmljdENoYWluID0gZmFsc2U7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdibG9ja0Vycm9ycycgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLmJsb2NrRXJyb3JzID0gdHJ1ZTtcblx0XHRcdFx0fSBlbHNlIGlmIChwcm9wTmFtZSA9PT0gJ2Jsb2NrRXJyb3JzJyAmJiBwcm9wLmluaXRpYWxpemVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLmJsb2NrRXJyb3JzID0gZmFsc2U7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gY29uZmlnO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IGNvbmZpZyBvcHRpb25zIGZyb20gZGVmaW5lKCkgY2FsbFxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdENvbmZpZyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0ge1xuXHRcdC8vIENvbmZpZyBpcyB0aGUgdGhpcmQgYXJndW1lbnQ6IGRlZmluZSgnTmFtZScsIGhhbmRsZXIsIGNvbmZpZylcblx0XHRjb25zdCBjb25maWdBcmcgPSBjYWxsLmFyZ3VtZW50c1sgMiBdO1xuXHRcdGlmICghY29uZmlnQXJnIHx8ICF0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGNvbmZpZ0FyZykpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRjb25zdCBjb25maWdSZXN1bHQgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjb25maWdBcmcpO1xuXHRcdHJldHVybiBjb25maWdSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHQqIENoZWNrIGlmIGEgbm9kZSBpcyBhIEBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHRcdCovXG5cdHByaXZhdGUgaXNEZWNvcmF0ZURlY29yYXRvciAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuRGVjb3JhdG9yIHtcblx0XHRpZiAoIXRzLmlzRGVjb3JhdG9yKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIEBkZWNvcmF0ZVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVjb3JhdGUnKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgQGRlY29yYXRlKCkgb3IgQGRlY29yYXRlKFBhcmVudFR5cGUpXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZXhwcmVzc2lvbikpIHtcblx0XHRcdGNvbnN0IGZuTmFtZSA9IGV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZm5OYW1lKSAmJiBmbk5hbWUudGV4dCA9PT0gJ2RlY29yYXRlJykge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gQ2hlY2sgZm9yIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSB3aGVyZSBNeUNvbGxlY3Rpb24gaXMgYSBjdXN0b20gY29sbGVjdGlvblxuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihmbk5hbWUpICYmXG5cdFx0XHRcdGZuTmFtZS5uYW1lLnRleHQgPT09ICdkZWNvcmF0ZScgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGZuTmFtZS5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGZuTmFtZS5leHByZXNzaW9uLnRleHQpXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIE1hcmsgYSBjYWxsIGV4cHJlc3Npb24gYXMgcHJvY2Vzc2VkIGFuZCByZXR1cm4gd2hldGhlciBpdCBhbHJlYWR5IHdhcy5cblx0ICovXG5cdHByaXZhdGUgbWFya1Byb2Nlc3NlZCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBib29sZWFuIHtcblx0XHRjb25zdCBtYXJrZWQgPSBjYWxsIGFzIHVua25vd24gYXMgeyBfX3RhY3RpY2FfcHJvY2Vzc2VkPzogYm9vbGVhbiB9O1xuXHRcdGlmIChtYXJrZWQuX190YWN0aWNhX3Byb2Nlc3NlZCkge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXHRcdG1hcmtlZC5fX3RhY3RpY2FfcHJvY2Vzc2VkID0gdHJ1ZTtcblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogUHJvY2VzcyBhIGRlZmluZSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgcHJvY2Vzc0RlZmluZUNhbGwgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBleGFjdCBjYWxsIGhhcyBhbHJlYWR5IGJlZW4gcHJvY2Vzc2VkIChwcmV2ZW50cyBkdXBsaWNhdGVzIGZyb20gY2hhaW5lZCBjYWxscylcblx0XHRpZiAodGhpcy5tYXJrUHJvY2Vzc2VkKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gR2V0IHRoZSB0eXBlIG5hbWUgYW5kIHNvdXJjZSBjb250ZXh0IGZyb20gYXJndW1lbnRzXG5cdFx0Y29uc3QgZGVmaW5lQ29udGV4dCA9IHRoaXMuZXh0cmFjdERlZmluZUNvbnRleHQoY2FsbCk7XG5cblx0XHQvLyBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGRlZmluZSgnQScpLmRlZmluZSgnQicpLCB3ZSB3YW50IHRoZSBwb3NpdGlvbiBvZiB0aGUgLmRlZmluZSgnQicpIHBhcnRcblx0XHQvLyBub3QgdGhlIHN0YXJ0IG9mIHRoZSBlbnRpcmUgZXhwcmVzc2lvblxuXHRcdGxldCBwb3NpdGlvbk5vZGU6IHRzLk5vZGUgPSBjYWxsO1xuXG5cdFx0Ly8gSWYgdGhpcyBpcyBhIGNoYWluZWQgY2FsbCwgZ2V0IHRoZSBwb3NpdGlvbiBvZiB0aGUgcHJvcGVydHkgYWNjZXNzIGV4cHJlc3Npb25cblx0XHQvLyB3aGljaCBpcyB0aGUgLmRlZmluZSBwYXJ0XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdC8vIFRoZSBleHByZXNzaW9uIGlzIHRoZSBwcm9wZXJ0eSBhY2Nlc3M6IChkZWZpbmUoJ1Jvb3RBc3luYycsIC4uLikpLmRlZmluZVxuXHRcdFx0Ly8gV2Ugd2FudCB0aGUgcG9zaXRpb24gb2YganVzdCB0aGUgLmRlZmluZSBwYXJ0XG5cdFx0XHRwb3NpdGlvbk5vZGUgPSBjYWxsLmV4cHJlc3Npb24ubmFtZTsgLy8gVGhpcyBpcyB0aGUgJ2RlZmluZScgaWRlbnRpZmllclxuXHRcdH1cblxuXHRcdGNvbnN0IHN0YXJ0UG9zID0gcG9zaXRpb25Ob2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpO1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihzb3VyY2VGaWxlLCBzdGFydFBvcyk7XG5cblx0XHRpZiAoIWRlZmluZUNvbnRleHQudHlwZU5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0NvdWxkIG5vdCBleHRyYWN0IHR5cGUgbmFtZSBmcm9tIGRlZmluZSgpIGNhbGwnLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgdHlwZU5hbWUgfSA9IGRlZmluZUNvbnRleHQ7XG5cblx0XHQvLyBEZXRlcm1pbmUgcGFyZW50IHR5cGUgYW5kIGNvbGxlY3Rpb24gYmFzZWQgb24gdGhlIGNhbGwgc291cmNlLlxuXHRcdGNvbnN0IHBhcmVudE5vZGUgPSBkZWZpbmVDb250ZXh0LnBhcmVudFR5cGU7XG5cdFx0Y29uc3QgeyBjb2xsZWN0aW9uSWQgfSA9IGRlZmluZUNvbnRleHQ7XG5cblx0XHQvLyBFeHRyYWN0IGNvbmZpZyBvcHRpb25zXG5cdFx0Y29uc3QgY29uZmlnID0gdGhpcy5leHRyYWN0Q29uZmlnKGNhbGwpO1xuXG5cdFx0Ly8gQ3JlYXRlIHR5cGUgbm9kZSBmaXJzdCBzbyBpdHMgaW50ZXJuYWwgZnVsbFBhdGggKGluY2x1ZGluZyBhbnkgY29sbGVjdGlvbiBwcmVmaXgpIGlzIHJlc29sdmVkLlxuXHRcdGNvbnN0IG5vZGUgPSBUeXBlR3JhcGhJbXBsLmNyZWF0ZU5vZGUoXG5cdFx0XHR0eXBlTmFtZSxcblx0XHRcdHBhcmVudE5vZGUsXG5cdFx0XHRzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0bGluZSArIDEsXG5cdFx0XHRjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0Y29sbGVjdGlvbklkXG5cdFx0KTtcblx0XHRub2RlLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA9IHRoaXMuZ2V0UmVnaXN0cnlJbnRlcmZhY2VOYW1lKGNvbGxlY3Rpb25JZCk7XG5cblx0XHQvLyBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBjb25zdHJ1Y3RvciBmdW5jdGlvblxuXHRcdG5vZGUucHJvcGVydGllcyA9IHRoaXMuZXh0cmFjdFByb3BlcnRpZXMoY2FsbCk7XG5cblx0XHQvLyBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZm9yIFR5cGVSZWdpc3RyeSBzaWduYXR1cmVcblx0XHRub2RlLmNvbnN0cnVjdG9yUGFyYW1zID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JQYXJhbXMoY2FsbCk7XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGhcblx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChwYXJlbnROb2RlLCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KG5vZGUpO1xuXHRcdH1cblxuXHRcdC8vIENyZWF0ZSBkZWZpbml0aW9uIGluZm8gdXNpbmcgdGhlIG5vZGUncyByZXNvbHZlZCBmdWxsUGF0aFxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiBwYXJlbnROb2RlID8gcGFyZW50Tm9kZS5mdWxsUGF0aCA6IG51bGwsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IGNvbmZpZy5zdHJpY3RDaGFpbiA/PyB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBjb25maWcuYmxvY2tFcnJvcnMgPz8gZmFsc2UsXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChub2RlLmZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0XHR0aGlzLmVkc1Njb3BlQnlOb2RlLnNldChjYWxsLCBub2RlLmZ1bGxQYXRoKTtcblxuXHRcdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnQ6IGNvbnN0IFVzZXIgPSBkZWZpbmUoJ1VzZXJFbnRpdHknLCAuLi4pIC0+IG1hcCBcIlVzZXJcIiB0byBcIlVzZXJFbnRpdHlcIlxuXHRcdC8vIEZvciBjaGFpbmVkIGNhbGxzIGxpa2UgY29uc3QgWCA9IGRlZmluZSgnQScpLmRlZmluZSgnQicpLCB3ZSB3YW50IHRvIG1hcCBYIC0+IEEgKHRoZSByb290KVxuXHRcdHRoaXMudHJhY2tWYXJpYWJsZUFzc2lnbm1lbnQoY2FsbCwgcGFyZW50Tm9kZSwgbm9kZS5mdWxsUGF0aCk7XG5cdH1cblxuXHQvKipcblx0ICogUHJvY2VzcyBhIGxhenkoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NMYXp5Q2FsbCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHQvLyBDaGVjayBpZiB0aGlzIGV4YWN0IGNhbGwgaGFzIGFscmVhZHkgYmVlbiBwcm9jZXNzZWQgKHByZXZlbnRzIGR1cGxpY2F0ZXMgZnJvbSBjaGFpbmVkIGNhbGxzKVxuXHRcdGlmICh0aGlzLm1hcmtQcm9jZXNzZWQoY2FsbCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBHZXQgdGhlIHR5cGUgbmFtZSBhbmQgc291cmNlIGNvbnRleHQgZnJvbSBhcmd1bWVudHNcblx0XHRjb25zdCBsYXp5Q29udGV4dCA9IHRoaXMuZXh0cmFjdExhenlDb250ZXh0KGNhbGwsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBkZWZpbmUoJ0EnKS5sYXp5KCdCJyksIHdlIHdhbnQgdGhlIHBvc2l0aW9uIG9mIHRoZSAubGF6eSgnQicpIHBhcnRcblx0XHQvLyBub3QgdGhlIHN0YXJ0IG9mIHRoZSBlbnRpcmUgZXhwcmVzc2lvblxuXHRcdGxldCBwb3NpdGlvbk5vZGU6IHRzLk5vZGUgPSBjYWxsO1xuXG5cdFx0Ly8gSWYgdGhpcyBpcyBhIGNoYWluZWQgY2FsbCwgZ2V0IHRoZSBwb3NpdGlvbiBvZiB0aGUgcHJvcGVydHkgYWNjZXNzIGV4cHJlc3Npb25cblx0XHQvLyB3aGljaCBpcyB0aGUgLmxhenkgcGFydFxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHQvLyBUaGUgZXhwcmVzc2lvbiBpcyB0aGUgcHJvcGVydHkgYWNjZXNzOiAoZGVmaW5lKCdSb290QXN5bmMnLCAuLi4pKS5sYXp5XG5cdFx0XHQvLyBXZSB3YW50IHRoZSBwb3NpdGlvbiBvZiBqdXN0IHRoZSAubGF6eSBwYXJ0XG5cdFx0XHRwb3NpdGlvbk5vZGUgPSBjYWxsLmV4cHJlc3Npb24ubmFtZTsgLy8gVGhpcyBpcyB0aGUgJ2xhenknIGlkZW50aWZpZXJcblx0XHR9XG5cblx0XHRjb25zdCBzdGFydFBvcyA9IHBvc2l0aW9uTm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKTtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oc291cmNlRmlsZSwgc3RhcnRQb3MpO1xuXG5cdFx0aWYgKCFsYXp5Q29udGV4dC50eXBlTmFtZSkge1xuXHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdG1lc3NhZ2UgOiAnQ291bGQgbm90IGV4dHJhY3QgdHlwZSBuYW1lIGZyb20gbGF6eSgpIGNhbGwnLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgdHlwZU5hbWUgfSA9IGxhenlDb250ZXh0O1xuXG5cdFx0Ly8gRGV0ZXJtaW5lIHBhcmVudCB0eXBlIGFuZCBjb2xsZWN0aW9uIGJhc2VkIG9uIHRoZSBjYWxsIHNvdXJjZS5cblx0XHRjb25zdCBwYXJlbnROb2RlID0gbGF6eUNvbnRleHQucGFyZW50VHlwZTtcblx0XHRjb25zdCB7IGNvbGxlY3Rpb25JZCB9ID0gbGF6eUNvbnRleHQ7XG5cblx0XHQvLyBFeHRyYWN0IGNvbmZpZyBvcHRpb25zXG5cdFx0Y29uc3QgY29uZmlnID0gdGhpcy5leHRyYWN0TGF6eUNvbmZpZyhjYWxsKTtcblxuXHRcdC8vIENyZWF0ZSB0eXBlIG5vZGUgZmlyc3Qgc28gaXRzIGludGVybmFsIGZ1bGxQYXRoIChpbmNsdWRpbmcgYW55IGNvbGxlY3Rpb24gcHJlZml4KSBpcyByZXNvbHZlZC5cblx0XHRjb25zdCBub2RlID0gVHlwZUdyYXBoSW1wbC5jcmVhdGVOb2RlKFxuXHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRwYXJlbnROb2RlLFxuXHRcdFx0c291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdGxpbmUgKyAxLFxuXHRcdFx0Y2hhcmFjdGVyICsgMSxcblx0XHRcdGNvbGxlY3Rpb25JZFxuXHRcdCk7XG5cdFx0bm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWUgPSB0aGlzLmdldFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZShjb2xsZWN0aW9uSWQpO1xuXG5cdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gdGhlIGNvbnN0cnVjdG9yIHJldHVybmVkIGJ5IHRoZSBsYXp5IGdldHRlclxuXHRcdG5vZGUucHJvcGVydGllcyA9IHRoaXMuZXh0cmFjdFByb3BlcnRpZXMoY2FsbCk7XG5cblx0XHQvLyBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZm9yIFR5cGVSZWdpc3RyeSBzaWduYXR1cmVcblx0XHRub2RlLmNvbnN0cnVjdG9yUGFyYW1zID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JQYXJhbXMoY2FsbCk7XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGhcblx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChwYXJlbnROb2RlLCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KG5vZGUpO1xuXHRcdH1cblxuXHRcdC8vIENyZWF0ZSBkZWZpbml0aW9uIGluZm8gdXNpbmcgdGhlIG5vZGUncyByZXNvbHZlZCBmdWxsUGF0aFxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiBwYXJlbnROb2RlID8gcGFyZW50Tm9kZS5mdWxsUGF0aCA6IG51bGwsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IGNvbmZpZy5zdHJpY3RDaGFpbiA/PyB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBjb25maWcuYmxvY2tFcnJvcnMgPz8gZmFsc2UsXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChub2RlLmZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0XHR0aGlzLmVkc1Njb3BlQnlOb2RlLnNldChjYWxsLCBub2RlLmZ1bGxQYXRoKTtcblxuXHRcdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnQ6IGNvbnN0IExhenlUeXBlID0gbGF6eSgnTGF6eVR5cGUnLCAuLi4pIC0+IG1hcCBcIkxhenlUeXBlXCIgLT4gXCJMYXp5VHlwZVwiXG5cdFx0Ly8gRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBjb25zdCBYID0gbGF6eSgnQScpLmRlZmluZSgnQicpLCB3ZSB3YW50IHRvIG1hcCBYIC0+IEEgKHRoZSByb290KVxuXHRcdHRoaXMudHJhY2tWYXJpYWJsZUFzc2lnbm1lbnQoY2FsbCwgcGFyZW50Tm9kZSwgbm9kZS5mdWxsUGF0aCk7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBsYXp5KCkgY2FsbCBhcmd1bWVudHMgaW50byBhIG5vcm1hbGl6ZWQgc2hhcGUuXG5cdCAqIEhhbmRsZXMgbmFtZWQvdW5uYW1lZCBhbmQgZXhwbGljaXQtc291cmNlIGZvcm1zLCBib3RoIGFzIGZyZWUgY2FsbHNcblx0ICogYW5kIGFzIG1ldGhvZCBjYWxscy5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdExhenlDYWxsQXJncyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7XG5cdFx0c291cmNlPzogdHMuRXhwcmVzc2lvbjtcblx0XHRuYW1lPzogc3RyaW5nO1xuXHRcdGdldHRlcjogdHMuRXhwcmVzc2lvbjtcblx0XHRjb25maWc/OiB0cy5FeHByZXNzaW9uO1xuXHR9IHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBhcmdzID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0Y29uc3QgaXNNZXRob2RDYWxsID0gdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKTtcblxuXHRcdGlmIChpc01ldGhvZENhbGwpIHtcblx0XHRcdC8vIFNvdXJjZSBpcyB0aGUgb2JqZWN0IG9mIHRoZSBwcm9wZXJ0eSBhY2Nlc3M6IFR5cGUubGF6eSguLi4pXG5cdFx0XHRjb25zdCBzb3VyY2UgPSBjYWxsLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbWV0aG9kRmlyc3RBcmcgPSBhcmdzWyAwIF07XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKG1ldGhvZEZpcnN0QXJnKSkge1xuXHRcdFx0XHQvLyBUeXBlLmxhenkoJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRcdGlmIChhcmdzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0c291cmNlLFxuXHRcdFx0XHRcdG5hbWUgICA6IG1ldGhvZEZpcnN0QXJnLnRleHQsXG5cdFx0XHRcdFx0Z2V0dGVyIDogYXJnc1sgMSBdLFxuXHRcdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDIgXSxcblx0XHRcdFx0fTtcblx0XHRcdH1cblx0XHRcdC8vIFR5cGUubGF6eShnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRzb3VyY2UsXG5cdFx0XHRcdGdldHRlciA6IG1ldGhvZEZpcnN0QXJnLFxuXHRcdFx0XHRjb25maWcgOiBhcmdzWyAxIF0sXG5cdFx0XHR9O1xuXHRcdH1cblxuXHRcdC8vIEZyZWUgY2FsbDogbGF6eSguLi4pXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZpcnN0QXJnID0gYXJnc1sgMCBdO1xuXG5cdFx0Ly8gRXhwbGljaXQtc291cmNlIGZvcm06IGxhenkoc291cmNlLCAnTmFtZScsIGdldHRlciwgY29uZmlnPylcblx0XHQvLyBvciBsYXp5KHNvdXJjZSwgZ2V0dGVyLCBjb25maWc/KVxuXHRcdGlmIChhcmdzLmxlbmd0aCA+PSAyICYmIHRzLmlzSWRlbnRpZmllcihmaXJzdEFyZykpIHtcblx0XHRcdGNvbnN0IHNlY29uZEFyZyA9IGFyZ3NbIDEgXTtcblx0XHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoc2Vjb25kQXJnKSkge1xuXHRcdFx0XHQvLyBsYXp5KHNvdXJjZSwgJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRcdGlmIChhcmdzLmxlbmd0aCA8IDMpIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0c291cmNlIDogZmlyc3RBcmcsXG5cdFx0XHRcdFx0bmFtZSAgIDogc2Vjb25kQXJnLnRleHQsXG5cdFx0XHRcdFx0Z2V0dGVyIDogYXJnc1sgMiBdLFxuXHRcdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDMgXSxcblx0XHRcdFx0fTtcblx0XHRcdH1cblx0XHRcdC8vIGxhenkoc291cmNlLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRzb3VyY2UgOiBmaXJzdEFyZyxcblx0XHRcdFx0Z2V0dGVyIDogc2Vjb25kQXJnLFxuXHRcdFx0XHRjb25maWcgOiBhcmdzWyAyIF0sXG5cdFx0XHR9O1xuXHRcdH1cblxuXHRcdC8vIE5hbWVkIHJvb3QgZm9ybTogbGF6eSgnTmFtZScsIGdldHRlciwgY29uZmlnPylcblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGZpcnN0QXJnKSkge1xuXHRcdFx0aWYgKGFyZ3MubGVuZ3RoIDwgMikge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0bmFtZSAgIDogZmlyc3RBcmcudGV4dCxcblx0XHRcdFx0Z2V0dGVyIDogYXJnc1sgMSBdLFxuXHRcdFx0XHRjb25maWcgOiBhcmdzWyAyIF0sXG5cdFx0XHR9O1xuXHRcdH1cblxuXHRcdC8vIFVubmFtZWQgcm9vdCBmb3JtOiBsYXp5KGdldHRlciwgY29uZmlnPylcblx0XHRyZXR1cm4ge1xuXHRcdFx0Z2V0dGVyIDogZmlyc3RBcmcsXG5cdFx0XHRjb25maWcgOiBhcmdzWyAxIF0sXG5cdFx0fTtcblx0fVxuXG5cdC8qKlxuXHQgKiBVbndyYXAgdGhlIGNvbnN0cnVjdG9yIHJldHVybmVkIGJ5IGEgbGF6eSBnZXR0ZXIuXG5cdCAqIFN1cHBvcnRzOlxuXHQgKiAgICgpID0+IGNsYXNzIE5hbWUge31cblx0ICogICAoKSA9PiBmdW5jdGlvbiBOYW1lKCkge31cblx0ICogICAoKSA9PiB7IHJldHVybiBjbGFzcyBOYW1lIHt9OyB9XG5cdCAqICAgZnVuY3Rpb24gKCkgeyByZXR1cm4gZnVuY3Rpb24gTmFtZSgpIHt9OyB9XG5cdCAqL1xuXHRwcml2YXRlIHVud3JhcExhenlHZXR0ZXIgKGdldHRlckV4cHI6IHRzLkV4cHJlc3Npb24pOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGdldHRlckV4cHIpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGdldHRlckV4cHI7XG5cdFx0XHRpZiAoIXRzLmlzQmxvY2soYm9keSkpIHtcblx0XHRcdFx0cmV0dXJuIGJvZHk7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IHN0bXQgb2YgYm9keS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChzdG10KSAmJiBzdG10LmV4cHJlc3Npb24pIHtcblx0XHRcdFx0XHRyZXR1cm4gc3RtdC5leHByZXNzaW9uO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihnZXR0ZXJFeHByKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBnZXR0ZXJFeHByO1xuXHRcdFx0Zm9yIChjb25zdCBzdG10IG9mIGJvZHkuc3RhdGVtZW50cykge1xuXHRcdFx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQoc3RtdCkgJiYgc3RtdC5leHByZXNzaW9uKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHN0bXQuZXhwcmVzc2lvbjtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBOb3QgYSByZWNvZ25pemVkIGdldHRlciBwYXR0ZXJuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGEgY29uc3RydWN0b3IgbmFtZSBmcm9tIGEgY2xhc3MgZXhwcmVzc2lvbiwgY2xhc3MgZGVjbGFyYXRpb24sXG5cdCAqIG9yIG5hbWVkIGZ1bmN0aW9uIGV4cHJlc3Npb24uXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3Rvck5hbWUgKGNvbnN0cnVjdG9yRXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikgJiYgY29uc3RydWN0b3JFeHByLm5hbWUpIHtcblx0XHRcdHJldHVybiBjb25zdHJ1Y3RvckV4cHIubmFtZS50ZXh0O1xuXHRcdH1cblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKGNvbnN0cnVjdG9yRXhwcikgJiYgY29uc3RydWN0b3JFeHByLm5hbWUpIHtcblx0XHRcdHJldHVybiBjb25zdHJ1Y3RvckV4cHIubmFtZS50ZXh0O1xuXHRcdH1cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSAmJiBjb25zdHJ1Y3RvckV4cHIubmFtZSkge1xuXHRcdFx0cmV0dXJuIGNvbnN0cnVjdG9yRXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0aGUgdHlwZSBuYW1lIGZyb20gZWl0aGVyIGEgZGVmaW5lKCkgb3IgbGF6eSgpIGNhbGwuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZSAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChjYWxsKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMuZXh0cmFjdFR5cGVOYW1lKGNhbGwpO1xuXHRcdH1cblx0XHRpZiAodGhpcy5pc0xhenlDYWxsKGNhbGwpKSB7XG5cdFx0XHRjb25zdCBhcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdFx0aWYgKCFhcmdzKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAoYXJncy5uYW1lKSB7XG5cdFx0XHRcdHJldHVybiBhcmdzLm5hbWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLnVud3JhcExhenlHZXR0ZXIoYXJncy5nZXR0ZXIpO1xuXHRcdFx0aWYgKGNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0XHRyZXR1cm4gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JOYW1lKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0aGUgZnVsbCBsYXp5KCkgY2FsbCBjb250ZXh0OiB0eXBlIG5hbWUsIHBhcmVudCB0eXBlLCBhbmQgY29sbGVjdGlvbi5cblx0ICogSGFuZGxlcyBkaXJlY3QgY2FsbHMsIHByb3BlcnR5LWFjY2VzcyBjYWxscywgY2hhaW5lZCBjYWxscywgYW5kIHRoZVxuXHQgKiBleHBsaWNpdC1zb3VyY2UgZm9ybSBgbGF6eShzb3VyY2UsICdUeXBlTmFtZScsIGdldHRlcilgLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0TGF6eUNvbnRleHQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKToge1xuXHRcdHR5cGVOYW1lPzogc3RyaW5nO1xuXHRcdHBhcmVudFR5cGU/OiBUeXBlTm9kZTtcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmc7XG5cdH0ge1xuXHRcdGNvbnN0IGFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0aWYgKCFhcmdzKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0bGV0IHR5cGVOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQgPSBhcmdzLm5hbWU7XG5cdFx0aWYgKCF0eXBlTmFtZSkge1xuXHRcdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy51bndyYXBMYXp5R2V0dGVyKGFyZ3MuZ2V0dGVyKTtcblx0XHRcdGlmIChjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdFx0dHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3Rvck5hbWUoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0aWYgKCF0eXBlTmFtZSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gY2FsbDtcblxuXHRcdC8vIERpcmVjdCBjYWxsOiBsYXp5KCdUeXBlTmFtZScsIC4uLikgb3IgbGF6eShzb3VyY2UsICdUeXBlTmFtZScsIGdldHRlcilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2xhenknKSB7XG5cdFx0XHRpZiAoYXJncy5zb3VyY2UgJiYgdHMuaXNJZGVudGlmaWVyKGFyZ3Muc291cmNlKSkge1xuXHRcdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKGFyZ3Muc291cmNlLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0XHRcdHBhcmVudFR5cGUgICA6IHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSxcblx0XHRcdFx0XHRjb2xsZWN0aW9uSWQgOiBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCxcblx0XHRcdFx0fTtcblx0XHRcdH1cblx0XHRcdC8vIFBsYWluIHJvb3QgbGF6eSBpbiBkZWZhdWx0IGNvbGxlY3Rpb25cblx0XHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiBYLmxhenkoJ1R5cGVOYW1lJywgLi4uKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLm5hbWUudGV4dCA9PT0gJ2xhenknKSB7XG5cdFx0XHRjb25zdCBvYmogPSBleHByZXNzaW9uLmV4cHJlc3Npb247XG5cblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIob2JqKSkge1xuXHRcdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKG9iai50ZXh0KTtcblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHR0eXBlTmFtZSxcblx0XHRcdFx0XHRwYXJlbnRUeXBlICAgOiBzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUsXG5cdFx0XHRcdFx0Y29sbGVjdGlvbklkIDogc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQsXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihvYmopKSB7XG5cdFx0XHRcdC8vIE5lc3RlZCBhY2Nlc3M6IGluc3RhbmNlLlR5cGUubGF6eSAtIHRyeSB0byByZXNvbHZlXG5cdFx0XHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKG9iaik7XG5cdFx0XHRcdGlmIChjaGFpbi5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoY2hhaW4uam9pbignLicpKTtcblx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUgfTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihvYmopKSB7XG5cdFx0XHRcdC8vIERldGVybWluZSB0aGUgY29sbGVjdGlvbiBjb250ZXh0IGZyb20gdGhlIHJvb3Qgb2YgdGhlIGNoYWluIHNvIHRoYXRcblx0XHRcdFx0Ly8gY3VzdG9tLWNvbGxlY3Rpb24gdHlwZXMgZG8gbm90IGdldCBjb25mdXNlZCB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcy5cblx0XHRcdFx0Y29uc3Qgcm9vdElkID0gdGhpcy5nZXRSb290SWRlbnRpZmllcihvYmouZXhwcmVzc2lvbik7XG5cdFx0XHRcdGNvbnN0IGV4cGVjdGVkQ29sbGVjdGlvbklkID0gcm9vdElkXG5cdFx0XHRcdFx0PyB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uocm9vdElkLnRleHQpLmNvbGxlY3Rpb25JZFxuXHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXG5cdFx0XHRcdC8vIENoYWluZWQgY2FsbDogZGVmaW5lKCdBJykubGF6eSgnQicpIG9yIGxhenkoJ0EnKS5sYXp5KCdCJylcblx0XHRcdFx0aWYgKHRoaXMuaXNEZWZpbmVDYWxsKG9iaikpIHtcblx0XHRcdFx0XHR0aGlzLnByb2Nlc3NEZWZpbmVDYWxsKG9iaiwgc291cmNlRmlsZSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzTGF6eUNhbGwob2JqLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBCdWlsZGVyIGxvb2t1cCBjaGFpbjogQXBwLmxvb2t1cCgnVXNlcicpLmxhenkoJ0FkbWluJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMb29rdXBDYWxsKG9iaikpIHtcblx0XHRcdFx0XHRjb25zdCBsb29rZWRVcFBhdGggPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKG9iaik7XG5cdFx0XHRcdFx0aWYgKGxvb2tlZFVwUGF0aCkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUobG9va2VkVXBQYXRoKTtcblx0XHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZS5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgY29uZmlnIG9wdGlvbnMgZnJvbSBsYXp5KCkgY2FsbFxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0TGF6eUNvbmZpZyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0ge1xuXHRcdGNvbnN0IGFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0aWYgKCFhcmdzIHx8ICFhcmdzLmNvbmZpZyB8fCAhdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihhcmdzLmNvbmZpZykpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRjb25zdCBjb25maWdSZXN1bHQgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChhcmdzLmNvbmZpZyk7XG5cdFx0cmV0dXJuIGNvbmZpZ1Jlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHRcdCogVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHMgdGhhdCBjYXB0dXJlIGRlZmluZSgpIHJlc3VsdHNcblx0XHQqIGUuZy4sIGNvbnN0IFVzZXIgPSBkZWZpbmUoJ1VzZXJFbnRpdHknLCAuLi4pIG1hcHMgXCJVc2VyXCIgLT4gXCJVc2VyRW50aXR5XCJcblx0XHQqIEZvciBjaGFpbmVkIGNhbGxzIGxpa2UgY29uc3QgWCA9IGRlZmluZSgnQScpLmRlZmluZSgnQicpLCB3ZSBtYXAgWCAtPiBBICh0aGUgcm9vdCB0eXBlKVxuXHRcdCovXG5cdHByaXZhdGUgdHJhY2tWYXJpYWJsZUFzc2lnbm1lbnQgKFxuXHRcdGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLFxuXHRcdHBhcmVudE5vZGU6IFR5cGVOb2RlIHwgdW5kZWZpbmVkLFxuXHRcdGZ1bGxQYXRoOiBzdHJpbmdcblx0KTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBjYWxsIGlzIHRoZSByaWdodC1oYW5kIHNpZGUgb2YgYSB2YXJpYWJsZSBkZWNsYXJhdGlvblxuXHRcdC8vIFdhbGsgdXAgdGhlIHRyZWUgdG8gZmluZCBWYXJpYWJsZURlY2xhcmF0aW9uXG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBjYWxsLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihjdXJyZW50KSkge1xuXHRcdFx0XHQvLyBGb3VuZDogY29uc3QgWCA9IGRlZmluZSguLi4pXG5cdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudC5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHZhck5hbWUgPSBjdXJyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0XHQvLyBJZiB0aGlzIGlzIGEgY2hhaW5lZCBjYWxsIChoYXMgcGFyZW50KSwgZG9uJ3Qgb3ZlcndyaXRlIGV4aXN0aW5nIG1hcHBpbmdcblx0XHRcdFx0XHQvLyBUaGUgZmlyc3QgZGVmaW5lIGluIHRoZSBjaGFpbiBzZXRzIHRoZSBtYXBwaW5nIHRvIHRoZSByb290IHR5cGVcblx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSAmJiB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmhhcyh2YXJOYW1lKSkge1xuXHRcdFx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHR0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLnNldCh2YXJOYW1lLCBmdWxsUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0fVxuXHRcblx0LyoqXG5cdFx0KiBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50cyBmcm9tIGxvb2t1cCgpIGNhbGxzXG5cdFx0KiBlLmcuLCBjb25zdCBTZW50aWVuY2VDb25zdHJ1Y3RvciA9IGxvb2t1cCgnU2VudGllbmNlJykgbWFwcyBcIlNlbnRpZW5jZUNvbnN0cnVjdG9yXCIgLT4gXCJTZW50aWVuY2VcIlxuXHRcdCovXG5cdHByaXZhdGUgdHJhY2tMb29rdXBBc3NpZ25tZW50IChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgdHlwZVBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdC8vIFdhbGsgdXAgdGhlIHRyZWUgdG8gZmluZCBWYXJpYWJsZURlY2xhcmF0aW9uXG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBjYWxsLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihjdXJyZW50KSkge1xuXHRcdFx0XHQvLyBGb3VuZDogY29uc3QgWCA9IGxvb2t1cCguLi4pXG5cdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudC5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHZhck5hbWUgPSBjdXJyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0XHR0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLnNldCh2YXJOYW1lLCB0eXBlUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdCogVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHMgZnJvbSBuZXcgVHlwZSgpIGNhbGxzXG5cdFx0KiBlLmcuLCBjb25zdCB1c2VyID0gbmV3IFVzZXJUeXBlKCkgbWFwcyBcInVzZXJcIiAtPiBcIlVzZXJUeXBlXCJcblx0XHQqL1xuXHRwcml2YXRlIHRyYWNrTmV3QXNzaWdubWVudCAobmV3RXhwcjogdHMuTmV3RXhwcmVzc2lvbiwgdHlwZVBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdC8vIFdhbGsgdXAgdGhlIHRyZWUgdG8gZmluZCBWYXJpYWJsZURlY2xhcmF0aW9uXG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBuZXdFeHByLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihjdXJyZW50KSkge1xuXHRcdFx0XHQvLyBGb3VuZDogY29uc3QgWCA9IG5ldyBUeXBlKC4uLilcblx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50Lm5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgdmFyTmFtZSA9IGN1cnJlbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRcdHRoaXMudmFyaWFibGVUb1R5cGVNYXAuc2V0KHZhck5hbWUsIHR5cGVQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm47XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdFx0KiBQcm9jZXNzIGEgQGRlY29yYXRlKCkgZGVjb3JhdG9yXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NEZWNvcmF0ZURlY29yYXRvciAoXG5cdFx0ZGVjb3JhdG9yOiB0cy5EZWNvcmF0b3IsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRjbGFzc0RlY2xQYXJhbT86IHRzLkNsYXNzRGVjbGFyYXRpb25cblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdGRlY29yYXRvci5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cblx0XHQvLyBHZXQgdGhlIGNsYXNzIGRlY2xhcmF0aW9uIC0gdXNlIHRoZSBwYXNzZWQgY29udGV4dCBpZiBwYXJlbnQgaXMgbm90IHNldFxuXHRcdGNvbnN0IGNsYXNzRGVjbCA9IGRlY29yYXRvci5wYXJlbnQgYXMgdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCB8fCBjbGFzc0RlY2xQYXJhbTtcblx0XHRpZiAoIWNsYXNzRGVjbCB8fCAhY2xhc3NEZWNsLm5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0RlY29yYXRlZCBjbGFzcyBoYXMgbm8gbmFtZScsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgdHlwZU5hbWUgPSBjbGFzc0RlY2wubmFtZS50ZXh0O1xuXHRcdGlmICghdHlwZU5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0RlY29yYXRlZCBjbGFzcyBoYXMgbm8gbmFtZScsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUGFyc2UgZGVjb3JhdG9yIGFyZ3VtZW50czogQGRlY29yYXRlKCksIEBkZWNvcmF0ZShQYXJlbnQpLFxuXHRcdC8vIEBkZWNvcmF0ZSh7IC4uLiB9KSwgQGRlY29yYXRlKFBhcmVudCwgeyAuLi4gfSksXG5cdFx0Ly8gQE15Q29sbGVjdGlvbi5kZWNvcmF0ZSgpLCBATXlDb2xsZWN0aW9uLmRlY29yYXRlKHsgLi4uIH0pXG5cdFx0bGV0IHBhcmVudE5vZGU6IFR5cGVOb2RlIHwgdW5kZWZpbmVkO1xuXHRcdGxldCBwYXJlbnRGdWxsUGF0aDogc3RyaW5nIHwgbnVsbCA9IG51bGw7XG5cdFx0bGV0IGNvbGxlY3Rpb25JZDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdGxldCBkZWNvcmF0b3JDb25maWc6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSA9IHt9O1xuXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZGVjb3JhdG9yLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRjb25zdCBjYWxsRXhwciA9IGRlY29yYXRvci5leHByZXNzaW9uO1xuXHRcdFx0Y29uc3QgY2FsbGVlID0gY2FsbEV4cHIuZXhwcmVzc2lvbjtcblxuXHRcdFx0Ly8gQ2hlY2sgZm9yIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSB3aGVyZSBNeUNvbGxlY3Rpb24gaXMgYSBjdXN0b20gY29sbGVjdGlvbi5cblx0XHRcdC8vIFRoZSBkZWNvcmF0ZWQgY2xhc3MgYmVjb21lcyBhIHJvb3QgdHlwZSBpbiB0aGF0IGNvbGxlY3Rpb24uXG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxlZSkgJiZcblx0XHRcdFx0Y2FsbGVlLm5hbWUudGV4dCA9PT0gJ2RlY29yYXRlJyAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoY2FsbGVlLmV4cHJlc3Npb24pICYmXG5cdFx0XHRcdHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5oYXMoY2FsbGVlLmV4cHJlc3Npb24udGV4dClcblx0XHRcdCkge1xuXHRcdFx0XHRjb2xsZWN0aW9uSWQgPSB0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuZ2V0KGNhbGxlZS5leHByZXNzaW9uLnRleHQpO1xuXHRcdFx0XHRpZiAoY2FsbEV4cHIuYXJndW1lbnRzLmxlbmd0aCA9PT0gMSAmJiB0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGNhbGxFeHByLmFyZ3VtZW50c1sgMCBdKSkge1xuXHRcdFx0XHRcdGRlY29yYXRvckNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGNhbGxFeHByLmFyZ3VtZW50c1sgMCBdKTtcblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgYXJncyA9IGNhbGxFeHByLmFyZ3VtZW50cztcblx0XHRcdFx0bGV0IHBhcmVudEFyZzogdHMuSWRlbnRpZmllciB8IHVuZGVmaW5lZDtcblx0XHRcdFx0bGV0IGNvbmZpZ0FyZzogdHMuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24gfCB1bmRlZmluZWQ7XG5cblx0XHRcdFx0Zm9yIChjb25zdCBhcmcgb2YgYXJncykge1xuXHRcdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0XHRcdFx0aWYgKHBhcmVudEFyZykge1xuXHRcdFx0XHRcdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0XHRcdFx0XHRtZXNzYWdlIDogJ0BkZWNvcmF0ZSgpIGFjY2VwdHMgb25seSBvbmUgcGFyZW50IHJlZmVyZW5jZScsXG5cdFx0XHRcdFx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRcdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHRcdHBhcmVudEFyZyA9IGFyZztcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0XHRcdFx0aWYgKGNvbmZpZ0FyZykge1xuXHRcdFx0XHRcdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0XHRcdFx0XHRtZXNzYWdlIDogJ0BkZWNvcmF0ZSgpIGFjY2VwdHMgb25seSBvbmUgY29uZmlnIG9iamVjdCcsXG5cdFx0XHRcdFx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRcdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHRcdGNvbmZpZ0FyZyA9IGFyZztcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRpZiAocGFyZW50QXJnKSB7XG5cdFx0XHRcdFx0cGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeUlkZW50aWZpZXIocGFyZW50QXJnLnRleHQpO1xuXHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHRwYXJlbnRGdWxsUGF0aCA9IHBhcmVudE5vZGUuZnVsbFBhdGg7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0aWYgKGNvbmZpZ0FyZykge1xuXHRcdFx0XHRcdGRlY29yYXRvckNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGNvbmZpZ0FyZyk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBCdWlsZCBmdWxsIHBhdGhcblx0XHRjb25zdCBmdWxsUGF0aCA9IHBhcmVudE5vZGUgPyBgJHtwYXJlbnROb2RlLmZ1bGxQYXRofS4ke3R5cGVOYW1lfWAgOiB0eXBlTmFtZTtcblxuXHRcdC8vIENyZWF0ZSBkZWZpbml0aW9uIGluZm8gZm9yIGRlY29yYXRlXG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IHR5cGVOYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlY29yYXRlJyxcblx0XHRcdHBhcmVudCAgICAgIDogcGFyZW50RnVsbFBhdGgsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IGRlY29yYXRvckNvbmZpZy5zdHJpY3RDaGFpbiA/PyB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBkZWNvcmF0b3JDb25maWcuYmxvY2tFcnJvcnMgPz8gZmFsc2UsXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChmdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdFx0dGhpcy5lZHNTY29wZUJ5Tm9kZS5zZXQoY2xhc3NEZWNsLCBmdWxsUGF0aCk7XG5cblx0XHQvLyBDcmVhdGUgdHlwZSBub2RlXG5cdFx0Y29uc3Qgbm9kZSA9IFR5cGVHcmFwaEltcGwuY3JlYXRlTm9kZShcblx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0cGFyZW50Tm9kZSxcblx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRsaW5lICsgMSxcblx0XHRcdGNoYXJhY3RlciArIDEsXG5cdFx0XHRjb2xsZWN0aW9uSWRcblx0XHQpO1xuXHRcdG5vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lID0gdGhpcy5nZXRSZWdpc3RyeUludGVyZmFjZU5hbWUobm9kZS5jb2xsZWN0aW9uSWQpO1xuXG5cdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGFuZCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZyb20gY2xhc3MgbWVtYmVyc1xuXHRcdG5vZGUucHJvcGVydGllcyA9IHRoaXMuZXh0cmFjdENsYXNzUHJvcGVydGllcyhjbGFzc0RlY2wpO1xuXHRcdG5vZGUuY29uc3RydWN0b3JQYXJhbXMgPSB0aGlzLmV4dHJhY3RDbGFzc0NvbnN0cnVjdG9yUGFyYW1zKGNsYXNzRGVjbCk7XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGhcblx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChwYXJlbnROb2RlLCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KG5vZGUpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHR5cGUgbmFtZSBmcm9tIGRlZmluZSgpIGNhbGwgYXJndW1lbnRzLlxuXHQgKiBIYW5kbGVzOlxuXHQgKiAgIGRlZmluZSgnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHQgKiAgIGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpICAgLy8gZXhwbGljaXQtc291cmNlIGZvcm1cblx0ICogICBkZWZpbmUoZnVuY3Rpb24gVHlwZU5hbWUoKSB7fSlcblx0ICogICBkZWZpbmUoKCkgPT4gY2xhc3MgVHlwZU5hbWUge30pXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RUeXBlTmFtZSAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGFyZ3MgPSBjYWxsLmFyZ3VtZW50cztcblxuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBmaXJzdEFyZyA9IGFyZ3NbIDAgXTtcblxuXHRcdC8vIEV4cGxpY2l0LXNvdXJjZSBmb3JtOiBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA+PSAyICYmIHRzLmlzSWRlbnRpZmllcihmaXJzdEFyZykgJiYgdHMuaXNTdHJpbmdMaXRlcmFsKGFyZ3NbIDEgXSkpIHtcblx0XHRcdHJldHVybiBhcmdzWyAxIF0udGV4dDtcblx0XHR9XG5cblx0XHQvLyBTdHJpbmcgbGl0ZXJhbDogZGVmaW5lKCdUeXBlTmFtZScsIC4uLilcblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGZpcnN0QXJnKSkge1xuXHRcdFx0cmV0dXJuIGZpcnN0QXJnLnRleHQ7XG5cdFx0fVxuXG5cdFx0Ly8gRnVuY3Rpb24gd2l0aCBuYW1lOiBkZWZpbmUoZnVuY3Rpb24gVHlwZU5hbWUoKSB7fSlcblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oZmlyc3RBcmcpICYmIGZpcnN0QXJnLm5hbWUpIHtcblx0XHRcdHJldHVybiBmaXJzdEFyZy5uYW1lLnRleHQ7XG5cdFx0fVxuXG5cdFx0Ly8gQXJyb3cgZnVuY3Rpb24gcmV0dXJuaW5nIGNsYXNzOiBkZWZpbmUoKCkgPT4gY2xhc3MgVHlwZU5hbWUge30pXG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihmaXJzdEFyZykpIHtcblx0XHRcdGNvbnN0IHsgYm9keSB9ID0gZmlyc3RBcmc7XG5cdFx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oYm9keSkgJiYgYm9keS5uYW1lKSB7XG5cdFx0XHRcdHJldHVybiBib2R5Lm5hbWUudGV4dDtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdGhlIGZ1bGwgZGVmaW5lKCkgY2FsbCBjb250ZXh0OiB0eXBlIG5hbWUsIHBhcmVudCB0eXBlLCBhbmQgY29sbGVjdGlvbi5cblx0ICogSGFuZGxlcyBkaXJlY3QgY2FsbHMsIHByb3BlcnR5LWFjY2VzcyBjYWxscywgY2hhaW5lZCBjYWxscywgYW5kIHRoZVxuXHQgKiBleHBsaWNpdC1zb3VyY2UgZm9ybSBgZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilgLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0RGVmaW5lQ29udGV4dCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7XG5cdFx0dHlwZU5hbWU/OiBzdHJpbmc7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Y29uc3QgdHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RUeXBlTmFtZShjYWxsKTtcblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBjYWxsO1xuXG5cdFx0Ly8gRGlyZWN0IGNhbGw6IGRlZmluZSgnVHlwZU5hbWUnLCAuLi4pIG9yIGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLnRleHQgPT09ICdkZWZpbmUnKSB7XG5cdFx0XHQvLyBFeHBsaWNpdC1zb3VyY2UgZm9ybTogZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilcblx0XHRcdGlmIChjYWxsLmFyZ3VtZW50cy5sZW5ndGggPj0gMiAmJiB0cy5pc0lkZW50aWZpZXIoY2FsbC5hcmd1bWVudHNbIDAgXSkpIHtcblx0XHRcdFx0Y29uc3Qgc291cmNlTmFtZSA9IGNhbGwuYXJndW1lbnRzWyAwIF0udGV4dDtcblx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShzb3VyY2VOYW1lKTtcblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHR0eXBlTmFtZSxcblx0XHRcdFx0XHRwYXJlbnRUeXBlICAgOiBzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUsXG5cdFx0XHRcdFx0Y29sbGVjdGlvbklkIDogc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQsXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cblx0XHRcdC8vIFBsYWluIHJvb3QgZGVmaW5lIGluIGRlZmF1bHQgY29sbGVjdGlvblxuXHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUgfTtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSBhY2Nlc3M6IFguZGVmaW5lKCdUeXBlTmFtZScsIC4uLilcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi5uYW1lLnRleHQgPT09ICdkZWZpbmUnKSB7XG5cdFx0XHRjb25zdCBvYmogPSBleHByZXNzaW9uLmV4cHJlc3Npb247XG5cblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIob2JqKSkge1xuXHRcdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKG9iai50ZXh0KTtcblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHR0eXBlTmFtZSxcblx0XHRcdFx0XHRwYXJlbnRUeXBlICAgOiBzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUsXG5cdFx0XHRcdFx0Y29sbGVjdGlvbklkIDogc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQsXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihvYmopKSB7XG5cdFx0XHRcdC8vIE5lc3RlZCBhY2Nlc3M6IGluc3RhbmNlLlR5cGUuZGVmaW5lIC0gdHJ5IHRvIHJlc29sdmVcblx0XHRcdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4ob2JqKTtcblx0XHRcdFx0aWYgKGNoYWluLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShjaGFpbi5qb2luKCcuJykpO1xuXHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSB9O1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gRGV0ZXJtaW5lIHRoZSBjb2xsZWN0aW9uIGNvbnRleHQgZnJvbSB0aGUgcm9vdCBvZiB0aGUgY2hhaW4gc28gdGhhdFxuXHRcdFx0XHQvLyBjdXN0b20tY29sbGVjdGlvbiB0eXBlcyBkbyBub3QgZ2V0IGNvbmZ1c2VkIHdpdGggZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzLlxuXHRcdFx0XHRjb25zdCByb290SWQgPSB0aGlzLmdldFJvb3RJZGVudGlmaWVyKG9iai5leHByZXNzaW9uKTtcblx0XHRcdFx0Y29uc3QgZXhwZWN0ZWRDb2xsZWN0aW9uSWQgPSByb290SWRcblx0XHRcdFx0XHQ/IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShyb290SWQudGV4dCkuY29sbGVjdGlvbklkXG5cdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHRcdFx0Ly8gQ2hhaW5lZCBjYWxsOiBkZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKSBvciBtbmVtb25pY2EuZGVmaW5lKCdBJykuZGVmaW5lKCdCJylcblx0XHRcdFx0aWYgKHRoaXMuaXNEZWZpbmVDYWxsKG9iaikpIHtcblx0XHRcdFx0XHR0aGlzLnByb2Nlc3NEZWZpbmVDYWxsKG9iaiwgY2FsbC5nZXRTb3VyY2VGaWxlKCkpO1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudFR5cGVOYW1lID0gdGhpcy5leHRyYWN0VHlwZU5hbWUob2JqKTtcblx0XHRcdFx0XHRpZiAocGFyZW50VHlwZU5hbWUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKHBhcmVudFR5cGVOYW1lLCBleHBlY3RlZENvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHQvLyBJbmhlcml0IGNvbGxlY3Rpb24gZnJvbSB0aGUgcGFyZW50IHR5cGUgKGlmIGFueSlcblx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gQ2hhaW5lZCBsYXp5IGNhbGw6IGxhenkoJ0EnKS5kZWZpbmUoJ0InKSBvciBUeXBlLmxhenkoJ0EnKS5kZWZpbmUoJ0InKVxuXHRcdFx0XHRpZiAodGhpcy5pc0xhenlDYWxsKG9iaikpIHtcblx0XHRcdFx0XHR0aGlzLnByb2Nlc3NMYXp5Q2FsbChvYmosIGNhbGwuZ2V0U291cmNlRmlsZSgpKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBCdWlsZGVyIGxvb2t1cCBjaGFpbjogQXBwLmxvb2t1cCgnVXNlcicpLmRlZmluZSgnQWRtaW4nKVxuXHRcdFx0XHRpZiAodGhpcy5pc0xvb2t1cENhbGwob2JqKSkge1xuXHRcdFx0XHRcdGNvbnN0IGxvb2tlZFVwUGF0aCA9IHRoaXMucmVzb2x2ZUxvb2t1cFBhdGgob2JqKTtcblx0XHRcdFx0XHRpZiAobG9va2VkVXBQYXRoKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShsb29rZWRVcFBhdGgpO1xuXHRcdFx0XHRcdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlLmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdH1cblxuXHQvKipcblx0ICogUHJlZml4IGEgZG90dGVkIHR5cGUgcGF0aCB3aXRoIGEgY29sbGVjdGlvbiBpZGVudGlmaWVyIHNvIGN1c3RvbS1jb2xsZWN0aW9uXG5cdCAqIHR5cGVzIGRvIG5vdCBjb2xsaWRlIHdpdGggZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzIGluIHRoZSBncmFwaC5cblx0ICovXG5cdHByaXZhdGUgcHJlZml4Q29sbGVjdGlvblBhdGggKHBhdGg6IHN0cmluZywgY29sbGVjdGlvbklkOiBzdHJpbmcpOiBzdHJpbmcge1xuXHRcdHJldHVybiBgJHtjb2xsZWN0aW9uSWR9Ojoke3BhdGh9YDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgZGVmaW5lKCkgc291cmNlIGlkZW50aWZpZXIgdG8gZWl0aGVyIGEgcGFyZW50IHR5cGUsIGEgY29sbGVjdGlvbixcblx0ICogb3IgdGhlIGRlZmF1bHQgKG1vZHVsZSBvYmplY3QpIGNvbGxlY3Rpb24uXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVEZWZpbmVTb3VyY2UgKHNvdXJjZU5hbWU6IHN0cmluZyk6IHtcblx0XHRwYXJlbnRUeXBlPzogVHlwZU5vZGU7XG5cdFx0Y29sbGVjdGlvbklkPzogc3RyaW5nO1xuXHR9IHtcblx0XHQvLyBNb2R1bGUgb2JqZWN0IGFsaWFzZXMgLT4gcm9vdCBpbiBkZWZhdWx0IGNvbGxlY3Rpb25cblx0XHRpZiAodGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuaGFzKHNvdXJjZU5hbWUpKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Ly8gQ29sbGVjdGlvbiB2YXJpYWJsZXMgLT4gcm9vdCBpbiB0aGF0IGNvbGxlY3Rpb25cblx0XHRjb25zdCBjb2xsZWN0aW9uSWQgPSB0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuZ2V0KHNvdXJjZU5hbWUpO1xuXHRcdGlmIChjb2xsZWN0aW9uSWQpIHtcblx0XHRcdHJldHVybiB7IGNvbGxlY3Rpb25JZCB9O1xuXHRcdH1cblxuXHRcdC8vIE90aGVyd2lzZSB0cmVhdCBhcyBhIHR5cGUgdmFyaWFibGUgcmVmZXJlbmNlXG5cdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeUlkZW50aWZpZXIoc291cmNlTmFtZSk7XG5cdFx0cmV0dXJuIHsgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGEgY2FsbCBleHByZXNzaW9uIGlzIGEgbG9va3VwKCkgY2FsbC5cblx0ICovXG5cdHByaXZhdGUgaXNMb29rdXBDYWxsIChub2RlOiB0cy5DYWxsRXhwcmVzc2lvbik6IGJvb2xlYW4ge1xuXHRcdGNvbnN0IGV4cHIgPSBub2RlLmV4cHJlc3Npb247XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSAmJiBleHByLnRleHQgPT09ICdsb29rdXAnKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpICYmIGV4cHIubmFtZS50ZXh0ID09PSAnbG9va3VwJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgbG9va3VwKCkgY2FsbCB0byBhIGRvdHRlZCB0eXBlIHBhdGggKGJlc3QgZWZmb3J0KS5cblx0ICogSGFuZGxlczpcblx0ICogICBsb29rdXAoJ1VzZXInKVxuXHQgKiAgIGxvb2t1cChzb3VyY2UsICdVc2VyJylcblx0ICogICBBcHAubG9va3VwKCdVc2VyJylcblx0ICogICBjb2xsZWN0aW9uLmxvb2t1cCgnVXNlci5BZG1pbicpXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVMb29rdXBQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBTaW5nbGUtYXJnIGxvb2t1cDogbG9va3VwKCdVc2VyJykgb3IgQXBwLmxvb2t1cCgnVXNlcicpXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAxKSB7XG5cdFx0XHRjb25zdCBhcmcgPSBhcmdzWyAwIF07XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGFyZykgfHwgdHMuaXNOb1N1YnN0aXR1dGlvblRlbXBsYXRlTGl0ZXJhbChhcmcpKSB7XG5cdFx0XHRcdGNvbnN0IHBhdGggPSBhcmcudGV4dDtcblx0XHRcdFx0Ly8gSWYgdGhpcyBpcyBhIG1ldGhvZCBjYWxsIG9uIGEgc291cmNlLCByZXNvbHZlIHJlbGF0aXZlIHRvIHRoYXQgc291cmNlLlxuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdGNvbnN0IHNvdXJjZUV4cHIgPSBjYWxsLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKHNvdXJjZUV4cHIpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBzb3VyY2VOYW1lID0gc291cmNlRXhwci50ZXh0O1xuXHRcdFx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShzb3VyY2VOYW1lKTtcblx0XHRcdFx0XHRcdGlmIChzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCkge1xuXHRcdFx0XHRcdFx0XHQvLyBDb2xsZWN0aW9uIGxvb2t1cDogcHJlZml4IHBhdGggd2l0aCB0aGUgY29sbGVjdGlvbiBpZFxuXHRcdFx0XHRcdFx0XHRyZXR1cm4gdGhpcy5wcmVmaXhDb2xsZWN0aW9uUGF0aChwYXRoLCBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRpZiAoc291cmNlQ29udGV4dC5wYXJlbnRUeXBlKSB7XG5cdFx0XHRcdFx0XHRcdC8vIFR5cGUgbG9va3VwOiByZWxhdGl2ZSBmaXJzdCwgdGhlbiByb290IGZhbGxiYWNrXG5cdFx0XHRcdFx0XHRcdGNvbnN0IHJlbGF0aXZlUGF0aCA9IGAke3NvdXJjZUNvbnRleHQucGFyZW50VHlwZS5mdWxsUGF0aH0uJHtwYXRofWA7XG5cdFx0XHRcdFx0XHRcdGlmICh0aGlzLmdyYXBoLmZpbmRUeXBlKHJlbGF0aXZlUGF0aCkpIHtcblx0XHRcdFx0XHRcdFx0XHRyZXR1cm4gcmVsYXRpdmVQYXRoO1xuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRcdHJldHVybiBwYXRoO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gVHdvLWFyZyBsb29rdXA6IGxvb2t1cChzb3VyY2UsICdVc2VyJylcblx0XHRpZiAoYXJncy5sZW5ndGggPj0gMikge1xuXHRcdFx0Y29uc3Qgc291cmNlQXJnID0gYXJnc1sgMCBdO1xuXHRcdFx0Y29uc3QgcGF0aEFyZyA9IGFyZ3NbIDEgXTtcblx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHNvdXJjZUFyZykgfHwgIXRzLmlzU3RyaW5nTGl0ZXJhbChwYXRoQXJnKSkge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgc291cmNlTmFtZSA9IHNvdXJjZUFyZy50ZXh0O1xuXHRcdFx0Y29uc3QgcGF0aCA9IHBhdGhBcmcudGV4dDtcblx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRpZiAoc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQpIHtcblx0XHRcdFx0cmV0dXJuIHRoaXMucHJlZml4Q29sbGVjdGlvblBhdGgocGF0aCwgc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQpO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSkge1xuXHRcdFx0XHRjb25zdCByZWxhdGl2ZVBhdGggPSBgJHtzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUuZnVsbFBhdGh9LiR7cGF0aH1gO1xuXHRcdFx0XHRpZiAodGhpcy5ncmFwaC5maW5kVHlwZShyZWxhdGl2ZVBhdGgpKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHJlbGF0aXZlUGF0aDtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdH1cblx0XHRcdHJldHVybiBwYXRoO1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0XHQqIEZpbmQgYSBwYXJlbnQgdHlwZSBieSBpdHMgbmFtZSwgc2VhcmNoaW5nIGluIHRoZSBncmFwaC5cblx0XHQqIFdoZW4gY29sbGVjdGlvbklkIGlzIHByb3ZpZGVkLCBvbmx5IHR5cGVzIGZyb20gdGhhdCBjb2xsZWN0aW9uIGFyZSBjb25zaWRlcmVkLlxuXHRcdCovXG5cdHByaXZhdGUgZmluZFBhcmVudFR5cGVCeU5hbWUgKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmdcblx0KTogVHlwZU5vZGUgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IG1hdGNoZXNDb2xsZWN0aW9uID0gKHR5cGU6IFR5cGVOb2RlKTogYm9vbGVhbiA9PiB7XG5cdFx0XHRpZiAoY29sbGVjdGlvbklkID09PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0cmV0dXJuIHR5cGUuY29sbGVjdGlvbklkID09PSB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdHlwZS5jb2xsZWN0aW9uSWQgPT09IGNvbGxlY3Rpb25JZDtcblx0XHR9O1xuXG5cdFx0Ly8gRmlyc3QgdHJ5IGV4YWN0IG1hdGNoIChkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMgdXNlIHRoZSBwbGFpbiBkb3R0ZWQgcGF0aClcblx0XHRjb25zdCBleGFjdCA9IHRoaXMuZ3JhcGguZmluZFR5cGUobmFtZSk7XG5cdFx0aWYgKGV4YWN0ICYmIG1hdGNoZXNDb2xsZWN0aW9uKGV4YWN0KSkge1xuXHRcdFx0cmV0dXJuIGV4YWN0O1xuXHRcdH1cblxuXHRcdC8vIFRoZW4gc2VhcmNoIHRocm91Z2ggYWxsIHR5cGVzIGZvciBvbmUgd2l0aCBtYXRjaGluZyBuYW1lIGFuZCBjb2xsZWN0aW9uXG5cdFx0Zm9yIChjb25zdCB0eXBlIG9mIHRoaXMuZ3JhcGguZ2V0QWxsVHlwZXMoKSkge1xuXHRcdFx0aWYgKHR5cGUubmFtZSA9PT0gbmFtZSAmJiBtYXRjaGVzQ29sbGVjdGlvbih0eXBlKSkge1xuXHRcdFx0XHRyZXR1cm4gdHlwZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBGaW5kIGEgcGFyZW50IHR5cGUgZnJvbSBhbiBpZGVudGlmaWVyIHJlZmVyZW5jZS5cblx0XHQqIEhhbmRsZXMgYm90aCBhbGlhc2VkIHZhcmlhYmxlcyAoY29uc3QgVXNlciA9IGRlZmluZSgnVXNlckVudGl0eScsIC4uLikpXG5cdFx0KiBhbmQgZGlyZWN0IGNsYXNzL3R5cGUgbmFtZXMuXG5cdFx0Ki9cblx0cHJpdmF0ZSBmaW5kUGFyZW50VHlwZUJ5SWRlbnRpZmllciAobmFtZTogc3RyaW5nKTogVHlwZU5vZGUgfCB1bmRlZmluZWQge1xuXHRcdC8vIEZpcnN0IGNoZWNrIHZhcmlhYmxlIG1hcHBpbmc6IGNvbnN0IFVzZXIgPSBkZWZpbmUoJ1VzZXJFbnRpdHknLCAuLi4pXG5cdFx0Y29uc3QgbWFwcGVkRnVsbFBhdGggPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChuYW1lKTtcblx0XHRpZiAobWFwcGVkRnVsbFBhdGgpIHtcblx0XHRcdGNvbnN0IG1hcHBlZE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKG1hcHBlZEZ1bGxQYXRoKTtcblx0XHRcdGlmIChtYXBwZWROb2RlKSByZXR1cm4gbWFwcGVkTm9kZTtcblx0XHR9XG5cblx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShuYW1lKTtcblx0XHRyZXR1cm4gcGFyZW50Tm9kZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgdGhlIGxlZnRtb3N0IGlkZW50aWZpZXIgb2YgYSBwcm9wZXJ0eS1hY2Nlc3MgY2hhaW4uXG5cdCAqIEZvciBgQXBwLmRlZmluZSgnVXNlcicpLmRlZmluZSgnQWRtaW4nKWAgdGhpcyByZXR1cm5zIHRoZSBgQXBwYCBpZGVudGlmaWVyLlxuXHQgKi9cblx0cHJpdmF0ZSBnZXRSb290SWRlbnRpZmllciAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHRzLklkZW50aWZpZXIgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5FeHByZXNzaW9uID0gZXhwcjtcblx0XHR3aGlsZSAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY3VycmVudCkpIHtcblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0fVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudCkpIHtcblx0XHRcdHJldHVybiBjdXJyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBHZXQgcHJvcGVydHkgY2hhaW4gZnJvbSBuZXN0ZWQgYWNjZXNzXG5cdFx0Ki9cblx0cHJpdmF0ZSBnZXRQcm9wZXJ0eUNoYWluIChleHByOiB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24gfCB0cy5JZGVudGlmaWVyKTogc3RyaW5nW10ge1xuXHRcdGNvbnN0IGNoYWluOiBzdHJpbmdbXSA9IFtdO1xuXG5cdFx0bGV0IGN1cnJlbnQ6IHRzLkV4cHJlc3Npb24gPSBleHByO1xuXHRcdHdoaWxlICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0aWYgKGN1cnJlbnQubmFtZSkge1xuXHRcdFx0XHRjaGFpbi51bnNoaWZ0KGN1cnJlbnQubmFtZS50ZXh0KTtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0fVxuXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50KSkge1xuXHRcdFx0Y2hhaW4udW5zaGlmdChjdXJyZW50LnRleHQpO1xuXHRcdH1cblxuXHRcdHJldHVybiBjaGFpbjtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlcm1pbmUgdGhlIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24gZm9yIGVpdGhlciBhIGRlZmluZSgpIG9yIGxhenkoKSBjYWxsLlxuXHQgKiBGb3IgZGVmaW5lKCkgdGhpcyBpcyB0aGUgY29uc3RydWN0IGhhbmRsZXI7IGZvciBsYXp5KCkgaXQgaXMgdGhlIHZhbHVlXG5cdCAqIHJldHVybmVkIGJ5IHRoZSBsYXp5IGdldHRlci5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENvbnN0cnVjdG9yRXhwcmVzc2lvbiAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBleHByID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGNvbnN0IG5hbWUgPSB0cy5pc0lkZW50aWZpZXIoZXhwcilcblx0XHRcdD8gZXhwci50ZXh0XG5cdFx0XHQ6IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpXG5cdFx0XHRcdD8gZXhwci5uYW1lLnRleHRcblx0XHRcdFx0OiAnJztcblxuXHRcdGlmIChuYW1lID09PSAnbGF6eScpIHtcblx0XHRcdGNvbnN0IGxhenlBcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdFx0aWYgKCFsYXp5QXJncykge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHRoaXMudW53cmFwTGF6eUdldHRlcihsYXp5QXJncy5nZXR0ZXIpO1xuXHRcdH1cblxuXHRcdC8vIGRlZmluZSgpIGNhbGxcblx0XHRjb25zdCBhcmdzID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIE1vZGVybiBmb3JtOiBkZWZpbmUoJ05hbWUnLCBoYW5kbGVyLCBjb25maWc/KVxuXHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoYXJnc1sgMCBdKSkge1xuXHRcdFx0cmV0dXJuIGFyZ3NbIDEgXTtcblx0XHR9XG5cblx0XHQvLyBMZWdhY3kgZm9ybTogZGVmaW5lKGZ1bmN0aW9uIE5hbWUoKSB7fSkgb3IgZGVmaW5lKCgpID0+IGNsYXNzIE5hbWUge30pXG5cdFx0cmV0dXJuIGFyZ3NbIDAgXTtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBjb25zdHJ1Y3RvciBmdW5jdGlvblxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UHJvcGVydGllcyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCk7XG5cdFx0aWYgKCFjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdHJldHVybiBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzRnJvbUNvbnN0cnVjdG9yKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBhIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24gKGZ1bmN0aW9uLCBhcnJvdywgb3IgY2xhc3MpLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UHJvcGVydGllc0Zyb21Db25zdHJ1Y3RvciAoY29uc3RydWN0b3JFeHByOiB0cy5FeHByZXNzaW9uKTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cblx0XHQvLyBCdWlsZCB0eXBlIG1hcCBmcm9tIGRhdGEgcGFyYW1ldGVyIChmb3IgdGhpcy54ID0gZGF0YS54IHBhdHRlcm5zKVxuXHRcdGNvbnN0IGRhdGFUeXBlTWFwID0gdGhpcy5idWlsZERhdGFUeXBlTWFwKGNvbnN0cnVjdG9yRXhwcik7XG5cblx0XHQvLyBIYW5kbGUgZnVuY3Rpb24gZXhwcmVzc2lvblxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzQXJyb3dGdW5jdGlvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGNvbnN0cnVjdG9yRXhwcjtcblxuXHRcdFx0Ly8gRmlyc3QsIGV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGB0aGlzYCBwYXJhbWV0ZXIgdHlwZSBhbm5vdGF0aW9uXG5cdFx0XHQvLyBUaGlzIGhhbmRsZXMgcGF0dGVybnMgbGlrZTogZnVuY3Rpb24odGhpczogU29tZVR5cGUsIGRhdGE6IFNvbWVUeXBlKSB7IH1cblx0XHRcdGNvbnN0IHRoaXNQYXJhbVByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RUaGlzUGFyYW1Qcm9wZXJ0aWVzKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRmb3IgKGNvbnN0IFsgbmFtZSwgcHJvcEluZm8gXSBvZiB0aGlzUGFyYW1Qcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHByb3BJbmZvKTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gRnVuY3Rpb24gYm9keSB3aXRoIHN0YXRlbWVudHNcblx0XHRcdGlmICh0cy5pc0Jsb2NrKGJvZHkpKSB7XG5cdFx0XHRcdGZvciAoY29uc3Qgc3RtdCBvZiBib2R5LnN0YXRlbWVudHMpIHtcblx0XHRcdFx0XHRpZiAodHMuaXNFeHByZXNzaW9uU3RhdGVtZW50KHN0bXQpKSB7XG5cdFx0XHRcdFx0XHR0aGlzLmV4dHJhY3RQcm9wZXJ0eUZyb21TdGF0ZW1lbnQoc3RtdC5leHByZXNzaW9uLCBwcm9wZXJ0aWVzLCBkYXRhVHlwZU1hcCk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gSGFuZGxlIGNsYXNzIGV4cHJlc3Npb25cblx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Ly8gRmlyc3QgcGFzczogY29sbGVjdCBhbGwgcHJvcGVydHkgdHlwZXMgZm9yIG1ldGhvZCBpbmZlcmVuY2Vcblx0XHRcdGNvbnN0IGNsYXNzUHJvcGVydHlUeXBlcyA9IHRoaXMuZXh0cmFjdENsYXNzUHJvcGVydHlUeXBlcyhjb25zdHJ1Y3RvckV4cHIpO1xuXG5cdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjb25zdHJ1Y3RvckV4cHIubWVtYmVycykge1xuXHRcdFx0XHQvLyBIYW5kbGUgcHJvcGVydHkgZGVjbGFyYXRpb25zXG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5RGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSkge1xuXHRcdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIHByb3BlcnRpZXNcblx0XHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4ge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHRcdFx0bS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQ7XG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXG5cdFx0XHRcdFx0Y29uc3QgbmFtZSA9IHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkgPyBtZW1iZXIubmFtZS50ZXh0IDogJyc7XG5cdFx0XHRcdFx0aWYgKG5hbWUpIHtcblx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdFx0dHlwZSAgICAgOiB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSksXG5cdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogISFtZW1iZXIucXVlc3Rpb25Ub2tlbixcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIEhhbmRsZSBtZXRob2QgZGVjbGFyYXRpb25zXG5cdFx0XHRcdGlmICh0cy5pc01ldGhvZERlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIG1ldGhvZHNcblx0XHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4ge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHRcdFx0bS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQ7XG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXG5cdFx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJNZXRob2RUeXBlKG1lbWJlciwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBIYW5kbGUgZ2V0dGVyIGRlY2xhcmF0aW9uc1xuXHRcdFx0XHRpZiAodHMuaXNHZXRBY2Nlc3NvcihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBnZXR0ZXJzXG5cdFx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0XHRcdG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkO1xuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblxuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdC8vIEZpcnN0IHRyeSBleHBsaWNpdCB0eXBlIGFubm90YXRpb24sIHRoZW4gaW5mZXIgZnJvbSBnZXR0ZXIgYm9keVxuXHRcdFx0XHRcdGxldCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdGlmICh0eXBlID09PSAndW5rbm93bicgJiYgbWVtYmVyLmJvZHkpIHtcblx0XHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyUmV0dXJuVHlwZUZyb21Cb2R5KG1lbWJlci5ib2R5LCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0XHRyZWFkb25seSA6IHRydWUsXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdC8qKlxuXHQgKiBCdWlsZCBhIHR5cGUgbWFwIGZyb20gYWxsIHBhcmFtZXRlcnMgd2l0aCBpbmxpbmUgb2JqZWN0IHR5cGUgYW5ub3RhdGlvbnNcblx0ICogUmV0dXJucyBhIG1hcCBvZiBcInBhcmFtTmFtZS5wcm9wZXJ0eU5hbWVcIiAtPiB0eXBlXG5cdCAqL1xuXHRwcml2YXRlIGJ1aWxkRGF0YVR5cGVNYXAgKGhhbmRsZXJBcmc6IHRzLkV4cHJlc3Npb24pOiBNYXA8c3RyaW5nLCBzdHJpbmc+IHtcblx0XHRjb25zdCB0eXBlTWFwID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblxuXHRcdGlmICghdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oaGFuZGxlckFyZykgJiYgIXRzLmlzQXJyb3dGdW5jdGlvbihoYW5kbGVyQXJnKSkge1xuXHRcdFx0cmV0dXJuIHR5cGVNYXA7XG5cdFx0fVxuXG5cdFx0Ly8gSXRlcmF0ZSBvdmVyIEFMTCBwYXJhbWV0ZXJzXG5cdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBoYW5kbGVyQXJnLnBhcmFtZXRlcnMpIHtcblx0XHRcdGlmICghcGFyYW0ubmFtZSB8fCAhcGFyYW0udHlwZSkgY29udGludWU7XG5cblx0XHRcdC8vIEdldCBwYXJhbWV0ZXIgbmFtZVxuXHRcdFx0bGV0IHBhcmFtTmFtZSA9ICcnO1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSkge1xuXHRcdFx0XHRwYXJhbU5hbWUgPSBwYXJhbS5uYW1lLnRleHQ7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRjb250aW51ZTsgLy8gU2tpcCBkZXN0cnVjdHVyZWQgcGFyYW1ldGVycyBmb3Igbm93XG5cdFx0XHR9XG5cblx0XHRcdC8vIENoZWNrIGlmIGl0J3MgYW4gaW5saW5lIG9iamVjdCB0eXBlIGxpdGVyYWxcblx0XHRcdGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZShwYXJhbS50eXBlKSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBwYXJhbS50eXBlLm1lbWJlcnMpIHtcblx0XHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0XHR0eXBlTWFwLnNldChgJHtwYXJhbU5hbWV9LiR7cHJvcE5hbWV9YCwgdHlwZSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHQvLyBTdG9yZSBzaW1wbGUgcGFyYW1ldGVyIHR5cGVzIGxpa2UgYGRlY29yYXRlVmFsdWU6IHN0cmluZ2Bcblx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKHBhcmFtLnR5cGUpO1xuXHRcdFx0XHRpZiAodHlwZSAhPT0gJ3Vua25vd24nKSB7XG5cdFx0XHRcdFx0dHlwZU1hcC5zZXQocGFyYW1OYW1lLCB0eXBlKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB0eXBlTWFwO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydHkgYWNjZXNzIGNoYWluIChlLmcuLCBcImRhdGFSZW5hbWVkLmlkXCIgZnJvbSBkYXRhUmVuYW1lZC5pZClcblx0ICogSGFuZGxlcyBmYWxsYmFja3MgbGlrZTogZGF0YS5wZXJtaXNzaW9ucyB8fCBbXVxuXHQgKi9cblx0cHJpdmF0ZSBnZXRQcm9wZXJ0eUFjY2Vzc0NoYWluIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBIYW5kbGUgaWRlbnRpZmllcjogZGF0YVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLnRleHQ7XG5cdFx0fVxuXHRcdC8vIEhhbmRsZSBwcm9wZXJ0eSBhY2Nlc3M6IGRhdGEucGVybWlzc2lvbnNcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdGNvbnN0IGJhc2UgPSB0aGlzLmdldFByb3BlcnR5QWNjZXNzQ2hhaW4oZXhwci5leHByZXNzaW9uKTtcblx0XHRcdGlmIChiYXNlKSB7XG5cdFx0XHRcdHJldHVybiBgJHtiYXNlfS4ke2V4cHIubmFtZS50ZXh0fWA7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdC8vIEhhbmRsZSBmYWxsYmFjayBwYXR0ZXJuOiBkYXRhLnBlcm1pc3Npb25zIHx8IFtdXG5cdFx0aWYgKHRzLmlzQmluYXJ5RXhwcmVzc2lvbihleHByKSAmJlxuXHRcdFx0ZXhwci5vcGVyYXRvclRva2VuLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuQmFyQmFyVG9rZW4pIHtcblx0XHRcdC8vIFJldHVybiB0aGUgbGVmdCBzaWRlIG9mIHx8IG9wZXJhdG9yXG5cdFx0XHRyZXR1cm4gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGV4cHIubGVmdCk7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0eSBhc3NpZ25tZW50IGZyb20gc3RhdGVtZW50XG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RQcm9wZXJ0eUZyb21TdGF0ZW1lbnQgKFxuXHRcdGV4cHI6IHRzLkV4cHJlc3Npb24sXG5cdFx0cHJvcGVydGllczogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPixcblx0XHRkYXRhVHlwZU1hcDogTWFwPHN0cmluZywgc3RyaW5nPiA9IG5ldyBNYXAoKVxuXHQpOiB2b2lkIHtcblx0XHQvLyBIYW5kbGU6IHRoaXMucHJvcGVydHkgPSB2YWx1ZVxuXHRcdGlmICh0cy5pc0JpbmFyeUV4cHJlc3Npb24oZXhwcikgJiZcblx0XHRcdGV4cHIub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkVxdWFsc1Rva2VuKSB7XG5cdFx0XHRjb25zdCB7IGxlZnQgfSA9IGV4cHI7XG5cblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihsZWZ0KSkge1xuXHRcdFx0XHQvLyBDaGVjayBpZiBhY2Nlc3NpbmcgJ3RoaXMnIChUaGlzS2V5d29yZClcblx0XHRcdFx0aWYgKGxlZnQuZXhwcmVzc2lvbi5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uc3QgbmFtZSA9IGxlZnQubmFtZT8udGV4dDtcblx0XHRcdFx0XHRpZiAobmFtZSkge1xuXHRcdFx0XHRcdFx0Ly8gVHJ5IHRvIGdldCB0eXBlIGZyb20gZGF0YVR5cGVNYXAgdXNpbmcgZnVsbCBhY2Nlc3MgY2hhaW4gKGUuZy4sIFwiZGF0YVJlbmFtZWQuaWRcIilcblx0XHRcdFx0XHRcdGNvbnN0IGFjY2Vzc0NoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGV4cHIucmlnaHQpO1xuXHRcdFx0XHRcdFx0bGV0IHR5cGUgPSBhY2Nlc3NDaGFpbiA/IGRhdGFUeXBlTWFwLmdldChhY2Nlc3NDaGFpbikgOiB1bmRlZmluZWQ7XG5cdFx0XHRcdFx0XHQvLyBJZiBub3QgZm91bmQgYW5kIFJIUyBpcyBhIHNpbXBsZSBpZGVudGlmaWVyLCB0cnkgbG9va2luZyBpdCB1cCBkaXJlY3RseVxuXHRcdFx0XHRcdFx0aWYgKCF0eXBlICYmIHRzLmlzSWRlbnRpZmllcihleHByLnJpZ2h0KSkge1xuXHRcdFx0XHRcdFx0XHR0eXBlID0gZGF0YVR5cGVNYXAuZ2V0KGV4cHIucmlnaHQudGV4dCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRpZiAoIXR5cGUpIHtcblx0XHRcdFx0XHRcdFx0dHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKGV4cHIucmlnaHQsIGRhdGFUeXBlTWFwKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdC8vIERvbid0IG92ZXJ3cml0ZSBhIGtub3duIHR5cGUgZnJvbSBhIGB0aGlzYCBhbm5vdGF0aW9uXG5cdFx0XHRcdFx0XHQvLyB3aXRoIGFuIHVua25vd24tYmVhcmluZyBpbmZlcmVuY2U6IGFuIGVtcHR5LWFycmF5XG5cdFx0XHRcdFx0XHQvLyBpbml0aWFsaXplciBpbmZlcnMgJ0FycmF5PHVua25vd24+Jywgd2hpY2ggbXVzdCBub3Rcblx0XHRcdFx0XHRcdC8vIGNsb2JiZXIgYW4gYW5ub3RhdGVkICdBcnJheTx7IGlkOiBudW1iZXIgfT4nIGVpdGhlclxuXHRcdFx0XHRcdFx0Y29uc3QgZXhpc3RpbmcgPSBwcm9wZXJ0aWVzLmdldChuYW1lKTtcblx0XHRcdFx0XHRcdGNvbnN0IHR5cGVIYXNVbmtub3duID0gIXR5cGUgfHwgdHlwZS5pbmNsdWRlcygndW5rbm93bicpO1xuXHRcdFx0XHRcdFx0Y29uc3QgZXhpc3RpbmdJc0tub3duID0gZXhpc3RpbmcgPyAhZXhpc3RpbmcudHlwZS5pbmNsdWRlcygndW5rbm93bicpIDogZmFsc2U7XG5cdFx0XHRcdFx0XHRpZiAoZXhpc3RpbmdJc0tub3duICYmIHR5cGVIYXNVbmtub3duKSB7XG5cdFx0XHRcdFx0XHRcdC8vIEtlZXAgdGhlIGJldHRlciB0eXBlIGZyb20gZXhwbGljaXQgYW5ub3RhdGlvblxuXHRcdFx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBIYW5kbGU6IE9iamVjdC5hc3NpZ24odGhpcywgeyBwcm9wOiB2YWx1ZSB9KVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBmbiA9IGV4cHIuZXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihmbikgJiZcblx0XHRcdFx0Zm4ubmFtZT8udGV4dCA9PT0gJ2Fzc2lnbicgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGZuLmV4cHJlc3Npb24pICYmXG5cdFx0XHRcdGZuLmV4cHJlc3Npb24udGV4dCA9PT0gJ09iamVjdCcpIHtcblx0XHRcdFx0Y29uc3QgYXJncyA9IGV4cHIuYXJndW1lbnRzO1xuXHRcdFx0XHRpZiAoYXJncy5sZW5ndGggPj0gMiAmJiBhcmdzWyAwIF0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIHRoZSBzZWNvbmQgYXJndW1lbnRcblx0XHRcdFx0XHRjb25zdCBwcm9wc0FyZyA9IGFyZ3NbIDEgXTtcblx0XHRcdFx0XHRpZiAodHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihwcm9wc0FyZykpIHtcblx0XHRcdFx0XHRcdGZvciAoY29uc3QgcHJvcCBvZiBwcm9wc0FyZy5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSAmJiB0cy5pc0lkZW50aWZpZXIocHJvcC5uYW1lKSkge1xuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBwcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0XHRcdFx0dHlwZSAgICAgOiB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihwcm9wLmluaXRpYWxpemVyKSxcblx0XHRcdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gY2xhc3MgZGVjbGFyYXRpb24gKGluY2x1ZGluZyBtZXRob2RzIGFuZCBnZXR0ZXJzKVxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q2xhc3NQcm9wZXJ0aWVzIChjbGFzc0RlY2w6IHRzLkNsYXNzRGVjbGFyYXRpb24pOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCBwcm9wZXJ0aWVzID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblxuXHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGNsYXNzRGVjbC5tZW1iZXJzKSB7XG5cdFx0XHQvLyBIYW5kbGUgcHJvcGVydHkgZGVjbGFyYXRpb25zXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eURlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUpIHtcblx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgcHJvcGVydGllc1xuXHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0ICAgICBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZCk7XG5cdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Y29uc3QgbmFtZSA9IHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkgPyBtZW1iZXIubmFtZS50ZXh0IDogJyc7XG5cdFx0XHRcdGlmIChuYW1lKSB7XG5cdFx0XHRcdFx0Ly8gSWYgbm8gZXhwbGljaXQgdHlwZSBidXQgaGFzIGluaXRpYWxpemVyLCBpbmZlciBmcm9tIGluaXRpYWxpemVyXG5cdFx0XHRcdFx0bGV0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0aWYgKHR5cGUgPT09ICd1bmtub3duJyAmJiBtZW1iZXIuaW5pdGlhbGl6ZXIpIHtcblx0XHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihtZW1iZXIuaW5pdGlhbGl6ZXIpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdG9wdGlvbmFsIDogISFtZW1iZXIucXVlc3Rpb25Ub2tlbixcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHQvLyBIYW5kbGUgbWV0aG9kIGRlY2xhcmF0aW9uc1xuXHRcdFx0aWYgKHRzLmlzTWV0aG9kRGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIG1ldGhvZHNcblx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdCAgICAgbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQpO1xuXHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlck1ldGhvZFR5cGUobWVtYmVyKTtcblx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gSGFuZGxlIGdldHRlciBkZWNsYXJhdGlvbnNcblx0XHRcdGlmICh0cy5pc0dldEFjY2Vzc29yKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBnZXR0ZXJzXG5cdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHQgICAgIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkKTtcblx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0Ly8gRmlyc3QgdHJ5IGV4cGxpY2l0IHR5cGUgYW5ub3RhdGlvbiwgdGhlbiBpbmZlciBmcm9tIGdldHRlciBib2R5XG5cdFx0XHRcdGxldCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRpZiAodHlwZSA9PT0gJ3Vua25vd24nICYmIG1lbWJlci5ib2R5KSB7XG5cdFx0XHRcdFx0dHlwZSA9IHRoaXMuaW5mZXJSZXR1cm5UeXBlRnJvbUJvZHkobWVtYmVyLmJvZHkpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRyZWFkb25seSA6IHRydWUsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBwcm9wZXJ0aWVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgY2xhc3MgcHJvcGVydHkgdHlwZXMgZm9yIG1ldGhvZCByZXR1cm4gdHlwZSBpbmZlcmVuY2Vcblx0ICogTWFwcyBwcm9wZXJ0eSBuYW1lcyB0byB0aGVpciBUeXBlU2NyaXB0IHR5cGUgc3RyaW5nc1xuXHQgKiBOb3RlOiBJbmNsdWRlcyBwcml2YXRlL3Byb3RlY3RlZCBwcm9wZXJ0aWVzIGZvciBtZXRob2QgaW5mZXJlbmNlXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDbGFzc1Byb3BlcnR5VHlwZXMgKGNsYXNzRGVjbDogdHMuQ2xhc3NFeHByZXNzaW9uKTogTWFwPHN0cmluZywgc3RyaW5nPiB7XG5cdFx0Y29uc3QgcHJvcGVydHlUeXBlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjbGFzc0RlY2wubWVtYmVycykge1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlEZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Ly8gSW5jbHVkZSBBTEwgcHJvcGVydGllcyAoZXZlbiBwcml2YXRlKSBmb3IgbWV0aG9kIHJldHVybiB0eXBlIGluZmVyZW5jZVxuXHRcdFx0XHQvLyBUaGUgdmlzaWJpbGl0eSBjaGVjayBpcyBkb25lIHdoZW4gYWRkaW5nIHRvIG91dHB1dCBwcm9wZXJ0aWVzXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRpZiAobWVtYmVyLnR5cGUpIHtcblx0XHRcdFx0XHRwcm9wZXJ0eVR5cGVzLnNldChuYW1lLCB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSkpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnR5VHlwZXM7XG5cdH1cblxuXHQvKipcblx0ICogSW5mZXIgbWV0aG9kIHR5cGUgZnJvbSBtZXRob2QgZGVjbGFyYXRpb25cblx0ICovXG5cdHByaXZhdGUgaW5mZXJNZXRob2RUeXBlIChtZXRob2Q6IHRzLk1ldGhvZERlY2xhcmF0aW9uLCBjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+KTogc3RyaW5nIHtcblx0XHRjb25zdCBwYXJhbXMgPSBtZXRob2QucGFyYW1ldGVycy5tYXAocGFyYW0gPT4ge1xuXHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpID8gcGFyYW0ubmFtZS50ZXh0IDogJ2FyZyc7XG5cdFx0XHRjb25zdCBwYXJhbVR5cGUgPSB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblx0XHRcdHJldHVybiBgJHtwYXJhbU5hbWV9OiAke3BhcmFtVHlwZX1gO1xuXHRcdH0pLmpvaW4oJywgJyk7XG5cblx0XHRjb25zdCByZXR1cm5UeXBlID0gdGhpcy5pbmZlclJldHVyblR5cGUobWV0aG9kLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXG5cdFx0aWYgKHBhcmFtcykge1xuXHRcdFx0cmV0dXJuIGAoJHtwYXJhbXN9KSA9PiAke3JldHVyblR5cGV9YDtcblx0XHR9XG5cdFx0cmV0dXJuIGAoKSA9PiAke3JldHVyblR5cGV9YDtcblx0fVxuXG5cdC8qKlxuXHRcdCogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gYHRoaXNgIHBhcmFtZXRlciB0eXBlIGFubm90YXRpb25cblx0XHQqIEhhbmRsZXMgcGF0dGVybnMgbGlrZTogZnVuY3Rpb24odGhpczogU29tZVR5cGUsIGRhdGE6IFNvbWVUeXBlKSB7IH1cblx0XHQqL1xuXHRwcml2YXRlIGV4dHJhY3RUaGlzUGFyYW1Qcm9wZXJ0aWVzIChoYW5kbGVyQXJnOiB0cy5GdW5jdGlvbkV4cHJlc3Npb24gfCB0cy5BcnJvd0Z1bmN0aW9uKTpcblx0XHRNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCBwcm9wZXJ0aWVzID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblxuXHRcdC8vIEZpbmQgdGhlIGB0aGlzYCBwYXJhbWV0ZXIgKGlmIGFueSlcblx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGhhbmRsZXJBcmcucGFyYW1ldGVycykge1xuXHRcdFx0aWYgKHBhcmFtLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpICYmIHBhcmFtLm5hbWUudGV4dCA9PT0gJ3RoaXMnICYmIHBhcmFtLnR5cGUpIHtcblx0XHRcdFx0Ly8gQ2hlY2sgaWYgaXQncyBhIHR5cGUgcmVmZXJlbmNlIChlLmcuLCBgdGhpczogdXNhZ2VgKVxuXHRcdFx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZShwYXJhbS50eXBlKSkge1xuXHRcdFx0XHRcdGNvbnN0IHR5cGVOYW1lID0gdHMuaXNJZGVudGlmaWVyKHBhcmFtLnR5cGUudHlwZU5hbWUpXG5cdFx0XHRcdFx0XHQ/IHBhcmFtLnR5cGUudHlwZU5hbWUudGV4dFxuXHRcdFx0XHRcdFx0OiAnJztcblxuXHRcdFx0XHRcdC8vIExvb2sgdXAgdGhlIHR5cGUgYWxpYXMgaW4gb3VyIGNvbGxlY3RlZCB0eXBlIGFsaWFzZXNcblx0XHRcdFx0XHRjb25zdCBhbGlhc2VkVHlwZSA9IHRoaXMudHlwZUFsaWFzZXMuZ2V0KHR5cGVOYW1lKTtcblx0XHRcdFx0XHRpZiAoYWxpYXNlZFR5cGUgJiYgdHMuaXNUeXBlTGl0ZXJhbE5vZGUoYWxpYXNlZFR5cGUpKSB7XG5cdFx0XHRcdFx0XHQvLyBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSB0aGUgdHlwZSBsaXRlcmFsXG5cdFx0XHRcdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBhbGlhc2VkVHlwZS5tZW1iZXJzKSB7XG5cdFx0XHRcdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KHByb3BOYW1lLCB7XG5cdFx0XHRcdFx0XHRcdFx0XHRuYW1lICAgICA6IHByb3BOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogISFtZW1iZXIucXVlc3Rpb25Ub2tlbixcblx0XHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBDaGVjayBpZiBpdCdzIGRpcmVjdGx5IGFuIGlubGluZSB0eXBlIGxpdGVyYWwgKGUuZy4sIGB0aGlzOiB7IGlkOiBzdHJpbmcgfWApXG5cdFx0XHRcdGVsc2UgaWYgKHRzLmlzVHlwZUxpdGVyYWxOb2RlKHBhcmFtLnR5cGUpKSB7XG5cdFx0XHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgcGFyYW0udHlwZS5tZW1iZXJzKSB7XG5cdFx0XHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChwcm9wTmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdG5hbWUgICAgIDogcHJvcE5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHRicmVhazsgLy8gRm91bmQgdGhlIGB0aGlzYCBwYXJhbWV0ZXIsIG5vIG5lZWQgdG8gY29udGludWVcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdC8qKlxuXHRcdCogSW5mZXIgVHlwZVNjcmlwdCB0eXBlIGZyb20gdHlwZSBub2RlXG5cdFx0Ki9cblx0LyoqXG5cdCAqIEluZmVyIFR5cGVTY3JpcHQgdHlwZSBmcm9tIHR5cGUgbm9kZVxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlclR5cGUgKHR5cGVOb2RlPzogdHMuVHlwZU5vZGUpOiBzdHJpbmcge1xuXHRcdGlmICghdHlwZU5vZGUpIHtcblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXG5cdFx0c3dpdGNoICh0eXBlTm9kZS5raW5kKSB7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlN0cmluZ0tleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bWJlcktleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkJvb2xlYW5LZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5kZWZpbmVkS2V5d29yZDpcblx0XHRcdHJldHVybiAndW5kZWZpbmVkJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bGwnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5BbnlLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdhbnknO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Vbmtub3duS2V5d29yZDpcblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlZvaWRLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICd2b2lkJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQXJyYXlUeXBlOlxuXHRcdFx0cmV0dXJuIGBBcnJheTwkeyAgdGhpcy5pbmZlclR5cGUoKHR5cGVOb2RlIGFzIHRzLkFycmF5VHlwZU5vZGUpLmVsZW1lbnRUeXBlKSAgfT5gO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlTGl0ZXJhbDoge1xuXHRcdFx0Ly8gSW5saW5lLWV4cGFuZCB0eXBlIGxpdGVyYWxzIGluc3RlYWQgb2YgY29sbGFwc2luZyB0byAnb2JqZWN0J1xuXHRcdFx0Y29uc3QgdHlwZUxpdCA9IHR5cGVOb2RlIGFzIHRzLlR5cGVMaXRlcmFsTm9kZTtcblx0XHRcdGNvbnN0IHByb3BzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgdHlwZUxpdC5tZW1iZXJzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRjb25zdCBvcHRpb25hbCA9IG1lbWJlci5xdWVzdGlvblRva2VuID8gJz8nIDogJyc7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRwcm9wcy5wdXNoKGAke3Byb3BOYW1lfSR7b3B0aW9uYWx9OiAke3R5cGV9YCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiBgeyAke3Byb3BzLmpvaW4oJzsgJyl9IH1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTGl0ZXJhbFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBzdHJpbmcgbGl0ZXJhbCB0eXBlcyBsaWtlICd1c2VyJywgJ2FkbWluJywgZXRjLlxuXHRcdFx0Y29uc3QgeyBsaXRlcmFsIH0gPSAodHlwZU5vZGUgYXMgdHMuTGl0ZXJhbFR5cGVOb2RlKTtcblx0XHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwobGl0ZXJhbCkpIHtcblx0XHRcdFx0Ly8gUmV0dXJuIHRoZSBhY3R1YWwgbGl0ZXJhbCB2YWx1ZSAoZS5nLiwgJ3VzZXInIGluc3RlYWQgb2Ygc3RyaW5nKVxuXHRcdFx0XHRyZXR1cm4gYCcke2xpdGVyYWwudGV4dH0nYDtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc051bWVyaWNMaXRlcmFsKGxpdGVyYWwpKSB7XG5cdFx0XHRcdHJldHVybiBsaXRlcmFsLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAobGl0ZXJhbC5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdHJldHVybiAndHJ1ZSc7XG5cdFx0XHR9XG5cdFx0XHRpZiAobGl0ZXJhbC5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRyZXR1cm4gJ2ZhbHNlJztcblx0XHRcdH1cblx0XHRcdGlmIChsaXRlcmFsLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQpIHtcblx0XHRcdFx0cmV0dXJuICdudWxsJztcblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlUmVmZXJlbmNlOiB7XG5cdFx0XHQvLyBIYW5kbGUgdHlwZSByZWZlcmVuY2VzIGxpa2UgTWFwPHN0cmluZywgbnVtYmVyPiwgUHJvcGVydHlJbmZvLCBldGMuXG5cdFx0XHRjb25zdCB0eXBlUmVmID0gdHlwZU5vZGUgYXMgdHMuVHlwZVJlZmVyZW5jZU5vZGU7XG5cdFx0XHRjb25zdCB0eXBlTmFtZSA9IHRzLmlzSWRlbnRpZmllcih0eXBlUmVmLnR5cGVOYW1lKVxuXHRcdFx0XHQ/IHR5cGVSZWYudHlwZU5hbWUudGV4dFxuXHRcdFx0XHQ6IHRzLmlzUXVhbGlmaWVkTmFtZSh0eXBlUmVmLnR5cGVOYW1lKVxuXHRcdFx0XHRcdD8gdGhpcy5nZXRRdWFsaWZpZWROYW1lVGV4dCh0eXBlUmVmLnR5cGVOYW1lKVxuXHRcdFx0XHRcdDogJ3Vua25vd24nO1xuXG5cdFx0XHQvLyBDaGVjayBpZiB0aGlzIGlzIGEgdHlwZSBhbGlhcyB3ZSBjYW4gcmVzb2x2ZVxuXHRcdFx0Y29uc3QgYWxpYXNlZFR5cGUgPSB0aGlzLnR5cGVBbGlhc2VzLmdldCh0eXBlTmFtZSk7XG5cdFx0XHRpZiAoYWxpYXNlZFR5cGUpIHtcblx0XHRcdFx0Ly8gUmVzb2x2ZSB0aGUgdHlwZSBhbGlhc1xuXHRcdFx0XHRyZXR1cm4gdGhpcy5pbmZlclR5cGUoYWxpYXNlZFR5cGUpO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBIYW5kbGUgSW5zdGFuY2VUeXBlPHR5cGVvZiBYPiBwYXR0ZXJuIC0+IGNvbnZlcnQgdG8gUGFyZW50X1hcblx0XHRcdGlmICh0eXBlTmFtZSA9PT0gJ0luc3RhbmNlVHlwZScgJiYgdHlwZVJlZi50eXBlQXJndW1lbnRzICYmIHR5cGVSZWYudHlwZUFyZ3VtZW50cy5sZW5ndGggPT09IDEpIHtcblx0XHRcdFx0Y29uc3QgYXJnID0gdHlwZVJlZi50eXBlQXJndW1lbnRzWyAwIF07XG5cdFx0XHRcdGlmIChhcmcua2luZCA9PT0gdHMuU3ludGF4S2luZC5UeXBlUXVlcnkpIHtcblx0XHRcdFx0XHRjb25zdCB0eXBlUXVlcnkgPSBhcmcgYXMgdHMuVHlwZVF1ZXJ5Tm9kZTtcblx0XHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKHR5cGVRdWVyeS5leHByTmFtZSkpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHF1ZXJ5VHlwZU5hbWUgPSB0eXBlUXVlcnkuZXhwck5hbWUudGV4dDtcblx0XHRcdFx0XHRcdC8vIExvb2sgdXAgdGhlIHR5cGUgaW4gdGhlIGdyYXBoIHRvIGdldCBmdWxsIHBhdGhcblx0XHRcdFx0XHRcdGNvbnN0IG1hdGNoZWRUeXBlID0gdGhpcy5ncmFwaC5maW5kVHlwZUJ5TmFtZShxdWVyeVR5cGVOYW1lKTtcblx0XHRcdFx0XHRcdGlmIChtYXRjaGVkVHlwZSkge1xuXHRcdFx0XHRcdFx0XHQvLyBDb252ZXJ0IGZ1bGwgcGF0aCB3aXRoIGRvdHMgdG8gdW5kZXJzY29yZXM6IFVzYWdlcy5Vc2FnZUVudHJ5IC0+IFVzYWdlc19Vc2FnZUVudHJ5XG5cdFx0XHRcdFx0XHRcdHJldHVybiBtYXRjaGVkVHlwZS5mdWxsUGF0aC5yZXBsYWNlKC9cXC4vZywgJ18nKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdC8vIEZhbGxiYWNrOiBqdXN0IHVzZSB0aGUgdHlwZSBuYW1lIGlmIG5vdCBmb3VuZCBpbiBncmFwaFxuXHRcdFx0XHRcdFx0cmV0dXJuIHF1ZXJ5VHlwZU5hbWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdGlmICghdHlwZVJlZi50eXBlQXJndW1lbnRzIHx8IHR5cGVSZWYudHlwZUFyZ3VtZW50cy5sZW5ndGggPT09IDApIHtcblx0XHRcdFx0Ly8gQ2hlY2sgaWYgdGhpcyB0eXBlIGV4aXN0cyBpbiBvdXIgZ3JhcGggLSBjb252ZXJ0IHRvIGZ1bGwgcGF0aCBmb3JtYXRcblx0XHRcdFx0Y29uc3QgbWF0Y2hlZFR5cGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlQnlOYW1lKHR5cGVOYW1lKTtcblx0XHRcdFx0aWYgKG1hdGNoZWRUeXBlKSB7XG5cdFx0XHRcdFx0Ly8gQ29udmVydCBmdWxsIHBhdGggd2l0aCBkb3RzIHRvIHVuZGVyc2NvcmVzOiBVc2FnZXMuVXNhZ2VFbnRyeSAtPiBVc2FnZXNfVXNhZ2VFbnRyeVxuXHRcdFx0XHRcdHJldHVybiBtYXRjaGVkVHlwZS5mdWxsUGF0aC5yZXBsYWNlKC9cXC4vZywgJ18nKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gdHlwZU5hbWU7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEJ1aWxkIGdlbmVyaWMgdHlwZSBhcmd1bWVudHNcblx0XHRcdGNvbnN0IHR5cGVBcmdzID0gdHlwZVJlZi50eXBlQXJndW1lbnRzLm1hcChhcmcgPT4gdGhpcy5pbmZlclR5cGUoYXJnKSk7XG5cdFx0XHRyZXR1cm4gYCR7dHlwZU5hbWV9PCR7dHlwZUFyZ3Muam9pbignLCAnKX0+YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVuaW9uVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHVuaW9uIHR5cGVzIGxpa2UgJ2EnIHwgJ2InIHwgJ2MnXG5cdFx0XHRjb25zdCB1bmlvblR5cGUgPSB0eXBlTm9kZSBhcyB0cy5VbmlvblR5cGVOb2RlO1xuXHRcdFx0Y29uc3QgdHlwZXMgPSB1bmlvblR5cGUudHlwZXMubWFwKHQgPT4gdGhpcy5pbmZlclR5cGUodCkpO1xuXHRcdFx0cmV0dXJuIHR5cGVzLmpvaW4oJyB8ICcpO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuSW50ZXJzZWN0aW9uVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIGludGVyc2VjdGlvbiB0eXBlcyBsaWtlIFR5cGVBICYgVHlwZUJcblx0XHRcdGNvbnN0IGludGVyc2VjdGlvblR5cGUgPSB0eXBlTm9kZSBhcyB0cy5JbnRlcnNlY3Rpb25UeXBlTm9kZTtcblx0XHRcdGNvbnN0IHR5cGVzID0gaW50ZXJzZWN0aW9uVHlwZS50eXBlcy5tYXAodCA9PiB0aGlzLmluZmVyVHlwZSh0KSk7XG5cdFx0XHRyZXR1cm4gdHlwZXMuam9pbignICYgJyk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UdXBsZVR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSB0dXBsZSB0eXBlcyBsaWtlIFtzdHJpbmcsIG51bWJlcl1cblx0XHRcdGNvbnN0IHR1cGxlVHlwZSA9IHR5cGVOb2RlIGFzIHRzLlR1cGxlVHlwZU5vZGU7XG5cdFx0XHRjb25zdCBlbGVtZW50cyA9IHR1cGxlVHlwZS5lbGVtZW50cy5tYXAoZWxlbSA9PiB0aGlzLmluZmVyVHlwZShlbGVtIGFzIHRzLlR5cGVOb2RlKSk7XG5cdFx0XHRyZXR1cm4gYFske2VsZW1lbnRzLmpvaW4oJywgJyl9XWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5PcHRpb25hbFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBvcHRpb25hbCBlbGVtZW50IGluIHR1cGxlOiBzdHJpbmc/XG5cdFx0XHRjb25zdCBvcHRpb25hbFR5cGUgPSB0eXBlTm9kZSBhcyB0cy5PcHRpb25hbFR5cGVOb2RlO1xuXHRcdFx0cmV0dXJuIGAke3RoaXMuaW5mZXJUeXBlKG9wdGlvbmFsVHlwZS50eXBlKSAgfT9gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuUmVzdFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSByZXN0IGVsZW1lbnQ6IC4uLlRcblx0XHRcdGNvbnN0IHJlc3RUeXBlID0gdHlwZU5vZGUgYXMgdHMuUmVzdFR5cGVOb2RlO1xuXHRcdFx0cmV0dXJuIGAuLi4keyAgdGhpcy5pbmZlclR5cGUocmVzdFR5cGUudHlwZSl9YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlBhcmVudGhlc2l6ZWRUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgcGFyZW50aGVzaXplZCB0eXBlczogKEEgfCBCKVxuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJUeXBlKCh0eXBlTm9kZSBhcyB0cy5QYXJlbnRoZXNpemVkVHlwZU5vZGUpLnR5cGUpO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuSW5kZXhlZEFjY2Vzc1R5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBpbmRleGVkIGFjY2VzczogVFtLXVxuXHRcdFx0Y29uc3QgaW5kZXhlZCA9IHR5cGVOb2RlIGFzIHRzLkluZGV4ZWRBY2Nlc3NUeXBlTm9kZTtcblx0XHRcdGxldCBvYmplY3RUeXBlID0gdGhpcy5pbmZlclR5cGUoaW5kZXhlZC5vYmplY3RUeXBlKTtcblx0XHRcdGNvbnN0IGluZGV4VHlwZSA9IHRoaXMuaW5mZXJUeXBlKGluZGV4ZWQuaW5kZXhUeXBlKTtcblx0XHRcdC8vIElmIG9iamVjdFR5cGUgaXMgJ29iamVjdCcsIHRyeSB0byByZXNvbHZlIHRoZSB1bmRlcmx5aW5nIHR5cGUgYWxpYXNcblx0XHRcdGlmIChvYmplY3RUeXBlID09PSAnb2JqZWN0JyAmJiB0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKGluZGV4ZWQub2JqZWN0VHlwZSkpIHtcblx0XHRcdFx0Y29uc3QgcmVmTmFtZSA9IHRzLmlzSWRlbnRpZmllcihpbmRleGVkLm9iamVjdFR5cGUudHlwZU5hbWUpID8gaW5kZXhlZC5vYmplY3RUeXBlLnR5cGVOYW1lLnRleHQgOiAnJztcblx0XHRcdFx0Y29uc3QgYWxpYXNlZCA9IHRoaXMudHlwZUFsaWFzZXMuZ2V0KHJlZk5hbWUpO1xuXHRcdFx0XHRpZiAoYWxpYXNlZCkge1xuXHRcdFx0XHRcdG9iamVjdFR5cGUgPSB0aGlzLmluZmVyVHlwZShhbGlhc2VkKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGAke29iamVjdFR5cGV9WyR7aW5kZXhUeXBlfV1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZU9wZXJhdG9yOiB7XG5cdFx0XHQvLyBIYW5kbGUga2V5b2YsIHJlYWRvbmx5LCB1bmlxdWUgb3BlcmF0b3JzXG5cdFx0XHRjb25zdCB0eXBlT3AgPSB0eXBlTm9kZSBhcyB0cy5UeXBlT3BlcmF0b3JOb2RlO1xuXHRcdFx0Y29uc3Qgb3BlcmF0b3IgPSB0cy5TeW50YXhLaW5kWyB0eXBlT3Aub3BlcmF0b3IgXTtcblx0XHRcdHJldHVybiBgJHtvcGVyYXRvcn0gJHt0aGlzLmluZmVyVHlwZSh0eXBlT3AudHlwZSl9YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR5cGVRdWVyeToge1xuXHRcdFx0Ly8gSGFuZGxlIHR5cGVvZiBleHByZXNzaW9ucyBsaWtlIGB0eXBlb2YgVXNhZ2VFbnRyeWBcblx0XHRcdGNvbnN0IHR5cGVRdWVyeSA9IHR5cGVOb2RlIGFzIHRzLlR5cGVRdWVyeU5vZGU7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKHR5cGVRdWVyeS5leHByTmFtZSkpIHtcblx0XHRcdFx0cmV0dXJuIGB0eXBlb2YgJHt0eXBlUXVlcnkuZXhwck5hbWUudGV4dH1gO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0ZGVmYXVsdDpcblx0XHRcdC8vIEZvciBjb21wbGV4IHR5cGVzLCByZXR1cm4gdGhlIHRleHQgcmVwcmVzZW50YXRpb25cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdFx0KiBJbmZlciByZXR1cm4gdHlwZSBmcm9tIGEgbWV0aG9kIGRlY2xhcmF0aW9uXG5cdFx0KiBVc2VzIGV4cGxpY2l0IHJldHVybiB0eXBlIGFubm90YXRpb24gb3IgaW5mZXJzIGZyb20gcmV0dXJuIHN0YXRlbWVudHNcblx0XHQqL1xuXHRwcml2YXRlIGluZmVyUmV0dXJuVHlwZSAobWV0aG9kOiB0cy5NZXRob2REZWNsYXJhdGlvbiwgY2xhc3NQcm9wZXJ0eVR5cGVzPzogTWFwPHN0cmluZywgc3RyaW5nPik6IHN0cmluZyB7XG5cdFx0Ly8gSWYgbWV0aG9kIGhhcyBleHBsaWNpdCByZXR1cm4gdHlwZSBhbm5vdGF0aW9uLCB1c2UgaXRcblx0XHRpZiAobWV0aG9kLnR5cGUpIHtcblx0XHRcdHJldHVybiB0aGlzLmluZmVyVHlwZShtZXRob2QudHlwZSk7XG5cdFx0fVxuXG5cdFx0Ly8gT3RoZXJ3aXNlLCB0cnkgdG8gaW5mZXIgZnJvbSByZXR1cm4gc3RhdGVtZW50cyBpbiB0aGUgbWV0aG9kIGJvZHlcblx0XHRpZiAobWV0aG9kLmJvZHkpIHtcblx0XHRcdHJldHVybiB0aGlzLmluZmVyUmV0dXJuVHlwZUZyb21Cb2R5KG1ldGhvZC5ib2R5LCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdH1cblxuXHRcdHJldHVybiAndW5rbm93bic7XG5cdH1cblxuXHQvKipcblx0XHQqIEluZmVyIHJldHVybiB0eXBlIGJ5IGFuYWx5emluZyByZXR1cm4gc3RhdGVtZW50cyBpbiB0aGUgbWV0aG9kIGJvZHlcblx0XHQqL1xuXHRwcml2YXRlIGluZmVyUmV0dXJuVHlwZUZyb21Cb2R5IChib2R5OiB0cy5CbG9jaywgY2xhc3NQcm9wZXJ0eVR5cGVzPzogTWFwPHN0cmluZywgc3RyaW5nPik6IHN0cmluZyB7XG5cdFx0Y29uc3QgcmV0dXJuVHlwZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblxuXHRcdGNvbnN0IHZpc2l0ID0gKG5vZGU6IHRzLk5vZGUpOiB2b2lkID0+IHtcblx0XHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKG5vZGUuZXhwcmVzc2lvbiwgdW5kZWZpbmVkLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0XHRpZiAodHlwZSAhPT0gJ3Vua25vd24nKSB7XG5cdFx0XHRcdFx0cmV0dXJuVHlwZXMuYWRkKHR5cGUpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgdmlzaXQpO1xuXHRcdH07XG5cblx0XHR2aXNpdChib2R5KTtcblxuXHRcdGlmIChyZXR1cm5UeXBlcy5zaXplID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gJ3ZvaWQnO1xuXHRcdH1cblx0XHRpZiAocmV0dXJuVHlwZXMuc2l6ZSA9PT0gMSkge1xuXHRcdFx0cmV0dXJuIEFycmF5LmZyb20ocmV0dXJuVHlwZXMpWyAwIF07XG5cdFx0fVxuXHRcdHJldHVybiBBcnJheS5mcm9tKHJldHVyblR5cGVzKS5qb2luKCcgfCAnKTtcblx0fVxuXG5cdC8qKlxuXHRcdCogR2V0IGZ1bGwgdGV4dCBmcm9tIGEgcXVhbGlmaWVkIG5hbWUgKGUuZy4sIE5hbWVzcGFjZS5UeXBlKVxuXHRcdCovXG5cdHByaXZhdGUgZ2V0UXVhbGlmaWVkTmFtZVRleHQgKHF1YWxpZmllZE5hbWU6IHRzLlF1YWxpZmllZE5hbWUpOiBzdHJpbmcge1xuXHRcdGNvbnN0IHBhcnRzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGxldCBjdXJyZW50OiB0cy5RdWFsaWZpZWROYW1lIHwgdHMuSWRlbnRpZmllciA9IHF1YWxpZmllZE5hbWU7XG5cblx0XHR3aGlsZSAodHMuaXNRdWFsaWZpZWROYW1lKGN1cnJlbnQpKSB7XG5cdFx0XHRwYXJ0cy51bnNoaWZ0KGN1cnJlbnQucmlnaHQudGV4dCk7XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5sZWZ0O1xuXHRcdH1cblx0XHRwYXJ0cy51bnNoaWZ0KGN1cnJlbnQudGV4dCk7XG5cblx0XHRyZXR1cm4gcGFydHMuam9pbignLicpO1xuXHR9XG5cblx0LyoqXG5cdCAqIEluZmVyIHR5cGUgZnJvbSBpbml0aWFsaXplclxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIgKFxuXHRcdGluaXRpYWxpemVyOiB0cy5FeHByZXNzaW9uLFxuXHRcdGRhdGFUeXBlTWFwPzogTWFwPHN0cmluZywgc3RyaW5nPixcblx0XHRjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+XG5cdCk6IHN0cmluZyB7XG5cdFx0c3dpdGNoIChpbml0aWFsaXplci5raW5kKSB7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlN0cmluZ0xpdGVyYWw6XG5cdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bWVyaWNMaXRlcmFsOlxuXHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZDpcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bGwnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5VbmRlZmluZWRLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICd1bmRlZmluZWQnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5BcnJheUxpdGVyYWxFeHByZXNzaW9uOlxuXHRcdFx0cmV0dXJuICdBcnJheTx1bmtub3duPic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk9iamVjdExpdGVyYWxFeHByZXNzaW9uOlxuXHRcdFx0cmV0dXJuICdvYmplY3QnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OZXdFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgbmV3IERhdGUoKSwgbmV3IE1hcCgpLCBldGMuXG5cdFx0XHRjb25zdCBuZXdFeHByID0gaW5pdGlhbGl6ZXIgYXMgdHMuTmV3RXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIobmV3RXhwci5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRyZXR1cm4gbmV3RXhwci5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ29iamVjdCc7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5CaW5hcnlFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgYXJpdGhtZXRpYyBvcGVyYXRpb25zOiBhICogYiwgYSArIGIsIGEgLSBiLCBhIC8gYlxuXHRcdFx0Y29uc3QgYmluYXJ5RXhwciA9IGluaXRpYWxpemVyIGFzIHRzLkJpbmFyeUV4cHJlc3Npb247XG5cdFx0XHRjb25zdCBsZWZ0VHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKGJpbmFyeUV4cHIubGVmdCwgZGF0YVR5cGVNYXAsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRjb25zdCByaWdodFR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihiaW5hcnlFeHByLnJpZ2h0LCBkYXRhVHlwZU1hcCwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0XG5cdFx0XHQvLyBDaGVjayBpZiBpdCdzIGFuIGFyaXRobWV0aWMgb3BlcmF0b3Jcblx0XHRcdGNvbnN0IG9wZXJhdG9yID0gYmluYXJ5RXhwci5vcGVyYXRvclRva2VuLmtpbmQ7XG5cdFx0XHRpZiAob3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuQXN0ZXJpc2tUb2tlbiB8fFxuXHRcdFx0XHQgICAgb3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuU2xhc2hUb2tlbiB8fFxuXHRcdFx0XHQgICAgb3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuTWludXNUb2tlbiB8fFxuXHRcdFx0XHQgICAgb3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuUGVyY2VudFRva2VuKSB7XG5cdFx0XHRcdC8vIEFyaXRobWV0aWMgb3BlcmF0aW9ucyBvbiBudW1iZXJzIHByb2R1Y2UgbnVtYmVyc1xuXHRcdFx0XHRpZiAoKGxlZnRUeXBlID09PSAnbnVtYmVyJyB8fCBsZWZ0VHlwZSA9PT0gJ3Vua25vd24nKSAmJlxuXHRcdFx0XHRcdCAgICAocmlnaHRUeXBlID09PSAnbnVtYmVyJyB8fCByaWdodFR5cGUgPT09ICd1bmtub3duJykpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGlmIChvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5QbHVzVG9rZW4pIHtcblx0XHRcdFx0Ly8gUGx1cyBjYW4gYmUgYWRkaXRpb24gb3Igc3RyaW5nIGNvbmNhdGVuYXRpb25cblx0XHRcdFx0aWYgKGxlZnRUeXBlID09PSAnc3RyaW5nJyB8fCByaWdodFR5cGUgPT09ICdzdHJpbmcnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChsZWZ0VHlwZSA9PT0gJ251bWJlcicgJiYgcmlnaHRUeXBlID09PSAnbnVtYmVyJykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gSGFuZGxlIHByb3BlcnR5IGFjY2VzcyBsaWtlIGRhdGEudmFsdWUsIGRhdGEuaWRcblx0XHRcdGlmIChkYXRhVHlwZU1hcCkge1xuXHRcdFx0XHRjb25zdCBhY2Nlc3NDaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihpbml0aWFsaXplcik7XG5cdFx0XHRcdGlmIChhY2Nlc3NDaGFpbikge1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSBkYXRhVHlwZU1hcC5nZXQoYWNjZXNzQ2hhaW4pO1xuXHRcdFx0XHRcdGlmICh0eXBlKSB7XG5cdFx0XHRcdFx0XHRyZXR1cm4gdHlwZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIEhhbmRsZSB0aGlzLm1hcC5zaXplIHBhdHRlcm4gKE1hcC5zaXplIHJldHVybnMgbnVtYmVyKVxuXHRcdFx0Y29uc3QgcHJvcEFjY2VzcyA9IGluaXRpYWxpemVyIGFzIHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihwcm9wQWNjZXNzLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IG91dGVyUHJvcCA9IHByb3BBY2Nlc3MuZXhwcmVzc2lvbjtcblx0XHRcdFx0Ly8gQ2hlY2sgZm9yIHRoaXMubWFwIHBhdHRlcm5cblx0XHRcdFx0bGV0IGlubmVyTmFtZSA9ICcnO1xuXHRcdFx0XHRpZiAob3V0ZXJQcm9wLmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdGlubmVyTmFtZSA9ICd0aGlzJztcblx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc0lkZW50aWZpZXIob3V0ZXJQcm9wLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0aW5uZXJOYW1lID0gb3V0ZXJQcm9wLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBtYXBQcm9wID0gb3V0ZXJQcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgZmluYWxQcm9wID0gcHJvcEFjY2Vzcy5uYW1lLnRleHQ7XG5cdFx0XHRcdC8vIHRoaXMubWFwLnNpemUgLT4gbnVtYmVyXG5cdFx0XHRcdGlmIChpbm5lck5hbWUgPT09ICd0aGlzJyAmJiBtYXBQcm9wID09PSAnbWFwJyAmJiBmaW5hbFByb3AgPT09ICdzaXplJykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLklkZW50aWZpZXI6IHtcblx0XHRcdC8vIEhhbmRsZSBpZGVudGlmaWVyIHJlZmVyZW5jZXMgaWYgaW4gZGF0YVR5cGVNYXBcblx0XHRcdGlmIChkYXRhVHlwZU1hcCkge1xuXHRcdFx0XHRjb25zdCBuYW1lID0gKGluaXRpYWxpemVyIGFzIHRzLklkZW50aWZpZXIpLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHR5cGUgPSBkYXRhVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0XHRcdGlmICh0eXBlKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHR5cGU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5DYWxsRXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gSGFuZGxlIGZ1bmN0aW9uIGNhbGxzIGxpa2UgRGF0ZS5ub3coKSwgcGFyc2VJbnQoKSwgZXRjLlxuXHRcdFx0Y29uc3QgY2FsbEV4cHIgPSBpbml0aWFsaXplciBhcyB0cy5DYWxsRXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsRXhwci5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBtZXRob2ROYW1lID0gY2FsbEV4cHIuZXhwcmVzc2lvbi5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IG9iak5hbWUgPSB0cy5pc0lkZW50aWZpZXIoY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uKVxuXHRcdFx0XHRcdD8gY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uLnRleHRcblx0XHRcdFx0XHQ6ICcnO1xuXHRcdFx0XHRcdFxuXHRcdFx0XHQvLyBEYXRlLm5vdygpIC0+IG51bWJlclxuXHRcdFx0XHRpZiAob2JqTmFtZSA9PT0gJ0RhdGUnICYmIG1ldGhvZE5hbWUgPT09ICdub3cnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIFN0cmluZyBtZXRob2RzIHRoYXQgcmV0dXJuIHN0cmluZ1xuXHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3RvU3RyaW5nJyB8fCBtZXRob2ROYW1lID09PSAndmFsdWVPZicpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gSGFuZGxlIE1hcCBwcm9wZXJ0eSBhY2Nlc3Mgb24gY2xhc3MgaW5zdGFuY2VzICh0aGlzLm1hcC4qKVxuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdGNvbnN0IG91dGVyUHJvcCA9IGNhbGxFeHByLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdFx0XHQvLyBIYW5kbGUgYm90aCAndGhpcycga2V5d29yZCBhbmQgaWRlbnRpZmllciBwYXR0ZXJuc1xuXHRcdFx0XHRcdGxldCBpbm5lck5hbWUgPSAnJztcblx0XHRcdFx0XHRpZiAob3V0ZXJQcm9wLmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdFx0aW5uZXJOYW1lID0gJ3RoaXMnO1xuXHRcdFx0XHRcdH0gZWxzZSBpZiAodHMuaXNJZGVudGlmaWVyKG91dGVyUHJvcC5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdFx0aW5uZXJOYW1lID0gb3V0ZXJQcm9wLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Y29uc3QgbWFwUHJvcCA9IG91dGVyUHJvcC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Ly8gdGhpcy5tYXAuWCgpIHBhdHRlcm5zXG5cdFx0XHRcdFx0aWYgKGlubmVyTmFtZSA9PT0gJ3RoaXMnICYmIG1hcFByb3AgPT09ICdtYXAnKSB7XG5cdFx0XHRcdFx0XHQvLyBUcnkgdG8gZ2V0IHRoZSBNYXAncyB2YWx1ZSB0eXBlIGZyb20gY2xhc3MgcHJvcGVydGllc1xuXHRcdFx0XHRcdFx0bGV0IG1hcFZhbHVlVHlwZSA9ICd1bmtub3duJztcblx0XHRcdFx0XHRcdGlmIChjbGFzc1Byb3BlcnR5VHlwZXMpIHtcblx0XHRcdFx0XHRcdFx0Y29uc3QgbWFwVHlwZSA9IGNsYXNzUHJvcGVydHlUeXBlcy5nZXQoJ21hcCcpO1xuXHRcdFx0XHRcdFx0XHRpZiAobWFwVHlwZSAmJiBtYXBUeXBlLnN0YXJ0c1dpdGgoJ01hcDwnKSkge1xuXHRcdFx0XHRcdFx0XHRcdC8vIFBhcnNlIE1hcDxLLCBWPiB0byBnZXQgVlxuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IG1hdGNoID0gbWFwVHlwZS5tYXRjaCgvTWFwPFteLF0rLFxccyooLispPiQvKTtcblx0XHRcdFx0XHRcdFx0XHRpZiAobWF0Y2gpIHtcblx0XHRcdFx0XHRcdFx0XHRcdG1hcFZhbHVlVHlwZSA9IG1hdGNoWyAxIF07XG5cdFx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2hhcycpIHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3NldCcpIHJldHVybiAndGhpcyc7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2dldCcpIHJldHVybiBtYXBWYWx1ZVR5cGU7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2RlbGV0ZScpIHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2NsZWFyJykgcmV0dXJuICd2b2lkJztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAndmFsdWVzJykgcmV0dXJuIGBJdGVyYWJsZUl0ZXJhdG9yPCR7bWFwVmFsdWVUeXBlfT5gO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdrZXlzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPHN0cmluZz4nO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdlbnRyaWVzJykgcmV0dXJuIGBJdGVyYWJsZUl0ZXJhdG9yPFtzdHJpbmcsICR7bWFwVmFsdWVUeXBlfV0+YDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gRGlyZWN0IG1hcC5YKCkgY2FsbHNcblx0XHRcdFx0aWYgKG9iak5hbWUgPT09ICdtYXAnIHx8IG9iak5hbWUgPT09ICdvYmonKSB7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdoYXMnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnc2V0JykgcmV0dXJuICd0aGlzJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2dldCcpIHJldHVybiAndW5rbm93bic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdkZWxldGUnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnY2xlYXInKSByZXR1cm4gJ3ZvaWQnO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAndmFsdWVzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPHVua25vd24+Jztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2tleXMnKSByZXR1cm4gJ0l0ZXJhYmxlSXRlcmF0b3I8c3RyaW5nPic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdlbnRyaWVzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPFtzdHJpbmcsIHVua25vd25dPic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIHBhcnNlSW50LCBwYXJzZUZsb2F0IC0+IG51bWJlclxuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjYWxsRXhwci5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBmbk5hbWUgPSBjYWxsRXhwci5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdwYXJzZUludCcgfHwgZm5OYW1lID09PSAncGFyc2VGbG9hdCcpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ1N0cmluZycpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ051bWJlcicpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ0Jvb2xlYW4nKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlRlbXBsYXRlRXhwcmVzc2lvbjpcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTm9TdWJzdGl0dXRpb25UZW1wbGF0ZUxpdGVyYWw6IHtcblx0XHRcdC8vIFRlbXBsYXRlIGxpdGVyYWxzIGxpa2UgYCR7YmFzZVZhbHVlfS0ke2V4dHJhfWAgYWx3YXlzIHByb2R1Y2Ugc3RyaW5nc1xuXHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdH1cblx0XHRkZWZhdWx0OlxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0KiBDb2xsZWN0IHVzYWdlIGluZm9ybWF0aW9uIGZvciB0eXBlIHJlZmVyZW5jZXNcblx0XHRcdCovXG5cdHByaXZhdGUgY29sbGVjdFVzYWdlIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgZm9yIG5ldyBUeXBlKCkgaW5zdGFudGlhdGlvblxuXHRcdGlmICh0cy5pc05ld0V4cHJlc3Npb24obm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRsZXQgdHlwZU5hbWU6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdHR5cGVOYW1lID0gdGhpcy5yZXNvbHZlVHlwZVBhdGgobm9kZS5leHByZXNzaW9uKTtcblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdHR5cGVOYW1lID0gdGhpcy5nZXRUeXBlTmFtZUZyb21FeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHlwZU5hbWUpIHtcblx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHQpO1xuXHRcdFx0XHR0aGlzLmFkZFVzYWdlKHR5cGVOYW1lLCB7XG5cdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRraW5kICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHR9KTtcblx0XHRcdFx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudCBmcm9tIG5ldyBUeXBlKCkgZm9yIGZsb3cgYW5hbHlzaXNcblx0XHRcdFx0dGhpcy50cmFja05ld0Fzc2lnbm1lbnQobm9kZSwgdHlwZU5hbWUpO1xuXHRcdFx0XHQvLyBBbHNvIHJlY29yZCBhcyBmbG93IGV2ZW50XG5cdFx0XHRcdHRoaXMuYWRkRmxvdyh0eXBlTmFtZSwge1xuXHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0a2luZCAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRjb250ZXh0ICA6ICduZXcgZXhwcmVzc2lvbicsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0Ly8gQ2hlY2sgZm9yIHByb3BlcnR5IGFjY2VzcyBvbiBpbnN0YW5jZXMgKHVzZXIuQWRtaW5UeXBlKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRcdC8vIENoZWNrIGlmIHRoaXMgbG9va3MgbGlrZSBhIHR5cGUgYWNjZXNzIHBhdHRlcm5cblx0XHRcdGlmIChwcm9wTmFtZSAmJiB0aGlzLmlzTGlrZWx5VHlwZU5hbWUocHJvcE5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0XHQvLyBUcnkgdG8gcmVzb2x2ZSBmdWxsIHBhdGhcblx0XHRcdFx0Y29uc3QgZnVsbFBhdGggPSB0aGlzLnJlc29sdmVUeXBlUGF0aChub2RlKTtcblx0XHRcdFx0aWYgKGZ1bGxQYXRoKSB7XG5cdFx0XHRcdFx0dGhpcy5hZGRVc2FnZShmdWxsUGF0aCwge1xuXHRcdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRcdGtpbmQgICAgIDogJ3Byb3BlcnR5QWNjZXNzJyxcblx0XHRcdFx0XHRcdGNvZGUgICAgIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFxuXHRcdC8vIENoZWNrIGZvciBsb29rdXAoJ1R5cGVOYW1lJykgb3IgbG9va3VwKHNvdXJjZSwgJ1R5cGVOYW1lJykgY2FsbHNcblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdGNvbnN0IGZ1bmNOYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKTtcblx0XHRcdGlmIChmdW5jTmFtZSA9PT0gJ2xvb2t1cCcgJiYgbm9kZS5hcmd1bWVudHMubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRjb25zdCB0eXBlUGF0aCA9IHRoaXMucmVzb2x2ZUxvb2t1cFBhdGgobm9kZSk7XG5cdFx0XHRcdGlmICh0eXBlUGF0aCkge1xuXHRcdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdFx0KTtcblx0XHRcdFx0XHR0aGlzLmFkZFVzYWdlKHR5cGVQYXRoLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdFx0a2luZCAgICAgOiAnbG9va3VwJyxcblx0XHRcdFx0XHRcdGNvZGUgICAgIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudCBmcm9tIGxvb2t1cCBmb3IgaW5zdGFudGlhdGlvbiB0cmFja2luZ1xuXHRcdFx0XHRcdHRoaXMudHJhY2tMb29rdXBBc3NpZ25tZW50KG5vZGUsIHR5cGVQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIEdldCBmdW5jdGlvbiBuYW1lIGZyb20gZXhwcmVzc2lvbiAoaWRlbnRpZmllciBvciBwcm9wZXJ0eSBhY2Nlc3MpXG5cdFx0XHQqL1xuXHRwcml2YXRlIGdldEZ1bmN0aW9uTmFtZSAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIGV4cHIudGV4dDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0KiBBZGQgYSB1c2FnZSB0byB0aGUgY29sbGVjdGlvblxuXHRcdFx0Ki9cblx0cHJpdmF0ZSBhZGRVc2FnZSAodHlwZVBhdGg6IHN0cmluZywgdXNhZ2U6IFVzYWdlSW5mbyk6IHZvaWQge1xuXHRcdC8vIE9ubHkgdHJhY2sgdXNhZ2VzIG9mIG1uZW1vbmljYS1kZWZpbmVkIHR5cGVzXG5cdFx0aWYgKCF0aGlzLmRlZmluaXRpb25zLmhhcyh0eXBlUGF0aCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKCF0aGlzLnVzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLnVzYWdlcy5zZXQodHlwZVBhdGgsIFtdKTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgZHVwbGljYXRlcyBiYXNlZCBvbiBsb2NhdGlvbiwgY29kZSwgYW5kIGtpbmRcblx0XHRjb25zdCBleGlzdGluZ1VzYWdlcyA9IHRoaXMudXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGlzRHVwbGljYXRlID0gZXhpc3RpbmdVc2FnZXMuc29tZShleGlzdGluZyA9PlxuXHRcdFx0ZXhpc3RpbmcubG9jYXRpb24gPT09IHVzYWdlLmxvY2F0aW9uICYmXG5cdFx0XHRcdGV4aXN0aW5nLmNvZGUgPT09IHVzYWdlLmNvZGUgJiZcblx0XHRcdFx0ZXhpc3Rpbmcua2luZCA9PT0gdXNhZ2Uua2luZCk7XG5cblx0XHRpZiAoIWlzRHVwbGljYXRlKSB7XG5cdFx0XHRleGlzdGluZ1VzYWdlcy5wdXNoKHVzYWdlKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBFRFMgKEV4ZWN1dGlvbiBEYXRhIFN0b3JhZ2UpIHVzYWdlIGluZm9ybWF0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RFRFMgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkgfHwgIW5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZ1bmNOYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIWZ1bmNOYW1lKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXHRcdC8vIEVuY2xvc2luZyBtbmVtb25pY2EgdHlwZSBwYXRoIOKAlCB3cmFwIGFyZ3MgYXJlIHVzdWFsbHkgbG9jYWxcblx0XHQvLyBmdW5jdGlvbnMsIHNvIHRoZSBvd25pbmcgZGVmaW5lKCkvbGF6eSgpIGhhbmRsZXIgb3IgZGVjb3JhdGVkXG5cdFx0Ly8gY2xhc3MgaXMgd2hhdCBlZHMuanNvbiBjb25zdW1lcnMgKEdyYXBoQnVpbGRlcikgY2FuIGpvaW4gb24uXG5cdFx0Y29uc3Qgc2NvcGUgPSB0aGlzLnJlc29sdmVFRFNTY29wZShub2RlKTtcblxuXHRcdC8vIHdyYXAoZm4pLCB3cmFwQ29uc3RydWN0b3JBcmcoZm4sIHBhcmVudCksIHVwZ3JhZGVDb25zdHJ1Y3RvckFyZyhhcmcsIGluc3QpLCB3cmFwSW5zdGFuY2VNZXRob2RzKG9iailcblx0XHRpZiAoXG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3dyYXAnIHx8XG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3dyYXBDb25zdHJ1Y3RvckFyZycgfHxcblx0XHRcdGZ1bmNOYW1lID09PSAndXBncmFkZUNvbnN0cnVjdG9yQXJnJyB8fFxuXHRcdFx0ZnVuY05hbWUgPT09ICd3cmFwSW5zdGFuY2VNZXRob2RzJ1xuXHRcdCkge1xuXHRcdFx0Y29uc3QgdGFyZ2V0VHlwZSA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShub2RlLmFyZ3VtZW50c1sgMCBdKTtcblx0XHRcdHRoaXMuYWRkRURTKHRhcmdldFR5cGUgfHwgc2NvcGUgfHwgJ3Vua25vd24nLCB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgIDogJ3dyYXAnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdHNjb3BlLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gY3VycmVudCgpLCBnZXRFcnJvckluc3RhbmNlKGVyciksIGdldEZsb3codGFyZ2V0Pylcblx0XHRpZiAoZnVuY05hbWUgPT09ICdjdXJyZW50JyB8fCBmdW5jTmFtZSA9PT0gJ2dldEVycm9ySW5zdGFuY2UnIHx8IGZ1bmNOYW1lID09PSAnZ2V0RmxvdycpIHtcblx0XHRcdHRoaXMuYWRkRURTKHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCA6ICdjb250ZXh0Q29uc3VtZScsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHNjb3BlLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gYXR0YWNoSG9va3MoY29sbGVjdGlvbikg4oCUIGZyb20gQG1uZW1vbmljYS9uZXN0anMsIHdpcmVzIGFcblx0XHQvLyBUeXBlc0NvbGxlY3Rpb24gdG8gZGl2ZSdzIGxpZmVjeWNsZSB0cmFjaW5nXG5cdFx0aWYgKGZ1bmNOYW1lID09PSAnYXR0YWNoSG9va3MnICYmIG5vZGUuYXJndW1lbnRzLmxlbmd0aCA+IDApIHtcblx0XHRcdGNvbnN0IGFyZyA9IG5vZGUuYXJndW1lbnRzWyAwIF07XG5cdFx0XHRpZiAodHMuaXNBcnJheUxpdGVyYWxFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGFyZy5lbGVtZW50cykge1xuXHRcdFx0XHRcdGNvbnN0IHRhcmdldFR5cGUgPSB0aGlzLnJlc29sdmVFRFNBcmd1bWVudFR5cGUoZWxlbWVudCk7XG5cdFx0XHRcdFx0dGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCBzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRcdFx0a2luZCAgICAgICA6ICdob29rQXR0YWNoJyxcblx0XHRcdFx0XHRcdGNvZGUsXG5cdFx0XHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdFx0XHRzY29wZSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgdGFyZ2V0VHlwZSA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShhcmcpO1xuXHRcdFx0XHR0aGlzLmFkZEVEUyh0YXJnZXRUeXBlIHx8IHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRcdGtpbmQgICAgICAgOiAnaG9va0F0dGFjaCcsXG5cdFx0XHRcdFx0Y29kZSxcblx0XHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdFx0c2NvcGUsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHR5cGUgZnJvbSBFRFMgY2FsbCBhcmd1bWVudCAoYmVzdCBlZmZvcnQpXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVFRFNBcmd1bWVudFR5cGUgKGFyZzogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCFhcmcpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gSWRlbnRpZmllcjogdmFyaWFibGUgbmFtZVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0Y29uc3QgbWFwcGVkID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQoYXJnLnRleHQpO1xuXHRcdFx0aWYgKG1hcHBlZCkge1xuXHRcdFx0XHRyZXR1cm4gbWFwcGVkO1xuXHRcdFx0fVxuXHRcdFx0Ly8gTWF5YmUgaXQncyBhIHR5cGUgbmFtZSBkaXJlY3RseVxuXHRcdFx0aWYgKHRoaXMuZGVmaW5pdGlvbnMuaGFzKGFyZy50ZXh0KSkge1xuXHRcdFx0XHRyZXR1cm4gYXJnLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2Vzczogb2JqLnByb3Bcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMucmVzb2x2ZVR5cGVQYXRoKGFyZyk7XG5cdFx0fVxuXG5cdFx0Ly8gVGhpcyBleHByZXNzaW9uOiB0aGlzLnNvbWV0aGluZ1xuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcmcpICYmIHRzLmlzSWRlbnRpZmllcihhcmcuZXhwcmVzc2lvbikgJiYgYXJnLmV4cHJlc3Npb24udGV4dCA9PT0gJ3RoaXMnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0aGUgZW5jbG9zaW5nIG1uZW1vbmljYSBzY29wZSBvZiBhbiBFRFMgY2FsbCBzaXRlIGJ5IHdhbGtpbmdcblx0ICogdXAgdGhlIHBhcmVudCBjaGFpbjogbmVhcmVzdCBkZWZpbmUoKS9sYXp5KCkgY2FsbCB3aG9zZSBoYW5kbGVyIGhvbGRzXG5cdCAqIHRoZSBub2RlLCBvciBuZWFyZXN0IEBkZWNvcmF0ZSgpLWVkIGNsYXNzIGRlY2xhcmF0aW9uLiBCZXN0IGVmZm9ydCDigJRcblx0ICogcmV0dXJucyB1bmRlZmluZWQgZm9yIGNhbGxzIG91dHNpZGUgYW55IHR5cGUgc2NvcGUgKG1vZHVsZSB0b3AgbGV2ZWwpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRURTU2NvcGUgKG5vZGU6IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbm9kZS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGNvbnN0IHNjb3BlUGF0aCA9IHRoaXMuZWRzU2NvcGVCeU5vZGUuZ2V0KGN1cnJlbnQpO1xuXHRcdFx0aWYgKHNjb3BlUGF0aCkge1xuXHRcdFx0XHRyZXR1cm4gc2NvcGVQYXRoO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhbiBFRFMgdXNhZ2UgdG8gdGhlIGNvbGxlY3Rpb25cblx0ICovXG5cdHByaXZhdGUgYWRkRURTICh0eXBlUGF0aDogc3RyaW5nLCBpbmZvOiBFRFNJbmZvKTogdm9pZCB7XG5cdFx0aWYgKCF0aGlzLmVkc1VzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLmVkc1VzYWdlcy5zZXQodHlwZVBhdGgsIFtdKTtcblx0XHR9XG5cblx0XHRjb25zdCBleGlzdGluZyA9IHRoaXMuZWRzVXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGlzRHVwbGljYXRlID0gZXhpc3Rpbmcuc29tZShlID0+IHtcblx0XHRcdHJldHVybiBlLmxvY2F0aW9uID09PSBpbmZvLmxvY2F0aW9uICYmXG5cdFx0XHRcdGUua2luZCA9PT0gaW5mby5raW5kICYmXG5cdFx0XHRcdGUuY29kZSA9PT0gaW5mby5jb2RlO1xuXHRcdH0pO1xuXG5cdFx0aWYgKCFpc0R1cGxpY2F0ZSkge1xuXHRcdFx0ZXhpc3RpbmcucHVzaChpbmZvKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBuYXRpdmUgZmxvdyBwYXR0ZXJucyAoaW5zdGFuY2UgdXNhZ2UgYWZ0ZXIgY3JlYXRpb24pXG5cdCAqIFBoYXNlIDE6IHByb3BlcnR5IGFjY2VzcywgbWV0aG9kIGNhbGxzLCBhcmd1bWVudHMsIHJldHVybiwgZGVzdHJ1Y3R1cmluZywgZXRjLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0RmxvdyAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIFByb3BlcnR5IHJlYWQ6IHVzZXIubmFtZSBvciB1c2VyPy5uYW1lXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93UHJvcGVydHlBY2Nlc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRWxlbWVudCBhY2Nlc3M6IHVzZXJbJ25hbWUnXVxuXHRcdGlmICh0cy5pc0VsZW1lbnRBY2Nlc3NFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93RWxlbWVudEFjY2Vzcyhub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSB3cml0ZTogdXNlci5uYW1lID0gdmFsdWVcblx0XHRpZiAodHMuaXNCaW5hcnlFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkVxdWFsc1Rva2VuKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93QXNzaWdubWVudChub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBNZXRob2QgY2FsbDogdXNlci52YWxpZGF0ZSgpICBBTkQgIGFyZ3VtZW50IHBhc3Npbmc6IHByb2Nlc3NVc2VyKHVzZXIpXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93TWV0aG9kQ2FsbChub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dBcmd1bWVudFBhc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRGVzdHJ1Y3R1cmUgcmVhZDogY29uc3QgeyBuYW1lIH0gPSB1c2VyXG5cdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLmluaXRpYWxpemVyKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93RGVzdHJ1Y3R1cmUobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUmV0dXJuIGluc3RhbmNlOiByZXR1cm4gdXNlclxuXHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dSZXR1cm4obm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gU3ByZWFkOiB7IC4uLnVzZXIgfVxuXHRcdGlmICh0cy5pc1NwcmVhZEVsZW1lbnQobm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dTcHJlYWQobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgcHJvcGVydHkgYWNjZXNzIGZsb3cgKHJlYWQgb3IgY29uZGl0aW9uYWwpXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93UHJvcGVydHlBY2Nlc3MgKG5vZGU6IHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHByb3BOYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0Ly8gU2tpcCBpZiB0aGlzIGlzIGEgdHlwZSBjb25zdHJ1Y3RvciBhY2Nlc3MgKGUuZy4sIFVzZXJUeXBlLmRlZmluZSlcblx0XHRpZiAocHJvcE5hbWUgPT09ICdkZWZpbmUnIHx8IHByb3BOYW1lID09PSAnbGF6eScpIHsgcmV0dXJuOyB9XG5cblx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgICAgOiAncHJvcGVydHlSZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHRwcm9wZXJ0eU5hbWUgOiBwcm9wTmFtZSxcblx0XHRcdHRhcmdldFR5cGUgICA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGVsZW1lbnQgYWNjZXNzIGZsb3c6IHVzZXJbJ25hbWUnXVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0VsZW1lbnRBY2Nlc3MgKG5vZGU6IHRzLkVsZW1lbnRBY2Nlc3NFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3Qgb2JqZWN0VHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0aWYgKCFvYmplY3RUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0dGhpcy5hZGRGbG93KG9iamVjdFR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICA6ICdlbGVtZW50QWNjZXNzJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogb2JqZWN0VHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgYXNzaWdubWVudCBmbG93OiB1c2VyLm5hbWUgPSB2YWx1ZSBvciB1c2VyID0gb3RoZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dBc3NpZ25tZW50IChub2RlOiB0cy5CaW5hcnlFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gUHJvcGVydHkgd3JpdGU6IHVzZXIubmFtZSA9IHZhbHVlXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUubGVmdCkpIHtcblx0XHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmxlZnQuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRcdGNvbnN0IHByb3BOYW1lID0gbm9kZS5sZWZ0Lm5hbWUudGV4dDtcblx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0KTtcblx0XHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgICAgOiAncHJvcGVydHlXcml0ZScsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHByb3BlcnR5TmFtZSA6IHByb3BOYW1lLFxuXHRcdFx0XHR0YXJnZXRUeXBlICAgOiBvYmplY3RUeXBlXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBWYXJpYWJsZSByZWFzc2lnbm1lbnQ6IHVzZXIgPSBvdGhlclxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIobm9kZS5sZWZ0KSkge1xuXHRcdFx0Y29uc3QgdmFyTmFtZSA9IG5vZGUubGVmdC50ZXh0O1xuXHRcdFx0Y29uc3QgbWFwcGVkVHlwZSA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KHZhck5hbWUpO1xuXHRcdFx0aWYgKCFtYXBwZWRUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdCk7XG5cdFx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0XHR0aGlzLmFkZEZsb3cobWFwcGVkVHlwZSwge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCAgICAgICA6ICdyZWFzc2lnbm1lbnQnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHR0YXJnZXRUeXBlIDogbWFwcGVkVHlwZVxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgbWV0aG9kIGNhbGwgZmxvdzogdXNlci52YWxpZGF0ZSgpXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93TWV0aG9kQ2FsbCAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbikpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IG1ldGhvZE5hbWUgPSBub2RlLmV4cHJlc3Npb24ubmFtZS50ZXh0O1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIFNraXAgaWYgdGhpcyBpcyBhIHR5cGUgY29uc3RydWN0b3IgY2FsbCAoZS5nLiwgbmV3IFVzZXJUeXBlKCkpXG5cdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdkZWZpbmUnIHx8IG1ldGhvZE5hbWUgPT09ICdsYXp5JykgeyByZXR1cm47IH1cblxuXHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgICA6ICdtZXRob2RDYWxsJyxcblx0XHRcdGNvZGUsXG5cdFx0XHRwcm9wZXJ0eU5hbWUgOiBtZXRob2ROYW1lLFxuXHRcdFx0dGFyZ2V0VHlwZSAgIDogb2JqZWN0VHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgYXJndW1lbnQgcGFzc2luZyBmbG93OiBwcm9jZXNzVXNlcih1c2VyKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0FyZ3VtZW50UGFzcyAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRjb25zdCBhcmcgPSBub2RlLmFyZ3VtZW50c1sgaSBdO1xuXHRcdFx0Y29uc3QgYXJnVHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKGFyZyk7XG5cdFx0XHRpZiAoIWFyZ1R5cGUpIHsgY29udGludWU7IH1cblxuXHRcdFx0Y29uc3QgZnVuY05hbWUgPSB0aGlzLmdldEZ1bmN0aW9uTmFtZShub2RlLmV4cHJlc3Npb24pIHx8ICdhbm9ueW1vdXMnO1xuXHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHQpO1xuXHRcdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdFx0dGhpcy5hZGRGbG93KGFyZ1R5cGUsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAncGFzc0FzQXJnJyxcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSA6IGFyZ1R5cGUsXG5cdFx0XHRcdGNvbnRleHQgICAgOiBgYXJnICR7aX0gdG8gJHtmdW5jTmFtZX1gXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBkZXN0cnVjdHVyaW5nIGZsb3c6IGNvbnN0IHsgbmFtZSB9ID0gdXNlclxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0Rlc3RydWN0dXJlIChub2RlOiB0cy5WYXJpYWJsZURlY2xhcmF0aW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc09iamVjdEJpbmRpbmdQYXR0ZXJuKG5vZGUubmFtZSkpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBzb3VyY2VUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5pbml0aWFsaXplciEpO1xuXHRcdGlmICghc291cmNlVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIEV4dHJhY3QgZGVzdHJ1Y3R1cmVkIHByb3BlcnR5IG5hbWVzXG5cdFx0Y29uc3QgcHJvcHM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIG5vZGUubmFtZS5lbGVtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihlbGVtZW50Lm5hbWUpKSB7XG5cdFx0XHRcdHByb3BzLnB1c2goZWxlbWVudC5uYW1lLnRleHQpO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHRoaXMuYWRkRmxvdyhzb3VyY2VUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnZGVzdHJ1Y3R1cmVSZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogc291cmNlVHlwZSxcblx0XHRcdGNvbnRleHQgICAgOiBwcm9wcy5qb2luKCcsICcpXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCByZXR1cm4gZmxvdzogcmV0dXJuIHVzZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dSZXR1cm4gKG5vZGU6IHRzLlJldHVyblN0YXRlbWVudCwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHJldHVyblR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24hKTtcblx0XHRpZiAoIXJldHVyblR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHR0aGlzLmFkZEZsb3cocmV0dXJuVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ3JldHVybicsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHJldHVyblR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IHNwcmVhZCBmbG93OiB7IC4uLnVzZXIgfVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd1NwcmVhZCAobm9kZTogdHMuU3ByZWFkRWxlbWVudCwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHNwcmVhZFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghc3ByZWFkVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuYWRkRmxvdyhzcHJlYWRUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnc3ByZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogc3ByZWFkVHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgdHlwZSBmcm9tIGFuIGV4cHJlc3Npb24gKGlkZW50aWZpZXIsIHByb3BlcnR5IGFjY2VzcywgZXRjLilcblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUV4cHJlc3Npb25UeXBlIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBJZGVudGlmaWVyOiB1c2VyXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGV4cHIudGV4dCk7XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiB1c2VyLm5hbWUgKHJldHVybiBvYmplY3QgdHlwZSwgbm90IHByb3BlcnR5IHR5cGUpXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUoZXhwci5leHByZXNzaW9uKTtcblx0XHR9XG5cblx0XHQvLyBFbGVtZW50IGFjY2VzczogdXNlclsnbmFtZSddXG5cdFx0aWYgKHRzLmlzRWxlbWVudEFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdHJldHVybiB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShleHByLmV4cHJlc3Npb24pO1xuXHRcdH1cblxuXHRcdC8vIFRoaXMgZXhwcmVzc2lvbjogdGhpcyAoaWYgaW4gYSBtZXRob2QsIHdlIGNhbid0IHJlc29sdmUgd2l0aG91dCBtb3JlIGNvbnRleHQpXG5cdFx0aWYgKGV4cHIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhIGZsb3cgdXNhZ2UgdG8gdGhlIGNvbGxlY3Rpb25cblx0ICovXG5cdHByaXZhdGUgYWRkRmxvdyAodHlwZVBhdGg6IHN0cmluZywgaW5mbzogRmxvd0luZm8pOiB2b2lkIHtcblx0XHRpZiAoIXRoaXMuZmxvd1VzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLmZsb3dVc2FnZXMuc2V0KHR5cGVQYXRoLCBbXSk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZXhpc3RpbmcgPSB0aGlzLmZsb3dVc2FnZXMuZ2V0KHR5cGVQYXRoKSE7XG5cdFx0Y29uc3QgaXNEdXBsaWNhdGUgPSBleGlzdGluZy5zb21lKGUgPT4ge1xuXHRcdFx0cmV0dXJuIGUubG9jYXRpb24gPT09IGluZm8ubG9jYXRpb24gJiZcblx0XHRcdFx0ZS5raW5kID09PSBpbmZvLmtpbmQgJiZcblx0XHRcdFx0ZS5jb2RlID09PSBpbmZvLmNvZGU7XG5cdFx0fSk7XG5cblx0XHRpZiAoIWlzRHVwbGljYXRlKSB7XG5cdFx0XHRleGlzdGluZy5wdXNoKGluZm8pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdFx0KiBHZXQgdHlwZSBuYW1lIGZyb20gZXhwcmVzc2lvbiAoaWRlbnRpZmllciBvciBwcm9wZXJ0eSBhY2Nlc3MpXG5cdFx0XHQqL1xuXHRwcml2YXRlIGdldFR5cGVOYW1lRnJvbUV4cHJlc3Npb24gKGV4cHI6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdGNvbnN0IG5hbWUgPSBleHByLnRleHQ7XG5cdFx0XHQvLyBDaGVjayBpZiB0aGlzIGlkZW50aWZpZXIgaXMgYSB2YXJpYWJsZSBtYXBwZWQgdG8gYSB0eXBlIChlLmcuLCBmcm9tIGxvb2t1cClcblx0XHRcdGNvbnN0IG1hcHBlZFR5cGUgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChuYW1lKTtcblx0XHRcdGlmIChtYXBwZWRUeXBlKSB7XG5cdFx0XHRcdHJldHVybiBtYXBwZWRUeXBlO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIG5hbWU7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4oZXhwcik7XG5cdFx0XHRyZXR1cm4gY2hhaW4uam9pbignLicpO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cdFxuXHQvKipcblx0XHRcdCogUmVzb2x2ZSBmdWxsIHR5cGUgcGF0aCBmcm9tIHByb3BlcnR5IGFjY2Vzc1xuXHRcdFx0Ki9cblx0cHJpdmF0ZSByZXNvbHZlVHlwZVBhdGggKGV4cHI6IHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4oZXhwcik7XG5cdFx0aWYgKGNoYWluLmxlbmd0aCA9PT0gMCkgcmV0dXJuIHVuZGVmaW5lZDtcblx0XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBjaGFpbiBtYXRjaGVzIGEga25vd24gdHlwZVxuXHRcdGNvbnN0IGZ1bGxQYXRoID0gY2hhaW4uam9pbignLicpO1xuXHRcdGlmICh0aGlzLmRlZmluaXRpb25zLmhhcyhmdWxsUGF0aCkpIHtcblx0XHRcdHJldHVybiBmdWxsUGF0aDtcblx0XHR9XG5cdFxuXHRcdC8vIFRyeSBqdXN0IHRoZSBwcm9wZXJ0eSBuYW1lXG5cdFx0Y29uc3QgcHJvcE5hbWUgPSBjaGFpblsgY2hhaW4ubGVuZ3RoIC0gMSBdO1xuXHRcdGZvciAoY29uc3QgWyBwYXRoIF0gb2YgdGhpcy5kZWZpbml0aW9ucykge1xuXHRcdFx0aWYgKHBhdGguZW5kc1dpdGgoYC4ke3Byb3BOYW1lfWApIHx8IHBhdGggPT09IHByb3BOYW1lKSB7XG5cdFx0XHRcdHJldHVybiBwYXRoO1xuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0cmV0dXJuIGZ1bGxQYXRoO1xuXHR9XG5cdFxuXHQvKipcblx0XHRcdCAqIENoZWNrIGlmIGEgbmFtZSBsb29rcyBsaWtlIGEgdHlwZSAoc3RhcnRzIHdpdGggdXBwZXJjYXNlKVxuXHRcdFx0ICovXG5cdHByaXZhdGUgaXNMaWtlbHlUeXBlTmFtZSAobmFtZTogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0cmV0dXJuIG5hbWVbIDAgXSA+PSAnQScgJiYgbmFtZVsgMCBdIDw9ICdaJztcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQgKiBSZXNvbHZlIGEgY29uc3RydWN0b3IgcGFyYW1ldGVyIHR5cGUsIGV4cGFuZGluZyBpbmxpbmUgb2JqZWN0IGxpdGVyYWxzXG5cdFx0XHQgKiBhbmQgdHlwZSBhbGlhc2VzIHdoZXJlIHBvc3NpYmxlLlxuXHRcdFx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUNvbnN0cnVjdG9yUGFyYW1UeXBlICh0eXBlTm9kZTogdHMuVHlwZU5vZGUgfCB1bmRlZmluZWQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHlwZU5vZGUpIHJldHVybiB1bmRlZmluZWQ7XG5cblx0XHQvLyBEaXJlY3QgaW5saW5lIHR5cGUgbGl0ZXJhbDogeyBwcm9wOiB0eXBlIH1cblx0XHRpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUodHlwZU5vZGUpKSB7XG5cdFx0XHRjb25zdCBwcm9wczogc3RyaW5nW10gPSBbXTtcblx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIHR5cGVOb2RlLm1lbWJlcnMpIHtcblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdGNvbnN0IG9wdGlvbmFsID0gbWVtYmVyLnF1ZXN0aW9uVG9rZW4gPyAnPycgOiAnJztcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdHByb3BzLnB1c2goYCR7cHJvcE5hbWV9JHtvcHRpb25hbH06ICR7dHlwZX1gKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGB7ICR7cHJvcHMuam9pbignOyAnKX0gfWA7XG5cdFx0fVxuXG5cdFx0Ly8gVHlwZSByZWZlcmVuY2U6IHVzYWdlLCBVc2VyRGF0YSwgZXRjLiAtIHJlY3Vyc2l2ZWx5IGV4cGFuZFxuXHRcdGlmICh0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHR5cGVOb2RlKSAmJiB0cy5pc0lkZW50aWZpZXIodHlwZU5vZGUudHlwZU5hbWUpKSB7XG5cdFx0XHRjb25zdCB0eXBlTmFtZSA9IHR5cGVOb2RlLnR5cGVOYW1lLnRleHQ7XG5cdFx0XHRjb25zdCBhbGlhc2VkVHlwZSA9IHRoaXMudHlwZUFsaWFzZXMuZ2V0KHR5cGVOYW1lKTtcblx0XHRcdGlmIChhbGlhc2VkVHlwZSkge1xuXHRcdFx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMucmVzb2x2ZUNvbnN0cnVjdG9yUGFyYW1UeXBlKGFsaWFzZWRUeXBlKTtcblx0XHRcdFx0aWYgKGV4cGFuZGVkKSByZXR1cm4gZXhwYW5kZWQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBJZiBub3QgYW4gb2JqZWN0IHR5cGUgYWxpYXMsIHJldHVybiB0aGUgdHlwZSBuYW1lIHdpdGggYXJnc1xuXHRcdFx0aWYgKHR5cGVOb2RlLnR5cGVBcmd1bWVudHMgJiYgdHlwZU5vZGUudHlwZUFyZ3VtZW50cy5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdGNvbnN0IGFyZ3MgPSB0eXBlTm9kZS50eXBlQXJndW1lbnRzLm1hcChhcmcgPT4gdGhpcy5pbmZlclR5cGUoYXJnKSk7XG5cdFx0XHRcdHJldHVybiBgJHt0eXBlTmFtZSAgfTwkeyAgYXJncy5qb2luKCcsICcpICB9PmA7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdHlwZU5hbWU7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHRcdFx0ICogRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZyb20gYSBjbGFzcy1saWtlIG5vZGUuXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q2xhc3NDb25zdHJ1Y3RvclBhcmFtcyAoY2xhc3NMaWtlOiB0cy5DbGFzc0RlY2xhcmF0aW9uIHwgdHMuQ2xhc3NFeHByZXNzaW9uKTpcblx0XHRDb25zdHJ1Y3RvclBhcmFtSW5mb1tdIHtcblx0XHRjb25zdCBwYXJhbXM6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10gPSBbXTtcblxuXHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGNsYXNzTGlrZS5tZW1iZXJzKSB7XG5cdFx0XHRpZiAoIXRzLmlzQ29uc3RydWN0b3JEZWNsYXJhdGlvbihtZW1iZXIpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXG5cdFx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIG1lbWJlci5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRcdGlmICghcGFyYW0ubmFtZSB8fCAhdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpKSBjb250aW51ZTtcblx0XHRcdFx0aWYgKCFwYXJhbS50eXBlKSBjb250aW51ZTtcblxuXHRcdFx0XHRjb25zdCBwYXJhbU5hbWUgPSBwYXJhbS5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IGV4cGFuZGVkVHlwZSA9IHRoaXMucmVzb2x2ZUNvbnN0cnVjdG9yUGFyYW1UeXBlKHBhcmFtLnR5cGUpIHx8IHRoaXMuaW5mZXJUeXBlKHBhcmFtLnR5cGUpO1xuXG5cdFx0XHRcdHBhcmFtcy5wdXNoKHtcblx0XHRcdFx0XHRuYW1lICAgICA6IHBhcmFtTmFtZSxcblx0XHRcdFx0XHR0eXBlICAgICA6IGV4cGFuZGVkVHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6ICEhcGFyYW0ucXVlc3Rpb25Ub2tlbiB8fCAhIXBhcmFtLmluaXRpYWxpemVyXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdFx0YnJlYWs7IC8vIE9ubHkgcHJvY2VzcyBmaXJzdCBjb25zdHJ1Y3RvclxuXHRcdH1cblxuXHRcdHJldHVybiBwYXJhbXM7XG5cdH1cblxuXHQvKipcblx0XHRcdCAqIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGRlZmluZSgpIGNhbGxcblx0XHRcdCAqIFRoaXMgaXMgdXNlZCBmb3IgVHlwZVJlZ2lzdHJ5IGNvbnN0cnVjdG9yIHNpZ25hdHVyZXNcblx0XHRcdCAqIFByZXNlcnZlcyBwYXJhbWV0ZXIgbmFtZXMgYW5kIGV4cGFuZHMgb2JqZWN0IHR5cGVzIHRvIHRoZWlyIHN0cnVjdHVyZVxuXHRcdFx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10ge1xuXHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yRXhwcmVzc2lvbihjYWxsKTtcblx0XHRpZiAoIWNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0cmV0dXJuIFtdO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtc0Zyb21Db25zdHJ1Y3Rvcihjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHRcdCAqIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGEgY29uc3RydWN0b3IgZXhwcmVzc2lvbi5cblx0XHRcdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtc0Zyb21Db25zdHJ1Y3RvciAoY29uc3RydWN0b3JFeHByOiB0cy5FeHByZXNzaW9uKTogQ29uc3RydWN0b3JQYXJhbUluZm9bXSB7XG5cdFx0Y29uc3QgcGFyYW1zOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdID0gW107XG5cdFxuXHRcdC8vIEhhbmRsZSBmdW5jdGlvbiBleHByZXNzaW9uIG9yIGFycm93IGZ1bmN0aW9uXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikgfHwgdHMuaXNBcnJvd0Z1bmN0aW9uKGNvbnN0cnVjdG9yRXhwcikpIHtcblx0XHRcdC8vIExvb2sgZm9yIGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgKHNlY29uZCBwYXJhbSBhZnRlciBgdGhpc2ApXG5cdFx0XHQvLyBQYXR0ZXJuczogZnVuY3Rpb24odGhpczogVHlwZSwgZGF0YTogeyAuLi4gfSkgb3IgKHRoaXM6IFR5cGUsIGRhdGE6IHsgLi4uIH0pID0+XG5cdFx0XHRmb3IgKGxldCBpID0gMDsgaSA8IGNvbnN0cnVjdG9yRXhwci5wYXJhbWV0ZXJzLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRcdGNvbnN0IHBhcmFtID0gY29uc3RydWN0b3JFeHByLnBhcmFtZXRlcnNbIGkgXTtcblx0XHRcdFx0aWYgKCFwYXJhbS50eXBlKSBjb250aW51ZTtcblx0XG5cdFx0XHRcdC8vIFNraXAgYHRoaXNgIHBhcmFtZXRlciAoZmlyc3QgcGFyYW0pXG5cdFx0XHRcdGlmIChcblx0XHRcdFx0XHRpID09PSAwICYmXG5cdFx0XHRcdFx0cGFyYW0ubmFtZS5raW5kID09PSB0cy5TeW50YXhLaW5kLklkZW50aWZpZXIgJiZcblx0XHRcdFx0XHQocGFyYW0ubmFtZSBhcyB0cy5JZGVudGlmaWVyKS50ZXh0ID09PSAndGhpcydcblx0XHRcdFx0KSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XG5cdFx0XHRcdC8vIEdldCBwYXJhbWV0ZXIgbmFtZSBhbmQgZXhwYW5kIGl0cyB0eXBlXG5cdFx0XHRcdGNvbnN0IHBhcmFtTmFtZSA9IHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSA/IHBhcmFtLm5hbWUudGV4dCA6ICdhcmcnO1xuXHRcdFx0XHRjb25zdCBleHBhbmRlZFR5cGUgPSB0aGlzLnJlc29sdmVDb25zdHJ1Y3RvclBhcmFtVHlwZShwYXJhbS50eXBlKSB8fCB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblx0XHRcdFx0XHRcblx0XHRcdFx0cGFyYW1zLnB1c2goe1xuXHRcdFx0XHRcdG5hbWUgICAgIDogcGFyYW1OYW1lLFxuXHRcdFx0XHRcdHR5cGUgICAgIDogZXhwYW5kZWRUeXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogISFwYXJhbS5xdWVzdGlvblRva2VuIHx8ICEhcGFyYW0uaW5pdGlhbGl6ZXJcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcblx0XHQvLyBIYW5kbGUgY2xhc3MgZXhwcmVzc2lvbiAtIGNoZWNrIGNvbnN0cnVjdG9yIG1ldGhvZFxuXHRcdGlmICh0cy5pc0NsYXNzRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHRjb25zdCBjbGFzc1BhcmFtcyA9IHRoaXMuZXh0cmFjdENsYXNzQ29uc3RydWN0b3JQYXJhbXMoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdGZvciAoY29uc3QgcGFyYW0gb2YgY2xhc3NQYXJhbXMpIHtcblx0XHRcdFx0cGFyYW1zLnB1c2gocGFyYW0pO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBwYXJhbXM7XG5cdH1cbn1cbiJdfQ==