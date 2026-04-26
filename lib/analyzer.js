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
        this.typeAliases = new Map();
        // Track variable assignments: variableName -> fullPath of the type it holds
        this.variableToTypeMap = new Map();
        this.program = program;
    }
    /**
     * Lazily-resolved TypeChecker. Returns undefined when the analyzer was
     * created without a ts.Program (e.g. in unit tests using
     * analyzeSource(string)). All callers must be null-safe.
     */
    getTypeChecker() {
        if (!this.program)
            return undefined;
        if (!this._typeChecker) {
            this._typeChecker = this.program.getTypeChecker();
        }
        return this._typeChecker;
    }
    /**
     * Resolve a TS TypeNode (e.g. a generic argument or `this:` annotation)
     * into a property map using the TypeChecker. Returns undefined if no
     * checker is available, the type is not an object, or it has no
     * accessible properties.
     *
     * This is the bridge that lets declared interfaces in another file
     * become tactica's source of truth.
     */
    resolvePropertiesFromTypeNode(typeNode) {
        const checker = this.getTypeChecker();
        if (!checker)
            return undefined;
        let type;
        try {
            type = checker.getTypeFromTypeNode(typeNode);
        }
        catch {
            return undefined;
        }
        const symbols = type.getProperties();
        if (!symbols || symbols.length === 0)
            return undefined;
        const properties = new Map();
        for (const symbol of symbols) {
            const name = symbol.getName();
            let typeStr = 'unknown';
            try {
                const propType = checker.getTypeOfSymbolAtLocation(symbol, typeNode);
                typeStr = checker.typeToString(propType, typeNode, ts.TypeFormatFlags.NoTruncation | ts.TypeFormatFlags.UseSingleQuotesForStringLiteralType);
            }
            catch {
                typeStr = 'unknown';
            }
            const optional = (symbol.getFlags() & ts.SymbolFlags.Optional) !== 0;
            properties.set(name, { name, type: typeStr, optional });
        }
        return properties;
    }
    /**
     * Resolve a TypeNode that represents the constructor-args generic
     * (TArgs in `define<TInstance, TArgs>`) into a ConstructorParamInfo
     * array. We treat the args type as the shape of a single positional
     * argument named `data`, mirroring the conventional
     * `function(this, data) { … }` signature. When the args type is a
     * tuple, each tuple element becomes a positional parameter.
     */
    resolveConstructorParamsFromTypeNode(typeNode) {
        const checker = this.getTypeChecker();
        if (!checker)
            return undefined;
        let type;
        try {
            type = checker.getTypeFromTypeNode(typeNode);
        }
        catch {
            return undefined;
        }
        // Tuple shape: TArgs = [Foo, Bar] -> two positional params.
        if (checker.isTupleType(type)) {
            const tupleArgs = type.typeArguments ?? [];
            const params = [];
            for (let i = 0; i < tupleArgs.length; i++) {
                const elementType = tupleArgs[i];
                const typeStr = checker.typeToString(elementType, typeNode, ts.TypeFormatFlags.NoTruncation);
                params.push({ name: `arg${i}`, type: typeStr, optional: false });
            }
            return params;
        }
        // Object shape: TArgs = { x: number; y: number } -> single `data` param.
        const symbols = type.getProperties();
        if (symbols && symbols.length > 0) {
            const props = [];
            for (const symbol of symbols) {
                const name = symbol.getName();
                const optional = (symbol.getFlags() & ts.SymbolFlags.Optional) !== 0;
                let typeStr = 'unknown';
                try {
                    const propType = checker.getTypeOfSymbolAtLocation(symbol, typeNode);
                    typeStr = checker.typeToString(propType, typeNode, ts.TypeFormatFlags.NoTruncation);
                }
                catch {
                    typeStr = 'unknown';
                }
                props.push(`${name}${optional ? '?' : ''}: ${typeStr}`);
            }
            return [{ name: 'data', type: `{ ${props.join('; ')} }`, optional: false }];
        }
        // Primitive / unresolvable — fall back to a single typed `data` param.
        const typeStr = checker.typeToString(type, typeNode, ts.TypeFormatFlags.NoTruncation);
        if (typeStr && typeStr !== 'any' && typeStr !== 'unknown') {
            return [{ name: 'data', type: typeStr, optional: false }];
        }
        return undefined;
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
     * Compare each TypeNode's declared shape (from generic args or `this:`
     * annotation) against its inferred shape (from constructor body) and
     * return a list of drift reports.
     *
     * Heuristics:
     *  - Suppress reports when there is no declared shape, since inference
     *    is the only source of truth in that case.
     *  - Suppress reports when the body uses `Object.assign(this, data)`
     *    style — i.e. inferred set is empty — because the assignments
     *    aren't visible textually. Only contradictory inferred entries
     *    raise drift.
     *  - Compare type strings as-is (the TypeChecker normalizes them).
     */
    detectDrift() {
        const reports = [];
        for (const node of this.graph.allTypes.values()) {
            const declared = node.declaredProperties;
            if (!declared || declared.size === 0)
                continue;
            const inferred = node.properties;
            const inferredHasContent = inferred && inferred.size > 0;
            // declared but body never assigns anything → likely Object.assign
            // pattern, not drift.
            if (!inferredHasContent)
                continue;
            // 1. Type mismatches on overlapping keys.
            for (const [key, declaredProp] of declared) {
                const inferredProp = inferred.get(key);
                if (!inferredProp) {
                    // declared but never assigned: report only if the user's
                    // inferred set is otherwise non-trivial (contradictory)
                    reports.push({
                        typeName: node.fullPath,
                        fileName: node.sourceFile,
                        line: node.line,
                        key,
                        declaredType: declaredProp.type,
                        inferredType: undefined,
                        kind: 'declaredOnly',
                        message: `${node.fullPath}.${key}: declared as '${declaredProp.type}' but never assigned in constructor body`,
                    });
                    continue;
                }
                if (declaredProp.type !== inferredProp.type &&
                    inferredProp.type !== 'unknown' &&
                    declaredProp.type !== 'unknown') {
                    reports.push({
                        typeName: node.fullPath,
                        fileName: node.sourceFile,
                        line: node.line,
                        key,
                        declaredType: declaredProp.type,
                        inferredType: inferredProp.type,
                        kind: 'typeMismatch',
                        message: `${node.fullPath}.${key}: declared '${declaredProp.type}' but body assigns '${inferredProp.type}'`,
                    });
                }
            }
            // 2. Inferred keys not in declaration.
            if (inferred) {
                for (const [key, inferredProp] of inferred) {
                    if (!declared.has(key)) {
                        reports.push({
                            typeName: node.fullPath,
                            fileName: node.sourceFile,
                            line: node.line,
                            key,
                            declaredType: undefined,
                            inferredType: inferredProp.type,
                            kind: 'inferredOnly',
                            message: `${node.fullPath}.${key}: assigned in body but not declared`,
                        });
                    }
                }
            }
        }
        return reports;
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
        // Check for define() calls
        if (this.isDefineCall(node)) {
            this.processDefineCall(node, sourceFile);
        }
        // Check for decorate() decorator
        if (this.isDecorateDecorator(node)) {
            this.processDecorateDecorator(node, sourceFile, currentClass);
        }
        // Check for type usages (new Type(), type annotations, etc.)
        this.collectUsage(node, sourceFile);
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
     * Check if a node is a define() call
     */
    isDefineCall(node) {
        if (!ts.isCallExpression(node)) {
            return false;
        }
        const expression = node.expression;
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
        * Extract config options from define() call
        */
    extractConfig(call) {
        const config = {};
        // Config is the third argument: define('Name', handler, config)
        const configArg = call.arguments[2];
        if (!configArg || !ts.isObjectLiteralExpression(configArg)) {
            return config;
        }
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
        * Check if a node is a @decorate() decorator
        */
    isDecorateDecorator(node) {
        if (!ts.isDecorator(node)) {
            return false;
        }
        const expression = node.expression;
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
        }
        return false;
    }
    /**
     * Process a define() call
     */
    processDefineCall(call, sourceFile) {
        // Check if this exact call has already been processed (prevents duplicates from chained calls)
        if (call.__tactica_processed) {
            return;
        }
        call.__tactica_processed = true;
        // Get the type name from arguments
        const typeName = this.extractTypeName(call);
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
        if (!typeName) {
            this.errors.push({
                message: 'Could not extract type name from define() call',
                file: sourceFile.fileName,
                line: line + 1,
                column: character + 1,
            });
            return;
        }
        // Determine parent type
        const parentNode = this.findParentType(call, sourceFile);
        // Build full path
        const fullPath = parentNode ? `${parentNode.fullPath}.${typeName}` : typeName;
        // Extract config options
        const config = this.extractConfig(call);
        // Create definition info
        const definition = {
            name: typeName,
            location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
            kind: 'define',
            parent: parentNode ? parentNode.fullPath : null,
            strictChain: config.strictChain ?? true,
            blockErrors: config.blockErrors ?? false,
        };
        this.definitions.set(fullPath, definition);
        // Create type node
        const node = graph_1.TypeGraphImpl.createNode(typeName, parentNode, sourceFile.fileName, line + 1, character + 1);
        // Extract properties from constructor function
        node.properties = this.extractProperties(call);
        // Extract constructor parameters for TypeRegistry signature
        node.constructorParams = this.extractConstructorParams(call);
        // Declared shape: prefer explicit generic args on define<TInstance, TArgs>(…).
        // Only populated when ts.Program is available (CLI path).
        // The generator treats declaredProperties / declaredConstructorParams
        // as authoritative when set, and the drift detector compares them
        // against the inference above.
        const declaredFromGenerics = this.extractDeclaredFromGenerics(call);
        if (declaredFromGenerics.properties) {
            node.declaredProperties = declaredFromGenerics.properties;
            node.propertiesSource = 'generic';
        }
        if (declaredFromGenerics.constructorParams) {
            node.declaredConstructorParams = declaredFromGenerics.constructorParams;
        }
        // Fallback declared shape: explicit `this:` annotation, resolved
        // through the TypeChecker so cross-file aliases work too.
        if (!node.declaredProperties) {
            const declaredFromThis = this.extractDeclaredFromThisAnnotation(call);
            if (declaredFromThis) {
                node.declaredProperties = declaredFromThis;
                node.propertiesSource = 'thisAnnotation';
            }
        }
        // If nothing declared, the inferred shape *is* the canonical view.
        if (!node.propertiesSource) {
            node.propertiesSource = 'inference';
        }
        // Add to graph
        if (parentNode) {
            this.graph.addChild(parentNode, node);
        }
        else {
            this.graph.addRoot(node);
        }
        // Track variable assignment: const User = define('UserEntity', ...) -> map "User" to "UserEntity"
        // For chained calls like const X = define('A').define('B'), we want to map X -> A (the root)
        this.trackVariableAssignment(call, parentNode, fullPath);
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
        * Track variable assignments from lookupTyped() calls
        * e.g., const SentienceConstructor = lookupTyped('Sentience') maps "SentienceConstructor" -> "Sentience"
        */
    trackLookupTypedAssignment(call, typePath) {
        // Walk up the tree to find VariableDeclaration
        let current = call.parent;
        while (current) {
            if (ts.isVariableDeclaration(current)) {
                // Found: const X = lookupTyped(...)
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
        // Try to find parent type from decorator arguments
        let parentNode;
        let parentFullPath = null;
        if (ts.isCallExpression(decorator.expression)) {
            const args = decorator.expression.arguments;
            if (args.length > 0 && ts.isIdentifier(args[0])) {
                const parentName = args[0].text;
                // First try exact match
                parentNode = this.graph.findType(parentName);
                // Then search through all types for one with matching name
                if (!parentNode) {
                    for (const type of this.graph.getAllTypes()) {
                        if (type.name === parentName) {
                            parentNode = type;
                            break;
                        }
                    }
                }
                if (parentNode) {
                    parentFullPath = parentNode.fullPath;
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
            strictChain: true, // decorate uses strict defaults
            blockErrors: false,
        };
        this.definitions.set(fullPath, definition);
        // Create type node
        const node = graph_1.TypeGraphImpl.createNode(typeName, parentNode, sourceFile.fileName, line + 1, character + 1);
        // Extract properties from class members
        node.properties = this.extractClassProperties(classDecl);
        // Add to graph
        if (parentNode) {
            this.graph.addChild(parentNode, node);
        }
        else {
            this.graph.addRoot(node);
        }
    }
    /**
     * Extract type name from define() call arguments
     */
    extractTypeName(call) {
        const args = call.arguments;
        // define('TypeName', handler) or define(() => class)
        if (args.length === 0) {
            return undefined;
        }
        const firstArg = args[0];
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
            const body = firstArg.body;
            if (ts.isClassExpression(body) && body.name) {
                return body.name.text;
            }
        }
        return undefined;
    }
    /**
     * Find parent type node for nested define calls
     */
    findParentType(call, _sourceFile) {
        const expression = call.expression;
        // Check for method call: SomeType.define('SubType', ...)
        if (!ts.isPropertyAccessExpression(expression)) {
            return undefined;
        }
        // Get the object being called on (SomeType in SomeType.define)
        const obj = expression.expression;
        if (ts.isIdentifier(obj)) {
            // Direct reference to parent type - search by simple name
            const name = obj.text;
            // First check variable mapping: const User = define('UserEntity', ...)
            // In this case, name is "User" but we need to find "UserEntity"
            const mappedFullPath = this.variableToTypeMap.get(name);
            if (mappedFullPath) {
                const mappedNode = this.graph.findType(mappedFullPath);
                if (mappedNode)
                    return mappedNode;
            }
            // First try exact match
            const exact = this.graph.findType(name);
            if (exact)
                return exact;
            // Then search through all types for one with matching name
            for (const type of this.graph.getAllTypes()) {
                if (type.name === name) {
                    return type;
                }
            }
            return undefined;
        }
        if (ts.isPropertyAccessExpression(obj)) {
            // Nested access: instance.Type.define - try to resolve
            const chain = this.getPropertyChain(obj);
            if (chain.length > 0) {
                return this.graph.findType(chain.join('.'));
            }
        }
        // Handle chained define: define('UserEntity', ...).define('UserResponse', ...)
        if (ts.isCallExpression(obj)) {
            // This is a chained call - the object is itself a define() call
            // Check if the parent call is a define() that hasn't been processed yet
            if (this.isDefineCall(obj)) {
                // Process the parent define() call first to create its type node
                // Use the sourceFile from the current context
                this.processDefineCall(obj, _sourceFile);
                // Now find and return the newly created parent type
                const parentTypeName = this.extractTypeName(obj);
                if (parentTypeName) {
                    return this.findParentTypeByName(parentTypeName);
                }
            }
        }
        return undefined;
    }
    /**
        * Find a parent type by its name, searching in the graph
        */
    findParentTypeByName(name) {
        // First try exact match
        const exact = this.graph.findType(name);
        if (exact)
            return exact;
        // Then search through all types for one with matching name
        for (const type of this.graph.getAllTypes()) {
            if (type.name === name) {
                return type;
            }
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
     * Extract properties from constructor function
     */
    extractProperties(call) {
        const properties = new Map();
        const handlerArg = call.arguments[1];
        if (!handlerArg) {
            return properties;
        }
        // Build type map from data parameter (for this.x = data.x patterns)
        const dataTypeMap = this.buildDataTypeMap(handlerArg);
        // Handle function expression
        if (ts.isFunctionExpression(handlerArg) || ts.isArrowFunction(handlerArg)) {
            const body = handlerArg.body;
            // First, extract properties from `this` parameter type annotation
            // This handles patterns like: function(this: SomeType, data: SomeType) { }
            const thisParamProperties = this.extractThisParamProperties(handlerArg);
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
        if (ts.isClassExpression(handlerArg)) {
            // First pass: collect all property types for method inference
            const classPropertyTypes = this.extractClassPropertyTypes(handlerArg);
            for (const member of handlerArg.members) {
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
                        const hasPrivateOrProtected = member.modifiers.some(m => m.kind === ts.SyntaxKind.PrivateKeyword ||
                            m.kind === ts.SyntaxKind.ProtectedKeyword);
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
            const left = expr.left;
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
                        properties.set(name, {
                            name,
                            type,
                            optional: false,
                        });
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
                return 'Array<' + this.inferType(typeNode.elementType) + '>';
            case ts.SyntaxKind.TypeLiteral:
                return 'object';
            case ts.SyntaxKind.LiteralType: {
                // Handle string literal types like 'user', 'admin', etc.
                const literal = typeNode.literal;
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
                            const typeName = typeQuery.exprName.text;
                            // Look up the type in the graph to get full path
                            const typeNode = this.graph.findTypeByName(typeName);
                            if (typeNode) {
                                // Convert full path with dots to underscores: Usages.UsageEntry -> Usages_UsageEntry
                                return typeNode.fullPath.replace(/\./g, '_');
                            }
                            // Fallback: just use the type name if not found in graph
                            return typeName;
                        }
                    }
                }
                if (!typeRef.typeArguments || typeRef.typeArguments.length === 0) {
                    // Check if this type exists in our graph - convert to full path format
                    const typeNode = this.graph.findTypeByName(typeName);
                    if (typeNode) {
                        // Convert full path with dots to underscores: Usages.UsageEntry -> Usages_UsageEntry
                        return typeNode.fullPath.replace(/\./g, "_");
                    }
                    return typeName;
                }
                // Build generic type arguments
                const args = typeRef.typeArguments.map(arg => this.inferType(arg));
                return `${typeName}<${args.join(', ')}>`;
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
                return this.inferType(optionalType.type) + '?';
            }
            case ts.SyntaxKind.RestType: {
                // Handle rest element: ...T
                const restType = typeNode;
                return '...' + this.inferType(restType.type);
            }
            case ts.SyntaxKind.ParenthesizedType: {
                // Handle parenthesized types: (A | B)
                return this.inferType(typeNode.type);
            }
            case ts.SyntaxKind.IndexedAccessType: {
                // Handle indexed access: T[K]
                const indexed = typeNode;
                const objectType = this.inferType(indexed.objectType);
                const indexType = this.inferType(indexed.indexType);
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
            const typeName = this.getTypeNameFromExpression(node.expression);
            if (typeName) {
                const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                this.addUsage(typeName, {
                    location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
                    kind: 'instantiation',
                    code: node.getText(sourceFile).slice(0, 100),
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
        // Check for lookupTyped('TypeName') calls
        if (ts.isCallExpression(node) && node.expression) {
            const funcName = this.getFunctionName(node.expression);
            if (funcName === 'lookupTyped' && node.arguments.length > 0) {
                const firstArg = node.arguments[0];
                if (ts.isStringLiteral(firstArg) || ts.isNoSubstitutionTemplateLiteral(firstArg)) {
                    const typePath = firstArg.text;
                    const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                    this.addUsage(typePath, {
                        location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
                        kind: 'lookup',
                        code: node.getText(sourceFile).slice(0, 100),
                    });
                    // Track variable assignment from lookupTyped for instantiation tracking
                    this.trackLookupTypedAssignment(node, typePath);
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
        * Get type name from expression (identifier or property access)
        */
    getTypeNameFromExpression(expr) {
        if (ts.isIdentifier(expr)) {
            const name = expr.text;
            // Check if this identifier is a variable mapped to a type (e.g., from lookupTyped)
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
     * Extract the user-declared instance / args shapes from explicit
     * generic arguments on `define<TInstance, TArgs>(…)`.
     *
     * Returns whatever subset can be resolved — both, one, or neither.
     * Requires a TypeChecker (CLI path); silently no-ops without one.
     */
    extractDeclaredFromGenerics(call) {
        const result = {};
        if (!call.typeArguments || call.typeArguments.length === 0)
            return result;
        const tInstance = call.typeArguments[0];
        if (tInstance) {
            const props = this.resolvePropertiesFromTypeNode(tInstance);
            if (props && props.size > 0)
                result.properties = props;
        }
        const tArgs = call.typeArguments[1];
        if (tArgs) {
            const params = this.resolveConstructorParamsFromTypeNode(tArgs);
            if (params && params.length > 0)
                result.constructorParams = params;
        }
        return result;
    }
    /**
     * Extract user-declared instance shape from the constructor's
     * `this:` annotation, resolved via the TypeChecker so imported
     * type aliases work across files. Returns undefined when no checker
     * is available or the annotation is missing.
     */
    extractDeclaredFromThisAnnotation(call) {
        const handlerArg = call.arguments[1];
        if (!handlerArg)
            return undefined;
        if (!ts.isFunctionExpression(handlerArg) && !ts.isArrowFunction(handlerArg))
            return undefined;
        for (const param of handlerArg.parameters) {
            if (param.name &&
                ts.isIdentifier(param.name) &&
                param.name.text === 'this' &&
                param.type) {
                const props = this.resolvePropertiesFromTypeNode(param.type);
                if (props && props.size > 0)
                    return props;
                return undefined;
            }
        }
        return undefined;
    }
    /**
         * Extract constructor parameters from define() call
         * This is used for TypeRegistry constructor signatures
         * Preserves parameter names and expands object types to their structure
         */
    extractConstructorParams(call) {
        const params = [];
        const handlerArg = call.arguments[1];
        if (!handlerArg)
            return params;
        // Helper to resolve type alias and extract properties
        const resolveTypeAndExtract = (typeNode) => {
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
                    const expanded = resolveTypeAndExtract(aliasedType);
                    if (expanded)
                        return expanded;
                }
                // If not an object type alias, return the type name
                return typeName;
            }
            return undefined;
        };
        // Handle function expression or arrow function
        if (ts.isFunctionExpression(handlerArg) || ts.isArrowFunction(handlerArg)) {
            // Look for constructor parameters (second param after `this`)
            // Patterns: function(this: Type, data: { ... }) or (this: Type, data: { ... }) =>
            for (let i = 0; i < handlerArg.parameters.length; i++) {
                const param = handlerArg.parameters[i];
                if (!param.type)
                    continue;
                // Skip `this` parameter (first param)
                if (i === 0 && param.name.kind === ts.SyntaxKind.Identifier && param.name.text === 'this') {
                    continue;
                }
                // Get parameter name and expand its type
                const paramName = ts.isIdentifier(param.name) ? param.name.text : 'arg';
                const expandedType = resolveTypeAndExtract(param.type) || this.inferType(param.type);
                params.push({
                    name: paramName,
                    type: expandedType,
                    optional: !!param.questionToken || !!param.initializer
                });
            }
        }
        // Handle class expression - check constructor method
        if (ts.isClassExpression(handlerArg)) {
            for (const member of handlerArg.members) {
                if (ts.isConstructorDeclaration(member)) {
                    for (const param of member.parameters) {
                        if (!param.name || !ts.isIdentifier(param.name))
                            continue;
                        if (param.type) {
                            const paramName = param.name.text;
                            const expandedType = resolveTypeAndExtract(param.type) || this.inferType(param.type);
                            params.push({
                                name: paramName,
                                type: expandedType,
                                optional: !!param.questionToken || !!param.initializer
                            });
                        }
                    }
                    break; // Only process first constructor
                }
            }
        }
        return params;
    }
}
exports.MnemonicaAnalyzer = MnemonicaAnalyzer;
//# sourceMappingURL=analyzer.js.map