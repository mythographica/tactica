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
exports.TopologicaAnalyzer = void 0;
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const ts = __importStar(require("typescript"));
const graph_1 = require("./graph");
/**
 * Analyzer for Topologica directory-based type definitions
 * Scans directory structures to create type hierarchies like:
 * ai-types/Sentience/Consciousness/Empathy/Gratitude/
 *
 * Now with AST-based property extraction from TypeScript/JavaScript files
 */
class TopologicaAnalyzer {
    constructor() {
        this.errors = [];
        this.graph = new graph_1.TypeGraphImpl();
    }
    /**
     * Analyze a directory structure for topologica type definitions
     */
    analyzeDirectory(directoryPath) {
        this.errors = [];
        if (!fs.existsSync(directoryPath)) {
            this.errors.push(`Directory does not exist: ${directoryPath}`);
            return { types: this.graph.allTypes, errors: this.errors };
        }
        if (!fs.statSync(directoryPath).isDirectory()) {
            this.errors.push(`Path is not a directory: ${directoryPath}`);
            return { types: this.graph.allTypes, errors: this.errors };
        }
        this.scanDirectory(directoryPath, undefined, directoryPath);
        return {
            types: this.graph.allTypes,
            errors: this.errors,
        };
    }
    /**
     * Recursively scan directory structure to build type hierarchy
     */
    scanDirectory(currentPath, parentNode, rootPath) {
        try {
            const entries = fs.readdirSync(currentPath, { withFileTypes: true });
            for (const entry of entries) {
                if (entry.isDirectory()) {
                    // Create type node for this directory
                    const typeName = entry.name;
                    const fullPath = parentNode ? `${parentNode.fullPath}.${typeName}` : typeName;
                    const dirPath = path.join(currentPath, entry.name);
                    // Extract properties and constructor params from the handler file if it exists
                    const { properties, constructorParams, handlerLocation } = this.extractPropertiesFromDir(dirPath);
                    // Create the type node with proper source location for Go to Definition
                    const typeNode = {
                        name: typeName,
                        fullPath: fullPath,
                        properties: properties,
                        constructorParams: constructorParams,
                        parent: parentNode,
                        children: new Map(),
                        sourceFile: handlerLocation?.filePath || dirPath,
                        line: handlerLocation?.line || 0,
                        column: handlerLocation?.column || 0,
                        constructorName: typeName
                    };
                    // Add to graph
                    if (parentNode) {
                        this.graph.addChild(parentNode, typeNode);
                    }
                    else {
                        // Add as root type
                        this.graph.addRoot(typeNode);
                    }
                    // Scan children of this directory
                    this.scanDirectory(dirPath, typeNode, rootPath);
                }
            }
        }
        catch (error) {
            this.errors.push(`Error scanning directory ${currentPath}: ${error.message}`);
        }
    }
    /**
     * Extract properties from a directory's index file
     * Supports both .ts and .js files
     */
    extractPropertiesFromDir(dirPath) {
        const properties = new Map();
        let constructorParams;
        // Check for TypeScript file first, then JavaScript
        const tsFile = path.join(dirPath, 'index.ts');
        const jsFile = path.join(dirPath, 'index.js');
        let targetFile;
        if (fs.existsSync(tsFile)) {
            targetFile = tsFile;
        }
        else if (fs.existsSync(jsFile)) {
            targetFile = jsFile;
        }
        if (!targetFile) {
            return { properties };
        }
        // Default location points to the index file (will be updated if handler found)
        let handlerLocation;
        try {
            const content = fs.readFileSync(targetFile, 'utf-8');
            const sourceFile = ts.createSourceFile(targetFile, content, ts.ScriptTarget.Latest, true);
            // Collect type aliases from the file (e.g., SentienceData = { ... })
            const typeAliases = this.collectTypeAliases(sourceFile);
            // Find handler function and extract property assignments and constructor params
            const result = this.extractPropertiesFromSourceFile(sourceFile, properties, typeAliases);
            constructorParams = result.constructorParams;
            // Use the handler function location if found
            if (result.handlerLocation) {
                handlerLocation = result.handlerLocation;
            }
        }
        catch (error) {
            this.errors.push(`Error parsing ${targetFile}: ${error.message}`);
        }
        return { properties, constructorParams, handlerLocation };
    }
    /**
     * Collect type aliases from source file
     * e.g., export type SentienceData = { awareness?: string; }
     */
    collectTypeAliases(sourceFile) {
        const typeAliases = new Map();
        const visit = (node) => {
            // Look for type alias declarations: export type Name = Type;
            if (ts.isTypeAliasDeclaration(node)) {
                const name = node.name.text;
                typeAliases.set(name, node.type);
            }
            ts.forEachChild(node, visit);
        };
        visit(sourceFile);
        return typeAliases;
    }
    /**
     * Extract property assignments from a source file
     * Returns constructor parameters and handler location if found
     */
    extractPropertiesFromSourceFile(sourceFile, properties, typeAliases) {
        let constructorParams;
        let handlerLocation;
        const visit = (node) => {
            // Look for exported function declarations (topologica convention: one exported function per file)
            if (ts.isFunctionDeclaration(node) && node.name) {
                // Check if it's exported
                const isExported = node.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword);
                if (isExported) {
                    this.extractThisProperties(node, properties);
                    // Extract constructor params and location from the exported function
                    if (!constructorParams) {
                        constructorParams = this.extractConstructorParams(node, typeAliases);
                        // Capture the function location
                        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                        handlerLocation = {
                            filePath: sourceFile.fileName,
                            line: line + 1, // 1-based
                            column: character + 1 // 1-based
                        };
                    }
                }
            }
            // Also check function expressions/arrow functions assigned to exports
            else if (ts.isFunctionExpression(node) || ts.isArrowFunction(node)) {
                this.extractThisProperties(node, properties);
                // Extract constructor params from non-exported functions too
                if (!constructorParams) {
                    constructorParams = this.extractConstructorParams(node, typeAliases);
                    // Capture the function location
                    const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                    handlerLocation = {
                        filePath: sourceFile.fileName,
                        line: line + 1, // 1-based
                        column: character + 1 // 1-based
                    };
                }
            }
            ts.forEachChild(node, visit);
        };
        visit(sourceFile);
        return { constructorParams, handlerLocation };
    }
    /**
     * Extract `this.property = value` assignments from a function body
     */
    extractThisProperties(func, properties) {
        const { body } = func;
        if (!body)
            return;
        const visitStatements = (node) => {
            // Handle expression statements
            if (ts.isExpressionStatement(node)) {
                const expr = node.expression;
                // Check for this.prop = value
                if (ts.isBinaryExpression(expr) &&
                    expr.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
                    const { left } = expr;
                    const { right } = expr;
                    // Check if left side is this.property
                    if (ts.isPropertyAccessExpression(left) &&
                        left.expression.kind === ts.SyntaxKind.ThisKeyword) {
                        const propName = left.name.text;
                        const propType = this.inferType(right);
                        properties.set(propName, {
                            name: propName,
                            type: propType,
                            optional: false,
                            readonly: false
                        });
                    }
                }
                // Check for Object.assign(this, {...})
                if (ts.isCallExpression(expr)) {
                    const callExpr = expr;
                    if (this.isObjectAssignCall(callExpr)) {
                        this.extractFromObjectAssign(callExpr, properties);
                    }
                }
            }
            ts.forEachChild(node, visitStatements);
        };
        visitStatements(body);
    }
    /**
     * Check if a call expression is Object.assign(this, ...)
     */
    isObjectAssignCall(callExpr) {
        const expr = callExpr.expression;
        if (!ts.isPropertyAccessExpression(expr))
            return false;
        const objName = ts.isIdentifier(expr.expression) ? expr.expression.text : null;
        const methodName = expr.name.text;
        if (objName === 'Object' && methodName === 'assign') {
            const firstArg = callExpr.arguments[0];
            if (firstArg && firstArg.kind === ts.SyntaxKind.ThisKeyword) {
                return true;
            }
        }
        return false;
    }
    /**
     * Extract properties from Object.assign(this, data) pattern
     */
    extractFromObjectAssign(callExpr, properties) {
        // Look for the data argument (second argument)
        const dataArg = callExpr.arguments[1];
        if (!dataArg)
            return;
        // If it's an object literal, extract properties
        if (ts.isObjectLiteralExpression(dataArg)) {
            for (const prop of dataArg.properties) {
                if (ts.isPropertyAssignment(prop) && ts.isIdentifier(prop.name)) {
                    const propName = prop.name.text;
                    const propType = this.inferType(prop.initializer);
                    properties.set(propName, {
                        name: propName,
                        type: propType,
                        optional: false,
                        readonly: false
                    });
                }
            }
        }
    }
    /**
     * Extract constructor parameters from a function
     * Similar to main analyzer - skips `this` parameter and expands data types
     */
    extractConstructorParams(func, typeAliases) {
        if (!func.parameters || func.parameters.length === 0) {
            return undefined;
        }
        const params = [];
        // Skip `this` parameter (first param) and extract data parameters
        for (let i = 0; i < func.parameters.length; i++) {
            const param = func.parameters[i];
            // Skip `this` parameter (first param)
            if (i === 0 && param.name.kind === ts.SyntaxKind.Identifier &&
                param.name.text === 'this') {
                continue;
            }
            if (!param.type)
                continue;
            const paramName = ts.isIdentifier(param.name) ? param.name.text : 'arg';
            const optional = param.questionToken !== undefined || param.initializer !== undefined;
            // Expand type to object literal if possible
            const expandedType = this.expandTypeToObject(param.type, typeAliases);
            const paramType = expandedType || this.typeNodeToSimpleString(param.type);
            params.push({
                name: paramName,
                type: paramType,
                optional: optional
            });
        }
        return params.length > 0 ? params : undefined;
    }
    /**
     * Expand a type node to its object literal representation
     * Similar to main analyzer's resolveTypeAndExtract
     */
    expandTypeToObject(typeNode, typeAliases) {
        // Direct inline type literal: { prop: type }
        if (ts.isTypeLiteralNode(typeNode)) {
            const props = [];
            for (const member of typeNode.members) {
                if (ts.isPropertySignature(member) && ts.isIdentifier(member.name)) {
                    const propName = member.name.text;
                    const opt = member.questionToken ? '?' : '';
                    const type = this.typeNodeToSimpleString(member.type);
                    props.push(`${propName}${opt}: ${type}`);
                }
            }
            return `{ ${props.join('; ')} }`;
        }
        // Type reference: SentienceData, etc. - try to expand from type aliases
        if (ts.isTypeReferenceNode(typeNode) && ts.isIdentifier(typeNode.typeName)) {
            const typeName = typeNode.typeName.text;
            // If we have type aliases, try to expand the referenced type
            if (typeAliases) {
                const aliasedType = typeAliases.get(typeName);
                if (aliasedType) {
                    const expanded = this.expandTypeToObject(aliasedType, typeAliases);
                    if (expanded)
                        return expanded;
                }
            }
            // If not an object type alias, return the type name
            return typeName;
        }
        return undefined;
    }
    /**
     * Convert a TypeScript type node to a simple string representation
     */
    typeNodeToSimpleString(typeNode) {
        if (!typeNode)
            return 'any';
        switch (typeNode.kind) {
            case ts.SyntaxKind.StringKeyword:
                return 'string';
            case ts.SyntaxKind.NumberKeyword:
                return 'number';
            case ts.SyntaxKind.BooleanKeyword:
                return 'boolean';
            case ts.SyntaxKind.AnyKeyword:
                return 'any';
            case ts.SyntaxKind.ArrayType:
                return 'Array<any>';
            case ts.SyntaxKind.TypeReference: {
                const typeRef = typeNode;
                if (ts.isIdentifier(typeRef.typeName)) {
                    return typeRef.typeName.text;
                }
                return 'any';
            }
            default:
                return 'any';
        }
    }
    /**
     * Infer TypeScript type from an expression
     */
    inferType(node) {
        switch (node.kind) {
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
                return 'Array<any>';
            case ts.SyntaxKind.ObjectLiteralExpression:
                return 'object';
            case ts.SyntaxKind.NewExpression:
                return this.inferNewExpressionType(node);
            case ts.SyntaxKind.ConditionalExpression:
                return this.inferType(node.whenTrue);
            case ts.SyntaxKind.BinaryExpression: {
                const binExpr = node;
                // Check for logical OR pattern: value || default
                if (binExpr.operatorToken.kind === ts.SyntaxKind.BarBarToken) {
                    // Return the type of the right side (the default value)
                    return this.inferType(binExpr.right);
                }
                return 'any';
            }
            case ts.SyntaxKind.PropertyAccessExpression: {
                const propAccess = node;
                // Handle data?.property patterns
                return this.inferType(propAccess);
            }
            case ts.SyntaxKind.CallExpression: {
                const callExpr = node;
                return this.inferCallExpressionType(callExpr);
            }
            default:
                return 'any';
        }
    }
    /**
     * Infer type from new expressions like new Date(), new Array(), etc.
     */
    inferNewExpressionType(node) {
        const expr = node.expression;
        if (ts.isIdentifier(expr)) {
            switch (expr.text) {
                case 'Date':
                    return 'number'; // Date.now() returns number
                case 'Array':
                    return 'Array<any>';
                case 'Map':
                    return 'Map<any, any>';
                case 'Set':
                    return 'Set<any>';
                case 'RegExp':
                    return 'RegExp';
                default:
                    return expr.text;
            }
        }
        return 'any';
    }
    /**
     * Infer type from call expressions like Date.now(), parseInt(), etc.
     */
    inferCallExpressionType(node) {
        const expr = node.expression;
        // Handle Date.now()
        if (ts.isPropertyAccessExpression(expr)) {
            const obj = expr.expression;
            const method = expr.name.text;
            if (ts.isIdentifier(obj) && obj.text === 'Date' && method === 'now') {
                return 'number';
            }
        }
        // Handle parseInt, parseFloat, String(), Number(), Boolean()
        if (ts.isIdentifier(expr)) {
            switch (expr.text) {
                case 'parseInt':
                case 'parseFloat':
                    return 'number';
                case 'String':
                    return 'string';
                case 'Number':
                    return 'number';
                case 'Boolean':
                    return 'boolean';
            }
        }
        return 'any';
    }
    /**
     * Get the type graph
     */
    getGraph() {
        return this.graph;
    }
    /**
     * Get collected errors
     */
    getErrors() {
        return this.errors;
    }
}
exports.TopologicaAnalyzer = TopologicaAnalyzer;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoidG9wb2xvZ2ljYS1hbmFseXplci5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzIjpbIi4uL3NyYy90b3BvbG9naWNhLWFuYWx5emVyLnRzIl0sIm5hbWVzIjpbXSwibWFwcGluZ3MiOiJBQUFBLFlBQVksQ0FBQzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7O0FBRWIsdUNBQXlCO0FBQ3pCLDJDQUE2QjtBQUM3QiwrQ0FBaUM7QUFJakMsbUNBQXdDO0FBRXhDOzs7Ozs7R0FNRztBQUNILE1BQWEsa0JBQWtCO0lBQS9CO1FBQ1MsV0FBTSxHQUFhLEVBQUUsQ0FBQztRQUN0QixVQUFLLEdBQUcsSUFBSSxxQkFBYSxFQUFFLENBQUM7SUF5aUJyQyxDQUFDO0lBdmlCQTs7T0FFRztJQUNILGdCQUFnQixDQUFFLGFBQXFCO1FBQ3RDLElBQUksQ0FBQyxNQUFNLEdBQUcsRUFBRSxDQUFDO1FBRWpCLElBQUksQ0FBQyxFQUFFLENBQUMsVUFBVSxDQUFDLGFBQWEsQ0FBQyxFQUFFLENBQUM7WUFDbkMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsNkJBQTZCLGFBQWEsRUFBRSxDQUFDLENBQUM7WUFDL0QsT0FBTyxFQUFFLEtBQUssRUFBRyxJQUFJLENBQUMsS0FBSyxDQUFDLFFBQVEsRUFBRSxNQUFNLEVBQUcsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDO1FBQzlELENBQUM7UUFFRCxJQUFJLENBQUMsRUFBRSxDQUFDLFFBQVEsQ0FBQyxhQUFhLENBQUMsQ0FBQyxXQUFXLEVBQUUsRUFBRSxDQUFDO1lBQy9DLElBQUksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLDRCQUE0QixhQUFhLEVBQUUsQ0FBQyxDQUFDO1lBQzlELE9BQU8sRUFBRSxLQUFLLEVBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLEVBQUUsTUFBTSxFQUFHLElBQUksQ0FBQyxNQUFNLEVBQUUsQ0FBQztRQUM5RCxDQUFDO1FBRUQsSUFBSSxDQUFDLGFBQWEsQ0FBQyxhQUFh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LENBQUM7Z0JBQ2pCLEtBQUssU0FBUztvQkFDYixPQUFPLFNBQVMsQ0FBQztZQUNsQixDQUFDO1FBQ0YsQ0FBQztRQUVELE9BQU8sS0FBSyxDQUFDO0lBQ2QsQ0FBQztJQUVEOztPQUVHO0lBQ0gsUUFBUTtRQUNQLE9BQU8sSUFBSSxDQUFDLEtBQUssQ0FBQztJQUNuQixDQUFDO0lBRUQ7O09BRUc7SUFDSCxTQUFTO1FBQ1IsT0FBTyxJQUFJLENBQUMsTUFBTSxDQUFDO0lBQ3BCLENBQUM7Q0FDRDtBQTNpQkQsZ0RBMmlCQyIsInNvdXJjZXNDb250ZW50IjpbIid1c2Ugc3RyaWN0JztcblxuaW1wb3J0ICogYXMgZnMgZnJvbSAnZnMnO1xuaW1wb3J0ICogYXMgcGF0aCBmcm9tICdwYXRoJztcbmltcG9ydCAqIGFzIHRzIGZyb20gJ3R5cGVzY3JpcHQnO1xuaW1wb3J0IHtcblx0VHlwZU5vZGUsIFByb3BlcnR5SW5mbywgQ29uc3RydWN0b3JQYXJhbUluZm8gXG59IGZyb20gJy4vdHlwZXMnO1xuaW1wb3J0IHsgVHlwZUdyYXBoSW1wbCB9IGZyb20gJy4vZ3JhcGgnO1xuXG4vKipcbiAqIEFuYWx5emVyIGZvciBUb3BvbG9naWNhIGRpcmVjdG9yeS1iYXNlZCB0eXBlIGRlZmluaXRpb25zXG4gKiBTY2FucyBkaXJlY3Rvcnkgc3RydWN0dXJlcyB0byBjcmVhdGUgdHlwZSBoaWVyYXJjaGllcyBsaWtlOlxuICogYWktdHlwZXMvU2VudGllbmNlL0NvbnNjaW91c25lc3MvRW1wYXRoeS9HcmF0aXR1ZGUvXG4gKiBcbiAqIE5vdyB3aXRoIEFTVC1iYXNlZCBwcm9wZXJ0eSBleHRyYWN0aW9uIGZyb20gVHlwZVNjcmlwdC9KYXZhU2NyaXB0IGZpbGVzXG4gKi9cbmV4cG9ydCBjbGFzcyBUb3BvbG9naWNhQW5hbHl6ZXIge1xuXHRwcml2YXRlIGVycm9yczogc3RyaW5nW10gPSBbXTtcblx0cHJpdmF0ZSBncmFwaCA9IG5ldyBUeXBlR3JhcGhJbXBsKCk7XG5cblx0LyoqXG5cdCAqIEFuYWx5emUgYSBkaXJlY3Rvcnkgc3RydWN0dXJlIGZvciB0b3BvbG9naWNhIHR5cGUgZGVmaW5pdGlvbnNcblx0ICovXG5cdGFuYWx5emVEaXJlY3RvcnkgKGRpcmVjdG9yeVBhdGg6IHN0cmluZyk6IHsgdHlwZXM6IE1hcDxzdHJpbmcsIFR5cGVOb2RlPiwgZXJyb3JzOiBzdHJpbmdbXSB9IHtcblx0XHR0aGlzLmVycm9ycyA9IFtdO1xuXHRcdFxuXHRcdGlmICghZnMuZXhpc3RzU3luYyhkaXJlY3RvcnlQYXRoKSkge1xuXHRcdFx0dGhpcy5lcnJvcnMucHVzaChgRGlyZWN0b3J5IGRvZXMgbm90IGV4aXN0OiAke2RpcmVjdG9yeVBhdGh9YCk7XG5cdFx0XHRyZXR1cm4geyB0eXBlcyA6IHRoaXMuZ3JhcGguYWxsVHlwZXMsIGVycm9ycyA6IHRoaXMuZXJyb3JzIH07XG5cdFx0fVxuXG5cdFx0aWYgKCFmcy5zdGF0U3luYyhkaXJlY3RvcnlQYXRoKS5pc0RpcmVjdG9yeSgpKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKGBQYXRoIGlzIG5vdCBhIGRpcmVjdG9yeTogJHtkaXJlY3RvcnlQYXRofWApO1xuXHRcdFx0cmV0dXJuIHsgdHlwZXMgOiB0aGlzLmdyYXBoLmFsbFR5cGVzLCBlcnJvcnMgOiB0aGlzLmVycm9ycyB9O1xuXHRcdH1cblxuXHRcdHRoaXMuc2NhbkRpcmVjdG9yeShkaXJlY3RvcnlQYXRoLCB1bmRlZmluZWQsIGRpcmVjdG9yeVBhdGgpO1xuXHRcdFxuXHRcdHJldHVybiB7XG5cdFx0XHR0eXBlcyAgOiB0aGlzLmdyYXBoLmFsbFR5cGVzLFxuXHRcdFx0ZXJyb3JzIDogdGhpcy5lcnJvcnMsXG5cdFx0fTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZWN1cnNpdmVseSBzY2FuIGRpcmVjdG9yeSBzdHJ1Y3R1cmUgdG8gYnVpbGQgdHlwZSBoaWVyYXJjaHlcblx0ICovXG5cdHByaXZhdGUgc2NhbkRpcmVjdG9yeSAoY3VycmVudFBhdGg6IHN0cmluZywgcGFyZW50Tm9kZTogVHlwZU5vZGUgfCB1bmRlZmluZWQsIHJvb3RQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHR0cnkge1xuXHRcdFx0Y29uc3QgZW50cmllcyA9IGZzLnJlYWRkaXJTeW5jKGN1cnJlbnRQYXRoLCB7IHdpdGhGaWxlVHlwZXMgOiB0cnVlIH0pO1xuXHRcdFx0XG5cdFx0XHRmb3IgKGNvbnN0IGVudHJ5IG9mIGVudHJpZXMpIHtcblx0XHRcdFx0aWYgKGVudHJ5LmlzRGlyZWN0b3J5KCkpIHtcblx0XHRcdFx0XHQvLyBDcmVhdGUgdHlwZSBub2RlIGZvciB0aGlzIGRpcmVjdG9yeVxuXHRcdFx0XHRcdGNvbnN0IHR5cGVOYW1lID0gZW50cnkubmFtZTtcblx0XHRcdFx0XHRjb25zdCBmdWxsUGF0aCA9IHBhcmVudE5vZGUgPyBgJHtwYXJlbnROb2RlLmZ1bGxQYXRofS4ke3R5cGVOYW1lfWAgOiB0eXBlTmFtZTtcblx0XHRcdFx0XHRjb25zdCBkaXJQYXRoID0gcGF0aC5qb2luKGN1cnJlbnRQYXRoLCBlbnRyeS5uYW1lKTtcblx0XHRcdFx0XHRcblx0XHRcdFx0XHQvLyBFeHRyYWN0IHByb3BlcnRpZXMgYW5kIGNvbnN0cnVjdG9yIHBhcmFtcyBmcm9tIHRoZSBoYW5kbGVyIGZpbGUgaWYgaXQgZXhpc3RzXG5cdFx0XHRcdFx0Y29uc3Qge1xuXHRcdFx0XHRcdFx0cHJvcGVydGllcywgY29uc3RydWN0b3JQYXJhbXMsIGhhbmRsZXJMb2NhdGlvbiBcblx0XHRcdFx0XHR9ID0gdGhpcy5leHRyYWN0UHJvcGVydGllc0Zyb21EaXIoZGlyUGF0aCk7XG5cdFx0XHRcdFx0XG5cdFx0XHRcdFx0Ly8gQ3JlYXRlIHRoZSB0eXBlIG5vZGUgd2l0aCBwcm9wZXIgc291cmNlIGxvY2F0aW9uIGZvciBHbyB0byBEZWZpbml0aW9uXG5cdFx0XHRcdFx0Y29uc3QgdHlwZU5vZGU6IFR5cGVOb2RlID0ge1xuXHRcdFx0XHRcdFx0bmFtZSAgICAgICAgICAgICAgOiB0eXBlTmFtZSxcblx0XHRcdFx0XHRcdGZ1bGxQYXRoICAgICAgICAgIDogZnVsbFBhdGgsXG5cdFx0XHRcdFx0XHRwcm9wZXJ0aWVzICAgICAgICA6IHByb3BlcnRpZXMsXG5cdFx0XHRcdFx0XHRjb25zdHJ1Y3RvclBhcmFtcyA6IGNvbnN0cnVjdG9yUGFyYW1zLFxuXHRcdFx0XHRcdFx0cGFyZW50ICAgICAgICAgICAgOiBwYXJlbnROb2RlLFxuXHRcdFx0XHRcdFx0Y2hpbGRyZW4gICAgICAgICAgOiBuZXcgTWFwKCksXG5cdFx0XHRcdFx0XHRzb3VyY2VGaWxlICAgICAgICA6IGhhbmRsZXJMb2NhdGlvbj8uZmlsZVBhdGggfHwgZGlyUGF0aCxcblx0XHRcdFx0XHRcdGxpbmUgICAgICAgICAgICAgIDogaGFuZGxlckxvY2F0aW9uPy5saW5lIHx8IDAsXG5cdFx0XHRcdFx0XHRjb2x1bW4gICAgICAgICAgICA6IGhhbmRsZXJMb2NhdGlvbj8uY29sdW1uIHx8IDAsXG5cdFx0XHRcdFx0XHRjb25zdHJ1Y3Rvck5hbWUgICA6IHR5cGVOYW1lXG5cdFx0XHRcdFx0fTtcblx0XHRcdFx0XHRcblx0XHRcdFx0XHQvLyBBZGQgdG8gZ3JhcGhcblx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0XHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChwYXJlbnROb2RlLCB0eXBlTm9kZSk7XG5cdFx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHRcdC8vIEFkZCBhcyByb290IHR5cGVcblx0XHRcdFx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdCh0eXBlTm9kZSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFxuXHRcdFx0XHRcdC8vIFNjYW4gY2hpbGRyZW4gb2YgdGhpcyBkaXJlY3Rvcnlcblx0XHRcdFx0XHR0aGlzLnNjYW5EaXJlY3RvcnkoZGlyUGF0aCwgdHlwZU5vZGUsIHJvb3RQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH0gY2F0Y2ggKGVycm9yKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKGBFcnJvciBzY2FubmluZyBkaXJlY3RvcnkgJHtjdXJyZW50UGF0aH06ICR7KGVycm9yIGFzIEVycm9yKS5tZXNzYWdlfWApO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBhIGRpcmVjdG9yeSdzIGluZGV4IGZpbGVcblx0ICogU3VwcG9ydHMgYm90aCAudHMgYW5kIC5qcyBmaWxlc1xuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UHJvcGVydGllc0Zyb21EaXIgKGRpclBhdGg6IHN0cmluZyk6IHtcblx0XHRwcm9wZXJ0aWVzOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+O1xuXHRcdGNvbnN0cnVjdG9yUGFyYW1zPzogQ29uc3RydWN0b3JQYXJhbUluZm9bXTtcblx0XHRoYW5kbGVyTG9jYXRpb24/OiB7IGZpbGVQYXRoOiBzdHJpbmc7IGxpbmU6IG51bWJlcjsgY29sdW1uOiBudW1iZXIgfTtcblx0fSB7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cdFx0bGV0IGNvbnN0cnVjdG9yUGFyYW1zOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdIHwgdW5kZWZpbmVkO1xuXHRcdFxuXHRcdC8vIENoZWNrIGZvciBUeXBlU2NyaXB0IGZpbGUgZmlyc3QsIHRoZW4gSmF2YVNjcmlwdFxuXHRcdGNvbnN0IHRzRmlsZSA9IHBhdGguam9pbihkaXJQYXRoLCAnaW5kZXgudHMnKTtcblx0XHRjb25zdCBqc0ZpbGUgPSBwYXRoLmpvaW4oZGlyUGF0aCwgJ2luZGV4LmpzJyk7XG5cdFx0XG5cdFx0bGV0IHRhcmdldEZpbGU6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRcblx0XHRpZiAoZnMuZXhpc3RzU3luYyh0c0ZpbGUpKSB7XG5cdFx0XHR0YXJnZXRGaWxlID0gdHNGaWxlO1xuXHRcdH0gZWxzZSBpZiAoZnMuZXhpc3RzU3luYyhqc0ZpbGUpKSB7XG5cdFx0XHR0YXJnZXRGaWxlID0ganNGaWxlO1xuXHRcdH1cblx0XHRcblx0XHRpZiAoIXRhcmdldEZpbGUpIHtcblx0XHRcdHJldHVybiB7IHByb3BlcnRpZXMgfTtcblx0XHR9XG5cdFx0XG5cdFx0Ly8gRGVmYXVsdCBsb2NhdGlvbiBwb2ludHMgdG8gdGhlIGluZGV4IGZpbGUgKHdpbGwgYmUgdXBkYXRlZCBpZiBoYW5kbGVyIGZvdW5kKVxuXHRcdGxldCBoYW5kbGVyTG9jYXRpb246IHsgZmlsZVBhdGg6IHN0cmluZzsgbGluZTogbnVtYmVyOyBjb2x1bW46IG51bWJlciB9IHwgdW5kZWZpbmVkO1xuXHRcdFxuXHRcdHRyeSB7XG5cdFx0XHRjb25zdCBjb250ZW50ID0gZnMucmVhZEZpbGVTeW5jKHRhcmdldEZpbGUsICd1dGYtOCcpO1xuXHRcdFx0Y29uc3Qgc291cmNlRmlsZSA9IHRzLmNyZWF0ZVNvdXJjZUZpbGUoXG5cdFx0XHRcdHRhcmdldEZpbGUsXG5cdFx0XHRcdGNvbnRlbnQsXG5cdFx0XHRcdHRzLlNjcmlwdFRhcmdldC5MYXRlc3QsXG5cdFx0XHRcdHRydWVcblx0XHRcdCk7XG5cdFx0XHRcblx0XHRcdC8vIENvbGxlY3QgdHlwZSBhbGlhc2VzIGZyb20gdGhlIGZpbGUgKGUuZy4sIFNlbnRpZW5jZURhdGEgPSB7IC4uLiB9KVxuXHRcdFx0Y29uc3QgdHlwZUFsaWFzZXMgPSB0aGlzLmNvbGxlY3RUeXBlQWxpYXNlcyhzb3VyY2VGaWxlKTtcblx0XHRcdFxuXHRcdFx0Ly8gRmluZCBoYW5kbGVyIGZ1bmN0aW9uIGFuZCBleHRyYWN0IHByb3BlcnR5IGFzc2lnbm1lbnRzIGFuZCBjb25zdHJ1Y3RvciBwYXJhbXNcblx0XHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMuZXh0cmFjdFByb3BlcnRpZXNGcm9tU291cmNlRmlsZShzb3VyY2VGaWxlLCBwcm9wZXJ0aWVzLCB0eXBlQWxpYXNlcyk7XG5cdFx0XHRjb25zdHJ1Y3RvclBhcmFtcyA9IHJlc3VsdC5jb25zdHJ1Y3RvclBhcmFtcztcblx0XHRcdFxuXHRcdFx0Ly8gVXNlIHRoZSBoYW5kbGVyIGZ1bmN0aW9uIGxvY2F0aW9uIGlmIGZvdW5kXG5cdFx0XHRpZiAocmVzdWx0LmhhbmRsZXJMb2NhdGlvbikge1xuXHRcdFx0XHRoYW5kbGVyTG9jYXRpb24gPSByZXN1bHQuaGFuZGxlckxvY2F0aW9uO1xuXHRcdFx0fVxuXHRcdFx0XG5cdFx0fSBjYXRjaCAoZXJyb3IpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goYEVycm9yIHBhcnNpbmcgJHt0YXJnZXRGaWxlfTogJHsoZXJyb3IgYXMgRXJyb3IpLm1lc3NhZ2V9YCk7XG5cdFx0fVxuXHRcdFxuXHRcdHJldHVybiB7IHByb3BlcnRpZXMsIGNvbnN0cnVjdG9yUGFyYW1zLCBoYW5kbGVyTG9jYXRpb24gfTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IHR5cGUgYWxpYXNlcyBmcm9tIHNvdXJjZSBmaWxlXG5cdCAqIGUuZy4sIGV4cG9ydCB0eXBlIFNlbnRpZW5jZURhdGEgPSB7IGF3YXJlbmVzcz86IHN0cmluZzsgfVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0VHlwZUFsaWFzZXMgKHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiBNYXA8c3RyaW5nLCB0cy5UeXBlTm9kZT4ge1xuXHRcdGNvbnN0IHR5cGVBbGlhc2VzID0gbmV3IE1hcDxzdHJpbmcsIHRzLlR5cGVOb2RlPigpO1xuXHRcdFxuXHRcdGNvbnN0IHZpc2l0ID0gKG5vZGU6IHRzLk5vZGUpOiB2b2lkID0+IHtcblx0XHRcdC8vIExvb2sgZm9yIHR5cGUgYWxpYXMgZGVjbGFyYXRpb25zOiBleHBvcnQgdHlwZSBOYW1lID0gVHlwZTtcblx0XHRcdGlmICh0cy5pc1R5cGVBbGlhc0RlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHRcdGNvbnN0IG5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRcdFx0dHlwZUFsaWFzZXMuc2V0KG5hbWUsIG5vZGUudHlwZSk7XG5cdFx0XHR9XG5cdFx0XHRcblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCB2aXNpdCk7XG5cdFx0fTtcblx0XHRcblx0XHR2aXNpdChzb3VyY2VGaWxlKTtcblx0XHRyZXR1cm4gdHlwZUFsaWFzZXM7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0eSBhc3NpZ25tZW50cyBmcm9tIGEgc291cmNlIGZpbGVcblx0ICogUmV0dXJucyBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGFuZCBoYW5kbGVyIGxvY2F0aW9uIGlmIGZvdW5kXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RQcm9wZXJ0aWVzRnJvbVNvdXJjZUZpbGUgKFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0cHJvcGVydGllczogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPixcblx0XHR0eXBlQWxpYXNlcz86IE1hcDxzdHJpbmcsIHRzLlR5cGVOb2RlPlxuXHQpOiB7XG5cdFx0Y29uc3RydWN0b3JQYXJhbXM/OiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdO1xuXHRcdGhhbmRsZXJMb2NhdGlvbj86IHsgZmlsZVBhdGg6IHN0cmluZzsgbGluZTogbnVtYmVyOyBjb2x1bW46IG51bWJlciB9O1xuXHR9IHtcblx0XHRsZXQgY29uc3RydWN0b3JQYXJhbXM6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10gfCB1bmRlZmluZWQ7XG5cdFx0bGV0IGhhbmRsZXJMb2NhdGlvbjogeyBmaWxlUGF0aDogc3RyaW5nOyBsaW5lOiBudW1iZXI7IGNvbHVtbjogbnVtYmVyIH0gfCB1bmRlZmluZWQ7XG5cdFx0XG5cdFx0Y29uc3QgdmlzaXQgPSAobm9kZTogdHMuTm9kZSk6IHZvaWQgPT4ge1xuXHRcdFx0Ly8gTG9vayBmb3IgZXhwb3J0ZWQgZnVuY3Rpb24gZGVjbGFyYXRpb25zICh0b3BvbG9naWNhIGNvbnZlbnRpb246IG9uZSBleHBvcnRlZCBmdW5jdGlvbiBwZXIgZmlsZSlcblx0XHRcdGlmICh0cy5pc0Z1bmN0aW9uRGVjbGFyYXRpb24obm9kZSkgJiYgbm9kZS5uYW1lKSB7XG5cdFx0XHRcdC8vIENoZWNrIGlmIGl0J3MgZXhwb3J0ZWRcblx0XHRcdFx0Y29uc3QgaXNFeHBvcnRlZCA9IG5vZGUubW9kaWZpZXJzPy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLkV4cG9ydEtleXdvcmQpO1xuXHRcdFx0XHRcblx0XHRcdFx0aWYgKGlzRXhwb3J0ZWQpIHtcblx0XHRcdFx0XHR0aGlzLmV4dHJhY3RUaGlzUHJvcGVydGllcyhub2RlLCBwcm9wZXJ0aWVzKTtcblx0XHRcdFx0XHQvLyBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtcyBhbmQgbG9jYXRpb24gZnJvbSB0aGUgZXhwb3J0ZWQgZnVuY3Rpb25cblx0XHRcdFx0XHRpZiAoIWNvbnN0cnVjdG9yUGFyYW1zKSB7XG5cdFx0XHRcdFx0XHRjb25zdHJ1Y3RvclBhcmFtcyA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zKG5vZGUsIHR5cGVBbGlhc2VzKTtcblx0XHRcdFx0XHRcdC8vIENhcHR1cmUgdGhlIGZ1bmN0aW9uIGxvY2F0aW9uXG5cdFx0XHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0XHRcdCk7XG5cdFx0XHRcdFx0XHRoYW5kbGVyTG9jYXRpb24gPSB7XG5cdFx0XHRcdFx0XHRcdGZpbGVQYXRoIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0XHRcdFx0bGluZSAgICAgOiBsaW5lICsgMSwgLy8gMS1iYXNlZFxuXHRcdFx0XHRcdFx0XHRjb2x1bW4gICA6IGNoYXJhY3RlciArIDEgLy8gMS1iYXNlZFxuXHRcdFx0XHRcdFx0fTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIEFsc28gY2hlY2sgZnVuY3Rpb24gZXhwcmVzc2lvbnMvYXJyb3cgZnVuY3Rpb25zIGFzc2lnbmVkIHRvIGV4cG9ydHNcblx0XHRcdGVsc2UgaWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKG5vZGUpIHx8IHRzLmlzQXJyb3dGdW5jdGlvbihub2RlKSkge1xuXHRcdFx0XHR0aGlzLmV4dHJhY3RUaGlzUHJvcGVydGllcyhub2RlLCBwcm9wZXJ0aWVzKTtcblx0XHRcdFx0Ly8gRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbXMgZnJvbSBub24tZXhwb3J0ZWQgZnVuY3Rpb25zIHRvb1xuXHRcdFx0XHRpZiAoIWNvbnN0cnVjdG9yUGFyYW1zKSB7XG5cdFx0XHRcdFx0Y29uc3RydWN0b3JQYXJhbXMgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyhub2RlLCB0eXBlQWxpYXNlcyk7XG5cdFx0XHRcdFx0Ly8gQ2FwdHVyZSB0aGUgZnVuY3Rpb24gbG9jYXRpb25cblx0XHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHRcdCk7XG5cdFx0XHRcdFx0aGFuZGxlckxvY2F0aW9uID0ge1xuXHRcdFx0XHRcdFx0ZmlsZVBhdGggOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRcdFx0bGluZSAgICAgOiBsaW5lICsgMSwgLy8gMS1iYXNlZFxuXHRcdFx0XHRcdFx0Y29sdW1uICAgOiBjaGFyYWN0ZXIgKyAxIC8vIDEtYmFzZWRcblx0XHRcdFx0XHR9O1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRcblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCB2aXNpdCk7XG5cdFx0fTtcblx0XHRcblx0XHR2aXNpdChzb3VyY2VGaWxlKTtcblx0XHRyZXR1cm4geyBjb25zdHJ1Y3RvclBhcmFtcywgaGFuZGxlckxvY2F0aW9uIH07XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBgdGhpcy5wcm9wZXJ0eSA9IHZhbHVlYCBhc3NpZ25tZW50cyBmcm9tIGEgZnVuY3Rpb24gYm9keVxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0VGhpc1Byb3BlcnRpZXMgKFxuXHRcdGZ1bmM6IHRzLkZ1bmN0aW9uRGVjbGFyYXRpb24gfCB0cy5GdW5jdGlvbkV4cHJlc3Npb24gfCB0cy5BcnJvd0Z1bmN0aW9uLFxuXHRcdHByb3BlcnRpZXM6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz5cblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgeyBib2R5IH0gPSBmdW5jO1xuXHRcdGlmICghYm9keSkgcmV0dXJuO1xuXHRcdFxuXHRcdGNvbnN0IHZpc2l0U3RhdGVtZW50cyA9IChub2RlOiB0cy5Ob2RlKTogdm9pZCA9PiB7XG5cdFx0XHQvLyBIYW5kbGUgZXhwcmVzc2lvbiBzdGF0ZW1lbnRzXG5cdFx0XHRpZiAodHMuaXNFeHByZXNzaW9uU3RhdGVtZW50KG5vZGUpKSB7XG5cdFx0XHRcdGNvbnN0IGV4cHIgPSBub2RlLmV4cHJlc3Npb247XG5cdFx0XHRcdFxuXHRcdFx0XHQvLyBDaGVjayBmb3IgdGhpcy5wcm9wID0gdmFsdWVcblx0XHRcdFx0aWYgKHRzLmlzQmluYXJ5RXhwcmVzc2lvbihleHByKSAmJiBcblx0XHRcdFx0ICAgIGV4cHIub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkVxdWFsc1Rva2VuKSB7XG5cdFx0XHRcdFx0Y29uc3QgeyBsZWZ0IH0gPSBleHByO1xuXHRcdFx0XHRcdGNvbnN0IHsgcmlnaHQgfSA9IGV4cHI7XG5cdFx0XHRcdFx0XG5cdFx0XHRcdFx0Ly8gQ2hlY2sgaWYgbGVmdCBzaWRlIGlzIHRoaXMucHJvcGVydHlcblx0XHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obGVmdCkgJiZcblx0XHRcdFx0XHQgICAgbGVmdC5leHByZXNzaW9uLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbGVmdC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0XHRjb25zdCBwcm9wVHlwZSA9IHRoaXMuaW5mZXJUeXBlKHJpZ2h0KTtcblx0XHRcdFx0XHRcdFxuXHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQocHJvcE5hbWUsIHtcblx0XHRcdFx0XHRcdFx0bmFtZSAgICAgOiBwcm9wTmFtZSxcblx0XHRcdFx0XHRcdFx0dHlwZSAgICAgOiBwcm9wVHlwZSxcblx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdFx0cmVhZG9ubHkgOiBmYWxzZVxuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHRcdFxuXHRcdFx0XHQvLyBDaGVjayBmb3IgT2JqZWN0LmFzc2lnbih0aGlzLCB7Li4ufSlcblx0XHRcdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdFx0XHRjb25zdCBjYWxsRXhwciA9IGV4cHI7XG5cdFx0XHRcdFx0aWYgKHRoaXMuaXNPYmplY3RBc3NpZ25DYWxsKGNhbGxFeHByKSkge1xuXHRcdFx0XHRcdFx0dGhpcy5leHRyYWN0RnJvbU9iamVjdEFzc2lnbihjYWxsRXhwciwgcHJvcGVydGllcyk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRcblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCB2aXNpdFN0YXRlbWVudHMpO1xuXHRcdH07XG5cdFx0XG5cdFx0dmlzaXRTdGF0ZW1lbnRzKGJvZHkpO1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGEgY2FsbCBleHByZXNzaW9uIGlzIE9iamVjdC5hc3NpZ24odGhpcywgLi4uKVxuXHQgKi9cblx0cHJpdmF0ZSBpc09iamVjdEFzc2lnbkNhbGwgKGNhbGxFeHByOiB0cy5DYWxsRXhwcmVzc2lvbik6IGJvb2xlYW4ge1xuXHRcdGNvbnN0IGV4cHIgPSBjYWxsRXhwci5leHByZXNzaW9uO1xuXHRcdGlmICghdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHJldHVybiBmYWxzZTtcblx0XHRcblx0XHRjb25zdCBvYmpOYW1lID0gdHMuaXNJZGVudGlmaWVyKGV4cHIuZXhwcmVzc2lvbikgPyBleHByLmV4cHJlc3Npb24udGV4dCA6IG51bGw7XG5cdFx0Y29uc3QgbWV0aG9kTmFtZSA9IGV4cHIubmFtZS50ZXh0O1xuXHRcdFxuXHRcdGlmIChvYmpOYW1lID09PSAnT2JqZWN0JyAmJiBtZXRob2ROYW1lID09PSAnYXNzaWduJykge1xuXHRcdFx0Y29uc3QgZmlyc3RBcmcgPSBjYWxsRXhwci5hcmd1bWVudHNbIDAgXTtcblx0XHRcdGlmIChmaXJzdEFyZyAmJiBmaXJzdEFyZy5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRcblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gT2JqZWN0LmFzc2lnbih0aGlzLCBkYXRhKSBwYXR0ZXJuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RGcm9tT2JqZWN0QXNzaWduIChcblx0XHRjYWxsRXhwcjogdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0cHJvcGVydGllczogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPlxuXHQpOiB2b2lkIHtcblx0XHQvLyBMb29rIGZvciB0aGUgZGF0YSBhcmd1bWVudCAoc2Vjb25kIGFyZ3VtZW50KVxuXHRcdGNvbnN0IGRhdGFBcmcgPSBjYWxsRXhwci5hcmd1bWVudHNbIDEgXTtcblx0XHRpZiAoIWRhdGFBcmcpIHJldHVybjtcblx0XHRcblx0XHQvLyBJZiBpdCdzIGFuIG9iamVjdCBsaXRlcmFsLCBleHRyYWN0IHByb3BlcnRpZXNcblx0XHRpZiAodHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihkYXRhQXJnKSkge1xuXHRcdFx0Zm9yIChjb25zdCBwcm9wIG9mIGRhdGFBcmcucHJvcGVydGllcykge1xuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFzc2lnbm1lbnQocHJvcCkgJiYgdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IHByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRcdGNvbnN0IHByb3BUeXBlID0gdGhpcy5pbmZlclR5cGUocHJvcC5pbml0aWFsaXplcik7XG5cdFx0XHRcdFx0XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQocHJvcE5hbWUsIHtcblx0XHRcdFx0XHRcdG5hbWUgICAgIDogcHJvcE5hbWUsXG5cdFx0XHRcdFx0XHR0eXBlICAgICA6IHByb3BUeXBlLFxuXHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdHJlYWRvbmx5IDogZmFsc2Vcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBhIGZ1bmN0aW9uXG5cdCAqIFNpbWlsYXIgdG8gbWFpbiBhbmFseXplciAtIHNraXBzIGB0aGlzYCBwYXJhbWV0ZXIgYW5kIGV4cGFuZHMgZGF0YSB0eXBlc1xuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JQYXJhbXMgKFxuXHRcdGZ1bmM6IHRzLkZ1bmN0aW9uRGVjbGFyYXRpb24gfCB0cy5GdW5jdGlvbkV4cHJlc3Npb24gfCB0cy5BcnJvd0Z1bmN0aW9uLFxuXHRcdHR5cGVBbGlhc2VzPzogTWFwPHN0cmluZywgdHMuVHlwZU5vZGU+XG5cdCk6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10gfCB1bmRlZmluZWQge1xuXHRcdGlmICghZnVuYy5wYXJhbWV0ZXJzIHx8IGZ1bmMucGFyYW1ldGVycy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcGFyYW1zOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdID0gW107XG5cdFx0XG5cdFx0Ly8gU2tpcCBgdGhpc2AgcGFyYW1ldGVyIChmaXJzdCBwYXJhbSkgYW5kIGV4dHJhY3QgZGF0YSBwYXJhbWV0ZXJzXG5cdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBmdW5jLnBhcmFtZXRlcnMubGVuZ3RoOyBpKyspIHtcblx0XHRcdGNvbnN0IHBhcmFtID0gZnVuYy5wYXJhbWV0ZXJzWyBpIF07XG5cdFx0XHRcblx0XHRcdC8vIFNraXAgYHRoaXNgIHBhcmFtZXRlciAoZmlyc3QgcGFyYW0pXG5cdFx0XHRpZiAoaSA9PT0gMCAmJiBwYXJhbS5uYW1lLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuSWRlbnRpZmllciAmJlxuXHRcdFx0ICAgIChwYXJhbS5uYW1lIGFzIHRzLklkZW50aWZpZXIpLnRleHQgPT09ICd0aGlzJykge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdFxuXHRcdFx0aWYgKCFwYXJhbS50eXBlKSBjb250aW51ZTtcblx0XHRcdFxuXHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpID8gcGFyYW0ubmFtZS50ZXh0IDogJ2FyZyc7XG5cdFx0XHRjb25zdCBvcHRpb25hbCA9IHBhcmFtLnF1ZXN0aW9uVG9rZW4gIT09IHVuZGVmaW5lZCB8fCBwYXJhbS5pbml0aWFsaXplciAhPT0gdW5kZWZpbmVkO1xuXHRcdFx0XG5cdFx0XHQvLyBFeHBhbmQgdHlwZSB0byBvYmplY3QgbGl0ZXJhbCBpZiBwb3NzaWJsZVxuXHRcdFx0Y29uc3QgZXhwYW5kZWRUeXBlID0gdGhpcy5leHBhbmRUeXBlVG9PYmplY3QocGFyYW0udHlwZSwgdHlwZUFsaWFzZXMpO1xuXHRcdFx0Y29uc3QgcGFyYW1UeXBlID0gZXhwYW5kZWRUeXBlIHx8IHRoaXMudHlwZU5vZGVUb1NpbXBsZVN0cmluZyhwYXJhbS50eXBlKTtcblx0XHRcdFxuXHRcdFx0cGFyYW1zLnB1c2goe1xuXHRcdFx0XHRuYW1lICAgICA6IHBhcmFtTmFtZSxcblx0XHRcdFx0dHlwZSAgICAgOiBwYXJhbVR5cGUsXG5cdFx0XHRcdG9wdGlvbmFsIDogb3B0aW9uYWxcblx0XHRcdH0pO1xuXHRcdH1cblx0XHRcblx0XHRyZXR1cm4gcGFyYW1zLmxlbmd0aCA+IDAgPyBwYXJhbXMgOiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXhwYW5kIGEgdHlwZSBub2RlIHRvIGl0cyBvYmplY3QgbGl0ZXJhbCByZXByZXNlbnRhdGlvblxuXHQgKiBTaW1pbGFyIHRvIG1haW4gYW5hbHl6ZXIncyByZXNvbHZlVHlwZUFuZEV4dHJhY3Rcblx0ICovXG5cdHByaXZhdGUgZXhwYW5kVHlwZVRvT2JqZWN0IChcblx0XHR0eXBlTm9kZTogdHMuVHlwZU5vZGUsXG5cdFx0dHlwZUFsaWFzZXM/OiBNYXA8c3RyaW5nLCB0cy5UeXBlTm9kZT5cblx0KTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBEaXJlY3QgaW5saW5lIHR5cGUgbGl0ZXJhbDogeyBwcm9wOiB0eXBlIH1cblx0XHRpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUodHlwZU5vZGUpKSB7XG5cdFx0XHRjb25zdCBwcm9wczogc3RyaW5nW10gPSBbXTtcblx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIHR5cGVOb2RlLm1lbWJlcnMpIHtcblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdGNvbnN0IG9wdCA9IG1lbWJlci5xdWVzdGlvblRva2VuID8gJz8nIDogJyc7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMudHlwZU5vZGVUb1NpbXBsZVN0cmluZyhtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0cHJvcHMucHVzaChgJHtwcm9wTmFtZX0ke29wdH06ICR7dHlwZX1gKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGB7ICR7cHJvcHMuam9pbignOyAnKX0gfWA7XG5cdFx0fVxuXG5cdFx0Ly8gVHlwZSByZWZlcmVuY2U6IFNlbnRpZW5jZURhdGEsIGV0Yy4gLSB0cnkgdG8gZXhwYW5kIGZyb20gdHlwZSBhbGlhc2VzXG5cdFx0aWYgKHRzLmlzVHlwZVJlZmVyZW5jZU5vZGUodHlwZU5vZGUpICYmIHRzLmlzSWRlbnRpZmllcih0eXBlTm9kZS50eXBlTmFtZSkpIHtcblx0XHRcdGNvbnN0IHR5cGVOYW1lID0gdHlwZU5vZGUudHlwZU5hbWUudGV4dDtcblx0XHRcdFxuXHRcdFx0Ly8gSWYgd2UgaGF2ZSB0eXBlIGFsaWFzZXMsIHRyeSB0byBleHBhbmQgdGhlIHJlZmVyZW5jZWQgdHlwZVxuXHRcdFx0aWYgKHR5cGVBbGlhc2VzKSB7XG5cdFx0XHRcdGNvbnN0IGFsaWFzZWRUeXBlID0gdHlwZUFsaWFzZXMuZ2V0KHR5cGVOYW1lKTtcblx0XHRcdFx0aWYgKGFsaWFzZWRUeXBlKSB7XG5cdFx0XHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmV4cGFuZFR5cGVUb09iamVjdChhbGlhc2VkVHlwZSwgdHlwZUFsaWFzZXMpO1xuXHRcdFx0XHRcdGlmIChleHBhbmRlZCkgcmV0dXJuIGV4cGFuZGVkO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRcblx0XHRcdC8vIElmIG5vdCBhbiBvYmplY3QgdHlwZSBhbGlhcywgcmV0dXJuIHRoZSB0eXBlIG5hbWVcblx0XHRcdHJldHVybiB0eXBlTmFtZTtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbnZlcnQgYSBUeXBlU2NyaXB0IHR5cGUgbm9kZSB0byBhIHNpbXBsZSBzdHJpbmcgcmVwcmVzZW50YXRpb25cblx0ICovXG5cdHByaXZhdGUgdHlwZU5vZGVUb1NpbXBsZVN0cmluZyAodHlwZU5vZGU6IHRzLlR5cGVOb2RlIHwgdW5kZWZpbmVkKTogc3RyaW5nIHtcblx0XHRpZiAoIXR5cGVOb2RlKSByZXR1cm4gJ2FueSc7XG5cdFx0XG5cdFx0c3dpdGNoICh0eXBlTm9kZS5raW5kKSB7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlN0cmluZ0tleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bWJlcktleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkJvb2xlYW5LZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQW55S2V5d29yZDpcblx0XHRcdHJldHVybiAnYW55Jztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQXJyYXlUeXBlOlxuXHRcdFx0cmV0dXJuICdBcnJheTxhbnk+Jztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZVJlZmVyZW5jZToge1xuXHRcdFx0Y29uc3QgdHlwZVJlZiA9IHR5cGVOb2RlIGFzIHRzLlR5cGVSZWZlcmVuY2VOb2RlO1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcih0eXBlUmVmLnR5cGVOYW1lKSkge1xuXHRcdFx0XHRyZXR1cm4gdHlwZVJlZi50eXBlTmFtZS50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICdhbnknO1xuXHRcdH1cblx0XHRkZWZhdWx0OlxuXHRcdFx0cmV0dXJuICdhbnknO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBJbmZlciBUeXBlU2NyaXB0IHR5cGUgZnJvbSBhbiBleHByZXNzaW9uXG5cdCAqL1xuXHRwcml2YXRlIGluZmVyVHlwZSAobm9kZTogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB7XG5cdFx0c3dpdGNoIChub2RlLmtpbmQpIHtcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuU3RyaW5nTGl0ZXJhbDpcblx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVtZXJpY0xpdGVyYWw6XG5cdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkOlxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdWxsS2V5d29yZDpcblx0XHRcdHJldHVybiAnbnVsbCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVuZGVmaW5lZEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3VuZGVmaW5lZCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkFycmF5TGl0ZXJhbEV4cHJlc3Npb246XG5cdFx0XHRyZXR1cm4gJ0FycmF5PGFueT4nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5PYmplY3RMaXRlcmFsRXhwcmVzc2lvbjpcblx0XHRcdHJldHVybiAnb2JqZWN0Jztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTmV3RXhwcmVzc2lvbjpcblx0XHRcdHJldHVybiB0aGlzLmluZmVyTmV3RXhwcmVzc2lvblR5cGUobm9kZSBhcyB0cy5OZXdFeHByZXNzaW9uKTtcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQ29uZGl0aW9uYWxFeHByZXNzaW9uOlxuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJUeXBlKChub2RlIGFzIHRzLkNvbmRpdGlvbmFsRXhwcmVzc2lvbikud2hlblRydWUpO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5CaW5hcnlFeHByZXNzaW9uOiB7XG5cdFx0XHRjb25zdCBiaW5FeHByID0gbm9kZSBhcyB0cy5CaW5hcnlFeHByZXNzaW9uO1xuXHRcdFx0Ly8gQ2hlY2sgZm9yIGxvZ2ljYWwgT1IgcGF0dGVybjogdmFsdWUgfHwgZGVmYXVsdFxuXHRcdFx0aWYgKGJpbkV4cHIub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkJhckJhclRva2VuKSB7XG5cdFx0XHRcdC8vIFJldHVybiB0aGUgdHlwZSBvZiB0aGUgcmlnaHQgc2lkZSAodGhlIGRlZmF1bHQgdmFsdWUpXG5cdFx0XHRcdHJldHVybiB0aGlzLmluZmVyVHlwZShiaW5FeHByLnJpZ2h0KTtcblx0XHRcdH1cblx0XHRcdHJldHVybiAnYW55Jztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbjoge1xuXHRcdFx0Y29uc3QgcHJvcEFjY2VzcyA9IG5vZGUgYXMgdHMuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uO1xuXHRcdFx0Ly8gSGFuZGxlIGRhdGE/LnByb3BlcnR5IHBhdHRlcm5zXG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclR5cGUocHJvcEFjY2Vzcyk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5DYWxsRXhwcmVzc2lvbjoge1xuXHRcdFx0Y29uc3QgY2FsbEV4cHIgPSBub2RlIGFzIHRzLkNhbGxFeHByZXNzaW9uO1xuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJDYWxsRXhwcmVzc2lvblR5cGUoY2FsbEV4cHIpO1xuXHRcdH1cblx0XHRkZWZhdWx0OlxuXHRcdFx0cmV0dXJuICdhbnknO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBJbmZlciB0eXBlIGZyb20gbmV3IGV4cHJlc3Npb25zIGxpa2UgbmV3IERhdGUoKSwgbmV3IEFycmF5KCksIGV0Yy5cblx0ICovXG5cdHByaXZhdGUgaW5mZXJOZXdFeHByZXNzaW9uVHlwZSAobm9kZTogdHMuTmV3RXhwcmVzc2lvbik6IHN0cmluZyB7XG5cdFx0Y29uc3QgZXhwciA9IG5vZGUuZXhwcmVzc2lvbjtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRzd2l0Y2ggKGV4cHIudGV4dCkge1xuXHRcdFx0Y2FzZSAnRGF0ZSc6XG5cdFx0XHRcdHJldHVybiAnbnVtYmVyJzsgLy8gRGF0ZS5ub3coKSByZXR1cm5zIG51bWJlclxuXHRcdFx0Y2FzZSAnQXJyYXknOlxuXHRcdFx0XHRyZXR1cm4gJ0FycmF5PGFueT4nO1xuXHRcdFx0Y2FzZSAnTWFwJzpcblx0XHRcdFx0cmV0dXJuICdNYXA8YW55LCBhbnk+Jztcblx0XHRcdGNhc2UgJ1NldCc6XG5cdFx0XHRcdHJldHVybiAnU2V0PGFueT4nO1xuXHRcdFx0Y2FzZSAnUmVnRXhwJzpcblx0XHRcdFx0cmV0dXJuICdSZWdFeHAnO1xuXHRcdFx0ZGVmYXVsdDpcblx0XHRcdFx0cmV0dXJuIGV4cHIudGV4dDtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuICdhbnknO1xuXHR9XG5cblx0LyoqXG5cdCAqIEluZmVyIHR5cGUgZnJvbSBjYWxsIGV4cHJlc3Npb25zIGxpa2UgRGF0ZS5ub3coKSwgcGFyc2VJbnQoKSwgZXRjLlxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlckNhbGxFeHByZXNzaW9uVHlwZSAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcge1xuXHRcdGNvbnN0IGV4cHIgPSBub2RlLmV4cHJlc3Npb247XG5cdFx0XG5cdFx0Ly8gSGFuZGxlIERhdGUubm93KClcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdGNvbnN0IG9iaiA9IGV4cHIuZXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IG1ldGhvZCA9IGV4cHIubmFtZS50ZXh0O1xuXHRcdFx0XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG9iaikgJiYgb2JqLnRleHQgPT09ICdEYXRlJyAmJiBtZXRob2QgPT09ICdub3cnKSB7XG5cdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdH1cblx0XHR9XG5cdFx0XG5cdFx0Ly8gSGFuZGxlIHBhcnNlSW50LCBwYXJzZUZsb2F0LCBTdHJpbmcoKSwgTnVtYmVyKCksIEJvb2xlYW4oKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHN3aXRjaCAoZXhwci50ZXh0KSB7XG5cdFx0XHRjYXNlICdwYXJzZUludCc6XG5cdFx0XHRjYXNlICdwYXJzZUZsb2F0Jzpcblx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0Y2FzZSAnU3RyaW5nJzpcblx0XHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdFx0Y2FzZSAnTnVtYmVyJzpcblx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0Y2FzZSAnQm9vbGVhbic6XG5cdFx0XHRcdHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdFxuXHRcdHJldHVybiAnYW55Jztcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgdGhlIHR5cGUgZ3JhcGhcblx0ICovXG5cdGdldEdyYXBoICgpOiBUeXBlR3JhcGhJbXBsIHtcblx0XHRyZXR1cm4gdGhpcy5ncmFwaDtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGVycm9yc1xuXHQgKi9cblx0Z2V0RXJyb3JzICgpOiBzdHJpbmdbXSB7XG5cdFx0cmV0dXJuIHRoaXMuZXJyb3JzO1xuXHR9XG59XG4iXX0=