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
            ({ constructorParams } = result);
            // Use the handler function location if found
            if (result.handlerLocation) {
                ({ handlerLocation } = result);
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
                        // line and column are 1-based
                        handlerLocation = {
                            filePath: sourceFile.fileName,
                            line: line + 1,
                            column: character + 1
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
                    // line and column are 1-based
                    handlerLocation = {
                        filePath: sourceFile.fileName,
                        line: line + 1,
                        column: character + 1
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
            const [firstArg] = callExpr.arguments;
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
        const [, dataArg] = callExpr.arguments;
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
                    // Date.now() returns number
                    return 'number';
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoidG9wb2xvZ2ljYS1hbmFseXplci5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzIjpbIi4uL3NyYy90b3BvbG9naWNhLWFuYWx5emVyLnRzIl0sIm5hbWVzIjpbXSwibWFwcGluZ3MiOiJBQUFBLFlBQVksQ0FBQzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7O0FBRWIsdUNBQXlCO0FBQ3pCLDJDQUE2QjtBQUM3QiwrQ0FBaUM7QUFJakMsbUNBQXdDO0FBRXhDOzs7Ozs7R0FNRztBQUNILE1BQWEsa0JBQWtCO0lBQS9CO1FBQ1MsV0FBTSxHQUFhLEVBQUUsQ0FBQztRQUN0QixVQUFLLEdBQUcsSUFBSSxxQkFBYSxFQUFFLENBQUM7SUE0aUJyQyxDQUFDO0lBMWlCQTs7T0FFRztJQUNILGdCQUFnQixDQUFFLGFBQXFCO1FBQ3RDLElBQUksQ0FBQyxNQUFNLEdBQUcsRUFBRSxDQUFDO1FBRWpCLElBQUksQ0FBQyxFQUFFLENBQUMsVUFBVSxDQUFDLGFBQWEsQ0FBQyxFQUFFLENBQUM7WUFDbkMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsNkJBQTZCLGFBQWEsRUFBRSxDQUFDLENBQUM7WUFDL0QsT0FBTyxFQUFFLEtBQUssRUFBRyxJQUFJLENBQUMsS0FBSyxDQUFDLFFBQVEsRUFBRSxNQUFNLEVBQUcsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDO1FBQzlELENBQUM7UUFFRCxJQUFJLENBQUMsRUFBRSxDQUFDLFFBQVEsQ0FBQyxhQUFhLENBQUMsQ0FBQyxXQUFXLEVBQUUsRUFBRSxDQUFDO1lBQy9DLElBQUksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLDRCQUE0QixhQUFhLEVBQUUsQ0FBQyxDQUFDO1lBQzlELE9BQU8sRUFBRSxLQUFLLEVBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLEVBQUUsTUFBTSxFQUFHLElBQUksQ0FBQyxNQUFNLEVBQUUsQ0FBQztRQUM5RCxDQUFDO1FBRUQsSUFBSSxDQUFDLGFBQWEsQ0FBQyxhQUFh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QUFPLFFBQVEsQ0FBQztnQkFDakIsS0FBSyxTQUFTO29CQUNiLE9BQU8sU0FBUyxDQUFDO1lBQ2xCLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxLQUFLLENBQUM7SUFDZCxDQUFDO0lBRUQ7O09BRUc7SUFDSCxRQUFRO1FBQ1AsT0FBTyxJQUFJLENBQUMsS0FBSyxDQUFDO0lBQ25CLENBQUM7SUFFRDs7T0FFRztJQUNILFNBQVM7UUFDUixPQUFPLElBQUksQ0FBQyxNQUFNLENBQUM7SUFDcEIsQ0FBQztDQUNEO0FBOWlCRCxnREE4aUJDIiwic291cmNlc0NvbnRlbnQiOlsiJ3VzZSBzdHJpY3QnO1xuXG5pbXBvcnQgKiBhcyBmcyBmcm9tICdmcyc7XG5pbXBvcnQgKiBhcyBwYXRoIGZyb20gJ3BhdGgnO1xuaW1wb3J0ICogYXMgdHMgZnJvbSAndHlwZXNjcmlwdCc7XG5pbXBvcnQge1xuXHRUeXBlTm9kZSwgUHJvcGVydHlJbmZvLCBDb25zdHJ1Y3RvclBhcmFtSW5mbyBcbn0gZnJvbSAnLi90eXBlcyc7XG5pbXBvcnQgeyBUeXBlR3JhcGhJbXBsIH0gZnJvbSAnLi9ncmFwaCc7XG5cbi8qKlxuICogQW5hbHl6ZXIgZm9yIFRvcG9sb2dpY2EgZGlyZWN0b3J5LWJhc2VkIHR5cGUgZGVmaW5pdGlvbnNcbiAqIFNjYW5zIGRpcmVjdG9yeSBzdHJ1Y3R1cmVzIHRvIGNyZWF0ZSB0eXBlIGhpZXJhcmNoaWVzIGxpa2U6XG4gKiBhaS10eXBlcy9TZW50aWVuY2UvQ29uc2Npb3VzbmVzcy9FbXBhdGh5L0dyYXRpdHVkZS9cbiAqIFxuICogTm93IHdpdGggQVNULWJhc2VkIHByb3BlcnR5IGV4dHJhY3Rpb24gZnJvbSBUeXBlU2NyaXB0L0phdmFTY3JpcHQgZmlsZXNcbiAqL1xuZXhwb3J0IGNsYXNzIFRvcG9sb2dpY2FBbmFseXplciB7XG5cdHByaXZhdGUgZXJyb3JzOiBzdHJpbmdbXSA9IFtdO1xuXHRwcml2YXRlIGdyYXBoID0gbmV3IFR5cGVHcmFwaEltcGwoKTtcblxuXHQvKipcblx0ICogQW5hbHl6ZSBhIGRpcmVjdG9yeSBzdHJ1Y3R1cmUgZm9yIHRvcG9sb2dpY2EgdHlwZSBkZWZpbml0aW9uc1xuXHQgKi9cblx0YW5hbHl6ZURpcmVjdG9yeSAoZGlyZWN0b3J5UGF0aDogc3RyaW5nKTogeyB0eXBlczogTWFwPHN0cmluZywgVHlwZU5vZGU+LCBlcnJvcnM6IHN0cmluZ1tdIH0ge1xuXHRcdHRoaXMuZXJyb3JzID0gW107XG5cdFx0XG5cdFx0aWYgKCFmcy5leGlzdHNTeW5jKGRpcmVjdG9yeVBhdGgpKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKGBEaXJlY3RvcnkgZG9lcyBub3QgZXhpc3Q6ICR7ZGlyZWN0b3J5UGF0aH1gKTtcblx0XHRcdHJldHVybiB7IHR5cGVzIDogdGhpcy5ncmFwaC5hbGxUeXBlcywgZXJyb3JzIDogdGhpcy5lcnJvcnMgfTtcblx0XHR9XG5cblx0XHRpZiAoIWZzLnN0YXRTeW5jKGRpcmVjdG9yeVBhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goYFBhdGggaXMgbm90IGEgZGlyZWN0b3J5OiAke2RpcmVjdG9yeVBhdGh9YCk7XG5cdFx0XHRyZXR1cm4geyB0eXBlcyA6IHRoaXMuZ3JhcGguYWxsVHlwZXMsIGVycm9ycyA6IHRoaXMuZXJyb3JzIH07XG5cdFx0fVxuXG5cdFx0dGhpcy5zY2FuRGlyZWN0b3J5KGRpcmVjdG9yeVBhdGgsIHVuZGVmaW5lZCwgZGlyZWN0b3J5UGF0aCk7XG5cdFx0XG5cdFx0cmV0dXJuIHtcblx0XHRcdHR5cGVzICA6IHRoaXMuZ3JhcGguYWxsVHlwZXMsXG5cdFx0XHRlcnJvcnMgOiB0aGlzLmVycm9ycyxcblx0XHR9O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY3Vyc2l2ZWx5IHNjYW4gZGlyZWN0b3J5IHN0cnVjdHVyZSB0byBidWlsZCB0eXBlIGhpZXJhcmNoeVxuXHQgKi9cblx0cHJpdmF0ZSBzY2FuRGlyZWN0b3J5IChjdXJyZW50UGF0aDogc3RyaW5nLCBwYXJlbnROb2RlOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCwgcm9vdFBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdHRyeSB7XG5cdFx0XHRjb25zdCBlbnRyaWVzID0gZnMucmVhZGRpclN5bmMoY3VycmVudFBhdGgsIHsgd2l0aEZpbGVUeXBlcyA6IHRydWUgfSk7XG5cdFx0XHRcblx0XHRcdGZvciAoY29uc3QgZW50cnkgb2YgZW50cmllcykge1xuXHRcdFx0XHRpZiAoZW50cnkuaXNEaXJlY3RvcnkoKSkge1xuXHRcdFx0XHRcdC8vIENyZWF0ZSB0eXBlIG5vZGUgZm9yIHRoaXMgZGlyZWN0b3J5XG5cdFx0XHRcdFx0Y29uc3QgdHlwZU5hbWUgPSBlbnRyeS5uYW1lO1xuXHRcdFx0XHRcdGNvbnN0IGZ1bGxQYXRoID0gcGFyZW50Tm9kZSA/IGAke3BhcmVudE5vZGUuZnVsbFBhdGh9LiR7dHlwZU5hbWV9YCA6IHR5cGVOYW1lO1xuXHRcdFx0XHRcdGNvbnN0IGRpclBhdGggPSBwYXRoLmpvaW4oY3VycmVudFBhdGgsIGVudHJ5Lm5hbWUpO1xuXHRcdFx0XHRcdFxuXHRcdFx0XHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBhbmQgY29uc3RydWN0b3IgcGFyYW1zIGZyb20gdGhlIGhhbmRsZXIgZmlsZSBpZiBpdCBleGlzdHNcblx0XHRcdFx0XHRjb25zdCB7XG5cdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLCBjb25zdHJ1Y3RvclBhcmFtcywgaGFuZGxlckxvY2F0aW9uIFxuXHRcdFx0XHRcdH0gPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzRnJvbURpcihkaXJQYXRoKTtcblx0XHRcdFx0XHRcblx0XHRcdFx0XHQvLyBDcmVhdGUgdGhlIHR5cGUgbm9kZSB3aXRoIHByb3BlciBzb3VyY2UgbG9jYXRpb24gZm9yIEdvIHRvIERlZmluaXRpb25cblx0XHRcdFx0XHRjb25zdCB0eXBlTm9kZTogVHlwZU5vZGUgPSB7XG5cdFx0XHRcdFx0XHRuYW1lICAgICAgICAgICAgICA6IHR5cGVOYW1lLFxuXHRcdFx0XHRcdFx0ZnVsbFBhdGggICAgICAgICAgOiBmdWxsUGF0aCxcblx0XHRcdFx0XHRcdHByb3BlcnRpZXMgICAgICAgIDogcHJvcGVydGllcyxcblx0XHRcdFx0XHRcdGNvbnN0cnVjdG9yUGFyYW1zIDogY29uc3RydWN0b3JQYXJhbXMsXG5cdFx0XHRcdFx0XHRwYXJlbnQgICAgICAgICAgICA6IHBhcmVudE5vZGUsXG5cdFx0XHRcdFx0XHRjaGlsZHJlbiAgICAgICAgICA6IG5ldyBNYXAoKSxcblx0XHRcdFx0XHRcdHNvdXJjZUZpbGUgICAgICAgIDogaGFuZGxlckxvY2F0aW9uPy5maWxlUGF0aCB8fCBkaXJQYXRoLFxuXHRcdFx0XHRcdFx0bGluZSAgICAgICAgICAgICAgOiBoYW5kbGVyTG9jYXRpb24/LmxpbmUgfHwgMCxcblx0XHRcdFx0XHRcdGNvbHVtbiAgICAgICAgICAgIDogaGFuZGxlckxvY2F0aW9uPy5jb2x1bW4gfHwgMCxcblx0XHRcdFx0XHRcdGNvbnN0cnVjdG9yTmFtZSAgIDogdHlwZU5hbWVcblx0XHRcdFx0XHR9O1xuXHRcdFx0XHRcdFxuXHRcdFx0XHRcdC8vIEFkZCB0byBncmFwaFxuXHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHR0aGlzLmdyYXBoLmFkZENoaWxkKHBhcmVudE5vZGUsIHR5cGVOb2RlKTtcblx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0Ly8gQWRkIGFzIHJvb3QgdHlwZVxuXHRcdFx0XHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KHR5cGVOb2RlKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XG5cdFx0XHRcdFx0Ly8gU2NhbiBjaGlsZHJlbiBvZiB0aGlzIGRpcmVjdG9yeVxuXHRcdFx0XHRcdHRoaXMuc2NhbkRpcmVjdG9yeShkaXJQYXRoLCB0eXBlTm9kZSwgcm9vdFBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fSBjYXRjaCAoZXJyb3IpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goYEVycm9yIHNjYW5uaW5nIGRpcmVjdG9yeSAke2N1cnJlbnRQYXRofTogJHsoZXJyb3IgYXMgRXJyb3IpLm1lc3NhZ2V9YCk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGEgZGlyZWN0b3J5J3MgaW5kZXggZmlsZVxuXHQgKiBTdXBwb3J0cyBib3RoIC50cyBhbmQgLmpzIGZpbGVzXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RQcm9wZXJ0aWVzRnJvbURpciAoZGlyUGF0aDogc3RyaW5nKToge1xuXHRcdHByb3BlcnRpZXM6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz47XG5cdFx0Y29uc3RydWN0b3JQYXJhbXM/OiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdO1xuXHRcdGhhbmRsZXJMb2NhdGlvbj86IHsgZmlsZVBhdGg6IHN0cmluZzsgbGluZTogbnVtYmVyOyBjb2x1bW46IG51bWJlciB9O1xuXHR9IHtcblx0XHRjb25zdCBwcm9wZXJ0aWVzID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblx0XHRsZXQgY29uc3RydWN0b3JQYXJhbXM6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10gfCB1bmRlZmluZWQ7XG5cdFx0XG5cdFx0Ly8gQ2hlY2sgZm9yIFR5cGVTY3JpcHQgZmlsZSBmaXJzdCwgdGhlbiBKYXZhU2NyaXB0XG5cdFx0Y29uc3QgdHNGaWxlID0gcGF0aC5qb2luKGRpclBhdGgsICdpbmRleC50cycpO1xuXHRcdGNvbnN0IGpzRmlsZSA9IHBhdGguam9pbihkaXJQYXRoLCAnaW5kZXguanMnKTtcblx0XHRcblx0XHRsZXQgdGFyZ2V0RmlsZTogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdFxuXHRcdGlmIChmcy5leGlzdHNTeW5jKHRzRmlsZSkpIHtcblx0XHRcdHRhcmdldEZpbGUgPSB0c0ZpbGU7XG5cdFx0fSBlbHNlIGlmIChmcy5leGlzdHNTeW5jKGpzRmlsZSkpIHtcblx0XHRcdHRhcmdldEZpbGUgPSBqc0ZpbGU7XG5cdFx0fVxuXHRcdFxuXHRcdGlmICghdGFyZ2V0RmlsZSkge1xuXHRcdFx0cmV0dXJuIHsgcHJvcGVydGllcyB9O1xuXHRcdH1cblx0XHRcblx0XHQvLyBEZWZhdWx0IGxvY2F0aW9uIHBvaW50cyB0byB0aGUgaW5kZXggZmlsZSAod2lsbCBiZSB1cGRhdGVkIGlmIGhhbmRsZXIgZm91bmQpXG5cdFx0bGV0IGhhbmRsZXJMb2NhdGlvbjogeyBmaWxlUGF0aDogc3RyaW5nOyBsaW5lOiBudW1iZXI7IGNvbHVtbjogbnVtYmVyIH0gfCB1bmRlZmluZWQ7XG5cdFx0XG5cdFx0dHJ5IHtcblx0XHRcdGNvbnN0IGNvbnRlbnQgPSBmcy5yZWFkRmlsZVN5bmModGFyZ2V0RmlsZSwgJ3V0Zi04Jyk7XG5cdFx0XHRjb25zdCBzb3VyY2VGaWxlID0gdHMuY3JlYXRlU291cmNlRmlsZShcblx0XHRcdFx0dGFyZ2V0RmlsZSxcblx0XHRcdFx0Y29udGVudCxcblx0XHRcdFx0dHMuU2NyaXB0VGFyZ2V0LkxhdGVzdCxcblx0XHRcdFx0dHJ1ZVxuXHRcdFx0KTtcblx0XHRcdFxuXHRcdFx0Ly8gQ29sbGVjdCB0eXBlIGFsaWFzZXMgZnJvbSB0aGUgZmlsZSAoZS5nLiwgU2VudGllbmNlRGF0YSA9IHsgLi4uIH0pXG5cdFx0XHRjb25zdCB0eXBlQWxpYXNlcyA9IHRoaXMuY29sbGVjdFR5cGVBbGlhc2VzKHNvdXJjZUZpbGUpO1xuXHRcdFx0XG5cdFx0XHQvLyBGaW5kIGhhbmRsZXIgZnVuY3Rpb24gYW5kIGV4dHJhY3QgcHJvcGVydHkgYXNzaWdubWVudHMgYW5kIGNvbnN0cnVjdG9yIHBhcmFtc1xuXHRcdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5leHRyYWN0UHJvcGVydGllc0Zyb21Tb3VyY2VGaWxlKHNvdXJjZUZpbGUsIHByb3BlcnRpZXMsIHR5cGVBbGlhc2VzKTtcblx0XHRcdCggeyBjb25zdHJ1Y3RvclBhcmFtcyB9ID0gcmVzdWx0ICk7XG5cblx0XHRcdC8vIFVzZSB0aGUgaGFuZGxlciBmdW5jdGlvbiBsb2NhdGlvbiBpZiBmb3VuZFxuXHRcdFx0aWYgKHJlc3VsdC5oYW5kbGVyTG9jYXRpb24pIHtcblx0XHRcdFx0KCB7IGhhbmRsZXJMb2NhdGlvbiB9ID0gcmVzdWx0ICk7XG5cdFx0XHR9XG5cdFx0XHRcblx0XHR9IGNhdGNoIChlcnJvcikge1xuXHRcdFx0dGhpcy5lcnJvcnMucHVzaChgRXJyb3IgcGFyc2luZyAke3RhcmdldEZpbGV9OiAkeyhlcnJvciBhcyBFcnJvcikubWVzc2FnZX1gKTtcblx0XHR9XG5cdFx0XG5cdFx0cmV0dXJuIHsgcHJvcGVydGllcywgY29uc3RydWN0b3JQYXJhbXMsIGhhbmRsZXJMb2NhdGlvbiB9O1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgdHlwZSBhbGlhc2VzIGZyb20gc291cmNlIGZpbGVcblx0ICogZS5nLiwgZXhwb3J0IHR5cGUgU2VudGllbmNlRGF0YSA9IHsgYXdhcmVuZXNzPzogc3RyaW5nOyB9XG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RUeXBlQWxpYXNlcyAoc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IE1hcDxzdHJpbmcsIHRzLlR5cGVOb2RlPiB7XG5cdFx0Y29uc3QgdHlwZUFsaWFzZXMgPSBuZXcgTWFwPHN0cmluZywgdHMuVHlwZU5vZGU+KCk7XG5cdFx0XG5cdFx0Y29uc3QgdmlzaXQgPSAobm9kZTogdHMuTm9kZSk6IHZvaWQgPT4ge1xuXHRcdFx0Ly8gTG9vayBmb3IgdHlwZSBhbGlhcyBkZWNsYXJhdGlvbnM6IGV4cG9ydCB0eXBlIE5hbWUgPSBUeXBlO1xuXHRcdFx0aWYgKHRzLmlzVHlwZUFsaWFzRGVjbGFyYXRpb24obm9kZSkpIHtcblx0XHRcdFx0Y29uc3QgbmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0XHR0eXBlQWxpYXNlcy5zZXQobmFtZSwgbm9kZS50eXBlKTtcblx0XHRcdH1cblx0XHRcdFxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIHZpc2l0KTtcblx0XHR9O1xuXHRcdFxuXHRcdHZpc2l0KHNvdXJjZUZpbGUpO1xuXHRcdHJldHVybiB0eXBlQWxpYXNlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnR5IGFzc2lnbm1lbnRzIGZyb20gYSBzb3VyY2UgZmlsZVxuXHQgKiBSZXR1cm5zIGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgYW5kIGhhbmRsZXIgbG9jYXRpb24gaWYgZm91bmRcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFByb3BlcnRpZXNGcm9tU291cmNlRmlsZSAoXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRwcm9wZXJ0aWVzOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+LFxuXHRcdHR5cGVBbGlhc2VzPzogTWFwPHN0cmluZywgdHMuVHlwZU5vZGU+XG5cdCk6IHtcblx0XHRjb25zdHJ1Y3RvclBhcmFtcz86IENvbnN0cnVjdG9yUGFyYW1JbmZvW107XG5cdFx0aGFuZGxlckxvY2F0aW9uPzogeyBmaWxlUGF0aDogc3RyaW5nOyBsaW5lOiBudW1iZXI7IGNvbHVtbjogbnVtYmVyIH07XG5cdH0ge1xuXHRcdGxldCBjb25zdHJ1Y3RvclBhcmFtczogQ29uc3RydWN0b3JQYXJhbUluZm9bXSB8IHVuZGVmaW5lZDtcblx0XHRsZXQgaGFuZGxlckxvY2F0aW9uOiB7IGZpbGVQYXRoOiBzdHJpbmc7IGxpbmU6IG51bWJlcjsgY29sdW1uOiBudW1iZXIgfSB8IHVuZGVmaW5lZDtcblx0XHRcblx0XHRjb25zdCB2aXNpdCA9IChub2RlOiB0cy5Ob2RlKTogdm9pZCA9PiB7XG5cdFx0XHQvLyBMb29rIGZvciBleHBvcnRlZCBmdW5jdGlvbiBkZWNsYXJhdGlvbnMgKHRvcG9sb2dpY2EgY29udmVudGlvbjogb25lIGV4cG9ydGVkIGZ1bmN0aW9uIHBlciBmaWxlKVxuXHRcdFx0aWYgKHRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdFx0Ly8gQ2hlY2sgaWYgaXQncyBleHBvcnRlZFxuXHRcdFx0XHRjb25zdCBpc0V4cG9ydGVkID0gbm9kZS5tb2RpZmllcnM/LnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRXhwb3J0S2V5d29yZCk7XG5cdFx0XHRcdFxuXHRcdFx0XHRpZiAoaXNFeHBvcnRlZCkge1xuXHRcdFx0XHRcdHRoaXMuZXh0cmFjdFRoaXNQcm9wZXJ0aWVzKG5vZGUsIHByb3BlcnRpZXMpO1xuXHRcdFx0XHRcdC8vIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1zIGFuZCBsb2NhdGlvbiBmcm9tIHRoZSBleHBvcnRlZCBmdW5jdGlvblxuXHRcdFx0XHRcdGlmICghY29uc3RydWN0b3JQYXJhbXMpIHtcblx0XHRcdFx0XHRcdGNvbnN0cnVjdG9yUGFyYW1zID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JQYXJhbXMobm9kZSwgdHlwZUFsaWFzZXMpO1xuXHRcdFx0XHRcdFx0Ly8gQ2FwdHVyZSB0aGUgZnVuY3Rpb24gbG9jYXRpb25cblx0XHRcdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHRcdFx0KTtcblx0XHRcdFx0XHRcdC8vIGxpbmUgYW5kIGNvbHVtbiBhcmUgMS1iYXNlZFxuXHRcdFx0XHRcdFx0aGFuZGxlckxvY2F0aW9uID0ge1xuXHRcdFx0XHRcdFx0XHRmaWxlUGF0aCA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdFx0XHRcdGxpbmUgICAgIDogbGluZSArIDEsXG5cdFx0XHRcdFx0XHRcdGNvbHVtbiAgIDogY2hhcmFjdGVyICsgMVxuXHRcdFx0XHRcdFx0fTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIEFsc28gY2hlY2sgZnVuY3Rpb24gZXhwcmVzc2lvbnMvYXJyb3cgZnVuY3Rpb25zIGFzc2lnbmVkIHRvIGV4cG9ydHNcblx0XHRcdGVsc2UgaWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKG5vZGUpIHx8IHRzLmlzQXJyb3dGdW5jdGlvbihub2RlKSkge1xuXHRcdFx0XHR0aGlzLmV4dHJhY3RUaGlzUHJvcGVydGllcyhub2RlLCBwcm9wZXJ0aWVzKTtcblx0XHRcdFx0Ly8gRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbXMgZnJvbSBub24tZXhwb3J0ZWQgZnVuY3Rpb25zIHRvb1xuXHRcdFx0XHRpZiAoIWNvbnN0cnVjdG9yUGFyYW1zKSB7XG5cdFx0XHRcdFx0Y29uc3RydWN0b3JQYXJhbXMgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyhub2RlLCB0eXBlQWxpYXNlcyk7XG5cdFx0XHRcdFx0Ly8gQ2FwdHVyZSB0aGUgZnVuY3Rpb24gbG9jYXRpb25cblx0XHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHRcdCk7XG5cdFx0XHRcdFx0Ly8gbGluZSBhbmQgY29sdW1uIGFyZSAxLWJhc2VkXG5cdFx0XHRcdFx0aGFuZGxlckxvY2F0aW9uID0ge1xuXHRcdFx0XHRcdFx0ZmlsZVBhdGggOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRcdFx0bGluZSAgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0XHRcdGNvbHVtbiAgIDogY2hhcmFjdGVyICsgMVxuXHRcdFx0XHRcdH07XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdFxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIHZpc2l0KTtcblx0XHR9O1xuXHRcdFxuXHRcdHZpc2l0KHNvdXJjZUZpbGUpO1xuXHRcdHJldHVybiB7IGNvbnN0cnVjdG9yUGFyYW1zLCBoYW5kbGVyTG9jYXRpb24gfTtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGB0aGlzLnByb3BlcnR5ID0gdmFsdWVgIGFzc2lnbm1lbnRzIGZyb20gYSBmdW5jdGlvbiBib2R5XG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RUaGlzUHJvcGVydGllcyAoXG5cdFx0ZnVuYzogdHMuRnVuY3Rpb25EZWNsYXJhdGlvbiB8IHRzLkZ1bmN0aW9uRXhwcmVzc2lvbiB8IHRzLkFycm93RnVuY3Rpb24sXG5cdFx0cHJvcGVydGllczogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPlxuXHQpOiB2b2lkIHtcblx0XHRjb25zdCB7IGJvZHkgfSA9IGZ1bmM7XG5cdFx0aWYgKCFib2R5KSByZXR1cm47XG5cdFx0XG5cdFx0Y29uc3QgdmlzaXRTdGF0ZW1lbnRzID0gKG5vZGU6IHRzLk5vZGUpOiB2b2lkID0+IHtcblx0XHRcdC8vIEhhbmRsZSBleHByZXNzaW9uIHN0YXRlbWVudHNcblx0XHRcdGlmICh0cy5pc0V4cHJlc3Npb25TdGF0ZW1lbnQobm9kZSkpIHtcblx0XHRcdFx0Y29uc3QgZXhwciA9IG5vZGUuZXhwcmVzc2lvbjtcblx0XHRcdFx0XG5cdFx0XHRcdC8vIENoZWNrIGZvciB0aGlzLnByb3AgPSB2YWx1ZVxuXHRcdFx0XHRpZiAodHMuaXNCaW5hcnlFeHByZXNzaW9uKGV4cHIpICYmIFxuXHRcdFx0XHQgICAgZXhwci5vcGVyYXRvclRva2VuLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRXF1YWxzVG9rZW4pIHtcblx0XHRcdFx0XHRjb25zdCB7IGxlZnQgfSA9IGV4cHI7XG5cdFx0XHRcdFx0Y29uc3QgeyByaWdodCB9ID0gZXhwcjtcblx0XHRcdFx0XHRcblx0XHRcdFx0XHQvLyBDaGVjayBpZiBsZWZ0IHNpZGUgaXMgdGhpcy5wcm9wZXJ0eVxuXHRcdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihsZWZ0KSAmJlxuXHRcdFx0XHRcdCAgICBsZWZ0LmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBsZWZ0Lm5hbWUudGV4dDtcblx0XHRcdFx0XHRcdGNvbnN0IHByb3BUeXBlID0gdGhpcy5pbmZlclR5cGUocmlnaHQpO1xuXHRcdFx0XHRcdFx0XG5cdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChwcm9wTmFtZSwge1xuXHRcdFx0XHRcdFx0XHRuYW1lICAgICA6IHByb3BOYW1lLFxuXHRcdFx0XHRcdFx0XHR0eXBlICAgICA6IHByb3BUeXBlLFxuXHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0XHRyZWFkb25seSA6IGZhbHNlXG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0XG5cdFx0XHRcdC8vIENoZWNrIGZvciBPYmplY3QuYXNzaWduKHRoaXMsIHsuLi59KVxuXHRcdFx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0XHRcdGNvbnN0IGNhbGxFeHByID0gZXhwcjtcblx0XHRcdFx0XHRpZiAodGhpcy5pc09iamVjdEFzc2lnbkNhbGwoY2FsbEV4cHIpKSB7XG5cdFx0XHRcdFx0XHR0aGlzLmV4dHJhY3RGcm9tT2JqZWN0QXNzaWduKGNhbGxFeHByLCBwcm9wZXJ0aWVzKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdFxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIHZpc2l0U3RhdGVtZW50cyk7XG5cdFx0fTtcblx0XHRcblx0XHR2aXNpdFN0YXRlbWVudHMoYm9keSk7XG5cdH1cblxuXHQvKipcblx0ICogQ2hlY2sgaWYgYSBjYWxsIGV4cHJlc3Npb24gaXMgT2JqZWN0LmFzc2lnbih0aGlzLCAuLi4pXG5cdCAqL1xuXHRwcml2YXRlIGlzT2JqZWN0QXNzaWduQ2FsbCAoY2FsbEV4cHI6IHRzLkNhbGxFeHByZXNzaW9uKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgZXhwciA9IGNhbGxFeHByLmV4cHJlc3Npb247XG5cdFx0aWYgKCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkgcmV0dXJuIGZhbHNlO1xuXHRcdFxuXHRcdGNvbnN0IG9iak5hbWUgPSB0cy5pc0lkZW50aWZpZXIoZXhwci5leHByZXNzaW9uKSA/IGV4cHIuZXhwcmVzc2lvbi50ZXh0IDogbnVsbDtcblx0XHRjb25zdCBtZXRob2ROYW1lID0gZXhwci5uYW1lLnRleHQ7XG5cdFx0XG5cdFx0aWYgKG9iak5hbWUgPT09ICdPYmplY3QnICYmIG1ldGhvZE5hbWUgPT09ICdhc3NpZ24nKSB7XG5cdFx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBjYWxsRXhwci5hcmd1bWVudHM7XG5cdFx0XHRpZiAoZmlyc3RBcmcgJiYgZmlyc3RBcmcua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblx0XHR9XG5cdFx0XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIE9iamVjdC5hc3NpZ24odGhpcywgZGF0YSkgcGF0dGVyblxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0RnJvbU9iamVjdEFzc2lnbiAoXG5cdFx0Y2FsbEV4cHI6IHRzLkNhbGxFeHByZXNzaW9uLFxuXHRcdHByb3BlcnRpZXM6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz5cblx0KTogdm9pZCB7XG5cdFx0Ly8gTG9vayBmb3IgdGhlIGRhdGEgYXJndW1lbnQgKHNlY29uZCBhcmd1bWVudClcblx0XHRjb25zdCBbICwgZGF0YUFyZyBdID0gY2FsbEV4cHIuYXJndW1lbnRzO1xuXHRcdGlmICghZGF0YUFyZykgcmV0dXJuO1xuXHRcdFxuXHRcdC8vIElmIGl0J3MgYW4gb2JqZWN0IGxpdGVyYWwsIGV4dHJhY3QgcHJvcGVydGllc1xuXHRcdGlmICh0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGRhdGFBcmcpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IHByb3Agb2YgZGF0YUFyZy5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSAmJiB0cy5pc0lkZW50aWZpZXIocHJvcC5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gcHJvcC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Y29uc3QgcHJvcFR5cGUgPSB0aGlzLmluZmVyVHlwZShwcm9wLmluaXRpYWxpemVyKTtcblx0XHRcdFx0XHRcblx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChwcm9wTmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSAgICAgOiBwcm9wTmFtZSxcblx0XHRcdFx0XHRcdHR5cGUgICAgIDogcHJvcFR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0cmVhZG9ubHkgOiBmYWxzZVxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGEgZnVuY3Rpb25cblx0ICogU2ltaWxhciB0byBtYWluIGFuYWx5emVyIC0gc2tpcHMgYHRoaXNgIHBhcmFtZXRlciBhbmQgZXhwYW5kcyBkYXRhIHR5cGVzXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyAoXG5cdFx0ZnVuYzogdHMuRnVuY3Rpb25EZWNsYXJhdGlvbiB8IHRzLkZ1bmN0aW9uRXhwcmVzc2lvbiB8IHRzLkFycm93RnVuY3Rpb24sXG5cdFx0dHlwZUFsaWFzZXM/OiBNYXA8c3RyaW5nLCB0cy5UeXBlTm9kZT5cblx0KTogQ29uc3RydWN0b3JQYXJhbUluZm9bXSB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCFmdW5jLnBhcmFtZXRlcnMgfHwgZnVuYy5wYXJhbWV0ZXJzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBwYXJhbXM6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10gPSBbXTtcblx0XHRcblx0XHQvLyBTa2lwIGB0aGlzYCBwYXJhbWV0ZXIgKGZpcnN0IHBhcmFtKSBhbmQgZXh0cmFjdCBkYXRhIHBhcmFtZXRlcnNcblx0XHRmb3IgKGxldCBpID0gMDsgaSA8IGZ1bmMucGFyYW1ldGVycy5sZW5ndGg7IGkrKykge1xuXHRcdFx0Y29uc3QgcGFyYW0gPSBmdW5jLnBhcmFtZXRlcnNbIGkgXTtcblx0XHRcdFxuXHRcdFx0Ly8gU2tpcCBgdGhpc2AgcGFyYW1ldGVyIChmaXJzdCBwYXJhbSlcblx0XHRcdGlmIChpID09PSAwICYmIHBhcmFtLm5hbWUua2luZCA9PT0gdHMuU3ludGF4S2luZC5JZGVudGlmaWVyICYmXG5cdFx0XHQgICAgKHBhcmFtLm5hbWUgYXMgdHMuSWRlbnRpZmllcikudGV4dCA9PT0gJ3RoaXMnKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0XG5cdFx0XHRpZiAoIXBhcmFtLnR5cGUpIGNvbnRpbnVlO1xuXHRcdFx0XG5cdFx0XHRjb25zdCBwYXJhbU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgPyBwYXJhbS5uYW1lLnRleHQgOiAnYXJnJztcblx0XHRcdGNvbnN0IG9wdGlvbmFsID0gcGFyYW0ucXVlc3Rpb25Ub2tlbiAhPT0gdW5kZWZpbmVkIHx8IHBhcmFtLmluaXRpYWxpemVyICE9PSB1bmRlZmluZWQ7XG5cdFx0XHRcblx0XHRcdC8vIEV4cGFuZCB0eXBlIHRvIG9iamVjdCBsaXRlcmFsIGlmIHBvc3NpYmxlXG5cdFx0XHRjb25zdCBleHBhbmRlZFR5cGUgPSB0aGlzLmV4cGFuZFR5cGVUb09iamVjdChwYXJhbS50eXBlLCB0eXBlQWxpYXNlcyk7XG5cdFx0XHRjb25zdCBwYXJhbVR5cGUgPSBleHBhbmRlZFR5cGUgfHwgdGhpcy50eXBlTm9kZVRvU2ltcGxlU3RyaW5nKHBhcmFtLnR5cGUpO1xuXHRcdFx0XG5cdFx0XHRwYXJhbXMucHVzaCh7XG5cdFx0XHRcdG5hbWUgICAgIDogcGFyYW1OYW1lLFxuXHRcdFx0XHR0eXBlICAgICA6IHBhcmFtVHlwZSxcblx0XHRcdFx0b3B0aW9uYWwgOiBvcHRpb25hbFxuXHRcdFx0fSk7XG5cdFx0fVxuXHRcdFxuXHRcdHJldHVybiBwYXJhbXMubGVuZ3RoID4gMCA/IHBhcmFtcyA6IHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHBhbmQgYSB0eXBlIG5vZGUgdG8gaXRzIG9iamVjdCBsaXRlcmFsIHJlcHJlc2VudGF0aW9uXG5cdCAqIFNpbWlsYXIgdG8gbWFpbiBhbmFseXplcidzIHJlc29sdmVUeXBlQW5kRXh0cmFjdFxuXHQgKi9cblx0cHJpdmF0ZSBleHBhbmRUeXBlVG9PYmplY3QgKFxuXHRcdHR5cGVOb2RlOiB0cy5UeXBlTm9kZSxcblx0XHR0eXBlQWxpYXNlcz86IE1hcDxzdHJpbmcsIHRzLlR5cGVOb2RlPlxuXHQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdC8vIERpcmVjdCBpbmxpbmUgdHlwZSBsaXRlcmFsOiB7IHByb3A6IHR5cGUgfVxuXHRcdGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZSh0eXBlTm9kZSkpIHtcblx0XHRcdGNvbnN0IHByb3BzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgdHlwZU5vZGUubWVtYmVycykge1xuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Y29uc3Qgb3B0ID0gbWVtYmVyLnF1ZXN0aW9uVG9rZW4gPyAnPycgOiAnJztcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy50eXBlTm9kZVRvU2ltcGxlU3RyaW5nKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRwcm9wcy5wdXNoKGAke3Byb3BOYW1lfSR7b3B0fTogJHt0eXBlfWApO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gYHsgJHtwcm9wcy5qb2luKCc7ICcpfSB9YDtcblx0XHR9XG5cblx0XHQvLyBUeXBlIHJlZmVyZW5jZTogU2VudGllbmNlRGF0YSwgZXRjLiAtIHRyeSB0byBleHBhbmQgZnJvbSB0eXBlIGFsaWFzZXNcblx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZSh0eXBlTm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKHR5cGVOb2RlLnR5cGVOYW1lKSkge1xuXHRcdFx0Y29uc3QgdHlwZU5hbWUgPSB0eXBlTm9kZS50eXBlTmFtZS50ZXh0O1xuXHRcdFx0XG5cdFx0XHQvLyBJZiB3ZSBoYXZlIHR5cGUgYWxpYXNlcywgdHJ5IHRvIGV4cGFuZCB0aGUgcmVmZXJlbmNlZCB0eXBlXG5cdFx0XHRpZiAodHlwZUFsaWFzZXMpIHtcblx0XHRcdFx0Y29uc3QgYWxpYXNlZFR5cGUgPSB0eXBlQWxpYXNlcy5nZXQodHlwZU5hbWUpO1xuXHRcdFx0XHRpZiAoYWxpYXNlZFR5cGUpIHtcblx0XHRcdFx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMuZXhwYW5kVHlwZVRvT2JqZWN0KGFsaWFzZWRUeXBlLCB0eXBlQWxpYXNlcyk7XG5cdFx0XHRcdFx0aWYgKGV4cGFuZGVkKSByZXR1cm4gZXhwYW5kZWQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdFxuXHRcdFx0Ly8gSWYgbm90IGFuIG9iamVjdCB0eXBlIGFsaWFzLCByZXR1cm4gdGhlIHR5cGUgbmFtZVxuXHRcdFx0cmV0dXJuIHR5cGVOYW1lO1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogQ29udmVydCBhIFR5cGVTY3JpcHQgdHlwZSBub2RlIHRvIGEgc2ltcGxlIHN0cmluZyByZXByZXNlbnRhdGlvblxuXHQgKi9cblx0cHJpdmF0ZSB0eXBlTm9kZVRvU2ltcGxlU3RyaW5nICh0eXBlTm9kZTogdHMuVHlwZU5vZGUgfCB1bmRlZmluZWQpOiBzdHJpbmcge1xuXHRcdGlmICghdHlwZU5vZGUpIHJldHVybiAnYW55Jztcblx0XHRcblx0XHRzd2l0Y2ggKHR5cGVOb2RlLmtpbmQpIHtcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuU3RyaW5nS2V5d29yZDpcblx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVtYmVyS2V5d29yZDpcblx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQm9vbGVhbktleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5BbnlLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdhbnknO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5BcnJheVR5cGU6XG5cdFx0XHRyZXR1cm4gJ0FycmF5PGFueT4nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlUmVmZXJlbmNlOiB7XG5cdFx0XHRjb25zdCB0eXBlUmVmID0gdHlwZU5vZGUgYXMgdHMuVHlwZVJlZmVyZW5jZU5vZGU7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKHR5cGVSZWYudHlwZU5hbWUpKSB7XG5cdFx0XHRcdHJldHVybiB0eXBlUmVmLnR5cGVOYW1lLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ2FueSc7XG5cdFx0fVxuXHRcdGRlZmF1bHQ6XG5cdFx0XHRyZXR1cm4gJ2FueSc7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEluZmVyIFR5cGVTY3JpcHQgdHlwZSBmcm9tIGFuIGV4cHJlc3Npb25cblx0ICovXG5cdHByaXZhdGUgaW5mZXJUeXBlIChub2RlOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHtcblx0XHRzd2l0Y2ggKG5vZGUua2luZCkge1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5TdHJpbmdMaXRlcmFsOlxuXHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdW1lcmljTGl0ZXJhbDpcblx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHJ1ZUtleXdvcmQ6XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZDpcblx0XHRcdHJldHVybiAnYm9vbGVhbic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bGxLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdudWxsJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5kZWZpbmVkS2V5d29yZDpcblx0XHRcdHJldHVybiAndW5kZWZpbmVkJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbjpcblx0XHRcdHJldHVybiAnQXJyYXk8YW55Pic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk9iamVjdExpdGVyYWxFeHByZXNzaW9uOlxuXHRcdFx0cmV0dXJuICdvYmplY3QnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OZXdFeHByZXNzaW9uOlxuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJOZXdFeHByZXNzaW9uVHlwZShub2RlIGFzIHRzLk5ld0V4cHJlc3Npb24pO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Db25kaXRpb25hbEV4cHJlc3Npb246XG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclR5cGUoKG5vZGUgYXMgdHMuQ29uZGl0aW9uYWxFeHByZXNzaW9uKS53aGVuVHJ1ZSk7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkJpbmFyeUV4cHJlc3Npb246IHtcblx0XHRcdGNvbnN0IGJpbkV4cHIgPSBub2RlIGFzIHRzLkJpbmFyeUV4cHJlc3Npb247XG5cdFx0XHQvLyBDaGVjayBmb3IgbG9naWNhbCBPUiBwYXR0ZXJuOiB2YWx1ZSB8fCBkZWZhdWx0XG5cdFx0XHRpZiAoYmluRXhwci5vcGVyYXRvclRva2VuLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuQmFyQmFyVG9rZW4pIHtcblx0XHRcdFx0Ly8gUmV0dXJuIHRoZSB0eXBlIG9mIHRoZSByaWdodCBzaWRlICh0aGUgZGVmYXVsdCB2YWx1ZSlcblx0XHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJUeXBlKGJpbkV4cHIucmlnaHQpO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICdhbnknO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uOiB7XG5cdFx0XHRjb25zdCBwcm9wQWNjZXNzID0gbm9kZSBhcyB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb247XG5cdFx0XHQvLyBIYW5kbGUgZGF0YT8ucHJvcGVydHkgcGF0dGVybnNcblx0XHRcdHJldHVybiB0aGlzLmluZmVyVHlwZShwcm9wQWNjZXNzKTtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkNhbGxFeHByZXNzaW9uOiB7XG5cdFx0XHRjb25zdCBjYWxsRXhwciA9IG5vZGUgYXMgdHMuQ2FsbEV4cHJlc3Npb247XG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlckNhbGxFeHByZXNzaW9uVHlwZShjYWxsRXhwcik7XG5cdFx0fVxuXHRcdGRlZmF1bHQ6XG5cdFx0XHRyZXR1cm4gJ2FueSc7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEluZmVyIHR5cGUgZnJvbSBuZXcgZXhwcmVzc2lvbnMgbGlrZSBuZXcgRGF0ZSgpLCBuZXcgQXJyYXkoKSwgZXRjLlxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlck5ld0V4cHJlc3Npb25UeXBlIChub2RlOiB0cy5OZXdFeHByZXNzaW9uKTogc3RyaW5nIHtcblx0XHRjb25zdCBleHByID0gbm9kZS5leHByZXNzaW9uO1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHN3aXRjaCAoZXhwci50ZXh0KSB7XG5cdFx0XHRjYXNlICdEYXRlJzpcblx0XHRcdFx0Ly8gRGF0ZS5ub3coKSByZXR1cm5zIG51bWJlclxuXHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRjYXNlICdBcnJheSc6XG5cdFx0XHRcdHJldHVybiAnQXJyYXk8YW55Pic7XG5cdFx0XHRjYXNlICdNYXAnOlxuXHRcdFx0XHRyZXR1cm4gJ01hcDxhbnksIGFueT4nO1xuXHRcdFx0Y2FzZSAnU2V0Jzpcblx0XHRcdFx0cmV0dXJuICdTZXQ8YW55Pic7XG5cdFx0XHRjYXNlICdSZWdFeHAnOlxuXHRcdFx0XHRyZXR1cm4gJ1JlZ0V4cCc7XG5cdFx0XHRkZWZhdWx0OlxuXHRcdFx0XHRyZXR1cm4gZXhwci50ZXh0O1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gJ2FueSc7XG5cdH1cblxuXHQvKipcblx0ICogSW5mZXIgdHlwZSBmcm9tIGNhbGwgZXhwcmVzc2lvbnMgbGlrZSBEYXRlLm5vdygpLCBwYXJzZUludCgpLCBldGMuXG5cdCAqL1xuXHRwcml2YXRlIGluZmVyQ2FsbEV4cHJlc3Npb25UeXBlIChub2RlOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB7XG5cdFx0Y29uc3QgZXhwciA9IG5vZGUuZXhwcmVzc2lvbjtcblx0XHRcblx0XHQvLyBIYW5kbGUgRGF0ZS5ub3coKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0Y29uc3Qgb2JqID0gZXhwci5leHByZXNzaW9uO1xuXHRcdFx0Y29uc3QgbWV0aG9kID0gZXhwci5uYW1lLnRleHQ7XG5cdFx0XHRcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIob2JqKSAmJiBvYmoudGV4dCA9PT0gJ0RhdGUnICYmIG1ldGhvZCA9PT0gJ25vdycpIHtcblx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRcblx0XHQvLyBIYW5kbGUgcGFyc2VJbnQsIHBhcnNlRmxvYXQsIFN0cmluZygpLCBOdW1iZXIoKSwgQm9vbGVhbigpXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0c3dpdGNoIChleHByLnRleHQpIHtcblx0XHRcdGNhc2UgJ3BhcnNlSW50Jzpcblx0XHRcdGNhc2UgJ3BhcnNlRmxvYXQnOlxuXHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRjYXNlICdTdHJpbmcnOlxuXHRcdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0XHRjYXNlICdOdW1iZXInOlxuXHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRjYXNlICdCb29sZWFuJzpcblx0XHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRcdH1cblx0XHR9XG5cdFx0XG5cdFx0cmV0dXJuICdhbnknO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCB0aGUgdHlwZSBncmFwaFxuXHQgKi9cblx0Z2V0R3JhcGggKCk6IFR5cGVHcmFwaEltcGwge1xuXHRcdHJldHVybiB0aGlzLmdyYXBoO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBjb2xsZWN0ZWQgZXJyb3JzXG5cdCAqL1xuXHRnZXRFcnJvcnMgKCk6IHN0cmluZ1tdIHtcblx0XHRyZXR1cm4gdGhpcy5lcnJvcnM7XG5cdH1cbn1cbiJdfQ==