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
        // Store program for future use (currently unused but kept for extensibility)
        void program;
    }
    /**
     * Analyze a source file for Mnemonica type definitions
     */
    analyzeFile(sourceFile) {
        this.errors = [];
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
     * Visit a node in the AST
     */
    visitNode(node, sourceFile) {
        // Check for define() calls
        if (this.isDefineCall(node)) {
            this.processDefineCall(node, sourceFile);
        }
        // Check for decorate() decorator
        if (this.isDecorateDecorator(node)) {
            this.processDecorateDecorator(node, sourceFile);
        }
        // Recursively visit children
        ts.forEachChild(node, child => this.visitNode(child, sourceFile));
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
            return expression.name.text === 'define';
        }
        return false;
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
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, call.getStart());
        // Get the type name from arguments
        const typeName = this.extractTypeName(call);
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
        const parentNode = this.findParentType(call);
        // Create type node
        const node = graph_1.TypeGraphImpl.createNode(typeName, parentNode, sourceFile.fileName, line + 1, character + 1);
        // Extract properties from constructor function
        node.properties = this.extractProperties(call);
        // Add to graph
        if (parentNode) {
            this.graph.addChild(parentNode, node);
        }
        else {
            this.graph.addRoot(node);
        }
    }
    /**
     * Process a @decorate() decorator
     */
    processDecorateDecorator(decorator, sourceFile) {
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, decorator.getStart());
        // Get the class declaration
        const classDecl = decorator.parent;
        if (!classDecl.name) {
            this.errors.push({
                message: 'Decorated class has no name',
                file: sourceFile.fileName,
                line: line + 1,
                column: character + 1,
            });
            return;
        }
        const typeName = classDecl.name.text;
        // Try to find parent type from decorator arguments
        let parentNode;
        if (ts.isCallExpression(decorator.expression)) {
            const args = decorator.expression.arguments;
            if (args.length > 0 && ts.isIdentifier(args[0])) {
                const parentName = args[0].text;
                parentNode = this.graph.findType(parentName);
            }
        }
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
    findParentType(call) {
        const expression = call.expression;
        // Check for method call: SomeType.define('SubType', ...)
        if (!ts.isPropertyAccessExpression(expression)) {
            return undefined;
        }
        // Get the object being called on (SomeType in SomeType.define)
        const obj = expression.expression;
        if (ts.isIdentifier(obj)) {
            // Direct reference to parent type
            return this.graph.findType(obj.text);
        }
        if (ts.isPropertyAccessExpression(obj)) {
            // Nested access: instance.Type.define - try to resolve
            const chain = this.getPropertyChain(obj);
            if (chain.length > 0) {
                return this.graph.findType(chain.join('.'));
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
            chain.unshift(current.name.text);
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
        // Handle function expression
        if (ts.isFunctionExpression(handlerArg) || ts.isArrowFunction(handlerArg)) {
            const body = handlerArg.body;
            // Function body with statements
            if (ts.isBlock(body)) {
                for (const stmt of body.statements) {
                    if (ts.isExpressionStatement(stmt)) {
                        this.extractPropertyFromStatement(stmt.expression, properties);
                    }
                }
            }
        }
        // Handle class expression
        if (ts.isClassExpression(handlerArg)) {
            for (const member of handlerArg.members) {
                if (ts.isPropertyDeclaration(member) && member.name) {
                    const name = ts.isIdentifier(member.name) ? member.name.text : '';
                    if (name) {
                        properties.set(name, {
                            name,
                            type: this.inferType(member.type),
                            optional: !!member.questionToken,
                        });
                    }
                }
            }
        }
        return properties;
    }
    /**
     * Extract property assignment from statement
     */
    extractPropertyFromStatement(expr, properties) {
        // Handle: this.property = value
        if (ts.isBinaryExpression(expr) &&
            expr.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
            const left = expr.left;
            if (ts.isPropertyAccessExpression(left)) {
                // Check if accessing 'this'
                if (ts.isIdentifier(left.expression) && left.expression.text === 'this') {
                    const name = left.name.text;
                    properties.set(name, {
                        name,
                        type: 'unknown',
                        optional: false,
                    });
                }
            }
        }
        // Handle: Object.assign(this, { prop: value })
        if (ts.isCallExpression(expr)) {
            const fn = expr.expression;
            if (ts.isPropertyAccessExpression(fn) &&
                fn.name.text === 'assign' &&
                ts.isIdentifier(fn.expression) &&
                fn.expression.text === 'Object') {
                const args = expr.arguments;
                if (args.length >= 2 && ts.isIdentifier(args[0]) && args[0].text === 'this') {
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
     * Extract properties from class declaration
     */
    extractClassProperties(classDecl) {
        const properties = new Map();
        for (const member of classDecl.members) {
            if (ts.isPropertyDeclaration(member) && member.name) {
                const name = ts.isIdentifier(member.name) ? member.name.text : '';
                if (name) {
                    properties.set(name, {
                        name,
                        type: this.inferType(member.type),
                        optional: !!member.questionToken,
                    });
                }
            }
        }
        return properties;
    }
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
            default:
                // For complex types, return the text representation
                return 'unknown';
        }
    }
    /**
     * Infer type from initializer
     */
    inferTypeFromInitializer(initializer) {
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
            default:
                return 'unknown';
        }
    }
}
exports.MnemonicaAnalyzer = MnemonicaAnalyzer;
//# sourceMappingURL=analyzer.js.map