'use strict';

import * as ts from 'typescript';
import { TypeNode, PropertyInfo, AnalyzeResult, AnalyzeError } from './types';
import { TypeGraphImpl } from './graph';

/**
 * AST Analyzer for finding Mnemonica define() and decorate() calls
 */
export class MnemonicaAnalyzer {
	private errors: AnalyzeError[] = [];
	private graph = new TypeGraphImpl();

	constructor(program?: ts.Program) {
		// Store program for future use (currently unused but kept for extensibility)
		void program;
	}

	/**
	 * Analyze a source file for Mnemonica type definitions
	 */
	analyzeFile(sourceFile: ts.SourceFile): AnalyzeResult {
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
	analyzeSource(sourceCode: string, fileName = 'temp.ts'): AnalyzeResult {
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
	getGraph(): TypeGraphImpl {
		return this.graph;
	}

	/**
	 * Visit a node in the AST
	 */
	private visitNode(node: ts.Node, sourceFile: ts.SourceFile): void {
		// Check for define() calls
		if (this.isDefineCall(node)) {
			this.processDefineCall(node as ts.CallExpression, sourceFile);
		}

		// Check for decorate() decorator
		if (this.isDecorateDecorator(node)) {
			this.processDecorateDecorator(node as ts.Decorator, sourceFile);
		}

		// Recursively visit children
		ts.forEachChild(node, child => this.visitNode(child, sourceFile));
	}

	/**
	 * Check if a node is a define() call
	 */
	private isDefineCall(node: ts.Node): node is ts.CallExpression {
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
	private isDecorateDecorator(node: ts.Node): node is ts.Decorator {
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
	private processDefineCall(call: ts.CallExpression, sourceFile: ts.SourceFile): void {
		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			call.getStart()
		);

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
		const node = TypeGraphImpl.createNode(
			typeName,
			parentNode,
			sourceFile.fileName,
			line + 1,
			character + 1
		);

		// Extract properties from constructor function
		node.properties = this.extractProperties(call);

		// Add to graph
		if (parentNode) {
			this.graph.addChild(parentNode, node);
		} else {
			this.graph.addRoot(node);
		}
	}

	/**
	 * Process a @decorate() decorator
	 */
	private processDecorateDecorator(decorator: ts.Decorator, sourceFile: ts.SourceFile): void {
		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			decorator.getStart()
		);

		// Get the class declaration
		const classDecl = decorator.parent as ts.ClassDeclaration;
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
		let parentNode: TypeNode | undefined;
		if (ts.isCallExpression(decorator.expression)) {
			const args = decorator.expression.arguments;
			if (args.length > 0 && ts.isIdentifier(args[0])) {
				const parentName = args[0].text;
				parentNode = this.graph.findType(parentName);
			}
		}

		// Create type node
		const node = TypeGraphImpl.createNode(
			typeName,
			parentNode,
			sourceFile.fileName,
			line + 1,
			character + 1
		);

		// Extract properties from class members
		node.properties = this.extractClassProperties(classDecl);

		// Add to graph
		if (parentNode) {
			this.graph.addChild(parentNode, node);
		} else {
			this.graph.addRoot(node);
		}
	}

	/**
	 * Extract type name from define() call arguments
	 */
	private extractTypeName(call: ts.CallExpression): string | undefined {
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
	private findParentType(call: ts.CallExpression): TypeNode | undefined {
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
	private getPropertyChain(expr: ts.PropertyAccessExpression | ts.Identifier): string[] {
		const chain: string[] = [];

		let current: ts.Expression = expr;
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
	private extractProperties(call: ts.CallExpression): Map<string, PropertyInfo> {
		const properties = new Map<string, PropertyInfo>();

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
	private extractPropertyFromStatement(
		expr: ts.Expression,
		properties: Map<string, PropertyInfo>
	): void {
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
	private extractClassProperties(classDecl: ts.ClassDeclaration): Map<string, PropertyInfo> {
		const properties = new Map<string, PropertyInfo>();

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
	private inferType(typeNode?: ts.TypeNode): string {
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
				return 'Array<' + this.inferType((typeNode as ts.ArrayTypeNode).elementType) + '>';
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
	private inferTypeFromInitializer(initializer: ts.Expression): string {
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
