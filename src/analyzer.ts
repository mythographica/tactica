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
	private visitNode(node: ts.Node, sourceFile: ts.SourceFile, currentClass?: ts.ClassDeclaration): void {
		// Check for define() calls
		if (this.isDefineCall(node)) {
			this.processDefineCall(node as ts.CallExpression, sourceFile);
		}

		// Check for decorate() decorator
		if (this.isDecorateDecorator(node)) {
			this.processDecorateDecorator(node as ts.Decorator, sourceFile, currentClass);
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
			return expression.name?.text === 'define';
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
			call.getStart(sourceFile)
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
	private processDecorateDecorator(decorator: ts.Decorator, sourceFile: ts.SourceFile, classDeclParam?: ts.ClassDeclaration): void {
		const { line, character } = ts.getLineAndCharacterOfPosition(
			sourceFile,
			decorator.getStart(sourceFile)
		);

		// Get the class declaration - use the passed context if parent is not set
		const classDecl = decorator.parent as ts.ClassDeclaration | undefined || classDeclParam;
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
		let parentNode: TypeNode | undefined;
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
			// Direct reference to parent type - search by simple name
			const name = obj.text;
			// First try exact match
			const exact = this.graph.findType(name);
			if (exact) return exact;
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

		return undefined;
	}

	/**
	 * Get property chain from nested access
	 */
	private getPropertyChain(expr: ts.PropertyAccessExpression | ts.Identifier): string[] {
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
	 * Extract properties from constructor function
	 */
	private extractProperties(call: ts.CallExpression): Map<string, PropertyInfo> {
		const properties = new Map<string, PropertyInfo>();

		const handlerArg = call.arguments[1];
		if (!handlerArg) {
			return properties;
		}

		// Build type map from data parameter (for this.x = data.x patterns)
		const dataTypeMap = this.buildDataTypeMap(handlerArg);

		// Handle function expression
		if (ts.isFunctionExpression(handlerArg) || ts.isArrowFunction(handlerArg)) {
			const body = handlerArg.body;

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
	 * Build a type map from all parameters with inline object type annotations
	 * Returns a map of "paramName.propertyName" -> type
	 */
	private buildDataTypeMap(handlerArg: ts.Expression): Map<string, string> {
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
		}

		return typeMap;
	}

	/**
	 * Extract property access chain (e.g., "dataRenamed.id" from dataRenamed.id)
	 * Handles fallbacks like: data.permissions || []
	 */
	private getPropertyAccessChain(expr: ts.Expression): string | undefined {
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
	private extractPropertyFromStatement(
		expr: ts.Expression,
		properties: Map<string, PropertyInfo>,
		dataTypeMap: Map<string, string> = new Map()
	): void {
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
						if (!type) {
							type = this.inferTypeFromInitializer(expr.right);
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
	 * Extract properties from class declaration
	 */
	private extractClassProperties(classDecl: ts.ClassDeclaration): Map<string, PropertyInfo> {
		const properties = new Map<string, PropertyInfo>();

		for (const member of classDecl.members) {
			if (ts.isPropertyDeclaration(member) && member.name) {
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
			case ts.SyntaxKind.NewExpression: {
				// Handle new Date(), new Map(), etc.
				const newExpr = initializer as ts.NewExpression;
				if (ts.isIdentifier(newExpr.expression)) {
					return newExpr.expression.text;
				}
				return 'object';
			}
			default:
				return 'unknown';
		}
	}
}
