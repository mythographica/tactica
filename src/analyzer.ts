'use strict';

import * as ts from 'typescript';
import { TypeNode, PropertyInfo, AnalyzeResult, AnalyzeError, DefinitionInfo, UsageInfo } from './types';
import { TypeGraphImpl } from './graph';

/**
 * AST Analyzer for finding Mnemonica define() and decorate() calls
 */
export class MnemonicaAnalyzer {
	private errors: AnalyzeError[] = [];
	private graph = new TypeGraphImpl();
	private definitions = new Map<string, DefinitionInfo>();
	private usages = new Map<string, UsageInfo[]>();

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
	 * Get collected definitions
	 */
	getDefinitions(): Map<string, DefinitionInfo> {
		return this.definitions;
	}

	/**
	 * Get collected usages
	 */
	getUsages(): Map<string, UsageInfo[]> {
		return this.usages;
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

		// Check for type usages (new Type(), type annotations, etc.)
		this.collectUsage(node, sourceFile);

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
		* Extract config options from define() call
		*/
	private extractConfig(call: ts.CallExpression): { strictChain?: boolean; blockErrors?: boolean } {
		const config: { strictChain?: boolean; blockErrors?: boolean } = {};

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
				} else if (propName === 'strictChain' && prop.initializer.kind === ts.SyntaxKind.FalseKeyword) {
					config.strictChain = false;
				} else if (propName === 'blockErrors' && prop.initializer.kind === ts.SyntaxKind.TrueKeyword) {
					config.blockErrors = true;
				} else if (propName === 'blockErrors' && prop.initializer.kind === ts.SyntaxKind.FalseKeyword) {
					config.blockErrors = false;
				}
			}
		}

		return config;
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

		// Build full path
		const fullPath = parentNode ? `${parentNode.fullPath}.${typeName}` : typeName;

		// Extract config options
		const config = this.extractConfig(call);

		// Create definition info
		const definition: DefinitionInfo = {
			name: typeName,
			location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
			kind: 'define',
			parent: parentNode ? parentNode.fullPath : null,
			strictChain: config.strictChain ?? true,
			blockErrors: config.blockErrors ?? false,
		};
		this.definitions.set(fullPath, definition);

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
		let parentFullPath: string | null = null;
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
		const definition: DefinitionInfo = {
			name: typeName,
			location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
			kind: 'decorate',
			parent: parentFullPath,
			strictChain: true, // decorate uses strict defaults
			blockErrors: false,
		};
		this.definitions.set(fullPath, definition);

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
			} else {
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
			case ts.SyntaxKind.LiteralType: {
				// Handle string literal types like 'user', 'admin', etc.
				const literal = (typeNode as ts.LiteralTypeNode).literal;
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
			default:
				// For complex types, return the text representation
				return 'unknown';
		}
	}

	/**
	 * Infer type from initializer
	 */
	private inferTypeFromInitializer(initializer: ts.Expression, dataTypeMap?: Map<string, string>): string {
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
			case ts.SyntaxKind.BinaryExpression: {
				// Handle arithmetic operations: a * b, a + b, a - b, a / b
				const binaryExpr = initializer as ts.BinaryExpression;
				const leftType = this.inferTypeFromInitializer(binaryExpr.left, dataTypeMap);
				const rightType = this.inferTypeFromInitializer(binaryExpr.right, dataTypeMap);
				
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
				return 'unknown';
			}
			case ts.SyntaxKind.Identifier: {
				// Handle identifier references if in dataTypeMap
				if (dataTypeMap) {
					const name = (initializer as ts.Identifier).text;
					const type = dataTypeMap.get(name);
					if (type) {
						return type;
					}
				}
				return 'unknown';
			}
			case ts.SyntaxKind.CallExpression: {
				// Handle function calls like Date.now(), parseInt(), etc.
				const callExpr = initializer as ts.CallExpression;
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
		private collectUsage(node: ts.Node, sourceFile: ts.SourceFile): void {
			// Check for new Type() instantiation
			if (ts.isNewExpression(node) && node.expression) {
				const typeName = this.getTypeNameFromExpression(node.expression);
				if (typeName) {
					const { line, character } = ts.getLineAndCharacterOfPosition(
						sourceFile,
						node.getStart(sourceFile)
					);
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
					const { line, character } = ts.getLineAndCharacterOfPosition(
						sourceFile,
						node.getStart(sourceFile)
					);
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
		}
	
		/**
			* Add a usage to the collection
			*/
		private addUsage(typePath: string, usage: UsageInfo): void {
		// Only track usages of mnemonica-defined types
		if (!this.definitions.has(typePath)) {
			return;
		}
			if (!this.usages.has(typePath)) {
				this.usages.set(typePath, []);
			}
			this.usages.get(typePath)!.push(usage);
		}
	
		/**
			* Get type name from expression (identifier or property access)
			*/
		private getTypeNameFromExpression(expr: ts.Expression): string | undefined {
			if (ts.isIdentifier(expr)) {
				return expr.text;
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
		private resolveTypePath(expr: ts.PropertyAccessExpression): string | undefined {
			const chain = this.getPropertyChain(expr);
			if (chain.length === 0) return undefined;
	
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
		private isLikelyTypeName(name: string): boolean {
			return name[0] >= 'A' && name[0] <= 'Z';
		}
	}
