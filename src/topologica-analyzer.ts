'use strict';

import * as fs from 'fs';
import * as path from 'path';
import * as ts from 'typescript';
import { TypeNode, PropertyInfo, ConstructorParamInfo } from './types';
import { TypeGraphImpl } from './graph';

/**
 * Analyzer for Topologica directory-based type definitions
 * Scans directory structures to create type hierarchies like:
 * ai-types/Sentience/Consciousness/Empathy/Gratitude/
 * 
 * Now with AST-based property extraction from TypeScript/JavaScript files
 */
export class TopologicaAnalyzer {
	private errors: string[] = [];
	private graph = new TypeGraphImpl();

	/**
	 * Analyze a directory structure for topologica type definitions
	 */
	analyzeDirectory(directoryPath: string): { types: Map<string, TypeNode>, errors: string[] } {
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
	private scanDirectory(currentPath: string, parentNode: TypeNode | undefined, rootPath: string): void {
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
					const typeNode: TypeNode = {
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
					} else {
						// Add as root type
						this.graph.addRoot(typeNode);
					}
					
					// Scan children of this directory
					this.scanDirectory(dirPath, typeNode, rootPath);
				}
			}
		} catch (error) {
			this.errors.push(`Error scanning directory ${currentPath}: ${(error as Error).message}`);
		}
	}

	/**
	 * Extract properties from a directory's index file
	 * Supports both .ts and .js files
	 */
	private extractPropertiesFromDir(dirPath: string): {
		properties: Map<string, PropertyInfo>;
		constructorParams?: ConstructorParamInfo[];
		handlerLocation?: { filePath: string; line: number; column: number };
	} {
		const properties = new Map<string, PropertyInfo>();
		let constructorParams: ConstructorParamInfo[] | undefined;
		
		// Check for TypeScript file first, then JavaScript
		const tsFile = path.join(dirPath, 'index.ts');
		const jsFile = path.join(dirPath, 'index.js');
		
		let targetFile: string | undefined;
		
		if (fs.existsSync(tsFile)) {
			targetFile = tsFile;
		} else if (fs.existsSync(jsFile)) {
			targetFile = jsFile;
		}
		
		if (!targetFile) {
			return { properties };
		}
		
		// Default location points to the index file
		const handlerLocation = { filePath: targetFile, line: 1, column: 1 };
		
		try {
			const content = fs.readFileSync(targetFile, 'utf-8');
			const sourceFile = ts.createSourceFile(
				targetFile,
				content,
				ts.ScriptTarget.Latest,
				true
			);
			
			// Collect type aliases from the file (e.g., SentienceData = { ... })
			const typeAliases = this.collectTypeAliases(sourceFile);
			
			// Find handler function and extract property assignments and constructor params
			constructorParams = this.extractPropertiesFromSourceFile(sourceFile, properties, typeAliases);
			
		} catch (error) {
			this.errors.push(`Error parsing ${targetFile}: ${(error as Error).message}`);
		}
		
		return { properties, constructorParams, handlerLocation };
	}

	/**
	 * Collect type aliases from source file
	 * e.g., export type SentienceData = { awareness?: string; }
	 */
	private collectTypeAliases(sourceFile: ts.SourceFile): Map<string, ts.TypeNode> {
		const typeAliases = new Map<string, ts.TypeNode>();
		
		const visit = (node: ts.Node): void => {
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
	 * Returns constructor parameters if found
	 */
	private extractPropertiesFromSourceFile(
		sourceFile: ts.SourceFile,
		properties: Map<string, PropertyInfo>,
		typeAliases?: Map<string, ts.TypeNode>
	): ConstructorParamInfo[] | undefined {
		let constructorParams: ConstructorParamInfo[] | undefined;
		
		const visit = (node: ts.Node): void => {
			// Look for function declarations, function expressions, or arrow functions
			if (ts.isFunctionDeclaration(node) ||
			    ts.isFunctionExpression(node) ||
			    ts.isArrowFunction(node)) {
				this.extractThisProperties(node, properties);
				// Extract constructor params from the first function found
				if (!constructorParams) {
					constructorParams = this.extractConstructorParams(node, typeAliases);
				}
			}
			
			ts.forEachChild(node, visit);
		};
		
		visit(sourceFile);
		return constructorParams;
	}

	/**
	 * Extract `this.property = value` assignments from a function body
	 */
	private extractThisProperties(
		func: ts.FunctionDeclaration | ts.FunctionExpression | ts.ArrowFunction,
		properties: Map<string, PropertyInfo>
	): void {
		const body = func.body;
		if (!body) return;
		
		const visitStatements = (node: ts.Node): void => {
			// Handle expression statements
			if (ts.isExpressionStatement(node)) {
				const expr = node.expression;
				
				// Check for this.prop = value
				if (ts.isBinaryExpression(expr) && 
				    expr.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
					const left = expr.left;
					const right = expr.right;
					
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
	private isObjectAssignCall(callExpr: ts.CallExpression): boolean {
		const expr = callExpr.expression;
		if (!ts.isPropertyAccessExpression(expr)) return false;
		
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
	private extractFromObjectAssign(
		callExpr: ts.CallExpression,
		properties: Map<string, PropertyInfo>
	): void {
		// Look for the data argument (second argument)
		const dataArg = callExpr.arguments[1];
		if (!dataArg) return;
		
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
	private extractConstructorParams(
		func: ts.FunctionDeclaration | ts.FunctionExpression | ts.ArrowFunction,
		typeAliases?: Map<string, ts.TypeNode>
	): ConstructorParamInfo[] | undefined {
		if (!func.parameters || func.parameters.length === 0) {
			return undefined;
		}

		const params: ConstructorParamInfo[] = [];
		
		// Skip `this` parameter (first param) and extract data parameters
		for (let i = 0; i < func.parameters.length; i++) {
			const param = func.parameters[i];
			
			// Skip `this` parameter (first param)
			if (i === 0 && param.name.kind === ts.SyntaxKind.Identifier &&
			    (param.name as ts.Identifier).text === 'this') {
				continue;
			}
			
			if (!param.type) continue;
			
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
	private expandTypeToObject(
		typeNode: ts.TypeNode,
		typeAliases?: Map<string, ts.TypeNode>
	): string | undefined {
		// Direct inline type literal: { prop: type }
		if (ts.isTypeLiteralNode(typeNode)) {
			const props: string[] = [];
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
					if (expanded) return expanded;
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
	private typeNodeToSimpleString(typeNode: ts.TypeNode | undefined): string {
		if (!typeNode) return 'any';
		
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
				const typeRef = typeNode as ts.TypeReferenceNode;
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
	private inferType(node: ts.Expression): string {
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
				return this.inferNewExpressionType(node as ts.NewExpression);
			case ts.SyntaxKind.ConditionalExpression:
				return this.inferType((node as ts.ConditionalExpression).whenTrue);
			case ts.SyntaxKind.BinaryExpression: {
				const binExpr = node as ts.BinaryExpression;
				// Check for logical OR pattern: value || default
				if (binExpr.operatorToken.kind === ts.SyntaxKind.BarBarToken) {
					// Return the type of the right side (the default value)
					return this.inferType(binExpr.right);
				}
				return 'any';
			}
			case ts.SyntaxKind.PropertyAccessExpression: {
				const propAccess = node as ts.PropertyAccessExpression;
				// Handle data?.property patterns
				return this.inferType(propAccess);
			}
			case ts.SyntaxKind.CallExpression: {
				const callExpr = node as ts.CallExpression;
				return this.inferCallExpressionType(callExpr);
			}
			default:
				return 'any';
		}
	}

	/**
	 * Infer type from new expressions like new Date(), new Array(), etc.
	 */
	private inferNewExpressionType(node: ts.NewExpression): string {
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
	private inferCallExpressionType(node: ts.CallExpression): string {
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
	getGraph(): TypeGraphImpl {
		return this.graph;
	}

	/**
	 * Get collected errors
	 */
	getErrors(): string[] {
		return this.errors;
	}
}
