'use strict';

import * as path from 'path';
import * as ts from 'typescript';
import {
	ScopeAnalysis, ScopeInfo, ScopeKind, ScopeVariable, UsageInfo
} from './types';

/**
 * Compile-time view over the analyzer's definitions, used to attach mnemonica
 * type paths to variables. Name-based heuristics only — the no-getTypeChecker()
 * precedent stays.
 */
export interface ScopeTypeResolver {
	/** Resolve a bare constructor/type name to a mnemonica fullPath (undefined when unknown or ambiguous) */
	resolveByName(name: string): string | undefined;
	/** True when the dotted path is a known mnemonica type */
	hasPath(fullPath: string): boolean;
}

/**
 * Internal scope record: numeric span (1-based line/col) kept for
 * findHolderScopeId() containment matching; ScopeInfo itself carries strings.
 */
interface ScopeSpan {
	scopeId: string;
	startLine: number;
	startCol: number;
	endLine: number;
	endCol: number;
}

/**
 * Raw variable record collected during the AST walk. typePath is resolved
 * later in build(), once definitions are known.
 */
interface PendingVariable {
	variable: ScopeVariable;
	/** Bare constructor name for `new X(...)` initializers */
	newName?: string;
	/** Root identifier + property chain for `new a.b.C(...)` initializers */
	newChainRoot?: string;
	newChainRest?: string[];
	/** String-literal path of a `lookup('A.B')` initializer */
	lookupPath?: string;
	/** Root identifier of the receiver for `receiver.lookup('A.B')` / `lookup(source, 'A.B')` */
	lookupReceiver?: string;
	/** Raw type annotation text (e.g. 'UserEntity_UserResponse') */
	annotation?: string;
	/** Scope chain from declaration site outward, for chain-root lookup */
	scopeChain: string[];
}

const ASSIGNMENT_OPERATORS = new Set<ts.SyntaxKind>([
	ts.SyntaxKind.EqualsToken,
	ts.SyntaxKind.PlusEqualsToken,
	ts.SyntaxKind.MinusEqualsToken,
	ts.SyntaxKind.AsteriskEqualsToken,
	ts.SyntaxKind.AsteriskAsteriskEqualsToken,
	ts.SyntaxKind.SlashEqualsToken,
	ts.SyntaxKind.PercentEqualsToken,
	ts.SyntaxKind.LessThanLessThanEqualsToken,
	ts.SyntaxKind.GreaterThanGreaterThanEqualsToken,
	ts.SyntaxKind.GreaterThanGreaterThanGreaterThanEqualsToken,
	ts.SyntaxKind.AmpersandEqualsToken,
	ts.SyntaxKind.BarEqualsToken,
	ts.SyntaxKind.CaretEqualsToken,
	ts.SyntaxKind.AmpersandAmpersandEqualsToken,
	ts.SyntaxKind.BarBarEqualsToken,
	ts.SyntaxKind.QuestionQuestionEqualsToken,
]);

/**
 * Local-scope walker (instrumentation walker plan, Phase 2).
 *
 * Tracks function/method/arrow scopes ONLY (decision 5: no block scopes),
 * plus one synthetic 'module' scope per file — the plan requires module-scope
 * instance creations to be labeled, not dropped. Variables carry isMutable
 * (const vs let/var/parameter) and `reassignments`: each reassignment site of
 * a mutable binding is a flow-termination point (decision 6) — downstream the
 * walker stops following that binding there.
 *
 * Usage: addFile() per source file, then build(resolver) once definitions are
 * known. findHolderScopeId(location) maps a usage location string to the
 * innermost scope containing it (usages.json holderScopeId).
 */
export class LocalScopeWalker {
	private scopes = new Map<string, ScopeInfo>();
	private spans = new Map<string, ScopeSpan[]>();
	private variables = new Map<string, ScopeVariable>();
	private pending: PendingVariable[] = [];
	/**
	 * Arrow/function-expression node -> name it is bound to (`const f = () => …`,
	 * `{ handler: () => … }`, class properties). Program source files can be
	 * UNBOUND (no node.parent pointers), so binding names travel through this
	 * map instead of parent lookups.
	 */
	private boundNames = new Map<ts.Node, string>();

	/**
	 * Track one source file. Re-adding the same file replaces its records,
	 * so a walker may safely be reused across passes.
	 */
	addFile (sourceFile: ts.SourceFile): void {
		const filePath = path.resolve(sourceFile.fileName);
		this.dropFile(filePath);

		const moduleScope: ScopeInfo = {
			scopeId  : filePath,
			name     : filePath,
			kind     : 'module',
			filePath,
			location : `${filePath}:1:1`,
		};
		this.scopes.set(moduleScope.scopeId, moduleScope);

		const spans: ScopeSpan[] = [];
		this.spans.set(filePath, spans);
		spans.push(this.spanOf(sourceFile, sourceFile, moduleScope.scopeId));

		const scopeStack: string[] = [ moduleScope.scopeId ];
		const classStack: string[] = [];
		this.visitNode(sourceFile, sourceFile, filePath, scopeStack, classStack, spans);
	}

	/**
	 * Resolve pending typePaths and return the analysis.
	 */
	build (resolver?: ScopeTypeResolver): ScopeAnalysis {
		if (resolver) {
			for (const entry of this.pending) {
				const typePath = this.resolveVariableTypePath(entry, resolver);
				if (typePath) {
					entry.variable.typePath = typePath;
				}
			}
		}

		const analysis: ScopeAnalysis = {
			scopes    : this.scopes,
			variables : this.variables,
		};
		return analysis;
	}

	/**
	 * Map a usage location string ('abs/file.ts:line:col') to the innermost
	 * scope containing it. Module scope is the fallback, so every location
	 * inside a tracked file resolves to some scope.
	 */
	findHolderScopeId (location: string): string | undefined {
		const lastColon = location.lastIndexOf(':');
		const prevColon = location.lastIndexOf(':', lastColon - 1);
		if (lastColon < 0 || prevColon < 0) {
			return undefined;
		}
		const filePath = path.resolve(location.slice(0, prevColon));
		const line = Number(location.slice(prevColon + 1, lastColon));
		const col = Number(location.slice(lastColon + 1));
		if (!Number.isFinite(line) || !Number.isFinite(col)) {
			return undefined;
		}

		const spans = this.spans.get(filePath);
		if (!spans) {
			return undefined;
		}

		let best: ScopeSpan | undefined;
		for (const span of spans) {
			const startsBefore = span.startLine < line || (span.startLine === line && span.startCol <= col);
			const endsAfter = span.endLine > line || (span.endLine === line && span.endCol >= col);
			if (!startsBefore || !endsAfter) {
				continue;
			}
			// Innermost = smallest containing span
			if (best && (best.startLine < span.startLine ||
				(best.startLine === span.startLine && best.startCol <= span.startCol))) {
				best = span;
				continue;
			}
			if (!best) {
				best = span;
			}
		}
		const result = best?.scopeId;
		return result;
	}

	/**
	 * Remove every record belonging to one file (re-add support).
	 */
	private dropFile (filePath: string): void {
		for (const [ scopeId, scope ] of this.scopes) {
			if (scope.filePath === filePath) {
				this.scopes.delete(scopeId);
			}
		}
		for (const key of Array.from(this.variables.keys())) {
			if (key.startsWith(`${filePath}#`) || key.startsWith(`${filePath}:`)) {
				this.variables.delete(key);
			}
		}
		this.pending = this.pending.filter(entry =>
			!entry.variable.declaration.startsWith(`${filePath}:`));
		this.spans.delete(filePath);
	}

	/**
	 * Attach holderScopeId to every usage whose location falls inside a
	 * tracked scope. Additive on UsageInfo; usages outside tracked files
	 * are left untouched.
	 */
	static attachHolderScopeIds (usages: Map<string, UsageInfo[]>, walker: LocalScopeWalker): void {
		for (const usageList of usages.values()) {
			for (const usage of usageList) {
				const scopeId = walker.findHolderScopeId(usage.location);
				if (scopeId) {
					usage.holderScopeId = scopeId;
				}
			}
		}
	}

	private visitNode (
		node: ts.Node,
		sourceFile: ts.SourceFile,
		filePath: string,
		scopeStack: string[],
		classStack: string[],
		spans: ScopeSpan[]
	): void {
		const scopeKind = LocalScopeWalker.scopeKindOf(node);
		let entered = false;
		if (scopeKind && this.hasBody(node)) {
			this.enterScope(node, scopeKind, sourceFile, filePath, scopeStack, classStack, spans);
			entered = true;
		}

		const isClass = ts.isClassDeclaration(node) || ts.isClassExpression(node);
		if (isClass) {
			classStack.push(node.name?.text ?? '');
		}

		this.collectBoundName(node);
		this.collectVariableDeclarationList(node, sourceFile, scopeStack);
		this.collectReassignment(node, sourceFile, scopeStack);

		ts.forEachChild(node, child => {
			this.visitNode(child, sourceFile, filePath, scopeStack, classStack, spans);
		});

		if (isClass) {
			classStack.pop();
		}
		if (entered) {
			scopeStack.pop();
		}
	}

	private static scopeKindOf (node: ts.Node): ScopeKind | undefined {
		if (ts.isMethodDeclaration(node) || ts.isGetAccessorDeclaration(node) ||
			ts.isSetAccessorDeclaration(node) || ts.isConstructorDeclaration(node)) {
			return 'method';
		}
		if (ts.isFunctionDeclaration(node) || ts.isFunctionExpression(node)) {
			return 'function';
		}
		if (ts.isArrowFunction(node)) {
			return 'arrow';
		}
		return undefined;
	}

	private hasBody (node: ts.Node): boolean {
		const bodyHolder = node as ts.FunctionLikeDeclaration;
		const result = bodyHolder.body !== undefined;
		return result;
	}

	private enterScope (
		node: ts.Node,
		kind: ScopeKind,
		sourceFile: ts.SourceFile,
		filePath: string,
		scopeStack: string[],
		classStack: string[],
		spans: ScopeSpan[]
	): void {
		const { line, character } = sourceFile.getLineAndCharacterOfPosition(node.getStart(sourceFile));
		const scopeId = `${filePath}:${line + 1}:${character + 1}`;
		const parentScopeId = scopeStack[ scopeStack.length - 1 ];

		const scope: ScopeInfo = {
			scopeId,
			name     : this.scopeName(node, kind, filePath, line + 1, classStack),
			kind,
			parentScopeId,
			filePath,
			location : scopeId,
		};
		this.scopes.set(scopeId, scope);
		spans.push(this.spanOf(node, sourceFile, scopeId));
		scopeStack.push(scopeId);

		// Parameters are variables of the scope; they are reassignable, so
		// isMutable: true — a parameter reassignment terminates the flow too
		const fn = node as ts.FunctionLikeDeclaration;
		for (const param of fn.parameters ?? []) {
			if (!ts.isIdentifier(param.name)) {
				// Skip destructured parameters (analyzer precedent)
				continue;
			}
			this.recordVariable(param.name.text, param.name, sourceFile, scopeStack, {
				isParameter : true,
				// `this` parameters (mnemonica handlers) are never reassignable
				isMutable   : param.name.text !== 'this',
				annotation  : param.type?.getText(sourceFile),
			});
		}
	}

	/**
	 * Decision 8 labeling: functions by name; methods as Class.method;
	 * arrows/functions bound to a variable or property take that name;
	 * anonymous holders are labeled file:line.
	 */
	private scopeName (
		node: ts.Node,
		kind: ScopeKind,
		filePath: string,
		line: number,
		classStack: string[]
	): string {
		const named = node as ts.NamedDeclaration;
		if (kind === 'method') {
			const methodName = named.name ? named.name.getText() : 'anonymous';
			const className = classStack[ classStack.length - 1 ];
			const ctor = ts.isConstructorDeclaration(node) ? 'constructor' : methodName;
			const methodScopeName = className ? `${className}.${ctor}` : ctor;
			return methodScopeName;
		}
		if (named.name && ts.isIdentifier(named.name)) {
			const declaredName = named.name.text;
			return declaredName;
		}
		// Bound names come from the boundNames map — program files may be
		// unbound, so node.parent is not a reliable path to the variable name
		const bound = this.boundNames.get(node);
		if (bound) {
			return bound;
		}
		const result = `${filePath}:${line}`;
		return result;
	}

	private spanOf (
		node: ts.Node,
		sourceFile: ts.SourceFile,
		scopeId: string
	): ScopeSpan {
		const start = sourceFile.getLineAndCharacterOfPosition(node.getStart(sourceFile));
		const end = sourceFile.getLineAndCharacterOfPosition(node.getEnd());
		const span: ScopeSpan = {
			scopeId,
			startLine : start.line + 1,
			startCol  : start.character + 1,
			endLine   : end.line + 1,
			endCol    : end.character + 1,
		};
		return span;
	}

	/**
	 * Record the name an arrow/function-expression is bound to, without
	 * relying on node.parent (unbound program files): `const f = () => …`,
	 * `{ handler: () => … }`, `class C { run = () => … }`.
	 */
	private collectBoundName (node: ts.Node): void {
		if (ts.isVariableDeclaration(node) && ts.isIdentifier(node.name) && node.initializer &&
			(ts.isArrowFunction(node.initializer) || ts.isFunctionExpression(node.initializer))) {
			this.boundNames.set(node.initializer, node.name.text);
			return;
		}
		if ((ts.isPropertyAssignment(node) || ts.isPropertyDeclaration(node)) &&
			ts.isIdentifier(node.name) && node.initializer &&
			(ts.isArrowFunction(node.initializer) || ts.isFunctionExpression(node.initializer))) {
			this.boundNames.set(node.initializer, node.name.text);
		}
	}

	private collectVariableDeclarationList (
		node: ts.Node,
		sourceFile: ts.SourceFile,
		scopeStack: string[]
	): void {
		if (!ts.isVariableDeclarationList(node)) {
			return;
		}
		// Flags live on the list itself — no parent walk needed (the list's
		// parent may be unset on unbound program files)
		const isConst = (node.flags & ts.NodeFlags.Const) !== 0;
		for (const decl of node.declarations) {
			// Destructuring declarations are skipped: only plain
			// `const/let/var x = …` has an identifier name
			if (!ts.isIdentifier(decl.name)) {
				continue;
			}
			this.recordVariable(decl.name.text, decl.name, sourceFile, scopeStack, {
				isParameter : false,
				isMutable   : !isConst,
				annotation  : decl.type?.getText(sourceFile),
				initializer : decl.initializer,
			});
		}
	}

	private recordVariable (
		name: string,
		node: ts.Node,
		sourceFile: ts.SourceFile,
		scopeStack: string[],
		options: {
			isParameter: boolean;
			isMutable: boolean;
			annotation?: string;
			initializer?: ts.Expression;
		}
	): void {
		const scopeId = scopeStack[ scopeStack.length - 1 ];
		const { line, character } = sourceFile.getLineAndCharacterOfPosition(node.getStart(sourceFile));
		const filePath = path.resolve(sourceFile.fileName);

		const variable: ScopeVariable = {
			name,
			scopeId,
			declaration   : `${filePath}:${line + 1}:${character + 1}`,
			isParameter   : options.isParameter,
			isMutable     : options.isMutable,
			reassignments : [],
		};
		const inferred = options.annotation ?? (
			options.initializer ? LocalScopeWalker.inferInitializerKind(options.initializer) : undefined
		);
		if (inferred) {
			variable.inferredType = inferred;
		}

		const pendingEntry: PendingVariable = {
			variable,
			scopeChain : [ ...scopeStack ].reverse(),
			annotation : options.annotation,
		};
		const { initializer } = options;
		if (initializer && ts.isNewExpression(initializer)) {
			const { expression } = initializer;
			if (ts.isIdentifier(expression)) {
				pendingEntry.newName = expression.text;
			} else if (ts.isPropertyAccessExpression(expression)) {
				const chain = LocalScopeWalker.unwrapPropertyAccess(expression);
				if (chain.length > 1) {
					const [ root, ...rest ] = chain;
					pendingEntry.newChainRoot = root;
					pendingEntry.newChainRest = rest;
				}
			}
		}
		if (initializer && ts.isCallExpression(initializer)) {
			const lookup = LocalScopeWalker.unwrapLookupCall(initializer);
			if (lookup) {
				pendingEntry.lookupPath = lookup.path;
				pendingEntry.lookupReceiver = lookup.receiver;
			}
		}
		this.pending.push(pendingEntry);
		this.variables.set(`${scopeId}#${name}`, variable);
	}

	/**
	 * `a.b.c` → ['a', 'b', 'c'] (left-to-right); undefined-safe for
	 * non-identifier roots.
	 */
	private static unwrapPropertyAccess (expression: ts.PropertyAccessExpression): string[] {
		const chain: string[] = [];
		let current: ts.Expression = expression;
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
	 * `lookup('A.B')`, `App.lookup('A.B')`, `lookup(source, 'A.B')` → the
	 * string-literal path plus the receiver's root identifier when there is
	 * one. Only literal paths are tracked: a computed path is data the static
	 * walker cannot follow, so it is skipped (the analyzer's usage pass still
	 * records the lookup call itself).
	 */
	private static unwrapLookupCall (call: ts.CallExpression): { path: string; receiver?: string } | undefined {
		const { expression } = call;
		const [ firstArg, secondArg ] = call.arguments;

		if (ts.isIdentifier(expression)) {
			if (expression.text !== 'lookup') {
				return undefined;
			}
			// lookup('A.B')
			if (firstArg && ts.isStringLiteralLike(firstArg)) {
				const result = { path : firstArg.text };
				return result;
			}
			// lookup(source, 'A.B') — explicit-source form
			if (firstArg && ts.isIdentifier(firstArg) && secondArg && ts.isStringLiteralLike(secondArg)) {
				const result = { path : secondArg.text, receiver : firstArg.text };
				return result;
			}
			return undefined;
		}

		if (ts.isPropertyAccessExpression(expression) && expression.name.text === 'lookup') {
			if (!firstArg || !ts.isStringLiteralLike(firstArg)) {
				return undefined;
			}
			const chain = LocalScopeWalker.unwrapPropertyAccess(expression);
			// chain < 2 means no identifier receiver (e.g. this.lookup('A.B'))
			if (chain.length < 2) {
				const pathOnly = { path : firstArg.text };
				return pathOnly;
			}
			const [ receiver ] = chain;
			const result = { path : firstArg.text, receiver };
			return result;
		}

		return undefined;
	}

	/**
	 * Cheap initializer classification for inferredType. Deliberately tiny:
	 * literal kinds and `new X` constructor names; everything else undefined.
	 */
	private static inferInitializerKind (initializer: ts.Expression): string | undefined {
		if (ts.isStringLiteralLike(initializer) || ts.isTemplateExpression(initializer)) {
			return 'string';
		}
		if (ts.isNumericLiteral(initializer)) {
			return 'number';
		}
		if (initializer.kind === ts.SyntaxKind.TrueKeyword || initializer.kind === ts.SyntaxKind.FalseKeyword) {
			return 'boolean';
		}
		if (ts.isArrowFunction(initializer) || ts.isFunctionExpression(initializer)) {
			return 'function';
		}
		if (ts.isArrayLiteralExpression(initializer)) {
			return 'Array<unknown>';
		}
		if (ts.isNewExpression(initializer) && ts.isIdentifier(initializer.expression)) {
			const result = initializer.expression.text;
			return result;
		}
		return undefined;
	}

	/**
	 * Reassignment of a let/var/parameter binding: a flow-termination point
	 * (decision 6). Recorded on the variable so the Phase 3 walker stops
	 * following that binding there.
	 */
	private collectReassignment (
		node: ts.Node,
		sourceFile: ts.SourceFile,
		scopeStack: string[]
	): void {
		let target: ts.Identifier | undefined;
		if (ts.isBinaryExpression(node) &&
			ASSIGNMENT_OPERATORS.has(node.operatorToken.kind) &&
			ts.isIdentifier(node.left)) {
			target = node.left;
		}
		if ((ts.isPrefixUnaryExpression(node) || ts.isPostfixUnaryExpression(node)) &&
			(node.operator === ts.SyntaxKind.PlusPlusToken || node.operator === ts.SyntaxKind.MinusMinusToken) &&
			ts.isIdentifier(node.operand)) {
			target = node.operand;
		}
		if (!target) {
			return;
		}
		// Note: a declaration initializer (`let x = 5`) is a VariableDeclaration,
		// never a BinaryExpression, so it cannot reach this path as a "reassignment"

		const variable = this.findVariable(target.text, scopeStack);
		if (!variable) {
			return;
		}
		const filePath = path.resolve(sourceFile.fileName);
		const { line, character } = sourceFile.getLineAndCharacterOfPosition(target.getStart(sourceFile));
		variable.reassignments.push(`${filePath}:${line + 1}:${character + 1}`);
	}

	/**
	 * Find a variable by name walking the scope chain outward.
	 */
	private findVariable (name: string, scopeStack: string[]): ScopeVariable | undefined {
		for (let i = scopeStack.length - 1; i >= 0; i--) {
			const variable = this.variables.get(`${scopeStack[ i ]}#${name}`);
			if (variable) {
				return variable;
			}
		}
		return undefined;
	}

	private resolveVariableTypePath (entry: PendingVariable, resolver: ScopeTypeResolver): string | undefined {
		// `new SomeType(...)` — bare constructor name
		if (entry.newName) {
			const resolved = resolver.resolveByName(entry.newName);
			if (resolved) {
				return resolved;
			}
		}

		// `new instance.Sub.Type(...)` — chain off a tracked variable's typePath
		if (entry.newChainRoot && entry.newChainRest && entry.newChainRest.length > 0) {
			for (const scopeId of entry.scopeChain) {
				const rootVariable = this.variables.get(`${scopeId}#${entry.newChainRoot}`);
				if (!rootVariable?.typePath) {
					continue;
				}
				const candidate = [ rootVariable.typePath, ...entry.newChainRest ].join('.');
				if (resolver.hasPath(candidate)) {
					return candidate;
				}
			}
		}

		// `lookup('A.B')` / `receiver.lookup('A.B')` initializers
		if (entry.lookupPath) {
			// Receiver-relative first: `user.lookup('AdminEntity')` resolves
			// against the receiver variable's typePath when that yields a
			// known path (mirrors the analyzer's relative-then-root rule)
			if (entry.lookupReceiver) {
				for (const scopeId of entry.scopeChain) {
					const receiverVariable = this.variables.get(`${scopeId}#${entry.lookupReceiver}`);
					if (!receiverVariable?.typePath) {
						continue;
					}
					const candidate = `${receiverVariable.typePath}.${entry.lookupPath}`;
					if (resolver.hasPath(candidate)) {
						return candidate;
					}
				}
			}
			if (resolver.hasPath(entry.lookupPath)) {
				return entry.lookupPath;
			}
			const byName = resolver.resolveByName(entry.lookupPath);
			if (byName) {
				return byName;
			}
		}

		// Type annotation: 'UserEntity_UserResponse' (tactica types.ts naming)
		// → dotted path, or a bare known type name
		if (entry.annotation) {
			const dotted = entry.annotation.replace(/_/g, '.');
			if (dotted.includes('.') && resolver.hasPath(dotted)) {
				return dotted;
			}
			const byName = resolver.resolveByName(entry.annotation);
			if (byName) {
				return byName;
			}
		}

		return undefined;
	}
}
