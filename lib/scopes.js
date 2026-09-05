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
exports.LocalScopeWalker = void 0;
const path = __importStar(require("path"));
const ts = __importStar(require("typescript"));
const ASSIGNMENT_OPERATORS = new Set([
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
class LocalScopeWalker {
    constructor() {
        this.scopes = new Map();
        this.spans = new Map();
        this.variables = new Map();
        this.pending = [];
        /**
         * Arrow/function-expression node -> name it is bound to (`const f = () => …`,
         * `{ handler: () => … }`, class properties). Program source files can be
         * UNBOUND (no node.parent pointers), so binding names travel through this
         * map instead of parent lookups.
         */
        this.boundNames = new Map();
    }
    /**
     * Track one source file. Re-adding the same file replaces its records,
     * so a walker may safely be reused across passes.
     */
    addFile(sourceFile) {
        const filePath = path.resolve(sourceFile.fileName);
        this.dropFile(filePath);
        const moduleScope = {
            scopeId: filePath,
            name: filePath,
            kind: 'module',
            filePath,
            location: `${filePath}:1:1`,
        };
        this.scopes.set(moduleScope.scopeId, moduleScope);
        const spans = [];
        this.spans.set(filePath, spans);
        spans.push(this.spanOf(sourceFile, sourceFile, moduleScope.scopeId));
        const scopeStack = [moduleScope.scopeId];
        const classStack = [];
        this.visitNode(sourceFile, sourceFile, filePath, scopeStack, classStack, spans);
    }
    /**
     * Resolve pending typePaths and return the analysis.
     */
    build(resolver) {
        if (resolver) {
            for (const entry of this.pending) {
                const typePath = this.resolveVariableTypePath(entry, resolver);
                if (typePath) {
                    entry.variable.typePath = typePath;
                }
            }
        }
        const analysis = {
            scopes: this.scopes,
            variables: this.variables,
        };
        return analysis;
    }
    /**
     * Map a usage location string ('abs/file.ts:line:col') to the innermost
     * scope containing it. Module scope is the fallback, so every location
     * inside a tracked file resolves to some scope.
     */
    findHolderScopeId(location) {
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
        let best;
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
    dropFile(filePath) {
        for (const [scopeId, scope] of this.scopes) {
            if (scope.filePath === filePath) {
                this.scopes.delete(scopeId);
            }
        }
        for (const key of Array.from(this.variables.keys())) {
            if (key.startsWith(`${filePath}#`) || key.startsWith(`${filePath}:`)) {
                this.variables.delete(key);
            }
        }
        this.pending = this.pending.filter(entry => !entry.variable.declaration.startsWith(`${filePath}:`));
        this.spans.delete(filePath);
    }
    /**
     * Attach holderScopeId to every usage whose location falls inside a
     * tracked scope. Additive on UsageInfo; usages outside tracked files
     * are left untouched.
     */
    static attachHolderScopeIds(usages, walker) {
        for (const usageList of usages.values()) {
            for (const usage of usageList) {
                const scopeId = walker.findHolderScopeId(usage.location);
                if (scopeId) {
                    usage.holderScopeId = scopeId;
                }
            }
        }
    }
    visitNode(node, sourceFile, filePath, scopeStack, classStack, spans) {
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
    static scopeKindOf(node) {
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
    hasBody(node) {
        const bodyHolder = node;
        const result = bodyHolder.body !== undefined;
        return result;
    }
    enterScope(node, kind, sourceFile, filePath, scopeStack, classStack, spans) {
        const { line, character } = sourceFile.getLineAndCharacterOfPosition(node.getStart(sourceFile));
        const scopeId = `${filePath}:${line + 1}:${character + 1}`;
        const parentScopeId = scopeStack[scopeStack.length - 1];
        const scope = {
            scopeId,
            name: this.scopeName(node, kind, filePath, line + 1, classStack),
            kind,
            parentScopeId,
            filePath,
            location: scopeId,
        };
        this.scopes.set(scopeId, scope);
        spans.push(this.spanOf(node, sourceFile, scopeId));
        scopeStack.push(scopeId);
        // Parameters are variables of the scope; they are reassignable, so
        // isMutable: true — a parameter reassignment terminates the flow too
        const fn = node;
        for (const param of fn.parameters ?? []) {
            if (!ts.isIdentifier(param.name)) {
                // Skip destructured parameters (analyzer precedent)
                continue;
            }
            this.recordVariable(param.name.text, param.name, sourceFile, scopeStack, {
                isParameter: true,
                // `this` parameters (mnemonica handlers) are never reassignable
                isMutable: param.name.text !== 'this',
                annotation: param.type?.getText(sourceFile),
            });
        }
    }
    /**
     * Decision 8 labeling: functions by name; methods as Class.method;
     * arrows/functions bound to a variable or property take that name;
     * anonymous holders are labeled file:line.
     */
    scopeName(node, kind, filePath, line, classStack) {
        const named = node;
        if (kind === 'method') {
            const methodName = named.name ? named.name.getText() : 'anonymous';
            const className = classStack[classStack.length - 1];
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
    spanOf(node, sourceFile, scopeId) {
        const start = sourceFile.getLineAndCharacterOfPosition(node.getStart(sourceFile));
        const end = sourceFile.getLineAndCharacterOfPosition(node.getEnd());
        const span = {
            scopeId,
            startLine: start.line + 1,
            startCol: start.character + 1,
            endLine: end.line + 1,
            endCol: end.character + 1,
        };
        return span;
    }
    /**
     * Record the name an arrow/function-expression is bound to, without
     * relying on node.parent (unbound program files): `const f = () => …`,
     * `{ handler: () => … }`, `class C { run = () => … }`.
     */
    collectBoundName(node) {
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
    collectVariableDeclarationList(node, sourceFile, scopeStack) {
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
                isParameter: false,
                isMutable: !isConst,
                annotation: decl.type?.getText(sourceFile),
                initializer: decl.initializer,
            });
        }
    }
    recordVariable(name, node, sourceFile, scopeStack, options) {
        const scopeId = scopeStack[scopeStack.length - 1];
        const { line, character } = sourceFile.getLineAndCharacterOfPosition(node.getStart(sourceFile));
        const filePath = path.resolve(sourceFile.fileName);
        const variable = {
            name,
            scopeId,
            declaration: `${filePath}:${line + 1}:${character + 1}`,
            isParameter: options.isParameter,
            isMutable: options.isMutable,
            reassignments: [],
        };
        const inferred = options.annotation ?? (options.initializer ? LocalScopeWalker.inferInitializerKind(options.initializer) : undefined);
        if (inferred) {
            variable.inferredType = inferred;
        }
        const pendingEntry = {
            variable,
            scopeChain: [...scopeStack].reverse(),
            annotation: options.annotation,
        };
        const { initializer } = options;
        if (initializer && ts.isNewExpression(initializer)) {
            const { expression } = initializer;
            if (ts.isIdentifier(expression)) {
                pendingEntry.newName = expression.text;
            }
            else if (ts.isPropertyAccessExpression(expression)) {
                const chain = LocalScopeWalker.unwrapPropertyAccess(expression);
                if (chain.length > 1) {
                    const [root, ...rest] = chain;
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
    static unwrapPropertyAccess(expression) {
        const chain = [];
        let current = expression;
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
    static unwrapLookupCall(call) {
        const { expression } = call;
        const [firstArg, secondArg] = call.arguments;
        if (ts.isIdentifier(expression)) {
            if (expression.text !== 'lookup') {
                return undefined;
            }
            // lookup('A.B')
            if (firstArg && ts.isStringLiteralLike(firstArg)) {
                const result = { path: firstArg.text };
                return result;
            }
            // lookup(source, 'A.B') — explicit-source form
            if (firstArg && ts.isIdentifier(firstArg) && secondArg && ts.isStringLiteralLike(secondArg)) {
                const result = { path: secondArg.text, receiver: firstArg.text };
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
                const pathOnly = { path: firstArg.text };
                return pathOnly;
            }
            const [receiver] = chain;
            const result = { path: firstArg.text, receiver };
            return result;
        }
        return undefined;
    }
    /**
     * Cheap initializer classification for inferredType. Deliberately tiny:
     * literal kinds and `new X` constructor names; everything else undefined.
     */
    static inferInitializerKind(initializer) {
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
    collectReassignment(node, sourceFile, scopeStack) {
        let target;
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
    findVariable(name, scopeStack) {
        for (let i = scopeStack.length - 1; i >= 0; i--) {
            const variable = this.variables.get(`${scopeStack[i]}#${name}`);
            if (variable) {
                return variable;
            }
        }
        return undefined;
    }
    resolveVariableTypePath(entry, resolver) {
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
                const candidate = [rootVariable.typePath, ...entry.newChainRest].join('.');
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
exports.LocalScopeWalker = LocalScopeWalker;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoic2NvcGVzLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL3Njb3Blcy50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQSxZQUFZLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQUViLDJDQUE2QjtBQUM3QiwrQ0FBaUM7QUFrRGpDLE1BQU0sb0JBQW9CLEdBQUcsSUFBSSxHQUFHLENBQWdCO0lBQ25ELEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVztJQUN6QixFQUFFLENBQUMsVUFBVSxDQUFDLGVBQWU7SUFDN0IsRUFBRSxDQUFDLFVBQVUsQ0FBQyxnQkFBZ0I7SUFDOUIsRUFBRSxDQUFDLFVBQVUsQ0FBQyxtQkFBbUI7SUFDakMsRUFBRSxDQUFDLFVBQVUsQ0FBQywyQkFBMkI7SUFDekMsRUFBRSxDQUFDLFVBQVUsQ0FBQyxnQkFBZ0I7SUFDOUIsRUFBRSxDQUFDLFVBQVUsQ0FBQyxrQkFBa0I7SUFDaEMsRUFBRSxDQUFDLFVBQVUsQ0FBQywyQkFBMkI7SUFDekMsRUFBRSxDQUFDLFVBQVUsQ0FBQyxpQ0FBaUM7SUFDL0MsRUFBRSxDQUFDLFVBQVUsQ0FBQyw0Q0FBNEM7SUFDMUQsRUFBRSxDQUFDLFVBQVUsQ0FBQyxvQkFBb0I7SUFDbEMsRUFBRSxDQUFDLFVBQVUsQ0FBQyxjQUFjO0lBQzVCLEVBQUUsQ0FBQyxVQUFVLENBQUMsZ0JBQWdCO0lBQzlCLEVBQUUsQ0FBQyxVQUFVLENBQUMsNkJBQTZCO0lBQzNDLEVBQUUsQ0FBQyxVQUFVLENBQUMsaUJBQWlCO0lBQy9CLEVBQUUsQ0FBQyxVQUFVLENBQUMsMkJBQTJCO0NBQ3pDLENBQUMsQ0FBQztBQUVIOzs7Ozs7Ozs7Ozs7O0dBYUc7QUFDSCxNQUFhLGdCQUFnQjtJQUE3QjtRQUNTLFdBQU0sR0FBRyxJQUFJLEdBQUcsRUFBcUIsQ0FBQztRQUN0QyxVQUFLLEdBQUcsSUFBSSxHQUFHLEVBQXVCLENBQUM7UUFDdkMsY0FBUyxHQUFHLElBQUksR0FBRyxF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QUFDO0NBQ0Q7QUFubEJELDRDQW1sQkMiLCJzb3VyY2VzQ29udGVudCI6WyIndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIHBhdGggZnJvbSAncGF0aCc7XG5pbXBvcnQgKiBhcyB0cyBmcm9tICd0eXBlc2NyaXB0JztcbmltcG9ydCB7XG5cdFNjb3BlQW5hbHlzaXMsIFNjb3BlSW5mbywgU2NvcGVLaW5kLCBTY29wZVZhcmlhYmxlLCBVc2FnZUluZm9cbn0gZnJvbSAnLi90eXBlcyc7XG5cbi8qKlxuICogQ29tcGlsZS10aW1lIHZpZXcgb3ZlciB0aGUgYW5hbHl6ZXIncyBkZWZpbml0aW9ucywgdXNlZCB0byBhdHRhY2ggbW5lbW9uaWNhXG4gKiB0eXBlIHBhdGhzIHRvIHZhcmlhYmxlcy4gTmFtZS1iYXNlZCBoZXVyaXN0aWNzIG9ubHkg4oCUIHRoZSBuby1nZXRUeXBlQ2hlY2tlcigpXG4gKiBwcmVjZWRlbnQgc3RheXMuXG4gKi9cbmV4cG9ydCBpbnRlcmZhY2UgU2NvcGVUeXBlUmVzb2x2ZXIge1xuXHQvKiogUmVzb2x2ZSBhIGJhcmUgY29uc3RydWN0b3IvdHlwZSBuYW1lIHRvIGEgbW5lbW9uaWNhIGZ1bGxQYXRoICh1bmRlZmluZWQgd2hlbiB1bmtub3duIG9yIGFtYmlndW91cykgKi9cblx0cmVzb2x2ZUJ5TmFtZShuYW1lOiBzdHJpbmcpOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdC8qKiBUcnVlIHdoZW4gdGhlIGRvdHRlZCBwYXRoIGlzIGEga25vd24gbW5lbW9uaWNhIHR5cGUgKi9cblx0aGFzUGF0aChmdWxsUGF0aDogc3RyaW5nKTogYm9vbGVhbjtcbn1cblxuLyoqXG4gKiBJbnRlcm5hbCBzY29wZSByZWNvcmQ6IG51bWVyaWMgc3BhbiAoMS1iYXNlZCBsaW5lL2NvbCkga2VwdCBmb3JcbiAqIGZpbmRIb2xkZXJTY29wZUlkKCkgY29udGFpbm1lbnQgbWF0Y2hpbmc7IFNjb3BlSW5mbyBpdHNlbGYgY2FycmllcyBzdHJpbmdzLlxuICovXG5pbnRlcmZhY2UgU2NvcGVTcGFuIHtcblx0c2NvcGVJZDogc3RyaW5nO1xuXHRzdGFydExpbmU6IG51bWJlcjtcblx0c3RhcnRDb2w6IG51bWJlcjtcblx0ZW5kTGluZTogbnVtYmVyO1xuXHRlbmRDb2w6IG51bWJlcjtcbn1cblxuLyoqXG4gKiBSYXcgdmFyaWFibGUgcmVjb3JkIGNvbGxlY3RlZCBkdXJpbmcgdGhlIEFTVCB3YWxrLiB0eXBlUGF0aCBpcyByZXNvbHZlZFxuICogbGF0ZXIgaW4gYnVpbGQoKSwgb25jZSBkZWZpbml0aW9ucyBhcmUga25vd24uXG4gKi9cbmludGVyZmFjZSBQZW5kaW5nVmFyaWFibGUge1xuXHR2YXJpYWJsZTogU2NvcGVWYXJpYWJsZTtcblx0LyoqIEJhcmUgY29uc3RydWN0b3IgbmFtZSBmb3IgYG5ldyBYKC4uLilgIGluaXRpYWxpemVycyAqL1xuXHRuZXdOYW1lPzogc3RyaW5nO1xuXHQvKiogUm9vdCBpZGVudGlmaWVyICsgcHJvcGVydHkgY2hhaW4gZm9yIGBuZXcgYS5iLkMoLi4uKWAgaW5pdGlhbGl6ZXJzICovXG5cdG5ld0NoYWluUm9vdD86IHN0cmluZztcblx0bmV3Q2hhaW5SZXN0Pzogc3RyaW5nW107XG5cdC8qKiBTdHJpbmctbGl0ZXJhbCBwYXRoIG9mIGEgYGxvb2t1cCgnQS5CJylgIGluaXRpYWxpemVyICovXG5cdGxvb2t1cFBhdGg/OiBzdHJpbmc7XG5cdC8qKiBSb290IGlkZW50aWZpZXIgb2YgdGhlIHJlY2VpdmVyIGZvciBgcmVjZWl2ZXIubG9va3VwKCdBLkInKWAgLyBgbG9va3VwKHNvdXJjZSwgJ0EuQicpYCAqL1xuXHRsb29rdXBSZWNlaXZlcj86IHN0cmluZztcblx0LyoqIFJhdyB0eXBlIGFubm90YXRpb24gdGV4dCAoZS5nLiAnVXNlckVudGl0eV9Vc2VyUmVzcG9uc2UnKSAqL1xuXHRhbm5vdGF0aW9uPzogc3RyaW5nO1xuXHQvKiogU2NvcGUgY2hhaW4gZnJvbSBkZWNsYXJhdGlvbiBzaXRlIG91dHdhcmQsIGZvciBjaGFpbi1yb290IGxvb2t1cCAqL1xuXHRzY29wZUNoYWluOiBzdHJpbmdbXTtcbn1cblxuY29uc3QgQVNTSUdOTUVOVF9PUEVSQVRPUlMgPSBuZXcgU2V0PHRzLlN5bnRheEtpbmQ+KFtcblx0dHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbixcblx0dHMuU3ludGF4S2luZC5QbHVzRXF1YWxzVG9rZW4sXG5cdHRzLlN5bnRheEtpbmQuTWludXNFcXVhbHNUb2tlbixcblx0dHMuU3ludGF4S2luZC5Bc3Rlcmlza0VxdWFsc1Rva2VuLFxuXHR0cy5TeW50YXhLaW5kLkFzdGVyaXNrQXN0ZXJpc2tFcXVhbHNUb2tlbixcblx0dHMuU3ludGF4S2luZC5TbGFzaEVxdWFsc1Rva2VuLFxuXHR0cy5TeW50YXhLaW5kLlBlcmNlbnRFcXVhbHNUb2tlbixcblx0dHMuU3ludGF4S2luZC5MZXNzVGhhbkxlc3NUaGFuRXF1YWxzVG9rZW4sXG5cdHRzLlN5bnRheEtpbmQuR3JlYXRlclRoYW5HcmVhdGVyVGhhbkVxdWFsc1Rva2VuLFxuXHR0cy5TeW50YXhLaW5kLkdyZWF0ZXJUaGFuR3JlYXRlclRoYW5HcmVhdGVyVGhhbkVxdWFsc1Rva2VuLFxuXHR0cy5TeW50YXhLaW5kLkFtcGVyc2FuZEVxdWFsc1Rva2VuLFxuXHR0cy5TeW50YXhLaW5kLkJhckVxdWFsc1Rva2VuLFxuXHR0cy5TeW50YXhLaW5kLkNhcmV0RXF1YWxzVG9rZW4sXG5cdHRzLlN5bnRheEtpbmQuQW1wZXJzYW5kQW1wZXJzYW5kRXF1YWxzVG9rZW4sXG5cdHRzLlN5bnRheEtpbmQuQmFyQmFyRXF1YWxzVG9rZW4sXG5cdHRzLlN5bnRheEtpbmQuUXVlc3Rpb25RdWVzdGlvbkVxdWFsc1Rva2VuLFxuXSk7XG5cbi8qKlxuICogTG9jYWwtc2NvcGUgd2Fsa2VyIChpbnN0cnVtZW50YXRpb24gd2Fsa2VyIHBsYW4sIFBoYXNlIDIpLlxuICpcbiAqIFRyYWNrcyBmdW5jdGlvbi9tZXRob2QvYXJyb3cgc2NvcGVzIE9OTFkgKGRlY2lzaW9uIDU6IG5vIGJsb2NrIHNjb3BlcyksXG4gKiBwbHVzIG9uZSBzeW50aGV0aWMgJ21vZHVsZScgc2NvcGUgcGVyIGZpbGUg4oCUIHRoZSBwbGFuIHJlcXVpcmVzIG1vZHVsZS1zY29wZVxuICogaW5zdGFuY2UgY3JlYXRpb25zIHRvIGJlIGxhYmVsZWQsIG5vdCBkcm9wcGVkLiBWYXJpYWJsZXMgY2FycnkgaXNNdXRhYmxlXG4gKiAoY29uc3QgdnMgbGV0L3Zhci9wYXJhbWV0ZXIpIGFuZCBgcmVhc3NpZ25tZW50c2A6IGVhY2ggcmVhc3NpZ25tZW50IHNpdGUgb2ZcbiAqIGEgbXV0YWJsZSBiaW5kaW5nIGlzIGEgZmxvdy10ZXJtaW5hdGlvbiBwb2ludCAoZGVjaXNpb24gNikg4oCUIGRvd25zdHJlYW0gdGhlXG4gKiB3YWxrZXIgc3RvcHMgZm9sbG93aW5nIHRoYXQgYmluZGluZyB0aGVyZS5cbiAqXG4gKiBVc2FnZTogYWRkRmlsZSgpIHBlciBzb3VyY2UgZmlsZSwgdGhlbiBidWlsZChyZXNvbHZlcikgb25jZSBkZWZpbml0aW9ucyBhcmVcbiAqIGtub3duLiBmaW5kSG9sZGVyU2NvcGVJZChsb2NhdGlvbikgbWFwcyBhIHVzYWdlIGxvY2F0aW9uIHN0cmluZyB0byB0aGVcbiAqIGlubmVybW9zdCBzY29wZSBjb250YWluaW5nIGl0ICh1c2FnZXMuanNvbiBob2xkZXJTY29wZUlkKS5cbiAqL1xuZXhwb3J0IGNsYXNzIExvY2FsU2NvcGVXYWxrZXIge1xuXHRwcml2YXRlIHNjb3BlcyA9IG5ldyBNYXA8c3RyaW5nLCBTY29wZUluZm8+KCk7XG5cdHByaXZhdGUgc3BhbnMgPSBuZXcgTWFwPHN0cmluZywgU2NvcGVTcGFuW10+KCk7XG5cdHByaXZhdGUgdmFyaWFibGVzID0gbmV3IE1hcDxzdHJpbmcsIFNjb3BlVmFyaWFibGU+KCk7XG5cdHByaXZhdGUgcGVuZGluZzogUGVuZGluZ1ZhcmlhYmxlW10gPSBbXTtcblx0LyoqXG5cdCAqIEFycm93L2Z1bmN0aW9uLWV4cHJlc3Npb24gbm9kZSAtPiBuYW1lIGl0IGlzIGJvdW5kIHRvIChgY29uc3QgZiA9ICgpID0+IOKApmAsXG5cdCAqIGB7IGhhbmRsZXI6ICgpID0+IOKApiB9YCwgY2xhc3MgcHJvcGVydGllcykuIFByb2dyYW0gc291cmNlIGZpbGVzIGNhbiBiZVxuXHQgKiBVTkJPVU5EIChubyBub2RlLnBhcmVudCBwb2ludGVycyksIHNvIGJpbmRpbmcgbmFtZXMgdHJhdmVsIHRocm91Z2ggdGhpc1xuXHQgKiBtYXAgaW5zdGVhZCBvZiBwYXJlbnQgbG9va3Vwcy5cblx0ICovXG5cdHByaXZhdGUgYm91bmROYW1lcyA9IG5ldyBNYXA8dHMuTm9kZSwgc3RyaW5nPigpO1xuXG5cdC8qKlxuXHQgKiBUcmFjayBvbmUgc291cmNlIGZpbGUuIFJlLWFkZGluZyB0aGUgc2FtZSBmaWxlIHJlcGxhY2VzIGl0cyByZWNvcmRzLFxuXHQgKiBzbyBhIHdhbGtlciBtYXkgc2FmZWx5IGJlIHJldXNlZCBhY3Jvc3MgcGFzc2VzLlxuXHQgKi9cblx0YWRkRmlsZSAoc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5yZXNvbHZlKHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXHRcdHRoaXMuZHJvcEZpbGUoZmlsZVBhdGgpO1xuXG5cdFx0Y29uc3QgbW9kdWxlU2NvcGU6IFNjb3BlSW5mbyA9IHtcblx0XHRcdHNjb3BlSWQgIDogZmlsZVBhdGgsXG5cdFx0XHRuYW1lICAgICA6IGZpbGVQYXRoLFxuXHRcdFx0a2luZCAgICAgOiAnbW9kdWxlJyxcblx0XHRcdGZpbGVQYXRoLFxuXHRcdFx0bG9jYXRpb24gOiBgJHtmaWxlUGF0aH06MToxYCxcblx0XHR9O1xuXHRcdHRoaXMuc2NvcGVzLnNldChtb2R1bGVTY29wZS5zY29wZUlkLCBtb2R1bGVTY29wZSk7XG5cblx0XHRjb25zdCBzcGFuczogU2NvcGVTcGFuW10gPSBbXTtcblx0XHR0aGlzLnNwYW5zLnNldChmaWxlUGF0aCwgc3BhbnMpO1xuXHRcdHNwYW5zLnB1c2godGhpcy5zcGFuT2Yoc291cmNlRmlsZSwgc291cmNlRmlsZSwgbW9kdWxlU2NvcGUuc2NvcGVJZCkpO1xuXG5cdFx0Y29uc3Qgc2NvcGVTdGFjazogc3RyaW5nW10gPSBbIG1vZHVsZVNjb3BlLnNjb3BlSWQgXTtcblx0XHRjb25zdCBjbGFzc1N0YWNrOiBzdHJpbmdbXSA9IFtdO1xuXHRcdHRoaXMudmlzaXROb2RlKHNvdXJjZUZpbGUsIHNvdXJjZUZpbGUsIGZpbGVQYXRoLCBzY29wZVN0YWNrLCBjbGFzc1N0YWNrLCBzcGFucyk7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBwZW5kaW5nIHR5cGVQYXRocyBhbmQgcmV0dXJuIHRoZSBhbmFseXNpcy5cblx0ICovXG5cdGJ1aWxkIChyZXNvbHZlcj86IFNjb3BlVHlwZVJlc29sdmVyKTogU2NvcGVBbmFseXNpcyB7XG5cdFx0aWYgKHJlc29sdmVyKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGVudHJ5IG9mIHRoaXMucGVuZGluZykge1xuXHRcdFx0XHRjb25zdCB0eXBlUGF0aCA9IHRoaXMucmVzb2x2ZVZhcmlhYmxlVHlwZVBhdGgoZW50cnksIHJlc29sdmVyKTtcblx0XHRcdFx0aWYgKHR5cGVQYXRoKSB7XG5cdFx0XHRcdFx0ZW50cnkudmFyaWFibGUudHlwZVBhdGggPSB0eXBlUGF0aDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGNvbnN0IGFuYWx5c2lzOiBTY29wZUFuYWx5c2lzID0ge1xuXHRcdFx0c2NvcGVzICAgIDogdGhpcy5zY29wZXMsXG5cdFx0XHR2YXJpYWJsZXMgOiB0aGlzLnZhcmlhYmxlcyxcblx0XHR9O1xuXHRcdHJldHVybiBhbmFseXNpcztcblx0fVxuXG5cdC8qKlxuXHQgKiBNYXAgYSB1c2FnZSBsb2NhdGlvbiBzdHJpbmcgKCdhYnMvZmlsZS50czpsaW5lOmNvbCcpIHRvIHRoZSBpbm5lcm1vc3Rcblx0ICogc2NvcGUgY29udGFpbmluZyBpdC4gTW9kdWxlIHNjb3BlIGlzIHRoZSBmYWxsYmFjaywgc28gZXZlcnkgbG9jYXRpb25cblx0ICogaW5zaWRlIGEgdHJhY2tlZCBmaWxlIHJlc29sdmVzIHRvIHNvbWUgc2NvcGUuXG5cdCAqL1xuXHRmaW5kSG9sZGVyU2NvcGVJZCAobG9jYXRpb246IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgbGFzdENvbG9uID0gbG9jYXRpb24ubGFzdEluZGV4T2YoJzonKTtcblx0XHRjb25zdCBwcmV2Q29sb24gPSBsb2NhdGlvbi5sYXN0SW5kZXhPZignOicsIGxhc3RDb2xvbiAtIDEpO1xuXHRcdGlmIChsYXN0Q29sb24gPCAwIHx8IHByZXZDb2xvbiA8IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5yZXNvbHZlKGxvY2F0aW9uLnNsaWNlKDAsIHByZXZDb2xvbikpO1xuXHRcdGNvbnN0IGxpbmUgPSBOdW1iZXIobG9jYXRpb24uc2xpY2UocHJldkNvbG9uICsgMSwgbGFzdENvbG9uKSk7XG5cdFx0Y29uc3QgY29sID0gTnVtYmVyKGxvY2F0aW9uLnNsaWNlKGxhc3RDb2xvbiArIDEpKTtcblx0XHRpZiAoIU51bWJlci5pc0Zpbml0ZShsaW5lKSB8fCAhTnVtYmVyLmlzRmluaXRlKGNvbCkpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3BhbnMgPSB0aGlzLnNwYW5zLmdldChmaWxlUGF0aCk7XG5cdFx0aWYgKCFzcGFucykge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRsZXQgYmVzdDogU2NvcGVTcGFuIHwgdW5kZWZpbmVkO1xuXHRcdGZvciAoY29uc3Qgc3BhbiBvZiBzcGFucykge1xuXHRcdFx0Y29uc3Qgc3RhcnRzQmVmb3JlID0gc3Bhbi5zdGFydExpbmUgPCBsaW5lIHx8IChzcGFuLnN0YXJ0TGluZSA9PT0gbGluZSAmJiBzcGFuLnN0YXJ0Q29sIDw9IGNvbCk7XG5cdFx0XHRjb25zdCBlbmRzQWZ0ZXIgPSBzcGFuLmVuZExpbmUgPiBsaW5lIHx8IChzcGFuLmVuZExpbmUgPT09IGxpbmUgJiYgc3Bhbi5lbmRDb2wgPj0gY29sKTtcblx0XHRcdGlmICghc3RhcnRzQmVmb3JlIHx8ICFlbmRzQWZ0ZXIpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHQvLyBJbm5lcm1vc3QgPSBzbWFsbGVzdCBjb250YWluaW5nIHNwYW5cblx0XHRcdGlmIChiZXN0ICYmIChiZXN0LnN0YXJ0TGluZSA8IHNwYW4uc3RhcnRMaW5lIHx8XG5cdFx0XHRcdChiZXN0LnN0YXJ0TGluZSA9PT0gc3Bhbi5zdGFydExpbmUgJiYgYmVzdC5zdGFydENvbCA8PSBzcGFuLnN0YXJ0Q29sKSkpIHtcblx0XHRcdFx0YmVzdCA9IHNwYW47XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0aWYgKCFiZXN0KSB7XG5cdFx0XHRcdGJlc3QgPSBzcGFuO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBiZXN0Py5zY29wZUlkO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVtb3ZlIGV2ZXJ5IHJlY29yZCBiZWxvbmdpbmcgdG8gb25lIGZpbGUgKHJlLWFkZCBzdXBwb3J0KS5cblx0ICovXG5cdHByaXZhdGUgZHJvcEZpbGUgKGZpbGVQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHRmb3IgKGNvbnN0IFsgc2NvcGVJZCwgc2NvcGUgXSBvZiB0aGlzLnNjb3Blcykge1xuXHRcdFx0aWYgKHNjb3BlLmZpbGVQYXRoID09PSBmaWxlUGF0aCkge1xuXHRcdFx0XHR0aGlzLnNjb3Blcy5kZWxldGUoc2NvcGVJZCk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGZvciAoY29uc3Qga2V5IG9mIEFycmF5LmZyb20odGhpcy52YXJpYWJsZXMua2V5cygpKSkge1xuXHRcdFx0aWYgKGtleS5zdGFydHNXaXRoKGAke2ZpbGVQYXRofSNgKSB8fCBrZXkuc3RhcnRzV2l0aChgJHtmaWxlUGF0aH06YCkpIHtcblx0XHRcdFx0dGhpcy52YXJpYWJsZXMuZGVsZXRlKGtleSk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHRoaXMucGVuZGluZyA9IHRoaXMucGVuZGluZy5maWx0ZXIoZW50cnkgPT5cblx0XHRcdCFlbnRyeS52YXJpYWJsZS5kZWNsYXJhdGlvbi5zdGFydHNXaXRoKGAke2ZpbGVQYXRofTpgKSk7XG5cdFx0dGhpcy5zcGFucy5kZWxldGUoZmlsZVBhdGgpO1xuXHR9XG5cblx0LyoqXG5cdCAqIEF0dGFjaCBob2xkZXJTY29wZUlkIHRvIGV2ZXJ5IHVzYWdlIHdob3NlIGxvY2F0aW9uIGZhbGxzIGluc2lkZSBhXG5cdCAqIHRyYWNrZWQgc2NvcGUuIEFkZGl0aXZlIG9uIFVzYWdlSW5mbzsgdXNhZ2VzIG91dHNpZGUgdHJhY2tlZCBmaWxlc1xuXHQgKiBhcmUgbGVmdCB1bnRvdWNoZWQuXG5cdCAqL1xuXHRzdGF0aWMgYXR0YWNoSG9sZGVyU2NvcGVJZHMgKHVzYWdlczogTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+LCB3YWxrZXI6IExvY2FsU2NvcGVXYWxrZXIpOiB2b2lkIHtcblx0XHRmb3IgKGNvbnN0IHVzYWdlTGlzdCBvZiB1c2FnZXMudmFsdWVzKCkpIHtcblx0XHRcdGZvciAoY29uc3QgdXNhZ2Ugb2YgdXNhZ2VMaXN0KSB7XG5cdFx0XHRcdGNvbnN0IHNjb3BlSWQgPSB3YWxrZXIuZmluZEhvbGRlclNjb3BlSWQodXNhZ2UubG9jYXRpb24pO1xuXHRcdFx0XHRpZiAoc2NvcGVJZCkge1xuXHRcdFx0XHRcdHVzYWdlLmhvbGRlclNjb3BlSWQgPSBzY29wZUlkO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0cHJpdmF0ZSB2aXNpdE5vZGUgKFxuXHRcdG5vZGU6IHRzLk5vZGUsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRmaWxlUGF0aDogc3RyaW5nLFxuXHRcdHNjb3BlU3RhY2s6IHN0cmluZ1tdLFxuXHRcdGNsYXNzU3RhY2s6IHN0cmluZ1tdLFxuXHRcdHNwYW5zOiBTY29wZVNwYW5bXVxuXHQpOiB2b2lkIHtcblx0XHRjb25zdCBzY29wZUtpbmQgPSBMb2NhbFNjb3BlV2Fsa2VyLnNjb3BlS2luZE9mKG5vZGUpO1xuXHRcdGxldCBlbnRlcmVkID0gZmFsc2U7XG5cdFx0aWYgKHNjb3BlS2luZCAmJiB0aGlzLmhhc0JvZHkobm9kZSkpIHtcblx0XHRcdHRoaXMuZW50ZXJTY29wZShub2RlLCBzY29wZUtpbmQsIHNvdXJjZUZpbGUsIGZpbGVQYXRoLCBzY29wZVN0YWNrLCBjbGFzc1N0YWNrLCBzcGFucyk7XG5cdFx0XHRlbnRlcmVkID0gdHJ1ZTtcblx0XHR9XG5cblx0XHRjb25zdCBpc0NsYXNzID0gdHMuaXNDbGFzc0RlY2xhcmF0aW9uKG5vZGUpIHx8IHRzLmlzQ2xhc3NFeHByZXNzaW9uKG5vZGUpO1xuXHRcdGlmIChpc0NsYXNzKSB7XG5cdFx0XHRjbGFzc1N0YWNrLnB1c2gobm9kZS5uYW1lPy50ZXh0ID8/ICcnKTtcblx0XHR9XG5cblx0XHR0aGlzLmNvbGxlY3RCb3VuZE5hbWUobm9kZSk7XG5cdFx0dGhpcy5jb2xsZWN0VmFyaWFibGVEZWNsYXJhdGlvbkxpc3Qobm9kZSwgc291cmNlRmlsZSwgc2NvcGVTdGFjayk7XG5cdFx0dGhpcy5jb2xsZWN0UmVhc3NpZ25tZW50KG5vZGUsIHNvdXJjZUZpbGUsIHNjb3BlU3RhY2spO1xuXG5cdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHtcblx0XHRcdHRoaXMudmlzaXROb2RlKGNoaWxkLCBzb3VyY2VGaWxlLCBmaWxlUGF0aCwgc2NvcGVTdGFjaywgY2xhc3NTdGFjaywgc3BhbnMpO1xuXHRcdH0pO1xuXG5cdFx0aWYgKGlzQ2xhc3MpIHtcblx0XHRcdGNsYXNzU3RhY2sucG9wKCk7XG5cdFx0fVxuXHRcdGlmIChlbnRlcmVkKSB7XG5cdFx0XHRzY29wZVN0YWNrLnBvcCgpO1xuXHRcdH1cblx0fVxuXG5cdHByaXZhdGUgc3RhdGljIHNjb3BlS2luZE9mIChub2RlOiB0cy5Ob2RlKTogU2NvcGVLaW5kIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNNZXRob2REZWNsYXJhdGlvbihub2RlKSB8fCB0cy5pc0dldEFjY2Vzc29yRGVjbGFyYXRpb24obm9kZSkgfHxcblx0XHRcdHRzLmlzU2V0QWNjZXNzb3JEZWNsYXJhdGlvbihub2RlKSB8fCB0cy5pc0NvbnN0cnVjdG9yRGVjbGFyYXRpb24obm9kZSkpIHtcblx0XHRcdHJldHVybiAnbWV0aG9kJztcblx0XHR9XG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihub2RlKSB8fCB0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuICdmdW5jdGlvbic7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0Fycm93RnVuY3Rpb24obm9kZSkpIHtcblx0XHRcdHJldHVybiAnYXJyb3cnO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0cHJpdmF0ZSBoYXNCb2R5IChub2RlOiB0cy5Ob2RlKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgYm9keUhvbGRlciA9IG5vZGUgYXMgdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb247XG5cdFx0Y29uc3QgcmVzdWx0ID0gYm9keUhvbGRlci5ib2R5ICE9PSB1bmRlZmluZWQ7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdHByaXZhdGUgZW50ZXJTY29wZSAoXG5cdFx0bm9kZTogdHMuTm9kZSxcblx0XHRraW5kOiBTY29wZUtpbmQsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRmaWxlUGF0aDogc3RyaW5nLFxuXHRcdHNjb3BlU3RhY2s6IHN0cmluZ1tdLFxuXHRcdGNsYXNzU3RhY2s6IHN0cmluZ1tdLFxuXHRcdHNwYW5zOiBTY29wZVNwYW5bXVxuXHQpOiB2b2lkIHtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gc291cmNlRmlsZS5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpKTtcblx0XHRjb25zdCBzY29wZUlkID0gYCR7ZmlsZVBhdGh9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IHBhcmVudFNjb3BlSWQgPSBzY29wZVN0YWNrWyBzY29wZVN0YWNrLmxlbmd0aCAtIDEgXTtcblxuXHRcdGNvbnN0IHNjb3BlOiBTY29wZUluZm8gPSB7XG5cdFx0XHRzY29wZUlkLFxuXHRcdFx0bmFtZSAgICAgOiB0aGlzLnNjb3BlTmFtZShub2RlLCBraW5kLCBmaWxlUGF0aCwgbGluZSArIDEsIGNsYXNzU3RhY2spLFxuXHRcdFx0a2luZCxcblx0XHRcdHBhcmVudFNjb3BlSWQsXG5cdFx0XHRmaWxlUGF0aCxcblx0XHRcdGxvY2F0aW9uIDogc2NvcGVJZCxcblx0XHR9O1xuXHRcdHRoaXMuc2NvcGVzLnNldChzY29wZUlkLCBzY29wZSk7XG5cdFx0c3BhbnMucHVzaCh0aGlzLnNwYW5PZihub2RlLCBzb3VyY2VGaWxlLCBzY29wZUlkKSk7XG5cdFx0c2NvcGVTdGFjay5wdXNoKHNjb3BlSWQpO1xuXG5cdFx0Ly8gUGFyYW1ldGVycyBhcmUgdmFyaWFibGVzIG9mIHRoZSBzY29wZTsgdGhleSBhcmUgcmVhc3NpZ25hYmxlLCBzb1xuXHRcdC8vIGlzTXV0YWJsZTogdHJ1ZSDigJQgYSBwYXJhbWV0ZXIgcmVhc3NpZ25tZW50IHRlcm1pbmF0ZXMgdGhlIGZsb3cgdG9vXG5cdFx0Y29uc3QgZm4gPSBub2RlIGFzIHRzLkZ1bmN0aW9uTGlrZURlY2xhcmF0aW9uO1xuXHRcdGZvciAoY29uc3QgcGFyYW0gb2YgZm4ucGFyYW1ldGVycyA/PyBbXSkge1xuXHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkpIHtcblx0XHRcdFx0Ly8gU2tpcCBkZXN0cnVjdHVyZWQgcGFyYW1ldGVycyAoYW5hbHl6ZXIgcHJlY2VkZW50KVxuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdHRoaXMucmVjb3JkVmFyaWFibGUocGFyYW0ubmFtZS50ZXh0LCBwYXJhbS5uYW1lLCBzb3VyY2VGaWxlLCBzY29wZVN0YWNrLCB7XG5cdFx0XHRcdGlzUGFyYW1ldGVyIDogdHJ1ZSxcblx0XHRcdFx0Ly8gYHRoaXNgIHBhcmFtZXRlcnMgKG1uZW1vbmljYSBoYW5kbGVycykgYXJlIG5ldmVyIHJlYXNzaWduYWJsZVxuXHRcdFx0XHRpc011dGFibGUgICA6IHBhcmFtLm5hbWUudGV4dCAhPT0gJ3RoaXMnLFxuXHRcdFx0XHRhbm5vdGF0aW9uICA6IHBhcmFtLnR5cGU/LmdldFRleHQoc291cmNlRmlsZSksXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRGVjaXNpb24gOCBsYWJlbGluZzogZnVuY3Rpb25zIGJ5IG5hbWU7IG1ldGhvZHMgYXMgQ2xhc3MubWV0aG9kO1xuXHQgKiBhcnJvd3MvZnVuY3Rpb25zIGJvdW5kIHRvIGEgdmFyaWFibGUgb3IgcHJvcGVydHkgdGFrZSB0aGF0IG5hbWU7XG5cdCAqIGFub255bW91cyBob2xkZXJzIGFyZSBsYWJlbGVkIGZpbGU6bGluZS5cblx0ICovXG5cdHByaXZhdGUgc2NvcGVOYW1lIChcblx0XHRub2RlOiB0cy5Ob2RlLFxuXHRcdGtpbmQ6IFNjb3BlS2luZCxcblx0XHRmaWxlUGF0aDogc3RyaW5nLFxuXHRcdGxpbmU6IG51bWJlcixcblx0XHRjbGFzc1N0YWNrOiBzdHJpbmdbXVxuXHQpOiBzdHJpbmcge1xuXHRcdGNvbnN0IG5hbWVkID0gbm9kZSBhcyB0cy5OYW1lZERlY2xhcmF0aW9uO1xuXHRcdGlmIChraW5kID09PSAnbWV0aG9kJykge1xuXHRcdFx0Y29uc3QgbWV0aG9kTmFtZSA9IG5hbWVkLm5hbWUgPyBuYW1lZC5uYW1lLmdldFRleHQoKSA6ICdhbm9ueW1vdXMnO1xuXHRcdFx0Y29uc3QgY2xhc3NOYW1lID0gY2xhc3NTdGFja1sgY2xhc3NTdGFjay5sZW5ndGggLSAxIF07XG5cdFx0XHRjb25zdCBjdG9yID0gdHMuaXNDb25zdHJ1Y3RvckRlY2xhcmF0aW9uKG5vZGUpID8gJ2NvbnN0cnVjdG9yJyA6IG1ldGhvZE5hbWU7XG5cdFx0XHRjb25zdCBtZXRob2RTY29wZU5hbWUgPSBjbGFzc05hbWUgPyBgJHtjbGFzc05hbWV9LiR7Y3Rvcn1gIDogY3Rvcjtcblx0XHRcdHJldHVybiBtZXRob2RTY29wZU5hbWU7XG5cdFx0fVxuXHRcdGlmIChuYW1lZC5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihuYW1lZC5uYW1lKSkge1xuXHRcdFx0Y29uc3QgZGVjbGFyZWROYW1lID0gbmFtZWQubmFtZS50ZXh0O1xuXHRcdFx0cmV0dXJuIGRlY2xhcmVkTmFtZTtcblx0XHR9XG5cdFx0Ly8gQm91bmQgbmFtZXMgY29tZSBmcm9tIHRoZSBib3VuZE5hbWVzIG1hcCDigJQgcHJvZ3JhbSBmaWxlcyBtYXkgYmVcblx0XHQvLyB1bmJvdW5kLCBzbyBub2RlLnBhcmVudCBpcyBub3QgYSByZWxpYWJsZSBwYXRoIHRvIHRoZSB2YXJpYWJsZSBuYW1lXG5cdFx0Y29uc3QgYm91bmQgPSB0aGlzLmJvdW5kTmFtZXMuZ2V0KG5vZGUpO1xuXHRcdGlmIChib3VuZCkge1xuXHRcdFx0cmV0dXJuIGJvdW5kO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBgJHtmaWxlUGF0aH06JHtsaW5lfWA7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdHByaXZhdGUgc3Bhbk9mIChcblx0XHRub2RlOiB0cy5Ob2RlLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0c2NvcGVJZDogc3RyaW5nXG5cdCk6IFNjb3BlU3BhbiB7XG5cdFx0Y29uc3Qgc3RhcnQgPSBzb3VyY2VGaWxlLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSkpO1xuXHRcdGNvbnN0IGVuZCA9IHNvdXJjZUZpbGUuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24obm9kZS5nZXRFbmQoKSk7XG5cdFx0Y29uc3Qgc3BhbjogU2NvcGVTcGFuID0ge1xuXHRcdFx0c2NvcGVJZCxcblx0XHRcdHN0YXJ0TGluZSA6IHN0YXJ0LmxpbmUgKyAxLFxuXHRcdFx0c3RhcnRDb2wgIDogc3RhcnQuY2hhcmFjdGVyICsgMSxcblx0XHRcdGVuZExpbmUgICA6IGVuZC5saW5lICsgMSxcblx0XHRcdGVuZENvbCAgICA6IGVuZC5jaGFyYWN0ZXIgKyAxLFxuXHRcdH07XG5cdFx0cmV0dXJuIHNwYW47XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIHRoZSBuYW1lIGFuIGFycm93L2Z1bmN0aW9uLWV4cHJlc3Npb24gaXMgYm91bmQgdG8sIHdpdGhvdXRcblx0ICogcmVseWluZyBvbiBub2RlLnBhcmVudCAodW5ib3VuZCBwcm9ncmFtIGZpbGVzKTogYGNvbnN0IGYgPSAoKSA9PiDigKZgLFxuXHQgKiBgeyBoYW5kbGVyOiAoKSA9PiDigKYgfWAsIGBjbGFzcyBDIHsgcnVuID0gKCkgPT4g4oCmIH1gLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Qm91bmROYW1lIChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSAmJiBub2RlLmluaXRpYWxpemVyICYmXG5cdFx0XHQodHMuaXNBcnJvd0Z1bmN0aW9uKG5vZGUuaW5pdGlhbGl6ZXIpIHx8IHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKG5vZGUuaW5pdGlhbGl6ZXIpKSkge1xuXHRcdFx0dGhpcy5ib3VuZE5hbWVzLnNldChub2RlLmluaXRpYWxpemVyLCBub2RlLm5hbWUudGV4dCk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGlmICgodHMuaXNQcm9wZXJ0eUFzc2lnbm1lbnQobm9kZSkgfHwgdHMuaXNQcm9wZXJ0eURlY2xhcmF0aW9uKG5vZGUpKSAmJlxuXHRcdFx0dHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkgJiYgbm9kZS5pbml0aWFsaXplciAmJlxuXHRcdFx0KHRzLmlzQXJyb3dGdW5jdGlvbihub2RlLmluaXRpYWxpemVyKSB8fCB0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihub2RlLmluaXRpYWxpemVyKSkpIHtcblx0XHRcdHRoaXMuYm91bmROYW1lcy5zZXQobm9kZS5pbml0aWFsaXplciwgbm9kZS5uYW1lLnRleHQpO1xuXHRcdH1cblx0fVxuXG5cdHByaXZhdGUgY29sbGVjdFZhcmlhYmxlRGVjbGFyYXRpb25MaXN0IChcblx0XHRub2RlOiB0cy5Ob2RlLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0c2NvcGVTdGFjazogc3RyaW5nW11cblx0KTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb25MaXN0KG5vZGUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdC8vIEZsYWdzIGxpdmUgb24gdGhlIGxpc3QgaXRzZWxmIOKAlCBubyBwYXJlbnQgd2FsayBuZWVkZWQgKHRoZSBsaXN0J3Ncblx0XHQvLyBwYXJlbnQgbWF5IGJlIHVuc2V0IG9uIHVuYm91bmQgcHJvZ3JhbSBmaWxlcylcblx0XHRjb25zdCBpc0NvbnN0ID0gKG5vZGUuZmxhZ3MgJiB0cy5Ob2RlRmxhZ3MuQ29uc3QpICE9PSAwO1xuXHRcdGZvciAoY29uc3QgZGVjbCBvZiBub2RlLmRlY2xhcmF0aW9ucykge1xuXHRcdFx0Ly8gRGVzdHJ1Y3R1cmluZyBkZWNsYXJhdGlvbnMgYXJlIHNraXBwZWQ6IG9ubHkgcGxhaW5cblx0XHRcdC8vIGBjb25zdC9sZXQvdmFyIHggPSDigKZgIGhhcyBhbiBpZGVudGlmaWVyIG5hbWVcblx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGRlY2wubmFtZSkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHR0aGlzLnJlY29yZFZhcmlhYmxlKGRlY2wubmFtZS50ZXh0LCBkZWNsLm5hbWUsIHNvdXJjZUZpbGUsIHNjb3BlU3RhY2ssIHtcblx0XHRcdFx0aXNQYXJhbWV0ZXIgOiBmYWxzZSxcblx0XHRcdFx0aXNNdXRhYmxlICAgOiAhaXNDb25zdCxcblx0XHRcdFx0YW5ub3RhdGlvbiAgOiBkZWNsLnR5cGU/LmdldFRleHQoc291cmNlRmlsZSksXG5cdFx0XHRcdGluaXRpYWxpemVyIDogZGVjbC5pbml0aWFsaXplcixcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdHByaXZhdGUgcmVjb3JkVmFyaWFibGUgKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRub2RlOiB0cy5Ob2RlLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0c2NvcGVTdGFjazogc3RyaW5nW10sXG5cdFx0b3B0aW9uczoge1xuXHRcdFx0aXNQYXJhbWV0ZXI6IGJvb2xlYW47XG5cdFx0XHRpc011dGFibGU6IGJvb2xlYW47XG5cdFx0XHRhbm5vdGF0aW9uPzogc3RyaW5nO1xuXHRcdFx0aW5pdGlhbGl6ZXI/OiB0cy5FeHByZXNzaW9uO1xuXHRcdH1cblx0KTogdm9pZCB7XG5cdFx0Y29uc3Qgc2NvcGVJZCA9IHNjb3BlU3RhY2tbIHNjb3BlU3RhY2subGVuZ3RoIC0gMSBdO1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSBzb3VyY2VGaWxlLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSkpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5yZXNvbHZlKHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXG5cdFx0Y29uc3QgdmFyaWFibGU6IFNjb3BlVmFyaWFibGUgPSB7XG5cdFx0XHRuYW1lLFxuXHRcdFx0c2NvcGVJZCxcblx0XHRcdGRlY2xhcmF0aW9uICAgOiBgJHtmaWxlUGF0aH06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRpc1BhcmFtZXRlciAgIDogb3B0aW9ucy5pc1BhcmFtZXRlcixcblx0XHRcdGlzTXV0YWJsZSAgICAgOiBvcHRpb25zLmlzTXV0YWJsZSxcblx0XHRcdHJlYXNzaWdubWVudHMgOiBbXSxcblx0XHR9O1xuXHRcdGNvbnN0IGluZmVycmVkID0gb3B0aW9ucy5hbm5vdGF0aW9uID8/IChcblx0XHRcdG9wdGlvbnMuaW5pdGlhbGl6ZXIgPyBMb2NhbFNjb3BlV2Fsa2VyLmluZmVySW5pdGlhbGl6ZXJLaW5kKG9wdGlvbnMuaW5pdGlhbGl6ZXIpIDogdW5kZWZpbmVkXG5cdFx0KTtcblx0XHRpZiAoaW5mZXJyZWQpIHtcblx0XHRcdHZhcmlhYmxlLmluZmVycmVkVHlwZSA9IGluZmVycmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IHBlbmRpbmdFbnRyeTogUGVuZGluZ1ZhcmlhYmxlID0ge1xuXHRcdFx0dmFyaWFibGUsXG5cdFx0XHRzY29wZUNoYWluIDogWyAuLi5zY29wZVN0YWNrIF0ucmV2ZXJzZSgpLFxuXHRcdFx0YW5ub3RhdGlvbiA6IG9wdGlvbnMuYW5ub3RhdGlvbixcblx0XHR9O1xuXHRcdGNvbnN0IHsgaW5pdGlhbGl6ZXIgfSA9IG9wdGlvbnM7XG5cdFx0aWYgKGluaXRpYWxpemVyICYmIHRzLmlzTmV3RXhwcmVzc2lvbihpbml0aWFsaXplcikpIHtcblx0XHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gaW5pdGlhbGl6ZXI7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdHBlbmRpbmdFbnRyeS5uZXdOYW1lID0gZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0fSBlbHNlIGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBjaGFpbiA9IExvY2FsU2NvcGVXYWxrZXIudW53cmFwUHJvcGVydHlBY2Nlc3MoZXhwcmVzc2lvbik7XG5cdFx0XHRcdGlmIChjaGFpbi5sZW5ndGggPiAxKSB7XG5cdFx0XHRcdFx0Y29uc3QgWyByb290LCAuLi5yZXN0IF0gPSBjaGFpbjtcblx0XHRcdFx0XHRwZW5kaW5nRW50cnkubmV3Q2hhaW5Sb290ID0gcm9vdDtcblx0XHRcdFx0XHRwZW5kaW5nRW50cnkubmV3Q2hhaW5SZXN0ID0gcmVzdDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAoaW5pdGlhbGl6ZXIgJiYgdHMuaXNDYWxsRXhwcmVzc2lvbihpbml0aWFsaXplcikpIHtcblx0XHRcdGNvbnN0IGxvb2t1cCA9IExvY2FsU2NvcGVXYWxrZXIudW53cmFwTG9va3VwQ2FsbChpbml0aWFsaXplcik7XG5cdFx0XHRpZiAobG9va3VwKSB7XG5cdFx0XHRcdHBlbmRpbmdFbnRyeS5sb29rdXBQYXRoID0gbG9va3VwLnBhdGg7XG5cdFx0XHRcdHBlbmRpbmdFbnRyeS5sb29rdXBSZWNlaXZlciA9IGxvb2t1cC5yZWNlaXZlcjtcblx0XHRcdH1cblx0XHR9XG5cdFx0dGhpcy5wZW5kaW5nLnB1c2gocGVuZGluZ0VudHJ5KTtcblx0XHR0aGlzLnZhcmlhYmxlcy5zZXQoYCR7c2NvcGVJZH0jJHtuYW1lfWAsIHZhcmlhYmxlKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBgYS5iLmNgIOKGkiBbJ2EnLCAnYicsICdjJ10gKGxlZnQtdG8tcmlnaHQpOyB1bmRlZmluZWQtc2FmZSBmb3Jcblx0ICogbm9uLWlkZW50aWZpZXIgcm9vdHMuXG5cdCAqL1xuXHRwcml2YXRlIHN0YXRpYyB1bndyYXBQcm9wZXJ0eUFjY2VzcyAoZXhwcmVzc2lvbjogdHMuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKTogc3RyaW5nW10ge1xuXHRcdGNvbnN0IGNoYWluOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGxldCBjdXJyZW50OiB0cy5FeHByZXNzaW9uID0gZXhwcmVzc2lvbjtcblx0XHR3aGlsZSAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY3VycmVudCkpIHtcblx0XHRcdGNoYWluLnVuc2hpZnQoY3VycmVudC5uYW1lLnRleHQpO1xuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50KSkge1xuXHRcdFx0Y2hhaW4udW5zaGlmdChjdXJyZW50LnRleHQpO1xuXHRcdH1cblx0XHRyZXR1cm4gY2hhaW47XG5cdH1cblxuXHQvKipcblx0ICogYGxvb2t1cCgnQS5CJylgLCBgQXBwLmxvb2t1cCgnQS5CJylgLCBgbG9va3VwKHNvdXJjZSwgJ0EuQicpYCDihpIgdGhlXG5cdCAqIHN0cmluZy1saXRlcmFsIHBhdGggcGx1cyB0aGUgcmVjZWl2ZXIncyByb290IGlkZW50aWZpZXIgd2hlbiB0aGVyZSBpc1xuXHQgKiBvbmUuIE9ubHkgbGl0ZXJhbCBwYXRocyBhcmUgdHJhY2tlZDogYSBjb21wdXRlZCBwYXRoIGlzIGRhdGEgdGhlIHN0YXRpY1xuXHQgKiB3YWxrZXIgY2Fubm90IGZvbGxvdywgc28gaXQgaXMgc2tpcHBlZCAodGhlIGFuYWx5emVyJ3MgdXNhZ2UgcGFzcyBzdGlsbFxuXHQgKiByZWNvcmRzIHRoZSBsb29rdXAgY2FsbCBpdHNlbGYpLlxuXHQgKi9cblx0cHJpdmF0ZSBzdGF0aWMgdW53cmFwTG9va3VwQ2FsbCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7IHBhdGg6IHN0cmluZzsgcmVjZWl2ZXI/OiBzdHJpbmcgfSB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBjYWxsO1xuXHRcdGNvbnN0IFsgZmlyc3RBcmcsIHNlY29uZEFyZyBdID0gY2FsbC5hcmd1bWVudHM7XG5cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRpZiAoZXhwcmVzc2lvbi50ZXh0ICE9PSAnbG9va3VwJykge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Ly8gbG9va3VwKCdBLkInKVxuXHRcdFx0aWYgKGZpcnN0QXJnICYmIHRzLmlzU3RyaW5nTGl0ZXJhbExpa2UoZmlyc3RBcmcpKSB7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdCA9IHsgcGF0aCA6IGZpcnN0QXJnLnRleHQgfTtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHRcdC8vIGxvb2t1cChzb3VyY2UsICdBLkInKSDigJQgZXhwbGljaXQtc291cmNlIGZvcm1cblx0XHRcdGlmIChmaXJzdEFyZyAmJiB0cy5pc0lkZW50aWZpZXIoZmlyc3RBcmcpICYmIHNlY29uZEFyZyAmJiB0cy5pc1N0cmluZ0xpdGVyYWxMaWtlKHNlY29uZEFyZykpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0ID0geyBwYXRoIDogc2Vjb25kQXJnLnRleHQsIHJlY2VpdmVyIDogZmlyc3RBcmcudGV4dCB9O1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi5uYW1lLnRleHQgPT09ICdsb29rdXAnKSB7XG5cdFx0XHRpZiAoIWZpcnN0QXJnIHx8ICF0cy5pc1N0cmluZ0xpdGVyYWxMaWtlKGZpcnN0QXJnKSkge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgY2hhaW4gPSBMb2NhbFNjb3BlV2Fsa2VyLnVud3JhcFByb3BlcnR5QWNjZXNzKGV4cHJlc3Npb24pO1xuXHRcdFx0Ly8gY2hhaW4gPCAyIG1lYW5zIG5vIGlkZW50aWZpZXIgcmVjZWl2ZXIgKGUuZy4gdGhpcy5sb29rdXAoJ0EuQicpKVxuXHRcdFx0aWYgKGNoYWluLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0Y29uc3QgcGF0aE9ubHkgPSB7IHBhdGggOiBmaXJzdEFyZy50ZXh0IH07XG5cdFx0XHRcdHJldHVybiBwYXRoT25seTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IFsgcmVjZWl2ZXIgXSA9IGNoYWluO1xuXHRcdFx0Y29uc3QgcmVzdWx0ID0geyBwYXRoIDogZmlyc3RBcmcudGV4dCwgcmVjZWl2ZXIgfTtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVhcCBpbml0aWFsaXplciBjbGFzc2lmaWNhdGlvbiBmb3IgaW5mZXJyZWRUeXBlLiBEZWxpYmVyYXRlbHkgdGlueTpcblx0ICogbGl0ZXJhbCBraW5kcyBhbmQgYG5ldyBYYCBjb25zdHJ1Y3RvciBuYW1lczsgZXZlcnl0aGluZyBlbHNlIHVuZGVmaW5lZC5cblx0ICovXG5cdHByaXZhdGUgc3RhdGljIGluZmVySW5pdGlhbGl6ZXJLaW5kIChpbml0aWFsaXplcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbExpa2UoaW5pdGlhbGl6ZXIpIHx8IHRzLmlzVGVtcGxhdGVFeHByZXNzaW9uKGluaXRpYWxpemVyKSkge1xuXHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdH1cblx0XHRpZiAodHMuaXNOdW1lcmljTGl0ZXJhbChpbml0aWFsaXplcikpIHtcblx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHR9XG5cdFx0aWYgKGluaXRpYWxpemVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVHJ1ZUtleXdvcmQgfHwgaW5pdGlhbGl6ZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQpIHtcblx0XHRcdHJldHVybiAnYm9vbGVhbic7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0Fycm93RnVuY3Rpb24oaW5pdGlhbGl6ZXIpIHx8IHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGluaXRpYWxpemVyKSkge1xuXHRcdFx0cmV0dXJuICdmdW5jdGlvbic7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0FycmF5TGl0ZXJhbEV4cHJlc3Npb24oaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRyZXR1cm4gJ0FycmF5PHVua25vd24+Jztcblx0XHR9XG5cdFx0aWYgKHRzLmlzTmV3RXhwcmVzc2lvbihpbml0aWFsaXplcikgJiYgdHMuaXNJZGVudGlmaWVyKGluaXRpYWxpemVyLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSBpbml0aWFsaXplci5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlYXNzaWdubWVudCBvZiBhIGxldC92YXIvcGFyYW1ldGVyIGJpbmRpbmc6IGEgZmxvdy10ZXJtaW5hdGlvbiBwb2ludFxuXHQgKiAoZGVjaXNpb24gNikuIFJlY29yZGVkIG9uIHRoZSB2YXJpYWJsZSBzbyB0aGUgUGhhc2UgMyB3YWxrZXIgc3RvcHNcblx0ICogZm9sbG93aW5nIHRoYXQgYmluZGluZyB0aGVyZS5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdFJlYXNzaWdubWVudCAoXG5cdFx0bm9kZTogdHMuTm9kZSxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdHNjb3BlU3RhY2s6IHN0cmluZ1tdXG5cdCk6IHZvaWQge1xuXHRcdGxldCB0YXJnZXQ6IHRzLklkZW50aWZpZXIgfCB1bmRlZmluZWQ7XG5cdFx0aWYgKHRzLmlzQmluYXJ5RXhwcmVzc2lvbihub2RlKSAmJlxuXHRcdFx0QVNTSUdOTUVOVF9PUEVSQVRPUlMuaGFzKG5vZGUub3BlcmF0b3JUb2tlbi5raW5kKSAmJlxuXHRcdFx0dHMuaXNJZGVudGlmaWVyKG5vZGUubGVmdCkpIHtcblx0XHRcdHRhcmdldCA9IG5vZGUubGVmdDtcblx0XHR9XG5cdFx0aWYgKCh0cy5pc1ByZWZpeFVuYXJ5RXhwcmVzc2lvbihub2RlKSB8fCB0cy5pc1Bvc3RmaXhVbmFyeUV4cHJlc3Npb24obm9kZSkpICYmXG5cdFx0XHQobm9kZS5vcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5QbHVzUGx1c1Rva2VuIHx8IG5vZGUub3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuTWludXNNaW51c1Rva2VuKSAmJlxuXHRcdFx0dHMuaXNJZGVudGlmaWVyKG5vZGUub3BlcmFuZCkpIHtcblx0XHRcdHRhcmdldCA9IG5vZGUub3BlcmFuZDtcblx0XHR9XG5cdFx0aWYgKCF0YXJnZXQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Ly8gTm90ZTogYSBkZWNsYXJhdGlvbiBpbml0aWFsaXplciAoYGxldCB4ID0gNWApIGlzIGEgVmFyaWFibGVEZWNsYXJhdGlvbixcblx0XHQvLyBuZXZlciBhIEJpbmFyeUV4cHJlc3Npb24sIHNvIGl0IGNhbm5vdCByZWFjaCB0aGlzIHBhdGggYXMgYSBcInJlYXNzaWdubWVudFwiXG5cblx0XHRjb25zdCB2YXJpYWJsZSA9IHRoaXMuZmluZFZhcmlhYmxlKHRhcmdldC50ZXh0LCBzY29wZVN0YWNrKTtcblx0XHRpZiAoIXZhcmlhYmxlKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5yZXNvbHZlKHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSBzb3VyY2VGaWxlLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKHRhcmdldC5nZXRTdGFydChzb3VyY2VGaWxlKSk7XG5cdFx0dmFyaWFibGUucmVhc3NpZ25tZW50cy5wdXNoKGAke2ZpbGVQYXRofToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCk7XG5cdH1cblxuXHQvKipcblx0ICogRmluZCBhIHZhcmlhYmxlIGJ5IG5hbWUgd2Fsa2luZyB0aGUgc2NvcGUgY2hhaW4gb3V0d2FyZC5cblx0ICovXG5cdHByaXZhdGUgZmluZFZhcmlhYmxlIChuYW1lOiBzdHJpbmcsIHNjb3BlU3RhY2s6IHN0cmluZ1tdKTogU2NvcGVWYXJpYWJsZSB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChsZXQgaSA9IHNjb3BlU3RhY2subGVuZ3RoIC0gMTsgaSA+PSAwOyBpLS0pIHtcblx0XHRcdGNvbnN0IHZhcmlhYmxlID0gdGhpcy52YXJpYWJsZXMuZ2V0KGAke3Njb3BlU3RhY2tbIGkgXX0jJHtuYW1lfWApO1xuXHRcdFx0aWYgKHZhcmlhYmxlKSB7XG5cdFx0XHRcdHJldHVybiB2YXJpYWJsZTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdHByaXZhdGUgcmVzb2x2ZVZhcmlhYmxlVHlwZVBhdGggKGVudHJ5OiBQZW5kaW5nVmFyaWFibGUsIHJlc29sdmVyOiBTY29wZVR5cGVSZXNvbHZlcik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gYG5ldyBTb21lVHlwZSguLi4pYCDigJQgYmFyZSBjb25zdHJ1Y3RvciBuYW1lXG5cdFx0aWYgKGVudHJ5Lm5ld05hbWUpIHtcblx0XHRcdGNvbnN0IHJlc29sdmVkID0gcmVzb2x2ZXIucmVzb2x2ZUJ5TmFtZShlbnRyeS5uZXdOYW1lKTtcblx0XHRcdGlmIChyZXNvbHZlZCkge1xuXHRcdFx0XHRyZXR1cm4gcmVzb2x2ZWQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gYG5ldyBpbnN0YW5jZS5TdWIuVHlwZSguLi4pYCDigJQgY2hhaW4gb2ZmIGEgdHJhY2tlZCB2YXJpYWJsZSdzIHR5cGVQYXRoXG5cdFx0aWYgKGVudHJ5Lm5ld0NoYWluUm9vdCAmJiBlbnRyeS5uZXdDaGFpblJlc3QgJiYgZW50cnkubmV3Q2hhaW5SZXN0Lmxlbmd0aCA+IDApIHtcblx0XHRcdGZvciAoY29uc3Qgc2NvcGVJZCBvZiBlbnRyeS5zY29wZUNoYWluKSB7XG5cdFx0XHRcdGNvbnN0IHJvb3RWYXJpYWJsZSA9IHRoaXMudmFyaWFibGVzLmdldChgJHtzY29wZUlkfSMke2VudHJ5Lm5ld0NoYWluUm9vdH1gKTtcblx0XHRcdFx0aWYgKCFyb290VmFyaWFibGU/LnR5cGVQYXRoKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgY2FuZGlkYXRlID0gWyByb290VmFyaWFibGUudHlwZVBhdGgsIC4uLmVudHJ5Lm5ld0NoYWluUmVzdCBdLmpvaW4oJy4nKTtcblx0XHRcdFx0aWYgKHJlc29sdmVyLmhhc1BhdGgoY2FuZGlkYXRlKSkge1xuXHRcdFx0XHRcdHJldHVybiBjYW5kaWRhdGU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBgbG9va3VwKCdBLkInKWAgLyBgcmVjZWl2ZXIubG9va3VwKCdBLkInKWAgaW5pdGlhbGl6ZXJzXG5cdFx0aWYgKGVudHJ5Lmxvb2t1cFBhdGgpIHtcblx0XHRcdC8vIFJlY2VpdmVyLXJlbGF0aXZlIGZpcnN0OiBgdXNlci5sb29rdXAoJ0FkbWluRW50aXR5JylgIHJlc29sdmVzXG5cdFx0XHQvLyBhZ2FpbnN0IHRoZSByZWNlaXZlciB2YXJpYWJsZSdzIHR5cGVQYXRoIHdoZW4gdGhhdCB5aWVsZHMgYVxuXHRcdFx0Ly8ga25vd24gcGF0aCAobWlycm9ycyB0aGUgYW5hbHl6ZXIncyByZWxhdGl2ZS10aGVuLXJvb3QgcnVsZSlcblx0XHRcdGlmIChlbnRyeS5sb29rdXBSZWNlaXZlcikge1xuXHRcdFx0XHRmb3IgKGNvbnN0IHNjb3BlSWQgb2YgZW50cnkuc2NvcGVDaGFpbikge1xuXHRcdFx0XHRcdGNvbnN0IHJlY2VpdmVyVmFyaWFibGUgPSB0aGlzLnZhcmlhYmxlcy5nZXQoYCR7c2NvcGVJZH0jJHtlbnRyeS5sb29rdXBSZWNlaXZlcn1gKTtcblx0XHRcdFx0XHRpZiAoIXJlY2VpdmVyVmFyaWFibGU/LnR5cGVQYXRoKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Y29uc3QgY2FuZGlkYXRlID0gYCR7cmVjZWl2ZXJWYXJpYWJsZS50eXBlUGF0aH0uJHtlbnRyeS5sb29rdXBQYXRofWA7XG5cdFx0XHRcdFx0aWYgKHJlc29sdmVyLmhhc1BhdGgoY2FuZGlkYXRlKSkge1xuXHRcdFx0XHRcdFx0cmV0dXJuIGNhbmRpZGF0ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGlmIChyZXNvbHZlci5oYXNQYXRoKGVudHJ5Lmxvb2t1cFBhdGgpKSB7XG5cdFx0XHRcdHJldHVybiBlbnRyeS5sb29rdXBQYXRoO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgYnlOYW1lID0gcmVzb2x2ZXIucmVzb2x2ZUJ5TmFtZShlbnRyeS5sb29rdXBQYXRoKTtcblx0XHRcdGlmIChieU5hbWUpIHtcblx0XHRcdFx0cmV0dXJuIGJ5TmFtZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBUeXBlIGFubm90YXRpb246ICdVc2VyRW50aXR5X1VzZXJSZXNwb25zZScgKHRhY3RpY2EgdHlwZXMudHMgbmFtaW5nKVxuXHRcdC8vIOKGkiBkb3R0ZWQgcGF0aCwgb3IgYSBiYXJlIGtub3duIHR5cGUgbmFtZVxuXHRcdGlmIChlbnRyeS5hbm5vdGF0aW9uKSB7XG5cdFx0XHRjb25zdCBkb3R0ZWQgPSBlbnRyeS5hbm5vdGF0aW9uLnJlcGxhY2UoL18vZywgJy4nKTtcblx0XHRcdGlmIChkb3R0ZWQuaW5jbHVkZXMoJy4nKSAmJiByZXNvbHZlci5oYXNQYXRoKGRvdHRlZCkpIHtcblx0XHRcdFx0cmV0dXJuIGRvdHRlZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGJ5TmFtZSA9IHJlc29sdmVyLnJlc29sdmVCeU5hbWUoZW50cnkuYW5ub3RhdGlvbik7XG5cdFx0XHRpZiAoYnlOYW1lKSB7XG5cdFx0XHRcdHJldHVybiBieU5hbWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxufVxuIl19