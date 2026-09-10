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
                pendingEntry.lookupCall = initializer;
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
            // known path (value-scope tier — innermost binding wins)
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
            // The analyzer's tier law above value scope (import scope,
            // source-relative, root): an imported `Holder.lookup('Token')`
            // or `lookup(App, 'Crate')` resolves exactly as the usages pass
            // resolved it, so scopes.json agrees with the hard-fail verdicts
            if (resolver.resolveLookup && entry.lookupCall) {
                const resolved = resolver.resolveLookup(entry.lookupCall);
                if (resolved && resolver.hasPath(resolved)) {
                    return resolved;
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoic2NvcGVzLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL3Njb3Blcy50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQSxZQUFZLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQUViLDJDQUE2QjtBQUM3QiwrQ0FBaUM7QUE0RGpDLE1BQU0sb0JBQW9CLEdBQUcsSUFBSSxHQUFHLENBQWdCO0lBQ25ELEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVztJQUN6QixFQUFFLENBQUMsVUFBVSxDQUFDLGVBQWU7SUFDN0IsRUFBRSxDQUFDLFVBQVUsQ0FBQyxnQkFBZ0I7SUFDOUIsRUFBRSxDQUFDLFVBQVUsQ0FBQyxtQkFBbUI7SUFDakMsRUFBRSxDQUFDLFVBQVUsQ0FBQywyQkFBMkI7SUFDekMsRUFBRSxDQUFDLFVBQVUsQ0FBQyxnQkFBZ0I7SUFDOUIsRUFBRSxDQUFDLFVBQVUsQ0FBQyxrQkFBa0I7SUFDaEMsRUFBRSxDQUFDLFVBQVUsQ0FBQywyQkFBMkI7SUFDekMsRUFBRSxDQUFDLFVBQVUsQ0FBQyxpQ0FBaUM7SUFDL0MsRUFBRSxDQUFDLFVBQVUsQ0FBQyw0Q0FBNEM7SUFDMUQsRUFBRSxDQUFDLFVBQVUsQ0FBQyxvQkFBb0I7SUFDbEMsRUFBRSxDQUFDLFVBQVUsQ0FBQyxjQUFjO0lBQzVCLEVBQUUsQ0FBQyxVQUFVLENBQUMsZ0JBQWdCO0lBQzlCLEVBQUUsQ0FBQyxVQUFVLENBQUMsNkJBQTZCO0lBQzNDLEVBQUUsQ0FBQyxVQUFVLENBQUMsaUJBQWlCO0lBQy9CLEVBQUUsQ0FBQyxVQUFVLENBQUMsMkJBQTJCO0NBQ3pDLENBQUMsQ0FBQztBQUVIOzs7Ozs7Ozs7Ozs7O0dBYUc7QUFDSCxNQUFhLGdCQUFnQjtJQUE3QjtRQUNTLFdBQU0sR0FBRyxJQUFJLEdBQUcsRUFBcUIsQ0FBQztRQUN0QyxVQUFLLEdBQUcsSUFBSSxHQUFHLEVBQXVCLENBQUM7UUFDdkMsY0FBUyxHQUFHLElBQUksR0FBRyxF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Q0FBQyxPQUFPLENBQUMsSUFBSSxFQUFFLEdBQUcsQ0FBQyxDQUFDO1lBQ25ELElBQUksTUFBTSxDQUFDLFFBQVEsQ0FBQyxHQUFHLENBQUMsSUFBSSxRQUFRLENBQUMsT0FBTyxDQUFDLE1BQU0sQ0FBQyxFQUFFLENBQUM7Z0JBQ3RELE9BQU8sTUFBTSxDQUFDO1lBQ2YsQ0FBQztZQUNELE1BQU0sTUFBTSxHQUFHLFFBQVEsQ0FBQyxhQUFhLENBQUMsS0FBSyxDQUFDLFVBQVUsQ0FBQyxDQUFDO1lBQ3hELElBQUksTUFBTSxFQUFFLENBQUM7Z0JBQ1osT0FBTyxNQUFNLENBQUM7WUFDZixDQUFDO1FBQ0YsQ0FBQztRQUVELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7Q0FDRDtBQTlsQkQsNENBOGxCQyIsInNvdXJjZXNDb250ZW50IjpbIid1c2Ugc3RyaWN0JztcblxuaW1wb3J0ICogYXMgcGF0aCBmcm9tICdwYXRoJztcbmltcG9ydCAqIGFzIHRzIGZyb20gJ3R5cGVzY3JpcHQnO1xuaW1wb3J0IHtcblx0U2NvcGVBbmFseXNpcywgU2NvcGVJbmZvLCBTY29wZUtpbmQsIFNjb3BlVmFyaWFibGUsIFVzYWdlSW5mb1xufSBmcm9tICcuL3R5cGVzJztcblxuLyoqXG4gKiBDb21waWxlLXRpbWUgdmlldyBvdmVyIHRoZSBhbmFseXplcidzIGRlZmluaXRpb25zLCB1c2VkIHRvIGF0dGFjaCBtbmVtb25pY2FcbiAqIHR5cGUgcGF0aHMgdG8gdmFyaWFibGVzLiBOYW1lLWJhc2VkIGhldXJpc3RpY3Mgb25seSDigJQgdGhlIG5vLWdldFR5cGVDaGVja2VyKClcbiAqIHByZWNlZGVudCBzdGF5cy5cbiAqL1xuZXhwb3J0IGludGVyZmFjZSBTY29wZVR5cGVSZXNvbHZlciB7XG5cdC8qKiBSZXNvbHZlIGEgYmFyZSBjb25zdHJ1Y3Rvci90eXBlIG5hbWUgdG8gYSBtbmVtb25pY2EgZnVsbFBhdGggKHVuZGVmaW5lZCB3aGVuIHVua25vd24gb3IgYW1iaWd1b3VzKSAqL1xuXHRyZXNvbHZlQnlOYW1lKG5hbWU6IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0LyoqIFRydWUgd2hlbiB0aGUgZG90dGVkIHBhdGggaXMgYSBrbm93biBtbmVtb25pY2EgdHlwZSAqL1xuXHRoYXNQYXRoKGZ1bGxQYXRoOiBzdHJpbmcpOiBib29sZWFuO1xuXHQvKipcblx0ICogT3B0aW9uYWwgbG9va3VwLWxhdyBkZWxlZ2F0ZTogcmVzb2x2ZSBhIGBsb29rdXAoKWAgaW5pdGlhbGl6ZXIgY2FsbFxuXHQgKiB0aHJvdWdoIHRoZSBhbmFseXplcidzIGZ1bGwgdGllciBsYXcgKHZhbHVlIHNjb3BlLCBpbXBvcnQgc2NvcGUsXG5cdCAqIHNvdXJjZS1yZWxhdGl2ZSwgcm9vdCkuIFRoZSB3YWxrZXIgcnVucyBpdHMgb3duIHNjb3BlLWNoYWluXG5cdCAqIHZhbHVlLXNjb3BlIHRpZXIgZmlyc3Q7IHRoaXMgYmFja3MgdGhlIHRpZXJzIGFib3ZlIGl0IHNvIHNjb3Blcy5qc29uXG5cdCAqIHR5cGVQYXRocyBhZ3JlZSB3aXRoIHRoZSBhbmFseXplcidzIChoYXJkLWZhaWwpIHZlcmRpY3RzLlxuXHQgKi9cblx0cmVzb2x2ZUxvb2t1cD8oY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG59XG5cbi8qKlxuICogSW50ZXJuYWwgc2NvcGUgcmVjb3JkOiBudW1lcmljIHNwYW4gKDEtYmFzZWQgbGluZS9jb2wpIGtlcHQgZm9yXG4gKiBmaW5kSG9sZGVyU2NvcGVJZCgpIGNvbnRhaW5tZW50IG1hdGNoaW5nOyBTY29wZUluZm8gaXRzZWxmIGNhcnJpZXMgc3RyaW5ncy5cbiAqL1xuaW50ZXJmYWNlIFNjb3BlU3BhbiB7XG5cdHNjb3BlSWQ6IHN0cmluZztcblx0c3RhcnRMaW5lOiBudW1iZXI7XG5cdHN0YXJ0Q29sOiBudW1iZXI7XG5cdGVuZExpbmU6IG51bWJlcjtcblx0ZW5kQ29sOiBudW1iZXI7XG59XG5cbi8qKlxuICogUmF3IHZhcmlhYmxlIHJlY29yZCBjb2xsZWN0ZWQgZHVyaW5nIHRoZSBBU1Qgd2Fsay4gdHlwZVBhdGggaXMgcmVzb2x2ZWRcbiAqIGxhdGVyIGluIGJ1aWxkKCksIG9uY2UgZGVmaW5pdGlvbnMgYXJlIGtub3duLlxuICovXG5pbnRlcmZhY2UgUGVuZGluZ1ZhcmlhYmxlIHtcblx0dmFyaWFibGU6IFNjb3BlVmFyaWFibGU7XG5cdC8qKiBCYXJlIGNvbnN0cnVjdG9yIG5hbWUgZm9yIGBuZXcgWCguLi4pYCBpbml0aWFsaXplcnMgKi9cblx0bmV3TmFtZT86IHN0cmluZztcblx0LyoqIFJvb3QgaWRlbnRpZmllciArIHByb3BlcnR5IGNoYWluIGZvciBgbmV3IGEuYi5DKC4uLilgIGluaXRpYWxpemVycyAqL1xuXHRuZXdDaGFpblJvb3Q/OiBzdHJpbmc7XG5cdG5ld0NoYWluUmVzdD86IHN0cmluZ1tdO1xuXHQvKiogU3RyaW5nLWxpdGVyYWwgcGF0aCBvZiBhIGBsb29rdXAoJ0EuQicpYCBpbml0aWFsaXplciAqL1xuXHRsb29rdXBQYXRoPzogc3RyaW5nO1xuXHQvKiogUm9vdCBpZGVudGlmaWVyIG9mIHRoZSByZWNlaXZlciBmb3IgYHJlY2VpdmVyLmxvb2t1cCgnQS5CJylgIC8gYGxvb2t1cChzb3VyY2UsICdBLkInKWAgKi9cblx0bG9va3VwUmVjZWl2ZXI/OiBzdHJpbmc7XG5cdC8qKiBUaGUgbG9va3VwKCkgY2FsbCBub2RlIGl0c2VsZiDigJQgaGFuZGVkIHRvIHRoZSByZXNvbHZlcidzIGxvb2t1cC1sYXcgZGVsZWdhdGUgKi9cblx0bG9va3VwQ2FsbD86IHRzLkNhbGxFeHByZXNzaW9uO1xuXHQvKiogUmF3IHR5cGUgYW5ub3RhdGlvbiB0ZXh0IChlLmcuICdVc2VyRW50aXR5X1VzZXJSZXNwb25zZScpICovXG5cdGFubm90YXRpb24/OiBzdHJpbmc7XG5cdC8qKiBTY29wZSBjaGFpbiBmcm9tIGRlY2xhcmF0aW9uIHNpdGUgb3V0d2FyZCwgZm9yIGNoYWluLXJvb3QgbG9va3VwICovXG5cdHNjb3BlQ2hhaW46IHN0cmluZ1tdO1xufVxuXG5jb25zdCBBU1NJR05NRU5UX09QRVJBVE9SUyA9IG5ldyBTZXQ8dHMuU3ludGF4S2luZD4oW1xuXHR0cy5TeW50YXhLaW5kLkVxdWFsc1Rva2VuLFxuXHR0cy5TeW50YXhLaW5kLlBsdXNFcXVhbHNUb2tlbixcblx0dHMuU3ludGF4S2luZC5NaW51c0VxdWFsc1Rva2VuLFxuXHR0cy5TeW50YXhLaW5kLkFzdGVyaXNrRXF1YWxzVG9rZW4sXG5cdHRzLlN5bnRheEtpbmQuQXN0ZXJpc2tBc3Rlcmlza0VxdWFsc1Rva2VuLFxuXHR0cy5TeW50YXhLaW5kLlNsYXNoRXF1YWxzVG9rZW4sXG5cdHRzLlN5bnRheEtpbmQuUGVyY2VudEVxdWFsc1Rva2VuLFxuXHR0cy5TeW50YXhLaW5kLkxlc3NUaGFuTGVzc1RoYW5FcXVhbHNUb2tlbixcblx0dHMuU3ludGF4S2luZC5HcmVhdGVyVGhhbkdyZWF0ZXJUaGFuRXF1YWxzVG9rZW4sXG5cdHRzLlN5bnRheEtpbmQuR3JlYXRlclRoYW5HcmVhdGVyVGhhbkdyZWF0ZXJUaGFuRXF1YWxzVG9rZW4sXG5cdHRzLlN5bnRheEtpbmQuQW1wZXJzYW5kRXF1YWxzVG9rZW4sXG5cdHRzLlN5bnRheEtpbmQuQmFyRXF1YWxzVG9rZW4sXG5cdHRzLlN5bnRheEtpbmQuQ2FyZXRFcXVhbHNUb2tlbixcblx0dHMuU3ludGF4S2luZC5BbXBlcnNhbmRBbXBlcnNhbmRFcXVhbHNUb2tlbixcblx0dHMuU3ludGF4S2luZC5CYXJCYXJFcXVhbHNUb2tlbixcblx0dHMuU3ludGF4S2luZC5RdWVzdGlvblF1ZXN0aW9uRXF1YWxzVG9rZW4sXG5dKTtcblxuLyoqXG4gKiBMb2NhbC1zY29wZSB3YWxrZXIgKGluc3RydW1lbnRhdGlvbiB3YWxrZXIgcGxhbiwgUGhhc2UgMikuXG4gKlxuICogVHJhY2tzIGZ1bmN0aW9uL21ldGhvZC9hcnJvdyBzY29wZXMgT05MWSAoZGVjaXNpb24gNTogbm8gYmxvY2sgc2NvcGVzKSxcbiAqIHBsdXMgb25lIHN5bnRoZXRpYyAnbW9kdWxlJyBzY29wZSBwZXIgZmlsZSDigJQgdGhlIHBsYW4gcmVxdWlyZXMgbW9kdWxlLXNjb3BlXG4gKiBpbnN0YW5jZSBjcmVhdGlvbnMgdG8gYmUgbGFiZWxlZCwgbm90IGRyb3BwZWQuIFZhcmlhYmxlcyBjYXJyeSBpc011dGFibGVcbiAqIChjb25zdCB2cyBsZXQvdmFyL3BhcmFtZXRlcikgYW5kIGByZWFzc2lnbm1lbnRzYDogZWFjaCByZWFzc2lnbm1lbnQgc2l0ZSBvZlxuICogYSBtdXRhYmxlIGJpbmRpbmcgaXMgYSBmbG93LXRlcm1pbmF0aW9uIHBvaW50IChkZWNpc2lvbiA2KSDigJQgZG93bnN0cmVhbSB0aGVcbiAqIHdhbGtlciBzdG9wcyBmb2xsb3dpbmcgdGhhdCBiaW5kaW5nIHRoZXJlLlxuICpcbiAqIFVzYWdlOiBhZGRGaWxlKCkgcGVyIHNvdXJjZSBmaWxlLCB0aGVuIGJ1aWxkKHJlc29sdmVyKSBvbmNlIGRlZmluaXRpb25zIGFyZVxuICoga25vd24uIGZpbmRIb2xkZXJTY29wZUlkKGxvY2F0aW9uKSBtYXBzIGEgdXNhZ2UgbG9jYXRpb24gc3RyaW5nIHRvIHRoZVxuICogaW5uZXJtb3N0IHNjb3BlIGNvbnRhaW5pbmcgaXQgKHVzYWdlcy5qc29uIGhvbGRlclNjb3BlSWQpLlxuICovXG5leHBvcnQgY2xhc3MgTG9jYWxTY29wZVdhbGtlciB7XG5cdHByaXZhdGUgc2NvcGVzID0gbmV3IE1hcDxzdHJpbmcsIFNjb3BlSW5mbz4oKTtcblx0cHJpdmF0ZSBzcGFucyA9IG5ldyBNYXA8c3RyaW5nLCBTY29wZVNwYW5bXT4oKTtcblx0cHJpdmF0ZSB2YXJpYWJsZXMgPSBuZXcgTWFwPHN0cmluZywgU2NvcGVWYXJpYWJsZT4oKTtcblx0cHJpdmF0ZSBwZW5kaW5nOiBQZW5kaW5nVmFyaWFibGVbXSA9IFtdO1xuXHQvKipcblx0ICogQXJyb3cvZnVuY3Rpb24tZXhwcmVzc2lvbiBub2RlIC0+IG5hbWUgaXQgaXMgYm91bmQgdG8gKGBjb25zdCBmID0gKCkgPT4g4oCmYCxcblx0ICogYHsgaGFuZGxlcjogKCkgPT4g4oCmIH1gLCBjbGFzcyBwcm9wZXJ0aWVzKS4gUHJvZ3JhbSBzb3VyY2UgZmlsZXMgY2FuIGJlXG5cdCAqIFVOQk9VTkQgKG5vIG5vZGUucGFyZW50IHBvaW50ZXJzKSwgc28gYmluZGluZyBuYW1lcyB0cmF2ZWwgdGhyb3VnaCB0aGlzXG5cdCAqIG1hcCBpbnN0ZWFkIG9mIHBhcmVudCBsb29rdXBzLlxuXHQgKi9cblx0cHJpdmF0ZSBib3VuZE5hbWVzID0gbmV3IE1hcDx0cy5Ob2RlLCBzdHJpbmc+KCk7XG5cblx0LyoqXG5cdCAqIFRyYWNrIG9uZSBzb3VyY2UgZmlsZS4gUmUtYWRkaW5nIHRoZSBzYW1lIGZpbGUgcmVwbGFjZXMgaXRzIHJlY29yZHMsXG5cdCAqIHNvIGEgd2Fsa2VyIG1heSBzYWZlbHkgYmUgcmV1c2VkIGFjcm9zcyBwYXNzZXMuXG5cdCAqL1xuXHRhZGRGaWxlIChzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLnJlc29sdmUoc291cmNlRmlsZS5maWxlTmFtZSk7XG5cdFx0dGhpcy5kcm9wRmlsZShmaWxlUGF0aCk7XG5cblx0XHRjb25zdCBtb2R1bGVTY29wZTogU2NvcGVJbmZvID0ge1xuXHRcdFx0c2NvcGVJZCAgOiBmaWxlUGF0aCxcblx0XHRcdG5hbWUgICAgIDogZmlsZVBhdGgsXG5cdFx0XHRraW5kICAgICA6ICdtb2R1bGUnLFxuXHRcdFx0ZmlsZVBhdGgsXG5cdFx0XHRsb2NhdGlvbiA6IGAke2ZpbGVQYXRofToxOjFgLFxuXHRcdH07XG5cdFx0dGhpcy5zY29wZXMuc2V0KG1vZHVsZVNjb3BlLnNjb3BlSWQsIG1vZHVsZVNjb3BlKTtcblxuXHRcdGNvbnN0IHNwYW5zOiBTY29wZVNwYW5bXSA9IFtdO1xuXHRcdHRoaXMuc3BhbnMuc2V0KGZpbGVQYXRoLCBzcGFucyk7XG5cdFx0c3BhbnMucHVzaCh0aGlzLnNwYW5PZihzb3VyY2VGaWxlLCBzb3VyY2VGaWxlLCBtb2R1bGVTY29wZS5zY29wZUlkKSk7XG5cblx0XHRjb25zdCBzY29wZVN0YWNrOiBzdHJpbmdbXSA9IFsgbW9kdWxlU2NvcGUuc2NvcGVJZCBdO1xuXHRcdGNvbnN0IGNsYXNzU3RhY2s6IHN0cmluZ1tdID0gW107XG5cdFx0dGhpcy52aXNpdE5vZGUoc291cmNlRmlsZSwgc291cmNlRmlsZSwgZmlsZVBhdGgsIHNjb3BlU3RhY2ssIGNsYXNzU3RhY2ssIHNwYW5zKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHBlbmRpbmcgdHlwZVBhdGhzIGFuZCByZXR1cm4gdGhlIGFuYWx5c2lzLlxuXHQgKi9cblx0YnVpbGQgKHJlc29sdmVyPzogU2NvcGVUeXBlUmVzb2x2ZXIpOiBTY29wZUFuYWx5c2lzIHtcblx0XHRpZiAocmVzb2x2ZXIpIHtcblx0XHRcdGZvciAoY29uc3QgZW50cnkgb2YgdGhpcy5wZW5kaW5nKSB7XG5cdFx0XHRcdGNvbnN0IHR5cGVQYXRoID0gdGhpcy5yZXNvbHZlVmFyaWFibGVUeXBlUGF0aChlbnRyeSwgcmVzb2x2ZXIpO1xuXHRcdFx0XHRpZiAodHlwZVBhdGgpIHtcblx0XHRcdFx0XHRlbnRyeS52YXJpYWJsZS50eXBlUGF0aCA9IHR5cGVQYXRoO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgYW5hbHlzaXM6IFNjb3BlQW5hbHlzaXMgPSB7XG5cdFx0XHRzY29wZXMgICAgOiB0aGlzLnNjb3Blcyxcblx0XHRcdHZhcmlhYmxlcyA6IHRoaXMudmFyaWFibGVzLFxuXHRcdH07XG5cdFx0cmV0dXJuIGFuYWx5c2lzO1xuXHR9XG5cblx0LyoqXG5cdCAqIE1hcCBhIHVzYWdlIGxvY2F0aW9uIHN0cmluZyAoJ2Ficy9maWxlLnRzOmxpbmU6Y29sJykgdG8gdGhlIGlubmVybW9zdFxuXHQgKiBzY29wZSBjb250YWluaW5nIGl0LiBNb2R1bGUgc2NvcGUgaXMgdGhlIGZhbGxiYWNrLCBzbyBldmVyeSBsb2NhdGlvblxuXHQgKiBpbnNpZGUgYSB0cmFja2VkIGZpbGUgcmVzb2x2ZXMgdG8gc29tZSBzY29wZS5cblx0ICovXG5cdGZpbmRIb2xkZXJTY29wZUlkIChsb2NhdGlvbjogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBsYXN0Q29sb24gPSBsb2NhdGlvbi5sYXN0SW5kZXhPZignOicpO1xuXHRcdGNvbnN0IHByZXZDb2xvbiA9IGxvY2F0aW9uLmxhc3RJbmRleE9mKCc6JywgbGFzdENvbG9uIC0gMSk7XG5cdFx0aWYgKGxhc3RDb2xvbiA8IDAgfHwgcHJldkNvbG9uIDwgMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLnJlc29sdmUobG9jYXRpb24uc2xpY2UoMCwgcHJldkNvbG9uKSk7XG5cdFx0Y29uc3QgbGluZSA9IE51bWJlcihsb2NhdGlvbi5zbGljZShwcmV2Q29sb24gKyAxLCBsYXN0Q29sb24pKTtcblx0XHRjb25zdCBjb2wgPSBOdW1iZXIobG9jYXRpb24uc2xpY2UobGFzdENvbG9uICsgMSkpO1xuXHRcdGlmICghTnVtYmVyLmlzRmluaXRlKGxpbmUpIHx8ICFOdW1iZXIuaXNGaW5pdGUoY29sKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBzcGFucyA9IHRoaXMuc3BhbnMuZ2V0KGZpbGVQYXRoKTtcblx0XHRpZiAoIXNwYW5zKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGxldCBiZXN0OiBTY29wZVNwYW4gfCB1bmRlZmluZWQ7XG5cdFx0Zm9yIChjb25zdCBzcGFuIG9mIHNwYW5zKSB7XG5cdFx0XHRjb25zdCBzdGFydHNCZWZvcmUgPSBzcGFuLnN0YXJ0TGluZSA8IGxpbmUgfHwgKHNwYW4uc3RhcnRMaW5lID09PSBsaW5lICYmIHNwYW4uc3RhcnRDb2wgPD0gY29sKTtcblx0XHRcdGNvbnN0IGVuZHNBZnRlciA9IHNwYW4uZW5kTGluZSA+IGxpbmUgfHwgKHNwYW4uZW5kTGluZSA9PT0gbGluZSAmJiBzcGFuLmVuZENvbCA+PSBjb2wpO1xuXHRcdFx0aWYgKCFzdGFydHNCZWZvcmUgfHwgIWVuZHNBZnRlcikge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdC8vIElubmVybW9zdCA9IHNtYWxsZXN0IGNvbnRhaW5pbmcgc3BhblxuXHRcdFx0aWYgKGJlc3QgJiYgKGJlc3Quc3RhcnRMaW5lIDwgc3Bhbi5zdGFydExpbmUgfHxcblx0XHRcdFx0KGJlc3Quc3RhcnRMaW5lID09PSBzcGFuLnN0YXJ0TGluZSAmJiBiZXN0LnN0YXJ0Q29sIDw9IHNwYW4uc3RhcnRDb2wpKSkge1xuXHRcdFx0XHRiZXN0ID0gc3Bhbjtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRpZiAoIWJlc3QpIHtcblx0XHRcdFx0YmVzdCA9IHNwYW47XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGJlc3Q/LnNjb3BlSWQ7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZW1vdmUgZXZlcnkgcmVjb3JkIGJlbG9uZ2luZyB0byBvbmUgZmlsZSAocmUtYWRkIHN1cHBvcnQpLlxuXHQgKi9cblx0cHJpdmF0ZSBkcm9wRmlsZSAoZmlsZVBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdGZvciAoY29uc3QgWyBzY29wZUlkLCBzY29wZSBdIG9mIHRoaXMuc2NvcGVzKSB7XG5cdFx0XHRpZiAoc2NvcGUuZmlsZVBhdGggPT09IGZpbGVQYXRoKSB7XG5cdFx0XHRcdHRoaXMuc2NvcGVzLmRlbGV0ZShzY29wZUlkKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0Zm9yIChjb25zdCBrZXkgb2YgQXJyYXkuZnJvbSh0aGlzLnZhcmlhYmxlcy5rZXlzKCkpKSB7XG5cdFx0XHRpZiAoa2V5LnN0YXJ0c1dpdGgoYCR7ZmlsZVBhdGh9I2ApIHx8IGtleS5zdGFydHNXaXRoKGAke2ZpbGVQYXRofTpgKSkge1xuXHRcdFx0XHR0aGlzLnZhcmlhYmxlcy5kZWxldGUoa2V5KTtcblx0XHRcdH1cblx0XHR9XG5cdFx0dGhpcy5wZW5kaW5nID0gdGhpcy5wZW5kaW5nLmZpbHRlcihlbnRyeSA9PlxuXHRcdFx0IWVudHJ5LnZhcmlhYmxlLmRlY2xhcmF0aW9uLnN0YXJ0c1dpdGgoYCR7ZmlsZVBhdGh9OmApKTtcblx0XHR0aGlzLnNwYW5zLmRlbGV0ZShmaWxlUGF0aCk7XG5cdH1cblxuXHQvKipcblx0ICogQXR0YWNoIGhvbGRlclNjb3BlSWQgdG8gZXZlcnkgdXNhZ2Ugd2hvc2UgbG9jYXRpb24gZmFsbHMgaW5zaWRlIGFcblx0ICogdHJhY2tlZCBzY29wZS4gQWRkaXRpdmUgb24gVXNhZ2VJbmZvOyB1c2FnZXMgb3V0c2lkZSB0cmFja2VkIGZpbGVzXG5cdCAqIGFyZSBsZWZ0IHVudG91Y2hlZC5cblx0ICovXG5cdHN0YXRpYyBhdHRhY2hIb2xkZXJTY29wZUlkcyAodXNhZ2VzOiBNYXA8c3RyaW5nLCBVc2FnZUluZm9bXT4sIHdhbGtlcjogTG9jYWxTY29wZVdhbGtlcik6IHZvaWQge1xuXHRcdGZvciAoY29uc3QgdXNhZ2VMaXN0IG9mIHVzYWdlcy52YWx1ZXMoKSkge1xuXHRcdFx0Zm9yIChjb25zdCB1c2FnZSBvZiB1c2FnZUxpc3QpIHtcblx0XHRcdFx0Y29uc3Qgc2NvcGVJZCA9IHdhbGtlci5maW5kSG9sZGVyU2NvcGVJZCh1c2FnZS5sb2NhdGlvbik7XG5cdFx0XHRcdGlmIChzY29wZUlkKSB7XG5cdFx0XHRcdFx0dXNhZ2UuaG9sZGVyU2NvcGVJZCA9IHNjb3BlSWQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHRwcml2YXRlIHZpc2l0Tm9kZSAoXG5cdFx0bm9kZTogdHMuTm9kZSxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdGZpbGVQYXRoOiBzdHJpbmcsXG5cdFx0c2NvcGVTdGFjazogc3RyaW5nW10sXG5cdFx0Y2xhc3NTdGFjazogc3RyaW5nW10sXG5cdFx0c3BhbnM6IFNjb3BlU3BhbltdXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IHNjb3BlS2luZCA9IExvY2FsU2NvcGVXYWxrZXIuc2NvcGVLaW5kT2Yobm9kZSk7XG5cdFx0bGV0IGVudGVyZWQgPSBmYWxzZTtcblx0XHRpZiAoc2NvcGVLaW5kICYmIHRoaXMuaGFzQm9keShub2RlKSkge1xuXHRcdFx0dGhpcy5lbnRlclNjb3BlKG5vZGUsIHNjb3BlS2luZCwgc291cmNlRmlsZSwgZmlsZVBhdGgsIHNjb3BlU3RhY2ssIGNsYXNzU3RhY2ssIHNwYW5zKTtcblx0XHRcdGVudGVyZWQgPSB0cnVlO1xuXHRcdH1cblxuXHRcdGNvbnN0IGlzQ2xhc3MgPSB0cy5pc0NsYXNzRGVjbGFyYXRpb24obm9kZSkgfHwgdHMuaXNDbGFzc0V4cHJlc3Npb24obm9kZSk7XG5cdFx0aWYgKGlzQ2xhc3MpIHtcblx0XHRcdGNsYXNzU3RhY2sucHVzaChub2RlLm5hbWU/LnRleHQgPz8gJycpO1xuXHRcdH1cblxuXHRcdHRoaXMuY29sbGVjdEJvdW5kTmFtZShub2RlKTtcblx0XHR0aGlzLmNvbGxlY3RWYXJpYWJsZURlY2xhcmF0aW9uTGlzdChub2RlLCBzb3VyY2VGaWxlLCBzY29wZVN0YWNrKTtcblx0XHR0aGlzLmNvbGxlY3RSZWFzc2lnbm1lbnQobm9kZSwgc291cmNlRmlsZSwgc2NvcGVTdGFjayk7XG5cblx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgY2hpbGQgPT4ge1xuXHRcdFx0dGhpcy52aXNpdE5vZGUoY2hpbGQsIHNvdXJjZUZpbGUsIGZpbGVQYXRoLCBzY29wZVN0YWNrLCBjbGFzc1N0YWNrLCBzcGFucyk7XG5cdFx0fSk7XG5cblx0XHRpZiAoaXNDbGFzcykge1xuXHRcdFx0Y2xhc3NTdGFjay5wb3AoKTtcblx0XHR9XG5cdFx0aWYgKGVudGVyZWQpIHtcblx0XHRcdHNjb3BlU3RhY2sucG9wKCk7XG5cdFx0fVxuXHR9XG5cblx0cHJpdmF0ZSBzdGF0aWMgc2NvcGVLaW5kT2YgKG5vZGU6IHRzLk5vZGUpOiBTY29wZUtpbmQgfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc01ldGhvZERlY2xhcmF0aW9uKG5vZGUpIHx8IHRzLmlzR2V0QWNjZXNzb3JEZWNsYXJhdGlvbihub2RlKSB8fFxuXHRcdFx0dHMuaXNTZXRBY2Nlc3NvckRlY2xhcmF0aW9uKG5vZGUpIHx8IHRzLmlzQ29uc3RydWN0b3JEZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuICdtZXRob2QnO1xuXHRcdH1cblx0XHRpZiAodHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKG5vZGUpIHx8IHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gJ2Z1bmN0aW9uJztcblx0XHR9XG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuICdhcnJvdyc7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHRwcml2YXRlIGhhc0JvZHkgKG5vZGU6IHRzLk5vZGUpOiBib29sZWFuIHtcblx0XHRjb25zdCBib2R5SG9sZGVyID0gbm9kZSBhcyB0cy5GdW5jdGlvbkxpa2VEZWNsYXJhdGlvbjtcblx0XHRjb25zdCByZXN1bHQgPSBib2R5SG9sZGVyLmJvZHkgIT09IHVuZGVmaW5lZDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0cHJpdmF0ZSBlbnRlclNjb3BlIChcblx0XHRub2RlOiB0cy5Ob2RlLFxuXHRcdGtpbmQ6IFNjb3BlS2luZCxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdGZpbGVQYXRoOiBzdHJpbmcsXG5cdFx0c2NvcGVTdGFjazogc3RyaW5nW10sXG5cdFx0Y2xhc3NTdGFjazogc3RyaW5nW10sXG5cdFx0c3BhbnM6IFNjb3BlU3BhbltdXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSBzb3VyY2VGaWxlLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSkpO1xuXHRcdGNvbnN0IHNjb3BlSWQgPSBgJHtmaWxlUGF0aH06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgcGFyZW50U2NvcGVJZCA9IHNjb3BlU3RhY2tbIHNjb3BlU3RhY2subGVuZ3RoIC0gMSBdO1xuXG5cdFx0Y29uc3Qgc2NvcGU6IFNjb3BlSW5mbyA9IHtcblx0XHRcdHNjb3BlSWQsXG5cdFx0XHRuYW1lICAgICA6IHRoaXMuc2NvcGVOYW1lKG5vZGUsIGtpbmQsIGZpbGVQYXRoLCBsaW5lICsgMSwgY2xhc3NTdGFjayksXG5cdFx0XHRraW5kLFxuXHRcdFx0cGFyZW50U2NvcGVJZCxcblx0XHRcdGZpbGVQYXRoLFxuXHRcdFx0bG9jYXRpb24gOiBzY29wZUlkLFxuXHRcdH07XG5cdFx0dGhpcy5zY29wZXMuc2V0KHNjb3BlSWQsIHNjb3BlKTtcblx0XHRzcGFucy5wdXNoKHRoaXMuc3Bhbk9mKG5vZGUsIHNvdXJjZUZpbGUsIHNjb3BlSWQpKTtcblx0XHRzY29wZVN0YWNrLnB1c2goc2NvcGVJZCk7XG5cblx0XHQvLyBQYXJhbWV0ZXJzIGFyZSB2YXJpYWJsZXMgb2YgdGhlIHNjb3BlOyB0aGV5IGFyZSByZWFzc2lnbmFibGUsIHNvXG5cdFx0Ly8gaXNNdXRhYmxlOiB0cnVlIOKAlCBhIHBhcmFtZXRlciByZWFzc2lnbm1lbnQgdGVybWluYXRlcyB0aGUgZmxvdyB0b29cblx0XHRjb25zdCBmbiA9IG5vZGUgYXMgdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb247XG5cdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBmbi5wYXJhbWV0ZXJzID8/IFtdKSB7XG5cdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSkge1xuXHRcdFx0XHQvLyBTa2lwIGRlc3RydWN0dXJlZCBwYXJhbWV0ZXJzIChhbmFseXplciBwcmVjZWRlbnQpXG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0dGhpcy5yZWNvcmRWYXJpYWJsZShwYXJhbS5uYW1lLnRleHQsIHBhcmFtLm5hbWUsIHNvdXJjZUZpbGUsIHNjb3BlU3RhY2ssIHtcblx0XHRcdFx0aXNQYXJhbWV0ZXIgOiB0cnVlLFxuXHRcdFx0XHQvLyBgdGhpc2AgcGFyYW1ldGVycyAobW5lbW9uaWNhIGhhbmRsZXJzKSBhcmUgbmV2ZXIgcmVhc3NpZ25hYmxlXG5cdFx0XHRcdGlzTXV0YWJsZSAgIDogcGFyYW0ubmFtZS50ZXh0ICE9PSAndGhpcycsXG5cdFx0XHRcdGFubm90YXRpb24gIDogcGFyYW0udHlwZT8uZ2V0VGV4dChzb3VyY2VGaWxlKSxcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBEZWNpc2lvbiA4IGxhYmVsaW5nOiBmdW5jdGlvbnMgYnkgbmFtZTsgbWV0aG9kcyBhcyBDbGFzcy5tZXRob2Q7XG5cdCAqIGFycm93cy9mdW5jdGlvbnMgYm91bmQgdG8gYSB2YXJpYWJsZSBvciBwcm9wZXJ0eSB0YWtlIHRoYXQgbmFtZTtcblx0ICogYW5vbnltb3VzIGhvbGRlcnMgYXJlIGxhYmVsZWQgZmlsZTpsaW5lLlxuXHQgKi9cblx0cHJpdmF0ZSBzY29wZU5hbWUgKFxuXHRcdG5vZGU6IHRzLk5vZGUsXG5cdFx0a2luZDogU2NvcGVLaW5kLFxuXHRcdGZpbGVQYXRoOiBzdHJpbmcsXG5cdFx0bGluZTogbnVtYmVyLFxuXHRcdGNsYXNzU3RhY2s6IHN0cmluZ1tdXG5cdCk6IHN0cmluZyB7XG5cdFx0Y29uc3QgbmFtZWQgPSBub2RlIGFzIHRzLk5hbWVkRGVjbGFyYXRpb247XG5cdFx0aWYgKGtpbmQgPT09ICdtZXRob2QnKSB7XG5cdFx0XHRjb25zdCBtZXRob2ROYW1lID0gbmFtZWQubmFtZSA/IG5hbWVkLm5hbWUuZ2V0VGV4dCgpIDogJ2Fub255bW91cyc7XG5cdFx0XHRjb25zdCBjbGFzc05hbWUgPSBjbGFzc1N0YWNrWyBjbGFzc1N0YWNrLmxlbmd0aCAtIDEgXTtcblx0XHRcdGNvbnN0IGN0b3IgPSB0cy5pc0NvbnN0cnVjdG9yRGVjbGFyYXRpb24obm9kZSkgPyAnY29uc3RydWN0b3InIDogbWV0aG9kTmFtZTtcblx0XHRcdGNvbnN0IG1ldGhvZFNjb3BlTmFtZSA9IGNsYXNzTmFtZSA/IGAke2NsYXNzTmFtZX0uJHtjdG9yfWAgOiBjdG9yO1xuXHRcdFx0cmV0dXJuIG1ldGhvZFNjb3BlTmFtZTtcblx0XHR9XG5cdFx0aWYgKG5hbWVkLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG5hbWVkLm5hbWUpKSB7XG5cdFx0XHRjb25zdCBkZWNsYXJlZE5hbWUgPSBuYW1lZC5uYW1lLnRleHQ7XG5cdFx0XHRyZXR1cm4gZGVjbGFyZWROYW1lO1xuXHRcdH1cblx0XHQvLyBCb3VuZCBuYW1lcyBjb21lIGZyb20gdGhlIGJvdW5kTmFtZXMgbWFwIOKAlCBwcm9ncmFtIGZpbGVzIG1heSBiZVxuXHRcdC8vIHVuYm91bmQsIHNvIG5vZGUucGFyZW50IGlzIG5vdCBhIHJlbGlhYmxlIHBhdGggdG8gdGhlIHZhcmlhYmxlIG5hbWVcblx0XHRjb25zdCBib3VuZCA9IHRoaXMuYm91bmROYW1lcy5nZXQobm9kZSk7XG5cdFx0aWYgKGJvdW5kKSB7XG5cdFx0XHRyZXR1cm4gYm91bmQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGAke2ZpbGVQYXRofToke2xpbmV9YDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0cHJpdmF0ZSBzcGFuT2YgKFxuXHRcdG5vZGU6IHRzLk5vZGUsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRzY29wZUlkOiBzdHJpbmdcblx0KTogU2NvcGVTcGFuIHtcblx0XHRjb25zdCBzdGFydCA9IHNvdXJjZUZpbGUuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24obm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKSk7XG5cdFx0Y29uc3QgZW5kID0gc291cmNlRmlsZS5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihub2RlLmdldEVuZCgpKTtcblx0XHRjb25zdCBzcGFuOiBTY29wZVNwYW4gPSB7XG5cdFx0XHRzY29wZUlkLFxuXHRcdFx0c3RhcnRMaW5lIDogc3RhcnQubGluZSArIDEsXG5cdFx0XHRzdGFydENvbCAgOiBzdGFydC5jaGFyYWN0ZXIgKyAxLFxuXHRcdFx0ZW5kTGluZSAgIDogZW5kLmxpbmUgKyAxLFxuXHRcdFx0ZW5kQ29sICAgIDogZW5kLmNoYXJhY3RlciArIDEsXG5cdFx0fTtcblx0XHRyZXR1cm4gc3Bhbjtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgdGhlIG5hbWUgYW4gYXJyb3cvZnVuY3Rpb24tZXhwcmVzc2lvbiBpcyBib3VuZCB0bywgd2l0aG91dFxuXHQgKiByZWx5aW5nIG9uIG5vZGUucGFyZW50ICh1bmJvdW5kIHByb2dyYW0gZmlsZXMpOiBgY29uc3QgZiA9ICgpID0+IOKApmAsXG5cdCAqIGB7IGhhbmRsZXI6ICgpID0+IOKApiB9YCwgYGNsYXNzIEMgeyBydW4gPSAoKSA9PiDigKYgfWAuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RCb3VuZE5hbWUgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAodHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpICYmIHRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpICYmIG5vZGUuaW5pdGlhbGl6ZXIgJiZcblx0XHRcdCh0cy5pc0Fycm93RnVuY3Rpb24obm9kZS5pbml0aWFsaXplcikgfHwgdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24obm9kZS5pbml0aWFsaXplcikpKSB7XG5cdFx0XHR0aGlzLmJvdW5kTmFtZXMuc2V0KG5vZGUuaW5pdGlhbGl6ZXIsIG5vZGUubmFtZS50ZXh0KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKCh0cy5pc1Byb3BlcnR5QXNzaWdubWVudChub2RlKSB8fCB0cy5pc1Byb3BlcnR5RGVjbGFyYXRpb24obm9kZSkpICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSAmJiBub2RlLmluaXRpYWxpemVyICYmXG5cdFx0XHQodHMuaXNBcnJvd0Z1bmN0aW9uKG5vZGUuaW5pdGlhbGl6ZXIpIHx8IHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKG5vZGUuaW5pdGlhbGl6ZXIpKSkge1xuXHRcdFx0dGhpcy5ib3VuZE5hbWVzLnNldChub2RlLmluaXRpYWxpemVyLCBub2RlLm5hbWUudGV4dCk7XG5cdFx0fVxuXHR9XG5cblx0cHJpdmF0ZSBjb2xsZWN0VmFyaWFibGVEZWNsYXJhdGlvbkxpc3QgKFxuXHRcdG5vZGU6IHRzLk5vZGUsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRzY29wZVN0YWNrOiBzdHJpbmdbXVxuXHQpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbkxpc3Qobm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Ly8gRmxhZ3MgbGl2ZSBvbiB0aGUgbGlzdCBpdHNlbGYg4oCUIG5vIHBhcmVudCB3YWxrIG5lZWRlZCAodGhlIGxpc3Qnc1xuXHRcdC8vIHBhcmVudCBtYXkgYmUgdW5zZXQgb24gdW5ib3VuZCBwcm9ncmFtIGZpbGVzKVxuXHRcdGNvbnN0IGlzQ29uc3QgPSAobm9kZS5mbGFncyAmIHRzLk5vZGVGbGFncy5Db25zdCkgIT09IDA7XG5cdFx0Zm9yIChjb25zdCBkZWNsIG9mIG5vZGUuZGVjbGFyYXRpb25zKSB7XG5cdFx0XHQvLyBEZXN0cnVjdHVyaW5nIGRlY2xhcmF0aW9ucyBhcmUgc2tpcHBlZDogb25seSBwbGFpblxuXHRcdFx0Ly8gYGNvbnN0L2xldC92YXIgeCA9IOKApmAgaGFzIGFuIGlkZW50aWZpZXIgbmFtZVxuXHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoZGVjbC5uYW1lKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdHRoaXMucmVjb3JkVmFyaWFibGUoZGVjbC5uYW1lLnRleHQsIGRlY2wubmFtZSwgc291cmNlRmlsZSwgc2NvcGVTdGFjaywge1xuXHRcdFx0XHRpc1BhcmFtZXRlciA6IGZhbHNlLFxuXHRcdFx0XHRpc011dGFibGUgICA6ICFpc0NvbnN0LFxuXHRcdFx0XHRhbm5vdGF0aW9uICA6IGRlY2wudHlwZT8uZ2V0VGV4dChzb3VyY2VGaWxlKSxcblx0XHRcdFx0aW5pdGlhbGl6ZXIgOiBkZWNsLmluaXRpYWxpemVyLFxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0cHJpdmF0ZSByZWNvcmRWYXJpYWJsZSAoXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdG5vZGU6IHRzLk5vZGUsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRzY29wZVN0YWNrOiBzdHJpbmdbXSxcblx0XHRvcHRpb25zOiB7XG5cdFx0XHRpc1BhcmFtZXRlcjogYm9vbGVhbjtcblx0XHRcdGlzTXV0YWJsZTogYm9vbGVhbjtcblx0XHRcdGFubm90YXRpb24/OiBzdHJpbmc7XG5cdFx0XHRpbml0aWFsaXplcj86IHRzLkV4cHJlc3Npb247XG5cdFx0fVxuXHQpOiB2b2lkIHtcblx0XHRjb25zdCBzY29wZUlkID0gc2NvcGVTdGFja1sgc2NvcGVTdGFjay5sZW5ndGggLSAxIF07XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHNvdXJjZUZpbGUuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24obm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKSk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLnJlc29sdmUoc291cmNlRmlsZS5maWxlTmFtZSk7XG5cblx0XHRjb25zdCB2YXJpYWJsZTogU2NvcGVWYXJpYWJsZSA9IHtcblx0XHRcdG5hbWUsXG5cdFx0XHRzY29wZUlkLFxuXHRcdFx0ZGVjbGFyYXRpb24gICA6IGAke2ZpbGVQYXRofToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdGlzUGFyYW1ldGVyICAgOiBvcHRpb25zLmlzUGFyYW1ldGVyLFxuXHRcdFx0aXNNdXRhYmxlICAgICA6IG9wdGlvbnMuaXNNdXRhYmxlLFxuXHRcdFx0cmVhc3NpZ25tZW50cyA6IFtdLFxuXHRcdH07XG5cdFx0Y29uc3QgaW5mZXJyZWQgPSBvcHRpb25zLmFubm90YXRpb24gPz8gKFxuXHRcdFx0b3B0aW9ucy5pbml0aWFsaXplciA/IExvY2FsU2NvcGVXYWxrZXIuaW5mZXJJbml0aWFsaXplcktpbmQob3B0aW9ucy5pbml0aWFsaXplcikgOiB1bmRlZmluZWRcblx0XHQpO1xuXHRcdGlmIChpbmZlcnJlZCkge1xuXHRcdFx0dmFyaWFibGUuaW5mZXJyZWRUeXBlID0gaW5mZXJyZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcGVuZGluZ0VudHJ5OiBQZW5kaW5nVmFyaWFibGUgPSB7XG5cdFx0XHR2YXJpYWJsZSxcblx0XHRcdHNjb3BlQ2hhaW4gOiBbIC4uLnNjb3BlU3RhY2sgXS5yZXZlcnNlKCksXG5cdFx0XHRhbm5vdGF0aW9uIDogb3B0aW9ucy5hbm5vdGF0aW9uLFxuXHRcdH07XG5cdFx0Y29uc3QgeyBpbml0aWFsaXplciB9ID0gb3B0aW9ucztcblx0XHRpZiAoaW5pdGlhbGl6ZXIgJiYgdHMuaXNOZXdFeHByZXNzaW9uKGluaXRpYWxpemVyKSkge1xuXHRcdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBpbml0aWFsaXplcjtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0cGVuZGluZ0VudHJ5Lm5ld05hbWUgPSBleHByZXNzaW9uLnRleHQ7XG5cdFx0XHR9IGVsc2UgaWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IGNoYWluID0gTG9jYWxTY29wZVdhbGtlci51bndyYXBQcm9wZXJ0eUFjY2VzcyhleHByZXNzaW9uKTtcblx0XHRcdFx0aWYgKGNoYWluLmxlbmd0aCA+IDEpIHtcblx0XHRcdFx0XHRjb25zdCBbIHJvb3QsIC4uLnJlc3QgXSA9IGNoYWluO1xuXHRcdFx0XHRcdHBlbmRpbmdFbnRyeS5uZXdDaGFpblJvb3QgPSByb290O1xuXHRcdFx0XHRcdHBlbmRpbmdFbnRyeS5uZXdDaGFpblJlc3QgPSByZXN0O1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGlmIChpbml0aWFsaXplciAmJiB0cy5pc0NhbGxFeHByZXNzaW9uKGluaXRpYWxpemVyKSkge1xuXHRcdFx0Y29uc3QgbG9va3VwID0gTG9jYWxTY29wZVdhbGtlci51bndyYXBMb29rdXBDYWxsKGluaXRpYWxpemVyKTtcblx0XHRcdGlmIChsb29rdXApIHtcblx0XHRcdFx0cGVuZGluZ0VudHJ5Lmxvb2t1cFBhdGggPSBsb29rdXAucGF0aDtcblx0XHRcdFx0cGVuZGluZ0VudHJ5Lmxvb2t1cFJlY2VpdmVyID0gbG9va3VwLnJlY2VpdmVyO1xuXHRcdFx0XHRwZW5kaW5nRW50cnkubG9va3VwQ2FsbCA9IGluaXRpYWxpemVyO1xuXHRcdFx0fVxuXHRcdH1cblx0XHR0aGlzLnBlbmRpbmcucHVzaChwZW5kaW5nRW50cnkpO1xuXHRcdHRoaXMudmFyaWFibGVzLnNldChgJHtzY29wZUlkfSMke25hbWV9YCwgdmFyaWFibGUpO1xuXHR9XG5cblx0LyoqXG5cdCAqIGBhLmIuY2Ag4oaSIFsnYScsICdiJywgJ2MnXSAobGVmdC10by1yaWdodCk7IHVuZGVmaW5lZC1zYWZlIGZvclxuXHQgKiBub24taWRlbnRpZmllciByb290cy5cblx0ICovXG5cdHByaXZhdGUgc3RhdGljIHVud3JhcFByb3BlcnR5QWNjZXNzIChleHByZXNzaW9uOiB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24pOiBzdHJpbmdbXSB7XG5cdFx0Y29uc3QgY2hhaW46IHN0cmluZ1tdID0gW107XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLkV4cHJlc3Npb24gPSBleHByZXNzaW9uO1xuXHRcdHdoaWxlICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0Y2hhaW4udW5zaGlmdChjdXJyZW50Lm5hbWUudGV4dCk7XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5leHByZXNzaW9uO1xuXHRcdH1cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQpKSB7XG5cdFx0XHRjaGFpbi51bnNoaWZ0KGN1cnJlbnQudGV4dCk7XG5cdFx0fVxuXHRcdHJldHVybiBjaGFpbjtcblx0fVxuXG5cdC8qKlxuXHQgKiBgbG9va3VwKCdBLkInKWAsIGBBcHAubG9va3VwKCdBLkInKWAsIGBsb29rdXAoc291cmNlLCAnQS5CJylgIOKGkiB0aGVcblx0ICogc3RyaW5nLWxpdGVyYWwgcGF0aCBwbHVzIHRoZSByZWNlaXZlcidzIHJvb3QgaWRlbnRpZmllciB3aGVuIHRoZXJlIGlzXG5cdCAqIG9uZS4gT25seSBsaXRlcmFsIHBhdGhzIGFyZSB0cmFja2VkOiBhIGNvbXB1dGVkIHBhdGggaXMgZGF0YSB0aGUgc3RhdGljXG5cdCAqIHdhbGtlciBjYW5ub3QgZm9sbG93LCBzbyBpdCBpcyBza2lwcGVkICh0aGUgYW5hbHl6ZXIncyB1c2FnZSBwYXNzIHN0aWxsXG5cdCAqIHJlY29yZHMgdGhlIGxvb2t1cCBjYWxsIGl0c2VsZikuXG5cdCAqL1xuXHRwcml2YXRlIHN0YXRpYyB1bndyYXBMb29rdXBDYWxsIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHsgcGF0aDogc3RyaW5nOyByZWNlaXZlcj86IHN0cmluZyB9IHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IGNhbGw7XG5cdFx0Y29uc3QgWyBmaXJzdEFyZywgc2Vjb25kQXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikpIHtcblx0XHRcdGlmIChleHByZXNzaW9uLnRleHQgIT09ICdsb29rdXAnKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBsb29rdXAoJ0EuQicpXG5cdFx0XHRpZiAoZmlyc3RBcmcgJiYgdHMuaXNTdHJpbmdMaXRlcmFsTGlrZShmaXJzdEFyZykpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0ID0geyBwYXRoIDogZmlyc3RBcmcudGV4dCB9O1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0Ly8gbG9va3VwKHNvdXJjZSwgJ0EuQicpIOKAlCBleHBsaWNpdC1zb3VyY2UgZm9ybVxuXHRcdFx0aWYgKGZpcnN0QXJnICYmIHRzLmlzSWRlbnRpZmllcihmaXJzdEFyZykgJiYgc2Vjb25kQXJnICYmIHRzLmlzU3RyaW5nTGl0ZXJhbExpa2Uoc2Vjb25kQXJnKSkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQgPSB7IHBhdGggOiBzZWNvbmRBcmcudGV4dCwgcmVjZWl2ZXIgOiBmaXJzdEFyZy50ZXh0IH07XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLm5hbWUudGV4dCA9PT0gJ2xvb2t1cCcpIHtcblx0XHRcdGlmICghZmlyc3RBcmcgfHwgIXRzLmlzU3RyaW5nTGl0ZXJhbExpa2UoZmlyc3RBcmcpKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBjaGFpbiA9IExvY2FsU2NvcGVXYWxrZXIudW53cmFwUHJvcGVydHlBY2Nlc3MoZXhwcmVzc2lvbik7XG5cdFx0XHQvLyBjaGFpbiA8IDIgbWVhbnMgbm8gaWRlbnRpZmllciByZWNlaXZlciAoZS5nLiB0aGlzLmxvb2t1cCgnQS5CJykpXG5cdFx0XHRpZiAoY2hhaW4ubGVuZ3RoIDwgMikge1xuXHRcdFx0XHRjb25zdCBwYXRoT25seSA9IHsgcGF0aCA6IGZpcnN0QXJnLnRleHQgfTtcblx0XHRcdFx0cmV0dXJuIHBhdGhPbmx5O1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgWyByZWNlaXZlciBdID0gY2hhaW47XG5cdFx0XHRjb25zdCByZXN1bHQgPSB7IHBhdGggOiBmaXJzdEFyZy50ZXh0LCByZWNlaXZlciB9O1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWFwIGluaXRpYWxpemVyIGNsYXNzaWZpY2F0aW9uIGZvciBpbmZlcnJlZFR5cGUuIERlbGliZXJhdGVseSB0aW55OlxuXHQgKiBsaXRlcmFsIGtpbmRzIGFuZCBgbmV3IFhgIGNvbnN0cnVjdG9yIG5hbWVzOyBldmVyeXRoaW5nIGVsc2UgdW5kZWZpbmVkLlxuXHQgKi9cblx0cHJpdmF0ZSBzdGF0aWMgaW5mZXJJbml0aWFsaXplcktpbmQgKGluaXRpYWxpemVyOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsTGlrZShpbml0aWFsaXplcikgfHwgdHMuaXNUZW1wbGF0ZUV4cHJlc3Npb24oaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0fVxuXHRcdGlmICh0cy5pc051bWVyaWNMaXRlcmFsKGluaXRpYWxpemVyKSkge1xuXHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdH1cblx0XHRpZiAoaW5pdGlhbGl6ZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCB8fCBpbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHR9XG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihpbml0aWFsaXplcikgfHwgdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRyZXR1cm4gJ2Z1bmN0aW9uJztcblx0XHR9XG5cdFx0aWYgKHRzLmlzQXJyYXlMaXRlcmFsRXhwcmVzc2lvbihpbml0aWFsaXplcikpIHtcblx0XHRcdHJldHVybiAnQXJyYXk8dW5rbm93bj4nO1xuXHRcdH1cblx0XHRpZiAodHMuaXNOZXdFeHByZXNzaW9uKGluaXRpYWxpemVyKSAmJiB0cy5pc0lkZW50aWZpZXIoaW5pdGlhbGl6ZXIuZXhwcmVzc2lvbikpIHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGluaXRpYWxpemVyLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVhc3NpZ25tZW50IG9mIGEgbGV0L3Zhci9wYXJhbWV0ZXIgYmluZGluZzogYSBmbG93LXRlcm1pbmF0aW9uIHBvaW50XG5cdCAqIChkZWNpc2lvbiA2KS4gUmVjb3JkZWQgb24gdGhlIHZhcmlhYmxlIHNvIHRoZSBQaGFzZSAzIHdhbGtlciBzdG9wc1xuXHQgKiBmb2xsb3dpbmcgdGhhdCBiaW5kaW5nIHRoZXJlLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0UmVhc3NpZ25tZW50IChcblx0XHRub2RlOiB0cy5Ob2RlLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0c2NvcGVTdGFjazogc3RyaW5nW11cblx0KTogdm9pZCB7XG5cdFx0bGV0IHRhcmdldDogdHMuSWRlbnRpZmllciB8IHVuZGVmaW5lZDtcblx0XHRpZiAodHMuaXNCaW5hcnlFeHByZXNzaW9uKG5vZGUpICYmXG5cdFx0XHRBU1NJR05NRU5UX09QRVJBVE9SUy5oYXMobm9kZS5vcGVyYXRvclRva2VuLmtpbmQpICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIobm9kZS5sZWZ0KSkge1xuXHRcdFx0dGFyZ2V0ID0gbm9kZS5sZWZ0O1xuXHRcdH1cblx0XHRpZiAoKHRzLmlzUHJlZml4VW5hcnlFeHByZXNzaW9uKG5vZGUpIHx8IHRzLmlzUG9zdGZpeFVuYXJ5RXhwcmVzc2lvbihub2RlKSkgJiZcblx0XHRcdChub2RlLm9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLlBsdXNQbHVzVG9rZW4gfHwgbm9kZS5vcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5NaW51c01pbnVzVG9rZW4pICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIobm9kZS5vcGVyYW5kKSkge1xuXHRcdFx0dGFyZ2V0ID0gbm9kZS5vcGVyYW5kO1xuXHRcdH1cblx0XHRpZiAoIXRhcmdldCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHQvLyBOb3RlOiBhIGRlY2xhcmF0aW9uIGluaXRpYWxpemVyIChgbGV0IHggPSA1YCkgaXMgYSBWYXJpYWJsZURlY2xhcmF0aW9uLFxuXHRcdC8vIG5ldmVyIGEgQmluYXJ5RXhwcmVzc2lvbiwgc28gaXQgY2Fubm90IHJlYWNoIHRoaXMgcGF0aCBhcyBhIFwicmVhc3NpZ25tZW50XCJcblxuXHRcdGNvbnN0IHZhcmlhYmxlID0gdGhpcy5maW5kVmFyaWFibGUodGFyZ2V0LnRleHQsIHNjb3BlU3RhY2spO1xuXHRcdGlmICghdmFyaWFibGUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLnJlc29sdmUoc291cmNlRmlsZS5maWxlTmFtZSk7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHNvdXJjZUZpbGUuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24odGFyZ2V0LmdldFN0YXJ0KHNvdXJjZUZpbGUpKTtcblx0XHR2YXJpYWJsZS5yZWFzc2lnbm1lbnRzLnB1c2goYCR7ZmlsZVBhdGh9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBGaW5kIGEgdmFyaWFibGUgYnkgbmFtZSB3YWxraW5nIHRoZSBzY29wZSBjaGFpbiBvdXR3YXJkLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kVmFyaWFibGUgKG5hbWU6IHN0cmluZywgc2NvcGVTdGFjazogc3RyaW5nW10pOiBTY29wZVZhcmlhYmxlIHwgdW5kZWZpbmVkIHtcblx0XHRmb3IgKGxldCBpID0gc2NvcGVTdGFjay5sZW5ndGggLSAxOyBpID49IDA7IGktLSkge1xuXHRcdFx0Y29uc3QgdmFyaWFibGUgPSB0aGlzLnZhcmlhYmxlcy5nZXQoYCR7c2NvcGVTdGFja1sgaSBdfSMke25hbWV9YCk7XG5cdFx0XHRpZiAodmFyaWFibGUpIHtcblx0XHRcdFx0cmV0dXJuIHZhcmlhYmxlO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0cHJpdmF0ZSByZXNvbHZlVmFyaWFibGVUeXBlUGF0aCAoZW50cnk6IFBlbmRpbmdWYXJpYWJsZSwgcmVzb2x2ZXI6IFNjb3BlVHlwZVJlc29sdmVyKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBgbmV3IFNvbWVUeXBlKC4uLilgIOKAlCBiYXJlIGNvbnN0cnVjdG9yIG5hbWVcblx0XHRpZiAoZW50cnkubmV3TmFtZSkge1xuXHRcdFx0Y29uc3QgcmVzb2x2ZWQgPSByZXNvbHZlci5yZXNvbHZlQnlOYW1lKGVudHJ5Lm5ld05hbWUpO1xuXHRcdFx0aWYgKHJlc29sdmVkKSB7XG5cdFx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBgbmV3IGluc3RhbmNlLlN1Yi5UeXBlKC4uLilgIOKAlCBjaGFpbiBvZmYgYSB0cmFja2VkIHZhcmlhYmxlJ3MgdHlwZVBhdGhcblx0XHRpZiAoZW50cnkubmV3Q2hhaW5Sb290ICYmIGVudHJ5Lm5ld0NoYWluUmVzdCAmJiBlbnRyeS5uZXdDaGFpblJlc3QubGVuZ3RoID4gMCkge1xuXHRcdFx0Zm9yIChjb25zdCBzY29wZUlkIG9mIGVudHJ5LnNjb3BlQ2hhaW4pIHtcblx0XHRcdFx0Y29uc3Qgcm9vdFZhcmlhYmxlID0gdGhpcy52YXJpYWJsZXMuZ2V0KGAke3Njb3BlSWR9IyR7ZW50cnkubmV3Q2hhaW5Sb290fWApO1xuXHRcdFx0XHRpZiAoIXJvb3RWYXJpYWJsZT8udHlwZVBhdGgpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBjYW5kaWRhdGUgPSBbIHJvb3RWYXJpYWJsZS50eXBlUGF0aCwgLi4uZW50cnkubmV3Q2hhaW5SZXN0IF0uam9pbignLicpO1xuXHRcdFx0XHRpZiAocmVzb2x2ZXIuaGFzUGF0aChjYW5kaWRhdGUpKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGNhbmRpZGF0ZTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIGBsb29rdXAoJ0EuQicpYCAvIGByZWNlaXZlci5sb29rdXAoJ0EuQicpYCBpbml0aWFsaXplcnNcblx0XHRpZiAoZW50cnkubG9va3VwUGF0aCkge1xuXHRcdFx0Ly8gUmVjZWl2ZXItcmVsYXRpdmUgZmlyc3Q6IGB1c2VyLmxvb2t1cCgnQWRtaW5FbnRpdHknKWAgcmVzb2x2ZXNcblx0XHRcdC8vIGFnYWluc3QgdGhlIHJlY2VpdmVyIHZhcmlhYmxlJ3MgdHlwZVBhdGggd2hlbiB0aGF0IHlpZWxkcyBhXG5cdFx0XHQvLyBrbm93biBwYXRoICh2YWx1ZS1zY29wZSB0aWVyIOKAlCBpbm5lcm1vc3QgYmluZGluZyB3aW5zKVxuXHRcdFx0aWYgKGVudHJ5Lmxvb2t1cFJlY2VpdmVyKSB7XG5cdFx0XHRcdGZvciAoY29uc3Qgc2NvcGVJZCBvZiBlbnRyeS5zY29wZUNoYWluKSB7XG5cdFx0XHRcdFx0Y29uc3QgcmVjZWl2ZXJWYXJpYWJsZSA9IHRoaXMudmFyaWFibGVzLmdldChgJHtzY29wZUlkfSMke2VudHJ5Lmxvb2t1cFJlY2VpdmVyfWApO1xuXHRcdFx0XHRcdGlmICghcmVjZWl2ZXJWYXJpYWJsZT8udHlwZVBhdGgpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCBjYW5kaWRhdGUgPSBgJHtyZWNlaXZlclZhcmlhYmxlLnR5cGVQYXRofS4ke2VudHJ5Lmxvb2t1cFBhdGh9YDtcblx0XHRcdFx0XHRpZiAocmVzb2x2ZXIuaGFzUGF0aChjYW5kaWRhdGUpKSB7XG5cdFx0XHRcdFx0XHRyZXR1cm4gY2FuZGlkYXRlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gVGhlIGFuYWx5emVyJ3MgdGllciBsYXcgYWJvdmUgdmFsdWUgc2NvcGUgKGltcG9ydCBzY29wZSxcblx0XHRcdC8vIHNvdXJjZS1yZWxhdGl2ZSwgcm9vdCk6IGFuIGltcG9ydGVkIGBIb2xkZXIubG9va3VwKCdUb2tlbicpYFxuXHRcdFx0Ly8gb3IgYGxvb2t1cChBcHAsICdDcmF0ZScpYCByZXNvbHZlcyBleGFjdGx5IGFzIHRoZSB1c2FnZXMgcGFzc1xuXHRcdFx0Ly8gcmVzb2x2ZWQgaXQsIHNvIHNjb3Blcy5qc29uIGFncmVlcyB3aXRoIHRoZSBoYXJkLWZhaWwgdmVyZGljdHNcblx0XHRcdGlmIChyZXNvbHZlci5yZXNvbHZlTG9va3VwICYmIGVudHJ5Lmxvb2t1cENhbGwpIHtcblx0XHRcdFx0Y29uc3QgcmVzb2x2ZWQgPSByZXNvbHZlci5yZXNvbHZlTG9va3VwKGVudHJ5Lmxvb2t1cENhbGwpO1xuXHRcdFx0XHRpZiAocmVzb2x2ZWQgJiYgcmVzb2x2ZXIuaGFzUGF0aChyZXNvbHZlZCkpIHtcblx0XHRcdFx0XHRyZXR1cm4gcmVzb2x2ZWQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGlmIChyZXNvbHZlci5oYXNQYXRoKGVudHJ5Lmxvb2t1cFBhdGgpKSB7XG5cdFx0XHRcdHJldHVybiBlbnRyeS5sb29rdXBQYXRoO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgYnlOYW1lID0gcmVzb2x2ZXIucmVzb2x2ZUJ5TmFtZShlbnRyeS5sb29rdXBQYXRoKTtcblx0XHRcdGlmIChieU5hbWUpIHtcblx0XHRcdFx0cmV0dXJuIGJ5TmFtZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBUeXBlIGFubm90YXRpb246ICdVc2VyRW50aXR5X1VzZXJSZXNwb25zZScgKHRhY3RpY2EgdHlwZXMudHMgbmFtaW5nKVxuXHRcdC8vIOKGkiBkb3R0ZWQgcGF0aCwgb3IgYSBiYXJlIGtub3duIHR5cGUgbmFtZVxuXHRcdGlmIChlbnRyeS5hbm5vdGF0aW9uKSB7XG5cdFx0XHRjb25zdCBkb3R0ZWQgPSBlbnRyeS5hbm5vdGF0aW9uLnJlcGxhY2UoL18vZywgJy4nKTtcblx0XHRcdGlmIChkb3R0ZWQuaW5jbHVkZXMoJy4nKSAmJiByZXNvbHZlci5oYXNQYXRoKGRvdHRlZCkpIHtcblx0XHRcdFx0cmV0dXJuIGRvdHRlZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGJ5TmFtZSA9IHJlc29sdmVyLnJlc29sdmVCeU5hbWUoZW50cnkuYW5ub3RhdGlvbik7XG5cdFx0XHRpZiAoYnlOYW1lKSB7XG5cdFx0XHRcdHJldHVybiBieU5hbWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxufVxuIl19