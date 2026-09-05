import * as ts from 'typescript';
import { ScopeAnalysis, UsageInfo } from './types';
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
export declare class LocalScopeWalker {
    private scopes;
    private spans;
    private variables;
    private pending;
    /**
     * Arrow/function-expression node -> name it is bound to (`const f = () => …`,
     * `{ handler: () => … }`, class properties). Program source files can be
     * UNBOUND (no node.parent pointers), so binding names travel through this
     * map instead of parent lookups.
     */
    private boundNames;
    /**
     * Track one source file. Re-adding the same file replaces its records,
     * so a walker may safely be reused across passes.
     */
    addFile(sourceFile: ts.SourceFile): void;
    /**
     * Resolve pending typePaths and return the analysis.
     */
    build(resolver?: ScopeTypeResolver): ScopeAnalysis;
    /**
     * Map a usage location string ('abs/file.ts:line:col') to the innermost
     * scope containing it. Module scope is the fallback, so every location
     * inside a tracked file resolves to some scope.
     */
    findHolderScopeId(location: string): string | undefined;
    /**
     * Remove every record belonging to one file (re-add support).
     */
    private dropFile;
    /**
     * Attach holderScopeId to every usage whose location falls inside a
     * tracked scope. Additive on UsageInfo; usages outside tracked files
     * are left untouched.
     */
    static attachHolderScopeIds(usages: Map<string, UsageInfo[]>, walker: LocalScopeWalker): void;
    private visitNode;
    private static scopeKindOf;
    private hasBody;
    private enterScope;
    /**
     * Decision 8 labeling: functions by name; methods as Class.method;
     * arrows/functions bound to a variable or property take that name;
     * anonymous holders are labeled file:line.
     */
    private scopeName;
    private spanOf;
    /**
     * Record the name an arrow/function-expression is bound to, without
     * relying on node.parent (unbound program files): `const f = () => …`,
     * `{ handler: () => … }`, `class C { run = () => … }`.
     */
    private collectBoundName;
    private collectVariableDeclarationList;
    private recordVariable;
    /**
     * `a.b.c` → ['a', 'b', 'c'] (left-to-right); undefined-safe for
     * non-identifier roots.
     */
    private static unwrapPropertyAccess;
    /**
     * `lookup('A.B')`, `App.lookup('A.B')`, `lookup(source, 'A.B')` → the
     * string-literal path plus the receiver's root identifier when there is
     * one. Only literal paths are tracked: a computed path is data the static
     * walker cannot follow, so it is skipped (the analyzer's usage pass still
     * records the lookup call itself).
     */
    private static unwrapLookupCall;
    /**
     * Cheap initializer classification for inferredType. Deliberately tiny:
     * literal kinds and `new X` constructor names; everything else undefined.
     */
    private static inferInitializerKind;
    /**
     * Reassignment of a let/var/parameter binding: a flow-termination point
     * (decision 6). Recorded on the variable so the Phase 3 walker stops
     * following that binding there.
     */
    private collectReassignment;
    /**
     * Find a variable by name walking the scope chain outward.
     */
    private findVariable;
    private resolveVariableTypePath;
}
