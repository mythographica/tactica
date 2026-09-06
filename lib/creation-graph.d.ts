import * as ts from 'typescript';
import { LocalScopeWalker } from './scopes';
import { CreationGraph, ModuleGraph, ScopeAnalysis, UsageInfo } from './types';
/**
 * Inside-out creation walker (instrumentation walker plan, Phase 3).
 *
 * Starts at the certain points — instantiation usages carrying a
 * holderScopeId — then walks OUTWARD: who invokes or references the holder,
 * crossing files through the module graph (barrels chased the same way
 * ModuleGraphBuilder.resolveOrigin does), until no callers remain. Terminals
 * are the starters (application entry points). The walk never assumes a
 * linear Trie (decision 1: strictChain:false permits cycles/out-of-order
 * construction), so traversal is cycle-guarded DFS, and every anchor records
 * which constructor expression was actually used.
 *
 * Deliberate approximations (no getTypeChecker(), name-based only):
 * - Namespace imports (`import * as ns`): when the namespace's source module
 *   exposes the holder's export, ANY reference to the alias counts as a
 *   caller reference.
 * - Method scopes bind to their CLASS name (callers reference the class);
 *   instance-method call sites (`obj.method()`) are not distinguishable
 *   without the checker.
 * - Any non-declaration identifier counts as a reference (invocations,
 *   pass-as-arg, rebinding); type-position references are not filtered.
 * - Module scopes end the invocation walk, but a terminal module still
 *   gains its IMPORTERS as callers: entry modules hand classes to the
 *   framework as values (a bootstrap call receiving the root module),
 *   which no call-walk can see — the import relation bridges them to
 *   the center.
 */
export declare class CreationGraphBuilder {
    private moduleGraph;
    private scopeAnalysis;
    private scopeWalker;
    /** Keyed by path.resolve(sourceFile.fileName), matching scopeIds */
    private sourceFiles;
    /** filePath -> (identifier text -> reference locations), built lazily per file */
    private referencesByFile;
    constructor(moduleGraph: ModuleGraph, scopeAnalysis: ScopeAnalysis, scopeWalker: LocalScopeWalker, sourceFiles: Map<string, ts.SourceFile>);
    /**
     * Build the creation graph from the analyzer's usages (holderScopeId
     * already attached). Always returns a graph, empty arrays when nothing
     * creates mnemonica instances.
     */
    build(usages: Map<string, UsageInfo[]>): CreationGraph;
    /**
     * One anchor per instantiation usage with a known holder scope.
     */
    private collectAnchors;
    /**
     * Same-line heuristic for the anchor's variable: the variable declared in
     * the holder scope on the same line as the creation, whose typePath (when
     * known) matches the created type.
     */
    private matchAnchorVariable;
    /**
     * Parse the 1-based line out of a file.ts:Line:Col location string.
     */
    private static lineOf;
    private static nodeOf;
    /**
     * The name a scope is reachable by: functions/arrows take their scope
     * name; methods take their class (the part before '.') — that is what
     * callers reference. Anonymous holders (file:line labels) and module
     * scopes have no binding name.
     */
    private static bindingNameOf;
    /**
     * Scope ids referencing `bindingName` inside one file (invocations,
     * pass-as-arg, rebindings — any non-declaration identifier).
     */
    private callersOf;
    /**
     * Callers in OTHER modules, followed through the module graph when the
     * holder's binding is exported (the plan's "if f is exported" branch,
     * including the barrel chase).
     */
    private findCrossFileCallers;
    /**
     * Modules importing bindings whose ORIGIN is `filePath` — the
     * exports-and-usage bridge for terminal module scopes. Any binding kind
     * counts (named, default, re-export): resolveImportOrigin chases barrels
     * to the declaring module; namespace imports and external packages never
     * resolve, so neither connects. Returned as module-scope scopeIds — a
     * module's scopeId IS its resolved filePath.
     */
    private importersOf;
    /**
     * The local identifier an import binding presents for reference search,
     * when the binding resolves to the holder's export — undefined otherwise.
     */
    private importReferencesHolder;
    /**
     * True when a namespace import's source module exposes `exportedName`
     * whose origin is the holder's module. Expressed as resolving a synthetic
     * named binding, so star barrels and named re-exports are chased by the
     * same machinery as plain imports.
     */
    private namespaceExposes;
    /**
     * Chase an import binding to the module that actually declares it,
     * following re-export chains (barrels). Same shape as
     * ModuleGraphBuilder.resolveOrigin, run here over the BUILT graph
     * (sourceModule values are already resolved absolute paths).
     * Cycle-guarded; undefined when the origin is external or the chain loops.
     */
    private resolveImportOrigin;
    /**
     * All references to `name` in a file as location strings. The per-file
     * index is built lazily in ONE pass (every identifier bucketed by text)
     * and cached.
     */
    private referencesIn;
    /**
     * Bucket every identifier reference by name. Declaration and wiring
     * positions are NOT references: import/export specifiers, declaration
     * names, property-access `.name`, and property-assignment keys go into a
     * skip set of NODES — program files can be unbound, so parent-pointer
     * checks are impossible (the scopes walker precedent, Phase 2).
     * ShorthandPropertyAssignment names DO count: `{ foo }` is a genuine
     * reference to foo.
     */
    private static collectReferences;
    /**
     * Register the identifier nodes that must NOT count as references when
     * `node` is a wiring/declaration construct. Runs on the parent before
     * descending, so the skip set is populated before the identifier nodes
     * themselves are visited.
     */
    private static registerSkips;
}
