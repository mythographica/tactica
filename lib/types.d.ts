/**
 * Type definitions for Tactica
 */
export interface TacticaConfig {
    /** Output directory for generated types (default: .tactica) */
    outputDir?: string;
    /** Files to include (glob patterns) */
    include?: string[];
    /** Files to exclude (glob patterns) */
    exclude?: string[];
    /** Enable verbose logging */
    verbose?: boolean;
    /** Generate global augmentation instead of module augmentation (default: true) */
    globalAugmentation?: boolean;
}
export interface PropertyInfo {
    name: string;
    type: string;
    optional: boolean;
    /** True if this is a getter property (readonly) */
    readonly?: boolean;
}
/** Constructor parameter info for TypeRegistry signatures */
export interface ConstructorParamInfo {
    /** Parameter name (e.g., "usages", "data", "config") */
    name: string;
    /** The type string - can be a simple type or expanded object literal */
    type: string;
    optional: boolean;
}
export interface TypeNode {
    /** Type name (e.g., "SecondType") */
    name: string;
    /** Full path (e.g., "FirstType.SecondType") */
    fullPath: string;
    /** Properties defined in this type's constructor */
    properties: Map<string, PropertyInfo>;
    /** Constructor parameters (for TypeRegistry constructor signature) */
    constructorParams?: ConstructorParamInfo[];
    /** Parent type node */
    parent?: TypeNode;
    /** Child types */
    children: Map<string, TypeNode>;
    /** Source file path */
    sourceFile: string;
    /** Line number in source */
    line: number;
    /** Column number in source */
    column: number;
    /** Constructor function name or class name */
    constructorName?: string;
    /** Collection identifier if the type belongs to a custom collection (undefined = default/global registry) */
    collectionId?: string;
    /** Registry interface name for custom collections using Option B (user-provided registry interface) */
    registryInterfaceName?: string;
}
export interface TypeGraph {
    /** Root types, keyed by full path (custom-collection roots carry the `collectionId::` prefix) */
    roots: Map<string, TypeNode>;
    /** All types by full path */
    allTypes: Map<string, TypeNode>;
    /** Add a root type */
    addRoot(node: TypeNode): void;
    /** Find a type by full path */
    findType(fullPath: string): TypeNode | undefined;
    /** Get all types as array */
    getAllTypes(): TypeNode[];
    /** Clear the graph */
    clear(): void;
}
export interface AnalyzeResult {
    /** Types found in the analysis */
    types: TypeNode[];
    /** Errors encountered */
    errors: AnalyzeError[];
}
export interface AnalyzeError {
    message: string;
    file: string;
    line: number;
    column: number;
}
export interface GeneratedTypes {
    /** Content of the .d.ts file */
    content: string;
    /** Types that were generated */
    types: string[];
}
/**
 * Definition info for code navigation
 */
export interface DefinitionInfo {
    /** Type name (e.g., "AdminType") */
    name: string;
    /** Location in source: file.ts:Line:Col */
    location: string;
    /** How type was created: 'define' or 'decorate' */
    kind: 'define' | 'decorate';
    /** Parent type full path, null if root */
    parent: string | null;
    /** strictChain config option */
    strictChain: boolean;
    /** blockErrors config option */
    blockErrors: boolean;
}
/**
 * Usage info for code navigation
 */
export interface UsageInfo {
    /** Location in source: file.ts:Line:Col */
    location: string;
    /** Kind of usage: instantiation, typeAnnotation, propertyAccess, lookup, reference */
    kind: 'instantiation' | 'typeAnnotation' | 'propertyAccess' | 'lookup' | 'reference';
    /** Code snippet */
    code: string;
    /**
     * Scope holding this usage (LocalScopeWalker scopeId: module scope is the
     * file path, function scopes are file:line:col). Additive; absent when the
     * usage sits outside tracked files.
     */
    holderScopeId?: string;
    /**
     * Constructor expression text at an instantiation site ('Thing',
     * 'user.AdminEntity', 'T2' for a lookup alias). Additive; set only on
     * kind 'instantiation'. Feeds CreationAnchor.constructorText (Phase 3).
     */
    constructorText?: string;
}
/**
 * JSON output for definitions.json
 */
export interface DefinitionsJson {
    version: string;
    generatedAt: string;
    definitions: Record<string, DefinitionInfo>;
}
/**
 * JSON output for usages.json
 */
export interface UsagesJson {
    version: string;
    generatedAt: string;
    usages: Record<string, UsageInfo[]>;
}
/**
 * EDS (Execution Data Storage) kind for tracking execution flow patterns
 */
export type EDSKind = 'wrap' | 'contextConsume' | 'hookAttach';
/**
 * EDS info for execution data flow tracking
 */
export interface EDSInfo {
    /** Location in source: file.ts:Line:Col */
    location: string;
    /** Kind of EDS usage */
    kind: EDSKind;
    /** Code snippet */
    code: string;
    /** Resolved target type if detectable */
    targetType?: string;
    /** Enclosing mnemonica type path (define/lazy handler or decorated class) */
    scope?: string;
    /** Location of the enclosing wrap site whose runtime wrapping caused this entry */
    via?: string;
    /** Mnemonica type fullPaths instantiated inside the wrapped body — guaranteed path hits */
    createsTypes?: string[];
    /** Label string literal passed to wrap(fn, …, 'label') when statically visible */
    label?: string;
    /** scopeId (scopes.json) of the wrapped callback's own scope — joins to the creation graph */
    callbackScopeId?: string;
    /** Identifier passed as the instance/context argument ('user'), when it is one */
    instanceArg?: string;
    /** scopeId of the scope holding the wrap call site — joins to the creation graph */
    scopeId?: string;
    /** Mnemonica fullPath of the instance argument, resolved through scope variables */
    wrapsTypePath?: string;
    /** Wrap-family function name ('wrap' | 'wrapConstructorArg' | …) — joins the
     *  call site to dive's engine knot in graph consumers */
    fn?: string;
}
/**
 * JSON output for eds.json
 */
export interface EDSJson {
    version: string;
    generatedAt: string;
    eds: Record<string, EDSInfo[]>;
}
/**
 * Instrumentation kind for framework lifecycle crossroads
 */
export type InstrumentationKind = 'interceptor' | 'guard' | 'pipe' | 'filter' | 'middleware';
/**
 * Instrumentation scope: where the point attaches.
 * 'global' for provider-token registrations, 'module' for middleware wired
 * via consumer.apply() AND for bare heritage declarations whose attachment
 * is statically unknown, `controller:Name` / `method:Class.method` for
 * decorator-scoped attachments.
 */
export type InstrumentationScope = 'global' | 'module' | `controller:${string}` | `method:${string}`;
/**
 * Instrumentation point: a framework lifecycle crossroad (interceptor,
 * guard, pipe, filter, middleware) detected syntactically. The vocabulary
 * that turns a syntactic shape into a point comes from plugins — with no
 * plugin loaded, no points are collected.
 *
 * Dedupe/scope decision: points are keyed by (kind, className, location,
 * scope) and duplicates merge their `targets`. A class detected both by
 * heritage (a plugin-listed `implements` interface) and by a decorator
 * site yields SEPARATE entries — the class-declaration point keeps scope
 * 'module' (attachment unknown) while each registration site carries its
 * own scope. One point serving multiple scopes via merged scope lists was
 * rejected: consumers (mnemographica diamonds) key off a single scope per
 * point, and separate entries keep that contract simple.
 */
export interface InstrumentationPoint {
    /** Kind of lifecycle crossroad */
    kind: InstrumentationKind;
    /** Class providing the instrumentation (e.g., "AuthGuard") */
    className: string;
    /** Location in source: file.ts:Line:Col (class declaration when declared in-project, else the registration site) */
    location: string;
    /** Code snippet: signature / first line, like EDS `code` */
    code: string;
    /** Where the point attaches */
    scope: InstrumentationScope;
    /** Controller/provider names the point attaches to; empty for global points */
    targets: string[];
}
/**
 * JSON output for instrumentation.json
 */
export interface InstrumentationJson {
    /** Schema version: 2 adds the optional creationGraph key (Phase 3) */
    version: number;
    generatedAt: string;
    points: InstrumentationPoint[];
    /**
     * Inside-out creation walk (instrumentation walker plan, Phase 3): which
     * scopes create mnemonica instances and who calls them, walked outward to
     * the starters. Absent when the writer is called without creation-graph
     * data (direct library use); always present from the CLI.
     */
    creationGraph?: CreationGraph;
}
/**
 * Flow kind for tracking native instance usage patterns
 */
export type FlowKind = 'propertyRead' | 'propertyWrite' | 'methodCall' | 'destructureRead' | 'passAsArg' | 'return' | 'spread' | 'arrayElement' | 'conditionalAccess' | 'elementAccess' | 'reassignment' | 'instantiation';
/**
 * Flow info for native instance usage tracking
 */
export interface FlowInfo {
    /** Location in source: file.ts:Line:Col */
    location: string;
    /** Kind of flow */
    kind: FlowKind;
    /** Code snippet */
    code: string;
    /** Property name if applicable */
    propertyName?: string;
    /** Resolved target type if known */
    targetType?: string;
    /** Context (function name, param position, etc.) */
    context?: string;
}
/**
 * JSON output for flow.json
 */
export interface FlowJson {
    version: string;
    generatedAt: string;
    flow: Record<string, FlowInfo[]>;
}
/**
 * What a module-level binding is. Variables are classified as 'const'
 * regardless of let/var — mutability (reassignment tracking) is the
 * local-scope walker's concern (Phase 2), not the module graph's.
 */
export type ModuleBindingKind = 'function' | 'class' | 'const' | 'type' | 'unknown';
/**
 * How a binding enters a module
 */
export type ModuleImportKind = 'named' | 'default' | 'namespace' | 'require';
/**
 * A generic module-level binding (export, import, or re-export).
 *
 * `name` is always the name this module presents: the local identifier for
 * imports, the exported name for exports. `importAlias` carries the original
 * name in the source module when it differs (`import { X as Y }` → name 'Y',
 * importAlias 'X'; `export { X as Y } from …` → name 'Y', importAlias 'X').
 * For default imports name is the local identifier and the source lookup key
 * is 'default' (implied by importKind); for namespace imports/exports name is
 * the namespace alias ('*' for bare `export * from …`).
 */
export interface ModuleBinding {
    /** Name as presented in this module (local name for imports, exported name for exports) */
    name: string;
    /** What the binding is; backfilled from the origin module when resolvable */
    kind: ModuleBindingKind;
    /**
     * Resolved absolute file path of the source module (the module itself for
     * local declarations; the raw specifier when resolution fails)
     */
    sourceModule: string;
    /** How the binding enters the module (absent on plain local exports) */
    importKind?: ModuleImportKind;
    /** Original name in the source module when aliased */
    importAlias?: string;
    /** True for `export { X } from './y'` / `export * from './y'` (barrels) */
    isReExport: boolean;
    /**
     * True when the specifier resolved into node_modules
     * (ts.resolveModuleName's isExternalLibraryImport). External bindings are
     * recorded for reference but never enter `dependencies` and are never walked.
     * Node.js builtins are not recorded as bindings at all — see
     * ModuleInfo.builtinSpecifiers.
     */
    external?: boolean;
}
/**
 * Per-module record of the cross-file graph (modules.json)
 */
export interface ModuleInfo {
    /** Absolute file path (map key) */
    filePath: string;
    /** Mnemonica type fullPaths defined in this module */
    definedTypes: string[];
    /** Everything this module exports (local declarations and re-exports) */
    exportedBindings: ModuleBinding[];
    /** Everything this module imports (re-exports appear here too, marked isReExport) */
    importedBindings: ModuleBinding[];
    /** Absolute paths of analyzed project modules this module imports from */
    dependencies: string[];
    /** Import specifiers that module resolution could not resolve (node builtins excluded — see builtinSpecifiers) */
    unresolvedSpecifiers: string[];
    /**
     * Node.js builtin specifiers this module imports ('path', 'node:fs', …),
     * matched against node:module's builtinModules in both bare and
     * `node:`-prefixed forms. Recorded for honesty only: builtins produce no
     * bindings, never enter `dependencies`/`unresolvedSpecifiers`, and never
     * produce edges.
     */
    builtinSpecifiers: string[];
}
/**
 * A cross-module usage of a mnemonica type: usageModule imports a binding
 * whose origin module defines the type.
 */
export interface CrossModuleUsage {
    /** Matched mnemonica type fullPath (or the imported name when unmatched) */
    typePath: string;
    /** Absolute path of the module where the type is defined (re-export chains chased to the origin) */
    definitionModule: string;
    /** Absolute path of the importing module */
    usageModule: string;
    /** Import site: file.ts:Line:Col */
    usageLocation: string;
}
/**
 * The full module graph
 */
export interface ModuleGraph {
    /** Keyed by absolute file path */
    modules: Map<string, ModuleInfo>;
    edges: CrossModuleUsage[];
    /**
     * Circular import chains (each an array of absolute paths). Recorded, not
     * an error — mnemonica strictChain:false permits non-linear construction
     */
    cycles: string[][];
}
/**
 * JSON output for modules.json
 */
export interface ModulesJson {
    version: string;
    generatedAt: string;
    modules: Record<string, ModuleInfo>;
    edges: CrossModuleUsage[];
    cycles: string[][];
}
/**
 * What a tracked scope is. Decision 5 (resolved 2026-09-03): function,
 * method, and arrow scopes ONLY — no block scopes. 'module' is the synthetic
 * per-file root scope so module-level instance creations are labeled, not
 * dropped (walker plan: "recorded as a rooted instance").
 */
export type ScopeKind = 'module' | 'function' | 'method' | 'arrow';
/**
 * One tracked scope (scopes.json)
 */
export interface ScopeInfo {
    /** Unique id: module scope is the file path; function scopes are file:line:col of the scope node */
    scopeId: string;
    /** Decision 8 labeling: function/method name ('Class.method' for methods), file:line for anonymous holders */
    name: string;
    kind: ScopeKind;
    /** Nearest enclosing scope (undefined on module scopes) */
    parentScopeId?: string;
    /** Absolute file path */
    filePath: string;
    /** Scope start: file.ts:Line:Col (module scope: file:1:1) */
    location: string;
}
/**
 * One tracked variable (scopes.json)
 */
export interface ScopeVariable {
    name: string;
    /** Owning scope */
    scopeId: string;
    /** Mnemonica type fullPath when known (new X() on a known type, new inst.Sub() chaining, or a known annotation) */
    typePath?: string;
    /** Cheap textual type: annotation text or tiny initializer classification */
    inferredType?: string;
    /** Declaration site: file.ts:Line:Col */
    declaration: string;
    isParameter: boolean;
    /** const = false; let/var and parameters = true (parameters are reassignable) */
    isMutable: boolean;
    /**
     * Reassignment sites (file.ts:Line:Col) of this binding — flow-termination
     * points (decision 6): the Phase 3 walker stops following the binding there
     */
    reassignments: string[];
}
/**
 * The full local-scope analysis
 */
export interface ScopeAnalysis {
    /** Keyed by scopeId */
    scopes: Map<string, ScopeInfo>;
    /** Keyed by `${scopeId}#${name}` */
    variables: Map<string, ScopeVariable>;
}
/**
 * JSON output for scopes.json
 */
export interface ScopesJson {
    version: string;
    generatedAt: string;
    scopes: Record<string, ScopeInfo>;
    variables: ScopeVariable[];
}
/**
 * One node of the creation graph (instrumentation walker plan, Phase 3):
 * a scope that creates mnemonica instances, or one sitting on a call path
 * to a creator.
 */
export interface CreationGraphNode {
    /** LocalScopeWalker scopeId (module scope = file path; function scopes = file:line:col) */
    scopeId: string;
    /** Decision 8 label: function/method name ('Class.method'), file:line for anonymous holders */
    name: string;
    kind: ScopeKind;
    /** Absolute file path */
    filePath: string;
    /** Scope start: file.ts:Line:Col */
    location: string;
    /** True when the walk found no callers — an application entry point */
    starter: boolean;
}
/**
 * One edge of the creation graph: the caller scope invokes or references the
 * callee scope. Direction is inside-out: caller → callee, where the callee is
 * closer to the creation site.
 */
export interface CreationGraphEdge {
    /** Calling scope's scopeId */
    caller: string;
    /** Called (holder) scope's scopeId */
    callee: string;
}
/**
 * An instantiation anchor: one mnemonica creation site pinned to its holder
 * scope.
 *
 * `variable`/`terminatedAt` are a documented heuristic: the variable declared
 * in the holder scope on the SAME line as the creation, whose typePath (when
 * known) matches the created type. `terminatedAt` is that variable's first
 * reassignment site — the decision 6 flow-termination point where the walker
 * stops following the binding.
 */
export interface CreationAnchor {
    /** Creation site: file.ts:Line:Col (the usages.json location) */
    location: string;
    /** Scope holding the creation (scopes.json scopeId) */
    holderScopeId: string;
    /** Mnemonica type fullPath being created */
    typePath: string;
    /** Constructor expression text ('Thing', 'user.AdminEntity', a lookup alias name) */
    constructorText?: string;
    /**
     * True when the holder is the module scope — a rooted instance (plan:
     * legitimate root or developer error; labeled, not policed)
     */
    rooted?: boolean;
    /** Variable the fresh instance was bound to (same-line heuristic) */
    variable?: string;
    /** First reassignment site of that variable: file.ts:Line:Col */
    terminatedAt?: string;
}
/**
 * The creation graph: everything that leads to mnemonica instances being
 * created. Emitted as the `creationGraph` key of instrumentation.json v2.
 */
export interface CreationGraph {
    nodes: CreationGraphNode[];
    edges: CreationGraphEdge[];
    anchors: CreationAnchor[];
}
/**
 * JSON output for hierarchy.json
 */
export interface HierarchyJson {
    version: string;
    generatedAt: string;
    roots: HierarchyNode[];
}
/**
 * Structured hierarchy node for machine consumption.
 */
export interface HierarchyNode {
    /** Type name (e.g., "AdminType") */
    name: string;
    /** Full dotted path (e.g., "UserType.AdminType") */
    fullPath: string;
    /** Location in source: file.ts:Line:Col */
    location: string;
    /** Child types in the Trie */
    children: HierarchyNode[];
}
