import * as ts from 'typescript';
import { AnalyzeResult, DefinitionInfo, UsageInfo, EDSInfo, FlowInfo, InstrumentationPoint, ResolutionError } from './types';
import { TypeGraphImpl } from './graph';
import { TacticaPlugin } from './plugins';
/**
 * AST Analyzer for finding Mnemonica define() and decorate() calls
 *
 * Framework-blind by construction: instrumentation detection vocabulary
 * (interface names, decorator names, provider tokens, middleware wiring)
 * comes entirely from plugins — with none loaded, zero points are collected.
 */
export declare class MnemonicaAnalyzer {
    private errors;
    private graph;
    private definitions;
    private usages;
    private edsUsages;
    private flowUsages;
    private edsScopeByNode;
    private functionBindings;
    private nestedWrapVia;
    private wrapEntryByNode;
    private variableToTypeMap;
    private moduleObjectVariables;
    private createTypesCollectionVariables;
    private collectionVariables;
    private collectionInfo;
    private collectionCounter;
    private instrumentationClassDecls;
    private instrumentationSites;
    private instrumentationVocabulary;
    private referencedTypeDecls;
    private referencedTypeImports;
    private referencedTypeReExports;
    private referencedTypeExportStars;
    private referencedTypeExportAliases;
    private referencedTypeNamespaces;
    private referencedTypeNamespaceStars;
    private referencedTypeResolutionCache;
    private referencedTypeCompilerOptions;
    private currentReferencedTypeFile;
    private expandingReferencedAliases;
    private defineSites;
    private graphReferenceErrors;
    private lookupReferencesValidated;
    private lookupReferences;
    private plainTypeReferencesValidated;
    private plainTypeReferences;
    private fileGraphBindings;
    private currentGraphAnchor;
    private processedCalls;
    constructor(program?: ts.Program, plugins?: TacticaPlugin[]);
    /**
     * Reset usage-related state for a fresh pass.
     * Call before the usage-collection pass to avoid duplicates from definition pass.
     */
    resetUsages(): void;
    /**
     * Analyze a source file for Mnemonica type definitions
     */
    analyzeFile(sourceFile: ts.SourceFile): AnalyzeResult;
    /**
     * Analyze source code string
     */
    analyzeSource(sourceCode: string, fileName?: string): AnalyzeResult;
    /**
     * Get the type graph
     */
    getGraph(): TypeGraphImpl;
    /**
     * Get collected definitions
     */
    getDefinitions(): Map<string, DefinitionInfo>;
    /**
     * Get collected usages
     */
    getUsages(): Map<string, UsageInfo[]>;
    /**
     * Get collected EDS usages
     */
    getEDSUsages(): Map<string, EDSInfo[]>;
    /**
     * Get collected flow usages
     */
    getFlowUsages(): Map<string, FlowInfo[]>;
    /**
     * Get collected instrumentation points.
     * Registration sites referencing a class declared in the same project
     * resolve to the class declaration's location/code; external classes
     * (e.g., a framework-builtin implementation from node_modules) keep
     * the registration site.
     * Deduped by kind+className+location+scope with targets merged — a
     * class detected by heritage AND by a decorator site yields separate
     * entries with distinct scopes (see InstrumentationPoint in types.ts).
     */
    getInstrumentationPoints(): InstrumentationPoint[];
    /**
     * Add a topologica type to the analyzer for usage tracking.
     * This allows the analyzer to recognize topologica types when collecting usages.
     */
    addTopologicaType(fullPath: string, node: import('./types').TypeNode): void;
    /**
     * Set parent nodes in a source file to enable AST traversal up
     */
    private setParentNodesInSourceFile;
    /**
     * Visit a node in the AST
     */
    private visitNode;
    /**
     * Track imports from 'mnemonica' so aliases of the module object and
     * createTypesCollection are recognized without relying on the type checker.
     */
    private trackImports;
    /**
     * Record a named referenced-type declaration (type alias, class, or
     * interface) for the file currently being visited.
     */
    private trackReferencedTypeDeclaration;
    /**
     * Record the importing file's named/namespace/default import bindings so
     * referenced-type names resolve through the file's own import statements
     * (F10) rather than a program-wide name map.
     */
    private trackReferencedTypeImport;
    /**
     * Record re-export wiring (`export { X } from '…'`, `export * from '…'`,
     * `export { X as Y }`) so resolution can chase barrels to the origin
     * module. Mirrors ModuleGraphBuilder.resolveOrigin, name-based only.
     */
    private trackReferencedTypeReExport;
    /**
     * Resolve a module specifier from a containing file with the program's
     * compilerOptions (tsconfig `paths`, extensionless imports, index files).
     * Module resolution only — the no-getTypeChecker() precedent stays.
     */
    private resolveReferencedTypeModule;
    /**
     * Look up a name in one resolved module, chasing re-export barrels with a
     * bounded depth. External (node_modules) modules hold no in-project
     * declarations and stop the chase.
     */
    private findReferencedTypeInModule;
    /**
     * Resolve a referenced type name as used in fromFile, import-aware:
     *   1. the file's own import statements (relative + tsconfig paths,
     *      chased through re-export barrels),
     *   2. the file's local declarations,
     *   3. the unique same-named declaration across scanned files.
     * Returns undefined when nothing matches (or the match is ambiguous),
     * in which case the caller falls back to `unknown`.
     */
    private resolveReferencedTypeDeclaration;
    /**
     * External/ambient declaration files (.d.ts, anything under
     * node_modules) never participate in plain-TS referenced-type
     * resolution or the ambiguity law: they are not project source, the
     * CLI never analyzes them, and a user-local declaration always wins
     * over a package-declared same-named type.
     */
    private isExternalDeclFile;
    /**
     * Properties of a referenced class/interface/alias-of-literal declaration,
     * shared by `this:`-parameter expansion and inline type emission.
     */
    private referencedDeclarationProperties;
    /**
     * Expand a referenced-type declaration to a self-contained type string
     * for emission into generated files: type aliases through inferType,
     * classes and interfaces through their (public, non-method) fields.
     * Nested references resolve against the declaring file while expanding.
     */
    private expandReferencedTypeDeclaration;
    private expandReferencedTypeDeclarationInner;
    /**
     * Resolve a simple (non-qualified) type reference: import-aware
     * declaration expansion first, then the InstanceType<typeof X> pattern,
     * then mnemonica graph types; known globals keep their bare name and
     * anything else falls back to `unknown` so generated files never carry
     * an unresolvable bare name. Returns undefined when the caller should
     * keep the generic spelling (handled separately).
     */
    private resolveSimpleTypeReference;
    /**
     * Resolve a qualified type reference (models.Inner.Crate) through the
     * current file's namespace imports. The chain's head must be a namespace
     * import; middle segments descend through namespace declarations, named
     * re-exports of namespaces, and `export * as ns from '…'` barrels (each
     * segment consumed exactly once, so the walk cannot cycle); the final
     * segment resolves to a declaration which is expanded inline. When the
     * precise walk finds nothing, the legacy rightmost-name lookup in the
     * head module keeps one-level forms (models.Type) working — nested
     * declarations are recorded by plain name there too. Returns undefined
     * when the head is not a namespace import or nothing resolves.
     */
    private inferQualifiedTypeReference;
    /**
     * Find a namespace declaration by name directly inside a module block.
     */
    private findNamespaceInBlock;
    /**
     * Find a named type declaration (alias, class, interface) directly inside
     * a namespace block — the final segment of a descended qualified chain.
     */
    private findReferencedTypeInBlock;
    /**
     * Fallback for a type-reference name that resolves to no declaration and
     * no graph type: known globals keep their bare name (they resolve without
     * an import); everything else becomes `unknown` so generated types.ts
     * never carries an unresolvable bare name (README's documented behavior)
     * and the site is recorded for the plain-TS ambiguity validation.
     */
    private unresolvedTypeReferenceFallback;
    /**
     * Record one define()/lazy()/@decorate() site under its runtime
     * namespace key. Two sites in one namespace are a same-namespace
     * duplicate (the runtime throws ALREADY_DECLARED); every site is kept
     * so the failure can report all locations.
     */
    private recordDefineSite;
    /**
     * Fatal resolution failures (hard-fail law): same-namespace duplicate
     * mnemonica definitions plus ambiguous/unresolved mnemonica-graph
     * references. The CLI prints every location and writes no output.
     */
    getResolutionErrors(): ResolutionError[];
    /**
     * Resolve a reference to a mnemonica graph type name, import-aware and
     * path-aware (the hard-fail identity law, mirroring the runtime):
     *   1. value scope — a tracked top-level binding in the referencing file
     *      (`const Address = User.define('Address', …)`),
     *   2. import scope — a binding exported from a module this file imports
     *      (barrels chased),
     *   3. nearest-chain — the anchor type's own subtypes first, then each
     *      ancestor level (relative-first),
     *   4. root — roots of the anchor's collection,
     *   5. program-wide — only when exactly one type carries the name.
     * Ambiguity (several candidates and nothing disambiguates) and absence
     * are both returned as such — the caller records a hard failure; a bare
     * first-match name is never emitted.
     */
    private resolveGraphTypeName;
    /**
     * Find a graph constructor binding exported by a resolved module,
     * chasing re-export barrels with a bounded depth.
     */
    private findGraphBindingInModule;
    /**
     * Validate literal lookup() paths recorded during the usages pass
     * against the complete graph. A lookup path matching no type is what the
     * runtime answers with `undefined` — the TypeError arrives one line
     * later at the `new` — so it joins the hard-fail law. The relative-first
     * step already ran inside resolveLookupPath; whatever was recorded is
     * the root-resolution result, so a plain findType check is the exact
     * runtime law. Same-named types elsewhere in the graph are listed as
     * did-you-mean candidates. Runs once per usages pass (re-armed by
     * resetUsages); non-literal lookup arguments are never recorded and
     * stay best-effort.
     */
    private validateLookupReferences;
    /**
     * Record a plain-TS type reference site that resolved to nothing and
     * fell back to `unknown`, for the lazily-run ambiguity validation.
     * Deduped by (name, location): inferType can visit the same node more
     * than once per pass (constructor params + property inference).
     */
    private recordPlainTypeReferenceSite;
    /**
     * Project-source declaration files carrying `name` — one entry per
     * file, so same-file interface merging counts once (not ambiguous).
     * External/ambient declarations (.d.ts, anything under node_modules)
     * never count: a user-local declaration always wins over a package-
     * declared same-named type, so an external collision stays soft.
     */
    private plainTypeDeclarationFiles;
    /**
     * Validate plain-TS type reference sites recorded during the usages
     * pass against the complete declaration map. A name declared in
     * several project-source files — with no import in the referencing
     * file to anchor it — is ambiguous: silently emitting `unknown` would
     * hide a real type the author meant, so it joins the hard-fail law
     * (the plain-TS tier of the same identity law as graph references).
     * Absence (ghost names) and external collisions stay soft `unknown`.
     * Runs once per usages pass (re-armed by resetUsages), mirroring
     * validateLookupReferences: recording happens on every pass, but only
     * the usages pass sees the complete declaration map.
     */
    private validatePlainTypeReferences;
    /**
     * `file:line:column` of a recorded declaration, for the ambiguity
     * report. Nodes recorded during traversal keep their positions; a
     * synthetic/unpositioned node falls back to the file itself.
     */
    private plainDeclLocation;
    /**
     * Record a hard-fail graph reference error with the reference site and
     * every candidate location.
     */
    private recordGraphReferenceError;
    /**
     * Location (`file:line:column`) of an AST node, derived without parent
     * pointers when necessary.
     */
    private nodeLocation;
    /**
     * Track aliases of the mnemonica module object, e.g.:
     *   const m = mnemonica;
     *   const App = m;
     */
    private trackModuleObjectAliases;
    /**
     * Track custom collection variables, e.g.:
     *   const MyCollection = createTypesCollection();
     *   const Other = MyCollection;
     *
     * Also detects Option B user-provided registry interfaces:
     *   export interface MyCollectionRegistry {}
     *   const MyCollection = createTypesCollection<MyCollectionRegistry>();
     */
    private trackCollectionAliases;
    /**
     * Extract the registry interface name from createTypesCollection<Registry>()
     * when the interface is declared in the same source file.
     */
    private extractRegistryInterfaceName;
    /**
     * Get the registry interface name for a collection id.
     */
    private getRegistryInterfaceName;
    /**
     * Check if an expression is a createTypesCollection() call.
     * Handles:
     *   createTypesCollection()
     *   ctc() // aliased import
     *   mnemonica.createTypesCollection() // module object method
     *   m.createTypesCollection() // aliased module object
     */
    private isCreateTypesCollectionCall;
    /**
     * Generate a unique collection identifier.
     */
    private nextCollectionId;
    /**
     * Check if a node is a define() call
     */
    private isDefineCall;
    /**
     * Check if a node is a lazy() call
     */
    private isLazyCall;
    /**
        * Extract config options from an object literal
        */
    private extractConfigFromObjectLiteral;
    /**
        * Extract config options from define() call
        */
    private extractConfig;
    /**
        * Check if a node is a @decorate() decorator
        */
    private isDecorateDecorator;
    /**
     * Mark a call expression as processed and return whether it already was.
     */
    private markProcessed;
    /**
     * Process a define() call
     */
    private processDefineCall;
    /**
     * Process a lazy() call
     */
    private processLazyCall;
    /**
     * Extract lazy() call arguments into a normalized shape.
     * Handles named/unnamed and explicit-source forms, both as free calls
     * and as method calls.
     */
    private extractLazyCallArgs;
    /**
     * Unwrap the constructor returned by a lazy getter.
     * Supports:
     *   () => class Name {}
     *   () => function Name() {}
     *   () => { return class Name {}; }
     *   function () { return function Name() {}; }
     */
    private unwrapLazyGetter;
    /**
     * Extract a constructor name from a class expression, class declaration,
     * or named function expression.
     */
    private extractConstructorName;
    /**
     * Extract the type name from either a define() or lazy() call.
     */
    private extractMnemonicaTypeName;
    /**
     * Extract the full lazy() call context: type name, parent type, and collection.
     * Handles direct calls, property-access calls, chained calls, and the
     * explicit-source form `lazy(source, 'TypeName', getter)`.
     */
    private extractLazyContext;
    /**
     * Extract config options from lazy() call
     */
    private extractLazyConfig;
    /**
        * Track variable assignments that capture define() results
        * e.g., const User = define('UserEntity', ...) maps "User" -> "UserEntity"
        * For chained calls like const X = define('A').define('B'), we map X -> A (the root type)
        */
    private trackVariableAssignment;
    /**
     * Mirror a variable -> mnemonica fullPath binding into the per-file
     * value-scope map (graph identity law: `typeof X` and bare references
     * resolve through the file's own bindings first).
     */
    private trackFileGraphBinding;
    /**
        * Track variable assignments from lookup() calls
        * e.g., const SentienceConstructor = lookup('Sentience') maps "SentienceConstructor" -> "Sentience"
        */
    private trackLookupAssignment;
    /**
        * Track variable assignments from new Type() calls
        * e.g., const user = new UserType() maps "user" -> "UserType"
        */
    private trackNewAssignment;
    /**
        * Process a @decorate() decorator
     */
    private processDecorateDecorator;
    /**
     * Extract type name from define() call arguments.
     * Handles:
     *   define('TypeName', handler)
     *   define(source, 'TypeName', handler)   // explicit-source form
     *   define(function TypeName() {})
     *   define(() => class TypeName {})
     */
    private extractTypeName;
    /**
     * Extract the full define() call context: type name, parent type, and collection.
     * Handles direct calls, property-access calls, chained calls, and the
     * explicit-source form `define(source, 'TypeName', handler)`.
     */
    private extractDefineContext;
    /**
     * Prefix a dotted type path with a collection identifier so custom-collection
     * types do not collide with default-collection types in the graph.
     */
    private prefixCollectionPath;
    /**
     * Resolve a define() source identifier to either a parent type, a collection,
     * or the default (module object) collection.
     */
    private resolveDefineSource;
    /**
     * Check if a call expression is a lookup() call.
     */
    private isLookupCall;
    /**
     * Resolve a lookup() call to a dotted type path (best effort).
     * Handles:
     *   lookup('User')
     *   lookup(source, 'User')
     *   App.lookup('User')
     *   collection.lookup('User.Admin')
     */
    private resolveLookupPath;
    /**
     * Lookup-law delegate for the local-scope walker (scopes.json typePath
     * metadata): resolve a lookup() initializer call through exactly the
     * tiers the usages pass resolved it against (same source resolution,
     * same complete graph). The walker runs its own scope-chain value-scope
     * tier before delegating; everything above value scope lands here, so
     * scopes.json never disagrees with the hard-fail-law verdicts.
     */
    resolveLookupCallPath(call: ts.CallExpression): string | undefined;
    /**
        * Find a parent type by its name, searching in the graph.
        * When collectionId is provided, only types from that collection are considered.
        */
    private findParentTypeByName;
    /**
        * Find a parent type from an identifier reference.
        * Handles both aliased variables (const User = define('UserEntity', ...))
        * and direct class/type names.
        */
    private findParentTypeByIdentifier;
    /**
     * Get the leftmost identifier of a property-access chain.
     * For `App.define('User').define('Admin')` this returns the `App` identifier.
     */
    private getRootIdentifier;
    /**
        * Get property chain from nested access
        */
    private getPropertyChain;
    /**
     * Determine the constructor expression for either a define() or lazy() call.
     * For define() this is the construct handler; for lazy() it is the value
     * returned by the lazy getter.
     */
    private extractConstructorExpression;
    /**
     * Extract properties from constructor function
     */
    private extractProperties;
    /**
     * Extract properties from a constructor expression (function, arrow, or class).
     */
    private extractPropertiesFromConstructor;
    /**
     * Build a type map from all parameters with inline object type annotations
     * Returns a map of "paramName.propertyName" -> type
     */
    private buildDataTypeMap;
    /**
     * Extract property access chain (e.g., "dataRenamed.id" from dataRenamed.id)
     * Handles fallbacks like: data.permissions || []
     */
    private getPropertyAccessChain;
    /**
     * Extract property assignment from statement
     */
    private extractPropertyFromStatement;
    /**
     * Extract properties from class declaration (including methods and getters)
     */
    private extractClassProperties;
    /**
     * Extract class property types for method return type inference
     * Maps property names to their TypeScript type strings
     * Note: Includes private/protected properties for method inference
     */
    private extractClassPropertyTypes;
    /**
     * Infer method type from method declaration
     */
    private inferMethodType;
    /**
        * Extract properties from `this` parameter type annotation
        * Handles patterns like: function(this: SomeType, data: SomeType) { }
        */
    private extractThisParamProperties;
    /**
        * Infer TypeScript type from type node
        */
    /**
     * Infer TypeScript type from type node
     */
    private inferType;
    /**
        * Infer return type from a method declaration
        * Uses explicit return type annotation or infers from return statements
        */
    private inferReturnType;
    /**
        * Infer return type by analyzing return statements in the method body
        */
    private inferReturnTypeFromBody;
    /**
     * Infer type from initializer
     */
    private inferTypeFromInitializer;
    /**
            * Collect usage information for type references
            */
    private collectUsage;
    /**
            * Get function name from expression (identifier or property access)
            */
    private getFunctionName;
    /**
            * Add a usage to the collection
            */
    private addUsage;
    /**
     * Collect EDS (Execution Data Storage) usage information
     */
    private collectEDS;
    /**
     * Resolve type from EDS call argument (best effort)
     */
    private resolveEDSArgumentType;
    /**
     * Resolve the enclosing mnemonica scope of an EDS call site by walking
     * up the parent chain: nearest define()/lazy() call whose handler holds
     * the node, or nearest @decorate()-ed class declaration. Best effort —
     * returns undefined for calls outside any type scope (module top level).
     */
    private resolveEDSScope;
    /**
     * Resolve a wrap site's instance/context argument to a mnemonica type
     * path — the fire-and-forget-wrapper attribution fallback when the call
     * sits outside any define()/lazy() handler: a tracked assignment
     * (`const holder = new Holder(...)`), else the root identifier's
     * (property-access roots included) parameter annotation resolved
     * through the graph law. Ambiguity or absence stays silent — this is a
     * metadata heuristic, not the identity-law surface.
     */
    private resolveWrapInstanceTypePath;
    /**
     * Resolve a bare-identifier type annotation of the nearest enclosing
     * function's parameter through the mnemonica-graph tiers (value scope,
     * imports, roots, program-wide-unique). Non-identifier and generic
     * annotations are not graph references; ambiguity and absence yield
     * undefined.
     */
    private resolveParameterAnnotationTypePath;
    /**
     * Resolve a wrap() argument to its function node without the type
     * checker: direct function expressions/arrows, or same-file bindings
     * (`const fn = () => ...`, `function fn() ...`). Best effort — method
     * references, .bind() products and cross-file identifiers stay
     * unresolved; the callsite entry itself is still recorded.
     */
    private resolveFunctionArgument;
    /**
     * Analyse a wrapped function's body for guaranteed runtime paths:
     * dive wraps returned functions as well (recursively), so each
     * function-valued return is a nested wrap site, and each `new Type()`
     * inside the body means the path hits that type's constructor (which
     * attachHooks wraps too). Both facts are 100% ensured, so they are
     * recorded AoT. Nested function bodies are NOT walked here — they
     * belong to their own wrap analysis, reached via the return chain.
     * Depth-capped and cycle-guarded.
     */
    private analyzeWrappedBody;
    /**
     * Record one function-valued return of a wrapped body as a nested wrap
     * site (`via` = the site whose wrapping caused it) and recurse into
     * its own returns. Returns through identifiers resolve through the
     * same-file bindings table; unresolvable returns are simply skipped.
     * A return declared outside any type scope inherits the causing wrap
     * site's scope attribution (the generation chain is the only holder).
     */
    private recordWrappedReturn;
    /**
     * Add an EDS usage to the collection
     * Returns the stored entry (the existing one when this is a duplicate),
     * so callers can enrich it after nested body analysis.
     */
    private addEDS;
    /**
     * Collect native flow patterns (instance usage after creation)
     * Phase 1: property access, method calls, arguments, return, destructuring, etc.
     */
    private collectFlow;
    /**
     * Collect property access flow (read or conditional)
     */
    private collectFlowPropertyAccess;
    /**
     * Collect element access flow: user['name']
     */
    private collectFlowElementAccess;
    /**
     * Collect assignment flow: user.name = value or user = other
     */
    private collectFlowAssignment;
    /**
     * Collect method call flow: user.validate()
     */
    private collectFlowMethodCall;
    /**
     * Collect argument passing flow: processUser(user)
     */
    private collectFlowArgumentPass;
    /**
     * Collect destructuring flow: const { name } = user
     */
    private collectFlowDestructure;
    /**
     * Collect return flow: return user
     */
    private collectFlowReturn;
    /**
     * Collect spread flow: { ...user }
     */
    private collectFlowSpread;
    /**
     * Resolve type from an expression (identifier, property access, etc.)
     */
    private resolveExpressionType;
    /**
     * Add a flow usage to the collection
     */
    private addFlow;
    /**
            * Get type name from expression (identifier or property access)
            */
    private getTypeNameFromExpression;
    /**
            * Resolve full type path from property access
            */
    private resolveTypePath;
    /**
             * Check if a name looks like a type (starts with uppercase)
             */
    private isLikelyTypeName;
    /**
             * Resolve a constructor parameter type, expanding inline object literals
             * and type aliases where possible.
             */
    private resolveConstructorParamType;
    /**
             * Extract constructor parameters from a class-like node.
             */
    private extractClassConstructorParams;
    /**
             * Extract constructor parameters from define() call
             * This is used for TypeRegistry constructor signatures
             * Preserves parameter names and expands object types to their structure
             */
    private extractConstructorParams;
    /**
             * Extract constructor parameters from a constructor expression.
             */
    private extractConstructorParamsFromConstructor;
    /**
     * Collect framework instrumentation points. Purely syntactic: heritage
     * clauses, decorator application sites, provider-token object literals
     * and consumer.apply().forRoutes() wiring. The vocabulary comes from
     * plugins; identifier text is matched as-is — no import resolution,
     * the type checker stays unused.
     */
    private collectInstrumentation;
    /**
     * Record a named class declaration for instrumentation site resolution
     * and detect heritage-based kinds (`implements <plugin interface>`)
     */
    private collectInstrumentationClass;
    /**
     * Detect decorator application sites: plugin-listed decorators applied
     * with class arguments on a class or one of its methods. One site per
     * referenced class identifier.
     */
    private collectInstrumentationDecorator;
    /**
     * Detect global registrations: object literals shaped like
     * `{ provide: <plugin-listed token>, useClass: X }`.
     * useExisting/useFactory without a useClass identifier are not
     * statically obvious — skipped rather than guessed.
     */
    private collectInstrumentationProvider;
    /**
     * Detect middleware wiring: `consumer.apply(Mw1, Mw2).forRoutes(...)`
     * inside a class's configure() method. Targets come from forRoutes
     * arguments when statically readable (string routes or controller
     * identifiers), else []. Shape-based, so a plugin must opt in via
     * `middlewareWiring: true`.
     */
    private collectInstrumentationMiddleware;
    /**
     * Walk up the parent chain looking for an enclosing configure() method
     */
    private isInsideConfigureMethod;
}
