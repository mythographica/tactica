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
exports.MnemonicaAnalyzer = void 0;
const nodePath = __importStar(require("path"));
const ts = __importStar(require("typescript"));
const graph_1 = require("./graph");
const plugins_1 = require("./plugins");
/**
 * Global/builtin type names that are safe to emit bare into generated files
 * — they resolve in any TypeScript compilation without an import.
 */
const KNOWN_GLOBAL_TYPES = new Set([
    'Date', 'RegExp', 'Error', 'EvalError', 'RangeError', 'ReferenceError',
    'SyntaxError', 'TypeError', 'URIError', 'AggregateError',
    'Map', 'Set', 'WeakMap', 'WeakSet', 'WeakRef', 'FinalizationRegistry',
    'Promise', 'Array', 'ReadonlyArray', 'Record', 'Partial', 'Required',
    'Readonly', 'Pick', 'Omit', 'Exclude', 'Extract', 'NonNullable',
    'ReturnType', 'InstanceType', 'Parameters', 'ConstructorParameters',
    'ThisType', 'ThisParameterType', 'OmitThisParameter',
    'Uppercase', 'Lowercase', 'Capitalize', 'Uncapitalize',
    'String', 'Number', 'Boolean', 'Symbol', 'BigInt', 'Object', 'Function',
    'Iterable', 'Iterator', 'Generator', 'AsyncIterable', 'AsyncIterator',
    'AsyncGenerator', 'IterableIterator', 'AsyncIterableIterator',
    'PropertyKey', 'ArrayBuffer', 'SharedArrayBuffer', 'DataView',
    'Int8Array', 'Uint8Array', 'Uint8ClampedArray', 'Int16Array',
    'Uint16Array', 'Int32Array', 'Uint32Array', 'Float32Array',
    'Float64Array', 'BigInt64Array', 'BigUint64Array', 'Intl'
]);
// Generic globals whose bare emission would be invalid TS (TS2314):
// `new Map()` carries no type arguments, so the field type fills them
// with unknown. Keys must also be members of KNOWN_GLOBAL_TYPES.
const GENERIC_GLOBAL_DEFAULT_ARGS = new Map([
    ['Map', 'Map<unknown, unknown>'],
    ['WeakMap', 'WeakMap<object, unknown>'],
    ['Set', 'Set<unknown>'],
    ['WeakSet', 'WeakSet<object>'],
    ['WeakRef', 'WeakRef<object>'],
    ['FinalizationRegistry', 'FinalizationRegistry<unknown>'],
    ['Promise', 'Promise<unknown>'],
    ['Array', 'Array<unknown>'],
    ['ReadonlyArray', 'ReadonlyArray<unknown>']
]);
// Bound for chasing re-export barrels (export { X } from '…', export * from '…')
const MAX_REEXPORT_CHASE_DEPTH = 5;
// Bound for walking class/interface extends chains during referenced-type
// expansion (inherited members merge into the expanded fields)
const MAX_HERITAGE_DEPTH = 8;
// Bound for reading a receiver's declared type back to the generated types
// it names (aliases, unions, intersections, interface extends)
const MAX_ANNOTATION_OWNER_DEPTH = 8;
/**
 * AST Analyzer for finding Mnemonica define() and decorate() calls
 *
 * Framework-blind by construction: instrumentation detection vocabulary
 * (interface names, decorator names, provider tokens, middleware wiring)
 * comes entirely from plugins — with none loaded, zero points are collected.
 */
class MnemonicaAnalyzer {
    constructor(program, plugins = []) {
        this.errors = [];
        this.graph = new graph_1.TypeGraphImpl();
        this.definitions = new Map();
        this.usages = new Map();
        this.edsUsages = new Map();
        this.flowUsages = new Map();
        // Enclosing mnemonica scope for EDS keying: define()/lazy() call node
        // or @decorate()-ed class declaration -> fullPath of the type it owns.
        // Populated on the definitions pass; AST nodes persist across passes,
        // so entries stay valid after resetUsages().
        this.edsScopeByNode = new Map();
        // Same-file function bindings (`fileName#name` -> function node) for
        // resolving wrap(fn) arguments syntactically — the checker stays unused
        this.functionBindings = new Map();
        // Constructor values by declaring file and exported/local name. Resolution
        // uses the same import and re-export wiring as referenced-type declarations.
        this.constructorBindings = new Map();
        // wrap call node -> location of the enclosing wrap site (plus that
        // site's scope attribution), so nested wrap() calls inside a wrapped
        // body carry the `via` link — and inherit the scope when they have
        // none of their own
        this.nestedWrapVia = new Map();
        // wrap call node -> its collected entry, so a lexically nested wrap
        // (visited BEFORE the outer wrap call, per source order) gets its
        // `via` back-patched when the outer body is analysed
        this.wrapEntryByNode = new Map();
        // Track variable assignments: variableName -> fullPath of the type it holds
        this.variableToTypeMap = new Map();
        // Exported builder values and their transitive self-reference exclusions.
        this.builderCandidates = [];
        this.excludedTypePaths = new Set();
        // Type paths defined on a chain that starts at the free define() or
        // lookup(): such a chain carries the global TypeRegistry itself, so its
        // exported values enter the registry as `typeof X`, never through
        // RegistryOf (TypeRegistry would be its own base: TS2456/TS2310).
        // Sticky across passes, like excludedTypePaths
        this.freeChainTypePaths = new Set();
        this.generatedTypeImports = new Map();
        // Absolute directories holding the generated output; an import resolving
        // into one of them (relative or through tsconfig `paths`) is generated
        this.generatedOutputDirs = [];
        // `${containingFile}::${specifier}` -> does it resolve into the output
        this.generatedSpecifierCache = new Map();
        // Track mnemonica module-object variables (e.g., import { mnemonica } from 'mnemonica'; const m = mnemonica)
        this.moduleObjectVariables = new Set();
        // file -> (local name -> imported name) for named imports from
        // 'mnemonica' — import-awareness for the construction-function
        // recognition (call/apply/bind) and the utils forms (merge/fork):
        // userland functions with those names must never match
        this.mnemonicaNamedImports = new Map();
        // Track imported aliases of createTypesCollection (e.g., import { createTypesCollection as ctc })
        this.createTypesCollectionVariables = new Set();
        // Track custom collection variables: variableName -> collectionId
        this.collectionVariables = new Map();
        // Track custom collection metadata for Option B registry emission
        this.collectionInfo = new Map();
        this.collectionCounter = 0;
        // Instrumentation collection (syntactic only — no type checker):
        // every named class declaration by simple name, for resolving
        // registration sites to declaration locations (best effort, last wins)
        this.instrumentationClassDecls = new Map();
        // Registration sites: decorator applications, provider-token object
        // literals, consumer.apply() middleware wiring
        this.instrumentationSites = [];
        // Referenced-type resolution (F10): per-file declarations and imports.
        // A type name used in file X resolves through X's own import statements
        // first (relative + tsconfig-paths, via ts.resolveModuleName), then
        // X's local declarations, then — only when nothing imports or declares
        // the name — the unique same-named declaration across scanned files.
        // Genuine ambiguity or an unresolvable reference yields `unknown`, never
        // a bare emitted name: generated types.ts carries no imports of its own.
        this.referencedTypeDecls = new Map();
        this.referencedTypeImports = new Map();
        // file -> (exported name -> re-export specifier) for `export { X } from '…'`
        this.referencedTypeReExports = new Map();
        // file -> specifiers of `export * from '…'`
        this.referencedTypeExportStars = new Map();
        // file -> (exported name -> local name) for `export { X as Y }`
        this.referencedTypeExportAliases = new Map();
        // file -> (namespace name -> namespace declaration) — middle segments
        // of qualified references (models.Inner.Crate) descend through these
        this.referencedTypeNamespaces = new Map();
        // file -> (namespace name -> specifier) for `export * as ns from '…'`
        // barrels — a nested module namespace one segment deep
        this.referencedTypeNamespaceStars = new Map();
        // `${containingFile}::${specifier}` -> resolution (undefined = failed)
        this.referencedTypeResolutionCache = new Map();
        // file -> (const name -> array literal) for consts with array-literal
        // initializers (`as const` / `satisfies` unwrapped), so a
        // `typeof statusList[number]` field type expands to the element literal
        // union instead of leaking a bare unresolvable `typeof` query into the
        // generated file. Declarations persist across passes — entries stay
        // valid after resetUsages(), same as referencedTypeDecls
        this.referencedTypeConstArrays = new Map();
        // File whose AST is currently being visited; references resolve against it
        this.currentReferencedTypeFile = '';
        // Alias names currently being expanded (cycle guard)
        this.expandingReferencedAliases = new Set();
        // Mnemonica-graph identity law (hard fail): every define()/lazy()/
        // @decorate() site keyed by its runtime namespace (collection roots:
        // `<collection>::<name>`; subtypes: `<parentFullPath>.<name>`). Two
        // sites in one namespace are a same-namespace duplicate — the runtime
        // throws ALREADY_DECLARED — and must abort generation.
        this.defineSites = new Map();
        // Mnemonica-graph references that stayed ambiguous after path-aware
        // resolution or resolved to nothing (hard-fail class 2)
        this.graphReferenceErrors = [];
        // Guards lookup()-path validation so it runs once per usages pass
        // (getResolutionErrors may be called repeatedly); resetUsages re-arms it
        this.lookupReferencesValidated = false;
        // Literal lookup() call sites with their resolved paths. Kept apart from
        // the usages map on purpose: addUsage drops paths the graph does not
        // know (usages.json indexes references to KNOWN types), but an unknown
        // lookup path is exactly the hard-fail case — the runtime returns
        // undefined there and the TypeError arrives one line later
        this.lookupReferences = [];
        // Guards plain-TS reference validation so it runs once per usages pass
        // (getResolutionErrors may be called repeatedly); resetUsages re-arms it
        this.plainTypeReferencesValidated = false;
        // Plain-TS type reference sites whose resolution fell through imports,
        // locals, the program-wide scan, and the graph to a soft `unknown`.
        // Validated lazily from getResolutionErrors against the complete
        // declaration map: a name several project-source files declare — with
        // no import in the referencing file to anchor it — is the plain-TS
        // ambiguity hard-fail class (one tier below the graph identity law);
        // absence (ghost names) stays soft. Recording happens on every pass,
        // the verdict only here — pass 1 sees an incomplete declaration map,
        // so only the usages pass is authoritative (mirrors lookup references)
        this.plainTypeReferences = [];
        // Per-file top-level variable -> mnemonica fullPath bindings (value
        // scope): `const Address = User.define('Address', …)` makes `Address`
        // denote User.Address wherever that file's references are resolved
        this.fileGraphBindings = new Map();
        // define()/lazy() calls already extracted this pass. The CLI re-analyzes
        // every file after resetUsages(); clearing the set lets the second pass
        // re-extract every constructor against the COMPLETE graph — pass 1 sees
        // forward references as `none` (soft unknown) because later files have
        // not been visited yet, so only pass-2 resolution is authoritative for
        // the hard-fail identity law. The stamp lives here rather than on the
        // AST node so it can actually be cleared. (Chained calls visit the same
        // node twice within one pass; the in-pass dedup below stays.)
        this.processedCalls = new Set();
        // Compiler options drive ts.resolveModuleName for import-aware
        // referenced-type resolution (tsconfig `paths`, extensionless
        // imports); the type checker itself stays unused.
        this.referencedTypeCompilerOptions = program?.getCompilerOptions() ?? {};
        this.instrumentationVocabulary = (0, plugins_1.mergeTacticaPlugins)(plugins);
    }
    /**
     * Directories holding the generated output. Imports resolving into them
     * name generated types, whatever specifier reaches them (a relative
     * path, a tsconfig `paths` alias, a custom --output name).
     */
    setGeneratedOutputDirs(dirs) {
        this.generatedOutputDirs = dirs.map(dir => nodePath.resolve(dir));
        this.generatedSpecifierCache.clear();
    }
    /**
     * Reset usage-related state for a fresh pass.
     * Call before the usage-collection pass to avoid duplicates from definition pass.
     */
    resetUsages() {
        this.usages.clear();
        this.edsUsages.clear();
        this.flowUsages.clear();
        this.variableToTypeMap.clear();
        // EDS entry references go stale with edsUsages; via links are
        // re-derived on the next pass
        this.wrapEntryByNode.clear();
        this.nestedWrapVia.clear();
        // Note: moduleObjectVariables and collectionVariables intentionally persist
        // across definition and usage passes.
        // Re-extraction in the usages pass is what makes graph reference
        // resolution authoritative: pass 1 resolves against an incomplete
        // graph (forward references read as `none`), pass 2 against all of it.
        this.processedCalls.clear();
        // lookup()-path validation runs against the recorded sites; a fresh
        // pass must re-record and re-validate (pass-1 results would be
        // premature — the graph is still incomplete)
        this.lookupReferencesValidated = false;
        this.lookupReferences = [];
        this.plainTypeReferencesValidated = false;
        this.plainTypeReferences = [];
    }
    /**
     * Analyze a source file for Mnemonica type definitions
     */
    analyzeFile(sourceFile) {
        this.errors = [];
        // Referenced-type names in this file resolve against its own imports
        this.currentReferencedTypeFile = nodePath.resolve(sourceFile.fileName);
        // Ensure parent nodes are set for AST traversal
        this.setParentNodesInSourceFile(sourceFile);
        this.visitNode(sourceFile, sourceFile);
        return {
            types: this.graph.getAllTypes(),
            errors: this.errors,
        };
    }
    /**
     * Analyze source code string
     */
    analyzeSource(sourceCode, fileName = 'temp.ts') {
        const sourceFile = ts.createSourceFile(fileName, sourceCode, ts.ScriptTarget.Latest, true);
        return this.analyzeFile(sourceFile);
    }
    /**
     * Get the type graph
     */
    getGraph() {
        return this.graph;
    }
    getBuilderValues() {
        const result = [];
        const seen = new Set();
        for (const candidate of this.builderCandidates) {
            // excludedTypePaths covers both passes: a candidate recorded in
            // pass 1, before a cross-file alias was known, stays excluded
            // once pass 2 finds its self-reference
            if (candidate.excluded || this.excludedTypePaths.has(candidate.fullPath)) {
                continue;
            }
            for (const exported of candidate.exports) {
                const key = `${candidate.kind}|${exported.sourceFile}|${exported.name}|${candidate.fullPath}`;
                if (seen.has(key)) {
                    continue;
                }
                seen.add(key);
                result.push({
                    name: exported.name,
                    sourceFile: exported.sourceFile,
                    kind: candidate.kind,
                    fullPath: candidate.fullPath,
                    defaultImport: exported.defaultImport
                });
            }
        }
        return result;
    }
    /**
     * Get collected definitions
     */
    getDefinitions() {
        return this.definitions;
    }
    /**
     * The collections.json manifest: one entry per minted collection, in
     * minting order, preceded by the default-collection entry whenever
     * default-collection types exist. The default entry has no id/location
     * (there is no call site — unprefixed fullPaths are its identity).
     * Format 1.2: the registry interface is NOT emitted (it is a
     * TypeScript-only concern — the in-memory registryInterfaceName that
     * types.ts/registry.ts are generated from stays on the TypeNode).
     */
    getCollectionsManifest() {
        const entries = [];
        const hasDefaultTypes = this.graph.getAllTypes().some(t => t.collectionId === undefined);
        if (hasDefaultTypes) {
            entries.push({
                id: null,
                name: 'defaultTypes',
                location: null,
                language: 'typescript'
            });
        }
        for (const [id, info] of this.collectionInfo) {
            const entry = {
                id,
                name: info.variableName,
                location: `${info.sourceFile}:${info.line}:${info.column}`,
                language: 'typescript'
            };
            entries.push(entry);
        }
        return entries;
    }
    /**
     * Get collected usages
     */
    getUsages() {
        return this.usages;
    }
    /**
     * Get collected EDS usages
     */
    getEDSUsages() {
        return this.edsUsages;
    }
    /**
     * Get collected flow usages
     */
    getFlowUsages() {
        return this.flowUsages;
    }
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
    getInstrumentationPoints() {
        const points = new Map();
        const addPoint = (point) => {
            const key = `${point.kind}|${point.className}|${point.location}|${point.scope}`;
            const existing = points.get(key);
            if (existing) {
                const merged = new Set([...existing.targets, ...point.targets]);
                existing.targets = Array.from(merged);
                return;
            }
            points.set(key, point);
        };
        for (const site of this.instrumentationSites) {
            const decl = this.instrumentationClassDecls.get(site.className);
            const point = {
                kind: site.kind,
                className: site.className,
                location: decl ? decl.location : site.location,
                code: decl ? decl.code : site.code,
                scope: site.scope,
                targets: site.targets,
            };
            addPoint(point);
        }
        // Heritage-declared classes always emit a declaration point with
        // scope 'module' (attachment statically unknown); registration
        // sites above carry the narrower scopes as separate entries
        for (const [className, decl] of this.instrumentationClassDecls) {
            if (!decl.kind) {
                continue;
            }
            const point = {
                kind: decl.kind,
                className: className,
                location: decl.location,
                code: decl.code,
                scope: 'module',
                targets: [],
            };
            addPoint(point);
        }
        const result = Array.from(points.values());
        return result;
    }
    /**
     * Add a topologica type to the analyzer for usage tracking.
     * This allows the analyzer to recognize topologica types when collecting usages.
     */
    addTopologicaType(fullPath, node) {
        // Skip if already exists
        if (this.graph.allTypes.has(fullPath)) {
            return;
        }
        // Add to graph so it can be found during usage collection
        if (node.parent) {
            // Add as child of parent
            this.graph.addChild(node.parent, node);
        }
        else {
            // Add as root
            this.graph.addRoot(node);
        }
        // Also add to definitions so it's recognized as a known type
        const definition = {
            name: node.name,
            location: `${node.sourceFile}:${node.line}:${node.column}`,
            kind: 'define',
            parent: node.parent ? node.parent.fullPath : null,
            strictChain: true,
            blockErrors: false
        };
        this.definitions.set(fullPath, definition);
    }
    /**
     * Set parent nodes in a source file to enable AST traversal up
     */
    setParentNodesInSourceFile(sourceFile) {
        const setParent = (node, parent) => {
            // TypeScript doesn't expose parent as writable, but we need it
            // eslint-disable-next-line @typescript-eslint/no-explicit-any
            node.parent = parent;
            ts.forEachChild(node, child => setParent(child, node));
        };
        setParent(sourceFile);
    }
    /**
     * Visit a node in the AST
     */
    visitNode(node, sourceFile, currentClass) {
        // Track mnemonica module-object aliases and custom collection variables
        // before processing define()/lookup() calls so source resolution works.
        this.trackImports(node);
        this.trackModuleObjectAliases(node);
        this.trackCollectionAliases(node, sourceFile);
        this.trackBuilderExportAssignment(node);
        this.trackConstructorBinding(node);
        // Check for define() calls
        if (this.isDefineCall(node)) {
            this.processDefineCall(node, sourceFile);
        }
        // Check for lazy() calls
        if (this.isLazyCall(node)) {
            this.processLazyCall(node, sourceFile);
        }
        // Check for decorate() decorator
        if (this.isDecorateDecorator(node)) {
            this.processDecorateDecorator(node, sourceFile, currentClass);
        }
        // Check for type usages (new Type(), type annotations, etc.)
        this.collectUsage(node, sourceFile);
        // Check for EDS patterns (wrap, current, getFlow, etc.)
        this.collectEDS(node, sourceFile);
        // Check for native flow patterns (property access, method calls, etc.)
        this.collectFlow(node, sourceFile);
        // Check for framework instrumentation points (vocabulary supplied
        // by plugins; syntactic only — no type checker)
        this.collectInstrumentation(node, sourceFile);
        // Collect referenced-type declarations (aliases, classes, interfaces)
        // per file, and the file's import wiring, for import-aware resolution
        this.trackReferencedTypeDeclaration(node);
        this.trackReferencedTypeImport(node);
        this.trackReferencedTypeReExport(node);
        this.trackReferencedTypeConstArray(node);
        // Track same-file function bindings so EDS can resolve wrap(fn)
        // arguments without the type checker (best effort, last wins)
        if (ts.isFunctionDeclaration(node) && node.name) {
            const key = `${sourceFile.fileName}#${node.name.text}`;
            this.functionBindings.set(key, node);
        }
        if (ts.isVariableDeclaration(node) &&
            ts.isIdentifier(node.name) &&
            node.initializer &&
            (ts.isArrowFunction(node.initializer) || ts.isFunctionExpression(node.initializer))) {
            const key = `${sourceFile.fileName}#${node.name.text}`;
            this.functionBindings.set(key, node.initializer);
        }
        // Track class declarations for decorator parent lookup
        if (ts.isClassDeclaration(node)) {
            // Visit children with this class as the current context
            ts.forEachChild(node, child => this.visitNode(child, sourceFile, node));
        }
        else {
            // Recursively visit children
            ts.forEachChild(node, child => this.visitNode(child, sourceFile, currentClass));
        }
    }
    trackConstructorBinding(node) {
        let name;
        let handler;
        if (ts.isVariableDeclaration(node) && ts.isIdentifier(node.name) && node.initializer) {
            name = node.name.text;
            handler = node.initializer;
        }
        else if ((ts.isFunctionDeclaration(node) || ts.isClassDeclaration(node)) && node.name) {
            name = node.name.text;
            handler = node;
        }
        if (!name || !handler) {
            return;
        }
        const filePath = this.currentReferencedTypeFile;
        let bindings = this.constructorBindings.get(filePath);
        if (!bindings) {
            bindings = new Map();
            this.constructorBindings.set(filePath, bindings);
        }
        bindings.set(name, handler);
    }
    /**
     * Does an import specifier name the generated output? A conventional
     * `.tactica` path always does; otherwise the specifier is resolved with
     * the program's compilerOptions (tsconfig `paths` included) as if the
     * generated files existed — on a fresh clone they are not written yet.
     */
    isGeneratedTypeSpecifier(specifier) {
        if (specifier.includes('.tactica')) {
            return true;
        }
        const outputDirs = this.generatedOutputDirs;
        if (outputDirs.length === 0) {
            return false;
        }
        const cacheKey = `${this.currentReferencedTypeFile}::${specifier}`;
        const cached = this.generatedSpecifierCache.get(cacheKey);
        if (cached !== undefined) {
            return cached;
        }
        const insideOutput = (fileOrDir) => {
            const absolute = nodePath.resolve(fileOrDir);
            const inside = outputDirs.some(dir => absolute === dir || absolute.startsWith(dir + nodePath.sep));
            return inside;
        };
        const host = {
            fileExists: fileName => insideOutput(fileName) || ts.sys.fileExists(fileName),
            readFile: fileName => ts.sys.readFile(fileName),
            directoryExists: directoryName => insideOutput(directoryName) || ts.sys.directoryExists(directoryName),
        };
        const resolved = ts.resolveModuleName(specifier, this.currentReferencedTypeFile, this.referencedTypeCompilerOptions, host).resolvedModule;
        const result = resolved !== undefined && insideOutput(resolved.resolvedFileName);
        this.generatedSpecifierCache.set(cacheKey, result);
        return result;
    }
    /**
     * Track imports from 'mnemonica' so aliases of the module object and
     * createTypesCollection are recognized without relying on the type checker.
     */
    trackImports(node) {
        if (!ts.isImportDeclaration(node)) {
            return;
        }
        const { moduleSpecifier } = node;
        if (ts.isStringLiteral(moduleSpecifier) && this.isGeneratedTypeSpecifier(moduleSpecifier.text)) {
            let imports = this.generatedTypeImports.get(this.currentReferencedTypeFile);
            if (!imports) {
                imports = new Set();
                this.generatedTypeImports.set(this.currentReferencedTypeFile, imports);
            }
            const generatedClause = node.importClause;
            if (generatedClause?.name) {
                imports.add(generatedClause.name.text);
            }
            if (generatedClause?.namedBindings && ts.isNamedImports(generatedClause.namedBindings)) {
                for (const element of generatedClause.namedBindings.elements) {
                    imports.add(element.name.text);
                }
            }
            if (generatedClause?.namedBindings && ts.isNamespaceImport(generatedClause.namedBindings)) {
                imports.add(generatedClause.namedBindings.name.text);
            }
        }
        if (!ts.isStringLiteral(moduleSpecifier) || moduleSpecifier.text !== 'mnemonica') {
            return;
        }
        const clause = node.importClause;
        if (!clause) {
            return;
        }
        // import { mnemonica, createTypesCollection } from 'mnemonica'
        if (clause.namedBindings && ts.isNamedImports(clause.namedBindings)) {
            for (const element of clause.namedBindings.elements) {
                const localName = element.name.text;
                const importedName = element.propertyName
                    ? element.propertyName.text
                    : localName;
                if (importedName === 'mnemonica') {
                    this.moduleObjectVariables.add(localName);
                }
                if (importedName === 'createTypesCollection') {
                    this.createTypesCollectionVariables.add(localName);
                }
                let fileImports = this.mnemonicaNamedImports.get(this.currentReferencedTypeFile);
                if (!fileImports) {
                    fileImports = new Map();
                    this.mnemonicaNamedImports.set(this.currentReferencedTypeFile, fileImports);
                }
                fileImports.set(localName, importedName);
            }
        }
        // import * as mnemonica from 'mnemonica'
        if (clause.namedBindings && ts.isNamespaceImport(clause.namedBindings)) {
            this.moduleObjectVariables.add(clause.namedBindings.name.text);
        }
        // import mnemonica from 'mnemonica' (default import) — treat as module object too
        if (clause.name) {
            this.moduleObjectVariables.add(clause.name.text);
        }
    }
    /**
     * Record a named referenced-type declaration (type alias, class, or
     * interface) for the file currently being visited.
     */
    trackReferencedTypeDeclaration(node) {
        // Namespaces are the middle segments of qualified references
        // (models.Inner.Crate) — recorded separately from the plain-name
        // declaration table (string-named `module '…'` declarations are
        // ambient externals and stay out)
        if (ts.isModuleDeclaration(node) && ts.isIdentifier(node.name) &&
            node.body && ts.isModuleBlock(node.body)) {
            const namespaceFilePath = this.currentReferencedTypeFile;
            let namespaces = this.referencedTypeNamespaces.get(namespaceFilePath);
            if (!namespaces) {
                namespaces = new Map();
                this.referencedTypeNamespaces.set(namespaceFilePath, namespaces);
            }
            namespaces.set(node.name.text, node);
            return;
        }
        let name = '';
        let kind;
        let declNode;
        if (ts.isTypeAliasDeclaration(node) && ts.isIdentifier(node.name)) {
            name = node.name.text;
            kind = 'alias';
            declNode = node;
        }
        else if (ts.isClassDeclaration(node) && node.name) {
            name = node.name.text;
            kind = 'class';
            declNode = node;
        }
        else if (ts.isInterfaceDeclaration(node) && ts.isIdentifier(node.name)) {
            name = node.name.text;
            kind = 'interface';
            declNode = node;
        }
        if (!kind || !declNode || !name) {
            return;
        }
        const filePath = this.currentReferencedTypeFile;
        let decls = this.referencedTypeDecls.get(filePath);
        if (!decls) {
            decls = new Map();
            this.referencedTypeDecls.set(filePath, decls);
        }
        const entry = { kind, node: declNode, file: filePath };
        decls.set(name, entry);
        // `export default class Foo {}` is also reachable under the 'default'
        // binding for default importers
        if (kind === 'class') {
            const classNode = declNode;
            const isExported = classNode.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword) ?? false;
            const isDefault = classNode.modifiers?.some(m => m.kind === ts.SyntaxKind.DefaultKeyword) ?? false;
            if (isExported && isDefault) {
                decls.set('default', entry);
            }
        }
    }
    /**
     * Record consts initialized with an array literal (optionally wrapped in
     * `as const` / `satisfies`), so a `typeof statusList[number]` field type
     * expands to the element literal union — the generated file carries no
     * imports, so emitting the bare `typeof statusList` query would be an
     * unresolvable name downstream. First binding wins: a nested shadow
     * must not replace the module-level const the typeof refers to.
     */
    trackReferencedTypeConstArray(node) {
        if (!ts.isVariableDeclaration(node) || !ts.isIdentifier(node.name) || !node.initializer) {
            return;
        }
        const { initializer: rawInitializer } = node;
        let initializer = rawInitializer;
        while (ts.isAsExpression(initializer) ||
            ts.isSatisfiesExpression(initializer) ||
            // the angle-bracket assertion spelling (`<const>[…]`) is the
            // same const-array marker as the `as const` form (F17)
            ts.isTypeAssertionExpression(initializer)) {
            initializer = initializer.expression;
        }
        if (!ts.isArrayLiteralExpression(initializer)) {
            return;
        }
        const filePath = this.currentReferencedTypeFile;
        let consts = this.referencedTypeConstArrays.get(filePath);
        if (!consts) {
            consts = new Map();
            this.referencedTypeConstArrays.set(filePath, consts);
        }
        if (!consts.has(node.name.text)) {
            consts.set(node.name.text, initializer);
        }
    }
    /**
     * Find the array literal behind a module const referenced through
     * `typeof`: the declaring file's own consts first (the F13 case is a
     * NON-exported const in the same module as the expanded class), then —
     * when the file imports the name — the imported module's consts.
     * External modules are never analyzed, so those yield nothing.
     */
    findReferencedConstArray(name, fromFile) {
        const local = this.referencedTypeConstArrays.get(fromFile)?.get(name);
        if (local) {
            return local;
        }
        const imported = this.referencedTypeImports.get(fromFile)?.get(name);
        if (!imported || imported.isNamespace) {
            return undefined;
        }
        const resolution = this.resolveReferencedTypeModule(imported.specifier, fromFile);
        if (!resolution || resolution.isExternal) {
            return undefined;
        }
        const found = this.referencedTypeConstArrays.get(resolution.resolvedPath)?.get(imported.originalName);
        return found;
    }
    /**
     * Element literal types of a tracked const array: every element must be
     * a plain literal (optionally wrapped in `as const` / `satisfies` /
     * `<const>` assertions) — string, numeric (unary `-`/`+` preserved),
     * boolean, or null. Spreads, identifiers, and nested arrays mean the
     * union is not statically visible and yield undefined, so the caller
     * degrades the field to `unknown` rather than guessing.
     */
    literalTypesOfArray(arrayLiteral) {
        const literals = [];
        for (const element of arrayLiteral.elements) {
            if (ts.isSpreadElement(element)) {
                return undefined;
            }
            const literal = this.literalTypeOfExpression(element);
            if (literal === undefined) {
                return undefined;
            }
            literals.push(literal);
        }
        if (literals.length === 0) {
            return undefined;
        }
        const result = literals;
        return result;
    }
    /**
     * The literal type of one array element: a plain literal (optionally
     * wrapped in `as const` / `satisfies` / assertion expressions) —
     * string, numeric (unary `-`/`+` preserved), boolean, or null.
     * Anything else yields undefined.
     */
    literalTypeOfExpression(expr) {
        let inner = expr;
        while (ts.isAsExpression(inner) || ts.isSatisfiesExpression(inner) || ts.isTypeAssertionExpression(inner)) {
            inner = inner.expression;
        }
        if (ts.isStringLiteral(inner) || ts.isNoSubstitutionTemplateLiteral(inner)) {
            const literal = `'${inner.text}'`;
            return literal;
        }
        if (ts.isPrefixUnaryExpression(inner) && ts.isNumericLiteral(inner.operand)) {
            if (inner.operator === ts.SyntaxKind.MinusToken) {
                const negative = `-${inner.operand.text}`;
                return negative;
            }
            if (inner.operator === ts.SyntaxKind.PlusToken) {
                return inner.operand.text;
            }
            return undefined;
        }
        if (ts.isNumericLiteral(inner)) {
            return inner.text;
        }
        if (inner.kind === ts.SyntaxKind.TrueKeyword) {
            return 'true';
        }
        if (inner.kind === ts.SyntaxKind.FalseKeyword) {
            return 'false';
        }
        if (inner.kind === ts.SyntaxKind.NullKeyword) {
            return 'null';
        }
        return undefined;
    }
    /**
     * F22: the const-assertion check shared by the value-level and
     * declaration-level paths — `expr as const` and `<const>expr` parse
     * identically (a TypeReferenceNode named 'const'). General `<T>expr`
     * assertions never match.
     */
    isConstAssertionType(type) {
        const constAssertion = ts.isTypeReferenceNode(type) &&
            ts.isIdentifier(type.typeName) &&
            type.typeName.text === 'const';
        return constAssertion;
    }
    /**
     * The array literal behind a value-level element access: inline
     * (`(<const>[…])[0]`, `([…] as const)[1]`), parenthesized, or a
     * tracked module const array (`const x = <const>[…]` / `x[0]`, F17
     * tracking). Only const assertions are unwrapped — general
     * assertions stay unknown (F22 scope boundary).
     */
    constArrayLiteralOf(expr) {
        let current = expr;
        while (ts.isParenthesizedExpression(current)) {
            current = current.expression;
        }
        if (ts.isArrayLiteralExpression(current)) {
            return current;
        }
        if ((ts.isAsExpression(current) || ts.isTypeAssertionExpression(current)) &&
            this.isConstAssertionType(current.type)) {
            const inner = current.expression;
            const literal = ts.isArrayLiteralExpression(inner) ? inner : undefined;
            return literal;
        }
        if (ts.isIdentifier(current)) {
            const tracked = this.referencedTypeConstArrays.get(this.currentReferencedTypeFile)?.get(current.text);
            return tracked;
        }
        return undefined;
    }
    /**
     * Emit-type for `typeof name` when `name` is a tracked const array: the
     * union of its element literal types (`'active' | 'closed'`). Every
     * other typeof source — non-array consts, functions, classes, names not
     * tracked at all — yields undefined, so the caller degrades the field
     * to `unknown`: a bare `typeof name` emitted into types.ts has no
     * import to resolve against downstream.
     */
    typeOfConstArrayUnion(name, fromFile) {
        const arrayLiteral = this.findReferencedConstArray(name, fromFile);
        if (!arrayLiteral) {
            return undefined;
        }
        const literals = this.literalTypesOfArray(arrayLiteral);
        if (!literals) {
            return undefined;
        }
        const union = literals.join(' | ');
        return union;
    }
    /**
     * Record the importing file's named/namespace/default import bindings so
     * referenced-type names resolve through the file's own import statements
     * (F10) rather than a program-wide name map.
     */
    trackReferencedTypeImport(node) {
        if (!ts.isImportDeclaration(node)) {
            return;
        }
        const { moduleSpecifier } = node;
        if (!ts.isStringLiteral(moduleSpecifier)) {
            return;
        }
        const clause = node.importClause;
        if (!clause) {
            return;
        }
        const filePath = this.currentReferencedTypeFile;
        let imports = this.referencedTypeImports.get(filePath);
        if (!imports) {
            imports = new Map();
            this.referencedTypeImports.set(filePath, imports);
        }
        // import { SharedShape } from '…' / import { SharedShape as S } from '…'
        if (clause.namedBindings && ts.isNamedImports(clause.namedBindings)) {
            for (const element of clause.namedBindings.elements) {
                const localName = element.name.text;
                const originalName = element.propertyName ? element.propertyName.text : localName;
                imports.set(localName, {
                    originalName,
                    specifier: moduleSpecifier.text,
                    isNamespace: false
                });
            }
        }
        // import * as models from '…' — resolved when a qualified name
        // (models.SharedShape) is encountered
        if (clause.namedBindings && ts.isNamespaceImport(clause.namedBindings)) {
            imports.set(clause.namedBindings.name.text, {
                originalName: '',
                specifier: moduleSpecifier.text,
                isNamespace: true
            });
        }
        // import SharedShape from '…' (default import)
        if (clause.name) {
            imports.set(clause.name.text, {
                originalName: 'default',
                specifier: moduleSpecifier.text,
                isNamespace: false
            });
        }
    }
    /**
     * Record re-export wiring (`export { X } from '…'`, `export * from '…'`,
     * `export { X as Y }`) so resolution can chase barrels to the origin
     * module. Mirrors ModuleGraphBuilder.resolveOrigin, name-based only.
     */
    trackReferencedTypeReExport(node) {
        if (!ts.isExportDeclaration(node)) {
            return;
        }
        const filePath = this.currentReferencedTypeFile;
        const { moduleSpecifier } = node;
        const specifierText = moduleSpecifier && ts.isStringLiteral(moduleSpecifier)
            ? moduleSpecifier.text
            : undefined;
        if (node.exportClause && ts.isNamedExports(node.exportClause)) {
            for (const element of node.exportClause.elements) {
                const exportedName = element.name.text;
                const localName = element.propertyName ? element.propertyName.text : exportedName;
                this.markBuilderExport(exportedName, localName, filePath, specifierText);
                if (specifierText) {
                    // export { X } from '…' / export { X as Y } from '…'
                    let reExports = this.referencedTypeReExports.get(filePath);
                    if (!reExports) {
                        reExports = new Map();
                        this.referencedTypeReExports.set(filePath, reExports);
                    }
                    reExports.set(exportedName, specifierText);
                }
                else if (localName !== exportedName) {
                    // export { X as Y } — same-file alias of a local declaration
                    let aliases = this.referencedTypeExportAliases.get(filePath);
                    if (!aliases) {
                        aliases = new Map();
                        this.referencedTypeExportAliases.set(filePath, aliases);
                    }
                    aliases.set(exportedName, localName);
                }
            }
            return;
        }
        if (node.exportClause && ts.isNamespaceExport(node.exportClause)) {
            // `export * as ns from '…'` — a nested module namespace; middle
            // segments of qualified references (barrel.Deep.Gadget) chase it
            if (specifierText) {
                let stars = this.referencedTypeNamespaceStars.get(filePath);
                if (!stars) {
                    stars = new Map();
                    this.referencedTypeNamespaceStars.set(filePath, stars);
                }
                stars.set(node.exportClause.name.text, specifierText);
            }
            return;
        }
        if (!node.exportClause && specifierText) {
            // export * from '…'
            let stars = this.referencedTypeExportStars.get(filePath);
            if (!stars) {
                stars = [];
                this.referencedTypeExportStars.set(filePath, stars);
            }
            stars.push(specifierText);
        }
    }
    /**
     * Resolve a module specifier from a containing file with the program's
     * compilerOptions (tsconfig `paths`, extensionless imports, index files).
     * Module resolution only — the no-getTypeChecker() precedent stays.
     */
    resolveReferencedTypeModule(specifier, containingFile) {
        const cacheKey = `${containingFile}::${specifier}`;
        if (this.referencedTypeResolutionCache.has(cacheKey)) {
            const cached = this.referencedTypeResolutionCache.get(cacheKey);
            return cached === undefined ? undefined : cached;
        }
        const resolution = ts.resolveModuleName(specifier, containingFile, this.referencedTypeCompilerOptions, ts.sys).resolvedModule;
        const result = resolution
            ? {
                resolvedPath: nodePath.resolve(resolution.resolvedFileName),
                isExternal: !!resolution.isExternalLibraryImport
            }
            : undefined;
        this.referencedTypeResolutionCache.set(cacheKey, result);
        const finalResult = result;
        return finalResult;
    }
    /**
     * Look up a name in one resolved module, chasing re-export barrels with a
     * bounded depth. External (node_modules) modules hold no in-project
     * declarations and stop the chase.
     */
    findReferencedTypeInModule(modulePath, name, depth) {
        if (depth > MAX_REEXPORT_CHASE_DEPTH) {
            return undefined;
        }
        const decls = this.referencedTypeDecls.get(modulePath);
        const direct = decls?.get(name);
        if (direct) {
            return direct;
        }
        // export { X as Y } — resolve through the local name
        const localAlias = this.referencedTypeExportAliases.get(modulePath)?.get(name);
        if (localAlias) {
            const aliased = decls?.get(localAlias);
            if (aliased) {
                return aliased;
            }
        }
        const reExports = this.referencedTypeReExports.get(modulePath);
        const reExportSpecifier = reExports?.get(name);
        if (reExportSpecifier) {
            const nextResolution = this.resolveReferencedTypeModule(reExportSpecifier, modulePath);
            if (nextResolution && !nextResolution.isExternal) {
                const found = this.findReferencedTypeInModule(nextResolution.resolvedPath, name, depth + 1);
                if (found) {
                    return found;
                }
            }
        }
        const stars = this.referencedTypeExportStars.get(modulePath);
        if (stars) {
            for (const starSpecifier of stars) {
                const nextResolution = this.resolveReferencedTypeModule(starSpecifier, modulePath);
                if (!nextResolution || nextResolution.isExternal) {
                    continue;
                }
                const found = this.findReferencedTypeInModule(nextResolution.resolvedPath, name, depth + 1);
                if (found) {
                    return found;
                }
            }
        }
        return undefined;
    }
    /**
     * Resolve a referenced type name as used in fromFile, import-aware:
     *   1. the file's own import statements (relative + tsconfig paths,
     *      chased through re-export barrels),
     *   2. the file's local declarations,
     *   3. the unique same-named declaration across scanned files.
     * Returns undefined when nothing matches (or the match is ambiguous),
     * in which case the caller falls back to `unknown`.
     */
    resolveReferencedTypeDeclaration(name, fromFile) {
        // 1. the file's own imports win — an import is never shadowed by a
        // same-named local declaration elsewhere in the program (F10)
        const imported = this.referencedTypeImports.get(fromFile)?.get(name);
        if (imported && !imported.isNamespace) {
            const resolution = this.resolveReferencedTypeModule(imported.specifier, fromFile);
            if (resolution && !resolution.isExternal) {
                const found = this.findReferencedTypeInModule(resolution.resolvedPath, imported.originalName, 0);
                if (found) {
                    return found;
                }
            }
        }
        // 2. local declaration in the referencing file itself
        const local = this.referencedTypeDecls.get(fromFile)?.get(name);
        if (local) {
            return local;
        }
        // 3. program-wide fallback, unique declaration only — ambiguity and
        // absence both yield undefined (the caller emits `unknown`).
        // External/ambient declarations (.d.ts, node_modules) do not
        // participate: a user-local declaration always wins over a
        // package-declared same-named type (the plain-TS tier of the
        // identity law; ambiguity among the remaining declarations is
        // validated separately as a hard fail)
        let unique;
        let count = 0;
        for (const [filePath, decls] of this.referencedTypeDecls) {
            if (this.isExternalDeclFile(filePath)) {
                continue;
            }
            const candidate = decls.get(name);
            if (candidate) {
                count++;
                unique = candidate;
                if (count > 1) {
                    return undefined;
                }
            }
        }
        const result = count === 1 ? unique : undefined;
        return result;
    }
    /**
     * External/ambient declaration files (.d.ts, anything under
     * node_modules) never participate in plain-TS referenced-type
     * resolution or the ambiguity law: they are not project source, the
     * CLI never analyzes them, and a user-local declaration always wins
     * over a package-declared same-named type.
     */
    isExternalDeclFile(file) {
        const external = file.endsWith('.d.ts') ||
            file.includes(`${nodePath.sep}node_modules${nodePath.sep}`);
        return external;
    }
    /**
     * Properties of a referenced class/interface/alias-of-literal declaration,
     * shared by `this:`-parameter expansion and inline type emission.
     * Inherited members are included: the extends chain is walked
     * (depth-capped, cycle-guarded) and parent fields merge first, the
     * declaration's own fields overriding on name clash.
     */
    referencedDeclarationProperties(decl) {
        const visited = new Set();
        const properties = this.referencedDeclarationPropertiesInner(decl, visited, 0);
        return properties;
    }
    /**
     * Fields of one member of an intersection alias: an inline literal, or
     * a named type resolved import-aware from the file declaring the alias.
     * A member that does not resolve (a generated type not written yet, an
     * external type) adds nothing.
     */
    intersectionMemberProperties(member, fromFile, visited, depth) {
        const properties = new Map();
        if (ts.isParenthesizedTypeNode(member)) {
            const inner = this.intersectionMemberProperties(member.type, fromFile, visited, depth);
            return inner;
        }
        if (ts.isTypeLiteralNode(member)) {
            this.collectTypeElementProperties([...member.members], properties);
            return properties;
        }
        if (ts.isTypeReferenceNode(member) && ts.isIdentifier(member.typeName)) {
            const memberDecl = this.resolveReferencedTypeDeclaration(member.typeName.text, fromFile);
            if (memberDecl) {
                const resolved = this.referencedDeclarationPropertiesInner(memberDecl, visited, depth);
                return resolved;
            }
        }
        return properties;
    }
    referencedDeclarationPropertiesInner(decl, visited, depth) {
        const ownProperties = new Map();
        const declNode = decl.node;
        const declName = declNode.name && ts.isIdentifier(declNode.name) ? declNode.name.text : '';
        const visitKey = `${decl.kind}:${decl.file}:${declName}`;
        if (depth > MAX_HERITAGE_DEPTH || visited.has(visitKey)) {
            return ownProperties;
        }
        visited.add(visitKey);
        if (decl.kind === 'class') {
            const classProps = this.extractClassProperties(decl.node);
            for (const [name, info] of classProps) {
                ownProperties.set(name, info);
            }
        }
        else if (decl.kind === 'interface') {
            const iface = decl.node;
            this.collectTypeElementProperties([...iface.members], ownProperties);
        }
        else {
            const aliasType = decl.node.type;
            if (ts.isTypeLiteralNode(aliasType)) {
                this.collectTypeElementProperties([...aliasType.members], ownProperties);
            }
            else if (ts.isIntersectionTypeNode(aliasType)) {
                // an intersection alias carries every member's fields; a later
                // member overrides an earlier one on name clash
                for (const member of aliasType.types) {
                    const memberProps = this.intersectionMemberProperties(member, decl.file, visited, depth + 1);
                    for (const [name, info] of memberProps) {
                        ownProperties.set(name, info);
                    }
                }
            }
            else {
                return ownProperties;
            }
        }
        // heritage merges parent fields first; the declaration's own fields
        // override on name clash (later bases override earlier ones)
        const merged = new Map();
        for (const baseDecl of this.resolveHeritageDeclarations(decl)) {
            const baseProps = this.referencedDeclarationPropertiesInner(baseDecl, visited, depth + 1);
            for (const [name, info] of baseProps) {
                merged.set(name, info);
            }
        }
        for (const [name, info] of ownProperties) {
            merged.set(name, info);
        }
        return merged;
    }
    /**
     * Property signatures of interface/alias type-literal members, into
     * the given map.
     */
    collectTypeElementProperties(members, properties) {
        for (const member of members) {
            if (ts.isPropertySignature(member) && ts.isIdentifier(member.name)) {
                const propName = member.name.text;
                const type = this.inferType(member.type);
                properties.set(propName, {
                    name: propName,
                    type,
                    optional: !!member.questionToken,
                });
            }
        }
    }
    /**
     * Resolve the heritage clause of a class (`extends Base`) or interface
     * (`extends A, B`) to referenced-type declarations through the SAME
     * import-aware machinery as plain references (the declaring file's own
     * imports first, then its locals, then the unique program-wide
     * declaration). Unresolvable or external bases yield nothing — their
     * inherited fields simply stay absent, same as before this walk
     * existed. Mixin calls (`extends mixin(X)`) and namespace access are
     * not followed.
     */
    resolveHeritageDeclarations(decl) {
        const { heritageClauses } = decl.node;
        if (!heritageClauses) {
            return [];
        }
        const bases = [];
        for (const clause of heritageClauses) {
            if (clause.token !== ts.SyntaxKind.ExtendsKeyword) {
                continue;
            }
            for (const heritageType of clause.types) {
                if (!ts.isIdentifier(heritageType.expression)) {
                    continue;
                }
                const baseName = heritageType.expression.text;
                const baseDecl = this.resolveReferencedTypeDeclaration(baseName, decl.file);
                if (baseDecl) {
                    bases.push(baseDecl);
                }
            }
        }
        const result = bases;
        return result;
    }
    /**
     * Expand a referenced-type declaration to a self-contained type string
     * for emission into generated files: type aliases through inferType,
     * classes and interfaces through their (public, non-method) fields.
     * Nested references resolve against the declaring file while expanding.
     */
    expandReferencedTypeDeclaration(decl) {
        const referencingFile = this.currentReferencedTypeFile;
        this.currentReferencedTypeFile = decl.file;
        try {
            const result = this.expandReferencedTypeDeclarationInner(decl);
            return result;
        }
        finally {
            this.currentReferencedTypeFile = referencingFile;
        }
    }
    expandReferencedTypeDeclarationInner(decl) {
        if (decl.kind === 'alias') {
            const aliasNode = decl.node;
            const aliasName = ts.isIdentifier(aliasNode.name) ? aliasNode.name.text : '';
            if (aliasName && this.expandingReferencedAliases.has(aliasName)) {
                // Self-referential alias chain — bail out
                return 'unknown';
            }
            if (aliasName) {
                this.expandingReferencedAliases.add(aliasName);
            }
            const expanded = this.inferType(aliasNode.type);
            if (aliasName) {
                this.expandingReferencedAliases.delete(aliasName);
            }
            return expanded;
        }
        const declProperties = this.referencedDeclarationProperties(decl);
        const props = Array.from(declProperties.entries()).map(([propName, info]) => {
            const optional = info.optional ? '?' : '';
            return `${propName}${optional}: ${info.type}`;
        });
        const result = `{ ${props.join('; ')} }`;
        return result;
    }
    /**
     * Emitted instance-type alias for a graph node — the name types.ts /
     * registry.ts actually declare. Option B collection types carry their
     * registry interface prefix; collection types WITHOUT a registry
     * interface are never emitted, so no valid alias exists for them
     * (undefined — callers degrade to `unknown`, never a bare name).
     */
    getEmittedInstanceTypeName(node) {
        if (node.collectionId && !node.registryInterfaceName) {
            return undefined;
        }
        const dotted = node.collectionId
            ? node.fullPath.slice(node.collectionId.length + 2)
            : node.fullPath;
        const prefix = node.registryInterfaceName ? `${node.registryInterfaceName}_` : '';
        const result = `${prefix}${dotted.replace(/\./g, '_')}`;
        return result;
    }
    /**
     * Resolve a simple (non-qualified) type reference: import-aware
     * declaration expansion first, then the InstanceType<typeof X> pattern,
     * then mnemonica graph types; known globals keep their bare name and
     * anything else falls back to `unknown` so generated files never carry
     * an unresolvable bare name. Returns undefined when the caller should
     * keep the generic spelling (handled separately).
     */
    resolveSimpleTypeReference(typeName, typeArgs, refNode) {
        // Import-aware referenced-type declaration (F10)
        const decl = this.resolveReferencedTypeDeclaration(typeName, this.currentReferencedTypeFile);
        if (decl) {
            const expanded = this.expandReferencedTypeDeclaration(decl);
            if (expanded !== undefined) {
                return expanded;
            }
            const unknownResult = 'unknown';
            return unknownResult;
        }
        // InstanceType<typeof X> law (0.2.0 behavior, restored): the
        // generated alias already IS the instance type — resolve X through
        // the graph tiers and drop the wrapper. Must run BEFORE the graph
        // resolution: 'InstanceType' is an ambient global, never a graph
        // type (the old special case below sat inside the graph-unique
        // branch and was dead code). When X does not resolve, the WHOLE
        // expression degrades to `unknown` — never emit
        // `InstanceType<unknown>`: invalid TS (TS2344, 'unknown' does not
        // satisfy the constructor constraint). Reached directly or through
        // a local alias (`XInstance = InstanceType<typeof X>`).
        if (typeName === 'InstanceType' && typeArgs && typeArgs.length === 1) {
            const [instanceArg] = typeArgs;
            if (instanceArg && ts.isTypeQueryNode(instanceArg) && ts.isIdentifier(instanceArg.exprName)) {
                const queryResult = this.resolveGraphTypeName(instanceArg.exprName.text);
                if (queryResult.status === 'unique') {
                    // undefined when the type is never emitted (collection
                    // without a registry interface) — degrade, never bare
                    const aliasResult = this.getEmittedInstanceTypeName(queryResult.node) ?? 'unknown';
                    return aliasResult;
                }
                if (queryResult.status === 'ambiguous') {
                    this.recordGraphReferenceError(instanceArg.exprName.text, instanceArg, queryResult);
                }
                const degradedResult = 'unknown';
                return degradedResult;
            }
            const inferredArg = this.inferType(instanceArg);
            if (inferredArg === 'unknown') {
                const degradedWrapper = 'unknown';
                return degradedWrapper;
            }
            const wrappedResult = `InstanceType<${inferredArg}>`;
            return wrappedResult;
        }
        // Mnemonica-graph identity law: path-aware resolution (value scope,
        // imports, nearest-chain, root, program-wide). Ambiguity between
        // real graph types is a hard failure; a name no graph type carries
        // stays in the plain-TS soft scope and falls to `unknown`.
        const graphResult = this.resolveGraphTypeName(typeName);
        if (graphResult.status === 'unique') {
            // Handle InstanceType<typeof X> pattern -> convert to Parent_X
            if (typeName === 'InstanceType' && typeArgs && typeArgs.length === 1) {
                const [arg] = typeArgs;
                if (arg.kind === ts.SyntaxKind.TypeQuery) {
                    const typeQuery = arg;
                    if (ts.isIdentifier(typeQuery.exprName)) {
                        const queryResult = this.resolveGraphTypeName(typeQuery.exprName.text);
                        if (queryResult.status === 'unique') {
                            // Emitted alias: Usages.UsageEntry -> Usages_UsageEntry
                            // (Option B collections carry the registry prefix;
                            // undefined when never emitted — degrade)
                            const queryAlias = this.getEmittedInstanceTypeName(queryResult.node) ?? 'unknown';
                            return queryAlias;
                        }
                        if (queryResult.status === 'ambiguous') {
                            this.recordGraphReferenceError(typeQuery.exprName.text, typeQuery, queryResult);
                        }
                        // Not a known mnemonica type — no bare emission
                        return 'unknown';
                    }
                }
            }
            if (!typeArgs || typeArgs.length === 0) {
                // Emitted alias: Usages.UsageEntry -> Usages_UsageEntry
                // (Option B collections carry the registry prefix;
                // undefined when never emitted — degrade)
                const graphAlias = this.getEmittedInstanceTypeName(graphResult.node) ?? 'unknown';
                return graphAlias;
            }
            // Generic use of a graph type keeps its simple name; the
            // generator upgrades it to the full-path instance type name
            return `${typeName}<${typeArgs.map(a => this.inferType(a)).join(', ')}>`;
        }
        if (graphResult.status === 'ambiguous') {
            this.recordGraphReferenceError(typeName, refNode ?? this.currentReferencedTypeFile, graphResult);
        }
        if (typeArgs && typeArgs.length > 0) {
            if (KNOWN_GLOBAL_TYPES.has(typeName)) {
                const genericResult = `${typeName}<${typeArgs.map(a => this.inferType(a)).join(', ')}>`;
                return genericResult;
            }
            // Emission restoration (0.2.0 behavior): a non-graph outer
            // generic that is NOT declared in any analyzed project file is
            // an ambient/lib construct (MapIterator, lib helpers) — it
            // resolves in every consumer compilation without an import, so
            // emit it VERBATIM with inner graph aliases resolved. A name
            // declared in project files stays unknown: the self-contained
            // types.ts can carry neither the bare name nor an import.
            if (!this.isProjectDeclaredTypeName(typeName)) {
                const verbatimResult = `${typeName}<${typeArgs.map(a => this.inferType(a)).join(', ')}>`;
                return verbatimResult;
            }
            // Generic reference to a non-global, non-graph PROJECT-LOCAL
            // type cannot be emitted bare into the generated file
            if (refNode) {
                this.recordPlainTypeReferenceSite(typeName, refNode);
            }
            return 'unknown';
        }
        const fallbackResult = this.unresolvedTypeReferenceFallback(typeName, refNode);
        return fallbackResult;
    }
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
    inferQualifiedTypeReference(typeRef) {
        if (!ts.isQualifiedName(typeRef.typeName)) {
            return undefined;
        }
        // flatten the qualified name chain: models.Inner.Crate → ['models', 'Inner', 'Crate']
        const segments = [];
        let chain = typeRef.typeName;
        while (ts.isQualifiedName(chain)) {
            segments.unshift(chain.right.text);
            chain = chain.left;
        }
        segments.unshift(chain.text);
        const namespaceImport = this.referencedTypeImports.get(this.currentReferencedTypeFile)?.get(segments[0]);
        if (!namespaceImport || !namespaceImport.isNamespace) {
            return undefined;
        }
        const resolution = this.resolveReferencedTypeModule(namespaceImport.specifier, this.currentReferencedTypeFile);
        if (!resolution || resolution.isExternal) {
            return undefined;
        }
        // descend the middle segments: a module context resolves the segment
        // as a namespace declaration / namespace re-export; a namespace-block
        // context resolves it as a nested namespace declaration
        let qualifier = {
            modulePath: resolution.resolvedPath
        };
        for (let i = 1; i < segments.length - 1 && qualifier; i++) {
            const segment = segments[i];
            if (qualifier.block) {
                const nested = this.findNamespaceInBlock(qualifier.block, segment);
                if (nested?.body && ts.isModuleBlock(nested.body)) {
                    qualifier = { modulePath: qualifier.modulePath, block: nested.body };
                    continue;
                }
                qualifier = undefined;
                break;
            }
            const namespaceDecl = this.referencedTypeNamespaces.get(qualifier.modulePath)?.get(segment);
            if (namespaceDecl?.body && ts.isModuleBlock(namespaceDecl.body)) {
                qualifier = { modulePath: qualifier.modulePath, block: namespaceDecl.body };
                continue;
            }
            const starSpecifier = this.referencedTypeNamespaceStars.get(qualifier.modulePath)?.get(segment);
            if (starSpecifier) {
                const nextResolution = this.resolveReferencedTypeModule(starSpecifier, qualifier.modulePath);
                if (nextResolution && !nextResolution.isExternal) {
                    qualifier = { modulePath: nextResolution.resolvedPath };
                    continue;
                }
            }
            const reExportSpecifier = this.referencedTypeReExports.get(qualifier.modulePath)?.get(segment);
            if (reExportSpecifier) {
                const nextResolution = this.resolveReferencedTypeModule(reExportSpecifier, qualifier.modulePath);
                const reExported = nextResolution && !nextResolution.isExternal
                    ? this.referencedTypeNamespaces.get(nextResolution.resolvedPath)?.get(segment)
                    : undefined;
                if (reExported?.body && ts.isModuleBlock(reExported.body)) {
                    qualifier = { modulePath: nextResolution.resolvedPath, block: reExported.body };
                    continue;
                }
            }
            qualifier = undefined;
        }
        const finalName = segments[segments.length - 1];
        let decl;
        if (qualifier?.block) {
            decl = this.findReferencedTypeInBlock(qualifier.block, qualifier.modulePath, finalName);
        }
        else if (qualifier) {
            decl = this.findReferencedTypeInModule(qualifier.modulePath, finalName, 0);
        }
        // legacy fallback: rightmost name anywhere in the head module
        // (namespace-nested declarations are also recorded by plain name)
        if (!decl) {
            decl = this.findReferencedTypeInModule(resolution.resolvedPath, finalName, 0);
        }
        if (!decl) {
            return undefined;
        }
        const expanded = this.expandReferencedTypeDeclaration(decl);
        return expanded;
    }
    /**
     * Find a namespace declaration by name directly inside a module block.
     */
    findNamespaceInBlock(block, name) {
        for (const statement of block.statements) {
            if (ts.isModuleDeclaration(statement) && ts.isIdentifier(statement.name) &&
                statement.name.text === name) {
                const result = statement;
                return result;
            }
        }
        return undefined;
    }
    /**
     * Find a named type declaration (alias, class, interface) directly inside
     * a namespace block — the final segment of a descended qualified chain.
     */
    findReferencedTypeInBlock(block, filePath, name) {
        for (const statement of block.statements) {
            if (ts.isTypeAliasDeclaration(statement) && ts.isIdentifier(statement.name) &&
                statement.name.text === name) {
                const result = { kind: 'alias', node: statement, file: filePath };
                return result;
            }
            if (ts.isClassDeclaration(statement) && statement.name && statement.name.text === name) {
                const result = { kind: 'class', node: statement, file: filePath };
                return result;
            }
            if (ts.isInterfaceDeclaration(statement) && ts.isIdentifier(statement.name) &&
                statement.name.text === name) {
                const result = { kind: 'interface', node: statement, file: filePath };
                return result;
            }
        }
        return undefined;
    }
    /**
     * Fallback for a type-reference name that resolves to no declaration and
     * no graph type: known globals keep their bare name (they resolve without
     * an import); everything else becomes `unknown` so generated types.ts
     * never carries an unresolvable bare name (README's documented behavior)
     * and the site is recorded for the plain-TS ambiguity validation.
     */
    unresolvedTypeReferenceFallback(typeName, refNode) {
        if (KNOWN_GLOBAL_TYPES.has(typeName)) {
            return typeName;
        }
        if (refNode) {
            this.recordPlainTypeReferenceSite(typeName, refNode);
        }
        const result = 'unknown';
        return result;
    }
    /**
     * Record one define()/lazy()/@decorate() site under its runtime
     * namespace key. Two sites in one namespace are a same-namespace
     * duplicate (the runtime throws ALREADY_DECLARED); every site is kept
     * so the failure can report all locations.
     */
    recordDefineSite(namespaceKey, location) {
        let sites = this.defineSites.get(namespaceKey);
        if (!sites) {
            sites = [];
            this.defineSites.set(namespaceKey, sites);
        }
        if (!sites.includes(location)) {
            sites.push(location);
        }
    }
    /**
     * Fatal resolution failures (hard-fail law): same-namespace duplicate
     * mnemonica definitions plus ambiguous/unresolved mnemonica-graph
     * references. The CLI prints every location and writes no output.
     */
    getResolutionErrors() {
        this.validateLookupReferences();
        this.validatePlainTypeReferences();
        const errors = [];
        for (const [namespaceKey, sites] of this.defineSites) {
            if (sites.length < 2) {
                continue;
            }
            const displayName = namespaceKey.replace(/^[^:]+::/, '');
            const message = `Duplicate definition of '${displayName}' in one namespace — ` +
                'the mnemonica runtime would throw ALREADY_DECLARED';
            errors.push({ message, locations: [...sites] });
        }
        for (const error of this.graphReferenceErrors) {
            errors.push(error);
        }
        const result = errors;
        return result;
    }
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
    resolveGraphTypeName(name) {
        // 1. value scope in the referencing file itself
        const localBinding = this.fileGraphBindings.get(this.currentReferencedTypeFile)?.get(name);
        if (localBinding) {
            const node = this.graph.findType(localBinding);
            if (node) {
                const valueResult = { status: 'unique', node };
                return valueResult;
            }
        }
        // 2. import scope — the imported module's exported binding
        const imported = this.referencedTypeImports.get(this.currentReferencedTypeFile)?.get(name);
        if (imported && !imported.isNamespace) {
            const resolution = this.resolveReferencedTypeModule(imported.specifier, this.currentReferencedTypeFile);
            if (resolution && !resolution.isExternal) {
                const fullPath = this.findGraphBindingInModule(resolution.resolvedPath, imported.originalName, 0);
                if (fullPath) {
                    const node = this.graph.findType(fullPath);
                    if (node) {
                        const importResult = { status: 'unique', node };
                        return importResult;
                    }
                }
            }
        }
        // 3-5. chain / root / program-wide tiers
        const result = (0, graph_1.resolveGraphTypeReference)(this.graph, name, this.currentGraphAnchor);
        return result;
    }
    /**
     * Find a graph constructor binding exported by a resolved module,
     * chasing re-export barrels with a bounded depth.
     */
    findGraphBindingInModule(modulePath, name, depth) {
        if (depth > MAX_REEXPORT_CHASE_DEPTH) {
            return undefined;
        }
        const direct = this.fileGraphBindings.get(modulePath)?.get(name);
        if (direct) {
            return direct;
        }
        const reExports = this.referencedTypeReExports.get(modulePath);
        const reExportSpecifier = reExports?.get(name);
        if (reExportSpecifier) {
            const nextResolution = this.resolveReferencedTypeModule(reExportSpecifier, modulePath);
            if (nextResolution && !nextResolution.isExternal) {
                const found = this.findGraphBindingInModule(nextResolution.resolvedPath, name, depth + 1);
                if (found) {
                    return found;
                }
            }
        }
        const stars = this.referencedTypeExportStars.get(modulePath);
        if (stars) {
            for (const starSpecifier of stars) {
                const nextResolution = this.resolveReferencedTypeModule(starSpecifier, modulePath);
                if (!nextResolution || nextResolution.isExternal) {
                    continue;
                }
                const found = this.findGraphBindingInModule(nextResolution.resolvedPath, name, depth + 1);
                if (found) {
                    return found;
                }
            }
        }
        return undefined;
    }
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
    validateLookupReferences() {
        if (this.lookupReferencesValidated) {
            return;
        }
        this.lookupReferencesValidated = true;
        // group sites by path: every failing site of the same path is listed
        const sitesByPath = new Map();
        for (const ref of this.lookupReferences) {
            const sites = sitesByPath.get(ref.path) ?? [];
            sites.push(ref.location);
            sitesByPath.set(ref.path, sites);
        }
        for (const [typePath, sites] of sitesByPath) {
            if (this.graph.findType(typePath)) {
                continue;
            }
            // did-you-mean: types carrying the same name anywhere in the
            // graph (never a first-match pick — the full list only)
            const unprefixed = typePath.replace(/^[^:]+::/, '');
            const lastSegment = unprefixed.split('.').pop() ?? unprefixed;
            const candidates = this.graph.getAllTypes().filter(t => t.name === lastSegment);
            if (candidates.length === 0) {
                const noneError = {
                    message: `Unresolved lookup of mnemonica type '${typePath}': no type at that path — ` +
                        'the runtime would return undefined',
                    locations: sites,
                };
                this.graphReferenceErrors.push(noneError);
                continue;
            }
            const candidateLocations = candidates.map(n => `${n.sourceFile}:${n.line}:${n.column}`);
            const candidatePaths = candidates.map(n => n.fullPath).join(', ');
            const ambiguousError = {
                message: `Unresolved lookup of mnemonica type '${typePath}': the runtime would return ` +
                    `undefined — ${candidates.length} graph type(s) carry the name ` +
                    `off-root (${candidatePaths}); use the full dotted path`,
                locations: [...sites, ...candidateLocations],
            };
            this.graphReferenceErrors.push(ambiguousError);
        }
    }
    /**
     * Record a plain-TS type reference site that resolved to nothing and
     * fell back to `unknown`, for the lazily-run ambiguity validation.
     * Deduped by (name, location): inferType can visit the same node more
     * than once per pass (constructor params + property inference).
     */
    recordPlainTypeReferenceSite(name, refNode) {
        const location = this.nodeLocation(refNode);
        const file = this.currentReferencedTypeFile;
        const already = this.plainTypeReferences.some((ref) => ref.name === name && ref.location === location);
        if (already) {
            return;
        }
        this.plainTypeReferences.push({ name, location, file });
    }
    /**
     * Project-source declaration files carrying `name` — one entry per
     * file, so same-file interface merging counts once (not ambiguous).
     * External/ambient declarations (.d.ts, anything under node_modules)
     * never count: a user-local declaration always wins over a package-
     * declared same-named type, so an external collision stays soft.
     */
    plainTypeDeclarationFiles(name) {
        const files = [];
        for (const [file, decls] of this.referencedTypeDecls) {
            if (!this.isExternalDeclFile(file) && decls.has(name)) {
                files.push(file);
            }
        }
        return files;
    }
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
    validatePlainTypeReferences() {
        if (this.plainTypeReferencesValidated) {
            return;
        }
        this.plainTypeReferencesValidated = true;
        const sitesByName = new Map();
        for (const ref of this.plainTypeReferences) {
            const sites = sitesByName.get(ref.name) ?? [];
            sites.push(ref);
            sitesByName.set(ref.name, sites);
        }
        for (const [name, sites] of sitesByName) {
            // an import binding in the referencing file anchors the name —
            // the author already disambiguated (the import may just point
            // at an unanalyzable external module, which stays soft)
            const unanchored = sites.filter((site) => !this.referencedTypeImports.get(site.file)?.has(name));
            if (unanchored.length === 0) {
                continue;
            }
            const declFiles = this.plainTypeDeclarationFiles(name);
            if (declFiles.length < 2) {
                continue;
            }
            const message = `Ambiguous reference to type '${name}': ${declFiles.length} declarations ` +
                'share the name and no import disambiguates — import the one you mean';
            const declLocations = declFiles.map((file) => this.plainDeclLocation(file, name));
            const error = {
                message,
                locations: [...unanchored.map((site) => site.location), ...declLocations]
            };
            this.graphReferenceErrors.push(error);
        }
    }
    /**
     * `file:line:column` of a recorded declaration, for the ambiguity
     * report. Nodes recorded during traversal keep their positions; a
     * synthetic/unpositioned node falls back to the file itself.
     */
    plainDeclLocation(file, name) {
        const decl = this.referencedTypeDecls.get(file)?.get(name);
        const node = decl?.node;
        let location = `${file}:1:1`;
        if (node && node.pos >= 0) {
            const sourceFile = node.getSourceFile();
            const line = sourceFile.getLineAndCharacterOfPosition(node.getStart()).line + 1;
            const column = sourceFile.getLineAndCharacterOfPosition(node.getStart()).character + 1;
            location = `${file}:${line}:${column}`;
        }
        const result = location;
        return result;
    }
    /**
     * Record a hard-fail graph reference error with the reference site and
     * every candidate location.
     */
    recordGraphReferenceError(name, refNode, result) {
        const location = typeof refNode === 'string' ? refNode : this.nodeLocation(refNode);
        if (result.status === 'ambiguous') {
            const candidateLocations = result.candidates.map(n => `${n.sourceFile}:${n.line}:${n.column}`);
            const ambiguousMessage = `Ambiguous reference to mnemonica type '${name}': ` +
                `${result.candidates.length} types share the name and neither the parent chain ` +
                'nor the imports disambiguate';
            const ambiguousError = {
                message: ambiguousMessage,
                locations: [location, ...candidateLocations],
            };
            this.graphReferenceErrors.push(ambiguousError);
            return;
        }
        const unresolvedMessage = `Unresolved reference to mnemonica type '${name}': no type matches ` +
            'by value scope, imports, parent chain, or root path';
        const unresolvedError = { message: unresolvedMessage, locations: [location] };
        this.graphReferenceErrors.push(unresolvedError);
    }
    /**
     * Location (`file:line:column`) of an AST node, derived without parent
     * pointers when necessary.
     */
    nodeLocation(node) {
        let current = node;
        while (current && !ts.isSourceFile(current)) {
            current = current.parent;
        }
        if (!current) {
            const fallback = this.currentReferencedTypeFile;
            return fallback;
        }
        const start = node.getStart(current);
        const { line, character } = ts.getLineAndCharacterOfPosition(current, start);
        const location = `${current.fileName}:${line + 1}:${character + 1}`;
        return location;
    }
    /**
     * Track aliases of the mnemonica module object, e.g.:
     *   const m = mnemonica;
     *   const App = m;
     */
    trackModuleObjectAliases(node) {
        if (!ts.isVariableDeclaration(node) || !ts.isIdentifier(node.name)) {
            return;
        }
        const { initializer } = node;
        if (!initializer) {
            return;
        }
        if (ts.isIdentifier(initializer) && this.moduleObjectVariables.has(initializer.text)) {
            this.moduleObjectVariables.add(node.name.text);
        }
    }
    /**
     * Track custom collection variables, e.g.:
     *   const MyCollection = createTypesCollection();
     *   const Other = MyCollection;
     *
     * Also detects Option B user-provided registry interfaces:
     *   export interface MyCollectionRegistry {}
     *   const MyCollection = createTypesCollection<MyCollectionRegistry>();
     */
    trackCollectionAliases(node, sourceFile) {
        if (!ts.isVariableDeclaration(node) || !ts.isIdentifier(node.name)) {
            return;
        }
        const { initializer } = node;
        if (!initializer) {
            return;
        }
        // Direct createTypesCollection() call
        if (this.isCreateTypesCollectionCall(initializer)) {
            // The CLI re-analyzes every file on the usages pass (see resetUsages):
            // minting a fresh id here would re-register the collection's types
            // under a second `collectionId::` prefix and duplicate every emission.
            const collectionId = this.collectionVariables.get(node.name.text) ?? this.nextCollectionId();
            this.collectionVariables.set(node.name.text, collectionId);
            const registryInterfaceName = this.extractRegistryInterfaceName(initializer, sourceFile);
            const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart());
            this.collectionInfo.set(collectionId, {
                variableName: node.name.text,
                sourceFile: sourceFile.fileName,
                registryInterfaceName: registryInterfaceName,
                line: line + 1,
                column: character + 1
            });
            return;
        }
        // Alias of another collection variable
        if (ts.isIdentifier(initializer)) {
            const existing = this.collectionVariables.get(initializer.text);
            if (existing) {
                this.collectionVariables.set(node.name.text, existing);
            }
        }
    }
    /**
     * Extract the registry interface name from createTypesCollection<Registry>()
     * when the interface is declared in the same source file.
     */
    extractRegistryInterfaceName(call, sourceFile) {
        const typeArgs = call.typeArguments;
        if (!typeArgs || typeArgs.length === 0) {
            return undefined;
        }
        const [firstTypeArg] = typeArgs;
        if (!ts.isTypeReferenceNode(firstTypeArg) || !ts.isIdentifier(firstTypeArg.typeName)) {
            return undefined;
        }
        const name = firstTypeArg.typeName.text;
        // Confirm the interface exists in the same source file.
        for (const statement of sourceFile.statements) {
            if (ts.isInterfaceDeclaration(statement) &&
                statement.name.text === name) {
                return name;
            }
        }
        return undefined;
    }
    /**
     * Stamp a node with its collection's emission info: the Option B registry
     * interface name and the collection's home file — the module the generated
     * augmentation must target (the interface is confirmed declared there).
     * A type's own sourceFile is NOT the target: multi-file collections define
     * types across many modules while the interface lives at the
     * createTypesCollection() call site.
     */
    applyCollectionEmissionInfo(node, collectionId) {
        if (!collectionId) {
            return;
        }
        const info = this.collectionInfo.get(collectionId);
        if (!info) {
            return;
        }
        node.registryInterfaceName = info.registryInterfaceName;
        node.collectionSourceFile = info.sourceFile;
    }
    /**
     * Check if an expression is a createTypesCollection() call.
     * Handles:
     *   createTypesCollection()
     *   ctc() // aliased import
     *   mnemonica.createTypesCollection() // module object method
     *   m.createTypesCollection() // aliased module object
     */
    isCreateTypesCollectionCall(node) {
        if (!ts.isCallExpression(node)) {
            return false;
        }
        const expr = node.expression;
        // Direct call or aliased import: createTypesCollection() / ctc()
        if (ts.isIdentifier(expr)) {
            return expr.text === 'createTypesCollection' ||
                this.createTypesCollectionVariables.has(expr.text);
        }
        // Module object method: mnemonica.createTypesCollection()
        if (ts.isPropertyAccessExpression(expr) &&
            expr.name.text === 'createTypesCollection' &&
            ts.isIdentifier(expr.expression) &&
            this.moduleObjectVariables.has(expr.expression.text)) {
            return true;
        }
        return false;
    }
    /**
     * Generate a unique collection identifier.
     */
    nextCollectionId() {
        this.collectionCounter++;
        const result = `collection_${this.collectionCounter}`;
        return result;
    }
    /**
     * Check if a node is a define() call
     */
    isDefineCall(node) {
        if (!ts.isCallExpression(node)) {
            return false;
        }
        const { expression } = node;
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
     * Check if a node is a lazy() call
     */
    isLazyCall(node) {
        if (!ts.isCallExpression(node)) {
            return false;
        }
        const { expression } = node;
        // Check for direct call: lazy('TypeName', getter, ...)
        if (ts.isIdentifier(expression) && expression.text === 'lazy') {
            return true;
        }
        // Check for method call: SomeType.lazy('SubType', getter, ...)
        if (ts.isPropertyAccessExpression(expression)) {
            return expression.name?.text === 'lazy';
        }
        return false;
    }
    /**
        * Extract config options from an object literal
        */
    extractConfigFromObjectLiteral(configArg) {
        const config = {};
        for (const prop of configArg.properties) {
            if (ts.isPropertyAssignment(prop) && ts.isIdentifier(prop.name)) {
                const propName = prop.name.text;
                if (propName === 'strictChain' && prop.initializer.kind === ts.SyntaxKind.TrueKeyword) {
                    config.strictChain = true;
                }
                else if (propName === 'strictChain' && prop.initializer.kind === ts.SyntaxKind.FalseKeyword) {
                    config.strictChain = false;
                }
                else if (propName === 'blockErrors' && prop.initializer.kind === ts.SyntaxKind.TrueKeyword) {
                    config.blockErrors = true;
                }
                else if (propName === 'blockErrors' && prop.initializer.kind === ts.SyntaxKind.FalseKeyword) {
                    config.blockErrors = false;
                }
            }
        }
        return config;
    }
    /**
        * Extract config options from define() call
        */
    extractConfig(call) {
        // Config is the third argument: define('Name', handler, config)
        const [, , configArg] = call.arguments;
        if (!configArg || !ts.isObjectLiteralExpression(configArg)) {
            return {};
        }
        const configResult = this.extractConfigFromObjectLiteral(configArg);
        return configResult;
    }
    /**
        * Check if a node is a @decorate() decorator
        */
    isDecorateDecorator(node) {
        if (!ts.isDecorator(node)) {
            return false;
        }
        const { expression } = node;
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
            // Check for @MyCollection.decorate() where MyCollection is a custom collection
            if (ts.isPropertyAccessExpression(fnName) &&
                fnName.name.text === 'decorate' &&
                ts.isIdentifier(fnName.expression) &&
                this.collectionVariables.has(fnName.expression.text)) {
                return true;
            }
        }
        return false;
    }
    /**
     * Mark a call expression as processed and return whether it already was.
     */
    markProcessed(call) {
        if (this.processedCalls.has(call)) {
            return true;
        }
        this.processedCalls.add(call);
        return false;
    }
    /**
     * Process a define() call
     */
    processDefineCall(call, sourceFile) {
        // Check if this exact call has already been processed (prevents duplicates from chained calls)
        if (this.markProcessed(call)) {
            return;
        }
        const computedNames = this.extractComputedTypeNames(call);
        if (computedNames !== undefined) {
            for (const typeName of computedNames) {
                const computedContext = this.extractDefineContext(call, typeName);
                this.processDefineContext(call, sourceFile, computedContext, true);
            }
            return;
        }
        // Get the type name and source context from arguments
        const defineContext = this.extractDefineContext(call);
        this.processDefineContext(call, sourceFile, defineContext, false);
    }
    processDefineContext(call, sourceFile, defineContext, metadataOnly) {
        // For chained calls like define('A').define('B'), we want the position of the .define('B') part
        // not the start of the entire expression
        let positionNode = call;
        // If this is a chained call, get the position of the property access expression
        // which is the .define part
        if (ts.isPropertyAccessExpression(call.expression)) {
            // The expression is the property access: (define('RootAsync', ...)).define
            // We want the position of just the .define part
            // This is the 'define' identifier
            positionNode = call.expression.name;
        }
        const startPos = positionNode.getStart(sourceFile);
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, startPos);
        if (!defineContext.typeName) {
            this.errors.push({
                message: 'Could not extract type name from define() call',
                file: sourceFile.fileName,
                line: line + 1,
                column: character + 1,
            });
            return;
        }
        const { typeName } = defineContext;
        // Determine parent type and collection based on the call source.
        const parentNode = defineContext.parentType;
        const { collectionId } = defineContext;
        // Extract config options
        const config = this.extractConfig(call);
        // Create type node first so its internal fullPath (including any collection prefix) is resolved.
        const node = graph_1.TypeGraphImpl.createNode(typeName, parentNode, sourceFile.fileName, line + 1, character + 1, collectionId);
        this.applyCollectionEmissionInfo(node, collectionId);
        node.metadataOnly = metadataOnly;
        // Same-namespace duplicate detection (hard-fail law): key by the
        // runtime namespace — collection roots `<collection>::<name>`, or
        // `<parentFullPath>.<name>` for subtypes
        this.recordDefineSite(parentNode ? `${parentNode.fullPath}.${typeName}` : `${collectionId ?? 'default'}::${typeName}`, `${sourceFile.fileName}:${line + 1}:${character + 1}`);
        // Extract properties from constructor function — the new node anchors
        // relative-first graph reference resolution while its own signature
        // is being read
        const previousAnchor = this.currentGraphAnchor;
        this.currentGraphAnchor = node;
        try {
            node.properties = this.extractProperties(call);
            // Extract constructor parameters for TypeRegistry signature
            node.constructorParams = this.extractConstructorParams(call);
        }
        finally {
            this.currentGraphAnchor = previousAnchor;
        }
        const constructorExpr = this.extractConstructorExpression(call);
        node.instanceTypeOverride = this.hasAnyThisAnnotation(constructorExpr) ? 'any' : undefined;
        // Async constructor detection (async modifier, syntactic only)
        node.isAsync = this.isAsyncConstructHandler(this.extractConstructorExpression(call));
        // Add to graph
        if (parentNode) {
            this.graph.addChild(parentNode, node);
        }
        else {
            this.graph.addRoot(node);
        }
        // Create definition info using the node's resolved fullPath
        const definition = {
            name: typeName,
            location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
            kind: 'define',
            parent: parentNode ? parentNode.fullPath : null,
            strictChain: config.strictChain ?? true,
            blockErrors: config.blockErrors ?? false,
        };
        this.definitions.set(node.fullPath, definition);
        if (!metadataOnly) {
            this.edsScopeByNode.set(call, node.fullPath);
            // Track variable assignment: const User = define('UserEntity', ...) -> map "User" to "UserEntity"
            // A multi-hop initializer binds the LAST hop: define() returns the
            // defined type's constructor (F18)
            this.trackVariableAssignment(call, parentNode, node.fullPath, sourceFile);
        }
    }
    /**
     * Process a lazy() call
     */
    processLazyCall(call, sourceFile) {
        // Check if this exact call has already been processed (prevents duplicates from chained calls)
        if (this.markProcessed(call)) {
            return;
        }
        // Get the type name and source context from arguments
        const lazyContext = this.extractLazyContext(call, sourceFile);
        // For chained calls like define('A').lazy('B'), we want the position of the .lazy('B') part
        // not the start of the entire expression
        let positionNode = call;
        // If this is a chained call, get the position of the property access expression
        // which is the .lazy part
        if (ts.isPropertyAccessExpression(call.expression)) {
            // The expression is the property access: (define('RootAsync', ...)).lazy
            // We want the position of just the .lazy part
            // This is the 'lazy' identifier
            positionNode = call.expression.name;
        }
        const startPos = positionNode.getStart(sourceFile);
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, startPos);
        // The unnamed forms — lazy(getter), Type.lazy(getter, config?),
        // lazy(source, getter, config?) — throw TYPENAME_MUST_BE_A_STRING at
        // runtime (the name is required), so generating a type from the
        // getter's constructor name would bless code that crashes. They are
        // an analyzer error naming the call site and the required form.
        const lazyArgs = this.extractLazyCallArgs(call);
        if (lazyArgs && lazyArgs.name === undefined) {
            this.errors.push({
                message: 'lazy() requires a type name: lazy(\'Name\', getter)',
                file: sourceFile.fileName,
                line: line + 1,
                column: character + 1,
            });
            return;
        }
        if (!lazyContext.typeName) {
            this.errors.push({
                message: 'Could not extract type name from lazy() call',
                file: sourceFile.fileName,
                line: line + 1,
                column: character + 1,
            });
            return;
        }
        const { typeName } = lazyContext;
        // Determine parent type and collection based on the call source.
        const parentNode = lazyContext.parentType;
        const { collectionId } = lazyContext;
        // Extract config options
        const config = this.extractLazyConfig(call);
        // Create type node first so its internal fullPath (including any collection prefix) is resolved.
        const node = graph_1.TypeGraphImpl.createNode(typeName, parentNode, sourceFile.fileName, line + 1, character + 1, collectionId);
        this.applyCollectionEmissionInfo(node, collectionId);
        // Same-namespace duplicate detection (hard-fail law)
        this.recordDefineSite(parentNode ? `${parentNode.fullPath}.${typeName}` : `${collectionId ?? 'default'}::${typeName}`, `${sourceFile.fileName}:${line + 1}:${character + 1}`);
        // Extract properties from the constructor returned by the lazy getter
        // — the new node anchors relative-first graph reference resolution
        const previousAnchor = this.currentGraphAnchor;
        this.currentGraphAnchor = node;
        try {
            node.properties = this.extractProperties(call);
            // Extract constructor parameters for TypeRegistry signature
            node.constructorParams = this.extractConstructorParams(call);
        }
        finally {
            this.currentGraphAnchor = previousAnchor;
        }
        const constructorExpr = this.extractConstructorExpression(call);
        node.instanceTypeOverride = this.hasAnyThisAnnotation(constructorExpr) ? 'any' : undefined;
        // Async constructor detection (async modifier, syntactic only)
        node.isAsync = this.isAsyncConstructHandler(this.extractConstructorExpression(call));
        // Add to graph
        if (parentNode) {
            this.graph.addChild(parentNode, node);
        }
        else {
            this.graph.addRoot(node);
        }
        // Create definition info using the node's resolved fullPath
        const definition = {
            name: typeName,
            location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
            kind: 'define',
            parent: parentNode ? parentNode.fullPath : null,
            strictChain: config.strictChain ?? true,
            blockErrors: config.blockErrors ?? false,
        };
        this.definitions.set(node.fullPath, definition);
        this.edsScopeByNode.set(call, node.fullPath);
        // Track variable assignment: const LazyType = lazy('LazyType', ...) -> map "LazyType" -> "LazyType"
        // For chained calls like const X = lazy('A').define('B'), we want to map X -> A (the root)
        this.trackVariableAssignment(call, parentNode, node.fullPath, sourceFile);
    }
    /**
     * Extract lazy() call arguments into a normalized shape.
     * Handles named/unnamed and explicit-source forms, both as free calls
     * and as method calls. The unnamed shapes return `name: undefined` —
     * processLazyCall rejects them with an analyzer error (the runtime
     * requires the name), so no type is generated for them.
     */
    extractLazyCallArgs(call) {
        const args = call.arguments;
        const isMethodCall = ts.isPropertyAccessExpression(call.expression);
        if (isMethodCall) {
            // Source is the object of the property access: Type.lazy(...)
            const source = call.expression.expression;
            if (args.length === 0) {
                return undefined;
            }
            const [methodFirstArg] = args;
            if (ts.isStringLiteral(methodFirstArg)) {
                // Type.lazy('Name', getter, config?)
                if (args.length < 2) {
                    return undefined;
                }
                return {
                    source,
                    name: methodFirstArg.text,
                    getter: args[1],
                    config: args[2],
                };
            }
            // Type.lazy(getter, config?)
            return {
                source,
                getter: methodFirstArg,
                config: args[1],
            };
        }
        // Free call: lazy(...)
        if (args.length === 0) {
            return undefined;
        }
        const [firstArg] = args;
        // Explicit-source form: lazy(source, 'Name', getter, config?)
        // or lazy(source, getter, config?)
        if (args.length >= 2 && ts.isIdentifier(firstArg)) {
            const [, secondArg] = args;
            if (ts.isStringLiteral(secondArg)) {
                // lazy(source, 'Name', getter, config?)
                if (args.length < 3) {
                    return undefined;
                }
                return {
                    source: firstArg,
                    name: secondArg.text,
                    getter: args[2],
                    config: args[3],
                };
            }
            // lazy(source, getter, config?)
            return {
                source: firstArg,
                getter: secondArg,
                config: args[2],
            };
        }
        // Named root form: lazy('Name', getter, config?)
        if (ts.isStringLiteral(firstArg)) {
            if (args.length < 2) {
                return undefined;
            }
            return {
                name: firstArg.text,
                getter: args[1],
                config: args[2],
            };
        }
        // Unnamed root form: lazy(getter, config?)
        return {
            getter: firstArg,
            config: args[1],
        };
    }
    /**
     * Unwrap the constructor returned by a lazy getter.
     * Supports:
     *   () => class Name {}
     *   () => function Name() {}
     *   () => { return class Name {}; }
     *   function () { return function Name() {}; }
     */
    unwrapLazyGetter(getterExpr) {
        if (ts.isArrowFunction(getterExpr)) {
            const { body } = getterExpr;
            if (!ts.isBlock(body)) {
                return body;
            }
            for (const stmt of body.statements) {
                if (ts.isReturnStatement(stmt) && stmt.expression) {
                    return stmt.expression;
                }
            }
            return undefined;
        }
        if (ts.isFunctionExpression(getterExpr)) {
            const { body } = getterExpr;
            for (const stmt of body.statements) {
                if (ts.isReturnStatement(stmt) && stmt.expression) {
                    return stmt.expression;
                }
            }
            return undefined;
        }
        // Not a recognized getter pattern
        return undefined;
    }
    /**
     * Extract a constructor name from a class expression, class declaration,
     * or named function expression.
     */
    extractConstructorName(constructorExpr) {
        if (ts.isClassExpression(constructorExpr) && constructorExpr.name) {
            return constructorExpr.name.text;
        }
        if (ts.isClassDeclaration(constructorExpr) && constructorExpr.name) {
            return constructorExpr.name.text;
        }
        if (ts.isFunctionExpression(constructorExpr) && constructorExpr.name) {
            return constructorExpr.name.text;
        }
        return undefined;
    }
    /**
     * Extract the type name from either a define() or lazy() call.
     */
    extractMnemonicaTypeName(call) {
        if (this.isDefineCall(call)) {
            return this.extractTypeName(call);
        }
        if (this.isLazyCall(call)) {
            const args = this.extractLazyCallArgs(call);
            if (!args) {
                return undefined;
            }
            if (args.name) {
                return args.name;
            }
            const constructorExpr = this.unwrapLazyGetter(args.getter);
            if (constructorExpr) {
                return this.extractConstructorName(constructorExpr);
            }
        }
        return undefined;
    }
    /**
     * Extract the full lazy() call context: type name, parent type, and collection.
     * Handles direct calls, property-access calls, chained calls, and the
     * explicit-source form `lazy(source, 'TypeName', getter)`.
     */
    extractLazyContext(call, sourceFile) {
        const args = this.extractLazyCallArgs(call);
        if (!args) {
            return {};
        }
        let typeName = args.name;
        if (!typeName) {
            const constructorExpr = this.unwrapLazyGetter(args.getter);
            if (constructorExpr) {
                typeName = this.extractConstructorName(constructorExpr);
            }
        }
        if (!typeName) {
            return {};
        }
        const { expression } = call;
        // Direct call: lazy('TypeName', ...) or lazy(source, 'TypeName', getter)
        if (ts.isIdentifier(expression) && expression.text === 'lazy') {
            if (args.source && ts.isIdentifier(args.source)) {
                const sourceContext = this.resolveDefineSource(args.source.text);
                return {
                    typeName,
                    parentType: sourceContext.parentType,
                    collectionId: sourceContext.collectionId,
                };
            }
            // Plain root lazy in default collection
            return { typeName };
        }
        // Property access: X.lazy('TypeName', ...)
        if (ts.isPropertyAccessExpression(expression) && expression.name.text === 'lazy') {
            const obj = expression.expression;
            if (ts.isIdentifier(obj)) {
                const sourceContext = this.resolveDefineSource(obj.text);
                return {
                    typeName,
                    parentType: sourceContext.parentType,
                    collectionId: sourceContext.collectionId,
                };
            }
            if (ts.isPropertyAccessExpression(obj)) {
                // Nested access: instance.Type.lazy - try to resolve
                const chain = this.getPropertyChain(obj);
                if (chain.length > 0) {
                    const parentNode = this.graph.findType(chain.join('.'));
                    return { typeName, parentType: parentNode };
                }
            }
            if (ts.isCallExpression(obj)) {
                // Determine the collection context from the root of the chain so that
                // custom-collection types do not get confused with default-collection types.
                const rootId = this.getRootIdentifier(obj.expression);
                const expectedCollectionId = rootId
                    ? this.resolveDefineSource(rootId.text).collectionId
                    : undefined;
                // Chained call: define('A').lazy('B') or lazy('A').lazy('B')
                if (this.isDefineCall(obj)) {
                    this.processDefineCall(obj, sourceFile);
                    const parentTypeName = this.extractMnemonicaTypeName(obj);
                    if (parentTypeName) {
                        const parentNode = this.findParentTypeByName(parentTypeName, expectedCollectionId);
                        return { typeName, parentType: parentNode, collectionId: parentNode?.collectionId };
                    }
                }
                if (this.isLazyCall(obj)) {
                    this.processLazyCall(obj, sourceFile);
                    const parentTypeName = this.extractMnemonicaTypeName(obj);
                    if (parentTypeName) {
                        const parentNode = this.findParentTypeByName(parentTypeName, expectedCollectionId);
                        return { typeName, parentType: parentNode, collectionId: parentNode?.collectionId };
                    }
                }
                // Builder lookup chain: App.lookup('User').lazy('Admin')
                if (this.isLookupCall(obj)) {
                    const lookedUpPath = this.resolveLookupPath(obj);
                    if (lookedUpPath) {
                        const parentNode = this.graph.findType(lookedUpPath);
                        if (parentNode) {
                            return { typeName, parentType: parentNode, collectionId: parentNode.collectionId };
                        }
                    }
                }
            }
        }
        return { typeName };
    }
    /**
     * Extract config options from lazy() call
     */
    extractLazyConfig(call) {
        const args = this.extractLazyCallArgs(call);
        if (!args || !args.config || !ts.isObjectLiteralExpression(args.config)) {
            return {};
        }
        const configResult = this.extractConfigFromObjectLiteral(args.config);
        return configResult;
    }
    /**
     * Does the handler name a generated type — directly, or through the type
     * aliases, interfaces and classes it references (followed across files,
     * each declaration once)? Such a handler is typed by its own registry
     * entry, so its value cannot be derived.
     */
    hasGeneratedTypeReference(handler) {
        if (!handler) {
            return false;
        }
        const visited = new Set();
        const result = this.referencesGeneratedType(handler, this.currentReferencedTypeFile, visited);
        return result;
    }
    referencesGeneratedType(node, file, visited) {
        if (ts.isIdentifier(node) && this.generatedTypeImports.get(file)?.has(node.text)) {
            return true;
        }
        // `type X = …`, `this: X`, `interface X extends Y`: follow the named
        // declaration, resolved from the file that uses the name
        let referencedName;
        if (ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName)) {
            referencedName = node.typeName;
        }
        else if (ts.isExpressionWithTypeArguments(node) && ts.isIdentifier(node.expression)) {
            referencedName = node.expression;
        }
        if (referencedName) {
            const declaration = this.resolveReferencedTypeDeclaration(referencedName.text, file);
            if (declaration && !visited.has(declaration.node)) {
                visited.add(declaration.node);
                if (this.referencesGeneratedType(declaration.node, declaration.file, visited)) {
                    return true;
                }
            }
        }
        const children = [];
        ts.forEachChild(node, child => {
            children.push(child);
        });
        for (const child of children) {
            if (this.referencesGeneratedType(child, file, visited)) {
                return true;
            }
        }
        return false;
    }
    hasSelfTypeAnnotation(handler, fullPath) {
        if (!handler || !ts.isFunctionLike(handler)) {
            return false;
        }
        const typeName = fullPath.split('.').pop();
        for (const parameter of handler.parameters) {
            if (!ts.isIdentifier(parameter.name) || parameter.name.text !== 'this' || !parameter.type) {
                continue;
            }
            const annotation = parameter.type.getText();
            const result = annotation === typeName || annotation.endsWith(`.${typeName}`) ||
                annotation === `InstanceType<typeof ${typeName}>`;
            return result;
        }
        return false;
    }
    /**
     * True when a define hop sits on a chain that starts at the free
     * define() or lookup() — the value then carries the global
     * TypeRegistry, not a registry of its own. Free when: the call is the
     * free `define('X', …)` / `lazy('X', …)` root (an explicit-source
     * `define(source, 'X', …)` only when its source is free); its parent
     * type was defined on a free chain; or its receiver chain starts at the
     * imported free `define`/`lookup` (`define('A').define('B')`,
     * `lookup('A').define('B')`). A free hop's path is recorded, so the
     * next hop on the chain sees its parent as free.
     */
    isFreeChainHop(call, parentNode, fullPath) {
        const callee = call.expression;
        const [firstArg] = call.arguments;
        const freeRoot = ts.isIdentifier(callee) && firstArg !== undefined && ts.isStringLiteralLike(firstArg);
        let base = ts.isPropertyAccessExpression(callee) ? callee.expression : undefined;
        while (base && (ts.isPropertyAccessExpression(base) || ts.isCallExpression(base))) {
            base = base.expression;
        }
        const importedAs = base && ts.isIdentifier(base)
            ? this.mnemonicaNamedImports.get(this.currentReferencedTypeFile)?.get(base.text)
            : undefined;
        const free = freeRoot ||
            (parentNode !== undefined && this.freeChainTypePaths.has(parentNode.fullPath)) ||
            importedAs === 'define' ||
            importedAs === 'lookup';
        if (free) {
            this.freeChainTypePaths.add(fullPath);
        }
        return free;
    }
    recordBuilderCandidate(name, fullPath, kind, sourceFile, declaration, excluded) {
        const candidate = {
            name,
            sourceFile: sourceFile.fileName,
            kind,
            fullPath,
            exports: [],
            excluded
        };
        const statement = declaration.parent.parent;
        const modifiers = ts.isVariableStatement(statement) ? ts.getModifiers(statement) ?? [] : [];
        const isDefault = modifiers.some(modifier => modifier.kind === ts.SyntaxKind.DefaultKeyword);
        const isExported = modifiers.some(modifier => modifier.kind === ts.SyntaxKind.ExportKeyword);
        if (isExported) {
            candidate.exports.push({
                name: name,
                sourceFile: sourceFile.fileName,
                defaultImport: isDefault
            });
        }
        this.builderCandidates.push(candidate);
    }
    markBuilderExport(exportedName, originalName, filePath, moduleSpecifier) {
        if (!moduleSpecifier) {
            for (const candidate of this.builderCandidates) {
                const matchesCandidate = nodePath.resolve(candidate.sourceFile) === nodePath.resolve(filePath)
                    && candidate.name === originalName
                    && !candidate.excluded;
                if (matchesCandidate) {
                    candidate.exports.push({ name: exportedName, sourceFile: filePath });
                }
            }
            return;
        }
        const resolution = this.resolveReferencedTypeModule(moduleSpecifier, filePath);
        if (resolution?.isExternal) {
            return;
        }
        const fallbackPath = moduleSpecifier.endsWith('.ts')
            ? nodePath.resolve(nodePath.dirname(filePath), moduleSpecifier)
            : `${nodePath.resolve(nodePath.dirname(filePath), moduleSpecifier)}.ts`;
        const resolvedPath = resolution?.resolvedPath ?? fallbackPath;
        for (const candidate of this.builderCandidates) {
            if (nodePath.resolve(candidate.sourceFile) !== nodePath.resolve(resolvedPath) || candidate.excluded) {
                continue;
            }
            const matchesName = originalName === 'default'
                ? candidate.exports.some(exported => exported.name === 'default')
                : candidate.name === originalName;
            if (matchesName) {
                candidate.exports.push({
                    name: exportedName,
                    sourceFile: filePath,
                    defaultImport: originalName === 'default'
                });
            }
        }
    }
    trackBuilderExportAssignment(node) {
        if (!ts.isExportAssignment(node) || !ts.isIdentifier(node.expression)) {
            return;
        }
        const filePath = this.currentReferencedTypeFile;
        for (const candidate of this.builderCandidates) {
            const matchesCandidate = nodePath.resolve(candidate.sourceFile) === nodePath.resolve(filePath)
                && candidate.name === node.expression.text
                && !candidate.excluded;
            if (matchesCandidate) {
                candidate.exports.push({ name: node.expression.text, sourceFile: filePath, defaultImport: true });
            }
        }
    }
    /**
        * Track variable assignments that capture define() results
        * e.g., const User = define('UserEntity', ...) maps "User" -> "UserEntity"
        * For chained calls like const X = define('A').define('B'), we map X -> A (the root type)
        */
    trackVariableAssignment(call, parentNode, fullPath, sourceFile) {
        // Check if this call is the right-hand side of a variable declaration
        // Walk up the tree to find VariableDeclaration
        let current = call.parent;
        while (current) {
            if (ts.isVariableDeclaration(current)) {
                // Found: const X = define(...)
                if (ts.isIdentifier(current.name)) {
                    const varName = current.name.text;
                    // F18: define() returns the DEFINED type's constructor,
                    // so a const holding a multi-hop initializer
                    // (`const X = A.define('B').define('C')`) binds the LAST
                    // hop — a deeper hop must not bind, and the outermost
                    // hop binds unconditionally (visit-order independent)
                    if (this.isDeeperDefineHop(call)) {
                        return;
                    }
                    // For chained lazy calls like const X = define('A').lazy('B'),
                    // the first call in the chain sets the mapping (lazy hop
                    // keeps it — pinned behavior)
                    if (parentNode && this.variableToTypeMap.has(varName)) {
                        return;
                    }
                    const typeNode = this.graph.findType(fullPath);
                    if (typeNode?.collectionId === undefined) {
                        const selfReference = this.hasGeneratedTypeReference(this.extractConstructorExpression(call)) ||
                            this.hasSelfTypeAnnotation(this.extractConstructorExpression(call), fullPath);
                        const excluded = selfReference || (parentNode !== undefined && this.excludedTypePaths.has(parentNode.fullPath));
                        if (excluded) {
                            this.excludedTypePaths.add(fullPath);
                        }
                        // A free-chain value stays extracted: it carries the
                        // global TypeRegistry, so deriving it is circular
                        // (RegistryOf) or grows faster than the type count
                        // (typeof). Only builder values with a registry of
                        // their own are derived
                        if (!this.isFreeChainHop(call, parentNode, fullPath)) {
                            const kind = ts.isIdentifier(call.expression) ? 'typeof' : 'registryOf';
                            this.recordBuilderCandidate(varName, fullPath, kind, sourceFile, current, excluded);
                        }
                    }
                    this.variableToTypeMap.set(varName, fullPath);
                    this.trackFileGraphBinding(varName, fullPath);
                }
                return;
            }
            current = current.parent;
        }
    }
    /**
     * A `.define(...)` hop wrapped by another `.define(...)` call is not
     * the value its const ends up holding — the OUTERMOST hop of the
     * initializer chain is (define() returns the defined type's
     * constructor). Only the outermost hop may bind the variable.
     */
    isDeeperDefineHop(call) {
        const { parent } = call;
        const deeper = !!parent &&
            ts.isPropertyAccessExpression(parent) &&
            parent.name.text === 'define' &&
            ts.isCallExpression(parent.parent) &&
            parent.parent.expression === parent;
        return deeper;
    }
    /**
     * Mirror a variable -> mnemonica fullPath binding into the per-file
     * value-scope map (graph identity law: `typeof X` and bare references
     * resolve through the file's own bindings first).
     */
    trackFileGraphBinding(varName, fullPath) {
        const filePath = this.currentReferencedTypeFile;
        let bindings = this.fileGraphBindings.get(filePath);
        if (!bindings) {
            bindings = new Map();
            this.fileGraphBindings.set(filePath, bindings);
        }
        bindings.set(varName, fullPath);
    }
    /**
        * Track variable assignments from lookup() calls
        * e.g., const SentienceConstructor = lookup('Sentience') maps "SentienceConstructor" -> "Sentience"
        */
    trackLookupAssignment(call, typePath) {
        this.bindResultVariable(call, typePath);
    }
    /**
        * Track variable assignments from new Type() calls
        * e.g., const user = new UserType() maps "user" -> "UserType"
        */
    trackNewAssignment(newExpr, typePath) {
        let effectivePath = typePath;
        let current = newExpr.parent;
        // Chain-form construction: new R().A().B() — the result variable
        // holds the OUTERMOST tip's instance (await-transparent), not the
        // inner new's type. Walk the chain, keeping the last resolvable tip.
        while (current) {
            if (ts.isPropertyAccessExpression(current) &&
                ts.isCallExpression(current.parent) &&
                current.parent.expression === current) {
                const tip = this.resolveChainTipTypePath(current.parent);
                if (tip) {
                    effectivePath = tip;
                }
                current = current.parent.parent;
                continue;
            }
            break;
        }
        this.bindResultVariable(newExpr, effectivePath);
    }
    /**
     * Bind the nearest enclosing `const/let/var X = …` to a mnemonica
     * fullPath — the shared result-variable walker behind new/lookup/
     * chain/fork/merge/call tracking (value scope: downstream references
     * and `this.x = x` assignments resolve through the same binding).
     */
    bindResultVariable(from, typePath) {
        let current = from.parent;
        while (current) {
            if (ts.isVariableDeclaration(current)) {
                // Found: const X = <construction>
                if (ts.isIdentifier(current.name)) {
                    const varName = current.name.text;
                    this.variableToTypeMap.set(varName, typePath);
                    this.trackFileGraphBinding(varName, typePath);
                }
                return;
            }
            // Scope boundary: a construction inside a nested class/function
            // body does not bind the outer variable —
            // `const X = define('X', class { m = new Map() })` holds the
            // defined constructor, not a Map. Without this stop the class-body
            // instantiation clobbers X's binding and a later X.define('Child')
            // loses its parent (the child lands as a bare default-collection
            // root — fatal for custom collections, whose fullPaths the
            // name-only fallback cannot see).
            if (ts.isClassLike(current) || ts.isFunctionLike(current)) {
                return;
            }
            current = current.parent;
        }
    }
    /**
     * Record an `instantiation` usage for a construction-shape call
     * (chain tip / call / apply / fork / clone / merge —
     * byte-indistinguishable from `new` until the deferred
     * mechanism-kind revision). `constructorText` defaults to the callee
     * expression text so the site stays readable without new fields;
     * call/apply override it with the Ctor argument text.
     */
    recordConstructionUsage(call, typePath, sourceFile, constructorText) {
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, call.getStart(sourceFile));
        const ctorText = constructorText ?? call.expression.getText(sourceFile);
        this.addUsage(typePath, {
            location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
            kind: 'instantiation',
            code: call.getText(sourceFile).slice(0, 100),
            constructorText: ctorText.slice(0, 100),
        });
    }
    /**
     * Resolve the type a construction-chain tip call constructs:
     * `new R(...).A(...)` constructs R.A; `await new R(...).A(...).B(...)`
     * constructs R.A.B. The receiver is the nested chain (NewExpression
     * base, then tip calls); exact fullPath first, and only when the root
     * itself is unknown does the prop-name fallback law apply (so plain
     * method calls on fresh instances never record a construction).
     */
    resolveChainTipTypePath(call) {
        if (!ts.isPropertyAccessExpression(call.expression)) {
            return undefined;
        }
        const receiver = call.expression;
        let rootPath;
        if (ts.isNewExpression(receiver.expression)) {
            const inner = receiver.expression;
            rootPath = ts.isPropertyAccessExpression(inner.expression)
                ? this.resolveTypePath(inner.expression)
                : this.getTypeNameFromExpression(inner.expression);
        }
        else if (ts.isCallExpression(receiver.expression)) {
            rootPath = this.resolveChainTipTypePath(receiver.expression);
        }
        else {
            return undefined;
        }
        if (!rootPath) {
            return undefined;
        }
        const candidate = `${rootPath}.${receiver.name.text}`;
        if (this.definitions.has(candidate)) {
            return candidate;
        }
        if (!this.definitions.has(rootPath)) {
            return this.resolveTypePath(receiver);
        }
        return undefined;
    }
    /**
     * True when `expr` denotes a construction function imported from
     * 'mnemonica' — the named-import form (`import { call } from
     * 'mnemonica'`, aliases included) or a member of a tracked
     * module-object alias (`mnemonica.call`). Userland call/apply/bind
     * functions never match.
     */
    isMnemonicaConstructionFn(expr, fn) {
        if (ts.isIdentifier(expr)) {
            const imported = this.mnemonicaNamedImports.get(this.currentReferencedTypeFile)?.get(expr.text);
            const matched = imported === fn;
            return matched;
        }
        if (ts.isPropertyAccessExpression(expr) && expr.name.text === fn) {
            const matched = ts.isIdentifier(expr.expression) &&
                this.moduleObjectVariables.has(expr.expression.text);
            return matched;
        }
        return false;
    }
    /**
     * mnemonica call/apply(entity, Ctor, ...) / bind(entity, Ctor):
     * resolve the Ctor argument (arg 1) to a graph fullPath through the
     * same tiers as the `new` branch (value scope for identifiers,
     * chain resolution for property accesses).
     */
    resolveConstructionFnTypePath(call) {
        const callee = call.expression;
        const isCallOrApply = this.isMnemonicaConstructionFn(callee, 'call') ||
            this.isMnemonicaConstructionFn(callee, 'apply');
        const isBind = this.isMnemonicaConstructionFn(callee, 'bind');
        if (!isCallOrApply && !isBind) {
            return undefined;
        }
        if (call.arguments.length < 2) {
            return undefined;
        }
        const [, ctorArg] = call.arguments;
        const known = this.resolveCtorArgTypePath(ctorArg);
        return known;
    }
    /**
     * Resolve an expression passed where a constructor is expected (the
     * Ctor of call/apply/bind, a plugin factory's constructed target) to a
     * defined type's fullPath: value scope for identifiers, chain
     * resolution for property accesses.
     */
    resolveCtorArgTypePath(ctorArg) {
        let resolved;
        if (ts.isPropertyAccessExpression(ctorArg)) {
            resolved = this.resolveTypePath(ctorArg);
        }
        else if (ts.isIdentifier(ctorArg)) {
            const bound = this.variableToTypeMap.get(ctorArg.text);
            if (bound) {
                resolved = bound;
            }
            else {
                const graphResult = this.resolveGraphTypeName(ctorArg.text);
                if (graphResult.status === 'unique') {
                    resolved = graphResult.node.fullPath;
                }
            }
        }
        const known = resolved && this.definitions.has(resolved) ? resolved : undefined;
        return known;
    }
    /**
     * instance.fork(...) / instance.clone(...) on a tracked variable —
     * runtime returns `this`, so the result carries the source type.
     */
    resolveForkLikeTypePath(call) {
        if (!ts.isPropertyAccessExpression(call.expression)) {
            return undefined;
        }
        const method = call.expression.name.text;
        if (method !== 'fork' && method !== 'clone') {
            return undefined;
        }
        const receiver = call.expression.expression;
        if (!ts.isIdentifier(receiver)) {
            return undefined;
        }
        const result = this.variableToTypeMap.get(receiver.text);
        return result;
    }
    /**
     * Free utils forms: utils.merge(a, b, ...) (also the direct named
     * import `merge(a, b)`) and the curried utils.fork(instance)(...).
     * The result binds to arg 0's type — runtime returns a's lineage over
     * b's context; a's fullPath is the honest approximation within the
     * output contract (documented in README).
     */
    resolveUtilsFnTypePath(call) {
        const callee = call.expression;
        const isUtilsOwner = (owner) => {
            if (ts.isIdentifier(owner)) {
                const imported = this.mnemonicaNamedImports.get(this.currentReferencedTypeFile)?.get(owner.text);
                return imported === 'utils';
            }
            const matched = ts.isPropertyAccessExpression(owner) && owner.name.text === 'utils' &&
                ts.isIdentifier(owner.expression) && this.moduleObjectVariables.has(owner.expression.text);
            return matched;
        };
        let subjectArg;
        if (ts.isPropertyAccessExpression(callee) && isUtilsOwner(callee.expression) &&
            (callee.name.text === 'merge' || callee.name.text === 'fork')) {
            const [firstArg] = call.arguments;
            subjectArg = firstArg;
        }
        else if (ts.isIdentifier(callee)) {
            const imported = this.mnemonicaNamedImports.get(this.currentReferencedTypeFile)?.get(callee.text);
            if (imported === 'merge' || imported === 'fork') {
                const [firstArg] = call.arguments;
                subjectArg = firstArg;
            }
        }
        else if (ts.isCallExpression(callee) && ts.isPropertyAccessExpression(callee.expression) &&
            callee.expression.name.text === 'fork' && isUtilsOwner(callee.expression.expression)) {
            // utils.fork(instance)(...args) — the curried form
            const [firstArg] = callee.arguments;
            subjectArg = firstArg;
        }
        if (!subjectArg || !ts.isIdentifier(subjectArg)) {
            return undefined;
        }
        const result = this.variableToTypeMap.get(subjectArg.text);
        return result;
    }
    /**
        * Process a @decorate() decorator
     */
    processDecorateDecorator(decorator, sourceFile, classDeclParam) {
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, decorator.getStart(sourceFile));
        // Get the class declaration - use the passed context if parent is not set
        const classDecl = decorator.parent || classDeclParam;
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
        // Parse decorator arguments: @decorate(), @decorate(Parent),
        // @decorate({ ... }), @decorate(Parent, { ... }),
        // @MyCollection.decorate(), @MyCollection.decorate({ ... })
        let parentNode;
        let parentFullPath = null;
        let collectionId;
        let decoratorConfig = {};
        if (ts.isCallExpression(decorator.expression)) {
            const callExpr = decorator.expression;
            const callee = callExpr.expression;
            // Check for @MyCollection.decorate() where MyCollection is a custom collection.
            // The decorated class becomes a root type in that collection.
            if (ts.isPropertyAccessExpression(callee) &&
                callee.name.text === 'decorate' &&
                ts.isIdentifier(callee.expression) &&
                this.collectionVariables.has(callee.expression.text)) {
                collectionId = this.collectionVariables.get(callee.expression.text);
                if (callExpr.arguments.length === 1 && ts.isObjectLiteralExpression(callExpr.arguments[0])) {
                    decoratorConfig = this.extractConfigFromObjectLiteral(callExpr.arguments[0]);
                }
            }
            else {
                const args = callExpr.arguments;
                let parentArg;
                let configArg;
                for (const arg of args) {
                    if (ts.isIdentifier(arg)) {
                        if (parentArg) {
                            this.errors.push({
                                message: '@decorate() accepts only one parent reference',
                                file: sourceFile.fileName,
                                line: line + 1,
                                column: character + 1,
                            });
                        }
                        else {
                            parentArg = arg;
                        }
                    }
                    else if (ts.isObjectLiteralExpression(arg)) {
                        if (configArg) {
                            this.errors.push({
                                message: '@decorate() accepts only one config object',
                                file: sourceFile.fileName,
                                line: line + 1,
                                column: character + 1,
                            });
                        }
                        else {
                            configArg = arg;
                        }
                    }
                }
                if (parentArg) {
                    parentNode = this.findParentTypeByIdentifier(parentArg.text);
                    if (parentNode) {
                        parentFullPath = parentNode.fullPath;
                    }
                }
                if (configArg) {
                    decoratorConfig = this.extractConfigFromObjectLiteral(configArg);
                }
            }
        }
        // Build full path — a root decorated into a custom collection
        // carries the collectionId:: prefix, exactly like the graph node's
        // fullPath: definitions.json keys must join hierarchy.json (the
        // prefix was dropped here before, so a decorated collection root
        // never joined)
        const fullPath = parentNode
            ? `${parentNode.fullPath}.${typeName}`
            : collectionId
                ? `${collectionId}::${typeName}`
                : typeName;
        // Create definition info for decorate
        const definition = {
            name: typeName,
            location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
            kind: 'decorate',
            parent: parentFullPath,
            strictChain: decoratorConfig.strictChain ?? true,
            blockErrors: decoratorConfig.blockErrors ?? false,
        };
        this.definitions.set(fullPath, definition);
        this.edsScopeByNode.set(classDecl, fullPath);
        // Create type node
        const node = graph_1.TypeGraphImpl.createNode(typeName, parentNode, sourceFile.fileName, line + 1, character + 1, collectionId);
        this.applyCollectionEmissionInfo(node, node.collectionId);
        // Same-namespace duplicate detection (hard-fail law)
        this.recordDefineSite(parentNode ? `${parentNode.fullPath}.${typeName}` : `${collectionId ?? 'default'}::${typeName}`, `${sourceFile.fileName}:${line + 1}:${character + 1}`);
        // Extract properties and constructor parameters from class members —
        // the new node anchors relative-first graph reference resolution
        const previousAnchor = this.currentGraphAnchor;
        this.currentGraphAnchor = node;
        try {
            node.properties = this.extractClassProperties(classDecl);
            node.constructorParams = this.extractClassConstructorParams(classDecl);
        }
        finally {
            this.currentGraphAnchor = previousAnchor;
        }
        // Add to graph
        if (parentNode) {
            this.graph.addChild(parentNode, node);
        }
        else {
            this.graph.addRoot(node);
        }
    }
    /**
     * Extract type name from define() call arguments.
     * Handles:
     *   define('TypeName', handler)
     *   define(source, 'TypeName', handler)   // explicit-source form
     *   define(function TypeName() {})
     *   define(() => class TypeName {})
     */
    extractTypeName(call) {
        const args = call.arguments;
        if (args.length === 0) {
            return undefined;
        }
        const [firstArg] = args;
        // Explicit-source form: define(source, 'TypeName', handler)
        if (args.length >= 2 && ts.isIdentifier(firstArg) && ts.isStringLiteral(args[1])) {
            return args[1].text;
        }
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
            const { body } = firstArg;
            if (ts.isClassExpression(body) && body.name) {
                return body.name.text;
            }
        }
        return undefined;
    }
    /**
     * Resolve a computed define name only when it ranges over a closed const
     * object key set. Arbitrary strings and unresolved unions stay on the
     * existing warning-and-skip path.
     */
    extractComputedTypeNames(call) {
        const [firstArg] = call.arguments;
        if (!firstArg || !ts.isIdentifier(firstArg)) {
            return undefined;
        }
        const loopNames = this.resolveLoopKeyNames(firstArg);
        if (loopNames !== undefined) {
            return loopNames;
        }
        const parameterNames = this.resolveParameterKeyNames(firstArg, call.getSourceFile());
        return parameterNames;
    }
    resolveLoopKeyNames(name) {
        let current = name.parent;
        while (current) {
            if (ts.isForOfStatement(current) && ts.isVariableDeclarationList(current.initializer)) {
                const declaration = current.initializer.declarations.find(candidate => ts.isIdentifier(candidate.name) && candidate.name.text === name.text);
                if (declaration) {
                    const result = this.resolveObjectKeysCall(current.expression, current.getSourceFile());
                    return result;
                }
            }
            current = current.parent;
        }
        return undefined;
    }
    resolveObjectKeysCall(expression, sourceFile) {
        if (!ts.isCallExpression(expression) || !ts.isPropertyAccessExpression(expression.expression)) {
            return undefined;
        }
        const access = expression.expression;
        const [argument] = expression.arguments;
        if (!ts.isIdentifier(access.expression) || access.expression.text !== 'Object' ||
            access.name.text !== 'keys' || !argument || !ts.isIdentifier(argument)) {
            return undefined;
        }
        const result = this.resolveConstObjectKeys(argument.text, sourceFile);
        return result;
    }
    resolveParameterKeyNames(name, sourceFile) {
        let current = name.parent;
        while (current) {
            if (ts.isFunctionLike(current)) {
                const parameter = current.parameters.find(candidate => ts.isIdentifier(candidate.name) && candidate.name.text === name.text);
                if (parameter) {
                    if (!parameter.type) {
                        return undefined;
                    }
                    const result = this.resolveKeyofType(parameter.type, sourceFile);
                    return result;
                }
            }
            current = current.parent;
        }
        return undefined;
    }
    resolveKeyofType(typeNode, sourceFile) {
        if (ts.isParenthesizedTypeNode(typeNode)) {
            const result = this.resolveKeyofType(typeNode.type, sourceFile);
            return result;
        }
        if (ts.isTypeOperatorNode(typeNode) && typeNode.operator === ts.SyntaxKind.KeyOfKeyword) {
            const queried = typeNode.type;
            if (ts.isTypeQueryNode(queried) && ts.isIdentifier(queried.exprName)) {
                const result = this.resolveConstObjectKeys(queried.exprName.text, sourceFile);
                return result;
            }
            return undefined;
        }
        if (ts.isTypeReferenceNode(typeNode) && ts.isIdentifier(typeNode.typeName)) {
            const referencedName = typeNode.typeName.text;
            const alias = sourceFile.statements.find((statement) => ts.isTypeAliasDeclaration(statement) && statement.name.text === referencedName);
            if (alias) {
                const result = this.resolveKeyofType(alias.type, sourceFile);
                return result;
            }
        }
        return undefined;
    }
    resolveConstObjectKeys(name, sourceFile) {
        for (const statement of sourceFile.statements) {
            if (!ts.isVariableStatement(statement) ||
                (statement.declarationList.flags & ts.NodeFlags.Const) === 0) {
                continue;
            }
            for (const declaration of statement.declarationList.declarations) {
                if (!ts.isIdentifier(declaration.name) || declaration.name.text !== name ||
                    !declaration.initializer || !ts.isObjectLiteralExpression(declaration.initializer)) {
                    continue;
                }
                const names = [];
                for (const property of declaration.initializer.properties) {
                    if (!ts.isPropertyAssignment(property) ||
                        (!ts.isIdentifier(property.name) && !ts.isStringLiteral(property.name))) {
                        return undefined;
                    }
                    names.push(property.name.text);
                }
                return names;
            }
        }
        return undefined;
    }
    /**
     * Extract the full define() call context: type name, parent type, and collection.
     * Handles direct calls, property-access calls, chained calls, and the
     * explicit-source form `define(source, 'TypeName', handler)`.
     */
    extractDefineContext(call, typeNameOverride) {
        const typeName = typeNameOverride ?? this.extractTypeName(call);
        if (!typeName) {
            return {};
        }
        const { expression } = call;
        // Direct call: define('TypeName', ...) or define(source, 'TypeName', handler)
        if (ts.isIdentifier(expression) && expression.text === 'define') {
            // Explicit-source form: define(source, 'TypeName', handler)
            if (call.arguments.length >= 2 && ts.isIdentifier(call.arguments[0])) {
                const sourceName = call.arguments[0].text;
                const sourceContext = this.resolveDefineSource(sourceName);
                return {
                    typeName,
                    parentType: sourceContext.parentType,
                    collectionId: sourceContext.collectionId,
                };
            }
            // Plain root define in default collection
            return { typeName };
        }
        // Property access: X.define('TypeName', ...)
        if (ts.isPropertyAccessExpression(expression) && expression.name.text === 'define') {
            const obj = expression.expression;
            if (ts.isIdentifier(obj)) {
                const sourceContext = this.resolveDefineSource(obj.text);
                return {
                    typeName,
                    parentType: sourceContext.parentType,
                    collectionId: sourceContext.collectionId,
                };
            }
            if (ts.isPropertyAccessExpression(obj)) {
                // Nested access: instance.Type.define - try to resolve
                const chain = this.getPropertyChain(obj);
                if (chain.length > 0) {
                    const parentNode = this.graph.findType(chain.join('.'));
                    return { typeName, parentType: parentNode };
                }
            }
            if (ts.isCallExpression(obj)) {
                // Determine the collection context from the root of the chain so that
                // custom-collection types do not get confused with default-collection types.
                const rootId = this.getRootIdentifier(obj.expression);
                const expectedCollectionId = rootId
                    ? this.resolveDefineSource(rootId.text).collectionId
                    : undefined;
                // Chained call: define('A').define('B') or mnemonica.define('A').define('B')
                if (this.isDefineCall(obj)) {
                    this.processDefineCall(obj, call.getSourceFile());
                    const parentTypeName = this.extractTypeName(obj);
                    if (parentTypeName) {
                        const parentNode = this.findParentTypeByName(parentTypeName, expectedCollectionId);
                        // Inherit collection from the parent type (if any)
                        return { typeName, parentType: parentNode, collectionId: parentNode?.collectionId };
                    }
                }
                // Chained lazy call: lazy('A').define('B') or Type.lazy('A').define('B')
                if (this.isLazyCall(obj)) {
                    this.processLazyCall(obj, call.getSourceFile());
                    const parentTypeName = this.extractMnemonicaTypeName(obj);
                    if (parentTypeName) {
                        const parentNode = this.findParentTypeByName(parentTypeName, expectedCollectionId);
                        return { typeName, parentType: parentNode, collectionId: parentNode?.collectionId };
                    }
                }
                // Builder lookup chain: App.lookup('User').define('Admin')
                if (this.isLookupCall(obj)) {
                    const lookedUpPath = this.resolveLookupPath(obj);
                    if (lookedUpPath) {
                        const parentNode = this.graph.findType(lookedUpPath);
                        if (parentNode) {
                            return { typeName, parentType: parentNode, collectionId: parentNode.collectionId };
                        }
                    }
                }
            }
        }
        return { typeName };
    }
    /**
     * Prefix a dotted type path with a collection identifier so custom-collection
     * types do not collide with default-collection types in the graph.
     */
    prefixCollectionPath(path, collectionId) {
        return `${collectionId}::${path}`;
    }
    /**
     * Resolve a define() source identifier to either a parent type, a collection,
     * or the default (module object) collection.
     */
    resolveDefineSource(sourceName) {
        // Module object aliases -> root in default collection
        if (this.moduleObjectVariables.has(sourceName)) {
            return {};
        }
        // Collection variables -> root in that collection
        const collectionId = this.collectionVariables.get(sourceName);
        if (collectionId) {
            return { collectionId };
        }
        // Otherwise treat as a type variable reference
        const parentNode = this.findParentTypeByIdentifier(sourceName);
        return { parentType: parentNode, collectionId: parentNode?.collectionId };
    }
    /**
     * Check if a call expression is a lookup() call.
     */
    isLookupCall(node) {
        const expr = node.expression;
        if (ts.isIdentifier(expr) && expr.text === 'lookup') {
            return true;
        }
        if (ts.isPropertyAccessExpression(expr) && expr.name.text === 'lookup') {
            return true;
        }
        return false;
    }
    /**
     * Resolve a lookup() call to a dotted type path (best effort).
     * Handles:
     *   lookup('User')
     *   lookup(source, 'User')
     *   App.lookup('User')
     *   collection.lookup('User.Admin')
     */
    resolveLookupPath(call) {
        const args = call.arguments;
        if (args.length === 0) {
            return undefined;
        }
        // Single-arg lookup: lookup('User') or App.lookup('User')
        if (args.length === 1) {
            const [arg] = args;
            if (ts.isStringLiteral(arg) || ts.isNoSubstitutionTemplateLiteral(arg)) {
                const path = arg.text;
                // If this is a method call on a source, resolve relative to that source.
                if (ts.isPropertyAccessExpression(call.expression)) {
                    const sourceExpr = call.expression.expression;
                    if (ts.isIdentifier(sourceExpr)) {
                        const sourceName = sourceExpr.text;
                        const sourceContext = this.resolveDefineSource(sourceName);
                        if (sourceContext.parentType) {
                            // Type lookup: relative first, then root fallback.
                            // For a type inside a custom collection the fallback root is
                            // the collection root, never the default collection.
                            const relativePath = `${sourceContext.parentType.fullPath}.${path}`;
                            if (this.graph.findType(relativePath)) {
                                return relativePath;
                            }
                            if (sourceContext.collectionId) {
                                return this.prefixCollectionPath(path, sourceContext.collectionId);
                            }
                            return path;
                        }
                        if (sourceContext.collectionId) {
                            // Collection lookup: prefix path with the collection id
                            return this.prefixCollectionPath(path, sourceContext.collectionId);
                        }
                    }
                }
                return path;
            }
            return undefined;
        }
        // Two-arg lookup: lookup(source, 'User')
        if (args.length >= 2) {
            const [sourceArg, pathArg] = args;
            if (!ts.isIdentifier(sourceArg) || !ts.isStringLiteral(pathArg)) {
                return undefined;
            }
            const sourceName = sourceArg.text;
            const path = pathArg.text;
            const sourceContext = this.resolveDefineSource(sourceName);
            if (sourceContext.parentType) {
                // Same relative-first law as the single-arg form; collection
                // members fall back to their collection root, not the global one.
                const relativePath = `${sourceContext.parentType.fullPath}.${path}`;
                if (this.graph.findType(relativePath)) {
                    return relativePath;
                }
                if (sourceContext.collectionId) {
                    return this.prefixCollectionPath(path, sourceContext.collectionId);
                }
                return path;
            }
            if (sourceContext.collectionId) {
                return this.prefixCollectionPath(path, sourceContext.collectionId);
            }
            return path;
        }
        return undefined;
    }
    /**
     * Lookup-law delegate for the local-scope walker (scopes.json typePath
     * metadata): resolve a lookup() initializer call through exactly the
     * tiers the usages pass resolved it against (same source resolution,
     * same complete graph). The walker runs its own scope-chain value-scope
     * tier before delegating; everything above value scope lands here, so
     * scopes.json never disagrees with the hard-fail-law verdicts.
     */
    resolveLookupCallPath(call) {
        const result = this.resolveLookupPath(call);
        return result;
    }
    /**
        * Find a parent type by its name, searching in the graph.
        * When collectionId is provided, only types from that collection are considered.
        */
    findParentTypeByName(name, collectionId) {
        const matchesCollection = (type) => {
            if (collectionId === undefined) {
                return type.collectionId === undefined;
            }
            return type.collectionId === collectionId;
        };
        // First try exact match (default-collection types use the plain dotted path)
        const exact = this.graph.findType(name);
        if (exact && matchesCollection(exact)) {
            return exact;
        }
        // Then search through all types for one with matching name and collection
        for (const type of this.graph.getAllTypes()) {
            if (type.name === name && matchesCollection(type)) {
                return type;
            }
        }
        return undefined;
    }
    /**
        * Find a parent type from an identifier reference.
        * Handles both aliased variables (const User = define('UserEntity', ...))
        * and direct class/type names.
        */
    findParentTypeByIdentifier(name) {
        // First check variable mapping: const User = define('UserEntity', ...)
        const mappedFullPath = this.variableToTypeMap.get(name);
        if (mappedFullPath) {
            const mappedNode = this.graph.findType(mappedFullPath);
            if (mappedNode)
                return mappedNode;
        }
        const parentNode = this.findParentTypeByName(name);
        return parentNode;
    }
    /**
     * Get the leftmost identifier of a property-access chain.
     * For `App.define('User').define('Admin')` this returns the `App` identifier.
     */
    getRootIdentifier(expr) {
        let current = expr;
        while (ts.isPropertyAccessExpression(current)) {
            current = current.expression;
        }
        if (ts.isIdentifier(current)) {
            return current;
        }
        return undefined;
    }
    /**
        * Get property chain from nested access
        */
    getPropertyChain(expr) {
        const chain = [];
        let current = expr;
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
    findConstructorInModule(modulePath, name, depth) {
        if (depth > MAX_REEXPORT_CHASE_DEPTH) {
            return undefined;
        }
        const bindings = this.constructorBindings.get(modulePath);
        const direct = bindings?.get(name);
        if (direct) {
            return direct;
        }
        const localAlias = this.referencedTypeExportAliases.get(modulePath)?.get(name);
        if (localAlias) {
            const aliased = bindings?.get(localAlias);
            if (aliased) {
                return aliased;
            }
        }
        const reExportSpecifier = this.referencedTypeReExports.get(modulePath)?.get(name);
        if (reExportSpecifier) {
            const nextResolution = this.resolveReferencedTypeModule(reExportSpecifier, modulePath);
            if (nextResolution && !nextResolution.isExternal) {
                const found = this.findConstructorInModule(nextResolution.resolvedPath, name, depth + 1);
                if (found) {
                    return found;
                }
            }
        }
        const stars = this.referencedTypeExportStars.get(modulePath);
        if (stars) {
            for (const starSpecifier of stars) {
                const nextResolution = this.resolveReferencedTypeModule(starSpecifier, modulePath);
                if (!nextResolution || nextResolution.isExternal) {
                    continue;
                }
                const found = this.findConstructorInModule(nextResolution.resolvedPath, name, depth + 1);
                if (found) {
                    return found;
                }
            }
        }
        return undefined;
    }
    resolveHeldConstructor(name, fromFile) {
        const filePath = nodePath.resolve(fromFile);
        const imported = this.referencedTypeImports.get(filePath)?.get(name);
        if (imported && !imported.isNamespace) {
            const resolution = this.resolveReferencedTypeModule(imported.specifier, filePath);
            if (resolution && !resolution.isExternal) {
                const found = this.findConstructorInModule(resolution.resolvedPath, imported.originalName, 0);
                if (found) {
                    return found;
                }
            }
        }
        const local = this.constructorBindings.get(filePath)?.get(name);
        return local;
    }
    unwrapConstructorAssertions(handler) {
        let current = handler;
        while (ts.isParenthesizedExpression(current) || ts.isAsExpression(current) ||
            ts.isTypeAssertionExpression(current)) {
            current = current.expression;
        }
        return current;
    }
    resolveConstructorExpression(expression, sourceFile) {
        const current = this.unwrapConstructorAssertions(expression);
        if (!ts.isIdentifier(current)) {
            return current;
        }
        const resolved = this.resolveHeldConstructor(current.text, sourceFile.fileName);
        if (!resolved) {
            return current;
        }
        const result = this.unwrapConstructorAssertions(resolved);
        return result;
    }
    /**
     * Determine the constructor expression for either a define() or lazy() call.
     * For define() this is the construct handler; for lazy() it is the value
     * returned by the lazy getter. Identifiers resolve to their declarations.
     */
    extractConstructorExpression(call) {
        const expr = call.expression;
        const name = ts.isIdentifier(expr)
            ? expr.text
            : ts.isPropertyAccessExpression(expr)
                ? expr.name.text
                : '';
        let handler;
        if (name === 'lazy') {
            const lazyArgs = this.extractLazyCallArgs(call);
            if (lazyArgs) {
                handler = this.unwrapLazyGetter(lazyArgs.getter);
            }
        }
        else {
            const args = call.arguments;
            if (ts.isStringLiteral(args[0])) {
                const [, modernHandler] = args;
                handler = modernHandler;
            }
            else {
                const [legacyHandler] = args;
                handler = legacyHandler;
            }
        }
        if (!handler) {
            return undefined;
        }
        const result = this.resolveConstructorExpression(handler, call.getSourceFile());
        return result;
    }
    /**
     * Detect an async constructor handler: the async modifier on a
     * function expression or arrow. Async CLASSES (a class constructor
     * returning a Promise) are deliberately NOT detected — the syntactic
     * class shape gives no reliable signal without a type checker, and the
     * owner decided they are typed by the user in userland.
     */
    isAsyncConstructHandler(constructorExpr) {
        if (!constructorExpr) {
            return false;
        }
        const isFn = ts.isFunctionExpression(constructorExpr) ||
            ts.isArrowFunction(constructorExpr) || ts.isFunctionDeclaration(constructorExpr);
        if (!isFn) {
            return false;
        }
        const modifiers = ts.getModifiers(constructorExpr);
        const result = !!modifiers && modifiers.some((modifier) => {
            return modifier.kind === ts.SyntaxKind.AsyncKeyword;
        });
        return result;
    }
    /**
     * Extract properties from constructor function
     */
    extractProperties(call) {
        const constructorExpr = this.extractConstructorExpression(call);
        if (!constructorExpr) {
            return new Map();
        }
        const referencingFile = this.currentReferencedTypeFile;
        this.currentReferencedTypeFile = nodePath.resolve(constructorExpr.getSourceFile().fileName);
        try {
            const result = this.extractPropertiesFromConstructor(constructorExpr);
            return result;
        }
        finally {
            this.currentReferencedTypeFile = referencingFile;
        }
    }
    /**
     * Extract properties from a constructor expression (function, arrow, or class).
     */
    extractPropertiesFromConstructor(constructorExpr) {
        const properties = new Map();
        // Build type map from data parameter (for this.x = data.x patterns)
        const dataTypeMap = this.buildDataTypeMap(constructorExpr);
        // Handle function expression
        if (ts.isFunctionExpression(constructorExpr) || ts.isArrowFunction(constructorExpr) ||
            ts.isFunctionDeclaration(constructorExpr)) {
            const { body } = constructorExpr;
            // First, extract properties from `this` parameter type annotation
            // This handles patterns like: function(this: SomeType, data: SomeType) { }
            const thisParamProperties = this.extractThisParamProperties(constructorExpr);
            for (const [name, propInfo] of thisParamProperties) {
                properties.set(name, propInfo);
            }
            // An annotated this is the complete declared instance type: assignments
            // beyond it add nothing. A generated .tactica or graph-name annotation
            // is the output, not the source, so those handlers keep assignment extraction.
            const hasGeneratedReference = this.hasGeneratedThisAnnotation(constructorExpr);
            const hasAuthoritativeThisAnnotation = !hasGeneratedReference && constructorExpr.parameters.some(param => {
                const result = ts.isIdentifier(param.name) && param.name.text === 'this' && param.type !== undefined;
                return result;
            });
            if (!hasAuthoritativeThisAnnotation && body && ts.isBlock(body)) {
                for (const stmt of body.statements) {
                    if (ts.isExpressionStatement(stmt)) {
                        this.extractPropertyFromStatement(stmt.expression, properties, dataTypeMap);
                    }
                }
            }
        }
        // Handle class expression
        if (ts.isClassExpression(constructorExpr) || ts.isClassDeclaration(constructorExpr)) {
            // First pass: collect all property types for method inference
            const classPropertyTypes = this.extractClassPropertyTypes(constructorExpr);
            for (const member of constructorExpr.members) {
                // Handle property declarations
                if (ts.isPropertyDeclaration(member) && member.name) {
                    // Skip private and protected properties
                    if (member.modifiers) {
                        const hasPrivateOrProtected = member.modifiers.some(m => {
                            return m.kind === ts.SyntaxKind.PrivateKeyword ||
                                m.kind === ts.SyntaxKind.ProtectedKeyword;
                        });
                        if (hasPrivateOrProtected) {
                            continue;
                        }
                    }
                    const name = ts.isIdentifier(member.name) ? member.name.text : '';
                    if (name) {
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
                // Handle method declarations
                if (ts.isMethodDeclaration(member) && member.name && ts.isIdentifier(member.name)) {
                    // Skip private and protected methods
                    if (member.modifiers) {
                        const hasPrivateOrProtected = member.modifiers.some(m => {
                            return m.kind === ts.SyntaxKind.PrivateKeyword ||
                                m.kind === ts.SyntaxKind.ProtectedKeyword;
                        });
                        if (hasPrivateOrProtected) {
                            continue;
                        }
                    }
                    const name = member.name.text;
                    const type = this.inferMethodType(member, classPropertyTypes);
                    properties.set(name, {
                        name,
                        type,
                        optional: false,
                    });
                }
                // Handle getter declarations
                if (ts.isGetAccessor(member) && member.name && ts.isIdentifier(member.name)) {
                    // Skip private and protected getters
                    if (member.modifiers) {
                        const hasPrivateOrProtected = member.modifiers.some(m => {
                            return m.kind === ts.SyntaxKind.PrivateKeyword ||
                                m.kind === ts.SyntaxKind.ProtectedKeyword;
                        });
                        if (hasPrivateOrProtected) {
                            continue;
                        }
                    }
                    const name = member.name.text;
                    // First try explicit type annotation, then infer from getter body
                    let type = this.inferType(member.type);
                    if (type === 'unknown' && member.body) {
                        type = this.inferReturnTypeFromBody(member.body, classPropertyTypes);
                    }
                    properties.set(name, {
                        name,
                        type,
                        optional: false,
                        readonly: true,
                    });
                }
            }
        }
        return properties;
    }
    /**
     * Build a type map from all parameters with inline object type annotations
     * Returns a map of "paramName.propertyName" -> type
     */
    buildDataTypeMap(handlerArg) {
        const typeMap = new Map();
        if (!ts.isFunctionExpression(handlerArg) && !ts.isArrowFunction(handlerArg) &&
            !ts.isFunctionDeclaration(handlerArg)) {
            return typeMap;
        }
        // Iterate over ALL parameters
        for (const param of handlerArg.parameters) {
            if (!param.name || !param.type)
                continue;
            // Get parameter name
            let paramName = '';
            if (ts.isIdentifier(param.name)) {
                paramName = param.name.text;
            }
            else {
                // Skip destructured parameters for now
                continue;
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
            else {
                // Named type reference (alias/interface/class, imported or
                // local — F14): decompose the resolved declaration into
                // per-property entries through the same import-aware
                // machinery as constructor signatures (F10), including the
                // heritage walk (F13). Without this, `this.x = param.y`
                // read `unknown` for named params — only inline literals
                // were decomposed. Unresolvable → whole-param fallback
                // below; a bare name is never emitted either way
                let namedDecl;
                if (ts.isTypeReferenceNode(param.type) && ts.isIdentifier(param.type.typeName)) {
                    const paramTypeName = param.type.typeName.text;
                    namedDecl = this.resolveReferencedTypeDeclaration(paramTypeName, this.currentReferencedTypeFile);
                }
                if (namedDecl) {
                    // member types resolve against the DECLARING file
                    const referencingFile = this.currentReferencedTypeFile;
                    this.currentReferencedTypeFile = namedDecl.file;
                    try {
                        const declProperties = this.referencedDeclarationProperties(namedDecl);
                        for (const [propName, info] of declProperties) {
                            typeMap.set(`${paramName}.${propName}`, info.type);
                        }
                    }
                    finally {
                        this.currentReferencedTypeFile = referencingFile;
                    }
                    // keep the whole-param entry too: `this.x = data` (the
                    // bare parameter) assigns the full expanded shape —
                    // the same string constructor-signature emission uses
                    const wholeType = this.expandReferencedTypeDeclaration(namedDecl);
                    if (wholeType && wholeType !== 'unknown') {
                        typeMap.set(paramName, wholeType);
                    }
                }
                else {
                    // Store simple parameter types like `decorateValue: string`
                    const type = this.inferType(param.type);
                    if (type !== 'unknown') {
                        typeMap.set(paramName, type);
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
    getPropertyAccessChain(expr) {
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
    extractPropertyFromStatement(expr, properties, dataTypeMap = new Map()) {
        // Handle: this.property = value
        if (ts.isBinaryExpression(expr) &&
            expr.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
            const { left } = expr;
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
                        // a bound construction result (new/lookup/chain/fork/
                        // merge/call): the value scope binding supplies the
                        // graph type — emitted by its instance-type name
                        if (!type && ts.isIdentifier(expr.right)) {
                            const bound = this.variableToTypeMap.get(expr.right.text);
                            if (bound) {
                                // Emit the alias types.ts declares (Option B
                                // registry prefix), not the raw collectionId::
                                // fullPath; never-emitted types fall through
                                // to initializer inference
                                const boundNode = this.graph.findType(bound);
                                const boundAlias = boundNode
                                    ? this.getEmittedInstanceTypeName(boundNode)
                                    : undefined;
                                if (boundAlias) {
                                    type = boundAlias;
                                }
                            }
                        }
                        if (!type) {
                            type = this.inferTypeFromInitializer(expr.right, dataTypeMap);
                        }
                        // Don't overwrite a known type from a `this` annotation
                        // with an unknown-bearing inference: an empty-array
                        // initializer infers 'Array<unknown>', which must not
                        // clobber an annotated 'Array<{ id: number }>' either.
                        // "Known" on the EXISTING side means the whole type IS
                        // `unknown` (exact match) — a substring match treats
                        // `Record<string, unknown>` as unknown-bearing and let
                        // inference clobber a good annotation (F14)
                        const existing = properties.get(name);
                        const typeHasUnknown = !type || type.includes('unknown');
                        const existingIsKnown = existing ? existing.type.trim() !== 'unknown' : false;
                        if (existingIsKnown && typeHasUnknown) {
                            // Keep the better type from explicit annotation
                        }
                        else {
                            properties.set(name, {
                                name,
                                type,
                                optional: existing ? existing.optional : false,
                            });
                        }
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
                    const [, propsArg] = args;
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
                    else if (ts.isIdentifier(propsArg)) {
                        // Object.assign(this, data) — the identifier form: every
                        // per-property entry the data parameter contributed to
                        // the type map becomes an own property. This is what
                        // carries the fields for the self-referencing
                        // intersection-alias root pattern (F21): the this-alias
                        // is ergonomic-only and its intersection members are
                        // never expanded, so the assign is where the root's
                        // fields must come from
                        const paramName = propsArg.text;
                        for (const [key, type] of dataTypeMap) {
                            if (!key.startsWith(`${paramName}.`)) {
                                continue;
                            }
                            const name = key.slice(paramName.length + 1);
                            properties.set(name, {
                                name,
                                type,
                                optional: false,
                            });
                        }
                    }
                }
            }
        }
    }
    /**
     * Extract properties from class declaration (including methods and getters)
     */
    extractClassProperties(classDecl) {
        const properties = new Map();
        for (const member of classDecl.members) {
            // Handle property declarations
            if (ts.isPropertyDeclaration(member) && member.name) {
                // Skip private and protected properties
                if (member.modifiers) {
                    const hasPrivateOrProtected = member.modifiers.some(m => m.kind === ts.SyntaxKind.PrivateKeyword ||
                        m.kind === ts.SyntaxKind.ProtectedKeyword);
                    if (hasPrivateOrProtected) {
                        continue;
                    }
                }
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
            // Handle method declarations
            if (ts.isMethodDeclaration(member) && member.name && ts.isIdentifier(member.name)) {
                // Skip private and protected methods
                if (member.modifiers) {
                    const hasPrivateOrProtected = member.modifiers.some(m => m.kind === ts.SyntaxKind.PrivateKeyword ||
                        m.kind === ts.SyntaxKind.ProtectedKeyword);
                    if (hasPrivateOrProtected) {
                        continue;
                    }
                }
                const name = member.name.text;
                const type = this.inferMethodType(member);
                properties.set(name, {
                    name,
                    type,
                    optional: false,
                });
            }
            // Handle getter declarations
            if (ts.isGetAccessor(member) && member.name && ts.isIdentifier(member.name)) {
                // Skip private and protected getters
                if (member.modifiers) {
                    const hasPrivateOrProtected = member.modifiers.some(m => m.kind === ts.SyntaxKind.PrivateKeyword ||
                        m.kind === ts.SyntaxKind.ProtectedKeyword);
                    if (hasPrivateOrProtected) {
                        continue;
                    }
                }
                const name = member.name.text;
                // First try explicit type annotation, then infer from getter body
                let type = this.inferType(member.type);
                if (type === 'unknown' && member.body) {
                    type = this.inferReturnTypeFromBody(member.body);
                }
                properties.set(name, {
                    name,
                    type,
                    optional: false,
                    readonly: true,
                });
            }
        }
        return properties;
    }
    /**
     * Extract class property types for method return type inference
     * Maps property names to their TypeScript type strings
     * Note: Includes private/protected properties for method inference
     */
    extractClassPropertyTypes(classDecl) {
        const propertyTypes = new Map();
        for (const member of classDecl.members) {
            if (ts.isPropertyDeclaration(member) && member.name && ts.isIdentifier(member.name)) {
                // Include ALL properties (even private) for method return type inference
                // The visibility check is done when adding to output properties
                const name = member.name.text;
                if (member.type) {
                    propertyTypes.set(name, this.inferType(member.type));
                }
            }
        }
        return propertyTypes;
    }
    /**
     * Infer method type from method declaration
     */
    inferMethodType(method, classPropertyTypes) {
        const params = method.parameters.map(param => {
            const paramName = ts.isIdentifier(param.name) ? param.name.text : 'arg';
            const paramType = this.inferType(param.type);
            return `${paramName}: ${paramType}`;
        }).join(', ');
        const returnType = this.inferReturnType(method, classPropertyTypes);
        if (params) {
            return `(${params}) => ${returnType}`;
        }
        return `() => ${returnType}`;
    }
    hasGeneratedThisAnnotation(handler) {
        if (this.hasGeneratedTypeReference(handler)) {
            return true;
        }
        if (!ts.isFunctionExpression(handler) && !ts.isArrowFunction(handler) &&
            !ts.isFunctionDeclaration(handler)) {
            return false;
        }
        for (const param of handler.parameters) {
            const isThis = ts.isIdentifier(param.name) && param.name.text === 'this';
            if (!isThis || !param.type || !ts.isTypeReferenceNode(param.type) ||
                !ts.isIdentifier(param.type.typeName)) {
                continue;
            }
            const typeName = param.type.typeName.text;
            if (this.currentGraphAnchor?.name === typeName || this.currentGraphAnchor?.fullPath === typeName) {
                return true;
            }
            const graphType = this.graph.findTypeByName(typeName);
            if (graphType) {
                return true;
            }
        }
        return false;
    }
    hasAnyThisAnnotation(handler) {
        if (!handler || (!ts.isFunctionExpression(handler) && !ts.isArrowFunction(handler) &&
            !ts.isFunctionDeclaration(handler))) {
            return false;
        }
        const result = handler.parameters.some(param => {
            const matches = ts.isIdentifier(param.name) && param.name.text === 'this' &&
                param.type?.kind === ts.SyntaxKind.AnyKeyword;
            return matches;
        });
        return result;
    }
    /**
        * Extract properties from `this` parameter type annotation
        * Handles patterns like: function(this: SomeType, data: SomeType) { }
        */
    extractThisParamProperties(handlerArg) {
        const properties = new Map();
        // Find the `this` parameter (if any)
        for (const param of handlerArg.parameters) {
            if (param.name && ts.isIdentifier(param.name) && param.name.text === 'this' && param.type) {
                // Check if it's a type reference (e.g., `this: usage`)
                if (ts.isTypeReferenceNode(param.type)) {
                    const typeName = ts.isIdentifier(param.type.typeName)
                        ? param.type.typeName.text
                        : '';
                    // Resolve through the referencing file's own imports first (F10)
                    const decl = typeName
                        ? this.resolveReferencedTypeDeclaration(typeName, this.currentReferencedTypeFile)
                        : undefined;
                    if (decl) {
                        const declProperties = this.referencedDeclarationProperties(decl);
                        for (const [propName, info] of declProperties) {
                            properties.set(propName, info);
                        }
                    }
                }
                // Check if it's directly an inline type literal (e.g., `this: { id: string }`)
                else if (ts.isTypeLiteralNode(param.type)) {
                    for (const member of param.type.members) {
                        if (ts.isPropertySignature(member) && ts.isIdentifier(member.name)) {
                            const propName = member.name.text;
                            const type = this.inferType(member.type);
                            properties.set(propName, {
                                name: propName,
                                type,
                                optional: !!member.questionToken,
                            });
                        }
                    }
                }
                // Found the `this` parameter, no need to continue
                break;
            }
        }
        return properties;
    }
    /**
        * Infer TypeScript type from type node
        */
    /**
     * Infer TypeScript type from type node
     */
    inferType(typeNode) {
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
                return `Array<${this.inferType(typeNode.elementType)}>`;
            case ts.SyntaxKind.TypeLiteral: {
                // Inline-expand type literals instead of collapsing to 'object'
                const typeLit = typeNode;
                const props = [];
                for (const member of typeLit.members) {
                    if (ts.isPropertySignature(member) && ts.isIdentifier(member.name)) {
                        const propName = member.name.text;
                        const optional = member.questionToken ? '?' : '';
                        const type = this.inferType(member.type);
                        props.push(`${propName}${optional}: ${type}`);
                    }
                }
                return `{ ${props.join('; ')} }`;
            }
            case ts.SyntaxKind.LiteralType: {
                // Handle string literal types like 'user', 'admin', etc.
                const { literal } = typeNode;
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
                if (literal.kind === ts.SyntaxKind.NullKeyword) {
                    return 'null';
                }
                return 'unknown';
            }
            case ts.SyntaxKind.TypeReference: {
                // Handle type references like Map<string, number>, PropertyInfo, etc.
                const typeRef = typeNode;
                // Qualified names (Namespace.Type): resolve through namespace imports
                if (ts.isQualifiedName(typeRef.typeName)) {
                    const resolvedQualified = this.inferQualifiedTypeReference(typeRef);
                    if (resolvedQualified !== undefined) {
                        return resolvedQualified;
                    }
                    // unresolved qualified references must not leak a bare name
                    return 'unknown';
                }
                const typeName = ts.isIdentifier(typeRef.typeName) ? typeRef.typeName.text : 'unknown';
                // Import-aware referenced-type resolution (F10): a declaration
                // reached through the current file's own imports (or its locals,
                // or a unique program-wide declaration) expands inline
                const simpleRef = this.resolveSimpleTypeReference(typeName, typeRef.typeArguments, typeRef);
                if (simpleRef !== undefined) {
                    return simpleRef;
                }
                // Build generic type arguments
                const typeArgs = (typeRef.typeArguments ?? []).map(arg => this.inferType(arg));
                return `${typeName}<${typeArgs.join(', ')}>`;
            }
            case ts.SyntaxKind.UnionType: {
                // Handle union types like 'a' | 'b' | 'c'
                const unionType = typeNode;
                const types = unionType.types.map(t => this.inferType(t));
                return types.join(' | ');
            }
            case ts.SyntaxKind.IntersectionType: {
                // Handle intersection types like TypeA & TypeB
                const intersectionType = typeNode;
                const types = intersectionType.types.map(t => this.inferType(t));
                return types.join(' & ');
            }
            case ts.SyntaxKind.TupleType: {
                // Handle tuple types like [string, number]
                const tupleType = typeNode;
                const elements = tupleType.elements.map(elem => this.inferType(elem));
                return `[${elements.join(', ')}]`;
            }
            case ts.SyntaxKind.OptionalType: {
                // Handle optional element in tuple: string?
                const optionalType = typeNode;
                return `${this.inferType(optionalType.type)}?`;
            }
            case ts.SyntaxKind.RestType: {
                // Handle rest element: ...T
                const restType = typeNode;
                return `...${this.inferType(restType.type)}`;
            }
            case ts.SyntaxKind.ParenthesizedType: {
                // Handle parenthesized types: (A | B)
                return this.inferType(typeNode.type);
            }
            case ts.SyntaxKind.IndexedAccessType: {
                // Handle indexed access: T[K]
                const indexed = typeNode;
                // F23: unwrap parentheses around the object — `(typeof
                // list)[number]` must take the typeof branch like the bare
                // spelling; otherwise the general path infers the union and
                // glues the suffix onto the LAST member
                // (`'a' | 'b'[number]`)
                let objectNode = indexed.objectType;
                while (ts.isParenthesizedTypeNode(objectNode)) {
                    objectNode = objectNode.type;
                }
                // `typeof constArray[K]` — element type of a tracked const array:
                // emit the element literal union directly (assembling
                // `union[K]` text would misread precedence, and when the const
                // is not statically visible the honest answer is `unknown`,
                // never a bare `typeof name` query)
                if (ts.isTypeQueryNode(objectNode) && ts.isIdentifier(objectNode.exprName)) {
                    const queryName = objectNode.exprName.text;
                    const arrayLiteral = this.findReferencedConstArray(queryName, this.currentReferencedTypeFile);
                    const literals = arrayLiteral ? this.literalTypesOfArray(arrayLiteral) : undefined;
                    if (!literals) {
                        return 'unknown';
                    }
                    if (ts.isLiteralTypeNode(indexed.indexType) && ts.isNumericLiteral(indexed.indexType.literal)) {
                        const elementIndex = parseInt(indexed.indexType.literal.text, 10);
                        const element = literals[elementIndex];
                        const elementResult = element === undefined ? 'unknown' : element;
                        return elementResult;
                    }
                    const unionResult = literals.join(' | ');
                    return unionResult;
                }
                let objectType = this.inferType(objectNode);
                const indexType = this.inferType(indexed.indexType);
                // If objectType is 'object', try to resolve the underlying referenced type
                if (objectType === 'object' && ts.isTypeReferenceNode(objectNode)) {
                    const refName = ts.isIdentifier(objectNode.typeName) ? objectNode.typeName.text : '';
                    if (refName) {
                        const decl = this.resolveReferencedTypeDeclaration(refName, this.currentReferencedTypeFile);
                        if (decl) {
                            const expanded = this.expandReferencedTypeDeclaration(decl);
                            if (expanded) {
                                objectType = expanded;
                            }
                        }
                    }
                }
                // Invariant: an index suffix must NEVER be glued onto an
                // unresolved/fallback target — `unknown[number]` / `object[K]`
                // are invalid TypeScript in the generated file (hard compile
                // break, F17). When either side did not resolve, the WHOLE
                // indexed access degrades to `unknown`.
                const targetUnresolved = objectType === 'unknown' || objectType === 'object';
                const indexUnresolved = indexType === 'unknown';
                if (targetUnresolved || indexUnresolved) {
                    return 'unknown';
                }
                return `${objectType}[${indexType}]`;
            }
            case ts.SyntaxKind.TypeOperator: {
                // Handle keyof, readonly, unique operators
                const typeOp = typeNode;
                const operator = ts.SyntaxKind[typeOp.operator];
                return `${operator} ${this.inferType(typeOp.type)}`;
            }
            case ts.SyntaxKind.TypeQuery: {
                // `typeof x` as a FIELD TYPE: the generated file has no imports,
                // so a bare `typeof x` would be an unresolvable name downstream.
                // When x is a tracked const array, emit its element literal
                // union; otherwise degrade to `unknown`. (InstanceType<typeof X>
                // graph types are handled in resolveSimpleTypeReference before
                // inferType runs.)
                const typeQuery = typeNode;
                if (ts.isIdentifier(typeQuery.exprName)) {
                    const union = this.typeOfConstArrayUnion(typeQuery.exprName.text, this.currentReferencedTypeFile);
                    if (union) {
                        return union;
                    }
                }
                return 'unknown';
            }
            default:
                // For complex types, return the text representation
                return 'unknown';
        }
    }
    /**
        * Infer return type from a method declaration
        * Uses explicit return type annotation or infers from return statements
        */
    inferReturnType(method, classPropertyTypes) {
        // If method has explicit return type annotation, use it
        if (method.type) {
            return this.inferType(method.type);
        }
        // Otherwise, try to infer from return statements in the method body
        if (method.body) {
            return this.inferReturnTypeFromBody(method.body, classPropertyTypes);
        }
        return 'unknown';
    }
    /**
        * Infer return type by analyzing return statements in the method body
        */
    inferReturnTypeFromBody(body, classPropertyTypes) {
        const returnTypes = new Set();
        const visit = (node) => {
            if (ts.isReturnStatement(node) && node.expression) {
                const type = this.inferTypeFromInitializer(node.expression, undefined, classPropertyTypes);
                if (type !== 'unknown') {
                    returnTypes.add(type);
                }
            }
            ts.forEachChild(node, visit);
        };
        visit(body);
        if (returnTypes.size === 0) {
            return 'void';
        }
        if (returnTypes.size === 1) {
            return Array.from(returnTypes)[0];
        }
        return Array.from(returnTypes).join(' | ');
    }
    /**
     * Infer type from initializer
     */
    inferTypeFromInitializer(initializer, dataTypeMap, classPropertyTypes) {
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
                const newExpr = initializer;
                if (ts.isIdentifier(newExpr.expression)) {
                    const constructedName = newExpr.expression.text;
                    // Explicit type arguments survive: new Map<string, object>()
                    // emits Map<string, object> — dropping them produced a bare
                    // generic, which is invalid TS in the generated file (TS2314)
                    if (newExpr.typeArguments && newExpr.typeArguments.length > 0) {
                        const argTypes = newExpr.typeArguments.map(arg => this.inferType(arg));
                        return `${constructedName}<${argTypes.join(', ')}>`;
                    }
                    // No type arguments: a known generic global still needs its
                    // parameter list — fill it with unknown (Map<unknown, unknown>)
                    const defaultedGeneric = GENERIC_GLOBAL_DEFAULT_ARGS.get(constructedName);
                    if (defaultedGeneric) {
                        return defaultedGeneric;
                    }
                    return constructedName;
                }
                return 'object';
            }
            case ts.SyntaxKind.BinaryExpression: {
                // Handle arithmetic operations: a * b, a + b, a - b, a / b
                const binaryExpr = initializer;
                const leftType = this.inferTypeFromInitializer(binaryExpr.left, dataTypeMap, classPropertyTypes);
                const rightType = this.inferTypeFromInitializer(binaryExpr.right, dataTypeMap, classPropertyTypes);
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
                // Handle this.map.size pattern (Map.size returns number)
                const propAccess = initializer;
                if (ts.isPropertyAccessExpression(propAccess.expression)) {
                    const outerProp = propAccess.expression;
                    // Check for this.map pattern
                    let innerName = '';
                    if (outerProp.expression.kind === ts.SyntaxKind.ThisKeyword) {
                        innerName = 'this';
                    }
                    else if (ts.isIdentifier(outerProp.expression)) {
                        innerName = outerProp.expression.text;
                    }
                    const mapProp = outerProp.name.text;
                    const finalProp = propAccess.name.text;
                    // this.map.size -> number
                    if (innerName === 'this' && mapProp === 'map' && finalProp === 'size') {
                        return 'number';
                    }
                }
                return 'unknown';
            }
            case ts.SyntaxKind.Identifier: {
                // Handle identifier references if in dataTypeMap
                if (dataTypeMap) {
                    const name = initializer.text;
                    const type = dataTypeMap.get(name);
                    if (type) {
                        return type;
                    }
                }
                return 'unknown';
            }
            case ts.SyntaxKind.ElementAccessExpression: {
                // F22: value-level element access over a const-asserted
                // literal array — `(<const>[…])[0]`, `([…] as const)[1]`, or
                // a tracked module const (`const x = <const>[…]`; `x[0]`) —
                // infers the element's literal type, the value-level twin of
                // the typeof-path union. Non-numeric indexes, non-literal
                // elements, and general assertions stay `unknown`.
                const elementAccess = initializer;
                const argument = elementAccess.argumentExpression;
                if (!argument || !ts.isNumericLiteral(argument)) {
                    return 'unknown';
                }
                const arrayLiteral = this.constArrayLiteralOf(elementAccess.expression);
                if (!arrayLiteral) {
                    return 'unknown';
                }
                const element = arrayLiteral.elements[parseInt(argument.text, 10)];
                if (!element || ts.isSpreadElement(element)) {
                    return 'unknown';
                }
                const literal = this.literalTypeOfExpression(element);
                const elementResult = literal ?? 'unknown';
                return elementResult;
            }
            case ts.SyntaxKind.CallExpression: {
                // Handle function calls like Date.now(), parseInt(), etc.
                const callExpr = initializer;
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
                    // Handle Map property access on class instances (this.map.*)
                    if (ts.isPropertyAccessExpression(callExpr.expression.expression)) {
                        const outerProp = callExpr.expression.expression;
                        // Handle both 'this' keyword and identifier patterns
                        let innerName = '';
                        if (outerProp.expression.kind === ts.SyntaxKind.ThisKeyword) {
                            innerName = 'this';
                        }
                        else if (ts.isIdentifier(outerProp.expression)) {
                            innerName = outerProp.expression.text;
                        }
                        const mapProp = outerProp.name.text;
                        // this.map.X() patterns
                        if (innerName === 'this' && mapProp === 'map') {
                            // Try to get the Map's value type from class properties
                            let mapValueType = 'unknown';
                            if (classPropertyTypes) {
                                const mapType = classPropertyTypes.get('map');
                                if (mapType && mapType.startsWith('Map<')) {
                                    // Parse Map<K, V> to get V
                                    const match = mapType.match(/Map<[^,]+,\s*(.+)>$/);
                                    if (match) {
                                        [, mapValueType] = match;
                                    }
                                }
                            }
                            if (methodName === 'has')
                                return 'boolean';
                            if (methodName === 'set')
                                return 'this';
                            if (methodName === 'get')
                                return mapValueType;
                            if (methodName === 'delete')
                                return 'boolean';
                            if (methodName === 'clear')
                                return 'void';
                            if (methodName === 'values')
                                return `IterableIterator<${mapValueType}>`;
                            if (methodName === 'keys')
                                return 'IterableIterator<string>';
                            if (methodName === 'entries')
                                return `IterableIterator<[string, ${mapValueType}]>`;
                        }
                    }
                    // Direct map.X() calls
                    if (objName === 'map' || objName === 'obj') {
                        if (methodName === 'has')
                            return 'boolean';
                        if (methodName === 'set')
                            return 'this';
                        if (methodName === 'get')
                            return 'unknown';
                        if (methodName === 'delete')
                            return 'boolean';
                        if (methodName === 'clear')
                            return 'void';
                        if (methodName === 'values')
                            return 'IterableIterator<unknown>';
                        if (methodName === 'keys')
                            return 'IterableIterator<string>';
                        if (methodName === 'entries')
                            return 'IterableIterator<[string, unknown]>';
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
    collectUsage(node, sourceFile) {
        // Check for new Type() instantiation
        if (ts.isNewExpression(node) && node.expression) {
            // `new receiver.Sub()` may construct several types (a receiver
            // typed as a union, or one tactica cannot bind): each gets the
            // record; the result variable binds only to a single answer
            let typeNames = [];
            if (ts.isPropertyAccessExpression(node.expression)) {
                typeNames = this.resolveUsageTypePaths(node.expression).paths;
            }
            else {
                const typeName = this.getTypeNameFromExpression(node.expression);
                typeNames = typeName ? [typeName] : [];
            }
            if (typeNames.length === 1) {
                // Track variable assignment from new Type() for flow analysis
                this.trackNewAssignment(node, typeNames[0]);
            }
            for (const typeName of typeNames) {
                const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                this.addUsage(typeName, {
                    location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
                    kind: 'instantiation',
                    code: node.getText(sourceFile).slice(0, 100),
                    // Constructor expression text ('Thing', 'user.AdminEntity',
                    // a lookup alias) — CreationAnchor.constructorText (Phase 3)
                    constructorText: node.expression.getText(sourceFile).slice(0, 100),
                });
                // Also record as flow event
                this.addFlow(typeName, {
                    location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
                    kind: 'instantiation',
                    code: node.getText(sourceFile).slice(0, 100),
                    context: 'new expression',
                });
            }
        }
        // Check for property access on instances (user.AdminType)
        if (ts.isPropertyAccessExpression(node)) {
            const propName = node.name.text;
            // instance.clone — the PROPERTY form (core types it
            // `readonly clone: this`): the result variable binds to the
            // source instance's type, same as the fork()/clone() call
            // forms (await-transparent). The call form's recording happens
            // in the CallExpression branch; the property branch skips it
            // to avoid a duplicate entry at the same site
            if (propName === 'clone' && ts.isIdentifier(node.expression)) {
                const clonedPath = this.variableToTypeMap.get(node.expression.text);
                const isCallForm = ts.isCallExpression(node.parent) && node.parent.expression === node;
                if (clonedPath) {
                    if (!isCallForm) {
                        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                        this.addUsage(clonedPath, {
                            location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
                            kind: 'instantiation',
                            code: node.getText(sourceFile).slice(0, 100),
                            constructorText: node.getText(sourceFile).slice(0, 100),
                        });
                    }
                    this.bindResultVariable(node, clonedPath);
                }
            }
            // Check if this looks like a type access pattern
            if (propName && this.isLikelyTypeName(propName)) {
                // new x.Sub(…): the NewExpression branch already recorded
                // the site as an instantiation, so a propertyAccess record
                // would duplicate it — one record per site, the same law as
                // the clone guard above. (A whole-callee-parenthesized
                // new (x.Sub)() never matches here: the access's parent is
                // the ParenthesizedExpression, and the instantiation branch
                // cannot resolve that callee — this access stays the site's
                // only record.)
                const isNewCallee = ts.isNewExpression(node.parent) && node.parent.expression === node;
                // x.Sub(…) as a chain tip or a bare subtype call: the
                // CallExpression branch records the site as an
                // instantiation — the same one-record law
                const isConstructionCallee = ts.isCallExpression(node.parent) &&
                    node.parent.expression === node &&
                    (this.resolveChainTipTypePath(node.parent) !== undefined ||
                        this.resolveBareSubtypeCall(node.parent).length > 0);
                const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                const accessed = isNewCallee || isConstructionCallee
                    ? []
                    : this.resolveUsageTypePaths(node).paths;
                for (const fullPath of accessed) {
                    this.addUsage(fullPath, {
                        location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
                        kind: 'propertyAccess',
                        code: node.getText(sourceFile).slice(0, 100),
                    });
                }
            }
        }
        // Check for lookup('TypeName') or lookup(source, 'TypeName') calls
        if (ts.isCallExpression(node) && node.expression) {
            const funcName = this.getFunctionName(node.expression);
            if (funcName === 'lookup' && node.arguments.length > 0) {
                const typePath = this.resolveLookupPath(node);
                if (typePath) {
                    const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                    const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
                    this.addUsage(typePath, {
                        location,
                        kind: 'lookup',
                        code: node.getText(sourceFile).slice(0, 100),
                    });
                    // Track variable assignment from lookup for instantiation tracking
                    this.trackLookupAssignment(node, typePath);
                    // Record for the hard-fail law even when addUsage dropped
                    // the path (unknown paths are exactly the failure class)
                    this.lookupReferences.push({ path: typePath, location });
                }
            }
            // Chain-form construction: `new R(...).A(...)` / the awaited
            // single-chain `await new R(...).A(...).B(...)` — the call on
            // the fresh instance constructs the chain TIP (await is
            // transparent; the NewExpression branch already recorded the
            // inner root). The result variable binds to the tip, not the
            // root (trackNewAssignment resolves the same tip)
            const chainTip = this.resolveChainTipTypePath(node);
            if (chainTip) {
                this.recordConstructionUsage(node, chainTip, sourceFile);
                const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                this.addFlow(chainTip, {
                    location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
                    kind: 'instantiation',
                    code: node.getText(sourceFile).slice(0, 100),
                    context: 'chained construction',
                });
            }
            // Bare subtype call on a known receiver: `instance.Sub(…)`
            // constructs without `new`, as the chain tip does. The
            // variable it initializes binds to a single answer
            const bareCallPaths = chainTip ? [] : this.resolveBareSubtypeCall(node);
            for (const barePath of bareCallPaths) {
                this.recordConstructionUsage(node, barePath, sourceFile);
                const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                this.addFlow(barePath, {
                    location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
                    kind: 'instantiation',
                    code: node.getText(sourceFile).slice(0, 100),
                    context: 'bare subtype call',
                });
            }
            if (bareCallPaths.length === 1) {
                this.bindDirectResult(node, bareCallPaths[0]);
            }
            // mnemonica call/apply(entity, Ctor, ...) / bind(entity, Ctor) —
            // typed construction without `new`: the Ctor argument (arg 1) is
            // the constructed type. Import-aware: only identifiers actually
            // imported from 'mnemonica' (or members of a tracked
            // module-object alias) match — userland call/apply/bind never
            // do. call/apply record the construction; bind() constructs
            // nothing — it only binds the result variable to the Ctor's
            // type (runtime InstanceResult<Merge<E,T>> approximated by T
            // within the output contract)
            const constructionPath = this.resolveConstructionFnTypePath(node);
            if (constructionPath) {
                const isBindForm = this.isMnemonicaConstructionFn(node.expression, 'bind');
                if (!isBindForm) {
                    const ctorArgText = node.arguments[1]?.getText(sourceFile);
                    this.recordConstructionUsage(node, constructionPath, sourceFile, ctorArgText);
                    const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                    this.addFlow(constructionPath, {
                        location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
                        kind: 'instantiation',
                        code: node.getText(sourceFile).slice(0, 100),
                        context: 'call/apply construction',
                    });
                }
                this.bindResultVariable(node, constructionPath);
            }
            // instance.fork()/clone() — runtime re-runs construction (hooks
            // fire, a distinct instance on a distinct line), so an
            // `instantiation` usage records the site IN ADDITION to the
            // result-var binding and the generic methodCall flow (the entry
            // is byte-indistinguishable from `new` until the deferred
            // mechanism-kind revision — the owner's explicit call). Free
            // utils.merge(a, b, ...) / utils.fork(instance)(...) are
            // construction of a's type too (merge = fork(a) over b's
            // context); the result binding keeps the documented arg-0
            // approximation
            const forkLikePath = this.resolveForkLikeTypePath(node);
            if (forkLikePath) {
                this.recordConstructionUsage(node, forkLikePath, sourceFile);
                this.bindResultVariable(node, forkLikePath);
            }
            const utilsPath = this.resolveUtilsFnTypePath(node);
            if (utilsPath) {
                this.recordConstructionUsage(node, utilsPath, sourceFile);
                this.bindResultVariable(node, utilsPath);
            }
        }
    }
    /**
            * Get function name from expression (identifier or property access)
            */
    getFunctionName(expr) {
        if (ts.isIdentifier(expr)) {
            return expr.text;
        }
        if (ts.isPropertyAccessExpression(expr)) {
            return expr.name.text;
        }
        return undefined;
    }
    /**
            * Add a usage to the collection
            */
    addUsage(typePath, usage) {
        // Only track usages of mnemonica-defined types
        if (!this.definitions.has(typePath)) {
            return;
        }
        if (!this.usages.has(typePath)) {
            this.usages.set(typePath, []);
        }
        // Check for duplicates based on location, code, and kind
        const existingUsages = this.usages.get(typePath);
        const isDuplicate = existingUsages.some(existing => existing.location === usage.location &&
            existing.code === usage.code &&
            existing.kind === usage.kind);
        if (!isDuplicate) {
            existingUsages.push(usage);
        }
    }
    /**
     * Collect EDS (Execution Data Storage) usage information
     */
    collectEDS(node, sourceFile) {
        if (!ts.isCallExpression(node) || !node.expression) {
            return;
        }
        const funcName = this.getFunctionName(node.expression);
        if (!funcName) {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        // Enclosing mnemonica type path — wrap args are usually local
        // functions, so the owning define()/lazy() handler or decorated
        // class is what eds.json consumers (GraphBuilder) can join on.
        const scope = this.resolveEDSScope(node);
        // wrap(fn), wrapConstructorArg(fn, parent), upgradeConstructorArg(arg, inst), wrapInstanceMethods(obj)
        if (funcName === 'wrap' ||
            funcName === 'wrapConstructorArg' ||
            funcName === 'upgradeConstructorArg' ||
            funcName === 'wrapInstanceMethods') {
            const targetType = this.resolveEDSArgumentType(node.arguments[0]);
            // dive's wrap-family signatures (dive/src/index.ts):
            //   wrap(fn, label?) | wrap(fn, context?, label?)
            //   wrapConstructorArg(fn, context)
            //   upgradeConstructorArg(arg, instance)
            //   wrapInstanceMethods(instance)
            // …so the instance/context arg sits at args[1] (args[0] for
            // wrapInstanceMethods) and a string literal in args[1..2] is the label
            const instanceArgNode = funcName === 'wrapInstanceMethods'
                ? node.arguments[0]
                : node.arguments[1];
            // Fire-and-forget wrappers (wire-up helpers, registration
            // functions) sit outside any define()/lazy() handler, so the
            // lexical scope is absent — attribute through the instance/context
            // argument instead: a tracked assignment, else the enclosing
            // function's parameter annotation resolved through the graph law
            const instanceTypePath = instanceArgNode
                ? this.resolveWrapInstanceTypePath(instanceArgNode)
                : undefined;
            const effectiveScope = scope ?? instanceTypePath;
            const info = {
                location,
                kind: 'wrap',
                code,
                targetType: targetType || undefined,
                scope: effectiveScope,
                fn: funcName,
            };
            if (instanceArgNode && ts.isIdentifier(instanceArgNode)) {
                info.instanceArg = instanceArgNode.text;
            }
            for (const extraArg of [node.arguments[1], node.arguments[2]]) {
                if (extraArg && ts.isStringLiteral(extraArg)) {
                    info.label = extraArg.text;
                    break;
                }
            }
            // A wrap() call nested inside another wrapped body carries the
            // link to the site whose runtime wrapping caused it — and, when
            // the nested site has no scope of its own, the causing site's
            // scope attribution travels with the link
            const viaLink = this.nestedWrapVia.get(node);
            if (viaLink) {
                info.via = viaLink.via;
                if (info.scope === undefined) {
                    info.scope = viaLink.scope;
                }
            }
            // dive wraps returned functions too, and any mnemonica instance
            // created inside the wrapped body is a guaranteed path hit —
            // both are calculable AoT, so record them
            const wrapped = this.resolveFunctionArgument(node.arguments[0], sourceFile);
            if (wrapped) {
                // The wrapped callback gets its own scope in scopes.json keyed by
                // its start position — record that scopeId so graph consumers can
                // join a wrap entry to the callback's creation node
                const callbackPos = ts.getLineAndCharacterOfPosition(sourceFile, wrapped.getStart(sourceFile));
                const callbackFile = nodePath.resolve(sourceFile.fileName);
                info.callbackScopeId = `${callbackFile}:${callbackPos.line + 1}:${callbackPos.character + 1}`;
                const createsTypes = new Set();
                this.analyzeWrappedBody(wrapped, location, sourceFile, 0, new Set(), createsTypes, effectiveScope);
                if (createsTypes.size > 0) {
                    info.createsTypes = Array.from(createsTypes);
                }
            }
            const stored = this.addEDS(targetType || effectiveScope || 'unknown', info);
            this.wrapEntryByNode.set(node, stored);
            return;
        }
        // current(), getErrorInstance(err), getFlow(target?)
        if (funcName === 'current' || funcName === 'getErrorInstance' || funcName === 'getFlow') {
            this.addEDS(scope || 'unknown', {
                location,
                kind: 'contextConsume',
                code,
                scope,
            });
            return;
        }
        // attachHooks(collection) — from @mnemonica/otel, wires a
        // TypesCollection to dive's lifecycle tracing
        if (funcName === 'attachHooks' && node.arguments.length > 0) {
            const [arg] = node.arguments;
            if (ts.isArrayLiteralExpression(arg)) {
                for (const element of arg.elements) {
                    const targetType = this.resolveEDSArgumentType(element);
                    this.addEDS(targetType || scope || 'unknown', {
                        location,
                        kind: 'hookAttach',
                        code,
                        targetType: targetType || undefined,
                        scope,
                    });
                }
            }
            else {
                const targetType = this.resolveEDSArgumentType(arg);
                this.addEDS(targetType || scope || 'unknown', {
                    location,
                    kind: 'hookAttach',
                    code,
                    targetType: targetType || undefined,
                    scope,
                });
            }
            return;
        }
    }
    /**
     * Resolve type from EDS call argument (best effort)
     */
    resolveEDSArgumentType(arg) {
        if (!arg) {
            return undefined;
        }
        // Identifier: variable name
        if (ts.isIdentifier(arg)) {
            const mapped = this.variableToTypeMap.get(arg.text);
            if (mapped) {
                return mapped;
            }
            // Maybe it's a type name directly
            if (this.definitions.has(arg.text)) {
                return arg.text;
            }
            // let-in-try: a let/var binding declared without a tracked
            // initializer and assigned later in the SAME scope (the
            // fire-and-forget catch-guard pattern: `let fn; try { fn =
            // … } catch { return } wrap(fn, …)`) — follow the first
            // statically-visible in-scope assignment. No flow analysis:
            // function/class boundaries are not crossed, a
            // never-assigned binding stays unknown (F20 discipline).
            // When the assignment resolves, its evidence WINS over any
            // declaration annotation (the constructed subtype is the more
            // specific truth); an unresolvable RHS (a userland call, say)
            // falls through to the annotation claim below.
            const assigned = this.followScopeAssignment(arg.text, arg);
            if (assigned) {
                const resolved = this.resolveEDSArgumentType(assigned);
                if (resolved) {
                    return resolved;
                }
            }
            // Annotation fallback — the F20 discipline one argument over:
            // an explicit declaration or parameter annotation is a user
            // claim written in the AST, not flow analysis. Parameter
            // first: it shadows an outer let, same as the context-arg path.
            const annotated = this.resolveParameterAnnotationTypePath(arg.text, arg) ??
                this.resolveVariableAnnotationTypePath(arg.text, arg);
            return annotated;
        }
        // NewExpression: the constructed type — reachable directly
        // (wrap(new T(), …)) or through a followed assignment
        if (ts.isNewExpression(arg)) {
            const ctorExpr = arg.expression;
            const name = ts.isPropertyAccessExpression(ctorExpr)
                ? this.resolveTypePath(ctorExpr)
                : this.getTypeNameFromExpression(ctorExpr);
            const known = name && this.definitions.has(name) ? name : undefined;
            return known;
        }
        // Property access: obj.prop
        if (ts.isPropertyAccessExpression(arg)) {
            return this.resolveTypePath(arg);
        }
        // This expression: this.something
        if (ts.isPropertyAccessExpression(arg) && ts.isIdentifier(arg.expression) && arg.expression.text === 'this') {
            return undefined;
        }
        return undefined;
    }
    /**
     * let-in-try: find the RIGHT-HAND SIDE of the first statically-visible
     * assignment to `name` in the scope that declares it. The declaring
     * container is found innermost-out (blocks, case clauses, the source
     * file — the F20 walk); the scan recurses into nested blocks (try/
     * catch/finally, if/else, loops, switch cases) but NEVER crosses
     * function or class boundaries — an assignment inside a closure does
     * not attribute. Returns undefined when the binding is declared but
     * never assigned in scope (and stops there: an inner declaration
     * shadows any outer binding).
     */
    followScopeAssignment(name, from) {
        let current = from;
        while (current) {
            const statements = ts.isBlock(current) || ts.isModuleBlock(current) || ts.isSourceFile(current)
                ? current.statements
                : ts.isCaseClause(current) || ts.isDefaultClause(current)
                    ? current.statements
                    : undefined;
            if (statements && this.statementsDeclareVariable(statements, name)) {
                const rhs = this.findAssignmentRhsInStatements(statements, name);
                return rhs;
            }
            current = current.parent;
        }
        return undefined;
    }
    /**
     * True when the statement list contains a `let`/`var`/`const`
     * declaration for `name` (any initializer form).
     */
    statementsDeclareVariable(statements, name) {
        for (const statement of statements) {
            if (!ts.isVariableStatement(statement)) {
                continue;
            }
            for (const declaration of statement.declarationList.declarations) {
                if (ts.isIdentifier(declaration.name) && declaration.name.text === name) {
                    return true;
                }
            }
        }
        return false;
    }
    /**
     * First `name = rhs` assignment in the statement list, recursing
     * into nested in-scope blocks. Function and class bodies are
     * boundaries and are not entered.
     */
    findAssignmentRhsInStatements(statements, name) {
        for (const statement of statements) {
            const direct = this.directAssignmentRhs(statement, name);
            if (direct) {
                return direct;
            }
            for (const nested of this.nestedScopeBlocks(statement)) {
                const found = this.findAssignmentRhsInStatements(nested, name);
                if (found) {
                    return found;
                }
            }
        }
        return undefined;
    }
    /**
     * `name = rhs` as a direct expression statement.
     */
    directAssignmentRhs(statement, name) {
        if (!ts.isExpressionStatement(statement)) {
            return undefined;
        }
        const expr = statement.expression;
        if (!ts.isBinaryExpression(expr) || expr.operatorToken.kind !== ts.SyntaxKind.EqualsToken) {
            return undefined;
        }
        if (!ts.isIdentifier(expr.left) || expr.left.text !== name) {
            return undefined;
        }
        const rhs = expr.right;
        return rhs;
    }
    /**
     * Statement lists of the nested blocks that stay INSIDE the current
     * scope — try/catch/finally, if/else, loops, switch cases, nested
     * blocks, labeled statements. Function-like and class bodies are
     * scope boundaries and yield nothing.
     */
    nestedScopeBlocks(statement) {
        const blocks = [];
        const push = (node) => {
            if (node && ts.isBlock(node)) {
                blocks.push([...node.statements]);
            }
        };
        if (ts.isBlock(statement)) {
            blocks.push([...statement.statements]);
        }
        else if (ts.isTryStatement(statement)) {
            push(statement.tryBlock);
            if (statement.catchClause) {
                push(statement.catchClause.block);
            }
            push(statement.finallyBlock);
        }
        else if (ts.isIfStatement(statement)) {
            push(statement.thenStatement);
            push(statement.elseStatement);
        }
        else if (ts.isForStatement(statement) || ts.isForInStatement(statement) ||
            ts.isForOfStatement(statement) || ts.isWhileStatement(statement) ||
            ts.isDoStatement(statement) || ts.isWithStatement(statement)) {
            push(statement.statement);
        }
        else if (ts.isSwitchStatement(statement)) {
            for (const clause of statement.caseBlock.clauses) {
                blocks.push([...clause.statements]);
            }
        }
        else if (ts.isLabeledStatement(statement)) {
            const nested = this.nestedScopeBlocks(statement.statement);
            for (const block of nested) {
                blocks.push([...block]);
            }
        }
        const result = blocks;
        return result;
    }
    /**
     * Resolve the enclosing mnemonica scope of an EDS call site by walking
     * up the parent chain: nearest define()/lazy() call whose handler holds
     * the node, or nearest @decorate()-ed class declaration. Best effort —
     * returns undefined for calls outside any type scope (module top level).
     */
    resolveEDSScope(node) {
        let current = node.parent;
        while (current) {
            const scopePath = this.edsScopeByNode.get(current);
            if (scopePath) {
                return scopePath;
            }
            current = current.parent;
        }
        return undefined;
    }
    /**
     * Resolve a wrap site's instance/context argument to a mnemonica type
     * path — the fire-and-forget-wrapper attribution fallback when the call
     * sits outside any define()/lazy() handler: a tracked assignment
     * (`const holder = new Holder(...)`), else the root identifier's
     * (property-access roots included) parameter annotation resolved
     * through the graph law. Ambiguity or absence stays silent — this is a
     * metadata heuristic, not the identity-law surface.
     */
    resolveWrapInstanceTypePath(arg) {
        const fromBinding = (name, from) => {
            const mapped = this.variableToTypeMap.get(name);
            if (mapped) {
                return mapped;
            }
            const annotationType = this.resolveParameterAnnotationTypePath(name, from) ??
                // F20 cheap tier: the identifier is bound to a let/var/const
                // with an EXPLICIT type annotation — resolve the annotation
                // through the graph law. No flow-sensitive assignment
                // tracking: an UNANNOTATED let still buckets unknown
                this.resolveVariableAnnotationTypePath(name, from);
            return annotationType;
        };
        if (ts.isIdentifier(arg)) {
            const result = fromBinding(arg.text, arg);
            return result;
        }
        if (ts.isPropertyAccessExpression(arg)) {
            const root = this.getRootIdentifier(arg);
            if (root) {
                const result = fromBinding(root.text, arg);
                return result;
            }
        }
        return undefined;
    }
    /**
     * Emission-law helper (0.2.0 restoration): is `name` declared in any
     * ANALYZED PROJECT file? External/ambient files (.d.ts, node_modules)
     * do not count. A name with no project declaration is an ambient/lib
     * construct — safe to emit verbatim into the self-contained types.ts;
     * a project-local name is not (no imports in the generated file).
     */
    isProjectDeclaredTypeName(name) {
        for (const [file, decls] of this.referencedTypeDecls) {
            if (this.isExternalDeclFile(file)) {
                continue;
            }
            if (decls.has(name)) {
                return true;
            }
        }
        const result = false;
        return result;
    }
    /**
     * F24: resolve a bare-identifier annotation to a graph fullPath. The
     * annotation may name the type directly (`LedgerUpdate`) or carry
     * the GENERATED instance alias of a nested type
     * (`UpdatePay_SomeTerminal`, imported from the generated types file
     * via tsconfig paths) — not a graph node NAME. The name is tried
     * as-is first, then its underscore→dotted form (the generated alias
     * naming law; the same mapping scopes.json uses for annotations).
     * Ambiguity and absence yield undefined.
     */
    resolveAnnotationTypePath(name) {
        const direct = this.resolveGraphTypeName(name);
        if (direct.status === 'unique') {
            const result = direct.node.fullPath;
            return result;
        }
        if (!name.includes('_')) {
            return undefined;
        }
        const aliased = this.resolveGraphTypeName(name.replace(/_/g, '.'));
        if (aliased.status === 'unique') {
            const result = aliased.node.fullPath;
            return result;
        }
        return undefined;
    }
    /**
     * Resolve a bare-identifier type annotation of the nearest enclosing
     * function's parameter through the mnemonica-graph tiers (value scope,
     * imports, roots, program-wide-unique). Non-identifier and generic
     * annotations are not graph references; ambiguity and absence yield
     * undefined.
     */
    resolveParameterAnnotationTypePath(name, from) {
        let current = from.parent;
        while (current) {
            if (ts.isFunctionLike(current)) {
                for (const param of current.parameters ?? []) {
                    if (!ts.isIdentifier(param.name) || param.name.text !== name || !param.type ||
                        !ts.isTypeReferenceNode(param.type) ||
                        !ts.isIdentifier(param.type.typeName) ||
                        (param.type.typeArguments?.length ?? 0) > 0) {
                        continue;
                    }
                    const resolved = this.resolveAnnotationTypePath(param.type.typeName.text);
                    if (resolved) {
                        return resolved;
                    }
                }
                return undefined;
            }
            current = current.parent;
        }
        return undefined;
    }
    /**
     * F20 cheap tier: the wrap argument is an identifier declared with an
     * EXPLICIT type annotation (`let updateCommitted: LedgerUpdate;`
     * assigned later in a flow the analyzer does not track). The
     * annotation resolves through the same graph tiers as parameter
     * annotations. Deliberately NOT flow-sensitive: an UNANNOTATED
     * let/var still buckets unknown, and a const with an analyzable
     * initializer stays the recommended discipline. The lookup walks the
     * enclosing statement containers innermost-out, so a shadowing inner
     * declaration wins.
     */
    resolveVariableAnnotationTypePath(name, from) {
        let current = from;
        while (current) {
            const statements = ts.isBlock(current) || ts.isModuleBlock(current) || ts.isSourceFile(current)
                ? current.statements
                : ts.isCaseClause(current) || ts.isDefaultClause(current)
                    ? current.statements
                    : undefined;
            if (statements) {
                const resolved = this.findAnnotatedVariableTypePath(statements, name);
                if (resolved) {
                    return resolved;
                }
            }
            current = current.parent;
        }
        return undefined;
    }
    /**
     * First variable declaration carrying an explicit bare-identifier type
     * annotation for `name` in the given statement list, resolved through
     * the graph law.
     */
    findAnnotatedVariableTypePath(statements, name) {
        for (const statement of statements) {
            if (!ts.isVariableStatement(statement)) {
                continue;
            }
            for (const declaration of statement.declarationList.declarations) {
                if (!ts.isIdentifier(declaration.name) || declaration.name.text !== name ||
                    !declaration.type ||
                    !ts.isTypeReferenceNode(declaration.type) ||
                    !ts.isIdentifier(declaration.type.typeName) ||
                    (declaration.type.typeArguments?.length ?? 0) > 0) {
                    continue;
                }
                const resolved = this.resolveAnnotationTypePath(declaration.type.typeName.text);
                if (resolved) {
                    return resolved;
                }
            }
        }
        return undefined;
    }
    /**
     * Resolve a wrap() argument to its function node without the type
     * checker: direct function expressions/arrows, or same-file bindings
     * (`const fn = () => ...`, `function fn() ...`). Best effort — method
     * references, .bind() products and cross-file identifiers stay
     * unresolved; the callsite entry itself is still recorded.
     */
    resolveFunctionArgument(arg, sourceFile) {
        if (!arg) {
            return undefined;
        }
        if (ts.isArrowFunction(arg) || ts.isFunctionExpression(arg)) {
            return arg;
        }
        if (ts.isIdentifier(arg)) {
            const key = `${sourceFile.fileName}#${arg.text}`;
            const bound = this.functionBindings.get(key);
            if (bound) {
                return bound;
            }
        }
        return undefined;
    }
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
    analyzeWrappedBody(fn, viaLocation, sourceFile, depth, visited, createsTypes, fallbackScope) {
        if (depth > 5 || visited.has(fn) || !fn.body) {
            return;
        }
        visited.add(fn);
        // Arrow with expression body: implicit return
        if (ts.isArrowFunction(fn) && !ts.isBlock(fn.body)) {
            this.recordWrappedReturn(fn.body, viaLocation, sourceFile, depth, visited, fallbackScope);
            return;
        }
        const walk = (node) => {
            if (node !== fn.body && (ts.isFunctionExpression(node) ||
                ts.isArrowFunction(node) ||
                ts.isFunctionDeclaration(node) ||
                ts.isMethodDeclaration(node))) {
                // nested function bodies are analysed through the return chain
                return;
            }
            if (ts.isReturnStatement(node) && node.expression) {
                this.recordWrappedReturn(node.expression, viaLocation, sourceFile, depth, visited, fallbackScope);
            }
            if (ts.isNewExpression(node)) {
                const created = this.resolveExpressionType(node.expression) ||
                    (ts.isIdentifier(node.expression) && this.definitions.has(node.expression.text)
                        ? node.expression.text
                        : undefined);
                if (created) {
                    createsTypes.add(created);
                }
            }
            if (ts.isCallExpression(node)) {
                const nestedName = this.getFunctionName(node.expression);
                if (nestedName === 'wrap' ||
                    nestedName === 'wrapConstructorArg' ||
                    nestedName === 'upgradeConstructorArg' ||
                    nestedName === 'wrapInstanceMethods') {
                    // the nested call may already be collected (visited
                    // before this outer wrap site) — back-patch its entry,
                    // otherwise leave the link (with this site's scope) for
                    // collectEDS to pick up
                    const nestedEntry = this.wrapEntryByNode.get(node);
                    if (nestedEntry) {
                        nestedEntry.via = viaLocation;
                        if (nestedEntry.scope === undefined) {
                            nestedEntry.scope = fallbackScope;
                        }
                    }
                    else {
                        this.nestedWrapVia.set(node, { via: viaLocation, scope: fallbackScope });
                    }
                }
            }
            ts.forEachChild(node, walk);
        };
        walk(fn.body);
    }
    /**
     * Record one function-valued return of a wrapped body as a nested wrap
     * site (`via` = the site whose wrapping caused it) and recurse into
     * its own returns. Returns through identifiers resolve through the
     * same-file bindings table; unresolvable returns are simply skipped.
     * A return declared outside any type scope inherits the causing wrap
     * site's scope attribution (the generation chain is the only holder).
     */
    recordWrappedReturn(expr, viaLocation, sourceFile, depth, visited, fallbackScope) {
        const returned = this.resolveFunctionArgument(expr, sourceFile);
        if (!returned) {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, returned.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = returned.getText(sourceFile).slice(0, 100);
        const scope = this.resolveEDSScope(returned) ?? fallbackScope;
        const entry = this.addEDS(scope || 'unknown', {
            location,
            kind: 'wrap',
            code,
            scope,
            via: viaLocation,
            // dive wraps returned functions through the same wrap machinery
            fn: 'wrap',
        });
        // the returned function's own returns are wrapped in turn; `via`
        // chains to this nested entry's location
        const nestedCreates = new Set();
        this.analyzeWrappedBody(returned, location, sourceFile, depth + 1, visited, nestedCreates, scope);
        if (nestedCreates.size > 0) {
            entry.createsTypes = Array.from(nestedCreates);
        }
    }
    /**
     * Add an EDS usage to the collection
     * Returns the stored entry (the existing one when this is a duplicate),
     * so callers can enrich it after nested body analysis.
     */
    addEDS(typePath, info) {
        if (!this.edsUsages.has(typePath)) {
            this.edsUsages.set(typePath, []);
        }
        const existing = this.edsUsages.get(typePath);
        const duplicate = existing.find(e => {
            return e.location === info.location &&
                e.kind === info.kind &&
                e.code === info.code;
        });
        if (duplicate) {
            return duplicate;
        }
        existing.push(info);
        return info;
    }
    /**
     * Collect native flow patterns (instance usage after creation)
     * Phase 1: property access, method calls, arguments, return, destructuring, etc.
     */
    collectFlow(node, sourceFile) {
        // Property read: user.name or user?.name
        if (ts.isPropertyAccessExpression(node)) {
            this.collectFlowPropertyAccess(node, sourceFile);
            return;
        }
        // Element access: user['name']
        if (ts.isElementAccessExpression(node)) {
            this.collectFlowElementAccess(node, sourceFile);
            return;
        }
        // Property write: user.name = value
        if (ts.isBinaryExpression(node) && node.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
            this.collectFlowAssignment(node, sourceFile);
            return;
        }
        // Method call: user.validate()  AND  argument passing: processUser(user)
        if (ts.isCallExpression(node) && node.expression) {
            this.collectFlowMethodCall(node, sourceFile);
            this.collectFlowArgumentPass(node, sourceFile);
            return;
        }
        // Destructure read: const { name } = user
        if (ts.isVariableDeclaration(node) && node.initializer) {
            this.collectFlowDestructure(node, sourceFile);
            return;
        }
        // Return instance: return user
        if (ts.isReturnStatement(node) && node.expression) {
            this.collectFlowReturn(node, sourceFile);
            return;
        }
        // Spread: { ...user }
        if (ts.isSpreadElement(node)) {
            this.collectFlowSpread(node, sourceFile);
            return;
        }
    }
    /**
     * Collect property access flow (read or conditional)
     */
    collectFlowPropertyAccess(node, sourceFile) {
        const objectType = this.resolveExpressionType(node.expression);
        if (!objectType) {
            return;
        }
        const propName = node.name.text;
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        // Skip if this is a type constructor access (e.g., UserType.define)
        if (propName === 'define' || propName === 'lazy') {
            return;
        }
        this.addFlow(objectType, {
            location,
            kind: 'propertyRead',
            code,
            propertyName: propName,
            targetType: objectType
        });
    }
    /**
     * Collect element access flow: user['name']
     */
    collectFlowElementAccess(node, sourceFile) {
        const objectType = this.resolveExpressionType(node.expression);
        if (!objectType) {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        this.addFlow(objectType, {
            location,
            kind: 'elementAccess',
            code,
            targetType: objectType
        });
    }
    /**
     * Collect assignment flow: user.name = value or user = other
     */
    collectFlowAssignment(node, sourceFile) {
        // Property write: user.name = value
        if (ts.isPropertyAccessExpression(node.left)) {
            const objectType = this.resolveExpressionType(node.left.expression);
            if (!objectType) {
                return;
            }
            const propName = node.left.name.text;
            const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
            const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
            const code = node.getText(sourceFile).slice(0, 100);
            this.addFlow(objectType, {
                location,
                kind: 'propertyWrite',
                code,
                propertyName: propName,
                targetType: objectType
            });
            return;
        }
        // Variable reassignment: user = other
        if (ts.isIdentifier(node.left)) {
            const varName = node.left.text;
            const mappedType = this.variableToTypeMap.get(varName);
            if (!mappedType) {
                return;
            }
            const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
            const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
            const code = node.getText(sourceFile).slice(0, 100);
            this.addFlow(mappedType, {
                location,
                kind: 'reassignment',
                code,
                targetType: mappedType
            });
        }
    }
    /**
     * Collect method call flow: user.validate()
     */
    collectFlowMethodCall(node, sourceFile) {
        if (!ts.isPropertyAccessExpression(node.expression)) {
            return;
        }
        const objectType = this.resolveExpressionType(node.expression.expression);
        if (!objectType) {
            return;
        }
        const methodName = node.expression.name.text;
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        // Skip if this is a type constructor call (e.g., new UserType())
        if (methodName === 'define' || methodName === 'lazy') {
            return;
        }
        this.addFlow(objectType, {
            location,
            kind: 'methodCall',
            code,
            propertyName: methodName,
            targetType: objectType
        });
    }
    /**
     * Collect argument passing flow: processUser(user)
     */
    collectFlowArgumentPass(node, sourceFile) {
        for (let i = 0; i < node.arguments.length; i++) {
            const arg = node.arguments[i];
            const argType = this.resolveExpressionType(arg);
            if (!argType) {
                continue;
            }
            const funcName = this.getFunctionName(node.expression) || 'anonymous';
            const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
            const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
            const code = node.getText(sourceFile).slice(0, 100);
            this.addFlow(argType, {
                location,
                kind: 'passAsArg',
                code,
                targetType: argType,
                context: `arg ${i} to ${funcName}`
            });
        }
    }
    /**
     * Collect destructuring flow: const { name } = user
     */
    collectFlowDestructure(node, sourceFile) {
        if (!ts.isObjectBindingPattern(node.name)) {
            return;
        }
        const sourceType = this.resolveExpressionType(node.initializer);
        if (!sourceType) {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        // Extract destructured property names
        const props = [];
        for (const element of node.name.elements) {
            if (ts.isIdentifier(element.name)) {
                props.push(element.name.text);
            }
        }
        this.addFlow(sourceType, {
            location,
            kind: 'destructureRead',
            code,
            targetType: sourceType,
            context: props.join(', ')
        });
    }
    /**
     * Collect return flow: return user
     */
    collectFlowReturn(node, sourceFile) {
        const returnType = this.resolveExpressionType(node.expression);
        if (!returnType) {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        this.addFlow(returnType, {
            location,
            kind: 'return',
            code,
            targetType: returnType
        });
    }
    /**
     * Collect spread flow: { ...user }
     */
    collectFlowSpread(node, sourceFile) {
        const spreadType = this.resolveExpressionType(node.expression);
        if (!spreadType) {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        this.addFlow(spreadType, {
            location,
            kind: 'spread',
            code,
            targetType: spreadType
        });
    }
    /**
     * Resolve type from an expression (identifier, property access, etc.)
     */
    resolveExpressionType(expr) {
        // Identifier: user
        if (ts.isIdentifier(expr)) {
            return this.variableToTypeMap.get(expr.text);
        }
        // Property access: user.name (return object type, not property type)
        if (ts.isPropertyAccessExpression(expr)) {
            return this.resolveExpressionType(expr.expression);
        }
        // Element access: user['name']
        if (ts.isElementAccessExpression(expr)) {
            return this.resolveExpressionType(expr.expression);
        }
        // This expression: this (if in a method, we can't resolve without more context)
        if (expr.kind === ts.SyntaxKind.ThisKeyword) {
            return undefined;
        }
        return undefined;
    }
    /**
     * Add a flow usage to the collection
     */
    addFlow(typePath, info) {
        if (!this.flowUsages.has(typePath)) {
            this.flowUsages.set(typePath, []);
        }
        const existing = this.flowUsages.get(typePath);
        const isDuplicate = existing.some(e => {
            return e.location === info.location &&
                e.kind === info.kind &&
                e.code === info.code;
        });
        if (!isDuplicate) {
            existing.push(info);
        }
    }
    /**
            * Get type name from expression (identifier or property access)
            */
    getTypeNameFromExpression(expr) {
        if (ts.isIdentifier(expr)) {
            const name = expr.text;
            // Check if this identifier is a variable mapped to a type (e.g., from lookup)
            const mappedType = this.variableToTypeMap.get(name);
            if (mappedType) {
                return mappedType;
            }
            return name;
        }
        if (ts.isPropertyAccessExpression(expr)) {
            const chain = this.getPropertyChain(expr);
            return chain.join('.');
        }
        return undefined;
    }
    /**
     * The one candidate whose parent type is defined in `fileName`, or
     * undefined when none or several qualify.
     */
    subtypeOwnedByFile(candidates, fileName) {
        const file = nodePath.resolve(fileName);
        const owned = candidates.filter((candidate) => {
            const parent = this.definitions.get(candidate)?.parent;
            const parentLocation = parent ? this.definitions.get(parent)?.location : undefined;
            const parentFile = parentLocation ? parentLocation.replace(/:\d+:\d+$/, '') : undefined;
            const inFile = parentFile !== undefined && nodePath.resolve(parentFile) === file;
            return inFile;
        });
        const result = owned.length === 1 ? owned[0] : undefined;
        return result;
    }
    /**
            * Resolve full type path from property access
            */
    resolveTypePath(expr) {
        const chain = this.getPropertyChain(expr);
        if (chain.length === 0)
            return undefined;
        // Check if this chain matches a known type
        const fullPath = chain.join('.');
        if (this.definitions.has(fullPath)) {
            return fullPath;
        }
        // Instance receiver: `lesson.Native` where `lesson` is bound to a
        // Run.Lesson instance means Run.Lesson.Native — resolve through the
        // variable's type before falling back to the bare name
        if (chain.length > 1) {
            const receiverType = this.variableToTypeMap.get(chain[0]);
            const viaReceiver = receiverType ? `${receiverType}.${chain.slice(1).join('.')}` : undefined;
            if (viaReceiver && this.definitions.has(viaReceiver)) {
                return viaReceiver;
            }
        }
        // Try just the property name
        const propName = chain[chain.length - 1];
        const candidates = [];
        for (const [path] of this.definitions) {
            if (path.endsWith(`.${propName}`) || path === propName) {
                candidates.push(path);
            }
        }
        // Several types share the name (Correct.StatUpdate and
        // Mistake.StatUpdate): `new this.StatUpdate()` inside a type's own
        // file means THAT type's subtype — prefer the candidate whose parent
        // is defined in the file the access sits in (topologica: one file
        // per type). Otherwise the first match, as before.
        if (candidates.length > 1) {
            const owned = this.subtypeOwnedByFile(candidates, expr.getSourceFile().fileName);
            if (owned) {
                return owned;
            }
        }
        if (candidates.length > 0) {
            return candidates[0];
        }
        return fullPath;
    }
    /**
     * Every type a `receiver.Sub` access can denote, for usage
     * attribution: the exact path, the receiver's value binding, the
     * receiver's declared type (one or several generated types), or —
     * when none applies — every namesake. A construction through a
     * receiver tactica cannot bind is never given to one namesake only:
     * a type left without usages reads as never constructed. The
     * same-file preference (subtypeOwnedByFile) still picks one namesake.
     */
    resolveUsageTypePaths(expr) {
        const chain = this.getPropertyChain(expr);
        const fullPath = chain.join('.');
        if (chain.length > 0 && this.definitions.has(fullPath)) {
            const exact = { paths: [fullPath], via: 'exact' };
            return exact;
        }
        if (chain.length > 1) {
            const rest = chain.slice(1).join('.');
            const receiverType = this.variableToTypeMap.get(chain[0]);
            const viaReceiver = receiverType ? `${receiverType}.${rest}` : undefined;
            if (viaReceiver && this.definitions.has(viaReceiver)) {
                const bound = { paths: [viaReceiver], via: 'binding' };
                return bound;
            }
            const annotated = this.resolveReceiverAnnotationOwners(expr, chain[0])
                .map(owner => `${owner}.${rest}`)
                .filter(path => this.definitions.has(path));
            if (annotated.length > 0) {
                const viaAnnotation = { paths: annotated, via: 'annotation' };
                return viaAnnotation;
            }
        }
        const propName = expr.name.text;
        const candidates = [];
        for (const [path] of this.definitions) {
            if (path.endsWith(`.${propName}`) || path === propName) {
                candidates.push(path);
            }
        }
        const owned = candidates.length > 1
            ? this.subtypeOwnedByFile(candidates, expr.getSourceFile().fileName)
            : undefined;
        const byName = { paths: owned ? [owned] : candidates, via: 'name' };
        return byName;
    }
    /**
     * The fullPaths of the generated types a receiver's declared type
     * names: `gadget: Alpha_Gadget | Beta_Gadget` → Alpha.Gadget and
     * Beta.Gadget. Read from the annotation, not from a TypeChecker (the
     * analyzer runs without one).
     */
    resolveReceiverAnnotationOwners(from, name) {
        const typeNode = this.findDeclaredTypeOf(from, name);
        const owners = typeNode
            ? this.collectAnnotationOwners(typeNode, this.currentReferencedTypeFile, new Set(), 0)
            : [];
        const unique = Array.from(new Set(owners));
        return unique;
    }
    /**
     * The type annotation of the nearest declaration of `name` visible
     * from `from`: a parameter of an enclosing function, or a
     * `const/let/var` in an enclosing block or the file. The first
     * declaration found wins (shadowing), annotated or not.
     */
    findDeclaredTypeOf(from, name) {
        let current = from.parent;
        while (current) {
            if (ts.isFunctionLike(current)) {
                const param = current.parameters.find(p => ts.isIdentifier(p.name) && p.name.text === name);
                if (param) {
                    const paramType = param.type;
                    return paramType;
                }
            }
            if (ts.isBlock(current) || ts.isSourceFile(current) || ts.isModuleBlock(current)) {
                for (const statement of current.statements) {
                    if (!ts.isVariableStatement(statement)) {
                        continue;
                    }
                    const decl = statement.declarationList.declarations
                        .find(d => ts.isIdentifier(d.name) && d.name.text === name);
                    if (decl) {
                        const declType = decl.type;
                        return declType;
                    }
                }
            }
            current = current.parent;
        }
        return undefined;
    }
    collectAnnotationOwners(typeNode, fromFile, visited, depth) {
        const owners = [];
        if (depth > MAX_ANNOTATION_OWNER_DEPTH) {
            return owners;
        }
        if (ts.isParenthesizedTypeNode(typeNode)) {
            owners.push(...this.collectAnnotationOwners(typeNode.type, fromFile, visited, depth + 1));
        }
        else if (ts.isUnionTypeNode(typeNode) || ts.isIntersectionTypeNode(typeNode)) {
            for (const member of typeNode.types) {
                owners.push(...this.collectAnnotationOwners(member, fromFile, visited, depth + 1));
            }
        }
        else if (ts.isTypeReferenceNode(typeNode) && ts.isIdentifier(typeNode.typeName)) {
            owners.push(...this.ownersOfTypeName(typeNode.typeName.text, fromFile, visited, depth + 1));
        }
        return owners;
    }
    /**
     * A type name → the generated types it stands for: a generated
     * instance alias itself (an import rename is read back to the original
     * name), or a type alias / interface `extends` leading to them,
     * followed across files like referenced types are.
     */
    ownersOfTypeName(name, fromFile, visited, depth) {
        const owners = [];
        const imported = this.referencedTypeImports.get(fromFile)?.get(name);
        const originalName = imported && !imported.isNamespace ? imported.originalName : name;
        const generated = this.findPathByEmittedName(originalName);
        if (generated) {
            owners.push(generated);
            return owners;
        }
        const visitKey = `${fromFile}#${name}`;
        if (depth > MAX_ANNOTATION_OWNER_DEPTH || visited.has(visitKey)) {
            return owners;
        }
        visited.add(visitKey);
        const decl = this.resolveReferencedTypeDeclaration(name, fromFile);
        if (!decl) {
            return owners;
        }
        if (ts.isTypeAliasDeclaration(decl.node)) {
            owners.push(...this.collectAnnotationOwners(decl.node.type, decl.file, visited, depth + 1));
        }
        else if (ts.isInterfaceDeclaration(decl.node)) {
            for (const clause of decl.node.heritageClauses ?? []) {
                for (const heritage of clause.types) {
                    if (ts.isIdentifier(heritage.expression)) {
                        owners.push(...this.ownersOfTypeName(heritage.expression.text, decl.file, visited, depth + 1));
                    }
                }
            }
        }
        return owners;
    }
    /**
     * The fullPath whose emitted instance alias is `emittedName`
     * (`Alpha_Gadget` → `Alpha.Gadget`), from the current graph
     */
    findPathByEmittedName(emittedName) {
        for (const node of this.graph.bfs()) {
            if (this.getEmittedInstanceTypeName(node) === emittedName) {
                const found = node.fullPath;
                return found;
            }
        }
        return undefined;
    }
    /**
     * A bare subtype call — `instance.Sub(…)` without `new` — constructs,
     * as the chain tip `new R().Sub()` does. Counted only when the
     * receiver is known as a value binding or by its declared type: a
     * receiver tactica cannot see may be anything, and an uppercase
     * method name alone is not a construction.
     */
    resolveBareSubtypeCall(call) {
        const callee = call.expression;
        if (!ts.isPropertyAccessExpression(callee) ||
            !ts.isIdentifier(callee.expression) ||
            !this.isLikelyTypeName(callee.name.text)) {
            const none = [];
            return none;
        }
        const resolved = this.resolveUsageTypePaths(callee);
        const paths = resolved.via === 'binding' || resolved.via === 'annotation'
            ? resolved.paths
            : [];
        return paths;
    }
    /**
     * The `const x = <call>` (await and parentheses transparent) the call
     * initializes directly — not a call nested inside the initializer
     */
    bindDirectResult(call, typePath) {
        let current = call;
        while (ts.isAwaitExpression(current.parent) || ts.isParenthesizedExpression(current.parent)) {
            current = current.parent;
        }
        const holder = current.parent;
        if (ts.isVariableDeclaration(holder) && holder.initializer === current && ts.isIdentifier(holder.name)) {
            this.variableToTypeMap.set(holder.name.text, typePath);
            this.trackFileGraphBinding(holder.name.text, typePath);
        }
    }
    /**
             * Check if a name looks like a type (starts with uppercase)
             */
    isLikelyTypeName(name) {
        return name[0] >= 'A' && name[0] <= 'Z';
    }
    /**
             * Resolve a constructor parameter type, expanding inline object literals
             * and type aliases where possible.
             */
    resolveConstructorParamType(typeNode) {
        if (!typeNode)
            return undefined;
        // Direct inline type literal: { prop: type }
        if (ts.isTypeLiteralNode(typeNode)) {
            const props = [];
            for (const member of typeNode.members) {
                if (ts.isPropertySignature(member) && ts.isIdentifier(member.name)) {
                    const propName = member.name.text;
                    const optional = member.questionToken ? '?' : '';
                    const type = this.inferType(member.type);
                    props.push(`${propName}${optional}: ${type}`);
                }
            }
            return `{ ${props.join('; ')} }`;
        }
        // Type reference: usage, UserData, etc. - resolve import-aware and
        // expand the referenced declaration where possible (F10)
        if (ts.isTypeReferenceNode(typeNode) && ts.isIdentifier(typeNode.typeName)) {
            const typeName = typeNode.typeName.text;
            const decl = this.resolveReferencedTypeDeclaration(typeName, this.currentReferencedTypeFile);
            if (decl) {
                const expanded = this.expandReferencedTypeDeclaration(decl);
                if (expanded)
                    return expanded;
            }
            // mnemonica graph types keep their simple name — the generator
            // upgrades them to full-path instance type names. Resolution is
            // path-aware (hard-fail law): ambiguity between real graph types
            // records a fatal error instead of silently picking one.
            const graphResult = this.resolveGraphTypeName(typeName);
            if (graphResult.status === 'unique') {
                const simpleResult = typeName;
                return simpleResult;
            }
            if (graphResult.status === 'ambiguous') {
                this.recordGraphReferenceError(typeName, typeNode, graphResult);
                const unknownGraphResult = 'unknown';
                return unknownGraphResult;
            }
            // If not an object type alias, return the type name with args
            if (typeNode.typeArguments && typeNode.typeArguments.length > 0) {
                if (KNOWN_GLOBAL_TYPES.has(typeName)) {
                    const args = typeNode.typeArguments.map(arg => this.inferType(arg));
                    return `${typeName}<${args.join(', ')}>`;
                }
                // generic reference to a non-global, non-graph type cannot be
                // emitted bare into the generated file
                this.recordPlainTypeReferenceSite(typeName, typeNode);
                const unknownGenericResult = 'unknown';
                return unknownGenericResult;
            }
            const fallbackResult = this.unresolvedTypeReferenceFallback(typeName, typeNode);
            return fallbackResult;
        }
        return undefined;
    }
    /**
             * Extract constructor parameters from a class-like node.
             */
    extractClassConstructorParams(classLike) {
        const params = [];
        for (const member of classLike.members) {
            if (!ts.isConstructorDeclaration(member)) {
                continue;
            }
            for (const param of member.parameters) {
                if (!param.name || !ts.isIdentifier(param.name))
                    continue;
                if (!param.type)
                    continue;
                const paramName = param.name.text;
                const expandedType = this.resolveConstructorParamType(param.type) || this.inferType(param.type);
                params.push({
                    name: paramName,
                    type: expandedType,
                    optional: !!param.questionToken || !!param.initializer,
                    // rest marker for the definitions.json args contract
                    ...(param.dotDotDotToken ? { kind: 'rest' } : {})
                });
            }
            // Only process first constructor
            break;
        }
        return params;
    }
    /**
             * Extract constructor parameters from define() call
             * This is used for TypeRegistry constructor signatures
             * Preserves parameter names and expands object types to their structure
             */
    extractConstructorParams(call) {
        const constructorExpr = this.extractConstructorExpression(call);
        if (!constructorExpr) {
            const fallbackParams = [{
                    name: 'args',
                    type: 'unknown[]',
                    optional: false,
                    kind: 'rest',
                }];
            return fallbackParams;
        }
        const referencingFile = this.currentReferencedTypeFile;
        this.currentReferencedTypeFile = nodePath.resolve(constructorExpr.getSourceFile().fileName);
        try {
            const result = this.extractConstructorParamsFromConstructor(constructorExpr);
            return result;
        }
        finally {
            this.currentReferencedTypeFile = referencingFile;
        }
    }
    /**
             * Extract constructor parameters from a constructor expression.
             */
    extractConstructorParamsFromConstructor(constructorExpr) {
        const params = [];
        // Handle function expression or arrow function
        if (ts.isFunctionExpression(constructorExpr) || ts.isArrowFunction(constructorExpr) ||
            ts.isFunctionDeclaration(constructorExpr)) {
            // Look for constructor parameters (second param after `this`)
            // Patterns: function(this: Type, data: { ... }) or (this: Type, data: { ... }) =>
            for (let i = 0; i < constructorExpr.parameters.length; i++) {
                const param = constructorExpr.parameters[i];
                if (!param.type)
                    continue;
                // Skip `this` parameter (first param)
                if (i === 0 &&
                    param.name.kind === ts.SyntaxKind.Identifier &&
                    param.name.text === 'this') {
                    continue;
                }
                // Get parameter name and expand its type
                const paramName = ts.isIdentifier(param.name) ? param.name.text : 'arg';
                const expandedType = this.resolveConstructorParamType(param.type) || this.inferType(param.type);
                params.push({
                    name: paramName,
                    type: expandedType,
                    optional: !!param.questionToken || !!param.initializer,
                    // rest marker for the definitions.json args contract
                    ...(param.dotDotDotToken ? { kind: 'rest' } : {})
                });
            }
        }
        // Handle class expression - check constructor method
        if (ts.isClassExpression(constructorExpr) || ts.isClassDeclaration(constructorExpr)) {
            const classParams = this.extractClassConstructorParams(constructorExpr);
            for (const param of classParams) {
                params.push(param);
            }
        }
        return params;
    }
    /**
     * Collect framework instrumentation points. Purely syntactic: heritage
     * clauses, decorator application sites, provider-token object literals
     * and consumer.apply().forRoutes() wiring. The vocabulary comes from
     * plugins; identifier text is matched as-is — no import resolution,
     * the type checker stays unused.
     */
    collectInstrumentation(node, sourceFile) {
        if (ts.isClassDeclaration(node) && node.name) {
            this.collectInstrumentationClass(node, sourceFile);
        }
        if (ts.isDecorator(node)) {
            this.collectInstrumentationDecorator(node, sourceFile);
        }
        if (ts.isObjectLiteralExpression(node)) {
            this.collectInstrumentationProvider(node, sourceFile);
        }
        if (ts.isCallExpression(node)) {
            this.collectInstrumentationMiddleware(node, sourceFile);
        }
    }
    /**
     * Record a named class declaration for instrumentation site resolution
     * and detect heritage-based kinds (`implements <plugin interface>`)
     */
    collectInstrumentationClass(node, sourceFile) {
        if (!node.name) {
            return;
        }
        const className = node.name.text;
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.name.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        // First line of the declaration, like EDS `code` snippets
        const code = node.getText(sourceFile).split('\n')[0].slice(0, 100);
        let kind;
        if (node.heritageClauses) {
            for (const clause of node.heritageClauses) {
                if (clause.token !== ts.SyntaxKind.ImplementsKeyword) {
                    continue;
                }
                for (const type of clause.types) {
                    if (!ts.isIdentifier(type.expression)) {
                        continue;
                    }
                    const matched = this.instrumentationVocabulary.interfaces[type.expression.text];
                    if (matched) {
                        kind = matched;
                    }
                }
            }
        }
        const decl = {
            location,
            code,
        };
        if (kind) {
            decl.kind = kind;
        }
        this.instrumentationClassDecls.set(className, decl);
    }
    /**
     * Detect decorator application sites: plugin-listed decorators applied
     * with class arguments on a class or one of its methods. One site per
     * referenced class identifier.
     */
    collectInstrumentationDecorator(node, sourceFile) {
        const { expression } = node;
        if (!ts.isCallExpression(expression) || !ts.isIdentifier(expression.expression)) {
            return;
        }
        const kind = this.instrumentationVocabulary.useDecorators[expression.expression.text];
        if (!kind) {
            return;
        }
        // The decorator's parent is the decorated node: a controller class,
        // one of its methods, or one of its method parameters
        // (@Body(mvp.forType(Dto)) on a handler argument)
        const decorated = node.parent;
        let scope;
        let targets;
        if (ts.isClassDeclaration(decorated) && decorated.name) {
            scope = `controller:${decorated.name.text}`;
            targets = [decorated.name.text];
        }
        else if (ts.isMethodDeclaration(decorated) &&
            ts.isIdentifier(decorated.name) &&
            ts.isClassDeclaration(decorated.parent) &&
            decorated.parent.name) {
            const className = decorated.parent.name.text;
            scope = `method:${className}.${decorated.name.text}`;
            targets = [className];
        }
        else if (ts.isParameter(decorated)) {
            // Parameter decorators take the enclosing method's scope — the
            // attachment point is the handler, not the argument name; the
            // same method:Class.method form as method-level sites. Params of
            // constructors, functions, and unnameable hosts stay silent, the
            // same convention as other unresolvable decorator parents
            const host = decorated.parent;
            if (host &&
                ts.isMethodDeclaration(host) &&
                ts.isIdentifier(host.name) &&
                ts.isClassDeclaration(host.parent) &&
                host.parent.name) {
                const className = host.parent.name.text;
                scope = `method:${className}.${host.name.text}`;
                targets = [className];
            }
            else {
                return;
            }
        }
        else {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        for (const arg of expression.arguments) {
            // Class reference: @Register(Impl) or an inline instance:
            // @Register(new Impl({ ...options }))
            let className;
            // per-arg kind: factory-call args carry their own configured
            // kind, everything else takes the decorator's
            let argKind = kind;
            if (ts.isIdentifier(arg)) {
                className = arg.text;
            }
            else if (ts.isNewExpression(arg) && ts.isIdentifier(arg.expression)) {
                className = arg.expression.text;
            }
            else if (ts.isCallExpression(arg) && ts.isPropertyAccessExpression(arg.expression)) {
                // Pipe-factory shape: @UsePipes(mvp.forType(Dto)) — the
                // call's method name is plugin-listed, the target class sits
                // in the configured argument position (default 0)
                const factory = this.instrumentationVocabulary.decoratorArgFactories[arg.expression.name.text];
                if (factory) {
                    const targetArg = arg.arguments[factory.targetArg ?? 0];
                    if (targetArg && ts.isIdentifier(targetArg)) {
                        className = targetArg.text;
                        argKind = factory.kind;
                    }
                    // The plugin declares that this factory constructs its
                    // target on the caller's behalf: the call site is a
                    // construction like `new`, recorded as an instantiation
                    if (targetArg && factory.instantiation) {
                        this.recordFactoryConstruction(arg, targetArg, sourceFile);
                    }
                }
            }
            if (!className) {
                continue;
            }
            this.instrumentationSites.push({
                kind: argKind,
                className,
                location,
                code,
                scope,
                targets,
            });
        }
    }
    /**
     * A plugin-listed decorator-arg factory with `instantiation: true`
     * (`@Body(mvp.forType(Entity, Dto))`) constructs the type at its
     * target argument later, at runtime: record the factory call as that
     * type's `instantiation` usage and flow, the same as call/apply. A
     * target that resolves to no defined type records nothing.
     */
    recordFactoryConstruction(call, targetArg, sourceFile) {
        const constructedPath = this.resolveCtorArgTypePath(targetArg);
        if (!constructedPath) {
            return;
        }
        this.recordConstructionUsage(call, constructedPath, sourceFile, targetArg.getText(sourceFile));
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, call.getStart(sourceFile));
        this.addFlow(constructedPath, {
            location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
            kind: 'instantiation',
            code: call.getText(sourceFile).slice(0, 100),
            context: 'plugin factory construction',
        });
    }
    /**
     * Detect global registrations: object literals shaped like
     * `{ provide: <plugin-listed token>, useClass: X }`.
     * useExisting/useFactory without a useClass identifier are not
     * statically obvious — skipped rather than guessed.
     */
    collectInstrumentationProvider(node, sourceFile) {
        let kind;
        let useClassName;
        for (const prop of node.properties) {
            if (!ts.isPropertyAssignment(prop) ||
                !ts.isIdentifier(prop.name) ||
                !ts.isIdentifier(prop.initializer)) {
                continue;
            }
            if (prop.name.text === 'provide') {
                kind = this.instrumentationVocabulary.appTokens[prop.initializer.text];
            }
            if (prop.name.text === 'useClass') {
                useClassName = prop.initializer.text;
            }
        }
        if (!kind || !useClassName) {
            return;
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        this.instrumentationSites.push({
            kind,
            className: useClassName,
            location,
            code,
            scope: 'global',
            targets: [],
        });
    }
    /**
     * Detect middleware wiring: `consumer.apply(Mw1, Mw2).forRoutes(...)`
     * inside a class's configure() method. Targets come from forRoutes
     * arguments when statically readable (string routes or controller
     * identifiers), else []. Shape-based, so a plugin must opt in via
     * `middlewareWiring: true`.
     */
    collectInstrumentationMiddleware(node, sourceFile) {
        if (!this.instrumentationVocabulary.middlewareWiring) {
            return;
        }
        if (!ts.isPropertyAccessExpression(node.expression) ||
            node.expression.name.text !== 'forRoutes') {
            return;
        }
        const applyCall = node.expression.expression;
        if (!ts.isCallExpression(applyCall) ||
            !ts.isPropertyAccessExpression(applyCall.expression) ||
            applyCall.expression.name.text !== 'apply') {
            return;
        }
        if (!this.isInsideConfigureMethod(node)) {
            return;
        }
        const targets = [];
        for (const arg of node.arguments) {
            if (ts.isIdentifier(arg) || ts.isStringLiteral(arg)) {
                targets.push(arg.text);
            }
        }
        const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, applyCall.getStart(sourceFile));
        const location = `${sourceFile.fileName}:${line + 1}:${character + 1}`;
        const code = node.getText(sourceFile).slice(0, 100);
        for (const arg of applyCall.arguments) {
            if (!ts.isIdentifier(arg)) {
                continue;
            }
            this.instrumentationSites.push({
                kind: 'middleware',
                className: arg.text,
                location,
                code,
                scope: 'module',
                targets,
            });
        }
    }
    /**
     * Walk up the parent chain looking for an enclosing configure() method
     */
    isInsideConfigureMethod(node) {
        let current = node.parent;
        while (current) {
            if (ts.isMethodDeclaration(current) &&
                ts.isIdentifier(current.name) &&
                current.name.text === 'configure') {
                return true;
            }
            current = current.parent;
        }
        return false;
    }
}
exports.MnemonicaAnalyzer = MnemonicaAnalyzer;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYW5hbHl6ZXIuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvYW5hbHl6ZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFFYiwrQ0FBaUM7QUFDakMsK0NBQWlDO0FBT2pDLG1DQUVpQjtBQUNqQix1Q0FFbUI7QUFxRm5COzs7R0FHRztBQUNILE1BQU0sa0JBQWtCLEdBQUcsSUFBSSxHQUFHLENBQUM7SUFDbEMsTUFBTSxFQUFFLFFBQVEsRUFBRSxPQUFPLEVBQUUsV0FBVyxFQUFFLFlBQVksRUFBRSxnQkFBZ0I7SUFDdEUsYUFBYSxFQUFFLFdBQVcsRUFBRSxVQUFVLEVBQUUsZ0JBQWdCO0lBQ3hELEtBQUssRUFBRSxLQUFLLEVBQUUsU0FBUyxFQUFFLFNBQVMsRUFBRSxTQUFTLEVBQUUsc0JBQXNCO0lBQ3JFLFNBQVMsRUFBRSxPQUFPLEVBQUUsZUFBZSxFQUFFLFFBQVEsRUFBRSxTQUFTLEVBQUUsVUFBVTtJQUNwRSxVQUFVLEVBQUUsTUFBTSxFQUFFLE1BQU0sRUFBRSxTQUFTLEVBQUUsU0FBUyxFQUFFLGFBQWE7SUFDL0QsWUFBWSxFQUFFLGNBQWMsRUFBRSxZQUFZLEVBQUUsdUJBQXVCO0lBQ25FLFVBQVUsRUFBRSxtQkFBbUIsRUFBRSxtQkFBbUI7SUFDcEQsV0FBVyxFQUFFLFdBQVcsRUFBRSxZQUFZLEVBQUUsY0FBYztJQUN0RCxRQUFRLEVBQUUsUUFBUSxFQUFFLFNBQVMsRUFBRSxRQUFRLEVBQUUsUUFBUSxFQUFFLFFBQVEsRUFBRSxVQUFVO0lBQ3ZFLFVBQVUsRUFBRSxVQUFVLEVBQUUsV0FBVyxFQUFFLGVBQWUsRUFBRSxlQUFlO0lBQ3JFLGdCQUFnQixFQUFFLGtCQUFrQixFQUFFLHVCQUF1QjtJQUM3RCxhQUFhLEVBQUUsYUFBYSxFQUFFLG1CQUFtQixFQUFFLFVBQVU7SUFDN0QsV0FBVyxFQUFFLFlBQVksRUFBRSxtQkFB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QVM7WUFDVixDQUFDO1lBQ0QsSUFBSSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQztnQkFDOUIsSUFBSSxFQUFRLFlBQVk7Z0JBQ3hCLFNBQVMsRUFBRyxHQUFHLENBQUMsSUFBSTtnQkFDcEIsUUFBUTtnQkFDUixJQUFJO2dCQUNKLEtBQUssRUFBTyxRQUFRO2dCQUNwQixPQUFPO2FBQ1AsQ0FBQyxDQUFDO1FBQ0osQ0FBQztJQUNGLENBQUM7SUFFRDs7T0FFRztJQUNLLHVCQUF1QixDQUFFLElBQWE7UUFDN0MsSUFBSSxPQUFPLEdBQXdCLElBQUksQ0FBQyxNQUFNLENBQUM7UUFDL0MsT0FBTyxPQUFPLEVBQUUsQ0FBQztZQUNoQixJQUNDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxPQUFPLENBQUM7Z0JBQy9CLEVBQUUsQ0FBQyxZQUFZLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQztnQkFDN0IsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssV0FBVyxFQUNoQyxDQUFDO2dCQUNGLE9BQU8sSUFBSSxDQUFDO1lBQ2IsQ0FBQztZQUNELE9BQU8sR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDO1FBQzFCLENBQUM7UUFDRCxPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7Q0FDRDtBQTVzT0QsOENBNHNPQyIsInNvdXJjZXNDb250ZW50IjpbIid1c2Ugc3RyaWN0JztcblxuaW1wb3J0ICogYXMgbm9kZVBhdGggZnJvbSAncGF0aCc7XG5pbXBvcnQgKiBhcyB0cyBmcm9tICd0eXBlc2NyaXB0JztcbmltcG9ydCB7XG5cdFR5cGVOb2RlLCBQcm9wZXJ0eUluZm8sIEFuYWx5emVSZXN1bHQsIEFuYWx5emVFcnJvcixcblx0RGVmaW5pdGlvbkluZm8sIFVzYWdlSW5mbywgQ29uc3RydWN0b3JQYXJhbUluZm8sXG5cdEVEU0luZm8sIEZsb3dJbmZvLCBJbnN0cnVtZW50YXRpb25LaW5kLCBJbnN0cnVtZW50YXRpb25Qb2ludCxcblx0SW5zdHJ1bWVudGF0aW9uU2NvcGUsIFJlc29sdXRpb25FcnJvciwgQ29sbGVjdGlvbk1hbmlmZXN0RW50cnksIEJ1aWxkZXJWYWx1ZVxufSBmcm9tICcuL3R5cGVzJztcbmltcG9ydCB7XG5cdFR5cGVHcmFwaEltcGwsIHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UsIEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCBcbn0gZnJvbSAnLi9ncmFwaCc7XG5pbXBvcnQge1xuXHRJbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5LCBUYWN0aWNhUGx1Z2luLCBtZXJnZVRhY3RpY2FQbHVnaW5zXG59IGZyb20gJy4vcGx1Z2lucyc7XG5cbmludGVyZmFjZSBDb2xsZWN0aW9uSW5mbyB7XG5cdHZhcmlhYmxlTmFtZTogc3RyaW5nO1xuXHRzb3VyY2VGaWxlOiBzdHJpbmc7XG5cdHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZT86IHN0cmluZztcblx0LyoqIDEtYmFzZWQgcG9zaXRpb24gb2YgdGhlIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIHZhcmlhYmxlIGRlY2xhcmF0aW9uICovXG5cdGxpbmU6IG51bWJlcjtcblx0Y29sdW1uOiBudW1iZXI7XG59XG5cbmludGVyZmFjZSBCdWlsZGVyRXhwb3J0IHtcblx0bmFtZTogc3RyaW5nO1xuXHRzb3VyY2VGaWxlOiBzdHJpbmc7XG5cdGRlZmF1bHRJbXBvcnQ/OiBib29sZWFuO1xufVxuXG5pbnRlcmZhY2UgQnVpbGRlckNhbmRpZGF0ZSB7XG5cdG5hbWU6IHN0cmluZztcblx0c291cmNlRmlsZTogc3RyaW5nO1xuXHRraW5kOiAncmVnaXN0cnlPZicgfCAndHlwZW9mJztcblx0ZnVsbFBhdGg6IHN0cmluZztcblx0ZXhwb3J0czogQnVpbGRlckV4cG9ydFtdO1xuXHRleGNsdWRlZDogYm9vbGVhbjtcbn1cblxuLyoqXG4gKiBMb2NhdGlvbi9jb2RlIGNhcHR1cmVkIGF0IGEgY2xhc3MgZGVjbGFyYXRpb24sIHVzZWQgdG8gcmVzb2x2ZVxuICogaW5zdHJ1bWVudGF0aW9uIHJlZ2lzdHJhdGlvbiBzaXRlcyB0byB0aGUgZGVjbGFyZWQgY2xhc3NcbiAqL1xuaW50ZXJmYWNlIEluc3RydW1lbnRhdGlvbkNsYXNzRGVjbCB7XG5cdGtpbmQ/OiBJbnN0cnVtZW50YXRpb25LaW5kO1xuXHRsb2NhdGlvbjogc3RyaW5nO1xuXHRjb2RlOiBzdHJpbmc7XG59XG5cbi8qKlxuICogUmF3IHJlZ2lzdHJhdGlvbiBzaXRlIChkZWNvcmF0b3IsIEFQUF8qIHByb3ZpZGVyLCBjb25zdW1lci5hcHBseSkuXG4gKiBMb2NhdGlvbi9jb2RlIGFyZSB0aGUgc2l0ZSdzIG93bjsgZ2V0SW5zdHJ1bWVudGF0aW9uUG9pbnRzKCkgcmV3cml0ZXNcbiAqIHRoZW0gdG8gdGhlIGNsYXNzIGRlY2xhcmF0aW9uIHdoZW4gdGhlIGNsYXNzIGlzIGRlY2xhcmVkIGluLXByb2plY3QuXG4gKi9cbmludGVyZmFjZSBJbnN0cnVtZW50YXRpb25TaXRlIHtcblx0a2luZDogSW5zdHJ1bWVudGF0aW9uS2luZDtcblx0Y2xhc3NOYW1lOiBzdHJpbmc7XG5cdGxvY2F0aW9uOiBzdHJpbmc7XG5cdGNvZGU6IHN0cmluZztcblx0c2NvcGU6IEluc3RydW1lbnRhdGlvblNjb3BlO1xuXHR0YXJnZXRzOiBzdHJpbmdbXTtcbn1cblxuLyoqXG4gKiBBIG5hbWVkIHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbiAodHlwZSBhbGlhcywgY2xhc3MsIG9yIGludGVyZmFjZSlcbiAqIHJlY29yZGVkIHBlciBmaWxlLCBzbyByZWZlcmVuY2VzIGNhbiBiZSByZXNvbHZlZCB0aHJvdWdoIHRoZSBpbXBvcnRpbmdcbiAqIGZpbGUncyBvd24gaW1wb3J0cyBpbnN0ZWFkIG9mIGEgcHJvZ3JhbS13aWRlIGxhc3Qtd2lucyBuYW1lIG1hcCAoRjEwKS5cbiAqL1xuaW50ZXJmYWNlIFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24ge1xuXHRraW5kOiAnYWxpYXMnIHwgJ2NsYXNzJyB8ICdpbnRlcmZhY2UnO1xuXHRub2RlOiB0cy5UeXBlQWxpYXNEZWNsYXJhdGlvbiB8IHRzLkNsYXNzRGVjbGFyYXRpb24gfCB0cy5JbnRlcmZhY2VEZWNsYXJhdGlvbjtcblx0LyoqIGZpbGUgdGhhdCBkZWNsYXJlcyB0aGUgdHlwZSDigJQgbmVzdGVkIHJlZmVyZW5jZXMgcmVzb2x2ZSBhZ2FpbnN0IGl0ICovXG5cdGZpbGU6IHN0cmluZztcbn1cblxuLyoqXG4gKiBPbmUgaW1wb3J0IGJpbmRpbmcgb2YgYSByZWZlcmVuY2VkIHR5cGU6IHRoZSBsb2NhbCBuYW1lIHVuZGVyIHdoaWNoIHRoZVxuICogZmlsZSBrbm93cyBpdCwgdGhlIG9yaWdpbmFsIGV4cG9ydGVkIG5hbWUgaW4gdGhlIHNvdXJjZSBtb2R1bGUsIGFuZCB0aGVcbiAqIHNwZWNpZmllciBpdCBjYW1lIGZyb20uXG4gKi9cbmludGVyZmFjZSBSZWZlcmVuY2VkVHlwZUltcG9ydCB7XG5cdG9yaWdpbmFsTmFtZTogc3RyaW5nO1xuXHRzcGVjaWZpZXI6IHN0cmluZztcblx0aXNOYW1lc3BhY2U6IGJvb2xlYW47XG59XG5cbi8qKlxuICogUmVzdWx0IG9mIHJlc29sdmluZyBvbmUgbW9kdWxlIHNwZWNpZmllciBmcm9tIG9uZSBjb250YWluaW5nIGZpbGUuXG4gKi9cbmludGVyZmFjZSBSZWZlcmVuY2VkVHlwZVJlc29sdXRpb24ge1xuXHRyZXNvbHZlZFBhdGg6IHN0cmluZztcblx0aXNFeHRlcm5hbDogYm9vbGVhbjtcbn1cblxudHlwZSBDb25zdHJ1Y3RvckhhbmRsZXIgPSB0cy5FeHByZXNzaW9uIHwgdHMuRnVuY3Rpb25EZWNsYXJhdGlvbiB8IHRzLkNsYXNzRGVjbGFyYXRpb247XG50eXBlIEZ1bmN0aW9uQ29uc3RydWN0b3JIYW5kbGVyID0gdHMuRnVuY3Rpb25FeHByZXNzaW9uIHwgdHMuQXJyb3dGdW5jdGlvbiB8IHRzLkZ1bmN0aW9uRGVjbGFyYXRpb247XG50eXBlIENsYXNzQ29uc3RydWN0b3JIYW5kbGVyID0gdHMuQ2xhc3NFeHByZXNzaW9uIHwgdHMuQ2xhc3NEZWNsYXJhdGlvbjtcblxuLyoqXG4gKiBHbG9iYWwvYnVpbHRpbiB0eXBlIG5hbWVzIHRoYXQgYXJlIHNhZmUgdG8gZW1pdCBiYXJlIGludG8gZ2VuZXJhdGVkIGZpbGVzXG4gKiDigJQgdGhleSByZXNvbHZlIGluIGFueSBUeXBlU2NyaXB0IGNvbXBpbGF0aW9uIHdpdGhvdXQgYW4gaW1wb3J0LlxuICovXG5jb25zdCBLTk9XTl9HTE9CQUxfVFlQRVMgPSBuZXcgU2V0KFtcblx0J0RhdGUnLCAnUmVnRXhwJywgJ0Vycm9yJywgJ0V2YWxFcnJvcicsICdSYW5nZUVycm9yJywgJ1JlZmVyZW5jZUVycm9yJyxcblx0J1N5bnRheEVycm9yJywgJ1R5cGVFcnJvcicsICdVUklFcnJvcicsICdBZ2dyZWdhdGVFcnJvcicsXG5cdCdNYXAnLCAnU2V0JywgJ1dlYWtNYXAnLCAnV2Vha1NldCcsICdXZWFrUmVmJywgJ0ZpbmFsaXphdGlvblJlZ2lzdHJ5Jyxcblx0J1Byb21pc2UnLCAnQXJyYXknLCAnUmVhZG9ubHlBcnJheScsICdSZWNvcmQnLCAnUGFydGlhbCcsICdSZXF1aXJlZCcsXG5cdCdSZWFkb25seScsICdQaWNrJywgJ09taXQnLCAnRXhjbHVkZScsICdFeHRyYWN0JywgJ05vbk51bGxhYmxlJyxcblx0J1JldHVyblR5cGUnLCAnSW5zdGFuY2VUeXBlJywgJ1BhcmFtZXRlcnMnLCAnQ29uc3RydWN0b3JQYXJhbWV0ZXJzJyxcblx0J1RoaXNUeXBlJywgJ1RoaXNQYXJhbWV0ZXJUeXBlJywgJ09taXRUaGlzUGFyYW1ldGVyJyxcblx0J1VwcGVyY2FzZScsICdMb3dlcmNhc2UnLCAnQ2FwaXRhbGl6ZScsICdVbmNhcGl0YWxpemUnLFxuXHQnU3RyaW5nJywgJ051bWJlcicsICdCb29sZWFuJywgJ1N5bWJvbCcsICdCaWdJbnQnLCAnT2JqZWN0JywgJ0Z1bmN0aW9uJyxcblx0J0l0ZXJhYmxlJywgJ0l0ZXJhdG9yJywgJ0dlbmVyYXRvcicsICdBc3luY0l0ZXJhYmxlJywgJ0FzeW5jSXRlcmF0b3InLFxuXHQnQXN5bmNHZW5lcmF0b3InLCAnSXRlcmFibGVJdGVyYXRvcicsICdBc3luY0l0ZXJhYmxlSXRlcmF0b3InLFxuXHQnUHJvcGVydHlLZXknLCAnQXJyYXlCdWZmZXInLCAnU2hhcmVkQXJyYXlCdWZmZXInLCAnRGF0YVZpZXcnLFxuXHQnSW50OEFycmF5JywgJ1VpbnQ4QXJyYXknLCAnVWludDhDbGFtcGVkQXJyYXknLCAnSW50MTZBcnJheScsXG5cdCdVaW50MTZBcnJheScsICdJbnQzMkFycmF5JywgJ1VpbnQzMkFycmF5JywgJ0Zsb2F0MzJBcnJheScsXG5cdCdGbG9hdDY0QXJyYXknLCAnQmlnSW50NjRBcnJheScsICdCaWdVaW50NjRBcnJheScsICdJbnRsJ1xuXSk7XG5cbi8vIEdlbmVyaWMgZ2xvYmFscyB3aG9zZSBiYXJlIGVtaXNzaW9uIHdvdWxkIGJlIGludmFsaWQgVFMgKFRTMjMxNCk6XG4vLyBgbmV3IE1hcCgpYCBjYXJyaWVzIG5vIHR5cGUgYXJndW1lbnRzLCBzbyB0aGUgZmllbGQgdHlwZSBmaWxscyB0aGVtXG4vLyB3aXRoIHVua25vd24uIEtleXMgbXVzdCBhbHNvIGJlIG1lbWJlcnMgb2YgS05PV05fR0xPQkFMX1RZUEVTLlxuY29uc3QgR0VORVJJQ19HTE9CQUxfREVGQVVMVF9BUkdTID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oW1xuXHRbICdNYXAnLCAnTWFwPHVua25vd24sIHVua25vd24+JyBdLFxuXHRbICdXZWFrTWFwJywgJ1dlYWtNYXA8b2JqZWN0LCB1bmtub3duPicgXSxcblx0WyAnU2V0JywgJ1NldDx1bmtub3duPicgXSxcblx0WyAnV2Vha1NldCcsICdXZWFrU2V0PG9iamVjdD4nIF0sXG5cdFsgJ1dlYWtSZWYnLCAnV2Vha1JlZjxvYmplY3Q+JyBdLFxuXHRbICdGaW5hbGl6YXRpb25SZWdpc3RyeScsICdGaW5hbGl6YXRpb25SZWdpc3RyeTx1bmtub3duPicgXSxcblx0WyAnUHJvbWlzZScsICdQcm9taXNlPHVua25vd24+JyBdLFxuXHRbICdBcnJheScsICdBcnJheTx1bmtub3duPicgXSxcblx0WyAnUmVhZG9ubHlBcnJheScsICdSZWFkb25seUFycmF5PHVua25vd24+JyBdXG5dKTtcblxuLy8gQm91bmQgZm9yIGNoYXNpbmcgcmUtZXhwb3J0IGJhcnJlbHMgKGV4cG9ydCB7IFggfSBmcm9tICfigKYnLCBleHBvcnQgKiBmcm9tICfigKYnKVxuY29uc3QgTUFYX1JFRVhQT1JUX0NIQVNFX0RFUFRIID0gNTtcbi8vIEJvdW5kIGZvciB3YWxraW5nIGNsYXNzL2ludGVyZmFjZSBleHRlbmRzIGNoYWlucyBkdXJpbmcgcmVmZXJlbmNlZC10eXBlXG4vLyBleHBhbnNpb24gKGluaGVyaXRlZCBtZW1iZXJzIG1lcmdlIGludG8gdGhlIGV4cGFuZGVkIGZpZWxkcylcbmNvbnN0IE1BWF9IRVJJVEFHRV9ERVBUSCA9IDg7XG4vLyBCb3VuZCBmb3IgcmVhZGluZyBhIHJlY2VpdmVyJ3MgZGVjbGFyZWQgdHlwZSBiYWNrIHRvIHRoZSBnZW5lcmF0ZWQgdHlwZXNcbi8vIGl0IG5hbWVzIChhbGlhc2VzLCB1bmlvbnMsIGludGVyc2VjdGlvbnMsIGludGVyZmFjZSBleHRlbmRzKVxuY29uc3QgTUFYX0FOTk9UQVRJT05fT1dORVJfREVQVEggPSA4O1xuXG4vKipcbiAqIEV2ZXJ5IHR5cGUgYSBgcmVjZWl2ZXIuU3ViYCBhY2Nlc3MgY2FuIGRlbm90ZSwgYW5kIGhvdyBpdCB3YXMgZm91bmQ6XG4gKiBgZXhhY3RgICh0aGUgZG90dGVkIGNoYWluIGlzIGEgdHlwZSBwYXRoKSwgYGJpbmRpbmdgICh0aGUgcmVjZWl2ZXInc1xuICogdmFsdWUgYmluZGluZyksIGBhbm5vdGF0aW9uYCAodGhlIHJlY2VpdmVyJ3MgZGVjbGFyZWQgdHlwZSksIGBuYW1lYFxuICogKG5hbWVzYWtlcyBieSB0aGUgbGFzdCBzZWdtZW50IOKAlCB0aGUgcmVjZWl2ZXIgaXRzZWxmIGlzIHVua25vd24pLlxuICovXG5pbnRlcmZhY2UgVXNhZ2VUeXBlUGF0aHMge1xuXHRwYXRoczogc3RyaW5nW107XG5cdHZpYTogJ2V4YWN0JyB8ICdiaW5kaW5nJyB8ICdhbm5vdGF0aW9uJyB8ICduYW1lJztcbn1cblxuLyoqXG4gKiBBU1QgQW5hbHl6ZXIgZm9yIGZpbmRpbmcgTW5lbW9uaWNhIGRlZmluZSgpIGFuZCBkZWNvcmF0ZSgpIGNhbGxzXG4gKlxuICogRnJhbWV3b3JrLWJsaW5kIGJ5IGNvbnN0cnVjdGlvbjogaW5zdHJ1bWVudGF0aW9uIGRldGVjdGlvbiB2b2NhYnVsYXJ5XG4gKiAoaW50ZXJmYWNlIG5hbWVzLCBkZWNvcmF0b3IgbmFtZXMsIHByb3ZpZGVyIHRva2VucywgbWlkZGxld2FyZSB3aXJpbmcpXG4gKiBjb21lcyBlbnRpcmVseSBmcm9tIHBsdWdpbnMg4oCUIHdpdGggbm9uZSBsb2FkZWQsIHplcm8gcG9pbnRzIGFyZSBjb2xsZWN0ZWQuXG4gKi9cbmV4cG9ydCBjbGFzcyBNbmVtb25pY2FBbmFseXplciB7XG5cdHByaXZhdGUgZXJyb3JzOiBBbmFseXplRXJyb3JbXSA9IFtdO1xuXHRwcml2YXRlIGdyYXBoID0gbmV3IFR5cGVHcmFwaEltcGwoKTtcblx0cHJpdmF0ZSBkZWZpbml0aW9ucyA9IG5ldyBNYXA8c3RyaW5nLCBEZWZpbml0aW9uSW5mbz4oKTtcblx0cHJpdmF0ZSB1c2FnZXMgPSBuZXcgTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+KCk7XG5cdHByaXZhdGUgZWRzVXNhZ2VzID0gbmV3IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4oKTtcblx0cHJpdmF0ZSBmbG93VXNhZ2VzID0gbmV3IE1hcDxzdHJpbmcsIEZsb3dJbmZvW10+KCk7XG5cdC8vIEVuY2xvc2luZyBtbmVtb25pY2Egc2NvcGUgZm9yIEVEUyBrZXlpbmc6IGRlZmluZSgpL2xhenkoKSBjYWxsIG5vZGVcblx0Ly8gb3IgQGRlY29yYXRlKCktZWQgY2xhc3MgZGVjbGFyYXRpb24gLT4gZnVsbFBhdGggb2YgdGhlIHR5cGUgaXQgb3ducy5cblx0Ly8gUG9wdWxhdGVkIG9uIHRoZSBkZWZpbml0aW9ucyBwYXNzOyBBU1Qgbm9kZXMgcGVyc2lzdCBhY3Jvc3MgcGFzc2VzLFxuXHQvLyBzbyBlbnRyaWVzIHN0YXkgdmFsaWQgYWZ0ZXIgcmVzZXRVc2FnZXMoKS5cblx0cHJpdmF0ZSBlZHNTY29wZUJ5Tm9kZSA9IG5ldyBNYXA8dHMuTm9kZSwgc3RyaW5nPigpO1xuXHQvLyBTYW1lLWZpbGUgZnVuY3Rpb24gYmluZGluZ3MgKGBmaWxlTmFtZSNuYW1lYCAtPiBmdW5jdGlvbiBub2RlKSBmb3Jcblx0Ly8gcmVzb2x2aW5nIHdyYXAoZm4pIGFyZ3VtZW50cyBzeW50YWN0aWNhbGx5IOKAlCB0aGUgY2hlY2tlciBzdGF5cyB1bnVzZWRcblx0cHJpdmF0ZSBmdW5jdGlvbkJpbmRpbmdzID0gbmV3IE1hcDxzdHJpbmcsIHRzLkZ1bmN0aW9uTGlrZURlY2xhcmF0aW9uPigpO1xuXHQvLyBDb25zdHJ1Y3RvciB2YWx1ZXMgYnkgZGVjbGFyaW5nIGZpbGUgYW5kIGV4cG9ydGVkL2xvY2FsIG5hbWUuIFJlc29sdXRpb25cblx0Ly8gdXNlcyB0aGUgc2FtZSBpbXBvcnQgYW5kIHJlLWV4cG9ydCB3aXJpbmcgYXMgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9ucy5cblx0cHJpdmF0ZSBjb25zdHJ1Y3RvckJpbmRpbmdzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIENvbnN0cnVjdG9ySGFuZGxlcj4+KCk7XG5cdC8vIHdyYXAgY2FsbCBub2RlIC0+IGxvY2F0aW9uIG9mIHRoZSBlbmNsb3Npbmcgd3JhcCBzaXRlIChwbHVzIHRoYXRcblx0Ly8gc2l0ZSdzIHNjb3BlIGF0dHJpYnV0aW9uKSwgc28gbmVzdGVkIHdyYXAoKSBjYWxscyBpbnNpZGUgYSB3cmFwcGVkXG5cdC8vIGJvZHkgY2FycnkgdGhlIGB2aWFgIGxpbmsg4oCUIGFuZCBpbmhlcml0IHRoZSBzY29wZSB3aGVuIHRoZXkgaGF2ZVxuXHQvLyBub25lIG9mIHRoZWlyIG93blxuXHRwcml2YXRlIG5lc3RlZFdyYXBWaWEgPSBuZXcgTWFwPHRzLk5vZGUsIHsgdmlhOiBzdHJpbmc7IHNjb3BlPzogc3RyaW5nIH0+KCk7XG5cdC8vIHdyYXAgY2FsbCBub2RlIC0+IGl0cyBjb2xsZWN0ZWQgZW50cnksIHNvIGEgbGV4aWNhbGx5IG5lc3RlZCB3cmFwXG5cdC8vICh2aXNpdGVkIEJFRk9SRSB0aGUgb3V0ZXIgd3JhcCBjYWxsLCBwZXIgc291cmNlIG9yZGVyKSBnZXRzIGl0c1xuXHQvLyBgdmlhYCBiYWNrLXBhdGNoZWQgd2hlbiB0aGUgb3V0ZXIgYm9keSBpcyBhbmFseXNlZFxuXHRwcml2YXRlIHdyYXBFbnRyeUJ5Tm9kZSA9IG5ldyBNYXA8dHMuTm9kZSwgRURTSW5mbz4oKTtcblx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHM6IHZhcmlhYmxlTmFtZSAtPiBmdWxsUGF0aCBvZiB0aGUgdHlwZSBpdCBob2xkc1xuXHRwcml2YXRlIHZhcmlhYmxlVG9UeXBlTWFwID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0Ly8gRXhwb3J0ZWQgYnVpbGRlciB2YWx1ZXMgYW5kIHRoZWlyIHRyYW5zaXRpdmUgc2VsZi1yZWZlcmVuY2UgZXhjbHVzaW9ucy5cblx0cHJpdmF0ZSBidWlsZGVyQ2FuZGlkYXRlczogQnVpbGRlckNhbmRpZGF0ZVtdID0gW107XG5cdHByaXZhdGUgZXhjbHVkZWRUeXBlUGF0aHMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0Ly8gVHlwZSBwYXRocyBkZWZpbmVkIG9uIGEgY2hhaW4gdGhhdCBzdGFydHMgYXQgdGhlIGZyZWUgZGVmaW5lKCkgb3Jcblx0Ly8gbG9va3VwKCk6IHN1Y2ggYSBjaGFpbiBjYXJyaWVzIHRoZSBnbG9iYWwgVHlwZVJlZ2lzdHJ5IGl0c2VsZiwgc28gaXRzXG5cdC8vIGV4cG9ydGVkIHZhbHVlcyBlbnRlciB0aGUgcmVnaXN0cnkgYXMgYHR5cGVvZiBYYCwgbmV2ZXIgdGhyb3VnaFxuXHQvLyBSZWdpc3RyeU9mIChUeXBlUmVnaXN0cnkgd291bGQgYmUgaXRzIG93biBiYXNlOiBUUzI0NTYvVFMyMzEwKS5cblx0Ly8gU3RpY2t5IGFjcm9zcyBwYXNzZXMsIGxpa2UgZXhjbHVkZWRUeXBlUGF0aHNcblx0cHJpdmF0ZSBmcmVlQ2hhaW5UeXBlUGF0aHMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0cHJpdmF0ZSBnZW5lcmF0ZWRUeXBlSW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBTZXQ8c3RyaW5nPj4oKTtcblx0Ly8gQWJzb2x1dGUgZGlyZWN0b3JpZXMgaG9sZGluZyB0aGUgZ2VuZXJhdGVkIG91dHB1dDsgYW4gaW1wb3J0IHJlc29sdmluZ1xuXHQvLyBpbnRvIG9uZSBvZiB0aGVtIChyZWxhdGl2ZSBvciB0aHJvdWdoIHRzY29uZmlnIGBwYXRoc2ApIGlzIGdlbmVyYXRlZFxuXHRwcml2YXRlIGdlbmVyYXRlZE91dHB1dERpcnM6IHN0cmluZ1tdID0gW107XG5cdC8vIGAke2NvbnRhaW5pbmdGaWxlfTo6JHtzcGVjaWZpZXJ9YCAtPiBkb2VzIGl0IHJlc29sdmUgaW50byB0aGUgb3V0cHV0XG5cdHByaXZhdGUgZ2VuZXJhdGVkU3BlY2lmaWVyQ2FjaGUgPSBuZXcgTWFwPHN0cmluZywgYm9vbGVhbj4oKTtcblx0Ly8gVHJhY2sgbW5lbW9uaWNhIG1vZHVsZS1vYmplY3QgdmFyaWFibGVzIChlLmcuLCBpbXBvcnQgeyBtbmVtb25pY2EgfSBmcm9tICdtbmVtb25pY2EnOyBjb25zdCBtID0gbW5lbW9uaWNhKVxuXHRwcml2YXRlIG1vZHVsZU9iamVjdFZhcmlhYmxlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHQvLyBmaWxlIC0+IChsb2NhbCBuYW1lIC0+IGltcG9ydGVkIG5hbWUpIGZvciBuYW1lZCBpbXBvcnRzIGZyb21cblx0Ly8gJ21uZW1vbmljYScg4oCUIGltcG9ydC1hd2FyZW5lc3MgZm9yIHRoZSBjb25zdHJ1Y3Rpb24tZnVuY3Rpb25cblx0Ly8gcmVjb2duaXRpb24gKGNhbGwvYXBwbHkvYmluZCkgYW5kIHRoZSB1dGlscyBmb3JtcyAobWVyZ2UvZm9yayk6XG5cdC8vIHVzZXJsYW5kIGZ1bmN0aW9ucyB3aXRoIHRob3NlIG5hbWVzIG11c3QgbmV2ZXIgbWF0Y2hcblx0cHJpdmF0ZSBtbmVtb25pY2FOYW1lZEltcG9ydHMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgc3RyaW5nPj4oKTtcblx0Ly8gVHJhY2sgaW1wb3J0ZWQgYWxpYXNlcyBvZiBjcmVhdGVUeXBlc0NvbGxlY3Rpb24gKGUuZy4sIGltcG9ydCB7IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbiBhcyBjdGMgfSlcblx0cHJpdmF0ZSBjcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0Ly8gVHJhY2sgY3VzdG9tIGNvbGxlY3Rpb24gdmFyaWFibGVzOiB2YXJpYWJsZU5hbWUgLT4gY29sbGVjdGlvbklkXG5cdHByaXZhdGUgY29sbGVjdGlvblZhcmlhYmxlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdC8vIFRyYWNrIGN1c3RvbSBjb2xsZWN0aW9uIG1ldGFkYXRhIGZvciBPcHRpb24gQiByZWdpc3RyeSBlbWlzc2lvblxuXHRwcml2YXRlIGNvbGxlY3Rpb25JbmZvID0gbmV3IE1hcDxzdHJpbmcsIENvbGxlY3Rpb25JbmZvPigpO1xuXHRwcml2YXRlIGNvbGxlY3Rpb25Db3VudGVyID0gMDtcblx0Ly8gSW5zdHJ1bWVudGF0aW9uIGNvbGxlY3Rpb24gKHN5bnRhY3RpYyBvbmx5IOKAlCBubyB0eXBlIGNoZWNrZXIpOlxuXHQvLyBldmVyeSBuYW1lZCBjbGFzcyBkZWNsYXJhdGlvbiBieSBzaW1wbGUgbmFtZSwgZm9yIHJlc29sdmluZ1xuXHQvLyByZWdpc3RyYXRpb24gc2l0ZXMgdG8gZGVjbGFyYXRpb24gbG9jYXRpb25zIChiZXN0IGVmZm9ydCwgbGFzdCB3aW5zKVxuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMgPSBuZXcgTWFwPHN0cmluZywgSW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNsPigpO1xuXHQvLyBSZWdpc3RyYXRpb24gc2l0ZXM6IGRlY29yYXRvciBhcHBsaWNhdGlvbnMsIHByb3ZpZGVyLXRva2VuIG9iamVjdFxuXHQvLyBsaXRlcmFscywgY29uc3VtZXIuYXBwbHkoKSBtaWRkbGV3YXJlIHdpcmluZ1xuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvblNpdGVzOiBJbnN0cnVtZW50YXRpb25TaXRlW10gPSBbXTtcblx0Ly8gTWVyZ2VkIHBsdWdpbiB2b2NhYnVsYXJ5IGZvciBpbnN0cnVtZW50YXRpb24gZGV0ZWN0aW9uIChlbXB0eSB3aGVuXG5cdC8vIG5vIHBsdWdpbnMgd2VyZSBwYXNzZWQg4oCUIHRoZSBhbmFseXplciB0aGVuIGNvbGxlY3RzIG5vIHBvaW50cylcblx0cHJpdmF0ZSBpbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5OiBJbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5O1xuXHQvLyBSZWZlcmVuY2VkLXR5cGUgcmVzb2x1dGlvbiAoRjEwKTogcGVyLWZpbGUgZGVjbGFyYXRpb25zIGFuZCBpbXBvcnRzLlxuXHQvLyBBIHR5cGUgbmFtZSB1c2VkIGluIGZpbGUgWCByZXNvbHZlcyB0aHJvdWdoIFgncyBvd24gaW1wb3J0IHN0YXRlbWVudHNcblx0Ly8gZmlyc3QgKHJlbGF0aXZlICsgdHNjb25maWctcGF0aHMsIHZpYSB0cy5yZXNvbHZlTW9kdWxlTmFtZSksIHRoZW5cblx0Ly8gWCdzIGxvY2FsIGRlY2xhcmF0aW9ucywgdGhlbiDigJQgb25seSB3aGVuIG5vdGhpbmcgaW1wb3J0cyBvciBkZWNsYXJlc1xuXHQvLyB0aGUgbmFtZSDigJQgdGhlIHVuaXF1ZSBzYW1lLW5hbWVkIGRlY2xhcmF0aW9uIGFjcm9zcyBzY2FubmVkIGZpbGVzLlxuXHQvLyBHZW51aW5lIGFtYmlndWl0eSBvciBhbiB1bnJlc29sdmFibGUgcmVmZXJlbmNlIHlpZWxkcyBgdW5rbm93bmAsIG5ldmVyXG5cdC8vIGEgYmFyZSBlbWl0dGVkIG5hbWU6IGdlbmVyYXRlZCB0eXBlcy50cyBjYXJyaWVzIG5vIGltcG9ydHMgb2YgaXRzIG93bi5cblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZURlY2xzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24+PigpO1xuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlSW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZUltcG9ydD4+KCk7XG5cdC8vIGZpbGUgLT4gKGV4cG9ydGVkIG5hbWUgLT4gcmUtZXhwb3J0IHNwZWNpZmllcikgZm9yIGBleHBvcnQgeyBYIH0gZnJvbSAn4oCmJ2Bcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZVJlRXhwb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBmaWxlIC0+IHNwZWNpZmllcnMgb2YgYGV4cG9ydCAqIGZyb20gJ+KApidgXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmdbXT4oKTtcblx0Ly8gZmlsZSAtPiAoZXhwb3J0ZWQgbmFtZSAtPiBsb2NhbCBuYW1lKSBmb3IgYGV4cG9ydCB7IFggYXMgWSB9YFxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBmaWxlIC0+IChuYW1lc3BhY2UgbmFtZSAtPiBuYW1lc3BhY2UgZGVjbGFyYXRpb24pIOKAlCBtaWRkbGUgc2VnbWVudHNcblx0Ly8gb2YgcXVhbGlmaWVkIHJlZmVyZW5jZXMgKG1vZGVscy5Jbm5lci5DcmF0ZSkgZGVzY2VuZCB0aHJvdWdoIHRoZXNlXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHRzLk1vZHVsZURlY2xhcmF0aW9uPj4oKTtcblx0Ly8gZmlsZSAtPiAobmFtZXNwYWNlIG5hbWUgLT4gc3BlY2lmaWVyKSBmb3IgYGV4cG9ydCAqIGFzIG5zIGZyb20gJ+KApidgXG5cdC8vIGJhcnJlbHMg4oCUIGEgbmVzdGVkIG1vZHVsZSBuYW1lc3BhY2Ugb25lIHNlZ21lbnQgZGVlcFxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlU3RhcnMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgc3RyaW5nPj4oKTtcblx0Ly8gYCR7Y29udGFpbmluZ0ZpbGV9Ojoke3NwZWNpZmllcn1gIC0+IHJlc29sdXRpb24gKHVuZGVmaW5lZCA9IGZhaWxlZClcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZVJlc29sdXRpb25DYWNoZSA9IG5ldyBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZVJlc29sdXRpb24gfCB1bmRlZmluZWQ+KCk7XG5cdC8vIGZpbGUgLT4gKGNvbnN0IG5hbWUgLT4gYXJyYXkgbGl0ZXJhbCkgZm9yIGNvbnN0cyB3aXRoIGFycmF5LWxpdGVyYWxcblx0Ly8gaW5pdGlhbGl6ZXJzIChgYXMgY29uc3RgIC8gYHNhdGlzZmllc2AgdW53cmFwcGVkKSwgc28gYVxuXHQvLyBgdHlwZW9mIHN0YXR1c0xpc3RbbnVtYmVyXWAgZmllbGQgdHlwZSBleHBhbmRzIHRvIHRoZSBlbGVtZW50IGxpdGVyYWxcblx0Ly8gdW5pb24gaW5zdGVhZCBvZiBsZWFraW5nIGEgYmFyZSB1bnJlc29sdmFibGUgYHR5cGVvZmAgcXVlcnkgaW50byB0aGVcblx0Ly8gZ2VuZXJhdGVkIGZpbGUuIERlY2xhcmF0aW9ucyBwZXJzaXN0IGFjcm9zcyBwYXNzZXMg4oCUIGVudHJpZXMgc3RheVxuXHQvLyB2YWxpZCBhZnRlciByZXNldFVzYWdlcygpLCBzYW1lIGFzIHJlZmVyZW5jZWRUeXBlRGVjbHNcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24+PigpO1xuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlQ29tcGlsZXJPcHRpb25zOiB0cy5Db21waWxlck9wdGlvbnM7XG5cdC8vIEZpbGUgd2hvc2UgQVNUIGlzIGN1cnJlbnRseSBiZWluZyB2aXNpdGVkOyByZWZlcmVuY2VzIHJlc29sdmUgYWdhaW5zdCBpdFxuXHRwcml2YXRlIGN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSAnJztcblx0Ly8gQWxpYXMgbmFtZXMgY3VycmVudGx5IGJlaW5nIGV4cGFuZGVkIChjeWNsZSBndWFyZClcblx0cHJpdmF0ZSBleHBhbmRpbmdSZWZlcmVuY2VkQWxpYXNlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHQvLyBNbmVtb25pY2EtZ3JhcGggaWRlbnRpdHkgbGF3IChoYXJkIGZhaWwpOiBldmVyeSBkZWZpbmUoKS9sYXp5KCkvXG5cdC8vIEBkZWNvcmF0ZSgpIHNpdGUga2V5ZWQgYnkgaXRzIHJ1bnRpbWUgbmFtZXNwYWNlIChjb2xsZWN0aW9uIHJvb3RzOlxuXHQvLyBgPGNvbGxlY3Rpb24+Ojo8bmFtZT5gOyBzdWJ0eXBlczogYDxwYXJlbnRGdWxsUGF0aD4uPG5hbWU+YCkuIFR3b1xuXHQvLyBzaXRlcyBpbiBvbmUgbmFtZXNwYWNlIGFyZSBhIHNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZSDigJQgdGhlIHJ1bnRpbWVcblx0Ly8gdGhyb3dzIEFMUkVBRFlfREVDTEFSRUQg4oCUIGFuZCBtdXN0IGFib3J0IGdlbmVyYXRpb24uXG5cdHByaXZhdGUgZGVmaW5lU2l0ZXMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nW10+KCk7XG5cdC8vIE1uZW1vbmljYS1ncmFwaCByZWZlcmVuY2VzIHRoYXQgc3RheWVkIGFtYmlndW91cyBhZnRlciBwYXRoLWF3YXJlXG5cdC8vIHJlc29sdXRpb24gb3IgcmVzb2x2ZWQgdG8gbm90aGluZyAoaGFyZC1mYWlsIGNsYXNzIDIpXG5cdHByaXZhdGUgZ3JhcGhSZWZlcmVuY2VFcnJvcnM6IFJlc29sdXRpb25FcnJvcltdID0gW107XG5cdC8vIEd1YXJkcyBsb29rdXAoKS1wYXRoIHZhbGlkYXRpb24gc28gaXQgcnVucyBvbmNlIHBlciB1c2FnZXMgcGFzc1xuXHQvLyAoZ2V0UmVzb2x1dGlvbkVycm9ycyBtYXkgYmUgY2FsbGVkIHJlcGVhdGVkbHkpOyByZXNldFVzYWdlcyByZS1hcm1zIGl0XG5cdHByaXZhdGUgbG9va3VwUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHQvLyBMaXRlcmFsIGxvb2t1cCgpIGNhbGwgc2l0ZXMgd2l0aCB0aGVpciByZXNvbHZlZCBwYXRocy4gS2VwdCBhcGFydCBmcm9tXG5cdC8vIHRoZSB1c2FnZXMgbWFwIG9uIHB1cnBvc2U6IGFkZFVzYWdlIGRyb3BzIHBhdGhzIHRoZSBncmFwaCBkb2VzIG5vdFxuXHQvLyBrbm93ICh1c2FnZXMuanNvbiBpbmRleGVzIHJlZmVyZW5jZXMgdG8gS05PV04gdHlwZXMpLCBidXQgYW4gdW5rbm93blxuXHQvLyBsb29rdXAgcGF0aCBpcyBleGFjdGx5IHRoZSBoYXJkLWZhaWwgY2FzZSDigJQgdGhlIHJ1bnRpbWUgcmV0dXJuc1xuXHQvLyB1bmRlZmluZWQgdGhlcmUgYW5kIHRoZSBUeXBlRXJyb3IgYXJyaXZlcyBvbmUgbGluZSBsYXRlclxuXHRwcml2YXRlIGxvb2t1cFJlZmVyZW5jZXM6IHsgcGF0aDogc3RyaW5nOyBsb2NhdGlvbjogc3RyaW5nIH1bXSA9IFtdO1xuXHQvLyBHdWFyZHMgcGxhaW4tVFMgcmVmZXJlbmNlIHZhbGlkYXRpb24gc28gaXQgcnVucyBvbmNlIHBlciB1c2FnZXMgcGFzc1xuXHQvLyAoZ2V0UmVzb2x1dGlvbkVycm9ycyBtYXkgYmUgY2FsbGVkIHJlcGVhdGVkbHkpOyByZXNldFVzYWdlcyByZS1hcm1zIGl0XG5cdHByaXZhdGUgcGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHQvLyBQbGFpbi1UUyB0eXBlIHJlZmVyZW5jZSBzaXRlcyB3aG9zZSByZXNvbHV0aW9uIGZlbGwgdGhyb3VnaCBpbXBvcnRzLFxuXHQvLyBsb2NhbHMsIHRoZSBwcm9ncmFtLXdpZGUgc2NhbiwgYW5kIHRoZSBncmFwaCB0byBhIHNvZnQgYHVua25vd25gLlxuXHQvLyBWYWxpZGF0ZWQgbGF6aWx5IGZyb20gZ2V0UmVzb2x1dGlvbkVycm9ycyBhZ2FpbnN0IHRoZSBjb21wbGV0ZVxuXHQvLyBkZWNsYXJhdGlvbiBtYXA6IGEgbmFtZSBzZXZlcmFsIHByb2plY3Qtc291cmNlIGZpbGVzIGRlY2xhcmUg4oCUIHdpdGhcblx0Ly8gbm8gaW1wb3J0IGluIHRoZSByZWZlcmVuY2luZyBmaWxlIHRvIGFuY2hvciBpdCDigJQgaXMgdGhlIHBsYWluLVRTXG5cdC8vIGFtYmlndWl0eSBoYXJkLWZhaWwgY2xhc3MgKG9uZSB0aWVyIGJlbG93IHRoZSBncmFwaCBpZGVudGl0eSBsYXcpO1xuXHQvLyBhYnNlbmNlIChnaG9zdCBuYW1lcykgc3RheXMgc29mdC4gUmVjb3JkaW5nIGhhcHBlbnMgb24gZXZlcnkgcGFzcyxcblx0Ly8gdGhlIHZlcmRpY3Qgb25seSBoZXJlIOKAlCBwYXNzIDEgc2VlcyBhbiBpbmNvbXBsZXRlIGRlY2xhcmF0aW9uIG1hcCxcblx0Ly8gc28gb25seSB0aGUgdXNhZ2VzIHBhc3MgaXMgYXV0aG9yaXRhdGl2ZSAobWlycm9ycyBsb29rdXAgcmVmZXJlbmNlcylcblx0cHJpdmF0ZSBwbGFpblR5cGVSZWZlcmVuY2VzOiB7IG5hbWU6IHN0cmluZzsgbG9jYXRpb246IHN0cmluZzsgZmlsZTogc3RyaW5nIH1bXSA9IFtdO1xuXHQvLyBQZXItZmlsZSB0b3AtbGV2ZWwgdmFyaWFibGUgLT4gbW5lbW9uaWNhIGZ1bGxQYXRoIGJpbmRpbmdzICh2YWx1ZVxuXHQvLyBzY29wZSk6IGBjb25zdCBBZGRyZXNzID0gVXNlci5kZWZpbmUoJ0FkZHJlc3MnLCDigKYpYCBtYWtlcyBgQWRkcmVzc2Bcblx0Ly8gZGVub3RlIFVzZXIuQWRkcmVzcyB3aGVyZXZlciB0aGF0IGZpbGUncyByZWZlcmVuY2VzIGFyZSByZXNvbHZlZFxuXHRwcml2YXRlIGZpbGVHcmFwaEJpbmRpbmdzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHN0cmluZz4+KCk7XG5cdC8vIFRoZSBncmFwaCB0eXBlIHdob3NlIGNvbnN0cnVjdG9yIGlzIGN1cnJlbnRseSBiZWluZyBleHRyYWN0ZWQ7XG5cdC8vIGFuY2hvcnMgcmVsYXRpdmUtZmlyc3QgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb25cblx0cHJpdmF0ZSBjdXJyZW50R3JhcGhBbmNob3I6IFR5cGVOb2RlIHwgdW5kZWZpbmVkO1xuXHQvLyBkZWZpbmUoKS9sYXp5KCkgY2FsbHMgYWxyZWFkeSBleHRyYWN0ZWQgdGhpcyBwYXNzLiBUaGUgQ0xJIHJlLWFuYWx5emVzXG5cdC8vIGV2ZXJ5IGZpbGUgYWZ0ZXIgcmVzZXRVc2FnZXMoKTsgY2xlYXJpbmcgdGhlIHNldCBsZXRzIHRoZSBzZWNvbmQgcGFzc1xuXHQvLyByZS1leHRyYWN0IGV2ZXJ5IGNvbnN0cnVjdG9yIGFnYWluc3QgdGhlIENPTVBMRVRFIGdyYXBoIOKAlCBwYXNzIDEgc2Vlc1xuXHQvLyBmb3J3YXJkIHJlZmVyZW5jZXMgYXMgYG5vbmVgIChzb2Z0IHVua25vd24pIGJlY2F1c2UgbGF0ZXIgZmlsZXMgaGF2ZVxuXHQvLyBub3QgYmVlbiB2aXNpdGVkIHlldCwgc28gb25seSBwYXNzLTIgcmVzb2x1dGlvbiBpcyBhdXRob3JpdGF0aXZlIGZvclxuXHQvLyB0aGUgaGFyZC1mYWlsIGlkZW50aXR5IGxhdy4gVGhlIHN0YW1wIGxpdmVzIGhlcmUgcmF0aGVyIHRoYW4gb24gdGhlXG5cdC8vIEFTVCBub2RlIHNvIGl0IGNhbiBhY3R1YWxseSBiZSBjbGVhcmVkLiAoQ2hhaW5lZCBjYWxscyB2aXNpdCB0aGUgc2FtZVxuXHQvLyBub2RlIHR3aWNlIHdpdGhpbiBvbmUgcGFzczsgdGhlIGluLXBhc3MgZGVkdXAgYmVsb3cgc3RheXMuKVxuXHRwcml2YXRlIHByb2Nlc3NlZENhbGxzID0gbmV3IFNldDx0cy5DYWxsRXhwcmVzc2lvbj4oKTtcblxuXHRjb25zdHJ1Y3RvciAocHJvZ3JhbT86IHRzLlByb2dyYW0sIHBsdWdpbnM6IFRhY3RpY2FQbHVnaW5bXSA9IFtdKSB7XG5cdFx0Ly8gQ29tcGlsZXIgb3B0aW9ucyBkcml2ZSB0cy5yZXNvbHZlTW9kdWxlTmFtZSBmb3IgaW1wb3J0LWF3YXJlXG5cdFx0Ly8gcmVmZXJlbmNlZC10eXBlIHJlc29sdXRpb24gKHRzY29uZmlnIGBwYXRoc2AsIGV4dGVuc2lvbmxlc3Ncblx0XHQvLyBpbXBvcnRzKTsgdGhlIHR5cGUgY2hlY2tlciBpdHNlbGYgc3RheXMgdW51c2VkLlxuXHRcdHRoaXMucmVmZXJlbmNlZFR5cGVDb21waWxlck9wdGlvbnMgPSBwcm9ncmFtPy5nZXRDb21waWxlck9wdGlvbnMoKSA/PyB7fTtcblx0XHR0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkgPSBtZXJnZVRhY3RpY2FQbHVnaW5zKHBsdWdpbnMpO1xuXHR9XG5cblx0LyoqXG5cdCAqIERpcmVjdG9yaWVzIGhvbGRpbmcgdGhlIGdlbmVyYXRlZCBvdXRwdXQuIEltcG9ydHMgcmVzb2x2aW5nIGludG8gdGhlbVxuXHQgKiBuYW1lIGdlbmVyYXRlZCB0eXBlcywgd2hhdGV2ZXIgc3BlY2lmaWVyIHJlYWNoZXMgdGhlbSAoYSByZWxhdGl2ZVxuXHQgKiBwYXRoLCBhIHRzY29uZmlnIGBwYXRoc2AgYWxpYXMsIGEgY3VzdG9tIC0tb3V0cHV0IG5hbWUpLlxuXHQgKi9cblx0c2V0R2VuZXJhdGVkT3V0cHV0RGlycyAoZGlyczogc3RyaW5nW10pOiB2b2lkIHtcblx0XHR0aGlzLmdlbmVyYXRlZE91dHB1dERpcnMgPSBkaXJzLm1hcChkaXIgPT4gbm9kZVBhdGgucmVzb2x2ZShkaXIpKTtcblx0XHR0aGlzLmdlbmVyYXRlZFNwZWNpZmllckNhY2hlLmNsZWFyKCk7XG5cdH1cblxuXHQvKipcblx0ICogUmVzZXQgdXNhZ2UtcmVsYXRlZCBzdGF0ZSBmb3IgYSBmcmVzaCBwYXNzLlxuXHQgKiBDYWxsIGJlZm9yZSB0aGUgdXNhZ2UtY29sbGVjdGlvbiBwYXNzIHRvIGF2b2lkIGR1cGxpY2F0ZXMgZnJvbSBkZWZpbml0aW9uIHBhc3MuXG5cdCAqL1xuXHRyZXNldFVzYWdlcyAoKTogdm9pZCB7XG5cdFx0dGhpcy51c2FnZXMuY2xlYXIoKTtcblx0XHR0aGlzLmVkc1VzYWdlcy5jbGVhcigpO1xuXHRcdHRoaXMuZmxvd1VzYWdlcy5jbGVhcigpO1xuXHRcdHRoaXMudmFyaWFibGVUb1R5cGVNYXAuY2xlYXIoKTtcblx0XHQvLyBFRFMgZW50cnkgcmVmZXJlbmNlcyBnbyBzdGFsZSB3aXRoIGVkc1VzYWdlczsgdmlhIGxpbmtzIGFyZVxuXHRcdC8vIHJlLWRlcml2ZWQgb24gdGhlIG5leHQgcGFzc1xuXHRcdHRoaXMud3JhcEVudHJ5QnlOb2RlLmNsZWFyKCk7XG5cdFx0dGhpcy5uZXN0ZWRXcmFwVmlhLmNsZWFyKCk7XG5cdFx0Ly8gTm90ZTogbW9kdWxlT2JqZWN0VmFyaWFibGVzIGFuZCBjb2xsZWN0aW9uVmFyaWFibGVzIGludGVudGlvbmFsbHkgcGVyc2lzdFxuXHRcdC8vIGFjcm9zcyBkZWZpbml0aW9uIGFuZCB1c2FnZSBwYXNzZXMuXG5cdFx0Ly8gUmUtZXh0cmFjdGlvbiBpbiB0aGUgdXNhZ2VzIHBhc3MgaXMgd2hhdCBtYWtlcyBncmFwaCByZWZlcmVuY2Vcblx0XHQvLyByZXNvbHV0aW9uIGF1dGhvcml0YXRpdmU6IHBhc3MgMSByZXNvbHZlcyBhZ2FpbnN0IGFuIGluY29tcGxldGVcblx0XHQvLyBncmFwaCAoZm9yd2FyZCByZWZlcmVuY2VzIHJlYWQgYXMgYG5vbmVgKSwgcGFzcyAyIGFnYWluc3QgYWxsIG9mIGl0LlxuXHRcdHRoaXMucHJvY2Vzc2VkQ2FsbHMuY2xlYXIoKTtcblx0XHQvLyBsb29rdXAoKS1wYXRoIHZhbGlkYXRpb24gcnVucyBhZ2FpbnN0IHRoZSByZWNvcmRlZCBzaXRlczsgYSBmcmVzaFxuXHRcdC8vIHBhc3MgbXVzdCByZS1yZWNvcmQgYW5kIHJlLXZhbGlkYXRlIChwYXNzLTEgcmVzdWx0cyB3b3VsZCBiZVxuXHRcdC8vIHByZW1hdHVyZSDigJQgdGhlIGdyYXBoIGlzIHN0aWxsIGluY29tcGxldGUpXG5cdFx0dGhpcy5sb29rdXBSZWZlcmVuY2VzVmFsaWRhdGVkID0gZmFsc2U7XG5cdFx0dGhpcy5sb29rdXBSZWZlcmVuY2VzID0gW107XG5cdFx0dGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzVmFsaWRhdGVkID0gZmFsc2U7XG5cdFx0dGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzID0gW107XG5cdH1cblxuXHQvKipcblx0ICogQW5hbHl6ZSBhIHNvdXJjZSBmaWxlIGZvciBNbmVtb25pY2EgdHlwZSBkZWZpbml0aW9uc1xuXHQgKi9cblx0YW5hbHl6ZUZpbGUgKHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiBBbmFseXplUmVzdWx0IHtcblx0XHR0aGlzLmVycm9ycyA9IFtdO1xuXHRcdC8vIFJlZmVyZW5jZWQtdHlwZSBuYW1lcyBpbiB0aGlzIGZpbGUgcmVzb2x2ZSBhZ2FpbnN0IGl0cyBvd24gaW1wb3J0c1xuXHRcdHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9IG5vZGVQYXRoLnJlc29sdmUoc291cmNlRmlsZS5maWxlTmFtZSk7XG5cdFx0Ly8gRW5zdXJlIHBhcmVudCBub2RlcyBhcmUgc2V0IGZvciBBU1QgdHJhdmVyc2FsXG5cdFx0dGhpcy5zZXRQYXJlbnROb2Rlc0luU291cmNlRmlsZShzb3VyY2VGaWxlKTtcblx0XHR0aGlzLnZpc2l0Tm9kZShzb3VyY2VGaWxlLCBzb3VyY2VGaWxlKTtcblxuXHRcdHJldHVybiB7XG5cdFx0XHR0eXBlcyAgOiB0aGlzLmdyYXBoLmdldEFsbFR5cGVzKCksXG5cdFx0XHRlcnJvcnMgOiB0aGlzLmVycm9ycyxcblx0XHR9O1xuXHR9XG5cblx0LyoqXG5cdCAqIEFuYWx5emUgc291cmNlIGNvZGUgc3RyaW5nXG5cdCAqL1xuXHRhbmFseXplU291cmNlIChzb3VyY2VDb2RlOiBzdHJpbmcsIGZpbGVOYW1lID0gJ3RlbXAudHMnKTogQW5hbHl6ZVJlc3VsdCB7XG5cdFx0Y29uc3Qgc291cmNlRmlsZSA9IHRzLmNyZWF0ZVNvdXJjZUZpbGUoXG5cdFx0XHRmaWxlTmFtZSxcblx0XHRcdHNvdXJjZUNvZGUsXG5cdFx0XHR0cy5TY3JpcHRUYXJnZXQuTGF0ZXN0LFxuXHRcdFx0dHJ1ZVxuXHRcdCk7XG5cdFx0cmV0dXJuIHRoaXMuYW5hbHl6ZUZpbGUoc291cmNlRmlsZSk7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IHRoZSB0eXBlIGdyYXBoXG5cdCAqL1xuXHRnZXRHcmFwaCAoKTogVHlwZUdyYXBoSW1wbCB7XG5cdFx0cmV0dXJuIHRoaXMuZ3JhcGg7XG5cdH1cblxuXHRnZXRCdWlsZGVyVmFsdWVzICgpOiBCdWlsZGVyVmFsdWVbXSB7XG5cdFx0Y29uc3QgcmVzdWx0OiBCdWlsZGVyVmFsdWVbXSA9IFtdO1xuXHRcdGNvbnN0IHNlZW4gPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHRmb3IgKGNvbnN0IGNhbmRpZGF0ZSBvZiB0aGlzLmJ1aWxkZXJDYW5kaWRhdGVzKSB7XG5cdFx0XHQvLyBleGNsdWRlZFR5cGVQYXRocyBjb3ZlcnMgYm90aCBwYXNzZXM6IGEgY2FuZGlkYXRlIHJlY29yZGVkIGluXG5cdFx0XHQvLyBwYXNzIDEsIGJlZm9yZSBhIGNyb3NzLWZpbGUgYWxpYXMgd2FzIGtub3duLCBzdGF5cyBleGNsdWRlZFxuXHRcdFx0Ly8gb25jZSBwYXNzIDIgZmluZHMgaXRzIHNlbGYtcmVmZXJlbmNlXG5cdFx0XHRpZiAoY2FuZGlkYXRlLmV4Y2x1ZGVkIHx8IHRoaXMuZXhjbHVkZWRUeXBlUGF0aHMuaGFzKGNhbmRpZGF0ZS5mdWxsUGF0aCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGV4cG9ydGVkIG9mIGNhbmRpZGF0ZS5leHBvcnRzKSB7XG5cdFx0XHRcdGNvbnN0IGtleSA9YCR7Y2FuZGlkYXRlLmtpbmR9fCR7ZXhwb3J0ZWQuc291cmNlRmlsZX18JHtleHBvcnRlZC5uYW1lfXwke2NhbmRpZGF0ZS5mdWxsUGF0aH1gO1xuXHRcdFx0XHRpZiAoc2Vlbi5oYXMoa2V5KSkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHNlZW4uYWRkKGtleSk7XG5cdFx0XHRcdHJlc3VsdC5wdXNoKHtcblx0XHRcdFx0XHRuYW1lICAgICAgICAgIDogZXhwb3J0ZWQubmFtZSxcblx0XHRcdFx0XHRzb3VyY2VGaWxlICAgIDogZXhwb3J0ZWQuc291cmNlRmlsZSxcblx0XHRcdFx0XHRraW5kICAgICAgICAgIDogY2FuZGlkYXRlLmtpbmQsXG5cdFx0XHRcdFx0ZnVsbFBhdGggICAgICA6IGNhbmRpZGF0ZS5mdWxsUGF0aCxcblx0XHRcdFx0XHRkZWZhdWx0SW1wb3J0IDogZXhwb3J0ZWQuZGVmYXVsdEltcG9ydFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGRlZmluaXRpb25zXG5cdCAqL1xuXHRnZXREZWZpbml0aW9ucyAoKTogTWFwPHN0cmluZywgRGVmaW5pdGlvbkluZm8+IHtcblx0XHRyZXR1cm4gdGhpcy5kZWZpbml0aW9ucztcblx0fVxuXG5cdC8qKlxuXHQgKiBUaGUgY29sbGVjdGlvbnMuanNvbiBtYW5pZmVzdDogb25lIGVudHJ5IHBlciBtaW50ZWQgY29sbGVjdGlvbiwgaW5cblx0ICogbWludGluZyBvcmRlciwgcHJlY2VkZWQgYnkgdGhlIGRlZmF1bHQtY29sbGVjdGlvbiBlbnRyeSB3aGVuZXZlclxuXHQgKiBkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMgZXhpc3QuIFRoZSBkZWZhdWx0IGVudHJ5IGhhcyBubyBpZC9sb2NhdGlvblxuXHQgKiAodGhlcmUgaXMgbm8gY2FsbCBzaXRlIOKAlCB1bnByZWZpeGVkIGZ1bGxQYXRocyBhcmUgaXRzIGlkZW50aXR5KS5cblx0ICogRm9ybWF0IDEuMjogdGhlIHJlZ2lzdHJ5IGludGVyZmFjZSBpcyBOT1QgZW1pdHRlZCAoaXQgaXMgYVxuXHQgKiBUeXBlU2NyaXB0LW9ubHkgY29uY2VybiDigJQgdGhlIGluLW1lbW9yeSByZWdpc3RyeUludGVyZmFjZU5hbWUgdGhhdFxuXHQgKiB0eXBlcy50cy9yZWdpc3RyeS50cyBhcmUgZ2VuZXJhdGVkIGZyb20gc3RheXMgb24gdGhlIFR5cGVOb2RlKS5cblx0ICovXG5cdGdldENvbGxlY3Rpb25zTWFuaWZlc3QgKCk6IENvbGxlY3Rpb25NYW5pZmVzdEVudHJ5W10ge1xuXHRcdGNvbnN0IGVudHJpZXM6IENvbGxlY3Rpb25NYW5pZmVzdEVudHJ5W10gPSBbXTtcblx0XHRjb25zdCBoYXNEZWZhdWx0VHlwZXMgPSB0aGlzLmdyYXBoLmdldEFsbFR5cGVzKCkuc29tZSh0ID0+IHQuY29sbGVjdGlvbklkID09PSB1bmRlZmluZWQpO1xuXHRcdGlmIChoYXNEZWZhdWx0VHlwZXMpIHtcblx0XHRcdGVudHJpZXMucHVzaCh7XG5cdFx0XHRcdGlkICAgICAgIDogbnVsbCxcblx0XHRcdFx0bmFtZSAgICAgOiAnZGVmYXVsdFR5cGVzJyxcblx0XHRcdFx0bG9jYXRpb24gOiBudWxsLFxuXHRcdFx0XHRsYW5ndWFnZSA6ICd0eXBlc2NyaXB0J1xuXHRcdFx0fSk7XG5cdFx0fVxuXHRcdGZvciAoY29uc3QgWyBpZCwgaW5mbyBdIG9mIHRoaXMuY29sbGVjdGlvbkluZm8pIHtcblx0XHRcdGNvbnN0IGVudHJ5OiBDb2xsZWN0aW9uTWFuaWZlc3RFbnRyeSA9IHtcblx0XHRcdFx0aWQsXG5cdFx0XHRcdG5hbWUgICAgIDogaW5mby52YXJpYWJsZU5hbWUsXG5cdFx0XHRcdGxvY2F0aW9uIDogYCR7aW5mby5zb3VyY2VGaWxlfToke2luZm8ubGluZX06JHtpbmZvLmNvbHVtbn1gLFxuXHRcdFx0XHRsYW5ndWFnZSA6ICd0eXBlc2NyaXB0J1xuXHRcdFx0fTtcblx0XHRcdGVudHJpZXMucHVzaChlbnRyeSk7XG5cdFx0fVxuXHRcdHJldHVybiBlbnRyaWVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBjb2xsZWN0ZWQgdXNhZ2VzXG5cdCAqL1xuXHRnZXRVc2FnZXMgKCk6IE1hcDxzdHJpbmcsIFVzYWdlSW5mb1tdPiB7XG5cdFx0cmV0dXJuIHRoaXMudXNhZ2VzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBjb2xsZWN0ZWQgRURTIHVzYWdlc1xuXHQgKi9cblx0Z2V0RURTVXNhZ2VzICgpOiBNYXA8c3RyaW5nLCBFRFNJbmZvW10+IHtcblx0XHRyZXR1cm4gdGhpcy5lZHNVc2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBmbG93IHVzYWdlc1xuXHQgKi9cblx0Z2V0Rmxvd1VzYWdlcyAoKTogTWFwPHN0cmluZywgRmxvd0luZm9bXT4ge1xuXHRcdHJldHVybiB0aGlzLmZsb3dVc2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBpbnN0cnVtZW50YXRpb24gcG9pbnRzLlxuXHQgKiBSZWdpc3RyYXRpb24gc2l0ZXMgcmVmZXJlbmNpbmcgYSBjbGFzcyBkZWNsYXJlZCBpbiB0aGUgc2FtZSBwcm9qZWN0XG5cdCAqIHJlc29sdmUgdG8gdGhlIGNsYXNzIGRlY2xhcmF0aW9uJ3MgbG9jYXRpb24vY29kZTsgZXh0ZXJuYWwgY2xhc3Nlc1xuXHQgKiAoZS5nLiwgYSBmcmFtZXdvcmstYnVpbHRpbiBpbXBsZW1lbnRhdGlvbiBmcm9tIG5vZGVfbW9kdWxlcykga2VlcFxuXHQgKiB0aGUgcmVnaXN0cmF0aW9uIHNpdGUuXG5cdCAqIERlZHVwZWQgYnkga2luZCtjbGFzc05hbWUrbG9jYXRpb24rc2NvcGUgd2l0aCB0YXJnZXRzIG1lcmdlZCDigJQgYVxuXHQgKiBjbGFzcyBkZXRlY3RlZCBieSBoZXJpdGFnZSBBTkQgYnkgYSBkZWNvcmF0b3Igc2l0ZSB5aWVsZHMgc2VwYXJhdGVcblx0ICogZW50cmllcyB3aXRoIGRpc3RpbmN0IHNjb3BlcyAoc2VlIEluc3RydW1lbnRhdGlvblBvaW50IGluIHR5cGVzLnRzKS5cblx0ICovXG5cdGdldEluc3RydW1lbnRhdGlvblBvaW50cyAoKTogSW5zdHJ1bWVudGF0aW9uUG9pbnRbXSB7XG5cdFx0Y29uc3QgcG9pbnRzID0gbmV3IE1hcDxzdHJpbmcsIEluc3RydW1lbnRhdGlvblBvaW50PigpO1xuXG5cdFx0Y29uc3QgYWRkUG9pbnQgPSAocG9pbnQ6IEluc3RydW1lbnRhdGlvblBvaW50KTogdm9pZCA9PiB7XG5cdFx0XHRjb25zdCBrZXkgPSBgJHtwb2ludC5raW5kfXwke3BvaW50LmNsYXNzTmFtZX18JHtwb2ludC5sb2NhdGlvbn18JHtwb2ludC5zY29wZX1gO1xuXHRcdFx0Y29uc3QgZXhpc3RpbmcgPSBwb2ludHMuZ2V0KGtleSk7XG5cdFx0XHRpZiAoZXhpc3RpbmcpIHtcblx0XHRcdFx0Y29uc3QgbWVyZ2VkID0gbmV3IFNldChbIC4uLmV4aXN0aW5nLnRhcmdldHMsIC4uLnBvaW50LnRhcmdldHMgXSk7XG5cdFx0XHRcdGV4aXN0aW5nLnRhcmdldHMgPSBBcnJheS5mcm9tKG1lcmdlZCk7XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdHBvaW50cy5zZXQoa2V5LCBwb2ludCk7XG5cdFx0fTtcblxuXHRcdGZvciAoY29uc3Qgc2l0ZSBvZiB0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzKSB7XG5cdFx0XHRjb25zdCBkZWNsID0gdGhpcy5pbnN0cnVtZW50YXRpb25DbGFzc0RlY2xzLmdldChzaXRlLmNsYXNzTmFtZSk7XG5cdFx0XHRjb25zdCBwb2ludDogSW5zdHJ1bWVudGF0aW9uUG9pbnQgPSB7XG5cdFx0XHRcdGtpbmQgICAgICA6IHNpdGUua2luZCxcblx0XHRcdFx0Y2xhc3NOYW1lIDogc2l0ZS5jbGFzc05hbWUsXG5cdFx0XHRcdGxvY2F0aW9uICA6IGRlY2wgPyBkZWNsLmxvY2F0aW9uIDogc2l0ZS5sb2NhdGlvbixcblx0XHRcdFx0Y29kZSAgICAgIDogZGVjbCA/IGRlY2wuY29kZSA6IHNpdGUuY29kZSxcblx0XHRcdFx0c2NvcGUgICAgIDogc2l0ZS5zY29wZSxcblx0XHRcdFx0dGFyZ2V0cyAgIDogc2l0ZS50YXJnZXRzLFxuXHRcdFx0fTtcblx0XHRcdGFkZFBvaW50KHBvaW50KTtcblx0XHR9XG5cblx0XHQvLyBIZXJpdGFnZS1kZWNsYXJlZCBjbGFzc2VzIGFsd2F5cyBlbWl0IGEgZGVjbGFyYXRpb24gcG9pbnQgd2l0aFxuXHRcdC8vIHNjb3BlICdtb2R1bGUnIChhdHRhY2htZW50IHN0YXRpY2FsbHkgdW5rbm93bik7IHJlZ2lzdHJhdGlvblxuXHRcdC8vIHNpdGVzIGFib3ZlIGNhcnJ5IHRoZSBuYXJyb3dlciBzY29wZXMgYXMgc2VwYXJhdGUgZW50cmllc1xuXHRcdGZvciAoY29uc3QgWyBjbGFzc05hbWUsIGRlY2wgXSBvZiB0aGlzLmluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMpIHtcblx0XHRcdGlmICghZGVjbC5raW5kKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgcG9pbnQ6IEluc3RydW1lbnRhdGlvblBvaW50ID0ge1xuXHRcdFx0XHRraW5kICAgICAgOiBkZWNsLmtpbmQsXG5cdFx0XHRcdGNsYXNzTmFtZSA6IGNsYXNzTmFtZSxcblx0XHRcdFx0bG9jYXRpb24gIDogZGVjbC5sb2NhdGlvbixcblx0XHRcdFx0Y29kZSAgICAgIDogZGVjbC5jb2RlLFxuXHRcdFx0XHRzY29wZSAgICAgOiAnbW9kdWxlJyxcblx0XHRcdFx0dGFyZ2V0cyAgIDogW10sXG5cdFx0XHR9O1xuXHRcdFx0YWRkUG9pbnQocG9pbnQpO1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlc3VsdCA9IEFycmF5LmZyb20ocG9pbnRzLnZhbHVlcygpKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhIHRvcG9sb2dpY2EgdHlwZSB0byB0aGUgYW5hbHl6ZXIgZm9yIHVzYWdlIHRyYWNraW5nLlxuXHQgKiBUaGlzIGFsbG93cyB0aGUgYW5hbHl6ZXIgdG8gcmVjb2duaXplIHRvcG9sb2dpY2EgdHlwZXMgd2hlbiBjb2xsZWN0aW5nIHVzYWdlcy5cblx0ICovXG5cdGFkZFRvcG9sb2dpY2FUeXBlIChmdWxsUGF0aDogc3RyaW5nLCBub2RlOiBpbXBvcnQoJy4vdHlwZXMnKS5UeXBlTm9kZSk6IHZvaWQge1xuXHRcdC8vIFNraXAgaWYgYWxyZWFkeSBleGlzdHNcblx0XHRpZiAodGhpcy5ncmFwaC5hbGxUeXBlcy5oYXMoZnVsbFBhdGgpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoIHNvIGl0IGNhbiBiZSBmb3VuZCBkdXJpbmcgdXNhZ2UgY29sbGVjdGlvblxuXHRcdGlmIChub2RlLnBhcmVudCkge1xuXHRcdFx0Ly8gQWRkIGFzIGNoaWxkIG9mIHBhcmVudFxuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChub2RlLnBhcmVudCwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdC8vIEFkZCBhcyByb290XG5cdFx0XHR0aGlzLmdyYXBoLmFkZFJvb3Qobm9kZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQWxzbyBhZGQgdG8gZGVmaW5pdGlvbnMgc28gaXQncyByZWNvZ25pemVkIGFzIGEga25vd24gdHlwZVxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiBub2RlLm5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke25vZGUuc291cmNlRmlsZX06JHtub2RlLmxpbmV9OiR7bm9kZS5jb2x1bW59YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlZmluZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IG5vZGUucGFyZW50ID8gbm9kZS5wYXJlbnQuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBmYWxzZVxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQoZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFNldCBwYXJlbnQgbm9kZXMgaW4gYSBzb3VyY2UgZmlsZSB0byBlbmFibGUgQVNUIHRyYXZlcnNhbCB1cFxuXHQgKi9cblx0cHJpdmF0ZSBzZXRQYXJlbnROb2Rlc0luU291cmNlRmlsZSAoc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHNldFBhcmVudCA9IChub2RlOiB0cy5Ob2RlLCBwYXJlbnQ/OiB0cy5Ob2RlKSA9PiB7XG5cdFx0XHQvLyBUeXBlU2NyaXB0IGRvZXNuJ3QgZXhwb3NlIHBhcmVudCBhcyB3cml0YWJsZSwgYnV0IHdlIG5lZWQgaXRcblx0XHRcdC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBAdHlwZXNjcmlwdC1lc2xpbnQvbm8tZXhwbGljaXQtYW55XG5cdFx0XHQobm9kZSBhcyBhbnkpLnBhcmVudCA9IHBhcmVudDtcblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCBjaGlsZCA9PiBzZXRQYXJlbnQoY2hpbGQsIG5vZGUpKTtcblx0XHR9O1xuXHRcdHNldFBhcmVudChzb3VyY2VGaWxlKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBWaXNpdCBhIG5vZGUgaW4gdGhlIEFTVFxuXHQgKi9cblx0cHJpdmF0ZSB2aXNpdE5vZGUgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsIGN1cnJlbnRDbGFzcz86IHRzLkNsYXNzRGVjbGFyYXRpb24pOiB2b2lkIHtcblx0XHQvLyBUcmFjayBtbmVtb25pY2EgbW9kdWxlLW9iamVjdCBhbGlhc2VzIGFuZCBjdXN0b20gY29sbGVjdGlvbiB2YXJpYWJsZXNcblx0XHQvLyBiZWZvcmUgcHJvY2Vzc2luZyBkZWZpbmUoKS9sb29rdXAoKSBjYWxscyBzbyBzb3VyY2UgcmVzb2x1dGlvbiB3b3Jrcy5cblx0XHR0aGlzLnRyYWNrSW1wb3J0cyhub2RlKTtcblx0XHR0aGlzLnRyYWNrTW9kdWxlT2JqZWN0QWxpYXNlcyhub2RlKTtcblx0XHR0aGlzLnRyYWNrQ29sbGVjdGlvbkFsaWFzZXMobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0dGhpcy50cmFja0J1aWxkZXJFeHBvcnRBc3NpZ25tZW50KG5vZGUpO1xuXHRcdHRoaXMudHJhY2tDb25zdHJ1Y3RvckJpbmRpbmcobm9kZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgZGVmaW5lKCkgY2FsbHNcblx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0RlZmluZUNhbGwobm9kZSBhcyB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIGxhenkoKSBjYWxsc1xuXHRcdGlmICh0aGlzLmlzTGF6eUNhbGwobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0xhenlDYWxsKG5vZGUgYXMgdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGUpO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHRcdGlmICh0aGlzLmlzRGVjb3JhdGVEZWNvcmF0b3Iobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0RlY29yYXRlRGVjb3JhdG9yKG5vZGUgYXMgdHMuRGVjb3JhdG9yLCBzb3VyY2VGaWxlLCBjdXJyZW50Q2xhc3MpO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciB0eXBlIHVzYWdlcyAobmV3IFR5cGUoKSwgdHlwZSBhbm5vdGF0aW9ucywgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RVc2FnZShub2RlLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIENoZWNrIGZvciBFRFMgcGF0dGVybnMgKHdyYXAsIGN1cnJlbnQsIGdldEZsb3csIGV0Yy4pXG5cdFx0dGhpcy5jb2xsZWN0RURTKG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIG5hdGl2ZSBmbG93IHBhdHRlcm5zIChwcm9wZXJ0eSBhY2Nlc3MsIG1ldGhvZCBjYWxscywgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RGbG93KG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIGZyYW1ld29yayBpbnN0cnVtZW50YXRpb24gcG9pbnRzICh2b2NhYnVsYXJ5IHN1cHBsaWVkXG5cdFx0Ly8gYnkgcGx1Z2luczsgc3ludGFjdGljIG9ubHkg4oCUIG5vIHR5cGUgY2hlY2tlcilcblx0XHR0aGlzLmNvbGxlY3RJbnN0cnVtZW50YXRpb24obm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDb2xsZWN0IHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbnMgKGFsaWFzZXMsIGNsYXNzZXMsIGludGVyZmFjZXMpXG5cdFx0Ly8gcGVyIGZpbGUsIGFuZCB0aGUgZmlsZSdzIGltcG9ydCB3aXJpbmcsIGZvciBpbXBvcnQtYXdhcmUgcmVzb2x1dGlvblxuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKG5vZGUpO1xuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZUltcG9ydChub2RlKTtcblx0XHR0aGlzLnRyYWNrUmVmZXJlbmNlZFR5cGVSZUV4cG9ydChub2RlKTtcblx0XHR0aGlzLnRyYWNrUmVmZXJlbmNlZFR5cGVDb25zdEFycmF5KG5vZGUpO1xuXG5cdFx0Ly8gVHJhY2sgc2FtZS1maWxlIGZ1bmN0aW9uIGJpbmRpbmdzIHNvIEVEUyBjYW4gcmVzb2x2ZSB3cmFwKGZuKVxuXHRcdC8vIGFyZ3VtZW50cyB3aXRob3V0IHRoZSB0eXBlIGNoZWNrZXIgKGJlc3QgZWZmb3J0LCBsYXN0IHdpbnMpXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9IyR7bm9kZS5uYW1lLnRleHR9YDtcblx0XHRcdHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5zZXQoa2V5LCBub2RlKTtcblx0XHR9XG5cdFx0aWYgKFxuXHRcdFx0dHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSAmJlxuXHRcdFx0bm9kZS5pbml0aWFsaXplciAmJlxuXHRcdFx0KHRzLmlzQXJyb3dGdW5jdGlvbihub2RlLmluaXRpYWxpemVyKSB8fCB0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihub2RlLmluaXRpYWxpemVyKSlcblx0XHQpIHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9IyR7bm9kZS5uYW1lLnRleHR9YDtcblx0XHRcdHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5zZXQoa2V5LCBub2RlLmluaXRpYWxpemVyKTtcblx0XHR9XG5cblx0XHQvLyBUcmFjayBjbGFzcyBkZWNsYXJhdGlvbnMgZm9yIGRlY29yYXRvciBwYXJlbnQgbG9va3VwXG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0Ly8gVmlzaXQgY2hpbGRyZW4gd2l0aCB0aGlzIGNsYXNzIGFzIHRoZSBjdXJyZW50IGNvbnRleHRcblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCBjaGlsZCA9PiB0aGlzLnZpc2l0Tm9kZShjaGlsZCwgc291cmNlRmlsZSwgbm9kZSkpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHQvLyBSZWN1cnNpdmVseSB2aXNpdCBjaGlsZHJlblxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHRoaXMudmlzaXROb2RlKGNoaWxkLCBzb3VyY2VGaWxlLCBjdXJyZW50Q2xhc3MpKTtcblx0XHR9XG5cdH1cblxuXHRwcml2YXRlIHRyYWNrQ29uc3RydWN0b3JCaW5kaW5nIChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0bGV0IG5hbWU6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRsZXQgaGFuZGxlcjogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkO1xuXHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkgJiYgbm9kZS5pbml0aWFsaXplcikge1xuXHRcdFx0bmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0aGFuZGxlciA9IG5vZGUuaW5pdGlhbGl6ZXI7XG5cdFx0fSBlbHNlIGlmICgodHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKG5vZGUpIHx8IHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSkgJiYgbm9kZS5uYW1lKSB7XG5cdFx0XHRuYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0XHRoYW5kbGVyID0gbm9kZTtcblx0XHR9XG5cdFx0aWYgKCFuYW1lIHx8ICFoYW5kbGVyKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGZpbGVQYXRoID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGxldCBiaW5kaW5ncyA9IHRoaXMuY29uc3RydWN0b3JCaW5kaW5ncy5nZXQoZmlsZVBhdGgpO1xuXHRcdGlmICghYmluZGluZ3MpIHtcblx0XHRcdGJpbmRpbmdzID0gbmV3IE1hcDxzdHJpbmcsIENvbnN0cnVjdG9ySGFuZGxlcj4oKTtcblx0XHRcdHRoaXMuY29uc3RydWN0b3JCaW5kaW5ncy5zZXQoZmlsZVBhdGgsIGJpbmRpbmdzKTtcblx0XHR9XG5cdFx0YmluZGluZ3Muc2V0KG5hbWUsIGhhbmRsZXIpO1xuXHR9XG5cblx0LyoqXG5cdCAqIERvZXMgYW4gaW1wb3J0IHNwZWNpZmllciBuYW1lIHRoZSBnZW5lcmF0ZWQgb3V0cHV0PyBBIGNvbnZlbnRpb25hbFxuXHQgKiBgLnRhY3RpY2FgIHBhdGggYWx3YXlzIGRvZXM7IG90aGVyd2lzZSB0aGUgc3BlY2lmaWVyIGlzIHJlc29sdmVkIHdpdGhcblx0ICogdGhlIHByb2dyYW0ncyBjb21waWxlck9wdGlvbnMgKHRzY29uZmlnIGBwYXRoc2AgaW5jbHVkZWQpIGFzIGlmIHRoZVxuXHQgKiBnZW5lcmF0ZWQgZmlsZXMgZXhpc3RlZCDigJQgb24gYSBmcmVzaCBjbG9uZSB0aGV5IGFyZSBub3Qgd3JpdHRlbiB5ZXQuXG5cdCAqL1xuXHRwcml2YXRlIGlzR2VuZXJhdGVkVHlwZVNwZWNpZmllciAoc3BlY2lmaWVyOiBzdHJpbmcpOiBib29sZWFuIHtcblx0XHRpZiAoc3BlY2lmaWVyLmluY2x1ZGVzKCcudGFjdGljYScpKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cdFx0Y29uc3Qgb3V0cHV0RGlycyA9IHRoaXMuZ2VuZXJhdGVkT3V0cHV0RGlycztcblx0XHRpZiAob3V0cHV0RGlycy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Y29uc3QgY2FjaGVLZXkgPSBgJHt0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGV9Ojoke3NwZWNpZmllcn1gO1xuXHRcdGNvbnN0IGNhY2hlZCA9IHRoaXMuZ2VuZXJhdGVkU3BlY2lmaWVyQ2FjaGUuZ2V0KGNhY2hlS2V5KTtcblx0XHRpZiAoY2FjaGVkICE9PSB1bmRlZmluZWQpIHtcblx0XHRcdHJldHVybiBjYWNoZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGluc2lkZU91dHB1dCA9IChmaWxlT3JEaXI6IHN0cmluZyk6IGJvb2xlYW4gPT4ge1xuXHRcdFx0Y29uc3QgYWJzb2x1dGUgPSBub2RlUGF0aC5yZXNvbHZlKGZpbGVPckRpcik7XG5cdFx0XHRjb25zdCBpbnNpZGUgPSBvdXRwdXREaXJzLnNvbWUoZGlyID0+IGFic29sdXRlID09PSBkaXIgfHwgYWJzb2x1dGUuc3RhcnRzV2l0aChkaXIgKyBub2RlUGF0aC5zZXApKTtcblx0XHRcdHJldHVybiBpbnNpZGU7XG5cdFx0fTtcblx0XHRjb25zdCBob3N0OiB0cy5Nb2R1bGVSZXNvbHV0aW9uSG9zdCA9IHtcblx0XHRcdGZpbGVFeGlzdHMgICAgICA6IGZpbGVOYW1lID0+IGluc2lkZU91dHB1dChmaWxlTmFtZSkgfHwgdHMuc3lzLmZpbGVFeGlzdHMoZmlsZU5hbWUpLFxuXHRcdFx0cmVhZEZpbGUgICAgICAgIDogZmlsZU5hbWUgPT4gdHMuc3lzLnJlYWRGaWxlKGZpbGVOYW1lKSxcblx0XHRcdGRpcmVjdG9yeUV4aXN0cyA6IGRpcmVjdG9yeU5hbWUgPT4gaW5zaWRlT3V0cHV0KGRpcmVjdG9yeU5hbWUpIHx8IHRzLnN5cy5kaXJlY3RvcnlFeGlzdHMoZGlyZWN0b3J5TmFtZSksXG5cdFx0fTtcblx0XHRjb25zdCByZXNvbHZlZCA9IHRzLnJlc29sdmVNb2R1bGVOYW1lKFxuXHRcdFx0c3BlY2lmaWVyLFxuXHRcdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlLFxuXHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUNvbXBpbGVyT3B0aW9ucyxcblx0XHRcdGhvc3Rcblx0XHQpLnJlc29sdmVkTW9kdWxlO1xuXHRcdGNvbnN0IHJlc3VsdCA9IHJlc29sdmVkICE9PSB1bmRlZmluZWQgJiYgaW5zaWRlT3V0cHV0KHJlc29sdmVkLnJlc29sdmVkRmlsZU5hbWUpO1xuXHRcdHRoaXMuZ2VuZXJhdGVkU3BlY2lmaWVyQ2FjaGUuc2V0KGNhY2hlS2V5LCByZXN1bHQpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgaW1wb3J0cyBmcm9tICdtbmVtb25pY2EnIHNvIGFsaWFzZXMgb2YgdGhlIG1vZHVsZSBvYmplY3QgYW5kXG5cdCAqIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbiBhcmUgcmVjb2duaXplZCB3aXRob3V0IHJlbHlpbmcgb24gdGhlIHR5cGUgY2hlY2tlci5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tJbXBvcnRzIChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc0ltcG9ydERlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBtb2R1bGVTcGVjaWZpZXIgfSA9IG5vZGU7XG5cdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChtb2R1bGVTcGVjaWZpZXIpICYmIHRoaXMuaXNHZW5lcmF0ZWRUeXBlU3BlY2lmaWVyKG1vZHVsZVNwZWNpZmllci50ZXh0KSkge1xuXHRcdFx0bGV0IGltcG9ydHMgPSB0aGlzLmdlbmVyYXRlZFR5cGVJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0aWYgKCFpbXBvcnRzKSB7XG5cdFx0XHRcdGltcG9ydHMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHRcdFx0dGhpcy5nZW5lcmF0ZWRUeXBlSW1wb3J0cy5zZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlLCBpbXBvcnRzKTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGdlbmVyYXRlZENsYXVzZSA9IG5vZGUuaW1wb3J0Q2xhdXNlO1xuXHRcdFx0aWYgKGdlbmVyYXRlZENsYXVzZT8ubmFtZSkge1xuXHRcdFx0XHRpbXBvcnRzLmFkZChnZW5lcmF0ZWRDbGF1c2UubmFtZS50ZXh0KTtcblx0XHRcdH1cblx0XHRcdGlmIChnZW5lcmF0ZWRDbGF1c2U/Lm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lZEltcG9ydHMoZ2VuZXJhdGVkQ2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBnZW5lcmF0ZWRDbGF1c2UubmFtZWRCaW5kaW5ncy5lbGVtZW50cykge1xuXHRcdFx0XHRcdGltcG9ydHMuYWRkKGVsZW1lbnQubmFtZS50ZXh0KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKGdlbmVyYXRlZENsYXVzZT8ubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVzcGFjZUltcG9ydChnZW5lcmF0ZWRDbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdFx0aW1wb3J0cy5hZGQoZ2VuZXJhdGVkQ2xhdXNlLm5hbWVkQmluZGluZ3MubmFtZS50ZXh0KTtcblx0XHRcdH1cblx0XHR9XG5cdFx0aWYgKCF0cy5pc1N0cmluZ0xpdGVyYWwobW9kdWxlU3BlY2lmaWVyKSB8fCBtb2R1bGVTcGVjaWZpZXIudGV4dCAhPT0gJ21uZW1vbmljYScpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCBjbGF1c2UgPSBub2RlLmltcG9ydENsYXVzZTtcblx0XHRpZiAoIWNsYXVzZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGltcG9ydCB7IG1uZW1vbmljYSwgY3JlYXRlVHlwZXNDb2xsZWN0aW9uIH0gZnJvbSAnbW5lbW9uaWNhJ1xuXHRcdGlmIChjbGF1c2UubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVkSW1wb3J0cyhjbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBjbGF1c2UubmFtZWRCaW5kaW5ncy5lbGVtZW50cykge1xuXHRcdFx0XHRjb25zdCBsb2NhbE5hbWUgPSBlbGVtZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgaW1wb3J0ZWROYW1lID0gZWxlbWVudC5wcm9wZXJ0eU5hbWVcblx0XHRcdFx0XHQ/IGVsZW1lbnQucHJvcGVydHlOYW1lLnRleHRcblx0XHRcdFx0XHQ6IGxvY2FsTmFtZTtcblx0XHRcdFx0aWYgKGltcG9ydGVkTmFtZSA9PT0gJ21uZW1vbmljYScpIHtcblx0XHRcdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQobG9jYWxOYW1lKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoaW1wb3J0ZWROYW1lID09PSAnY3JlYXRlVHlwZXNDb2xsZWN0aW9uJykge1xuXHRcdFx0XHRcdHRoaXMuY3JlYXRlVHlwZXNDb2xsZWN0aW9uVmFyaWFibGVzLmFkZChsb2NhbE5hbWUpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGxldCBmaWxlSW1wb3J0cyA9IHRoaXMubW5lbW9uaWNhTmFtZWRJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHRpZiAoIWZpbGVJbXBvcnRzKSB7XG5cdFx0XHRcdFx0ZmlsZUltcG9ydHMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0XHRcdHRoaXMubW5lbW9uaWNhTmFtZWRJbXBvcnRzLnNldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUsIGZpbGVJbXBvcnRzKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRmaWxlSW1wb3J0cy5zZXQobG9jYWxOYW1lLCBpbXBvcnRlZE5hbWUpO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIGltcG9ydCAqIGFzIG1uZW1vbmljYSBmcm9tICdtbmVtb25pY2EnXG5cdFx0aWYgKGNsYXVzZS5uYW1lZEJpbmRpbmdzICYmIHRzLmlzTmFtZXNwYWNlSW1wb3J0KGNsYXVzZS5uYW1lZEJpbmRpbmdzKSkge1xuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuYWRkKGNsYXVzZS5uYW1lZEJpbmRpbmdzLm5hbWUudGV4dCk7XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0IG1uZW1vbmljYSBmcm9tICdtbmVtb25pY2EnIChkZWZhdWx0IGltcG9ydCkg4oCUIHRyZWF0IGFzIG1vZHVsZSBvYmplY3QgdG9vXG5cdFx0aWYgKGNsYXVzZS5uYW1lKSB7XG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQoY2xhdXNlLm5hbWUudGV4dCk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhIG5hbWVkIHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbiAodHlwZSBhbGlhcywgY2xhc3MsIG9yXG5cdCAqIGludGVyZmFjZSkgZm9yIHRoZSBmaWxlIGN1cnJlbnRseSBiZWluZyB2aXNpdGVkLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHQvLyBOYW1lc3BhY2VzIGFyZSB0aGUgbWlkZGxlIHNlZ21lbnRzIG9mIHF1YWxpZmllZCByZWZlcmVuY2VzXG5cdFx0Ly8gKG1vZGVscy5Jbm5lci5DcmF0ZSkg4oCUIHJlY29yZGVkIHNlcGFyYXRlbHkgZnJvbSB0aGUgcGxhaW4tbmFtZVxuXHRcdC8vIGRlY2xhcmF0aW9uIHRhYmxlIChzdHJpbmctbmFtZWQgYG1vZHVsZSAn4oCmJ2AgZGVjbGFyYXRpb25zIGFyZVxuXHRcdC8vIGFtYmllbnQgZXh0ZXJuYWxzIGFuZCBzdGF5IG91dClcblx0XHRpZiAodHMuaXNNb2R1bGVEZWNsYXJhdGlvbihub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSAmJlxuXHRcdFx0bm9kZS5ib2R5ICYmIHRzLmlzTW9kdWxlQmxvY2sobm9kZS5ib2R5KSkge1xuXHRcdFx0Y29uc3QgbmFtZXNwYWNlRmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0XHRsZXQgbmFtZXNwYWNlcyA9IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzLmdldChuYW1lc3BhY2VGaWxlUGF0aCk7XG5cdFx0XHRpZiAoIW5hbWVzcGFjZXMpIHtcblx0XHRcdFx0bmFtZXNwYWNlcyA9IG5ldyBNYXA8c3RyaW5nLCB0cy5Nb2R1bGVEZWNsYXJhdGlvbj4oKTtcblx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMuc2V0KG5hbWVzcGFjZUZpbGVQYXRoLCBuYW1lc3BhY2VzKTtcblx0XHRcdH1cblx0XHRcdG5hbWVzcGFjZXMuc2V0KG5vZGUubmFtZS50ZXh0LCBub2RlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRsZXQgbmFtZSA9ICcnO1xuXHRcdGxldCBraW5kOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uWydraW5kJ10gfCB1bmRlZmluZWQ7XG5cdFx0bGV0IGRlY2xOb2RlOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uWydub2RlJ10gfCB1bmRlZmluZWQ7XG5cblx0XHRpZiAodHMuaXNUeXBlQWxpYXNEZWNsYXJhdGlvbihub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSkge1xuXHRcdFx0bmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0a2luZCA9ICdhbGlhcyc7XG5cdFx0XHRkZWNsTm9kZSA9IG5vZGU7XG5cdFx0fSBlbHNlIGlmICh0cy5pc0NsYXNzRGVjbGFyYXRpb24obm9kZSkgJiYgbm9kZS5uYW1lKSB7XG5cdFx0XHRuYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0XHRraW5kID0gJ2NsYXNzJztcblx0XHRcdGRlY2xOb2RlID0gbm9kZTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzSW50ZXJmYWNlRGVjbGFyYXRpb24obm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdG5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRcdGtpbmQgPSAnaW50ZXJmYWNlJztcblx0XHRcdGRlY2xOb2RlID0gbm9kZTtcblx0XHR9XG5cblx0XHRpZiAoIWtpbmQgfHwgIWRlY2xOb2RlIHx8ICFuYW1lKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0bGV0IGRlY2xzID0gdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLmdldChmaWxlUGF0aCk7XG5cdFx0aWYgKCFkZWNscykge1xuXHRcdFx0ZGVjbHMgPSBuZXcgTWFwPHN0cmluZywgUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbj4oKTtcblx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscy5zZXQoZmlsZVBhdGgsIGRlY2xzKTtcblx0XHR9XG5cdFx0Y29uc3QgZW50cnk6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gPSB7IGtpbmQsIG5vZGUgOiBkZWNsTm9kZSwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0ZGVjbHMuc2V0KG5hbWUsIGVudHJ5KTtcblxuXHRcdC8vIGBleHBvcnQgZGVmYXVsdCBjbGFzcyBGb28ge31gIGlzIGFsc28gcmVhY2hhYmxlIHVuZGVyIHRoZSAnZGVmYXVsdCdcblx0XHQvLyBiaW5kaW5nIGZvciBkZWZhdWx0IGltcG9ydGVyc1xuXHRcdGlmIChraW5kID09PSAnY2xhc3MnKSB7XG5cdFx0XHRjb25zdCBjbGFzc05vZGUgPSBkZWNsTm9kZSBhcyB0cy5DbGFzc0RlY2xhcmF0aW9uO1xuXHRcdFx0Y29uc3QgaXNFeHBvcnRlZCA9IGNsYXNzTm9kZS5tb2RpZmllcnM/LnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRXhwb3J0S2V5d29yZCkgPz8gZmFsc2U7XG5cdFx0XHRjb25zdCBpc0RlZmF1bHQgPSBjbGFzc05vZGUubW9kaWZpZXJzPy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLkRlZmF1bHRLZXl3b3JkKSA/PyBmYWxzZTtcblx0XHRcdGlmIChpc0V4cG9ydGVkICYmIGlzRGVmYXVsdCkge1xuXHRcdFx0XHRkZWNscy5zZXQoJ2RlZmF1bHQnLCBlbnRyeSk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBjb25zdHMgaW5pdGlhbGl6ZWQgd2l0aCBhbiBhcnJheSBsaXRlcmFsIChvcHRpb25hbGx5IHdyYXBwZWQgaW5cblx0ICogYGFzIGNvbnN0YCAvIGBzYXRpc2ZpZXNgKSwgc28gYSBgdHlwZW9mIHN0YXR1c0xpc3RbbnVtYmVyXWAgZmllbGQgdHlwZVxuXHQgKiBleHBhbmRzIHRvIHRoZSBlbGVtZW50IGxpdGVyYWwgdW5pb24g4oCUIHRoZSBnZW5lcmF0ZWQgZmlsZSBjYXJyaWVzIG5vXG5cdCAqIGltcG9ydHMsIHNvIGVtaXR0aW5nIHRoZSBiYXJlIGB0eXBlb2Ygc3RhdHVzTGlzdGAgcXVlcnkgd291bGQgYmUgYW5cblx0ICogdW5yZXNvbHZhYmxlIG5hbWUgZG93bnN0cmVhbS4gRmlyc3QgYmluZGluZyB3aW5zOiBhIG5lc3RlZCBzaGFkb3dcblx0ICogbXVzdCBub3QgcmVwbGFjZSB0aGUgbW9kdWxlLWxldmVsIGNvbnN0IHRoZSB0eXBlb2YgcmVmZXJzIHRvLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlQ29uc3RBcnJheSAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpIHx8ICF0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSB8fCAhbm9kZS5pbml0aWFsaXplcikge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCB7IGluaXRpYWxpemVyOiByYXdJbml0aWFsaXplciB9ID0gbm9kZTtcblx0XHRsZXQgaW5pdGlhbGl6ZXI6IHRzLkV4cHJlc3Npb24gPSByYXdJbml0aWFsaXplcjtcblx0XHR3aGlsZSAoXG5cdFx0XHR0cy5pc0FzRXhwcmVzc2lvbihpbml0aWFsaXplcikgfHxcblx0XHRcdHRzLmlzU2F0aXNmaWVzRXhwcmVzc2lvbihpbml0aWFsaXplcikgfHxcblx0XHRcdC8vIHRoZSBhbmdsZS1icmFja2V0IGFzc2VydGlvbiBzcGVsbGluZyAoYDxjb25zdD5b4oCmXWApIGlzIHRoZVxuXHRcdFx0Ly8gc2FtZSBjb25zdC1hcnJheSBtYXJrZXIgYXMgdGhlIGBhcyBjb25zdGAgZm9ybSAoRjE3KVxuXHRcdFx0dHMuaXNUeXBlQXNzZXJ0aW9uRXhwcmVzc2lvbihpbml0aWFsaXplcilcblx0XHQpIHtcblx0XHRcdGluaXRpYWxpemVyID0gaW5pdGlhbGl6ZXIuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0aWYgKCF0cy5pc0FycmF5TGl0ZXJhbEV4cHJlc3Npb24oaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGZpbGVQYXRoID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGxldCBjb25zdHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuZ2V0KGZpbGVQYXRoKTtcblx0XHRpZiAoIWNvbnN0cykge1xuXHRcdFx0Y29uc3RzID0gbmV3IE1hcDxzdHJpbmcsIHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24+KCk7XG5cdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuc2V0KGZpbGVQYXRoLCBjb25zdHMpO1xuXHRcdH1cblx0XHRpZiAoIWNvbnN0cy5oYXMobm9kZS5uYW1lLnRleHQpKSB7XG5cdFx0XHRjb25zdHMuc2V0KG5vZGUubmFtZS50ZXh0LCBpbml0aWFsaXplcik7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEZpbmQgdGhlIGFycmF5IGxpdGVyYWwgYmVoaW5kIGEgbW9kdWxlIGNvbnN0IHJlZmVyZW5jZWQgdGhyb3VnaFxuXHQgKiBgdHlwZW9mYDogdGhlIGRlY2xhcmluZyBmaWxlJ3Mgb3duIGNvbnN0cyBmaXJzdCAodGhlIEYxMyBjYXNlIGlzIGFcblx0ICogTk9OLWV4cG9ydGVkIGNvbnN0IGluIHRoZSBzYW1lIG1vZHVsZSBhcyB0aGUgZXhwYW5kZWQgY2xhc3MpLCB0aGVuIOKAlFxuXHQgKiB3aGVuIHRoZSBmaWxlIGltcG9ydHMgdGhlIG5hbWUg4oCUIHRoZSBpbXBvcnRlZCBtb2R1bGUncyBjb25zdHMuXG5cdCAqIEV4dGVybmFsIG1vZHVsZXMgYXJlIG5ldmVyIGFuYWx5emVkLCBzbyB0aG9zZSB5aWVsZCBub3RoaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kUmVmZXJlbmNlZENvbnN0QXJyYXkgKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRmcm9tRmlsZTogc3RyaW5nXG5cdCk6IHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGxvY2FsID0gdGhpcy5yZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzLmdldChmcm9tRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWwpIHtcblx0XHRcdHJldHVybiBsb2NhbDtcblx0XHR9XG5cdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoZnJvbUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKCFpbXBvcnRlZCB8fCBpbXBvcnRlZC5pc05hbWVzcGFjZSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKGltcG9ydGVkLnNwZWNpZmllciwgZnJvbUZpbGUpO1xuXHRcdGlmICghcmVzb2x1dGlvbiB8fCByZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGZvdW5kID0gdGhpcy5yZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzLmdldChyZXNvbHV0aW9uLnJlc29sdmVkUGF0aCk/LmdldChpbXBvcnRlZC5vcmlnaW5hbE5hbWUpO1xuXHRcdHJldHVybiBmb3VuZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFbGVtZW50IGxpdGVyYWwgdHlwZXMgb2YgYSB0cmFja2VkIGNvbnN0IGFycmF5OiBldmVyeSBlbGVtZW50IG11c3QgYmVcblx0ICogYSBwbGFpbiBsaXRlcmFsIChvcHRpb25hbGx5IHdyYXBwZWQgaW4gYGFzIGNvbnN0YCAvIGBzYXRpc2ZpZXNgIC9cblx0ICogYDxjb25zdD5gIGFzc2VydGlvbnMpIOKAlCBzdHJpbmcsIG51bWVyaWMgKHVuYXJ5IGAtYC9gK2AgcHJlc2VydmVkKSxcblx0ICogYm9vbGVhbiwgb3IgbnVsbC4gU3ByZWFkcywgaWRlbnRpZmllcnMsIGFuZCBuZXN0ZWQgYXJyYXlzIG1lYW4gdGhlXG5cdCAqIHVuaW9uIGlzIG5vdCBzdGF0aWNhbGx5IHZpc2libGUgYW5kIHlpZWxkIHVuZGVmaW5lZCwgc28gdGhlIGNhbGxlclxuXHQgKiBkZWdyYWRlcyB0aGUgZmllbGQgdG8gYHVua25vd25gIHJhdGhlciB0aGFuIGd1ZXNzaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBsaXRlcmFsVHlwZXNPZkFycmF5IChhcnJheUxpdGVyYWw6IHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24pOiBzdHJpbmdbXSB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgbGl0ZXJhbHM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGFycmF5TGl0ZXJhbC5lbGVtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzU3ByZWFkRWxlbWVudChlbGVtZW50KSkge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbGl0ZXJhbCA9IHRoaXMubGl0ZXJhbFR5cGVPZkV4cHJlc3Npb24oZWxlbWVudCk7XG5cdFx0XHRpZiAobGl0ZXJhbCA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRsaXRlcmFscy5wdXNoKGxpdGVyYWwpO1xuXHRcdH1cblx0XHRpZiAobGl0ZXJhbHMubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBsaXRlcmFscztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFRoZSBsaXRlcmFsIHR5cGUgb2Ygb25lIGFycmF5IGVsZW1lbnQ6IGEgcGxhaW4gbGl0ZXJhbCAob3B0aW9uYWxseVxuXHQgKiB3cmFwcGVkIGluIGBhcyBjb25zdGAgLyBgc2F0aXNmaWVzYCAvIGFzc2VydGlvbiBleHByZXNzaW9ucykg4oCUXG5cdCAqIHN0cmluZywgbnVtZXJpYyAodW5hcnkgYC1gL2ArYCBwcmVzZXJ2ZWQpLCBib29sZWFuLCBvciBudWxsLlxuXHQgKiBBbnl0aGluZyBlbHNlIHlpZWxkcyB1bmRlZmluZWQuXG5cdCAqL1xuXHRwcml2YXRlIGxpdGVyYWxUeXBlT2ZFeHByZXNzaW9uIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgaW5uZXI6IHRzLkV4cHJlc3Npb24gPSBleHByO1xuXHRcdHdoaWxlICh0cy5pc0FzRXhwcmVzc2lvbihpbm5lcikgfHwgdHMuaXNTYXRpc2ZpZXNFeHByZXNzaW9uKGlubmVyKSB8fCB0cy5pc1R5cGVBc3NlcnRpb25FeHByZXNzaW9uKGlubmVyKSkge1xuXHRcdFx0aW5uZXIgPSBpbm5lci5leHByZXNzaW9uO1xuXHRcdH1cblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGlubmVyKSB8fCB0cy5pc05vU3Vic3RpdHV0aW9uVGVtcGxhdGVMaXRlcmFsKGlubmVyKSkge1xuXHRcdFx0Y29uc3QgbGl0ZXJhbCA9IGAnJHtpbm5lci50ZXh0fSdgO1xuXHRcdFx0cmV0dXJuIGxpdGVyYWw7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1ByZWZpeFVuYXJ5RXhwcmVzc2lvbihpbm5lcikgJiYgdHMuaXNOdW1lcmljTGl0ZXJhbChpbm5lci5vcGVyYW5kKSkge1xuXHRcdFx0aWYgKGlubmVyLm9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLk1pbnVzVG9rZW4pIHtcblx0XHRcdFx0Y29uc3QgbmVnYXRpdmUgPSBgLSR7aW5uZXIub3BlcmFuZC50ZXh0fWA7XG5cdFx0XHRcdHJldHVybiBuZWdhdGl2ZTtcblx0XHRcdH1cblx0XHRcdGlmIChpbm5lci5vcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5QbHVzVG9rZW4pIHtcblx0XHRcdFx0cmV0dXJuIGlubmVyLm9wZXJhbmQudGV4dDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc051bWVyaWNMaXRlcmFsKGlubmVyKSkge1xuXHRcdFx0cmV0dXJuIGlubmVyLnRleHQ7XG5cdFx0fVxuXHRcdGlmIChpbm5lci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRyZXR1cm4gJ3RydWUnO1xuXHRcdH1cblx0XHRpZiAoaW5uZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQpIHtcblx0XHRcdHJldHVybiAnZmFsc2UnO1xuXHRcdH1cblx0XHRpZiAoaW5uZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5OdWxsS2V5d29yZCkge1xuXHRcdFx0cmV0dXJuICdudWxsJztcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGMjI6IHRoZSBjb25zdC1hc3NlcnRpb24gY2hlY2sgc2hhcmVkIGJ5IHRoZSB2YWx1ZS1sZXZlbCBhbmRcblx0ICogZGVjbGFyYXRpb24tbGV2ZWwgcGF0aHMg4oCUIGBleHByIGFzIGNvbnN0YCBhbmQgYDxjb25zdD5leHByYCBwYXJzZVxuXHQgKiBpZGVudGljYWxseSAoYSBUeXBlUmVmZXJlbmNlTm9kZSBuYW1lZCAnY29uc3QnKS4gR2VuZXJhbCBgPFQ+ZXhwcmBcblx0ICogYXNzZXJ0aW9ucyBuZXZlciBtYXRjaC5cblx0ICovXG5cdHByaXZhdGUgaXNDb25zdEFzc2VydGlvblR5cGUgKHR5cGU6IHRzLlR5cGVOb2RlKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgY29uc3RBc3NlcnRpb24gPSB0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHR5cGUpICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIodHlwZS50eXBlTmFtZSkgJiZcblx0XHRcdHR5cGUudHlwZU5hbWUudGV4dCA9PT0gJ2NvbnN0Jztcblx0XHRyZXR1cm4gY29uc3RBc3NlcnRpb247XG5cdH1cblxuXHQvKipcblx0ICogVGhlIGFycmF5IGxpdGVyYWwgYmVoaW5kIGEgdmFsdWUtbGV2ZWwgZWxlbWVudCBhY2Nlc3M6IGlubGluZVxuXHQgKiAoYCg8Y29uc3Q+W+KApl0pWzBdYCwgYChb4oCmXSBhcyBjb25zdClbMV1gKSwgcGFyZW50aGVzaXplZCwgb3IgYVxuXHQgKiB0cmFja2VkIG1vZHVsZSBjb25zdCBhcnJheSAoYGNvbnN0IHggPSA8Y29uc3Q+W+KApl1gIC8gYHhbMF1gLCBGMTdcblx0ICogdHJhY2tpbmcpLiBPbmx5IGNvbnN0IGFzc2VydGlvbnMgYXJlIHVud3JhcHBlZCDigJQgZ2VuZXJhbFxuXHQgKiBhc3NlcnRpb25zIHN0YXkgdW5rbm93biAoRjIyIHNjb3BlIGJvdW5kYXJ5KS5cblx0ICovXG5cdHByaXZhdGUgY29uc3RBcnJheUxpdGVyYWxPZiAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5FeHByZXNzaW9uID0gZXhwcjtcblx0XHR3aGlsZSAodHMuaXNQYXJlbnRoZXNpemVkRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0aWYgKHRzLmlzQXJyYXlMaXRlcmFsRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0cmV0dXJuIGN1cnJlbnQ7XG5cdFx0fVxuXHRcdGlmICgodHMuaXNBc0V4cHJlc3Npb24oY3VycmVudCkgfHwgdHMuaXNUeXBlQXNzZXJ0aW9uRXhwcmVzc2lvbihjdXJyZW50KSkgJiZcblx0XHRcdHRoaXMuaXNDb25zdEFzc2VydGlvblR5cGUoY3VycmVudC50eXBlKSkge1xuXHRcdFx0Y29uc3QgaW5uZXIgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0XHRjb25zdCBsaXRlcmFsID0gdHMuaXNBcnJheUxpdGVyYWxFeHByZXNzaW9uKGlubmVyKSA/IGlubmVyIDogdW5kZWZpbmVkO1xuXHRcdFx0cmV0dXJuIGxpdGVyYWw7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudCkpIHtcblx0XHRcdGNvbnN0IHRyYWNrZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChjdXJyZW50LnRleHQpO1xuXHRcdFx0cmV0dXJuIHRyYWNrZWQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRW1pdC10eXBlIGZvciBgdHlwZW9mIG5hbWVgIHdoZW4gYG5hbWVgIGlzIGEgdHJhY2tlZCBjb25zdCBhcnJheTogdGhlXG5cdCAqIHVuaW9uIG9mIGl0cyBlbGVtZW50IGxpdGVyYWwgdHlwZXMgKGAnYWN0aXZlJyB8ICdjbG9zZWQnYCkuIEV2ZXJ5XG5cdCAqIG90aGVyIHR5cGVvZiBzb3VyY2Ug4oCUIG5vbi1hcnJheSBjb25zdHMsIGZ1bmN0aW9ucywgY2xhc3NlcywgbmFtZXMgbm90XG5cdCAqIHRyYWNrZWQgYXQgYWxsIOKAlCB5aWVsZHMgdW5kZWZpbmVkLCBzbyB0aGUgY2FsbGVyIGRlZ3JhZGVzIHRoZSBmaWVsZFxuXHQgKiB0byBgdW5rbm93bmA6IGEgYmFyZSBgdHlwZW9mIG5hbWVgIGVtaXR0ZWQgaW50byB0eXBlcy50cyBoYXMgbm9cblx0ICogaW1wb3J0IHRvIHJlc29sdmUgYWdhaW5zdCBkb3duc3RyZWFtLlxuXHQgKi9cblx0cHJpdmF0ZSB0eXBlT2ZDb25zdEFycmF5VW5pb24gKG5hbWU6IHN0cmluZywgZnJvbUZpbGU6IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJyYXlMaXRlcmFsID0gdGhpcy5maW5kUmVmZXJlbmNlZENvbnN0QXJyYXkobmFtZSwgZnJvbUZpbGUpO1xuXHRcdGlmICghYXJyYXlMaXRlcmFsKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBsaXRlcmFscyA9IHRoaXMubGl0ZXJhbFR5cGVzT2ZBcnJheShhcnJheUxpdGVyYWwpO1xuXHRcdGlmICghbGl0ZXJhbHMpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHVuaW9uID0gbGl0ZXJhbHMuam9pbignIHwgJyk7XG5cdFx0cmV0dXJuIHVuaW9uO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCB0aGUgaW1wb3J0aW5nIGZpbGUncyBuYW1lZC9uYW1lc3BhY2UvZGVmYXVsdCBpbXBvcnQgYmluZGluZ3Mgc29cblx0ICogcmVmZXJlbmNlZC10eXBlIG5hbWVzIHJlc29sdmUgdGhyb3VnaCB0aGUgZmlsZSdzIG93biBpbXBvcnQgc3RhdGVtZW50c1xuXHQgKiAoRjEwKSByYXRoZXIgdGhhbiBhIHByb2dyYW0td2lkZSBuYW1lIG1hcC5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tSZWZlcmVuY2VkVHlwZUltcG9ydCAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNJbXBvcnREZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCB7IG1vZHVsZVNwZWNpZmllciB9ID0gbm9kZTtcblx0XHRpZiAoIXRzLmlzU3RyaW5nTGl0ZXJhbChtb2R1bGVTcGVjaWZpZXIpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGNsYXVzZSA9IG5vZGUuaW1wb3J0Q2xhdXNlO1xuXHRcdGlmICghY2xhdXNlKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0bGV0IGltcG9ydHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoZmlsZVBhdGgpO1xuXHRcdGlmICghaW1wb3J0cykge1xuXHRcdFx0aW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZUltcG9ydD4oKTtcblx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLnNldChmaWxlUGF0aCwgaW1wb3J0cyk7XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0IHsgU2hhcmVkU2hhcGUgfSBmcm9tICfigKYnIC8gaW1wb3J0IHsgU2hhcmVkU2hhcGUgYXMgUyB9IGZyb20gJ+KApidcblx0XHRpZiAoY2xhdXNlLm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lZEltcG9ydHMoY2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2YgY2xhdXNlLm5hbWVkQmluZGluZ3MuZWxlbWVudHMpIHtcblx0XHRcdFx0Y29uc3QgbG9jYWxOYW1lID0gZWxlbWVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IG9yaWdpbmFsTmFtZSA9IGVsZW1lbnQucHJvcGVydHlOYW1lID8gZWxlbWVudC5wcm9wZXJ0eU5hbWUudGV4dCA6IGxvY2FsTmFtZTtcblx0XHRcdFx0aW1wb3J0cy5zZXQobG9jYWxOYW1lLCB7XG5cdFx0XHRcdFx0b3JpZ2luYWxOYW1lLFxuXHRcdFx0XHRcdHNwZWNpZmllciAgIDogbW9kdWxlU3BlY2lmaWVyLnRleHQsXG5cdFx0XHRcdFx0aXNOYW1lc3BhY2UgOiBmYWxzZVxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgKiBhcyBtb2RlbHMgZnJvbSAn4oCmJyDigJQgcmVzb2x2ZWQgd2hlbiBhIHF1YWxpZmllZCBuYW1lXG5cdFx0Ly8gKG1vZGVscy5TaGFyZWRTaGFwZSkgaXMgZW5jb3VudGVyZWRcblx0XHRpZiAoY2xhdXNlLm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lc3BhY2VJbXBvcnQoY2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHRpbXBvcnRzLnNldChjbGF1c2UubmFtZWRCaW5kaW5ncy5uYW1lLnRleHQsIHtcblx0XHRcdFx0b3JpZ2luYWxOYW1lIDogJycsXG5cdFx0XHRcdHNwZWNpZmllciAgICA6IG1vZHVsZVNwZWNpZmllci50ZXh0LFxuXHRcdFx0XHRpc05hbWVzcGFjZSAgOiB0cnVlXG5cdFx0XHR9KTtcblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgU2hhcmVkU2hhcGUgZnJvbSAn4oCmJyAoZGVmYXVsdCBpbXBvcnQpXG5cdFx0aWYgKGNsYXVzZS5uYW1lKSB7XG5cdFx0XHRpbXBvcnRzLnNldChjbGF1c2UubmFtZS50ZXh0LCB7XG5cdFx0XHRcdG9yaWdpbmFsTmFtZSA6ICdkZWZhdWx0Jyxcblx0XHRcdFx0c3BlY2lmaWVyICAgIDogbW9kdWxlU3BlY2lmaWVyLnRleHQsXG5cdFx0XHRcdGlzTmFtZXNwYWNlICA6IGZhbHNlXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIHJlLWV4cG9ydCB3aXJpbmcgKGBleHBvcnQgeyBYIH0gZnJvbSAn4oCmJ2AsIGBleHBvcnQgKiBmcm9tICfigKYnYCxcblx0ICogYGV4cG9ydCB7IFggYXMgWSB9YCkgc28gcmVzb2x1dGlvbiBjYW4gY2hhc2UgYmFycmVscyB0byB0aGUgb3JpZ2luXG5cdCAqIG1vZHVsZS4gTWlycm9ycyBNb2R1bGVHcmFwaEJ1aWxkZXIucmVzb2x2ZU9yaWdpbiwgbmFtZS1iYXNlZCBvbmx5LlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlUmVFeHBvcnQgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzRXhwb3J0RGVjbGFyYXRpb24obm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0Y29uc3QgeyBtb2R1bGVTcGVjaWZpZXIgfSA9IG5vZGU7XG5cdFx0Y29uc3Qgc3BlY2lmaWVyVGV4dCA9IG1vZHVsZVNwZWNpZmllciAmJiB0cy5pc1N0cmluZ0xpdGVyYWwobW9kdWxlU3BlY2lmaWVyKVxuXHRcdFx0PyBtb2R1bGVTcGVjaWZpZXIudGV4dFxuXHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHRpZiAobm9kZS5leHBvcnRDbGF1c2UgJiYgdHMuaXNOYW1lZEV4cG9ydHMobm9kZS5leHBvcnRDbGF1c2UpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2Ygbm9kZS5leHBvcnRDbGF1c2UuZWxlbWVudHMpIHtcblx0XHRcdFx0Y29uc3QgZXhwb3J0ZWROYW1lID0gZWxlbWVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IGxvY2FsTmFtZSA9IGVsZW1lbnQucHJvcGVydHlOYW1lID8gZWxlbWVudC5wcm9wZXJ0eU5hbWUudGV4dCA6IGV4cG9ydGVkTmFtZTtcblx0XHRcdFx0dGhpcy5tYXJrQnVpbGRlckV4cG9ydChleHBvcnRlZE5hbWUsIGxvY2FsTmFtZSwgZmlsZVBhdGgsIHNwZWNpZmllclRleHQpO1xuXHRcdFx0XHRpZiAoc3BlY2lmaWVyVGV4dCkge1xuXHRcdFx0XHRcdC8vIGV4cG9ydCB7IFggfSBmcm9tICfigKYnIC8gZXhwb3J0IHsgWCBhcyBZIH0gZnJvbSAn4oCmJ1xuXHRcdFx0XHRcdGxldCByZUV4cG9ydHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLmdldChmaWxlUGF0aCk7XG5cdFx0XHRcdFx0aWYgKCFyZUV4cG9ydHMpIHtcblx0XHRcdFx0XHRcdHJlRXhwb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLnNldChmaWxlUGF0aCwgcmVFeHBvcnRzKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0cmVFeHBvcnRzLnNldChleHBvcnRlZE5hbWUsIHNwZWNpZmllclRleHQpO1xuXHRcdFx0XHR9IGVsc2UgaWYgKGxvY2FsTmFtZSAhPT0gZXhwb3J0ZWROYW1lKSB7XG5cdFx0XHRcdFx0Ly8gZXhwb3J0IHsgWCBhcyBZIH0g4oCUIHNhbWUtZmlsZSBhbGlhcyBvZiBhIGxvY2FsIGRlY2xhcmF0aW9uXG5cdFx0XHRcdFx0bGV0IGFsaWFzZXMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0XHRcdGlmICghYWxpYXNlcykge1xuXHRcdFx0XHRcdFx0YWxpYXNlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcy5zZXQoZmlsZVBhdGgsIGFsaWFzZXMpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRhbGlhc2VzLnNldChleHBvcnRlZE5hbWUsIGxvY2FsTmFtZSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAobm9kZS5leHBvcnRDbGF1c2UgJiYgdHMuaXNOYW1lc3BhY2VFeHBvcnQobm9kZS5leHBvcnRDbGF1c2UpKSB7XG5cdFx0XHQvLyBgZXhwb3J0ICogYXMgbnMgZnJvbSAn4oCmJ2Ag4oCUIGEgbmVzdGVkIG1vZHVsZSBuYW1lc3BhY2U7IG1pZGRsZVxuXHRcdFx0Ly8gc2VnbWVudHMgb2YgcXVhbGlmaWVkIHJlZmVyZW5jZXMgKGJhcnJlbC5EZWVwLkdhZGdldCkgY2hhc2UgaXRcblx0XHRcdGlmIChzcGVjaWZpZXJUZXh0KSB7XG5cdFx0XHRcdGxldCBzdGFycyA9IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VTdGFycy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0XHRpZiAoIXN0YXJzKSB7XG5cdFx0XHRcdFx0c3RhcnMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VTdGFycy5zZXQoZmlsZVBhdGgsIHN0YXJzKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRzdGFycy5zZXQobm9kZS5leHBvcnRDbGF1c2UubmFtZS50ZXh0LCBzcGVjaWZpZXJUZXh0KTtcblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAoIW5vZGUuZXhwb3J0Q2xhdXNlICYmIHNwZWNpZmllclRleHQpIHtcblx0XHRcdC8vIGV4cG9ydCAqIGZyb20gJ+KApidcblx0XHRcdGxldCBzdGFycyA9IHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0aWYgKCFzdGFycykge1xuXHRcdFx0XHRzdGFycyA9IFtdO1xuXHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuc2V0KGZpbGVQYXRoLCBzdGFycyk7XG5cdFx0XHR9XG5cdFx0XHRzdGFycy5wdXNoKHNwZWNpZmllclRleHQpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgbW9kdWxlIHNwZWNpZmllciBmcm9tIGEgY29udGFpbmluZyBmaWxlIHdpdGggdGhlIHByb2dyYW0nc1xuXHQgKiBjb21waWxlck9wdGlvbnMgKHRzY29uZmlnIGBwYXRoc2AsIGV4dGVuc2lvbmxlc3MgaW1wb3J0cywgaW5kZXggZmlsZXMpLlxuXHQgKiBNb2R1bGUgcmVzb2x1dGlvbiBvbmx5IOKAlCB0aGUgbm8tZ2V0VHlwZUNoZWNrZXIoKSBwcmVjZWRlbnQgc3RheXMuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZSAoc3BlY2lmaWVyOiBzdHJpbmcsIGNvbnRhaW5pbmdGaWxlOiBzdHJpbmcpOlxuXHRcdFJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2FjaGVLZXkgPSBgJHtjb250YWluaW5nRmlsZX06OiR7c3BlY2lmaWVyfWA7XG5cdFx0aWYgKHRoaXMucmVmZXJlbmNlZFR5cGVSZXNvbHV0aW9uQ2FjaGUuaGFzKGNhY2hlS2V5KSkge1xuXHRcdFx0Y29uc3QgY2FjaGVkID0gdGhpcy5yZWZlcmVuY2VkVHlwZVJlc29sdXRpb25DYWNoZS5nZXQoY2FjaGVLZXkpO1xuXHRcdFx0cmV0dXJuIGNhY2hlZCA9PT0gdW5kZWZpbmVkID8gdW5kZWZpbmVkIDogY2FjaGVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlc29sdXRpb24gPSB0cy5yZXNvbHZlTW9kdWxlTmFtZShcblx0XHRcdHNwZWNpZmllcixcblx0XHRcdGNvbnRhaW5pbmdGaWxlLFxuXHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUNvbXBpbGVyT3B0aW9ucyxcblx0XHRcdHRzLnN5c1xuXHRcdCkucmVzb2x2ZWRNb2R1bGU7XG5cblx0XHRjb25zdCByZXN1bHQ6IFJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbiB8IHVuZGVmaW5lZCA9IHJlc29sdXRpb25cblx0XHRcdD8ge1xuXHRcdFx0XHRyZXNvbHZlZFBhdGggOiBub2RlUGF0aC5yZXNvbHZlKHJlc29sdXRpb24ucmVzb2x2ZWRGaWxlTmFtZSksXG5cdFx0XHRcdGlzRXh0ZXJuYWwgICA6ICEhcmVzb2x1dGlvbi5pc0V4dGVybmFsTGlicmFyeUltcG9ydFxuXHRcdFx0fVxuXHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbkNhY2hlLnNldChjYWNoZUtleSwgcmVzdWx0KTtcblx0XHRjb25zdCBmaW5hbFJlc3VsdCA9IHJlc3VsdDtcblx0XHRyZXR1cm4gZmluYWxSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogTG9vayB1cCBhIG5hbWUgaW4gb25lIHJlc29sdmVkIG1vZHVsZSwgY2hhc2luZyByZS1leHBvcnQgYmFycmVscyB3aXRoIGFcblx0ICogYm91bmRlZCBkZXB0aC4gRXh0ZXJuYWwgKG5vZGVfbW9kdWxlcykgbW9kdWxlcyBob2xkIG5vIGluLXByb2plY3Rcblx0ICogZGVjbGFyYXRpb25zIGFuZCBzdG9wIHRoZSBjaGFzZS5cblx0ICovXG5cdHByaXZhdGUgZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUgKFxuXHRcdG1vZHVsZVBhdGg6IHN0cmluZyxcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0ZGVwdGg6IG51bWJlclxuXHQpOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoZGVwdGggPiBNQVhfUkVFWFBPUlRfQ0hBU0VfREVQVEgpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGVjbHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRGVjbHMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGNvbnN0IGRpcmVjdCA9IGRlY2xzPy5nZXQobmFtZSk7XG5cdFx0aWYgKGRpcmVjdCkge1xuXHRcdFx0cmV0dXJuIGRpcmVjdDtcblx0XHR9XG5cdFx0Ly8gZXhwb3J0IHsgWCBhcyBZIH0g4oCUIHJlc29sdmUgdGhyb3VnaCB0aGUgbG9jYWwgbmFtZVxuXHRcdGNvbnN0IGxvY2FsQWxpYXMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcy5nZXQobW9kdWxlUGF0aCk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWxBbGlhcykge1xuXHRcdFx0Y29uc3QgYWxpYXNlZCA9IGRlY2xzPy5nZXQobG9jYWxBbGlhcyk7XG5cdFx0XHRpZiAoYWxpYXNlZCkge1xuXHRcdFx0XHRyZXR1cm4gYWxpYXNlZDtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCByZUV4cG9ydHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLmdldChtb2R1bGVQYXRoKTtcblx0XHRjb25zdCByZUV4cG9ydFNwZWNpZmllciA9IHJlRXhwb3J0cz8uZ2V0KG5hbWUpO1xuXHRcdGlmIChyZUV4cG9ydFNwZWNpZmllcikge1xuXHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShyZUV4cG9ydFNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRpZiAobmV4dFJlc29sdXRpb24gJiYgIW5leHRSZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgbmFtZSwgZGVwdGggKyAxKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGlmIChzdGFycykge1xuXHRcdFx0Zm9yIChjb25zdCBzdGFyU3BlY2lmaWVyIG9mIHN0YXJzKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoc3RhclNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRcdGlmICghbmV4dFJlc29sdXRpb24gfHwgbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZShuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIG5hbWUsIGRlcHRoICsgMSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHJlZmVyZW5jZWQgdHlwZSBuYW1lIGFzIHVzZWQgaW4gZnJvbUZpbGUsIGltcG9ydC1hd2FyZTpcblx0ICogICAxLiB0aGUgZmlsZSdzIG93biBpbXBvcnQgc3RhdGVtZW50cyAocmVsYXRpdmUgKyB0c2NvbmZpZyBwYXRocyxcblx0ICogICAgICBjaGFzZWQgdGhyb3VnaCByZS1leHBvcnQgYmFycmVscyksXG5cdCAqICAgMi4gdGhlIGZpbGUncyBsb2NhbCBkZWNsYXJhdGlvbnMsXG5cdCAqICAgMy4gdGhlIHVuaXF1ZSBzYW1lLW5hbWVkIGRlY2xhcmF0aW9uIGFjcm9zcyBzY2FubmVkIGZpbGVzLlxuXHQgKiBSZXR1cm5zIHVuZGVmaW5lZCB3aGVuIG5vdGhpbmcgbWF0Y2hlcyAob3IgdGhlIG1hdGNoIGlzIGFtYmlndW91cyksXG5cdCAqIGluIHdoaWNoIGNhc2UgdGhlIGNhbGxlciBmYWxscyBiYWNrIHRvIGB1bmtub3duYC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRmcm9tRmlsZTogc3RyaW5nXG5cdCk6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdC8vIDEuIHRoZSBmaWxlJ3Mgb3duIGltcG9ydHMgd2luIOKAlCBhbiBpbXBvcnQgaXMgbmV2ZXIgc2hhZG93ZWQgYnkgYVxuXHRcdC8vIHNhbWUtbmFtZWQgbG9jYWwgZGVjbGFyYXRpb24gZWxzZXdoZXJlIGluIHRoZSBwcm9ncmFtIChGMTApXG5cdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoZnJvbUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGltcG9ydGVkICYmICFpbXBvcnRlZC5pc05hbWVzcGFjZSkge1xuXHRcdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKGltcG9ydGVkLnNwZWNpZmllciwgZnJvbUZpbGUpO1xuXHRcdFx0aWYgKHJlc29sdXRpb24gJiYgIXJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRjb25zdCBmb3VuZCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUocmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIGltcG9ydGVkLm9yaWdpbmFsTmFtZSwgMCk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIDIuIGxvY2FsIGRlY2xhcmF0aW9uIGluIHRoZSByZWZlcmVuY2luZyBmaWxlIGl0c2VsZlxuXHRcdGNvbnN0IGxvY2FsID0gdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLmdldChmcm9tRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWwpIHtcblx0XHRcdHJldHVybiBsb2NhbDtcblx0XHR9XG5cblx0XHQvLyAzLiBwcm9ncmFtLXdpZGUgZmFsbGJhY2ssIHVuaXF1ZSBkZWNsYXJhdGlvbiBvbmx5IOKAlCBhbWJpZ3VpdHkgYW5kXG5cdFx0Ly8gYWJzZW5jZSBib3RoIHlpZWxkIHVuZGVmaW5lZCAodGhlIGNhbGxlciBlbWl0cyBgdW5rbm93bmApLlxuXHRcdC8vIEV4dGVybmFsL2FtYmllbnQgZGVjbGFyYXRpb25zICguZC50cywgbm9kZV9tb2R1bGVzKSBkbyBub3Rcblx0XHQvLyBwYXJ0aWNpcGF0ZTogYSB1c2VyLWxvY2FsIGRlY2xhcmF0aW9uIGFsd2F5cyB3aW5zIG92ZXIgYVxuXHRcdC8vIHBhY2thZ2UtZGVjbGFyZWQgc2FtZS1uYW1lZCB0eXBlICh0aGUgcGxhaW4tVFMgdGllciBvZiB0aGVcblx0XHQvLyBpZGVudGl0eSBsYXc7IGFtYmlndWl0eSBhbW9uZyB0aGUgcmVtYWluaW5nIGRlY2xhcmF0aW9ucyBpc1xuXHRcdC8vIHZhbGlkYXRlZCBzZXBhcmF0ZWx5IGFzIGEgaGFyZCBmYWlsKVxuXHRcdGxldCB1bmlxdWU6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQ7XG5cdFx0bGV0IGNvdW50ID0gMDtcblx0XHRmb3IgKGNvbnN0IFsgZmlsZVBhdGgsIGRlY2xzIF0gb2YgdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzKSB7XG5cdFx0XHRpZiAodGhpcy5pc0V4dGVybmFsRGVjbEZpbGUoZmlsZVBhdGgpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgY2FuZGlkYXRlID0gZGVjbHMuZ2V0KG5hbWUpO1xuXHRcdFx0aWYgKGNhbmRpZGF0ZSkge1xuXHRcdFx0XHRjb3VudCsrO1xuXHRcdFx0XHR1bmlxdWUgPSBjYW5kaWRhdGU7XG5cdFx0XHRcdGlmIChjb3VudCA+IDEpIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVzdWx0ID0gY291bnQgPT09IDEgPyB1bmlxdWUgOiB1bmRlZmluZWQ7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRlcm5hbC9hbWJpZW50IGRlY2xhcmF0aW9uIGZpbGVzICguZC50cywgYW55dGhpbmcgdW5kZXJcblx0ICogbm9kZV9tb2R1bGVzKSBuZXZlciBwYXJ0aWNpcGF0ZSBpbiBwbGFpbi1UUyByZWZlcmVuY2VkLXR5cGVcblx0ICogcmVzb2x1dGlvbiBvciB0aGUgYW1iaWd1aXR5IGxhdzogdGhleSBhcmUgbm90IHByb2plY3Qgc291cmNlLCB0aGVcblx0ICogQ0xJIG5ldmVyIGFuYWx5emVzIHRoZW0sIGFuZCBhIHVzZXItbG9jYWwgZGVjbGFyYXRpb24gYWx3YXlzIHdpbnNcblx0ICogb3ZlciBhIHBhY2thZ2UtZGVjbGFyZWQgc2FtZS1uYW1lZCB0eXBlLlxuXHQgKi9cblx0cHJpdmF0ZSBpc0V4dGVybmFsRGVjbEZpbGUgKGZpbGU6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRcdGNvbnN0IGV4dGVybmFsID0gZmlsZS5lbmRzV2l0aCgnLmQudHMnKSB8fFxuXHRcdFx0ZmlsZS5pbmNsdWRlcyhgJHtub2RlUGF0aC5zZXB9bm9kZV9tb2R1bGVzJHtub2RlUGF0aC5zZXB9YCk7XG5cdFx0cmV0dXJuIGV4dGVybmFsO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb3BlcnRpZXMgb2YgYSByZWZlcmVuY2VkIGNsYXNzL2ludGVyZmFjZS9hbGlhcy1vZi1saXRlcmFsIGRlY2xhcmF0aW9uLFxuXHQgKiBzaGFyZWQgYnkgYHRoaXM6YC1wYXJhbWV0ZXIgZXhwYW5zaW9uIGFuZCBpbmxpbmUgdHlwZSBlbWlzc2lvbi5cblx0ICogSW5oZXJpdGVkIG1lbWJlcnMgYXJlIGluY2x1ZGVkOiB0aGUgZXh0ZW5kcyBjaGFpbiBpcyB3YWxrZWRcblx0ICogKGRlcHRoLWNhcHBlZCwgY3ljbGUtZ3VhcmRlZCkgYW5kIHBhcmVudCBmaWVsZHMgbWVyZ2UgZmlyc3QsIHRoZVxuXHQgKiBkZWNsYXJhdGlvbidzIG93biBmaWVsZHMgb3ZlcnJpZGluZyBvbiBuYW1lIGNsYXNoLlxuXHQgKi9cblx0cHJpdmF0ZSByZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzIChkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKTpcblx0XHRNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCB2aXNpdGVkID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllc0lubmVyKGRlY2wsIHZpc2l0ZWQsIDApO1xuXHRcdHJldHVybiBwcm9wZXJ0aWVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpZWxkcyBvZiBvbmUgbWVtYmVyIG9mIGFuIGludGVyc2VjdGlvbiBhbGlhczogYW4gaW5saW5lIGxpdGVyYWwsIG9yXG5cdCAqIGEgbmFtZWQgdHlwZSByZXNvbHZlZCBpbXBvcnQtYXdhcmUgZnJvbSB0aGUgZmlsZSBkZWNsYXJpbmcgdGhlIGFsaWFzLlxuXHQgKiBBIG1lbWJlciB0aGF0IGRvZXMgbm90IHJlc29sdmUgKGEgZ2VuZXJhdGVkIHR5cGUgbm90IHdyaXR0ZW4geWV0LCBhblxuXHQgKiBleHRlcm5hbCB0eXBlKSBhZGRzIG5vdGhpbmcuXG5cdCAqL1xuXHRwcml2YXRlIGludGVyc2VjdGlvbk1lbWJlclByb3BlcnRpZXMgKFxuXHRcdG1lbWJlcjogdHMuVHlwZU5vZGUsXG5cdFx0ZnJvbUZpbGU6IHN0cmluZyxcblx0XHR2aXNpdGVkOiBTZXQ8c3RyaW5nPixcblx0XHRkZXB0aDogbnVtYmVyXG5cdCk6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXHRcdGlmICh0cy5pc1BhcmVudGhlc2l6ZWRUeXBlTm9kZShtZW1iZXIpKSB7XG5cdFx0XHRjb25zdCBpbm5lciA9IHRoaXMuaW50ZXJzZWN0aW9uTWVtYmVyUHJvcGVydGllcyhtZW1iZXIudHlwZSwgZnJvbUZpbGUsIHZpc2l0ZWQsIGRlcHRoKTtcblx0XHRcdHJldHVybiBpbm5lcjtcblx0XHR9XG5cdFx0aWYgKHRzLmlzVHlwZUxpdGVyYWxOb2RlKG1lbWJlcikpIHtcblx0XHRcdHRoaXMuY29sbGVjdFR5cGVFbGVtZW50UHJvcGVydGllcyhbIC4uLm1lbWJlci5tZW1iZXJzIF0sIHByb3BlcnRpZXMpO1xuXHRcdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci50eXBlTmFtZSkpIHtcblx0XHRcdGNvbnN0IG1lbWJlckRlY2wgPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKG1lbWJlci50eXBlTmFtZS50ZXh0LCBmcm9tRmlsZSk7XG5cdFx0XHRpZiAobWVtYmVyRGVjbCkge1xuXHRcdFx0XHRjb25zdCByZXNvbHZlZCA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllc0lubmVyKG1lbWJlckRlY2wsIHZpc2l0ZWQsIGRlcHRoKTtcblx0XHRcdFx0cmV0dXJuIHJlc29sdmVkO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdHByaXZhdGUgcmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllc0lubmVyIChcblx0XHRkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uLFxuXHRcdHZpc2l0ZWQ6IFNldDxzdHJpbmc+LFxuXHRcdGRlcHRoOiBudW1iZXJcblx0KTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3Qgb3duUHJvcGVydGllcyA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cdFx0Y29uc3QgZGVjbE5vZGUgPSBkZWNsLm5vZGUgYXMgdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHRzLkludGVyZmFjZURlY2xhcmF0aW9uO1xuXHRcdGNvbnN0IGRlY2xOYW1lID0gZGVjbE5vZGUubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIoZGVjbE5vZGUubmFtZSkgPyBkZWNsTm9kZS5uYW1lLnRleHQgOiAnJztcblx0XHRjb25zdCB2aXNpdEtleSA9IGAke2RlY2wua2luZH06JHtkZWNsLmZpbGV9OiR7ZGVjbE5hbWV9YDtcblx0XHRpZiAoZGVwdGggPiBNQVhfSEVSSVRBR0VfREVQVEggfHwgdmlzaXRlZC5oYXModmlzaXRLZXkpKSB7XG5cdFx0XHRyZXR1cm4gb3duUHJvcGVydGllcztcblx0XHR9XG5cdFx0dmlzaXRlZC5hZGQodmlzaXRLZXkpO1xuXG5cdFx0aWYgKGRlY2wua2luZCA9PT0gJ2NsYXNzJykge1xuXHRcdFx0Y29uc3QgY2xhc3NQcm9wcyA9IHRoaXMuZXh0cmFjdENsYXNzUHJvcGVydGllcyhkZWNsLm5vZGUgYXMgdHMuQ2xhc3NEZWNsYXJhdGlvbik7XG5cdFx0XHRmb3IgKGNvbnN0IFsgbmFtZSwgaW5mbyBdIG9mIGNsYXNzUHJvcHMpIHtcblx0XHRcdFx0b3duUHJvcGVydGllcy5zZXQobmFtZSwgaW5mbyk7XG5cdFx0XHR9XG5cdFx0fSBlbHNlIGlmIChkZWNsLmtpbmQgPT09ICdpbnRlcmZhY2UnKSB7XG5cdFx0XHRjb25zdCBpZmFjZSA9IGRlY2wubm9kZSBhcyB0cy5JbnRlcmZhY2VEZWNsYXJhdGlvbjtcblx0XHRcdHRoaXMuY29sbGVjdFR5cGVFbGVtZW50UHJvcGVydGllcyhbIC4uLmlmYWNlLm1lbWJlcnMgXSwgb3duUHJvcGVydGllcyk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdGNvbnN0IGFsaWFzVHlwZSA9IChkZWNsLm5vZGUgYXMgdHMuVHlwZUFsaWFzRGVjbGFyYXRpb24pLnR5cGU7XG5cdFx0XHRpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUoYWxpYXNUeXBlKSkge1xuXHRcdFx0XHR0aGlzLmNvbGxlY3RUeXBlRWxlbWVudFByb3BlcnRpZXMoWyAuLi5hbGlhc1R5cGUubWVtYmVycyBdLCBvd25Qcm9wZXJ0aWVzKTtcblx0XHRcdH0gZWxzZSBpZiAodHMuaXNJbnRlcnNlY3Rpb25UeXBlTm9kZShhbGlhc1R5cGUpKSB7XG5cdFx0XHRcdC8vIGFuIGludGVyc2VjdGlvbiBhbGlhcyBjYXJyaWVzIGV2ZXJ5IG1lbWJlcidzIGZpZWxkczsgYSBsYXRlclxuXHRcdFx0XHQvLyBtZW1iZXIgb3ZlcnJpZGVzIGFuIGVhcmxpZXIgb25lIG9uIG5hbWUgY2xhc2hcblx0XHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgYWxpYXNUeXBlLnR5cGVzKSB7XG5cdFx0XHRcdFx0Y29uc3QgbWVtYmVyUHJvcHMgPSB0aGlzLmludGVyc2VjdGlvbk1lbWJlclByb3BlcnRpZXMobWVtYmVyLCBkZWNsLmZpbGUsIHZpc2l0ZWQsIGRlcHRoICsgMSk7XG5cdFx0XHRcdFx0Zm9yIChjb25zdCBbIG5hbWUsIGluZm8gXSBvZiBtZW1iZXJQcm9wcykge1xuXHRcdFx0XHRcdFx0b3duUHJvcGVydGllcy5zZXQobmFtZSwgaW5mbyk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRyZXR1cm4gb3duUHJvcGVydGllcztcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBoZXJpdGFnZSBtZXJnZXMgcGFyZW50IGZpZWxkcyBmaXJzdDsgdGhlIGRlY2xhcmF0aW9uJ3Mgb3duIGZpZWxkc1xuXHRcdC8vIG92ZXJyaWRlIG9uIG5hbWUgY2xhc2ggKGxhdGVyIGJhc2VzIG92ZXJyaWRlIGVhcmxpZXIgb25lcylcblx0XHRjb25zdCBtZXJnZWQgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXHRcdGZvciAoY29uc3QgYmFzZURlY2wgb2YgdGhpcy5yZXNvbHZlSGVyaXRhZ2VEZWNsYXJhdGlvbnMoZGVjbCkpIHtcblx0XHRcdGNvbnN0IGJhc2VQcm9wcyA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllc0lubmVyKGJhc2VEZWNsLCB2aXNpdGVkLCBkZXB0aCArIDEpO1xuXHRcdFx0Zm9yIChjb25zdCBbIG5hbWUsIGluZm8gXSBvZiBiYXNlUHJvcHMpIHtcblx0XHRcdFx0bWVyZ2VkLnNldChuYW1lLCBpbmZvKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0Zm9yIChjb25zdCBbIG5hbWUsIGluZm8gXSBvZiBvd25Qcm9wZXJ0aWVzKSB7XG5cdFx0XHRtZXJnZWQuc2V0KG5hbWUsIGluZm8pO1xuXHRcdH1cblx0XHRyZXR1cm4gbWVyZ2VkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb3BlcnR5IHNpZ25hdHVyZXMgb2YgaW50ZXJmYWNlL2FsaWFzIHR5cGUtbGl0ZXJhbCBtZW1iZXJzLCBpbnRvXG5cdCAqIHRoZSBnaXZlbiBtYXAuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RUeXBlRWxlbWVudFByb3BlcnRpZXMgKFxuXHRcdG1lbWJlcnM6IHJlYWRvbmx5IHRzLlR5cGVFbGVtZW50W10sXG5cdFx0cHJvcGVydGllczogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPlxuXHQpOiB2b2lkIHtcblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBtZW1iZXJzKSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChwcm9wTmFtZSwge1xuXHRcdFx0XHRcdG5hbWUgICAgIDogcHJvcE5hbWUsXG5cdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHRoZSBoZXJpdGFnZSBjbGF1c2Ugb2YgYSBjbGFzcyAoYGV4dGVuZHMgQmFzZWApIG9yIGludGVyZmFjZVxuXHQgKiAoYGV4dGVuZHMgQSwgQmApIHRvIHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbnMgdGhyb3VnaCB0aGUgU0FNRVxuXHQgKiBpbXBvcnQtYXdhcmUgbWFjaGluZXJ5IGFzIHBsYWluIHJlZmVyZW5jZXMgKHRoZSBkZWNsYXJpbmcgZmlsZSdzIG93blxuXHQgKiBpbXBvcnRzIGZpcnN0LCB0aGVuIGl0cyBsb2NhbHMsIHRoZW4gdGhlIHVuaXF1ZSBwcm9ncmFtLXdpZGVcblx0ICogZGVjbGFyYXRpb24pLiBVbnJlc29sdmFibGUgb3IgZXh0ZXJuYWwgYmFzZXMgeWllbGQgbm90aGluZyDigJQgdGhlaXJcblx0ICogaW5oZXJpdGVkIGZpZWxkcyBzaW1wbHkgc3RheSBhYnNlbnQsIHNhbWUgYXMgYmVmb3JlIHRoaXMgd2Fsa1xuXHQgKiBleGlzdGVkLiBNaXhpbiBjYWxscyAoYGV4dGVuZHMgbWl4aW4oWClgKSBhbmQgbmFtZXNwYWNlIGFjY2VzcyBhcmVcblx0ICogbm90IGZvbGxvd2VkLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlSGVyaXRhZ2VEZWNsYXJhdGlvbnMgKGRlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24pOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uW10ge1xuXHRcdGNvbnN0IHsgaGVyaXRhZ2VDbGF1c2VzIH0gPSAoZGVjbC5ub2RlIGFzIHRzLkNsYXNzRGVjbGFyYXRpb24gfCB0cy5JbnRlcmZhY2VEZWNsYXJhdGlvbik7XG5cdFx0aWYgKCFoZXJpdGFnZUNsYXVzZXMpIHtcblx0XHRcdHJldHVybiBbXTtcblx0XHR9XG5cdFx0Y29uc3QgYmFzZXM6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25bXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgY2xhdXNlIG9mIGhlcml0YWdlQ2xhdXNlcykge1xuXHRcdFx0aWYgKGNsYXVzZS50b2tlbiAhPT0gdHMuU3ludGF4S2luZC5FeHRlbmRzS2V5d29yZCkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3QgaGVyaXRhZ2VUeXBlIG9mIGNsYXVzZS50eXBlcykge1xuXHRcdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihoZXJpdGFnZVR5cGUuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBiYXNlTmFtZSA9IGhlcml0YWdlVHlwZS5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRcdGNvbnN0IGJhc2VEZWNsID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihiYXNlTmFtZSwgZGVjbC5maWxlKTtcblx0XHRcdFx0aWYgKGJhc2VEZWNsKSB7XG5cdFx0XHRcdFx0YmFzZXMucHVzaChiYXNlRGVjbCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gYmFzZXM7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHBhbmQgYSByZWZlcmVuY2VkLXR5cGUgZGVjbGFyYXRpb24gdG8gYSBzZWxmLWNvbnRhaW5lZCB0eXBlIHN0cmluZ1xuXHQgKiBmb3IgZW1pc3Npb24gaW50byBnZW5lcmF0ZWQgZmlsZXM6IHR5cGUgYWxpYXNlcyB0aHJvdWdoIGluZmVyVHlwZSxcblx0ICogY2xhc3NlcyBhbmQgaW50ZXJmYWNlcyB0aHJvdWdoIHRoZWlyIChwdWJsaWMsIG5vbi1tZXRob2QpIGZpZWxkcy5cblx0ICogTmVzdGVkIHJlZmVyZW5jZXMgcmVzb2x2ZSBhZ2FpbnN0IHRoZSBkZWNsYXJpbmcgZmlsZSB3aGlsZSBleHBhbmRpbmcuXG5cdCAqL1xuXHRwcml2YXRlIGV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gKGRlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IHJlZmVyZW5jaW5nRmlsZSA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSBkZWNsLmZpbGU7XG5cdFx0dHJ5IHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMuZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbklubmVyKGRlY2wpO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gcmVmZXJlbmNpbmdGaWxlO1xuXHRcdH1cblx0fVxuXG5cdHByaXZhdGUgZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbklubmVyIChkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoZGVjbC5raW5kID09PSAnYWxpYXMnKSB7XG5cdFx0XHRjb25zdCBhbGlhc05vZGUgPSBkZWNsLm5vZGUgYXMgdHMuVHlwZUFsaWFzRGVjbGFyYXRpb247XG5cdFx0XHRjb25zdCBhbGlhc05hbWUgPSB0cy5pc0lkZW50aWZpZXIoYWxpYXNOb2RlLm5hbWUpID8gYWxpYXNOb2RlLm5hbWUudGV4dCA6ICcnO1xuXHRcdFx0aWYgKGFsaWFzTmFtZSAmJiB0aGlzLmV4cGFuZGluZ1JlZmVyZW5jZWRBbGlhc2VzLmhhcyhhbGlhc05hbWUpKSB7XG5cdFx0XHRcdC8vIFNlbGYtcmVmZXJlbnRpYWwgYWxpYXMgY2hhaW4g4oCUIGJhaWwgb3V0XG5cdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHR9XG5cdFx0XHRpZiAoYWxpYXNOYW1lKSB7XG5cdFx0XHRcdHRoaXMuZXhwYW5kaW5nUmVmZXJlbmNlZEFsaWFzZXMuYWRkKGFsaWFzTmFtZSk7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMuaW5mZXJUeXBlKGFsaWFzTm9kZS50eXBlKTtcblx0XHRcdGlmIChhbGlhc05hbWUpIHtcblx0XHRcdFx0dGhpcy5leHBhbmRpbmdSZWZlcmVuY2VkQWxpYXNlcy5kZWxldGUoYWxpYXNOYW1lKTtcblx0XHRcdH1cblx0XHRcdHJldHVybiBleHBhbmRlZDtcblx0XHR9XG5cblx0XHRjb25zdCBkZWNsUHJvcGVydGllcyA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllcyhkZWNsKTtcblx0XHRjb25zdCBwcm9wcyA9IEFycmF5LmZyb20oZGVjbFByb3BlcnRpZXMuZW50cmllcygpKS5tYXAoKFsgcHJvcE5hbWUsIGluZm8gXSkgPT4ge1xuXHRcdFx0Y29uc3Qgb3B0aW9uYWwgPSBpbmZvLm9wdGlvbmFsID8gJz8nIDogJyc7XG5cdFx0XHRyZXR1cm4gYCR7cHJvcE5hbWV9JHtvcHRpb25hbH06ICR7aW5mby50eXBlfWA7XG5cdFx0fSk7XG5cblx0XHRjb25zdCByZXN1bHQgPSBgeyAke3Byb3BzLmpvaW4oJzsgJyl9IH1gO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRW1pdHRlZCBpbnN0YW5jZS10eXBlIGFsaWFzIGZvciBhIGdyYXBoIG5vZGUg4oCUIHRoZSBuYW1lIHR5cGVzLnRzIC9cblx0ICogcmVnaXN0cnkudHMgYWN0dWFsbHkgZGVjbGFyZS4gT3B0aW9uIEIgY29sbGVjdGlvbiB0eXBlcyBjYXJyeSB0aGVpclxuXHQgKiByZWdpc3RyeSBpbnRlcmZhY2UgcHJlZml4OyBjb2xsZWN0aW9uIHR5cGVzIFdJVEhPVVQgYSByZWdpc3RyeVxuXHQgKiBpbnRlcmZhY2UgYXJlIG5ldmVyIGVtaXR0ZWQsIHNvIG5vIHZhbGlkIGFsaWFzIGV4aXN0cyBmb3IgdGhlbVxuXHQgKiAodW5kZWZpbmVkIOKAlCBjYWxsZXJzIGRlZ3JhZGUgdG8gYHVua25vd25gLCBuZXZlciBhIGJhcmUgbmFtZSkuXG5cdCAqL1xuXHRwcml2YXRlIGdldEVtaXR0ZWRJbnN0YW5jZVR5cGVOYW1lIChub2RlOiBUeXBlTm9kZSk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKG5vZGUuY29sbGVjdGlvbklkICYmICFub2RlLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgZG90dGVkID0gbm9kZS5jb2xsZWN0aW9uSWRcblx0XHRcdD8gbm9kZS5mdWxsUGF0aC5zbGljZShub2RlLmNvbGxlY3Rpb25JZC5sZW5ndGggKyAyKVxuXHRcdFx0OiBub2RlLmZ1bGxQYXRoO1xuXHRcdGNvbnN0IHByZWZpeCA9IG5vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lID8gYCR7bm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWV9X2AgOiAnJztcblx0XHRjb25zdCByZXN1bHQgPSBgJHtwcmVmaXh9JHtkb3R0ZWQucmVwbGFjZSgvXFwuL2csICdfJyl9YDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSBzaW1wbGUgKG5vbi1xdWFsaWZpZWQpIHR5cGUgcmVmZXJlbmNlOiBpbXBvcnQtYXdhcmVcblx0ICogZGVjbGFyYXRpb24gZXhwYW5zaW9uIGZpcnN0LCB0aGVuIHRoZSBJbnN0YW5jZVR5cGU8dHlwZW9mIFg+IHBhdHRlcm4sXG5cdCAqIHRoZW4gbW5lbW9uaWNhIGdyYXBoIHR5cGVzOyBrbm93biBnbG9iYWxzIGtlZXAgdGhlaXIgYmFyZSBuYW1lIGFuZFxuXHQgKiBhbnl0aGluZyBlbHNlIGZhbGxzIGJhY2sgdG8gYHVua25vd25gIHNvIGdlbmVyYXRlZCBmaWxlcyBuZXZlciBjYXJyeVxuXHQgKiBhbiB1bnJlc29sdmFibGUgYmFyZSBuYW1lLiBSZXR1cm5zIHVuZGVmaW5lZCB3aGVuIHRoZSBjYWxsZXIgc2hvdWxkXG5cdCAqIGtlZXAgdGhlIGdlbmVyaWMgc3BlbGxpbmcgKGhhbmRsZWQgc2VwYXJhdGVseSkuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVTaW1wbGVUeXBlUmVmZXJlbmNlIChcblx0XHR0eXBlTmFtZTogc3RyaW5nLFxuXHRcdHR5cGVBcmdzPzogdHMuTm9kZUFycmF5PHRzLlR5cGVOb2RlPixcblx0XHRyZWZOb2RlPzogdHMuTm9kZVxuXHQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdC8vIEltcG9ydC1hd2FyZSByZWZlcmVuY2VkLXR5cGUgZGVjbGFyYXRpb24gKEYxMClcblx0XHRjb25zdCBkZWNsID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbih0eXBlTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRpZiAoZGVjbCkge1xuXHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oZGVjbCk7XG5cdFx0XHRpZiAoZXhwYW5kZWQgIT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRyZXR1cm4gZXhwYW5kZWQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCB1bmtub3duUmVzdWx0ID0gJ3Vua25vd24nO1xuXHRcdFx0cmV0dXJuIHVua25vd25SZXN1bHQ7XG5cdFx0fVxuXG5cdFx0Ly8gSW5zdGFuY2VUeXBlPHR5cGVvZiBYPiBsYXcgKDAuMi4wIGJlaGF2aW9yLCByZXN0b3JlZCk6IHRoZVxuXHRcdC8vIGdlbmVyYXRlZCBhbGlhcyBhbHJlYWR5IElTIHRoZSBpbnN0YW5jZSB0eXBlIOKAlCByZXNvbHZlIFggdGhyb3VnaFxuXHRcdC8vIHRoZSBncmFwaCB0aWVycyBhbmQgZHJvcCB0aGUgd3JhcHBlci4gTXVzdCBydW4gQkVGT1JFIHRoZSBncmFwaFxuXHRcdC8vIHJlc29sdXRpb246ICdJbnN0YW5jZVR5cGUnIGlzIGFuIGFtYmllbnQgZ2xvYmFsLCBuZXZlciBhIGdyYXBoXG5cdFx0Ly8gdHlwZSAodGhlIG9sZCBzcGVjaWFsIGNhc2UgYmVsb3cgc2F0IGluc2lkZSB0aGUgZ3JhcGgtdW5pcXVlXG5cdFx0Ly8gYnJhbmNoIGFuZCB3YXMgZGVhZCBjb2RlKS4gV2hlbiBYIGRvZXMgbm90IHJlc29sdmUsIHRoZSBXSE9MRVxuXHRcdC8vIGV4cHJlc3Npb24gZGVncmFkZXMgdG8gYHVua25vd25gIOKAlCBuZXZlciBlbWl0XG5cdFx0Ly8gYEluc3RhbmNlVHlwZTx1bmtub3duPmA6IGludmFsaWQgVFMgKFRTMjM0NCwgJ3Vua25vd24nIGRvZXMgbm90XG5cdFx0Ly8gc2F0aXNmeSB0aGUgY29uc3RydWN0b3IgY29uc3RyYWludCkuIFJlYWNoZWQgZGlyZWN0bHkgb3IgdGhyb3VnaFxuXHRcdC8vIGEgbG9jYWwgYWxpYXMgKGBYSW5zdGFuY2UgPSBJbnN0YW5jZVR5cGU8dHlwZW9mIFg+YCkuXG5cdFx0aWYgKHR5cGVOYW1lID09PSAnSW5zdGFuY2VUeXBlJyAmJiB0eXBlQXJncyAmJiB0eXBlQXJncy5sZW5ndGggPT09IDEpIHtcblx0XHRcdGNvbnN0IFsgaW5zdGFuY2VBcmcgXSA9IHR5cGVBcmdzO1xuXHRcdFx0aWYgKGluc3RhbmNlQXJnICYmIHRzLmlzVHlwZVF1ZXJ5Tm9kZShpbnN0YW5jZUFyZykgJiYgdHMuaXNJZGVudGlmaWVyKGluc3RhbmNlQXJnLmV4cHJOYW1lKSkge1xuXHRcdFx0XHRjb25zdCBxdWVyeVJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUoaW5zdGFuY2VBcmcuZXhwck5hbWUudGV4dCk7XG5cdFx0XHRcdGlmIChxdWVyeVJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRcdFx0Ly8gdW5kZWZpbmVkIHdoZW4gdGhlIHR5cGUgaXMgbmV2ZXIgZW1pdHRlZCAoY29sbGVjdGlvblxuXHRcdFx0XHRcdC8vIHdpdGhvdXQgYSByZWdpc3RyeSBpbnRlcmZhY2UpIOKAlCBkZWdyYWRlLCBuZXZlciBiYXJlXG5cdFx0XHRcdFx0Y29uc3QgYWxpYXNSZXN1bHQgPSB0aGlzLmdldEVtaXR0ZWRJbnN0YW5jZVR5cGVOYW1lKHF1ZXJ5UmVzdWx0Lm5vZGUpID8/ICd1bmtub3duJztcblx0XHRcdFx0XHRyZXR1cm4gYWxpYXNSZXN1bHQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKHF1ZXJ5UmVzdWx0LnN0YXR1cyA9PT0gJ2FtYmlndW91cycpIHtcblx0XHRcdFx0XHR0aGlzLnJlY29yZEdyYXBoUmVmZXJlbmNlRXJyb3IoaW5zdGFuY2VBcmcuZXhwck5hbWUudGV4dCwgaW5zdGFuY2VBcmcsIHF1ZXJ5UmVzdWx0KTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBkZWdyYWRlZFJlc3VsdCA9ICd1bmtub3duJztcblx0XHRcdFx0cmV0dXJuIGRlZ3JhZGVkUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgaW5mZXJyZWRBcmcgPSB0aGlzLmluZmVyVHlwZShpbnN0YW5jZUFyZyk7XG5cdFx0XHRpZiAoaW5mZXJyZWRBcmcgPT09ICd1bmtub3duJykge1xuXHRcdFx0XHRjb25zdCBkZWdyYWRlZFdyYXBwZXIgPSAndW5rbm93bic7XG5cdFx0XHRcdHJldHVybiBkZWdyYWRlZFdyYXBwZXI7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCB3cmFwcGVkUmVzdWx0ID0gYEluc3RhbmNlVHlwZTwke2luZmVycmVkQXJnfT5gO1xuXHRcdFx0cmV0dXJuIHdyYXBwZWRSZXN1bHQ7XG5cdFx0fVxuXG5cdFx0Ly8gTW5lbW9uaWNhLWdyYXBoIGlkZW50aXR5IGxhdzogcGF0aC1hd2FyZSByZXNvbHV0aW9uICh2YWx1ZSBzY29wZSxcblx0XHQvLyBpbXBvcnRzLCBuZWFyZXN0LWNoYWluLCByb290LCBwcm9ncmFtLXdpZGUpLiBBbWJpZ3VpdHkgYmV0d2VlblxuXHRcdC8vIHJlYWwgZ3JhcGggdHlwZXMgaXMgYSBoYXJkIGZhaWx1cmU7IGEgbmFtZSBubyBncmFwaCB0eXBlIGNhcnJpZXNcblx0XHQvLyBzdGF5cyBpbiB0aGUgcGxhaW4tVFMgc29mdCBzY29wZSBhbmQgZmFsbHMgdG8gYHVua25vd25gLlxuXHRcdGNvbnN0IGdyYXBoUmVzdWx0ID0gdGhpcy5yZXNvbHZlR3JhcGhUeXBlTmFtZSh0eXBlTmFtZSk7XG5cdFx0aWYgKGdyYXBoUmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdC8vIEhhbmRsZSBJbnN0YW5jZVR5cGU8dHlwZW9mIFg+IHBhdHRlcm4gLT4gY29udmVydCB0byBQYXJlbnRfWFxuXHRcdFx0aWYgKHR5cGVOYW1lID09PSAnSW5zdGFuY2VUeXBlJyAmJiB0eXBlQXJncyAmJiB0eXBlQXJncy5sZW5ndGggPT09IDEpIHtcblx0XHRcdFx0Y29uc3QgWyBhcmcgXSA9IHR5cGVBcmdzO1xuXHRcdFx0XHRpZiAoYXJnLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVHlwZVF1ZXJ5KSB7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZVF1ZXJ5ID0gYXJnIGFzIHRzLlR5cGVRdWVyeU5vZGU7XG5cdFx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcih0eXBlUXVlcnkuZXhwck5hbWUpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBxdWVyeVJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUodHlwZVF1ZXJ5LmV4cHJOYW1lLnRleHQpO1xuXHRcdFx0XHRcdFx0aWYgKHF1ZXJ5UmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdFx0XHRcdFx0Ly8gRW1pdHRlZCBhbGlhczogVXNhZ2VzLlVzYWdlRW50cnkgLT4gVXNhZ2VzX1VzYWdlRW50cnlcblx0XHRcdFx0XHRcdFx0Ly8gKE9wdGlvbiBCIGNvbGxlY3Rpb25zIGNhcnJ5IHRoZSByZWdpc3RyeSBwcmVmaXg7XG5cdFx0XHRcdFx0XHRcdC8vIHVuZGVmaW5lZCB3aGVuIG5ldmVyIGVtaXR0ZWQg4oCUIGRlZ3JhZGUpXG5cdFx0XHRcdFx0XHRcdGNvbnN0IHF1ZXJ5QWxpYXMgPSB0aGlzLmdldEVtaXR0ZWRJbnN0YW5jZVR5cGVOYW1lKHF1ZXJ5UmVzdWx0Lm5vZGUpID8/ICd1bmtub3duJztcblx0XHRcdFx0XHRcdFx0cmV0dXJuIHF1ZXJ5QWxpYXM7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRpZiAocXVlcnlSZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0XHRcdFx0XHR0aGlzLnJlY29yZEdyYXBoUmVmZXJlbmNlRXJyb3IodHlwZVF1ZXJ5LmV4cHJOYW1lLnRleHQsIHR5cGVRdWVyeSwgcXVlcnlSZXN1bHQpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0Ly8gTm90IGEga25vd24gbW5lbW9uaWNhIHR5cGUg4oCUIG5vIGJhcmUgZW1pc3Npb25cblx0XHRcdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAoIXR5cGVBcmdzIHx8IHR5cGVBcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHQvLyBFbWl0dGVkIGFsaWFzOiBVc2FnZXMuVXNhZ2VFbnRyeSAtPiBVc2FnZXNfVXNhZ2VFbnRyeVxuXHRcdFx0XHQvLyAoT3B0aW9uIEIgY29sbGVjdGlvbnMgY2FycnkgdGhlIHJlZ2lzdHJ5IHByZWZpeDtcblx0XHRcdFx0Ly8gdW5kZWZpbmVkIHdoZW4gbmV2ZXIgZW1pdHRlZCDigJQgZGVncmFkZSlcblx0XHRcdFx0Y29uc3QgZ3JhcGhBbGlhcyA9IHRoaXMuZ2V0RW1pdHRlZEluc3RhbmNlVHlwZU5hbWUoZ3JhcGhSZXN1bHQubm9kZSkgPz8gJ3Vua25vd24nO1xuXHRcdFx0XHRyZXR1cm4gZ3JhcGhBbGlhcztcblx0XHRcdH1cblx0XHRcdC8vIEdlbmVyaWMgdXNlIG9mIGEgZ3JhcGggdHlwZSBrZWVwcyBpdHMgc2ltcGxlIG5hbWU7IHRoZVxuXHRcdFx0Ly8gZ2VuZXJhdG9yIHVwZ3JhZGVzIGl0IHRvIHRoZSBmdWxsLXBhdGggaW5zdGFuY2UgdHlwZSBuYW1lXG5cdFx0XHRyZXR1cm4gYCR7dHlwZU5hbWV9PCR7dHlwZUFyZ3MubWFwKGEgPT4gdGhpcy5pbmZlclR5cGUoYSkpLmpvaW4oJywgJyl9PmA7XG5cdFx0fVxuXHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHR0aGlzLnJlY29yZEdyYXBoUmVmZXJlbmNlRXJyb3IodHlwZU5hbWUsIHJlZk5vZGUgPz8gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlLCBncmFwaFJlc3VsdCk7XG5cdFx0fVxuXG5cdFx0aWYgKHR5cGVBcmdzICYmIHR5cGVBcmdzLmxlbmd0aCA+IDApIHtcblx0XHRcdGlmIChLTk9XTl9HTE9CQUxfVFlQRVMuaGFzKHR5cGVOYW1lKSkge1xuXHRcdFx0XHRjb25zdCBnZW5lcmljUmVzdWx0ID0gYCR7dHlwZU5hbWV9PCR7dHlwZUFyZ3MubWFwKGEgPT4gdGhpcy5pbmZlclR5cGUoYSkpLmpvaW4oJywgJyl9PmA7XG5cdFx0XHRcdHJldHVybiBnZW5lcmljUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0Ly8gRW1pc3Npb24gcmVzdG9yYXRpb24gKDAuMi4wIGJlaGF2aW9yKTogYSBub24tZ3JhcGggb3V0ZXJcblx0XHRcdC8vIGdlbmVyaWMgdGhhdCBpcyBOT1QgZGVjbGFyZWQgaW4gYW55IGFuYWx5emVkIHByb2plY3QgZmlsZSBpc1xuXHRcdFx0Ly8gYW4gYW1iaWVudC9saWIgY29uc3RydWN0IChNYXBJdGVyYXRvciwgbGliIGhlbHBlcnMpIOKAlCBpdFxuXHRcdFx0Ly8gcmVzb2x2ZXMgaW4gZXZlcnkgY29uc3VtZXIgY29tcGlsYXRpb24gd2l0aG91dCBhbiBpbXBvcnQsIHNvXG5cdFx0XHQvLyBlbWl0IGl0IFZFUkJBVElNIHdpdGggaW5uZXIgZ3JhcGggYWxpYXNlcyByZXNvbHZlZC4gQSBuYW1lXG5cdFx0XHQvLyBkZWNsYXJlZCBpbiBwcm9qZWN0IGZpbGVzIHN0YXlzIHVua25vd246IHRoZSBzZWxmLWNvbnRhaW5lZFxuXHRcdFx0Ly8gdHlwZXMudHMgY2FuIGNhcnJ5IG5laXRoZXIgdGhlIGJhcmUgbmFtZSBub3IgYW4gaW1wb3J0LlxuXHRcdFx0aWYgKCF0aGlzLmlzUHJvamVjdERlY2xhcmVkVHlwZU5hbWUodHlwZU5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHZlcmJhdGltUmVzdWx0ID0gYCR7dHlwZU5hbWV9PCR7dHlwZUFyZ3MubWFwKGEgPT4gdGhpcy5pbmZlclR5cGUoYSkpLmpvaW4oJywgJyl9PmA7XG5cdFx0XHRcdHJldHVybiB2ZXJiYXRpbVJlc3VsdDtcblx0XHRcdH1cblx0XHRcdC8vIEdlbmVyaWMgcmVmZXJlbmNlIHRvIGEgbm9uLWdsb2JhbCwgbm9uLWdyYXBoIFBST0pFQ1QtTE9DQUxcblx0XHRcdC8vIHR5cGUgY2Fubm90IGJlIGVtaXR0ZWQgYmFyZSBpbnRvIHRoZSBnZW5lcmF0ZWQgZmlsZVxuXHRcdFx0aWYgKHJlZk5vZGUpIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRQbGFpblR5cGVSZWZlcmVuY2VTaXRlKHR5cGVOYW1lLCByZWZOb2RlKTtcblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmFsbGJhY2tSZXN1bHQgPSB0aGlzLnVucmVzb2x2ZWRUeXBlUmVmZXJlbmNlRmFsbGJhY2sodHlwZU5hbWUsIHJlZk5vZGUpO1xuXHRcdHJldHVybiBmYWxsYmFja1Jlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgcXVhbGlmaWVkIHR5cGUgcmVmZXJlbmNlIChtb2RlbHMuSW5uZXIuQ3JhdGUpIHRocm91Z2ggdGhlXG5cdCAqIGN1cnJlbnQgZmlsZSdzIG5hbWVzcGFjZSBpbXBvcnRzLiBUaGUgY2hhaW4ncyBoZWFkIG11c3QgYmUgYSBuYW1lc3BhY2Vcblx0ICogaW1wb3J0OyBtaWRkbGUgc2VnbWVudHMgZGVzY2VuZCB0aHJvdWdoIG5hbWVzcGFjZSBkZWNsYXJhdGlvbnMsIG5hbWVkXG5cdCAqIHJlLWV4cG9ydHMgb2YgbmFtZXNwYWNlcywgYW5kIGBleHBvcnQgKiBhcyBucyBmcm9tICfigKYnYCBiYXJyZWxzIChlYWNoXG5cdCAqIHNlZ21lbnQgY29uc3VtZWQgZXhhY3RseSBvbmNlLCBzbyB0aGUgd2FsayBjYW5ub3QgY3ljbGUpOyB0aGUgZmluYWxcblx0ICogc2VnbWVudCByZXNvbHZlcyB0byBhIGRlY2xhcmF0aW9uIHdoaWNoIGlzIGV4cGFuZGVkIGlubGluZS4gV2hlbiB0aGVcblx0ICogcHJlY2lzZSB3YWxrIGZpbmRzIG5vdGhpbmcsIHRoZSBsZWdhY3kgcmlnaHRtb3N0LW5hbWUgbG9va3VwIGluIHRoZVxuXHQgKiBoZWFkIG1vZHVsZSBrZWVwcyBvbmUtbGV2ZWwgZm9ybXMgKG1vZGVscy5UeXBlKSB3b3JraW5nIOKAlCBuZXN0ZWRcblx0ICogZGVjbGFyYXRpb25zIGFyZSByZWNvcmRlZCBieSBwbGFpbiBuYW1lIHRoZXJlIHRvby4gUmV0dXJucyB1bmRlZmluZWRcblx0ICogd2hlbiB0aGUgaGVhZCBpcyBub3QgYSBuYW1lc3BhY2UgaW1wb3J0IG9yIG5vdGhpbmcgcmVzb2x2ZXMuXG5cdCAqL1xuXHRwcml2YXRlIGluZmVyUXVhbGlmaWVkVHlwZVJlZmVyZW5jZSAodHlwZVJlZjogdHMuVHlwZVJlZmVyZW5jZU5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHMuaXNRdWFsaWZpZWROYW1lKHR5cGVSZWYudHlwZU5hbWUpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIGZsYXR0ZW4gdGhlIHF1YWxpZmllZCBuYW1lIGNoYWluOiBtb2RlbHMuSW5uZXIuQ3JhdGUg4oaSIFsnbW9kZWxzJywgJ0lubmVyJywgJ0NyYXRlJ11cblx0XHRjb25zdCBzZWdtZW50czogc3RyaW5nW10gPSBbXTtcblx0XHRsZXQgY2hhaW46IHRzLkVudGl0eU5hbWUgPSB0eXBlUmVmLnR5cGVOYW1lO1xuXHRcdHdoaWxlICh0cy5pc1F1YWxpZmllZE5hbWUoY2hhaW4pKSB7XG5cdFx0XHRzZWdtZW50cy51bnNoaWZ0KGNoYWluLnJpZ2h0LnRleHQpO1xuXHRcdFx0Y2hhaW4gPSBjaGFpbi5sZWZ0O1xuXHRcdH1cblx0XHRzZWdtZW50cy51bnNoaWZ0KGNoYWluLnRleHQpO1xuXG5cdFx0Y29uc3QgbmFtZXNwYWNlSW1wb3J0ID0gdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChzZWdtZW50c1sgMCBdKTtcblx0XHRpZiAoIW5hbWVzcGFjZUltcG9ydCB8fCAhbmFtZXNwYWNlSW1wb3J0LmlzTmFtZXNwYWNlKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShuYW1lc3BhY2VJbXBvcnQuc3BlY2lmaWVyLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdGlmICghcmVzb2x1dGlvbiB8fCByZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gZGVzY2VuZCB0aGUgbWlkZGxlIHNlZ21lbnRzOiBhIG1vZHVsZSBjb250ZXh0IHJlc29sdmVzIHRoZSBzZWdtZW50XG5cdFx0Ly8gYXMgYSBuYW1lc3BhY2UgZGVjbGFyYXRpb24gLyBuYW1lc3BhY2UgcmUtZXhwb3J0OyBhIG5hbWVzcGFjZS1ibG9ja1xuXHRcdC8vIGNvbnRleHQgcmVzb2x2ZXMgaXQgYXMgYSBuZXN0ZWQgbmFtZXNwYWNlIGRlY2xhcmF0aW9uXG5cdFx0bGV0IHF1YWxpZmllcjogeyBtb2R1bGVQYXRoOiBzdHJpbmc7IGJsb2NrPzogdHMuTW9kdWxlQmxvY2sgfSB8IHVuZGVmaW5lZCA9IHtcblx0XHRcdG1vZHVsZVBhdGggOiByZXNvbHV0aW9uLnJlc29sdmVkUGF0aFxuXHRcdH07XG5cdFx0Zm9yIChsZXQgaSA9IDE7IGkgPCBzZWdtZW50cy5sZW5ndGggLSAxICYmIHF1YWxpZmllcjsgaSsrKSB7XG5cdFx0XHRjb25zdCBzZWdtZW50ID0gc2VnbWVudHNbIGkgXTtcblx0XHRcdGlmIChxdWFsaWZpZXIuYmxvY2spIHtcblx0XHRcdFx0Y29uc3QgbmVzdGVkID0gdGhpcy5maW5kTmFtZXNwYWNlSW5CbG9jayhxdWFsaWZpZXIuYmxvY2ssIHNlZ21lbnQpO1xuXHRcdFx0XHRpZiAobmVzdGVkPy5ib2R5ICYmIHRzLmlzTW9kdWxlQmxvY2sobmVzdGVkLmJvZHkpKSB7XG5cdFx0XHRcdFx0cXVhbGlmaWVyID0geyBtb2R1bGVQYXRoIDogcXVhbGlmaWVyLm1vZHVsZVBhdGgsIGJsb2NrIDogbmVzdGVkLmJvZHkgfTtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRxdWFsaWZpZXIgPSB1bmRlZmluZWQ7XG5cdFx0XHRcdGJyZWFrO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbmFtZXNwYWNlRGVjbDogdHMuTW9kdWxlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQgPVxuXHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlcy5nZXQocXVhbGlmaWVyLm1vZHVsZVBhdGgpPy5nZXQoc2VnbWVudCk7XG5cdFx0XHRpZiAobmFtZXNwYWNlRGVjbD8uYm9keSAmJiB0cy5pc01vZHVsZUJsb2NrKG5hbWVzcGFjZURlY2wuYm9keSkpIHtcblx0XHRcdFx0cXVhbGlmaWVyID0geyBtb2R1bGVQYXRoIDogcXVhbGlmaWVyLm1vZHVsZVBhdGgsIGJsb2NrIDogbmFtZXNwYWNlRGVjbC5ib2R5IH07XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgc3RhclNwZWNpZmllciA9IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VTdGFycy5nZXQocXVhbGlmaWVyLm1vZHVsZVBhdGgpPy5nZXQoc2VnbWVudCk7XG5cdFx0XHRpZiAoc3RhclNwZWNpZmllcikge1xuXHRcdFx0XHRjb25zdCBuZXh0UmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKHN0YXJTcGVjaWZpZXIsIHF1YWxpZmllci5tb2R1bGVQYXRoKTtcblx0XHRcdFx0aWYgKG5leHRSZXNvbHV0aW9uICYmICFuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdFx0cXVhbGlmaWVyID0geyBtb2R1bGVQYXRoIDogbmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoIH07XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGNvbnN0IHJlRXhwb3J0U3BlY2lmaWVyID0gdGhpcy5yZWZlcmVuY2VkVHlwZVJlRXhwb3J0cy5nZXQocXVhbGlmaWVyLm1vZHVsZVBhdGgpPy5nZXQoc2VnbWVudCk7XG5cdFx0XHRpZiAocmVFeHBvcnRTcGVjaWZpZXIpIHtcblx0XHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShyZUV4cG9ydFNwZWNpZmllciwgcXVhbGlmaWVyLm1vZHVsZVBhdGgpO1xuXHRcdFx0XHRjb25zdCByZUV4cG9ydGVkOiB0cy5Nb2R1bGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCA9XG5cdFx0XHRcdFx0bmV4dFJlc29sdXRpb24gJiYgIW5leHRSZXNvbHV0aW9uLmlzRXh0ZXJuYWxcblx0XHRcdFx0XHRcdD8gdGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMuZ2V0KG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCk/LmdldChzZWdtZW50KVxuXHRcdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cdFx0XHRcdGlmIChyZUV4cG9ydGVkPy5ib2R5ICYmIHRzLmlzTW9kdWxlQmxvY2socmVFeHBvcnRlZC5ib2R5KSkge1xuXHRcdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IG5leHRSZXNvbHV0aW9uIS5yZXNvbHZlZFBhdGgsIGJsb2NrIDogcmVFeHBvcnRlZC5ib2R5IH07XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHF1YWxpZmllciA9IHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBmaW5hbE5hbWUgPSBzZWdtZW50c1sgc2VnbWVudHMubGVuZ3RoIC0gMSBdO1xuXHRcdGxldCBkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkO1xuXHRcdGlmIChxdWFsaWZpZXI/LmJsb2NrKSB7XG5cdFx0XHRkZWNsID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbkJsb2NrKHF1YWxpZmllci5ibG9jaywgcXVhbGlmaWVyLm1vZHVsZVBhdGgsIGZpbmFsTmFtZSk7XG5cdFx0fSBlbHNlIGlmIChxdWFsaWZpZXIpIHtcblx0XHRcdGRlY2wgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKHF1YWxpZmllci5tb2R1bGVQYXRoLCBmaW5hbE5hbWUsIDApO1xuXHRcdH1cblx0XHQvLyBsZWdhY3kgZmFsbGJhY2s6IHJpZ2h0bW9zdCBuYW1lIGFueXdoZXJlIGluIHRoZSBoZWFkIG1vZHVsZVxuXHRcdC8vIChuYW1lc3BhY2UtbmVzdGVkIGRlY2xhcmF0aW9ucyBhcmUgYWxzbyByZWNvcmRlZCBieSBwbGFpbiBuYW1lKVxuXHRcdGlmICghZGVjbCkge1xuXHRcdFx0ZGVjbCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUocmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIGZpbmFsTmFtZSwgMCk7XG5cdFx0fVxuXHRcdGlmICghZGVjbCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMuZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihkZWNsKTtcblx0XHRyZXR1cm4gZXhwYW5kZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmluZCBhIG5hbWVzcGFjZSBkZWNsYXJhdGlvbiBieSBuYW1lIGRpcmVjdGx5IGluc2lkZSBhIG1vZHVsZSBibG9jay5cblx0ICovXG5cdHByaXZhdGUgZmluZE5hbWVzcGFjZUluQmxvY2sgKGJsb2NrOiB0cy5Nb2R1bGVCbG9jaywgbmFtZTogc3RyaW5nKTogdHMuTW9kdWxlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIGJsb2NrLnN0YXRlbWVudHMpIHtcblx0XHRcdGlmICh0cy5pc01vZHVsZURlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiYgdHMuaXNJZGVudGlmaWVyKHN0YXRlbWVudC5uYW1lKSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdCA9IHN0YXRlbWVudDtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGaW5kIGEgbmFtZWQgdHlwZSBkZWNsYXJhdGlvbiAoYWxpYXMsIGNsYXNzLCBpbnRlcmZhY2UpIGRpcmVjdGx5IGluc2lkZVxuXHQgKiBhIG5hbWVzcGFjZSBibG9jayDigJQgdGhlIGZpbmFsIHNlZ21lbnQgb2YgYSBkZXNjZW5kZWQgcXVhbGlmaWVkIGNoYWluLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kUmVmZXJlbmNlZFR5cGVJbkJsb2NrIChcblx0XHRibG9jazogdHMuTW9kdWxlQmxvY2ssXG5cdFx0ZmlsZVBhdGg6IHN0cmluZyxcblx0XHRuYW1lOiBzdHJpbmdcblx0KTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2YgYmxvY2suc3RhdGVtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzVHlwZUFsaWFzRGVjbGFyYXRpb24oc3RhdGVtZW50KSAmJiB0cy5pc0lkZW50aWZpZXIoc3RhdGVtZW50Lm5hbWUpICYmXG5cdFx0XHRcdHN0YXRlbWVudC5uYW1lLnRleHQgPT09IG5hbWUpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0OiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uID0geyBraW5kIDogJ2FsaWFzJywgbm9kZSA6IHN0YXRlbWVudCwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiYgc3RhdGVtZW50Lm5hbWUgJiYgc3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZSkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQ6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gPSB7IGtpbmQgOiAnY2xhc3MnLCBub2RlIDogc3RhdGVtZW50LCBmaWxlIDogZmlsZVBhdGggfTtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc0ludGVyZmFjZURlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiYgdHMuaXNJZGVudGlmaWVyKHN0YXRlbWVudC5uYW1lKSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiA9IHsga2luZCA6ICdpbnRlcmZhY2UnLCBub2RlIDogc3RhdGVtZW50LCBmaWxlIDogZmlsZVBhdGggfTtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGYWxsYmFjayBmb3IgYSB0eXBlLXJlZmVyZW5jZSBuYW1lIHRoYXQgcmVzb2x2ZXMgdG8gbm8gZGVjbGFyYXRpb24gYW5kXG5cdCAqIG5vIGdyYXBoIHR5cGU6IGtub3duIGdsb2JhbHMga2VlcCB0aGVpciBiYXJlIG5hbWUgKHRoZXkgcmVzb2x2ZSB3aXRob3V0XG5cdCAqIGFuIGltcG9ydCk7IGV2ZXJ5dGhpbmcgZWxzZSBiZWNvbWVzIGB1bmtub3duYCBzbyBnZW5lcmF0ZWQgdHlwZXMudHNcblx0ICogbmV2ZXIgY2FycmllcyBhbiB1bnJlc29sdmFibGUgYmFyZSBuYW1lIChSRUFETUUncyBkb2N1bWVudGVkIGJlaGF2aW9yKVxuXHQgKiBhbmQgdGhlIHNpdGUgaXMgcmVjb3JkZWQgZm9yIHRoZSBwbGFpbi1UUyBhbWJpZ3VpdHkgdmFsaWRhdGlvbi5cblx0ICovXG5cdHByaXZhdGUgdW5yZXNvbHZlZFR5cGVSZWZlcmVuY2VGYWxsYmFjayAodHlwZU5hbWU6IHN0cmluZywgcmVmTm9kZT86IHRzLk5vZGUpOiBzdHJpbmcge1xuXHRcdGlmIChLTk9XTl9HTE9CQUxfVFlQRVMuaGFzKHR5cGVOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHR5cGVOYW1lO1xuXHRcdH1cblx0XHRpZiAocmVmTm9kZSkge1xuXHRcdFx0dGhpcy5yZWNvcmRQbGFpblR5cGVSZWZlcmVuY2VTaXRlKHR5cGVOYW1lLCByZWZOb2RlKTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gJ3Vua25vd24nO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIG9uZSBkZWZpbmUoKS9sYXp5KCkvQGRlY29yYXRlKCkgc2l0ZSB1bmRlciBpdHMgcnVudGltZVxuXHQgKiBuYW1lc3BhY2Uga2V5LiBUd28gc2l0ZXMgaW4gb25lIG5hbWVzcGFjZSBhcmUgYSBzYW1lLW5hbWVzcGFjZVxuXHQgKiBkdXBsaWNhdGUgKHRoZSBydW50aW1lIHRocm93cyBBTFJFQURZX0RFQ0xBUkVEKTsgZXZlcnkgc2l0ZSBpcyBrZXB0XG5cdCAqIHNvIHRoZSBmYWlsdXJlIGNhbiByZXBvcnQgYWxsIGxvY2F0aW9ucy5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkRGVmaW5lU2l0ZSAobmFtZXNwYWNlS2V5OiBzdHJpbmcsIGxvY2F0aW9uOiBzdHJpbmcpOiB2b2lkIHtcblx0XHRsZXQgc2l0ZXMgPSB0aGlzLmRlZmluZVNpdGVzLmdldChuYW1lc3BhY2VLZXkpO1xuXHRcdGlmICghc2l0ZXMpIHtcblx0XHRcdHNpdGVzID0gW107XG5cdFx0XHR0aGlzLmRlZmluZVNpdGVzLnNldChuYW1lc3BhY2VLZXksIHNpdGVzKTtcblx0XHR9XG5cdFx0aWYgKCFzaXRlcy5pbmNsdWRlcyhsb2NhdGlvbikpIHtcblx0XHRcdHNpdGVzLnB1c2gobG9jYXRpb24pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBGYXRhbCByZXNvbHV0aW9uIGZhaWx1cmVzIChoYXJkLWZhaWwgbGF3KTogc2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlXG5cdCAqIG1uZW1vbmljYSBkZWZpbml0aW9ucyBwbHVzIGFtYmlndW91cy91bnJlc29sdmVkIG1uZW1vbmljYS1ncmFwaFxuXHQgKiByZWZlcmVuY2VzLiBUaGUgQ0xJIHByaW50cyBldmVyeSBsb2NhdGlvbiBhbmQgd3JpdGVzIG5vIG91dHB1dC5cblx0ICovXG5cdGdldFJlc29sdXRpb25FcnJvcnMgKCk6IFJlc29sdXRpb25FcnJvcltdIHtcblx0XHR0aGlzLnZhbGlkYXRlTG9va3VwUmVmZXJlbmNlcygpO1xuXHRcdHRoaXMudmFsaWRhdGVQbGFpblR5cGVSZWZlcmVuY2VzKCk7XG5cdFx0Y29uc3QgZXJyb3JzOiBSZXNvbHV0aW9uRXJyb3JbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgWyBuYW1lc3BhY2VLZXksIHNpdGVzIF0gb2YgdGhpcy5kZWZpbmVTaXRlcykge1xuXHRcdFx0aWYgKHNpdGVzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBkaXNwbGF5TmFtZSA9IG5hbWVzcGFjZUtleS5yZXBsYWNlKC9eW146XSs6Oi8sICcnKTtcblx0XHRcdGNvbnN0IG1lc3NhZ2UgPSBgRHVwbGljYXRlIGRlZmluaXRpb24gb2YgJyR7ZGlzcGxheU5hbWV9JyBpbiBvbmUgbmFtZXNwYWNlIOKAlCBgICtcblx0XHRcdFx0J3RoZSBtbmVtb25pY2EgcnVudGltZSB3b3VsZCB0aHJvdyBBTFJFQURZX0RFQ0xBUkVEJztcblx0XHRcdGVycm9ycy5wdXNoKHsgbWVzc2FnZSwgbG9jYXRpb25zIDogWyAuLi5zaXRlcyBdIH0pO1xuXHRcdH1cblx0XHRmb3IgKGNvbnN0IGVycm9yIG9mIHRoaXMuZ3JhcGhSZWZlcmVuY2VFcnJvcnMpIHtcblx0XHRcdGVycm9ycy5wdXNoKGVycm9yKTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gZXJyb3JzO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHJlZmVyZW5jZSB0byBhIG1uZW1vbmljYSBncmFwaCB0eXBlIG5hbWUsIGltcG9ydC1hd2FyZSBhbmRcblx0ICogcGF0aC1hd2FyZSAodGhlIGhhcmQtZmFpbCBpZGVudGl0eSBsYXcsIG1pcnJvcmluZyB0aGUgcnVudGltZSk6XG5cdCAqICAgMS4gdmFsdWUgc2NvcGUg4oCUIGEgdHJhY2tlZCB0b3AtbGV2ZWwgYmluZGluZyBpbiB0aGUgcmVmZXJlbmNpbmcgZmlsZVxuXHQgKiAgICAgIChgY29uc3QgQWRkcmVzcyA9IFVzZXIuZGVmaW5lKCdBZGRyZXNzJywg4oCmKWApLFxuXHQgKiAgIDIuIGltcG9ydCBzY29wZSDigJQgYSBiaW5kaW5nIGV4cG9ydGVkIGZyb20gYSBtb2R1bGUgdGhpcyBmaWxlIGltcG9ydHNcblx0ICogICAgICAoYmFycmVscyBjaGFzZWQpLFxuXHQgKiAgIDMuIG5lYXJlc3QtY2hhaW4g4oCUIHRoZSBhbmNob3IgdHlwZSdzIG93biBzdWJ0eXBlcyBmaXJzdCwgdGhlbiBlYWNoXG5cdCAqICAgICAgYW5jZXN0b3IgbGV2ZWwgKHJlbGF0aXZlLWZpcnN0KSxcblx0ICogICA0LiByb290IOKAlCByb290cyBvZiB0aGUgYW5jaG9yJ3MgY29sbGVjdGlvbixcblx0ICogICA1LiBwcm9ncmFtLXdpZGUg4oCUIG9ubHkgd2hlbiBleGFjdGx5IG9uZSB0eXBlIGNhcnJpZXMgdGhlIG5hbWUuXG5cdCAqIEFtYmlndWl0eSAoc2V2ZXJhbCBjYW5kaWRhdGVzIGFuZCBub3RoaW5nIGRpc2FtYmlndWF0ZXMpIGFuZCBhYnNlbmNlXG5cdCAqIGFyZSBib3RoIHJldHVybmVkIGFzIHN1Y2gg4oCUIHRoZSBjYWxsZXIgcmVjb3JkcyBhIGhhcmQgZmFpbHVyZTsgYSBiYXJlXG5cdCAqIGZpcnN0LW1hdGNoIG5hbWUgaXMgbmV2ZXIgZW1pdHRlZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUdyYXBoVHlwZU5hbWUgKG5hbWU6IHN0cmluZyk6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCB7XG5cdFx0Ly8gMS4gdmFsdWUgc2NvcGUgaW4gdGhlIHJlZmVyZW5jaW5nIGZpbGUgaXRzZWxmXG5cdFx0Y29uc3QgbG9jYWxCaW5kaW5nID0gdGhpcy5maWxlR3JhcGhCaW5kaW5ncy5nZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChsb2NhbEJpbmRpbmcpIHtcblx0XHRcdGNvbnN0IG5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGxvY2FsQmluZGluZyk7XG5cdFx0XHRpZiAobm9kZSkge1xuXHRcdFx0XHRjb25zdCB2YWx1ZVJlc3VsdDogR3JhcGhUeXBlUmVmZXJlbmNlUmVzdWx0ID0geyBzdGF0dXMgOiAndW5pcXVlJywgbm9kZSB9O1xuXHRcdFx0XHRyZXR1cm4gdmFsdWVSZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gMi4gaW1wb3J0IHNjb3BlIOKAlCB0aGUgaW1wb3J0ZWQgbW9kdWxlJ3MgZXhwb3J0ZWQgYmluZGluZ1xuXHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAoaW1wb3J0ZWQgJiYgIWltcG9ydGVkLmlzTmFtZXNwYWNlKSB7XG5cdFx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoaW1wb3J0ZWQuc3BlY2lmaWVyLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0aWYgKHJlc29sdXRpb24gJiYgIXJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRjb25zdCBmdWxsUGF0aCA9IHRoaXMuZmluZEdyYXBoQmluZGluZ0luTW9kdWxlKHJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBpbXBvcnRlZC5vcmlnaW5hbE5hbWUsIDApO1xuXHRcdFx0XHRpZiAoZnVsbFBhdGgpIHtcblx0XHRcdFx0XHRjb25zdCBub2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShmdWxsUGF0aCk7XG5cdFx0XHRcdFx0aWYgKG5vZGUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGltcG9ydFJlc3VsdDogR3JhcGhUeXBlUmVmZXJlbmNlUmVzdWx0ID0geyBzdGF0dXMgOiAndW5pcXVlJywgbm9kZSB9O1xuXHRcdFx0XHRcdFx0cmV0dXJuIGltcG9ydFJlc3VsdDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyAzLTUuIGNoYWluIC8gcm9vdCAvIHByb2dyYW0td2lkZSB0aWVyc1xuXHRcdGNvbnN0IHJlc3VsdCA9IHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UodGhpcy5ncmFwaCwgbmFtZSwgdGhpcy5jdXJyZW50R3JhcGhBbmNob3IpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRmluZCBhIGdyYXBoIGNvbnN0cnVjdG9yIGJpbmRpbmcgZXhwb3J0ZWQgYnkgYSByZXNvbHZlZCBtb2R1bGUsXG5cdCAqIGNoYXNpbmcgcmUtZXhwb3J0IGJhcnJlbHMgd2l0aCBhIGJvdW5kZWQgZGVwdGguXG5cdCAqL1xuXHRwcml2YXRlIGZpbmRHcmFwaEJpbmRpbmdJbk1vZHVsZSAobW9kdWxlUGF0aDogc3RyaW5nLCBuYW1lOiBzdHJpbmcsIGRlcHRoOiBudW1iZXIpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmIChkZXB0aCA+IE1BWF9SRUVYUE9SVF9DSEFTRV9ERVBUSCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBkaXJlY3QgPSB0aGlzLmZpbGVHcmFwaEJpbmRpbmdzLmdldChtb2R1bGVQYXRoKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChkaXJlY3QpIHtcblx0XHRcdHJldHVybiBkaXJlY3Q7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVFeHBvcnRzID0gdGhpcy5yZWZlcmVuY2VkVHlwZVJlRXhwb3J0cy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0Y29uc3QgcmVFeHBvcnRTcGVjaWZpZXIgPSByZUV4cG9ydHM/LmdldChuYW1lKTtcblx0XHRpZiAocmVFeHBvcnRTcGVjaWZpZXIpIHtcblx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUocmVFeHBvcnRTcGVjaWZpZXIsIG1vZHVsZVBhdGgpO1xuXHRcdFx0aWYgKG5leHRSZXNvbHV0aW9uICYmICFuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kR3JhcGhCaW5kaW5nSW5Nb2R1bGUobmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBuYW1lLCBkZXB0aCArIDEpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCBzdGFycyA9IHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0aWYgKHN0YXJzKSB7XG5cdFx0XHRmb3IgKGNvbnN0IHN0YXJTcGVjaWZpZXIgb2Ygc3RhcnMpIHtcblx0XHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShzdGFyU3BlY2lmaWVyLCBtb2R1bGVQYXRoKTtcblx0XHRcdFx0aWYgKCFuZXh0UmVzb2x1dGlvbiB8fCBuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRHcmFwaEJpbmRpbmdJbk1vZHVsZShuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIG5hbWUsIGRlcHRoICsgMSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogVmFsaWRhdGUgbGl0ZXJhbCBsb29rdXAoKSBwYXRocyByZWNvcmRlZCBkdXJpbmcgdGhlIHVzYWdlcyBwYXNzXG5cdCAqIGFnYWluc3QgdGhlIGNvbXBsZXRlIGdyYXBoLiBBIGxvb2t1cCBwYXRoIG1hdGNoaW5nIG5vIHR5cGUgaXMgd2hhdCB0aGVcblx0ICogcnVudGltZSBhbnN3ZXJzIHdpdGggYHVuZGVmaW5lZGAg4oCUIHRoZSBUeXBlRXJyb3IgYXJyaXZlcyBvbmUgbGluZVxuXHQgKiBsYXRlciBhdCB0aGUgYG5ld2Ag4oCUIHNvIGl0IGpvaW5zIHRoZSBoYXJkLWZhaWwgbGF3LiBUaGUgcmVsYXRpdmUtZmlyc3Rcblx0ICogc3RlcCBhbHJlYWR5IHJhbiBpbnNpZGUgcmVzb2x2ZUxvb2t1cFBhdGg7IHdoYXRldmVyIHdhcyByZWNvcmRlZCBpc1xuXHQgKiB0aGUgcm9vdC1yZXNvbHV0aW9uIHJlc3VsdCwgc28gYSBwbGFpbiBmaW5kVHlwZSBjaGVjayBpcyB0aGUgZXhhY3Rcblx0ICogcnVudGltZSBsYXcuIFNhbWUtbmFtZWQgdHlwZXMgZWxzZXdoZXJlIGluIHRoZSBncmFwaCBhcmUgbGlzdGVkIGFzXG5cdCAqIGRpZC15b3UtbWVhbiBjYW5kaWRhdGVzLiBSdW5zIG9uY2UgcGVyIHVzYWdlcyBwYXNzIChyZS1hcm1lZCBieVxuXHQgKiByZXNldFVzYWdlcyk7IG5vbi1saXRlcmFsIGxvb2t1cCBhcmd1bWVudHMgYXJlIG5ldmVyIHJlY29yZGVkIGFuZFxuXHQgKiBzdGF5IGJlc3QtZWZmb3J0LlxuXHQgKi9cblx0cHJpdmF0ZSB2YWxpZGF0ZUxvb2t1cFJlZmVyZW5jZXMgKCk6IHZvaWQge1xuXHRcdGlmICh0aGlzLmxvb2t1cFJlZmVyZW5jZXNWYWxpZGF0ZWQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0dGhpcy5sb29rdXBSZWZlcmVuY2VzVmFsaWRhdGVkID0gdHJ1ZTtcblx0XHQvLyBncm91cCBzaXRlcyBieSBwYXRoOiBldmVyeSBmYWlsaW5nIHNpdGUgb2YgdGhlIHNhbWUgcGF0aCBpcyBsaXN0ZWRcblx0XHRjb25zdCBzaXRlc0J5UGF0aCA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmdbXT4oKTtcblx0XHRmb3IgKGNvbnN0IHJlZiBvZiB0aGlzLmxvb2t1cFJlZmVyZW5jZXMpIHtcblx0XHRcdGNvbnN0IHNpdGVzID0gc2l0ZXNCeVBhdGguZ2V0KHJlZi5wYXRoKSA/PyBbXTtcblx0XHRcdHNpdGVzLnB1c2gocmVmLmxvY2F0aW9uKTtcblx0XHRcdHNpdGVzQnlQYXRoLnNldChyZWYucGF0aCwgc2l0ZXMpO1xuXHRcdH1cblx0XHRmb3IgKGNvbnN0IFsgdHlwZVBhdGgsIHNpdGVzIF0gb2Ygc2l0ZXNCeVBhdGgpIHtcblx0XHRcdGlmICh0aGlzLmdyYXBoLmZpbmRUeXBlKHR5cGVQYXRoKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdC8vIGRpZC15b3UtbWVhbjogdHlwZXMgY2FycnlpbmcgdGhlIHNhbWUgbmFtZSBhbnl3aGVyZSBpbiB0aGVcblx0XHRcdC8vIGdyYXBoIChuZXZlciBhIGZpcnN0LW1hdGNoIHBpY2sg4oCUIHRoZSBmdWxsIGxpc3Qgb25seSlcblx0XHRcdGNvbnN0IHVucHJlZml4ZWQgPSB0eXBlUGF0aC5yZXBsYWNlKC9eW146XSs6Oi8sICcnKTtcblx0XHRcdGNvbnN0IGxhc3RTZWdtZW50ID0gdW5wcmVmaXhlZC5zcGxpdCgnLicpLnBvcCgpID8/IHVucHJlZml4ZWQ7XG5cdFx0XHRjb25zdCBjYW5kaWRhdGVzID0gdGhpcy5ncmFwaC5nZXRBbGxUeXBlcygpLmZpbHRlcih0ID0+IHQubmFtZSA9PT0gbGFzdFNlZ21lbnQpO1xuXHRcdFx0aWYgKGNhbmRpZGF0ZXMubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRcdGNvbnN0IG5vbmVFcnJvcjogUmVzb2x1dGlvbkVycm9yID0ge1xuXHRcdFx0XHRcdG1lc3NhZ2UgOiBgVW5yZXNvbHZlZCBsb29rdXAgb2YgbW5lbW9uaWNhIHR5cGUgJyR7dHlwZVBhdGh9Jzogbm8gdHlwZSBhdCB0aGF0IHBhdGgg4oCUIGAgK1xuXHRcdFx0XHRcdFx0J3RoZSBydW50aW1lIHdvdWxkIHJldHVybiB1bmRlZmluZWQnLFxuXHRcdFx0XHRcdGxvY2F0aW9ucyA6IHNpdGVzLFxuXHRcdFx0XHR9O1xuXHRcdFx0XHR0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzLnB1c2gobm9uZUVycm9yKTtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBjYW5kaWRhdGVMb2NhdGlvbnMgPSBjYW5kaWRhdGVzLm1hcChuID0+IGAke24uc291cmNlRmlsZX06JHtuLmxpbmV9OiR7bi5jb2x1bW59YCk7XG5cdFx0XHRjb25zdCBjYW5kaWRhdGVQYXRocyA9IGNhbmRpZGF0ZXMubWFwKG4gPT4gbi5mdWxsUGF0aCkuam9pbignLCAnKTtcblx0XHRcdGNvbnN0IGFtYmlndW91c0Vycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7XG5cdFx0XHRcdG1lc3NhZ2UgOiBgVW5yZXNvbHZlZCBsb29rdXAgb2YgbW5lbW9uaWNhIHR5cGUgJyR7dHlwZVBhdGh9JzogdGhlIHJ1bnRpbWUgd291bGQgcmV0dXJuIGAgK1xuXHRcdFx0XHRcdGB1bmRlZmluZWQg4oCUICR7Y2FuZGlkYXRlcy5sZW5ndGh9IGdyYXBoIHR5cGUocykgY2FycnkgdGhlIG5hbWUgYCArXG5cdFx0XHRcdFx0YG9mZi1yb290ICgke2NhbmRpZGF0ZVBhdGhzfSk7IHVzZSB0aGUgZnVsbCBkb3R0ZWQgcGF0aGAsXG5cdFx0XHRcdGxvY2F0aW9ucyA6IFsgLi4uc2l0ZXMsIC4uLmNhbmRpZGF0ZUxvY2F0aW9ucyBdLFxuXHRcdFx0fTtcblx0XHRcdHRoaXMuZ3JhcGhSZWZlcmVuY2VFcnJvcnMucHVzaChhbWJpZ3VvdXNFcnJvcik7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhIHBsYWluLVRTIHR5cGUgcmVmZXJlbmNlIHNpdGUgdGhhdCByZXNvbHZlZCB0byBub3RoaW5nIGFuZFxuXHQgKiBmZWxsIGJhY2sgdG8gYHVua25vd25gLCBmb3IgdGhlIGxhemlseS1ydW4gYW1iaWd1aXR5IHZhbGlkYXRpb24uXG5cdCAqIERlZHVwZWQgYnkgKG5hbWUsIGxvY2F0aW9uKTogaW5mZXJUeXBlIGNhbiB2aXNpdCB0aGUgc2FtZSBub2RlIG1vcmVcblx0ICogdGhhbiBvbmNlIHBlciBwYXNzIChjb25zdHJ1Y3RvciBwYXJhbXMgKyBwcm9wZXJ0eSBpbmZlcmVuY2UpLlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmRQbGFpblR5cGVSZWZlcmVuY2VTaXRlIChuYW1lOiBzdHJpbmcsIHJlZk5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRjb25zdCBsb2NhdGlvbiA9IHRoaXMubm9kZUxvY2F0aW9uKHJlZk5vZGUpO1xuXHRcdGNvbnN0IGZpbGUgPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0Y29uc3QgYWxyZWFkeSA9IHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlcy5zb21lKChyZWYpID0+IHJlZi5uYW1lID09PSBuYW1lICYmIHJlZi5sb2NhdGlvbiA9PT0gbG9jYXRpb24pO1xuXHRcdGlmIChhbHJlYWR5KSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlcy5wdXNoKHsgbmFtZSwgbG9jYXRpb24sIGZpbGUgfSk7XG5cdH1cblxuXHQvKipcblx0ICogUHJvamVjdC1zb3VyY2UgZGVjbGFyYXRpb24gZmlsZXMgY2FycnlpbmcgYG5hbWVgIOKAlCBvbmUgZW50cnkgcGVyXG5cdCAqIGZpbGUsIHNvIHNhbWUtZmlsZSBpbnRlcmZhY2UgbWVyZ2luZyBjb3VudHMgb25jZSAobm90IGFtYmlndW91cykuXG5cdCAqIEV4dGVybmFsL2FtYmllbnQgZGVjbGFyYXRpb25zICguZC50cywgYW55dGhpbmcgdW5kZXIgbm9kZV9tb2R1bGVzKVxuXHQgKiBuZXZlciBjb3VudDogYSB1c2VyLWxvY2FsIGRlY2xhcmF0aW9uIGFsd2F5cyB3aW5zIG92ZXIgYSBwYWNrYWdlLVxuXHQgKiBkZWNsYXJlZCBzYW1lLW5hbWVkIHR5cGUsIHNvIGFuIGV4dGVybmFsIGNvbGxpc2lvbiBzdGF5cyBzb2Z0LlxuXHQgKi9cblx0cHJpdmF0ZSBwbGFpblR5cGVEZWNsYXJhdGlvbkZpbGVzIChuYW1lOiBzdHJpbmcpOiBzdHJpbmdbXSB7XG5cdFx0Y29uc3QgZmlsZXM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBbIGZpbGUsIGRlY2xzIF0gb2YgdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzKSB7XG5cdFx0XHRpZiAoIXRoaXMuaXNFeHRlcm5hbERlY2xGaWxlKGZpbGUpICYmIGRlY2xzLmhhcyhuYW1lKSkge1xuXHRcdFx0XHRmaWxlcy5wdXNoKGZpbGUpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gZmlsZXM7XG5cdH1cblxuXHQvKipcblx0ICogVmFsaWRhdGUgcGxhaW4tVFMgdHlwZSByZWZlcmVuY2Ugc2l0ZXMgcmVjb3JkZWQgZHVyaW5nIHRoZSB1c2FnZXNcblx0ICogcGFzcyBhZ2FpbnN0IHRoZSBjb21wbGV0ZSBkZWNsYXJhdGlvbiBtYXAuIEEgbmFtZSBkZWNsYXJlZCBpblxuXHQgKiBzZXZlcmFsIHByb2plY3Qtc291cmNlIGZpbGVzIOKAlCB3aXRoIG5vIGltcG9ydCBpbiB0aGUgcmVmZXJlbmNpbmdcblx0ICogZmlsZSB0byBhbmNob3IgaXQg4oCUIGlzIGFtYmlndW91czogc2lsZW50bHkgZW1pdHRpbmcgYHVua25vd25gIHdvdWxkXG5cdCAqIGhpZGUgYSByZWFsIHR5cGUgdGhlIGF1dGhvciBtZWFudCwgc28gaXQgam9pbnMgdGhlIGhhcmQtZmFpbCBsYXdcblx0ICogKHRoZSBwbGFpbi1UUyB0aWVyIG9mIHRoZSBzYW1lIGlkZW50aXR5IGxhdyBhcyBncmFwaCByZWZlcmVuY2VzKS5cblx0ICogQWJzZW5jZSAoZ2hvc3QgbmFtZXMpIGFuZCBleHRlcm5hbCBjb2xsaXNpb25zIHN0YXkgc29mdCBgdW5rbm93bmAuXG5cdCAqIFJ1bnMgb25jZSBwZXIgdXNhZ2VzIHBhc3MgKHJlLWFybWVkIGJ5IHJlc2V0VXNhZ2VzKSwgbWlycm9yaW5nXG5cdCAqIHZhbGlkYXRlTG9va3VwUmVmZXJlbmNlczogcmVjb3JkaW5nIGhhcHBlbnMgb24gZXZlcnkgcGFzcywgYnV0IG9ubHlcblx0ICogdGhlIHVzYWdlcyBwYXNzIHNlZXMgdGhlIGNvbXBsZXRlIGRlY2xhcmF0aW9uIG1hcC5cblx0ICovXG5cdHByaXZhdGUgdmFsaWRhdGVQbGFpblR5cGVSZWZlcmVuY2VzICgpOiB2b2lkIHtcblx0XHRpZiAodGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzVmFsaWRhdGVkKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IHRydWU7XG5cdFx0Y29uc3Qgc2l0ZXNCeU5hbWUgPSBuZXcgTWFwPHN0cmluZywgeyBuYW1lOiBzdHJpbmc7IGxvY2F0aW9uOiBzdHJpbmc7IGZpbGU6IHN0cmluZyB9W10+KCk7XG5cdFx0Zm9yIChjb25zdCByZWYgb2YgdGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzKSB7XG5cdFx0XHRjb25zdCBzaXRlcyA9IHNpdGVzQnlOYW1lLmdldChyZWYubmFtZSkgPz8gW107XG5cdFx0XHRzaXRlcy5wdXNoKHJlZik7XG5cdFx0XHRzaXRlc0J5TmFtZS5zZXQocmVmLm5hbWUsIHNpdGVzKTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBbIG5hbWUsIHNpdGVzIF0gb2Ygc2l0ZXNCeU5hbWUpIHtcblx0XHRcdC8vIGFuIGltcG9ydCBiaW5kaW5nIGluIHRoZSByZWZlcmVuY2luZyBmaWxlIGFuY2hvcnMgdGhlIG5hbWUg4oCUXG5cdFx0XHQvLyB0aGUgYXV0aG9yIGFscmVhZHkgZGlzYW1iaWd1YXRlZCAodGhlIGltcG9ydCBtYXkganVzdCBwb2ludFxuXHRcdFx0Ly8gYXQgYW4gdW5hbmFseXphYmxlIGV4dGVybmFsIG1vZHVsZSwgd2hpY2ggc3RheXMgc29mdClcblx0XHRcdGNvbnN0IHVuYW5jaG9yZWQgPSBzaXRlcy5maWx0ZXIoKHNpdGUpID0+ICF0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoc2l0ZS5maWxlKT8uaGFzKG5hbWUpKTtcblx0XHRcdGlmICh1bmFuY2hvcmVkLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGRlY2xGaWxlcyA9IHRoaXMucGxhaW5UeXBlRGVjbGFyYXRpb25GaWxlcyhuYW1lKTtcblx0XHRcdGlmIChkZWNsRmlsZXMubGVuZ3RoIDwgMikge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IG1lc3NhZ2UgPSBgQW1iaWd1b3VzIHJlZmVyZW5jZSB0byB0eXBlICcke25hbWV9JzogJHtkZWNsRmlsZXMubGVuZ3RofSBkZWNsYXJhdGlvbnMgYCArXG5cdFx0XHRcdCdzaGFyZSB0aGUgbmFtZSBhbmQgbm8gaW1wb3J0IGRpc2FtYmlndWF0ZXMg4oCUIGltcG9ydCB0aGUgb25lIHlvdSBtZWFuJztcblx0XHRcdGNvbnN0IGRlY2xMb2NhdGlvbnMgPSBkZWNsRmlsZXMubWFwKChmaWxlKSA9PiB0aGlzLnBsYWluRGVjbExvY2F0aW9uKGZpbGUsIG5hbWUpKTtcblx0XHRcdGNvbnN0IGVycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7XG5cdFx0XHRcdG1lc3NhZ2UsXG5cdFx0XHRcdGxvY2F0aW9ucyA6IFsgLi4udW5hbmNob3JlZC5tYXAoKHNpdGUpID0+IHNpdGUubG9jYXRpb24pLCAuLi5kZWNsTG9jYXRpb25zIF1cblx0XHRcdH07XG5cdFx0XHR0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzLnB1c2goZXJyb3IpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBgZmlsZTpsaW5lOmNvbHVtbmAgb2YgYSByZWNvcmRlZCBkZWNsYXJhdGlvbiwgZm9yIHRoZSBhbWJpZ3VpdHlcblx0ICogcmVwb3J0LiBOb2RlcyByZWNvcmRlZCBkdXJpbmcgdHJhdmVyc2FsIGtlZXAgdGhlaXIgcG9zaXRpb25zOyBhXG5cdCAqIHN5bnRoZXRpYy91bnBvc2l0aW9uZWQgbm9kZSBmYWxscyBiYWNrIHRvIHRoZSBmaWxlIGl0c2VsZi5cblx0ICovXG5cdHByaXZhdGUgcGxhaW5EZWNsTG9jYXRpb24gKGZpbGU6IHN0cmluZywgbmFtZTogc3RyaW5nKTogc3RyaW5nIHtcblx0XHRjb25zdCBkZWNsID0gdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLmdldChmaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGNvbnN0IG5vZGUgPSBkZWNsPy5ub2RlO1xuXHRcdGxldCBsb2NhdGlvbiA9IGAke2ZpbGV9OjE6MWA7XG5cdFx0aWYgKG5vZGUgJiYgbm9kZS5wb3MgPj0gMCkge1xuXHRcdFx0Y29uc3Qgc291cmNlRmlsZSA9IG5vZGUuZ2V0U291cmNlRmlsZSgpO1xuXHRcdFx0Y29uc3QgbGluZSA9IHNvdXJjZUZpbGUuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24obm9kZS5nZXRTdGFydCgpKS5saW5lICsgMTtcblx0XHRcdGNvbnN0IGNvbHVtbiA9IHNvdXJjZUZpbGUuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24obm9kZS5nZXRTdGFydCgpKS5jaGFyYWN0ZXIgKyAxO1xuXHRcdFx0bG9jYXRpb24gPSBgJHtmaWxlfToke2xpbmV9OiR7Y29sdW1ufWA7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGxvY2F0aW9uO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGEgaGFyZC1mYWlsIGdyYXBoIHJlZmVyZW5jZSBlcnJvciB3aXRoIHRoZSByZWZlcmVuY2Ugc2l0ZSBhbmRcblx0ICogZXZlcnkgY2FuZGlkYXRlIGxvY2F0aW9uLlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yIChcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0cmVmTm9kZTogdHMuTm9kZSB8IHN0cmluZyxcblx0XHRyZXN1bHQ6IEV4dHJhY3Q8R3JhcGhUeXBlUmVmZXJlbmNlUmVzdWx0LCB7IHN0YXR1czogJ2FtYmlndW91cycgfCAnbm9uZScgfT5cblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSB0eXBlb2YgcmVmTm9kZSA9PT0gJ3N0cmluZycgPyByZWZOb2RlIDogdGhpcy5ub2RlTG9jYXRpb24ocmVmTm9kZSk7XG5cdFx0aWYgKHJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHRjb25zdCBjYW5kaWRhdGVMb2NhdGlvbnMgPSByZXN1bHQuY2FuZGlkYXRlcy5tYXAobiA9PiBgJHtuLnNvdXJjZUZpbGV9OiR7bi5saW5lfToke24uY29sdW1ufWApO1xuXHRcdFx0Y29uc3QgYW1iaWd1b3VzTWVzc2FnZSA9IGBBbWJpZ3VvdXMgcmVmZXJlbmNlIHRvIG1uZW1vbmljYSB0eXBlICcke25hbWV9JzogYCArXG5cdFx0XHRcdGAke3Jlc3VsdC5jYW5kaWRhdGVzLmxlbmd0aH0gdHlwZXMgc2hhcmUgdGhlIG5hbWUgYW5kIG5laXRoZXIgdGhlIHBhcmVudCBjaGFpbiBgICtcblx0XHRcdFx0J25vciB0aGUgaW1wb3J0cyBkaXNhbWJpZ3VhdGUnO1xuXHRcdFx0Y29uc3QgYW1iaWd1b3VzRXJyb3I6IFJlc29sdXRpb25FcnJvciA9IHtcblx0XHRcdFx0bWVzc2FnZSAgIDogYW1iaWd1b3VzTWVzc2FnZSxcblx0XHRcdFx0bG9jYXRpb25zIDogWyBsb2NhdGlvbiwgLi4uY2FuZGlkYXRlTG9jYXRpb25zIF0sXG5cdFx0XHR9O1xuXHRcdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKGFtYmlndW91c0Vycm9yKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgdW5yZXNvbHZlZE1lc3NhZ2UgPSBgVW5yZXNvbHZlZCByZWZlcmVuY2UgdG8gbW5lbW9uaWNhIHR5cGUgJyR7bmFtZX0nOiBubyB0eXBlIG1hdGNoZXMgYCArXG5cdFx0XHQnYnkgdmFsdWUgc2NvcGUsIGltcG9ydHMsIHBhcmVudCBjaGFpbiwgb3Igcm9vdCBwYXRoJztcblx0XHRjb25zdCB1bnJlc29sdmVkRXJyb3I6IFJlc29sdXRpb25FcnJvciA9IHsgbWVzc2FnZSA6IHVucmVzb2x2ZWRNZXNzYWdlLCBsb2NhdGlvbnMgOiBbIGxvY2F0aW9uIF0gfTtcblx0XHR0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzLnB1c2godW5yZXNvbHZlZEVycm9yKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBMb2NhdGlvbiAoYGZpbGU6bGluZTpjb2x1bW5gKSBvZiBhbiBBU1Qgbm9kZSwgZGVyaXZlZCB3aXRob3V0IHBhcmVudFxuXHQgKiBwb2ludGVycyB3aGVuIG5lY2Vzc2FyeS5cblx0ICovXG5cdHByaXZhdGUgbm9kZUxvY2F0aW9uIChub2RlOiB0cy5Ob2RlKTogc3RyaW5nIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5vZGU7XG5cdFx0d2hpbGUgKGN1cnJlbnQgJiYgIXRzLmlzU291cmNlRmlsZShjdXJyZW50KSkge1xuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRpZiAoIWN1cnJlbnQpIHtcblx0XHRcdGNvbnN0IGZhbGxiYWNrID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdFx0cmV0dXJuIGZhbGxiYWNrO1xuXHRcdH1cblx0XHRjb25zdCBzdGFydCA9IG5vZGUuZ2V0U3RhcnQoY3VycmVudCk7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKGN1cnJlbnQsIHN0YXJ0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke2N1cnJlbnQuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdHJldHVybiBsb2NhdGlvbjtcblx0fVxuXG5cdC8qKlxuXHQgKiBUcmFjayBhbGlhc2VzIG9mIHRoZSBtbmVtb25pY2EgbW9kdWxlIG9iamVjdCwgZS5nLjpcblx0ICogICBjb25zdCBtID0gbW5lbW9uaWNhO1xuXHQgKiAgIGNvbnN0IEFwcCA9IG07XG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrTW9kdWxlT2JqZWN0QWxpYXNlcyAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpIHx8ICF0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgaW5pdGlhbGl6ZXIgfSA9IG5vZGU7XG5cdFx0aWYgKCFpbml0aWFsaXplcikge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoaW5pdGlhbGl6ZXIpICYmIHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhpbml0aWFsaXplci50ZXh0KSkge1xuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuYWRkKG5vZGUubmFtZS50ZXh0KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgY3VzdG9tIGNvbGxlY3Rpb24gdmFyaWFibGVzLCBlLmcuOlxuXHQgKiAgIGNvbnN0IE15Q29sbGVjdGlvbiA9IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpO1xuXHQgKiAgIGNvbnN0IE90aGVyID0gTXlDb2xsZWN0aW9uO1xuXHQgKlxuXHQgKiBBbHNvIGRldGVjdHMgT3B0aW9uIEIgdXNlci1wcm92aWRlZCByZWdpc3RyeSBpbnRlcmZhY2VzOlxuXHQgKiAgIGV4cG9ydCBpbnRlcmZhY2UgTXlDb2xsZWN0aW9uUmVnaXN0cnkge31cblx0ICogICBjb25zdCBNeUNvbGxlY3Rpb24gPSBjcmVhdGVUeXBlc0NvbGxlY3Rpb248TXlDb2xsZWN0aW9uUmVnaXN0cnk+KCk7XG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrQ29sbGVjdGlvbkFsaWFzZXMgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSB8fCAhdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGluaXRpYWxpemVyIH0gPSBub2RlO1xuXHRcdGlmICghaW5pdGlhbGl6ZXIpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBEaXJlY3QgY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgY2FsbFxuXHRcdGlmICh0aGlzLmlzQ3JlYXRlVHlwZXNDb2xsZWN0aW9uQ2FsbChpbml0aWFsaXplcikpIHtcblx0XHRcdC8vIFRoZSBDTEkgcmUtYW5hbHl6ZXMgZXZlcnkgZmlsZSBvbiB0aGUgdXNhZ2VzIHBhc3MgKHNlZSByZXNldFVzYWdlcyk6XG5cdFx0XHQvLyBtaW50aW5nIGEgZnJlc2ggaWQgaGVyZSB3b3VsZCByZS1yZWdpc3RlciB0aGUgY29sbGVjdGlvbidzIHR5cGVzXG5cdFx0XHQvLyB1bmRlciBhIHNlY29uZCBgY29sbGVjdGlvbklkOjpgIHByZWZpeCBhbmQgZHVwbGljYXRlIGV2ZXJ5IGVtaXNzaW9uLlxuXHRcdFx0Y29uc3QgY29sbGVjdGlvbklkID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChub2RlLm5hbWUudGV4dCkgPz8gdGhpcy5uZXh0Q29sbGVjdGlvbklkKCk7XG5cdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuc2V0KG5vZGUubmFtZS50ZXh0LCBjb2xsZWN0aW9uSWQpO1xuXG5cdFx0XHRjb25zdCByZWdpc3RyeUludGVyZmFjZU5hbWUgPSB0aGlzLmV4dHJhY3RSZWdpc3RyeUludGVyZmFjZU5hbWUoXG5cdFx0XHRcdGluaXRpYWxpemVyIGFzIHRzLkNhbGxFeHByZXNzaW9uLFxuXHRcdFx0XHRzb3VyY2VGaWxlXG5cdFx0XHQpO1xuXHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKHNvdXJjZUZpbGUsIG5vZGUuZ2V0U3RhcnQoKSk7XG5cdFx0XHR0aGlzLmNvbGxlY3Rpb25JbmZvLnNldChjb2xsZWN0aW9uSWQsIHtcblx0XHRcdFx0dmFyaWFibGVOYW1lICAgICAgICAgIDogbm9kZS5uYW1lLnRleHQsXG5cdFx0XHRcdHNvdXJjZUZpbGUgICAgICAgICAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA6IHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSxcblx0XHRcdFx0bGluZSAgICAgICAgICAgICAgICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgICAgICAgICAgICAgICA6IGNoYXJhY3RlciArIDFcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEFsaWFzIG9mIGFub3RoZXIgY29sbGVjdGlvbiB2YXJpYWJsZVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRjb25zdCBleGlzdGluZyA9IHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5nZXQoaW5pdGlhbGl6ZXIudGV4dCk7XG5cdFx0XHRpZiAoZXhpc3RpbmcpIHtcblx0XHRcdFx0dGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLnNldChub2RlLm5hbWUudGV4dCwgZXhpc3RpbmcpO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSByZWdpc3RyeSBpbnRlcmZhY2UgbmFtZSBmcm9tIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbjxSZWdpc3RyeT4oKVxuXHQgKiB3aGVuIHRoZSBpbnRlcmZhY2UgaXMgZGVjbGFyZWQgaW4gdGhlIHNhbWUgc291cmNlIGZpbGUuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RSZWdpc3RyeUludGVyZmFjZU5hbWUgKFxuXHRcdGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGVcblx0KTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCB0eXBlQXJncyA9IGNhbGwudHlwZUFyZ3VtZW50cztcblx0XHRpZiAoIXR5cGVBcmdzIHx8IHR5cGVBcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBbIGZpcnN0VHlwZUFyZyBdID0gdHlwZUFyZ3M7XG5cdFx0aWYgKCF0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKGZpcnN0VHlwZUFyZykgfHwgIXRzLmlzSWRlbnRpZmllcihmaXJzdFR5cGVBcmcudHlwZU5hbWUpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IG5hbWUgPSBmaXJzdFR5cGVBcmcudHlwZU5hbWUudGV4dDtcblxuXHRcdC8vIENvbmZpcm0gdGhlIGludGVyZmFjZSBleGlzdHMgaW4gdGhlIHNhbWUgc291cmNlIGZpbGUuXG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc291cmNlRmlsZS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzSW50ZXJmYWNlRGVjbGFyYXRpb24oc3RhdGVtZW50KSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIG5hbWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBTdGFtcCBhIG5vZGUgd2l0aCBpdHMgY29sbGVjdGlvbidzIGVtaXNzaW9uIGluZm86IHRoZSBPcHRpb24gQiByZWdpc3RyeVxuXHQgKiBpbnRlcmZhY2UgbmFtZSBhbmQgdGhlIGNvbGxlY3Rpb24ncyBob21lIGZpbGUg4oCUIHRoZSBtb2R1bGUgdGhlIGdlbmVyYXRlZFxuXHQgKiBhdWdtZW50YXRpb24gbXVzdCB0YXJnZXQgKHRoZSBpbnRlcmZhY2UgaXMgY29uZmlybWVkIGRlY2xhcmVkIHRoZXJlKS5cblx0ICogQSB0eXBlJ3Mgb3duIHNvdXJjZUZpbGUgaXMgTk9UIHRoZSB0YXJnZXQ6IG11bHRpLWZpbGUgY29sbGVjdGlvbnMgZGVmaW5lXG5cdCAqIHR5cGVzIGFjcm9zcyBtYW55IG1vZHVsZXMgd2hpbGUgdGhlIGludGVyZmFjZSBsaXZlcyBhdCB0aGVcblx0ICogY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgY2FsbCBzaXRlLlxuXHQgKi9cblx0cHJpdmF0ZSBhcHBseUNvbGxlY3Rpb25FbWlzc2lvbkluZm8gKG5vZGU6IFR5cGVOb2RlLCBjb2xsZWN0aW9uSWQ/OiBzdHJpbmcpOiB2b2lkIHtcblx0XHRpZiAoIWNvbGxlY3Rpb25JZCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBpbmZvID0gdGhpcy5jb2xsZWN0aW9uSW5mby5nZXQoY29sbGVjdGlvbklkKTtcblx0XHRpZiAoIWluZm8pIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0bm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWUgPSBpbmZvLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZTtcblx0XHRub2RlLmNvbGxlY3Rpb25Tb3VyY2VGaWxlID0gaW5mby5zb3VyY2VGaWxlO1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGFuIGV4cHJlc3Npb24gaXMgYSBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSBjYWxsLlxuXHQgKiBIYW5kbGVzOlxuXHQgKiAgIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpXG5cdCAqICAgY3RjKCkgLy8gYWxpYXNlZCBpbXBvcnRcblx0ICogICBtbmVtb25pY2EuY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgLy8gbW9kdWxlIG9iamVjdCBtZXRob2Rcblx0ICogICBtLmNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIC8vIGFsaWFzZWQgbW9kdWxlIG9iamVjdFxuXHQgKi9cblx0cHJpdmF0ZSBpc0NyZWF0ZVR5cGVzQ29sbGVjdGlvbkNhbGwgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkNhbGxFeHByZXNzaW9uIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Y29uc3QgZXhwciA9IG5vZGUuZXhwcmVzc2lvbjtcblxuXHRcdC8vIERpcmVjdCBjYWxsIG9yIGFsaWFzZWQgaW1wb3J0OiBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSAvIGN0YygpXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIGV4cHIudGV4dCA9PT0gJ2NyZWF0ZVR5cGVzQ29sbGVjdGlvbicgfHxcblx0XHRcdFx0dGhpcy5jcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGV4cHIudGV4dCk7XG5cdFx0fVxuXG5cdFx0Ly8gTW9kdWxlIG9iamVjdCBtZXRob2Q6IG1uZW1vbmljYS5jcmVhdGVUeXBlc0NvbGxlY3Rpb24oKVxuXHRcdGlmIChcblx0XHRcdHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpICYmXG5cdFx0XHRleHByLm5hbWUudGV4dCA9PT0gJ2NyZWF0ZVR5cGVzQ29sbGVjdGlvbicgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcihleHByLmV4cHJlc3Npb24pICYmXG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoZXhwci5leHByZXNzaW9uLnRleHQpXG5cdFx0KSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogR2VuZXJhdGUgYSB1bmlxdWUgY29sbGVjdGlvbiBpZGVudGlmaWVyLlxuXHQgKi9cblx0cHJpdmF0ZSBuZXh0Q29sbGVjdGlvbklkICgpOiBzdHJpbmcge1xuXHRcdHRoaXMuY29sbGVjdGlvbkNvdW50ZXIrKztcblx0XHRjb25zdCByZXN1bHQgPSBgY29sbGVjdGlvbl8ke3RoaXMuY29sbGVjdGlvbkNvdW50ZXJ9YDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGEgbm9kZSBpcyBhIGRlZmluZSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgaXNEZWZpbmVDYWxsIChub2RlOiB0cy5Ob2RlKTogbm9kZSBpcyB0cy5DYWxsRXhwcmVzc2lvbiB7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIGRpcmVjdCBjYWxsOiBkZWZpbmUoJ1R5cGVOYW1lJywgLi4uKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIG1ldGhvZCBjYWxsOiBTb21lVHlwZS5kZWZpbmUoJ1N1YlR5cGUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gZXhwcmVzc2lvbi5uYW1lPy50ZXh0ID09PSAnZGVmaW5lJztcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogQ2hlY2sgaWYgYSBub2RlIGlzIGEgbGF6eSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgaXNMYXp5Q2FsbCAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuQ2FsbEV4cHJlc3Npb24ge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBkaXJlY3QgY2FsbDogbGF6eSgnVHlwZU5hbWUnLCBnZXR0ZXIsIC4uLilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2xhenknKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgbWV0aG9kIGNhbGw6IFNvbWVUeXBlLmxhenkoJ1N1YlR5cGUnLCBnZXR0ZXIsIC4uLilcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcmVzc2lvbikpIHtcblx0XHRcdHJldHVybiBleHByZXNzaW9uLm5hbWU/LnRleHQgPT09ICdsYXp5Jztcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0XHQqIEV4dHJhY3QgY29uZmlnIG9wdGlvbnMgZnJvbSBhbiBvYmplY3QgbGl0ZXJhbFxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsIChjb25maWdBcmc6IHRzLk9iamVjdExpdGVyYWxFeHByZXNzaW9uKTpcblx0XHR7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0ge1xuXHRcdGNvbnN0IGNvbmZpZzogeyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9ID0ge307XG5cblx0XHRmb3IgKGNvbnN0IHByb3Agb2YgY29uZmlnQXJnLnByb3BlcnRpZXMpIHtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSAmJiB0cy5pc0lkZW50aWZpZXIocHJvcC5uYW1lKSkge1xuXHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IHByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRpZiAocHJvcE5hbWUgPT09ICdzdHJpY3RDaGFpbicgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLnN0cmljdENoYWluID0gdHJ1ZTtcblx0XHRcdFx0fSBlbHNlIGlmIChwcm9wTmFtZSA9PT0gJ3N0cmljdENoYWluJyAmJiBwcm9wLmluaXRpYWxpemVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLnN0cmljdENoYWluID0gZmFsc2U7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdibG9ja0Vycm9ycycgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLmJsb2NrRXJyb3JzID0gdHJ1ZTtcblx0XHRcdFx0fSBlbHNlIGlmIChwcm9wTmFtZSA9PT0gJ2Jsb2NrRXJyb3JzJyAmJiBwcm9wLmluaXRpYWxpemVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLmJsb2NrRXJyb3JzID0gZmFsc2U7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gY29uZmlnO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IGNvbmZpZyBvcHRpb25zIGZyb20gZGVmaW5lKCkgY2FsbFxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdENvbmZpZyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0ge1xuXHRcdC8vIENvbmZpZyBpcyB0aGUgdGhpcmQgYXJndW1lbnQ6IGRlZmluZSgnTmFtZScsIGhhbmRsZXIsIGNvbmZpZylcblx0XHRjb25zdCBbICwgLCBjb25maWdBcmcgXSA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGlmICghY29uZmlnQXJnIHx8ICF0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGNvbmZpZ0FyZykpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRjb25zdCBjb25maWdSZXN1bHQgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjb25maWdBcmcpO1xuXHRcdHJldHVybiBjb25maWdSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHQqIENoZWNrIGlmIGEgbm9kZSBpcyBhIEBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHRcdCovXG5cdHByaXZhdGUgaXNEZWNvcmF0ZURlY29yYXRvciAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuRGVjb3JhdG9yIHtcblx0XHRpZiAoIXRzLmlzRGVjb3JhdG9yKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIEBkZWNvcmF0ZVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVjb3JhdGUnKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgQGRlY29yYXRlKCkgb3IgQGRlY29yYXRlKFBhcmVudFR5cGUpXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZXhwcmVzc2lvbikpIHtcblx0XHRcdGNvbnN0IGZuTmFtZSA9IGV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZm5OYW1lKSAmJiBmbk5hbWUudGV4dCA9PT0gJ2RlY29yYXRlJykge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gQ2hlY2sgZm9yIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSB3aGVyZSBNeUNvbGxlY3Rpb24gaXMgYSBjdXN0b20gY29sbGVjdGlvblxuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihmbk5hbWUpICYmXG5cdFx0XHRcdGZuTmFtZS5uYW1lLnRleHQgPT09ICdkZWNvcmF0ZScgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGZuTmFtZS5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGZuTmFtZS5leHByZXNzaW9uLnRleHQpXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIE1hcmsgYSBjYWxsIGV4cHJlc3Npb24gYXMgcHJvY2Vzc2VkIGFuZCByZXR1cm4gd2hldGhlciBpdCBhbHJlYWR5IHdhcy5cblx0ICovXG5cdHByaXZhdGUgbWFya1Byb2Nlc3NlZCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBib29sZWFuIHtcblx0XHRpZiAodGhpcy5wcm9jZXNzZWRDYWxscy5oYXMoY2FsbCkpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHR0aGlzLnByb2Nlc3NlZENhbGxzLmFkZChjYWxsKTtcblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogUHJvY2VzcyBhIGRlZmluZSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgcHJvY2Vzc0RlZmluZUNhbGwgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBleGFjdCBjYWxsIGhhcyBhbHJlYWR5IGJlZW4gcHJvY2Vzc2VkIChwcmV2ZW50cyBkdXBsaWNhdGVzIGZyb20gY2hhaW5lZCBjYWxscylcblx0XHRpZiAodGhpcy5tYXJrUHJvY2Vzc2VkKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgY29tcHV0ZWROYW1lcyA9IHRoaXMuZXh0cmFjdENvbXB1dGVkVHlwZU5hbWVzKGNhbGwpO1xuXHRcdGlmIChjb21wdXRlZE5hbWVzICE9PSB1bmRlZmluZWQpIHtcblx0XHRcdGZvciAoY29uc3QgdHlwZU5hbWUgb2YgY29tcHV0ZWROYW1lcykge1xuXHRcdFx0XHRjb25zdCBjb21wdXRlZENvbnRleHQgPSB0aGlzLmV4dHJhY3REZWZpbmVDb250ZXh0KGNhbGwsIHR5cGVOYW1lKTtcblx0XHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ29udGV4dChjYWxsLCBzb3VyY2VGaWxlLCBjb21wdXRlZENvbnRleHQsIHRydWUpO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEdldCB0aGUgdHlwZSBuYW1lIGFuZCBzb3VyY2UgY29udGV4dCBmcm9tIGFyZ3VtZW50c1xuXHRcdGNvbnN0IGRlZmluZUNvbnRleHQgPSB0aGlzLmV4dHJhY3REZWZpbmVDb250ZXh0KGNhbGwpO1xuXHRcdHRoaXMucHJvY2Vzc0RlZmluZUNvbnRleHQoY2FsbCwgc291cmNlRmlsZSwgZGVmaW5lQ29udGV4dCwgZmFsc2UpO1xuXHR9XG5cblx0cHJpdmF0ZSBwcm9jZXNzRGVmaW5lQ29udGV4dCAoXG5cdFx0Y2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRkZWZpbmVDb250ZXh0OiB7XG5cdFx0XHR0eXBlTmFtZT86IHN0cmluZztcblx0XHRcdHBhcmVudFR5cGU/OiBUeXBlTm9kZTtcblx0XHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0XHR9LFxuXHRcdG1ldGFkYXRhT25seTogYm9vbGVhblxuXHQpOiB2b2lkIHtcblx0XHQvLyBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGRlZmluZSgnQScpLmRlZmluZSgnQicpLCB3ZSB3YW50IHRoZSBwb3NpdGlvbiBvZiB0aGUgLmRlZmluZSgnQicpIHBhcnRcblx0XHQvLyBub3QgdGhlIHN0YXJ0IG9mIHRoZSBlbnRpcmUgZXhwcmVzc2lvblxuXHRcdGxldCBwb3NpdGlvbk5vZGU6IHRzLk5vZGUgPSBjYWxsO1xuXG5cdFx0Ly8gSWYgdGhpcyBpcyBhIGNoYWluZWQgY2FsbCwgZ2V0IHRoZSBwb3NpdGlvbiBvZiB0aGUgcHJvcGVydHkgYWNjZXNzIGV4cHJlc3Npb25cblx0XHQvLyB3aGljaCBpcyB0aGUgLmRlZmluZSBwYXJ0XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdC8vIFRoZSBleHByZXNzaW9uIGlzIHRoZSBwcm9wZXJ0eSBhY2Nlc3M6IChkZWZpbmUoJ1Jvb3RBc3luYycsIC4uLikpLmRlZmluZVxuXHRcdFx0Ly8gV2Ugd2FudCB0aGUgcG9zaXRpb24gb2YganVzdCB0aGUgLmRlZmluZSBwYXJ0XG5cdFx0XHQvLyBUaGlzIGlzIHRoZSAnZGVmaW5lJyBpZGVudGlmaWVyXG5cdFx0XHRwb3NpdGlvbk5vZGUgPSBjYWxsLmV4cHJlc3Npb24ubmFtZTtcblx0XHR9XG5cblx0XHRjb25zdCBzdGFydFBvcyA9IHBvc2l0aW9uTm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKTtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oc291cmNlRmlsZSwgc3RhcnRQb3MpO1xuXG5cdFx0aWYgKCFkZWZpbmVDb250ZXh0LnR5cGVOYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdDb3VsZCBub3QgZXh0cmFjdCB0eXBlIG5hbWUgZnJvbSBkZWZpbmUoKSBjYWxsJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IHR5cGVOYW1lIH0gPSBkZWZpbmVDb250ZXh0O1xuXG5cdFx0Ly8gRGV0ZXJtaW5lIHBhcmVudCB0eXBlIGFuZCBjb2xsZWN0aW9uIGJhc2VkIG9uIHRoZSBjYWxsIHNvdXJjZS5cblx0XHRjb25zdCBwYXJlbnROb2RlID0gZGVmaW5lQ29udGV4dC5wYXJlbnRUeXBlO1xuXHRcdGNvbnN0IHsgY29sbGVjdGlvbklkIH0gPSBkZWZpbmVDb250ZXh0O1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25maWcgb3B0aW9uc1xuXHRcdGNvbnN0IGNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZyhjYWxsKTtcblxuXHRcdC8vIENyZWF0ZSB0eXBlIG5vZGUgZmlyc3Qgc28gaXRzIGludGVybmFsIGZ1bGxQYXRoIChpbmNsdWRpbmcgYW55IGNvbGxlY3Rpb24gcHJlZml4KSBpcyByZXNvbHZlZC5cblx0XHRjb25zdCBub2RlID0gVHlwZUdyYXBoSW1wbC5jcmVhdGVOb2RlKFxuXHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRwYXJlbnROb2RlLFxuXHRcdFx0c291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdGxpbmUgKyAxLFxuXHRcdFx0Y2hhcmFjdGVyICsgMSxcblx0XHRcdGNvbGxlY3Rpb25JZFxuXHRcdCk7XG5cdFx0dGhpcy5hcHBseUNvbGxlY3Rpb25FbWlzc2lvbkluZm8obm9kZSwgY29sbGVjdGlvbklkKTtcblx0XHRub2RlLm1ldGFkYXRhT25seSA9IG1ldGFkYXRhT25seTtcblxuXHRcdC8vIFNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZSBkZXRlY3Rpb24gKGhhcmQtZmFpbCBsYXcpOiBrZXkgYnkgdGhlXG5cdFx0Ly8gcnVudGltZSBuYW1lc3BhY2Ug4oCUIGNvbGxlY3Rpb24gcm9vdHMgYDxjb2xsZWN0aW9uPjo6PG5hbWU+YCwgb3Jcblx0XHQvLyBgPHBhcmVudEZ1bGxQYXRoPi48bmFtZT5gIGZvciBzdWJ0eXBlc1xuXHRcdHRoaXMucmVjb3JkRGVmaW5lU2l0ZShcblx0XHRcdHBhcmVudE5vZGUgPyBgJHtwYXJlbnROb2RlLmZ1bGxQYXRofS4ke3R5cGVOYW1lfWAgOiBgJHtjb2xsZWN0aW9uSWQgPz8gJ2RlZmF1bHQnfTo6JHt0eXBlTmFtZX1gLFxuXHRcdFx0YCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWBcblx0XHQpO1xuXG5cdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gY29uc3RydWN0b3IgZnVuY3Rpb24g4oCUIHRoZSBuZXcgbm9kZSBhbmNob3JzXG5cdFx0Ly8gcmVsYXRpdmUtZmlyc3QgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb24gd2hpbGUgaXRzIG93biBzaWduYXR1cmVcblx0XHQvLyBpcyBiZWluZyByZWFkXG5cdFx0Y29uc3QgcHJldmlvdXNBbmNob3IgPSB0aGlzLmN1cnJlbnRHcmFwaEFuY2hvcjtcblx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IG5vZGU7XG5cdFx0dHJ5IHtcblx0XHRcdG5vZGUucHJvcGVydGllcyA9IHRoaXMuZXh0cmFjdFByb3BlcnRpZXMoY2FsbCk7XG5cblx0XHRcdC8vIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmb3IgVHlwZVJlZ2lzdHJ5IHNpZ25hdHVyZVxuXHRcdFx0bm9kZS5jb25zdHJ1Y3RvclBhcmFtcyA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zKGNhbGwpO1xuXHRcdH0gZmluYWxseSB7XG5cdFx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IHByZXZpb3VzQW5jaG9yO1xuXHRcdH1cblxuXHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yRXhwcmVzc2lvbihjYWxsKTtcblx0XHRub2RlLmluc3RhbmNlVHlwZU92ZXJyaWRlID0gdGhpcy5oYXNBbnlUaGlzQW5ub3RhdGlvbihjb25zdHJ1Y3RvckV4cHIpID8gJ2FueScgOiB1bmRlZmluZWQ7XG5cdFx0Ly8gQXN5bmMgY29uc3RydWN0b3IgZGV0ZWN0aW9uIChhc3luYyBtb2RpZmllciwgc3ludGFjdGljIG9ubHkpXG5cdFx0bm9kZS5pc0FzeW5jID0gdGhpcy5pc0FzeW5jQ29uc3RydWN0SGFuZGxlcih0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCkpO1xuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoXG5cdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkQ2hpbGQocGFyZW50Tm9kZSwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cblx0XHQvLyBDcmVhdGUgZGVmaW5pdGlvbiBpbmZvIHVzaW5nIHRoZSBub2RlJ3MgcmVzb2x2ZWQgZnVsbFBhdGhcblx0XHRjb25zdCBkZWZpbml0aW9uOiBEZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogcGFyZW50Tm9kZSA/IHBhcmVudE5vZGUuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiBjb25maWcuc3RyaWN0Q2hhaW4gPz8gdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogY29uZmlnLmJsb2NrRXJyb3JzID8/IGZhbHNlLFxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQobm9kZS5mdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdFx0aWYgKCFtZXRhZGF0YU9ubHkpIHtcblx0XHRcdHRoaXMuZWRzU2NvcGVCeU5vZGUuc2V0KGNhbGwsIG5vZGUuZnVsbFBhdGgpO1xuXG5cdFx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50OiBjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKSAtPiBtYXAgXCJVc2VyXCIgdG8gXCJVc2VyRW50aXR5XCJcblx0XHRcdC8vIEEgbXVsdGktaG9wIGluaXRpYWxpemVyIGJpbmRzIHRoZSBMQVNUIGhvcDogZGVmaW5lKCkgcmV0dXJucyB0aGVcblx0XHRcdC8vIGRlZmluZWQgdHlwZSdzIGNvbnN0cnVjdG9yIChGMTgpXG5cdFx0XHR0aGlzLnRyYWNrVmFyaWFibGVBc3NpZ25tZW50KGNhbGwsIHBhcmVudE5vZGUsIG5vZGUuZnVsbFBhdGgsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBQcm9jZXNzIGEgbGF6eSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgcHJvY2Vzc0xhenlDYWxsIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGlmIHRoaXMgZXhhY3QgY2FsbCBoYXMgYWxyZWFkeSBiZWVuIHByb2Nlc3NlZCAocHJldmVudHMgZHVwbGljYXRlcyBmcm9tIGNoYWluZWQgY2FsbHMpXG5cdFx0aWYgKHRoaXMubWFya1Byb2Nlc3NlZChjYWxsKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEdldCB0aGUgdHlwZSBuYW1lIGFuZCBzb3VyY2UgY29udGV4dCBmcm9tIGFyZ3VtZW50c1xuXHRcdGNvbnN0IGxhenlDb250ZXh0ID0gdGhpcy5leHRyYWN0TGF6eUNvbnRleHQoY2FsbCwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGRlZmluZSgnQScpLmxhenkoJ0InKSwgd2Ugd2FudCB0aGUgcG9zaXRpb24gb2YgdGhlIC5sYXp5KCdCJykgcGFydFxuXHRcdC8vIG5vdCB0aGUgc3RhcnQgb2YgdGhlIGVudGlyZSBleHByZXNzaW9uXG5cdFx0bGV0IHBvc2l0aW9uTm9kZTogdHMuTm9kZSA9IGNhbGw7XG5cblx0XHQvLyBJZiB0aGlzIGlzIGEgY2hhaW5lZCBjYWxsLCBnZXQgdGhlIHBvc2l0aW9uIG9mIHRoZSBwcm9wZXJ0eSBhY2Nlc3MgZXhwcmVzc2lvblxuXHRcdC8vIHdoaWNoIGlzIHRoZSAubGF6eSBwYXJ0XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdC8vIFRoZSBleHByZXNzaW9uIGlzIHRoZSBwcm9wZXJ0eSBhY2Nlc3M6IChkZWZpbmUoJ1Jvb3RBc3luYycsIC4uLikpLmxhenlcblx0XHRcdC8vIFdlIHdhbnQgdGhlIHBvc2l0aW9uIG9mIGp1c3QgdGhlIC5sYXp5IHBhcnRcblx0XHRcdC8vIFRoaXMgaXMgdGhlICdsYXp5JyBpZGVudGlmaWVyXG5cdFx0XHRwb3NpdGlvbk5vZGUgPSBjYWxsLmV4cHJlc3Npb24ubmFtZTtcblx0XHR9XG5cblx0XHRjb25zdCBzdGFydFBvcyA9IHBvc2l0aW9uTm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKTtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oc291cmNlRmlsZSwgc3RhcnRQb3MpO1xuXG5cdFx0Ly8gVGhlIHVubmFtZWQgZm9ybXMg4oCUIGxhenkoZ2V0dGVyKSwgVHlwZS5sYXp5KGdldHRlciwgY29uZmlnPyksXG5cdFx0Ly8gbGF6eShzb3VyY2UsIGdldHRlciwgY29uZmlnPykg4oCUIHRocm93IFRZUEVOQU1FX01VU1RfQkVfQV9TVFJJTkcgYXRcblx0XHQvLyBydW50aW1lICh0aGUgbmFtZSBpcyByZXF1aXJlZCksIHNvIGdlbmVyYXRpbmcgYSB0eXBlIGZyb20gdGhlXG5cdFx0Ly8gZ2V0dGVyJ3MgY29uc3RydWN0b3IgbmFtZSB3b3VsZCBibGVzcyBjb2RlIHRoYXQgY3Jhc2hlcy4gVGhleSBhcmVcblx0XHQvLyBhbiBhbmFseXplciBlcnJvciBuYW1pbmcgdGhlIGNhbGwgc2l0ZSBhbmQgdGhlIHJlcXVpcmVkIGZvcm0uXG5cdFx0Y29uc3QgbGF6eUFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0aWYgKGxhenlBcmdzICYmIGxhenlBcmdzLm5hbWUgPT09IHVuZGVmaW5lZCkge1xuXHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdG1lc3NhZ2UgOiAnbGF6eSgpIHJlcXVpcmVzIGEgdHlwZSBuYW1lOiBsYXp5KFxcJ05hbWVcXCcsIGdldHRlciknLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGlmICghbGF6eUNvbnRleHQudHlwZU5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0NvdWxkIG5vdCBleHRyYWN0IHR5cGUgbmFtZSBmcm9tIGxhenkoKSBjYWxsJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IHR5cGVOYW1lIH0gPSBsYXp5Q29udGV4dDtcblxuXHRcdC8vIERldGVybWluZSBwYXJlbnQgdHlwZSBhbmQgY29sbGVjdGlvbiBiYXNlZCBvbiB0aGUgY2FsbCBzb3VyY2UuXG5cdFx0Y29uc3QgcGFyZW50Tm9kZSA9IGxhenlDb250ZXh0LnBhcmVudFR5cGU7XG5cdFx0Y29uc3QgeyBjb2xsZWN0aW9uSWQgfSA9IGxhenlDb250ZXh0O1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25maWcgb3B0aW9uc1xuXHRcdGNvbnN0IGNvbmZpZyA9IHRoaXMuZXh0cmFjdExhenlDb25maWcoY2FsbCk7XG5cblx0XHQvLyBDcmVhdGUgdHlwZSBub2RlIGZpcnN0IHNvIGl0cyBpbnRlcm5hbCBmdWxsUGF0aCAoaW5jbHVkaW5nIGFueSBjb2xsZWN0aW9uIHByZWZpeCkgaXMgcmVzb2x2ZWQuXG5cdFx0Y29uc3Qgbm9kZSA9IFR5cGVHcmFwaEltcGwuY3JlYXRlTm9kZShcblx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0cGFyZW50Tm9kZSxcblx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRsaW5lICsgMSxcblx0XHRcdGNoYXJhY3RlciArIDEsXG5cdFx0XHRjb2xsZWN0aW9uSWRcblx0XHQpO1xuXHRcdHRoaXMuYXBwbHlDb2xsZWN0aW9uRW1pc3Npb25JbmZvKG5vZGUsIGNvbGxlY3Rpb25JZCk7XG5cblx0XHQvLyBTYW1lLW5hbWVzcGFjZSBkdXBsaWNhdGUgZGV0ZWN0aW9uIChoYXJkLWZhaWwgbGF3KVxuXHRcdHRoaXMucmVjb3JkRGVmaW5lU2l0ZShcblx0XHRcdHBhcmVudE5vZGUgPyBgJHtwYXJlbnROb2RlLmZ1bGxQYXRofS4ke3R5cGVOYW1lfWAgOiBgJHtjb2xsZWN0aW9uSWQgPz8gJ2RlZmF1bHQnfTo6JHt0eXBlTmFtZX1gLFxuXHRcdFx0YCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWBcblx0XHQpO1xuXG5cdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gdGhlIGNvbnN0cnVjdG9yIHJldHVybmVkIGJ5IHRoZSBsYXp5IGdldHRlclxuXHRcdC8vIOKAlCB0aGUgbmV3IG5vZGUgYW5jaG9ycyByZWxhdGl2ZS1maXJzdCBncmFwaCByZWZlcmVuY2UgcmVzb2x1dGlvblxuXHRcdGNvbnN0IHByZXZpb3VzQW5jaG9yID0gdGhpcy5jdXJyZW50R3JhcGhBbmNob3I7XG5cdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBub2RlO1xuXHRcdHRyeSB7XG5cdFx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzKGNhbGwpO1xuXG5cdFx0XHQvLyBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZm9yIFR5cGVSZWdpc3RyeSBzaWduYXR1cmVcblx0XHRcdG5vZGUuY29uc3RydWN0b3JQYXJhbXMgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyhjYWxsKTtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBwcmV2aW91c0FuY2hvcjtcblx0XHR9XG5cblx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCk7XG5cdFx0bm9kZS5pbnN0YW5jZVR5cGVPdmVycmlkZSA9IHRoaXMuaGFzQW55VGhpc0Fubm90YXRpb24oY29uc3RydWN0b3JFeHByKSA/ICdhbnknIDogdW5kZWZpbmVkO1xuXHRcdC8vIEFzeW5jIGNvbnN0cnVjdG9yIGRldGVjdGlvbiAoYXN5bmMgbW9kaWZpZXIsIHN5bnRhY3RpYyBvbmx5KVxuXHRcdG5vZGUuaXNBc3luYyA9IHRoaXMuaXNBc3luY0NvbnN0cnVjdEhhbmRsZXIodGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpKTtcblxuXHRcdC8vIEFkZCB0byBncmFwaFxuXHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZENoaWxkKHBhcmVudE5vZGUsIG5vZGUpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZFJvb3Qobm9kZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ3JlYXRlIGRlZmluaXRpb24gaW5mbyB1c2luZyB0aGUgbm9kZSdzIHJlc29sdmVkIGZ1bGxQYXRoXG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IHR5cGVOYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlZmluZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IHBhcmVudE5vZGUgPyBwYXJlbnROb2RlLmZ1bGxQYXRoIDogbnVsbCxcblx0XHRcdHN0cmljdENoYWluIDogY29uZmlnLnN0cmljdENoYWluID8/IHRydWUsXG5cdFx0XHRibG9ja0Vycm9ycyA6IGNvbmZpZy5ibG9ja0Vycm9ycyA/PyBmYWxzZSxcblx0XHR9O1xuXHRcdHRoaXMuZGVmaW5pdGlvbnMuc2V0KG5vZGUuZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXHRcdHRoaXMuZWRzU2NvcGVCeU5vZGUuc2V0KGNhbGwsIG5vZGUuZnVsbFBhdGgpO1xuXG5cdFx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudDogY29uc3QgTGF6eVR5cGUgPSBsYXp5KCdMYXp5VHlwZScsIC4uLikgLT4gbWFwIFwiTGF6eVR5cGVcIiAtPiBcIkxhenlUeXBlXCJcblx0XHQvLyBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGNvbnN0IFggPSBsYXp5KCdBJykuZGVmaW5lKCdCJyksIHdlIHdhbnQgdG8gbWFwIFggLT4gQSAodGhlIHJvb3QpXG5cdFx0dGhpcy50cmFja1ZhcmlhYmxlQXNzaWdubWVudChjYWxsLCBwYXJlbnROb2RlLCBub2RlLmZ1bGxQYXRoLCBzb3VyY2VGaWxlKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGxhenkoKSBjYWxsIGFyZ3VtZW50cyBpbnRvIGEgbm9ybWFsaXplZCBzaGFwZS5cblx0ICogSGFuZGxlcyBuYW1lZC91bm5hbWVkIGFuZCBleHBsaWNpdC1zb3VyY2UgZm9ybXMsIGJvdGggYXMgZnJlZSBjYWxsc1xuXHQgKiBhbmQgYXMgbWV0aG9kIGNhbGxzLiBUaGUgdW5uYW1lZCBzaGFwZXMgcmV0dXJuIGBuYW1lOiB1bmRlZmluZWRgIOKAlFxuXHQgKiBwcm9jZXNzTGF6eUNhbGwgcmVqZWN0cyB0aGVtIHdpdGggYW4gYW5hbHl6ZXIgZXJyb3IgKHRoZSBydW50aW1lXG5cdCAqIHJlcXVpcmVzIHRoZSBuYW1lKSwgc28gbm8gdHlwZSBpcyBnZW5lcmF0ZWQgZm9yIHRoZW0uXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q2FsbEFyZ3MgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKToge1xuXHRcdHNvdXJjZT86IHRzLkV4cHJlc3Npb247XG5cdFx0bmFtZT86IHN0cmluZztcblx0XHRnZXR0ZXI6IHRzLkV4cHJlc3Npb247XG5cdFx0Y29uZmlnPzogdHMuRXhwcmVzc2lvbjtcblx0fSB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGNvbnN0IGlzTWV0aG9kQ2FsbCA9IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbik7XG5cblx0XHRpZiAoaXNNZXRob2RDYWxsKSB7XG5cdFx0XHQvLyBTb3VyY2UgaXMgdGhlIG9iamVjdCBvZiB0aGUgcHJvcGVydHkgYWNjZXNzOiBUeXBlLmxhenkoLi4uKVxuXHRcdFx0Y29uc3Qgc291cmNlID0gY2FsbC5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IFsgbWV0aG9kRmlyc3RBcmcgXSA9IGFyZ3M7XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKG1ldGhvZEZpcnN0QXJnKSkge1xuXHRcdFx0XHQvLyBUeXBlLmxhenkoJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRcdGlmIChhcmdzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0c291cmNlLFxuXHRcdFx0XHRcdG5hbWUgICA6IG1ldGhvZEZpcnN0QXJnLnRleHQsXG5cdFx0XHRcdFx0Z2V0dGVyIDogYXJnc1sgMSBdLFxuXHRcdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDIgXSxcblx0XHRcdFx0fTtcblx0XHRcdH1cblx0XHRcdC8vIFR5cGUubGF6eShnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRzb3VyY2UsXG5cdFx0XHRcdGdldHRlciA6IG1ldGhvZEZpcnN0QXJnLFxuXHRcdFx0XHRjb25maWcgOiBhcmdzWyAxIF0sXG5cdFx0XHR9O1xuXHRcdH1cblxuXHRcdC8vIEZyZWUgY2FsbDogbGF6eSguLi4pXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGFyZ3M7XG5cblx0XHQvLyBFeHBsaWNpdC1zb3VyY2UgZm9ybTogbGF6eShzb3VyY2UsICdOYW1lJywgZ2V0dGVyLCBjb25maWc/KVxuXHRcdC8vIG9yIGxhenkoc291cmNlLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIgJiYgdHMuaXNJZGVudGlmaWVyKGZpcnN0QXJnKSkge1xuXHRcdFx0Y29uc3QgWyAsIHNlY29uZEFyZyBdID0gYXJncztcblx0XHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoc2Vjb25kQXJnKSkge1xuXHRcdFx0XHQvLyBsYXp5KHNvdXJjZSwgJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRcdGlmIChhcmdzLmxlbmd0aCA8IDMpIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0c291cmNlIDogZmlyc3RBcmcsXG5cdFx0XHRcdFx0bmFtZSAgIDogc2Vjb25kQXJnLnRleHQsXG5cdFx0XHRcdFx0Z2V0dGVyIDogYXJnc1sgMiBdLFxuXHRcdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDMgXSxcblx0XHRcdFx0fTtcblx0XHRcdH1cblx0XHRcdC8vIGxhenkoc291cmNlLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRzb3VyY2UgOiBmaXJzdEFyZyxcblx0XHRcdFx0Z2V0dGVyIDogc2Vjb25kQXJnLFxuXHRcdFx0XHRjb25maWcgOiBhcmdzWyAyIF0sXG5cdFx0XHR9O1xuXHRcdH1cblxuXHRcdC8vIE5hbWVkIHJvb3QgZm9ybTogbGF6eSgnTmFtZScsIGdldHRlciwgY29uZmlnPylcblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGZpcnN0QXJnKSkge1xuXHRcdFx0aWYgKGFyZ3MubGVuZ3RoIDwgMikge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0bmFtZSAgIDogZmlyc3RBcmcudGV4dCxcblx0XHRcdFx0Z2V0dGVyIDogYXJnc1sgMSBdLFxuXHRcdFx0XHRjb25maWcgOiBhcmdzWyAyIF0sXG5cdFx0XHR9O1xuXHRcdH1cblxuXHRcdC8vIFVubmFtZWQgcm9vdCBmb3JtOiBsYXp5KGdldHRlciwgY29uZmlnPylcblx0XHRyZXR1cm4ge1xuXHRcdFx0Z2V0dGVyIDogZmlyc3RBcmcsXG5cdFx0XHRjb25maWcgOiBhcmdzWyAxIF0sXG5cdFx0fTtcblx0fVxuXG5cdC8qKlxuXHQgKiBVbndyYXAgdGhlIGNvbnN0cnVjdG9yIHJldHVybmVkIGJ5IGEgbGF6eSBnZXR0ZXIuXG5cdCAqIFN1cHBvcnRzOlxuXHQgKiAgICgpID0+IGNsYXNzIE5hbWUge31cblx0ICogICAoKSA9PiBmdW5jdGlvbiBOYW1lKCkge31cblx0ICogICAoKSA9PiB7IHJldHVybiBjbGFzcyBOYW1lIHt9OyB9XG5cdCAqICAgZnVuY3Rpb24gKCkgeyByZXR1cm4gZnVuY3Rpb24gTmFtZSgpIHt9OyB9XG5cdCAqL1xuXHRwcml2YXRlIHVud3JhcExhenlHZXR0ZXIgKGdldHRlckV4cHI6IHRzLkV4cHJlc3Npb24pOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGdldHRlckV4cHIpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGdldHRlckV4cHI7XG5cdFx0XHRpZiAoIXRzLmlzQmxvY2soYm9keSkpIHtcblx0XHRcdFx0cmV0dXJuIGJvZHk7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IHN0bXQgb2YgYm9keS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChzdG10KSAmJiBzdG10LmV4cHJlc3Npb24pIHtcblx0XHRcdFx0XHRyZXR1cm4gc3RtdC5leHByZXNzaW9uO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihnZXR0ZXJFeHByKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBnZXR0ZXJFeHByO1xuXHRcdFx0Zm9yIChjb25zdCBzdG10IG9mIGJvZHkuc3RhdGVtZW50cykge1xuXHRcdFx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQoc3RtdCkgJiYgc3RtdC5leHByZXNzaW9uKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHN0bXQuZXhwcmVzc2lvbjtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBOb3QgYSByZWNvZ25pemVkIGdldHRlciBwYXR0ZXJuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGEgY29uc3RydWN0b3IgbmFtZSBmcm9tIGEgY2xhc3MgZXhwcmVzc2lvbiwgY2xhc3MgZGVjbGFyYXRpb24sXG5cdCAqIG9yIG5hbWVkIGZ1bmN0aW9uIGV4cHJlc3Npb24uXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3Rvck5hbWUgKGNvbnN0cnVjdG9yRXhwcjogQ29uc3RydWN0b3JIYW5kbGVyKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSAmJiBjb25zdHJ1Y3RvckV4cHIubmFtZSkge1xuXHRcdFx0cmV0dXJuIGNvbnN0cnVjdG9yRXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0NsYXNzRGVjbGFyYXRpb24oY29uc3RydWN0b3JFeHByKSAmJiBjb25zdHJ1Y3RvckV4cHIubmFtZSkge1xuXHRcdFx0cmV0dXJuIGNvbnN0cnVjdG9yRXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpICYmIGNvbnN0cnVjdG9yRXhwci5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gY29uc3RydWN0b3JFeHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSB0eXBlIG5hbWUgZnJvbSBlaXRoZXIgYSBkZWZpbmUoKSBvciBsYXp5KCkgY2FsbC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRoaXMuaXNEZWZpbmVDYWxsKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5leHRyYWN0VHlwZU5hbWUoY2FsbCk7XG5cdFx0fVxuXHRcdGlmICh0aGlzLmlzTGF6eUNhbGwoY2FsbCkpIHtcblx0XHRcdGNvbnN0IGFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0XHRpZiAoIWFyZ3MpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGlmIChhcmdzLm5hbWUpIHtcblx0XHRcdFx0cmV0dXJuIGFyZ3MubmFtZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMudW53cmFwTGF6eUdldHRlcihhcmdzLmdldHRlcik7XG5cdFx0XHRpZiAoY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRcdHJldHVybiB0aGlzLmV4dHJhY3RDb25zdHJ1Y3Rvck5hbWUoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSBmdWxsIGxhenkoKSBjYWxsIGNvbnRleHQ6IHR5cGUgbmFtZSwgcGFyZW50IHR5cGUsIGFuZCBjb2xsZWN0aW9uLlxuXHQgKiBIYW5kbGVzIGRpcmVjdCBjYWxscywgcHJvcGVydHktYWNjZXNzIGNhbGxzLCBjaGFpbmVkIGNhbGxzLCBhbmQgdGhlXG5cdCAqIGV4cGxpY2l0LXNvdXJjZSBmb3JtIGBsYXp5KHNvdXJjZSwgJ1R5cGVOYW1lJywgZ2V0dGVyKWAuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q29udGV4dCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB7XG5cdFx0dHlwZU5hbWU/OiBzdHJpbmc7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Y29uc3QgYXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRpZiAoIWFyZ3MpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRsZXQgdHlwZU5hbWU6IHN0cmluZyB8IHVuZGVmaW5lZCA9IGFyZ3MubmFtZTtcblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLnVud3JhcExhenlHZXR0ZXIoYXJncy5nZXR0ZXIpO1xuXHRcdFx0aWYgKGNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0XHR0eXBlTmFtZSA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yTmFtZShjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBjYWxsO1xuXG5cdFx0Ly8gRGlyZWN0IGNhbGw6IGxhenkoJ1R5cGVOYW1lJywgLi4uKSBvciBsYXp5KHNvdXJjZSwgJ1R5cGVOYW1lJywgZ2V0dGVyKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnbGF6eScpIHtcblx0XHRcdGlmIChhcmdzLnNvdXJjZSAmJiB0cy5pc0lkZW50aWZpZXIoYXJncy5zb3VyY2UpKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2UoYXJncy5zb3VyY2UudGV4dCk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXHRcdFx0Ly8gUGxhaW4gcm9vdCBsYXp5IGluIGRlZmF1bHQgY29sbGVjdGlvblxuXHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUgfTtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSBhY2Nlc3M6IFgubGF6eSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnbGF6eScpIHtcblx0XHRcdGNvbnN0IG9iaiA9IGV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblxuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihvYmopKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uob2JqLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0XHRcdHBhcmVudFR5cGUgICA6IHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSxcblx0XHRcdFx0XHRjb2xsZWN0aW9uSWQgOiBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCxcblx0XHRcdFx0fTtcblx0XHRcdH1cblxuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gTmVzdGVkIGFjY2VzczogaW5zdGFuY2UuVHlwZS5sYXp5IC0gdHJ5IHRvIHJlc29sdmVcblx0XHRcdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4ob2JqKTtcblx0XHRcdFx0aWYgKGNoYWluLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShjaGFpbi5qb2luKCcuJykpO1xuXHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSB9O1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gRGV0ZXJtaW5lIHRoZSBjb2xsZWN0aW9uIGNvbnRleHQgZnJvbSB0aGUgcm9vdCBvZiB0aGUgY2hhaW4gc28gdGhhdFxuXHRcdFx0XHQvLyBjdXN0b20tY29sbGVjdGlvbiB0eXBlcyBkbyBub3QgZ2V0IGNvbmZ1c2VkIHdpdGggZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzLlxuXHRcdFx0XHRjb25zdCByb290SWQgPSB0aGlzLmdldFJvb3RJZGVudGlmaWVyKG9iai5leHByZXNzaW9uKTtcblx0XHRcdFx0Y29uc3QgZXhwZWN0ZWRDb2xsZWN0aW9uSWQgPSByb290SWRcblx0XHRcdFx0XHQ/IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShyb290SWQudGV4dCkuY29sbGVjdGlvbklkXG5cdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHRcdFx0Ly8gQ2hhaW5lZCBjYWxsOiBkZWZpbmUoJ0EnKS5sYXp5KCdCJykgb3IgbGF6eSgnQScpLmxhenkoJ0InKVxuXHRcdFx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwob2JqKSkge1xuXHRcdFx0XHRcdHRoaXMucHJvY2Vzc0RlZmluZUNhbGwob2JqLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRpZiAodGhpcy5pc0xhenlDYWxsKG9iaikpIHtcblx0XHRcdFx0XHR0aGlzLnByb2Nlc3NMYXp5Q2FsbChvYmosIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudFR5cGVOYW1lID0gdGhpcy5leHRyYWN0TW5lbW9uaWNhVHlwZU5hbWUob2JqKTtcblx0XHRcdFx0XHRpZiAocGFyZW50VHlwZU5hbWUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKHBhcmVudFR5cGVOYW1lLCBleHBlY3RlZENvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIEJ1aWxkZXIgbG9va3VwIGNoYWluOiBBcHAubG9va3VwKCdVc2VyJykubGF6eSgnQWRtaW4nKVxuXHRcdFx0XHRpZiAodGhpcy5pc0xvb2t1cENhbGwob2JqKSkge1xuXHRcdFx0XHRcdGNvbnN0IGxvb2tlZFVwUGF0aCA9IHRoaXMucmVzb2x2ZUxvb2t1cFBhdGgob2JqKTtcblx0XHRcdFx0XHRpZiAobG9va2VkVXBQYXRoKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShsb29rZWRVcFBhdGgpO1xuXHRcdFx0XHRcdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlLmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBjb25maWcgb3B0aW9ucyBmcm9tIGxhenkoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q29uZmlnIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSB7XG5cdFx0Y29uc3QgYXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRpZiAoIWFyZ3MgfHwgIWFyZ3MuY29uZmlnIHx8ICF0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGFyZ3MuY29uZmlnKSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IGNvbmZpZ1Jlc3VsdCA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGFyZ3MuY29uZmlnKTtcblx0XHRyZXR1cm4gY29uZmlnUmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIERvZXMgdGhlIGhhbmRsZXIgbmFtZSBhIGdlbmVyYXRlZCB0eXBlIOKAlCBkaXJlY3RseSwgb3IgdGhyb3VnaCB0aGUgdHlwZVxuXHQgKiBhbGlhc2VzLCBpbnRlcmZhY2VzIGFuZCBjbGFzc2VzIGl0IHJlZmVyZW5jZXMgKGZvbGxvd2VkIGFjcm9zcyBmaWxlcyxcblx0ICogZWFjaCBkZWNsYXJhdGlvbiBvbmNlKT8gU3VjaCBhIGhhbmRsZXIgaXMgdHlwZWQgYnkgaXRzIG93biByZWdpc3RyeVxuXHQgKiBlbnRyeSwgc28gaXRzIHZhbHVlIGNhbm5vdCBiZSBkZXJpdmVkLlxuXHQgKi9cblx0cHJpdmF0ZSBoYXNHZW5lcmF0ZWRUeXBlUmVmZXJlbmNlIChoYW5kbGVyOiBDb25zdHJ1Y3RvckhhbmRsZXIgfCB1bmRlZmluZWQpOiBib29sZWFuIHtcblx0XHRpZiAoIWhhbmRsZXIpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Y29uc3QgdmlzaXRlZCA9IG5ldyBTZXQ8dHMuTm9kZT4oKTtcblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnJlZmVyZW5jZXNHZW5lcmF0ZWRUeXBlKGhhbmRsZXIsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSwgdmlzaXRlZCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdHByaXZhdGUgcmVmZXJlbmNlc0dlbmVyYXRlZFR5cGUgKG5vZGU6IHRzLk5vZGUsIGZpbGU6IHN0cmluZywgdmlzaXRlZDogU2V0PHRzLk5vZGU+KTogYm9vbGVhbiB7XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihub2RlKSAmJiB0aGlzLmdlbmVyYXRlZFR5cGVJbXBvcnRzLmdldChmaWxlKT8uaGFzKG5vZGUudGV4dCkpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHQvLyBgdHlwZSBYID0g4oCmYCwgYHRoaXM6IFhgLCBgaW50ZXJmYWNlIFggZXh0ZW5kcyBZYDogZm9sbG93IHRoZSBuYW1lZFxuXHRcdC8vIGRlY2xhcmF0aW9uLCByZXNvbHZlZCBmcm9tIHRoZSBmaWxlIHRoYXQgdXNlcyB0aGUgbmFtZVxuXHRcdGxldCByZWZlcmVuY2VkTmFtZTogdHMuSWRlbnRpZmllciB8IHVuZGVmaW5lZDtcblx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZShub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS50eXBlTmFtZSkpIHtcblx0XHRcdHJlZmVyZW5jZWROYW1lID0gbm9kZS50eXBlTmFtZTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzRXhwcmVzc2lvbldpdGhUeXBlQXJndW1lbnRzKG5vZGUpICYmIHRzLmlzSWRlbnRpZmllcihub2RlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZWZlcmVuY2VkTmFtZSA9IG5vZGUuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0aWYgKHJlZmVyZW5jZWROYW1lKSB7XG5cdFx0XHRjb25zdCBkZWNsYXJhdGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24ocmVmZXJlbmNlZE5hbWUudGV4dCwgZmlsZSk7XG5cdFx0XHRpZiAoZGVjbGFyYXRpb24gJiYgIXZpc2l0ZWQuaGFzKGRlY2xhcmF0aW9uLm5vZGUpKSB7XG5cdFx0XHRcdHZpc2l0ZWQuYWRkKGRlY2xhcmF0aW9uLm5vZGUpO1xuXHRcdFx0XHRpZiAodGhpcy5yZWZlcmVuY2VzR2VuZXJhdGVkVHlwZShkZWNsYXJhdGlvbi5ub2RlLCBkZWNsYXJhdGlvbi5maWxlLCB2aXNpdGVkKSkge1xuXHRcdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGNvbnN0IGNoaWxkcmVuOiB0cy5Ob2RlW10gPSBbXTtcblx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgY2hpbGQgPT4ge1xuXHRcdFx0Y2hpbGRyZW4ucHVzaChjaGlsZCk7XG5cdFx0fSk7XG5cdFx0Zm9yIChjb25zdCBjaGlsZCBvZiBjaGlsZHJlbikge1xuXHRcdFx0aWYgKHRoaXMucmVmZXJlbmNlc0dlbmVyYXRlZFR5cGUoY2hpbGQsIGZpbGUsIHZpc2l0ZWQpKSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHRwcml2YXRlIGhhc1NlbGZUeXBlQW5ub3RhdGlvbiAoaGFuZGxlcjogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkLCBmdWxsUGF0aDogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0aWYgKCFoYW5kbGVyIHx8ICF0cy5pc0Z1bmN0aW9uTGlrZShoYW5kbGVyKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblx0XHRjb25zdCB0eXBlTmFtZSA9IGZ1bGxQYXRoLnNwbGl0KCcuJykucG9wKCk7XG5cdFx0Zm9yIChjb25zdCBwYXJhbWV0ZXIgb2YgaGFuZGxlci5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihwYXJhbWV0ZXIubmFtZSkgfHwgcGFyYW1ldGVyLm5hbWUudGV4dCAhPT0gJ3RoaXMnIHx8ICFwYXJhbWV0ZXIudHlwZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGFubm90YXRpb24gPSBwYXJhbWV0ZXIudHlwZS5nZXRUZXh0KCk7XG5cdFx0XHRjb25zdCByZXN1bHQgPSBhbm5vdGF0aW9uID09PSB0eXBlTmFtZSB8fCBhbm5vdGF0aW9uLmVuZHNXaXRoKGAuJHt0eXBlTmFtZX1gKSB8fFxuXHRcdFx0XHRhbm5vdGF0aW9uID09PSBgSW5zdGFuY2VUeXBlPHR5cGVvZiAke3R5cGVOYW1lfT5gO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIFRydWUgd2hlbiBhIGRlZmluZSBob3Agc2l0cyBvbiBhIGNoYWluIHRoYXQgc3RhcnRzIGF0IHRoZSBmcmVlXG5cdCAqIGRlZmluZSgpIG9yIGxvb2t1cCgpIOKAlCB0aGUgdmFsdWUgdGhlbiBjYXJyaWVzIHRoZSBnbG9iYWxcblx0ICogVHlwZVJlZ2lzdHJ5LCBub3QgYSByZWdpc3RyeSBvZiBpdHMgb3duLiBGcmVlIHdoZW46IHRoZSBjYWxsIGlzIHRoZVxuXHQgKiBmcmVlIGBkZWZpbmUoJ1gnLCDigKYpYCAvIGBsYXp5KCdYJywg4oCmKWAgcm9vdCAoYW4gZXhwbGljaXQtc291cmNlXG5cdCAqIGBkZWZpbmUoc291cmNlLCAnWCcsIOKApilgIG9ubHkgd2hlbiBpdHMgc291cmNlIGlzIGZyZWUpOyBpdHMgcGFyZW50XG5cdCAqIHR5cGUgd2FzIGRlZmluZWQgb24gYSBmcmVlIGNoYWluOyBvciBpdHMgcmVjZWl2ZXIgY2hhaW4gc3RhcnRzIGF0IHRoZVxuXHQgKiBpbXBvcnRlZCBmcmVlIGBkZWZpbmVgL2Bsb29rdXBgIChgZGVmaW5lKCdBJykuZGVmaW5lKCdCJylgLFxuXHQgKiBgbG9va3VwKCdBJykuZGVmaW5lKCdCJylgKS4gQSBmcmVlIGhvcCdzIHBhdGggaXMgcmVjb3JkZWQsIHNvIHRoZVxuXHQgKiBuZXh0IGhvcCBvbiB0aGUgY2hhaW4gc2VlcyBpdHMgcGFyZW50IGFzIGZyZWUuXG5cdCAqL1xuXHRwcml2YXRlIGlzRnJlZUNoYWluSG9wIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgcGFyZW50Tm9kZTogVHlwZU5vZGUgfCB1bmRlZmluZWQsIGZ1bGxQYXRoOiBzdHJpbmcpOiBib29sZWFuIHtcblx0XHRjb25zdCBjYWxsZWUgPSBjYWxsLmV4cHJlc3Npb247XG5cdFx0Y29uc3QgWyBmaXJzdEFyZyBdID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0Y29uc3QgZnJlZVJvb3QgPSB0cy5pc0lkZW50aWZpZXIoY2FsbGVlKSAmJiBmaXJzdEFyZyAhPT0gdW5kZWZpbmVkICYmIHRzLmlzU3RyaW5nTGl0ZXJhbExpa2UoZmlyc3RBcmcpO1xuXHRcdGxldCBiYXNlOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkID0gdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbGVlKSA/IGNhbGxlZS5leHByZXNzaW9uIDogdW5kZWZpbmVkO1xuXHRcdHdoaWxlIChiYXNlICYmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihiYXNlKSB8fCB0cy5pc0NhbGxFeHByZXNzaW9uKGJhc2UpKSkge1xuXHRcdFx0YmFzZSA9IGJhc2UuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0Y29uc3QgaW1wb3J0ZWRBcyA9IGJhc2UgJiYgdHMuaXNJZGVudGlmaWVyKGJhc2UpXG5cdFx0XHQ/IHRoaXMubW5lbW9uaWNhTmFtZWRJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQoYmFzZS50ZXh0KVxuXHRcdFx0OiB1bmRlZmluZWQ7XG5cdFx0Y29uc3QgZnJlZSA9IGZyZWVSb290IHx8XG5cdFx0XHQocGFyZW50Tm9kZSAhPT0gdW5kZWZpbmVkICYmIHRoaXMuZnJlZUNoYWluVHlwZVBhdGhzLmhhcyhwYXJlbnROb2RlLmZ1bGxQYXRoKSkgfHxcblx0XHRcdGltcG9ydGVkQXMgPT09ICdkZWZpbmUnIHx8XG5cdFx0XHRpbXBvcnRlZEFzID09PSAnbG9va3VwJztcblx0XHRpZiAoZnJlZSkge1xuXHRcdFx0dGhpcy5mcmVlQ2hhaW5UeXBlUGF0aHMuYWRkKGZ1bGxQYXRoKTtcblx0XHR9XG5cdFx0cmV0dXJuIGZyZWU7XG5cdH1cblxuXHRwcml2YXRlIHJlY29yZEJ1aWxkZXJDYW5kaWRhdGUgKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRmdWxsUGF0aDogc3RyaW5nLFxuXHRcdGtpbmQ6ICdyZWdpc3RyeU9mJyB8ICd0eXBlb2YnLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0ZGVjbGFyYXRpb246IHRzLlZhcmlhYmxlRGVjbGFyYXRpb24sXG5cdFx0ZXhjbHVkZWQ6IGJvb2xlYW5cblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgY2FuZGlkYXRlOiBCdWlsZGVyQ2FuZGlkYXRlID0ge1xuXHRcdFx0bmFtZSxcblx0XHRcdHNvdXJjZUZpbGUgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0a2luZCxcblx0XHRcdGZ1bGxQYXRoLFxuXHRcdFx0ZXhwb3J0cyAgICA6IFtdLFxuXHRcdFx0ZXhjbHVkZWRcblx0XHR9O1xuXHRcdGNvbnN0IHN0YXRlbWVudCA9IGRlY2xhcmF0aW9uLnBhcmVudC5wYXJlbnQ7XG5cdFx0Y29uc3QgbW9kaWZpZXJzID0gdHMuaXNWYXJpYWJsZVN0YXRlbWVudChzdGF0ZW1lbnQpID8gdHMuZ2V0TW9kaWZpZXJzKHN0YXRlbWVudCkgPz8gW10gOiBbXTtcblx0XHRjb25zdCBpc0RlZmF1bHQgPSBtb2RpZmllcnMuc29tZShtb2RpZmllciA9PiBtb2RpZmllci5raW5kID09PSB0cy5TeW50YXhLaW5kLkRlZmF1bHRLZXl3b3JkKTtcblx0XHRjb25zdCBpc0V4cG9ydGVkID0gbW9kaWZpZXJzLnNvbWUobW9kaWZpZXIgPT4gbW9kaWZpZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5FeHBvcnRLZXl3b3JkKTtcblx0XHRpZiAoaXNFeHBvcnRlZCkge1xuXHRcdFx0Y2FuZGlkYXRlLmV4cG9ydHMucHVzaCh7XG5cdFx0XHRcdG5hbWUgICAgICAgICAgOiBuYW1lLFxuXHRcdFx0XHRzb3VyY2VGaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0ZGVmYXVsdEltcG9ydCA6IGlzRGVmYXVsdFxuXHRcdFx0fSk7XG5cdFx0fVxuXHRcdHRoaXMuYnVpbGRlckNhbmRpZGF0ZXMucHVzaChjYW5kaWRhdGUpO1xuXHR9XG5cblx0cHJpdmF0ZSBtYXJrQnVpbGRlckV4cG9ydCAoXG5cdFx0ZXhwb3J0ZWROYW1lOiBzdHJpbmcsXG5cdFx0b3JpZ2luYWxOYW1lOiBzdHJpbmcsXG5cdFx0ZmlsZVBhdGg6IHN0cmluZyxcblx0XHRtb2R1bGVTcGVjaWZpZXI/OiBzdHJpbmdcblx0KTogdm9pZCB7XG5cdFx0aWYgKCFtb2R1bGVTcGVjaWZpZXIpIHtcblx0XHRcdGZvciAoY29uc3QgY2FuZGlkYXRlIG9mIHRoaXMuYnVpbGRlckNhbmRpZGF0ZXMpIHtcblx0XHRcdFx0Y29uc3QgbWF0Y2hlc0NhbmRpZGF0ZSA9IG5vZGVQYXRoLnJlc29sdmUoY2FuZGlkYXRlLnNvdXJjZUZpbGUpID09PSBub2RlUGF0aC5yZXNvbHZlKGZpbGVQYXRoKVxuXHRcdFx0XHRcdCYmIGNhbmRpZGF0ZS5uYW1lID09PSBvcmlnaW5hbE5hbWVcblx0XHRcdFx0XHQmJiAhY2FuZGlkYXRlLmV4Y2x1ZGVkO1xuXHRcdFx0XHRpZiAobWF0Y2hlc0NhbmRpZGF0ZSkge1xuXHRcdFx0XHRcdGNhbmRpZGF0ZS5leHBvcnRzLnB1c2goeyBuYW1lIDogZXhwb3J0ZWROYW1lLCBzb3VyY2VGaWxlIDogZmlsZVBhdGggfSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKG1vZHVsZVNwZWNpZmllciwgZmlsZVBhdGgpO1xuXHRcdGlmIChyZXNvbHV0aW9uPy5pc0V4dGVybmFsKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGZhbGxiYWNrUGF0aCA9IG1vZHVsZVNwZWNpZmllci5lbmRzV2l0aCgnLnRzJylcblx0XHRcdD8gbm9kZVBhdGgucmVzb2x2ZShub2RlUGF0aC5kaXJuYW1lKGZpbGVQYXRoKSwgbW9kdWxlU3BlY2lmaWVyKVxuXHRcdFx0OiBgJHtub2RlUGF0aC5yZXNvbHZlKG5vZGVQYXRoLmRpcm5hbWUoZmlsZVBhdGgpLCBtb2R1bGVTcGVjaWZpZXIpfS50c2A7XG5cdFx0Y29uc3QgcmVzb2x2ZWRQYXRoID0gcmVzb2x1dGlvbj8ucmVzb2x2ZWRQYXRoID8/IGZhbGxiYWNrUGF0aDtcblx0XHRmb3IgKGNvbnN0IGNhbmRpZGF0ZSBvZiB0aGlzLmJ1aWxkZXJDYW5kaWRhdGVzKSB7XG5cdFx0XHRpZiAobm9kZVBhdGgucmVzb2x2ZShjYW5kaWRhdGUuc291cmNlRmlsZSkgIT09IG5vZGVQYXRoLnJlc29sdmUocmVzb2x2ZWRQYXRoKSB8fCBjYW5kaWRhdGUuZXhjbHVkZWQpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBtYXRjaGVzTmFtZSA9IG9yaWdpbmFsTmFtZSA9PT0gJ2RlZmF1bHQnXG5cdFx0XHRcdD8gY2FuZGlkYXRlLmV4cG9ydHMuc29tZShleHBvcnRlZCA9PiBleHBvcnRlZC5uYW1lID09PSAnZGVmYXVsdCcpXG5cdFx0XHRcdDogY2FuZGlkYXRlLm5hbWUgPT09IG9yaWdpbmFsTmFtZTtcblx0XHRcdGlmIChtYXRjaGVzTmFtZSkge1xuXHRcdFx0XHRjYW5kaWRhdGUuZXhwb3J0cy5wdXNoKHtcblx0XHRcdFx0XHRuYW1lICAgICAgICAgIDogZXhwb3J0ZWROYW1lLFxuXHRcdFx0XHRcdHNvdXJjZUZpbGUgICAgOiBmaWxlUGF0aCxcblx0XHRcdFx0XHRkZWZhdWx0SW1wb3J0IDogb3JpZ2luYWxOYW1lID09PSAnZGVmYXVsdCdcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0cHJpdmF0ZSB0cmFja0J1aWxkZXJFeHBvcnRBc3NpZ25tZW50IChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc0V4cG9ydEFzc2lnbm1lbnQobm9kZSkgfHwgIXRzLmlzSWRlbnRpZmllcihub2RlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGZpbGVQYXRoID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGZvciAoY29uc3QgY2FuZGlkYXRlIG9mIHRoaXMuYnVpbGRlckNhbmRpZGF0ZXMpIHtcblx0XHRcdGNvbnN0IG1hdGNoZXNDYW5kaWRhdGUgPSBub2RlUGF0aC5yZXNvbHZlKGNhbmRpZGF0ZS5zb3VyY2VGaWxlKSA9PT0gbm9kZVBhdGgucmVzb2x2ZShmaWxlUGF0aClcblx0XHRcdFx0JiYgY2FuZGlkYXRlLm5hbWUgPT09IG5vZGUuZXhwcmVzc2lvbi50ZXh0XG5cdFx0XHRcdCYmICFjYW5kaWRhdGUuZXhjbHVkZWQ7XG5cdFx0XHRpZiAobWF0Y2hlc0NhbmRpZGF0ZSkge1xuXHRcdFx0XHRjYW5kaWRhdGUuZXhwb3J0cy5wdXNoKHsgbmFtZSA6IG5vZGUuZXhwcmVzc2lvbi50ZXh0LCBzb3VyY2VGaWxlIDogZmlsZVBhdGgsIGRlZmF1bHRJbXBvcnQgOiB0cnVlIH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdCogVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHMgdGhhdCBjYXB0dXJlIGRlZmluZSgpIHJlc3VsdHNcblx0XHQqIGUuZy4sIGNvbnN0IFVzZXIgPSBkZWZpbmUoJ1VzZXJFbnRpdHknLCAuLi4pIG1hcHMgXCJVc2VyXCIgLT4gXCJVc2VyRW50aXR5XCJcblx0XHQqIEZvciBjaGFpbmVkIGNhbGxzIGxpa2UgY29uc3QgWCA9IGRlZmluZSgnQScpLmRlZmluZSgnQicpLCB3ZSBtYXAgWCAtPiBBICh0aGUgcm9vdCB0eXBlKVxuXHRcdCovXG5cdHByaXZhdGUgdHJhY2tWYXJpYWJsZUFzc2lnbm1lbnQgKFxuXHRcdGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLFxuXHRcdHBhcmVudE5vZGU6IFR5cGVOb2RlIHwgdW5kZWZpbmVkLFxuXHRcdGZ1bGxQYXRoOiBzdHJpbmcsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZVxuXHQpOiB2b2lkIHtcblx0XHQvLyBDaGVjayBpZiB0aGlzIGNhbGwgaXMgdGhlIHJpZ2h0LWhhbmQgc2lkZSBvZiBhIHZhcmlhYmxlIGRlY2xhcmF0aW9uXG5cdFx0Ly8gV2FsayB1cCB0aGUgdHJlZSB0byBmaW5kIFZhcmlhYmxlRGVjbGFyYXRpb25cblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IGNhbGwucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRcdC8vIEZvdW5kOiBjb25zdCBYID0gZGVmaW5lKC4uLilcblx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50Lm5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgdmFyTmFtZSA9IGN1cnJlbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRcdC8vIEYxODogZGVmaW5lKCkgcmV0dXJucyB0aGUgREVGSU5FRCB0eXBlJ3MgY29uc3RydWN0b3IsXG5cdFx0XHRcdFx0Ly8gc28gYSBjb25zdCBob2xkaW5nIGEgbXVsdGktaG9wIGluaXRpYWxpemVyXG5cdFx0XHRcdFx0Ly8gKGBjb25zdCBYID0gQS5kZWZpbmUoJ0InKS5kZWZpbmUoJ0MnKWApIGJpbmRzIHRoZSBMQVNUXG5cdFx0XHRcdFx0Ly8gaG9wIOKAlCBhIGRlZXBlciBob3AgbXVzdCBub3QgYmluZCwgYW5kIHRoZSBvdXRlcm1vc3Rcblx0XHRcdFx0XHQvLyBob3AgYmluZHMgdW5jb25kaXRpb25hbGx5ICh2aXNpdC1vcmRlciBpbmRlcGVuZGVudClcblx0XHRcdFx0XHRpZiAodGhpcy5pc0RlZXBlckRlZmluZUhvcChjYWxsKSkge1xuXHRcdFx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHQvLyBGb3IgY2hhaW5lZCBsYXp5IGNhbGxzIGxpa2UgY29uc3QgWCA9IGRlZmluZSgnQScpLmxhenkoJ0InKSxcblx0XHRcdFx0XHQvLyB0aGUgZmlyc3QgY2FsbCBpbiB0aGUgY2hhaW4gc2V0cyB0aGUgbWFwcGluZyAobGF6eSBob3Bcblx0XHRcdFx0XHQvLyBrZWVwcyBpdCDigJQgcGlubmVkIGJlaGF2aW9yKVxuXHRcdFx0XHRcdGlmIChwYXJlbnROb2RlICYmIHRoaXMudmFyaWFibGVUb1R5cGVNYXAuaGFzKHZhck5hbWUpKSB7XG5cdFx0XHRcdFx0XHRyZXR1cm47XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdGNvbnN0IHR5cGVOb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShmdWxsUGF0aCk7XG5cdFx0XHRcdFx0aWYgKHR5cGVOb2RlPy5jb2xsZWN0aW9uSWQgPT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRcdFx0Y29uc3Qgc2VsZlJlZmVyZW5jZSA9IHRoaXMuaGFzR2VuZXJhdGVkVHlwZVJlZmVyZW5jZSh0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCkpIHx8XG5cdFx0XHRcdFx0XHR0aGlzLmhhc1NlbGZUeXBlQW5ub3RhdGlvbih0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCksIGZ1bGxQYXRoKTtcblx0XHRcdFx0XHRcdGNvbnN0IGV4Y2x1ZGVkID0gc2VsZlJlZmVyZW5jZSB8fCAoXG5cdFx0XHRcdFx0XHRcdHBhcmVudE5vZGUgIT09IHVuZGVmaW5lZCAmJiB0aGlzLmV4Y2x1ZGVkVHlwZVBhdGhzLmhhcyhwYXJlbnROb2RlLmZ1bGxQYXRoKVxuXHRcdFx0XHRcdFx0KTtcblx0XHRcdFx0XHRcdGlmIChleGNsdWRlZCkge1xuXHRcdFx0XHRcdFx0XHR0aGlzLmV4Y2x1ZGVkVHlwZVBhdGhzLmFkZChmdWxsUGF0aCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHQvLyBBIGZyZWUtY2hhaW4gdmFsdWUgc3RheXMgZXh0cmFjdGVkOiBpdCBjYXJyaWVzIHRoZVxuXHRcdFx0XHRcdFx0Ly8gZ2xvYmFsIFR5cGVSZWdpc3RyeSwgc28gZGVyaXZpbmcgaXQgaXMgY2lyY3VsYXJcblx0XHRcdFx0XHRcdC8vIChSZWdpc3RyeU9mKSBvciBncm93cyBmYXN0ZXIgdGhhbiB0aGUgdHlwZSBjb3VudFxuXHRcdFx0XHRcdFx0Ly8gKHR5cGVvZikuIE9ubHkgYnVpbGRlciB2YWx1ZXMgd2l0aCBhIHJlZ2lzdHJ5IG9mXG5cdFx0XHRcdFx0XHQvLyB0aGVpciBvd24gYXJlIGRlcml2ZWRcblx0XHRcdFx0XHRcdGlmICghdGhpcy5pc0ZyZWVDaGFpbkhvcChjYWxsLCBwYXJlbnROb2RlLCBmdWxsUGF0aCkpIHtcblx0XHRcdFx0XHRcdFx0Y29uc3Qga2luZCA9IHRzLmlzSWRlbnRpZmllcihjYWxsLmV4cHJlc3Npb24pID8gJ3R5cGVvZicgOiAncmVnaXN0cnlPZic7XG5cdFx0XHRcdFx0XHRcdHRoaXMucmVjb3JkQnVpbGRlckNhbmRpZGF0ZSh2YXJOYW1lLCBmdWxsUGF0aCwga2luZCwgc291cmNlRmlsZSwgY3VycmVudCwgZXhjbHVkZWQpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHR0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLnNldCh2YXJOYW1lLCBmdWxsUGF0aCk7XG5cdFx0XHRcdFx0dGhpcy50cmFja0ZpbGVHcmFwaEJpbmRpbmcodmFyTmFtZSwgZnVsbFBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQSBgLmRlZmluZSguLi4pYCBob3Agd3JhcHBlZCBieSBhbm90aGVyIGAuZGVmaW5lKC4uLilgIGNhbGwgaXMgbm90XG5cdCAqIHRoZSB2YWx1ZSBpdHMgY29uc3QgZW5kcyB1cCBob2xkaW5nIOKAlCB0aGUgT1VURVJNT1NUIGhvcCBvZiB0aGVcblx0ICogaW5pdGlhbGl6ZXIgY2hhaW4gaXMgKGRlZmluZSgpIHJldHVybnMgdGhlIGRlZmluZWQgdHlwZSdzXG5cdCAqIGNvbnN0cnVjdG9yKS4gT25seSB0aGUgb3V0ZXJtb3N0IGhvcCBtYXkgYmluZCB0aGUgdmFyaWFibGUuXG5cdCAqL1xuXHRwcml2YXRlIGlzRGVlcGVyRGVmaW5lSG9wIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IGJvb2xlYW4ge1xuXHRcdGNvbnN0IHsgcGFyZW50IH0gPSBjYWxsO1xuXHRcdGNvbnN0IGRlZXBlciA9ICEhcGFyZW50ICYmXG5cdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihwYXJlbnQpICYmXG5cdFx0XHRwYXJlbnQubmFtZS50ZXh0ID09PSAnZGVmaW5lJyAmJlxuXHRcdFx0dHMuaXNDYWxsRXhwcmVzc2lvbihwYXJlbnQucGFyZW50KSAmJlxuXHRcdFx0cGFyZW50LnBhcmVudC5leHByZXNzaW9uID09PSBwYXJlbnQ7XG5cdFx0cmV0dXJuIGRlZXBlcjtcblx0fVxuXG5cdC8qKlxuXHQgKiBNaXJyb3IgYSB2YXJpYWJsZSAtPiBtbmVtb25pY2EgZnVsbFBhdGggYmluZGluZyBpbnRvIHRoZSBwZXItZmlsZVxuXHQgKiB2YWx1ZS1zY29wZSBtYXAgKGdyYXBoIGlkZW50aXR5IGxhdzogYHR5cGVvZiBYYCBhbmQgYmFyZSByZWZlcmVuY2VzXG5cdCAqIHJlc29sdmUgdGhyb3VnaCB0aGUgZmlsZSdzIG93biBiaW5kaW5ncyBmaXJzdCkuXG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrRmlsZUdyYXBoQmluZGluZyAodmFyTmFtZTogc3RyaW5nLCBmdWxsUGF0aDogc3RyaW5nKTogdm9pZCB7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0bGV0IGJpbmRpbmdzID0gdGhpcy5maWxlR3JhcGhCaW5kaW5ncy5nZXQoZmlsZVBhdGgpO1xuXHRcdGlmICghYmluZGluZ3MpIHtcblx0XHRcdGJpbmRpbmdzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0XHRcdHRoaXMuZmlsZUdyYXBoQmluZGluZ3Muc2V0KGZpbGVQYXRoLCBiaW5kaW5ncyk7XG5cdFx0fVxuXHRcdGJpbmRpbmdzLnNldCh2YXJOYW1lLCBmdWxsUGF0aCk7XG5cdH1cblx0XG5cdC8qKlxuXHRcdCogVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHMgZnJvbSBsb29rdXAoKSBjYWxsc1xuXHRcdCogZS5nLiwgY29uc3QgU2VudGllbmNlQ29uc3RydWN0b3IgPSBsb29rdXAoJ1NlbnRpZW5jZScpIG1hcHMgXCJTZW50aWVuY2VDb25zdHJ1Y3RvclwiIC0+IFwiU2VudGllbmNlXCJcblx0XHQqL1xuXHRwcml2YXRlIHRyYWNrTG9va3VwQXNzaWdubWVudCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHR5cGVQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShjYWxsLCB0eXBlUGF0aCk7XG5cdH1cblxuXHQvKipcblx0XHQqIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnRzIGZyb20gbmV3IFR5cGUoKSBjYWxsc1xuXHRcdCogZS5nLiwgY29uc3QgdXNlciA9IG5ldyBVc2VyVHlwZSgpIG1hcHMgXCJ1c2VyXCIgLT4gXCJVc2VyVHlwZVwiXG5cdFx0Ki9cblx0cHJpdmF0ZSB0cmFja05ld0Fzc2lnbm1lbnQgKG5ld0V4cHI6IHRzLk5ld0V4cHJlc3Npb24sIHR5cGVQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHRsZXQgZWZmZWN0aXZlUGF0aCA9IHR5cGVQYXRoO1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbmV3RXhwci5wYXJlbnQ7XG5cdFx0Ly8gQ2hhaW4tZm9ybSBjb25zdHJ1Y3Rpb246IG5ldyBSKCkuQSgpLkIoKSDigJQgdGhlIHJlc3VsdCB2YXJpYWJsZVxuXHRcdC8vIGhvbGRzIHRoZSBPVVRFUk1PU1QgdGlwJ3MgaW5zdGFuY2UgKGF3YWl0LXRyYW5zcGFyZW50KSwgbm90IHRoZVxuXHRcdC8vIGlubmVyIG5ldydzIHR5cGUuIFdhbGsgdGhlIGNoYWluLCBrZWVwaW5nIHRoZSBsYXN0IHJlc29sdmFibGUgdGlwLlxuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY3VycmVudCkgJiZcblx0XHRcdFx0dHMuaXNDYWxsRXhwcmVzc2lvbihjdXJyZW50LnBhcmVudCkgJiZcblx0XHRcdFx0Y3VycmVudC5wYXJlbnQuZXhwcmVzc2lvbiA9PT0gY3VycmVudCkge1xuXHRcdFx0XHRjb25zdCB0aXAgPSB0aGlzLnJlc29sdmVDaGFpblRpcFR5cGVQYXRoKGN1cnJlbnQucGFyZW50KTtcblx0XHRcdFx0aWYgKHRpcCkge1xuXHRcdFx0XHRcdGVmZmVjdGl2ZVBhdGggPSB0aXA7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50LnBhcmVudDtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRicmVhaztcblx0XHR9XG5cdFx0dGhpcy5iaW5kUmVzdWx0VmFyaWFibGUobmV3RXhwciwgZWZmZWN0aXZlUGF0aCk7XG5cdH1cblxuXHQvKipcblx0ICogQmluZCB0aGUgbmVhcmVzdCBlbmNsb3NpbmcgYGNvbnN0L2xldC92YXIgWCA9IOKApmAgdG8gYSBtbmVtb25pY2Fcblx0ICogZnVsbFBhdGgg4oCUIHRoZSBzaGFyZWQgcmVzdWx0LXZhcmlhYmxlIHdhbGtlciBiZWhpbmQgbmV3L2xvb2t1cC9cblx0ICogY2hhaW4vZm9yay9tZXJnZS9jYWxsIHRyYWNraW5nICh2YWx1ZSBzY29wZTogZG93bnN0cmVhbSByZWZlcmVuY2VzXG5cdCAqIGFuZCBgdGhpcy54ID0geGAgYXNzaWdubWVudHMgcmVzb2x2ZSB0aHJvdWdoIHRoZSBzYW1lIGJpbmRpbmcpLlxuXHQgKi9cblx0cHJpdmF0ZSBiaW5kUmVzdWx0VmFyaWFibGUgKGZyb206IHRzLk5vZGUsIHR5cGVQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IGZyb20ucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRcdC8vIEZvdW5kOiBjb25zdCBYID0gPGNvbnN0cnVjdGlvbj5cblx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50Lm5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgdmFyTmFtZSA9IGN1cnJlbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRcdHRoaXMudmFyaWFibGVUb1R5cGVNYXAuc2V0KHZhck5hbWUsIHR5cGVQYXRoKTtcblx0XHRcdFx0XHR0aGlzLnRyYWNrRmlsZUdyYXBoQmluZGluZyh2YXJOYW1lLCB0eXBlUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0Ly8gU2NvcGUgYm91bmRhcnk6IGEgY29uc3RydWN0aW9uIGluc2lkZSBhIG5lc3RlZCBjbGFzcy9mdW5jdGlvblxuXHRcdFx0Ly8gYm9keSBkb2VzIG5vdCBiaW5kIHRoZSBvdXRlciB2YXJpYWJsZSDigJRcblx0XHRcdC8vIGBjb25zdCBYID0gZGVmaW5lKCdYJywgY2xhc3MgeyBtID0gbmV3IE1hcCgpIH0pYCBob2xkcyB0aGVcblx0XHRcdC8vIGRlZmluZWQgY29uc3RydWN0b3IsIG5vdCBhIE1hcC4gV2l0aG91dCB0aGlzIHN0b3AgdGhlIGNsYXNzLWJvZHlcblx0XHRcdC8vIGluc3RhbnRpYXRpb24gY2xvYmJlcnMgWCdzIGJpbmRpbmcgYW5kIGEgbGF0ZXIgWC5kZWZpbmUoJ0NoaWxkJylcblx0XHRcdC8vIGxvc2VzIGl0cyBwYXJlbnQgKHRoZSBjaGlsZCBsYW5kcyBhcyBhIGJhcmUgZGVmYXVsdC1jb2xsZWN0aW9uXG5cdFx0XHQvLyByb290IOKAlCBmYXRhbCBmb3IgY3VzdG9tIGNvbGxlY3Rpb25zLCB3aG9zZSBmdWxsUGF0aHMgdGhlXG5cdFx0XHQvLyBuYW1lLW9ubHkgZmFsbGJhY2sgY2Fubm90IHNlZSkuXG5cdFx0XHRpZiAodHMuaXNDbGFzc0xpa2UoY3VycmVudCkgfHwgdHMuaXNGdW5jdGlvbkxpa2UoY3VycmVudCkpIHtcblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgYW4gYGluc3RhbnRpYXRpb25gIHVzYWdlIGZvciBhIGNvbnN0cnVjdGlvbi1zaGFwZSBjYWxsXG5cdCAqIChjaGFpbiB0aXAgLyBjYWxsIC8gYXBwbHkgLyBmb3JrIC8gY2xvbmUgLyBtZXJnZSDigJRcblx0ICogYnl0ZS1pbmRpc3Rpbmd1aXNoYWJsZSBmcm9tIGBuZXdgIHVudGlsIHRoZSBkZWZlcnJlZFxuXHQgKiBtZWNoYW5pc20ta2luZCByZXZpc2lvbikuIGBjb25zdHJ1Y3RvclRleHRgIGRlZmF1bHRzIHRvIHRoZSBjYWxsZWVcblx0ICogZXhwcmVzc2lvbiB0ZXh0IHNvIHRoZSBzaXRlIHN0YXlzIHJlYWRhYmxlIHdpdGhvdXQgbmV3IGZpZWxkcztcblx0ICogY2FsbC9hcHBseSBvdmVycmlkZSBpdCB3aXRoIHRoZSBDdG9yIGFyZ3VtZW50IHRleHQuXG5cdCAqL1xuXHRwcml2YXRlIHJlY29yZENvbnN0cnVjdGlvblVzYWdlIChcblx0XHRjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHR0eXBlUGF0aDogc3RyaW5nLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0Y29uc3RydWN0b3JUZXh0Pzogc3RyaW5nXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRjYWxsLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBjdG9yVGV4dCA9IGNvbnN0cnVjdG9yVGV4dCA/PyBjYWxsLmV4cHJlc3Npb24uZ2V0VGV4dChzb3VyY2VGaWxlKTtcblx0XHR0aGlzLmFkZFVzYWdlKHR5cGVQYXRoLCB7XG5cdFx0XHRsb2NhdGlvbiAgICAgICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdGtpbmQgICAgICAgICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdGNvZGUgICAgICAgICAgICA6IGNhbGwuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0Y29uc3RydWN0b3JUZXh0IDogY3RvclRleHQuc2xpY2UoMCwgMTAwKSxcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHRoZSB0eXBlIGEgY29uc3RydWN0aW9uLWNoYWluIHRpcCBjYWxsIGNvbnN0cnVjdHM6XG5cdCAqIGBuZXcgUiguLi4pLkEoLi4uKWAgY29uc3RydWN0cyBSLkE7IGBhd2FpdCBuZXcgUiguLi4pLkEoLi4uKS5CKC4uLilgXG5cdCAqIGNvbnN0cnVjdHMgUi5BLkIuIFRoZSByZWNlaXZlciBpcyB0aGUgbmVzdGVkIGNoYWluIChOZXdFeHByZXNzaW9uXG5cdCAqIGJhc2UsIHRoZW4gdGlwIGNhbGxzKTsgZXhhY3QgZnVsbFBhdGggZmlyc3QsIGFuZCBvbmx5IHdoZW4gdGhlIHJvb3Rcblx0ICogaXRzZWxmIGlzIHVua25vd24gZG9lcyB0aGUgcHJvcC1uYW1lIGZhbGxiYWNrIGxhdyBhcHBseSAoc28gcGxhaW5cblx0ICogbWV0aG9kIGNhbGxzIG9uIGZyZXNoIGluc3RhbmNlcyBuZXZlciByZWNvcmQgYSBjb25zdHJ1Y3Rpb24pLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlQ2hhaW5UaXBUeXBlUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmVjZWl2ZXIgPSBjYWxsLmV4cHJlc3Npb247XG5cdFx0bGV0IHJvb3RQYXRoOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdFx0aWYgKHRzLmlzTmV3RXhwcmVzc2lvbihyZWNlaXZlci5leHByZXNzaW9uKSkge1xuXHRcdFx0Y29uc3QgaW5uZXIgPSByZWNlaXZlci5leHByZXNzaW9uO1xuXHRcdFx0cm9vdFBhdGggPSB0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihpbm5lci5leHByZXNzaW9uKVxuXHRcdFx0XHQ/IHRoaXMucmVzb2x2ZVR5cGVQYXRoKGlubmVyLmV4cHJlc3Npb24pXG5cdFx0XHRcdDogdGhpcy5nZXRUeXBlTmFtZUZyb21FeHByZXNzaW9uKGlubmVyLmV4cHJlc3Npb24pO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihyZWNlaXZlci5leHByZXNzaW9uKSkge1xuXHRcdFx0cm9vdFBhdGggPSB0aGlzLnJlc29sdmVDaGFpblRpcFR5cGVQYXRoKHJlY2VpdmVyLmV4cHJlc3Npb24pO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRpZiAoIXJvb3RQYXRoKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBjYW5kaWRhdGUgPSBgJHtyb290UGF0aH0uJHtyZWNlaXZlci5uYW1lLnRleHR9YDtcblx0XHRpZiAodGhpcy5kZWZpbml0aW9ucy5oYXMoY2FuZGlkYXRlKSkge1xuXHRcdFx0cmV0dXJuIGNhbmRpZGF0ZTtcblx0XHR9XG5cdFx0aWYgKCF0aGlzLmRlZmluaXRpb25zLmhhcyhyb290UGF0aCkpIHtcblx0XHRcdHJldHVybiB0aGlzLnJlc29sdmVUeXBlUGF0aChyZWNlaXZlcik7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogVHJ1ZSB3aGVuIGBleHByYCBkZW5vdGVzIGEgY29uc3RydWN0aW9uIGZ1bmN0aW9uIGltcG9ydGVkIGZyb21cblx0ICogJ21uZW1vbmljYScg4oCUIHRoZSBuYW1lZC1pbXBvcnQgZm9ybSAoYGltcG9ydCB7IGNhbGwgfSBmcm9tXG5cdCAqICdtbmVtb25pY2EnYCwgYWxpYXNlcyBpbmNsdWRlZCkgb3IgYSBtZW1iZXIgb2YgYSB0cmFja2VkXG5cdCAqIG1vZHVsZS1vYmplY3QgYWxpYXMgKGBtbmVtb25pY2EuY2FsbGApLiBVc2VybGFuZCBjYWxsL2FwcGx5L2JpbmRcblx0ICogZnVuY3Rpb25zIG5ldmVyIG1hdGNoLlxuXHQgKi9cblx0cHJpdmF0ZSBpc01uZW1vbmljYUNvbnN0cnVjdGlvbkZuIChleHByOiB0cy5FeHByZXNzaW9uLCBmbjogJ2NhbGwnIHwgJ2FwcGx5JyB8ICdiaW5kJyk6IGJvb2xlYW4ge1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChleHByLnRleHQpO1xuXHRcdFx0Y29uc3QgbWF0Y2hlZCA9IGltcG9ydGVkID09PSBmbjtcblx0XHRcdHJldHVybiBtYXRjaGVkO1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikgJiYgZXhwci5uYW1lLnRleHQgPT09IGZuKSB7XG5cdFx0XHRjb25zdCBtYXRjaGVkID0gdHMuaXNJZGVudGlmaWVyKGV4cHIuZXhwcmVzc2lvbikgJiZcblx0XHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuaGFzKGV4cHIuZXhwcmVzc2lvbi50ZXh0KTtcblx0XHRcdHJldHVybiBtYXRjaGVkO1xuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogbW5lbW9uaWNhIGNhbGwvYXBwbHkoZW50aXR5LCBDdG9yLCAuLi4pIC8gYmluZChlbnRpdHksIEN0b3IpOlxuXHQgKiByZXNvbHZlIHRoZSBDdG9yIGFyZ3VtZW50IChhcmcgMSkgdG8gYSBncmFwaCBmdWxsUGF0aCB0aHJvdWdoIHRoZVxuXHQgKiBzYW1lIHRpZXJzIGFzIHRoZSBgbmV3YCBicmFuY2ggKHZhbHVlIHNjb3BlIGZvciBpZGVudGlmaWVycyxcblx0ICogY2hhaW4gcmVzb2x1dGlvbiBmb3IgcHJvcGVydHkgYWNjZXNzZXMpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlQ29uc3RydWN0aW9uRm5UeXBlUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGNhbGxlZSA9IGNhbGwuZXhwcmVzc2lvbjtcblx0XHRjb25zdCBpc0NhbGxPckFwcGx5ID0gdGhpcy5pc01uZW1vbmljYUNvbnN0cnVjdGlvbkZuKGNhbGxlZSwgJ2NhbGwnKSB8fFxuXHRcdFx0dGhpcy5pc01uZW1vbmljYUNvbnN0cnVjdGlvbkZuKGNhbGxlZSwgJ2FwcGx5Jyk7XG5cdFx0Y29uc3QgaXNCaW5kID0gdGhpcy5pc01uZW1vbmljYUNvbnN0cnVjdGlvbkZuKGNhbGxlZSwgJ2JpbmQnKTtcblx0XHRpZiAoIWlzQ2FsbE9yQXBwbHkgJiYgIWlzQmluZCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0aWYgKGNhbGwuYXJndW1lbnRzLmxlbmd0aCA8IDIpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IFsgLCBjdG9yQXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblx0XHRjb25zdCBrbm93biA9IHRoaXMucmVzb2x2ZUN0b3JBcmdUeXBlUGF0aChjdG9yQXJnKTtcblx0XHRyZXR1cm4ga25vd247XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhbiBleHByZXNzaW9uIHBhc3NlZCB3aGVyZSBhIGNvbnN0cnVjdG9yIGlzIGV4cGVjdGVkICh0aGVcblx0ICogQ3RvciBvZiBjYWxsL2FwcGx5L2JpbmQsIGEgcGx1Z2luIGZhY3RvcnkncyBjb25zdHJ1Y3RlZCB0YXJnZXQpIHRvIGFcblx0ICogZGVmaW5lZCB0eXBlJ3MgZnVsbFBhdGg6IHZhbHVlIHNjb3BlIGZvciBpZGVudGlmaWVycywgY2hhaW5cblx0ICogcmVzb2x1dGlvbiBmb3IgcHJvcGVydHkgYWNjZXNzZXMuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVDdG9yQXJnVHlwZVBhdGggKGN0b3JBcmc6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCByZXNvbHZlZDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdG9yQXJnKSkge1xuXHRcdFx0cmVzb2x2ZWQgPSB0aGlzLnJlc29sdmVUeXBlUGF0aChjdG9yQXJnKTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihjdG9yQXJnKSkge1xuXHRcdFx0Y29uc3QgYm91bmQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChjdG9yQXJnLnRleHQpO1xuXHRcdFx0aWYgKGJvdW5kKSB7XG5cdFx0XHRcdHJlc29sdmVkID0gYm91bmQ7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRjb25zdCBncmFwaFJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUoY3RvckFyZy50ZXh0KTtcblx0XHRcdFx0aWYgKGdyYXBoUmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdFx0XHRyZXNvbHZlZCA9IGdyYXBoUmVzdWx0Lm5vZGUuZnVsbFBhdGg7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc3Qga25vd24gPSByZXNvbHZlZCAmJiB0aGlzLmRlZmluaXRpb25zLmhhcyhyZXNvbHZlZCkgPyByZXNvbHZlZCA6IHVuZGVmaW5lZDtcblx0XHRyZXR1cm4ga25vd247XG5cdH1cblxuXHQvKipcblx0ICogaW5zdGFuY2UuZm9yayguLi4pIC8gaW5zdGFuY2UuY2xvbmUoLi4uKSBvbiBhIHRyYWNrZWQgdmFyaWFibGUg4oCUXG5cdCAqIHJ1bnRpbWUgcmV0dXJucyBgdGhpc2AsIHNvIHRoZSByZXN1bHQgY2FycmllcyB0aGUgc291cmNlIHR5cGUuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVGb3JrTGlrZVR5cGVQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBtZXRob2QgPSBjYWxsLmV4cHJlc3Npb24ubmFtZS50ZXh0O1xuXHRcdGlmIChtZXRob2QgIT09ICdmb3JrJyAmJiBtZXRob2QgIT09ICdjbG9uZScpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlY2VpdmVyID0gY2FsbC5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIocmVjZWl2ZXIpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChyZWNlaXZlci50ZXh0KTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEZyZWUgdXRpbHMgZm9ybXM6IHV0aWxzLm1lcmdlKGEsIGIsIC4uLikgKGFsc28gdGhlIGRpcmVjdCBuYW1lZFxuXHQgKiBpbXBvcnQgYG1lcmdlKGEsIGIpYCkgYW5kIHRoZSBjdXJyaWVkIHV0aWxzLmZvcmsoaW5zdGFuY2UpKC4uLikuXG5cdCAqIFRoZSByZXN1bHQgYmluZHMgdG8gYXJnIDAncyB0eXBlIOKAlCBydW50aW1lIHJldHVybnMgYSdzIGxpbmVhZ2Ugb3ZlclxuXHQgKiBiJ3MgY29udGV4dDsgYSdzIGZ1bGxQYXRoIGlzIHRoZSBob25lc3QgYXBwcm94aW1hdGlvbiB3aXRoaW4gdGhlXG5cdCAqIG91dHB1dCBjb250cmFjdCAoZG9jdW1lbnRlZCBpbiBSRUFETUUpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlVXRpbHNGblR5cGVQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2FsbGVlID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGNvbnN0IGlzVXRpbHNPd25lciA9IChvd25lcjogdHMuRXhwcmVzc2lvbik6IGJvb2xlYW4gPT4ge1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihvd25lcikpIHtcblx0XHRcdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLm1uZW1vbmljYU5hbWVkSW1wb3J0cy5nZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKT8uZ2V0KG93bmVyLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4gaW1wb3J0ZWQgPT09ICd1dGlscyc7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBtYXRjaGVkID0gdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ob3duZXIpICYmIG93bmVyLm5hbWUudGV4dCA9PT0gJ3V0aWxzJyAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIob3duZXIuZXhwcmVzc2lvbikgJiYgdGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuaGFzKG93bmVyLmV4cHJlc3Npb24udGV4dCk7XG5cdFx0XHRyZXR1cm4gbWF0Y2hlZDtcblx0XHR9O1xuXHRcdGxldCBzdWJqZWN0QXJnOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkO1xuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsZWUpICYmIGlzVXRpbHNPd25lcihjYWxsZWUuZXhwcmVzc2lvbikgJiZcblx0XHRcdChjYWxsZWUubmFtZS50ZXh0ID09PSAnbWVyZ2UnIHx8IGNhbGxlZS5uYW1lLnRleHQgPT09ICdmb3JrJykpIHtcblx0XHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdFx0c3ViamVjdEFyZyA9IGZpcnN0QXJnO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNJZGVudGlmaWVyKGNhbGxlZSkpIHtcblx0XHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChjYWxsZWUudGV4dCk7XG5cdFx0XHRpZiAoaW1wb3J0ZWQgPT09ICdtZXJnZScgfHwgaW1wb3J0ZWQgPT09ICdmb3JrJykge1xuXHRcdFx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblx0XHRcdFx0c3ViamVjdEFyZyA9IGZpcnN0QXJnO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSBpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihjYWxsZWUpICYmIHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxlZS5leHByZXNzaW9uKSAmJlxuXHRcdFx0Y2FsbGVlLmV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnZm9yaycgJiYgaXNVdGlsc093bmVyKGNhbGxlZS5leHByZXNzaW9uLmV4cHJlc3Npb24pKSB7XG5cdFx0XHQvLyB1dGlscy5mb3JrKGluc3RhbmNlKSguLi5hcmdzKSDigJQgdGhlIGN1cnJpZWQgZm9ybVxuXHRcdFx0Y29uc3QgWyBmaXJzdEFyZyBdID0gY2FsbGVlLmFyZ3VtZW50cztcblx0XHRcdHN1YmplY3RBcmcgPSBmaXJzdEFyZztcblx0XHR9XG5cdFx0aWYgKCFzdWJqZWN0QXJnIHx8ICF0cy5pc0lkZW50aWZpZXIoc3ViamVjdEFyZykpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KHN1YmplY3RBcmcudGV4dCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cblx0LyoqXG5cdFx0KiBQcm9jZXNzIGEgQGRlY29yYXRlKCkgZGVjb3JhdG9yXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NEZWNvcmF0ZURlY29yYXRvciAoXG5cdFx0ZGVjb3JhdG9yOiB0cy5EZWNvcmF0b3IsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRjbGFzc0RlY2xQYXJhbT86IHRzLkNsYXNzRGVjbGFyYXRpb25cblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdGRlY29yYXRvci5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cblx0XHQvLyBHZXQgdGhlIGNsYXNzIGRlY2xhcmF0aW9uIC0gdXNlIHRoZSBwYXNzZWQgY29udGV4dCBpZiBwYXJlbnQgaXMgbm90IHNldFxuXHRcdGNvbnN0IGNsYXNzRGVjbCA9IGRlY29yYXRvci5wYXJlbnQgYXMgdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCB8fCBjbGFzc0RlY2xQYXJhbTtcblx0XHRpZiAoIWNsYXNzRGVjbCB8fCAhY2xhc3NEZWNsLm5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0RlY29yYXRlZCBjbGFzcyBoYXMgbm8gbmFtZScsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgdHlwZU5hbWUgPSBjbGFzc0RlY2wubmFtZS50ZXh0O1xuXHRcdGlmICghdHlwZU5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0RlY29yYXRlZCBjbGFzcyBoYXMgbm8gbmFtZScsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUGFyc2UgZGVjb3JhdG9yIGFyZ3VtZW50czogQGRlY29yYXRlKCksIEBkZWNvcmF0ZShQYXJlbnQpLFxuXHRcdC8vIEBkZWNvcmF0ZSh7IC4uLiB9KSwgQGRlY29yYXRlKFBhcmVudCwgeyAuLi4gfSksXG5cdFx0Ly8gQE15Q29sbGVjdGlvbi5kZWNvcmF0ZSgpLCBATXlDb2xsZWN0aW9uLmRlY29yYXRlKHsgLi4uIH0pXG5cdFx0bGV0IHBhcmVudE5vZGU6IFR5cGVOb2RlIHwgdW5kZWZpbmVkO1xuXHRcdGxldCBwYXJlbnRGdWxsUGF0aDogc3RyaW5nIHwgbnVsbCA9IG51bGw7XG5cdFx0bGV0IGNvbGxlY3Rpb25JZDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdGxldCBkZWNvcmF0b3JDb25maWc6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSA9IHt9O1xuXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZGVjb3JhdG9yLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRjb25zdCBjYWxsRXhwciA9IGRlY29yYXRvci5leHByZXNzaW9uO1xuXHRcdFx0Y29uc3QgY2FsbGVlID0gY2FsbEV4cHIuZXhwcmVzc2lvbjtcblxuXHRcdFx0Ly8gQ2hlY2sgZm9yIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSB3aGVyZSBNeUNvbGxlY3Rpb24gaXMgYSBjdXN0b20gY29sbGVjdGlvbi5cblx0XHRcdC8vIFRoZSBkZWNvcmF0ZWQgY2xhc3MgYmVjb21lcyBhIHJvb3QgdHlwZSBpbiB0aGF0IGNvbGxlY3Rpb24uXG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxlZSkgJiZcblx0XHRcdFx0Y2FsbGVlLm5hbWUudGV4dCA9PT0gJ2RlY29yYXRlJyAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoY2FsbGVlLmV4cHJlc3Npb24pICYmXG5cdFx0XHRcdHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5oYXMoY2FsbGVlLmV4cHJlc3Npb24udGV4dClcblx0XHRcdCkge1xuXHRcdFx0XHRjb2xsZWN0aW9uSWQgPSB0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuZ2V0KGNhbGxlZS5leHByZXNzaW9uLnRleHQpO1xuXHRcdFx0XHRpZiAoY2FsbEV4cHIuYXJndW1lbnRzLmxlbmd0aCA9PT0gMSAmJiB0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGNhbGxFeHByLmFyZ3VtZW50c1sgMCBdKSkge1xuXHRcdFx0XHRcdGRlY29yYXRvckNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGNhbGxFeHByLmFyZ3VtZW50c1sgMCBdKTtcblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgYXJncyA9IGNhbGxFeHByLmFyZ3VtZW50cztcblx0XHRcdFx0bGV0IHBhcmVudEFyZzogdHMuSWRlbnRpZmllciB8IHVuZGVmaW5lZDtcblx0XHRcdFx0bGV0IGNvbmZpZ0FyZzogdHMuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24gfCB1bmRlZmluZWQ7XG5cblx0XHRcdFx0Zm9yIChjb25zdCBhcmcgb2YgYXJncykge1xuXHRcdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0XHRcdFx0aWYgKHBhcmVudEFyZykge1xuXHRcdFx0XHRcdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0XHRcdFx0XHRtZXNzYWdlIDogJ0BkZWNvcmF0ZSgpIGFjY2VwdHMgb25seSBvbmUgcGFyZW50IHJlZmVyZW5jZScsXG5cdFx0XHRcdFx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRcdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHRcdHBhcmVudEFyZyA9IGFyZztcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0XHRcdFx0aWYgKGNvbmZpZ0FyZykge1xuXHRcdFx0XHRcdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0XHRcdFx0XHRtZXNzYWdlIDogJ0BkZWNvcmF0ZSgpIGFjY2VwdHMgb25seSBvbmUgY29uZmlnIG9iamVjdCcsXG5cdFx0XHRcdFx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRcdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHRcdGNvbmZpZ0FyZyA9IGFyZztcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRpZiAocGFyZW50QXJnKSB7XG5cdFx0XHRcdFx0cGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeUlkZW50aWZpZXIocGFyZW50QXJnLnRleHQpO1xuXHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHRwYXJlbnRGdWxsUGF0aCA9IHBhcmVudE5vZGUuZnVsbFBhdGg7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0aWYgKGNvbmZpZ0FyZykge1xuXHRcdFx0XHRcdGRlY29yYXRvckNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGNvbmZpZ0FyZyk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBCdWlsZCBmdWxsIHBhdGgg4oCUIGEgcm9vdCBkZWNvcmF0ZWQgaW50byBhIGN1c3RvbSBjb2xsZWN0aW9uXG5cdFx0Ly8gY2FycmllcyB0aGUgY29sbGVjdGlvbklkOjogcHJlZml4LCBleGFjdGx5IGxpa2UgdGhlIGdyYXBoIG5vZGUnc1xuXHRcdC8vIGZ1bGxQYXRoOiBkZWZpbml0aW9ucy5qc29uIGtleXMgbXVzdCBqb2luIGhpZXJhcmNoeS5qc29uICh0aGVcblx0XHQvLyBwcmVmaXggd2FzIGRyb3BwZWQgaGVyZSBiZWZvcmUsIHNvIGEgZGVjb3JhdGVkIGNvbGxlY3Rpb24gcm9vdFxuXHRcdC8vIG5ldmVyIGpvaW5lZClcblx0XHRjb25zdCBmdWxsUGF0aCA9IHBhcmVudE5vZGVcblx0XHRcdD8gYCR7cGFyZW50Tm9kZS5mdWxsUGF0aH0uJHt0eXBlTmFtZX1gXG5cdFx0XHQ6IGNvbGxlY3Rpb25JZFxuXHRcdFx0XHQ/IGAke2NvbGxlY3Rpb25JZH06OiR7dHlwZU5hbWV9YFxuXHRcdFx0XHQ6IHR5cGVOYW1lO1xuXG5cdFx0Ly8gQ3JlYXRlIGRlZmluaXRpb24gaW5mbyBmb3IgZGVjb3JhdGVcblx0XHRjb25zdCBkZWZpbml0aW9uOiBEZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVjb3JhdGUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiBwYXJlbnRGdWxsUGF0aCxcblx0XHRcdHN0cmljdENoYWluIDogZGVjb3JhdG9yQ29uZmlnLnN0cmljdENoYWluID8/IHRydWUsXG5cdFx0XHRibG9ja0Vycm9ycyA6IGRlY29yYXRvckNvbmZpZy5ibG9ja0Vycm9ycyA/PyBmYWxzZSxcblx0XHR9O1xuXHRcdHRoaXMuZGVmaW5pdGlvbnMuc2V0KGZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0XHR0aGlzLmVkc1Njb3BlQnlOb2RlLnNldChjbGFzc0RlY2wsIGZ1bGxQYXRoKTtcblxuXHRcdC8vIENyZWF0ZSB0eXBlIG5vZGVcblx0XHRjb25zdCBub2RlID0gVHlwZUdyYXBoSW1wbC5jcmVhdGVOb2RlKFxuXHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRwYXJlbnROb2RlLFxuXHRcdFx0c291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdGxpbmUgKyAxLFxuXHRcdFx0Y2hhcmFjdGVyICsgMSxcblx0XHRcdGNvbGxlY3Rpb25JZFxuXHRcdCk7XG5cdFx0dGhpcy5hcHBseUNvbGxlY3Rpb25FbWlzc2lvbkluZm8obm9kZSwgbm9kZS5jb2xsZWN0aW9uSWQpO1xuXG5cdFx0Ly8gU2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlIGRldGVjdGlvbiAoaGFyZC1mYWlsIGxhdylcblx0XHR0aGlzLnJlY29yZERlZmluZVNpdGUoXG5cdFx0XHRwYXJlbnROb2RlID8gYCR7cGFyZW50Tm9kZS5mdWxsUGF0aH0uJHt0eXBlTmFtZX1gIDogYCR7Y29sbGVjdGlvbklkID8/ICdkZWZhdWx0J306OiR7dHlwZU5hbWV9YCxcblx0XHRcdGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gXG5cdFx0KTtcblxuXHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBhbmQgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGNsYXNzIG1lbWJlcnMg4oCUXG5cdFx0Ly8gdGhlIG5ldyBub2RlIGFuY2hvcnMgcmVsYXRpdmUtZmlyc3QgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb25cblx0XHRjb25zdCBwcmV2aW91c0FuY2hvciA9IHRoaXMuY3VycmVudEdyYXBoQW5jaG9yO1xuXHRcdHRoaXMuY3VycmVudEdyYXBoQW5jaG9yID0gbm9kZTtcblx0XHR0cnkge1xuXHRcdFx0bm9kZS5wcm9wZXJ0aWVzID0gdGhpcy5leHRyYWN0Q2xhc3NQcm9wZXJ0aWVzKGNsYXNzRGVjbCk7XG5cdFx0XHRub2RlLmNvbnN0cnVjdG9yUGFyYW1zID0gdGhpcy5leHRyYWN0Q2xhc3NDb25zdHJ1Y3RvclBhcmFtcyhjbGFzc0RlY2wpO1xuXHRcdH0gZmluYWxseSB7XG5cdFx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IHByZXZpb3VzQW5jaG9yO1xuXHRcdH1cblxuXHRcdC8vIEFkZCB0byBncmFwaFxuXHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZENoaWxkKHBhcmVudE5vZGUsIG5vZGUpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZFJvb3Qobm9kZSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdHlwZSBuYW1lIGZyb20gZGVmaW5lKCkgY2FsbCBhcmd1bWVudHMuXG5cdCAqIEhhbmRsZXM6XG5cdCAqICAgZGVmaW5lKCdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdCAqICAgZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcikgICAvLyBleHBsaWNpdC1zb3VyY2UgZm9ybVxuXHQgKiAgIGRlZmluZShmdW5jdGlvbiBUeXBlTmFtZSgpIHt9KVxuXHQgKiAgIGRlZmluZSgoKSA9PiBjbGFzcyBUeXBlTmFtZSB7fSlcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFR5cGVOYW1lIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGFyZ3M7XG5cblx0XHQvLyBFeHBsaWNpdC1zb3VyY2UgZm9ybTogZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilcblx0XHRpZiAoYXJncy5sZW5ndGggPj0gMiAmJiB0cy5pc0lkZW50aWZpZXIoZmlyc3RBcmcpICYmIHRzLmlzU3RyaW5nTGl0ZXJhbChhcmdzWyAxIF0pKSB7XG5cdFx0XHRyZXR1cm4gYXJnc1sgMSBdLnRleHQ7XG5cdFx0fVxuXG5cdFx0Ly8gU3RyaW5nIGxpdGVyYWw6IGRlZmluZSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChmaXJzdEFyZykpIHtcblx0XHRcdHJldHVybiBmaXJzdEFyZy50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIEZ1bmN0aW9uIHdpdGggbmFtZTogZGVmaW5lKGZ1bmN0aW9uIFR5cGVOYW1lKCkge30pXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGZpcnN0QXJnKSAmJiBmaXJzdEFyZy5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gZmlyc3RBcmcubmFtZS50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIEFycm93IGZ1bmN0aW9uIHJldHVybmluZyBjbGFzczogZGVmaW5lKCgpID0+IGNsYXNzIFR5cGVOYW1lIHt9KVxuXHRcdGlmICh0cy5pc0Fycm93RnVuY3Rpb24oZmlyc3RBcmcpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGZpcnN0QXJnO1xuXHRcdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGJvZHkpICYmIGJvZHkubmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gYm9keS5uYW1lLnRleHQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgY29tcHV0ZWQgZGVmaW5lIG5hbWUgb25seSB3aGVuIGl0IHJhbmdlcyBvdmVyIGEgY2xvc2VkIGNvbnN0XG5cdCAqIG9iamVjdCBrZXkgc2V0LiBBcmJpdHJhcnkgc3RyaW5ncyBhbmQgdW5yZXNvbHZlZCB1bmlvbnMgc3RheSBvbiB0aGVcblx0ICogZXhpc3Rpbmcgd2FybmluZy1hbmQtc2tpcCBwYXRoLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29tcHV0ZWRUeXBlTmFtZXMgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nW10gfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGlmICghZmlyc3RBcmcgfHwgIXRzLmlzSWRlbnRpZmllcihmaXJzdEFyZykpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGxvb3BOYW1lcyA9IHRoaXMucmVzb2x2ZUxvb3BLZXlOYW1lcyhmaXJzdEFyZyk7XG5cdFx0aWYgKGxvb3BOYW1lcyAhPT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRyZXR1cm4gbG9vcE5hbWVzO1xuXHRcdH1cblx0XHRjb25zdCBwYXJhbWV0ZXJOYW1lcyA9IHRoaXMucmVzb2x2ZVBhcmFtZXRlcktleU5hbWVzKGZpcnN0QXJnLCBjYWxsLmdldFNvdXJjZUZpbGUoKSk7XG5cdFx0cmV0dXJuIHBhcmFtZXRlck5hbWVzO1xuXHR9XG5cblx0cHJpdmF0ZSByZXNvbHZlTG9vcEtleU5hbWVzIChuYW1lOiB0cy5JZGVudGlmaWVyKTogc3RyaW5nW10gfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbmFtZS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc0Zvck9mU3RhdGVtZW50KGN1cnJlbnQpICYmIHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbkxpc3QoY3VycmVudC5pbml0aWFsaXplcikpIHtcblx0XHRcdFx0Y29uc3QgZGVjbGFyYXRpb24gPSBjdXJyZW50LmluaXRpYWxpemVyLmRlY2xhcmF0aW9ucy5maW5kKGNhbmRpZGF0ZSA9PlxuXHRcdFx0XHRcdHRzLmlzSWRlbnRpZmllcihjYW5kaWRhdGUubmFtZSkgJiYgY2FuZGlkYXRlLm5hbWUudGV4dCA9PT0gbmFtZS50ZXh0KTtcblx0XHRcdFx0aWYgKGRlY2xhcmF0aW9uKSB7XG5cdFx0XHRcdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5yZXNvbHZlT2JqZWN0S2V5c0NhbGwoY3VycmVudC5leHByZXNzaW9uLCBjdXJyZW50LmdldFNvdXJjZUZpbGUoKSk7XG5cdFx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0cHJpdmF0ZSByZXNvbHZlT2JqZWN0S2V5c0NhbGwgKGV4cHJlc3Npb246IHRzLkV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiBzdHJpbmdbXSB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKGV4cHJlc3Npb24pIHx8ICF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBhY2Nlc3MgPSBleHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0Y29uc3QgWyBhcmd1bWVudCBdID0gZXhwcmVzc2lvbi5hcmd1bWVudHM7XG5cdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoYWNjZXNzLmV4cHJlc3Npb24pIHx8IGFjY2Vzcy5leHByZXNzaW9uLnRleHQgIT09ICdPYmplY3QnIHx8XG5cdFx0XHRhY2Nlc3MubmFtZS50ZXh0ICE9PSAna2V5cycgfHwgIWFyZ3VtZW50IHx8ICF0cy5pc0lkZW50aWZpZXIoYXJndW1lbnQpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnJlc29sdmVDb25zdE9iamVjdEtleXMoYXJndW1lbnQudGV4dCwgc291cmNlRmlsZSk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdHByaXZhdGUgcmVzb2x2ZVBhcmFtZXRlcktleU5hbWVzIChuYW1lOiB0cy5JZGVudGlmaWVyLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogc3RyaW5nW10gfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbmFtZS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc0Z1bmN0aW9uTGlrZShjdXJyZW50KSkge1xuXHRcdFx0XHRjb25zdCBwYXJhbWV0ZXIgPSBjdXJyZW50LnBhcmFtZXRlcnMuZmluZChjYW5kaWRhdGUgPT5cblx0XHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoY2FuZGlkYXRlLm5hbWUpICYmIGNhbmRpZGF0ZS5uYW1lLnRleHQgPT09IG5hbWUudGV4dCk7XG5cdFx0XHRcdGlmIChwYXJhbWV0ZXIpIHtcblx0XHRcdFx0XHRpZiAoIXBhcmFtZXRlci50eXBlKSB7XG5cdFx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnJlc29sdmVLZXlvZlR5cGUocGFyYW1ldGVyLnR5cGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdHByaXZhdGUgcmVzb2x2ZUtleW9mVHlwZSAodHlwZU5vZGU6IHRzLlR5cGVOb2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogc3RyaW5nW10gfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc1BhcmVudGhlc2l6ZWRUeXBlTm9kZSh0eXBlTm9kZSkpIHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMucmVzb2x2ZUtleW9mVHlwZSh0eXBlTm9kZS50eXBlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1R5cGVPcGVyYXRvck5vZGUodHlwZU5vZGUpICYmIHR5cGVOb2RlLm9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLktleU9mS2V5d29yZCkge1xuXHRcdFx0Y29uc3QgcXVlcmllZCA9IHR5cGVOb2RlLnR5cGU7XG5cdFx0XHRpZiAodHMuaXNUeXBlUXVlcnlOb2RlKHF1ZXJpZWQpICYmIHRzLmlzSWRlbnRpZmllcihxdWVyaWVkLmV4cHJOYW1lKSkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnJlc29sdmVDb25zdE9iamVjdEtleXMocXVlcmllZC5leHByTmFtZS50ZXh0LCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHR5cGVOb2RlKSAmJiB0cy5pc0lkZW50aWZpZXIodHlwZU5vZGUudHlwZU5hbWUpKSB7XG5cdFx0XHRjb25zdCByZWZlcmVuY2VkTmFtZSA9IHR5cGVOb2RlLnR5cGVOYW1lLnRleHQ7XG5cdFx0XHRjb25zdCBhbGlhcyA9IHNvdXJjZUZpbGUuc3RhdGVtZW50cy5maW5kKChzdGF0ZW1lbnQpOiBzdGF0ZW1lbnQgaXMgdHMuVHlwZUFsaWFzRGVjbGFyYXRpb24gPT5cblx0XHRcdFx0dHMuaXNUeXBlQWxpYXNEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmIHN0YXRlbWVudC5uYW1lLnRleHQgPT09IHJlZmVyZW5jZWROYW1lKTtcblx0XHRcdGlmIChhbGlhcykge1xuXHRcdFx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnJlc29sdmVLZXlvZlR5cGUoYWxpYXMudHlwZSwgc291cmNlRmlsZSk7XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHRwcml2YXRlIHJlc29sdmVDb25zdE9iamVjdEtleXMgKG5hbWU6IHN0cmluZywgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHN0cmluZ1tdIHwgdW5kZWZpbmVkIHtcblx0XHRmb3IgKGNvbnN0IHN0YXRlbWVudCBvZiBzb3VyY2VGaWxlLnN0YXRlbWVudHMpIHtcblx0XHRcdGlmICghdHMuaXNWYXJpYWJsZVN0YXRlbWVudChzdGF0ZW1lbnQpIHx8XG5cdFx0XHRcdChzdGF0ZW1lbnQuZGVjbGFyYXRpb25MaXN0LmZsYWdzICYgdHMuTm9kZUZsYWdzLkNvbnN0KSA9PT0gMCkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3QgZGVjbGFyYXRpb24gb2Ygc3RhdGVtZW50LmRlY2xhcmF0aW9uTGlzdC5kZWNsYXJhdGlvbnMpIHtcblx0XHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoZGVjbGFyYXRpb24ubmFtZSkgfHwgZGVjbGFyYXRpb24ubmFtZS50ZXh0ICE9PSBuYW1lIHx8XG5cdFx0XHRcdFx0IWRlY2xhcmF0aW9uLmluaXRpYWxpemVyIHx8ICF0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGRlY2xhcmF0aW9uLmluaXRpYWxpemVyKSkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IG5hbWVzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdFx0XHRmb3IgKGNvbnN0IHByb3BlcnR5IG9mIGRlY2xhcmF0aW9uLmluaXRpYWxpemVyLnByb3BlcnRpZXMpIHtcblx0XHRcdFx0XHRpZiAoIXRzLmlzUHJvcGVydHlBc3NpZ25tZW50KHByb3BlcnR5KSB8fFxuXHRcdFx0XHRcdFx0KCF0cy5pc0lkZW50aWZpZXIocHJvcGVydHkubmFtZSkgJiYgIXRzLmlzU3RyaW5nTGl0ZXJhbChwcm9wZXJ0eS5uYW1lKSkpIHtcblx0XHRcdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdG5hbWVzLnB1c2gocHJvcGVydHkubmFtZS50ZXh0KTtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gbmFtZXM7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0aGUgZnVsbCBkZWZpbmUoKSBjYWxsIGNvbnRleHQ6IHR5cGUgbmFtZSwgcGFyZW50IHR5cGUsIGFuZCBjb2xsZWN0aW9uLlxuXHQgKiBIYW5kbGVzIGRpcmVjdCBjYWxscywgcHJvcGVydHktYWNjZXNzIGNhbGxzLCBjaGFpbmVkIGNhbGxzLCBhbmQgdGhlXG5cdCAqIGV4cGxpY2l0LXNvdXJjZSBmb3JtIGBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKWAuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3REZWZpbmVDb250ZXh0IChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgdHlwZU5hbWVPdmVycmlkZT86IHN0cmluZyk6IHtcblx0XHR0eXBlTmFtZT86IHN0cmluZztcblx0XHRwYXJlbnRUeXBlPzogVHlwZU5vZGU7XG5cdFx0Y29sbGVjdGlvbklkPzogc3RyaW5nO1xuXHR9IHtcblx0XHRjb25zdCB0eXBlTmFtZSA9IHR5cGVOYW1lT3ZlcnJpZGUgPz8gdGhpcy5leHRyYWN0VHlwZU5hbWUoY2FsbCk7XG5cdFx0aWYgKCF0eXBlTmFtZSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gY2FsbDtcblxuXHRcdC8vIERpcmVjdCBjYWxsOiBkZWZpbmUoJ1R5cGVOYW1lJywgLi4uKSBvciBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0Ly8gRXhwbGljaXQtc291cmNlIGZvcm06IGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdFx0XHRpZiAoY2FsbC5hcmd1bWVudHMubGVuZ3RoID49IDIgJiYgdHMuaXNJZGVudGlmaWVyKGNhbGwuYXJndW1lbnRzWyAwIF0pKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZU5hbWUgPSBjYWxsLmFyZ3VtZW50c1sgMCBdLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBQbGFpbiByb290IGRlZmluZSBpbiBkZWZhdWx0IGNvbGxlY3Rpb25cblx0XHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiBYLmRlZmluZSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0Y29uc3Qgb2JqID0gZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG9iaikpIHtcblx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShvYmoudGV4dCk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBOZXN0ZWQgYWNjZXNzOiBpbnN0YW5jZS5UeXBlLmRlZmluZSAtIHRyeSB0byByZXNvbHZlXG5cdFx0XHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKG9iaik7XG5cdFx0XHRcdGlmIChjaGFpbi5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoY2hhaW4uam9pbignLicpKTtcblx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUgfTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihvYmopKSB7XG5cdFx0XHRcdC8vIERldGVybWluZSB0aGUgY29sbGVjdGlvbiBjb250ZXh0IGZyb20gdGhlIHJvb3Qgb2YgdGhlIGNoYWluIHNvIHRoYXRcblx0XHRcdFx0Ly8gY3VzdG9tLWNvbGxlY3Rpb24gdHlwZXMgZG8gbm90IGdldCBjb25mdXNlZCB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcy5cblx0XHRcdFx0Y29uc3Qgcm9vdElkID0gdGhpcy5nZXRSb290SWRlbnRpZmllcihvYmouZXhwcmVzc2lvbik7XG5cdFx0XHRcdGNvbnN0IGV4cGVjdGVkQ29sbGVjdGlvbklkID0gcm9vdElkXG5cdFx0XHRcdFx0PyB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uocm9vdElkLnRleHQpLmNvbGxlY3Rpb25JZFxuXHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXG5cdFx0XHRcdC8vIENoYWluZWQgY2FsbDogZGVmaW5lKCdBJykuZGVmaW5lKCdCJykgb3IgbW5lbW9uaWNhLmRlZmluZSgnQScpLmRlZmluZSgnQicpXG5cdFx0XHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ2FsbChvYmosIGNhbGwuZ2V0U291cmNlRmlsZSgpKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdFR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0Ly8gSW5oZXJpdCBjb2xsZWN0aW9uIGZyb20gdGhlIHBhcmVudCB0eXBlIChpZiBhbnkpXG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIENoYWluZWQgbGF6eSBjYWxsOiBsYXp5KCdBJykuZGVmaW5lKCdCJykgb3IgVHlwZS5sYXp5KCdBJykuZGVmaW5lKCdCJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzTGF6eUNhbGwob2JqLCBjYWxsLmdldFNvdXJjZUZpbGUoKSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gQnVpbGRlciBsb29rdXAgY2hhaW46IEFwcC5sb29rdXAoJ1VzZXInKS5kZWZpbmUoJ0FkbWluJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMb29rdXBDYWxsKG9iaikpIHtcblx0XHRcdFx0XHRjb25zdCBsb29rZWRVcFBhdGggPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKG9iaik7XG5cdFx0XHRcdFx0aWYgKGxvb2tlZFVwUGF0aCkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUobG9va2VkVXBQYXRoKTtcblx0XHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZS5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHR9XG5cblx0LyoqXG5cdCAqIFByZWZpeCBhIGRvdHRlZCB0eXBlIHBhdGggd2l0aCBhIGNvbGxlY3Rpb24gaWRlbnRpZmllciBzbyBjdXN0b20tY29sbGVjdGlvblxuXHQgKiB0eXBlcyBkbyBub3QgY29sbGlkZSB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcyBpbiB0aGUgZ3JhcGguXG5cdCAqL1xuXHRwcml2YXRlIHByZWZpeENvbGxlY3Rpb25QYXRoIChwYXRoOiBzdHJpbmcsIGNvbGxlY3Rpb25JZDogc3RyaW5nKTogc3RyaW5nIHtcblx0XHRyZXR1cm4gYCR7Y29sbGVjdGlvbklkfTo6JHtwYXRofWA7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGRlZmluZSgpIHNvdXJjZSBpZGVudGlmaWVyIHRvIGVpdGhlciBhIHBhcmVudCB0eXBlLCBhIGNvbGxlY3Rpb24sXG5cdCAqIG9yIHRoZSBkZWZhdWx0IChtb2R1bGUgb2JqZWN0KSBjb2xsZWN0aW9uLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRGVmaW5lU291cmNlIChzb3VyY2VOYW1lOiBzdHJpbmcpOiB7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Ly8gTW9kdWxlIG9iamVjdCBhbGlhc2VzIC0+IHJvb3QgaW4gZGVmYXVsdCBjb2xsZWN0aW9uXG5cdFx0aWYgKHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhzb3VyY2VOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdC8vIENvbGxlY3Rpb24gdmFyaWFibGVzIC0+IHJvb3QgaW4gdGhhdCBjb2xsZWN0aW9uXG5cdFx0Y29uc3QgY29sbGVjdGlvbklkID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChzb3VyY2VOYW1lKTtcblx0XHRpZiAoY29sbGVjdGlvbklkKSB7XG5cdFx0XHRyZXR1cm4geyBjb2xsZWN0aW9uSWQgfTtcblx0XHR9XG5cblx0XHQvLyBPdGhlcndpc2UgdHJlYXQgYXMgYSB0eXBlIHZhcmlhYmxlIHJlZmVyZW5jZVxuXHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlJZGVudGlmaWVyKHNvdXJjZU5hbWUpO1xuXHRcdHJldHVybiB7IHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhIGNhbGwgZXhwcmVzc2lvbiBpcyBhIGxvb2t1cCgpIGNhbGwuXG5cdCAqL1xuXHRwcml2YXRlIGlzTG9va3VwQ2FsbCAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24pOiBib29sZWFuIHtcblx0XHRjb25zdCBleHByID0gbm9kZS5leHByZXNzaW9uO1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikgJiYgZXhwci50ZXh0ID09PSAnbG9va3VwJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSAmJiBleHByLm5hbWUudGV4dCA9PT0gJ2xvb2t1cCcpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGxvb2t1cCgpIGNhbGwgdG8gYSBkb3R0ZWQgdHlwZSBwYXRoIChiZXN0IGVmZm9ydCkuXG5cdCAqIEhhbmRsZXM6XG5cdCAqICAgbG9va3VwKCdVc2VyJylcblx0ICogICBsb29rdXAoc291cmNlLCAnVXNlcicpXG5cdCAqICAgQXBwLmxvb2t1cCgnVXNlcicpXG5cdCAqICAgY29sbGVjdGlvbi5sb29rdXAoJ1VzZXIuQWRtaW4nKVxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlTG9va3VwUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGFyZ3MgPSBjYWxsLmFyZ3VtZW50cztcblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gU2luZ2xlLWFyZyBsb29rdXA6IGxvb2t1cCgnVXNlcicpIG9yIEFwcC5sb29rdXAoJ1VzZXInKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMSkge1xuXHRcdFx0Y29uc3QgWyBhcmcgXSA9IGFyZ3M7XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGFyZykgfHwgdHMuaXNOb1N1YnN0aXR1dGlvblRlbXBsYXRlTGl0ZXJhbChhcmcpKSB7XG5cdFx0XHRcdGNvbnN0IHBhdGggPSBhcmcudGV4dDtcblx0XHRcdFx0Ly8gSWYgdGhpcyBpcyBhIG1ldGhvZCBjYWxsIG9uIGEgc291cmNlLCByZXNvbHZlIHJlbGF0aXZlIHRvIHRoYXQgc291cmNlLlxuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdGNvbnN0IHNvdXJjZUV4cHIgPSBjYWxsLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKHNvdXJjZUV4cHIpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBzb3VyY2VOYW1lID0gc291cmNlRXhwci50ZXh0O1xuXHRcdFx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShzb3VyY2VOYW1lKTtcblx0XHRcdFx0XHRcdGlmIChzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUpIHtcblx0XHRcdFx0XHRcdFx0Ly8gVHlwZSBsb29rdXA6IHJlbGF0aXZlIGZpcnN0LCB0aGVuIHJvb3QgZmFsbGJhY2suXG5cdFx0XHRcdFx0XHRcdC8vIEZvciBhIHR5cGUgaW5zaWRlIGEgY3VzdG9tIGNvbGxlY3Rpb24gdGhlIGZhbGxiYWNrIHJvb3QgaXNcblx0XHRcdFx0XHRcdFx0Ly8gdGhlIGNvbGxlY3Rpb24gcm9vdCwgbmV2ZXIgdGhlIGRlZmF1bHQgY29sbGVjdGlvbi5cblx0XHRcdFx0XHRcdFx0Y29uc3QgcmVsYXRpdmVQYXRoID0gYCR7c291cmNlQ29udGV4dC5wYXJlbnRUeXBlLmZ1bGxQYXRofS4ke3BhdGh9YDtcblx0XHRcdFx0XHRcdFx0aWYgKHRoaXMuZ3JhcGguZmluZFR5cGUocmVsYXRpdmVQYXRoKSkge1xuXHRcdFx0XHRcdFx0XHRcdHJldHVybiByZWxhdGl2ZVBhdGg7XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdFx0aWYgKHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKSB7XG5cdFx0XHRcdFx0XHRcdFx0cmV0dXJuIHRoaXMucHJlZml4Q29sbGVjdGlvblBhdGgocGF0aCwgc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRcdHJldHVybiBwYXRoO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKSB7XG5cdFx0XHRcdFx0XHRcdC8vIENvbGxlY3Rpb24gbG9va3VwOiBwcmVmaXggcGF0aCB3aXRoIHRoZSBjb2xsZWN0aW9uIGlkXG5cdFx0XHRcdFx0XHRcdHJldHVybiB0aGlzLnByZWZpeENvbGxlY3Rpb25QYXRoKHBhdGgsIHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHBhdGg7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIFR3by1hcmcgbG9va3VwOiBsb29rdXAoc291cmNlLCAnVXNlcicpXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIpIHtcblx0XHRcdGNvbnN0IFsgc291cmNlQXJnLCBwYXRoQXJnIF0gPSBhcmdzO1xuXHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoc291cmNlQXJnKSB8fCAhdHMuaXNTdHJpbmdMaXRlcmFsKHBhdGhBcmcpKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBzb3VyY2VOYW1lID0gc291cmNlQXJnLnRleHQ7XG5cdFx0XHRjb25zdCBwYXRoID0gcGF0aEFyZy50ZXh0O1xuXHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShzb3VyY2VOYW1lKTtcblx0XHRcdGlmIChzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUpIHtcblx0XHRcdFx0Ly8gU2FtZSByZWxhdGl2ZS1maXJzdCBsYXcgYXMgdGhlIHNpbmdsZS1hcmcgZm9ybTsgY29sbGVjdGlvblxuXHRcdFx0XHQvLyBtZW1iZXJzIGZhbGwgYmFjayB0byB0aGVpciBjb2xsZWN0aW9uIHJvb3QsIG5vdCB0aGUgZ2xvYmFsIG9uZS5cblx0XHRcdFx0Y29uc3QgcmVsYXRpdmVQYXRoID0gYCR7c291cmNlQ29udGV4dC5wYXJlbnRUeXBlLmZ1bGxQYXRofS4ke3BhdGh9YDtcblx0XHRcdFx0aWYgKHRoaXMuZ3JhcGguZmluZFR5cGUocmVsYXRpdmVQYXRoKSkge1xuXHRcdFx0XHRcdHJldHVybiByZWxhdGl2ZVBhdGg7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHRoaXMucHJlZml4Q29sbGVjdGlvblBhdGgocGF0aCwgc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiBwYXRoO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKSB7XG5cdFx0XHRcdHJldHVybiB0aGlzLnByZWZpeENvbGxlY3Rpb25QYXRoKHBhdGgsIHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKTtcblx0XHRcdH1cblx0XHRcdHJldHVybiBwYXRoO1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogTG9va3VwLWxhdyBkZWxlZ2F0ZSBmb3IgdGhlIGxvY2FsLXNjb3BlIHdhbGtlciAoc2NvcGVzLmpzb24gdHlwZVBhdGhcblx0ICogbWV0YWRhdGEpOiByZXNvbHZlIGEgbG9va3VwKCkgaW5pdGlhbGl6ZXIgY2FsbCB0aHJvdWdoIGV4YWN0bHkgdGhlXG5cdCAqIHRpZXJzIHRoZSB1c2FnZXMgcGFzcyByZXNvbHZlZCBpdCBhZ2FpbnN0IChzYW1lIHNvdXJjZSByZXNvbHV0aW9uLFxuXHQgKiBzYW1lIGNvbXBsZXRlIGdyYXBoKS4gVGhlIHdhbGtlciBydW5zIGl0cyBvd24gc2NvcGUtY2hhaW4gdmFsdWUtc2NvcGVcblx0ICogdGllciBiZWZvcmUgZGVsZWdhdGluZzsgZXZlcnl0aGluZyBhYm92ZSB2YWx1ZSBzY29wZSBsYW5kcyBoZXJlLCBzb1xuXHQgKiBzY29wZXMuanNvbiBuZXZlciBkaXNhZ3JlZXMgd2l0aCB0aGUgaGFyZC1mYWlsLWxhdyB2ZXJkaWN0cy5cblx0ICovXG5cdHJlc29sdmVMb29rdXBDYWxsUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMucmVzb2x2ZUxvb2t1cFBhdGgoY2FsbCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHRcdCogRmluZCBhIHBhcmVudCB0eXBlIGJ5IGl0cyBuYW1lLCBzZWFyY2hpbmcgaW4gdGhlIGdyYXBoLlxuXHRcdCogV2hlbiBjb2xsZWN0aW9uSWQgaXMgcHJvdmlkZWQsIG9ubHkgdHlwZXMgZnJvbSB0aGF0IGNvbGxlY3Rpb24gYXJlIGNvbnNpZGVyZWQuXG5cdFx0Ki9cblx0cHJpdmF0ZSBmaW5kUGFyZW50VHlwZUJ5TmFtZSAoXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZ1xuXHQpOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgbWF0Y2hlc0NvbGxlY3Rpb24gPSAodHlwZTogVHlwZU5vZGUpOiBib29sZWFuID0+IHtcblx0XHRcdGlmIChjb2xsZWN0aW9uSWQgPT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRyZXR1cm4gdHlwZS5jb2xsZWN0aW9uSWQgPT09IHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB0eXBlLmNvbGxlY3Rpb25JZCA9PT0gY29sbGVjdGlvbklkO1xuXHRcdH07XG5cblx0XHQvLyBGaXJzdCB0cnkgZXhhY3QgbWF0Y2ggKGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcyB1c2UgdGhlIHBsYWluIGRvdHRlZCBwYXRoKVxuXHRcdGNvbnN0IGV4YWN0ID0gdGhpcy5ncmFwaC5maW5kVHlwZShuYW1lKTtcblx0XHRpZiAoZXhhY3QgJiYgbWF0Y2hlc0NvbGxlY3Rpb24oZXhhY3QpKSB7XG5cdFx0XHRyZXR1cm4gZXhhY3Q7XG5cdFx0fVxuXG5cdFx0Ly8gVGhlbiBzZWFyY2ggdGhyb3VnaCBhbGwgdHlwZXMgZm9yIG9uZSB3aXRoIG1hdGNoaW5nIG5hbWUgYW5kIGNvbGxlY3Rpb25cblx0XHRmb3IgKGNvbnN0IHR5cGUgb2YgdGhpcy5ncmFwaC5nZXRBbGxUeXBlcygpKSB7XG5cdFx0XHRpZiAodHlwZS5uYW1lID09PSBuYW1lICYmIG1hdGNoZXNDb2xsZWN0aW9uKHR5cGUpKSB7XG5cdFx0XHRcdHJldHVybiB0eXBlO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0XHQqIEZpbmQgYSBwYXJlbnQgdHlwZSBmcm9tIGFuIGlkZW50aWZpZXIgcmVmZXJlbmNlLlxuXHRcdCogSGFuZGxlcyBib3RoIGFsaWFzZWQgdmFyaWFibGVzIChjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKSlcblx0XHQqIGFuZCBkaXJlY3QgY2xhc3MvdHlwZSBuYW1lcy5cblx0XHQqL1xuXHRwcml2YXRlIGZpbmRQYXJlbnRUeXBlQnlJZGVudGlmaWVyIChuYW1lOiBzdHJpbmcpOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gRmlyc3QgY2hlY2sgdmFyaWFibGUgbWFwcGluZzogY29uc3QgVXNlciA9IGRlZmluZSgnVXNlckVudGl0eScsIC4uLilcblx0XHRjb25zdCBtYXBwZWRGdWxsUGF0aCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KG5hbWUpO1xuXHRcdGlmIChtYXBwZWRGdWxsUGF0aCkge1xuXHRcdFx0Y29uc3QgbWFwcGVkTm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUobWFwcGVkRnVsbFBhdGgpO1xuXHRcdFx0aWYgKG1hcHBlZE5vZGUpIHJldHVybiBtYXBwZWROb2RlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKG5hbWUpO1xuXHRcdHJldHVybiBwYXJlbnROb2RlO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCB0aGUgbGVmdG1vc3QgaWRlbnRpZmllciBvZiBhIHByb3BlcnR5LWFjY2VzcyBjaGFpbi5cblx0ICogRm9yIGBBcHAuZGVmaW5lKCdVc2VyJykuZGVmaW5lKCdBZG1pbicpYCB0aGlzIHJldHVybnMgdGhlIGBBcHBgIGlkZW50aWZpZXIuXG5cdCAqL1xuXHRwcml2YXRlIGdldFJvb3RJZGVudGlmaWVyIChleHByOiB0cy5FeHByZXNzaW9uKTogdHMuSWRlbnRpZmllciB8IHVuZGVmaW5lZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLkV4cHJlc3Npb24gPSBleHByO1xuXHRcdHdoaWxlICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50KSkge1xuXHRcdFx0cmV0dXJuIGN1cnJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0XHQqIEdldCBwcm9wZXJ0eSBjaGFpbiBmcm9tIG5lc3RlZCBhY2Nlc3Ncblx0XHQqL1xuXHRwcml2YXRlIGdldFByb3BlcnR5Q2hhaW4gKGV4cHI6IHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbiB8IHRzLklkZW50aWZpZXIpOiBzdHJpbmdbXSB7XG5cdFx0Y29uc3QgY2hhaW46IHN0cmluZ1tdID0gW107XG5cblx0XHRsZXQgY3VycmVudDogdHMuRXhwcmVzc2lvbiA9IGV4cHI7XG5cdFx0d2hpbGUgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRpZiAoY3VycmVudC5uYW1lKSB7XG5cdFx0XHRcdGNoYWluLnVuc2hpZnQoY3VycmVudC5uYW1lLnRleHQpO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQuZXhwcmVzc2lvbjtcblx0XHR9XG5cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQpKSB7XG5cdFx0XHRjaGFpbi51bnNoaWZ0KGN1cnJlbnQudGV4dCk7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGNoYWluO1xuXHR9XG5cblx0cHJpdmF0ZSBmaW5kQ29uc3RydWN0b3JJbk1vZHVsZSAoXG5cdFx0bW9kdWxlUGF0aDogc3RyaW5nLFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRkZXB0aDogbnVtYmVyXG5cdCk6IENvbnN0cnVjdG9ySGFuZGxlciB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKGRlcHRoID4gTUFYX1JFRVhQT1JUX0NIQVNFX0RFUFRIKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IGJpbmRpbmdzID0gdGhpcy5jb25zdHJ1Y3RvckJpbmRpbmdzLmdldChtb2R1bGVQYXRoKTtcblx0XHRjb25zdCBkaXJlY3QgPSBiaW5kaW5ncz8uZ2V0KG5hbWUpO1xuXHRcdGlmIChkaXJlY3QpIHtcblx0XHRcdHJldHVybiBkaXJlY3Q7XG5cdFx0fVxuXHRcdGNvbnN0IGxvY2FsQWxpYXMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcy5nZXQobW9kdWxlUGF0aCk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWxBbGlhcykge1xuXHRcdFx0Y29uc3QgYWxpYXNlZCA9IGJpbmRpbmdzPy5nZXQobG9jYWxBbGlhcyk7XG5cdFx0XHRpZiAoYWxpYXNlZCkge1xuXHRcdFx0XHRyZXR1cm4gYWxpYXNlZDtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCByZUV4cG9ydFNwZWNpZmllciA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuZ2V0KG1vZHVsZVBhdGgpPy5nZXQobmFtZSk7XG5cdFx0aWYgKHJlRXhwb3J0U3BlY2lmaWVyKSB7XG5cdFx0XHRjb25zdCBuZXh0UmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKHJlRXhwb3J0U3BlY2lmaWVyLCBtb2R1bGVQYXRoKTtcblx0XHRcdGlmIChuZXh0UmVzb2x1dGlvbiAmJiAhbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRjb25zdCBmb3VuZCA9IHRoaXMuZmluZENvbnN0cnVjdG9ySW5Nb2R1bGUobmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBuYW1lLCBkZXB0aCArIDEpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCBzdGFycyA9IHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0aWYgKHN0YXJzKSB7XG5cdFx0XHRmb3IgKGNvbnN0IHN0YXJTcGVjaWZpZXIgb2Ygc3RhcnMpIHtcblx0XHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShzdGFyU3BlY2lmaWVyLCBtb2R1bGVQYXRoKTtcblx0XHRcdFx0aWYgKCFuZXh0UmVzb2x1dGlvbiB8fCBuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRDb25zdHJ1Y3RvckluTW9kdWxlKG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgbmFtZSwgZGVwdGggKyAxKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdHByaXZhdGUgcmVzb2x2ZUhlbGRDb25zdHJ1Y3RvciAobmFtZTogc3RyaW5nLCBmcm9tRmlsZTogc3RyaW5nKTogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBmaWxlUGF0aCA9IG5vZGVQYXRoLnJlc29sdmUoZnJvbUZpbGUpO1xuXHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KGZpbGVQYXRoKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChpbXBvcnRlZCAmJiAhaW1wb3J0ZWQuaXNOYW1lc3BhY2UpIHtcblx0XHRcdGNvbnN0IHJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShpbXBvcnRlZC5zcGVjaWZpZXIsIGZpbGVQYXRoKTtcblx0XHRcdGlmIChyZXNvbHV0aW9uICYmICFyZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRDb25zdHJ1Y3RvckluTW9kdWxlKHJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBpbXBvcnRlZC5vcmlnaW5hbE5hbWUsIDApO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc3QgbG9jYWwgPSB0aGlzLmNvbnN0cnVjdG9yQmluZGluZ3MuZ2V0KGZpbGVQYXRoKT8uZ2V0KG5hbWUpO1xuXHRcdHJldHVybiBsb2NhbDtcblx0fVxuXG5cdHByaXZhdGUgdW53cmFwQ29uc3RydWN0b3JBc3NlcnRpb25zIChoYW5kbGVyOiBDb25zdHJ1Y3RvckhhbmRsZXIpOiBDb25zdHJ1Y3RvckhhbmRsZXIge1xuXHRcdGxldCBjdXJyZW50ID0gaGFuZGxlcjtcblx0XHR3aGlsZSAodHMuaXNQYXJlbnRoZXNpemVkRXhwcmVzc2lvbihjdXJyZW50KSB8fCB0cy5pc0FzRXhwcmVzc2lvbihjdXJyZW50KSB8fFxuXHRcdFx0dHMuaXNUeXBlQXNzZXJ0aW9uRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0cmV0dXJuIGN1cnJlbnQ7XG5cdH1cblxuXHRwcml2YXRlIHJlc29sdmVDb25zdHJ1Y3RvckV4cHJlc3Npb24gKFxuXHRcdGV4cHJlc3Npb246IHRzLkV4cHJlc3Npb24sXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZVxuXHQpOiBDb25zdHJ1Y3RvckhhbmRsZXIgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGN1cnJlbnQgPSB0aGlzLnVud3JhcENvbnN0cnVjdG9yQXNzZXJ0aW9ucyhleHByZXNzaW9uKTtcblx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihjdXJyZW50KSkge1xuXHRcdFx0cmV0dXJuIGN1cnJlbnQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc29sdmVkID0gdGhpcy5yZXNvbHZlSGVsZENvbnN0cnVjdG9yKGN1cnJlbnQudGV4dCwgc291cmNlRmlsZS5maWxlTmFtZSk7XG5cdFx0aWYgKCFyZXNvbHZlZCkge1xuXHRcdFx0cmV0dXJuIGN1cnJlbnQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMudW53cmFwQ29uc3RydWN0b3JBc3NlcnRpb25zKHJlc29sdmVkKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIERldGVybWluZSB0aGUgY29uc3RydWN0b3IgZXhwcmVzc2lvbiBmb3IgZWl0aGVyIGEgZGVmaW5lKCkgb3IgbGF6eSgpIGNhbGwuXG5cdCAqIEZvciBkZWZpbmUoKSB0aGlzIGlzIHRoZSBjb25zdHJ1Y3QgaGFuZGxlcjsgZm9yIGxhenkoKSBpdCBpcyB0aGUgdmFsdWVcblx0ICogcmV0dXJuZWQgYnkgdGhlIGxhenkgZ2V0dGVyLiBJZGVudGlmaWVycyByZXNvbHZlIHRvIHRoZWlyIGRlY2xhcmF0aW9ucy5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENvbnN0cnVjdG9yRXhwcmVzc2lvbiAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBDb25zdHJ1Y3RvckhhbmRsZXIgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGV4cHIgPSBjYWxsLmV4cHJlc3Npb247XG5cdFx0Y29uc3QgbmFtZSA9IHRzLmlzSWRlbnRpZmllcihleHByKVxuXHRcdFx0PyBleHByLnRleHRcblx0XHRcdDogdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcilcblx0XHRcdFx0PyBleHByLm5hbWUudGV4dFxuXHRcdFx0XHQ6ICcnO1xuXHRcdGxldCBoYW5kbGVyOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkO1xuXG5cdFx0aWYgKG5hbWUgPT09ICdsYXp5Jykge1xuXHRcdFx0Y29uc3QgbGF6eUFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0XHRpZiAobGF6eUFyZ3MpIHtcblx0XHRcdFx0aGFuZGxlciA9IHRoaXMudW53cmFwTGF6eUdldHRlcihsYXp5QXJncy5nZXR0ZXIpO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSB7XG5cdFx0XHRjb25zdCBhcmdzID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGFyZ3NbIDAgXSkpIHtcblx0XHRcdFx0Y29uc3QgWyAsIG1vZGVybkhhbmRsZXIgXSA9IGFyZ3M7XG5cdFx0XHRcdGhhbmRsZXIgPSBtb2Rlcm5IYW5kbGVyO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgWyBsZWdhY3lIYW5kbGVyIF0gPSBhcmdzO1xuXHRcdFx0XHRoYW5kbGVyID0gbGVnYWN5SGFuZGxlcjtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRpZiAoIWhhbmRsZXIpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMucmVzb2x2ZUNvbnN0cnVjdG9yRXhwcmVzc2lvbihoYW5kbGVyLCBjYWxsLmdldFNvdXJjZUZpbGUoKSk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgYW4gYXN5bmMgY29uc3RydWN0b3IgaGFuZGxlcjogdGhlIGFzeW5jIG1vZGlmaWVyIG9uIGFcblx0ICogZnVuY3Rpb24gZXhwcmVzc2lvbiBvciBhcnJvdy4gQXN5bmMgQ0xBU1NFUyAoYSBjbGFzcyBjb25zdHJ1Y3RvclxuXHQgKiByZXR1cm5pbmcgYSBQcm9taXNlKSBhcmUgZGVsaWJlcmF0ZWx5IE5PVCBkZXRlY3RlZCDigJQgdGhlIHN5bnRhY3RpY1xuXHQgKiBjbGFzcyBzaGFwZSBnaXZlcyBubyByZWxpYWJsZSBzaWduYWwgd2l0aG91dCBhIHR5cGUgY2hlY2tlciwgYW5kIHRoZVxuXHQgKiBvd25lciBkZWNpZGVkIHRoZXkgYXJlIHR5cGVkIGJ5IHRoZSB1c2VyIGluIHVzZXJsYW5kLlxuXHQgKi9cblx0cHJpdmF0ZSBpc0FzeW5jQ29uc3RydWN0SGFuZGxlciAoY29uc3RydWN0b3JFeHByOiBDb25zdHJ1Y3RvckhhbmRsZXIgfCB1bmRlZmluZWQpOiBib29sZWFuIHtcblx0XHRpZiAoIWNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblx0XHRjb25zdCBpc0ZuID0gdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSB8fFxuXHRcdFx0dHMuaXNBcnJvd0Z1bmN0aW9uKGNvbnN0cnVjdG9yRXhwcikgfHwgdHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0aWYgKCFpc0ZuKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXHRcdGNvbnN0IG1vZGlmaWVycyA9IHRzLmdldE1vZGlmaWVycyhjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdGNvbnN0IHJlc3VsdCA9ICEhbW9kaWZpZXJzICYmIG1vZGlmaWVycy5zb21lKChtb2RpZmllcikgPT4ge1xuXHRcdFx0cmV0dXJuIG1vZGlmaWVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuQXN5bmNLZXl3b3JkO1xuXHRcdH0pO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gY29uc3RydWN0b3IgZnVuY3Rpb25cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFByb3BlcnRpZXMgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpO1xuXHRcdGlmICghY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRyZXR1cm4gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblx0XHR9XG5cdFx0Y29uc3QgcmVmZXJlbmNpbmdGaWxlID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9IG5vZGVQYXRoLnJlc29sdmUoY29uc3RydWN0b3JFeHByLmdldFNvdXJjZUZpbGUoKS5maWxlTmFtZSk7XG5cdFx0dHJ5IHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMuZXh0cmFjdFByb3BlcnRpZXNGcm9tQ29uc3RydWN0b3IoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fSBmaW5hbGx5IHtcblx0XHRcdHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9IHJlZmVyZW5jaW5nRmlsZTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gYSBjb25zdHJ1Y3RvciBleHByZXNzaW9uIChmdW5jdGlvbiwgYXJyb3csIG9yIGNsYXNzKS5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFByb3BlcnRpZXNGcm9tQ29uc3RydWN0b3IgKGNvbnN0cnVjdG9yRXhwcjogQ29uc3RydWN0b3JIYW5kbGVyKTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cblx0XHQvLyBCdWlsZCB0eXBlIG1hcCBmcm9tIGRhdGEgcGFyYW1ldGVyIChmb3IgdGhpcy54ID0gZGF0YS54IHBhdHRlcm5zKVxuXHRcdGNvbnN0IGRhdGFUeXBlTWFwID0gdGhpcy5idWlsZERhdGFUeXBlTWFwKGNvbnN0cnVjdG9yRXhwcik7XG5cblx0XHQvLyBIYW5kbGUgZnVuY3Rpb24gZXhwcmVzc2lvblxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzQXJyb3dGdW5jdGlvbihjb25zdHJ1Y3RvckV4cHIpIHx8XG5cdFx0XHR0cy5pc0Z1bmN0aW9uRGVjbGFyYXRpb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBjb25zdHJ1Y3RvckV4cHI7XG5cblx0XHRcdC8vIEZpcnN0LCBleHRyYWN0IHByb3BlcnRpZXMgZnJvbSBgdGhpc2AgcGFyYW1ldGVyIHR5cGUgYW5ub3RhdGlvblxuXHRcdFx0Ly8gVGhpcyBoYW5kbGVzIHBhdHRlcm5zIGxpa2U6IGZ1bmN0aW9uKHRoaXM6IFNvbWVUeXBlLCBkYXRhOiBTb21lVHlwZSkgeyB9XG5cdFx0XHRjb25zdCB0aGlzUGFyYW1Qcm9wZXJ0aWVzID0gdGhpcy5leHRyYWN0VGhpc1BhcmFtUHJvcGVydGllcyhjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0Zm9yIChjb25zdCBbIG5hbWUsIHByb3BJbmZvIF0gb2YgdGhpc1BhcmFtUHJvcGVydGllcykge1xuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCBwcm9wSW5mbyk7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEFuIGFubm90YXRlZCB0aGlzIGlzIHRoZSBjb21wbGV0ZSBkZWNsYXJlZCBpbnN0YW5jZSB0eXBlOiBhc3NpZ25tZW50c1xuXHRcdFx0Ly8gYmV5b25kIGl0IGFkZCBub3RoaW5nLiBBIGdlbmVyYXRlZCAudGFjdGljYSBvciBncmFwaC1uYW1lIGFubm90YXRpb25cblx0XHRcdC8vIGlzIHRoZSBvdXRwdXQsIG5vdCB0aGUgc291cmNlLCBzbyB0aG9zZSBoYW5kbGVycyBrZWVwIGFzc2lnbm1lbnQgZXh0cmFjdGlvbi5cblx0XHRcdGNvbnN0IGhhc0dlbmVyYXRlZFJlZmVyZW5jZSA9IHRoaXMuaGFzR2VuZXJhdGVkVGhpc0Fubm90YXRpb24oY29uc3RydWN0b3JFeHByKTtcblx0XHRcdGNvbnN0IGhhc0F1dGhvcml0YXRpdmVUaGlzQW5ub3RhdGlvbiA9ICFoYXNHZW5lcmF0ZWRSZWZlcmVuY2UgJiYgY29uc3RydWN0b3JFeHByLnBhcmFtZXRlcnMuc29tZShwYXJhbSA9PiB7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdCA9IHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSAmJiBwYXJhbS5uYW1lLnRleHQgPT09ICd0aGlzJyAmJiBwYXJhbS50eXBlICE9PSB1bmRlZmluZWQ7XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9KTtcblx0XHRcdGlmICghaGFzQXV0aG9yaXRhdGl2ZVRoaXNBbm5vdGF0aW9uICYmIGJvZHkgJiYgdHMuaXNCbG9jayhib2R5KSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IHN0bXQgb2YgYm9keS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdFx0aWYgKHRzLmlzRXhwcmVzc2lvblN0YXRlbWVudChzdG10KSkge1xuXHRcdFx0XHRcdFx0dGhpcy5leHRyYWN0UHJvcGVydHlGcm9tU3RhdGVtZW50KHN0bXQuZXhwcmVzc2lvbiwgcHJvcGVydGllcywgZGF0YVR5cGVNYXApO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIEhhbmRsZSBjbGFzcyBleHByZXNzaW9uXG5cdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikgfHwgdHMuaXNDbGFzc0RlY2xhcmF0aW9uKGNvbnN0cnVjdG9yRXhwcikpIHtcblx0XHRcdC8vIEZpcnN0IHBhc3M6IGNvbGxlY3QgYWxsIHByb3BlcnR5IHR5cGVzIGZvciBtZXRob2QgaW5mZXJlbmNlXG5cdFx0XHRjb25zdCBjbGFzc1Byb3BlcnR5VHlwZXMgPSB0aGlzLmV4dHJhY3RDbGFzc1Byb3BlcnR5VHlwZXMoY29uc3RydWN0b3JFeHByKTtcblxuXHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgY29uc3RydWN0b3JFeHByLm1lbWJlcnMpIHtcblx0XHRcdFx0Ly8gSGFuZGxlIHByb3BlcnR5IGRlY2xhcmF0aW9uc1xuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eURlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUpIHtcblx0XHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBwcm9wZXJ0aWVzXG5cdFx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0XHRcdG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkO1xuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblxuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpID8gbWVtYmVyLm5hbWUudGV4dCA6ICcnO1xuXHRcdFx0XHRcdGlmIChuYW1lKSB7XG5cdFx0XHRcdFx0XHRsZXQgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRcdGlmICh0eXBlID09PSAndW5rbm93bicgJiYgbWVtYmVyLmluaXRpYWxpemVyKSB7XG5cdFx0XHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihtZW1iZXIuaW5pdGlhbGl6ZXIpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBIYW5kbGUgbWV0aG9kIGRlY2xhcmF0aW9uc1xuXHRcdFx0XHRpZiAodHMuaXNNZXRob2REZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBtZXRob2RzXG5cdFx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0XHRcdG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkO1xuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblxuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyTWV0aG9kVHlwZShtZW1iZXIsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gSGFuZGxlIGdldHRlciBkZWNsYXJhdGlvbnNcblx0XHRcdFx0aWYgKHRzLmlzR2V0QWNjZXNzb3IobWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgZ2V0dGVyc1xuXHRcdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdFx0XHRtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZDtcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cblx0XHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHQvLyBGaXJzdCB0cnkgZXhwbGljaXQgdHlwZSBhbm5vdGF0aW9uLCB0aGVuIGluZmVyIGZyb20gZ2V0dGVyIGJvZHlcblx0XHRcdFx0XHRsZXQgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRpZiAodHlwZSA9PT0gJ3Vua25vd24nICYmIG1lbWJlci5ib2R5KSB7XG5cdFx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclJldHVyblR5cGVGcm9tQm9keShtZW1iZXIuYm9keSwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0cmVhZG9ubHkgOiB0cnVlLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHQvKipcblx0ICogQnVpbGQgYSB0eXBlIG1hcCBmcm9tIGFsbCBwYXJhbWV0ZXJzIHdpdGggaW5saW5lIG9iamVjdCB0eXBlIGFubm90YXRpb25zXG5cdCAqIFJldHVybnMgYSBtYXAgb2YgXCJwYXJhbU5hbWUucHJvcGVydHlOYW1lXCIgLT4gdHlwZVxuXHQgKi9cblx0cHJpdmF0ZSBidWlsZERhdGFUeXBlTWFwIChoYW5kbGVyQXJnOiBDb25zdHJ1Y3RvckhhbmRsZXIpOiBNYXA8c3RyaW5nLCBzdHJpbmc+IHtcblx0XHRjb25zdCB0eXBlTWFwID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblxuXHRcdGlmICghdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oaGFuZGxlckFyZykgJiYgIXRzLmlzQXJyb3dGdW5jdGlvbihoYW5kbGVyQXJnKSAmJlxuXHRcdFx0IXRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihoYW5kbGVyQXJnKSkge1xuXHRcdFx0cmV0dXJuIHR5cGVNYXA7XG5cdFx0fVxuXG5cdFx0Ly8gSXRlcmF0ZSBvdmVyIEFMTCBwYXJhbWV0ZXJzXG5cdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBoYW5kbGVyQXJnLnBhcmFtZXRlcnMpIHtcblx0XHRcdGlmICghcGFyYW0ubmFtZSB8fCAhcGFyYW0udHlwZSkgY29udGludWU7XG5cblx0XHRcdC8vIEdldCBwYXJhbWV0ZXIgbmFtZVxuXHRcdFx0bGV0IHBhcmFtTmFtZSA9ICcnO1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSkge1xuXHRcdFx0XHRwYXJhbU5hbWUgPSBwYXJhbS5uYW1lLnRleHQ7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHQvLyBTa2lwIGRlc3RydWN0dXJlZCBwYXJhbWV0ZXJzIGZvciBub3dcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cblx0XHRcdC8vIENoZWNrIGlmIGl0J3MgYW4gaW5saW5lIG9iamVjdCB0eXBlIGxpdGVyYWxcblx0XHRcdGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZShwYXJhbS50eXBlKSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBwYXJhbS50eXBlLm1lbWJlcnMpIHtcblx0XHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0XHR0eXBlTWFwLnNldChgJHtwYXJhbU5hbWV9LiR7cHJvcE5hbWV9YCwgdHlwZSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHQvLyBOYW1lZCB0eXBlIHJlZmVyZW5jZSAoYWxpYXMvaW50ZXJmYWNlL2NsYXNzLCBpbXBvcnRlZCBvclxuXHRcdFx0XHQvLyBsb2NhbCDigJQgRjE0KTogZGVjb21wb3NlIHRoZSByZXNvbHZlZCBkZWNsYXJhdGlvbiBpbnRvXG5cdFx0XHRcdC8vIHBlci1wcm9wZXJ0eSBlbnRyaWVzIHRocm91Z2ggdGhlIHNhbWUgaW1wb3J0LWF3YXJlXG5cdFx0XHRcdC8vIG1hY2hpbmVyeSBhcyBjb25zdHJ1Y3RvciBzaWduYXR1cmVzIChGMTApLCBpbmNsdWRpbmcgdGhlXG5cdFx0XHRcdC8vIGhlcml0YWdlIHdhbGsgKEYxMykuIFdpdGhvdXQgdGhpcywgYHRoaXMueCA9IHBhcmFtLnlgXG5cdFx0XHRcdC8vIHJlYWQgYHVua25vd25gIGZvciBuYW1lZCBwYXJhbXMg4oCUIG9ubHkgaW5saW5lIGxpdGVyYWxzXG5cdFx0XHRcdC8vIHdlcmUgZGVjb21wb3NlZC4gVW5yZXNvbHZhYmxlIOKGkiB3aG9sZS1wYXJhbSBmYWxsYmFja1xuXHRcdFx0XHQvLyBiZWxvdzsgYSBiYXJlIG5hbWUgaXMgbmV2ZXIgZW1pdHRlZCBlaXRoZXIgd2F5XG5cdFx0XHRcdGxldCBuYW1lZERlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQ7XG5cdFx0XHRcdGlmICh0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHBhcmFtLnR5cGUpICYmIHRzLmlzSWRlbnRpZmllcihwYXJhbS50eXBlLnR5cGVOYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHBhcmFtVHlwZU5hbWUgPSBwYXJhbS50eXBlLnR5cGVOYW1lLnRleHQ7XG5cdFx0XHRcdFx0bmFtZWREZWNsID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihwYXJhbVR5cGVOYW1lLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChuYW1lZERlY2wpIHtcblx0XHRcdFx0XHQvLyBtZW1iZXIgdHlwZXMgcmVzb2x2ZSBhZ2FpbnN0IHRoZSBERUNMQVJJTkcgZmlsZVxuXHRcdFx0XHRcdGNvbnN0IHJlZmVyZW5jaW5nRmlsZSA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRcdFx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSBuYW1lZERlY2wuZmlsZTtcblx0XHRcdFx0XHR0cnkge1xuXHRcdFx0XHRcdFx0Y29uc3QgZGVjbFByb3BlcnRpZXMgPSB0aGlzLnJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXMobmFtZWREZWNsKTtcblx0XHRcdFx0XHRcdGZvciAoY29uc3QgWyBwcm9wTmFtZSwgaW5mbyBdIG9mIGRlY2xQcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdFx0XHRcdHR5cGVNYXAuc2V0KGAke3BhcmFtTmFtZX0uJHtwcm9wTmFtZX1gLCBpbmZvLnR5cGUpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH0gZmluYWxseSB7XG5cdFx0XHRcdFx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSByZWZlcmVuY2luZ0ZpbGU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdC8vIGtlZXAgdGhlIHdob2xlLXBhcmFtIGVudHJ5IHRvbzogYHRoaXMueCA9IGRhdGFgICh0aGVcblx0XHRcdFx0XHQvLyBiYXJlIHBhcmFtZXRlcikgYXNzaWducyB0aGUgZnVsbCBleHBhbmRlZCBzaGFwZSDigJRcblx0XHRcdFx0XHQvLyB0aGUgc2FtZSBzdHJpbmcgY29uc3RydWN0b3Itc2lnbmF0dXJlIGVtaXNzaW9uIHVzZXNcblx0XHRcdFx0XHRjb25zdCB3aG9sZVR5cGUgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24obmFtZWREZWNsKTtcblx0XHRcdFx0XHRpZiAod2hvbGVUeXBlICYmIHdob2xlVHlwZSAhPT0gJ3Vua25vd24nKSB7XG5cdFx0XHRcdFx0XHR0eXBlTWFwLnNldChwYXJhbU5hbWUsIHdob2xlVHlwZSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdC8vIFN0b3JlIHNpbXBsZSBwYXJhbWV0ZXIgdHlwZXMgbGlrZSBgZGVjb3JhdGVWYWx1ZTogc3RyaW5nYFxuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblx0XHRcdFx0XHRpZiAodHlwZSAhPT0gJ3Vua25vd24nKSB7XG5cdFx0XHRcdFx0XHR0eXBlTWFwLnNldChwYXJhbU5hbWUsIHR5cGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB0eXBlTWFwO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydHkgYWNjZXNzIGNoYWluIChlLmcuLCBcImRhdGFSZW5hbWVkLmlkXCIgZnJvbSBkYXRhUmVuYW1lZC5pZClcblx0ICogSGFuZGxlcyBmYWxsYmFja3MgbGlrZTogZGF0YS5wZXJtaXNzaW9ucyB8fCBbXVxuXHQgKi9cblx0cHJpdmF0ZSBnZXRQcm9wZXJ0eUFjY2Vzc0NoYWluIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBIYW5kbGUgaWRlbnRpZmllcjogZGF0YVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLnRleHQ7XG5cdFx0fVxuXHRcdC8vIEhhbmRsZSBwcm9wZXJ0eSBhY2Nlc3M6IGRhdGEucGVybWlzc2lvbnNcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdGNvbnN0IGJhc2UgPSB0aGlzLmdldFByb3BlcnR5QWNjZXNzQ2hhaW4oZXhwci5leHByZXNzaW9uKTtcblx0XHRcdGlmIChiYXNlKSB7XG5cdFx0XHRcdHJldHVybiBgJHtiYXNlfS4ke2V4cHIubmFtZS50ZXh0fWA7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdC8vIEhhbmRsZSBmYWxsYmFjayBwYXR0ZXJuOiBkYXRhLnBlcm1pc3Npb25zIHx8IFtdXG5cdFx0aWYgKHRzLmlzQmluYXJ5RXhwcmVzc2lvbihleHByKSAmJlxuXHRcdFx0ZXhwci5vcGVyYXRvclRva2VuLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuQmFyQmFyVG9rZW4pIHtcblx0XHRcdC8vIFJldHVybiB0aGUgbGVmdCBzaWRlIG9mIHx8IG9wZXJhdG9yXG5cdFx0XHRyZXR1cm4gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGV4cHIubGVmdCk7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0eSBhc3NpZ25tZW50IGZyb20gc3RhdGVtZW50XG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RQcm9wZXJ0eUZyb21TdGF0ZW1lbnQgKFxuXHRcdGV4cHI6IHRzLkV4cHJlc3Npb24sXG5cdFx0cHJvcGVydGllczogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPixcblx0XHRkYXRhVHlwZU1hcDogTWFwPHN0cmluZywgc3RyaW5nPiA9IG5ldyBNYXAoKVxuXHQpOiB2b2lkIHtcblx0XHQvLyBIYW5kbGU6IHRoaXMucHJvcGVydHkgPSB2YWx1ZVxuXHRcdGlmICh0cy5pc0JpbmFyeUV4cHJlc3Npb24oZXhwcikgJiZcblx0XHRcdGV4cHIub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkVxdWFsc1Rva2VuKSB7XG5cdFx0XHRjb25zdCB7IGxlZnQgfSA9IGV4cHI7XG5cblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihsZWZ0KSkge1xuXHRcdFx0XHQvLyBDaGVjayBpZiBhY2Nlc3NpbmcgJ3RoaXMnIChUaGlzS2V5d29yZClcblx0XHRcdFx0aWYgKGxlZnQuZXhwcmVzc2lvbi5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uc3QgbmFtZSA9IGxlZnQubmFtZT8udGV4dDtcblx0XHRcdFx0XHRpZiAobmFtZSkge1xuXHRcdFx0XHRcdFx0Ly8gVHJ5IHRvIGdldCB0eXBlIGZyb20gZGF0YVR5cGVNYXAgdXNpbmcgZnVsbCBhY2Nlc3MgY2hhaW4gKGUuZy4sIFwiZGF0YVJlbmFtZWQuaWRcIilcblx0XHRcdFx0XHRcdGNvbnN0IGFjY2Vzc0NoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGV4cHIucmlnaHQpO1xuXHRcdFx0XHRcdFx0bGV0IHR5cGUgPSBhY2Nlc3NDaGFpbiA/IGRhdGFUeXBlTWFwLmdldChhY2Nlc3NDaGFpbikgOiB1bmRlZmluZWQ7XG5cdFx0XHRcdFx0XHQvLyBJZiBub3QgZm91bmQgYW5kIFJIUyBpcyBhIHNpbXBsZSBpZGVudGlmaWVyLCB0cnkgbG9va2luZyBpdCB1cCBkaXJlY3RseVxuXHRcdFx0XHRcdFx0aWYgKCF0eXBlICYmIHRzLmlzSWRlbnRpZmllcihleHByLnJpZ2h0KSkge1xuXHRcdFx0XHRcdFx0XHR0eXBlID0gZGF0YVR5cGVNYXAuZ2V0KGV4cHIucmlnaHQudGV4dCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHQvLyBhIGJvdW5kIGNvbnN0cnVjdGlvbiByZXN1bHQgKG5ldy9sb29rdXAvY2hhaW4vZm9yay9cblx0XHRcdFx0XHRcdC8vIG1lcmdlL2NhbGwpOiB0aGUgdmFsdWUgc2NvcGUgYmluZGluZyBzdXBwbGllcyB0aGVcblx0XHRcdFx0XHRcdC8vIGdyYXBoIHR5cGUg4oCUIGVtaXR0ZWQgYnkgaXRzIGluc3RhbmNlLXR5cGUgbmFtZVxuXHRcdFx0XHRcdFx0aWYgKCF0eXBlICYmIHRzLmlzSWRlbnRpZmllcihleHByLnJpZ2h0KSkge1xuXHRcdFx0XHRcdFx0XHRjb25zdCBib3VuZCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGV4cHIucmlnaHQudGV4dCk7XG5cdFx0XHRcdFx0XHRcdGlmIChib3VuZCkge1xuXHRcdFx0XHRcdFx0XHRcdC8vIEVtaXQgdGhlIGFsaWFzIHR5cGVzLnRzIGRlY2xhcmVzIChPcHRpb24gQlxuXHRcdFx0XHRcdFx0XHRcdC8vIHJlZ2lzdHJ5IHByZWZpeCksIG5vdCB0aGUgcmF3IGNvbGxlY3Rpb25JZDo6XG5cdFx0XHRcdFx0XHRcdFx0Ly8gZnVsbFBhdGg7IG5ldmVyLWVtaXR0ZWQgdHlwZXMgZmFsbCB0aHJvdWdoXG5cdFx0XHRcdFx0XHRcdFx0Ly8gdG8gaW5pdGlhbGl6ZXIgaW5mZXJlbmNlXG5cdFx0XHRcdFx0XHRcdFx0Y29uc3QgYm91bmROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShib3VuZCk7XG5cdFx0XHRcdFx0XHRcdFx0Y29uc3QgYm91bmRBbGlhcyA9IGJvdW5kTm9kZVxuXHRcdFx0XHRcdFx0XHRcdFx0PyB0aGlzLmdldEVtaXR0ZWRJbnN0YW5jZVR5cGVOYW1lKGJvdW5kTm9kZSlcblx0XHRcdFx0XHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0XHRcdFx0XHRcdGlmIChib3VuZEFsaWFzKSB7XG5cdFx0XHRcdFx0XHRcdFx0XHR0eXBlID0gYm91bmRBbGlhcztcblx0XHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdGlmICghdHlwZSkge1xuXHRcdFx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIoZXhwci5yaWdodCwgZGF0YVR5cGVNYXApO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0Ly8gRG9uJ3Qgb3ZlcndyaXRlIGEga25vd24gdHlwZSBmcm9tIGEgYHRoaXNgIGFubm90YXRpb25cblx0XHRcdFx0XHRcdC8vIHdpdGggYW4gdW5rbm93bi1iZWFyaW5nIGluZmVyZW5jZTogYW4gZW1wdHktYXJyYXlcblx0XHRcdFx0XHRcdC8vIGluaXRpYWxpemVyIGluZmVycyAnQXJyYXk8dW5rbm93bj4nLCB3aGljaCBtdXN0IG5vdFxuXHRcdFx0XHRcdFx0Ly8gY2xvYmJlciBhbiBhbm5vdGF0ZWQgJ0FycmF5PHsgaWQ6IG51bWJlciB9PicgZWl0aGVyLlxuXHRcdFx0XHRcdFx0Ly8gXCJLbm93blwiIG9uIHRoZSBFWElTVElORyBzaWRlIG1lYW5zIHRoZSB3aG9sZSB0eXBlIElTXG5cdFx0XHRcdFx0XHQvLyBgdW5rbm93bmAgKGV4YWN0IG1hdGNoKSDigJQgYSBzdWJzdHJpbmcgbWF0Y2ggdHJlYXRzXG5cdFx0XHRcdFx0XHQvLyBgUmVjb3JkPHN0cmluZywgdW5rbm93bj5gIGFzIHVua25vd24tYmVhcmluZyBhbmQgbGV0XG5cdFx0XHRcdFx0XHQvLyBpbmZlcmVuY2UgY2xvYmJlciBhIGdvb2QgYW5ub3RhdGlvbiAoRjE0KVxuXHRcdFx0XHRcdFx0Y29uc3QgZXhpc3RpbmcgPSBwcm9wZXJ0aWVzLmdldChuYW1lKTtcblx0XHRcdFx0XHRcdGNvbnN0IHR5cGVIYXNVbmtub3duID0gIXR5cGUgfHwgdHlwZS5pbmNsdWRlcygndW5rbm93bicpO1xuXHRcdFx0XHRcdFx0Y29uc3QgZXhpc3RpbmdJc0tub3duID0gZXhpc3RpbmcgPyBleGlzdGluZy50eXBlLnRyaW0oKSAhPT0gJ3Vua25vd24nIDogZmFsc2U7XG5cdFx0XHRcdFx0XHRpZiAoZXhpc3RpbmdJc0tub3duICYmIHR5cGVIYXNVbmtub3duKSB7XG5cdFx0XHRcdFx0XHRcdC8vIEtlZXAgdGhlIGJldHRlciB0eXBlIGZyb20gZXhwbGljaXQgYW5ub3RhdGlvblxuXHRcdFx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6IGV4aXN0aW5nID8gZXhpc3Rpbmcub3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gSGFuZGxlOiBPYmplY3QuYXNzaWduKHRoaXMsIHsgcHJvcDogdmFsdWUgfSlcblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0Y29uc3QgZm4gPSBleHByLmV4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZm4pICYmXG5cdFx0XHRcdGZuLm5hbWU/LnRleHQgPT09ICdhc3NpZ24nICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihmbi5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHRmbi5leHByZXNzaW9uLnRleHQgPT09ICdPYmplY3QnKSB7XG5cdFx0XHRcdGNvbnN0IGFyZ3MgPSBleHByLmFyZ3VtZW50cztcblx0XHRcdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIgJiYgYXJnc1sgMCBdLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdFx0XHQvLyBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSB0aGUgc2Vjb25kIGFyZ3VtZW50XG5cdFx0XHRcdFx0Y29uc3QgWyAsIHByb3BzQXJnIF0gPSBhcmdzO1xuXHRcdFx0XHRcdGlmICh0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKHByb3BzQXJnKSkge1xuXHRcdFx0XHRcdFx0Zm9yIChjb25zdCBwcm9wIG9mIHByb3BzQXJnLnByb3BlcnRpZXMpIHtcblx0XHRcdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBc3NpZ25tZW50KHByb3ApICYmIHRzLmlzSWRlbnRpZmllcihwcm9wLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRcdFx0Y29uc3QgbmFtZSA9IHByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0XHR0eXBlICAgICA6IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKHByb3AuaW5pdGlhbGl6ZXIpLFxuXHRcdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH0gZWxzZSBpZiAodHMuaXNJZGVudGlmaWVyKHByb3BzQXJnKSkge1xuXHRcdFx0XHRcdFx0Ly8gT2JqZWN0LmFzc2lnbih0aGlzLCBkYXRhKSDigJQgdGhlIGlkZW50aWZpZXIgZm9ybTogZXZlcnlcblx0XHRcdFx0XHRcdC8vIHBlci1wcm9wZXJ0eSBlbnRyeSB0aGUgZGF0YSBwYXJhbWV0ZXIgY29udHJpYnV0ZWQgdG9cblx0XHRcdFx0XHRcdC8vIHRoZSB0eXBlIG1hcCBiZWNvbWVzIGFuIG93biBwcm9wZXJ0eS4gVGhpcyBpcyB3aGF0XG5cdFx0XHRcdFx0XHQvLyBjYXJyaWVzIHRoZSBmaWVsZHMgZm9yIHRoZSBzZWxmLXJlZmVyZW5jaW5nXG5cdFx0XHRcdFx0XHQvLyBpbnRlcnNlY3Rpb24tYWxpYXMgcm9vdCBwYXR0ZXJuIChGMjEpOiB0aGUgdGhpcy1hbGlhc1xuXHRcdFx0XHRcdFx0Ly8gaXMgZXJnb25vbWljLW9ubHkgYW5kIGl0cyBpbnRlcnNlY3Rpb24gbWVtYmVycyBhcmVcblx0XHRcdFx0XHRcdC8vIG5ldmVyIGV4cGFuZGVkLCBzbyB0aGUgYXNzaWduIGlzIHdoZXJlIHRoZSByb290J3Ncblx0XHRcdFx0XHRcdC8vIGZpZWxkcyBtdXN0IGNvbWUgZnJvbVxuXHRcdFx0XHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gcHJvcHNBcmcudGV4dDtcblx0XHRcdFx0XHRcdGZvciAoY29uc3QgWyBrZXksIHR5cGUgXSBvZiBkYXRhVHlwZU1hcCkge1xuXHRcdFx0XHRcdFx0XHRpZiAoIWtleS5zdGFydHNXaXRoKGAke3BhcmFtTmFtZX0uYCkpIHtcblx0XHRcdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHRjb25zdCBuYW1lID0ga2V5LnNsaWNlKHBhcmFtTmFtZS5sZW5ndGggKyAxKTtcblx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gY2xhc3MgZGVjbGFyYXRpb24gKGluY2x1ZGluZyBtZXRob2RzIGFuZCBnZXR0ZXJzKVxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q2xhc3NQcm9wZXJ0aWVzIChjbGFzc0RlY2w6IHRzLkNsYXNzRGVjbGFyYXRpb24pOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCBwcm9wZXJ0aWVzID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblxuXHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGNsYXNzRGVjbC5tZW1iZXJzKSB7XG5cdFx0XHQvLyBIYW5kbGUgcHJvcGVydHkgZGVjbGFyYXRpb25zXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eURlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUpIHtcblx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgcHJvcGVydGllc1xuXHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0ICAgICBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZCk7XG5cdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Y29uc3QgbmFtZSA9IHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkgPyBtZW1iZXIubmFtZS50ZXh0IDogJyc7XG5cdFx0XHRcdGlmIChuYW1lKSB7XG5cdFx0XHRcdFx0Ly8gSWYgbm8gZXhwbGljaXQgdHlwZSBidXQgaGFzIGluaXRpYWxpemVyLCBpbmZlciBmcm9tIGluaXRpYWxpemVyXG5cdFx0XHRcdFx0bGV0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0aWYgKHR5cGUgPT09ICd1bmtub3duJyAmJiBtZW1iZXIuaW5pdGlhbGl6ZXIpIHtcblx0XHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihtZW1iZXIuaW5pdGlhbGl6ZXIpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdG9wdGlvbmFsIDogISFtZW1iZXIucXVlc3Rpb25Ub2tlbixcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHQvLyBIYW5kbGUgbWV0aG9kIGRlY2xhcmF0aW9uc1xuXHRcdFx0aWYgKHRzLmlzTWV0aG9kRGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIG1ldGhvZHNcblx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdCAgICAgbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQpO1xuXHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlck1ldGhvZFR5cGUobWVtYmVyKTtcblx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gSGFuZGxlIGdldHRlciBkZWNsYXJhdGlvbnNcblx0XHRcdGlmICh0cy5pc0dldEFjY2Vzc29yKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBnZXR0ZXJzXG5cdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHQgICAgIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkKTtcblx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0Ly8gRmlyc3QgdHJ5IGV4cGxpY2l0IHR5cGUgYW5ub3RhdGlvbiwgdGhlbiBpbmZlciBmcm9tIGdldHRlciBib2R5XG5cdFx0XHRcdGxldCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRpZiAodHlwZSA9PT0gJ3Vua25vd24nICYmIG1lbWJlci5ib2R5KSB7XG5cdFx0XHRcdFx0dHlwZSA9IHRoaXMuaW5mZXJSZXR1cm5UeXBlRnJvbUJvZHkobWVtYmVyLmJvZHkpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRyZWFkb25seSA6IHRydWUsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBwcm9wZXJ0aWVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgY2xhc3MgcHJvcGVydHkgdHlwZXMgZm9yIG1ldGhvZCByZXR1cm4gdHlwZSBpbmZlcmVuY2Vcblx0ICogTWFwcyBwcm9wZXJ0eSBuYW1lcyB0byB0aGVpciBUeXBlU2NyaXB0IHR5cGUgc3RyaW5nc1xuXHQgKiBOb3RlOiBJbmNsdWRlcyBwcml2YXRlL3Byb3RlY3RlZCBwcm9wZXJ0aWVzIGZvciBtZXRob2QgaW5mZXJlbmNlXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDbGFzc1Byb3BlcnR5VHlwZXMgKGNsYXNzRGVjbDogQ2xhc3NDb25zdHJ1Y3RvckhhbmRsZXIpOiBNYXA8c3RyaW5nLCBzdHJpbmc+IHtcblx0XHRjb25zdCBwcm9wZXJ0eVR5cGVzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblxuXHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGNsYXNzRGVjbC5tZW1iZXJzKSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eURlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHQvLyBJbmNsdWRlIEFMTCBwcm9wZXJ0aWVzIChldmVuIHByaXZhdGUpIGZvciBtZXRob2QgcmV0dXJuIHR5cGUgaW5mZXJlbmNlXG5cdFx0XHRcdC8vIFRoZSB2aXNpYmlsaXR5IGNoZWNrIGlzIGRvbmUgd2hlbiBhZGRpbmcgdG8gb3V0cHV0IHByb3BlcnRpZXNcblx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdGlmIChtZW1iZXIudHlwZSkge1xuXHRcdFx0XHRcdHByb3BlcnR5VHlwZXMuc2V0KG5hbWUsIHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydHlUeXBlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBJbmZlciBtZXRob2QgdHlwZSBmcm9tIG1ldGhvZCBkZWNsYXJhdGlvblxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlck1ldGhvZFR5cGUgKG1ldGhvZDogdHMuTWV0aG9kRGVjbGFyYXRpb24sIGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz4pOiBzdHJpbmcge1xuXHRcdGNvbnN0IHBhcmFtcyA9IG1ldGhvZC5wYXJhbWV0ZXJzLm1hcChwYXJhbSA9PiB7XG5cdFx0XHRjb25zdCBwYXJhbU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgPyBwYXJhbS5uYW1lLnRleHQgOiAnYXJnJztcblx0XHRcdGNvbnN0IHBhcmFtVHlwZSA9IHRoaXMuaW5mZXJUeXBlKHBhcmFtLnR5cGUpO1xuXHRcdFx0cmV0dXJuIGAke3BhcmFtTmFtZX06ICR7cGFyYW1UeXBlfWA7XG5cdFx0fSkuam9pbignLCAnKTtcblxuXHRcdGNvbnN0IHJldHVyblR5cGUgPSB0aGlzLmluZmVyUmV0dXJuVHlwZShtZXRob2QsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cblx0XHRpZiAocGFyYW1zKSB7XG5cdFx0XHRyZXR1cm4gYCgke3BhcmFtc30pID0+ICR7cmV0dXJuVHlwZX1gO1xuXHRcdH1cblx0XHRyZXR1cm4gYCgpID0+ICR7cmV0dXJuVHlwZX1gO1xuXHR9XG5cblx0cHJpdmF0ZSBoYXNHZW5lcmF0ZWRUaGlzQW5ub3RhdGlvbiAoaGFuZGxlcjogQ29uc3RydWN0b3JIYW5kbGVyKTogYm9vbGVhbiB7XG5cdFx0aWYgKHRoaXMuaGFzR2VuZXJhdGVkVHlwZVJlZmVyZW5jZShoYW5kbGVyKSkge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXHRcdGlmICghdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oaGFuZGxlcikgJiYgIXRzLmlzQXJyb3dGdW5jdGlvbihoYW5kbGVyKSAmJlxuXHRcdFx0IXRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihoYW5kbGVyKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGhhbmRsZXIucGFyYW1ldGVycykge1xuXHRcdFx0Y29uc3QgaXNUaGlzID0gdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpICYmIHBhcmFtLm5hbWUudGV4dCA9PT0gJ3RoaXMnO1xuXHRcdFx0aWYgKCFpc1RoaXMgfHwgIXBhcmFtLnR5cGUgfHwgIXRzLmlzVHlwZVJlZmVyZW5jZU5vZGUocGFyYW0udHlwZSkgfHxcblx0XHRcdFx0IXRzLmlzSWRlbnRpZmllcihwYXJhbS50eXBlLnR5cGVOYW1lKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHR5cGVOYW1lID0gcGFyYW0udHlwZS50eXBlTmFtZS50ZXh0O1xuXHRcdFx0aWYgKHRoaXMuY3VycmVudEdyYXBoQW5jaG9yPy5uYW1lID09PSB0eXBlTmFtZSB8fCB0aGlzLmN1cnJlbnRHcmFwaEFuY2hvcj8uZnVsbFBhdGggPT09IHR5cGVOYW1lKSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZ3JhcGhUeXBlID0gdGhpcy5ncmFwaC5maW5kVHlwZUJ5TmFtZSh0eXBlTmFtZSk7XG5cdFx0XHRpZiAoZ3JhcGhUeXBlKSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHRwcml2YXRlIGhhc0FueVRoaXNBbm5vdGF0aW9uIChoYW5kbGVyOiBDb25zdHJ1Y3RvckhhbmRsZXIgfCB1bmRlZmluZWQpOiBib29sZWFuIHtcblx0XHRpZiAoIWhhbmRsZXIgfHwgKCF0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihoYW5kbGVyKSAmJiAhdHMuaXNBcnJvd0Z1bmN0aW9uKGhhbmRsZXIpICYmXG5cdFx0XHQhdHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKGhhbmRsZXIpKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBoYW5kbGVyLnBhcmFtZXRlcnMuc29tZShwYXJhbSA9PiB7XG5cdFx0XHRjb25zdCBtYXRjaGVzID0gdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpICYmIHBhcmFtLm5hbWUudGV4dCA9PT0gJ3RoaXMnICYmXG5cdFx0XHRcdHBhcmFtLnR5cGU/LmtpbmQgPT09IHRzLlN5bnRheEtpbmQuQW55S2V5d29yZDtcblx0XHRcdHJldHVybiBtYXRjaGVzO1xuXHRcdH0pO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHQqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGB0aGlzYCBwYXJhbWV0ZXIgdHlwZSBhbm5vdGF0aW9uXG5cdFx0KiBIYW5kbGVzIHBhdHRlcm5zIGxpa2U6IGZ1bmN0aW9uKHRoaXM6IFNvbWVUeXBlLCBkYXRhOiBTb21lVHlwZSkgeyB9XG5cdFx0Ki9cblx0cHJpdmF0ZSBleHRyYWN0VGhpc1BhcmFtUHJvcGVydGllcyAoaGFuZGxlckFyZzogRnVuY3Rpb25Db25zdHJ1Y3RvckhhbmRsZXIpOlxuXHRcdE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Ly8gRmluZCB0aGUgYHRoaXNgIHBhcmFtZXRlciAoaWYgYW55KVxuXHRcdGZvciAoY29uc3QgcGFyYW0gb2YgaGFuZGxlckFyZy5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRpZiAocGFyYW0ubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgJiYgcGFyYW0ubmFtZS50ZXh0ID09PSAndGhpcycgJiYgcGFyYW0udHlwZSkge1xuXHRcdFx0XHQvLyBDaGVjayBpZiBpdCdzIGEgdHlwZSByZWZlcmVuY2UgKGUuZy4sIGB0aGlzOiB1c2FnZWApXG5cdFx0XHRcdGlmICh0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHBhcmFtLnR5cGUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSlcblx0XHRcdFx0XHRcdD8gcGFyYW0udHlwZS50eXBlTmFtZS50ZXh0XG5cdFx0XHRcdFx0XHQ6ICcnO1xuXG5cdFx0XHRcdFx0Ly8gUmVzb2x2ZSB0aHJvdWdoIHRoZSByZWZlcmVuY2luZyBmaWxlJ3Mgb3duIGltcG9ydHMgZmlyc3QgKEYxMClcblx0XHRcdFx0XHRjb25zdCBkZWNsID0gdHlwZU5hbWVcblx0XHRcdFx0XHRcdD8gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbih0eXBlTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKVxuXHRcdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cdFx0XHRcdFx0aWYgKGRlY2wpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGRlY2xQcm9wZXJ0aWVzID0gdGhpcy5yZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzKGRlY2wpO1xuXHRcdFx0XHRcdFx0Zm9yIChjb25zdCBbIHByb3BOYW1lLCBpbmZvIF0gb2YgZGVjbFByb3BlcnRpZXMpIHtcblx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQocHJvcE5hbWUsIGluZm8pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBDaGVjayBpZiBpdCdzIGRpcmVjdGx5IGFuIGlubGluZSB0eXBlIGxpdGVyYWwgKGUuZy4sIGB0aGlzOiB7IGlkOiBzdHJpbmcgfWApXG5cdFx0XHRcdGVsc2UgaWYgKHRzLmlzVHlwZUxpdGVyYWxOb2RlKHBhcmFtLnR5cGUpKSB7XG5cdFx0XHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgcGFyYW0udHlwZS5tZW1iZXJzKSB7XG5cdFx0XHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChwcm9wTmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdG5hbWUgICAgIDogcHJvcE5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBGb3VuZCB0aGUgYHRoaXNgIHBhcmFtZXRlciwgbm8gbmVlZCB0byBjb250aW51ZVxuXHRcdFx0XHRicmVhaztcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdC8qKlxuXHRcdCogSW5mZXIgVHlwZVNjcmlwdCB0eXBlIGZyb20gdHlwZSBub2RlXG5cdFx0Ki9cblx0LyoqXG5cdCAqIEluZmVyIFR5cGVTY3JpcHQgdHlwZSBmcm9tIHR5cGUgbm9kZVxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlclR5cGUgKHR5cGVOb2RlPzogdHMuVHlwZU5vZGUpOiBzdHJpbmcge1xuXHRcdGlmICghdHlwZU5vZGUpIHtcblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXG5cdFx0c3dpdGNoICh0eXBlTm9kZS5raW5kKSB7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlN0cmluZ0tleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bWJlcktleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkJvb2xlYW5LZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5kZWZpbmVkS2V5d29yZDpcblx0XHRcdHJldHVybiAndW5kZWZpbmVkJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bGwnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5BbnlLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdhbnknO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Vbmtub3duS2V5d29yZDpcblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlZvaWRLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICd2b2lkJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQXJyYXlUeXBlOlxuXHRcdFx0cmV0dXJuIGBBcnJheTwkeyAgdGhpcy5pbmZlclR5cGUoKHR5cGVOb2RlIGFzIHRzLkFycmF5VHlwZU5vZGUpLmVsZW1lbnRUeXBlKSAgfT5gO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlTGl0ZXJhbDoge1xuXHRcdFx0Ly8gSW5saW5lLWV4cGFuZCB0eXBlIGxpdGVyYWxzIGluc3RlYWQgb2YgY29sbGFwc2luZyB0byAnb2JqZWN0J1xuXHRcdFx0Y29uc3QgdHlwZUxpdCA9IHR5cGVOb2RlIGFzIHRzLlR5cGVMaXRlcmFsTm9kZTtcblx0XHRcdGNvbnN0IHByb3BzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgdHlwZUxpdC5tZW1iZXJzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRjb25zdCBvcHRpb25hbCA9IG1lbWJlci5xdWVzdGlvblRva2VuID8gJz8nIDogJyc7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRwcm9wcy5wdXNoKGAke3Byb3BOYW1lfSR7b3B0aW9uYWx9OiAke3R5cGV9YCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiBgeyAke3Byb3BzLmpvaW4oJzsgJyl9IH1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTGl0ZXJhbFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBzdHJpbmcgbGl0ZXJhbCB0eXBlcyBsaWtlICd1c2VyJywgJ2FkbWluJywgZXRjLlxuXHRcdFx0Y29uc3QgeyBsaXRlcmFsIH0gPSAodHlwZU5vZGUgYXMgdHMuTGl0ZXJhbFR5cGVOb2RlKTtcblx0XHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwobGl0ZXJhbCkpIHtcblx0XHRcdFx0Ly8gUmV0dXJuIHRoZSBhY3R1YWwgbGl0ZXJhbCB2YWx1ZSAoZS5nLiwgJ3VzZXInIGluc3RlYWQgb2Ygc3RyaW5nKVxuXHRcdFx0XHRyZXR1cm4gYCcke2xpdGVyYWwudGV4dH0nYDtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc051bWVyaWNMaXRlcmFsKGxpdGVyYWwpKSB7XG5cdFx0XHRcdHJldHVybiBsaXRlcmFsLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAobGl0ZXJhbC5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdHJldHVybiAndHJ1ZSc7XG5cdFx0XHR9XG5cdFx0XHRpZiAobGl0ZXJhbC5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRyZXR1cm4gJ2ZhbHNlJztcblx0XHRcdH1cblx0XHRcdGlmIChsaXRlcmFsLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQpIHtcblx0XHRcdFx0cmV0dXJuICdudWxsJztcblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlUmVmZXJlbmNlOiB7XG5cdFx0XHQvLyBIYW5kbGUgdHlwZSByZWZlcmVuY2VzIGxpa2UgTWFwPHN0cmluZywgbnVtYmVyPiwgUHJvcGVydHlJbmZvLCBldGMuXG5cdFx0XHRjb25zdCB0eXBlUmVmID0gdHlwZU5vZGUgYXMgdHMuVHlwZVJlZmVyZW5jZU5vZGU7XG5cblx0XHRcdC8vIFF1YWxpZmllZCBuYW1lcyAoTmFtZXNwYWNlLlR5cGUpOiByZXNvbHZlIHRocm91Z2ggbmFtZXNwYWNlIGltcG9ydHNcblx0XHRcdGlmICh0cy5pc1F1YWxpZmllZE5hbWUodHlwZVJlZi50eXBlTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcmVzb2x2ZWRRdWFsaWZpZWQgPSB0aGlzLmluZmVyUXVhbGlmaWVkVHlwZVJlZmVyZW5jZSh0eXBlUmVmKTtcblx0XHRcdFx0aWYgKHJlc29sdmVkUXVhbGlmaWVkICE9PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0XHRyZXR1cm4gcmVzb2x2ZWRRdWFsaWZpZWQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gdW5yZXNvbHZlZCBxdWFsaWZpZWQgcmVmZXJlbmNlcyBtdXN0IG5vdCBsZWFrIGEgYmFyZSBuYW1lXG5cdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHR9XG5cblx0XHRcdGNvbnN0IHR5cGVOYW1lID0gdHMuaXNJZGVudGlmaWVyKHR5cGVSZWYudHlwZU5hbWUpID8gdHlwZVJlZi50eXBlTmFtZS50ZXh0IDogJ3Vua25vd24nO1xuXG5cdFx0XHQvLyBJbXBvcnQtYXdhcmUgcmVmZXJlbmNlZC10eXBlIHJlc29sdXRpb24gKEYxMCk6IGEgZGVjbGFyYXRpb25cblx0XHRcdC8vIHJlYWNoZWQgdGhyb3VnaCB0aGUgY3VycmVudCBmaWxlJ3Mgb3duIGltcG9ydHMgKG9yIGl0cyBsb2NhbHMsXG5cdFx0XHQvLyBvciBhIHVuaXF1ZSBwcm9ncmFtLXdpZGUgZGVjbGFyYXRpb24pIGV4cGFuZHMgaW5saW5lXG5cdFx0XHRjb25zdCBzaW1wbGVSZWYgPSB0aGlzLnJlc29sdmVTaW1wbGVUeXBlUmVmZXJlbmNlKHR5cGVOYW1lLCB0eXBlUmVmLnR5cGVBcmd1bWVudHMsIHR5cGVSZWYpO1xuXHRcdFx0aWYgKHNpbXBsZVJlZiAhPT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdHJldHVybiBzaW1wbGVSZWY7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEJ1aWxkIGdlbmVyaWMgdHlwZSBhcmd1bWVudHNcblx0XHRcdGNvbnN0IHR5cGVBcmdzID0gKHR5cGVSZWYudHlwZUFyZ3VtZW50cyA/PyBbXSkubWFwKGFyZyA9PiB0aGlzLmluZmVyVHlwZShhcmcpKTtcblx0XHRcdHJldHVybiBgJHt0eXBlTmFtZX08JHt0eXBlQXJncy5qb2luKCcsICcpfT5gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5pb25UeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgdW5pb24gdHlwZXMgbGlrZSAnYScgfCAnYicgfCAnYydcblx0XHRcdGNvbnN0IHVuaW9uVHlwZSA9IHR5cGVOb2RlIGFzIHRzLlVuaW9uVHlwZU5vZGU7XG5cdFx0XHRjb25zdCB0eXBlcyA9IHVuaW9uVHlwZS50eXBlcy5tYXAodCA9PiB0aGlzLmluZmVyVHlwZSh0KSk7XG5cdFx0XHRyZXR1cm4gdHlwZXMuam9pbignIHwgJyk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5JbnRlcnNlY3Rpb25UeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgaW50ZXJzZWN0aW9uIHR5cGVzIGxpa2UgVHlwZUEgJiBUeXBlQlxuXHRcdFx0Y29uc3QgaW50ZXJzZWN0aW9uVHlwZSA9IHR5cGVOb2RlIGFzIHRzLkludGVyc2VjdGlvblR5cGVOb2RlO1xuXHRcdFx0Y29uc3QgdHlwZXMgPSBpbnRlcnNlY3Rpb25UeXBlLnR5cGVzLm1hcCh0ID0+IHRoaXMuaW5mZXJUeXBlKHQpKTtcblx0XHRcdHJldHVybiB0eXBlcy5qb2luKCcgJiAnKTtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR1cGxlVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHR1cGxlIHR5cGVzIGxpa2UgW3N0cmluZywgbnVtYmVyXVxuXHRcdFx0Y29uc3QgdHVwbGVUeXBlID0gdHlwZU5vZGUgYXMgdHMuVHVwbGVUeXBlTm9kZTtcblx0XHRcdGNvbnN0IGVsZW1lbnRzID0gdHVwbGVUeXBlLmVsZW1lbnRzLm1hcChlbGVtID0+IHRoaXMuaW5mZXJUeXBlKGVsZW0gYXMgdHMuVHlwZU5vZGUpKTtcblx0XHRcdHJldHVybiBgWyR7ZWxlbWVudHMuam9pbignLCAnKX1dYDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk9wdGlvbmFsVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIG9wdGlvbmFsIGVsZW1lbnQgaW4gdHVwbGU6IHN0cmluZz9cblx0XHRcdGNvbnN0IG9wdGlvbmFsVHlwZSA9IHR5cGVOb2RlIGFzIHRzLk9wdGlvbmFsVHlwZU5vZGU7XG5cdFx0XHRyZXR1cm4gYCR7dGhpcy5pbmZlclR5cGUob3B0aW9uYWxUeXBlLnR5cGUpICB9P2A7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5SZXN0VHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHJlc3QgZWxlbWVudDogLi4uVFxuXHRcdFx0Y29uc3QgcmVzdFR5cGUgPSB0eXBlTm9kZSBhcyB0cy5SZXN0VHlwZU5vZGU7XG5cdFx0XHRyZXR1cm4gYC4uLiR7ICB0aGlzLmluZmVyVHlwZShyZXN0VHlwZS50eXBlKX1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuUGFyZW50aGVzaXplZFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBwYXJlbnRoZXNpemVkIHR5cGVzOiAoQSB8IEIpXG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclR5cGUoKHR5cGVOb2RlIGFzIHRzLlBhcmVudGhlc2l6ZWRUeXBlTm9kZSkudHlwZSk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5JbmRleGVkQWNjZXNzVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIGluZGV4ZWQgYWNjZXNzOiBUW0tdXG5cdFx0XHRjb25zdCBpbmRleGVkID0gdHlwZU5vZGUgYXMgdHMuSW5kZXhlZEFjY2Vzc1R5cGVOb2RlO1xuXHRcdFx0Ly8gRjIzOiB1bndyYXAgcGFyZW50aGVzZXMgYXJvdW5kIHRoZSBvYmplY3Qg4oCUIGAodHlwZW9mXG5cdFx0XHQvLyBsaXN0KVtudW1iZXJdYCBtdXN0IHRha2UgdGhlIHR5cGVvZiBicmFuY2ggbGlrZSB0aGUgYmFyZVxuXHRcdFx0Ly8gc3BlbGxpbmc7IG90aGVyd2lzZSB0aGUgZ2VuZXJhbCBwYXRoIGluZmVycyB0aGUgdW5pb24gYW5kXG5cdFx0XHQvLyBnbHVlcyB0aGUgc3VmZml4IG9udG8gdGhlIExBU1QgbWVtYmVyXG5cdFx0XHQvLyAoYCdhJyB8ICdiJ1tudW1iZXJdYClcblx0XHRcdGxldCBvYmplY3ROb2RlOiB0cy5UeXBlTm9kZSA9IGluZGV4ZWQub2JqZWN0VHlwZTtcblx0XHRcdHdoaWxlICh0cy5pc1BhcmVudGhlc2l6ZWRUeXBlTm9kZShvYmplY3ROb2RlKSkge1xuXHRcdFx0XHRvYmplY3ROb2RlID0gb2JqZWN0Tm9kZS50eXBlO1xuXHRcdFx0fVxuXHRcdFx0Ly8gYHR5cGVvZiBjb25zdEFycmF5W0tdYCDigJQgZWxlbWVudCB0eXBlIG9mIGEgdHJhY2tlZCBjb25zdCBhcnJheTpcblx0XHRcdC8vIGVtaXQgdGhlIGVsZW1lbnQgbGl0ZXJhbCB1bmlvbiBkaXJlY3RseSAoYXNzZW1ibGluZ1xuXHRcdFx0Ly8gYHVuaW9uW0tdYCB0ZXh0IHdvdWxkIG1pc3JlYWQgcHJlY2VkZW5jZSwgYW5kIHdoZW4gdGhlIGNvbnN0XG5cdFx0XHQvLyBpcyBub3Qgc3RhdGljYWxseSB2aXNpYmxlIHRoZSBob25lc3QgYW5zd2VyIGlzIGB1bmtub3duYCxcblx0XHRcdC8vIG5ldmVyIGEgYmFyZSBgdHlwZW9mIG5hbWVgIHF1ZXJ5KVxuXHRcdFx0aWYgKHRzLmlzVHlwZVF1ZXJ5Tm9kZShvYmplY3ROb2RlKSAmJiB0cy5pc0lkZW50aWZpZXIob2JqZWN0Tm9kZS5leHByTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcXVlcnlOYW1lID0gb2JqZWN0Tm9kZS5leHByTmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBhcnJheUxpdGVyYWwgPSB0aGlzLmZpbmRSZWZlcmVuY2VkQ29uc3RBcnJheShxdWVyeU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRcdGNvbnN0IGxpdGVyYWxzID0gYXJyYXlMaXRlcmFsID8gdGhpcy5saXRlcmFsVHlwZXNPZkFycmF5KGFycmF5TGl0ZXJhbCkgOiB1bmRlZmluZWQ7XG5cdFx0XHRcdGlmICghbGl0ZXJhbHMpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmICh0cy5pc0xpdGVyYWxUeXBlTm9kZShpbmRleGVkLmluZGV4VHlwZSkgJiYgdHMuaXNOdW1lcmljTGl0ZXJhbChpbmRleGVkLmluZGV4VHlwZS5saXRlcmFsKSkge1xuXHRcdFx0XHRcdGNvbnN0IGVsZW1lbnRJbmRleCA9IHBhcnNlSW50KGluZGV4ZWQuaW5kZXhUeXBlLmxpdGVyYWwudGV4dCwgMTApO1xuXHRcdFx0XHRcdGNvbnN0IGVsZW1lbnQgPSBsaXRlcmFsc1sgZWxlbWVudEluZGV4IF07XG5cdFx0XHRcdFx0Y29uc3QgZWxlbWVudFJlc3VsdCA9IGVsZW1lbnQgPT09IHVuZGVmaW5lZCA/ICd1bmtub3duJyA6IGVsZW1lbnQ7XG5cdFx0XHRcdFx0cmV0dXJuIGVsZW1lbnRSZXN1bHQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgdW5pb25SZXN1bHQgPSBsaXRlcmFscy5qb2luKCcgfCAnKTtcblx0XHRcdFx0cmV0dXJuIHVuaW9uUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0bGV0IG9iamVjdFR5cGUgPSB0aGlzLmluZmVyVHlwZShvYmplY3ROb2RlKTtcblx0XHRcdGNvbnN0IGluZGV4VHlwZSA9IHRoaXMuaW5mZXJUeXBlKGluZGV4ZWQuaW5kZXhUeXBlKTtcblx0XHRcdC8vIElmIG9iamVjdFR5cGUgaXMgJ29iamVjdCcsIHRyeSB0byByZXNvbHZlIHRoZSB1bmRlcmx5aW5nIHJlZmVyZW5jZWQgdHlwZVxuXHRcdFx0aWYgKG9iamVjdFR5cGUgPT09ICdvYmplY3QnICYmIHRzLmlzVHlwZVJlZmVyZW5jZU5vZGUob2JqZWN0Tm9kZSkpIHtcblx0XHRcdFx0Y29uc3QgcmVmTmFtZSA9IHRzLmlzSWRlbnRpZmllcihvYmplY3ROb2RlLnR5cGVOYW1lKSA/IG9iamVjdE5vZGUudHlwZU5hbWUudGV4dCA6ICcnO1xuXHRcdFx0XHRpZiAocmVmTmFtZSkge1xuXHRcdFx0XHRcdGNvbnN0IGRlY2wgPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKHJlZk5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRcdFx0aWYgKGRlY2wpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGV4cGFuZGVkID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKGRlY2wpO1xuXHRcdFx0XHRcdFx0aWYgKGV4cGFuZGVkKSB7XG5cdFx0XHRcdFx0XHRcdG9iamVjdFR5cGUgPSBleHBhbmRlZDtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIEludmFyaWFudDogYW4gaW5kZXggc3VmZml4IG11c3QgTkVWRVIgYmUgZ2x1ZWQgb250byBhblxuXHRcdFx0Ly8gdW5yZXNvbHZlZC9mYWxsYmFjayB0YXJnZXQg4oCUIGB1bmtub3duW251bWJlcl1gIC8gYG9iamVjdFtLXWBcblx0XHRcdC8vIGFyZSBpbnZhbGlkIFR5cGVTY3JpcHQgaW4gdGhlIGdlbmVyYXRlZCBmaWxlIChoYXJkIGNvbXBpbGVcblx0XHRcdC8vIGJyZWFrLCBGMTcpLiBXaGVuIGVpdGhlciBzaWRlIGRpZCBub3QgcmVzb2x2ZSwgdGhlIFdIT0xFXG5cdFx0XHQvLyBpbmRleGVkIGFjY2VzcyBkZWdyYWRlcyB0byBgdW5rbm93bmAuXG5cdFx0XHRjb25zdCB0YXJnZXRVbnJlc29sdmVkID0gb2JqZWN0VHlwZSA9PT0gJ3Vua25vd24nIHx8IG9iamVjdFR5cGUgPT09ICdvYmplY3QnO1xuXHRcdFx0Y29uc3QgaW5kZXhVbnJlc29sdmVkID0gaW5kZXhUeXBlID09PSAndW5rbm93bic7XG5cdFx0XHRpZiAodGFyZ2V0VW5yZXNvbHZlZCB8fCBpbmRleFVucmVzb2x2ZWQpIHtcblx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdH1cblx0XHRcdHJldHVybiBgJHtvYmplY3RUeXBlfVske2luZGV4VHlwZX1dYDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR5cGVPcGVyYXRvcjoge1xuXHRcdFx0Ly8gSGFuZGxlIGtleW9mLCByZWFkb25seSwgdW5pcXVlIG9wZXJhdG9yc1xuXHRcdFx0Y29uc3QgdHlwZU9wID0gdHlwZU5vZGUgYXMgdHMuVHlwZU9wZXJhdG9yTm9kZTtcblx0XHRcdGNvbnN0IG9wZXJhdG9yID0gdHMuU3ludGF4S2luZFsgdHlwZU9wLm9wZXJhdG9yIF07XG5cdFx0XHRyZXR1cm4gYCR7b3BlcmF0b3J9ICR7dGhpcy5pbmZlclR5cGUodHlwZU9wLnR5cGUpfWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlUXVlcnk6IHtcblx0XHRcdC8vIGB0eXBlb2YgeGAgYXMgYSBGSUVMRCBUWVBFOiB0aGUgZ2VuZXJhdGVkIGZpbGUgaGFzIG5vIGltcG9ydHMsXG5cdFx0XHQvLyBzbyBhIGJhcmUgYHR5cGVvZiB4YCB3b3VsZCBiZSBhbiB1bnJlc29sdmFibGUgbmFtZSBkb3duc3RyZWFtLlxuXHRcdFx0Ly8gV2hlbiB4IGlzIGEgdHJhY2tlZCBjb25zdCBhcnJheSwgZW1pdCBpdHMgZWxlbWVudCBsaXRlcmFsXG5cdFx0XHQvLyB1bmlvbjsgb3RoZXJ3aXNlIGRlZ3JhZGUgdG8gYHVua25vd25gLiAoSW5zdGFuY2VUeXBlPHR5cGVvZiBYPlxuXHRcdFx0Ly8gZ3JhcGggdHlwZXMgYXJlIGhhbmRsZWQgaW4gcmVzb2x2ZVNpbXBsZVR5cGVSZWZlcmVuY2UgYmVmb3JlXG5cdFx0XHQvLyBpbmZlclR5cGUgcnVucy4pXG5cdFx0XHRjb25zdCB0eXBlUXVlcnkgPSB0eXBlTm9kZSBhcyB0cy5UeXBlUXVlcnlOb2RlO1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcih0eXBlUXVlcnkuZXhwck5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHVuaW9uID0gdGhpcy50eXBlT2ZDb25zdEFycmF5VW5pb24odHlwZVF1ZXJ5LmV4cHJOYW1lLnRleHQsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRcdGlmICh1bmlvbikge1xuXHRcdFx0XHRcdHJldHVybiB1bmlvbjtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0ZGVmYXVsdDpcblx0XHRcdC8vIEZvciBjb21wbGV4IHR5cGVzLCByZXR1cm4gdGhlIHRleHQgcmVwcmVzZW50YXRpb25cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdFx0KiBJbmZlciByZXR1cm4gdHlwZSBmcm9tIGEgbWV0aG9kIGRlY2xhcmF0aW9uXG5cdFx0KiBVc2VzIGV4cGxpY2l0IHJldHVybiB0eXBlIGFubm90YXRpb24gb3IgaW5mZXJzIGZyb20gcmV0dXJuIHN0YXRlbWVudHNcblx0XHQqL1xuXHRwcml2YXRlIGluZmVyUmV0dXJuVHlwZSAobWV0aG9kOiB0cy5NZXRob2REZWNsYXJhdGlvbiwgY2xhc3NQcm9wZXJ0eVR5cGVzPzogTWFwPHN0cmluZywgc3RyaW5nPik6IHN0cmluZyB7XG5cdFx0Ly8gSWYgbWV0aG9kIGhhcyBleHBsaWNpdCByZXR1cm4gdHlwZSBhbm5vdGF0aW9uLCB1c2UgaXRcblx0XHRpZiAobWV0aG9kLnR5cGUpIHtcblx0XHRcdHJldHVybiB0aGlzLmluZmVyVHlwZShtZXRob2QudHlwZSk7XG5cdFx0fVxuXG5cdFx0Ly8gT3RoZXJ3aXNlLCB0cnkgdG8gaW5mZXIgZnJvbSByZXR1cm4gc3RhdGVtZW50cyBpbiB0aGUgbWV0aG9kIGJvZHlcblx0XHRpZiAobWV0aG9kLmJvZHkpIHtcblx0XHRcdHJldHVybiB0aGlzLmluZmVyUmV0dXJuVHlwZUZyb21Cb2R5KG1ldGhvZC5ib2R5LCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdH1cblxuXHRcdHJldHVybiAndW5rbm93bic7XG5cdH1cblxuXHQvKipcblx0XHQqIEluZmVyIHJldHVybiB0eXBlIGJ5IGFuYWx5emluZyByZXR1cm4gc3RhdGVtZW50cyBpbiB0aGUgbWV0aG9kIGJvZHlcblx0XHQqL1xuXHRwcml2YXRlIGluZmVyUmV0dXJuVHlwZUZyb21Cb2R5IChib2R5OiB0cy5CbG9jaywgY2xhc3NQcm9wZXJ0eVR5cGVzPzogTWFwPHN0cmluZywgc3RyaW5nPik6IHN0cmluZyB7XG5cdFx0Y29uc3QgcmV0dXJuVHlwZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblxuXHRcdGNvbnN0IHZpc2l0ID0gKG5vZGU6IHRzLk5vZGUpOiB2b2lkID0+IHtcblx0XHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKG5vZGUuZXhwcmVzc2lvbiwgdW5kZWZpbmVkLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0XHRpZiAodHlwZSAhPT0gJ3Vua25vd24nKSB7XG5cdFx0XHRcdFx0cmV0dXJuVHlwZXMuYWRkKHR5cGUpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgdmlzaXQpO1xuXHRcdH07XG5cblx0XHR2aXNpdChib2R5KTtcblxuXHRcdGlmIChyZXR1cm5UeXBlcy5zaXplID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gJ3ZvaWQnO1xuXHRcdH1cblx0XHRpZiAocmV0dXJuVHlwZXMuc2l6ZSA9PT0gMSkge1xuXHRcdFx0cmV0dXJuIEFycmF5LmZyb20ocmV0dXJuVHlwZXMpWyAwIF07XG5cdFx0fVxuXHRcdHJldHVybiBBcnJheS5mcm9tKHJldHVyblR5cGVzKS5qb2luKCcgfCAnKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBJbmZlciB0eXBlIGZyb20gaW5pdGlhbGl6ZXJcblx0ICovXG5cdHByaXZhdGUgaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyIChcblx0XHRpbml0aWFsaXplcjogdHMuRXhwcmVzc2lvbixcblx0XHRkYXRhVHlwZU1hcD86IE1hcDxzdHJpbmcsIHN0cmluZz4sXG5cdFx0Y2xhc3NQcm9wZXJ0eVR5cGVzPzogTWFwPHN0cmluZywgc3RyaW5nPlxuXHQpOiBzdHJpbmcge1xuXHRcdHN3aXRjaCAoaW5pdGlhbGl6ZXIua2luZCkge1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5TdHJpbmdMaXRlcmFsOlxuXHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdW1lcmljTGl0ZXJhbDpcblx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHJ1ZUtleXdvcmQ6XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZDpcblx0XHRcdHJldHVybiAnYm9vbGVhbic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bGxLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdudWxsJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5kZWZpbmVkS2V5d29yZDpcblx0XHRcdHJldHVybiAndW5kZWZpbmVkJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbjpcblx0XHRcdHJldHVybiAnQXJyYXk8dW5rbm93bj4nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5PYmplY3RMaXRlcmFsRXhwcmVzc2lvbjpcblx0XHRcdHJldHVybiAnb2JqZWN0Jztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTmV3RXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gSGFuZGxlIG5ldyBEYXRlKCksIG5ldyBNYXAoKSwgZXRjLlxuXHRcdFx0Y29uc3QgbmV3RXhwciA9IGluaXRpYWxpemVyIGFzIHRzLk5ld0V4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG5ld0V4cHIuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y29uc3QgY29uc3RydWN0ZWROYW1lID0gbmV3RXhwci5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRcdC8vIEV4cGxpY2l0IHR5cGUgYXJndW1lbnRzIHN1cnZpdmU6IG5ldyBNYXA8c3RyaW5nLCBvYmplY3Q+KClcblx0XHRcdFx0Ly8gZW1pdHMgTWFwPHN0cmluZywgb2JqZWN0PiDigJQgZHJvcHBpbmcgdGhlbSBwcm9kdWNlZCBhIGJhcmVcblx0XHRcdFx0Ly8gZ2VuZXJpYywgd2hpY2ggaXMgaW52YWxpZCBUUyBpbiB0aGUgZ2VuZXJhdGVkIGZpbGUgKFRTMjMxNClcblx0XHRcdFx0aWYgKG5ld0V4cHIudHlwZUFyZ3VtZW50cyAmJiBuZXdFeHByLnR5cGVBcmd1bWVudHMubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRcdGNvbnN0IGFyZ1R5cGVzID0gbmV3RXhwci50eXBlQXJndW1lbnRzLm1hcChhcmcgPT4gdGhpcy5pbmZlclR5cGUoYXJnKSk7XG5cdFx0XHRcdFx0cmV0dXJuIGAke2NvbnN0cnVjdGVkTmFtZX08JHthcmdUeXBlcy5qb2luKCcsICcpfT5gO1xuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIE5vIHR5cGUgYXJndW1lbnRzOiBhIGtub3duIGdlbmVyaWMgZ2xvYmFsIHN0aWxsIG5lZWRzIGl0c1xuXHRcdFx0XHQvLyBwYXJhbWV0ZXIgbGlzdCDigJQgZmlsbCBpdCB3aXRoIHVua25vd24gKE1hcDx1bmtub3duLCB1bmtub3duPilcblx0XHRcdFx0Y29uc3QgZGVmYXVsdGVkR2VuZXJpYyA9IEdFTkVSSUNfR0xPQkFMX0RFRkFVTFRfQVJHUy5nZXQoY29uc3RydWN0ZWROYW1lKTtcblx0XHRcdFx0aWYgKGRlZmF1bHRlZEdlbmVyaWMpIHtcblx0XHRcdFx0XHRyZXR1cm4gZGVmYXVsdGVkR2VuZXJpYztcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gY29uc3RydWN0ZWROYW1lO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICdvYmplY3QnO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQmluYXJ5RXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gSGFuZGxlIGFyaXRobWV0aWMgb3BlcmF0aW9uczogYSAqIGIsIGEgKyBiLCBhIC0gYiwgYSAvIGJcblx0XHRcdGNvbnN0IGJpbmFyeUV4cHIgPSBpbml0aWFsaXplciBhcyB0cy5CaW5hcnlFeHByZXNzaW9uO1xuXHRcdFx0Y29uc3QgbGVmdFR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihiaW5hcnlFeHByLmxlZnQsIGRhdGFUeXBlTWFwLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0Y29uc3QgcmlnaHRUeXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIoYmluYXJ5RXhwci5yaWdodCwgZGF0YVR5cGVNYXAsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdFxuXHRcdFx0Ly8gQ2hlY2sgaWYgaXQncyBhbiBhcml0aG1ldGljIG9wZXJhdG9yXG5cdFx0XHRjb25zdCBvcGVyYXRvciA9IGJpbmFyeUV4cHIub3BlcmF0b3JUb2tlbi5raW5kO1xuXHRcdFx0aWYgKG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLkFzdGVyaXNrVG9rZW4gfHxcblx0XHRcdFx0ICAgIG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLlNsYXNoVG9rZW4gfHxcblx0XHRcdFx0ICAgIG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLk1pbnVzVG9rZW4gfHxcblx0XHRcdFx0ICAgIG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLlBlcmNlbnRUb2tlbikge1xuXHRcdFx0XHQvLyBBcml0aG1ldGljIG9wZXJhdGlvbnMgb24gbnVtYmVycyBwcm9kdWNlIG51bWJlcnNcblx0XHRcdFx0aWYgKChsZWZ0VHlwZSA9PT0gJ251bWJlcicgfHwgbGVmdFR5cGUgPT09ICd1bmtub3duJykgJiZcblx0XHRcdFx0XHQgICAgKHJpZ2h0VHlwZSA9PT0gJ251bWJlcicgfHwgcmlnaHRUeXBlID09PSAndW5rbm93bicpKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAob3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuUGx1c1Rva2VuKSB7XG5cdFx0XHRcdC8vIFBsdXMgY2FuIGJlIGFkZGl0aW9uIG9yIHN0cmluZyBjb25jYXRlbmF0aW9uXG5cdFx0XHRcdGlmIChsZWZ0VHlwZSA9PT0gJ3N0cmluZycgfHwgcmlnaHRUeXBlID09PSAnc3RyaW5nJykge1xuXHRcdFx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAobGVmdFR5cGUgPT09ICdudW1iZXInICYmIHJpZ2h0VHlwZSA9PT0gJ251bWJlcicpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb246IHtcblx0XHRcdC8vIEhhbmRsZSBwcm9wZXJ0eSBhY2Nlc3MgbGlrZSBkYXRhLnZhbHVlLCBkYXRhLmlkXG5cdFx0XHRpZiAoZGF0YVR5cGVNYXApIHtcblx0XHRcdFx0Y29uc3QgYWNjZXNzQ2hhaW4gPSB0aGlzLmdldFByb3BlcnR5QWNjZXNzQ2hhaW4oaW5pdGlhbGl6ZXIpO1xuXHRcdFx0XHRpZiAoYWNjZXNzQ2hhaW4pIHtcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gZGF0YVR5cGVNYXAuZ2V0KGFjY2Vzc0NoYWluKTtcblx0XHRcdFx0XHRpZiAodHlwZSkge1xuXHRcdFx0XHRcdFx0cmV0dXJuIHR5cGU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBIYW5kbGUgdGhpcy5tYXAuc2l6ZSBwYXR0ZXJuIChNYXAuc2l6ZSByZXR1cm5zIG51bWJlcilcblx0XHRcdGNvbnN0IHByb3BBY2Nlc3MgPSBpbml0aWFsaXplciBhcyB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ocHJvcEFjY2Vzcy5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBvdXRlclByb3AgPSBwcm9wQWNjZXNzLmV4cHJlc3Npb247XG5cdFx0XHRcdC8vIENoZWNrIGZvciB0aGlzLm1hcCBwYXR0ZXJuXG5cdFx0XHRcdGxldCBpbm5lck5hbWUgPSAnJztcblx0XHRcdFx0aWYgKG91dGVyUHJvcC5leHByZXNzaW9uLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdFx0XHRpbm5lck5hbWUgPSAndGhpcyc7XG5cdFx0XHRcdH0gZWxzZSBpZiAodHMuaXNJZGVudGlmaWVyKG91dGVyUHJvcC5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdGlubmVyTmFtZSA9IG91dGVyUHJvcC5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgbWFwUHJvcCA9IG91dGVyUHJvcC5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IGZpbmFsUHJvcCA9IHByb3BBY2Nlc3MubmFtZS50ZXh0O1xuXHRcdFx0XHQvLyB0aGlzLm1hcC5zaXplIC0+IG51bWJlclxuXHRcdFx0XHRpZiAoaW5uZXJOYW1lID09PSAndGhpcycgJiYgbWFwUHJvcCA9PT0gJ21hcCcgJiYgZmluYWxQcm9wID09PSAnc2l6ZScpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5JZGVudGlmaWVyOiB7XG5cdFx0XHQvLyBIYW5kbGUgaWRlbnRpZmllciByZWZlcmVuY2VzIGlmIGluIGRhdGFUeXBlTWFwXG5cdFx0XHRpZiAoZGF0YVR5cGVNYXApIHtcblx0XHRcdFx0Y29uc3QgbmFtZSA9IChpbml0aWFsaXplciBhcyB0cy5JZGVudGlmaWVyKS50ZXh0O1xuXHRcdFx0XHRjb25zdCB0eXBlID0gZGF0YVR5cGVNYXAuZ2V0KG5hbWUpO1xuXHRcdFx0XHRpZiAodHlwZSkge1xuXHRcdFx0XHRcdHJldHVybiB0eXBlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuRWxlbWVudEFjY2Vzc0V4cHJlc3Npb246IHtcblx0XHRcdC8vIEYyMjogdmFsdWUtbGV2ZWwgZWxlbWVudCBhY2Nlc3Mgb3ZlciBhIGNvbnN0LWFzc2VydGVkXG5cdFx0XHQvLyBsaXRlcmFsIGFycmF5IOKAlCBgKDxjb25zdD5b4oCmXSlbMF1gLCBgKFvigKZdIGFzIGNvbnN0KVsxXWAsIG9yXG5cdFx0XHQvLyBhIHRyYWNrZWQgbW9kdWxlIGNvbnN0IChgY29uc3QgeCA9IDxjb25zdD5b4oCmXWA7IGB4WzBdYCkg4oCUXG5cdFx0XHQvLyBpbmZlcnMgdGhlIGVsZW1lbnQncyBsaXRlcmFsIHR5cGUsIHRoZSB2YWx1ZS1sZXZlbCB0d2luIG9mXG5cdFx0XHQvLyB0aGUgdHlwZW9mLXBhdGggdW5pb24uIE5vbi1udW1lcmljIGluZGV4ZXMsIG5vbi1saXRlcmFsXG5cdFx0XHQvLyBlbGVtZW50cywgYW5kIGdlbmVyYWwgYXNzZXJ0aW9ucyBzdGF5IGB1bmtub3duYC5cblx0XHRcdGNvbnN0IGVsZW1lbnRBY2Nlc3MgPSBpbml0aWFsaXplciBhcyB0cy5FbGVtZW50QWNjZXNzRXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IGFyZ3VtZW50ID0gZWxlbWVudEFjY2Vzcy5hcmd1bWVudEV4cHJlc3Npb247XG5cdFx0XHRpZiAoIWFyZ3VtZW50IHx8ICF0cy5pc051bWVyaWNMaXRlcmFsKGFyZ3VtZW50KSkge1xuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgYXJyYXlMaXRlcmFsID0gdGhpcy5jb25zdEFycmF5TGl0ZXJhbE9mKGVsZW1lbnRBY2Nlc3MuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoIWFycmF5TGl0ZXJhbCkge1xuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZWxlbWVudCA9IGFycmF5TGl0ZXJhbC5lbGVtZW50c1sgcGFyc2VJbnQoYXJndW1lbnQudGV4dCwgMTApIF07XG5cdFx0XHRpZiAoIWVsZW1lbnQgfHwgdHMuaXNTcHJlYWRFbGVtZW50KGVsZW1lbnQpKSB7XG5cdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBsaXRlcmFsID0gdGhpcy5saXRlcmFsVHlwZU9mRXhwcmVzc2lvbihlbGVtZW50KTtcblx0XHRcdGNvbnN0IGVsZW1lbnRSZXN1bHQgPSBsaXRlcmFsID8/ICd1bmtub3duJztcblx0XHRcdHJldHVybiBlbGVtZW50UmVzdWx0O1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQ2FsbEV4cHJlc3Npb246IHtcblx0XHRcdC8vIEhhbmRsZSBmdW5jdGlvbiBjYWxscyBsaWtlIERhdGUubm93KCksIHBhcnNlSW50KCksIGV0Yy5cblx0XHRcdGNvbnN0IGNhbGxFeHByID0gaW5pdGlhbGl6ZXIgYXMgdHMuQ2FsbEV4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbEV4cHIuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y29uc3QgbWV0aG9kTmFtZSA9IGNhbGxFeHByLmV4cHJlc3Npb24ubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBvYmpOYW1lID0gdHMuaXNJZGVudGlmaWVyKGNhbGxFeHByLmV4cHJlc3Npb24uZXhwcmVzc2lvbilcblx0XHRcdFx0XHQ/IGNhbGxFeHByLmV4cHJlc3Npb24uZXhwcmVzc2lvbi50ZXh0XG5cdFx0XHRcdFx0OiAnJztcblx0XHRcdFx0XHRcblx0XHRcdFx0Ly8gRGF0ZS5ub3coKSAtPiBudW1iZXJcblx0XHRcdFx0aWYgKG9iak5hbWUgPT09ICdEYXRlJyAmJiBtZXRob2ROYW1lID09PSAnbm93Jykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBTdHJpbmcgbWV0aG9kcyB0aGF0IHJldHVybiBzdHJpbmdcblx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICd0b1N0cmluZycgfHwgbWV0aG9kTmFtZSA9PT0gJ3ZhbHVlT2YnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIEhhbmRsZSBNYXAgcHJvcGVydHkgYWNjZXNzIG9uIGNsYXNzIGluc3RhbmNlcyAodGhpcy5tYXAuKilcblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxFeHByLmV4cHJlc3Npb24uZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRjb25zdCBvdXRlclByb3AgPSBjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRcdFx0Ly8gSGFuZGxlIGJvdGggJ3RoaXMnIGtleXdvcmQgYW5kIGlkZW50aWZpZXIgcGF0dGVybnNcblx0XHRcdFx0XHRsZXQgaW5uZXJOYW1lID0gJyc7XG5cdFx0XHRcdFx0aWYgKG91dGVyUHJvcC5leHByZXNzaW9uLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdFx0XHRcdGlubmVyTmFtZSA9ICd0aGlzJztcblx0XHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihvdXRlclByb3AuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRcdGlubmVyTmFtZSA9IG91dGVyUHJvcC5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdGNvbnN0IG1hcFByb3AgPSBvdXRlclByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRcdC8vIHRoaXMubWFwLlgoKSBwYXR0ZXJuc1xuXHRcdFx0XHRcdGlmIChpbm5lck5hbWUgPT09ICd0aGlzJyAmJiBtYXBQcm9wID09PSAnbWFwJykge1xuXHRcdFx0XHRcdFx0Ly8gVHJ5IHRvIGdldCB0aGUgTWFwJ3MgdmFsdWUgdHlwZSBmcm9tIGNsYXNzIHByb3BlcnRpZXNcblx0XHRcdFx0XHRcdGxldCBtYXBWYWx1ZVR5cGUgPSAndW5rbm93bic7XG5cdFx0XHRcdFx0XHRpZiAoY2xhc3NQcm9wZXJ0eVR5cGVzKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnN0IG1hcFR5cGUgPSBjbGFzc1Byb3BlcnR5VHlwZXMuZ2V0KCdtYXAnKTtcblx0XHRcdFx0XHRcdFx0aWYgKG1hcFR5cGUgJiYgbWFwVHlwZS5zdGFydHNXaXRoKCdNYXA8JykpIHtcblx0XHRcdFx0XHRcdFx0XHQvLyBQYXJzZSBNYXA8SywgVj4gdG8gZ2V0IFZcblx0XHRcdFx0XHRcdFx0XHRjb25zdCBtYXRjaCA9IG1hcFR5cGUubWF0Y2goL01hcDxbXixdKyxcXHMqKC4rKT4kLyk7XG5cdFx0XHRcdFx0XHRcdFx0aWYgKG1hdGNoKSB7XG5cdFx0XHRcdFx0XHRcdFx0XHRbICwgbWFwVmFsdWVUeXBlIF0gPSBtYXRjaDtcblx0XHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnaGFzJykgcmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnc2V0JykgcmV0dXJuICd0aGlzJztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZ2V0JykgcmV0dXJuIG1hcFZhbHVlVHlwZTtcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZGVsZXRlJykgcmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnY2xlYXInKSByZXR1cm4gJ3ZvaWQnO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICd2YWx1ZXMnKSByZXR1cm4gYEl0ZXJhYmxlSXRlcmF0b3I8JHttYXBWYWx1ZVR5cGV9PmA7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2tleXMnKSByZXR1cm4gJ0l0ZXJhYmxlSXRlcmF0b3I8c3RyaW5nPic7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2VudHJpZXMnKSByZXR1cm4gYEl0ZXJhYmxlSXRlcmF0b3I8W3N0cmluZywgJHttYXBWYWx1ZVR5cGV9XT5gO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBEaXJlY3QgbWFwLlgoKSBjYWxsc1xuXHRcdFx0XHRpZiAob2JqTmFtZSA9PT0gJ21hcCcgfHwgb2JqTmFtZSA9PT0gJ29iaicpIHtcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2hhcycpIHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdzZXQnKSByZXR1cm4gJ3RoaXMnO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZ2V0JykgcmV0dXJuICd1bmtub3duJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2RlbGV0ZScpIHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdjbGVhcicpIHJldHVybiAndm9pZCc7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICd2YWx1ZXMnKSByZXR1cm4gJ0l0ZXJhYmxlSXRlcmF0b3I8dW5rbm93bj4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAna2V5cycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjxzdHJpbmc+Jztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2VudHJpZXMnKSByZXR1cm4gJ0l0ZXJhYmxlSXRlcmF0b3I8W3N0cmluZywgdW5rbm93bl0+Jztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gcGFyc2VJbnQsIHBhcnNlRmxvYXQgLT4gbnVtYmVyXG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGNhbGxFeHByLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IGZuTmFtZSA9IGNhbGxFeHByLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ3BhcnNlSW50JyB8fCBmbk5hbWUgPT09ICdwYXJzZUZsb2F0Jykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoZm5OYW1lID09PSAnU3RyaW5nJykge1xuXHRcdFx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoZm5OYW1lID09PSAnTnVtYmVyJykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoZm5OYW1lID09PSAnQm9vbGVhbicpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVGVtcGxhdGVFeHByZXNzaW9uOlxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Ob1N1YnN0aXR1dGlvblRlbXBsYXRlTGl0ZXJhbDoge1xuXHRcdFx0Ly8gVGVtcGxhdGUgbGl0ZXJhbHMgbGlrZSBgJHtiYXNlVmFsdWV9LSR7ZXh0cmF9YCBhbHdheXMgcHJvZHVjZSBzdHJpbmdzXG5cdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0fVxuXHRcdGRlZmF1bHQ6XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIENvbGxlY3QgdXNhZ2UgaW5mb3JtYXRpb24gZm9yIHR5cGUgcmVmZXJlbmNlc1xuXHRcdFx0Ki9cblx0cHJpdmF0ZSBjb2xsZWN0VXNhZ2UgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHQvLyBDaGVjayBmb3IgbmV3IFR5cGUoKSBpbnN0YW50aWF0aW9uXG5cdFx0aWYgKHRzLmlzTmV3RXhwcmVzc2lvbihub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdC8vIGBuZXcgcmVjZWl2ZXIuU3ViKClgIG1heSBjb25zdHJ1Y3Qgc2V2ZXJhbCB0eXBlcyAoYSByZWNlaXZlclxuXHRcdFx0Ly8gdHlwZWQgYXMgYSB1bmlvbiwgb3Igb25lIHRhY3RpY2EgY2Fubm90IGJpbmQpOiBlYWNoIGdldHMgdGhlXG5cdFx0XHQvLyByZWNvcmQ7IHRoZSByZXN1bHQgdmFyaWFibGUgYmluZHMgb25seSB0byBhIHNpbmdsZSBhbnN3ZXJcblx0XHRcdGxldCB0eXBlTmFtZXM6IHN0cmluZ1tdID0gW107XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obm9kZS5leHByZXNzaW9uKSkge1xuXHRcdFx0XHR0eXBlTmFtZXMgPSB0aGlzLnJlc29sdmVVc2FnZVR5cGVQYXRocyhub2RlLmV4cHJlc3Npb24pLnBhdGhzO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgdHlwZU5hbWUgPSB0aGlzLmdldFR5cGVOYW1lRnJvbUV4cHJlc3Npb24obm9kZS5leHByZXNzaW9uKTtcblx0XHRcdFx0dHlwZU5hbWVzID0gdHlwZU5hbWUgPyBbIHR5cGVOYW1lIF0gOiBbXTtcblx0XHRcdH1cblx0XHRcdGlmICh0eXBlTmFtZXMubGVuZ3RoID09PSAxKSB7XG5cdFx0XHRcdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnQgZnJvbSBuZXcgVHlwZSgpIGZvciBmbG93IGFuYWx5c2lzXG5cdFx0XHRcdHRoaXMudHJhY2tOZXdBc3NpZ25tZW50KG5vZGUsIHR5cGVOYW1lc1sgMCBdKTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3QgdHlwZU5hbWUgb2YgdHlwZU5hbWVzKSB7XG5cdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0dGhpcy5hZGRVc2FnZSh0eXBlTmFtZSwge1xuXHRcdFx0XHRcdGxvY2F0aW9uICAgICAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdGtpbmQgICAgICAgICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRjb2RlICAgICAgICAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHQvLyBDb25zdHJ1Y3RvciBleHByZXNzaW9uIHRleHQgKCdUaGluZycsICd1c2VyLkFkbWluRW50aXR5Jyxcblx0XHRcdFx0XHQvLyBhIGxvb2t1cCBhbGlhcykg4oCUIENyZWF0aW9uQW5jaG9yLmNvbnN0cnVjdG9yVGV4dCAoUGhhc2UgMylcblx0XHRcdFx0XHRjb25zdHJ1Y3RvclRleHQgOiBub2RlLmV4cHJlc3Npb24uZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHR9KTtcblx0XHRcdFx0Ly8gQWxzbyByZWNvcmQgYXMgZmxvdyBldmVudFxuXHRcdFx0XHR0aGlzLmFkZEZsb3codHlwZU5hbWUsIHtcblx0XHRcdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdGtpbmQgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0XHRcdGNvZGUgICAgIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0Y29udGV4dCAgOiAnbmV3IGV4cHJlc3Npb24nLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cdFxuXHRcdC8vIENoZWNrIGZvciBwcm9wZXJ0eSBhY2Nlc3Mgb24gaW5zdGFuY2VzICh1c2VyLkFkbWluVHlwZSlcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdGNvbnN0IHByb3BOYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0XHQvLyBpbnN0YW5jZS5jbG9uZSDigJQgdGhlIFBST1BFUlRZIGZvcm0gKGNvcmUgdHlwZXMgaXRcblx0XHRcdC8vIGByZWFkb25seSBjbG9uZTogdGhpc2ApOiB0aGUgcmVzdWx0IHZhcmlhYmxlIGJpbmRzIHRvIHRoZVxuXHRcdFx0Ly8gc291cmNlIGluc3RhbmNlJ3MgdHlwZSwgc2FtZSBhcyB0aGUgZm9yaygpL2Nsb25lKCkgY2FsbFxuXHRcdFx0Ly8gZm9ybXMgKGF3YWl0LXRyYW5zcGFyZW50KS4gVGhlIGNhbGwgZm9ybSdzIHJlY29yZGluZyBoYXBwZW5zXG5cdFx0XHQvLyBpbiB0aGUgQ2FsbEV4cHJlc3Npb24gYnJhbmNoOyB0aGUgcHJvcGVydHkgYnJhbmNoIHNraXBzIGl0XG5cdFx0XHQvLyB0byBhdm9pZCBhIGR1cGxpY2F0ZSBlbnRyeSBhdCB0aGUgc2FtZSBzaXRlXG5cdFx0XHRpZiAocHJvcE5hbWUgPT09ICdjbG9uZScgJiYgdHMuaXNJZGVudGlmaWVyKG5vZGUuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y29uc3QgY2xvbmVkUGF0aCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KG5vZGUuZXhwcmVzc2lvbi50ZXh0KTtcblx0XHRcdFx0Y29uc3QgaXNDYWxsRm9ybSA9IHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZS5wYXJlbnQpICYmIG5vZGUucGFyZW50LmV4cHJlc3Npb24gPT09IG5vZGU7XG5cdFx0XHRcdGlmIChjbG9uZWRQYXRoKSB7XG5cdFx0XHRcdFx0aWYgKCFpc0NhbGxGb3JtKSB7XG5cdFx0XHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0XHRcdCk7XG5cdFx0XHRcdFx0XHR0aGlzLmFkZFVzYWdlKGNsb25lZFBhdGgsIHtcblx0XHRcdFx0XHRcdFx0bG9jYXRpb24gICAgICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0XHRcdGtpbmQgICAgICAgICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRcdFx0Y29kZSAgICAgICAgICAgIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0XHRcdGNvbnN0cnVjdG9yVGV4dCA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdHRoaXMuYmluZFJlc3VsdFZhcmlhYmxlKG5vZGUsIGNsb25lZFBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBDaGVjayBpZiB0aGlzIGxvb2tzIGxpa2UgYSB0eXBlIGFjY2VzcyBwYXR0ZXJuXG5cdFx0XHRpZiAocHJvcE5hbWUgJiYgdGhpcy5pc0xpa2VseVR5cGVOYW1lKHByb3BOYW1lKSkge1xuXHRcdFx0XHQvLyBuZXcgeC5TdWIo4oCmKTogdGhlIE5ld0V4cHJlc3Npb24gYnJhbmNoIGFscmVhZHkgcmVjb3JkZWRcblx0XHRcdFx0Ly8gdGhlIHNpdGUgYXMgYW4gaW5zdGFudGlhdGlvbiwgc28gYSBwcm9wZXJ0eUFjY2VzcyByZWNvcmRcblx0XHRcdFx0Ly8gd291bGQgZHVwbGljYXRlIGl0IOKAlCBvbmUgcmVjb3JkIHBlciBzaXRlLCB0aGUgc2FtZSBsYXcgYXNcblx0XHRcdFx0Ly8gdGhlIGNsb25lIGd1YXJkIGFib3ZlLiAoQSB3aG9sZS1jYWxsZWUtcGFyZW50aGVzaXplZFxuXHRcdFx0XHQvLyBuZXcgKHguU3ViKSgpIG5ldmVyIG1hdGNoZXMgaGVyZTogdGhlIGFjY2VzcydzIHBhcmVudCBpc1xuXHRcdFx0XHQvLyB0aGUgUGFyZW50aGVzaXplZEV4cHJlc3Npb24sIGFuZCB0aGUgaW5zdGFudGlhdGlvbiBicmFuY2hcblx0XHRcdFx0Ly8gY2Fubm90IHJlc29sdmUgdGhhdCBjYWxsZWUg4oCUIHRoaXMgYWNjZXNzIHN0YXlzIHRoZSBzaXRlJ3Ncblx0XHRcdFx0Ly8gb25seSByZWNvcmQuKVxuXHRcdFx0XHRjb25zdCBpc05ld0NhbGxlZSA9IHRzLmlzTmV3RXhwcmVzc2lvbihub2RlLnBhcmVudCkgJiYgbm9kZS5wYXJlbnQuZXhwcmVzc2lvbiA9PT0gbm9kZTtcblx0XHRcdFx0Ly8geC5TdWIo4oCmKSBhcyBhIGNoYWluIHRpcCBvciBhIGJhcmUgc3VidHlwZSBjYWxsOiB0aGVcblx0XHRcdFx0Ly8gQ2FsbEV4cHJlc3Npb24gYnJhbmNoIHJlY29yZHMgdGhlIHNpdGUgYXMgYW5cblx0XHRcdFx0Ly8gaW5zdGFudGlhdGlvbiDigJQgdGhlIHNhbWUgb25lLXJlY29yZCBsYXdcblx0XHRcdFx0Y29uc3QgaXNDb25zdHJ1Y3Rpb25DYWxsZWUgPSB0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUucGFyZW50KSAmJlxuXHRcdFx0XHRcdG5vZGUucGFyZW50LmV4cHJlc3Npb24gPT09IG5vZGUgJiZcblx0XHRcdFx0XHQodGhpcy5yZXNvbHZlQ2hhaW5UaXBUeXBlUGF0aChub2RlLnBhcmVudCkgIT09IHVuZGVmaW5lZCB8fFxuXHRcdFx0XHRcdFx0dGhpcy5yZXNvbHZlQmFyZVN1YnR5cGVDYWxsKG5vZGUucGFyZW50KS5sZW5ndGggPiAwKTtcblx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHQpO1xuXHRcdFx0XHRjb25zdCBhY2Nlc3NlZCA9IGlzTmV3Q2FsbGVlIHx8IGlzQ29uc3RydWN0aW9uQ2FsbGVlXG5cdFx0XHRcdFx0PyBbXVxuXHRcdFx0XHRcdDogdGhpcy5yZXNvbHZlVXNhZ2VUeXBlUGF0aHMobm9kZSkucGF0aHM7XG5cdFx0XHRcdGZvciAoY29uc3QgZnVsbFBhdGggb2YgYWNjZXNzZWQpIHtcblx0XHRcdFx0XHR0aGlzLmFkZFVzYWdlKGZ1bGxQYXRoLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdFx0a2luZCAgICAgOiAncHJvcGVydHlBY2Nlc3MnLFxuXHRcdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0Ly8gQ2hlY2sgZm9yIGxvb2t1cCgnVHlwZU5hbWUnKSBvciBsb29rdXAoc291cmNlLCAnVHlwZU5hbWUnKSBjYWxsc1xuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0Y29uc3QgZnVuY05hbWUgPSB0aGlzLmdldEZ1bmN0aW9uTmFtZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdFx0aWYgKGZ1bmNOYW1lID09PSAnbG9va3VwJyAmJiBub2RlLmFyZ3VtZW50cy5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdGNvbnN0IHR5cGVQYXRoID0gdGhpcy5yZXNvbHZlTG9va3VwUGF0aChub2RlKTtcblx0XHRcdFx0aWYgKHR5cGVQYXRoKSB7XG5cdFx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0XHQpO1xuXHRcdFx0XHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRcdFx0dGhpcy5hZGRVc2FnZSh0eXBlUGF0aCwge1xuXHRcdFx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdFx0XHRraW5kIDogJ2xvb2t1cCcsXG5cdFx0XHRcdFx0XHRjb2RlIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudCBmcm9tIGxvb2t1cCBmb3IgaW5zdGFudGlhdGlvbiB0cmFja2luZ1xuXHRcdFx0XHRcdHRoaXMudHJhY2tMb29rdXBBc3NpZ25tZW50KG5vZGUsIHR5cGVQYXRoKTtcblx0XHRcdFx0XHQvLyBSZWNvcmQgZm9yIHRoZSBoYXJkLWZhaWwgbGF3IGV2ZW4gd2hlbiBhZGRVc2FnZSBkcm9wcGVkXG5cdFx0XHRcdFx0Ly8gdGhlIHBhdGggKHVua25vd24gcGF0aHMgYXJlIGV4YWN0bHkgdGhlIGZhaWx1cmUgY2xhc3MpXG5cdFx0XHRcdFx0dGhpcy5sb29rdXBSZWZlcmVuY2VzLnB1c2goeyBwYXRoIDogdHlwZVBhdGgsIGxvY2F0aW9uIH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdC8vIENoYWluLWZvcm0gY29uc3RydWN0aW9uOiBgbmV3IFIoLi4uKS5BKC4uLilgIC8gdGhlIGF3YWl0ZWRcblx0XHRcdC8vIHNpbmdsZS1jaGFpbiBgYXdhaXQgbmV3IFIoLi4uKS5BKC4uLikuQiguLi4pYCDigJQgdGhlIGNhbGwgb25cblx0XHRcdC8vIHRoZSBmcmVzaCBpbnN0YW5jZSBjb25zdHJ1Y3RzIHRoZSBjaGFpbiBUSVAgKGF3YWl0IGlzXG5cdFx0XHQvLyB0cmFuc3BhcmVudDsgdGhlIE5ld0V4cHJlc3Npb24gYnJhbmNoIGFscmVhZHkgcmVjb3JkZWQgdGhlXG5cdFx0XHQvLyBpbm5lciByb290KS4gVGhlIHJlc3VsdCB2YXJpYWJsZSBiaW5kcyB0byB0aGUgdGlwLCBub3QgdGhlXG5cdFx0XHQvLyByb290ICh0cmFja05ld0Fzc2lnbm1lbnQgcmVzb2x2ZXMgdGhlIHNhbWUgdGlwKVxuXHRcdFx0Y29uc3QgY2hhaW5UaXAgPSB0aGlzLnJlc29sdmVDaGFpblRpcFR5cGVQYXRoKG5vZGUpO1xuXHRcdFx0aWYgKGNoYWluVGlwKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkQ29uc3RydWN0aW9uVXNhZ2Uobm9kZSwgY2hhaW5UaXAsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdCk7XG5cdFx0XHRcdHRoaXMuYWRkRmxvdyhjaGFpblRpcCwge1xuXHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0a2luZCAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRjb250ZXh0ICA6ICdjaGFpbmVkIGNvbnN0cnVjdGlvbicsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBCYXJlIHN1YnR5cGUgY2FsbCBvbiBhIGtub3duIHJlY2VpdmVyOiBgaW5zdGFuY2UuU3ViKOKApilgXG5cdFx0XHQvLyBjb25zdHJ1Y3RzIHdpdGhvdXQgYG5ld2AsIGFzIHRoZSBjaGFpbiB0aXAgZG9lcy4gVGhlXG5cdFx0XHQvLyB2YXJpYWJsZSBpdCBpbml0aWFsaXplcyBiaW5kcyB0byBhIHNpbmdsZSBhbnN3ZXJcblx0XHRcdGNvbnN0IGJhcmVDYWxsUGF0aHMgPSBjaGFpblRpcCA/IFtdIDogdGhpcy5yZXNvbHZlQmFyZVN1YnR5cGVDYWxsKG5vZGUpO1xuXHRcdFx0Zm9yIChjb25zdCBiYXJlUGF0aCBvZiBiYXJlQ2FsbFBhdGhzKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkQ29uc3RydWN0aW9uVXNhZ2Uobm9kZSwgYmFyZVBhdGgsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdCk7XG5cdFx0XHRcdHRoaXMuYWRkRmxvdyhiYXJlUGF0aCwge1xuXHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0a2luZCAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRjb250ZXh0ICA6ICdiYXJlIHN1YnR5cGUgY2FsbCcsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGJhcmVDYWxsUGF0aHMubGVuZ3RoID09PSAxKSB7XG5cdFx0XHRcdHRoaXMuYmluZERpcmVjdFJlc3VsdChub2RlLCBiYXJlQ2FsbFBhdGhzWyAwIF0pO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBtbmVtb25pY2EgY2FsbC9hcHBseShlbnRpdHksIEN0b3IsIC4uLikgLyBiaW5kKGVudGl0eSwgQ3Rvcikg4oCUXG5cdFx0XHQvLyB0eXBlZCBjb25zdHJ1Y3Rpb24gd2l0aG91dCBgbmV3YDogdGhlIEN0b3IgYXJndW1lbnQgKGFyZyAxKSBpc1xuXHRcdFx0Ly8gdGhlIGNvbnN0cnVjdGVkIHR5cGUuIEltcG9ydC1hd2FyZTogb25seSBpZGVudGlmaWVycyBhY3R1YWxseVxuXHRcdFx0Ly8gaW1wb3J0ZWQgZnJvbSAnbW5lbW9uaWNhJyAob3IgbWVtYmVycyBvZiBhIHRyYWNrZWRcblx0XHRcdC8vIG1vZHVsZS1vYmplY3QgYWxpYXMpIG1hdGNoIOKAlCB1c2VybGFuZCBjYWxsL2FwcGx5L2JpbmQgbmV2ZXJcblx0XHRcdC8vIGRvLiBjYWxsL2FwcGx5IHJlY29yZCB0aGUgY29uc3RydWN0aW9uOyBiaW5kKCkgY29uc3RydWN0c1xuXHRcdFx0Ly8gbm90aGluZyDigJQgaXQgb25seSBiaW5kcyB0aGUgcmVzdWx0IHZhcmlhYmxlIHRvIHRoZSBDdG9yJ3Ncblx0XHRcdC8vIHR5cGUgKHJ1bnRpbWUgSW5zdGFuY2VSZXN1bHQ8TWVyZ2U8RSxUPj4gYXBwcm94aW1hdGVkIGJ5IFRcblx0XHRcdC8vIHdpdGhpbiB0aGUgb3V0cHV0IGNvbnRyYWN0KVxuXHRcdFx0Y29uc3QgY29uc3RydWN0aW9uUGF0aCA9IHRoaXMucmVzb2x2ZUNvbnN0cnVjdGlvbkZuVHlwZVBhdGgobm9kZSk7XG5cdFx0XHRpZiAoY29uc3RydWN0aW9uUGF0aCkge1xuXHRcdFx0XHRjb25zdCBpc0JpbmRGb3JtID0gdGhpcy5pc01uZW1vbmljYUNvbnN0cnVjdGlvbkZuKG5vZGUuZXhwcmVzc2lvbiwgJ2JpbmQnKTtcblx0XHRcdFx0aWYgKCFpc0JpbmRGb3JtKSB7XG5cdFx0XHRcdFx0Y29uc3QgY3RvckFyZ1RleHQgPSBub2RlLmFyZ3VtZW50c1sgMSBdPy5nZXRUZXh0KHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRcdHRoaXMucmVjb3JkQ29uc3RydWN0aW9uVXNhZ2Uobm9kZSwgY29uc3RydWN0aW9uUGF0aCwgc291cmNlRmlsZSwgY3RvckFyZ1RleHQpO1xuXHRcdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdFx0KTtcblx0XHRcdFx0XHR0aGlzLmFkZEZsb3coY29uc3RydWN0aW9uUGF0aCwge1xuXHRcdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRcdGtpbmQgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRcdGNvbnRleHQgIDogJ2NhbGwvYXBwbHkgY29uc3RydWN0aW9uJyxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShub2RlLCBjb25zdHJ1Y3Rpb25QYXRoKTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gaW5zdGFuY2UuZm9yaygpL2Nsb25lKCkg4oCUIHJ1bnRpbWUgcmUtcnVucyBjb25zdHJ1Y3Rpb24gKGhvb2tzXG5cdFx0XHQvLyBmaXJlLCBhIGRpc3RpbmN0IGluc3RhbmNlIG9uIGEgZGlzdGluY3QgbGluZSksIHNvIGFuXG5cdFx0XHQvLyBgaW5zdGFudGlhdGlvbmAgdXNhZ2UgcmVjb3JkcyB0aGUgc2l0ZSBJTiBBRERJVElPTiB0byB0aGVcblx0XHRcdC8vIHJlc3VsdC12YXIgYmluZGluZyBhbmQgdGhlIGdlbmVyaWMgbWV0aG9kQ2FsbCBmbG93ICh0aGUgZW50cnlcblx0XHRcdC8vIGlzIGJ5dGUtaW5kaXN0aW5ndWlzaGFibGUgZnJvbSBgbmV3YCB1bnRpbCB0aGUgZGVmZXJyZWRcblx0XHRcdC8vIG1lY2hhbmlzbS1raW5kIHJldmlzaW9uIOKAlCB0aGUgb3duZXIncyBleHBsaWNpdCBjYWxsKS4gRnJlZVxuXHRcdFx0Ly8gdXRpbHMubWVyZ2UoYSwgYiwgLi4uKSAvIHV0aWxzLmZvcmsoaW5zdGFuY2UpKC4uLikgYXJlXG5cdFx0XHQvLyBjb25zdHJ1Y3Rpb24gb2YgYSdzIHR5cGUgdG9vIChtZXJnZSA9IGZvcmsoYSkgb3ZlciBiJ3Ncblx0XHRcdC8vIGNvbnRleHQpOyB0aGUgcmVzdWx0IGJpbmRpbmcga2VlcHMgdGhlIGRvY3VtZW50ZWQgYXJnLTBcblx0XHRcdC8vIGFwcHJveGltYXRpb25cblx0XHRcdGNvbnN0IGZvcmtMaWtlUGF0aCA9IHRoaXMucmVzb2x2ZUZvcmtMaWtlVHlwZVBhdGgobm9kZSk7XG5cdFx0XHRpZiAoZm9ya0xpa2VQYXRoKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkQ29uc3RydWN0aW9uVXNhZ2Uobm9kZSwgZm9ya0xpa2VQYXRoLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0dGhpcy5iaW5kUmVzdWx0VmFyaWFibGUobm9kZSwgZm9ya0xpa2VQYXRoKTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHV0aWxzUGF0aCA9IHRoaXMucmVzb2x2ZVV0aWxzRm5UeXBlUGF0aChub2RlKTtcblx0XHRcdGlmICh1dGlsc1BhdGgpIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZShub2RlLCB1dGlsc1BhdGgsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShub2RlLCB1dGlsc1BhdGgpO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIEdldCBmdW5jdGlvbiBuYW1lIGZyb20gZXhwcmVzc2lvbiAoaWRlbnRpZmllciBvciBwcm9wZXJ0eSBhY2Nlc3MpXG5cdFx0XHQqL1xuXHRwcml2YXRlIGdldEZ1bmN0aW9uTmFtZSAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIGV4cHIudGV4dDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0KiBBZGQgYSB1c2FnZSB0byB0aGUgY29sbGVjdGlvblxuXHRcdFx0Ki9cblx0cHJpdmF0ZSBhZGRVc2FnZSAodHlwZVBhdGg6IHN0cmluZywgdXNhZ2U6IFVzYWdlSW5mbyk6IHZvaWQge1xuXHRcdC8vIE9ubHkgdHJhY2sgdXNhZ2VzIG9mIG1uZW1vbmljYS1kZWZpbmVkIHR5cGVzXG5cdFx0aWYgKCF0aGlzLmRlZmluaXRpb25zLmhhcyh0eXBlUGF0aCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKCF0aGlzLnVzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLnVzYWdlcy5zZXQodHlwZVBhdGgsIFtdKTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgZHVwbGljYXRlcyBiYXNlZCBvbiBsb2NhdGlvbiwgY29kZSwgYW5kIGtpbmRcblx0XHRjb25zdCBleGlzdGluZ1VzYWdlcyA9IHRoaXMudXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGlzRHVwbGljYXRlID0gZXhpc3RpbmdVc2FnZXMuc29tZShleGlzdGluZyA9PlxuXHRcdFx0ZXhpc3RpbmcubG9jYXRpb24gPT09IHVzYWdlLmxvY2F0aW9uICYmXG5cdFx0XHRcdGV4aXN0aW5nLmNvZGUgPT09IHVzYWdlLmNvZGUgJiZcblx0XHRcdFx0ZXhpc3Rpbmcua2luZCA9PT0gdXNhZ2Uua2luZCk7XG5cblx0XHRpZiAoIWlzRHVwbGljYXRlKSB7XG5cdFx0XHRleGlzdGluZ1VzYWdlcy5wdXNoKHVzYWdlKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBFRFMgKEV4ZWN1dGlvbiBEYXRhIFN0b3JhZ2UpIHVzYWdlIGluZm9ybWF0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RFRFMgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkgfHwgIW5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZ1bmNOYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIWZ1bmNOYW1lKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXHRcdC8vIEVuY2xvc2luZyBtbmVtb25pY2EgdHlwZSBwYXRoIOKAlCB3cmFwIGFyZ3MgYXJlIHVzdWFsbHkgbG9jYWxcblx0XHQvLyBmdW5jdGlvbnMsIHNvIHRoZSBvd25pbmcgZGVmaW5lKCkvbGF6eSgpIGhhbmRsZXIgb3IgZGVjb3JhdGVkXG5cdFx0Ly8gY2xhc3MgaXMgd2hhdCBlZHMuanNvbiBjb25zdW1lcnMgKEdyYXBoQnVpbGRlcikgY2FuIGpvaW4gb24uXG5cdFx0Y29uc3Qgc2NvcGUgPSB0aGlzLnJlc29sdmVFRFNTY29wZShub2RlKTtcblxuXHRcdC8vIHdyYXAoZm4pLCB3cmFwQ29uc3RydWN0b3JBcmcoZm4sIHBhcmVudCksIHVwZ3JhZGVDb25zdHJ1Y3RvckFyZyhhcmcsIGluc3QpLCB3cmFwSW5zdGFuY2VNZXRob2RzKG9iailcblx0XHRpZiAoXG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3dyYXAnIHx8XG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3dyYXBDb25zdHJ1Y3RvckFyZycgfHxcblx0XHRcdGZ1bmNOYW1lID09PSAndXBncmFkZUNvbnN0cnVjdG9yQXJnJyB8fFxuXHRcdFx0ZnVuY05hbWUgPT09ICd3cmFwSW5zdGFuY2VNZXRob2RzJ1xuXHRcdCkge1xuXHRcdFx0Y29uc3QgdGFyZ2V0VHlwZSA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShub2RlLmFyZ3VtZW50c1sgMCBdKTtcblx0XHRcdC8vIGRpdmUncyB3cmFwLWZhbWlseSBzaWduYXR1cmVzIChkaXZlL3NyYy9pbmRleC50cyk6XG5cdFx0XHQvLyAgIHdyYXAoZm4sIGxhYmVsPykgfCB3cmFwKGZuLCBjb250ZXh0PywgbGFiZWw/KVxuXHRcdFx0Ly8gICB3cmFwQ29uc3RydWN0b3JBcmcoZm4sIGNvbnRleHQpXG5cdFx0XHQvLyAgIHVwZ3JhZGVDb25zdHJ1Y3RvckFyZyhhcmcsIGluc3RhbmNlKVxuXHRcdFx0Ly8gICB3cmFwSW5zdGFuY2VNZXRob2RzKGluc3RhbmNlKVxuXHRcdFx0Ly8g4oCmc28gdGhlIGluc3RhbmNlL2NvbnRleHQgYXJnIHNpdHMgYXQgYXJnc1sxXSAoYXJnc1swXSBmb3Jcblx0XHRcdC8vIHdyYXBJbnN0YW5jZU1ldGhvZHMpIGFuZCBhIHN0cmluZyBsaXRlcmFsIGluIGFyZ3NbMS4uMl0gaXMgdGhlIGxhYmVsXG5cdFx0XHRjb25zdCBpbnN0YW5jZUFyZ05vZGUgPSBmdW5jTmFtZSA9PT0gJ3dyYXBJbnN0YW5jZU1ldGhvZHMnXG5cdFx0XHRcdD8gbm9kZS5hcmd1bWVudHNbIDAgXVxuXHRcdFx0XHQ6IG5vZGUuYXJndW1lbnRzWyAxIF07XG5cdFx0XHQvLyBGaXJlLWFuZC1mb3JnZXQgd3JhcHBlcnMgKHdpcmUtdXAgaGVscGVycywgcmVnaXN0cmF0aW9uXG5cdFx0XHQvLyBmdW5jdGlvbnMpIHNpdCBvdXRzaWRlIGFueSBkZWZpbmUoKS9sYXp5KCkgaGFuZGxlciwgc28gdGhlXG5cdFx0XHQvLyBsZXhpY2FsIHNjb3BlIGlzIGFic2VudCDigJQgYXR0cmlidXRlIHRocm91Z2ggdGhlIGluc3RhbmNlL2NvbnRleHRcblx0XHRcdC8vIGFyZ3VtZW50IGluc3RlYWQ6IGEgdHJhY2tlZCBhc3NpZ25tZW50LCBlbHNlIHRoZSBlbmNsb3Npbmdcblx0XHRcdC8vIGZ1bmN0aW9uJ3MgcGFyYW1ldGVyIGFubm90YXRpb24gcmVzb2x2ZWQgdGhyb3VnaCB0aGUgZ3JhcGggbGF3XG5cdFx0XHRjb25zdCBpbnN0YW5jZVR5cGVQYXRoID0gaW5zdGFuY2VBcmdOb2RlXG5cdFx0XHRcdD8gdGhpcy5yZXNvbHZlV3JhcEluc3RhbmNlVHlwZVBhdGgoaW5zdGFuY2VBcmdOb2RlKVxuXHRcdFx0XHQ6IHVuZGVmaW5lZDtcblx0XHRcdGNvbnN0IGVmZmVjdGl2ZVNjb3BlID0gc2NvcGUgPz8gaW5zdGFuY2VUeXBlUGF0aDtcblx0XHRcdGNvbnN0IGluZm86IEVEU0luZm8gPSB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgIDogJ3dyYXAnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdHNjb3BlICAgICAgOiBlZmZlY3RpdmVTY29wZSxcblx0XHRcdFx0Zm4gICAgICAgICA6IGZ1bmNOYW1lLFxuXHRcdFx0fTtcblx0XHRcdGlmIChpbnN0YW5jZUFyZ05vZGUgJiYgdHMuaXNJZGVudGlmaWVyKGluc3RhbmNlQXJnTm9kZSkpIHtcblx0XHRcdFx0aW5mby5pbnN0YW5jZUFyZyA9IGluc3RhbmNlQXJnTm9kZS50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBleHRyYUFyZyBvZiBbIG5vZGUuYXJndW1lbnRzWyAxIF0sIG5vZGUuYXJndW1lbnRzWyAyIF0gXSkge1xuXHRcdFx0XHRpZiAoZXh0cmFBcmcgJiYgdHMuaXNTdHJpbmdMaXRlcmFsKGV4dHJhQXJnKSkge1xuXHRcdFx0XHRcdGluZm8ubGFiZWwgPSBleHRyYUFyZy50ZXh0O1xuXHRcdFx0XHRcdGJyZWFrO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBBIHdyYXAoKSBjYWxsIG5lc3RlZCBpbnNpZGUgYW5vdGhlciB3cmFwcGVkIGJvZHkgY2FycmllcyB0aGVcblx0XHRcdC8vIGxpbmsgdG8gdGhlIHNpdGUgd2hvc2UgcnVudGltZSB3cmFwcGluZyBjYXVzZWQgaXQg4oCUIGFuZCwgd2hlblxuXHRcdFx0Ly8gdGhlIG5lc3RlZCBzaXRlIGhhcyBubyBzY29wZSBvZiBpdHMgb3duLCB0aGUgY2F1c2luZyBzaXRlJ3Ncblx0XHRcdC8vIHNjb3BlIGF0dHJpYnV0aW9uIHRyYXZlbHMgd2l0aCB0aGUgbGlua1xuXHRcdFx0Y29uc3QgdmlhTGluayA9IHRoaXMubmVzdGVkV3JhcFZpYS5nZXQobm9kZSk7XG5cdFx0XHRpZiAodmlhTGluaykge1xuXHRcdFx0XHRpbmZvLnZpYSA9IHZpYUxpbmsudmlhO1xuXHRcdFx0XHRpZiAoaW5mby5zY29wZSA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdFx0aW5mby5zY29wZSA9IHZpYUxpbmsuc2NvcGU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIGRpdmUgd3JhcHMgcmV0dXJuZWQgZnVuY3Rpb25zIHRvbywgYW5kIGFueSBtbmVtb25pY2EgaW5zdGFuY2Vcblx0XHRcdC8vIGNyZWF0ZWQgaW5zaWRlIHRoZSB3cmFwcGVkIGJvZHkgaXMgYSBndWFyYW50ZWVkIHBhdGggaGl0IOKAlFxuXHRcdFx0Ly8gYm90aCBhcmUgY2FsY3VsYWJsZSBBb1QsIHNvIHJlY29yZCB0aGVtXG5cdFx0XHRjb25zdCB3cmFwcGVkID0gdGhpcy5yZXNvbHZlRnVuY3Rpb25Bcmd1bWVudChub2RlLmFyZ3VtZW50c1sgMCBdLCBzb3VyY2VGaWxlKTtcblx0XHRcdGlmICh3cmFwcGVkKSB7XG5cdFx0XHRcdC8vIFRoZSB3cmFwcGVkIGNhbGxiYWNrIGdldHMgaXRzIG93biBzY29wZSBpbiBzY29wZXMuanNvbiBrZXllZCBieVxuXHRcdFx0XHQvLyBpdHMgc3RhcnQgcG9zaXRpb24g4oCUIHJlY29yZCB0aGF0IHNjb3BlSWQgc28gZ3JhcGggY29uc3VtZXJzIGNhblxuXHRcdFx0XHQvLyBqb2luIGEgd3JhcCBlbnRyeSB0byB0aGUgY2FsbGJhY2sncyBjcmVhdGlvbiBub2RlXG5cdFx0XHRcdGNvbnN0IGNhbGxiYWNrUG9zID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHR3cmFwcGVkLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdCk7XG5cdFx0XHRcdGNvbnN0IGNhbGxiYWNrRmlsZSA9IG5vZGVQYXRoLnJlc29sdmUoc291cmNlRmlsZS5maWxlTmFtZSk7XG5cdFx0XHRcdGluZm8uY2FsbGJhY2tTY29wZUlkID0gYCR7Y2FsbGJhY2tGaWxlfToke2NhbGxiYWNrUG9zLmxpbmUgKyAxfToke2NhbGxiYWNrUG9zLmNoYXJhY3RlciArIDF9YDtcblx0XHRcdFx0Y29uc3QgY3JlYXRlc1R5cGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0XHRcdHRoaXMuYW5hbHl6ZVdyYXBwZWRCb2R5KHdyYXBwZWQsIGxvY2F0aW9uLCBzb3VyY2VGaWxlLCAwLCBuZXcgU2V0KCksIGNyZWF0ZXNUeXBlcywgZWZmZWN0aXZlU2NvcGUpO1xuXHRcdFx0XHRpZiAoY3JlYXRlc1R5cGVzLnNpemUgPiAwKSB7XG5cdFx0XHRcdFx0aW5mby5jcmVhdGVzVHlwZXMgPSBBcnJheS5mcm9tKGNyZWF0ZXNUeXBlcyk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGNvbnN0IHN0b3JlZCA9IHRoaXMuYWRkRURTKHRhcmdldFR5cGUgfHwgZWZmZWN0aXZlU2NvcGUgfHwgJ3Vua25vd24nLCBpbmZvKTtcblx0XHRcdHRoaXMud3JhcEVudHJ5QnlOb2RlLnNldChub2RlLCBzdG9yZWQpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGN1cnJlbnQoKSwgZ2V0RXJyb3JJbnN0YW5jZShlcnIpLCBnZXRGbG93KHRhcmdldD8pXG5cdFx0aWYgKGZ1bmNOYW1lID09PSAnY3VycmVudCcgfHwgZnVuY05hbWUgPT09ICdnZXRFcnJvckluc3RhbmNlJyB8fCBmdW5jTmFtZSA9PT0gJ2dldEZsb3cnKSB7XG5cdFx0XHR0aGlzLmFkZEVEUyhzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgOiAnY29udGV4dENvbnN1bWUnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRzY29wZSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGF0dGFjaEhvb2tzKGNvbGxlY3Rpb24pIOKAlCBmcm9tIEBtbmVtb25pY2Evb3RlbCwgd2lyZXMgYVxuXHRcdC8vIFR5cGVzQ29sbGVjdGlvbiB0byBkaXZlJ3MgbGlmZWN5Y2xlIHRyYWNpbmdcblx0XHRpZiAoZnVuY05hbWUgPT09ICdhdHRhY2hIb29rcycgJiYgbm9kZS5hcmd1bWVudHMubGVuZ3RoID4gMCkge1xuXHRcdFx0Y29uc3QgWyBhcmcgXSA9IG5vZGUuYXJndW1lbnRzO1xuXHRcdFx0aWYgKHRzLmlzQXJyYXlMaXRlcmFsRXhwcmVzc2lvbihhcmcpKSB7XG5cdFx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBhcmcuZWxlbWVudHMpIHtcblx0XHRcdFx0XHRjb25zdCB0YXJnZXRUeXBlID0gdGhpcy5yZXNvbHZlRURTQXJndW1lbnRUeXBlKGVsZW1lbnQpO1xuXHRcdFx0XHRcdHRoaXMuYWRkRURTKHRhcmdldFR5cGUgfHwgc2NvcGUgfHwgJ3Vua25vd24nLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0XHRcdGtpbmQgICAgICAgOiAnaG9va0F0dGFjaCcsXG5cdFx0XHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRcdFx0dGFyZ2V0VHlwZSA6IHRhcmdldFR5cGUgfHwgdW5kZWZpbmVkLFxuXHRcdFx0XHRcdFx0c2NvcGUsXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGNvbnN0IHRhcmdldFR5cGUgPSB0aGlzLnJlc29sdmVFRFNBcmd1bWVudFR5cGUoYXJnKTtcblx0XHRcdFx0dGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCBzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0XHRraW5kICAgICAgIDogJ2hvb2tBdHRhY2gnLFxuXHRcdFx0XHRcdGNvZGUsXG5cdFx0XHRcdFx0dGFyZ2V0VHlwZSA6IHRhcmdldFR5cGUgfHwgdW5kZWZpbmVkLFxuXHRcdFx0XHRcdHNjb3BlLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0eXBlIGZyb20gRURTIGNhbGwgYXJndW1lbnQgKGJlc3QgZWZmb3J0KVxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRURTQXJndW1lbnRUeXBlIChhcmc6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghYXJnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIElkZW50aWZpZXI6IHZhcmlhYmxlIG5hbWVcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdGNvbnN0IG1hcHBlZCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGFyZy50ZXh0KTtcblx0XHRcdGlmIChtYXBwZWQpIHtcblx0XHRcdFx0cmV0dXJuIG1hcHBlZDtcblx0XHRcdH1cblx0XHRcdC8vIE1heWJlIGl0J3MgYSB0eXBlIG5hbWUgZGlyZWN0bHlcblx0XHRcdGlmICh0aGlzLmRlZmluaXRpb25zLmhhcyhhcmcudGV4dCkpIHtcblx0XHRcdFx0cmV0dXJuIGFyZy50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0Ly8gbGV0LWluLXRyeTogYSBsZXQvdmFyIGJpbmRpbmcgZGVjbGFyZWQgd2l0aG91dCBhIHRyYWNrZWRcblx0XHRcdC8vIGluaXRpYWxpemVyIGFuZCBhc3NpZ25lZCBsYXRlciBpbiB0aGUgU0FNRSBzY29wZSAodGhlXG5cdFx0XHQvLyBmaXJlLWFuZC1mb3JnZXQgY2F0Y2gtZ3VhcmQgcGF0dGVybjogYGxldCBmbjsgdHJ5IHsgZm4gPVxuXHRcdFx0Ly8g4oCmIH0gY2F0Y2ggeyByZXR1cm4gfSB3cmFwKGZuLCDigKYpYCkg4oCUIGZvbGxvdyB0aGUgZmlyc3Rcblx0XHRcdC8vIHN0YXRpY2FsbHktdmlzaWJsZSBpbi1zY29wZSBhc3NpZ25tZW50LiBObyBmbG93IGFuYWx5c2lzOlxuXHRcdFx0Ly8gZnVuY3Rpb24vY2xhc3MgYm91bmRhcmllcyBhcmUgbm90IGNyb3NzZWQsIGFcblx0XHRcdC8vIG5ldmVyLWFzc2lnbmVkIGJpbmRpbmcgc3RheXMgdW5rbm93biAoRjIwIGRpc2NpcGxpbmUpLlxuXHRcdFx0Ly8gV2hlbiB0aGUgYXNzaWdubWVudCByZXNvbHZlcywgaXRzIGV2aWRlbmNlIFdJTlMgb3ZlciBhbnlcblx0XHRcdC8vIGRlY2xhcmF0aW9uIGFubm90YXRpb24gKHRoZSBjb25zdHJ1Y3RlZCBzdWJ0eXBlIGlzIHRoZSBtb3JlXG5cdFx0XHQvLyBzcGVjaWZpYyB0cnV0aCk7IGFuIHVucmVzb2x2YWJsZSBSSFMgKGEgdXNlcmxhbmQgY2FsbCwgc2F5KVxuXHRcdFx0Ly8gZmFsbHMgdGhyb3VnaCB0byB0aGUgYW5ub3RhdGlvbiBjbGFpbSBiZWxvdy5cblx0XHRcdGNvbnN0IGFzc2lnbmVkID0gdGhpcy5mb2xsb3dTY29wZUFzc2lnbm1lbnQoYXJnLnRleHQsIGFyZyk7XG5cdFx0XHRpZiAoYXNzaWduZWQpIHtcblx0XHRcdFx0Y29uc3QgcmVzb2x2ZWQgPSB0aGlzLnJlc29sdmVFRFNBcmd1bWVudFR5cGUoYXNzaWduZWQpO1xuXHRcdFx0XHRpZiAocmVzb2x2ZWQpIHtcblx0XHRcdFx0XHRyZXR1cm4gcmVzb2x2ZWQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIEFubm90YXRpb24gZmFsbGJhY2sg4oCUIHRoZSBGMjAgZGlzY2lwbGluZSBvbmUgYXJndW1lbnQgb3Zlcjpcblx0XHRcdC8vIGFuIGV4cGxpY2l0IGRlY2xhcmF0aW9uIG9yIHBhcmFtZXRlciBhbm5vdGF0aW9uIGlzIGEgdXNlclxuXHRcdFx0Ly8gY2xhaW0gd3JpdHRlbiBpbiB0aGUgQVNULCBub3QgZmxvdyBhbmFseXNpcy4gUGFyYW1ldGVyXG5cdFx0XHQvLyBmaXJzdDogaXQgc2hhZG93cyBhbiBvdXRlciBsZXQsIHNhbWUgYXMgdGhlIGNvbnRleHQtYXJnIHBhdGguXG5cdFx0XHRjb25zdCBhbm5vdGF0ZWQgPSB0aGlzLnJlc29sdmVQYXJhbWV0ZXJBbm5vdGF0aW9uVHlwZVBhdGgoYXJnLnRleHQsIGFyZykgPz9cblx0XHRcdFx0dGhpcy5yZXNvbHZlVmFyaWFibGVBbm5vdGF0aW9uVHlwZVBhdGgoYXJnLnRleHQsIGFyZyk7XG5cdFx0XHRyZXR1cm4gYW5ub3RhdGVkO1xuXHRcdH1cblxuXHRcdC8vIE5ld0V4cHJlc3Npb246IHRoZSBjb25zdHJ1Y3RlZCB0eXBlIOKAlCByZWFjaGFibGUgZGlyZWN0bHlcblx0XHQvLyAod3JhcChuZXcgVCgpLCDigKYpKSBvciB0aHJvdWdoIGEgZm9sbG93ZWQgYXNzaWdubWVudFxuXHRcdGlmICh0cy5pc05ld0V4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0Y29uc3QgY3RvckV4cHIgPSBhcmcuZXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IG5hbWUgPSB0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdG9yRXhwcilcblx0XHRcdFx0PyB0aGlzLnJlc29sdmVUeXBlUGF0aChjdG9yRXhwcilcblx0XHRcdFx0OiB0aGlzLmdldFR5cGVOYW1lRnJvbUV4cHJlc3Npb24oY3RvckV4cHIpO1xuXHRcdFx0Y29uc3Qga25vd24gPSBuYW1lICYmIHRoaXMuZGVmaW5pdGlvbnMuaGFzKG5hbWUpID8gbmFtZSA6IHVuZGVmaW5lZDtcblx0XHRcdHJldHVybiBrbm93bjtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSBhY2Nlc3M6IG9iai5wcm9wXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdHJldHVybiB0aGlzLnJlc29sdmVUeXBlUGF0aChhcmcpO1xuXHRcdH1cblxuXHRcdC8vIFRoaXMgZXhwcmVzc2lvbjogdGhpcy5zb21ldGhpbmdcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXJnKSAmJiB0cy5pc0lkZW50aWZpZXIoYXJnLmV4cHJlc3Npb24pICYmIGFyZy5leHByZXNzaW9uLnRleHQgPT09ICd0aGlzJykge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIGxldC1pbi10cnk6IGZpbmQgdGhlIFJJR0hULUhBTkQgU0lERSBvZiB0aGUgZmlyc3Qgc3RhdGljYWxseS12aXNpYmxlXG5cdCAqIGFzc2lnbm1lbnQgdG8gYG5hbWVgIGluIHRoZSBzY29wZSB0aGF0IGRlY2xhcmVzIGl0LiBUaGUgZGVjbGFyaW5nXG5cdCAqIGNvbnRhaW5lciBpcyBmb3VuZCBpbm5lcm1vc3Qtb3V0IChibG9ja3MsIGNhc2UgY2xhdXNlcywgdGhlIHNvdXJjZVxuXHQgKiBmaWxlIOKAlCB0aGUgRjIwIHdhbGspOyB0aGUgc2NhbiByZWN1cnNlcyBpbnRvIG5lc3RlZCBibG9ja3MgKHRyeS9cblx0ICogY2F0Y2gvZmluYWxseSwgaWYvZWxzZSwgbG9vcHMsIHN3aXRjaCBjYXNlcykgYnV0IE5FVkVSIGNyb3NzZXNcblx0ICogZnVuY3Rpb24gb3IgY2xhc3MgYm91bmRhcmllcyDigJQgYW4gYXNzaWdubWVudCBpbnNpZGUgYSBjbG9zdXJlIGRvZXNcblx0ICogbm90IGF0dHJpYnV0ZS4gUmV0dXJucyB1bmRlZmluZWQgd2hlbiB0aGUgYmluZGluZyBpcyBkZWNsYXJlZCBidXRcblx0ICogbmV2ZXIgYXNzaWduZWQgaW4gc2NvcGUgKGFuZCBzdG9wcyB0aGVyZTogYW4gaW5uZXIgZGVjbGFyYXRpb25cblx0ICogc2hhZG93cyBhbnkgb3V0ZXIgYmluZGluZykuXG5cdCAqL1xuXHRwcml2YXRlIGZvbGxvd1Njb3BlQXNzaWdubWVudCAobmFtZTogc3RyaW5nLCBmcm9tOiB0cy5Ob2RlKTogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBmcm9tO1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRjb25zdCBzdGF0ZW1lbnRzOiB0cy5Ob2RlQXJyYXk8dHMuU3RhdGVtZW50PiB8IHVuZGVmaW5lZCA9XG5cdFx0XHRcdHRzLmlzQmxvY2soY3VycmVudCkgfHwgdHMuaXNNb2R1bGVCbG9jayhjdXJyZW50KSB8fCB0cy5pc1NvdXJjZUZpbGUoY3VycmVudClcblx0XHRcdFx0XHQ/IGN1cnJlbnQuc3RhdGVtZW50c1xuXHRcdFx0XHRcdDogdHMuaXNDYXNlQ2xhdXNlKGN1cnJlbnQpIHx8IHRzLmlzRGVmYXVsdENsYXVzZShjdXJyZW50KVxuXHRcdFx0XHRcdFx0PyBjdXJyZW50LnN0YXRlbWVudHNcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0aWYgKHN0YXRlbWVudHMgJiYgdGhpcy5zdGF0ZW1lbnRzRGVjbGFyZVZhcmlhYmxlKHN0YXRlbWVudHMsIG5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHJocyA9IHRoaXMuZmluZEFzc2lnbm1lbnRSaHNJblN0YXRlbWVudHMoc3RhdGVtZW50cywgbmFtZSk7XG5cdFx0XHRcdHJldHVybiByaHM7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogVHJ1ZSB3aGVuIHRoZSBzdGF0ZW1lbnQgbGlzdCBjb250YWlucyBhIGBsZXRgL2B2YXJgL2Bjb25zdGBcblx0ICogZGVjbGFyYXRpb24gZm9yIGBuYW1lYCAoYW55IGluaXRpYWxpemVyIGZvcm0pLlxuXHQgKi9cblx0cHJpdmF0ZSBzdGF0ZW1lbnRzRGVjbGFyZVZhcmlhYmxlIChzdGF0ZW1lbnRzOiByZWFkb25seSB0cy5TdGF0ZW1lbnRbXSwgbmFtZTogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc3RhdGVtZW50cykge1xuXHRcdFx0aWYgKCF0cy5pc1ZhcmlhYmxlU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGRlY2xhcmF0aW9uIG9mIHN0YXRlbWVudC5kZWNsYXJhdGlvbkxpc3QuZGVjbGFyYXRpb25zKSB7XG5cdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZGVjbGFyYXRpb24ubmFtZSkgJiYgZGVjbGFyYXRpb24ubmFtZS50ZXh0ID09PSBuYW1lKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpcnN0IGBuYW1lID0gcmhzYCBhc3NpZ25tZW50IGluIHRoZSBzdGF0ZW1lbnQgbGlzdCwgcmVjdXJzaW5nXG5cdCAqIGludG8gbmVzdGVkIGluLXNjb3BlIGJsb2Nrcy4gRnVuY3Rpb24gYW5kIGNsYXNzIGJvZGllcyBhcmVcblx0ICogYm91bmRhcmllcyBhbmQgYXJlIG5vdCBlbnRlcmVkLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kQXNzaWdubWVudFJoc0luU3RhdGVtZW50cyAoXG5cdFx0c3RhdGVtZW50czogcmVhZG9ubHkgdHMuU3RhdGVtZW50W10sXG5cdFx0bmFtZTogc3RyaW5nXG5cdCk6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIHN0YXRlbWVudHMpIHtcblx0XHRcdGNvbnN0IGRpcmVjdCA9IHRoaXMuZGlyZWN0QXNzaWdubWVudFJocyhzdGF0ZW1lbnQsIG5hbWUpO1xuXHRcdFx0aWYgKGRpcmVjdCkge1xuXHRcdFx0XHRyZXR1cm4gZGlyZWN0O1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBuZXN0ZWQgb2YgdGhpcy5uZXN0ZWRTY29wZUJsb2NrcyhzdGF0ZW1lbnQpKSB7XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kQXNzaWdubWVudFJoc0luU3RhdGVtZW50cyhuZXN0ZWQsIG5hbWUpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBgbmFtZSA9IHJoc2AgYXMgYSBkaXJlY3QgZXhwcmVzc2lvbiBzdGF0ZW1lbnQuXG5cdCAqL1xuXHRwcml2YXRlIGRpcmVjdEFzc2lnbm1lbnRSaHMgKHN0YXRlbWVudDogdHMuU3RhdGVtZW50LCBuYW1lOiBzdHJpbmcpOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIXRzLmlzRXhwcmVzc2lvblN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBleHByID0gc3RhdGVtZW50LmV4cHJlc3Npb247XG5cdFx0aWYgKCF0cy5pc0JpbmFyeUV4cHJlc3Npb24oZXhwcikgfHwgZXhwci5vcGVyYXRvclRva2VuLmtpbmQgIT09IHRzLlN5bnRheEtpbmQuRXF1YWxzVG9rZW4pIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGV4cHIubGVmdCkgfHwgZXhwci5sZWZ0LnRleHQgIT09IG5hbWUpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJocyA9IGV4cHIucmlnaHQ7XG5cdFx0cmV0dXJuIHJocztcblx0fVxuXG5cdC8qKlxuXHQgKiBTdGF0ZW1lbnQgbGlzdHMgb2YgdGhlIG5lc3RlZCBibG9ja3MgdGhhdCBzdGF5IElOU0lERSB0aGUgY3VycmVudFxuXHQgKiBzY29wZSDigJQgdHJ5L2NhdGNoL2ZpbmFsbHksIGlmL2Vsc2UsIGxvb3BzLCBzd2l0Y2ggY2FzZXMsIG5lc3RlZFxuXHQgKiBibG9ja3MsIGxhYmVsZWQgc3RhdGVtZW50cy4gRnVuY3Rpb24tbGlrZSBhbmQgY2xhc3MgYm9kaWVzIGFyZVxuXHQgKiBzY29wZSBib3VuZGFyaWVzIGFuZCB5aWVsZCBub3RoaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBuZXN0ZWRTY29wZUJsb2NrcyAoc3RhdGVtZW50OiB0cy5TdGF0ZW1lbnQpOiByZWFkb25seSAocmVhZG9ubHkgdHMuU3RhdGVtZW50W10pW10ge1xuXHRcdGNvbnN0IGJsb2NrczogdHMuU3RhdGVtZW50W11bXSA9IFtdO1xuXHRcdGNvbnN0IHB1c2ggPSAobm9kZTogdHMuU3RhdGVtZW50IHwgdW5kZWZpbmVkKTogdm9pZCA9PiB7XG5cdFx0XHRpZiAobm9kZSAmJiB0cy5pc0Jsb2NrKG5vZGUpKSB7XG5cdFx0XHRcdGJsb2Nrcy5wdXNoKFsgLi4ubm9kZS5zdGF0ZW1lbnRzIF0pO1xuXHRcdFx0fVxuXHRcdH07XG5cdFx0aWYgKHRzLmlzQmxvY2soc3RhdGVtZW50KSkge1xuXHRcdFx0YmxvY2tzLnB1c2goWyAuLi5zdGF0ZW1lbnQuc3RhdGVtZW50cyBdKTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzVHJ5U3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdHB1c2goc3RhdGVtZW50LnRyeUJsb2NrKTtcblx0XHRcdGlmIChzdGF0ZW1lbnQuY2F0Y2hDbGF1c2UpIHtcblx0XHRcdFx0cHVzaChzdGF0ZW1lbnQuY2F0Y2hDbGF1c2UuYmxvY2spO1xuXHRcdFx0fVxuXHRcdFx0cHVzaChzdGF0ZW1lbnQuZmluYWxseUJsb2NrKTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzSWZTdGF0ZW1lbnQoc3RhdGVtZW50KSkge1xuXHRcdFx0cHVzaChzdGF0ZW1lbnQudGhlblN0YXRlbWVudCk7XG5cdFx0XHRwdXNoKHN0YXRlbWVudC5lbHNlU3RhdGVtZW50KTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzRm9yU3RhdGVtZW50KHN0YXRlbWVudCkgfHwgdHMuaXNGb3JJblN0YXRlbWVudChzdGF0ZW1lbnQpIHx8XG5cdFx0XHR0cy5pc0Zvck9mU3RhdGVtZW50KHN0YXRlbWVudCkgfHwgdHMuaXNXaGlsZVN0YXRlbWVudChzdGF0ZW1lbnQpIHx8XG5cdFx0XHR0cy5pc0RvU3RhdGVtZW50KHN0YXRlbWVudCkgfHwgdHMuaXNXaXRoU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdHB1c2goc3RhdGVtZW50LnN0YXRlbWVudCk7XG5cdFx0fSBlbHNlIGlmICh0cy5pc1N3aXRjaFN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGNsYXVzZSBvZiBzdGF0ZW1lbnQuY2FzZUJsb2NrLmNsYXVzZXMpIHtcblx0XHRcdFx0YmxvY2tzLnB1c2goWyAuLi5jbGF1c2Uuc3RhdGVtZW50cyBdKTtcblx0XHRcdH1cblx0XHR9IGVsc2UgaWYgKHRzLmlzTGFiZWxlZFN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRjb25zdCBuZXN0ZWQgPSB0aGlzLm5lc3RlZFNjb3BlQmxvY2tzKHN0YXRlbWVudC5zdGF0ZW1lbnQpO1xuXHRcdFx0Zm9yIChjb25zdCBibG9jayBvZiBuZXN0ZWQpIHtcblx0XHRcdFx0YmxvY2tzLnB1c2goWyAuLi5ibG9jayBdKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gYmxvY2tzO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0aGUgZW5jbG9zaW5nIG1uZW1vbmljYSBzY29wZSBvZiBhbiBFRFMgY2FsbCBzaXRlIGJ5IHdhbGtpbmdcblx0ICogdXAgdGhlIHBhcmVudCBjaGFpbjogbmVhcmVzdCBkZWZpbmUoKS9sYXp5KCkgY2FsbCB3aG9zZSBoYW5kbGVyIGhvbGRzXG5cdCAqIHRoZSBub2RlLCBvciBuZWFyZXN0IEBkZWNvcmF0ZSgpLWVkIGNsYXNzIGRlY2xhcmF0aW9uLiBCZXN0IGVmZm9ydCDigJRcblx0ICogcmV0dXJucyB1bmRlZmluZWQgZm9yIGNhbGxzIG91dHNpZGUgYW55IHR5cGUgc2NvcGUgKG1vZHVsZSB0b3AgbGV2ZWwpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRURTU2NvcGUgKG5vZGU6IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbm9kZS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGNvbnN0IHNjb3BlUGF0aCA9IHRoaXMuZWRzU2NvcGVCeU5vZGUuZ2V0KGN1cnJlbnQpO1xuXHRcdFx0aWYgKHNjb3BlUGF0aCkge1xuXHRcdFx0XHRyZXR1cm4gc2NvcGVQYXRoO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSB3cmFwIHNpdGUncyBpbnN0YW5jZS9jb250ZXh0IGFyZ3VtZW50IHRvIGEgbW5lbW9uaWNhIHR5cGVcblx0ICogcGF0aCDigJQgdGhlIGZpcmUtYW5kLWZvcmdldC13cmFwcGVyIGF0dHJpYnV0aW9uIGZhbGxiYWNrIHdoZW4gdGhlIGNhbGxcblx0ICogc2l0cyBvdXRzaWRlIGFueSBkZWZpbmUoKS9sYXp5KCkgaGFuZGxlcjogYSB0cmFja2VkIGFzc2lnbm1lbnRcblx0ICogKGBjb25zdCBob2xkZXIgPSBuZXcgSG9sZGVyKC4uLilgKSwgZWxzZSB0aGUgcm9vdCBpZGVudGlmaWVyJ3Ncblx0ICogKHByb3BlcnR5LWFjY2VzcyByb290cyBpbmNsdWRlZCkgcGFyYW1ldGVyIGFubm90YXRpb24gcmVzb2x2ZWRcblx0ICogdGhyb3VnaCB0aGUgZ3JhcGggbGF3LiBBbWJpZ3VpdHkgb3IgYWJzZW5jZSBzdGF5cyBzaWxlbnQg4oCUIHRoaXMgaXMgYVxuXHQgKiBtZXRhZGF0YSBoZXVyaXN0aWMsIG5vdCB0aGUgaWRlbnRpdHktbGF3IHN1cmZhY2UuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVXcmFwSW5zdGFuY2VUeXBlUGF0aCAoYXJnOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBmcm9tQmluZGluZyA9IChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQgPT4ge1xuXHRcdFx0Y29uc3QgbWFwcGVkID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0XHRpZiAobWFwcGVkKSB7XG5cdFx0XHRcdHJldHVybiBtYXBwZWQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBhbm5vdGF0aW9uVHlwZSA9IHRoaXMucmVzb2x2ZVBhcmFtZXRlckFubm90YXRpb25UeXBlUGF0aChuYW1lLCBmcm9tKSA/P1xuXHRcdFx0XHQvLyBGMjAgY2hlYXAgdGllcjogdGhlIGlkZW50aWZpZXIgaXMgYm91bmQgdG8gYSBsZXQvdmFyL2NvbnN0XG5cdFx0XHRcdC8vIHdpdGggYW4gRVhQTElDSVQgdHlwZSBhbm5vdGF0aW9uIOKAlCByZXNvbHZlIHRoZSBhbm5vdGF0aW9uXG5cdFx0XHRcdC8vIHRocm91Z2ggdGhlIGdyYXBoIGxhdy4gTm8gZmxvdy1zZW5zaXRpdmUgYXNzaWdubWVudFxuXHRcdFx0XHQvLyB0cmFja2luZzogYW4gVU5BTk5PVEFURUQgbGV0IHN0aWxsIGJ1Y2tldHMgdW5rbm93blxuXHRcdFx0XHR0aGlzLnJlc29sdmVWYXJpYWJsZUFubm90YXRpb25UeXBlUGF0aChuYW1lLCBmcm9tKTtcblx0XHRcdHJldHVybiBhbm5vdGF0aW9uVHlwZTtcblx0XHR9O1xuXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihhcmcpKSB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSBmcm9tQmluZGluZyhhcmcudGV4dCwgYXJnKTtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcmcpKSB7XG5cdFx0XHRjb25zdCByb290ID0gdGhpcy5nZXRSb290SWRlbnRpZmllcihhcmcpO1xuXHRcdFx0aWYgKHJvb3QpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0ID0gZnJvbUJpbmRpbmcocm9vdC50ZXh0LCBhcmcpO1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEVtaXNzaW9uLWxhdyBoZWxwZXIgKDAuMi4wIHJlc3RvcmF0aW9uKTogaXMgYG5hbWVgIGRlY2xhcmVkIGluIGFueVxuXHQgKiBBTkFMWVpFRCBQUk9KRUNUIGZpbGU/IEV4dGVybmFsL2FtYmllbnQgZmlsZXMgKC5kLnRzLCBub2RlX21vZHVsZXMpXG5cdCAqIGRvIG5vdCBjb3VudC4gQSBuYW1lIHdpdGggbm8gcHJvamVjdCBkZWNsYXJhdGlvbiBpcyBhbiBhbWJpZW50L2xpYlxuXHQgKiBjb25zdHJ1Y3Qg4oCUIHNhZmUgdG8gZW1pdCB2ZXJiYXRpbSBpbnRvIHRoZSBzZWxmLWNvbnRhaW5lZCB0eXBlcy50cztcblx0ICogYSBwcm9qZWN0LWxvY2FsIG5hbWUgaXMgbm90IChubyBpbXBvcnRzIGluIHRoZSBnZW5lcmF0ZWQgZmlsZSkuXG5cdCAqL1xuXHRwcml2YXRlIGlzUHJvamVjdERlY2xhcmVkVHlwZU5hbWUgKG5hbWU6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRcdGZvciAoY29uc3QgWyBmaWxlLCBkZWNscyBdIG9mIHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscykge1xuXHRcdFx0aWYgKHRoaXMuaXNFeHRlcm5hbERlY2xGaWxlKGZpbGUpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGRlY2xzLmhhcyhuYW1lKSkge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gZmFsc2U7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGMjQ6IHJlc29sdmUgYSBiYXJlLWlkZW50aWZpZXIgYW5ub3RhdGlvbiB0byBhIGdyYXBoIGZ1bGxQYXRoLiBUaGVcblx0ICogYW5ub3RhdGlvbiBtYXkgbmFtZSB0aGUgdHlwZSBkaXJlY3RseSAoYExlZGdlclVwZGF0ZWApIG9yIGNhcnJ5XG5cdCAqIHRoZSBHRU5FUkFURUQgaW5zdGFuY2UgYWxpYXMgb2YgYSBuZXN0ZWQgdHlwZVxuXHQgKiAoYFVwZGF0ZVBheV9Tb21lVGVybWluYWxgLCBpbXBvcnRlZCBmcm9tIHRoZSBnZW5lcmF0ZWQgdHlwZXMgZmlsZVxuXHQgKiB2aWEgdHNjb25maWcgcGF0aHMpIOKAlCBub3QgYSBncmFwaCBub2RlIE5BTUUuIFRoZSBuYW1lIGlzIHRyaWVkXG5cdCAqIGFzLWlzIGZpcnN0LCB0aGVuIGl0cyB1bmRlcnNjb3Jl4oaSZG90dGVkIGZvcm0gKHRoZSBnZW5lcmF0ZWQgYWxpYXNcblx0ICogbmFtaW5nIGxhdzsgdGhlIHNhbWUgbWFwcGluZyBzY29wZXMuanNvbiB1c2VzIGZvciBhbm5vdGF0aW9ucykuXG5cdCAqIEFtYmlndWl0eSBhbmQgYWJzZW5jZSB5aWVsZCB1bmRlZmluZWQuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVBbm5vdGF0aW9uVHlwZVBhdGggKG5hbWU6IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgZGlyZWN0ID0gdGhpcy5yZXNvbHZlR3JhcGhUeXBlTmFtZShuYW1lKTtcblx0XHRpZiAoZGlyZWN0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGRpcmVjdC5ub2RlLmZ1bGxQYXRoO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9XG5cdFx0aWYgKCFuYW1lLmluY2x1ZGVzKCdfJykpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGFsaWFzZWQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKG5hbWUucmVwbGFjZSgvXy9nLCAnLicpKTtcblx0XHRpZiAoYWxpYXNlZC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSBhbGlhc2VkLm5vZGUuZnVsbFBhdGg7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSBiYXJlLWlkZW50aWZpZXIgdHlwZSBhbm5vdGF0aW9uIG9mIHRoZSBuZWFyZXN0IGVuY2xvc2luZ1xuXHQgKiBmdW5jdGlvbidzIHBhcmFtZXRlciB0aHJvdWdoIHRoZSBtbmVtb25pY2EtZ3JhcGggdGllcnMgKHZhbHVlIHNjb3BlLFxuXHQgKiBpbXBvcnRzLCByb290cywgcHJvZ3JhbS13aWRlLXVuaXF1ZSkuIE5vbi1pZGVudGlmaWVyIGFuZCBnZW5lcmljXG5cdCAqIGFubm90YXRpb25zIGFyZSBub3QgZ3JhcGggcmVmZXJlbmNlczsgYW1iaWd1aXR5IGFuZCBhYnNlbmNlIHlpZWxkXG5cdCAqIHVuZGVmaW5lZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVBhcmFtZXRlckFubm90YXRpb25UeXBlUGF0aCAobmFtZTogc3RyaW5nLCBmcm9tOiB0cy5Ob2RlKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IGZyb20ucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNGdW5jdGlvbkxpa2UoY3VycmVudCkpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBjdXJyZW50LnBhcmFtZXRlcnMgPz8gW10pIHtcblx0XHRcdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSB8fCBwYXJhbS5uYW1lLnRleHQgIT09IG5hbWUgfHwgIXBhcmFtLnR5cGUgfHxcblx0XHRcdFx0XHRcdCF0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHBhcmFtLnR5cGUpIHx8XG5cdFx0XHRcdFx0XHQhdHMuaXNJZGVudGlmaWVyKHBhcmFtLnR5cGUudHlwZU5hbWUpIHx8XG5cdFx0XHRcdFx0XHQocGFyYW0udHlwZS50eXBlQXJndW1lbnRzPy5sZW5ndGggPz8gMCkgPiAwKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Y29uc3QgcmVzb2x2ZWQgPSB0aGlzLnJlc29sdmVBbm5vdGF0aW9uVHlwZVBhdGgocGFyYW0udHlwZS50eXBlTmFtZS50ZXh0KTtcblx0XHRcdFx0XHRpZiAocmVzb2x2ZWQpIHtcblx0XHRcdFx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGMjAgY2hlYXAgdGllcjogdGhlIHdyYXAgYXJndW1lbnQgaXMgYW4gaWRlbnRpZmllciBkZWNsYXJlZCB3aXRoIGFuXG5cdCAqIEVYUExJQ0lUIHR5cGUgYW5ub3RhdGlvbiAoYGxldCB1cGRhdGVDb21taXR0ZWQ6IExlZGdlclVwZGF0ZTtgXG5cdCAqIGFzc2lnbmVkIGxhdGVyIGluIGEgZmxvdyB0aGUgYW5hbHl6ZXIgZG9lcyBub3QgdHJhY2spLiBUaGVcblx0ICogYW5ub3RhdGlvbiByZXNvbHZlcyB0aHJvdWdoIHRoZSBzYW1lIGdyYXBoIHRpZXJzIGFzIHBhcmFtZXRlclxuXHQgKiBhbm5vdGF0aW9ucy4gRGVsaWJlcmF0ZWx5IE5PVCBmbG93LXNlbnNpdGl2ZTogYW4gVU5BTk5PVEFURURcblx0ICogbGV0L3ZhciBzdGlsbCBidWNrZXRzIHVua25vd24sIGFuZCBhIGNvbnN0IHdpdGggYW4gYW5hbHl6YWJsZVxuXHQgKiBpbml0aWFsaXplciBzdGF5cyB0aGUgcmVjb21tZW5kZWQgZGlzY2lwbGluZS4gVGhlIGxvb2t1cCB3YWxrcyB0aGVcblx0ICogZW5jbG9zaW5nIHN0YXRlbWVudCBjb250YWluZXJzIGlubmVybW9zdC1vdXQsIHNvIGEgc2hhZG93aW5nIGlubmVyXG5cdCAqIGRlY2xhcmF0aW9uIHdpbnMuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVWYXJpYWJsZUFubm90YXRpb25UeXBlUGF0aCAobmFtZTogc3RyaW5nLCBmcm9tOiB0cy5Ob2RlKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IGZyb207XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGNvbnN0IHN0YXRlbWVudHM6IHRzLk5vZGVBcnJheTx0cy5TdGF0ZW1lbnQ+IHwgdW5kZWZpbmVkID1cblx0XHRcdFx0dHMuaXNCbG9jayhjdXJyZW50KSB8fCB0cy5pc01vZHVsZUJsb2NrKGN1cnJlbnQpIHx8IHRzLmlzU291cmNlRmlsZShjdXJyZW50KVxuXHRcdFx0XHRcdD8gY3VycmVudC5zdGF0ZW1lbnRzXG5cdFx0XHRcdFx0OiB0cy5pc0Nhc2VDbGF1c2UoY3VycmVudCkgfHwgdHMuaXNEZWZhdWx0Q2xhdXNlKGN1cnJlbnQpXG5cdFx0XHRcdFx0XHQ/IGN1cnJlbnQuc3RhdGVtZW50c1xuXHRcdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cdFx0XHRpZiAoc3RhdGVtZW50cykge1xuXHRcdFx0XHRjb25zdCByZXNvbHZlZCA9IHRoaXMuZmluZEFubm90YXRlZFZhcmlhYmxlVHlwZVBhdGgoc3RhdGVtZW50cywgbmFtZSk7XG5cdFx0XHRcdGlmIChyZXNvbHZlZCkge1xuXHRcdFx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpcnN0IHZhcmlhYmxlIGRlY2xhcmF0aW9uIGNhcnJ5aW5nIGFuIGV4cGxpY2l0IGJhcmUtaWRlbnRpZmllciB0eXBlXG5cdCAqIGFubm90YXRpb24gZm9yIGBuYW1lYCBpbiB0aGUgZ2l2ZW4gc3RhdGVtZW50IGxpc3QsIHJlc29sdmVkIHRocm91Z2hcblx0ICogdGhlIGdyYXBoIGxhdy5cblx0ICovXG5cdHByaXZhdGUgZmluZEFubm90YXRlZFZhcmlhYmxlVHlwZVBhdGggKFxuXHRcdHN0YXRlbWVudHM6IHJlYWRvbmx5IHRzLlN0YXRlbWVudFtdLFxuXHRcdG5hbWU6IHN0cmluZ1xuXHQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIHN0YXRlbWVudHMpIHtcblx0XHRcdGlmICghdHMuaXNWYXJpYWJsZVN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBkZWNsYXJhdGlvbiBvZiBzdGF0ZW1lbnQuZGVjbGFyYXRpb25MaXN0LmRlY2xhcmF0aW9ucykge1xuXHRcdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihkZWNsYXJhdGlvbi5uYW1lKSB8fCBkZWNsYXJhdGlvbi5uYW1lLnRleHQgIT09IG5hbWUgfHxcblx0XHRcdFx0XHQhZGVjbGFyYXRpb24udHlwZSB8fFxuXHRcdFx0XHRcdCF0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKGRlY2xhcmF0aW9uLnR5cGUpIHx8XG5cdFx0XHRcdFx0IXRzLmlzSWRlbnRpZmllcihkZWNsYXJhdGlvbi50eXBlLnR5cGVOYW1lKSB8fFxuXHRcdFx0XHRcdChkZWNsYXJhdGlvbi50eXBlLnR5cGVBcmd1bWVudHM/Lmxlbmd0aCA/PyAwKSA+IDApIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCByZXNvbHZlZCA9IHRoaXMucmVzb2x2ZUFubm90YXRpb25UeXBlUGF0aChkZWNsYXJhdGlvbi50eXBlLnR5cGVOYW1lLnRleHQpO1xuXHRcdFx0XHRpZiAocmVzb2x2ZWQpIHtcblx0XHRcdFx0XHRyZXR1cm4gcmVzb2x2ZWQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgd3JhcCgpIGFyZ3VtZW50IHRvIGl0cyBmdW5jdGlvbiBub2RlIHdpdGhvdXQgdGhlIHR5cGVcblx0ICogY2hlY2tlcjogZGlyZWN0IGZ1bmN0aW9uIGV4cHJlc3Npb25zL2Fycm93cywgb3Igc2FtZS1maWxlIGJpbmRpbmdzXG5cdCAqIChgY29uc3QgZm4gPSAoKSA9PiAuLi5gLCBgZnVuY3Rpb24gZm4oKSAuLi5gKS4gQmVzdCBlZmZvcnQg4oCUIG1ldGhvZFxuXHQgKiByZWZlcmVuY2VzLCAuYmluZCgpIHByb2R1Y3RzIGFuZCBjcm9zcy1maWxlIGlkZW50aWZpZXJzIHN0YXlcblx0ICogdW5yZXNvbHZlZDsgdGhlIGNhbGxzaXRlIGVudHJ5IGl0c2VsZiBpcyBzdGlsbCByZWNvcmRlZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUZ1bmN0aW9uQXJndW1lbnQgKFxuXHRcdGFyZzogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlXG5cdCk6IHRzLkZ1bmN0aW9uTGlrZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIWFyZykge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihhcmcpIHx8IHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdHJldHVybiBhcmc7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0Y29uc3Qga2V5ID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX0jJHthcmcudGV4dH1gO1xuXHRcdFx0Y29uc3QgYm91bmQgPSB0aGlzLmZ1bmN0aW9uQmluZGluZ3MuZ2V0KGtleSk7XG5cdFx0XHRpZiAoYm91bmQpIHtcblx0XHRcdFx0cmV0dXJuIGJvdW5kO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEFuYWx5c2UgYSB3cmFwcGVkIGZ1bmN0aW9uJ3MgYm9keSBmb3IgZ3VhcmFudGVlZCBydW50aW1lIHBhdGhzOlxuXHQgKiBkaXZlIHdyYXBzIHJldHVybmVkIGZ1bmN0aW9ucyBhcyB3ZWxsIChyZWN1cnNpdmVseSksIHNvIGVhY2hcblx0ICogZnVuY3Rpb24tdmFsdWVkIHJldHVybiBpcyBhIG5lc3RlZCB3cmFwIHNpdGUsIGFuZCBlYWNoIGBuZXcgVHlwZSgpYFxuXHQgKiBpbnNpZGUgdGhlIGJvZHkgbWVhbnMgdGhlIHBhdGggaGl0cyB0aGF0IHR5cGUncyBjb25zdHJ1Y3RvciAod2hpY2hcblx0ICogYXR0YWNoSG9va3Mgd3JhcHMgdG9vKS4gQm90aCBmYWN0cyBhcmUgMTAwJSBlbnN1cmVkLCBzbyB0aGV5IGFyZVxuXHQgKiByZWNvcmRlZCBBb1QuIE5lc3RlZCBmdW5jdGlvbiBib2RpZXMgYXJlIE5PVCB3YWxrZWQgaGVyZSDigJQgdGhleVxuXHQgKiBiZWxvbmcgdG8gdGhlaXIgb3duIHdyYXAgYW5hbHlzaXMsIHJlYWNoZWQgdmlhIHRoZSByZXR1cm4gY2hhaW4uXG5cdCAqIERlcHRoLWNhcHBlZCBhbmQgY3ljbGUtZ3VhcmRlZC5cblx0ICovXG5cdHByaXZhdGUgYW5hbHl6ZVdyYXBwZWRCb2R5IChcblx0XHRmbjogdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb24sXG5cdFx0dmlhTG9jYXRpb246IHN0cmluZyxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdGRlcHRoOiBudW1iZXIsXG5cdFx0dmlzaXRlZDogU2V0PHRzLk5vZGU+LFxuXHRcdGNyZWF0ZXNUeXBlczogU2V0PHN0cmluZz4sXG5cdFx0ZmFsbGJhY2tTY29wZT86IHN0cmluZ1xuXHQpOiB2b2lkIHtcblx0XHRpZiAoZGVwdGggPiA1IHx8IHZpc2l0ZWQuaGFzKGZuKSB8fCAhZm4uYm9keSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR2aXNpdGVkLmFkZChmbik7XG5cblx0XHQvLyBBcnJvdyB3aXRoIGV4cHJlc3Npb24gYm9keTogaW1wbGljaXQgcmV0dXJuXG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihmbikgJiYgIXRzLmlzQmxvY2soZm4uYm9keSkpIHtcblx0XHRcdHRoaXMucmVjb3JkV3JhcHBlZFJldHVybihmbi5ib2R5LCB2aWFMb2NhdGlvbiwgc291cmNlRmlsZSwgZGVwdGgsIHZpc2l0ZWQsIGZhbGxiYWNrU2NvcGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHdhbGsgPSAobm9kZTogdHMuTm9kZSk6IHZvaWQgPT4ge1xuXHRcdFx0aWYgKG5vZGUgIT09IGZuLmJvZHkgJiYgKFxuXHRcdFx0XHR0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihub2RlKSB8fFxuXHRcdFx0XHR0cy5pc0Fycm93RnVuY3Rpb24obm9kZSkgfHxcblx0XHRcdFx0dHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKG5vZGUpIHx8XG5cdFx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24obm9kZSlcblx0XHRcdCkpIHtcblx0XHRcdFx0Ly8gbmVzdGVkIGZ1bmN0aW9uIGJvZGllcyBhcmUgYW5hbHlzZWQgdGhyb3VnaCB0aGUgcmV0dXJuIGNoYWluXG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRXcmFwcGVkUmV0dXJuKG5vZGUuZXhwcmVzc2lvbiwgdmlhTG9jYXRpb24sIHNvdXJjZUZpbGUsIGRlcHRoLCB2aXNpdGVkLCBmYWxsYmFja1Njb3BlKTtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc05ld0V4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdFx0Y29uc3QgY3JlYXRlZCA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbikgfHxcblx0XHRcdFx0XHQodHMuaXNJZGVudGlmaWVyKG5vZGUuZXhwcmVzc2lvbikgJiYgdGhpcy5kZWZpbml0aW9ucy5oYXMobm9kZS5leHByZXNzaW9uLnRleHQpXG5cdFx0XHRcdFx0XHQ/IG5vZGUuZXhwcmVzc2lvbi50ZXh0XG5cdFx0XHRcdFx0XHQ6IHVuZGVmaW5lZCk7XG5cdFx0XHRcdGlmIChjcmVhdGVkKSB7XG5cdFx0XHRcdFx0Y3JlYXRlc1R5cGVzLmFkZChjcmVhdGVkKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdFx0Y29uc3QgbmVzdGVkTmFtZSA9IHRoaXMuZ2V0RnVuY3Rpb25OYW1lKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHRcdGlmIChcblx0XHRcdFx0XHRuZXN0ZWROYW1lID09PSAnd3JhcCcgfHxcblx0XHRcdFx0XHRuZXN0ZWROYW1lID09PSAnd3JhcENvbnN0cnVjdG9yQXJnJyB8fFxuXHRcdFx0XHRcdG5lc3RlZE5hbWUgPT09ICd1cGdyYWRlQ29uc3RydWN0b3JBcmcnIHx8XG5cdFx0XHRcdFx0bmVzdGVkTmFtZSA9PT0gJ3dyYXBJbnN0YW5jZU1ldGhvZHMnXG5cdFx0XHRcdCkge1xuXHRcdFx0XHRcdC8vIHRoZSBuZXN0ZWQgY2FsbCBtYXkgYWxyZWFkeSBiZSBjb2xsZWN0ZWQgKHZpc2l0ZWRcblx0XHRcdFx0XHQvLyBiZWZvcmUgdGhpcyBvdXRlciB3cmFwIHNpdGUpIOKAlCBiYWNrLXBhdGNoIGl0cyBlbnRyeSxcblx0XHRcdFx0XHQvLyBvdGhlcndpc2UgbGVhdmUgdGhlIGxpbmsgKHdpdGggdGhpcyBzaXRlJ3Mgc2NvcGUpIGZvclxuXHRcdFx0XHRcdC8vIGNvbGxlY3RFRFMgdG8gcGljayB1cFxuXHRcdFx0XHRcdGNvbnN0IG5lc3RlZEVudHJ5ID0gdGhpcy53cmFwRW50cnlCeU5vZGUuZ2V0KG5vZGUpO1xuXHRcdFx0XHRcdGlmIChuZXN0ZWRFbnRyeSkge1xuXHRcdFx0XHRcdFx0bmVzdGVkRW50cnkudmlhID0gdmlhTG9jYXRpb247XG5cdFx0XHRcdFx0XHRpZiAobmVzdGVkRW50cnkuc2NvcGUgPT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRcdFx0XHRuZXN0ZWRFbnRyeS5zY29wZSA9IGZhbGxiYWNrU2NvcGU7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHRcdHRoaXMubmVzdGVkV3JhcFZpYS5zZXQobm9kZSwgeyB2aWEgOiB2aWFMb2NhdGlvbiwgc2NvcGUgOiBmYWxsYmFja1Njb3BlIH0pO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIHdhbGspO1xuXHRcdH07XG5cdFx0d2Fsayhmbi5ib2R5KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgb25lIGZ1bmN0aW9uLXZhbHVlZCByZXR1cm4gb2YgYSB3cmFwcGVkIGJvZHkgYXMgYSBuZXN0ZWQgd3JhcFxuXHQgKiBzaXRlIChgdmlhYCA9IHRoZSBzaXRlIHdob3NlIHdyYXBwaW5nIGNhdXNlZCBpdCkgYW5kIHJlY3Vyc2UgaW50b1xuXHQgKiBpdHMgb3duIHJldHVybnMuIFJldHVybnMgdGhyb3VnaCBpZGVudGlmaWVycyByZXNvbHZlIHRocm91Z2ggdGhlXG5cdCAqIHNhbWUtZmlsZSBiaW5kaW5ncyB0YWJsZTsgdW5yZXNvbHZhYmxlIHJldHVybnMgYXJlIHNpbXBseSBza2lwcGVkLlxuXHQgKiBBIHJldHVybiBkZWNsYXJlZCBvdXRzaWRlIGFueSB0eXBlIHNjb3BlIGluaGVyaXRzIHRoZSBjYXVzaW5nIHdyYXBcblx0ICogc2l0ZSdzIHNjb3BlIGF0dHJpYnV0aW9uICh0aGUgZ2VuZXJhdGlvbiBjaGFpbiBpcyB0aGUgb25seSBob2xkZXIpLlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmRXcmFwcGVkUmV0dXJuIChcblx0XHRleHByOiB0cy5FeHByZXNzaW9uLFxuXHRcdHZpYUxvY2F0aW9uOiBzdHJpbmcsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRkZXB0aDogbnVtYmVyLFxuXHRcdHZpc2l0ZWQ6IFNldDx0cy5Ob2RlPixcblx0XHRmYWxsYmFja1Njb3BlPzogc3RyaW5nXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IHJldHVybmVkID0gdGhpcy5yZXNvbHZlRnVuY3Rpb25Bcmd1bWVudChleHByLCBzb3VyY2VGaWxlKTtcblx0XHRpZiAoIXJldHVybmVkKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRyZXR1cm5lZC5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gcmV0dXJuZWQuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXHRcdGNvbnN0IHNjb3BlID0gdGhpcy5yZXNvbHZlRURTU2NvcGUocmV0dXJuZWQpID8/IGZhbGxiYWNrU2NvcGU7XG5cdFx0Y29uc3QgZW50cnkgPSB0aGlzLmFkZEVEUyhzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCA6ICd3cmFwJyxcblx0XHRcdGNvZGUsXG5cdFx0XHRzY29wZSxcblx0XHRcdHZpYSAgOiB2aWFMb2NhdGlvbixcblx0XHRcdC8vIGRpdmUgd3JhcHMgcmV0dXJuZWQgZnVuY3Rpb25zIHRocm91Z2ggdGhlIHNhbWUgd3JhcCBtYWNoaW5lcnlcblx0XHRcdGZuICAgOiAnd3JhcCcsXG5cdFx0fSk7XG5cdFx0Ly8gdGhlIHJldHVybmVkIGZ1bmN0aW9uJ3Mgb3duIHJldHVybnMgYXJlIHdyYXBwZWQgaW4gdHVybjsgYHZpYWBcblx0XHQvLyBjaGFpbnMgdG8gdGhpcyBuZXN0ZWQgZW50cnkncyBsb2NhdGlvblxuXHRcdGNvbnN0IG5lc3RlZENyZWF0ZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHR0aGlzLmFuYWx5emVXcmFwcGVkQm9keShyZXR1cm5lZCwgbG9jYXRpb24sIHNvdXJjZUZpbGUsIGRlcHRoICsgMSwgdmlzaXRlZCwgbmVzdGVkQ3JlYXRlcywgc2NvcGUpO1xuXHRcdGlmIChuZXN0ZWRDcmVhdGVzLnNpemUgPiAwKSB7XG5cdFx0XHRlbnRyeS5jcmVhdGVzVHlwZXMgPSBBcnJheS5mcm9tKG5lc3RlZENyZWF0ZXMpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBBZGQgYW4gRURTIHVzYWdlIHRvIHRoZSBjb2xsZWN0aW9uXG5cdCAqIFJldHVybnMgdGhlIHN0b3JlZCBlbnRyeSAodGhlIGV4aXN0aW5nIG9uZSB3aGVuIHRoaXMgaXMgYSBkdXBsaWNhdGUpLFxuXHQgKiBzbyBjYWxsZXJzIGNhbiBlbnJpY2ggaXQgYWZ0ZXIgbmVzdGVkIGJvZHkgYW5hbHlzaXMuXG5cdCAqL1xuXHRwcml2YXRlIGFkZEVEUyAodHlwZVBhdGg6IHN0cmluZywgaW5mbzogRURTSW5mbyk6IEVEU0luZm8ge1xuXHRcdGlmICghdGhpcy5lZHNVc2FnZXMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0dGhpcy5lZHNVc2FnZXMuc2V0KHR5cGVQYXRoLCBbXSk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZXhpc3RpbmcgPSB0aGlzLmVkc1VzYWdlcy5nZXQodHlwZVBhdGgpITtcblx0XHRjb25zdCBkdXBsaWNhdGUgPSBleGlzdGluZy5maW5kKGUgPT4ge1xuXHRcdFx0cmV0dXJuIGUubG9jYXRpb24gPT09IGluZm8ubG9jYXRpb24gJiZcblx0XHRcdFx0ZS5raW5kID09PSBpbmZvLmtpbmQgJiZcblx0XHRcdFx0ZS5jb2RlID09PSBpbmZvLmNvZGU7XG5cdFx0fSk7XG5cblx0XHRpZiAoZHVwbGljYXRlKSB7XG5cdFx0XHRyZXR1cm4gZHVwbGljYXRlO1xuXHRcdH1cblx0XHRleGlzdGluZy5wdXNoKGluZm8pO1xuXHRcdHJldHVybiBpbmZvO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgbmF0aXZlIGZsb3cgcGF0dGVybnMgKGluc3RhbmNlIHVzYWdlIGFmdGVyIGNyZWF0aW9uKVxuXHQgKiBQaGFzZSAxOiBwcm9wZXJ0eSBhY2Nlc3MsIG1ldGhvZCBjYWxscywgYXJndW1lbnRzLCByZXR1cm4sIGRlc3RydWN0dXJpbmcsIGV0Yy5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3cgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHQvLyBQcm9wZXJ0eSByZWFkOiB1c2VyLm5hbWUgb3IgdXNlcj8ubmFtZVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd1Byb3BlcnR5QWNjZXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEVsZW1lbnQgYWNjZXNzOiB1c2VyWyduYW1lJ11cblx0XHRpZiAodHMuaXNFbGVtZW50QWNjZXNzRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0VsZW1lbnRBY2Nlc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgd3JpdGU6IHVzZXIubmFtZSA9IHZhbHVlXG5cdFx0aWYgKHRzLmlzQmluYXJ5RXhwcmVzc2lvbihub2RlKSAmJiBub2RlLm9wZXJhdG9yVG9rZW4ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0Fzc2lnbm1lbnQobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gTWV0aG9kIGNhbGw6IHVzZXIudmFsaWRhdGUoKSAgQU5EICBhcmd1bWVudCBwYXNzaW5nOiBwcm9jZXNzVXNlcih1c2VyKVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd01ldGhvZENhbGwobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93QXJndW1lbnRQYXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIERlc3RydWN0dXJlIHJlYWQ6IGNvbnN0IHsgbmFtZSB9ID0gdXNlclxuXHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgJiYgbm9kZS5pbml0aWFsaXplcikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0Rlc3RydWN0dXJlKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFJldHVybiBpbnN0YW5jZTogcmV0dXJuIHVzZXJcblx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQobm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93UmV0dXJuKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFNwcmVhZDogeyAuLi51c2VyIH1cblx0XHRpZiAodHMuaXNTcHJlYWRFbGVtZW50KG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93U3ByZWFkKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IHByb3BlcnR5IGFjY2VzcyBmbG93IChyZWFkIG9yIGNvbmRpdGlvbmFsKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd1Byb3BlcnR5QWNjZXNzIChub2RlOiB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBwcm9wTmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIFNraXAgaWYgdGhpcyBpcyBhIHR5cGUgY29uc3RydWN0b3IgYWNjZXNzIChlLmcuLCBVc2VyVHlwZS5kZWZpbmUpXG5cdFx0aWYgKHByb3BOYW1lID09PSAnZGVmaW5lJyB8fCBwcm9wTmFtZSA9PT0gJ2xhenknKSB7IHJldHVybjsgfVxuXG5cdFx0dGhpcy5hZGRGbG93KG9iamVjdFR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICAgIDogJ3Byb3BlcnR5UmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0cHJvcGVydHlOYW1lIDogcHJvcE5hbWUsXG5cdFx0XHR0YXJnZXRUeXBlICAgOiBvYmplY3RUeXBlXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBlbGVtZW50IGFjY2VzcyBmbG93OiB1c2VyWyduYW1lJ11cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dFbGVtZW50QWNjZXNzIChub2RlOiB0cy5FbGVtZW50QWNjZXNzRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnZWxlbWVudEFjY2VzcycsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGFzc2lnbm1lbnQgZmxvdzogdXNlci5uYW1lID0gdmFsdWUgb3IgdXNlciA9IG90aGVyXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93QXNzaWdubWVudCAobm9kZTogdHMuQmluYXJ5RXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIFByb3BlcnR5IHdyaXRlOiB1c2VyLm5hbWUgPSB2YWx1ZVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmxlZnQpKSB7XG5cdFx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5sZWZ0LmV4cHJlc3Npb24pO1xuXHRcdFx0aWYgKCFvYmplY3RUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0XHRjb25zdCBwcm9wTmFtZSA9IG5vZGUubGVmdC5uYW1lLnRleHQ7XG5cdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdCk7XG5cdFx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCAgICAgICAgIDogJ3Byb3BlcnR5V3JpdGUnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRwcm9wZXJ0eU5hbWUgOiBwcm9wTmFtZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSAgIDogb2JqZWN0VHlwZVxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gVmFyaWFibGUgcmVhc3NpZ25tZW50OiB1c2VyID0gb3RoZXJcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG5vZGUubGVmdCkpIHtcblx0XHRcdGNvbnN0IHZhck5hbWUgPSBub2RlLmxlZnQudGV4dDtcblx0XHRcdGNvbnN0IG1hcHBlZFR5cGUgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldCh2YXJOYW1lKTtcblx0XHRcdGlmICghbWFwcGVkVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHQpO1xuXHRcdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdFx0dGhpcy5hZGRGbG93KG1hcHBlZFR5cGUsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAncmVhc3NpZ25tZW50Jyxcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSA6IG1hcHBlZFR5cGVcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IG1ldGhvZCBjYWxsIGZsb3c6IHVzZXIudmFsaWRhdGUoKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd01ldGhvZENhbGwgKG5vZGU6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3Qgb2JqZWN0VHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbi5leHByZXNzaW9uKTtcblx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBtZXRob2ROYW1lID0gbm9kZS5leHByZXNzaW9uLm5hbWUudGV4dDtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHQvLyBTa2lwIGlmIHRoaXMgaXMgYSB0eXBlIGNvbnN0cnVjdG9yIGNhbGwgKGUuZy4sIG5ldyBVc2VyVHlwZSgpKVxuXHRcdGlmIChtZXRob2ROYW1lID09PSAnZGVmaW5lJyB8fCBtZXRob2ROYW1lID09PSAnbGF6eScpIHsgcmV0dXJuOyB9XG5cblx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgICAgOiAnbWV0aG9kQ2FsbCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0cHJvcGVydHlOYW1lIDogbWV0aG9kTmFtZSxcblx0XHRcdHRhcmdldFR5cGUgICA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGFyZ3VtZW50IHBhc3NpbmcgZmxvdzogcHJvY2Vzc1VzZXIodXNlcilcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dBcmd1bWVudFBhc3MgKG5vZGU6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuXHRcdFx0Y29uc3QgYXJnID0gbm9kZS5hcmd1bWVudHNbIGkgXTtcblx0XHRcdGNvbnN0IGFyZ1R5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShhcmcpO1xuXHRcdFx0aWYgKCFhcmdUeXBlKSB7IGNvbnRpbnVlOyB9XG5cblx0XHRcdGNvbnN0IGZ1bmNOYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKSB8fCAnYW5vbnltb3VzJztcblx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0KTtcblx0XHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRcdHRoaXMuYWRkRmxvdyhhcmdUeXBlLCB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgIDogJ3Bhc3NBc0FyZycsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHRhcmdldFR5cGUgOiBhcmdUeXBlLFxuXHRcdFx0XHRjb250ZXh0ICAgIDogYGFyZyAke2l9IHRvICR7ZnVuY05hbWV9YFxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgZGVzdHJ1Y3R1cmluZyBmbG93OiBjb25zdCB7IG5hbWUgfSA9IHVzZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dEZXN0cnVjdHVyZSAobm9kZTogdHMuVmFyaWFibGVEZWNsYXJhdGlvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNPYmplY3RCaW5kaW5nUGF0dGVybihub2RlLm5hbWUpKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3Qgc291cmNlVHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuaW5pdGlhbGl6ZXIhKTtcblx0XHRpZiAoIXNvdXJjZVR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHQvLyBFeHRyYWN0IGRlc3RydWN0dXJlZCBwcm9wZXJ0eSBuYW1lc1xuXHRcdGNvbnN0IHByb3BzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBub2RlLm5hbWUuZWxlbWVudHMpIHtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZWxlbWVudC5uYW1lKSkge1xuXHRcdFx0XHRwcm9wcy5wdXNoKGVsZW1lbnQubmFtZS50ZXh0KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHR0aGlzLmFkZEZsb3coc291cmNlVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ2Rlc3RydWN0dXJlUmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHNvdXJjZVR5cGUsXG5cdFx0XHRjb250ZXh0ICAgIDogcHJvcHMuam9pbignLCAnKVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgcmV0dXJuIGZsb3c6IHJldHVybiB1c2VyXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93UmV0dXJuIChub2RlOiB0cy5SZXR1cm5TdGF0ZW1lbnQsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCByZXR1cm5UeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uISk7XG5cdFx0aWYgKCFyZXR1cm5UeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0dGhpcy5hZGRGbG93KHJldHVyblR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICA6ICdyZXR1cm4nLFxuXHRcdFx0Y29kZSxcblx0XHRcdHRhcmdldFR5cGUgOiByZXR1cm5UeXBlXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBzcHJlYWQgZmxvdzogeyAuLi51c2VyIH1cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dTcHJlYWQgKG5vZGU6IHRzLlNwcmVhZEVsZW1lbnQsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCBzcHJlYWRUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIXNwcmVhZFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHR0aGlzLmFkZEZsb3coc3ByZWFkVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ3NwcmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHNwcmVhZFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHR5cGUgZnJvbSBhbiBleHByZXNzaW9uIChpZGVudGlmaWVyLCBwcm9wZXJ0eSBhY2Nlc3MsIGV0Yy4pXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVFeHByZXNzaW9uVHlwZSAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gSWRlbnRpZmllcjogdXNlclxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChleHByLnRleHQpO1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2VzczogdXNlci5uYW1lIChyZXR1cm4gb2JqZWN0IHR5cGUsIG5vdCBwcm9wZXJ0eSB0eXBlKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKGV4cHIuZXhwcmVzc2lvbik7XG5cdFx0fVxuXG5cdFx0Ly8gRWxlbWVudCBhY2Nlc3M6IHVzZXJbJ25hbWUnXVxuXHRcdGlmICh0cy5pc0VsZW1lbnRBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUoZXhwci5leHByZXNzaW9uKTtcblx0XHR9XG5cblx0XHQvLyBUaGlzIGV4cHJlc3Npb246IHRoaXMgKGlmIGluIGEgbWV0aG9kLCB3ZSBjYW4ndCByZXNvbHZlIHdpdGhvdXQgbW9yZSBjb250ZXh0KVxuXHRcdGlmIChleHByLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBBZGQgYSBmbG93IHVzYWdlIHRvIHRoZSBjb2xsZWN0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGFkZEZsb3cgKHR5cGVQYXRoOiBzdHJpbmcsIGluZm86IEZsb3dJbmZvKTogdm9pZCB7XG5cdFx0aWYgKCF0aGlzLmZsb3dVc2FnZXMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0dGhpcy5mbG93VXNhZ2VzLnNldCh0eXBlUGF0aCwgW10pO1xuXHRcdH1cblxuXHRcdGNvbnN0IGV4aXN0aW5nID0gdGhpcy5mbG93VXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGlzRHVwbGljYXRlID0gZXhpc3Rpbmcuc29tZShlID0+IHtcblx0XHRcdHJldHVybiBlLmxvY2F0aW9uID09PSBpbmZvLmxvY2F0aW9uICYmXG5cdFx0XHRcdGUua2luZCA9PT0gaW5mby5raW5kICYmXG5cdFx0XHRcdGUuY29kZSA9PT0gaW5mby5jb2RlO1xuXHRcdH0pO1xuXG5cdFx0aWYgKCFpc0R1cGxpY2F0ZSkge1xuXHRcdFx0ZXhpc3RpbmcucHVzaChpbmZvKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHRcdCogR2V0IHR5cGUgbmFtZSBmcm9tIGV4cHJlc3Npb24gKGlkZW50aWZpZXIgb3IgcHJvcGVydHkgYWNjZXNzKVxuXHRcdFx0Ki9cblx0cHJpdmF0ZSBnZXRUeXBlTmFtZUZyb21FeHByZXNzaW9uIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBuYW1lID0gZXhwci50ZXh0O1xuXHRcdFx0Ly8gQ2hlY2sgaWYgdGhpcyBpZGVudGlmaWVyIGlzIGEgdmFyaWFibGUgbWFwcGVkIHRvIGEgdHlwZSAoZS5nLiwgZnJvbSBsb29rdXApXG5cdFx0XHRjb25zdCBtYXBwZWRUeXBlID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0XHRpZiAobWFwcGVkVHlwZSkge1xuXHRcdFx0XHRyZXR1cm4gbWFwcGVkVHlwZTtcblx0XHRcdH1cblx0XHRcdHJldHVybiBuYW1lO1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKGV4cHIpO1xuXHRcdFx0cmV0dXJuIGNoYWluLmpvaW4oJy4nKTtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXHRcblx0LyoqXG5cdCAqIFRoZSBvbmUgY2FuZGlkYXRlIHdob3NlIHBhcmVudCB0eXBlIGlzIGRlZmluZWQgaW4gYGZpbGVOYW1lYCwgb3Jcblx0ICogdW5kZWZpbmVkIHdoZW4gbm9uZSBvciBzZXZlcmFsIHF1YWxpZnkuXG5cdCAqL1xuXHRwcml2YXRlIHN1YnR5cGVPd25lZEJ5RmlsZSAoY2FuZGlkYXRlczogc3RyaW5nW10sIGZpbGVOYW1lOiBzdHJpbmcpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGZpbGUgPSBub2RlUGF0aC5yZXNvbHZlKGZpbGVOYW1lKTtcblx0XHRjb25zdCBvd25lZCA9IGNhbmRpZGF0ZXMuZmlsdGVyKChjYW5kaWRhdGUpID0+IHtcblx0XHRcdGNvbnN0IHBhcmVudCA9IHRoaXMuZGVmaW5pdGlvbnMuZ2V0KGNhbmRpZGF0ZSk/LnBhcmVudDtcblx0XHRcdGNvbnN0IHBhcmVudExvY2F0aW9uID0gcGFyZW50ID8gdGhpcy5kZWZpbml0aW9ucy5nZXQocGFyZW50KT8ubG9jYXRpb24gOiB1bmRlZmluZWQ7XG5cdFx0XHRjb25zdCBwYXJlbnRGaWxlID0gcGFyZW50TG9jYXRpb24gPyBwYXJlbnRMb2NhdGlvbi5yZXBsYWNlKC86XFxkKzpcXGQrJC8sICcnKSA6IHVuZGVmaW5lZDtcblx0XHRcdGNvbnN0IGluRmlsZSA9IHBhcmVudEZpbGUgIT09IHVuZGVmaW5lZCAmJiBub2RlUGF0aC5yZXNvbHZlKHBhcmVudEZpbGUpID09PSBmaWxlO1xuXHRcdFx0cmV0dXJuIGluRmlsZTtcblx0XHR9KTtcblx0XHRjb25zdCByZXN1bHQgPSBvd25lZC5sZW5ndGggPT09IDEgPyBvd25lZFsgMCBdIDogdW5kZWZpbmVkO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHRcdCogUmVzb2x2ZSBmdWxsIHR5cGUgcGF0aCBmcm9tIHByb3BlcnR5IGFjY2Vzc1xuXHRcdFx0Ki9cblx0cHJpdmF0ZSByZXNvbHZlVHlwZVBhdGggKGV4cHI6IHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4oZXhwcik7XG5cdFx0aWYgKGNoYWluLmxlbmd0aCA9PT0gMCkgcmV0dXJuIHVuZGVmaW5lZDtcblx0XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBjaGFpbiBtYXRjaGVzIGEga25vd24gdHlwZVxuXHRcdGNvbnN0IGZ1bGxQYXRoID0gY2hhaW4uam9pbignLicpO1xuXHRcdGlmICh0aGlzLmRlZmluaXRpb25zLmhhcyhmdWxsUGF0aCkpIHtcblx0XHRcdHJldHVybiBmdWxsUGF0aDtcblx0XHR9XG5cdFxuXHRcdC8vIEluc3RhbmNlIHJlY2VpdmVyOiBgbGVzc29uLk5hdGl2ZWAgd2hlcmUgYGxlc3NvbmAgaXMgYm91bmQgdG8gYVxuXHRcdC8vIFJ1bi5MZXNzb24gaW5zdGFuY2UgbWVhbnMgUnVuLkxlc3Nvbi5OYXRpdmUg4oCUIHJlc29sdmUgdGhyb3VnaCB0aGVcblx0XHQvLyB2YXJpYWJsZSdzIHR5cGUgYmVmb3JlIGZhbGxpbmcgYmFjayB0byB0aGUgYmFyZSBuYW1lXG5cdFx0aWYgKGNoYWluLmxlbmd0aCA+IDEpIHtcblx0XHRcdGNvbnN0IHJlY2VpdmVyVHlwZSA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGNoYWluWyAwIF0pO1xuXHRcdFx0Y29uc3QgdmlhUmVjZWl2ZXIgPSByZWNlaXZlclR5cGUgPyBgJHtyZWNlaXZlclR5cGV9LiR7Y2hhaW4uc2xpY2UoMSkuam9pbignLicpfWAgOiB1bmRlZmluZWQ7XG5cdFx0XHRpZiAodmlhUmVjZWl2ZXIgJiYgdGhpcy5kZWZpbml0aW9ucy5oYXModmlhUmVjZWl2ZXIpKSB7XG5cdFx0XHRcdHJldHVybiB2aWFSZWNlaXZlcjtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBUcnkganVzdCB0aGUgcHJvcGVydHkgbmFtZVxuXHRcdGNvbnN0IHByb3BOYW1lID0gY2hhaW5bIGNoYWluLmxlbmd0aCAtIDEgXTtcblx0XHRjb25zdCBjYW5kaWRhdGVzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgWyBwYXRoIF0gb2YgdGhpcy5kZWZpbml0aW9ucykge1xuXHRcdFx0aWYgKHBhdGguZW5kc1dpdGgoYC4ke3Byb3BOYW1lfWApIHx8IHBhdGggPT09IHByb3BOYW1lKSB7XG5cdFx0XHRcdGNhbmRpZGF0ZXMucHVzaChwYXRoKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0Ly8gU2V2ZXJhbCB0eXBlcyBzaGFyZSB0aGUgbmFtZSAoQ29ycmVjdC5TdGF0VXBkYXRlIGFuZFxuXHRcdC8vIE1pc3Rha2UuU3RhdFVwZGF0ZSk6IGBuZXcgdGhpcy5TdGF0VXBkYXRlKClgIGluc2lkZSBhIHR5cGUncyBvd25cblx0XHQvLyBmaWxlIG1lYW5zIFRIQVQgdHlwZSdzIHN1YnR5cGUg4oCUIHByZWZlciB0aGUgY2FuZGlkYXRlIHdob3NlIHBhcmVudFxuXHRcdC8vIGlzIGRlZmluZWQgaW4gdGhlIGZpbGUgdGhlIGFjY2VzcyBzaXRzIGluICh0b3BvbG9naWNhOiBvbmUgZmlsZVxuXHRcdC8vIHBlciB0eXBlKS4gT3RoZXJ3aXNlIHRoZSBmaXJzdCBtYXRjaCwgYXMgYmVmb3JlLlxuXHRcdGlmIChjYW5kaWRhdGVzLmxlbmd0aCA+IDEpIHtcblx0XHRcdGNvbnN0IG93bmVkID0gdGhpcy5zdWJ0eXBlT3duZWRCeUZpbGUoY2FuZGlkYXRlcywgZXhwci5nZXRTb3VyY2VGaWxlKCkuZmlsZU5hbWUpO1xuXHRcdFx0aWYgKG93bmVkKSB7XG5cdFx0XHRcdHJldHVybiBvd25lZDtcblx0XHRcdH1cblx0XHR9XG5cdFx0aWYgKGNhbmRpZGF0ZXMubGVuZ3RoID4gMCkge1xuXHRcdFx0cmV0dXJuIGNhbmRpZGF0ZXNbIDAgXTtcblx0XHR9XG5cblx0XHRyZXR1cm4gZnVsbFBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogRXZlcnkgdHlwZSBhIGByZWNlaXZlci5TdWJgIGFjY2VzcyBjYW4gZGVub3RlLCBmb3IgdXNhZ2Vcblx0ICogYXR0cmlidXRpb246IHRoZSBleGFjdCBwYXRoLCB0aGUgcmVjZWl2ZXIncyB2YWx1ZSBiaW5kaW5nLCB0aGVcblx0ICogcmVjZWl2ZXIncyBkZWNsYXJlZCB0eXBlIChvbmUgb3Igc2V2ZXJhbCBnZW5lcmF0ZWQgdHlwZXMpLCBvciDigJRcblx0ICogd2hlbiBub25lIGFwcGxpZXMg4oCUIGV2ZXJ5IG5hbWVzYWtlLiBBIGNvbnN0cnVjdGlvbiB0aHJvdWdoIGFcblx0ICogcmVjZWl2ZXIgdGFjdGljYSBjYW5ub3QgYmluZCBpcyBuZXZlciBnaXZlbiB0byBvbmUgbmFtZXNha2Ugb25seTpcblx0ICogYSB0eXBlIGxlZnQgd2l0aG91dCB1c2FnZXMgcmVhZHMgYXMgbmV2ZXIgY29uc3RydWN0ZWQuIFRoZVxuXHQgKiBzYW1lLWZpbGUgcHJlZmVyZW5jZSAoc3VidHlwZU93bmVkQnlGaWxlKSBzdGlsbCBwaWNrcyBvbmUgbmFtZXNha2UuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVVc2FnZVR5cGVQYXRocyAoZXhwcjogdHMuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKTogVXNhZ2VUeXBlUGF0aHMge1xuXHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKGV4cHIpO1xuXHRcdGNvbnN0IGZ1bGxQYXRoID0gY2hhaW4uam9pbignLicpO1xuXHRcdGlmIChjaGFpbi5sZW5ndGggPiAwICYmIHRoaXMuZGVmaW5pdGlvbnMuaGFzKGZ1bGxQYXRoKSkge1xuXHRcdFx0Y29uc3QgZXhhY3Q6IFVzYWdlVHlwZVBhdGhzID0geyBwYXRocyA6IFsgZnVsbFBhdGggXSwgdmlhIDogJ2V4YWN0JyB9O1xuXHRcdFx0cmV0dXJuIGV4YWN0O1xuXHRcdH1cblx0XHRpZiAoY2hhaW4ubGVuZ3RoID4gMSkge1xuXHRcdFx0Y29uc3QgcmVzdCA9IGNoYWluLnNsaWNlKDEpLmpvaW4oJy4nKTtcblx0XHRcdGNvbnN0IHJlY2VpdmVyVHlwZSA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGNoYWluWyAwIF0pO1xuXHRcdFx0Y29uc3QgdmlhUmVjZWl2ZXIgPSByZWNlaXZlclR5cGUgPyBgJHtyZWNlaXZlclR5cGV9LiR7cmVzdH1gIDogdW5kZWZpbmVkO1xuXHRcdFx0aWYgKHZpYVJlY2VpdmVyICYmIHRoaXMuZGVmaW5pdGlvbnMuaGFzKHZpYVJlY2VpdmVyKSkge1xuXHRcdFx0XHRjb25zdCBib3VuZDogVXNhZ2VUeXBlUGF0aHMgPSB7IHBhdGhzIDogWyB2aWFSZWNlaXZlciBdLCB2aWEgOiAnYmluZGluZycgfTtcblx0XHRcdFx0cmV0dXJuIGJvdW5kO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgYW5ub3RhdGVkID0gdGhpcy5yZXNvbHZlUmVjZWl2ZXJBbm5vdGF0aW9uT3duZXJzKGV4cHIsIGNoYWluWyAwIF0pXG5cdFx0XHRcdC5tYXAob3duZXIgPT4gYCR7b3duZXJ9LiR7cmVzdH1gKVxuXHRcdFx0XHQuZmlsdGVyKHBhdGggPT4gdGhpcy5kZWZpbml0aW9ucy5oYXMocGF0aCkpO1xuXHRcdFx0aWYgKGFubm90YXRlZC5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdGNvbnN0IHZpYUFubm90YXRpb246IFVzYWdlVHlwZVBhdGhzID0geyBwYXRocyA6IGFubm90YXRlZCwgdmlhIDogJ2Fubm90YXRpb24nIH07XG5cdFx0XHRcdHJldHVybiB2aWFBbm5vdGF0aW9uO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zdCBwcm9wTmFtZSA9IGV4cHIubmFtZS50ZXh0O1xuXHRcdGNvbnN0IGNhbmRpZGF0ZXM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBbIHBhdGggXSBvZiB0aGlzLmRlZmluaXRpb25zKSB7XG5cdFx0XHRpZiAocGF0aC5lbmRzV2l0aChgLiR7cHJvcE5hbWV9YCkgfHwgcGF0aCA9PT0gcHJvcE5hbWUpIHtcblx0XHRcdFx0Y2FuZGlkYXRlcy5wdXNoKHBhdGgpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zdCBvd25lZCA9IGNhbmRpZGF0ZXMubGVuZ3RoID4gMVxuXHRcdFx0PyB0aGlzLnN1YnR5cGVPd25lZEJ5RmlsZShjYW5kaWRhdGVzLCBleHByLmdldFNvdXJjZUZpbGUoKS5maWxlTmFtZSlcblx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdGNvbnN0IGJ5TmFtZTogVXNhZ2VUeXBlUGF0aHMgPSB7IHBhdGhzIDogb3duZWQgPyBbIG93bmVkIF0gOiBjYW5kaWRhdGVzLCB2aWEgOiAnbmFtZScgfTtcblx0XHRyZXR1cm4gYnlOYW1lO1xuXHR9XG5cblx0LyoqXG5cdCAqIFRoZSBmdWxsUGF0aHMgb2YgdGhlIGdlbmVyYXRlZCB0eXBlcyBhIHJlY2VpdmVyJ3MgZGVjbGFyZWQgdHlwZVxuXHQgKiBuYW1lczogYGdhZGdldDogQWxwaGFfR2FkZ2V0IHwgQmV0YV9HYWRnZXRgIOKGkiBBbHBoYS5HYWRnZXQgYW5kXG5cdCAqIEJldGEuR2FkZ2V0LiBSZWFkIGZyb20gdGhlIGFubm90YXRpb24sIG5vdCBmcm9tIGEgVHlwZUNoZWNrZXIgKHRoZVxuXHQgKiBhbmFseXplciBydW5zIHdpdGhvdXQgb25lKS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVJlY2VpdmVyQW5ub3RhdGlvbk93bmVycyAoZnJvbTogdHMuTm9kZSwgbmFtZTogc3RyaW5nKTogc3RyaW5nW10ge1xuXHRcdGNvbnN0IHR5cGVOb2RlID0gdGhpcy5maW5kRGVjbGFyZWRUeXBlT2YoZnJvbSwgbmFtZSk7XG5cdFx0Y29uc3Qgb3duZXJzID0gdHlwZU5vZGVcblx0XHRcdD8gdGhpcy5jb2xsZWN0QW5ub3RhdGlvbk93bmVycyh0eXBlTm9kZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlLCBuZXcgU2V0PHN0cmluZz4oKSwgMClcblx0XHRcdDogW107XG5cdFx0Y29uc3QgdW5pcXVlID0gQXJyYXkuZnJvbShuZXcgU2V0KG93bmVycykpO1xuXHRcdHJldHVybiB1bmlxdWU7XG5cdH1cblxuXHQvKipcblx0ICogVGhlIHR5cGUgYW5ub3RhdGlvbiBvZiB0aGUgbmVhcmVzdCBkZWNsYXJhdGlvbiBvZiBgbmFtZWAgdmlzaWJsZVxuXHQgKiBmcm9tIGBmcm9tYDogYSBwYXJhbWV0ZXIgb2YgYW4gZW5jbG9zaW5nIGZ1bmN0aW9uLCBvciBhXG5cdCAqIGBjb25zdC9sZXQvdmFyYCBpbiBhbiBlbmNsb3NpbmcgYmxvY2sgb3IgdGhlIGZpbGUuIFRoZSBmaXJzdFxuXHQgKiBkZWNsYXJhdGlvbiBmb3VuZCB3aW5zIChzaGFkb3dpbmcpLCBhbm5vdGF0ZWQgb3Igbm90LlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kRGVjbGFyZWRUeXBlT2YgKGZyb206IHRzLk5vZGUsIG5hbWU6IHN0cmluZyk6IHRzLlR5cGVOb2RlIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IGZyb20ucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNGdW5jdGlvbkxpa2UoY3VycmVudCkpIHtcblx0XHRcdFx0Y29uc3QgcGFyYW0gPSBjdXJyZW50LnBhcmFtZXRlcnMuZmluZChwID0+IHRzLmlzSWRlbnRpZmllcihwLm5hbWUpICYmIHAubmFtZS50ZXh0ID09PSBuYW1lKTtcblx0XHRcdFx0aWYgKHBhcmFtKSB7XG5cdFx0XHRcdFx0Y29uc3QgcGFyYW1UeXBlID0gcGFyYW0udHlwZTtcblx0XHRcdFx0XHRyZXR1cm4gcGFyYW1UeXBlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNCbG9jayhjdXJyZW50KSB8fCB0cy5pc1NvdXJjZUZpbGUoY3VycmVudCkgfHwgdHMuaXNNb2R1bGVCbG9jayhjdXJyZW50KSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IHN0YXRlbWVudCBvZiBjdXJyZW50LnN0YXRlbWVudHMpIHtcblx0XHRcdFx0XHRpZiAoIXRzLmlzVmFyaWFibGVTdGF0ZW1lbnQoc3RhdGVtZW50KSkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdGNvbnN0IGRlY2wgPSBzdGF0ZW1lbnQuZGVjbGFyYXRpb25MaXN0LmRlY2xhcmF0aW9uc1xuXHRcdFx0XHRcdFx0LmZpbmQoZCA9PiB0cy5pc0lkZW50aWZpZXIoZC5uYW1lKSAmJiBkLm5hbWUudGV4dCA9PT0gbmFtZSk7XG5cdFx0XHRcdFx0aWYgKGRlY2wpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGRlY2xUeXBlID0gZGVjbC50eXBlO1xuXHRcdFx0XHRcdFx0cmV0dXJuIGRlY2xUeXBlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0cHJpdmF0ZSBjb2xsZWN0QW5ub3RhdGlvbk93bmVycyAoXG5cdFx0dHlwZU5vZGU6IHRzLlR5cGVOb2RlLFxuXHRcdGZyb21GaWxlOiBzdHJpbmcsXG5cdFx0dmlzaXRlZDogU2V0PHN0cmluZz4sXG5cdFx0ZGVwdGg6IG51bWJlclxuXHQpOiBzdHJpbmdbXSB7XG5cdFx0Y29uc3Qgb3duZXJzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGlmIChkZXB0aCA+IE1BWF9BTk5PVEFUSU9OX09XTkVSX0RFUFRIKSB7XG5cdFx0XHRyZXR1cm4gb3duZXJzO1xuXHRcdH1cblx0XHRpZiAodHMuaXNQYXJlbnRoZXNpemVkVHlwZU5vZGUodHlwZU5vZGUpKSB7XG5cdFx0XHRvd25lcnMucHVzaCguLi50aGlzLmNvbGxlY3RBbm5vdGF0aW9uT3duZXJzKHR5cGVOb2RlLnR5cGUsIGZyb21GaWxlLCB2aXNpdGVkLCBkZXB0aCArIDEpKTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzVW5pb25UeXBlTm9kZSh0eXBlTm9kZSkgfHwgdHMuaXNJbnRlcnNlY3Rpb25UeXBlTm9kZSh0eXBlTm9kZSkpIHtcblx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIHR5cGVOb2RlLnR5cGVzKSB7XG5cdFx0XHRcdG93bmVycy5wdXNoKC4uLnRoaXMuY29sbGVjdEFubm90YXRpb25Pd25lcnMobWVtYmVyLCBmcm9tRmlsZSwgdmlzaXRlZCwgZGVwdGggKyAxKSk7XG5cdFx0XHR9XG5cdFx0fSBlbHNlIGlmICh0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHR5cGVOb2RlKSAmJiB0cy5pc0lkZW50aWZpZXIodHlwZU5vZGUudHlwZU5hbWUpKSB7XG5cdFx0XHRvd25lcnMucHVzaCguLi50aGlzLm93bmVyc09mVHlwZU5hbWUodHlwZU5vZGUudHlwZU5hbWUudGV4dCwgZnJvbUZpbGUsIHZpc2l0ZWQsIGRlcHRoICsgMSkpO1xuXHRcdH1cblx0XHRyZXR1cm4gb3duZXJzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEEgdHlwZSBuYW1lIOKGkiB0aGUgZ2VuZXJhdGVkIHR5cGVzIGl0IHN0YW5kcyBmb3I6IGEgZ2VuZXJhdGVkXG5cdCAqIGluc3RhbmNlIGFsaWFzIGl0c2VsZiAoYW4gaW1wb3J0IHJlbmFtZSBpcyByZWFkIGJhY2sgdG8gdGhlIG9yaWdpbmFsXG5cdCAqIG5hbWUpLCBvciBhIHR5cGUgYWxpYXMgLyBpbnRlcmZhY2UgYGV4dGVuZHNgIGxlYWRpbmcgdG8gdGhlbSxcblx0ICogZm9sbG93ZWQgYWNyb3NzIGZpbGVzIGxpa2UgcmVmZXJlbmNlZCB0eXBlcyBhcmUuXG5cdCAqL1xuXHRwcml2YXRlIG93bmVyc09mVHlwZU5hbWUgKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRmcm9tRmlsZTogc3RyaW5nLFxuXHRcdHZpc2l0ZWQ6IFNldDxzdHJpbmc+LFxuXHRcdGRlcHRoOiBudW1iZXJcblx0KTogc3RyaW5nW10ge1xuXHRcdGNvbnN0IG93bmVyczogc3RyaW5nW10gPSBbXTtcblx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldChmcm9tRmlsZSk/LmdldChuYW1lKTtcblx0XHRjb25zdCBvcmlnaW5hbE5hbWUgPSBpbXBvcnRlZCAmJiAhaW1wb3J0ZWQuaXNOYW1lc3BhY2UgPyBpbXBvcnRlZC5vcmlnaW5hbE5hbWUgOiBuYW1lO1xuXHRcdGNvbnN0IGdlbmVyYXRlZCA9IHRoaXMuZmluZFBhdGhCeUVtaXR0ZWROYW1lKG9yaWdpbmFsTmFtZSk7XG5cdFx0aWYgKGdlbmVyYXRlZCkge1xuXHRcdFx0b3duZXJzLnB1c2goZ2VuZXJhdGVkKTtcblx0XHRcdHJldHVybiBvd25lcnM7XG5cdFx0fVxuXHRcdGNvbnN0IHZpc2l0S2V5ID0gYCR7ZnJvbUZpbGV9IyR7bmFtZX1gO1xuXHRcdGlmIChkZXB0aCA+IE1BWF9BTk5PVEFUSU9OX09XTkVSX0RFUFRIIHx8IHZpc2l0ZWQuaGFzKHZpc2l0S2V5KSkge1xuXHRcdFx0cmV0dXJuIG93bmVycztcblx0XHR9XG5cdFx0dmlzaXRlZC5hZGQodmlzaXRLZXkpO1xuXHRcdGNvbnN0IGRlY2wgPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKG5hbWUsIGZyb21GaWxlKTtcblx0XHRpZiAoIWRlY2wpIHtcblx0XHRcdHJldHVybiBvd25lcnM7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1R5cGVBbGlhc0RlY2xhcmF0aW9uKGRlY2wubm9kZSkpIHtcblx0XHRcdG93bmVycy5wdXNoKC4uLnRoaXMuY29sbGVjdEFubm90YXRpb25Pd25lcnMoZGVjbC5ub2RlLnR5cGUsIGRlY2wuZmlsZSwgdmlzaXRlZCwgZGVwdGggKyAxKSk7XG5cdFx0fSBlbHNlIGlmICh0cy5pc0ludGVyZmFjZURlY2xhcmF0aW9uKGRlY2wubm9kZSkpIHtcblx0XHRcdGZvciAoY29uc3QgY2xhdXNlIG9mIGRlY2wubm9kZS5oZXJpdGFnZUNsYXVzZXMgPz8gW10pIHtcblx0XHRcdFx0Zm9yIChjb25zdCBoZXJpdGFnZSBvZiBjbGF1c2UudHlwZXMpIHtcblx0XHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGhlcml0YWdlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0XHRvd25lcnMucHVzaCguLi50aGlzLm93bmVyc09mVHlwZU5hbWUoaGVyaXRhZ2UuZXhwcmVzc2lvbi50ZXh0LCBkZWNsLmZpbGUsIHZpc2l0ZWQsIGRlcHRoICsgMSkpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gb3duZXJzO1xuXHR9XG5cblx0LyoqXG5cdCAqIFRoZSBmdWxsUGF0aCB3aG9zZSBlbWl0dGVkIGluc3RhbmNlIGFsaWFzIGlzIGBlbWl0dGVkTmFtZWBcblx0ICogKGBBbHBoYV9HYWRnZXRgIOKGkiBgQWxwaGEuR2FkZ2V0YCksIGZyb20gdGhlIGN1cnJlbnQgZ3JhcGhcblx0ICovXG5cdHByaXZhdGUgZmluZFBhdGhCeUVtaXR0ZWROYW1lIChlbWl0dGVkTmFtZTogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRmb3IgKGNvbnN0IG5vZGUgb2YgdGhpcy5ncmFwaC5iZnMoKSkge1xuXHRcdFx0aWYgKHRoaXMuZ2V0RW1pdHRlZEluc3RhbmNlVHlwZU5hbWUobm9kZSkgPT09IGVtaXR0ZWROYW1lKSB7XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gbm9kZS5mdWxsUGF0aDtcblx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEEgYmFyZSBzdWJ0eXBlIGNhbGwg4oCUIGBpbnN0YW5jZS5TdWIo4oCmKWAgd2l0aG91dCBgbmV3YCDigJQgY29uc3RydWN0cyxcblx0ICogYXMgdGhlIGNoYWluIHRpcCBgbmV3IFIoKS5TdWIoKWAgZG9lcy4gQ291bnRlZCBvbmx5IHdoZW4gdGhlXG5cdCAqIHJlY2VpdmVyIGlzIGtub3duIGFzIGEgdmFsdWUgYmluZGluZyBvciBieSBpdHMgZGVjbGFyZWQgdHlwZTogYVxuXHQgKiByZWNlaXZlciB0YWN0aWNhIGNhbm5vdCBzZWUgbWF5IGJlIGFueXRoaW5nLCBhbmQgYW4gdXBwZXJjYXNlXG5cdCAqIG1ldGhvZCBuYW1lIGFsb25lIGlzIG5vdCBhIGNvbnN0cnVjdGlvbi5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUJhcmVTdWJ0eXBlQ2FsbCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmdbXSB7XG5cdFx0Y29uc3QgY2FsbGVlID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGlmICghdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbGVlKSB8fFxuXHRcdFx0IXRzLmlzSWRlbnRpZmllcihjYWxsZWUuZXhwcmVzc2lvbikgfHxcblx0XHRcdCF0aGlzLmlzTGlrZWx5VHlwZU5hbWUoY2FsbGVlLm5hbWUudGV4dCkpIHtcblx0XHRcdGNvbnN0IG5vbmU6IHN0cmluZ1tdID0gW107XG5cdFx0XHRyZXR1cm4gbm9uZTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzb2x2ZWQgPSB0aGlzLnJlc29sdmVVc2FnZVR5cGVQYXRocyhjYWxsZWUpO1xuXHRcdGNvbnN0IHBhdGhzID0gcmVzb2x2ZWQudmlhID09PSAnYmluZGluZycgfHwgcmVzb2x2ZWQudmlhID09PSAnYW5ub3RhdGlvbidcblx0XHRcdD8gcmVzb2x2ZWQucGF0aHNcblx0XHRcdDogW107XG5cdFx0cmV0dXJuIHBhdGhzO1xuXHR9XG5cblx0LyoqXG5cdCAqIFRoZSBgY29uc3QgeCA9IDxjYWxsPmAgKGF3YWl0IGFuZCBwYXJlbnRoZXNlcyB0cmFuc3BhcmVudCkgdGhlIGNhbGxcblx0ICogaW5pdGlhbGl6ZXMgZGlyZWN0bHkg4oCUIG5vdCBhIGNhbGwgbmVzdGVkIGluc2lkZSB0aGUgaW5pdGlhbGl6ZXJcblx0ICovXG5cdHByaXZhdGUgYmluZERpcmVjdFJlc3VsdCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHR5cGVQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSA9IGNhbGw7XG5cdFx0d2hpbGUgKHRzLmlzQXdhaXRFeHByZXNzaW9uKGN1cnJlbnQucGFyZW50KSB8fCB0cy5pc1BhcmVudGhlc2l6ZWRFeHByZXNzaW9uKGN1cnJlbnQucGFyZW50KSkge1xuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRjb25zdCBob2xkZXIgPSBjdXJyZW50LnBhcmVudDtcblx0XHRpZiAodHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKGhvbGRlcikgJiYgaG9sZGVyLmluaXRpYWxpemVyID09PSBjdXJyZW50ICYmIHRzLmlzSWRlbnRpZmllcihob2xkZXIubmFtZSkpIHtcblx0XHRcdHRoaXMudmFyaWFibGVUb1R5cGVNYXAuc2V0KGhvbGRlci5uYW1lLnRleHQsIHR5cGVQYXRoKTtcblx0XHRcdHRoaXMudHJhY2tGaWxlR3JhcGhCaW5kaW5nKGhvbGRlci5uYW1lLnRleHQsIHR5cGVQYXRoKTtcblx0XHR9XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0ICogQ2hlY2sgaWYgYSBuYW1lIGxvb2tzIGxpa2UgYSB0eXBlIChzdGFydHMgd2l0aCB1cHBlcmNhc2UpXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBpc0xpa2VseVR5cGVOYW1lIChuYW1lOiBzdHJpbmcpOiBib29sZWFuIHtcblx0XHRyZXR1cm4gbmFtZVsgMCBdID49ICdBJyAmJiBuYW1lWyAwIF0gPD0gJ1onO1xuXHR9XG5cdFxuXHQvKipcblx0XHRcdCAqIFJlc29sdmUgYSBjb25zdHJ1Y3RvciBwYXJhbWV0ZXIgdHlwZSwgZXhwYW5kaW5nIGlubGluZSBvYmplY3QgbGl0ZXJhbHNcblx0XHRcdCAqIGFuZCB0eXBlIGFsaWFzZXMgd2hlcmUgcG9zc2libGUuXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlQ29uc3RydWN0b3JQYXJhbVR5cGUgKHR5cGVOb2RlOiB0cy5UeXBlTm9kZSB8IHVuZGVmaW5lZCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCF0eXBlTm9kZSkgcmV0dXJuIHVuZGVmaW5lZDtcblxuXHRcdC8vIERpcmVjdCBpbmxpbmUgdHlwZSBsaXRlcmFsOiB7IHByb3A6IHR5cGUgfVxuXHRcdGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZSh0eXBlTm9kZSkpIHtcblx0XHRcdGNvbnN0IHByb3BzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgdHlwZU5vZGUubWVtYmVycykge1xuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Y29uc3Qgb3B0aW9uYWwgPSBtZW1iZXIucXVlc3Rpb25Ub2tlbiA/ICc/JyA6ICcnO1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0cHJvcHMucHVzaChgJHtwcm9wTmFtZX0ke29wdGlvbmFsfTogJHt0eXBlfWApO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gYHsgJHtwcm9wcy5qb2luKCc7ICcpfSB9YDtcblx0XHR9XG5cblx0XHQvLyBUeXBlIHJlZmVyZW5jZTogdXNhZ2UsIFVzZXJEYXRhLCBldGMuIC0gcmVzb2x2ZSBpbXBvcnQtYXdhcmUgYW5kXG5cdFx0Ly8gZXhwYW5kIHRoZSByZWZlcmVuY2VkIGRlY2xhcmF0aW9uIHdoZXJlIHBvc3NpYmxlIChGMTApXG5cdFx0aWYgKHRzLmlzVHlwZVJlZmVyZW5jZU5vZGUodHlwZU5vZGUpICYmIHRzLmlzSWRlbnRpZmllcih0eXBlTm9kZS50eXBlTmFtZSkpIHtcblx0XHRcdGNvbnN0IHR5cGVOYW1lID0gdHlwZU5vZGUudHlwZU5hbWUudGV4dDtcblx0XHRcdGNvbnN0IGRlY2wgPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKHR5cGVOYW1lLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0aWYgKGRlY2wpIHtcblx0XHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oZGVjbCk7XG5cdFx0XHRcdGlmIChleHBhbmRlZCkgcmV0dXJuIGV4cGFuZGVkO1xuXHRcdFx0fVxuXHRcdFx0Ly8gbW5lbW9uaWNhIGdyYXBoIHR5cGVzIGtlZXAgdGhlaXIgc2ltcGxlIG5hbWUg4oCUIHRoZSBnZW5lcmF0b3Jcblx0XHRcdC8vIHVwZ3JhZGVzIHRoZW0gdG8gZnVsbC1wYXRoIGluc3RhbmNlIHR5cGUgbmFtZXMuIFJlc29sdXRpb24gaXNcblx0XHRcdC8vIHBhdGgtYXdhcmUgKGhhcmQtZmFpbCBsYXcpOiBhbWJpZ3VpdHkgYmV0d2VlbiByZWFsIGdyYXBoIHR5cGVzXG5cdFx0XHQvLyByZWNvcmRzIGEgZmF0YWwgZXJyb3IgaW5zdGVhZCBvZiBzaWxlbnRseSBwaWNraW5nIG9uZS5cblx0XHRcdGNvbnN0IGdyYXBoUmVzdWx0ID0gdGhpcy5yZXNvbHZlR3JhcGhUeXBlTmFtZSh0eXBlTmFtZSk7XG5cdFx0XHRpZiAoZ3JhcGhSZXN1bHQuc3RhdHVzID09PSAndW5pcXVlJykge1xuXHRcdFx0XHRjb25zdCBzaW1wbGVSZXN1bHQgPSB0eXBlTmFtZTtcblx0XHRcdFx0cmV0dXJuIHNpbXBsZVJlc3VsdDtcblx0XHRcdH1cblx0XHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkR3JhcGhSZWZlcmVuY2VFcnJvcih0eXBlTmFtZSwgdHlwZU5vZGUsIGdyYXBoUmVzdWx0KTtcblx0XHRcdFx0Y29uc3QgdW5rbm93bkdyYXBoUmVzdWx0ID0gJ3Vua25vd24nO1xuXHRcdFx0XHRyZXR1cm4gdW5rbm93bkdyYXBoUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0Ly8gSWYgbm90IGFuIG9iamVjdCB0eXBlIGFsaWFzLCByZXR1cm4gdGhlIHR5cGUgbmFtZSB3aXRoIGFyZ3Ncblx0XHRcdGlmICh0eXBlTm9kZS50eXBlQXJndW1lbnRzICYmIHR5cGVOb2RlLnR5cGVBcmd1bWVudHMubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRpZiAoS05PV05fR0xPQkFMX1RZUEVTLmhhcyh0eXBlTmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBhcmdzID0gdHlwZU5vZGUudHlwZUFyZ3VtZW50cy5tYXAoYXJnID0+IHRoaXMuaW5mZXJUeXBlKGFyZykpO1xuXHRcdFx0XHRcdHJldHVybiBgJHt0eXBlTmFtZSAgfTwkeyAgYXJncy5qb2luKCcsICcpICB9PmA7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gZ2VuZXJpYyByZWZlcmVuY2UgdG8gYSBub24tZ2xvYmFsLCBub24tZ3JhcGggdHlwZSBjYW5ub3QgYmVcblx0XHRcdFx0Ly8gZW1pdHRlZCBiYXJlIGludG8gdGhlIGdlbmVyYXRlZCBmaWxlXG5cdFx0XHRcdHRoaXMucmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSh0eXBlTmFtZSwgdHlwZU5vZGUpO1xuXHRcdFx0XHRjb25zdCB1bmtub3duR2VuZXJpY1Jlc3VsdCA9ICd1bmtub3duJztcblx0XHRcdFx0cmV0dXJuIHVua25vd25HZW5lcmljUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZmFsbGJhY2tSZXN1bHQgPSB0aGlzLnVucmVzb2x2ZWRUeXBlUmVmZXJlbmNlRmFsbGJhY2sodHlwZU5hbWUsIHR5cGVOb2RlKTtcblx0XHRcdHJldHVybiBmYWxsYmFja1Jlc3VsdDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBhIGNsYXNzLWxpa2Ugbm9kZS5cblx0XHRcdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDbGFzc0NvbnN0cnVjdG9yUGFyYW1zIChjbGFzc0xpa2U6IHRzLkNsYXNzRGVjbGFyYXRpb24gfCB0cy5DbGFzc0V4cHJlc3Npb24pOlxuXHRcdENvbnN0cnVjdG9yUGFyYW1JbmZvW10ge1xuXHRcdGNvbnN0IHBhcmFtczogQ29uc3RydWN0b3JQYXJhbUluZm9bXSA9IFtdO1xuXG5cdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgY2xhc3NMaWtlLm1lbWJlcnMpIHtcblx0XHRcdGlmICghdHMuaXNDb25zdHJ1Y3RvckRlY2xhcmF0aW9uKG1lbWJlcikpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cblx0XHRcdGZvciAoY29uc3QgcGFyYW0gb2YgbWVtYmVyLnBhcmFtZXRlcnMpIHtcblx0XHRcdFx0aWYgKCFwYXJhbS5uYW1lIHx8ICF0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkpIGNvbnRpbnVlO1xuXHRcdFx0XHRpZiAoIXBhcmFtLnR5cGUpIGNvbnRpbnVlO1xuXG5cdFx0XHRcdGNvbnN0IHBhcmFtTmFtZSA9IHBhcmFtLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgZXhwYW5kZWRUeXBlID0gdGhpcy5yZXNvbHZlQ29uc3RydWN0b3JQYXJhbVR5cGUocGFyYW0udHlwZSkgfHwgdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cblx0XHRcdFx0cGFyYW1zLnB1c2goe1xuXHRcdFx0XHRcdG5hbWUgICAgIDogcGFyYW1OYW1lLFxuXHRcdFx0XHRcdHR5cGUgICAgIDogZXhwYW5kZWRUeXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogISFwYXJhbS5xdWVzdGlvblRva2VuIHx8ICEhcGFyYW0uaW5pdGlhbGl6ZXIsXG5cdFx0XHRcdFx0Ly8gcmVzdCBtYXJrZXIgZm9yIHRoZSBkZWZpbml0aW9ucy5qc29uIGFyZ3MgY29udHJhY3Rcblx0XHRcdFx0XHQuLi4ocGFyYW0uZG90RG90RG90VG9rZW4gPyB7IGtpbmQgOiAncmVzdCcgYXMgY29uc3QgfSA6IHt9KVxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHRcdC8vIE9ubHkgcHJvY2VzcyBmaXJzdCBjb25zdHJ1Y3RvclxuXHRcdFx0YnJlYWs7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHBhcmFtcztcblx0fVxuXG5cdC8qKlxuXHRcdFx0ICogRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZyb20gZGVmaW5lKCkgY2FsbFxuXHRcdFx0ICogVGhpcyBpcyB1c2VkIGZvciBUeXBlUmVnaXN0cnkgY29uc3RydWN0b3Igc2lnbmF0dXJlc1xuXHRcdFx0ICogUHJlc2VydmVzIHBhcmFtZXRlciBuYW1lcyBhbmQgZXhwYW5kcyBvYmplY3QgdHlwZXMgdG8gdGhlaXIgc3RydWN0dXJlXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JQYXJhbXMgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogQ29uc3RydWN0b3JQYXJhbUluZm9bXSB7XG5cdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpO1xuXHRcdGlmICghY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRjb25zdCBmYWxsYmFja1BhcmFtczogQ29uc3RydWN0b3JQYXJhbUluZm9bXSA9IFsge1xuXHRcdFx0XHRuYW1lICAgICA6ICdhcmdzJyxcblx0XHRcdFx0dHlwZSAgICAgOiAndW5rbm93bltdJyxcblx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0a2luZCAgICAgOiAncmVzdCcsXG5cdFx0XHR9IF07XG5cdFx0XHRyZXR1cm4gZmFsbGJhY2tQYXJhbXM7XG5cdFx0fVxuXHRcdGNvbnN0IHJlZmVyZW5jaW5nRmlsZSA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSBub2RlUGF0aC5yZXNvbHZlKGNvbnN0cnVjdG9yRXhwci5nZXRTb3VyY2VGaWxlKCkuZmlsZU5hbWUpO1xuXHRcdHRyeSB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtc0Zyb21Db25zdHJ1Y3Rvcihjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gcmVmZXJlbmNpbmdGaWxlO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdFx0ICogRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZyb20gYSBjb25zdHJ1Y3RvciBleHByZXNzaW9uLlxuXHRcdFx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zRnJvbUNvbnN0cnVjdG9yIChjb25zdHJ1Y3RvckV4cHI6IENvbnN0cnVjdG9ySGFuZGxlcik6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10ge1xuXHRcdGNvbnN0IHBhcmFtczogQ29uc3RydWN0b3JQYXJhbUluZm9bXSA9IFtdO1xuXHRcblx0XHQvLyBIYW5kbGUgZnVuY3Rpb24gZXhwcmVzc2lvbiBvciBhcnJvdyBmdW5jdGlvblxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzQXJyb3dGdW5jdGlvbihjb25zdHJ1Y3RvckV4cHIpIHx8XG5cdFx0XHR0cy5pc0Z1bmN0aW9uRGVjbGFyYXRpb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Ly8gTG9vayBmb3IgY29uc3RydWN0b3IgcGFyYW1ldGVycyAoc2Vjb25kIHBhcmFtIGFmdGVyIGB0aGlzYClcblx0XHRcdC8vIFBhdHRlcm5zOiBmdW5jdGlvbih0aGlzOiBUeXBlLCBkYXRhOiB7IC4uLiB9KSBvciAodGhpczogVHlwZSwgZGF0YTogeyAuLi4gfSkgPT5cblx0XHRcdGZvciAobGV0IGkgPSAwOyBpIDwgY29uc3RydWN0b3JFeHByLnBhcmFtZXRlcnMubGVuZ3RoOyBpKyspIHtcblx0XHRcdFx0Y29uc3QgcGFyYW0gPSBjb25zdHJ1Y3RvckV4cHIucGFyYW1ldGVyc1sgaSBdO1xuXHRcdFx0XHRpZiAoIXBhcmFtLnR5cGUpIGNvbnRpbnVlO1xuXHRcblx0XHRcdFx0Ly8gU2tpcCBgdGhpc2AgcGFyYW1ldGVyIChmaXJzdCBwYXJhbSlcblx0XHRcdFx0aWYgKFxuXHRcdFx0XHRcdGkgPT09IDAgJiZcblx0XHRcdFx0XHRwYXJhbS5uYW1lLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuSWRlbnRpZmllciAmJlxuXHRcdFx0XHRcdChwYXJhbS5uYW1lIGFzIHRzLklkZW50aWZpZXIpLnRleHQgPT09ICd0aGlzJ1xuXHRcdFx0XHQpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcblx0XHRcdFx0Ly8gR2V0IHBhcmFtZXRlciBuYW1lIGFuZCBleHBhbmQgaXRzIHR5cGVcblx0XHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpID8gcGFyYW0ubmFtZS50ZXh0IDogJ2FyZyc7XG5cdFx0XHRcdGNvbnN0IGV4cGFuZGVkVHlwZSA9IHRoaXMucmVzb2x2ZUNvbnN0cnVjdG9yUGFyYW1UeXBlKHBhcmFtLnR5cGUpIHx8IHRoaXMuaW5mZXJUeXBlKHBhcmFtLnR5cGUpO1xuXHRcdFx0XHRcdFxuXHRcdFx0XHRwYXJhbXMucHVzaCh7XG5cdFx0XHRcdFx0bmFtZSAgICAgOiBwYXJhbU5hbWUsXG5cdFx0XHRcdFx0dHlwZSAgICAgOiBleHBhbmRlZFR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiAhIXBhcmFtLnF1ZXN0aW9uVG9rZW4gfHwgISFwYXJhbS5pbml0aWFsaXplcixcblx0XHRcdFx0XHQvLyByZXN0IG1hcmtlciBmb3IgdGhlIGRlZmluaXRpb25zLmpzb24gYXJncyBjb250cmFjdFxuXHRcdFx0XHRcdC4uLihwYXJhbS5kb3REb3REb3RUb2tlbiA/IHsga2luZCA6ICdyZXN0JyBhcyBjb25zdCB9IDoge30pXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0Ly8gSGFuZGxlIGNsYXNzIGV4cHJlc3Npb24gLSBjaGVjayBjb25zdHJ1Y3RvciBtZXRob2Rcblx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSB8fCB0cy5pc0NsYXNzRGVjbGFyYXRpb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Y29uc3QgY2xhc3NQYXJhbXMgPSB0aGlzLmV4dHJhY3RDbGFzc0NvbnN0cnVjdG9yUGFyYW1zKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGNsYXNzUGFyYW1zKSB7XG5cdFx0XHRcdHBhcmFtcy5wdXNoKHBhcmFtKTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcGFyYW1zO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgZnJhbWV3b3JrIGluc3RydW1lbnRhdGlvbiBwb2ludHMuIFB1cmVseSBzeW50YWN0aWM6IGhlcml0YWdlXG5cdCAqIGNsYXVzZXMsIGRlY29yYXRvciBhcHBsaWNhdGlvbiBzaXRlcywgcHJvdmlkZXItdG9rZW4gb2JqZWN0IGxpdGVyYWxzXG5cdCAqIGFuZCBjb25zdW1lci5hcHBseSgpLmZvclJvdXRlcygpIHdpcmluZy4gVGhlIHZvY2FidWxhcnkgY29tZXMgZnJvbVxuXHQgKiBwbHVnaW5zOyBpZGVudGlmaWVyIHRleHQgaXMgbWF0Y2hlZCBhcy1pcyDigJQgbm8gaW1wb3J0IHJlc29sdXRpb24sXG5cdCAqIHRoZSB0eXBlIGNoZWNrZXIgc3RheXMgdW51c2VkLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0SW5zdHJ1bWVudGF0aW9uIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbkNsYXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0XHRpZiAodHMuaXNEZWNvcmF0b3Iobm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbkRlY29yYXRvcihub2RlLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cdFx0aWYgKHRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvblByb3ZpZGVyKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uTWlkZGxld2FyZShub2RlLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGEgbmFtZWQgY2xhc3MgZGVjbGFyYXRpb24gZm9yIGluc3RydW1lbnRhdGlvbiBzaXRlIHJlc29sdXRpb25cblx0ICogYW5kIGRldGVjdCBoZXJpdGFnZS1iYXNlZCBraW5kcyAoYGltcGxlbWVudHMgPHBsdWdpbiBpbnRlcmZhY2U+YClcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEluc3RydW1lbnRhdGlvbkNsYXNzIChub2RlOiB0cy5DbGFzc0RlY2xhcmF0aW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCFub2RlLm5hbWUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgY2xhc3NOYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUubmFtZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHQvLyBGaXJzdCBsaW5lIG9mIHRoZSBkZWNsYXJhdGlvbiwgbGlrZSBFRFMgYGNvZGVgIHNuaXBwZXRzXG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zcGxpdCgnXFxuJylbIDAgXS5zbGljZSgwLCAxMDApO1xuXG5cdFx0bGV0IGtpbmQ6IEluc3RydW1lbnRhdGlvbktpbmQgfCB1bmRlZmluZWQ7XG5cdFx0aWYgKG5vZGUuaGVyaXRhZ2VDbGF1c2VzKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGNsYXVzZSBvZiBub2RlLmhlcml0YWdlQ2xhdXNlcykge1xuXHRcdFx0XHRpZiAoY2xhdXNlLnRva2VuICE9PSB0cy5TeW50YXhLaW5kLkltcGxlbWVudHNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Zm9yIChjb25zdCB0eXBlIG9mIGNsYXVzZS50eXBlcykge1xuXHRcdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHR5cGUuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCBtYXRjaGVkID0gdGhpcy5pbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5LmludGVyZmFjZXNbIHR5cGUuZXhwcmVzc2lvbi50ZXh0IF07XG5cdFx0XHRcdFx0aWYgKG1hdGNoZWQpIHtcblx0XHRcdFx0XHRcdGtpbmQgPSBtYXRjaGVkO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGNvbnN0IGRlY2w6IEluc3RydW1lbnRhdGlvbkNsYXNzRGVjbCA9IHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0Y29kZSxcblx0XHR9O1xuXHRcdGlmIChraW5kKSB7XG5cdFx0XHRkZWNsLmtpbmQgPSBraW5kO1xuXHRcdH1cblx0XHR0aGlzLmluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMuc2V0KGNsYXNzTmFtZSwgZGVjbCk7XG5cdH1cblxuXHQvKipcblx0ICogRGV0ZWN0IGRlY29yYXRvciBhcHBsaWNhdGlvbiBzaXRlczogcGx1Z2luLWxpc3RlZCBkZWNvcmF0b3JzIGFwcGxpZWRcblx0ICogd2l0aCBjbGFzcyBhcmd1bWVudHMgb24gYSBjbGFzcyBvciBvbmUgb2YgaXRzIG1ldGhvZHMuIE9uZSBzaXRlIHBlclxuXHQgKiByZWZlcmVuY2VkIGNsYXNzIGlkZW50aWZpZXIuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25EZWNvcmF0b3IgKG5vZGU6IHRzLkRlY29yYXRvciwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24oZXhwcmVzc2lvbikgfHwgIXRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGtpbmQgPSB0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkudXNlRGVjb3JhdG9yc1sgZXhwcmVzc2lvbi5leHByZXNzaW9uLnRleHQgXTtcblx0XHRpZiAoIWtpbmQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBUaGUgZGVjb3JhdG9yJ3MgcGFyZW50IGlzIHRoZSBkZWNvcmF0ZWQgbm9kZTogYSBjb250cm9sbGVyIGNsYXNzLFxuXHRcdC8vIG9uZSBvZiBpdHMgbWV0aG9kcywgb3Igb25lIG9mIGl0cyBtZXRob2QgcGFyYW1ldGVyc1xuXHRcdC8vIChAQm9keShtdnAuZm9yVHlwZShEdG8pKSBvbiBhIGhhbmRsZXIgYXJndW1lbnQpXG5cdFx0Y29uc3QgZGVjb3JhdGVkID0gbm9kZS5wYXJlbnQ7XG5cdFx0bGV0IHNjb3BlOiBJbnN0cnVtZW50YXRpb25TY29wZTtcblx0XHRsZXQgdGFyZ2V0czogc3RyaW5nW107XG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihkZWNvcmF0ZWQpICYmIGRlY29yYXRlZC5uYW1lKSB7XG5cdFx0XHRzY29wZSA9IGBjb250cm9sbGVyOiR7ZGVjb3JhdGVkLm5hbWUudGV4dH1gO1xuXHRcdFx0dGFyZ2V0cyA9IFsgZGVjb3JhdGVkLm5hbWUudGV4dCBdO1xuXHRcdH0gZWxzZSBpZiAoXG5cdFx0XHR0cy5pc01ldGhvZERlY2xhcmF0aW9uKGRlY29yYXRlZCkgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcihkZWNvcmF0ZWQubmFtZSkgJiZcblx0XHRcdHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihkZWNvcmF0ZWQucGFyZW50KSAmJlxuXHRcdFx0ZGVjb3JhdGVkLnBhcmVudC5uYW1lXG5cdFx0KSB7XG5cdFx0XHRjb25zdCBjbGFzc05hbWUgPSBkZWNvcmF0ZWQucGFyZW50Lm5hbWUudGV4dDtcblx0XHRcdHNjb3BlID0gYG1ldGhvZDoke2NsYXNzTmFtZX0uJHtkZWNvcmF0ZWQubmFtZS50ZXh0fWA7XG5cdFx0XHR0YXJnZXRzID0gWyBjbGFzc05hbWUgXTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzUGFyYW1ldGVyKGRlY29yYXRlZCkpIHtcblx0XHRcdC8vIFBhcmFtZXRlciBkZWNvcmF0b3JzIHRha2UgdGhlIGVuY2xvc2luZyBtZXRob2QncyBzY29wZSDigJQgdGhlXG5cdFx0XHQvLyBhdHRhY2htZW50IHBvaW50IGlzIHRoZSBoYW5kbGVyLCBub3QgdGhlIGFyZ3VtZW50IG5hbWU7IHRoZVxuXHRcdFx0Ly8gc2FtZSBtZXRob2Q6Q2xhc3MubWV0aG9kIGZvcm0gYXMgbWV0aG9kLWxldmVsIHNpdGVzLiBQYXJhbXMgb2Zcblx0XHRcdC8vIGNvbnN0cnVjdG9ycywgZnVuY3Rpb25zLCBhbmQgdW5uYW1lYWJsZSBob3N0cyBzdGF5IHNpbGVudCwgdGhlXG5cdFx0XHQvLyBzYW1lIGNvbnZlbnRpb24gYXMgb3RoZXIgdW5yZXNvbHZhYmxlIGRlY29yYXRvciBwYXJlbnRzXG5cdFx0XHRjb25zdCBob3N0ID0gZGVjb3JhdGVkLnBhcmVudDtcblx0XHRcdGlmIChcblx0XHRcdFx0aG9zdCAmJlxuXHRcdFx0XHR0cy5pc01ldGhvZERlY2xhcmF0aW9uKGhvc3QpICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihob3N0Lm5hbWUpICYmXG5cdFx0XHRcdHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihob3N0LnBhcmVudCkgJiZcblx0XHRcdFx0aG9zdC5wYXJlbnQubmFtZVxuXHRcdFx0KSB7XG5cdFx0XHRcdGNvbnN0IGNsYXNzTmFtZSA9IGhvc3QucGFyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0c2NvcGUgPSBgbWV0aG9kOiR7Y2xhc3NOYW1lfS4ke2hvc3QubmFtZS50ZXh0fWA7XG5cdFx0XHRcdHRhcmdldHMgPSBbIGNsYXNzTmFtZSBdO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0Zm9yIChjb25zdCBhcmcgb2YgZXhwcmVzc2lvbi5hcmd1bWVudHMpIHtcblx0XHRcdC8vIENsYXNzIHJlZmVyZW5jZTogQFJlZ2lzdGVyKEltcGwpIG9yIGFuIGlubGluZSBpbnN0YW5jZTpcblx0XHRcdC8vIEBSZWdpc3RlcihuZXcgSW1wbCh7IC4uLm9wdGlvbnMgfSkpXG5cdFx0XHRsZXQgY2xhc3NOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdFx0XHQvLyBwZXItYXJnIGtpbmQ6IGZhY3RvcnktY2FsbCBhcmdzIGNhcnJ5IHRoZWlyIG93biBjb25maWd1cmVkXG5cdFx0XHQvLyBraW5kLCBldmVyeXRoaW5nIGVsc2UgdGFrZXMgdGhlIGRlY29yYXRvcidzXG5cdFx0XHRsZXQgYXJnS2luZCA9IGtpbmQ7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdFx0Y2xhc3NOYW1lID0gYXJnLnRleHQ7XG5cdFx0XHR9IGVsc2UgaWYgKHRzLmlzTmV3RXhwcmVzc2lvbihhcmcpICYmIHRzLmlzSWRlbnRpZmllcihhcmcuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y2xhc3NOYW1lID0gYXJnLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdH0gZWxzZSBpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihhcmcpICYmIHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFyZy5leHByZXNzaW9uKSkge1xuXHRcdFx0XHQvLyBQaXBlLWZhY3Rvcnkgc2hhcGU6IEBVc2VQaXBlcyhtdnAuZm9yVHlwZShEdG8pKSDigJQgdGhlXG5cdFx0XHRcdC8vIGNhbGwncyBtZXRob2QgbmFtZSBpcyBwbHVnaW4tbGlzdGVkLCB0aGUgdGFyZ2V0IGNsYXNzIHNpdHNcblx0XHRcdFx0Ly8gaW4gdGhlIGNvbmZpZ3VyZWQgYXJndW1lbnQgcG9zaXRpb24gKGRlZmF1bHQgMClcblx0XHRcdFx0Y29uc3QgZmFjdG9yeSA9IHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS5kZWNvcmF0b3JBcmdGYWN0b3JpZXNbIGFyZy5leHByZXNzaW9uLm5hbWUudGV4dCBdO1xuXHRcdFx0XHRpZiAoZmFjdG9yeSkge1xuXHRcdFx0XHRcdGNvbnN0IHRhcmdldEFyZyA9IGFyZy5hcmd1bWVudHNbIGZhY3RvcnkudGFyZ2V0QXJnID8/IDAgXTtcblx0XHRcdFx0XHRpZiAodGFyZ2V0QXJnICYmIHRzLmlzSWRlbnRpZmllcih0YXJnZXRBcmcpKSB7XG5cdFx0XHRcdFx0XHRjbGFzc05hbWUgPSB0YXJnZXRBcmcudGV4dDtcblx0XHRcdFx0XHRcdGFyZ0tpbmQgPSBmYWN0b3J5LmtpbmQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdC8vIFRoZSBwbHVnaW4gZGVjbGFyZXMgdGhhdCB0aGlzIGZhY3RvcnkgY29uc3RydWN0cyBpdHNcblx0XHRcdFx0XHQvLyB0YXJnZXQgb24gdGhlIGNhbGxlcidzIGJlaGFsZjogdGhlIGNhbGwgc2l0ZSBpcyBhXG5cdFx0XHRcdFx0Ly8gY29uc3RydWN0aW9uIGxpa2UgYG5ld2AsIHJlY29yZGVkIGFzIGFuIGluc3RhbnRpYXRpb25cblx0XHRcdFx0XHRpZiAodGFyZ2V0QXJnICYmIGZhY3RvcnkuaW5zdGFudGlhdGlvbikge1xuXHRcdFx0XHRcdFx0dGhpcy5yZWNvcmRGYWN0b3J5Q29uc3RydWN0aW9uKGFyZywgdGFyZ2V0QXJnLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGlmICghY2xhc3NOYW1lKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0dGhpcy5pbnN0cnVtZW50YXRpb25TaXRlcy5wdXNoKHtcblx0XHRcdFx0a2luZCA6IGFyZ0tpbmQsXG5cdFx0XHRcdGNsYXNzTmFtZSxcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHNjb3BlLFxuXHRcdFx0XHR0YXJnZXRzLFxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEEgcGx1Z2luLWxpc3RlZCBkZWNvcmF0b3ItYXJnIGZhY3Rvcnkgd2l0aCBgaW5zdGFudGlhdGlvbjogdHJ1ZWBcblx0ICogKGBAQm9keShtdnAuZm9yVHlwZShFbnRpdHksIER0bykpYCkgY29uc3RydWN0cyB0aGUgdHlwZSBhdCBpdHNcblx0ICogdGFyZ2V0IGFyZ3VtZW50IGxhdGVyLCBhdCBydW50aW1lOiByZWNvcmQgdGhlIGZhY3RvcnkgY2FsbCBhcyB0aGF0XG5cdCAqIHR5cGUncyBgaW5zdGFudGlhdGlvbmAgdXNhZ2UgYW5kIGZsb3csIHRoZSBzYW1lIGFzIGNhbGwvYXBwbHkuIEFcblx0ICogdGFyZ2V0IHRoYXQgcmVzb2x2ZXMgdG8gbm8gZGVmaW5lZCB0eXBlIHJlY29yZHMgbm90aGluZy5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkRmFjdG9yeUNvbnN0cnVjdGlvbiAoXG5cdFx0Y2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0dGFyZ2V0QXJnOiB0cy5FeHByZXNzaW9uLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGVcblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgY29uc3RydWN0ZWRQYXRoID0gdGhpcy5yZXNvbHZlQ3RvckFyZ1R5cGVQYXRoKHRhcmdldEFyZyk7XG5cdFx0aWYgKCFjb25zdHJ1Y3RlZFBhdGgpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0dGhpcy5yZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZShjYWxsLCBjb25zdHJ1Y3RlZFBhdGgsIHNvdXJjZUZpbGUsIHRhcmdldEFyZy5nZXRUZXh0KHNvdXJjZUZpbGUpKTtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0Y2FsbC5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0dGhpcy5hZGRGbG93KGNvbnN0cnVjdGVkUGF0aCwge1xuXHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdGtpbmQgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0Y29kZSAgICAgOiBjYWxsLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdGNvbnRleHQgIDogJ3BsdWdpbiBmYWN0b3J5IGNvbnN0cnVjdGlvbicsXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogRGV0ZWN0IGdsb2JhbCByZWdpc3RyYXRpb25zOiBvYmplY3QgbGl0ZXJhbHMgc2hhcGVkIGxpa2Vcblx0ICogYHsgcHJvdmlkZTogPHBsdWdpbi1saXN0ZWQgdG9rZW4+LCB1c2VDbGFzczogWCB9YC5cblx0ICogdXNlRXhpc3RpbmcvdXNlRmFjdG9yeSB3aXRob3V0IGEgdXNlQ2xhc3MgaWRlbnRpZmllciBhcmUgbm90XG5cdCAqIHN0YXRpY2FsbHkgb2J2aW91cyDigJQgc2tpcHBlZCByYXRoZXIgdGhhbiBndWVzc2VkLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0SW5zdHJ1bWVudGF0aW9uUHJvdmlkZXIgKG5vZGU6IHRzLk9iamVjdExpdGVyYWxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0bGV0IGtpbmQ6IEluc3RydW1lbnRhdGlvbktpbmQgfCB1bmRlZmluZWQ7XG5cdFx0bGV0IHVzZUNsYXNzTmFtZTogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXG5cdFx0Zm9yIChjb25zdCBwcm9wIG9mIG5vZGUucHJvcGVydGllcykge1xuXHRcdFx0aWYgKFxuXHRcdFx0XHQhdHMuaXNQcm9wZXJ0eUFzc2lnbm1lbnQocHJvcCkgfHxcblx0XHRcdFx0IXRzLmlzSWRlbnRpZmllcihwcm9wLm5hbWUpIHx8XG5cdFx0XHRcdCF0cy5pc0lkZW50aWZpZXIocHJvcC5pbml0aWFsaXplcilcblx0XHRcdCkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGlmIChwcm9wLm5hbWUudGV4dCA9PT0gJ3Byb3ZpZGUnKSB7XG5cdFx0XHRcdGtpbmQgPSB0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkuYXBwVG9rZW5zWyBwcm9wLmluaXRpYWxpemVyLnRleHQgXTtcblx0XHRcdH1cblx0XHRcdGlmIChwcm9wLm5hbWUudGV4dCA9PT0gJ3VzZUNsYXNzJykge1xuXHRcdFx0XHR1c2VDbGFzc05hbWUgPSBwcm9wLmluaXRpYWxpemVyLnRleHQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0aWYgKCFraW5kIHx8ICF1c2VDbGFzc05hbWUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHR0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzLnB1c2goe1xuXHRcdFx0a2luZCxcblx0XHRcdGNsYXNzTmFtZSA6IHVzZUNsYXNzTmFtZSxcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0Y29kZSxcblx0XHRcdHNjb3BlICAgICA6ICdnbG9iYWwnLFxuXHRcdFx0dGFyZ2V0cyAgIDogW10sXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogRGV0ZWN0IG1pZGRsZXdhcmUgd2lyaW5nOiBgY29uc3VtZXIuYXBwbHkoTXcxLCBNdzIpLmZvclJvdXRlcyguLi4pYFxuXHQgKiBpbnNpZGUgYSBjbGFzcydzIGNvbmZpZ3VyZSgpIG1ldGhvZC4gVGFyZ2V0cyBjb21lIGZyb20gZm9yUm91dGVzXG5cdCAqIGFyZ3VtZW50cyB3aGVuIHN0YXRpY2FsbHkgcmVhZGFibGUgKHN0cmluZyByb3V0ZXMgb3IgY29udHJvbGxlclxuXHQgKiBpZGVudGlmaWVycyksIGVsc2UgW10uIFNoYXBlLWJhc2VkLCBzbyBhIHBsdWdpbiBtdXN0IG9wdCBpbiB2aWFcblx0ICogYG1pZGRsZXdhcmVXaXJpbmc6IHRydWVgLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0SW5zdHJ1bWVudGF0aW9uTWlkZGxld2FyZSAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS5taWRkbGV3YXJlV2lyaW5nKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGlmIChcblx0XHRcdCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pIHx8XG5cdFx0XHRub2RlLmV4cHJlc3Npb24ubmFtZS50ZXh0ICE9PSAnZm9yUm91dGVzJ1xuXHRcdCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBhcHBseUNhbGwgPSBub2RlLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRpZiAoXG5cdFx0XHQhdHMuaXNDYWxsRXhwcmVzc2lvbihhcHBseUNhbGwpIHx8XG5cdFx0XHQhdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXBwbHlDYWxsLmV4cHJlc3Npb24pIHx8XG5cdFx0XHRhcHBseUNhbGwuZXhwcmVzc2lvbi5uYW1lLnRleHQgIT09ICdhcHBseSdcblx0XHQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKCF0aGlzLmlzSW5zaWRlQ29uZmlndXJlTWV0aG9kKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgdGFyZ2V0czogc3RyaW5nW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IGFyZyBvZiBub2RlLmFyZ3VtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihhcmcpIHx8IHRzLmlzU3RyaW5nTGl0ZXJhbChhcmcpKSB7XG5cdFx0XHRcdHRhcmdldHMucHVzaChhcmcudGV4dCk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdGFwcGx5Q2FsbC5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRmb3IgKGNvbnN0IGFyZyBvZiBhcHBseUNhbGwuYXJndW1lbnRzKSB7XG5cdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihhcmcpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0dGhpcy5pbnN0cnVtZW50YXRpb25TaXRlcy5wdXNoKHtcblx0XHRcdFx0a2luZCAgICAgIDogJ21pZGRsZXdhcmUnLFxuXHRcdFx0XHRjbGFzc05hbWUgOiBhcmcudGV4dCxcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHNjb3BlICAgICA6ICdtb2R1bGUnLFxuXHRcdFx0XHR0YXJnZXRzLFxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFdhbGsgdXAgdGhlIHBhcmVudCBjaGFpbiBsb29raW5nIGZvciBhbiBlbmNsb3NpbmcgY29uZmlndXJlKCkgbWV0aG9kXG5cdCAqL1xuXHRwcml2YXRlIGlzSW5zaWRlQ29uZmlndXJlTWV0aG9kIChub2RlOiB0cy5Ob2RlKTogYm9vbGVhbiB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBub2RlLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc01ldGhvZERlY2xhcmF0aW9uKGN1cnJlbnQpICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihjdXJyZW50Lm5hbWUpICYmXG5cdFx0XHRcdGN1cnJlbnQubmFtZS50ZXh0ID09PSAnY29uZmlndXJlJ1xuXHRcdFx0KSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cbn1cbiJdfQ==