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
                        const kind = ts.isIdentifier(call.expression) ? 'typeof' : 'registryOf';
                        this.recordBuilderCandidate(varName, fullPath, kind, sourceFile, current, excluded);
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
            let typeName;
            if (ts.isPropertyAccessExpression(node.expression)) {
                typeName = this.resolveTypePath(node.expression);
            }
            else {
                typeName = this.getTypeNameFromExpression(node.expression);
            }
            if (typeName) {
                const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                this.addUsage(typeName, {
                    location: `${sourceFile.fileName}:${line + 1}:${character + 1}`,
                    kind: 'instantiation',
                    code: node.getText(sourceFile).slice(0, 100),
                    // Constructor expression text ('Thing', 'user.AdminEntity',
                    // a lookup alias) — CreationAnchor.constructorText (Phase 3)
                    constructorText: node.expression.getText(sourceFile).slice(0, 100),
                });
                // Track variable assignment from new Type() for flow analysis
                this.trackNewAssignment(node, typeName);
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
                const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                // Try to resolve full path
                const fullPath = this.resolveTypePath(node);
                if (fullPath && !isNewCallee) {
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYW5hbHl6ZXIuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvYW5hbHl6ZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFFYiwrQ0FBaUM7QUFDakMsK0NBQWlDO0FBT2pDLG1DQUVpQjtBQUNqQix1Q0FFbUI7QUFxRm5COzs7R0FHRztBQUNILE1BQU0sa0JBQWtCLEdBQUcsSUFBSSxHQUFHLENBQUM7SUFDbEMsTUFBTSxFQUFFLFFBQVEsRUFBRSxPQUFPLEVBQUUsV0FBVyxFQUFFLFlBQVksRUFBRSxnQkFBZ0I7SUFDdEUsYUFBYSxFQUFFLFdBQVcsRUFBRSxVQUFVLEVBQUUsZ0JBQWdCO0lBQ3hELEtBQUssRUFBRSxLQUFLLEVBQUUsU0FBUyxFQUFFLFNBQVMsRUFBRSxTQUFTLEVBQUUsc0JBQXNCO0lBQ3JFLFNBQVMsRUFBRSxPQUFPLEVBQUUsZUFBZSxFQUFFLFFBQVEsRUFBRSxTQUFTLEVBQUUsVUFBVTtJQUNwRSxVQUFVLEVBQUUsTUFBTSxFQUFFLE1BQU0sRUFBRSxTQUFTLEVBQUUsU0FBUyxFQUFFLGFBQWE7SUFDL0QsWUFBWSxFQUFFLGNBQWMsRUFBRSxZQUFZLEVBQUUsdUJBQXVCO0lBQ25FLFVBQVUsRUFBRSxtQkFBbUIsRUFBRSxtQkFBbUI7SUFDcEQsV0FBVyxFQUFFLFdBQVcsRUFBRSxZQUFZLEVBQUUsY0FBYztJQUN0RCxRQUFRLEVBQUUsUUFBUSxFQUFFLFNBQVMsRUFBRSxRQUFRLEVBQUUsUUFBUSxFQUFFLFFBQVEsRUFBRSxVQUFVO0lBQ3ZFLFVBQVUsRUFBRSxVQUFVLEVBQUUsV0FBVyxFQUFFLGVBQWUsRUFBRSxlQUFlO0lBQ3JFLGdCQUFnQixFQUFFLGtCQUFrQixFQUFFLHVCQUF1QjtJQUM3RCxhQUFhLEVBQUUsYUFBYSxFQUFFLG1CQUFtQixFQUFFLFVBQVU7SUFDN0QsV0FBVyxFQUFFLFlBQVksRUFBRSxtQkFB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QUFZO2dCQUN4QixTQUFTLEVBQUcsR0FBRyxDQUFDLElBQUk7Z0JBQ3BCLFFBQVE7Z0JBQ1IsSUFBSTtnQkFDSixLQUFLLEVBQU8sUUFBUTtnQkFDcEIsT0FBTzthQUNQLENBQUMsQ0FBQztRQUNKLENBQUM7SUFDRixDQUFDO0lBRUQ7O09BRUc7SUFDSyx1QkFBdUIsQ0FBRSxJQUFhO1FBQzdDLElBQUksT0FBTyxHQUF3QixJQUFJLENBQUMsTUFBTSxDQUFDO1FBQy9DLE9BQU8sT0FBTyxFQUFFLENBQUM7WUFDaEIsSUFDQyxFQUFFLENBQUMsbUJBQW1CLENBQUMsT0FBTyxDQUFDO2dCQUMvQixFQUFFLENBQUMsWUFBWSxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUM7Z0JBQzdCLE9BQU8sQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLFdBQVcsRUFDaEMsQ0FBQztnQkFDRixPQUFPLElBQUksQ0FBQztZQUNiLENBQUM7WUFDRCxPQUFPLEdBQUcsT0FBTyxDQUFDLE1BQU0sQ0FBQztRQUMxQixDQUFDO1FBQ0QsT0FBTyxLQUFLLENBQUM7SUFDZCxDQUFDO0NBQ0Q7QUFoNE5ELDhDQWc0TkMiLCJzb3VyY2VzQ29udGVudCI6WyIndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIG5vZGVQYXRoIGZyb20gJ3BhdGgnO1xuaW1wb3J0ICogYXMgdHMgZnJvbSAndHlwZXNjcmlwdCc7XG5pbXBvcnQge1xuXHRUeXBlTm9kZSwgUHJvcGVydHlJbmZvLCBBbmFseXplUmVzdWx0LCBBbmFseXplRXJyb3IsXG5cdERlZmluaXRpb25JbmZvLCBVc2FnZUluZm8sIENvbnN0cnVjdG9yUGFyYW1JbmZvLFxuXHRFRFNJbmZvLCBGbG93SW5mbywgSW5zdHJ1bWVudGF0aW9uS2luZCwgSW5zdHJ1bWVudGF0aW9uUG9pbnQsXG5cdEluc3RydW1lbnRhdGlvblNjb3BlLCBSZXNvbHV0aW9uRXJyb3IsIENvbGxlY3Rpb25NYW5pZmVzdEVudHJ5LCBCdWlsZGVyVmFsdWVcbn0gZnJvbSAnLi90eXBlcyc7XG5pbXBvcnQge1xuXHRUeXBlR3JhcGhJbXBsLCByZXNvbHZlR3JhcGhUeXBlUmVmZXJlbmNlLCBHcmFwaFR5cGVSZWZlcmVuY2VSZXN1bHQgXG59IGZyb20gJy4vZ3JhcGgnO1xuaW1wb3J0IHtcblx0SW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeSwgVGFjdGljYVBsdWdpbiwgbWVyZ2VUYWN0aWNhUGx1Z2luc1xufSBmcm9tICcuL3BsdWdpbnMnO1xuXG5pbnRlcmZhY2UgQ29sbGVjdGlvbkluZm8ge1xuXHR2YXJpYWJsZU5hbWU6IHN0cmluZztcblx0c291cmNlRmlsZTogc3RyaW5nO1xuXHRyZWdpc3RyeUludGVyZmFjZU5hbWU/OiBzdHJpbmc7XG5cdC8qKiAxLWJhc2VkIHBvc2l0aW9uIG9mIHRoZSBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSB2YXJpYWJsZSBkZWNsYXJhdGlvbiAqL1xuXHRsaW5lOiBudW1iZXI7XG5cdGNvbHVtbjogbnVtYmVyO1xufVxuXG5pbnRlcmZhY2UgQnVpbGRlckV4cG9ydCB7XG5cdG5hbWU6IHN0cmluZztcblx0c291cmNlRmlsZTogc3RyaW5nO1xuXHRkZWZhdWx0SW1wb3J0PzogYm9vbGVhbjtcbn1cblxuaW50ZXJmYWNlIEJ1aWxkZXJDYW5kaWRhdGUge1xuXHRuYW1lOiBzdHJpbmc7XG5cdHNvdXJjZUZpbGU6IHN0cmluZztcblx0a2luZDogJ3JlZ2lzdHJ5T2YnIHwgJ3R5cGVvZic7XG5cdGZ1bGxQYXRoOiBzdHJpbmc7XG5cdGV4cG9ydHM6IEJ1aWxkZXJFeHBvcnRbXTtcblx0ZXhjbHVkZWQ6IGJvb2xlYW47XG59XG5cbi8qKlxuICogTG9jYXRpb24vY29kZSBjYXB0dXJlZCBhdCBhIGNsYXNzIGRlY2xhcmF0aW9uLCB1c2VkIHRvIHJlc29sdmVcbiAqIGluc3RydW1lbnRhdGlvbiByZWdpc3RyYXRpb24gc2l0ZXMgdG8gdGhlIGRlY2xhcmVkIGNsYXNzXG4gKi9cbmludGVyZmFjZSBJbnN0cnVtZW50YXRpb25DbGFzc0RlY2wge1xuXHRraW5kPzogSW5zdHJ1bWVudGF0aW9uS2luZDtcblx0bG9jYXRpb246IHN0cmluZztcblx0Y29kZTogc3RyaW5nO1xufVxuXG4vKipcbiAqIFJhdyByZWdpc3RyYXRpb24gc2l0ZSAoZGVjb3JhdG9yLCBBUFBfKiBwcm92aWRlciwgY29uc3VtZXIuYXBwbHkpLlxuICogTG9jYXRpb24vY29kZSBhcmUgdGhlIHNpdGUncyBvd247IGdldEluc3RydW1lbnRhdGlvblBvaW50cygpIHJld3JpdGVzXG4gKiB0aGVtIHRvIHRoZSBjbGFzcyBkZWNsYXJhdGlvbiB3aGVuIHRoZSBjbGFzcyBpcyBkZWNsYXJlZCBpbi1wcm9qZWN0LlxuICovXG5pbnRlcmZhY2UgSW5zdHJ1bWVudGF0aW9uU2l0ZSB7XG5cdGtpbmQ6IEluc3RydW1lbnRhdGlvbktpbmQ7XG5cdGNsYXNzTmFtZTogc3RyaW5nO1xuXHRsb2NhdGlvbjogc3RyaW5nO1xuXHRjb2RlOiBzdHJpbmc7XG5cdHNjb3BlOiBJbnN0cnVtZW50YXRpb25TY29wZTtcblx0dGFyZ2V0czogc3RyaW5nW107XG59XG5cbi8qKlxuICogQSBuYW1lZCByZWZlcmVuY2VkLXR5cGUgZGVjbGFyYXRpb24gKHR5cGUgYWxpYXMsIGNsYXNzLCBvciBpbnRlcmZhY2UpXG4gKiByZWNvcmRlZCBwZXIgZmlsZSwgc28gcmVmZXJlbmNlcyBjYW4gYmUgcmVzb2x2ZWQgdGhyb3VnaCB0aGUgaW1wb3J0aW5nXG4gKiBmaWxlJ3Mgb3duIGltcG9ydHMgaW5zdGVhZCBvZiBhIHByb2dyYW0td2lkZSBsYXN0LXdpbnMgbmFtZSBtYXAgKEYxMCkuXG4gKi9cbmludGVyZmFjZSBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHtcblx0a2luZDogJ2FsaWFzJyB8ICdjbGFzcycgfCAnaW50ZXJmYWNlJztcblx0bm9kZTogdHMuVHlwZUFsaWFzRGVjbGFyYXRpb24gfCB0cy5DbGFzc0RlY2xhcmF0aW9uIHwgdHMuSW50ZXJmYWNlRGVjbGFyYXRpb247XG5cdC8qKiBmaWxlIHRoYXQgZGVjbGFyZXMgdGhlIHR5cGUg4oCUIG5lc3RlZCByZWZlcmVuY2VzIHJlc29sdmUgYWdhaW5zdCBpdCAqL1xuXHRmaWxlOiBzdHJpbmc7XG59XG5cbi8qKlxuICogT25lIGltcG9ydCBiaW5kaW5nIG9mIGEgcmVmZXJlbmNlZCB0eXBlOiB0aGUgbG9jYWwgbmFtZSB1bmRlciB3aGljaCB0aGVcbiAqIGZpbGUga25vd3MgaXQsIHRoZSBvcmlnaW5hbCBleHBvcnRlZCBuYW1lIGluIHRoZSBzb3VyY2UgbW9kdWxlLCBhbmQgdGhlXG4gKiBzcGVjaWZpZXIgaXQgY2FtZSBmcm9tLlxuICovXG5pbnRlcmZhY2UgUmVmZXJlbmNlZFR5cGVJbXBvcnQge1xuXHRvcmlnaW5hbE5hbWU6IHN0cmluZztcblx0c3BlY2lmaWVyOiBzdHJpbmc7XG5cdGlzTmFtZXNwYWNlOiBib29sZWFuO1xufVxuXG4vKipcbiAqIFJlc3VsdCBvZiByZXNvbHZpbmcgb25lIG1vZHVsZSBzcGVjaWZpZXIgZnJvbSBvbmUgY29udGFpbmluZyBmaWxlLlxuICovXG5pbnRlcmZhY2UgUmVmZXJlbmNlZFR5cGVSZXNvbHV0aW9uIHtcblx0cmVzb2x2ZWRQYXRoOiBzdHJpbmc7XG5cdGlzRXh0ZXJuYWw6IGJvb2xlYW47XG59XG5cbnR5cGUgQ29uc3RydWN0b3JIYW5kbGVyID0gdHMuRXhwcmVzc2lvbiB8IHRzLkZ1bmN0aW9uRGVjbGFyYXRpb24gfCB0cy5DbGFzc0RlY2xhcmF0aW9uO1xudHlwZSBGdW5jdGlvbkNvbnN0cnVjdG9ySGFuZGxlciA9IHRzLkZ1bmN0aW9uRXhwcmVzc2lvbiB8IHRzLkFycm93RnVuY3Rpb24gfCB0cy5GdW5jdGlvbkRlY2xhcmF0aW9uO1xudHlwZSBDbGFzc0NvbnN0cnVjdG9ySGFuZGxlciA9IHRzLkNsYXNzRXhwcmVzc2lvbiB8IHRzLkNsYXNzRGVjbGFyYXRpb247XG5cbi8qKlxuICogR2xvYmFsL2J1aWx0aW4gdHlwZSBuYW1lcyB0aGF0IGFyZSBzYWZlIHRvIGVtaXQgYmFyZSBpbnRvIGdlbmVyYXRlZCBmaWxlc1xuICog4oCUIHRoZXkgcmVzb2x2ZSBpbiBhbnkgVHlwZVNjcmlwdCBjb21waWxhdGlvbiB3aXRob3V0IGFuIGltcG9ydC5cbiAqL1xuY29uc3QgS05PV05fR0xPQkFMX1RZUEVTID0gbmV3IFNldChbXG5cdCdEYXRlJywgJ1JlZ0V4cCcsICdFcnJvcicsICdFdmFsRXJyb3InLCAnUmFuZ2VFcnJvcicsICdSZWZlcmVuY2VFcnJvcicsXG5cdCdTeW50YXhFcnJvcicsICdUeXBlRXJyb3InLCAnVVJJRXJyb3InLCAnQWdncmVnYXRlRXJyb3InLFxuXHQnTWFwJywgJ1NldCcsICdXZWFrTWFwJywgJ1dlYWtTZXQnLCAnV2Vha1JlZicsICdGaW5hbGl6YXRpb25SZWdpc3RyeScsXG5cdCdQcm9taXNlJywgJ0FycmF5JywgJ1JlYWRvbmx5QXJyYXknLCAnUmVjb3JkJywgJ1BhcnRpYWwnLCAnUmVxdWlyZWQnLFxuXHQnUmVhZG9ubHknLCAnUGljaycsICdPbWl0JywgJ0V4Y2x1ZGUnLCAnRXh0cmFjdCcsICdOb25OdWxsYWJsZScsXG5cdCdSZXR1cm5UeXBlJywgJ0luc3RhbmNlVHlwZScsICdQYXJhbWV0ZXJzJywgJ0NvbnN0cnVjdG9yUGFyYW1ldGVycycsXG5cdCdUaGlzVHlwZScsICdUaGlzUGFyYW1ldGVyVHlwZScsICdPbWl0VGhpc1BhcmFtZXRlcicsXG5cdCdVcHBlcmNhc2UnLCAnTG93ZXJjYXNlJywgJ0NhcGl0YWxpemUnLCAnVW5jYXBpdGFsaXplJyxcblx0J1N0cmluZycsICdOdW1iZXInLCAnQm9vbGVhbicsICdTeW1ib2wnLCAnQmlnSW50JywgJ09iamVjdCcsICdGdW5jdGlvbicsXG5cdCdJdGVyYWJsZScsICdJdGVyYXRvcicsICdHZW5lcmF0b3InLCAnQXN5bmNJdGVyYWJsZScsICdBc3luY0l0ZXJhdG9yJyxcblx0J0FzeW5jR2VuZXJhdG9yJywgJ0l0ZXJhYmxlSXRlcmF0b3InLCAnQXN5bmNJdGVyYWJsZUl0ZXJhdG9yJyxcblx0J1Byb3BlcnR5S2V5JywgJ0FycmF5QnVmZmVyJywgJ1NoYXJlZEFycmF5QnVmZmVyJywgJ0RhdGFWaWV3Jyxcblx0J0ludDhBcnJheScsICdVaW50OEFycmF5JywgJ1VpbnQ4Q2xhbXBlZEFycmF5JywgJ0ludDE2QXJyYXknLFxuXHQnVWludDE2QXJyYXknLCAnSW50MzJBcnJheScsICdVaW50MzJBcnJheScsICdGbG9hdDMyQXJyYXknLFxuXHQnRmxvYXQ2NEFycmF5JywgJ0JpZ0ludDY0QXJyYXknLCAnQmlnVWludDY0QXJyYXknLCAnSW50bCdcbl0pO1xuXG4vLyBHZW5lcmljIGdsb2JhbHMgd2hvc2UgYmFyZSBlbWlzc2lvbiB3b3VsZCBiZSBpbnZhbGlkIFRTIChUUzIzMTQpOlxuLy8gYG5ldyBNYXAoKWAgY2FycmllcyBubyB0eXBlIGFyZ3VtZW50cywgc28gdGhlIGZpZWxkIHR5cGUgZmlsbHMgdGhlbVxuLy8gd2l0aCB1bmtub3duLiBLZXlzIG11c3QgYWxzbyBiZSBtZW1iZXJzIG9mIEtOT1dOX0dMT0JBTF9UWVBFUy5cbmNvbnN0IEdFTkVSSUNfR0xPQkFMX0RFRkFVTFRfQVJHUyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KFtcblx0WyAnTWFwJywgJ01hcDx1bmtub3duLCB1bmtub3duPicgXSxcblx0WyAnV2Vha01hcCcsICdXZWFrTWFwPG9iamVjdCwgdW5rbm93bj4nIF0sXG5cdFsgJ1NldCcsICdTZXQ8dW5rbm93bj4nIF0sXG5cdFsgJ1dlYWtTZXQnLCAnV2Vha1NldDxvYmplY3Q+JyBdLFxuXHRbICdXZWFrUmVmJywgJ1dlYWtSZWY8b2JqZWN0PicgXSxcblx0WyAnRmluYWxpemF0aW9uUmVnaXN0cnknLCAnRmluYWxpemF0aW9uUmVnaXN0cnk8dW5rbm93bj4nIF0sXG5cdFsgJ1Byb21pc2UnLCAnUHJvbWlzZTx1bmtub3duPicgXSxcblx0WyAnQXJyYXknLCAnQXJyYXk8dW5rbm93bj4nIF0sXG5cdFsgJ1JlYWRvbmx5QXJyYXknLCAnUmVhZG9ubHlBcnJheTx1bmtub3duPicgXVxuXSk7XG5cbi8vIEJvdW5kIGZvciBjaGFzaW5nIHJlLWV4cG9ydCBiYXJyZWxzIChleHBvcnQgeyBYIH0gZnJvbSAn4oCmJywgZXhwb3J0ICogZnJvbSAn4oCmJylcbmNvbnN0IE1BWF9SRUVYUE9SVF9DSEFTRV9ERVBUSCA9IDU7XG4vLyBCb3VuZCBmb3Igd2Fsa2luZyBjbGFzcy9pbnRlcmZhY2UgZXh0ZW5kcyBjaGFpbnMgZHVyaW5nIHJlZmVyZW5jZWQtdHlwZVxuLy8gZXhwYW5zaW9uIChpbmhlcml0ZWQgbWVtYmVycyBtZXJnZSBpbnRvIHRoZSBleHBhbmRlZCBmaWVsZHMpXG5jb25zdCBNQVhfSEVSSVRBR0VfREVQVEggPSA4O1xuXG4vKipcbiAqIEFTVCBBbmFseXplciBmb3IgZmluZGluZyBNbmVtb25pY2EgZGVmaW5lKCkgYW5kIGRlY29yYXRlKCkgY2FsbHNcbiAqXG4gKiBGcmFtZXdvcmstYmxpbmQgYnkgY29uc3RydWN0aW9uOiBpbnN0cnVtZW50YXRpb24gZGV0ZWN0aW9uIHZvY2FidWxhcnlcbiAqIChpbnRlcmZhY2UgbmFtZXMsIGRlY29yYXRvciBuYW1lcywgcHJvdmlkZXIgdG9rZW5zLCBtaWRkbGV3YXJlIHdpcmluZylcbiAqIGNvbWVzIGVudGlyZWx5IGZyb20gcGx1Z2lucyDigJQgd2l0aCBub25lIGxvYWRlZCwgemVybyBwb2ludHMgYXJlIGNvbGxlY3RlZC5cbiAqL1xuZXhwb3J0IGNsYXNzIE1uZW1vbmljYUFuYWx5emVyIHtcblx0cHJpdmF0ZSBlcnJvcnM6IEFuYWx5emVFcnJvcltdID0gW107XG5cdHByaXZhdGUgZ3JhcGggPSBuZXcgVHlwZUdyYXBoSW1wbCgpO1xuXHRwcml2YXRlIGRlZmluaXRpb25zID0gbmV3IE1hcDxzdHJpbmcsIERlZmluaXRpb25JbmZvPigpO1xuXHRwcml2YXRlIHVzYWdlcyA9IG5ldyBNYXA8c3RyaW5nLCBVc2FnZUluZm9bXT4oKTtcblx0cHJpdmF0ZSBlZHNVc2FnZXMgPSBuZXcgTWFwPHN0cmluZywgRURTSW5mb1tdPigpO1xuXHRwcml2YXRlIGZsb3dVc2FnZXMgPSBuZXcgTWFwPHN0cmluZywgRmxvd0luZm9bXT4oKTtcblx0Ly8gRW5jbG9zaW5nIG1uZW1vbmljYSBzY29wZSBmb3IgRURTIGtleWluZzogZGVmaW5lKCkvbGF6eSgpIGNhbGwgbm9kZVxuXHQvLyBvciBAZGVjb3JhdGUoKS1lZCBjbGFzcyBkZWNsYXJhdGlvbiAtPiBmdWxsUGF0aCBvZiB0aGUgdHlwZSBpdCBvd25zLlxuXHQvLyBQb3B1bGF0ZWQgb24gdGhlIGRlZmluaXRpb25zIHBhc3M7IEFTVCBub2RlcyBwZXJzaXN0IGFjcm9zcyBwYXNzZXMsXG5cdC8vIHNvIGVudHJpZXMgc3RheSB2YWxpZCBhZnRlciByZXNldFVzYWdlcygpLlxuXHRwcml2YXRlIGVkc1Njb3BlQnlOb2RlID0gbmV3IE1hcDx0cy5Ob2RlLCBzdHJpbmc+KCk7XG5cdC8vIFNhbWUtZmlsZSBmdW5jdGlvbiBiaW5kaW5ncyAoYGZpbGVOYW1lI25hbWVgIC0+IGZ1bmN0aW9uIG5vZGUpIGZvclxuXHQvLyByZXNvbHZpbmcgd3JhcChmbikgYXJndW1lbnRzIHN5bnRhY3RpY2FsbHkg4oCUIHRoZSBjaGVja2VyIHN0YXlzIHVudXNlZFxuXHRwcml2YXRlIGZ1bmN0aW9uQmluZGluZ3MgPSBuZXcgTWFwPHN0cmluZywgdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb24+KCk7XG5cdC8vIENvbnN0cnVjdG9yIHZhbHVlcyBieSBkZWNsYXJpbmcgZmlsZSBhbmQgZXhwb3J0ZWQvbG9jYWwgbmFtZS4gUmVzb2x1dGlvblxuXHQvLyB1c2VzIHRoZSBzYW1lIGltcG9ydCBhbmQgcmUtZXhwb3J0IHdpcmluZyBhcyByZWZlcmVuY2VkLXR5cGUgZGVjbGFyYXRpb25zLlxuXHRwcml2YXRlIGNvbnN0cnVjdG9yQmluZGluZ3MgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgQ29uc3RydWN0b3JIYW5kbGVyPj4oKTtcblx0Ly8gd3JhcCBjYWxsIG5vZGUgLT4gbG9jYXRpb24gb2YgdGhlIGVuY2xvc2luZyB3cmFwIHNpdGUgKHBsdXMgdGhhdFxuXHQvLyBzaXRlJ3Mgc2NvcGUgYXR0cmlidXRpb24pLCBzbyBuZXN0ZWQgd3JhcCgpIGNhbGxzIGluc2lkZSBhIHdyYXBwZWRcblx0Ly8gYm9keSBjYXJyeSB0aGUgYHZpYWAgbGluayDigJQgYW5kIGluaGVyaXQgdGhlIHNjb3BlIHdoZW4gdGhleSBoYXZlXG5cdC8vIG5vbmUgb2YgdGhlaXIgb3duXG5cdHByaXZhdGUgbmVzdGVkV3JhcFZpYSA9IG5ldyBNYXA8dHMuTm9kZSwgeyB2aWE6IHN0cmluZzsgc2NvcGU/OiBzdHJpbmcgfT4oKTtcblx0Ly8gd3JhcCBjYWxsIG5vZGUgLT4gaXRzIGNvbGxlY3RlZCBlbnRyeSwgc28gYSBsZXhpY2FsbHkgbmVzdGVkIHdyYXBcblx0Ly8gKHZpc2l0ZWQgQkVGT1JFIHRoZSBvdXRlciB3cmFwIGNhbGwsIHBlciBzb3VyY2Ugb3JkZXIpIGdldHMgaXRzXG5cdC8vIGB2aWFgIGJhY2stcGF0Y2hlZCB3aGVuIHRoZSBvdXRlciBib2R5IGlzIGFuYWx5c2VkXG5cdHByaXZhdGUgd3JhcEVudHJ5QnlOb2RlID0gbmV3IE1hcDx0cy5Ob2RlLCBFRFNJbmZvPigpO1xuXHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50czogdmFyaWFibGVOYW1lIC0+IGZ1bGxQYXRoIG9mIHRoZSB0eXBlIGl0IGhvbGRzXG5cdHByaXZhdGUgdmFyaWFibGVUb1R5cGVNYXAgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHQvLyBFeHBvcnRlZCBidWlsZGVyIHZhbHVlcyBhbmQgdGhlaXIgdHJhbnNpdGl2ZSBzZWxmLXJlZmVyZW5jZSBleGNsdXNpb25zLlxuXHRwcml2YXRlIGJ1aWxkZXJDYW5kaWRhdGVzOiBCdWlsZGVyQ2FuZGlkYXRlW10gPSBbXTtcblx0cHJpdmF0ZSBleGNsdWRlZFR5cGVQYXRocyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRwcml2YXRlIGdlbmVyYXRlZFR5cGVJbXBvcnRzID0gbmV3IE1hcDxzdHJpbmcsIFNldDxzdHJpbmc+PigpO1xuXHQvLyBBYnNvbHV0ZSBkaXJlY3RvcmllcyBob2xkaW5nIHRoZSBnZW5lcmF0ZWQgb3V0cHV0OyBhbiBpbXBvcnQgcmVzb2x2aW5nXG5cdC8vIGludG8gb25lIG9mIHRoZW0gKHJlbGF0aXZlIG9yIHRocm91Z2ggdHNjb25maWcgYHBhdGhzYCkgaXMgZ2VuZXJhdGVkXG5cdHByaXZhdGUgZ2VuZXJhdGVkT3V0cHV0RGlyczogc3RyaW5nW10gPSBbXTtcblx0Ly8gYCR7Y29udGFpbmluZ0ZpbGV9Ojoke3NwZWNpZmllcn1gIC0+IGRvZXMgaXQgcmVzb2x2ZSBpbnRvIHRoZSBvdXRwdXRcblx0cHJpdmF0ZSBnZW5lcmF0ZWRTcGVjaWZpZXJDYWNoZSA9IG5ldyBNYXA8c3RyaW5nLCBib29sZWFuPigpO1xuXHQvLyBUcmFjayBtbmVtb25pY2EgbW9kdWxlLW9iamVjdCB2YXJpYWJsZXMgKGUuZy4sIGltcG9ydCB7IG1uZW1vbmljYSB9IGZyb20gJ21uZW1vbmljYSc7IGNvbnN0IG0gPSBtbmVtb25pY2EpXG5cdHByaXZhdGUgbW9kdWxlT2JqZWN0VmFyaWFibGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdC8vIGZpbGUgLT4gKGxvY2FsIG5hbWUgLT4gaW1wb3J0ZWQgbmFtZSkgZm9yIG5hbWVkIGltcG9ydHMgZnJvbVxuXHQvLyAnbW5lbW9uaWNhJyDigJQgaW1wb3J0LWF3YXJlbmVzcyBmb3IgdGhlIGNvbnN0cnVjdGlvbi1mdW5jdGlvblxuXHQvLyByZWNvZ25pdGlvbiAoY2FsbC9hcHBseS9iaW5kKSBhbmQgdGhlIHV0aWxzIGZvcm1zIChtZXJnZS9mb3JrKTpcblx0Ly8gdXNlcmxhbmQgZnVuY3Rpb25zIHdpdGggdGhvc2UgbmFtZXMgbXVzdCBuZXZlciBtYXRjaFxuXHRwcml2YXRlIG1uZW1vbmljYU5hbWVkSW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBUcmFjayBpbXBvcnRlZCBhbGlhc2VzIG9mIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbiAoZS5nLiwgaW1wb3J0IHsgY3JlYXRlVHlwZXNDb2xsZWN0aW9uIGFzIGN0YyB9KVxuXHRwcml2YXRlIGNyZWF0ZVR5cGVzQ29sbGVjdGlvblZhcmlhYmxlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHQvLyBUcmFjayBjdXN0b20gY29sbGVjdGlvbiB2YXJpYWJsZXM6IHZhcmlhYmxlTmFtZSAtPiBjb2xsZWN0aW9uSWRcblx0cHJpdmF0ZSBjb2xsZWN0aW9uVmFyaWFibGVzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0Ly8gVHJhY2sgY3VzdG9tIGNvbGxlY3Rpb24gbWV0YWRhdGEgZm9yIE9wdGlvbiBCIHJlZ2lzdHJ5IGVtaXNzaW9uXG5cdHByaXZhdGUgY29sbGVjdGlvbkluZm8gPSBuZXcgTWFwPHN0cmluZywgQ29sbGVjdGlvbkluZm8+KCk7XG5cdHByaXZhdGUgY29sbGVjdGlvbkNvdW50ZXIgPSAwO1xuXHQvLyBJbnN0cnVtZW50YXRpb24gY29sbGVjdGlvbiAoc3ludGFjdGljIG9ubHkg4oCUIG5vIHR5cGUgY2hlY2tlcik6XG5cdC8vIGV2ZXJ5IG5hbWVkIGNsYXNzIGRlY2xhcmF0aW9uIGJ5IHNpbXBsZSBuYW1lLCBmb3IgcmVzb2x2aW5nXG5cdC8vIHJlZ2lzdHJhdGlvbiBzaXRlcyB0byBkZWNsYXJhdGlvbiBsb2NhdGlvbnMgKGJlc3QgZWZmb3J0LCBsYXN0IHdpbnMpXG5cdHByaXZhdGUgaW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNscyA9IG5ldyBNYXA8c3RyaW5nLCBJbnN0cnVtZW50YXRpb25DbGFzc0RlY2w+KCk7XG5cdC8vIFJlZ2lzdHJhdGlvbiBzaXRlczogZGVjb3JhdG9yIGFwcGxpY2F0aW9ucywgcHJvdmlkZXItdG9rZW4gb2JqZWN0XG5cdC8vIGxpdGVyYWxzLCBjb25zdW1lci5hcHBseSgpIG1pZGRsZXdhcmUgd2lyaW5nXG5cdHByaXZhdGUgaW5zdHJ1bWVudGF0aW9uU2l0ZXM6IEluc3RydW1lbnRhdGlvblNpdGVbXSA9IFtdO1xuXHQvLyBNZXJnZWQgcGx1Z2luIHZvY2FidWxhcnkgZm9yIGluc3RydW1lbnRhdGlvbiBkZXRlY3Rpb24gKGVtcHR5IHdoZW5cblx0Ly8gbm8gcGx1Z2lucyB3ZXJlIHBhc3NlZCDigJQgdGhlIGFuYWx5emVyIHRoZW4gY29sbGVjdHMgbm8gcG9pbnRzKVxuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvblZvY2FidWxhcnk6IEluc3RydW1lbnRhdGlvblZvY2FidWxhcnk7XG5cdC8vIFJlZmVyZW5jZWQtdHlwZSByZXNvbHV0aW9uIChGMTApOiBwZXItZmlsZSBkZWNsYXJhdGlvbnMgYW5kIGltcG9ydHMuXG5cdC8vIEEgdHlwZSBuYW1lIHVzZWQgaW4gZmlsZSBYIHJlc29sdmVzIHRocm91Z2ggWCdzIG93biBpbXBvcnQgc3RhdGVtZW50c1xuXHQvLyBmaXJzdCAocmVsYXRpdmUgKyB0c2NvbmZpZy1wYXRocywgdmlhIHRzLnJlc29sdmVNb2R1bGVOYW1lKSwgdGhlblxuXHQvLyBYJ3MgbG9jYWwgZGVjbGFyYXRpb25zLCB0aGVuIOKAlCBvbmx5IHdoZW4gbm90aGluZyBpbXBvcnRzIG9yIGRlY2xhcmVzXG5cdC8vIHRoZSBuYW1lIOKAlCB0aGUgdW5pcXVlIHNhbWUtbmFtZWQgZGVjbGFyYXRpb24gYWNyb3NzIHNjYW5uZWQgZmlsZXMuXG5cdC8vIEdlbnVpbmUgYW1iaWd1aXR5IG9yIGFuIHVucmVzb2x2YWJsZSByZWZlcmVuY2UgeWllbGRzIGB1bmtub3duYCwgbmV2ZXJcblx0Ly8gYSBiYXJlIGVtaXR0ZWQgbmFtZTogZ2VuZXJhdGVkIHR5cGVzLnRzIGNhcnJpZXMgbm8gaW1wb3J0cyBvZiBpdHMgb3duLlxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlRGVjbHMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbj4+KCk7XG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVJbXBvcnRzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlSW1wb3J0Pj4oKTtcblx0Ly8gZmlsZSAtPiAoZXhwb3J0ZWQgbmFtZSAtPiByZS1leHBvcnQgc3BlY2lmaWVyKSBmb3IgYGV4cG9ydCB7IFggfSBmcm9tICfigKYnYFxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHN0cmluZz4+KCk7XG5cdC8vIGZpbGUgLT4gc3BlY2lmaWVycyBvZiBgZXhwb3J0ICogZnJvbSAn4oCmJ2Bcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZUV4cG9ydFN0YXJzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZ1tdPigpO1xuXHQvLyBmaWxlIC0+IChleHBvcnRlZCBuYW1lIC0+IGxvY2FsIG5hbWUpIGZvciBgZXhwb3J0IHsgWCBhcyBZIH1gXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVFeHBvcnRBbGlhc2VzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHN0cmluZz4+KCk7XG5cdC8vIGZpbGUgLT4gKG5hbWVzcGFjZSBuYW1lIC0+IG5hbWVzcGFjZSBkZWNsYXJhdGlvbikg4oCUIG1pZGRsZSBzZWdtZW50c1xuXHQvLyBvZiBxdWFsaWZpZWQgcmVmZXJlbmNlcyAobW9kZWxzLklubmVyLkNyYXRlKSBkZXNjZW5kIHRocm91Z2ggdGhlc2Vcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgdHMuTW9kdWxlRGVjbGFyYXRpb24+PigpO1xuXHQvLyBmaWxlIC0+IChuYW1lc3BhY2UgbmFtZSAtPiBzcGVjaWZpZXIpIGZvciBgZXhwb3J0ICogYXMgbnMgZnJvbSAn4oCmJ2Bcblx0Ly8gYmFycmVscyDigJQgYSBuZXN0ZWQgbW9kdWxlIG5hbWVzcGFjZSBvbmUgc2VnbWVudCBkZWVwXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VTdGFycyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBgJHtjb250YWluaW5nRmlsZX06OiR7c3BlY2lmaWVyfWAgLT4gcmVzb2x1dGlvbiAodW5kZWZpbmVkID0gZmFpbGVkKVxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbkNhY2hlID0gbmV3IE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbiB8IHVuZGVmaW5lZD4oKTtcblx0Ly8gZmlsZSAtPiAoY29uc3QgbmFtZSAtPiBhcnJheSBsaXRlcmFsKSBmb3IgY29uc3RzIHdpdGggYXJyYXktbGl0ZXJhbFxuXHQvLyBpbml0aWFsaXplcnMgKGBhcyBjb25zdGAgLyBgc2F0aXNmaWVzYCB1bndyYXBwZWQpLCBzbyBhXG5cdC8vIGB0eXBlb2Ygc3RhdHVzTGlzdFtudW1iZXJdYCBmaWVsZCB0eXBlIGV4cGFuZHMgdG8gdGhlIGVsZW1lbnQgbGl0ZXJhbFxuXHQvLyB1bmlvbiBpbnN0ZWFkIG9mIGxlYWtpbmcgYSBiYXJlIHVucmVzb2x2YWJsZSBgdHlwZW9mYCBxdWVyeSBpbnRvIHRoZVxuXHQvLyBnZW5lcmF0ZWQgZmlsZS4gRGVjbGFyYXRpb25zIHBlcnNpc3QgYWNyb3NzIHBhc3NlcyDigJQgZW50cmllcyBzdGF5XG5cdC8vIHZhbGlkIGFmdGVyIHJlc2V0VXNhZ2VzKCksIHNhbWUgYXMgcmVmZXJlbmNlZFR5cGVEZWNsc1xuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgdHMuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbj4+KCk7XG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVDb21waWxlck9wdGlvbnM6IHRzLkNvbXBpbGVyT3B0aW9ucztcblx0Ly8gRmlsZSB3aG9zZSBBU1QgaXMgY3VycmVudGx5IGJlaW5nIHZpc2l0ZWQ7IHJlZmVyZW5jZXMgcmVzb2x2ZSBhZ2FpbnN0IGl0XG5cdHByaXZhdGUgY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9ICcnO1xuXHQvLyBBbGlhcyBuYW1lcyBjdXJyZW50bHkgYmVpbmcgZXhwYW5kZWQgKGN5Y2xlIGd1YXJkKVxuXHRwcml2YXRlIGV4cGFuZGluZ1JlZmVyZW5jZWRBbGlhc2VzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdC8vIE1uZW1vbmljYS1ncmFwaCBpZGVudGl0eSBsYXcgKGhhcmQgZmFpbCk6IGV2ZXJ5IGRlZmluZSgpL2xhenkoKS9cblx0Ly8gQGRlY29yYXRlKCkgc2l0ZSBrZXllZCBieSBpdHMgcnVudGltZSBuYW1lc3BhY2UgKGNvbGxlY3Rpb24gcm9vdHM6XG5cdC8vIGA8Y29sbGVjdGlvbj46OjxuYW1lPmA7IHN1YnR5cGVzOiBgPHBhcmVudEZ1bGxQYXRoPi48bmFtZT5gKS4gVHdvXG5cdC8vIHNpdGVzIGluIG9uZSBuYW1lc3BhY2UgYXJlIGEgc2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlIOKAlCB0aGUgcnVudGltZVxuXHQvLyB0aHJvd3MgQUxSRUFEWV9ERUNMQVJFRCDigJQgYW5kIG11c3QgYWJvcnQgZ2VuZXJhdGlvbi5cblx0cHJpdmF0ZSBkZWZpbmVTaXRlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmdbXT4oKTtcblx0Ly8gTW5lbW9uaWNhLWdyYXBoIHJlZmVyZW5jZXMgdGhhdCBzdGF5ZWQgYW1iaWd1b3VzIGFmdGVyIHBhdGgtYXdhcmVcblx0Ly8gcmVzb2x1dGlvbiBvciByZXNvbHZlZCB0byBub3RoaW5nIChoYXJkLWZhaWwgY2xhc3MgMilcblx0cHJpdmF0ZSBncmFwaFJlZmVyZW5jZUVycm9yczogUmVzb2x1dGlvbkVycm9yW10gPSBbXTtcblx0Ly8gR3VhcmRzIGxvb2t1cCgpLXBhdGggdmFsaWRhdGlvbiBzbyBpdCBydW5zIG9uY2UgcGVyIHVzYWdlcyBwYXNzXG5cdC8vIChnZXRSZXNvbHV0aW9uRXJyb3JzIG1heSBiZSBjYWxsZWQgcmVwZWF0ZWRseSk7IHJlc2V0VXNhZ2VzIHJlLWFybXMgaXRcblx0cHJpdmF0ZSBsb29rdXBSZWZlcmVuY2VzVmFsaWRhdGVkID0gZmFsc2U7XG5cdC8vIExpdGVyYWwgbG9va3VwKCkgY2FsbCBzaXRlcyB3aXRoIHRoZWlyIHJlc29sdmVkIHBhdGhzLiBLZXB0IGFwYXJ0IGZyb21cblx0Ly8gdGhlIHVzYWdlcyBtYXAgb24gcHVycG9zZTogYWRkVXNhZ2UgZHJvcHMgcGF0aHMgdGhlIGdyYXBoIGRvZXMgbm90XG5cdC8vIGtub3cgKHVzYWdlcy5qc29uIGluZGV4ZXMgcmVmZXJlbmNlcyB0byBLTk9XTiB0eXBlcyksIGJ1dCBhbiB1bmtub3duXG5cdC8vIGxvb2t1cCBwYXRoIGlzIGV4YWN0bHkgdGhlIGhhcmQtZmFpbCBjYXNlIOKAlCB0aGUgcnVudGltZSByZXR1cm5zXG5cdC8vIHVuZGVmaW5lZCB0aGVyZSBhbmQgdGhlIFR5cGVFcnJvciBhcnJpdmVzIG9uZSBsaW5lIGxhdGVyXG5cdHByaXZhdGUgbG9va3VwUmVmZXJlbmNlczogeyBwYXRoOiBzdHJpbmc7IGxvY2F0aW9uOiBzdHJpbmcgfVtdID0gW107XG5cdC8vIEd1YXJkcyBwbGFpbi1UUyByZWZlcmVuY2UgdmFsaWRhdGlvbiBzbyBpdCBydW5zIG9uY2UgcGVyIHVzYWdlcyBwYXNzXG5cdC8vIChnZXRSZXNvbHV0aW9uRXJyb3JzIG1heSBiZSBjYWxsZWQgcmVwZWF0ZWRseSk7IHJlc2V0VXNhZ2VzIHJlLWFybXMgaXRcblx0cHJpdmF0ZSBwbGFpblR5cGVSZWZlcmVuY2VzVmFsaWRhdGVkID0gZmFsc2U7XG5cdC8vIFBsYWluLVRTIHR5cGUgcmVmZXJlbmNlIHNpdGVzIHdob3NlIHJlc29sdXRpb24gZmVsbCB0aHJvdWdoIGltcG9ydHMsXG5cdC8vIGxvY2FscywgdGhlIHByb2dyYW0td2lkZSBzY2FuLCBhbmQgdGhlIGdyYXBoIHRvIGEgc29mdCBgdW5rbm93bmAuXG5cdC8vIFZhbGlkYXRlZCBsYXppbHkgZnJvbSBnZXRSZXNvbHV0aW9uRXJyb3JzIGFnYWluc3QgdGhlIGNvbXBsZXRlXG5cdC8vIGRlY2xhcmF0aW9uIG1hcDogYSBuYW1lIHNldmVyYWwgcHJvamVjdC1zb3VyY2UgZmlsZXMgZGVjbGFyZSDigJQgd2l0aFxuXHQvLyBubyBpbXBvcnQgaW4gdGhlIHJlZmVyZW5jaW5nIGZpbGUgdG8gYW5jaG9yIGl0IOKAlCBpcyB0aGUgcGxhaW4tVFNcblx0Ly8gYW1iaWd1aXR5IGhhcmQtZmFpbCBjbGFzcyAob25lIHRpZXIgYmVsb3cgdGhlIGdyYXBoIGlkZW50aXR5IGxhdyk7XG5cdC8vIGFic2VuY2UgKGdob3N0IG5hbWVzKSBzdGF5cyBzb2Z0LiBSZWNvcmRpbmcgaGFwcGVucyBvbiBldmVyeSBwYXNzLFxuXHQvLyB0aGUgdmVyZGljdCBvbmx5IGhlcmUg4oCUIHBhc3MgMSBzZWVzIGFuIGluY29tcGxldGUgZGVjbGFyYXRpb24gbWFwLFxuXHQvLyBzbyBvbmx5IHRoZSB1c2FnZXMgcGFzcyBpcyBhdXRob3JpdGF0aXZlIChtaXJyb3JzIGxvb2t1cCByZWZlcmVuY2VzKVxuXHRwcml2YXRlIHBsYWluVHlwZVJlZmVyZW5jZXM6IHsgbmFtZTogc3RyaW5nOyBsb2NhdGlvbjogc3RyaW5nOyBmaWxlOiBzdHJpbmcgfVtdID0gW107XG5cdC8vIFBlci1maWxlIHRvcC1sZXZlbCB2YXJpYWJsZSAtPiBtbmVtb25pY2EgZnVsbFBhdGggYmluZGluZ3MgKHZhbHVlXG5cdC8vIHNjb3BlKTogYGNvbnN0IEFkZHJlc3MgPSBVc2VyLmRlZmluZSgnQWRkcmVzcycsIOKApilgIG1ha2VzIGBBZGRyZXNzYFxuXHQvLyBkZW5vdGUgVXNlci5BZGRyZXNzIHdoZXJldmVyIHRoYXQgZmlsZSdzIHJlZmVyZW5jZXMgYXJlIHJlc29sdmVkXG5cdHByaXZhdGUgZmlsZUdyYXBoQmluZGluZ3MgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgc3RyaW5nPj4oKTtcblx0Ly8gVGhlIGdyYXBoIHR5cGUgd2hvc2UgY29uc3RydWN0b3IgaXMgY3VycmVudGx5IGJlaW5nIGV4dHJhY3RlZDtcblx0Ly8gYW5jaG9ycyByZWxhdGl2ZS1maXJzdCBncmFwaCByZWZlcmVuY2UgcmVzb2x1dGlvblxuXHRwcml2YXRlIGN1cnJlbnRHcmFwaEFuY2hvcjogVHlwZU5vZGUgfCB1bmRlZmluZWQ7XG5cdC8vIGRlZmluZSgpL2xhenkoKSBjYWxscyBhbHJlYWR5IGV4dHJhY3RlZCB0aGlzIHBhc3MuIFRoZSBDTEkgcmUtYW5hbHl6ZXNcblx0Ly8gZXZlcnkgZmlsZSBhZnRlciByZXNldFVzYWdlcygpOyBjbGVhcmluZyB0aGUgc2V0IGxldHMgdGhlIHNlY29uZCBwYXNzXG5cdC8vIHJlLWV4dHJhY3QgZXZlcnkgY29uc3RydWN0b3IgYWdhaW5zdCB0aGUgQ09NUExFVEUgZ3JhcGgg4oCUIHBhc3MgMSBzZWVzXG5cdC8vIGZvcndhcmQgcmVmZXJlbmNlcyBhcyBgbm9uZWAgKHNvZnQgdW5rbm93bikgYmVjYXVzZSBsYXRlciBmaWxlcyBoYXZlXG5cdC8vIG5vdCBiZWVuIHZpc2l0ZWQgeWV0LCBzbyBvbmx5IHBhc3MtMiByZXNvbHV0aW9uIGlzIGF1dGhvcml0YXRpdmUgZm9yXG5cdC8vIHRoZSBoYXJkLWZhaWwgaWRlbnRpdHkgbGF3LiBUaGUgc3RhbXAgbGl2ZXMgaGVyZSByYXRoZXIgdGhhbiBvbiB0aGVcblx0Ly8gQVNUIG5vZGUgc28gaXQgY2FuIGFjdHVhbGx5IGJlIGNsZWFyZWQuIChDaGFpbmVkIGNhbGxzIHZpc2l0IHRoZSBzYW1lXG5cdC8vIG5vZGUgdHdpY2Ugd2l0aGluIG9uZSBwYXNzOyB0aGUgaW4tcGFzcyBkZWR1cCBiZWxvdyBzdGF5cy4pXG5cdHByaXZhdGUgcHJvY2Vzc2VkQ2FsbHMgPSBuZXcgU2V0PHRzLkNhbGxFeHByZXNzaW9uPigpO1xuXG5cdGNvbnN0cnVjdG9yIChwcm9ncmFtPzogdHMuUHJvZ3JhbSwgcGx1Z2luczogVGFjdGljYVBsdWdpbltdID0gW10pIHtcblx0XHQvLyBDb21waWxlciBvcHRpb25zIGRyaXZlIHRzLnJlc29sdmVNb2R1bGVOYW1lIGZvciBpbXBvcnQtYXdhcmVcblx0XHQvLyByZWZlcmVuY2VkLXR5cGUgcmVzb2x1dGlvbiAodHNjb25maWcgYHBhdGhzYCwgZXh0ZW5zaW9ubGVzc1xuXHRcdC8vIGltcG9ydHMpOyB0aGUgdHlwZSBjaGVja2VyIGl0c2VsZiBzdGF5cyB1bnVzZWQuXG5cdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUNvbXBpbGVyT3B0aW9ucyA9IHByb2dyYW0/LmdldENvbXBpbGVyT3B0aW9ucygpID8/IHt9O1xuXHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeSA9IG1lcmdlVGFjdGljYVBsdWdpbnMocGx1Z2lucyk7XG5cdH1cblxuXHQvKipcblx0ICogRGlyZWN0b3JpZXMgaG9sZGluZyB0aGUgZ2VuZXJhdGVkIG91dHB1dC4gSW1wb3J0cyByZXNvbHZpbmcgaW50byB0aGVtXG5cdCAqIG5hbWUgZ2VuZXJhdGVkIHR5cGVzLCB3aGF0ZXZlciBzcGVjaWZpZXIgcmVhY2hlcyB0aGVtIChhIHJlbGF0aXZlXG5cdCAqIHBhdGgsIGEgdHNjb25maWcgYHBhdGhzYCBhbGlhcywgYSBjdXN0b20gLS1vdXRwdXQgbmFtZSkuXG5cdCAqL1xuXHRzZXRHZW5lcmF0ZWRPdXRwdXREaXJzIChkaXJzOiBzdHJpbmdbXSk6IHZvaWQge1xuXHRcdHRoaXMuZ2VuZXJhdGVkT3V0cHV0RGlycyA9IGRpcnMubWFwKGRpciA9PiBub2RlUGF0aC5yZXNvbHZlKGRpcikpO1xuXHRcdHRoaXMuZ2VuZXJhdGVkU3BlY2lmaWVyQ2FjaGUuY2xlYXIoKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNldCB1c2FnZS1yZWxhdGVkIHN0YXRlIGZvciBhIGZyZXNoIHBhc3MuXG5cdCAqIENhbGwgYmVmb3JlIHRoZSB1c2FnZS1jb2xsZWN0aW9uIHBhc3MgdG8gYXZvaWQgZHVwbGljYXRlcyBmcm9tIGRlZmluaXRpb24gcGFzcy5cblx0ICovXG5cdHJlc2V0VXNhZ2VzICgpOiB2b2lkIHtcblx0XHR0aGlzLnVzYWdlcy5jbGVhcigpO1xuXHRcdHRoaXMuZWRzVXNhZ2VzLmNsZWFyKCk7XG5cdFx0dGhpcy5mbG93VXNhZ2VzLmNsZWFyKCk7XG5cdFx0dGhpcy52YXJpYWJsZVRvVHlwZU1hcC5jbGVhcigpO1xuXHRcdC8vIEVEUyBlbnRyeSByZWZlcmVuY2VzIGdvIHN0YWxlIHdpdGggZWRzVXNhZ2VzOyB2aWEgbGlua3MgYXJlXG5cdFx0Ly8gcmUtZGVyaXZlZCBvbiB0aGUgbmV4dCBwYXNzXG5cdFx0dGhpcy53cmFwRW50cnlCeU5vZGUuY2xlYXIoKTtcblx0XHR0aGlzLm5lc3RlZFdyYXBWaWEuY2xlYXIoKTtcblx0XHQvLyBOb3RlOiBtb2R1bGVPYmplY3RWYXJpYWJsZXMgYW5kIGNvbGxlY3Rpb25WYXJpYWJsZXMgaW50ZW50aW9uYWxseSBwZXJzaXN0XG5cdFx0Ly8gYWNyb3NzIGRlZmluaXRpb24gYW5kIHVzYWdlIHBhc3Nlcy5cblx0XHQvLyBSZS1leHRyYWN0aW9uIGluIHRoZSB1c2FnZXMgcGFzcyBpcyB3aGF0IG1ha2VzIGdyYXBoIHJlZmVyZW5jZVxuXHRcdC8vIHJlc29sdXRpb24gYXV0aG9yaXRhdGl2ZTogcGFzcyAxIHJlc29sdmVzIGFnYWluc3QgYW4gaW5jb21wbGV0ZVxuXHRcdC8vIGdyYXBoIChmb3J3YXJkIHJlZmVyZW5jZXMgcmVhZCBhcyBgbm9uZWApLCBwYXNzIDIgYWdhaW5zdCBhbGwgb2YgaXQuXG5cdFx0dGhpcy5wcm9jZXNzZWRDYWxscy5jbGVhcigpO1xuXHRcdC8vIGxvb2t1cCgpLXBhdGggdmFsaWRhdGlvbiBydW5zIGFnYWluc3QgdGhlIHJlY29yZGVkIHNpdGVzOyBhIGZyZXNoXG5cdFx0Ly8gcGFzcyBtdXN0IHJlLXJlY29yZCBhbmQgcmUtdmFsaWRhdGUgKHBhc3MtMSByZXN1bHRzIHdvdWxkIGJlXG5cdFx0Ly8gcHJlbWF0dXJlIOKAlCB0aGUgZ3JhcGggaXMgc3RpbGwgaW5jb21wbGV0ZSlcblx0XHR0aGlzLmxvb2t1cFJlZmVyZW5jZXNWYWxpZGF0ZWQgPSBmYWxzZTtcblx0XHR0aGlzLmxvb2t1cFJlZmVyZW5jZXMgPSBbXTtcblx0XHR0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXNWYWxpZGF0ZWQgPSBmYWxzZTtcblx0XHR0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXMgPSBbXTtcblx0fVxuXG5cdC8qKlxuXHQgKiBBbmFseXplIGEgc291cmNlIGZpbGUgZm9yIE1uZW1vbmljYSB0eXBlIGRlZmluaXRpb25zXG5cdCAqL1xuXHRhbmFseXplRmlsZSAoc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IEFuYWx5emVSZXN1bHQge1xuXHRcdHRoaXMuZXJyb3JzID0gW107XG5cdFx0Ly8gUmVmZXJlbmNlZC10eXBlIG5hbWVzIGluIHRoaXMgZmlsZSByZXNvbHZlIGFnYWluc3QgaXRzIG93biBpbXBvcnRzXG5cdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gbm9kZVBhdGgucmVzb2x2ZShzb3VyY2VGaWxlLmZpbGVOYW1lKTtcblx0XHQvLyBFbnN1cmUgcGFyZW50IG5vZGVzIGFyZSBzZXQgZm9yIEFTVCB0cmF2ZXJzYWxcblx0XHR0aGlzLnNldFBhcmVudE5vZGVzSW5Tb3VyY2VGaWxlKHNvdXJjZUZpbGUpO1xuXHRcdHRoaXMudmlzaXROb2RlKHNvdXJjZUZpbGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0cmV0dXJuIHtcblx0XHRcdHR5cGVzICA6IHRoaXMuZ3JhcGguZ2V0QWxsVHlwZXMoKSxcblx0XHRcdGVycm9ycyA6IHRoaXMuZXJyb3JzLFxuXHRcdH07XG5cdH1cblxuXHQvKipcblx0ICogQW5hbHl6ZSBzb3VyY2UgY29kZSBzdHJpbmdcblx0ICovXG5cdGFuYWx5emVTb3VyY2UgKHNvdXJjZUNvZGU6IHN0cmluZywgZmlsZU5hbWUgPSAndGVtcC50cycpOiBBbmFseXplUmVzdWx0IHtcblx0XHRjb25zdCBzb3VyY2VGaWxlID0gdHMuY3JlYXRlU291cmNlRmlsZShcblx0XHRcdGZpbGVOYW1lLFxuXHRcdFx0c291cmNlQ29kZSxcblx0XHRcdHRzLlNjcmlwdFRhcmdldC5MYXRlc3QsXG5cdFx0XHR0cnVlXG5cdFx0KTtcblx0XHRyZXR1cm4gdGhpcy5hbmFseXplRmlsZShzb3VyY2VGaWxlKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgdGhlIHR5cGUgZ3JhcGhcblx0ICovXG5cdGdldEdyYXBoICgpOiBUeXBlR3JhcGhJbXBsIHtcblx0XHRyZXR1cm4gdGhpcy5ncmFwaDtcblx0fVxuXG5cdGdldEJ1aWxkZXJWYWx1ZXMgKCk6IEJ1aWxkZXJWYWx1ZVtdIHtcblx0XHRjb25zdCByZXN1bHQ6IEJ1aWxkZXJWYWx1ZVtdID0gW107XG5cdFx0Y29uc3Qgc2VlbiA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdGZvciAoY29uc3QgY2FuZGlkYXRlIG9mIHRoaXMuYnVpbGRlckNhbmRpZGF0ZXMpIHtcblx0XHRcdC8vIGV4Y2x1ZGVkVHlwZVBhdGhzIGNvdmVycyBib3RoIHBhc3NlczogYSBjYW5kaWRhdGUgcmVjb3JkZWQgaW5cblx0XHRcdC8vIHBhc3MgMSwgYmVmb3JlIGEgY3Jvc3MtZmlsZSBhbGlhcyB3YXMga25vd24sIHN0YXlzIGV4Y2x1ZGVkXG5cdFx0XHQvLyBvbmNlIHBhc3MgMiBmaW5kcyBpdHMgc2VsZi1yZWZlcmVuY2Vcblx0XHRcdGlmIChjYW5kaWRhdGUuZXhjbHVkZWQgfHwgdGhpcy5leGNsdWRlZFR5cGVQYXRocy5oYXMoY2FuZGlkYXRlLmZ1bGxQYXRoKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3QgZXhwb3J0ZWQgb2YgY2FuZGlkYXRlLmV4cG9ydHMpIHtcblx0XHRcdFx0Y29uc3Qga2V5ID1gJHtjYW5kaWRhdGUua2luZH18JHtleHBvcnRlZC5zb3VyY2VGaWxlfXwke2V4cG9ydGVkLm5hbWV9fCR7Y2FuZGlkYXRlLmZ1bGxQYXRofWA7XG5cdFx0XHRcdGlmIChzZWVuLmhhcyhrZXkpKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0c2Vlbi5hZGQoa2V5KTtcblx0XHRcdFx0cmVzdWx0LnB1c2goe1xuXHRcdFx0XHRcdG5hbWUgICAgICAgICAgOiBleHBvcnRlZC5uYW1lLFxuXHRcdFx0XHRcdHNvdXJjZUZpbGUgICAgOiBleHBvcnRlZC5zb3VyY2VGaWxlLFxuXHRcdFx0XHRcdGtpbmQgICAgICAgICAgOiBjYW5kaWRhdGUua2luZCxcblx0XHRcdFx0XHRmdWxsUGF0aCAgICAgIDogY2FuZGlkYXRlLmZ1bGxQYXRoLFxuXHRcdFx0XHRcdGRlZmF1bHRJbXBvcnQgOiBleHBvcnRlZC5kZWZhdWx0SW1wb3J0XG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBjb2xsZWN0ZWQgZGVmaW5pdGlvbnNcblx0ICovXG5cdGdldERlZmluaXRpb25zICgpOiBNYXA8c3RyaW5nLCBEZWZpbml0aW9uSW5mbz4ge1xuXHRcdHJldHVybiB0aGlzLmRlZmluaXRpb25zO1xuXHR9XG5cblx0LyoqXG5cdCAqIFRoZSBjb2xsZWN0aW9ucy5qc29uIG1hbmlmZXN0OiBvbmUgZW50cnkgcGVyIG1pbnRlZCBjb2xsZWN0aW9uLCBpblxuXHQgKiBtaW50aW5nIG9yZGVyLCBwcmVjZWRlZCBieSB0aGUgZGVmYXVsdC1jb2xsZWN0aW9uIGVudHJ5IHdoZW5ldmVyXG5cdCAqIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcyBleGlzdC4gVGhlIGRlZmF1bHQgZW50cnkgaGFzIG5vIGlkL2xvY2F0aW9uXG5cdCAqICh0aGVyZSBpcyBubyBjYWxsIHNpdGUg4oCUIHVucHJlZml4ZWQgZnVsbFBhdGhzIGFyZSBpdHMgaWRlbnRpdHkpLlxuXHQgKiBGb3JtYXQgMS4yOiB0aGUgcmVnaXN0cnkgaW50ZXJmYWNlIGlzIE5PVCBlbWl0dGVkIChpdCBpcyBhXG5cdCAqIFR5cGVTY3JpcHQtb25seSBjb25jZXJuIOKAlCB0aGUgaW4tbWVtb3J5IHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSB0aGF0XG5cdCAqIHR5cGVzLnRzL3JlZ2lzdHJ5LnRzIGFyZSBnZW5lcmF0ZWQgZnJvbSBzdGF5cyBvbiB0aGUgVHlwZU5vZGUpLlxuXHQgKi9cblx0Z2V0Q29sbGVjdGlvbnNNYW5pZmVzdCAoKTogQ29sbGVjdGlvbk1hbmlmZXN0RW50cnlbXSB7XG5cdFx0Y29uc3QgZW50cmllczogQ29sbGVjdGlvbk1hbmlmZXN0RW50cnlbXSA9IFtdO1xuXHRcdGNvbnN0IGhhc0RlZmF1bHRUeXBlcyA9IHRoaXMuZ3JhcGguZ2V0QWxsVHlwZXMoKS5zb21lKHQgPT4gdC5jb2xsZWN0aW9uSWQgPT09IHVuZGVmaW5lZCk7XG5cdFx0aWYgKGhhc0RlZmF1bHRUeXBlcykge1xuXHRcdFx0ZW50cmllcy5wdXNoKHtcblx0XHRcdFx0aWQgICAgICAgOiBudWxsLFxuXHRcdFx0XHRuYW1lICAgICA6ICdkZWZhdWx0VHlwZXMnLFxuXHRcdFx0XHRsb2NhdGlvbiA6IG51bGwsXG5cdFx0XHRcdGxhbmd1YWdlIDogJ3R5cGVzY3JpcHQnXG5cdFx0XHR9KTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBbIGlkLCBpbmZvIF0gb2YgdGhpcy5jb2xsZWN0aW9uSW5mbykge1xuXHRcdFx0Y29uc3QgZW50cnk6IENvbGxlY3Rpb25NYW5pZmVzdEVudHJ5ID0ge1xuXHRcdFx0XHRpZCxcblx0XHRcdFx0bmFtZSAgICAgOiBpbmZvLnZhcmlhYmxlTmFtZSxcblx0XHRcdFx0bG9jYXRpb24gOiBgJHtpbmZvLnNvdXJjZUZpbGV9OiR7aW5mby5saW5lfToke2luZm8uY29sdW1ufWAsXG5cdFx0XHRcdGxhbmd1YWdlIDogJ3R5cGVzY3JpcHQnXG5cdFx0XHR9O1xuXHRcdFx0ZW50cmllcy5wdXNoKGVudHJ5KTtcblx0XHR9XG5cdFx0cmV0dXJuIGVudHJpZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCB1c2FnZXNcblx0ICovXG5cdGdldFVzYWdlcyAoKTogTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+IHtcblx0XHRyZXR1cm4gdGhpcy51c2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBFRFMgdXNhZ2VzXG5cdCAqL1xuXHRnZXRFRFNVc2FnZXMgKCk6IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4ge1xuXHRcdHJldHVybiB0aGlzLmVkc1VzYWdlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGZsb3cgdXNhZ2VzXG5cdCAqL1xuXHRnZXRGbG93VXNhZ2VzICgpOiBNYXA8c3RyaW5nLCBGbG93SW5mb1tdPiB7XG5cdFx0cmV0dXJuIHRoaXMuZmxvd1VzYWdlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGluc3RydW1lbnRhdGlvbiBwb2ludHMuXG5cdCAqIFJlZ2lzdHJhdGlvbiBzaXRlcyByZWZlcmVuY2luZyBhIGNsYXNzIGRlY2xhcmVkIGluIHRoZSBzYW1lIHByb2plY3Rcblx0ICogcmVzb2x2ZSB0byB0aGUgY2xhc3MgZGVjbGFyYXRpb24ncyBsb2NhdGlvbi9jb2RlOyBleHRlcm5hbCBjbGFzc2VzXG5cdCAqIChlLmcuLCBhIGZyYW1ld29yay1idWlsdGluIGltcGxlbWVudGF0aW9uIGZyb20gbm9kZV9tb2R1bGVzKSBrZWVwXG5cdCAqIHRoZSByZWdpc3RyYXRpb24gc2l0ZS5cblx0ICogRGVkdXBlZCBieSBraW5kK2NsYXNzTmFtZStsb2NhdGlvbitzY29wZSB3aXRoIHRhcmdldHMgbWVyZ2VkIOKAlCBhXG5cdCAqIGNsYXNzIGRldGVjdGVkIGJ5IGhlcml0YWdlIEFORCBieSBhIGRlY29yYXRvciBzaXRlIHlpZWxkcyBzZXBhcmF0ZVxuXHQgKiBlbnRyaWVzIHdpdGggZGlzdGluY3Qgc2NvcGVzIChzZWUgSW5zdHJ1bWVudGF0aW9uUG9pbnQgaW4gdHlwZXMudHMpLlxuXHQgKi9cblx0Z2V0SW5zdHJ1bWVudGF0aW9uUG9pbnRzICgpOiBJbnN0cnVtZW50YXRpb25Qb2ludFtdIHtcblx0XHRjb25zdCBwb2ludHMgPSBuZXcgTWFwPHN0cmluZywgSW5zdHJ1bWVudGF0aW9uUG9pbnQ+KCk7XG5cblx0XHRjb25zdCBhZGRQb2ludCA9IChwb2ludDogSW5zdHJ1bWVudGF0aW9uUG9pbnQpOiB2b2lkID0+IHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3BvaW50LmtpbmR9fCR7cG9pbnQuY2xhc3NOYW1lfXwke3BvaW50LmxvY2F0aW9ufXwke3BvaW50LnNjb3BlfWA7XG5cdFx0XHRjb25zdCBleGlzdGluZyA9IHBvaW50cy5nZXQoa2V5KTtcblx0XHRcdGlmIChleGlzdGluZykge1xuXHRcdFx0XHRjb25zdCBtZXJnZWQgPSBuZXcgU2V0KFsgLi4uZXhpc3RpbmcudGFyZ2V0cywgLi4ucG9pbnQudGFyZ2V0cyBdKTtcblx0XHRcdFx0ZXhpc3RpbmcudGFyZ2V0cyA9IEFycmF5LmZyb20obWVyZ2VkKTtcblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0cG9pbnRzLnNldChrZXksIHBvaW50KTtcblx0XHR9O1xuXG5cdFx0Zm9yIChjb25zdCBzaXRlIG9mIHRoaXMuaW5zdHJ1bWVudGF0aW9uU2l0ZXMpIHtcblx0XHRcdGNvbnN0IGRlY2wgPSB0aGlzLmluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMuZ2V0KHNpdGUuY2xhc3NOYW1lKTtcblx0XHRcdGNvbnN0IHBvaW50OiBJbnN0cnVtZW50YXRpb25Qb2ludCA9IHtcblx0XHRcdFx0a2luZCAgICAgIDogc2l0ZS5raW5kLFxuXHRcdFx0XHRjbGFzc05hbWUgOiBzaXRlLmNsYXNzTmFtZSxcblx0XHRcdFx0bG9jYXRpb24gIDogZGVjbCA/IGRlY2wubG9jYXRpb24gOiBzaXRlLmxvY2F0aW9uLFxuXHRcdFx0XHRjb2RlICAgICAgOiBkZWNsID8gZGVjbC5jb2RlIDogc2l0ZS5jb2RlLFxuXHRcdFx0XHRzY29wZSAgICAgOiBzaXRlLnNjb3BlLFxuXHRcdFx0XHR0YXJnZXRzICAgOiBzaXRlLnRhcmdldHMsXG5cdFx0XHR9O1xuXHRcdFx0YWRkUG9pbnQocG9pbnQpO1xuXHRcdH1cblxuXHRcdC8vIEhlcml0YWdlLWRlY2xhcmVkIGNsYXNzZXMgYWx3YXlzIGVtaXQgYSBkZWNsYXJhdGlvbiBwb2ludCB3aXRoXG5cdFx0Ly8gc2NvcGUgJ21vZHVsZScgKGF0dGFjaG1lbnQgc3RhdGljYWxseSB1bmtub3duKTsgcmVnaXN0cmF0aW9uXG5cdFx0Ly8gc2l0ZXMgYWJvdmUgY2FycnkgdGhlIG5hcnJvd2VyIHNjb3BlcyBhcyBzZXBhcmF0ZSBlbnRyaWVzXG5cdFx0Zm9yIChjb25zdCBbIGNsYXNzTmFtZSwgZGVjbCBdIG9mIHRoaXMuaW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNscykge1xuXHRcdFx0aWYgKCFkZWNsLmtpbmQpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBwb2ludDogSW5zdHJ1bWVudGF0aW9uUG9pbnQgPSB7XG5cdFx0XHRcdGtpbmQgICAgICA6IGRlY2wua2luZCxcblx0XHRcdFx0Y2xhc3NOYW1lIDogY2xhc3NOYW1lLFxuXHRcdFx0XHRsb2NhdGlvbiAgOiBkZWNsLmxvY2F0aW9uLFxuXHRcdFx0XHRjb2RlICAgICAgOiBkZWNsLmNvZGUsXG5cdFx0XHRcdHNjb3BlICAgICA6ICdtb2R1bGUnLFxuXHRcdFx0XHR0YXJnZXRzICAgOiBbXSxcblx0XHRcdH07XG5cdFx0XHRhZGRQb2ludChwb2ludCk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVzdWx0ID0gQXJyYXkuZnJvbShwb2ludHMudmFsdWVzKCkpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogQWRkIGEgdG9wb2xvZ2ljYSB0eXBlIHRvIHRoZSBhbmFseXplciBmb3IgdXNhZ2UgdHJhY2tpbmcuXG5cdCAqIFRoaXMgYWxsb3dzIHRoZSBhbmFseXplciB0byByZWNvZ25pemUgdG9wb2xvZ2ljYSB0eXBlcyB3aGVuIGNvbGxlY3RpbmcgdXNhZ2VzLlxuXHQgKi9cblx0YWRkVG9wb2xvZ2ljYVR5cGUgKGZ1bGxQYXRoOiBzdHJpbmcsIG5vZGU6IGltcG9ydCgnLi90eXBlcycpLlR5cGVOb2RlKTogdm9pZCB7XG5cdFx0Ly8gU2tpcCBpZiBhbHJlYWR5IGV4aXN0c1xuXHRcdGlmICh0aGlzLmdyYXBoLmFsbFR5cGVzLmhhcyhmdWxsUGF0aCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGggc28gaXQgY2FuIGJlIGZvdW5kIGR1cmluZyB1c2FnZSBjb2xsZWN0aW9uXG5cdFx0aWYgKG5vZGUucGFyZW50KSB7XG5cdFx0XHQvLyBBZGQgYXMgY2hpbGQgb2YgcGFyZW50XG5cdFx0XHR0aGlzLmdyYXBoLmFkZENoaWxkKG5vZGUucGFyZW50LCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0Ly8gQWRkIGFzIHJvb3Rcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cblx0XHQvLyBBbHNvIGFkZCB0byBkZWZpbml0aW9ucyBzbyBpdCdzIHJlY29nbml6ZWQgYXMgYSBrbm93biB0eXBlXG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IG5vZGUubmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7bm9kZS5zb3VyY2VGaWxlfToke25vZGUubGluZX06JHtub2RlLmNvbHVtbn1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogbm9kZS5wYXJlbnQgPyBub2RlLnBhcmVudC5mdWxsUGF0aCA6IG51bGwsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IHRydWUsXG5cdFx0XHRibG9ja0Vycm9ycyA6IGZhbHNlXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChmdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdH1cblxuXHQvKipcblx0ICogU2V0IHBhcmVudCBub2RlcyBpbiBhIHNvdXJjZSBmaWxlIHRvIGVuYWJsZSBBU1QgdHJhdmVyc2FsIHVwXG5cdCAqL1xuXHRwcml2YXRlIHNldFBhcmVudE5vZGVzSW5Tb3VyY2VGaWxlIChzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3Qgc2V0UGFyZW50ID0gKG5vZGU6IHRzLk5vZGUsIHBhcmVudD86IHRzLk5vZGUpID0+IHtcblx0XHRcdC8vIFR5cGVTY3JpcHQgZG9lc24ndCBleHBvc2UgcGFyZW50IGFzIHdyaXRhYmxlLCBidXQgd2UgbmVlZCBpdFxuXHRcdFx0Ly8gZXNsaW50LWRpc2FibGUtbmV4dC1saW5lIEB0eXBlc2NyaXB0LWVzbGludC9uby1leHBsaWNpdC1hbnlcblx0XHRcdChub2RlIGFzIGFueSkucGFyZW50ID0gcGFyZW50O1xuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHNldFBhcmVudChjaGlsZCwgbm9kZSkpO1xuXHRcdH07XG5cdFx0c2V0UGFyZW50KHNvdXJjZUZpbGUpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFZpc2l0IGEgbm9kZSBpbiB0aGUgQVNUXG5cdCAqL1xuXHRwcml2YXRlIHZpc2l0Tm9kZSAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSwgY3VycmVudENsYXNzPzogdHMuQ2xhc3NEZWNsYXJhdGlvbik6IHZvaWQge1xuXHRcdC8vIFRyYWNrIG1uZW1vbmljYSBtb2R1bGUtb2JqZWN0IGFsaWFzZXMgYW5kIGN1c3RvbSBjb2xsZWN0aW9uIHZhcmlhYmxlc1xuXHRcdC8vIGJlZm9yZSBwcm9jZXNzaW5nIGRlZmluZSgpL2xvb2t1cCgpIGNhbGxzIHNvIHNvdXJjZSByZXNvbHV0aW9uIHdvcmtzLlxuXHRcdHRoaXMudHJhY2tJbXBvcnRzKG5vZGUpO1xuXHRcdHRoaXMudHJhY2tNb2R1bGVPYmplY3RBbGlhc2VzKG5vZGUpO1xuXHRcdHRoaXMudHJhY2tDb2xsZWN0aW9uQWxpYXNlcyhub2RlLCBzb3VyY2VGaWxlKTtcblx0XHR0aGlzLnRyYWNrQnVpbGRlckV4cG9ydEFzc2lnbm1lbnQobm9kZSk7XG5cdFx0dGhpcy50cmFja0NvbnN0cnVjdG9yQmluZGluZyhub2RlKTtcblxuXHRcdC8vIENoZWNrIGZvciBkZWZpbmUoKSBjYWxsc1xuXHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChub2RlKSkge1xuXHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ2FsbChub2RlIGFzIHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgbGF6eSgpIGNhbGxzXG5cdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChub2RlKSkge1xuXHRcdFx0dGhpcy5wcm9jZXNzTGF6eUNhbGwobm9kZSBhcyB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIGRlY29yYXRlKCkgZGVjb3JhdG9yXG5cdFx0aWYgKHRoaXMuaXNEZWNvcmF0ZURlY29yYXRvcihub2RlKSkge1xuXHRcdFx0dGhpcy5wcm9jZXNzRGVjb3JhdGVEZWNvcmF0b3Iobm9kZSBhcyB0cy5EZWNvcmF0b3IsIHNvdXJjZUZpbGUsIGN1cnJlbnRDbGFzcyk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIHR5cGUgdXNhZ2VzIChuZXcgVHlwZSgpLCB0eXBlIGFubm90YXRpb25zLCBldGMuKVxuXHRcdHRoaXMuY29sbGVjdFVzYWdlKG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIEVEUyBwYXR0ZXJucyAod3JhcCwgY3VycmVudCwgZ2V0RmxvdywgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RFRFMobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgbmF0aXZlIGZsb3cgcGF0dGVybnMgKHByb3BlcnR5IGFjY2VzcywgbWV0aG9kIGNhbGxzLCBldGMuKVxuXHRcdHRoaXMuY29sbGVjdEZsb3cobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgZnJhbWV3b3JrIGluc3RydW1lbnRhdGlvbiBwb2ludHMgKHZvY2FidWxhcnkgc3VwcGxpZWRcblx0XHQvLyBieSBwbHVnaW5zOyBzeW50YWN0aWMgb25seSDigJQgbm8gdHlwZSBjaGVja2VyKVxuXHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbihub2RlLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIENvbGxlY3QgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9ucyAoYWxpYXNlcywgY2xhc3NlcywgaW50ZXJmYWNlcylcblx0XHQvLyBwZXIgZmlsZSwgYW5kIHRoZSBmaWxlJ3MgaW1wb3J0IHdpcmluZywgZm9yIGltcG9ydC1hd2FyZSByZXNvbHV0aW9uXG5cdFx0dGhpcy50cmFja1JlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24obm9kZSk7XG5cdFx0dGhpcy50cmFja1JlZmVyZW5jZWRUeXBlSW1wb3J0KG5vZGUpO1xuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZVJlRXhwb3J0KG5vZGUpO1xuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXkobm9kZSk7XG5cblx0XHQvLyBUcmFjayBzYW1lLWZpbGUgZnVuY3Rpb24gYmluZGluZ3Mgc28gRURTIGNhbiByZXNvbHZlIHdyYXAoZm4pXG5cdFx0Ly8gYXJndW1lbnRzIHdpdGhvdXQgdGhlIHR5cGUgY2hlY2tlciAoYmVzdCBlZmZvcnQsIGxhc3Qgd2lucylcblx0XHRpZiAodHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKG5vZGUpICYmIG5vZGUubmFtZSkge1xuXHRcdFx0Y29uc3Qga2V5ID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX0jJHtub2RlLm5hbWUudGV4dH1gO1xuXHRcdFx0dGhpcy5mdW5jdGlvbkJpbmRpbmdzLnNldChrZXksIG5vZGUpO1xuXHRcdH1cblx0XHRpZiAoXG5cdFx0XHR0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpICYmXG5cdFx0XHRub2RlLmluaXRpYWxpemVyICYmXG5cdFx0XHQodHMuaXNBcnJvd0Z1bmN0aW9uKG5vZGUuaW5pdGlhbGl6ZXIpIHx8IHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKG5vZGUuaW5pdGlhbGl6ZXIpKVxuXHRcdCkge1xuXHRcdFx0Y29uc3Qga2V5ID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX0jJHtub2RlLm5hbWUudGV4dH1gO1xuXHRcdFx0dGhpcy5mdW5jdGlvbkJpbmRpbmdzLnNldChrZXksIG5vZGUuaW5pdGlhbGl6ZXIpO1xuXHRcdH1cblxuXHRcdC8vIFRyYWNrIGNsYXNzIGRlY2xhcmF0aW9ucyBmb3IgZGVjb3JhdG9yIHBhcmVudCBsb29rdXBcblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHQvLyBWaXNpdCBjaGlsZHJlbiB3aXRoIHRoaXMgY2xhc3MgYXMgdGhlIGN1cnJlbnQgY29udGV4dFxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHRoaXMudmlzaXROb2RlKGNoaWxkLCBzb3VyY2VGaWxlLCBub2RlKSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdC8vIFJlY3Vyc2l2ZWx5IHZpc2l0IGNoaWxkcmVuXG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgY2hpbGQgPT4gdGhpcy52aXNpdE5vZGUoY2hpbGQsIHNvdXJjZUZpbGUsIGN1cnJlbnRDbGFzcykpO1xuXHRcdH1cblx0fVxuXG5cdHByaXZhdGUgdHJhY2tDb25zdHJ1Y3RvckJpbmRpbmcgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRsZXQgbmFtZTogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdGxldCBoYW5kbGVyOiBDb25zdHJ1Y3RvckhhbmRsZXIgfCB1bmRlZmluZWQ7XG5cdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSAmJiBub2RlLmluaXRpYWxpemVyKSB7XG5cdFx0XHRuYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0XHRoYW5kbGVyID0gbm9kZS5pbml0aWFsaXplcjtcblx0XHR9IGVsc2UgaWYgKCh0cy5pc0Z1bmN0aW9uRGVjbGFyYXRpb24obm9kZSkgfHwgdHMuaXNDbGFzc0RlY2xhcmF0aW9uKG5vZGUpKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdG5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRcdGhhbmRsZXIgPSBub2RlO1xuXHRcdH1cblx0XHRpZiAoIW5hbWUgfHwgIWhhbmRsZXIpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0bGV0IGJpbmRpbmdzID0gdGhpcy5jb25zdHJ1Y3RvckJpbmRpbmdzLmdldChmaWxlUGF0aCk7XG5cdFx0aWYgKCFiaW5kaW5ncykge1xuXHRcdFx0YmluZGluZ3MgPSBuZXcgTWFwPHN0cmluZywgQ29uc3RydWN0b3JIYW5kbGVyPigpO1xuXHRcdFx0dGhpcy5jb25zdHJ1Y3RvckJpbmRpbmdzLnNldChmaWxlUGF0aCwgYmluZGluZ3MpO1xuXHRcdH1cblx0XHRiaW5kaW5ncy5zZXQobmFtZSwgaGFuZGxlcik7XG5cdH1cblxuXHQvKipcblx0ICogRG9lcyBhbiBpbXBvcnQgc3BlY2lmaWVyIG5hbWUgdGhlIGdlbmVyYXRlZCBvdXRwdXQ/IEEgY29udmVudGlvbmFsXG5cdCAqIGAudGFjdGljYWAgcGF0aCBhbHdheXMgZG9lczsgb3RoZXJ3aXNlIHRoZSBzcGVjaWZpZXIgaXMgcmVzb2x2ZWQgd2l0aFxuXHQgKiB0aGUgcHJvZ3JhbSdzIGNvbXBpbGVyT3B0aW9ucyAodHNjb25maWcgYHBhdGhzYCBpbmNsdWRlZCkgYXMgaWYgdGhlXG5cdCAqIGdlbmVyYXRlZCBmaWxlcyBleGlzdGVkIOKAlCBvbiBhIGZyZXNoIGNsb25lIHRoZXkgYXJlIG5vdCB3cml0dGVuIHlldC5cblx0ICovXG5cdHByaXZhdGUgaXNHZW5lcmF0ZWRUeXBlU3BlY2lmaWVyIChzcGVjaWZpZXI6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRcdGlmIChzcGVjaWZpZXIuaW5jbHVkZXMoJy50YWN0aWNhJykpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHRjb25zdCBvdXRwdXREaXJzID0gdGhpcy5nZW5lcmF0ZWRPdXRwdXREaXJzO1xuXHRcdGlmIChvdXRwdXREaXJzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblx0XHRjb25zdCBjYWNoZUtleSA9IGAke3RoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZX06OiR7c3BlY2lmaWVyfWA7XG5cdFx0Y29uc3QgY2FjaGVkID0gdGhpcy5nZW5lcmF0ZWRTcGVjaWZpZXJDYWNoZS5nZXQoY2FjaGVLZXkpO1xuXHRcdGlmIChjYWNoZWQgIT09IHVuZGVmaW5lZCkge1xuXHRcdFx0cmV0dXJuIGNhY2hlZDtcblx0XHR9XG5cdFx0Y29uc3QgaW5zaWRlT3V0cHV0ID0gKGZpbGVPckRpcjogc3RyaW5nKTogYm9vbGVhbiA9PiB7XG5cdFx0XHRjb25zdCBhYnNvbHV0ZSA9IG5vZGVQYXRoLnJlc29sdmUoZmlsZU9yRGlyKTtcblx0XHRcdGNvbnN0IGluc2lkZSA9IG91dHB1dERpcnMuc29tZShkaXIgPT4gYWJzb2x1dGUgPT09IGRpciB8fCBhYnNvbHV0ZS5zdGFydHNXaXRoKGRpciArIG5vZGVQYXRoLnNlcCkpO1xuXHRcdFx0cmV0dXJuIGluc2lkZTtcblx0XHR9O1xuXHRcdGNvbnN0IGhvc3Q6IHRzLk1vZHVsZVJlc29sdXRpb25Ib3N0ID0ge1xuXHRcdFx0ZmlsZUV4aXN0cyAgICAgIDogZmlsZU5hbWUgPT4gaW5zaWRlT3V0cHV0KGZpbGVOYW1lKSB8fCB0cy5zeXMuZmlsZUV4aXN0cyhmaWxlTmFtZSksXG5cdFx0XHRyZWFkRmlsZSAgICAgICAgOiBmaWxlTmFtZSA9PiB0cy5zeXMucmVhZEZpbGUoZmlsZU5hbWUpLFxuXHRcdFx0ZGlyZWN0b3J5RXhpc3RzIDogZGlyZWN0b3J5TmFtZSA9PiBpbnNpZGVPdXRwdXQoZGlyZWN0b3J5TmFtZSkgfHwgdHMuc3lzLmRpcmVjdG9yeUV4aXN0cyhkaXJlY3RvcnlOYW1lKSxcblx0XHR9O1xuXHRcdGNvbnN0IHJlc29sdmVkID0gdHMucmVzb2x2ZU1vZHVsZU5hbWUoXG5cdFx0XHRzcGVjaWZpZXIsXG5cdFx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUsXG5cdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlQ29tcGlsZXJPcHRpb25zLFxuXHRcdFx0aG9zdFxuXHRcdCkucmVzb2x2ZWRNb2R1bGU7XG5cdFx0Y29uc3QgcmVzdWx0ID0gcmVzb2x2ZWQgIT09IHVuZGVmaW5lZCAmJiBpbnNpZGVPdXRwdXQocmVzb2x2ZWQucmVzb2x2ZWRGaWxlTmFtZSk7XG5cdFx0dGhpcy5nZW5lcmF0ZWRTcGVjaWZpZXJDYWNoZS5zZXQoY2FjaGVLZXksIHJlc3VsdCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBUcmFjayBpbXBvcnRzIGZyb20gJ21uZW1vbmljYScgc28gYWxpYXNlcyBvZiB0aGUgbW9kdWxlIG9iamVjdCBhbmRcblx0ICogY3JlYXRlVHlwZXNDb2xsZWN0aW9uIGFyZSByZWNvZ25pemVkIHdpdGhvdXQgcmVseWluZyBvbiB0aGUgdHlwZSBjaGVja2VyLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja0ltcG9ydHMgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzSW1wb3J0RGVjbGFyYXRpb24obm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IG1vZHVsZVNwZWNpZmllciB9ID0gbm9kZTtcblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKG1vZHVsZVNwZWNpZmllcikgJiYgdGhpcy5pc0dlbmVyYXRlZFR5cGVTcGVjaWZpZXIobW9kdWxlU3BlY2lmaWVyLnRleHQpKSB7XG5cdFx0XHRsZXQgaW1wb3J0cyA9IHRoaXMuZ2VuZXJhdGVkVHlwZUltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRpZiAoIWltcG9ydHMpIHtcblx0XHRcdFx0aW1wb3J0cyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdFx0XHR0aGlzLmdlbmVyYXRlZFR5cGVJbXBvcnRzLnNldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUsIGltcG9ydHMpO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZ2VuZXJhdGVkQ2xhdXNlID0gbm9kZS5pbXBvcnRDbGF1c2U7XG5cdFx0XHRpZiAoZ2VuZXJhdGVkQ2xhdXNlPy5uYW1lKSB7XG5cdFx0XHRcdGltcG9ydHMuYWRkKGdlbmVyYXRlZENsYXVzZS5uYW1lLnRleHQpO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGdlbmVyYXRlZENsYXVzZT8ubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVkSW1wb3J0cyhnZW5lcmF0ZWRDbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGdlbmVyYXRlZENsYXVzZS5uYW1lZEJpbmRpbmdzLmVsZW1lbnRzKSB7XG5cdFx0XHRcdFx0aW1wb3J0cy5hZGQoZWxlbWVudC5uYW1lLnRleHQpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAoZ2VuZXJhdGVkQ2xhdXNlPy5uYW1lZEJpbmRpbmdzICYmIHRzLmlzTmFtZXNwYWNlSW1wb3J0KGdlbmVyYXRlZENsYXVzZS5uYW1lZEJpbmRpbmdzKSkge1xuXHRcdFx0XHRpbXBvcnRzLmFkZChnZW5lcmF0ZWRDbGF1c2UubmFtZWRCaW5kaW5ncy5uYW1lLnRleHQpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAoIXRzLmlzU3RyaW5nTGl0ZXJhbChtb2R1bGVTcGVjaWZpZXIpIHx8IG1vZHVsZVNwZWNpZmllci50ZXh0ICE9PSAnbW5lbW9uaWNhJykge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IGNsYXVzZSA9IG5vZGUuaW1wb3J0Q2xhdXNlO1xuXHRcdGlmICghY2xhdXNlKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0IHsgbW5lbW9uaWNhLCBjcmVhdGVUeXBlc0NvbGxlY3Rpb24gfSBmcm9tICdtbmVtb25pY2EnXG5cdFx0aWYgKGNsYXVzZS5uYW1lZEJpbmRpbmdzICYmIHRzLmlzTmFtZWRJbXBvcnRzKGNsYXVzZS5uYW1lZEJpbmRpbmdzKSkge1xuXHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGNsYXVzZS5uYW1lZEJpbmRpbmdzLmVsZW1lbnRzKSB7XG5cdFx0XHRcdGNvbnN0IGxvY2FsTmFtZSA9IGVsZW1lbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBpbXBvcnRlZE5hbWUgPSBlbGVtZW50LnByb3BlcnR5TmFtZVxuXHRcdFx0XHRcdD8gZWxlbWVudC5wcm9wZXJ0eU5hbWUudGV4dFxuXHRcdFx0XHRcdDogbG9jYWxOYW1lO1xuXHRcdFx0XHRpZiAoaW1wb3J0ZWROYW1lID09PSAnbW5lbW9uaWNhJykge1xuXHRcdFx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChsb2NhbE5hbWUpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChpbXBvcnRlZE5hbWUgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nKSB7XG5cdFx0XHRcdFx0dGhpcy5jcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMuYWRkKGxvY2FsTmFtZSk7XG5cdFx0XHRcdH1cblx0XHRcdFx0bGV0IGZpbGVJbXBvcnRzID0gdGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRcdGlmICghZmlsZUltcG9ydHMpIHtcblx0XHRcdFx0XHRmaWxlSW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHRcdFx0dGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuc2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSwgZmlsZUltcG9ydHMpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGZpbGVJbXBvcnRzLnNldChsb2NhbE5hbWUsIGltcG9ydGVkTmFtZSk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0ICogYXMgbW5lbW9uaWNhIGZyb20gJ21uZW1vbmljYSdcblx0XHRpZiAoY2xhdXNlLm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lc3BhY2VJbXBvcnQoY2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQoY2xhdXNlLm5hbWVkQmluZGluZ3MubmFtZS50ZXh0KTtcblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgbW5lbW9uaWNhIGZyb20gJ21uZW1vbmljYScgKGRlZmF1bHQgaW1wb3J0KSDigJQgdHJlYXQgYXMgbW9kdWxlIG9iamVjdCB0b29cblx0XHRpZiAoY2xhdXNlLm5hbWUpIHtcblx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChjbGF1c2UubmFtZS50ZXh0KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGEgbmFtZWQgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9uICh0eXBlIGFsaWFzLCBjbGFzcywgb3Jcblx0ICogaW50ZXJmYWNlKSBmb3IgdGhlIGZpbGUgY3VycmVudGx5IGJlaW5nIHZpc2l0ZWQuXG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdC8vIE5hbWVzcGFjZXMgYXJlIHRoZSBtaWRkbGUgc2VnbWVudHMgb2YgcXVhbGlmaWVkIHJlZmVyZW5jZXNcblx0XHQvLyAobW9kZWxzLklubmVyLkNyYXRlKSDigJQgcmVjb3JkZWQgc2VwYXJhdGVseSBmcm9tIHRoZSBwbGFpbi1uYW1lXG5cdFx0Ly8gZGVjbGFyYXRpb24gdGFibGUgKHN0cmluZy1uYW1lZCBgbW9kdWxlICfigKYnYCBkZWNsYXJhdGlvbnMgYXJlXG5cdFx0Ly8gYW1iaWVudCBleHRlcm5hbHMgYW5kIHN0YXkgb3V0KVxuXHRcdGlmICh0cy5pc01vZHVsZURlY2xhcmF0aW9uKG5vZGUpICYmIHRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpICYmXG5cdFx0XHRub2RlLmJvZHkgJiYgdHMuaXNNb2R1bGVCbG9jayhub2RlLmJvZHkpKSB7XG5cdFx0XHRjb25zdCBuYW1lc3BhY2VGaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRcdGxldCBuYW1lc3BhY2VzID0gdGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMuZ2V0KG5hbWVzcGFjZUZpbGVQYXRoKTtcblx0XHRcdGlmICghbmFtZXNwYWNlcykge1xuXHRcdFx0XHRuYW1lc3BhY2VzID0gbmV3IE1hcDxzdHJpbmcsIHRzLk1vZHVsZURlY2xhcmF0aW9uPigpO1xuXHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlcy5zZXQobmFtZXNwYWNlRmlsZVBhdGgsIG5hbWVzcGFjZXMpO1xuXHRcdFx0fVxuXHRcdFx0bmFtZXNwYWNlcy5zZXQobm9kZS5uYW1lLnRleHQsIG5vZGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGxldCBuYW1lID0gJyc7XG5cdFx0bGV0IGtpbmQ6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25bJ2tpbmQnXSB8IHVuZGVmaW5lZDtcblx0XHRsZXQgZGVjbE5vZGU6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25bJ25vZGUnXSB8IHVuZGVmaW5lZDtcblxuXHRcdGlmICh0cy5pc1R5cGVBbGlhc0RlY2xhcmF0aW9uKG5vZGUpICYmIHRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpKSB7XG5cdFx0XHRuYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0XHRraW5kID0gJ2FsaWFzJztcblx0XHRcdGRlY2xOb2RlID0gbm9kZTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdG5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRcdGtpbmQgPSAnY2xhc3MnO1xuXHRcdFx0ZGVjbE5vZGUgPSBub2RlO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNJbnRlcmZhY2VEZWNsYXJhdGlvbihub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSkge1xuXHRcdFx0bmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0a2luZCA9ICdpbnRlcmZhY2UnO1xuXHRcdFx0ZGVjbE5vZGUgPSBub2RlO1xuXHRcdH1cblxuXHRcdGlmICgha2luZCB8fCAhZGVjbE5vZGUgfHwgIW5hbWUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRsZXQgZGVjbHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRGVjbHMuZ2V0KGZpbGVQYXRoKTtcblx0XHRpZiAoIWRlY2xzKSB7XG5cdFx0XHRkZWNscyA9IG5ldyBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uPigpO1xuXHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLnNldChmaWxlUGF0aCwgZGVjbHMpO1xuXHRcdH1cblx0XHRjb25zdCBlbnRyeTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiA9IHsga2luZCwgbm9kZSA6IGRlY2xOb2RlLCBmaWxlIDogZmlsZVBhdGggfTtcblx0XHRkZWNscy5zZXQobmFtZSwgZW50cnkpO1xuXG5cdFx0Ly8gYGV4cG9ydCBkZWZhdWx0IGNsYXNzIEZvbyB7fWAgaXMgYWxzbyByZWFjaGFibGUgdW5kZXIgdGhlICdkZWZhdWx0J1xuXHRcdC8vIGJpbmRpbmcgZm9yIGRlZmF1bHQgaW1wb3J0ZXJzXG5cdFx0aWYgKGtpbmQgPT09ICdjbGFzcycpIHtcblx0XHRcdGNvbnN0IGNsYXNzTm9kZSA9IGRlY2xOb2RlIGFzIHRzLkNsYXNzRGVjbGFyYXRpb247XG5cdFx0XHRjb25zdCBpc0V4cG9ydGVkID0gY2xhc3NOb2RlLm1vZGlmaWVycz8uc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FeHBvcnRLZXl3b3JkKSA/PyBmYWxzZTtcblx0XHRcdGNvbnN0IGlzRGVmYXVsdCA9IGNsYXNzTm9kZS5tb2RpZmllcnM/LnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRGVmYXVsdEtleXdvcmQpID8/IGZhbHNlO1xuXHRcdFx0aWYgKGlzRXhwb3J0ZWQgJiYgaXNEZWZhdWx0KSB7XG5cdFx0XHRcdGRlY2xzLnNldCgnZGVmYXVsdCcsIGVudHJ5KTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGNvbnN0cyBpbml0aWFsaXplZCB3aXRoIGFuIGFycmF5IGxpdGVyYWwgKG9wdGlvbmFsbHkgd3JhcHBlZCBpblxuXHQgKiBgYXMgY29uc3RgIC8gYHNhdGlzZmllc2ApLCBzbyBhIGB0eXBlb2Ygc3RhdHVzTGlzdFtudW1iZXJdYCBmaWVsZCB0eXBlXG5cdCAqIGV4cGFuZHMgdG8gdGhlIGVsZW1lbnQgbGl0ZXJhbCB1bmlvbiDigJQgdGhlIGdlbmVyYXRlZCBmaWxlIGNhcnJpZXMgbm9cblx0ICogaW1wb3J0cywgc28gZW1pdHRpbmcgdGhlIGJhcmUgYHR5cGVvZiBzdGF0dXNMaXN0YCBxdWVyeSB3b3VsZCBiZSBhblxuXHQgKiB1bnJlc29sdmFibGUgbmFtZSBkb3duc3RyZWFtLiBGaXJzdCBiaW5kaW5nIHdpbnM6IGEgbmVzdGVkIHNoYWRvd1xuXHQgKiBtdXN0IG5vdCByZXBsYWNlIHRoZSBtb2R1bGUtbGV2ZWwgY29uc3QgdGhlIHR5cGVvZiByZWZlcnMgdG8uXG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrUmVmZXJlbmNlZFR5cGVDb25zdEFycmF5IChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgfHwgIXRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpIHx8ICFub2RlLmluaXRpYWxpemVyKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHsgaW5pdGlhbGl6ZXI6IHJhd0luaXRpYWxpemVyIH0gPSBub2RlO1xuXHRcdGxldCBpbml0aWFsaXplcjogdHMuRXhwcmVzc2lvbiA9IHJhd0luaXRpYWxpemVyO1xuXHRcdHdoaWxlIChcblx0XHRcdHRzLmlzQXNFeHByZXNzaW9uKGluaXRpYWxpemVyKSB8fFxuXHRcdFx0dHMuaXNTYXRpc2ZpZXNFeHByZXNzaW9uKGluaXRpYWxpemVyKSB8fFxuXHRcdFx0Ly8gdGhlIGFuZ2xlLWJyYWNrZXQgYXNzZXJ0aW9uIHNwZWxsaW5nIChgPGNvbnN0PlvigKZdYCkgaXMgdGhlXG5cdFx0XHQvLyBzYW1lIGNvbnN0LWFycmF5IG1hcmtlciBhcyB0aGUgYGFzIGNvbnN0YCBmb3JtIChGMTcpXG5cdFx0XHR0cy5pc1R5cGVBc3NlcnRpb25FeHByZXNzaW9uKGluaXRpYWxpemVyKVxuXHRcdCkge1xuXHRcdFx0aW5pdGlhbGl6ZXIgPSBpbml0aWFsaXplci5leHByZXNzaW9uO1xuXHRcdH1cblx0XHRpZiAoIXRzLmlzQXJyYXlMaXRlcmFsRXhwcmVzc2lvbihpbml0aWFsaXplcikpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0bGV0IGNvbnN0cyA9IHRoaXMucmVmZXJlbmNlZFR5cGVDb25zdEFycmF5cy5nZXQoZmlsZVBhdGgpO1xuXHRcdGlmICghY29uc3RzKSB7XG5cdFx0XHRjb25zdHMgPSBuZXcgTWFwPHN0cmluZywgdHMuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbj4oKTtcblx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVDb25zdEFycmF5cy5zZXQoZmlsZVBhdGgsIGNvbnN0cyk7XG5cdFx0fVxuXHRcdGlmICghY29uc3RzLmhhcyhub2RlLm5hbWUudGV4dCkpIHtcblx0XHRcdGNvbnN0cy5zZXQobm9kZS5uYW1lLnRleHQsIGluaXRpYWxpemVyKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRmluZCB0aGUgYXJyYXkgbGl0ZXJhbCBiZWhpbmQgYSBtb2R1bGUgY29uc3QgcmVmZXJlbmNlZCB0aHJvdWdoXG5cdCAqIGB0eXBlb2ZgOiB0aGUgZGVjbGFyaW5nIGZpbGUncyBvd24gY29uc3RzIGZpcnN0ICh0aGUgRjEzIGNhc2UgaXMgYVxuXHQgKiBOT04tZXhwb3J0ZWQgY29uc3QgaW4gdGhlIHNhbWUgbW9kdWxlIGFzIHRoZSBleHBhbmRlZCBjbGFzcyksIHRoZW4g4oCUXG5cdCAqIHdoZW4gdGhlIGZpbGUgaW1wb3J0cyB0aGUgbmFtZSDigJQgdGhlIGltcG9ydGVkIG1vZHVsZSdzIGNvbnN0cy5cblx0ICogRXh0ZXJuYWwgbW9kdWxlcyBhcmUgbmV2ZXIgYW5hbHl6ZWQsIHNvIHRob3NlIHlpZWxkIG5vdGhpbmcuXG5cdCAqL1xuXHRwcml2YXRlIGZpbmRSZWZlcmVuY2VkQ29uc3RBcnJheSAoXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdGZyb21GaWxlOiBzdHJpbmdcblx0KTogdHMuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgbG9jYWwgPSB0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuZ2V0KGZyb21GaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChsb2NhbCkge1xuXHRcdFx0cmV0dXJuIGxvY2FsO1xuXHRcdH1cblx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldChmcm9tRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAoIWltcG9ydGVkIHx8IGltcG9ydGVkLmlzTmFtZXNwYWNlKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoaW1wb3J0ZWQuc3BlY2lmaWVyLCBmcm9tRmlsZSk7XG5cdFx0aWYgKCFyZXNvbHV0aW9uIHx8IHJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgZm91bmQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuZ2V0KHJlc29sdXRpb24ucmVzb2x2ZWRQYXRoKT8uZ2V0KGltcG9ydGVkLm9yaWdpbmFsTmFtZSk7XG5cdFx0cmV0dXJuIGZvdW5kO1xuXHR9XG5cblx0LyoqXG5cdCAqIEVsZW1lbnQgbGl0ZXJhbCB0eXBlcyBvZiBhIHRyYWNrZWQgY29uc3QgYXJyYXk6IGV2ZXJ5IGVsZW1lbnQgbXVzdCBiZVxuXHQgKiBhIHBsYWluIGxpdGVyYWwgKG9wdGlvbmFsbHkgd3JhcHBlZCBpbiBgYXMgY29uc3RgIC8gYHNhdGlzZmllc2AgL1xuXHQgKiBgPGNvbnN0PmAgYXNzZXJ0aW9ucykg4oCUIHN0cmluZywgbnVtZXJpYyAodW5hcnkgYC1gL2ArYCBwcmVzZXJ2ZWQpLFxuXHQgKiBib29sZWFuLCBvciBudWxsLiBTcHJlYWRzLCBpZGVudGlmaWVycywgYW5kIG5lc3RlZCBhcnJheXMgbWVhbiB0aGVcblx0ICogdW5pb24gaXMgbm90IHN0YXRpY2FsbHkgdmlzaWJsZSBhbmQgeWllbGQgdW5kZWZpbmVkLCBzbyB0aGUgY2FsbGVyXG5cdCAqIGRlZ3JhZGVzIHRoZSBmaWVsZCB0byBgdW5rbm93bmAgcmF0aGVyIHRoYW4gZ3Vlc3NpbmcuXG5cdCAqL1xuXHRwcml2YXRlIGxpdGVyYWxUeXBlc09mQXJyYXkgKGFycmF5TGl0ZXJhbDogdHMuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbik6IHN0cmluZ1tdIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBsaXRlcmFsczogc3RyaW5nW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2YgYXJyYXlMaXRlcmFsLmVsZW1lbnRzKSB7XG5cdFx0XHRpZiAodHMuaXNTcHJlYWRFbGVtZW50KGVsZW1lbnQpKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBsaXRlcmFsID0gdGhpcy5saXRlcmFsVHlwZU9mRXhwcmVzc2lvbihlbGVtZW50KTtcblx0XHRcdGlmIChsaXRlcmFsID09PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGxpdGVyYWxzLnB1c2gobGl0ZXJhbCk7XG5cdFx0fVxuXHRcdGlmIChsaXRlcmFscy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGxpdGVyYWxzO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogVGhlIGxpdGVyYWwgdHlwZSBvZiBvbmUgYXJyYXkgZWxlbWVudDogYSBwbGFpbiBsaXRlcmFsIChvcHRpb25hbGx5XG5cdCAqIHdyYXBwZWQgaW4gYGFzIGNvbnN0YCAvIGBzYXRpc2ZpZXNgIC8gYXNzZXJ0aW9uIGV4cHJlc3Npb25zKSDigJRcblx0ICogc3RyaW5nLCBudW1lcmljICh1bmFyeSBgLWAvYCtgIHByZXNlcnZlZCksIGJvb2xlYW4sIG9yIG51bGwuXG5cdCAqIEFueXRoaW5nIGVsc2UgeWllbGRzIHVuZGVmaW5lZC5cblx0ICovXG5cdHByaXZhdGUgbGl0ZXJhbFR5cGVPZkV4cHJlc3Npb24gKGV4cHI6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBpbm5lcjogdHMuRXhwcmVzc2lvbiA9IGV4cHI7XG5cdFx0d2hpbGUgKHRzLmlzQXNFeHByZXNzaW9uKGlubmVyKSB8fCB0cy5pc1NhdGlzZmllc0V4cHJlc3Npb24oaW5uZXIpIHx8IHRzLmlzVHlwZUFzc2VydGlvbkV4cHJlc3Npb24oaW5uZXIpKSB7XG5cdFx0XHRpbm5lciA9IGlubmVyLmV4cHJlc3Npb247XG5cdFx0fVxuXHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoaW5uZXIpIHx8IHRzLmlzTm9TdWJzdGl0dXRpb25UZW1wbGF0ZUxpdGVyYWwoaW5uZXIpKSB7XG5cdFx0XHRjb25zdCBsaXRlcmFsID0gYCcke2lubmVyLnRleHR9J2A7XG5cdFx0XHRyZXR1cm4gbGl0ZXJhbDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJlZml4VW5hcnlFeHByZXNzaW9uKGlubmVyKSAmJiB0cy5pc051bWVyaWNMaXRlcmFsKGlubmVyLm9wZXJhbmQpKSB7XG5cdFx0XHRpZiAoaW5uZXIub3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuTWludXNUb2tlbikge1xuXHRcdFx0XHRjb25zdCBuZWdhdGl2ZSA9IGAtJHtpbm5lci5vcGVyYW5kLnRleHR9YDtcblx0XHRcdFx0cmV0dXJuIG5lZ2F0aXZlO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGlubmVyLm9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLlBsdXNUb2tlbikge1xuXHRcdFx0XHRyZXR1cm4gaW5uZXIub3BlcmFuZC50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzTnVtZXJpY0xpdGVyYWwoaW5uZXIpKSB7XG5cdFx0XHRyZXR1cm4gaW5uZXIudGV4dDtcblx0XHR9XG5cdFx0aWYgKGlubmVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVHJ1ZUtleXdvcmQpIHtcblx0XHRcdHJldHVybiAndHJ1ZSc7XG5cdFx0fVxuXHRcdGlmIChpbm5lci5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0cmV0dXJuICdmYWxzZSc7XG5cdFx0fVxuXHRcdGlmIChpbm5lci5raW5kID09PSB0cy5TeW50YXhLaW5kLk51bGxLZXl3b3JkKSB7XG5cdFx0XHRyZXR1cm4gJ251bGwnO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEYyMjogdGhlIGNvbnN0LWFzc2VydGlvbiBjaGVjayBzaGFyZWQgYnkgdGhlIHZhbHVlLWxldmVsIGFuZFxuXHQgKiBkZWNsYXJhdGlvbi1sZXZlbCBwYXRocyDigJQgYGV4cHIgYXMgY29uc3RgIGFuZCBgPGNvbnN0PmV4cHJgIHBhcnNlXG5cdCAqIGlkZW50aWNhbGx5IChhIFR5cGVSZWZlcmVuY2VOb2RlIG5hbWVkICdjb25zdCcpLiBHZW5lcmFsIGA8VD5leHByYFxuXHQgKiBhc3NlcnRpb25zIG5ldmVyIG1hdGNoLlxuXHQgKi9cblx0cHJpdmF0ZSBpc0NvbnN0QXNzZXJ0aW9uVHlwZSAodHlwZTogdHMuVHlwZU5vZGUpOiBib29sZWFuIHtcblx0XHRjb25zdCBjb25zdEFzc2VydGlvbiA9IHRzLmlzVHlwZVJlZmVyZW5jZU5vZGUodHlwZSkgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcih0eXBlLnR5cGVOYW1lKSAmJlxuXHRcdFx0dHlwZS50eXBlTmFtZS50ZXh0ID09PSAnY29uc3QnO1xuXHRcdHJldHVybiBjb25zdEFzc2VydGlvbjtcblx0fVxuXG5cdC8qKlxuXHQgKiBUaGUgYXJyYXkgbGl0ZXJhbCBiZWhpbmQgYSB2YWx1ZS1sZXZlbCBlbGVtZW50IGFjY2VzczogaW5saW5lXG5cdCAqIChgKDxjb25zdD5b4oCmXSlbMF1gLCBgKFvigKZdIGFzIGNvbnN0KVsxXWApLCBwYXJlbnRoZXNpemVkLCBvciBhXG5cdCAqIHRyYWNrZWQgbW9kdWxlIGNvbnN0IGFycmF5IChgY29uc3QgeCA9IDxjb25zdD5b4oCmXWAgLyBgeFswXWAsIEYxN1xuXHQgKiB0cmFja2luZykuIE9ubHkgY29uc3QgYXNzZXJ0aW9ucyBhcmUgdW53cmFwcGVkIOKAlCBnZW5lcmFsXG5cdCAqIGFzc2VydGlvbnMgc3RheSB1bmtub3duIChGMjIgc2NvcGUgYm91bmRhcnkpLlxuXHQgKi9cblx0cHJpdmF0ZSBjb25zdEFycmF5TGl0ZXJhbE9mIChleHByOiB0cy5FeHByZXNzaW9uKTogdHMuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLkV4cHJlc3Npb24gPSBleHByO1xuXHRcdHdoaWxlICh0cy5pc1BhcmVudGhlc2l6ZWRFeHByZXNzaW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5leHByZXNzaW9uO1xuXHRcdH1cblx0XHRpZiAodHMuaXNBcnJheUxpdGVyYWxFeHByZXNzaW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRyZXR1cm4gY3VycmVudDtcblx0XHR9XG5cdFx0aWYgKCh0cy5pc0FzRXhwcmVzc2lvbihjdXJyZW50KSB8fCB0cy5pc1R5cGVBc3NlcnRpb25FeHByZXNzaW9uKGN1cnJlbnQpKSAmJlxuXHRcdFx0dGhpcy5pc0NvbnN0QXNzZXJ0aW9uVHlwZShjdXJyZW50LnR5cGUpKSB7XG5cdFx0XHRjb25zdCBpbm5lciA9IGN1cnJlbnQuZXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IGxpdGVyYWwgPSB0cy5pc0FycmF5TGl0ZXJhbEV4cHJlc3Npb24oaW5uZXIpID8gaW5uZXIgOiB1bmRlZmluZWQ7XG5cdFx0XHRyZXR1cm4gbGl0ZXJhbDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50KSkge1xuXHRcdFx0Y29uc3QgdHJhY2tlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVDb25zdEFycmF5cy5nZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKT8uZ2V0KGN1cnJlbnQudGV4dCk7XG5cdFx0XHRyZXR1cm4gdHJhY2tlZDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFbWl0LXR5cGUgZm9yIGB0eXBlb2YgbmFtZWAgd2hlbiBgbmFtZWAgaXMgYSB0cmFja2VkIGNvbnN0IGFycmF5OiB0aGVcblx0ICogdW5pb24gb2YgaXRzIGVsZW1lbnQgbGl0ZXJhbCB0eXBlcyAoYCdhY3RpdmUnIHwgJ2Nsb3NlZCdgKS4gRXZlcnlcblx0ICogb3RoZXIgdHlwZW9mIHNvdXJjZSDigJQgbm9uLWFycmF5IGNvbnN0cywgZnVuY3Rpb25zLCBjbGFzc2VzLCBuYW1lcyBub3Rcblx0ICogdHJhY2tlZCBhdCBhbGwg4oCUIHlpZWxkcyB1bmRlZmluZWQsIHNvIHRoZSBjYWxsZXIgZGVncmFkZXMgdGhlIGZpZWxkXG5cdCAqIHRvIGB1bmtub3duYDogYSBiYXJlIGB0eXBlb2YgbmFtZWAgZW1pdHRlZCBpbnRvIHR5cGVzLnRzIGhhcyBub1xuXHQgKiBpbXBvcnQgdG8gcmVzb2x2ZSBhZ2FpbnN0IGRvd25zdHJlYW0uXG5cdCAqL1xuXHRwcml2YXRlIHR5cGVPZkNvbnN0QXJyYXlVbmlvbiAobmFtZTogc3RyaW5nLCBmcm9tRmlsZTogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBhcnJheUxpdGVyYWwgPSB0aGlzLmZpbmRSZWZlcmVuY2VkQ29uc3RBcnJheShuYW1lLCBmcm9tRmlsZSk7XG5cdFx0aWYgKCFhcnJheUxpdGVyYWwpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGxpdGVyYWxzID0gdGhpcy5saXRlcmFsVHlwZXNPZkFycmF5KGFycmF5TGl0ZXJhbCk7XG5cdFx0aWYgKCFsaXRlcmFscykge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgdW5pb24gPSBsaXRlcmFscy5qb2luKCcgfCAnKTtcblx0XHRyZXR1cm4gdW5pb247XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIHRoZSBpbXBvcnRpbmcgZmlsZSdzIG5hbWVkL25hbWVzcGFjZS9kZWZhdWx0IGltcG9ydCBiaW5kaW5ncyBzb1xuXHQgKiByZWZlcmVuY2VkLXR5cGUgbmFtZXMgcmVzb2x2ZSB0aHJvdWdoIHRoZSBmaWxlJ3Mgb3duIGltcG9ydCBzdGF0ZW1lbnRzXG5cdCAqIChGMTApIHJhdGhlciB0aGFuIGEgcHJvZ3JhbS13aWRlIG5hbWUgbWFwLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlSW1wb3J0IChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc0ltcG9ydERlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHsgbW9kdWxlU3BlY2lmaWVyIH0gPSBub2RlO1xuXHRcdGlmICghdHMuaXNTdHJpbmdMaXRlcmFsKG1vZHVsZVNwZWNpZmllcikpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgY2xhdXNlID0gbm9kZS5pbXBvcnRDbGF1c2U7XG5cdFx0aWYgKCFjbGF1c2UpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRsZXQgaW1wb3J0cyA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldChmaWxlUGF0aCk7XG5cdFx0aWYgKCFpbXBvcnRzKSB7XG5cdFx0XHRpbXBvcnRzID0gbmV3IE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlSW1wb3J0PigpO1xuXHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuc2V0KGZpbGVQYXRoLCBpbXBvcnRzKTtcblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgeyBTaGFyZWRTaGFwZSB9IGZyb20gJ+KApicgLyBpbXBvcnQgeyBTaGFyZWRTaGFwZSBhcyBTIH0gZnJvbSAn4oCmJ1xuXHRcdGlmIChjbGF1c2UubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVkSW1wb3J0cyhjbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBjbGF1c2UubmFtZWRCaW5kaW5ncy5lbGVtZW50cykge1xuXHRcdFx0XHRjb25zdCBsb2NhbE5hbWUgPSBlbGVtZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3Qgb3JpZ2luYWxOYW1lID0gZWxlbWVudC5wcm9wZXJ0eU5hbWUgPyBlbGVtZW50LnByb3BlcnR5TmFtZS50ZXh0IDogbG9jYWxOYW1lO1xuXHRcdFx0XHRpbXBvcnRzLnNldChsb2NhbE5hbWUsIHtcblx0XHRcdFx0XHRvcmlnaW5hbE5hbWUsXG5cdFx0XHRcdFx0c3BlY2lmaWVyICAgOiBtb2R1bGVTcGVjaWZpZXIudGV4dCxcblx0XHRcdFx0XHRpc05hbWVzcGFjZSA6IGZhbHNlXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIGltcG9ydCAqIGFzIG1vZGVscyBmcm9tICfigKYnIOKAlCByZXNvbHZlZCB3aGVuIGEgcXVhbGlmaWVkIG5hbWVcblx0XHQvLyAobW9kZWxzLlNoYXJlZFNoYXBlKSBpcyBlbmNvdW50ZXJlZFxuXHRcdGlmIChjbGF1c2UubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVzcGFjZUltcG9ydChjbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdGltcG9ydHMuc2V0KGNsYXVzZS5uYW1lZEJpbmRpbmdzLm5hbWUudGV4dCwge1xuXHRcdFx0XHRvcmlnaW5hbE5hbWUgOiAnJyxcblx0XHRcdFx0c3BlY2lmaWVyICAgIDogbW9kdWxlU3BlY2lmaWVyLnRleHQsXG5cdFx0XHRcdGlzTmFtZXNwYWNlICA6IHRydWVcblx0XHRcdH0pO1xuXHRcdH1cblxuXHRcdC8vIGltcG9ydCBTaGFyZWRTaGFwZSBmcm9tICfigKYnIChkZWZhdWx0IGltcG9ydClcblx0XHRpZiAoY2xhdXNlLm5hbWUpIHtcblx0XHRcdGltcG9ydHMuc2V0KGNsYXVzZS5uYW1lLnRleHQsIHtcblx0XHRcdFx0b3JpZ2luYWxOYW1lIDogJ2RlZmF1bHQnLFxuXHRcdFx0XHRzcGVjaWZpZXIgICAgOiBtb2R1bGVTcGVjaWZpZXIudGV4dCxcblx0XHRcdFx0aXNOYW1lc3BhY2UgIDogZmFsc2Vcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgcmUtZXhwb3J0IHdpcmluZyAoYGV4cG9ydCB7IFggfSBmcm9tICfigKYnYCwgYGV4cG9ydCAqIGZyb20gJ+KApidgLFxuXHQgKiBgZXhwb3J0IHsgWCBhcyBZIH1gKSBzbyByZXNvbHV0aW9uIGNhbiBjaGFzZSBiYXJyZWxzIHRvIHRoZSBvcmlnaW5cblx0ICogbW9kdWxlLiBNaXJyb3JzIE1vZHVsZUdyYXBoQnVpbGRlci5yZXNvbHZlT3JpZ2luLCBuYW1lLWJhc2VkIG9ubHkuXG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrUmVmZXJlbmNlZFR5cGVSZUV4cG9ydCAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNFeHBvcnREZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRjb25zdCB7IG1vZHVsZVNwZWNpZmllciB9ID0gbm9kZTtcblx0XHRjb25zdCBzcGVjaWZpZXJUZXh0ID0gbW9kdWxlU3BlY2lmaWVyICYmIHRzLmlzU3RyaW5nTGl0ZXJhbChtb2R1bGVTcGVjaWZpZXIpXG5cdFx0XHQ/IG1vZHVsZVNwZWNpZmllci50ZXh0XG5cdFx0XHQ6IHVuZGVmaW5lZDtcblxuXHRcdGlmIChub2RlLmV4cG9ydENsYXVzZSAmJiB0cy5pc05hbWVkRXhwb3J0cyhub2RlLmV4cG9ydENsYXVzZSkpIHtcblx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBub2RlLmV4cG9ydENsYXVzZS5lbGVtZW50cykge1xuXHRcdFx0XHRjb25zdCBleHBvcnRlZE5hbWUgPSBlbGVtZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgbG9jYWxOYW1lID0gZWxlbWVudC5wcm9wZXJ0eU5hbWUgPyBlbGVtZW50LnByb3BlcnR5TmFtZS50ZXh0IDogZXhwb3J0ZWROYW1lO1xuXHRcdFx0XHR0aGlzLm1hcmtCdWlsZGVyRXhwb3J0KGV4cG9ydGVkTmFtZSwgbG9jYWxOYW1lLCBmaWxlUGF0aCwgc3BlY2lmaWVyVGV4dCk7XG5cdFx0XHRcdGlmIChzcGVjaWZpZXJUZXh0KSB7XG5cdFx0XHRcdFx0Ly8gZXhwb3J0IHsgWCB9IGZyb20gJ+KApicgLyBleHBvcnQgeyBYIGFzIFkgfSBmcm9tICfigKYnXG5cdFx0XHRcdFx0bGV0IHJlRXhwb3J0cyA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuZ2V0KGZpbGVQYXRoKTtcblx0XHRcdFx0XHRpZiAoIXJlRXhwb3J0cykge1xuXHRcdFx0XHRcdFx0cmVFeHBvcnRzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0XHRcdFx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuc2V0KGZpbGVQYXRoLCByZUV4cG9ydHMpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRyZUV4cG9ydHMuc2V0KGV4cG9ydGVkTmFtZSwgc3BlY2lmaWVyVGV4dCk7XG5cdFx0XHRcdH0gZWxzZSBpZiAobG9jYWxOYW1lICE9PSBleHBvcnRlZE5hbWUpIHtcblx0XHRcdFx0XHQvLyBleHBvcnQgeyBYIGFzIFkgfSDigJQgc2FtZS1maWxlIGFsaWFzIG9mIGEgbG9jYWwgZGVjbGFyYXRpb25cblx0XHRcdFx0XHRsZXQgYWxpYXNlcyA9IHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRBbGlhc2VzLmdldChmaWxlUGF0aCk7XG5cdFx0XHRcdFx0aWYgKCFhbGlhc2VzKSB7XG5cdFx0XHRcdFx0XHRhbGlhc2VzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0XHRcdFx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRBbGlhc2VzLnNldChmaWxlUGF0aCwgYWxpYXNlcyk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdGFsaWFzZXMuc2V0KGV4cG9ydGVkTmFtZSwgbG9jYWxOYW1lKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGlmIChub2RlLmV4cG9ydENsYXVzZSAmJiB0cy5pc05hbWVzcGFjZUV4cG9ydChub2RlLmV4cG9ydENsYXVzZSkpIHtcblx0XHRcdC8vIGBleHBvcnQgKiBhcyBucyBmcm9tICfigKYnYCDigJQgYSBuZXN0ZWQgbW9kdWxlIG5hbWVzcGFjZTsgbWlkZGxlXG5cdFx0XHQvLyBzZWdtZW50cyBvZiBxdWFsaWZpZWQgcmVmZXJlbmNlcyAoYmFycmVsLkRlZXAuR2FkZ2V0KSBjaGFzZSBpdFxuXHRcdFx0aWYgKHNwZWNpZmllclRleHQpIHtcblx0XHRcdFx0bGV0IHN0YXJzID0gdGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZVN0YXJzLmdldChmaWxlUGF0aCk7XG5cdFx0XHRcdGlmICghc3RhcnMpIHtcblx0XHRcdFx0XHRzdGFycyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZVN0YXJzLnNldChmaWxlUGF0aCwgc3RhcnMpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHN0YXJzLnNldChub2RlLmV4cG9ydENsYXVzZS5uYW1lLnRleHQsIHNwZWNpZmllclRleHQpO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGlmICghbm9kZS5leHBvcnRDbGF1c2UgJiYgc3BlY2lmaWVyVGV4dCkge1xuXHRcdFx0Ly8gZXhwb3J0ICogZnJvbSAn4oCmJ1xuXHRcdFx0bGV0IHN0YXJzID0gdGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydFN0YXJzLmdldChmaWxlUGF0aCk7XG5cdFx0XHRpZiAoIXN0YXJzKSB7XG5cdFx0XHRcdHN0YXJzID0gW107XG5cdFx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycy5zZXQoZmlsZVBhdGgsIHN0YXJzKTtcblx0XHRcdH1cblx0XHRcdHN0YXJzLnB1c2goc3BlY2lmaWVyVGV4dCk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSBtb2R1bGUgc3BlY2lmaWVyIGZyb20gYSBjb250YWluaW5nIGZpbGUgd2l0aCB0aGUgcHJvZ3JhbSdzXG5cdCAqIGNvbXBpbGVyT3B0aW9ucyAodHNjb25maWcgYHBhdGhzYCwgZXh0ZW5zaW9ubGVzcyBpbXBvcnRzLCBpbmRleCBmaWxlcykuXG5cdCAqIE1vZHVsZSByZXNvbHV0aW9uIG9ubHkg4oCUIHRoZSBuby1nZXRUeXBlQ2hlY2tlcigpIHByZWNlZGVudCBzdGF5cy5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlIChzcGVjaWZpZXI6IHN0cmluZywgY29udGFpbmluZ0ZpbGU6IHN0cmluZyk6XG5cdFx0UmVmZXJlbmNlZFR5cGVSZXNvbHV0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBjYWNoZUtleSA9IGAke2NvbnRhaW5pbmdGaWxlfTo6JHtzcGVjaWZpZXJ9YDtcblx0XHRpZiAodGhpcy5yZWZlcmVuY2VkVHlwZVJlc29sdXRpb25DYWNoZS5oYXMoY2FjaGVLZXkpKSB7XG5cdFx0XHRjb25zdCBjYWNoZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbkNhY2hlLmdldChjYWNoZUtleSk7XG5cdFx0XHRyZXR1cm4gY2FjaGVkID09PSB1bmRlZmluZWQgPyB1bmRlZmluZWQgOiBjYWNoZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRzLnJlc29sdmVNb2R1bGVOYW1lKFxuXHRcdFx0c3BlY2lmaWVyLFxuXHRcdFx0Y29udGFpbmluZ0ZpbGUsXG5cdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlQ29tcGlsZXJPcHRpb25zLFxuXHRcdFx0dHMuc3lzXG5cdFx0KS5yZXNvbHZlZE1vZHVsZTtcblxuXHRcdGNvbnN0IHJlc3VsdDogUmVmZXJlbmNlZFR5cGVSZXNvbHV0aW9uIHwgdW5kZWZpbmVkID0gcmVzb2x1dGlvblxuXHRcdFx0PyB7XG5cdFx0XHRcdHJlc29sdmVkUGF0aCA6IG5vZGVQYXRoLnJlc29sdmUocmVzb2x1dGlvbi5yZXNvbHZlZEZpbGVOYW1lKSxcblx0XHRcdFx0aXNFeHRlcm5hbCAgIDogISFyZXNvbHV0aW9uLmlzRXh0ZXJuYWxMaWJyYXJ5SW1wb3J0XG5cdFx0XHR9XG5cdFx0XHQ6IHVuZGVmaW5lZDtcblxuXHRcdHRoaXMucmVmZXJlbmNlZFR5cGVSZXNvbHV0aW9uQ2FjaGUuc2V0KGNhY2hlS2V5LCByZXN1bHQpO1xuXHRcdGNvbnN0IGZpbmFsUmVzdWx0ID0gcmVzdWx0O1xuXHRcdHJldHVybiBmaW5hbFJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBMb29rIHVwIGEgbmFtZSBpbiBvbmUgcmVzb2x2ZWQgbW9kdWxlLCBjaGFzaW5nIHJlLWV4cG9ydCBiYXJyZWxzIHdpdGggYVxuXHQgKiBib3VuZGVkIGRlcHRoLiBFeHRlcm5hbCAobm9kZV9tb2R1bGVzKSBtb2R1bGVzIGhvbGQgbm8gaW4tcHJvamVjdFxuXHQgKiBkZWNsYXJhdGlvbnMgYW5kIHN0b3AgdGhlIGNoYXNlLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZSAoXG5cdFx0bW9kdWxlUGF0aDogc3RyaW5nLFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRkZXB0aDogbnVtYmVyXG5cdCk6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGlmIChkZXB0aCA+IE1BWF9SRUVYUE9SVF9DSEFTRV9ERVBUSCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBkZWNscyA9IHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0Y29uc3QgZGlyZWN0ID0gZGVjbHM/LmdldChuYW1lKTtcblx0XHRpZiAoZGlyZWN0KSB7XG5cdFx0XHRyZXR1cm4gZGlyZWN0O1xuXHRcdH1cblx0XHQvLyBleHBvcnQgeyBYIGFzIFkgfSDigJQgcmVzb2x2ZSB0aHJvdWdoIHRoZSBsb2NhbCBuYW1lXG5cdFx0Y29uc3QgbG9jYWxBbGlhcyA9IHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRBbGlhc2VzLmdldChtb2R1bGVQYXRoKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChsb2NhbEFsaWFzKSB7XG5cdFx0XHRjb25zdCBhbGlhc2VkID0gZGVjbHM/LmdldChsb2NhbEFsaWFzKTtcblx0XHRcdGlmIChhbGlhc2VkKSB7XG5cdFx0XHRcdHJldHVybiBhbGlhc2VkO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGNvbnN0IHJlRXhwb3J0cyA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGNvbnN0IHJlRXhwb3J0U3BlY2lmaWVyID0gcmVFeHBvcnRzPy5nZXQobmFtZSk7XG5cdFx0aWYgKHJlRXhwb3J0U3BlY2lmaWVyKSB7XG5cdFx0XHRjb25zdCBuZXh0UmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKHJlRXhwb3J0U3BlY2lmaWVyLCBtb2R1bGVQYXRoKTtcblx0XHRcdGlmIChuZXh0UmVzb2x1dGlvbiAmJiAhbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRjb25zdCBmb3VuZCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUobmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBuYW1lLCBkZXB0aCArIDEpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCBzdGFycyA9IHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0aWYgKHN0YXJzKSB7XG5cdFx0XHRmb3IgKGNvbnN0IHN0YXJTcGVjaWZpZXIgb2Ygc3RhcnMpIHtcblx0XHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShzdGFyU3BlY2lmaWVyLCBtb2R1bGVQYXRoKTtcblx0XHRcdFx0aWYgKCFuZXh0UmVzb2x1dGlvbiB8fCBuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgbmFtZSwgZGVwdGggKyAxKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgcmVmZXJlbmNlZCB0eXBlIG5hbWUgYXMgdXNlZCBpbiBmcm9tRmlsZSwgaW1wb3J0LWF3YXJlOlxuXHQgKiAgIDEuIHRoZSBmaWxlJ3Mgb3duIGltcG9ydCBzdGF0ZW1lbnRzIChyZWxhdGl2ZSArIHRzY29uZmlnIHBhdGhzLFxuXHQgKiAgICAgIGNoYXNlZCB0aHJvdWdoIHJlLWV4cG9ydCBiYXJyZWxzKSxcblx0ICogICAyLiB0aGUgZmlsZSdzIGxvY2FsIGRlY2xhcmF0aW9ucyxcblx0ICogICAzLiB0aGUgdW5pcXVlIHNhbWUtbmFtZWQgZGVjbGFyYXRpb24gYWNyb3NzIHNjYW5uZWQgZmlsZXMuXG5cdCAqIFJldHVybnMgdW5kZWZpbmVkIHdoZW4gbm90aGluZyBtYXRjaGVzIChvciB0aGUgbWF0Y2ggaXMgYW1iaWd1b3VzKSxcblx0ICogaW4gd2hpY2ggY2FzZSB0aGUgY2FsbGVyIGZhbGxzIGJhY2sgdG8gYHVua25vd25gLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiAoXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdGZyb21GaWxlOiBzdHJpbmdcblx0KTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gMS4gdGhlIGZpbGUncyBvd24gaW1wb3J0cyB3aW4g4oCUIGFuIGltcG9ydCBpcyBuZXZlciBzaGFkb3dlZCBieSBhXG5cdFx0Ly8gc2FtZS1uYW1lZCBsb2NhbCBkZWNsYXJhdGlvbiBlbHNld2hlcmUgaW4gdGhlIHByb2dyYW0gKEYxMClcblx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldChmcm9tRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAoaW1wb3J0ZWQgJiYgIWltcG9ydGVkLmlzTmFtZXNwYWNlKSB7XG5cdFx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoaW1wb3J0ZWQuc3BlY2lmaWVyLCBmcm9tRmlsZSk7XG5cdFx0XHRpZiAocmVzb2x1dGlvbiAmJiAhcmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZShyZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgaW1wb3J0ZWQub3JpZ2luYWxOYW1lLCAwKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gMi4gbG9jYWwgZGVjbGFyYXRpb24gaW4gdGhlIHJlZmVyZW5jaW5nIGZpbGUgaXRzZWxmXG5cdFx0Y29uc3QgbG9jYWwgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRGVjbHMuZ2V0KGZyb21GaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChsb2NhbCkge1xuXHRcdFx0cmV0dXJuIGxvY2FsO1xuXHRcdH1cblxuXHRcdC8vIDMuIHByb2dyYW0td2lkZSBmYWxsYmFjaywgdW5pcXVlIGRlY2xhcmF0aW9uIG9ubHkg4oCUIGFtYmlndWl0eSBhbmRcblx0XHQvLyBhYnNlbmNlIGJvdGggeWllbGQgdW5kZWZpbmVkICh0aGUgY2FsbGVyIGVtaXRzIGB1bmtub3duYCkuXG5cdFx0Ly8gRXh0ZXJuYWwvYW1iaWVudCBkZWNsYXJhdGlvbnMgKC5kLnRzLCBub2RlX21vZHVsZXMpIGRvIG5vdFxuXHRcdC8vIHBhcnRpY2lwYXRlOiBhIHVzZXItbG9jYWwgZGVjbGFyYXRpb24gYWx3YXlzIHdpbnMgb3ZlciBhXG5cdFx0Ly8gcGFja2FnZS1kZWNsYXJlZCBzYW1lLW5hbWVkIHR5cGUgKHRoZSBwbGFpbi1UUyB0aWVyIG9mIHRoZVxuXHRcdC8vIGlkZW50aXR5IGxhdzsgYW1iaWd1aXR5IGFtb25nIHRoZSByZW1haW5pbmcgZGVjbGFyYXRpb25zIGlzXG5cdFx0Ly8gdmFsaWRhdGVkIHNlcGFyYXRlbHkgYXMgYSBoYXJkIGZhaWwpXG5cdFx0bGV0IHVuaXF1ZTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZDtcblx0XHRsZXQgY291bnQgPSAwO1xuXHRcdGZvciAoY29uc3QgWyBmaWxlUGF0aCwgZGVjbHMgXSBvZiB0aGlzLnJlZmVyZW5jZWRUeXBlRGVjbHMpIHtcblx0XHRcdGlmICh0aGlzLmlzRXh0ZXJuYWxEZWNsRmlsZShmaWxlUGF0aCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBjYW5kaWRhdGUgPSBkZWNscy5nZXQobmFtZSk7XG5cdFx0XHRpZiAoY2FuZGlkYXRlKSB7XG5cdFx0XHRcdGNvdW50Kys7XG5cdFx0XHRcdHVuaXF1ZSA9IGNhbmRpZGF0ZTtcblx0XHRcdFx0aWYgKGNvdW50ID4gMSkge1xuXHRcdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCByZXN1bHQgPSBjb3VudCA9PT0gMSA/IHVuaXF1ZSA6IHVuZGVmaW5lZDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dGVybmFsL2FtYmllbnQgZGVjbGFyYXRpb24gZmlsZXMgKC5kLnRzLCBhbnl0aGluZyB1bmRlclxuXHQgKiBub2RlX21vZHVsZXMpIG5ldmVyIHBhcnRpY2lwYXRlIGluIHBsYWluLVRTIHJlZmVyZW5jZWQtdHlwZVxuXHQgKiByZXNvbHV0aW9uIG9yIHRoZSBhbWJpZ3VpdHkgbGF3OiB0aGV5IGFyZSBub3QgcHJvamVjdCBzb3VyY2UsIHRoZVxuXHQgKiBDTEkgbmV2ZXIgYW5hbHl6ZXMgdGhlbSwgYW5kIGEgdXNlci1sb2NhbCBkZWNsYXJhdGlvbiBhbHdheXMgd2luc1xuXHQgKiBvdmVyIGEgcGFja2FnZS1kZWNsYXJlZCBzYW1lLW5hbWVkIHR5cGUuXG5cdCAqL1xuXHRwcml2YXRlIGlzRXh0ZXJuYWxEZWNsRmlsZSAoZmlsZTogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgZXh0ZXJuYWwgPSBmaWxlLmVuZHNXaXRoKCcuZC50cycpIHx8XG5cdFx0XHRmaWxlLmluY2x1ZGVzKGAke25vZGVQYXRoLnNlcH1ub2RlX21vZHVsZXMke25vZGVQYXRoLnNlcH1gKTtcblx0XHRyZXR1cm4gZXh0ZXJuYWw7XG5cdH1cblxuXHQvKipcblx0ICogUHJvcGVydGllcyBvZiBhIHJlZmVyZW5jZWQgY2xhc3MvaW50ZXJmYWNlL2FsaWFzLW9mLWxpdGVyYWwgZGVjbGFyYXRpb24sXG5cdCAqIHNoYXJlZCBieSBgdGhpczpgLXBhcmFtZXRlciBleHBhbnNpb24gYW5kIGlubGluZSB0eXBlIGVtaXNzaW9uLlxuXHQgKiBJbmhlcml0ZWQgbWVtYmVycyBhcmUgaW5jbHVkZWQ6IHRoZSBleHRlbmRzIGNoYWluIGlzIHdhbGtlZFxuXHQgKiAoZGVwdGgtY2FwcGVkLCBjeWNsZS1ndWFyZGVkKSBhbmQgcGFyZW50IGZpZWxkcyBtZXJnZSBmaXJzdCwgdGhlXG5cdCAqIGRlY2xhcmF0aW9uJ3Mgb3duIGZpZWxkcyBvdmVycmlkaW5nIG9uIG5hbWUgY2xhc2guXG5cdCAqL1xuXHRwcml2YXRlIHJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXMgKGRlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24pOlxuXHRcdE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHZpc2l0ZWQgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHRjb25zdCBwcm9wZXJ0aWVzID0gdGhpcy5yZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzSW5uZXIoZGVjbCwgdmlzaXRlZCwgMCk7XG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHRwcml2YXRlIHJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXNJbm5lciAoXG5cdFx0ZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbixcblx0XHR2aXNpdGVkOiBTZXQ8c3RyaW5nPixcblx0XHRkZXB0aDogbnVtYmVyXG5cdCk6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IG93blByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXHRcdGNvbnN0IGRlY2xOb2RlID0gZGVjbC5ub2RlIGFzIHRzLkNsYXNzRGVjbGFyYXRpb24gfCB0cy5JbnRlcmZhY2VEZWNsYXJhdGlvbjtcblx0XHRjb25zdCBkZWNsTmFtZSA9IGRlY2xOb2RlLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKGRlY2xOb2RlLm5hbWUpID8gZGVjbE5vZGUubmFtZS50ZXh0IDogJyc7XG5cdFx0Y29uc3QgdmlzaXRLZXkgPSBgJHtkZWNsLmtpbmR9OiR7ZGVjbC5maWxlfToke2RlY2xOYW1lfWA7XG5cdFx0aWYgKGRlcHRoID4gTUFYX0hFUklUQUdFX0RFUFRIIHx8IHZpc2l0ZWQuaGFzKHZpc2l0S2V5KSkge1xuXHRcdFx0cmV0dXJuIG93blByb3BlcnRpZXM7XG5cdFx0fVxuXHRcdHZpc2l0ZWQuYWRkKHZpc2l0S2V5KTtcblxuXHRcdGlmIChkZWNsLmtpbmQgPT09ICdjbGFzcycpIHtcblx0XHRcdGNvbnN0IGNsYXNzUHJvcHMgPSB0aGlzLmV4dHJhY3RDbGFzc1Byb3BlcnRpZXMoZGVjbC5ub2RlIGFzIHRzLkNsYXNzRGVjbGFyYXRpb24pO1xuXHRcdFx0Zm9yIChjb25zdCBbIG5hbWUsIGluZm8gXSBvZiBjbGFzc1Byb3BzKSB7XG5cdFx0XHRcdG93blByb3BlcnRpZXMuc2V0KG5hbWUsIGluZm8pO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSBpZiAoZGVjbC5raW5kID09PSAnaW50ZXJmYWNlJykge1xuXHRcdFx0Y29uc3QgaWZhY2UgPSBkZWNsLm5vZGUgYXMgdHMuSW50ZXJmYWNlRGVjbGFyYXRpb247XG5cdFx0XHR0aGlzLmNvbGxlY3RUeXBlRWxlbWVudFByb3BlcnRpZXMoWyAuLi5pZmFjZS5tZW1iZXJzIF0sIG93blByb3BlcnRpZXMpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHRjb25zdCBhbGlhc1R5cGUgPSAoZGVjbC5ub2RlIGFzIHRzLlR5cGVBbGlhc0RlY2xhcmF0aW9uKS50eXBlO1xuXHRcdFx0aWYgKHRzLmlzVHlwZUxpdGVyYWxOb2RlKGFsaWFzVHlwZSkpIHtcblx0XHRcdFx0dGhpcy5jb2xsZWN0VHlwZUVsZW1lbnRQcm9wZXJ0aWVzKFsgLi4uYWxpYXNUeXBlLm1lbWJlcnMgXSwgb3duUHJvcGVydGllcyk7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRyZXR1cm4gb3duUHJvcGVydGllcztcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBoZXJpdGFnZSBtZXJnZXMgcGFyZW50IGZpZWxkcyBmaXJzdDsgdGhlIGRlY2xhcmF0aW9uJ3Mgb3duIGZpZWxkc1xuXHRcdC8vIG92ZXJyaWRlIG9uIG5hbWUgY2xhc2ggKGxhdGVyIGJhc2VzIG92ZXJyaWRlIGVhcmxpZXIgb25lcylcblx0XHRjb25zdCBtZXJnZWQgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXHRcdGZvciAoY29uc3QgYmFzZURlY2wgb2YgdGhpcy5yZXNvbHZlSGVyaXRhZ2VEZWNsYXJhdGlvbnMoZGVjbCkpIHtcblx0XHRcdGNvbnN0IGJhc2VQcm9wcyA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllc0lubmVyKGJhc2VEZWNsLCB2aXNpdGVkLCBkZXB0aCArIDEpO1xuXHRcdFx0Zm9yIChjb25zdCBbIG5hbWUsIGluZm8gXSBvZiBiYXNlUHJvcHMpIHtcblx0XHRcdFx0bWVyZ2VkLnNldChuYW1lLCBpbmZvKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0Zm9yIChjb25zdCBbIG5hbWUsIGluZm8gXSBvZiBvd25Qcm9wZXJ0aWVzKSB7XG5cdFx0XHRtZXJnZWQuc2V0KG5hbWUsIGluZm8pO1xuXHRcdH1cblx0XHRyZXR1cm4gbWVyZ2VkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb3BlcnR5IHNpZ25hdHVyZXMgb2YgaW50ZXJmYWNlL2FsaWFzIHR5cGUtbGl0ZXJhbCBtZW1iZXJzLCBpbnRvXG5cdCAqIHRoZSBnaXZlbiBtYXAuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RUeXBlRWxlbWVudFByb3BlcnRpZXMgKFxuXHRcdG1lbWJlcnM6IHJlYWRvbmx5IHRzLlR5cGVFbGVtZW50W10sXG5cdFx0cHJvcGVydGllczogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPlxuXHQpOiB2b2lkIHtcblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBtZW1iZXJzKSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChwcm9wTmFtZSwge1xuXHRcdFx0XHRcdG5hbWUgICAgIDogcHJvcE5hbWUsXG5cdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHRoZSBoZXJpdGFnZSBjbGF1c2Ugb2YgYSBjbGFzcyAoYGV4dGVuZHMgQmFzZWApIG9yIGludGVyZmFjZVxuXHQgKiAoYGV4dGVuZHMgQSwgQmApIHRvIHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbnMgdGhyb3VnaCB0aGUgU0FNRVxuXHQgKiBpbXBvcnQtYXdhcmUgbWFjaGluZXJ5IGFzIHBsYWluIHJlZmVyZW5jZXMgKHRoZSBkZWNsYXJpbmcgZmlsZSdzIG93blxuXHQgKiBpbXBvcnRzIGZpcnN0LCB0aGVuIGl0cyBsb2NhbHMsIHRoZW4gdGhlIHVuaXF1ZSBwcm9ncmFtLXdpZGVcblx0ICogZGVjbGFyYXRpb24pLiBVbnJlc29sdmFibGUgb3IgZXh0ZXJuYWwgYmFzZXMgeWllbGQgbm90aGluZyDigJQgdGhlaXJcblx0ICogaW5oZXJpdGVkIGZpZWxkcyBzaW1wbHkgc3RheSBhYnNlbnQsIHNhbWUgYXMgYmVmb3JlIHRoaXMgd2Fsa1xuXHQgKiBleGlzdGVkLiBNaXhpbiBjYWxscyAoYGV4dGVuZHMgbWl4aW4oWClgKSBhbmQgbmFtZXNwYWNlIGFjY2VzcyBhcmVcblx0ICogbm90IGZvbGxvd2VkLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlSGVyaXRhZ2VEZWNsYXJhdGlvbnMgKGRlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24pOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uW10ge1xuXHRcdGNvbnN0IHsgaGVyaXRhZ2VDbGF1c2VzIH0gPSAoZGVjbC5ub2RlIGFzIHRzLkNsYXNzRGVjbGFyYXRpb24gfCB0cy5JbnRlcmZhY2VEZWNsYXJhdGlvbik7XG5cdFx0aWYgKCFoZXJpdGFnZUNsYXVzZXMpIHtcblx0XHRcdHJldHVybiBbXTtcblx0XHR9XG5cdFx0Y29uc3QgYmFzZXM6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25bXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgY2xhdXNlIG9mIGhlcml0YWdlQ2xhdXNlcykge1xuXHRcdFx0aWYgKGNsYXVzZS50b2tlbiAhPT0gdHMuU3ludGF4S2luZC5FeHRlbmRzS2V5d29yZCkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3QgaGVyaXRhZ2VUeXBlIG9mIGNsYXVzZS50eXBlcykge1xuXHRcdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihoZXJpdGFnZVR5cGUuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBiYXNlTmFtZSA9IGhlcml0YWdlVHlwZS5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRcdGNvbnN0IGJhc2VEZWNsID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihiYXNlTmFtZSwgZGVjbC5maWxlKTtcblx0XHRcdFx0aWYgKGJhc2VEZWNsKSB7XG5cdFx0XHRcdFx0YmFzZXMucHVzaChiYXNlRGVjbCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gYmFzZXM7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHBhbmQgYSByZWZlcmVuY2VkLXR5cGUgZGVjbGFyYXRpb24gdG8gYSBzZWxmLWNvbnRhaW5lZCB0eXBlIHN0cmluZ1xuXHQgKiBmb3IgZW1pc3Npb24gaW50byBnZW5lcmF0ZWQgZmlsZXM6IHR5cGUgYWxpYXNlcyB0aHJvdWdoIGluZmVyVHlwZSxcblx0ICogY2xhc3NlcyBhbmQgaW50ZXJmYWNlcyB0aHJvdWdoIHRoZWlyIChwdWJsaWMsIG5vbi1tZXRob2QpIGZpZWxkcy5cblx0ICogTmVzdGVkIHJlZmVyZW5jZXMgcmVzb2x2ZSBhZ2FpbnN0IHRoZSBkZWNsYXJpbmcgZmlsZSB3aGlsZSBleHBhbmRpbmcuXG5cdCAqL1xuXHRwcml2YXRlIGV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gKGRlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IHJlZmVyZW5jaW5nRmlsZSA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSBkZWNsLmZpbGU7XG5cdFx0dHJ5IHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMuZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbklubmVyKGRlY2wpO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gcmVmZXJlbmNpbmdGaWxlO1xuXHRcdH1cblx0fVxuXG5cdHByaXZhdGUgZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbklubmVyIChkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoZGVjbC5raW5kID09PSAnYWxpYXMnKSB7XG5cdFx0XHRjb25zdCBhbGlhc05vZGUgPSBkZWNsLm5vZGUgYXMgdHMuVHlwZUFsaWFzRGVjbGFyYXRpb247XG5cdFx0XHRjb25zdCBhbGlhc05hbWUgPSB0cy5pc0lkZW50aWZpZXIoYWxpYXNOb2RlLm5hbWUpID8gYWxpYXNOb2RlLm5hbWUudGV4dCA6ICcnO1xuXHRcdFx0aWYgKGFsaWFzTmFtZSAmJiB0aGlzLmV4cGFuZGluZ1JlZmVyZW5jZWRBbGlhc2VzLmhhcyhhbGlhc05hbWUpKSB7XG5cdFx0XHRcdC8vIFNlbGYtcmVmZXJlbnRpYWwgYWxpYXMgY2hhaW4g4oCUIGJhaWwgb3V0XG5cdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHR9XG5cdFx0XHRpZiAoYWxpYXNOYW1lKSB7XG5cdFx0XHRcdHRoaXMuZXhwYW5kaW5nUmVmZXJlbmNlZEFsaWFzZXMuYWRkKGFsaWFzTmFtZSk7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMuaW5mZXJUeXBlKGFsaWFzTm9kZS50eXBlKTtcblx0XHRcdGlmIChhbGlhc05hbWUpIHtcblx0XHRcdFx0dGhpcy5leHBhbmRpbmdSZWZlcmVuY2VkQWxpYXNlcy5kZWxldGUoYWxpYXNOYW1lKTtcblx0XHRcdH1cblx0XHRcdHJldHVybiBleHBhbmRlZDtcblx0XHR9XG5cblx0XHRjb25zdCBkZWNsUHJvcGVydGllcyA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllcyhkZWNsKTtcblx0XHRjb25zdCBwcm9wcyA9IEFycmF5LmZyb20oZGVjbFByb3BlcnRpZXMuZW50cmllcygpKS5tYXAoKFsgcHJvcE5hbWUsIGluZm8gXSkgPT4ge1xuXHRcdFx0Y29uc3Qgb3B0aW9uYWwgPSBpbmZvLm9wdGlvbmFsID8gJz8nIDogJyc7XG5cdFx0XHRyZXR1cm4gYCR7cHJvcE5hbWV9JHtvcHRpb25hbH06ICR7aW5mby50eXBlfWA7XG5cdFx0fSk7XG5cblx0XHRjb25zdCByZXN1bHQgPSBgeyAke3Byb3BzLmpvaW4oJzsgJyl9IH1gO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRW1pdHRlZCBpbnN0YW5jZS10eXBlIGFsaWFzIGZvciBhIGdyYXBoIG5vZGUg4oCUIHRoZSBuYW1lIHR5cGVzLnRzIC9cblx0ICogcmVnaXN0cnkudHMgYWN0dWFsbHkgZGVjbGFyZS4gT3B0aW9uIEIgY29sbGVjdGlvbiB0eXBlcyBjYXJyeSB0aGVpclxuXHQgKiByZWdpc3RyeSBpbnRlcmZhY2UgcHJlZml4OyBjb2xsZWN0aW9uIHR5cGVzIFdJVEhPVVQgYSByZWdpc3RyeVxuXHQgKiBpbnRlcmZhY2UgYXJlIG5ldmVyIGVtaXR0ZWQsIHNvIG5vIHZhbGlkIGFsaWFzIGV4aXN0cyBmb3IgdGhlbVxuXHQgKiAodW5kZWZpbmVkIOKAlCBjYWxsZXJzIGRlZ3JhZGUgdG8gYHVua25vd25gLCBuZXZlciBhIGJhcmUgbmFtZSkuXG5cdCAqL1xuXHRwcml2YXRlIGdldEVtaXR0ZWRJbnN0YW5jZVR5cGVOYW1lIChub2RlOiBUeXBlTm9kZSk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKG5vZGUuY29sbGVjdGlvbklkICYmICFub2RlLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgZG90dGVkID0gbm9kZS5jb2xsZWN0aW9uSWRcblx0XHRcdD8gbm9kZS5mdWxsUGF0aC5zbGljZShub2RlLmNvbGxlY3Rpb25JZC5sZW5ndGggKyAyKVxuXHRcdFx0OiBub2RlLmZ1bGxQYXRoO1xuXHRcdGNvbnN0IHByZWZpeCA9IG5vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lID8gYCR7bm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWV9X2AgOiAnJztcblx0XHRjb25zdCByZXN1bHQgPSBgJHtwcmVmaXh9JHtkb3R0ZWQucmVwbGFjZSgvXFwuL2csICdfJyl9YDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSBzaW1wbGUgKG5vbi1xdWFsaWZpZWQpIHR5cGUgcmVmZXJlbmNlOiBpbXBvcnQtYXdhcmVcblx0ICogZGVjbGFyYXRpb24gZXhwYW5zaW9uIGZpcnN0LCB0aGVuIHRoZSBJbnN0YW5jZVR5cGU8dHlwZW9mIFg+IHBhdHRlcm4sXG5cdCAqIHRoZW4gbW5lbW9uaWNhIGdyYXBoIHR5cGVzOyBrbm93biBnbG9iYWxzIGtlZXAgdGhlaXIgYmFyZSBuYW1lIGFuZFxuXHQgKiBhbnl0aGluZyBlbHNlIGZhbGxzIGJhY2sgdG8gYHVua25vd25gIHNvIGdlbmVyYXRlZCBmaWxlcyBuZXZlciBjYXJyeVxuXHQgKiBhbiB1bnJlc29sdmFibGUgYmFyZSBuYW1lLiBSZXR1cm5zIHVuZGVmaW5lZCB3aGVuIHRoZSBjYWxsZXIgc2hvdWxkXG5cdCAqIGtlZXAgdGhlIGdlbmVyaWMgc3BlbGxpbmcgKGhhbmRsZWQgc2VwYXJhdGVseSkuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVTaW1wbGVUeXBlUmVmZXJlbmNlIChcblx0XHR0eXBlTmFtZTogc3RyaW5nLFxuXHRcdHR5cGVBcmdzPzogdHMuTm9kZUFycmF5PHRzLlR5cGVOb2RlPixcblx0XHRyZWZOb2RlPzogdHMuTm9kZVxuXHQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdC8vIEltcG9ydC1hd2FyZSByZWZlcmVuY2VkLXR5cGUgZGVjbGFyYXRpb24gKEYxMClcblx0XHRjb25zdCBkZWNsID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbih0eXBlTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRpZiAoZGVjbCkge1xuXHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oZGVjbCk7XG5cdFx0XHRpZiAoZXhwYW5kZWQgIT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRyZXR1cm4gZXhwYW5kZWQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCB1bmtub3duUmVzdWx0ID0gJ3Vua25vd24nO1xuXHRcdFx0cmV0dXJuIHVua25vd25SZXN1bHQ7XG5cdFx0fVxuXG5cdFx0Ly8gSW5zdGFuY2VUeXBlPHR5cGVvZiBYPiBsYXcgKDAuMi4wIGJlaGF2aW9yLCByZXN0b3JlZCk6IHRoZVxuXHRcdC8vIGdlbmVyYXRlZCBhbGlhcyBhbHJlYWR5IElTIHRoZSBpbnN0YW5jZSB0eXBlIOKAlCByZXNvbHZlIFggdGhyb3VnaFxuXHRcdC8vIHRoZSBncmFwaCB0aWVycyBhbmQgZHJvcCB0aGUgd3JhcHBlci4gTXVzdCBydW4gQkVGT1JFIHRoZSBncmFwaFxuXHRcdC8vIHJlc29sdXRpb246ICdJbnN0YW5jZVR5cGUnIGlzIGFuIGFtYmllbnQgZ2xvYmFsLCBuZXZlciBhIGdyYXBoXG5cdFx0Ly8gdHlwZSAodGhlIG9sZCBzcGVjaWFsIGNhc2UgYmVsb3cgc2F0IGluc2lkZSB0aGUgZ3JhcGgtdW5pcXVlXG5cdFx0Ly8gYnJhbmNoIGFuZCB3YXMgZGVhZCBjb2RlKS4gV2hlbiBYIGRvZXMgbm90IHJlc29sdmUsIHRoZSBXSE9MRVxuXHRcdC8vIGV4cHJlc3Npb24gZGVncmFkZXMgdG8gYHVua25vd25gIOKAlCBuZXZlciBlbWl0XG5cdFx0Ly8gYEluc3RhbmNlVHlwZTx1bmtub3duPmA6IGludmFsaWQgVFMgKFRTMjM0NCwgJ3Vua25vd24nIGRvZXMgbm90XG5cdFx0Ly8gc2F0aXNmeSB0aGUgY29uc3RydWN0b3IgY29uc3RyYWludCkuIFJlYWNoZWQgZGlyZWN0bHkgb3IgdGhyb3VnaFxuXHRcdC8vIGEgbG9jYWwgYWxpYXMgKGBYSW5zdGFuY2UgPSBJbnN0YW5jZVR5cGU8dHlwZW9mIFg+YCkuXG5cdFx0aWYgKHR5cGVOYW1lID09PSAnSW5zdGFuY2VUeXBlJyAmJiB0eXBlQXJncyAmJiB0eXBlQXJncy5sZW5ndGggPT09IDEpIHtcblx0XHRcdGNvbnN0IFsgaW5zdGFuY2VBcmcgXSA9IHR5cGVBcmdzO1xuXHRcdFx0aWYgKGluc3RhbmNlQXJnICYmIHRzLmlzVHlwZVF1ZXJ5Tm9kZShpbnN0YW5jZUFyZykgJiYgdHMuaXNJZGVudGlmaWVyKGluc3RhbmNlQXJnLmV4cHJOYW1lKSkge1xuXHRcdFx0XHRjb25zdCBxdWVyeVJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUoaW5zdGFuY2VBcmcuZXhwck5hbWUudGV4dCk7XG5cdFx0XHRcdGlmIChxdWVyeVJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRcdFx0Ly8gdW5kZWZpbmVkIHdoZW4gdGhlIHR5cGUgaXMgbmV2ZXIgZW1pdHRlZCAoY29sbGVjdGlvblxuXHRcdFx0XHRcdC8vIHdpdGhvdXQgYSByZWdpc3RyeSBpbnRlcmZhY2UpIOKAlCBkZWdyYWRlLCBuZXZlciBiYXJlXG5cdFx0XHRcdFx0Y29uc3QgYWxpYXNSZXN1bHQgPSB0aGlzLmdldEVtaXR0ZWRJbnN0YW5jZVR5cGVOYW1lKHF1ZXJ5UmVzdWx0Lm5vZGUpID8/ICd1bmtub3duJztcblx0XHRcdFx0XHRyZXR1cm4gYWxpYXNSZXN1bHQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKHF1ZXJ5UmVzdWx0LnN0YXR1cyA9PT0gJ2FtYmlndW91cycpIHtcblx0XHRcdFx0XHR0aGlzLnJlY29yZEdyYXBoUmVmZXJlbmNlRXJyb3IoaW5zdGFuY2VBcmcuZXhwck5hbWUudGV4dCwgaW5zdGFuY2VBcmcsIHF1ZXJ5UmVzdWx0KTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBkZWdyYWRlZFJlc3VsdCA9ICd1bmtub3duJztcblx0XHRcdFx0cmV0dXJuIGRlZ3JhZGVkUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgaW5mZXJyZWRBcmcgPSB0aGlzLmluZmVyVHlwZShpbnN0YW5jZUFyZyk7XG5cdFx0XHRpZiAoaW5mZXJyZWRBcmcgPT09ICd1bmtub3duJykge1xuXHRcdFx0XHRjb25zdCBkZWdyYWRlZFdyYXBwZXIgPSAndW5rbm93bic7XG5cdFx0XHRcdHJldHVybiBkZWdyYWRlZFdyYXBwZXI7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCB3cmFwcGVkUmVzdWx0ID0gYEluc3RhbmNlVHlwZTwke2luZmVycmVkQXJnfT5gO1xuXHRcdFx0cmV0dXJuIHdyYXBwZWRSZXN1bHQ7XG5cdFx0fVxuXG5cdFx0Ly8gTW5lbW9uaWNhLWdyYXBoIGlkZW50aXR5IGxhdzogcGF0aC1hd2FyZSByZXNvbHV0aW9uICh2YWx1ZSBzY29wZSxcblx0XHQvLyBpbXBvcnRzLCBuZWFyZXN0LWNoYWluLCByb290LCBwcm9ncmFtLXdpZGUpLiBBbWJpZ3VpdHkgYmV0d2VlblxuXHRcdC8vIHJlYWwgZ3JhcGggdHlwZXMgaXMgYSBoYXJkIGZhaWx1cmU7IGEgbmFtZSBubyBncmFwaCB0eXBlIGNhcnJpZXNcblx0XHQvLyBzdGF5cyBpbiB0aGUgcGxhaW4tVFMgc29mdCBzY29wZSBhbmQgZmFsbHMgdG8gYHVua25vd25gLlxuXHRcdGNvbnN0IGdyYXBoUmVzdWx0ID0gdGhpcy5yZXNvbHZlR3JhcGhUeXBlTmFtZSh0eXBlTmFtZSk7XG5cdFx0aWYgKGdyYXBoUmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdC8vIEhhbmRsZSBJbnN0YW5jZVR5cGU8dHlwZW9mIFg+IHBhdHRlcm4gLT4gY29udmVydCB0byBQYXJlbnRfWFxuXHRcdFx0aWYgKHR5cGVOYW1lID09PSAnSW5zdGFuY2VUeXBlJyAmJiB0eXBlQXJncyAmJiB0eXBlQXJncy5sZW5ndGggPT09IDEpIHtcblx0XHRcdFx0Y29uc3QgWyBhcmcgXSA9IHR5cGVBcmdzO1xuXHRcdFx0XHRpZiAoYXJnLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVHlwZVF1ZXJ5KSB7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZVF1ZXJ5ID0gYXJnIGFzIHRzLlR5cGVRdWVyeU5vZGU7XG5cdFx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcih0eXBlUXVlcnkuZXhwck5hbWUpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBxdWVyeVJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUodHlwZVF1ZXJ5LmV4cHJOYW1lLnRleHQpO1xuXHRcdFx0XHRcdFx0aWYgKHF1ZXJ5UmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdFx0XHRcdFx0Ly8gRW1pdHRlZCBhbGlhczogVXNhZ2VzLlVzYWdlRW50cnkgLT4gVXNhZ2VzX1VzYWdlRW50cnlcblx0XHRcdFx0XHRcdFx0Ly8gKE9wdGlvbiBCIGNvbGxlY3Rpb25zIGNhcnJ5IHRoZSByZWdpc3RyeSBwcmVmaXg7XG5cdFx0XHRcdFx0XHRcdC8vIHVuZGVmaW5lZCB3aGVuIG5ldmVyIGVtaXR0ZWQg4oCUIGRlZ3JhZGUpXG5cdFx0XHRcdFx0XHRcdGNvbnN0IHF1ZXJ5QWxpYXMgPSB0aGlzLmdldEVtaXR0ZWRJbnN0YW5jZVR5cGVOYW1lKHF1ZXJ5UmVzdWx0Lm5vZGUpID8/ICd1bmtub3duJztcblx0XHRcdFx0XHRcdFx0cmV0dXJuIHF1ZXJ5QWxpYXM7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRpZiAocXVlcnlSZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0XHRcdFx0XHR0aGlzLnJlY29yZEdyYXBoUmVmZXJlbmNlRXJyb3IodHlwZVF1ZXJ5LmV4cHJOYW1lLnRleHQsIHR5cGVRdWVyeSwgcXVlcnlSZXN1bHQpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0Ly8gTm90IGEga25vd24gbW5lbW9uaWNhIHR5cGUg4oCUIG5vIGJhcmUgZW1pc3Npb25cblx0XHRcdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAoIXR5cGVBcmdzIHx8IHR5cGVBcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHQvLyBFbWl0dGVkIGFsaWFzOiBVc2FnZXMuVXNhZ2VFbnRyeSAtPiBVc2FnZXNfVXNhZ2VFbnRyeVxuXHRcdFx0XHQvLyAoT3B0aW9uIEIgY29sbGVjdGlvbnMgY2FycnkgdGhlIHJlZ2lzdHJ5IHByZWZpeDtcblx0XHRcdFx0Ly8gdW5kZWZpbmVkIHdoZW4gbmV2ZXIgZW1pdHRlZCDigJQgZGVncmFkZSlcblx0XHRcdFx0Y29uc3QgZ3JhcGhBbGlhcyA9IHRoaXMuZ2V0RW1pdHRlZEluc3RhbmNlVHlwZU5hbWUoZ3JhcGhSZXN1bHQubm9kZSkgPz8gJ3Vua25vd24nO1xuXHRcdFx0XHRyZXR1cm4gZ3JhcGhBbGlhcztcblx0XHRcdH1cblx0XHRcdC8vIEdlbmVyaWMgdXNlIG9mIGEgZ3JhcGggdHlwZSBrZWVwcyBpdHMgc2ltcGxlIG5hbWU7IHRoZVxuXHRcdFx0Ly8gZ2VuZXJhdG9yIHVwZ3JhZGVzIGl0IHRvIHRoZSBmdWxsLXBhdGggaW5zdGFuY2UgdHlwZSBuYW1lXG5cdFx0XHRyZXR1cm4gYCR7dHlwZU5hbWV9PCR7dHlwZUFyZ3MubWFwKGEgPT4gdGhpcy5pbmZlclR5cGUoYSkpLmpvaW4oJywgJyl9PmA7XG5cdFx0fVxuXHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHR0aGlzLnJlY29yZEdyYXBoUmVmZXJlbmNlRXJyb3IodHlwZU5hbWUsIHJlZk5vZGUgPz8gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlLCBncmFwaFJlc3VsdCk7XG5cdFx0fVxuXG5cdFx0aWYgKHR5cGVBcmdzICYmIHR5cGVBcmdzLmxlbmd0aCA+IDApIHtcblx0XHRcdGlmIChLTk9XTl9HTE9CQUxfVFlQRVMuaGFzKHR5cGVOYW1lKSkge1xuXHRcdFx0XHRjb25zdCBnZW5lcmljUmVzdWx0ID0gYCR7dHlwZU5hbWV9PCR7dHlwZUFyZ3MubWFwKGEgPT4gdGhpcy5pbmZlclR5cGUoYSkpLmpvaW4oJywgJyl9PmA7XG5cdFx0XHRcdHJldHVybiBnZW5lcmljUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0Ly8gRW1pc3Npb24gcmVzdG9yYXRpb24gKDAuMi4wIGJlaGF2aW9yKTogYSBub24tZ3JhcGggb3V0ZXJcblx0XHRcdC8vIGdlbmVyaWMgdGhhdCBpcyBOT1QgZGVjbGFyZWQgaW4gYW55IGFuYWx5emVkIHByb2plY3QgZmlsZSBpc1xuXHRcdFx0Ly8gYW4gYW1iaWVudC9saWIgY29uc3RydWN0IChNYXBJdGVyYXRvciwgbGliIGhlbHBlcnMpIOKAlCBpdFxuXHRcdFx0Ly8gcmVzb2x2ZXMgaW4gZXZlcnkgY29uc3VtZXIgY29tcGlsYXRpb24gd2l0aG91dCBhbiBpbXBvcnQsIHNvXG5cdFx0XHQvLyBlbWl0IGl0IFZFUkJBVElNIHdpdGggaW5uZXIgZ3JhcGggYWxpYXNlcyByZXNvbHZlZC4gQSBuYW1lXG5cdFx0XHQvLyBkZWNsYXJlZCBpbiBwcm9qZWN0IGZpbGVzIHN0YXlzIHVua25vd246IHRoZSBzZWxmLWNvbnRhaW5lZFxuXHRcdFx0Ly8gdHlwZXMudHMgY2FuIGNhcnJ5IG5laXRoZXIgdGhlIGJhcmUgbmFtZSBub3IgYW4gaW1wb3J0LlxuXHRcdFx0aWYgKCF0aGlzLmlzUHJvamVjdERlY2xhcmVkVHlwZU5hbWUodHlwZU5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHZlcmJhdGltUmVzdWx0ID0gYCR7dHlwZU5hbWV9PCR7dHlwZUFyZ3MubWFwKGEgPT4gdGhpcy5pbmZlclR5cGUoYSkpLmpvaW4oJywgJyl9PmA7XG5cdFx0XHRcdHJldHVybiB2ZXJiYXRpbVJlc3VsdDtcblx0XHRcdH1cblx0XHRcdC8vIEdlbmVyaWMgcmVmZXJlbmNlIHRvIGEgbm9uLWdsb2JhbCwgbm9uLWdyYXBoIFBST0pFQ1QtTE9DQUxcblx0XHRcdC8vIHR5cGUgY2Fubm90IGJlIGVtaXR0ZWQgYmFyZSBpbnRvIHRoZSBnZW5lcmF0ZWQgZmlsZVxuXHRcdFx0aWYgKHJlZk5vZGUpIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRQbGFpblR5cGVSZWZlcmVuY2VTaXRlKHR5cGVOYW1lLCByZWZOb2RlKTtcblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmFsbGJhY2tSZXN1bHQgPSB0aGlzLnVucmVzb2x2ZWRUeXBlUmVmZXJlbmNlRmFsbGJhY2sodHlwZU5hbWUsIHJlZk5vZGUpO1xuXHRcdHJldHVybiBmYWxsYmFja1Jlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgcXVhbGlmaWVkIHR5cGUgcmVmZXJlbmNlIChtb2RlbHMuSW5uZXIuQ3JhdGUpIHRocm91Z2ggdGhlXG5cdCAqIGN1cnJlbnQgZmlsZSdzIG5hbWVzcGFjZSBpbXBvcnRzLiBUaGUgY2hhaW4ncyBoZWFkIG11c3QgYmUgYSBuYW1lc3BhY2Vcblx0ICogaW1wb3J0OyBtaWRkbGUgc2VnbWVudHMgZGVzY2VuZCB0aHJvdWdoIG5hbWVzcGFjZSBkZWNsYXJhdGlvbnMsIG5hbWVkXG5cdCAqIHJlLWV4cG9ydHMgb2YgbmFtZXNwYWNlcywgYW5kIGBleHBvcnQgKiBhcyBucyBmcm9tICfigKYnYCBiYXJyZWxzIChlYWNoXG5cdCAqIHNlZ21lbnQgY29uc3VtZWQgZXhhY3RseSBvbmNlLCBzbyB0aGUgd2FsayBjYW5ub3QgY3ljbGUpOyB0aGUgZmluYWxcblx0ICogc2VnbWVudCByZXNvbHZlcyB0byBhIGRlY2xhcmF0aW9uIHdoaWNoIGlzIGV4cGFuZGVkIGlubGluZS4gV2hlbiB0aGVcblx0ICogcHJlY2lzZSB3YWxrIGZpbmRzIG5vdGhpbmcsIHRoZSBsZWdhY3kgcmlnaHRtb3N0LW5hbWUgbG9va3VwIGluIHRoZVxuXHQgKiBoZWFkIG1vZHVsZSBrZWVwcyBvbmUtbGV2ZWwgZm9ybXMgKG1vZGVscy5UeXBlKSB3b3JraW5nIOKAlCBuZXN0ZWRcblx0ICogZGVjbGFyYXRpb25zIGFyZSByZWNvcmRlZCBieSBwbGFpbiBuYW1lIHRoZXJlIHRvby4gUmV0dXJucyB1bmRlZmluZWRcblx0ICogd2hlbiB0aGUgaGVhZCBpcyBub3QgYSBuYW1lc3BhY2UgaW1wb3J0IG9yIG5vdGhpbmcgcmVzb2x2ZXMuXG5cdCAqL1xuXHRwcml2YXRlIGluZmVyUXVhbGlmaWVkVHlwZVJlZmVyZW5jZSAodHlwZVJlZjogdHMuVHlwZVJlZmVyZW5jZU5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHMuaXNRdWFsaWZpZWROYW1lKHR5cGVSZWYudHlwZU5hbWUpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIGZsYXR0ZW4gdGhlIHF1YWxpZmllZCBuYW1lIGNoYWluOiBtb2RlbHMuSW5uZXIuQ3JhdGUg4oaSIFsnbW9kZWxzJywgJ0lubmVyJywgJ0NyYXRlJ11cblx0XHRjb25zdCBzZWdtZW50czogc3RyaW5nW10gPSBbXTtcblx0XHRsZXQgY2hhaW46IHRzLkVudGl0eU5hbWUgPSB0eXBlUmVmLnR5cGVOYW1lO1xuXHRcdHdoaWxlICh0cy5pc1F1YWxpZmllZE5hbWUoY2hhaW4pKSB7XG5cdFx0XHRzZWdtZW50cy51bnNoaWZ0KGNoYWluLnJpZ2h0LnRleHQpO1xuXHRcdFx0Y2hhaW4gPSBjaGFpbi5sZWZ0O1xuXHRcdH1cblx0XHRzZWdtZW50cy51bnNoaWZ0KGNoYWluLnRleHQpO1xuXG5cdFx0Y29uc3QgbmFtZXNwYWNlSW1wb3J0ID0gdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChzZWdtZW50c1sgMCBdKTtcblx0XHRpZiAoIW5hbWVzcGFjZUltcG9ydCB8fCAhbmFtZXNwYWNlSW1wb3J0LmlzTmFtZXNwYWNlKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShuYW1lc3BhY2VJbXBvcnQuc3BlY2lmaWVyLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdGlmICghcmVzb2x1dGlvbiB8fCByZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gZGVzY2VuZCB0aGUgbWlkZGxlIHNlZ21lbnRzOiBhIG1vZHVsZSBjb250ZXh0IHJlc29sdmVzIHRoZSBzZWdtZW50XG5cdFx0Ly8gYXMgYSBuYW1lc3BhY2UgZGVjbGFyYXRpb24gLyBuYW1lc3BhY2UgcmUtZXhwb3J0OyBhIG5hbWVzcGFjZS1ibG9ja1xuXHRcdC8vIGNvbnRleHQgcmVzb2x2ZXMgaXQgYXMgYSBuZXN0ZWQgbmFtZXNwYWNlIGRlY2xhcmF0aW9uXG5cdFx0bGV0IHF1YWxpZmllcjogeyBtb2R1bGVQYXRoOiBzdHJpbmc7IGJsb2NrPzogdHMuTW9kdWxlQmxvY2sgfSB8IHVuZGVmaW5lZCA9IHtcblx0XHRcdG1vZHVsZVBhdGggOiByZXNvbHV0aW9uLnJlc29sdmVkUGF0aFxuXHRcdH07XG5cdFx0Zm9yIChsZXQgaSA9IDE7IGkgPCBzZWdtZW50cy5sZW5ndGggLSAxICYmIHF1YWxpZmllcjsgaSsrKSB7XG5cdFx0XHRjb25zdCBzZWdtZW50ID0gc2VnbWVudHNbIGkgXTtcblx0XHRcdGlmIChxdWFsaWZpZXIuYmxvY2spIHtcblx0XHRcdFx0Y29uc3QgbmVzdGVkID0gdGhpcy5maW5kTmFtZXNwYWNlSW5CbG9jayhxdWFsaWZpZXIuYmxvY2ssIHNlZ21lbnQpO1xuXHRcdFx0XHRpZiAobmVzdGVkPy5ib2R5ICYmIHRzLmlzTW9kdWxlQmxvY2sobmVzdGVkLmJvZHkpKSB7XG5cdFx0XHRcdFx0cXVhbGlmaWVyID0geyBtb2R1bGVQYXRoIDogcXVhbGlmaWVyLm1vZHVsZVBhdGgsIGJsb2NrIDogbmVzdGVkLmJvZHkgfTtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRxdWFsaWZpZXIgPSB1bmRlZmluZWQ7XG5cdFx0XHRcdGJyZWFrO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbmFtZXNwYWNlRGVjbDogdHMuTW9kdWxlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQgPVxuXHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlcy5nZXQocXVhbGlmaWVyLm1vZHVsZVBhdGgpPy5nZXQoc2VnbWVudCk7XG5cdFx0XHRpZiAobmFtZXNwYWNlRGVjbD8uYm9keSAmJiB0cy5pc01vZHVsZUJsb2NrKG5hbWVzcGFjZURlY2wuYm9keSkpIHtcblx0XHRcdFx0cXVhbGlmaWVyID0geyBtb2R1bGVQYXRoIDogcXVhbGlmaWVyLm1vZHVsZVBhdGgsIGJsb2NrIDogbmFtZXNwYWNlRGVjbC5ib2R5IH07XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgc3RhclNwZWNpZmllciA9IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VTdGFycy5nZXQocXVhbGlmaWVyLm1vZHVsZVBhdGgpPy5nZXQoc2VnbWVudCk7XG5cdFx0XHRpZiAoc3RhclNwZWNpZmllcikge1xuXHRcdFx0XHRjb25zdCBuZXh0UmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKHN0YXJTcGVjaWZpZXIsIHF1YWxpZmllci5tb2R1bGVQYXRoKTtcblx0XHRcdFx0aWYgKG5leHRSZXNvbHV0aW9uICYmICFuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdFx0cXVhbGlmaWVyID0geyBtb2R1bGVQYXRoIDogbmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoIH07XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGNvbnN0IHJlRXhwb3J0U3BlY2lmaWVyID0gdGhpcy5yZWZlcmVuY2VkVHlwZVJlRXhwb3J0cy5nZXQocXVhbGlmaWVyLm1vZHVsZVBhdGgpPy5nZXQoc2VnbWVudCk7XG5cdFx0XHRpZiAocmVFeHBvcnRTcGVjaWZpZXIpIHtcblx0XHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShyZUV4cG9ydFNwZWNpZmllciwgcXVhbGlmaWVyLm1vZHVsZVBhdGgpO1xuXHRcdFx0XHRjb25zdCByZUV4cG9ydGVkOiB0cy5Nb2R1bGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCA9XG5cdFx0XHRcdFx0bmV4dFJlc29sdXRpb24gJiYgIW5leHRSZXNvbHV0aW9uLmlzRXh0ZXJuYWxcblx0XHRcdFx0XHRcdD8gdGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMuZ2V0KG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCk/LmdldChzZWdtZW50KVxuXHRcdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cdFx0XHRcdGlmIChyZUV4cG9ydGVkPy5ib2R5ICYmIHRzLmlzTW9kdWxlQmxvY2socmVFeHBvcnRlZC5ib2R5KSkge1xuXHRcdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IG5leHRSZXNvbHV0aW9uIS5yZXNvbHZlZFBhdGgsIGJsb2NrIDogcmVFeHBvcnRlZC5ib2R5IH07XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHF1YWxpZmllciA9IHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBmaW5hbE5hbWUgPSBzZWdtZW50c1sgc2VnbWVudHMubGVuZ3RoIC0gMSBdO1xuXHRcdGxldCBkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkO1xuXHRcdGlmIChxdWFsaWZpZXI/LmJsb2NrKSB7XG5cdFx0XHRkZWNsID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbkJsb2NrKHF1YWxpZmllci5ibG9jaywgcXVhbGlmaWVyLm1vZHVsZVBhdGgsIGZpbmFsTmFtZSk7XG5cdFx0fSBlbHNlIGlmIChxdWFsaWZpZXIpIHtcblx0XHRcdGRlY2wgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKHF1YWxpZmllci5tb2R1bGVQYXRoLCBmaW5hbE5hbWUsIDApO1xuXHRcdH1cblx0XHQvLyBsZWdhY3kgZmFsbGJhY2s6IHJpZ2h0bW9zdCBuYW1lIGFueXdoZXJlIGluIHRoZSBoZWFkIG1vZHVsZVxuXHRcdC8vIChuYW1lc3BhY2UtbmVzdGVkIGRlY2xhcmF0aW9ucyBhcmUgYWxzbyByZWNvcmRlZCBieSBwbGFpbiBuYW1lKVxuXHRcdGlmICghZGVjbCkge1xuXHRcdFx0ZGVjbCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUocmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIGZpbmFsTmFtZSwgMCk7XG5cdFx0fVxuXHRcdGlmICghZGVjbCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMuZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihkZWNsKTtcblx0XHRyZXR1cm4gZXhwYW5kZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmluZCBhIG5hbWVzcGFjZSBkZWNsYXJhdGlvbiBieSBuYW1lIGRpcmVjdGx5IGluc2lkZSBhIG1vZHVsZSBibG9jay5cblx0ICovXG5cdHByaXZhdGUgZmluZE5hbWVzcGFjZUluQmxvY2sgKGJsb2NrOiB0cy5Nb2R1bGVCbG9jaywgbmFtZTogc3RyaW5nKTogdHMuTW9kdWxlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIGJsb2NrLnN0YXRlbWVudHMpIHtcblx0XHRcdGlmICh0cy5pc01vZHVsZURlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiYgdHMuaXNJZGVudGlmaWVyKHN0YXRlbWVudC5uYW1lKSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdCA9IHN0YXRlbWVudDtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGaW5kIGEgbmFtZWQgdHlwZSBkZWNsYXJhdGlvbiAoYWxpYXMsIGNsYXNzLCBpbnRlcmZhY2UpIGRpcmVjdGx5IGluc2lkZVxuXHQgKiBhIG5hbWVzcGFjZSBibG9jayDigJQgdGhlIGZpbmFsIHNlZ21lbnQgb2YgYSBkZXNjZW5kZWQgcXVhbGlmaWVkIGNoYWluLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kUmVmZXJlbmNlZFR5cGVJbkJsb2NrIChcblx0XHRibG9jazogdHMuTW9kdWxlQmxvY2ssXG5cdFx0ZmlsZVBhdGg6IHN0cmluZyxcblx0XHRuYW1lOiBzdHJpbmdcblx0KTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2YgYmxvY2suc3RhdGVtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzVHlwZUFsaWFzRGVjbGFyYXRpb24oc3RhdGVtZW50KSAmJiB0cy5pc0lkZW50aWZpZXIoc3RhdGVtZW50Lm5hbWUpICYmXG5cdFx0XHRcdHN0YXRlbWVudC5uYW1lLnRleHQgPT09IG5hbWUpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0OiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uID0geyBraW5kIDogJ2FsaWFzJywgbm9kZSA6IHN0YXRlbWVudCwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiYgc3RhdGVtZW50Lm5hbWUgJiYgc3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZSkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQ6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gPSB7IGtpbmQgOiAnY2xhc3MnLCBub2RlIDogc3RhdGVtZW50LCBmaWxlIDogZmlsZVBhdGggfTtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc0ludGVyZmFjZURlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiYgdHMuaXNJZGVudGlmaWVyKHN0YXRlbWVudC5uYW1lKSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiA9IHsga2luZCA6ICdpbnRlcmZhY2UnLCBub2RlIDogc3RhdGVtZW50LCBmaWxlIDogZmlsZVBhdGggfTtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGYWxsYmFjayBmb3IgYSB0eXBlLXJlZmVyZW5jZSBuYW1lIHRoYXQgcmVzb2x2ZXMgdG8gbm8gZGVjbGFyYXRpb24gYW5kXG5cdCAqIG5vIGdyYXBoIHR5cGU6IGtub3duIGdsb2JhbHMga2VlcCB0aGVpciBiYXJlIG5hbWUgKHRoZXkgcmVzb2x2ZSB3aXRob3V0XG5cdCAqIGFuIGltcG9ydCk7IGV2ZXJ5dGhpbmcgZWxzZSBiZWNvbWVzIGB1bmtub3duYCBzbyBnZW5lcmF0ZWQgdHlwZXMudHNcblx0ICogbmV2ZXIgY2FycmllcyBhbiB1bnJlc29sdmFibGUgYmFyZSBuYW1lIChSRUFETUUncyBkb2N1bWVudGVkIGJlaGF2aW9yKVxuXHQgKiBhbmQgdGhlIHNpdGUgaXMgcmVjb3JkZWQgZm9yIHRoZSBwbGFpbi1UUyBhbWJpZ3VpdHkgdmFsaWRhdGlvbi5cblx0ICovXG5cdHByaXZhdGUgdW5yZXNvbHZlZFR5cGVSZWZlcmVuY2VGYWxsYmFjayAodHlwZU5hbWU6IHN0cmluZywgcmVmTm9kZT86IHRzLk5vZGUpOiBzdHJpbmcge1xuXHRcdGlmIChLTk9XTl9HTE9CQUxfVFlQRVMuaGFzKHR5cGVOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHR5cGVOYW1lO1xuXHRcdH1cblx0XHRpZiAocmVmTm9kZSkge1xuXHRcdFx0dGhpcy5yZWNvcmRQbGFpblR5cGVSZWZlcmVuY2VTaXRlKHR5cGVOYW1lLCByZWZOb2RlKTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gJ3Vua25vd24nO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIG9uZSBkZWZpbmUoKS9sYXp5KCkvQGRlY29yYXRlKCkgc2l0ZSB1bmRlciBpdHMgcnVudGltZVxuXHQgKiBuYW1lc3BhY2Uga2V5LiBUd28gc2l0ZXMgaW4gb25lIG5hbWVzcGFjZSBhcmUgYSBzYW1lLW5hbWVzcGFjZVxuXHQgKiBkdXBsaWNhdGUgKHRoZSBydW50aW1lIHRocm93cyBBTFJFQURZX0RFQ0xBUkVEKTsgZXZlcnkgc2l0ZSBpcyBrZXB0XG5cdCAqIHNvIHRoZSBmYWlsdXJlIGNhbiByZXBvcnQgYWxsIGxvY2F0aW9ucy5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkRGVmaW5lU2l0ZSAobmFtZXNwYWNlS2V5OiBzdHJpbmcsIGxvY2F0aW9uOiBzdHJpbmcpOiB2b2lkIHtcblx0XHRsZXQgc2l0ZXMgPSB0aGlzLmRlZmluZVNpdGVzLmdldChuYW1lc3BhY2VLZXkpO1xuXHRcdGlmICghc2l0ZXMpIHtcblx0XHRcdHNpdGVzID0gW107XG5cdFx0XHR0aGlzLmRlZmluZVNpdGVzLnNldChuYW1lc3BhY2VLZXksIHNpdGVzKTtcblx0XHR9XG5cdFx0aWYgKCFzaXRlcy5pbmNsdWRlcyhsb2NhdGlvbikpIHtcblx0XHRcdHNpdGVzLnB1c2gobG9jYXRpb24pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBGYXRhbCByZXNvbHV0aW9uIGZhaWx1cmVzIChoYXJkLWZhaWwgbGF3KTogc2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlXG5cdCAqIG1uZW1vbmljYSBkZWZpbml0aW9ucyBwbHVzIGFtYmlndW91cy91bnJlc29sdmVkIG1uZW1vbmljYS1ncmFwaFxuXHQgKiByZWZlcmVuY2VzLiBUaGUgQ0xJIHByaW50cyBldmVyeSBsb2NhdGlvbiBhbmQgd3JpdGVzIG5vIG91dHB1dC5cblx0ICovXG5cdGdldFJlc29sdXRpb25FcnJvcnMgKCk6IFJlc29sdXRpb25FcnJvcltdIHtcblx0XHR0aGlzLnZhbGlkYXRlTG9va3VwUmVmZXJlbmNlcygpO1xuXHRcdHRoaXMudmFsaWRhdGVQbGFpblR5cGVSZWZlcmVuY2VzKCk7XG5cdFx0Y29uc3QgZXJyb3JzOiBSZXNvbHV0aW9uRXJyb3JbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgWyBuYW1lc3BhY2VLZXksIHNpdGVzIF0gb2YgdGhpcy5kZWZpbmVTaXRlcykge1xuXHRcdFx0aWYgKHNpdGVzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBkaXNwbGF5TmFtZSA9IG5hbWVzcGFjZUtleS5yZXBsYWNlKC9eW146XSs6Oi8sICcnKTtcblx0XHRcdGNvbnN0IG1lc3NhZ2UgPSBgRHVwbGljYXRlIGRlZmluaXRpb24gb2YgJyR7ZGlzcGxheU5hbWV9JyBpbiBvbmUgbmFtZXNwYWNlIOKAlCBgICtcblx0XHRcdFx0J3RoZSBtbmVtb25pY2EgcnVudGltZSB3b3VsZCB0aHJvdyBBTFJFQURZX0RFQ0xBUkVEJztcblx0XHRcdGVycm9ycy5wdXNoKHsgbWVzc2FnZSwgbG9jYXRpb25zIDogWyAuLi5zaXRlcyBdIH0pO1xuXHRcdH1cblx0XHRmb3IgKGNvbnN0IGVycm9yIG9mIHRoaXMuZ3JhcGhSZWZlcmVuY2VFcnJvcnMpIHtcblx0XHRcdGVycm9ycy5wdXNoKGVycm9yKTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gZXJyb3JzO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHJlZmVyZW5jZSB0byBhIG1uZW1vbmljYSBncmFwaCB0eXBlIG5hbWUsIGltcG9ydC1hd2FyZSBhbmRcblx0ICogcGF0aC1hd2FyZSAodGhlIGhhcmQtZmFpbCBpZGVudGl0eSBsYXcsIG1pcnJvcmluZyB0aGUgcnVudGltZSk6XG5cdCAqICAgMS4gdmFsdWUgc2NvcGUg4oCUIGEgdHJhY2tlZCB0b3AtbGV2ZWwgYmluZGluZyBpbiB0aGUgcmVmZXJlbmNpbmcgZmlsZVxuXHQgKiAgICAgIChgY29uc3QgQWRkcmVzcyA9IFVzZXIuZGVmaW5lKCdBZGRyZXNzJywg4oCmKWApLFxuXHQgKiAgIDIuIGltcG9ydCBzY29wZSDigJQgYSBiaW5kaW5nIGV4cG9ydGVkIGZyb20gYSBtb2R1bGUgdGhpcyBmaWxlIGltcG9ydHNcblx0ICogICAgICAoYmFycmVscyBjaGFzZWQpLFxuXHQgKiAgIDMuIG5lYXJlc3QtY2hhaW4g4oCUIHRoZSBhbmNob3IgdHlwZSdzIG93biBzdWJ0eXBlcyBmaXJzdCwgdGhlbiBlYWNoXG5cdCAqICAgICAgYW5jZXN0b3IgbGV2ZWwgKHJlbGF0aXZlLWZpcnN0KSxcblx0ICogICA0LiByb290IOKAlCByb290cyBvZiB0aGUgYW5jaG9yJ3MgY29sbGVjdGlvbixcblx0ICogICA1LiBwcm9ncmFtLXdpZGUg4oCUIG9ubHkgd2hlbiBleGFjdGx5IG9uZSB0eXBlIGNhcnJpZXMgdGhlIG5hbWUuXG5cdCAqIEFtYmlndWl0eSAoc2V2ZXJhbCBjYW5kaWRhdGVzIGFuZCBub3RoaW5nIGRpc2FtYmlndWF0ZXMpIGFuZCBhYnNlbmNlXG5cdCAqIGFyZSBib3RoIHJldHVybmVkIGFzIHN1Y2gg4oCUIHRoZSBjYWxsZXIgcmVjb3JkcyBhIGhhcmQgZmFpbHVyZTsgYSBiYXJlXG5cdCAqIGZpcnN0LW1hdGNoIG5hbWUgaXMgbmV2ZXIgZW1pdHRlZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUdyYXBoVHlwZU5hbWUgKG5hbWU6IHN0cmluZyk6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCB7XG5cdFx0Ly8gMS4gdmFsdWUgc2NvcGUgaW4gdGhlIHJlZmVyZW5jaW5nIGZpbGUgaXRzZWxmXG5cdFx0Y29uc3QgbG9jYWxCaW5kaW5nID0gdGhpcy5maWxlR3JhcGhCaW5kaW5ncy5nZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChsb2NhbEJpbmRpbmcpIHtcblx0XHRcdGNvbnN0IG5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGxvY2FsQmluZGluZyk7XG5cdFx0XHRpZiAobm9kZSkge1xuXHRcdFx0XHRjb25zdCB2YWx1ZVJlc3VsdDogR3JhcGhUeXBlUmVmZXJlbmNlUmVzdWx0ID0geyBzdGF0dXMgOiAndW5pcXVlJywgbm9kZSB9O1xuXHRcdFx0XHRyZXR1cm4gdmFsdWVSZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gMi4gaW1wb3J0IHNjb3BlIOKAlCB0aGUgaW1wb3J0ZWQgbW9kdWxlJ3MgZXhwb3J0ZWQgYmluZGluZ1xuXHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAoaW1wb3J0ZWQgJiYgIWltcG9ydGVkLmlzTmFtZXNwYWNlKSB7XG5cdFx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoaW1wb3J0ZWQuc3BlY2lmaWVyLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0aWYgKHJlc29sdXRpb24gJiYgIXJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRjb25zdCBmdWxsUGF0aCA9IHRoaXMuZmluZEdyYXBoQmluZGluZ0luTW9kdWxlKHJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBpbXBvcnRlZC5vcmlnaW5hbE5hbWUsIDApO1xuXHRcdFx0XHRpZiAoZnVsbFBhdGgpIHtcblx0XHRcdFx0XHRjb25zdCBub2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShmdWxsUGF0aCk7XG5cdFx0XHRcdFx0aWYgKG5vZGUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGltcG9ydFJlc3VsdDogR3JhcGhUeXBlUmVmZXJlbmNlUmVzdWx0ID0geyBzdGF0dXMgOiAndW5pcXVlJywgbm9kZSB9O1xuXHRcdFx0XHRcdFx0cmV0dXJuIGltcG9ydFJlc3VsdDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyAzLTUuIGNoYWluIC8gcm9vdCAvIHByb2dyYW0td2lkZSB0aWVyc1xuXHRcdGNvbnN0IHJlc3VsdCA9IHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UodGhpcy5ncmFwaCwgbmFtZSwgdGhpcy5jdXJyZW50R3JhcGhBbmNob3IpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRmluZCBhIGdyYXBoIGNvbnN0cnVjdG9yIGJpbmRpbmcgZXhwb3J0ZWQgYnkgYSByZXNvbHZlZCBtb2R1bGUsXG5cdCAqIGNoYXNpbmcgcmUtZXhwb3J0IGJhcnJlbHMgd2l0aCBhIGJvdW5kZWQgZGVwdGguXG5cdCAqL1xuXHRwcml2YXRlIGZpbmRHcmFwaEJpbmRpbmdJbk1vZHVsZSAobW9kdWxlUGF0aDogc3RyaW5nLCBuYW1lOiBzdHJpbmcsIGRlcHRoOiBudW1iZXIpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmIChkZXB0aCA+IE1BWF9SRUVYUE9SVF9DSEFTRV9ERVBUSCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBkaXJlY3QgPSB0aGlzLmZpbGVHcmFwaEJpbmRpbmdzLmdldChtb2R1bGVQYXRoKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChkaXJlY3QpIHtcblx0XHRcdHJldHVybiBkaXJlY3Q7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVFeHBvcnRzID0gdGhpcy5yZWZlcmVuY2VkVHlwZVJlRXhwb3J0cy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0Y29uc3QgcmVFeHBvcnRTcGVjaWZpZXIgPSByZUV4cG9ydHM/LmdldChuYW1lKTtcblx0XHRpZiAocmVFeHBvcnRTcGVjaWZpZXIpIHtcblx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUocmVFeHBvcnRTcGVjaWZpZXIsIG1vZHVsZVBhdGgpO1xuXHRcdFx0aWYgKG5leHRSZXNvbHV0aW9uICYmICFuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kR3JhcGhCaW5kaW5nSW5Nb2R1bGUobmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBuYW1lLCBkZXB0aCArIDEpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCBzdGFycyA9IHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0aWYgKHN0YXJzKSB7XG5cdFx0XHRmb3IgKGNvbnN0IHN0YXJTcGVjaWZpZXIgb2Ygc3RhcnMpIHtcblx0XHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShzdGFyU3BlY2lmaWVyLCBtb2R1bGVQYXRoKTtcblx0XHRcdFx0aWYgKCFuZXh0UmVzb2x1dGlvbiB8fCBuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRHcmFwaEJpbmRpbmdJbk1vZHVsZShuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIG5hbWUsIGRlcHRoICsgMSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogVmFsaWRhdGUgbGl0ZXJhbCBsb29rdXAoKSBwYXRocyByZWNvcmRlZCBkdXJpbmcgdGhlIHVzYWdlcyBwYXNzXG5cdCAqIGFnYWluc3QgdGhlIGNvbXBsZXRlIGdyYXBoLiBBIGxvb2t1cCBwYXRoIG1hdGNoaW5nIG5vIHR5cGUgaXMgd2hhdCB0aGVcblx0ICogcnVudGltZSBhbnN3ZXJzIHdpdGggYHVuZGVmaW5lZGAg4oCUIHRoZSBUeXBlRXJyb3IgYXJyaXZlcyBvbmUgbGluZVxuXHQgKiBsYXRlciBhdCB0aGUgYG5ld2Ag4oCUIHNvIGl0IGpvaW5zIHRoZSBoYXJkLWZhaWwgbGF3LiBUaGUgcmVsYXRpdmUtZmlyc3Rcblx0ICogc3RlcCBhbHJlYWR5IHJhbiBpbnNpZGUgcmVzb2x2ZUxvb2t1cFBhdGg7IHdoYXRldmVyIHdhcyByZWNvcmRlZCBpc1xuXHQgKiB0aGUgcm9vdC1yZXNvbHV0aW9uIHJlc3VsdCwgc28gYSBwbGFpbiBmaW5kVHlwZSBjaGVjayBpcyB0aGUgZXhhY3Rcblx0ICogcnVudGltZSBsYXcuIFNhbWUtbmFtZWQgdHlwZXMgZWxzZXdoZXJlIGluIHRoZSBncmFwaCBhcmUgbGlzdGVkIGFzXG5cdCAqIGRpZC15b3UtbWVhbiBjYW5kaWRhdGVzLiBSdW5zIG9uY2UgcGVyIHVzYWdlcyBwYXNzIChyZS1hcm1lZCBieVxuXHQgKiByZXNldFVzYWdlcyk7IG5vbi1saXRlcmFsIGxvb2t1cCBhcmd1bWVudHMgYXJlIG5ldmVyIHJlY29yZGVkIGFuZFxuXHQgKiBzdGF5IGJlc3QtZWZmb3J0LlxuXHQgKi9cblx0cHJpdmF0ZSB2YWxpZGF0ZUxvb2t1cFJlZmVyZW5jZXMgKCk6IHZvaWQge1xuXHRcdGlmICh0aGlzLmxvb2t1cFJlZmVyZW5jZXNWYWxpZGF0ZWQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0dGhpcy5sb29rdXBSZWZlcmVuY2VzVmFsaWRhdGVkID0gdHJ1ZTtcblx0XHQvLyBncm91cCBzaXRlcyBieSBwYXRoOiBldmVyeSBmYWlsaW5nIHNpdGUgb2YgdGhlIHNhbWUgcGF0aCBpcyBsaXN0ZWRcblx0XHRjb25zdCBzaXRlc0J5UGF0aCA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmdbXT4oKTtcblx0XHRmb3IgKGNvbnN0IHJlZiBvZiB0aGlzLmxvb2t1cFJlZmVyZW5jZXMpIHtcblx0XHRcdGNvbnN0IHNpdGVzID0gc2l0ZXNCeVBhdGguZ2V0KHJlZi5wYXRoKSA/PyBbXTtcblx0XHRcdHNpdGVzLnB1c2gocmVmLmxvY2F0aW9uKTtcblx0XHRcdHNpdGVzQnlQYXRoLnNldChyZWYucGF0aCwgc2l0ZXMpO1xuXHRcdH1cblx0XHRmb3IgKGNvbnN0IFsgdHlwZVBhdGgsIHNpdGVzIF0gb2Ygc2l0ZXNCeVBhdGgpIHtcblx0XHRcdGlmICh0aGlzLmdyYXBoLmZpbmRUeXBlKHR5cGVQYXRoKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdC8vIGRpZC15b3UtbWVhbjogdHlwZXMgY2FycnlpbmcgdGhlIHNhbWUgbmFtZSBhbnl3aGVyZSBpbiB0aGVcblx0XHRcdC8vIGdyYXBoIChuZXZlciBhIGZpcnN0LW1hdGNoIHBpY2sg4oCUIHRoZSBmdWxsIGxpc3Qgb25seSlcblx0XHRcdGNvbnN0IHVucHJlZml4ZWQgPSB0eXBlUGF0aC5yZXBsYWNlKC9eW146XSs6Oi8sICcnKTtcblx0XHRcdGNvbnN0IGxhc3RTZWdtZW50ID0gdW5wcmVmaXhlZC5zcGxpdCgnLicpLnBvcCgpID8/IHVucHJlZml4ZWQ7XG5cdFx0XHRjb25zdCBjYW5kaWRhdGVzID0gdGhpcy5ncmFwaC5nZXRBbGxUeXBlcygpLmZpbHRlcih0ID0+IHQubmFtZSA9PT0gbGFzdFNlZ21lbnQpO1xuXHRcdFx0aWYgKGNhbmRpZGF0ZXMubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRcdGNvbnN0IG5vbmVFcnJvcjogUmVzb2x1dGlvbkVycm9yID0ge1xuXHRcdFx0XHRcdG1lc3NhZ2UgOiBgVW5yZXNvbHZlZCBsb29rdXAgb2YgbW5lbW9uaWNhIHR5cGUgJyR7dHlwZVBhdGh9Jzogbm8gdHlwZSBhdCB0aGF0IHBhdGgg4oCUIGAgK1xuXHRcdFx0XHRcdFx0J3RoZSBydW50aW1lIHdvdWxkIHJldHVybiB1bmRlZmluZWQnLFxuXHRcdFx0XHRcdGxvY2F0aW9ucyA6IHNpdGVzLFxuXHRcdFx0XHR9O1xuXHRcdFx0XHR0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzLnB1c2gobm9uZUVycm9yKTtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBjYW5kaWRhdGVMb2NhdGlvbnMgPSBjYW5kaWRhdGVzLm1hcChuID0+IGAke24uc291cmNlRmlsZX06JHtuLmxpbmV9OiR7bi5jb2x1bW59YCk7XG5cdFx0XHRjb25zdCBjYW5kaWRhdGVQYXRocyA9IGNhbmRpZGF0ZXMubWFwKG4gPT4gbi5mdWxsUGF0aCkuam9pbignLCAnKTtcblx0XHRcdGNvbnN0IGFtYmlndW91c0Vycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7XG5cdFx0XHRcdG1lc3NhZ2UgOiBgVW5yZXNvbHZlZCBsb29rdXAgb2YgbW5lbW9uaWNhIHR5cGUgJyR7dHlwZVBhdGh9JzogdGhlIHJ1bnRpbWUgd291bGQgcmV0dXJuIGAgK1xuXHRcdFx0XHRcdGB1bmRlZmluZWQg4oCUICR7Y2FuZGlkYXRlcy5sZW5ndGh9IGdyYXBoIHR5cGUocykgY2FycnkgdGhlIG5hbWUgYCArXG5cdFx0XHRcdFx0YG9mZi1yb290ICgke2NhbmRpZGF0ZVBhdGhzfSk7IHVzZSB0aGUgZnVsbCBkb3R0ZWQgcGF0aGAsXG5cdFx0XHRcdGxvY2F0aW9ucyA6IFsgLi4uc2l0ZXMsIC4uLmNhbmRpZGF0ZUxvY2F0aW9ucyBdLFxuXHRcdFx0fTtcblx0XHRcdHRoaXMuZ3JhcGhSZWZlcmVuY2VFcnJvcnMucHVzaChhbWJpZ3VvdXNFcnJvcik7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhIHBsYWluLVRTIHR5cGUgcmVmZXJlbmNlIHNpdGUgdGhhdCByZXNvbHZlZCB0byBub3RoaW5nIGFuZFxuXHQgKiBmZWxsIGJhY2sgdG8gYHVua25vd25gLCBmb3IgdGhlIGxhemlseS1ydW4gYW1iaWd1aXR5IHZhbGlkYXRpb24uXG5cdCAqIERlZHVwZWQgYnkgKG5hbWUsIGxvY2F0aW9uKTogaW5mZXJUeXBlIGNhbiB2aXNpdCB0aGUgc2FtZSBub2RlIG1vcmVcblx0ICogdGhhbiBvbmNlIHBlciBwYXNzIChjb25zdHJ1Y3RvciBwYXJhbXMgKyBwcm9wZXJ0eSBpbmZlcmVuY2UpLlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmRQbGFpblR5cGVSZWZlcmVuY2VTaXRlIChuYW1lOiBzdHJpbmcsIHJlZk5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRjb25zdCBsb2NhdGlvbiA9IHRoaXMubm9kZUxvY2F0aW9uKHJlZk5vZGUpO1xuXHRcdGNvbnN0IGZpbGUgPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0Y29uc3QgYWxyZWFkeSA9IHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlcy5zb21lKChyZWYpID0+IHJlZi5uYW1lID09PSBuYW1lICYmIHJlZi5sb2NhdGlvbiA9PT0gbG9jYXRpb24pO1xuXHRcdGlmIChhbHJlYWR5KSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlcy5wdXNoKHsgbmFtZSwgbG9jYXRpb24sIGZpbGUgfSk7XG5cdH1cblxuXHQvKipcblx0ICogUHJvamVjdC1zb3VyY2UgZGVjbGFyYXRpb24gZmlsZXMgY2FycnlpbmcgYG5hbWVgIOKAlCBvbmUgZW50cnkgcGVyXG5cdCAqIGZpbGUsIHNvIHNhbWUtZmlsZSBpbnRlcmZhY2UgbWVyZ2luZyBjb3VudHMgb25jZSAobm90IGFtYmlndW91cykuXG5cdCAqIEV4dGVybmFsL2FtYmllbnQgZGVjbGFyYXRpb25zICguZC50cywgYW55dGhpbmcgdW5kZXIgbm9kZV9tb2R1bGVzKVxuXHQgKiBuZXZlciBjb3VudDogYSB1c2VyLWxvY2FsIGRlY2xhcmF0aW9uIGFsd2F5cyB3aW5zIG92ZXIgYSBwYWNrYWdlLVxuXHQgKiBkZWNsYXJlZCBzYW1lLW5hbWVkIHR5cGUsIHNvIGFuIGV4dGVybmFsIGNvbGxpc2lvbiBzdGF5cyBzb2Z0LlxuXHQgKi9cblx0cHJpdmF0ZSBwbGFpblR5cGVEZWNsYXJhdGlvbkZpbGVzIChuYW1lOiBzdHJpbmcpOiBzdHJpbmdbXSB7XG5cdFx0Y29uc3QgZmlsZXM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBbIGZpbGUsIGRlY2xzIF0gb2YgdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzKSB7XG5cdFx0XHRpZiAoIXRoaXMuaXNFeHRlcm5hbERlY2xGaWxlKGZpbGUpICYmIGRlY2xzLmhhcyhuYW1lKSkge1xuXHRcdFx0XHRmaWxlcy5wdXNoKGZpbGUpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gZmlsZXM7XG5cdH1cblxuXHQvKipcblx0ICogVmFsaWRhdGUgcGxhaW4tVFMgdHlwZSByZWZlcmVuY2Ugc2l0ZXMgcmVjb3JkZWQgZHVyaW5nIHRoZSB1c2FnZXNcblx0ICogcGFzcyBhZ2FpbnN0IHRoZSBjb21wbGV0ZSBkZWNsYXJhdGlvbiBtYXAuIEEgbmFtZSBkZWNsYXJlZCBpblxuXHQgKiBzZXZlcmFsIHByb2plY3Qtc291cmNlIGZpbGVzIOKAlCB3aXRoIG5vIGltcG9ydCBpbiB0aGUgcmVmZXJlbmNpbmdcblx0ICogZmlsZSB0byBhbmNob3IgaXQg4oCUIGlzIGFtYmlndW91czogc2lsZW50bHkgZW1pdHRpbmcgYHVua25vd25gIHdvdWxkXG5cdCAqIGhpZGUgYSByZWFsIHR5cGUgdGhlIGF1dGhvciBtZWFudCwgc28gaXQgam9pbnMgdGhlIGhhcmQtZmFpbCBsYXdcblx0ICogKHRoZSBwbGFpbi1UUyB0aWVyIG9mIHRoZSBzYW1lIGlkZW50aXR5IGxhdyBhcyBncmFwaCByZWZlcmVuY2VzKS5cblx0ICogQWJzZW5jZSAoZ2hvc3QgbmFtZXMpIGFuZCBleHRlcm5hbCBjb2xsaXNpb25zIHN0YXkgc29mdCBgdW5rbm93bmAuXG5cdCAqIFJ1bnMgb25jZSBwZXIgdXNhZ2VzIHBhc3MgKHJlLWFybWVkIGJ5IHJlc2V0VXNhZ2VzKSwgbWlycm9yaW5nXG5cdCAqIHZhbGlkYXRlTG9va3VwUmVmZXJlbmNlczogcmVjb3JkaW5nIGhhcHBlbnMgb24gZXZlcnkgcGFzcywgYnV0IG9ubHlcblx0ICogdGhlIHVzYWdlcyBwYXNzIHNlZXMgdGhlIGNvbXBsZXRlIGRlY2xhcmF0aW9uIG1hcC5cblx0ICovXG5cdHByaXZhdGUgdmFsaWRhdGVQbGFpblR5cGVSZWZlcmVuY2VzICgpOiB2b2lkIHtcblx0XHRpZiAodGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzVmFsaWRhdGVkKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IHRydWU7XG5cdFx0Y29uc3Qgc2l0ZXNCeU5hbWUgPSBuZXcgTWFwPHN0cmluZywgeyBuYW1lOiBzdHJpbmc7IGxvY2F0aW9uOiBzdHJpbmc7IGZpbGU6IHN0cmluZyB9W10+KCk7XG5cdFx0Zm9yIChjb25zdCByZWYgb2YgdGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzKSB7XG5cdFx0XHRjb25zdCBzaXRlcyA9IHNpdGVzQnlOYW1lLmdldChyZWYubmFtZSkgPz8gW107XG5cdFx0XHRzaXRlcy5wdXNoKHJlZik7XG5cdFx0XHRzaXRlc0J5TmFtZS5zZXQocmVmLm5hbWUsIHNpdGVzKTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBbIG5hbWUsIHNpdGVzIF0gb2Ygc2l0ZXNCeU5hbWUpIHtcblx0XHRcdC8vIGFuIGltcG9ydCBiaW5kaW5nIGluIHRoZSByZWZlcmVuY2luZyBmaWxlIGFuY2hvcnMgdGhlIG5hbWUg4oCUXG5cdFx0XHQvLyB0aGUgYXV0aG9yIGFscmVhZHkgZGlzYW1iaWd1YXRlZCAodGhlIGltcG9ydCBtYXkganVzdCBwb2ludFxuXHRcdFx0Ly8gYXQgYW4gdW5hbmFseXphYmxlIGV4dGVybmFsIG1vZHVsZSwgd2hpY2ggc3RheXMgc29mdClcblx0XHRcdGNvbnN0IHVuYW5jaG9yZWQgPSBzaXRlcy5maWx0ZXIoKHNpdGUpID0+ICF0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoc2l0ZS5maWxlKT8uaGFzKG5hbWUpKTtcblx0XHRcdGlmICh1bmFuY2hvcmVkLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGRlY2xGaWxlcyA9IHRoaXMucGxhaW5UeXBlRGVjbGFyYXRpb25GaWxlcyhuYW1lKTtcblx0XHRcdGlmIChkZWNsRmlsZXMubGVuZ3RoIDwgMikge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IG1lc3NhZ2UgPSBgQW1iaWd1b3VzIHJlZmVyZW5jZSB0byB0eXBlICcke25hbWV9JzogJHtkZWNsRmlsZXMubGVuZ3RofSBkZWNsYXJhdGlvbnMgYCArXG5cdFx0XHRcdCdzaGFyZSB0aGUgbmFtZSBhbmQgbm8gaW1wb3J0IGRpc2FtYmlndWF0ZXMg4oCUIGltcG9ydCB0aGUgb25lIHlvdSBtZWFuJztcblx0XHRcdGNvbnN0IGRlY2xMb2NhdGlvbnMgPSBkZWNsRmlsZXMubWFwKChmaWxlKSA9PiB0aGlzLnBsYWluRGVjbExvY2F0aW9uKGZpbGUsIG5hbWUpKTtcblx0XHRcdGNvbnN0IGVycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7XG5cdFx0XHRcdG1lc3NhZ2UsXG5cdFx0XHRcdGxvY2F0aW9ucyA6IFsgLi4udW5hbmNob3JlZC5tYXAoKHNpdGUpID0+IHNpdGUubG9jYXRpb24pLCAuLi5kZWNsTG9jYXRpb25zIF1cblx0XHRcdH07XG5cdFx0XHR0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzLnB1c2goZXJyb3IpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBgZmlsZTpsaW5lOmNvbHVtbmAgb2YgYSByZWNvcmRlZCBkZWNsYXJhdGlvbiwgZm9yIHRoZSBhbWJpZ3VpdHlcblx0ICogcmVwb3J0LiBOb2RlcyByZWNvcmRlZCBkdXJpbmcgdHJhdmVyc2FsIGtlZXAgdGhlaXIgcG9zaXRpb25zOyBhXG5cdCAqIHN5bnRoZXRpYy91bnBvc2l0aW9uZWQgbm9kZSBmYWxscyBiYWNrIHRvIHRoZSBmaWxlIGl0c2VsZi5cblx0ICovXG5cdHByaXZhdGUgcGxhaW5EZWNsTG9jYXRpb24gKGZpbGU6IHN0cmluZywgbmFtZTogc3RyaW5nKTogc3RyaW5nIHtcblx0XHRjb25zdCBkZWNsID0gdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLmdldChmaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGNvbnN0IG5vZGUgPSBkZWNsPy5ub2RlO1xuXHRcdGxldCBsb2NhdGlvbiA9IGAke2ZpbGV9OjE6MWA7XG5cdFx0aWYgKG5vZGUgJiYgbm9kZS5wb3MgPj0gMCkge1xuXHRcdFx0Y29uc3Qgc291cmNlRmlsZSA9IG5vZGUuZ2V0U291cmNlRmlsZSgpO1xuXHRcdFx0Y29uc3QgbGluZSA9IHNvdXJjZUZpbGUuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24obm9kZS5nZXRTdGFydCgpKS5saW5lICsgMTtcblx0XHRcdGNvbnN0IGNvbHVtbiA9IHNvdXJjZUZpbGUuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24obm9kZS5nZXRTdGFydCgpKS5jaGFyYWN0ZXIgKyAxO1xuXHRcdFx0bG9jYXRpb24gPSBgJHtmaWxlfToke2xpbmV9OiR7Y29sdW1ufWA7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGxvY2F0aW9uO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGEgaGFyZC1mYWlsIGdyYXBoIHJlZmVyZW5jZSBlcnJvciB3aXRoIHRoZSByZWZlcmVuY2Ugc2l0ZSBhbmRcblx0ICogZXZlcnkgY2FuZGlkYXRlIGxvY2F0aW9uLlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yIChcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0cmVmTm9kZTogdHMuTm9kZSB8IHN0cmluZyxcblx0XHRyZXN1bHQ6IEV4dHJhY3Q8R3JhcGhUeXBlUmVmZXJlbmNlUmVzdWx0LCB7IHN0YXR1czogJ2FtYmlndW91cycgfCAnbm9uZScgfT5cblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSB0eXBlb2YgcmVmTm9kZSA9PT0gJ3N0cmluZycgPyByZWZOb2RlIDogdGhpcy5ub2RlTG9jYXRpb24ocmVmTm9kZSk7XG5cdFx0aWYgKHJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHRjb25zdCBjYW5kaWRhdGVMb2NhdGlvbnMgPSByZXN1bHQuY2FuZGlkYXRlcy5tYXAobiA9PiBgJHtuLnNvdXJjZUZpbGV9OiR7bi5saW5lfToke24uY29sdW1ufWApO1xuXHRcdFx0Y29uc3QgYW1iaWd1b3VzTWVzc2FnZSA9IGBBbWJpZ3VvdXMgcmVmZXJlbmNlIHRvIG1uZW1vbmljYSB0eXBlICcke25hbWV9JzogYCArXG5cdFx0XHRcdGAke3Jlc3VsdC5jYW5kaWRhdGVzLmxlbmd0aH0gdHlwZXMgc2hhcmUgdGhlIG5hbWUgYW5kIG5laXRoZXIgdGhlIHBhcmVudCBjaGFpbiBgICtcblx0XHRcdFx0J25vciB0aGUgaW1wb3J0cyBkaXNhbWJpZ3VhdGUnO1xuXHRcdFx0Y29uc3QgYW1iaWd1b3VzRXJyb3I6IFJlc29sdXRpb25FcnJvciA9IHtcblx0XHRcdFx0bWVzc2FnZSAgIDogYW1iaWd1b3VzTWVzc2FnZSxcblx0XHRcdFx0bG9jYXRpb25zIDogWyBsb2NhdGlvbiwgLi4uY2FuZGlkYXRlTG9jYXRpb25zIF0sXG5cdFx0XHR9O1xuXHRcdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKGFtYmlndW91c0Vycm9yKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgdW5yZXNvbHZlZE1lc3NhZ2UgPSBgVW5yZXNvbHZlZCByZWZlcmVuY2UgdG8gbW5lbW9uaWNhIHR5cGUgJyR7bmFtZX0nOiBubyB0eXBlIG1hdGNoZXMgYCArXG5cdFx0XHQnYnkgdmFsdWUgc2NvcGUsIGltcG9ydHMsIHBhcmVudCBjaGFpbiwgb3Igcm9vdCBwYXRoJztcblx0XHRjb25zdCB1bnJlc29sdmVkRXJyb3I6IFJlc29sdXRpb25FcnJvciA9IHsgbWVzc2FnZSA6IHVucmVzb2x2ZWRNZXNzYWdlLCBsb2NhdGlvbnMgOiBbIGxvY2F0aW9uIF0gfTtcblx0XHR0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzLnB1c2godW5yZXNvbHZlZEVycm9yKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBMb2NhdGlvbiAoYGZpbGU6bGluZTpjb2x1bW5gKSBvZiBhbiBBU1Qgbm9kZSwgZGVyaXZlZCB3aXRob3V0IHBhcmVudFxuXHQgKiBwb2ludGVycyB3aGVuIG5lY2Vzc2FyeS5cblx0ICovXG5cdHByaXZhdGUgbm9kZUxvY2F0aW9uIChub2RlOiB0cy5Ob2RlKTogc3RyaW5nIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5vZGU7XG5cdFx0d2hpbGUgKGN1cnJlbnQgJiYgIXRzLmlzU291cmNlRmlsZShjdXJyZW50KSkge1xuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRpZiAoIWN1cnJlbnQpIHtcblx0XHRcdGNvbnN0IGZhbGxiYWNrID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdFx0cmV0dXJuIGZhbGxiYWNrO1xuXHRcdH1cblx0XHRjb25zdCBzdGFydCA9IG5vZGUuZ2V0U3RhcnQoY3VycmVudCk7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKGN1cnJlbnQsIHN0YXJ0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke2N1cnJlbnQuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdHJldHVybiBsb2NhdGlvbjtcblx0fVxuXG5cdC8qKlxuXHQgKiBUcmFjayBhbGlhc2VzIG9mIHRoZSBtbmVtb25pY2EgbW9kdWxlIG9iamVjdCwgZS5nLjpcblx0ICogICBjb25zdCBtID0gbW5lbW9uaWNhO1xuXHQgKiAgIGNvbnN0IEFwcCA9IG07XG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrTW9kdWxlT2JqZWN0QWxpYXNlcyAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpIHx8ICF0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgaW5pdGlhbGl6ZXIgfSA9IG5vZGU7XG5cdFx0aWYgKCFpbml0aWFsaXplcikge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoaW5pdGlhbGl6ZXIpICYmIHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhpbml0aWFsaXplci50ZXh0KSkge1xuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuYWRkKG5vZGUubmFtZS50ZXh0KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgY3VzdG9tIGNvbGxlY3Rpb24gdmFyaWFibGVzLCBlLmcuOlxuXHQgKiAgIGNvbnN0IE15Q29sbGVjdGlvbiA9IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpO1xuXHQgKiAgIGNvbnN0IE90aGVyID0gTXlDb2xsZWN0aW9uO1xuXHQgKlxuXHQgKiBBbHNvIGRldGVjdHMgT3B0aW9uIEIgdXNlci1wcm92aWRlZCByZWdpc3RyeSBpbnRlcmZhY2VzOlxuXHQgKiAgIGV4cG9ydCBpbnRlcmZhY2UgTXlDb2xsZWN0aW9uUmVnaXN0cnkge31cblx0ICogICBjb25zdCBNeUNvbGxlY3Rpb24gPSBjcmVhdGVUeXBlc0NvbGxlY3Rpb248TXlDb2xsZWN0aW9uUmVnaXN0cnk+KCk7XG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrQ29sbGVjdGlvbkFsaWFzZXMgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSB8fCAhdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGluaXRpYWxpemVyIH0gPSBub2RlO1xuXHRcdGlmICghaW5pdGlhbGl6ZXIpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBEaXJlY3QgY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgY2FsbFxuXHRcdGlmICh0aGlzLmlzQ3JlYXRlVHlwZXNDb2xsZWN0aW9uQ2FsbChpbml0aWFsaXplcikpIHtcblx0XHRcdC8vIFRoZSBDTEkgcmUtYW5hbHl6ZXMgZXZlcnkgZmlsZSBvbiB0aGUgdXNhZ2VzIHBhc3MgKHNlZSByZXNldFVzYWdlcyk6XG5cdFx0XHQvLyBtaW50aW5nIGEgZnJlc2ggaWQgaGVyZSB3b3VsZCByZS1yZWdpc3RlciB0aGUgY29sbGVjdGlvbidzIHR5cGVzXG5cdFx0XHQvLyB1bmRlciBhIHNlY29uZCBgY29sbGVjdGlvbklkOjpgIHByZWZpeCBhbmQgZHVwbGljYXRlIGV2ZXJ5IGVtaXNzaW9uLlxuXHRcdFx0Y29uc3QgY29sbGVjdGlvbklkID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChub2RlLm5hbWUudGV4dCkgPz8gdGhpcy5uZXh0Q29sbGVjdGlvbklkKCk7XG5cdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuc2V0KG5vZGUubmFtZS50ZXh0LCBjb2xsZWN0aW9uSWQpO1xuXG5cdFx0XHRjb25zdCByZWdpc3RyeUludGVyZmFjZU5hbWUgPSB0aGlzLmV4dHJhY3RSZWdpc3RyeUludGVyZmFjZU5hbWUoXG5cdFx0XHRcdGluaXRpYWxpemVyIGFzIHRzLkNhbGxFeHByZXNzaW9uLFxuXHRcdFx0XHRzb3VyY2VGaWxlXG5cdFx0XHQpO1xuXHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKHNvdXJjZUZpbGUsIG5vZGUuZ2V0U3RhcnQoKSk7XG5cdFx0XHR0aGlzLmNvbGxlY3Rpb25JbmZvLnNldChjb2xsZWN0aW9uSWQsIHtcblx0XHRcdFx0dmFyaWFibGVOYW1lICAgICAgICAgIDogbm9kZS5uYW1lLnRleHQsXG5cdFx0XHRcdHNvdXJjZUZpbGUgICAgICAgICAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA6IHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSxcblx0XHRcdFx0bGluZSAgICAgICAgICAgICAgICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgICAgICAgICAgICAgICA6IGNoYXJhY3RlciArIDFcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEFsaWFzIG9mIGFub3RoZXIgY29sbGVjdGlvbiB2YXJpYWJsZVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRjb25zdCBleGlzdGluZyA9IHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5nZXQoaW5pdGlhbGl6ZXIudGV4dCk7XG5cdFx0XHRpZiAoZXhpc3RpbmcpIHtcblx0XHRcdFx0dGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLnNldChub2RlLm5hbWUudGV4dCwgZXhpc3RpbmcpO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSByZWdpc3RyeSBpbnRlcmZhY2UgbmFtZSBmcm9tIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbjxSZWdpc3RyeT4oKVxuXHQgKiB3aGVuIHRoZSBpbnRlcmZhY2UgaXMgZGVjbGFyZWQgaW4gdGhlIHNhbWUgc291cmNlIGZpbGUuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RSZWdpc3RyeUludGVyZmFjZU5hbWUgKFxuXHRcdGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGVcblx0KTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCB0eXBlQXJncyA9IGNhbGwudHlwZUFyZ3VtZW50cztcblx0XHRpZiAoIXR5cGVBcmdzIHx8IHR5cGVBcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBbIGZpcnN0VHlwZUFyZyBdID0gdHlwZUFyZ3M7XG5cdFx0aWYgKCF0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKGZpcnN0VHlwZUFyZykgfHwgIXRzLmlzSWRlbnRpZmllcihmaXJzdFR5cGVBcmcudHlwZU5hbWUpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IG5hbWUgPSBmaXJzdFR5cGVBcmcudHlwZU5hbWUudGV4dDtcblxuXHRcdC8vIENvbmZpcm0gdGhlIGludGVyZmFjZSBleGlzdHMgaW4gdGhlIHNhbWUgc291cmNlIGZpbGUuXG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc291cmNlRmlsZS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzSW50ZXJmYWNlRGVjbGFyYXRpb24oc3RhdGVtZW50KSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIG5hbWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBTdGFtcCBhIG5vZGUgd2l0aCBpdHMgY29sbGVjdGlvbidzIGVtaXNzaW9uIGluZm86IHRoZSBPcHRpb24gQiByZWdpc3RyeVxuXHQgKiBpbnRlcmZhY2UgbmFtZSBhbmQgdGhlIGNvbGxlY3Rpb24ncyBob21lIGZpbGUg4oCUIHRoZSBtb2R1bGUgdGhlIGdlbmVyYXRlZFxuXHQgKiBhdWdtZW50YXRpb24gbXVzdCB0YXJnZXQgKHRoZSBpbnRlcmZhY2UgaXMgY29uZmlybWVkIGRlY2xhcmVkIHRoZXJlKS5cblx0ICogQSB0eXBlJ3Mgb3duIHNvdXJjZUZpbGUgaXMgTk9UIHRoZSB0YXJnZXQ6IG11bHRpLWZpbGUgY29sbGVjdGlvbnMgZGVmaW5lXG5cdCAqIHR5cGVzIGFjcm9zcyBtYW55IG1vZHVsZXMgd2hpbGUgdGhlIGludGVyZmFjZSBsaXZlcyBhdCB0aGVcblx0ICogY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgY2FsbCBzaXRlLlxuXHQgKi9cblx0cHJpdmF0ZSBhcHBseUNvbGxlY3Rpb25FbWlzc2lvbkluZm8gKG5vZGU6IFR5cGVOb2RlLCBjb2xsZWN0aW9uSWQ/OiBzdHJpbmcpOiB2b2lkIHtcblx0XHRpZiAoIWNvbGxlY3Rpb25JZCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBpbmZvID0gdGhpcy5jb2xsZWN0aW9uSW5mby5nZXQoY29sbGVjdGlvbklkKTtcblx0XHRpZiAoIWluZm8pIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0bm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWUgPSBpbmZvLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZTtcblx0XHRub2RlLmNvbGxlY3Rpb25Tb3VyY2VGaWxlID0gaW5mby5zb3VyY2VGaWxlO1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGFuIGV4cHJlc3Npb24gaXMgYSBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSBjYWxsLlxuXHQgKiBIYW5kbGVzOlxuXHQgKiAgIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpXG5cdCAqICAgY3RjKCkgLy8gYWxpYXNlZCBpbXBvcnRcblx0ICogICBtbmVtb25pY2EuY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgLy8gbW9kdWxlIG9iamVjdCBtZXRob2Rcblx0ICogICBtLmNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIC8vIGFsaWFzZWQgbW9kdWxlIG9iamVjdFxuXHQgKi9cblx0cHJpdmF0ZSBpc0NyZWF0ZVR5cGVzQ29sbGVjdGlvbkNhbGwgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkNhbGxFeHByZXNzaW9uIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Y29uc3QgZXhwciA9IG5vZGUuZXhwcmVzc2lvbjtcblxuXHRcdC8vIERpcmVjdCBjYWxsIG9yIGFsaWFzZWQgaW1wb3J0OiBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSAvIGN0YygpXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIGV4cHIudGV4dCA9PT0gJ2NyZWF0ZVR5cGVzQ29sbGVjdGlvbicgfHxcblx0XHRcdFx0dGhpcy5jcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGV4cHIudGV4dCk7XG5cdFx0fVxuXG5cdFx0Ly8gTW9kdWxlIG9iamVjdCBtZXRob2Q6IG1uZW1vbmljYS5jcmVhdGVUeXBlc0NvbGxlY3Rpb24oKVxuXHRcdGlmIChcblx0XHRcdHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpICYmXG5cdFx0XHRleHByLm5hbWUudGV4dCA9PT0gJ2NyZWF0ZVR5cGVzQ29sbGVjdGlvbicgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcihleHByLmV4cHJlc3Npb24pICYmXG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoZXhwci5leHByZXNzaW9uLnRleHQpXG5cdFx0KSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogR2VuZXJhdGUgYSB1bmlxdWUgY29sbGVjdGlvbiBpZGVudGlmaWVyLlxuXHQgKi9cblx0cHJpdmF0ZSBuZXh0Q29sbGVjdGlvbklkICgpOiBzdHJpbmcge1xuXHRcdHRoaXMuY29sbGVjdGlvbkNvdW50ZXIrKztcblx0XHRjb25zdCByZXN1bHQgPSBgY29sbGVjdGlvbl8ke3RoaXMuY29sbGVjdGlvbkNvdW50ZXJ9YDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGEgbm9kZSBpcyBhIGRlZmluZSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgaXNEZWZpbmVDYWxsIChub2RlOiB0cy5Ob2RlKTogbm9kZSBpcyB0cy5DYWxsRXhwcmVzc2lvbiB7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIGRpcmVjdCBjYWxsOiBkZWZpbmUoJ1R5cGVOYW1lJywgLi4uKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIG1ldGhvZCBjYWxsOiBTb21lVHlwZS5kZWZpbmUoJ1N1YlR5cGUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gZXhwcmVzc2lvbi5uYW1lPy50ZXh0ID09PSAnZGVmaW5lJztcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogQ2hlY2sgaWYgYSBub2RlIGlzIGEgbGF6eSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgaXNMYXp5Q2FsbCAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuQ2FsbEV4cHJlc3Npb24ge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBkaXJlY3QgY2FsbDogbGF6eSgnVHlwZU5hbWUnLCBnZXR0ZXIsIC4uLilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2xhenknKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgbWV0aG9kIGNhbGw6IFNvbWVUeXBlLmxhenkoJ1N1YlR5cGUnLCBnZXR0ZXIsIC4uLilcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcmVzc2lvbikpIHtcblx0XHRcdHJldHVybiBleHByZXNzaW9uLm5hbWU/LnRleHQgPT09ICdsYXp5Jztcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0XHQqIEV4dHJhY3QgY29uZmlnIG9wdGlvbnMgZnJvbSBhbiBvYmplY3QgbGl0ZXJhbFxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsIChjb25maWdBcmc6IHRzLk9iamVjdExpdGVyYWxFeHByZXNzaW9uKTpcblx0XHR7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0ge1xuXHRcdGNvbnN0IGNvbmZpZzogeyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9ID0ge307XG5cblx0XHRmb3IgKGNvbnN0IHByb3Agb2YgY29uZmlnQXJnLnByb3BlcnRpZXMpIHtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSAmJiB0cy5pc0lkZW50aWZpZXIocHJvcC5uYW1lKSkge1xuXHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IHByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRpZiAocHJvcE5hbWUgPT09ICdzdHJpY3RDaGFpbicgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLnN0cmljdENoYWluID0gdHJ1ZTtcblx0XHRcdFx0fSBlbHNlIGlmIChwcm9wTmFtZSA9PT0gJ3N0cmljdENoYWluJyAmJiBwcm9wLmluaXRpYWxpemVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLnN0cmljdENoYWluID0gZmFsc2U7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdibG9ja0Vycm9ycycgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLmJsb2NrRXJyb3JzID0gdHJ1ZTtcblx0XHRcdFx0fSBlbHNlIGlmIChwcm9wTmFtZSA9PT0gJ2Jsb2NrRXJyb3JzJyAmJiBwcm9wLmluaXRpYWxpemVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLmJsb2NrRXJyb3JzID0gZmFsc2U7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gY29uZmlnO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IGNvbmZpZyBvcHRpb25zIGZyb20gZGVmaW5lKCkgY2FsbFxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdENvbmZpZyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0ge1xuXHRcdC8vIENvbmZpZyBpcyB0aGUgdGhpcmQgYXJndW1lbnQ6IGRlZmluZSgnTmFtZScsIGhhbmRsZXIsIGNvbmZpZylcblx0XHRjb25zdCBbICwgLCBjb25maWdBcmcgXSA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGlmICghY29uZmlnQXJnIHx8ICF0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGNvbmZpZ0FyZykpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRjb25zdCBjb25maWdSZXN1bHQgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjb25maWdBcmcpO1xuXHRcdHJldHVybiBjb25maWdSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHQqIENoZWNrIGlmIGEgbm9kZSBpcyBhIEBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHRcdCovXG5cdHByaXZhdGUgaXNEZWNvcmF0ZURlY29yYXRvciAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuRGVjb3JhdG9yIHtcblx0XHRpZiAoIXRzLmlzRGVjb3JhdG9yKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIEBkZWNvcmF0ZVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVjb3JhdGUnKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgQGRlY29yYXRlKCkgb3IgQGRlY29yYXRlKFBhcmVudFR5cGUpXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZXhwcmVzc2lvbikpIHtcblx0XHRcdGNvbnN0IGZuTmFtZSA9IGV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZm5OYW1lKSAmJiBmbk5hbWUudGV4dCA9PT0gJ2RlY29yYXRlJykge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gQ2hlY2sgZm9yIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSB3aGVyZSBNeUNvbGxlY3Rpb24gaXMgYSBjdXN0b20gY29sbGVjdGlvblxuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihmbk5hbWUpICYmXG5cdFx0XHRcdGZuTmFtZS5uYW1lLnRleHQgPT09ICdkZWNvcmF0ZScgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGZuTmFtZS5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGZuTmFtZS5leHByZXNzaW9uLnRleHQpXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIE1hcmsgYSBjYWxsIGV4cHJlc3Npb24gYXMgcHJvY2Vzc2VkIGFuZCByZXR1cm4gd2hldGhlciBpdCBhbHJlYWR5IHdhcy5cblx0ICovXG5cdHByaXZhdGUgbWFya1Byb2Nlc3NlZCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBib29sZWFuIHtcblx0XHRpZiAodGhpcy5wcm9jZXNzZWRDYWxscy5oYXMoY2FsbCkpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHR0aGlzLnByb2Nlc3NlZENhbGxzLmFkZChjYWxsKTtcblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogUHJvY2VzcyBhIGRlZmluZSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgcHJvY2Vzc0RlZmluZUNhbGwgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBleGFjdCBjYWxsIGhhcyBhbHJlYWR5IGJlZW4gcHJvY2Vzc2VkIChwcmV2ZW50cyBkdXBsaWNhdGVzIGZyb20gY2hhaW5lZCBjYWxscylcblx0XHRpZiAodGhpcy5tYXJrUHJvY2Vzc2VkKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgY29tcHV0ZWROYW1lcyA9IHRoaXMuZXh0cmFjdENvbXB1dGVkVHlwZU5hbWVzKGNhbGwpO1xuXHRcdGlmIChjb21wdXRlZE5hbWVzICE9PSB1bmRlZmluZWQpIHtcblx0XHRcdGZvciAoY29uc3QgdHlwZU5hbWUgb2YgY29tcHV0ZWROYW1lcykge1xuXHRcdFx0XHRjb25zdCBjb21wdXRlZENvbnRleHQgPSB0aGlzLmV4dHJhY3REZWZpbmVDb250ZXh0KGNhbGwsIHR5cGVOYW1lKTtcblx0XHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ29udGV4dChjYWxsLCBzb3VyY2VGaWxlLCBjb21wdXRlZENvbnRleHQsIHRydWUpO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEdldCB0aGUgdHlwZSBuYW1lIGFuZCBzb3VyY2UgY29udGV4dCBmcm9tIGFyZ3VtZW50c1xuXHRcdGNvbnN0IGRlZmluZUNvbnRleHQgPSB0aGlzLmV4dHJhY3REZWZpbmVDb250ZXh0KGNhbGwpO1xuXHRcdHRoaXMucHJvY2Vzc0RlZmluZUNvbnRleHQoY2FsbCwgc291cmNlRmlsZSwgZGVmaW5lQ29udGV4dCwgZmFsc2UpO1xuXHR9XG5cblx0cHJpdmF0ZSBwcm9jZXNzRGVmaW5lQ29udGV4dCAoXG5cdFx0Y2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRkZWZpbmVDb250ZXh0OiB7XG5cdFx0XHR0eXBlTmFtZT86IHN0cmluZztcblx0XHRcdHBhcmVudFR5cGU/OiBUeXBlTm9kZTtcblx0XHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0XHR9LFxuXHRcdG1ldGFkYXRhT25seTogYm9vbGVhblxuXHQpOiB2b2lkIHtcblx0XHQvLyBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGRlZmluZSgnQScpLmRlZmluZSgnQicpLCB3ZSB3YW50IHRoZSBwb3NpdGlvbiBvZiB0aGUgLmRlZmluZSgnQicpIHBhcnRcblx0XHQvLyBub3QgdGhlIHN0YXJ0IG9mIHRoZSBlbnRpcmUgZXhwcmVzc2lvblxuXHRcdGxldCBwb3NpdGlvbk5vZGU6IHRzLk5vZGUgPSBjYWxsO1xuXG5cdFx0Ly8gSWYgdGhpcyBpcyBhIGNoYWluZWQgY2FsbCwgZ2V0IHRoZSBwb3NpdGlvbiBvZiB0aGUgcHJvcGVydHkgYWNjZXNzIGV4cHJlc3Npb25cblx0XHQvLyB3aGljaCBpcyB0aGUgLmRlZmluZSBwYXJ0XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdC8vIFRoZSBleHByZXNzaW9uIGlzIHRoZSBwcm9wZXJ0eSBhY2Nlc3M6IChkZWZpbmUoJ1Jvb3RBc3luYycsIC4uLikpLmRlZmluZVxuXHRcdFx0Ly8gV2Ugd2FudCB0aGUgcG9zaXRpb24gb2YganVzdCB0aGUgLmRlZmluZSBwYXJ0XG5cdFx0XHQvLyBUaGlzIGlzIHRoZSAnZGVmaW5lJyBpZGVudGlmaWVyXG5cdFx0XHRwb3NpdGlvbk5vZGUgPSBjYWxsLmV4cHJlc3Npb24ubmFtZTtcblx0XHR9XG5cblx0XHRjb25zdCBzdGFydFBvcyA9IHBvc2l0aW9uTm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKTtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oc291cmNlRmlsZSwgc3RhcnRQb3MpO1xuXG5cdFx0aWYgKCFkZWZpbmVDb250ZXh0LnR5cGVOYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdDb3VsZCBub3QgZXh0cmFjdCB0eXBlIG5hbWUgZnJvbSBkZWZpbmUoKSBjYWxsJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IHR5cGVOYW1lIH0gPSBkZWZpbmVDb250ZXh0O1xuXG5cdFx0Ly8gRGV0ZXJtaW5lIHBhcmVudCB0eXBlIGFuZCBjb2xsZWN0aW9uIGJhc2VkIG9uIHRoZSBjYWxsIHNvdXJjZS5cblx0XHRjb25zdCBwYXJlbnROb2RlID0gZGVmaW5lQ29udGV4dC5wYXJlbnRUeXBlO1xuXHRcdGNvbnN0IHsgY29sbGVjdGlvbklkIH0gPSBkZWZpbmVDb250ZXh0O1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25maWcgb3B0aW9uc1xuXHRcdGNvbnN0IGNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZyhjYWxsKTtcblxuXHRcdC8vIENyZWF0ZSB0eXBlIG5vZGUgZmlyc3Qgc28gaXRzIGludGVybmFsIGZ1bGxQYXRoIChpbmNsdWRpbmcgYW55IGNvbGxlY3Rpb24gcHJlZml4KSBpcyByZXNvbHZlZC5cblx0XHRjb25zdCBub2RlID0gVHlwZUdyYXBoSW1wbC5jcmVhdGVOb2RlKFxuXHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRwYXJlbnROb2RlLFxuXHRcdFx0c291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdGxpbmUgKyAxLFxuXHRcdFx0Y2hhcmFjdGVyICsgMSxcblx0XHRcdGNvbGxlY3Rpb25JZFxuXHRcdCk7XG5cdFx0dGhpcy5hcHBseUNvbGxlY3Rpb25FbWlzc2lvbkluZm8obm9kZSwgY29sbGVjdGlvbklkKTtcblx0XHRub2RlLm1ldGFkYXRhT25seSA9IG1ldGFkYXRhT25seTtcblxuXHRcdC8vIFNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZSBkZXRlY3Rpb24gKGhhcmQtZmFpbCBsYXcpOiBrZXkgYnkgdGhlXG5cdFx0Ly8gcnVudGltZSBuYW1lc3BhY2Ug4oCUIGNvbGxlY3Rpb24gcm9vdHMgYDxjb2xsZWN0aW9uPjo6PG5hbWU+YCwgb3Jcblx0XHQvLyBgPHBhcmVudEZ1bGxQYXRoPi48bmFtZT5gIGZvciBzdWJ0eXBlc1xuXHRcdHRoaXMucmVjb3JkRGVmaW5lU2l0ZShcblx0XHRcdHBhcmVudE5vZGUgPyBgJHtwYXJlbnROb2RlLmZ1bGxQYXRofS4ke3R5cGVOYW1lfWAgOiBgJHtjb2xsZWN0aW9uSWQgPz8gJ2RlZmF1bHQnfTo6JHt0eXBlTmFtZX1gLFxuXHRcdFx0YCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWBcblx0XHQpO1xuXG5cdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gY29uc3RydWN0b3IgZnVuY3Rpb24g4oCUIHRoZSBuZXcgbm9kZSBhbmNob3JzXG5cdFx0Ly8gcmVsYXRpdmUtZmlyc3QgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb24gd2hpbGUgaXRzIG93biBzaWduYXR1cmVcblx0XHQvLyBpcyBiZWluZyByZWFkXG5cdFx0Y29uc3QgcHJldmlvdXNBbmNob3IgPSB0aGlzLmN1cnJlbnRHcmFwaEFuY2hvcjtcblx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IG5vZGU7XG5cdFx0dHJ5IHtcblx0XHRcdG5vZGUucHJvcGVydGllcyA9IHRoaXMuZXh0cmFjdFByb3BlcnRpZXMoY2FsbCk7XG5cblx0XHRcdC8vIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmb3IgVHlwZVJlZ2lzdHJ5IHNpZ25hdHVyZVxuXHRcdFx0bm9kZS5jb25zdHJ1Y3RvclBhcmFtcyA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zKGNhbGwpO1xuXHRcdH0gZmluYWxseSB7XG5cdFx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IHByZXZpb3VzQW5jaG9yO1xuXHRcdH1cblxuXHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yRXhwcmVzc2lvbihjYWxsKTtcblx0XHRub2RlLmluc3RhbmNlVHlwZU92ZXJyaWRlID0gdGhpcy5oYXNBbnlUaGlzQW5ub3RhdGlvbihjb25zdHJ1Y3RvckV4cHIpID8gJ2FueScgOiB1bmRlZmluZWQ7XG5cdFx0Ly8gQXN5bmMgY29uc3RydWN0b3IgZGV0ZWN0aW9uIChhc3luYyBtb2RpZmllciwgc3ludGFjdGljIG9ubHkpXG5cdFx0bm9kZS5pc0FzeW5jID0gdGhpcy5pc0FzeW5jQ29uc3RydWN0SGFuZGxlcih0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCkpO1xuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoXG5cdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkQ2hpbGQocGFyZW50Tm9kZSwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cblx0XHQvLyBDcmVhdGUgZGVmaW5pdGlvbiBpbmZvIHVzaW5nIHRoZSBub2RlJ3MgcmVzb2x2ZWQgZnVsbFBhdGhcblx0XHRjb25zdCBkZWZpbml0aW9uOiBEZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogcGFyZW50Tm9kZSA/IHBhcmVudE5vZGUuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiBjb25maWcuc3RyaWN0Q2hhaW4gPz8gdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogY29uZmlnLmJsb2NrRXJyb3JzID8/IGZhbHNlLFxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQobm9kZS5mdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdFx0aWYgKCFtZXRhZGF0YU9ubHkpIHtcblx0XHRcdHRoaXMuZWRzU2NvcGVCeU5vZGUuc2V0KGNhbGwsIG5vZGUuZnVsbFBhdGgpO1xuXG5cdFx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50OiBjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKSAtPiBtYXAgXCJVc2VyXCIgdG8gXCJVc2VyRW50aXR5XCJcblx0XHRcdC8vIEEgbXVsdGktaG9wIGluaXRpYWxpemVyIGJpbmRzIHRoZSBMQVNUIGhvcDogZGVmaW5lKCkgcmV0dXJucyB0aGVcblx0XHRcdC8vIGRlZmluZWQgdHlwZSdzIGNvbnN0cnVjdG9yIChGMTgpXG5cdFx0XHR0aGlzLnRyYWNrVmFyaWFibGVBc3NpZ25tZW50KGNhbGwsIHBhcmVudE5vZGUsIG5vZGUuZnVsbFBhdGgsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBQcm9jZXNzIGEgbGF6eSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgcHJvY2Vzc0xhenlDYWxsIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGlmIHRoaXMgZXhhY3QgY2FsbCBoYXMgYWxyZWFkeSBiZWVuIHByb2Nlc3NlZCAocHJldmVudHMgZHVwbGljYXRlcyBmcm9tIGNoYWluZWQgY2FsbHMpXG5cdFx0aWYgKHRoaXMubWFya1Byb2Nlc3NlZChjYWxsKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEdldCB0aGUgdHlwZSBuYW1lIGFuZCBzb3VyY2UgY29udGV4dCBmcm9tIGFyZ3VtZW50c1xuXHRcdGNvbnN0IGxhenlDb250ZXh0ID0gdGhpcy5leHRyYWN0TGF6eUNvbnRleHQoY2FsbCwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGRlZmluZSgnQScpLmxhenkoJ0InKSwgd2Ugd2FudCB0aGUgcG9zaXRpb24gb2YgdGhlIC5sYXp5KCdCJykgcGFydFxuXHRcdC8vIG5vdCB0aGUgc3RhcnQgb2YgdGhlIGVudGlyZSBleHByZXNzaW9uXG5cdFx0bGV0IHBvc2l0aW9uTm9kZTogdHMuTm9kZSA9IGNhbGw7XG5cblx0XHQvLyBJZiB0aGlzIGlzIGEgY2hhaW5lZCBjYWxsLCBnZXQgdGhlIHBvc2l0aW9uIG9mIHRoZSBwcm9wZXJ0eSBhY2Nlc3MgZXhwcmVzc2lvblxuXHRcdC8vIHdoaWNoIGlzIHRoZSAubGF6eSBwYXJ0XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdC8vIFRoZSBleHByZXNzaW9uIGlzIHRoZSBwcm9wZXJ0eSBhY2Nlc3M6IChkZWZpbmUoJ1Jvb3RBc3luYycsIC4uLikpLmxhenlcblx0XHRcdC8vIFdlIHdhbnQgdGhlIHBvc2l0aW9uIG9mIGp1c3QgdGhlIC5sYXp5IHBhcnRcblx0XHRcdC8vIFRoaXMgaXMgdGhlICdsYXp5JyBpZGVudGlmaWVyXG5cdFx0XHRwb3NpdGlvbk5vZGUgPSBjYWxsLmV4cHJlc3Npb24ubmFtZTtcblx0XHR9XG5cblx0XHRjb25zdCBzdGFydFBvcyA9IHBvc2l0aW9uTm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKTtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oc291cmNlRmlsZSwgc3RhcnRQb3MpO1xuXG5cdFx0Ly8gVGhlIHVubmFtZWQgZm9ybXMg4oCUIGxhenkoZ2V0dGVyKSwgVHlwZS5sYXp5KGdldHRlciwgY29uZmlnPyksXG5cdFx0Ly8gbGF6eShzb3VyY2UsIGdldHRlciwgY29uZmlnPykg4oCUIHRocm93IFRZUEVOQU1FX01VU1RfQkVfQV9TVFJJTkcgYXRcblx0XHQvLyBydW50aW1lICh0aGUgbmFtZSBpcyByZXF1aXJlZCksIHNvIGdlbmVyYXRpbmcgYSB0eXBlIGZyb20gdGhlXG5cdFx0Ly8gZ2V0dGVyJ3MgY29uc3RydWN0b3IgbmFtZSB3b3VsZCBibGVzcyBjb2RlIHRoYXQgY3Jhc2hlcy4gVGhleSBhcmVcblx0XHQvLyBhbiBhbmFseXplciBlcnJvciBuYW1pbmcgdGhlIGNhbGwgc2l0ZSBhbmQgdGhlIHJlcXVpcmVkIGZvcm0uXG5cdFx0Y29uc3QgbGF6eUFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0aWYgKGxhenlBcmdzICYmIGxhenlBcmdzLm5hbWUgPT09IHVuZGVmaW5lZCkge1xuXHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdG1lc3NhZ2UgOiAnbGF6eSgpIHJlcXVpcmVzIGEgdHlwZSBuYW1lOiBsYXp5KFxcJ05hbWVcXCcsIGdldHRlciknLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGlmICghbGF6eUNvbnRleHQudHlwZU5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0NvdWxkIG5vdCBleHRyYWN0IHR5cGUgbmFtZSBmcm9tIGxhenkoKSBjYWxsJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IHR5cGVOYW1lIH0gPSBsYXp5Q29udGV4dDtcblxuXHRcdC8vIERldGVybWluZSBwYXJlbnQgdHlwZSBhbmQgY29sbGVjdGlvbiBiYXNlZCBvbiB0aGUgY2FsbCBzb3VyY2UuXG5cdFx0Y29uc3QgcGFyZW50Tm9kZSA9IGxhenlDb250ZXh0LnBhcmVudFR5cGU7XG5cdFx0Y29uc3QgeyBjb2xsZWN0aW9uSWQgfSA9IGxhenlDb250ZXh0O1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25maWcgb3B0aW9uc1xuXHRcdGNvbnN0IGNvbmZpZyA9IHRoaXMuZXh0cmFjdExhenlDb25maWcoY2FsbCk7XG5cblx0XHQvLyBDcmVhdGUgdHlwZSBub2RlIGZpcnN0IHNvIGl0cyBpbnRlcm5hbCBmdWxsUGF0aCAoaW5jbHVkaW5nIGFueSBjb2xsZWN0aW9uIHByZWZpeCkgaXMgcmVzb2x2ZWQuXG5cdFx0Y29uc3Qgbm9kZSA9IFR5cGVHcmFwaEltcGwuY3JlYXRlTm9kZShcblx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0cGFyZW50Tm9kZSxcblx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRsaW5lICsgMSxcblx0XHRcdGNoYXJhY3RlciArIDEsXG5cdFx0XHRjb2xsZWN0aW9uSWRcblx0XHQpO1xuXHRcdHRoaXMuYXBwbHlDb2xsZWN0aW9uRW1pc3Npb25JbmZvKG5vZGUsIGNvbGxlY3Rpb25JZCk7XG5cblx0XHQvLyBTYW1lLW5hbWVzcGFjZSBkdXBsaWNhdGUgZGV0ZWN0aW9uIChoYXJkLWZhaWwgbGF3KVxuXHRcdHRoaXMucmVjb3JkRGVmaW5lU2l0ZShcblx0XHRcdHBhcmVudE5vZGUgPyBgJHtwYXJlbnROb2RlLmZ1bGxQYXRofS4ke3R5cGVOYW1lfWAgOiBgJHtjb2xsZWN0aW9uSWQgPz8gJ2RlZmF1bHQnfTo6JHt0eXBlTmFtZX1gLFxuXHRcdFx0YCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWBcblx0XHQpO1xuXG5cdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gdGhlIGNvbnN0cnVjdG9yIHJldHVybmVkIGJ5IHRoZSBsYXp5IGdldHRlclxuXHRcdC8vIOKAlCB0aGUgbmV3IG5vZGUgYW5jaG9ycyByZWxhdGl2ZS1maXJzdCBncmFwaCByZWZlcmVuY2UgcmVzb2x1dGlvblxuXHRcdGNvbnN0IHByZXZpb3VzQW5jaG9yID0gdGhpcy5jdXJyZW50R3JhcGhBbmNob3I7XG5cdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBub2RlO1xuXHRcdHRyeSB7XG5cdFx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzKGNhbGwpO1xuXG5cdFx0XHQvLyBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZm9yIFR5cGVSZWdpc3RyeSBzaWduYXR1cmVcblx0XHRcdG5vZGUuY29uc3RydWN0b3JQYXJhbXMgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyhjYWxsKTtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBwcmV2aW91c0FuY2hvcjtcblx0XHR9XG5cblx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCk7XG5cdFx0bm9kZS5pbnN0YW5jZVR5cGVPdmVycmlkZSA9IHRoaXMuaGFzQW55VGhpc0Fubm90YXRpb24oY29uc3RydWN0b3JFeHByKSA/ICdhbnknIDogdW5kZWZpbmVkO1xuXHRcdC8vIEFzeW5jIGNvbnN0cnVjdG9yIGRldGVjdGlvbiAoYXN5bmMgbW9kaWZpZXIsIHN5bnRhY3RpYyBvbmx5KVxuXHRcdG5vZGUuaXNBc3luYyA9IHRoaXMuaXNBc3luY0NvbnN0cnVjdEhhbmRsZXIodGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpKTtcblxuXHRcdC8vIEFkZCB0byBncmFwaFxuXHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZENoaWxkKHBhcmVudE5vZGUsIG5vZGUpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZFJvb3Qobm9kZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ3JlYXRlIGRlZmluaXRpb24gaW5mbyB1c2luZyB0aGUgbm9kZSdzIHJlc29sdmVkIGZ1bGxQYXRoXG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IHR5cGVOYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlZmluZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IHBhcmVudE5vZGUgPyBwYXJlbnROb2RlLmZ1bGxQYXRoIDogbnVsbCxcblx0XHRcdHN0cmljdENoYWluIDogY29uZmlnLnN0cmljdENoYWluID8/IHRydWUsXG5cdFx0XHRibG9ja0Vycm9ycyA6IGNvbmZpZy5ibG9ja0Vycm9ycyA/PyBmYWxzZSxcblx0XHR9O1xuXHRcdHRoaXMuZGVmaW5pdGlvbnMuc2V0KG5vZGUuZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXHRcdHRoaXMuZWRzU2NvcGVCeU5vZGUuc2V0KGNhbGwsIG5vZGUuZnVsbFBhdGgpO1xuXG5cdFx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudDogY29uc3QgTGF6eVR5cGUgPSBsYXp5KCdMYXp5VHlwZScsIC4uLikgLT4gbWFwIFwiTGF6eVR5cGVcIiAtPiBcIkxhenlUeXBlXCJcblx0XHQvLyBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGNvbnN0IFggPSBsYXp5KCdBJykuZGVmaW5lKCdCJyksIHdlIHdhbnQgdG8gbWFwIFggLT4gQSAodGhlIHJvb3QpXG5cdFx0dGhpcy50cmFja1ZhcmlhYmxlQXNzaWdubWVudChjYWxsLCBwYXJlbnROb2RlLCBub2RlLmZ1bGxQYXRoLCBzb3VyY2VGaWxlKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGxhenkoKSBjYWxsIGFyZ3VtZW50cyBpbnRvIGEgbm9ybWFsaXplZCBzaGFwZS5cblx0ICogSGFuZGxlcyBuYW1lZC91bm5hbWVkIGFuZCBleHBsaWNpdC1zb3VyY2UgZm9ybXMsIGJvdGggYXMgZnJlZSBjYWxsc1xuXHQgKiBhbmQgYXMgbWV0aG9kIGNhbGxzLiBUaGUgdW5uYW1lZCBzaGFwZXMgcmV0dXJuIGBuYW1lOiB1bmRlZmluZWRgIOKAlFxuXHQgKiBwcm9jZXNzTGF6eUNhbGwgcmVqZWN0cyB0aGVtIHdpdGggYW4gYW5hbHl6ZXIgZXJyb3IgKHRoZSBydW50aW1lXG5cdCAqIHJlcXVpcmVzIHRoZSBuYW1lKSwgc28gbm8gdHlwZSBpcyBnZW5lcmF0ZWQgZm9yIHRoZW0uXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q2FsbEFyZ3MgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKToge1xuXHRcdHNvdXJjZT86IHRzLkV4cHJlc3Npb247XG5cdFx0bmFtZT86IHN0cmluZztcblx0XHRnZXR0ZXI6IHRzLkV4cHJlc3Npb247XG5cdFx0Y29uZmlnPzogdHMuRXhwcmVzc2lvbjtcblx0fSB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGNvbnN0IGlzTWV0aG9kQ2FsbCA9IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbik7XG5cblx0XHRpZiAoaXNNZXRob2RDYWxsKSB7XG5cdFx0XHQvLyBTb3VyY2UgaXMgdGhlIG9iamVjdCBvZiB0aGUgcHJvcGVydHkgYWNjZXNzOiBUeXBlLmxhenkoLi4uKVxuXHRcdFx0Y29uc3Qgc291cmNlID0gY2FsbC5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IFsgbWV0aG9kRmlyc3RBcmcgXSA9IGFyZ3M7XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKG1ldGhvZEZpcnN0QXJnKSkge1xuXHRcdFx0XHQvLyBUeXBlLmxhenkoJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRcdGlmIChhcmdzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0c291cmNlLFxuXHRcdFx0XHRcdG5hbWUgICA6IG1ldGhvZEZpcnN0QXJnLnRleHQsXG5cdFx0XHRcdFx0Z2V0dGVyIDogYXJnc1sgMSBdLFxuXHRcdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDIgXSxcblx0XHRcdFx0fTtcblx0XHRcdH1cblx0XHRcdC8vIFR5cGUubGF6eShnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRzb3VyY2UsXG5cdFx0XHRcdGdldHRlciA6IG1ldGhvZEZpcnN0QXJnLFxuXHRcdFx0XHRjb25maWcgOiBhcmdzWyAxIF0sXG5cdFx0XHR9O1xuXHRcdH1cblxuXHRcdC8vIEZyZWUgY2FsbDogbGF6eSguLi4pXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGFyZ3M7XG5cblx0XHQvLyBFeHBsaWNpdC1zb3VyY2UgZm9ybTogbGF6eShzb3VyY2UsICdOYW1lJywgZ2V0dGVyLCBjb25maWc/KVxuXHRcdC8vIG9yIGxhenkoc291cmNlLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIgJiYgdHMuaXNJZGVudGlmaWVyKGZpcnN0QXJnKSkge1xuXHRcdFx0Y29uc3QgWyAsIHNlY29uZEFyZyBdID0gYXJncztcblx0XHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoc2Vjb25kQXJnKSkge1xuXHRcdFx0XHQvLyBsYXp5KHNvdXJjZSwgJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRcdGlmIChhcmdzLmxlbmd0aCA8IDMpIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0c291cmNlIDogZmlyc3RBcmcsXG5cdFx0XHRcdFx0bmFtZSAgIDogc2Vjb25kQXJnLnRleHQsXG5cdFx0XHRcdFx0Z2V0dGVyIDogYXJnc1sgMiBdLFxuXHRcdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDMgXSxcblx0XHRcdFx0fTtcblx0XHRcdH1cblx0XHRcdC8vIGxhenkoc291cmNlLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRzb3VyY2UgOiBmaXJzdEFyZyxcblx0XHRcdFx0Z2V0dGVyIDogc2Vjb25kQXJnLFxuXHRcdFx0XHRjb25maWcgOiBhcmdzWyAyIF0sXG5cdFx0XHR9O1xuXHRcdH1cblxuXHRcdC8vIE5hbWVkIHJvb3QgZm9ybTogbGF6eSgnTmFtZScsIGdldHRlciwgY29uZmlnPylcblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGZpcnN0QXJnKSkge1xuXHRcdFx0aWYgKGFyZ3MubGVuZ3RoIDwgMikge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0bmFtZSAgIDogZmlyc3RBcmcudGV4dCxcblx0XHRcdFx0Z2V0dGVyIDogYXJnc1sgMSBdLFxuXHRcdFx0XHRjb25maWcgOiBhcmdzWyAyIF0sXG5cdFx0XHR9O1xuXHRcdH1cblxuXHRcdC8vIFVubmFtZWQgcm9vdCBmb3JtOiBsYXp5KGdldHRlciwgY29uZmlnPylcblx0XHRyZXR1cm4ge1xuXHRcdFx0Z2V0dGVyIDogZmlyc3RBcmcsXG5cdFx0XHRjb25maWcgOiBhcmdzWyAxIF0sXG5cdFx0fTtcblx0fVxuXG5cdC8qKlxuXHQgKiBVbndyYXAgdGhlIGNvbnN0cnVjdG9yIHJldHVybmVkIGJ5IGEgbGF6eSBnZXR0ZXIuXG5cdCAqIFN1cHBvcnRzOlxuXHQgKiAgICgpID0+IGNsYXNzIE5hbWUge31cblx0ICogICAoKSA9PiBmdW5jdGlvbiBOYW1lKCkge31cblx0ICogICAoKSA9PiB7IHJldHVybiBjbGFzcyBOYW1lIHt9OyB9XG5cdCAqICAgZnVuY3Rpb24gKCkgeyByZXR1cm4gZnVuY3Rpb24gTmFtZSgpIHt9OyB9XG5cdCAqL1xuXHRwcml2YXRlIHVud3JhcExhenlHZXR0ZXIgKGdldHRlckV4cHI6IHRzLkV4cHJlc3Npb24pOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGdldHRlckV4cHIpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGdldHRlckV4cHI7XG5cdFx0XHRpZiAoIXRzLmlzQmxvY2soYm9keSkpIHtcblx0XHRcdFx0cmV0dXJuIGJvZHk7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IHN0bXQgb2YgYm9keS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChzdG10KSAmJiBzdG10LmV4cHJlc3Npb24pIHtcblx0XHRcdFx0XHRyZXR1cm4gc3RtdC5leHByZXNzaW9uO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihnZXR0ZXJFeHByKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBnZXR0ZXJFeHByO1xuXHRcdFx0Zm9yIChjb25zdCBzdG10IG9mIGJvZHkuc3RhdGVtZW50cykge1xuXHRcdFx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQoc3RtdCkgJiYgc3RtdC5leHByZXNzaW9uKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHN0bXQuZXhwcmVzc2lvbjtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBOb3QgYSByZWNvZ25pemVkIGdldHRlciBwYXR0ZXJuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGEgY29uc3RydWN0b3IgbmFtZSBmcm9tIGEgY2xhc3MgZXhwcmVzc2lvbiwgY2xhc3MgZGVjbGFyYXRpb24sXG5cdCAqIG9yIG5hbWVkIGZ1bmN0aW9uIGV4cHJlc3Npb24uXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3Rvck5hbWUgKGNvbnN0cnVjdG9yRXhwcjogQ29uc3RydWN0b3JIYW5kbGVyKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSAmJiBjb25zdHJ1Y3RvckV4cHIubmFtZSkge1xuXHRcdFx0cmV0dXJuIGNvbnN0cnVjdG9yRXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0NsYXNzRGVjbGFyYXRpb24oY29uc3RydWN0b3JFeHByKSAmJiBjb25zdHJ1Y3RvckV4cHIubmFtZSkge1xuXHRcdFx0cmV0dXJuIGNvbnN0cnVjdG9yRXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpICYmIGNvbnN0cnVjdG9yRXhwci5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gY29uc3RydWN0b3JFeHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSB0eXBlIG5hbWUgZnJvbSBlaXRoZXIgYSBkZWZpbmUoKSBvciBsYXp5KCkgY2FsbC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRoaXMuaXNEZWZpbmVDYWxsKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5leHRyYWN0VHlwZU5hbWUoY2FsbCk7XG5cdFx0fVxuXHRcdGlmICh0aGlzLmlzTGF6eUNhbGwoY2FsbCkpIHtcblx0XHRcdGNvbnN0IGFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0XHRpZiAoIWFyZ3MpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGlmIChhcmdzLm5hbWUpIHtcblx0XHRcdFx0cmV0dXJuIGFyZ3MubmFtZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMudW53cmFwTGF6eUdldHRlcihhcmdzLmdldHRlcik7XG5cdFx0XHRpZiAoY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRcdHJldHVybiB0aGlzLmV4dHJhY3RDb25zdHJ1Y3Rvck5hbWUoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSBmdWxsIGxhenkoKSBjYWxsIGNvbnRleHQ6IHR5cGUgbmFtZSwgcGFyZW50IHR5cGUsIGFuZCBjb2xsZWN0aW9uLlxuXHQgKiBIYW5kbGVzIGRpcmVjdCBjYWxscywgcHJvcGVydHktYWNjZXNzIGNhbGxzLCBjaGFpbmVkIGNhbGxzLCBhbmQgdGhlXG5cdCAqIGV4cGxpY2l0LXNvdXJjZSBmb3JtIGBsYXp5KHNvdXJjZSwgJ1R5cGVOYW1lJywgZ2V0dGVyKWAuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q29udGV4dCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB7XG5cdFx0dHlwZU5hbWU/OiBzdHJpbmc7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Y29uc3QgYXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRpZiAoIWFyZ3MpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRsZXQgdHlwZU5hbWU6IHN0cmluZyB8IHVuZGVmaW5lZCA9IGFyZ3MubmFtZTtcblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLnVud3JhcExhenlHZXR0ZXIoYXJncy5nZXR0ZXIpO1xuXHRcdFx0aWYgKGNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0XHR0eXBlTmFtZSA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yTmFtZShjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBjYWxsO1xuXG5cdFx0Ly8gRGlyZWN0IGNhbGw6IGxhenkoJ1R5cGVOYW1lJywgLi4uKSBvciBsYXp5KHNvdXJjZSwgJ1R5cGVOYW1lJywgZ2V0dGVyKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnbGF6eScpIHtcblx0XHRcdGlmIChhcmdzLnNvdXJjZSAmJiB0cy5pc0lkZW50aWZpZXIoYXJncy5zb3VyY2UpKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2UoYXJncy5zb3VyY2UudGV4dCk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXHRcdFx0Ly8gUGxhaW4gcm9vdCBsYXp5IGluIGRlZmF1bHQgY29sbGVjdGlvblxuXHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUgfTtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSBhY2Nlc3M6IFgubGF6eSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnbGF6eScpIHtcblx0XHRcdGNvbnN0IG9iaiA9IGV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblxuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihvYmopKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uob2JqLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0XHRcdHBhcmVudFR5cGUgICA6IHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSxcblx0XHRcdFx0XHRjb2xsZWN0aW9uSWQgOiBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCxcblx0XHRcdFx0fTtcblx0XHRcdH1cblxuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gTmVzdGVkIGFjY2VzczogaW5zdGFuY2UuVHlwZS5sYXp5IC0gdHJ5IHRvIHJlc29sdmVcblx0XHRcdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4ob2JqKTtcblx0XHRcdFx0aWYgKGNoYWluLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShjaGFpbi5qb2luKCcuJykpO1xuXHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSB9O1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gRGV0ZXJtaW5lIHRoZSBjb2xsZWN0aW9uIGNvbnRleHQgZnJvbSB0aGUgcm9vdCBvZiB0aGUgY2hhaW4gc28gdGhhdFxuXHRcdFx0XHQvLyBjdXN0b20tY29sbGVjdGlvbiB0eXBlcyBkbyBub3QgZ2V0IGNvbmZ1c2VkIHdpdGggZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzLlxuXHRcdFx0XHRjb25zdCByb290SWQgPSB0aGlzLmdldFJvb3RJZGVudGlmaWVyKG9iai5leHByZXNzaW9uKTtcblx0XHRcdFx0Y29uc3QgZXhwZWN0ZWRDb2xsZWN0aW9uSWQgPSByb290SWRcblx0XHRcdFx0XHQ/IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShyb290SWQudGV4dCkuY29sbGVjdGlvbklkXG5cdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHRcdFx0Ly8gQ2hhaW5lZCBjYWxsOiBkZWZpbmUoJ0EnKS5sYXp5KCdCJykgb3IgbGF6eSgnQScpLmxhenkoJ0InKVxuXHRcdFx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwob2JqKSkge1xuXHRcdFx0XHRcdHRoaXMucHJvY2Vzc0RlZmluZUNhbGwob2JqLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRpZiAodGhpcy5pc0xhenlDYWxsKG9iaikpIHtcblx0XHRcdFx0XHR0aGlzLnByb2Nlc3NMYXp5Q2FsbChvYmosIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudFR5cGVOYW1lID0gdGhpcy5leHRyYWN0TW5lbW9uaWNhVHlwZU5hbWUob2JqKTtcblx0XHRcdFx0XHRpZiAocGFyZW50VHlwZU5hbWUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKHBhcmVudFR5cGVOYW1lLCBleHBlY3RlZENvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIEJ1aWxkZXIgbG9va3VwIGNoYWluOiBBcHAubG9va3VwKCdVc2VyJykubGF6eSgnQWRtaW4nKVxuXHRcdFx0XHRpZiAodGhpcy5pc0xvb2t1cENhbGwob2JqKSkge1xuXHRcdFx0XHRcdGNvbnN0IGxvb2tlZFVwUGF0aCA9IHRoaXMucmVzb2x2ZUxvb2t1cFBhdGgob2JqKTtcblx0XHRcdFx0XHRpZiAobG9va2VkVXBQYXRoKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShsb29rZWRVcFBhdGgpO1xuXHRcdFx0XHRcdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlLmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBjb25maWcgb3B0aW9ucyBmcm9tIGxhenkoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q29uZmlnIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSB7XG5cdFx0Y29uc3QgYXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRpZiAoIWFyZ3MgfHwgIWFyZ3MuY29uZmlnIHx8ICF0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGFyZ3MuY29uZmlnKSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IGNvbmZpZ1Jlc3VsdCA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGFyZ3MuY29uZmlnKTtcblx0XHRyZXR1cm4gY29uZmlnUmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIERvZXMgdGhlIGhhbmRsZXIgbmFtZSBhIGdlbmVyYXRlZCB0eXBlIOKAlCBkaXJlY3RseSwgb3IgdGhyb3VnaCB0aGUgdHlwZVxuXHQgKiBhbGlhc2VzLCBpbnRlcmZhY2VzIGFuZCBjbGFzc2VzIGl0IHJlZmVyZW5jZXMgKGZvbGxvd2VkIGFjcm9zcyBmaWxlcyxcblx0ICogZWFjaCBkZWNsYXJhdGlvbiBvbmNlKT8gU3VjaCBhIGhhbmRsZXIgaXMgdHlwZWQgYnkgaXRzIG93biByZWdpc3RyeVxuXHQgKiBlbnRyeSwgc28gaXRzIHZhbHVlIGNhbm5vdCBiZSBkZXJpdmVkLlxuXHQgKi9cblx0cHJpdmF0ZSBoYXNHZW5lcmF0ZWRUeXBlUmVmZXJlbmNlIChoYW5kbGVyOiBDb25zdHJ1Y3RvckhhbmRsZXIgfCB1bmRlZmluZWQpOiBib29sZWFuIHtcblx0XHRpZiAoIWhhbmRsZXIpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Y29uc3QgdmlzaXRlZCA9IG5ldyBTZXQ8dHMuTm9kZT4oKTtcblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnJlZmVyZW5jZXNHZW5lcmF0ZWRUeXBlKGhhbmRsZXIsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSwgdmlzaXRlZCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdHByaXZhdGUgcmVmZXJlbmNlc0dlbmVyYXRlZFR5cGUgKG5vZGU6IHRzLk5vZGUsIGZpbGU6IHN0cmluZywgdmlzaXRlZDogU2V0PHRzLk5vZGU+KTogYm9vbGVhbiB7XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihub2RlKSAmJiB0aGlzLmdlbmVyYXRlZFR5cGVJbXBvcnRzLmdldChmaWxlKT8uaGFzKG5vZGUudGV4dCkpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHQvLyBgdHlwZSBYID0g4oCmYCwgYHRoaXM6IFhgLCBgaW50ZXJmYWNlIFggZXh0ZW5kcyBZYDogZm9sbG93IHRoZSBuYW1lZFxuXHRcdC8vIGRlY2xhcmF0aW9uLCByZXNvbHZlZCBmcm9tIHRoZSBmaWxlIHRoYXQgdXNlcyB0aGUgbmFtZVxuXHRcdGxldCByZWZlcmVuY2VkTmFtZTogdHMuSWRlbnRpZmllciB8IHVuZGVmaW5lZDtcblx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZShub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS50eXBlTmFtZSkpIHtcblx0XHRcdHJlZmVyZW5jZWROYW1lID0gbm9kZS50eXBlTmFtZTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzRXhwcmVzc2lvbldpdGhUeXBlQXJndW1lbnRzKG5vZGUpICYmIHRzLmlzSWRlbnRpZmllcihub2RlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZWZlcmVuY2VkTmFtZSA9IG5vZGUuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0aWYgKHJlZmVyZW5jZWROYW1lKSB7XG5cdFx0XHRjb25zdCBkZWNsYXJhdGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24ocmVmZXJlbmNlZE5hbWUudGV4dCwgZmlsZSk7XG5cdFx0XHRpZiAoZGVjbGFyYXRpb24gJiYgIXZpc2l0ZWQuaGFzKGRlY2xhcmF0aW9uLm5vZGUpKSB7XG5cdFx0XHRcdHZpc2l0ZWQuYWRkKGRlY2xhcmF0aW9uLm5vZGUpO1xuXHRcdFx0XHRpZiAodGhpcy5yZWZlcmVuY2VzR2VuZXJhdGVkVHlwZShkZWNsYXJhdGlvbi5ub2RlLCBkZWNsYXJhdGlvbi5maWxlLCB2aXNpdGVkKSkge1xuXHRcdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGNvbnN0IGNoaWxkcmVuOiB0cy5Ob2RlW10gPSBbXTtcblx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgY2hpbGQgPT4ge1xuXHRcdFx0Y2hpbGRyZW4ucHVzaChjaGlsZCk7XG5cdFx0fSk7XG5cdFx0Zm9yIChjb25zdCBjaGlsZCBvZiBjaGlsZHJlbikge1xuXHRcdFx0aWYgKHRoaXMucmVmZXJlbmNlc0dlbmVyYXRlZFR5cGUoY2hpbGQsIGZpbGUsIHZpc2l0ZWQpKSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHRwcml2YXRlIGhhc1NlbGZUeXBlQW5ub3RhdGlvbiAoaGFuZGxlcjogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkLCBmdWxsUGF0aDogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0aWYgKCFoYW5kbGVyIHx8ICF0cy5pc0Z1bmN0aW9uTGlrZShoYW5kbGVyKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblx0XHRjb25zdCB0eXBlTmFtZSA9IGZ1bGxQYXRoLnNwbGl0KCcuJykucG9wKCk7XG5cdFx0Zm9yIChjb25zdCBwYXJhbWV0ZXIgb2YgaGFuZGxlci5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihwYXJhbWV0ZXIubmFtZSkgfHwgcGFyYW1ldGVyLm5hbWUudGV4dCAhPT0gJ3RoaXMnIHx8ICFwYXJhbWV0ZXIudHlwZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGFubm90YXRpb24gPSBwYXJhbWV0ZXIudHlwZS5nZXRUZXh0KCk7XG5cdFx0XHRjb25zdCByZXN1bHQgPSBhbm5vdGF0aW9uID09PSB0eXBlTmFtZSB8fCBhbm5vdGF0aW9uLmVuZHNXaXRoKGAuJHt0eXBlTmFtZX1gKSB8fFxuXHRcdFx0XHRhbm5vdGF0aW9uID09PSBgSW5zdGFuY2VUeXBlPHR5cGVvZiAke3R5cGVOYW1lfT5gO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0cHJpdmF0ZSByZWNvcmRCdWlsZGVyQ2FuZGlkYXRlIChcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0ZnVsbFBhdGg6IHN0cmluZyxcblx0XHRraW5kOiAncmVnaXN0cnlPZicgfCAndHlwZW9mJyxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdGRlY2xhcmF0aW9uOiB0cy5WYXJpYWJsZURlY2xhcmF0aW9uLFxuXHRcdGV4Y2x1ZGVkOiBib29sZWFuXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IGNhbmRpZGF0ZTogQnVpbGRlckNhbmRpZGF0ZSA9IHtcblx0XHRcdG5hbWUsXG5cdFx0XHRzb3VyY2VGaWxlIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdGtpbmQsXG5cdFx0XHRmdWxsUGF0aCxcblx0XHRcdGV4cG9ydHMgICAgOiBbXSxcblx0XHRcdGV4Y2x1ZGVkXG5cdFx0fTtcblx0XHRjb25zdCBzdGF0ZW1lbnQgPSBkZWNsYXJhdGlvbi5wYXJlbnQucGFyZW50O1xuXHRcdGNvbnN0IG1vZGlmaWVycyA9IHRzLmlzVmFyaWFibGVTdGF0ZW1lbnQoc3RhdGVtZW50KSA/IHRzLmdldE1vZGlmaWVycyhzdGF0ZW1lbnQpID8/IFtdIDogW107XG5cdFx0Y29uc3QgaXNEZWZhdWx0ID0gbW9kaWZpZXJzLnNvbWUobW9kaWZpZXIgPT4gbW9kaWZpZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5EZWZhdWx0S2V5d29yZCk7XG5cdFx0Y29uc3QgaXNFeHBvcnRlZCA9IG1vZGlmaWVycy5zb21lKG1vZGlmaWVyID0+IG1vZGlmaWVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRXhwb3J0S2V5d29yZCk7XG5cdFx0aWYgKGlzRXhwb3J0ZWQpIHtcblx0XHRcdGNhbmRpZGF0ZS5leHBvcnRzLnB1c2goe1xuXHRcdFx0XHRuYW1lICAgICAgICAgIDogbmFtZSxcblx0XHRcdFx0c291cmNlRmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGRlZmF1bHRJbXBvcnQgOiBpc0RlZmF1bHRcblx0XHRcdH0pO1xuXHRcdH1cblx0XHR0aGlzLmJ1aWxkZXJDYW5kaWRhdGVzLnB1c2goY2FuZGlkYXRlKTtcblx0fVxuXG5cdHByaXZhdGUgbWFya0J1aWxkZXJFeHBvcnQgKFxuXHRcdGV4cG9ydGVkTmFtZTogc3RyaW5nLFxuXHRcdG9yaWdpbmFsTmFtZTogc3RyaW5nLFxuXHRcdGZpbGVQYXRoOiBzdHJpbmcsXG5cdFx0bW9kdWxlU3BlY2lmaWVyPzogc3RyaW5nXG5cdCk6IHZvaWQge1xuXHRcdGlmICghbW9kdWxlU3BlY2lmaWVyKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGNhbmRpZGF0ZSBvZiB0aGlzLmJ1aWxkZXJDYW5kaWRhdGVzKSB7XG5cdFx0XHRcdGNvbnN0IG1hdGNoZXNDYW5kaWRhdGUgPSBub2RlUGF0aC5yZXNvbHZlKGNhbmRpZGF0ZS5zb3VyY2VGaWxlKSA9PT0gbm9kZVBhdGgucmVzb2x2ZShmaWxlUGF0aClcblx0XHRcdFx0XHQmJiBjYW5kaWRhdGUubmFtZSA9PT0gb3JpZ2luYWxOYW1lXG5cdFx0XHRcdFx0JiYgIWNhbmRpZGF0ZS5leGNsdWRlZDtcblx0XHRcdFx0aWYgKG1hdGNoZXNDYW5kaWRhdGUpIHtcblx0XHRcdFx0XHRjYW5kaWRhdGUuZXhwb3J0cy5wdXNoKHsgbmFtZSA6IGV4cG9ydGVkTmFtZSwgc291cmNlRmlsZSA6IGZpbGVQYXRoIH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShtb2R1bGVTcGVjaWZpZXIsIGZpbGVQYXRoKTtcblx0XHRpZiAocmVzb2x1dGlvbj8uaXNFeHRlcm5hbCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBmYWxsYmFja1BhdGggPSBtb2R1bGVTcGVjaWZpZXIuZW5kc1dpdGgoJy50cycpXG5cdFx0XHQ/IG5vZGVQYXRoLnJlc29sdmUobm9kZVBhdGguZGlybmFtZShmaWxlUGF0aCksIG1vZHVsZVNwZWNpZmllcilcblx0XHRcdDogYCR7bm9kZVBhdGgucmVzb2x2ZShub2RlUGF0aC5kaXJuYW1lKGZpbGVQYXRoKSwgbW9kdWxlU3BlY2lmaWVyKX0udHNgO1xuXHRcdGNvbnN0IHJlc29sdmVkUGF0aCA9IHJlc29sdXRpb24/LnJlc29sdmVkUGF0aCA/PyBmYWxsYmFja1BhdGg7XG5cdFx0Zm9yIChjb25zdCBjYW5kaWRhdGUgb2YgdGhpcy5idWlsZGVyQ2FuZGlkYXRlcykge1xuXHRcdFx0aWYgKG5vZGVQYXRoLnJlc29sdmUoY2FuZGlkYXRlLnNvdXJjZUZpbGUpICE9PSBub2RlUGF0aC5yZXNvbHZlKHJlc29sdmVkUGF0aCkgfHwgY2FuZGlkYXRlLmV4Y2x1ZGVkKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbWF0Y2hlc05hbWUgPSBvcmlnaW5hbE5hbWUgPT09ICdkZWZhdWx0J1xuXHRcdFx0XHQ/IGNhbmRpZGF0ZS5leHBvcnRzLnNvbWUoZXhwb3J0ZWQgPT4gZXhwb3J0ZWQubmFtZSA9PT0gJ2RlZmF1bHQnKVxuXHRcdFx0XHQ6IGNhbmRpZGF0ZS5uYW1lID09PSBvcmlnaW5hbE5hbWU7XG5cdFx0XHRpZiAobWF0Y2hlc05hbWUpIHtcblx0XHRcdFx0Y2FuZGlkYXRlLmV4cG9ydHMucHVzaCh7XG5cdFx0XHRcdFx0bmFtZSAgICAgICAgICA6IGV4cG9ydGVkTmFtZSxcblx0XHRcdFx0XHRzb3VyY2VGaWxlICAgIDogZmlsZVBhdGgsXG5cdFx0XHRcdFx0ZGVmYXVsdEltcG9ydCA6IG9yaWdpbmFsTmFtZSA9PT0gJ2RlZmF1bHQnXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdHByaXZhdGUgdHJhY2tCdWlsZGVyRXhwb3J0QXNzaWdubWVudCAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNFeHBvcnRBc3NpZ25tZW50KG5vZGUpIHx8ICF0cy5pc0lkZW50aWZpZXIobm9kZS5leHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRmb3IgKGNvbnN0IGNhbmRpZGF0ZSBvZiB0aGlzLmJ1aWxkZXJDYW5kaWRhdGVzKSB7XG5cdFx0XHRjb25zdCBtYXRjaGVzQ2FuZGlkYXRlID0gbm9kZVBhdGgucmVzb2x2ZShjYW5kaWRhdGUuc291cmNlRmlsZSkgPT09IG5vZGVQYXRoLnJlc29sdmUoZmlsZVBhdGgpXG5cdFx0XHRcdCYmIGNhbmRpZGF0ZS5uYW1lID09PSBub2RlLmV4cHJlc3Npb24udGV4dFxuXHRcdFx0XHQmJiAhY2FuZGlkYXRlLmV4Y2x1ZGVkO1xuXHRcdFx0aWYgKG1hdGNoZXNDYW5kaWRhdGUpIHtcblx0XHRcdFx0Y2FuZGlkYXRlLmV4cG9ydHMucHVzaCh7IG5hbWUgOiBub2RlLmV4cHJlc3Npb24udGV4dCwgc291cmNlRmlsZSA6IGZpbGVQYXRoLCBkZWZhdWx0SW1wb3J0IDogdHJ1ZSB9KTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHQqIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnRzIHRoYXQgY2FwdHVyZSBkZWZpbmUoKSByZXN1bHRzXG5cdFx0KiBlLmcuLCBjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKSBtYXBzIFwiVXNlclwiIC0+IFwiVXNlckVudGl0eVwiXG5cdFx0KiBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGNvbnN0IFggPSBkZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKSwgd2UgbWFwIFggLT4gQSAodGhlIHJvb3QgdHlwZSlcblx0XHQqL1xuXHRwcml2YXRlIHRyYWNrVmFyaWFibGVBc3NpZ25tZW50IChcblx0XHRjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHRwYXJlbnROb2RlOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCxcblx0XHRmdWxsUGF0aDogc3RyaW5nLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGVcblx0KTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBjYWxsIGlzIHRoZSByaWdodC1oYW5kIHNpZGUgb2YgYSB2YXJpYWJsZSBkZWNsYXJhdGlvblxuXHRcdC8vIFdhbGsgdXAgdGhlIHRyZWUgdG8gZmluZCBWYXJpYWJsZURlY2xhcmF0aW9uXG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBjYWxsLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihjdXJyZW50KSkge1xuXHRcdFx0XHQvLyBGb3VuZDogY29uc3QgWCA9IGRlZmluZSguLi4pXG5cdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudC5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHZhck5hbWUgPSBjdXJyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0XHQvLyBGMTg6IGRlZmluZSgpIHJldHVybnMgdGhlIERFRklORUQgdHlwZSdzIGNvbnN0cnVjdG9yLFxuXHRcdFx0XHRcdC8vIHNvIGEgY29uc3QgaG9sZGluZyBhIG11bHRpLWhvcCBpbml0aWFsaXplclxuXHRcdFx0XHRcdC8vIChgY29uc3QgWCA9IEEuZGVmaW5lKCdCJykuZGVmaW5lKCdDJylgKSBiaW5kcyB0aGUgTEFTVFxuXHRcdFx0XHRcdC8vIGhvcCDigJQgYSBkZWVwZXIgaG9wIG11c3Qgbm90IGJpbmQsIGFuZCB0aGUgb3V0ZXJtb3N0XG5cdFx0XHRcdFx0Ly8gaG9wIGJpbmRzIHVuY29uZGl0aW9uYWxseSAodmlzaXQtb3JkZXIgaW5kZXBlbmRlbnQpXG5cdFx0XHRcdFx0aWYgKHRoaXMuaXNEZWVwZXJEZWZpbmVIb3AoY2FsbCkpIHtcblx0XHRcdFx0XHRcdHJldHVybjtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Ly8gRm9yIGNoYWluZWQgbGF6eSBjYWxscyBsaWtlIGNvbnN0IFggPSBkZWZpbmUoJ0EnKS5sYXp5KCdCJyksXG5cdFx0XHRcdFx0Ly8gdGhlIGZpcnN0IGNhbGwgaW4gdGhlIGNoYWluIHNldHMgdGhlIG1hcHBpbmcgKGxhenkgaG9wXG5cdFx0XHRcdFx0Ly8ga2VlcHMgaXQg4oCUIHBpbm5lZCBiZWhhdmlvcilcblx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSAmJiB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmhhcyh2YXJOYW1lKSkge1xuXHRcdFx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCB0eXBlTm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoZnVsbFBhdGgpO1xuXHRcdFx0XHRcdGlmICh0eXBlTm9kZT8uY29sbGVjdGlvbklkID09PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHNlbGZSZWZlcmVuY2UgPSB0aGlzLmhhc0dlbmVyYXRlZFR5cGVSZWZlcmVuY2UodGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpKSB8fFxuXHRcdFx0XHRcdFx0dGhpcy5oYXNTZWxmVHlwZUFubm90YXRpb24odGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpLCBmdWxsUGF0aCk7XG5cdFx0XHRcdFx0XHRjb25zdCBleGNsdWRlZCA9IHNlbGZSZWZlcmVuY2UgfHwgKFxuXHRcdFx0XHRcdFx0XHRwYXJlbnROb2RlICE9PSB1bmRlZmluZWQgJiYgdGhpcy5leGNsdWRlZFR5cGVQYXRocy5oYXMocGFyZW50Tm9kZS5mdWxsUGF0aClcblx0XHRcdFx0XHRcdCk7XG5cdFx0XHRcdFx0XHRpZiAoZXhjbHVkZWQpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5leGNsdWRlZFR5cGVQYXRocy5hZGQoZnVsbFBhdGgpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0Y29uc3Qga2luZCA9IHRzLmlzSWRlbnRpZmllcihjYWxsLmV4cHJlc3Npb24pID8gJ3R5cGVvZicgOiAncmVnaXN0cnlPZic7XG5cdFx0XHRcdFx0XHR0aGlzLnJlY29yZEJ1aWxkZXJDYW5kaWRhdGUodmFyTmFtZSwgZnVsbFBhdGgsIGtpbmQsIHNvdXJjZUZpbGUsIGN1cnJlbnQsIGV4Y2x1ZGVkKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0dGhpcy52YXJpYWJsZVRvVHlwZU1hcC5zZXQodmFyTmFtZSwgZnVsbFBhdGgpO1xuXHRcdFx0XHRcdHRoaXMudHJhY2tGaWxlR3JhcGhCaW5kaW5nKHZhck5hbWUsIGZ1bGxQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm47XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEEgYC5kZWZpbmUoLi4uKWAgaG9wIHdyYXBwZWQgYnkgYW5vdGhlciBgLmRlZmluZSguLi4pYCBjYWxsIGlzIG5vdFxuXHQgKiB0aGUgdmFsdWUgaXRzIGNvbnN0IGVuZHMgdXAgaG9sZGluZyDigJQgdGhlIE9VVEVSTU9TVCBob3Agb2YgdGhlXG5cdCAqIGluaXRpYWxpemVyIGNoYWluIGlzIChkZWZpbmUoKSByZXR1cm5zIHRoZSBkZWZpbmVkIHR5cGUnc1xuXHQgKiBjb25zdHJ1Y3RvcikuIE9ubHkgdGhlIG91dGVybW9zdCBob3AgbWF5IGJpbmQgdGhlIHZhcmlhYmxlLlxuXHQgKi9cblx0cHJpdmF0ZSBpc0RlZXBlckRlZmluZUhvcCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBib29sZWFuIHtcblx0XHRjb25zdCB7IHBhcmVudCB9ID0gY2FsbDtcblx0XHRjb25zdCBkZWVwZXIgPSAhIXBhcmVudCAmJlxuXHRcdFx0dHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ocGFyZW50KSAmJlxuXHRcdFx0cGFyZW50Lm5hbWUudGV4dCA9PT0gJ2RlZmluZScgJiZcblx0XHRcdHRzLmlzQ2FsbEV4cHJlc3Npb24ocGFyZW50LnBhcmVudCkgJiZcblx0XHRcdHBhcmVudC5wYXJlbnQuZXhwcmVzc2lvbiA9PT0gcGFyZW50O1xuXHRcdHJldHVybiBkZWVwZXI7XG5cdH1cblxuXHQvKipcblx0ICogTWlycm9yIGEgdmFyaWFibGUgLT4gbW5lbW9uaWNhIGZ1bGxQYXRoIGJpbmRpbmcgaW50byB0aGUgcGVyLWZpbGVcblx0ICogdmFsdWUtc2NvcGUgbWFwIChncmFwaCBpZGVudGl0eSBsYXc6IGB0eXBlb2YgWGAgYW5kIGJhcmUgcmVmZXJlbmNlc1xuXHQgKiByZXNvbHZlIHRocm91Z2ggdGhlIGZpbGUncyBvd24gYmluZGluZ3MgZmlyc3QpLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja0ZpbGVHcmFwaEJpbmRpbmcgKHZhck5hbWU6IHN0cmluZywgZnVsbFBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGxldCBiaW5kaW5ncyA9IHRoaXMuZmlsZUdyYXBoQmluZGluZ3MuZ2V0KGZpbGVQYXRoKTtcblx0XHRpZiAoIWJpbmRpbmdzKSB7XG5cdFx0XHRiaW5kaW5ncyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHR0aGlzLmZpbGVHcmFwaEJpbmRpbmdzLnNldChmaWxlUGF0aCwgYmluZGluZ3MpO1xuXHRcdH1cblx0XHRiaW5kaW5ncy5zZXQodmFyTmFtZSwgZnVsbFBhdGgpO1xuXHR9XG5cdFxuXHQvKipcblx0XHQqIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnRzIGZyb20gbG9va3VwKCkgY2FsbHNcblx0XHQqIGUuZy4sIGNvbnN0IFNlbnRpZW5jZUNvbnN0cnVjdG9yID0gbG9va3VwKCdTZW50aWVuY2UnKSBtYXBzIFwiU2VudGllbmNlQ29uc3RydWN0b3JcIiAtPiBcIlNlbnRpZW5jZVwiXG5cdFx0Ki9cblx0cHJpdmF0ZSB0cmFja0xvb2t1cEFzc2lnbm1lbnQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLCB0eXBlUGF0aDogc3RyaW5nKTogdm9pZCB7XG5cdFx0dGhpcy5iaW5kUmVzdWx0VmFyaWFibGUoY2FsbCwgdHlwZVBhdGgpO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50cyBmcm9tIG5ldyBUeXBlKCkgY2FsbHNcblx0XHQqIGUuZy4sIGNvbnN0IHVzZXIgPSBuZXcgVXNlclR5cGUoKSBtYXBzIFwidXNlclwiIC0+IFwiVXNlclR5cGVcIlxuXHRcdCovXG5cdHByaXZhdGUgdHJhY2tOZXdBc3NpZ25tZW50IChuZXdFeHByOiB0cy5OZXdFeHByZXNzaW9uLCB0eXBlUGF0aDogc3RyaW5nKTogdm9pZCB7XG5cdFx0bGV0IGVmZmVjdGl2ZVBhdGggPSB0eXBlUGF0aDtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5ld0V4cHIucGFyZW50O1xuXHRcdC8vIENoYWluLWZvcm0gY29uc3RydWN0aW9uOiBuZXcgUigpLkEoKS5CKCkg4oCUIHRoZSByZXN1bHQgdmFyaWFibGVcblx0XHQvLyBob2xkcyB0aGUgT1VURVJNT1NUIHRpcCdzIGluc3RhbmNlIChhd2FpdC10cmFuc3BhcmVudCksIG5vdCB0aGVcblx0XHQvLyBpbm5lciBuZXcncyB0eXBlLiBXYWxrIHRoZSBjaGFpbiwga2VlcGluZyB0aGUgbGFzdCByZXNvbHZhYmxlIHRpcC5cblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGN1cnJlbnQpICYmXG5cdFx0XHRcdHRzLmlzQ2FsbEV4cHJlc3Npb24oY3VycmVudC5wYXJlbnQpICYmXG5cdFx0XHRcdGN1cnJlbnQucGFyZW50LmV4cHJlc3Npb24gPT09IGN1cnJlbnQpIHtcblx0XHRcdFx0Y29uc3QgdGlwID0gdGhpcy5yZXNvbHZlQ2hhaW5UaXBUeXBlUGF0aChjdXJyZW50LnBhcmVudCk7XG5cdFx0XHRcdGlmICh0aXApIHtcblx0XHRcdFx0XHRlZmZlY3RpdmVQYXRoID0gdGlwO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudC5wYXJlbnQ7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0YnJlYWs7XG5cdFx0fVxuXHRcdHRoaXMuYmluZFJlc3VsdFZhcmlhYmxlKG5ld0V4cHIsIGVmZmVjdGl2ZVBhdGgpO1xuXHR9XG5cblx0LyoqXG5cdCAqIEJpbmQgdGhlIG5lYXJlc3QgZW5jbG9zaW5nIGBjb25zdC9sZXQvdmFyIFggPSDigKZgIHRvIGEgbW5lbW9uaWNhXG5cdCAqIGZ1bGxQYXRoIOKAlCB0aGUgc2hhcmVkIHJlc3VsdC12YXJpYWJsZSB3YWxrZXIgYmVoaW5kIG5ldy9sb29rdXAvXG5cdCAqIGNoYWluL2ZvcmsvbWVyZ2UvY2FsbCB0cmFja2luZyAodmFsdWUgc2NvcGU6IGRvd25zdHJlYW0gcmVmZXJlbmNlc1xuXHQgKiBhbmQgYHRoaXMueCA9IHhgIGFzc2lnbm1lbnRzIHJlc29sdmUgdGhyb3VnaCB0aGUgc2FtZSBiaW5kaW5nKS5cblx0ICovXG5cdHByaXZhdGUgYmluZFJlc3VsdFZhcmlhYmxlIChmcm9tOiB0cy5Ob2RlLCB0eXBlUGF0aDogc3RyaW5nKTogdm9pZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBmcm9tLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihjdXJyZW50KSkge1xuXHRcdFx0XHQvLyBGb3VuZDogY29uc3QgWCA9IDxjb25zdHJ1Y3Rpb24+XG5cdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudC5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHZhck5hbWUgPSBjdXJyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0XHR0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLnNldCh2YXJOYW1lLCB0eXBlUGF0aCk7XG5cdFx0XHRcdFx0dGhpcy50cmFja0ZpbGVHcmFwaEJpbmRpbmcodmFyTmFtZSwgdHlwZVBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdC8vIFNjb3BlIGJvdW5kYXJ5OiBhIGNvbnN0cnVjdGlvbiBpbnNpZGUgYSBuZXN0ZWQgY2xhc3MvZnVuY3Rpb25cblx0XHRcdC8vIGJvZHkgZG9lcyBub3QgYmluZCB0aGUgb3V0ZXIgdmFyaWFibGUg4oCUXG5cdFx0XHQvLyBgY29uc3QgWCA9IGRlZmluZSgnWCcsIGNsYXNzIHsgbSA9IG5ldyBNYXAoKSB9KWAgaG9sZHMgdGhlXG5cdFx0XHQvLyBkZWZpbmVkIGNvbnN0cnVjdG9yLCBub3QgYSBNYXAuIFdpdGhvdXQgdGhpcyBzdG9wIHRoZSBjbGFzcy1ib2R5XG5cdFx0XHQvLyBpbnN0YW50aWF0aW9uIGNsb2JiZXJzIFgncyBiaW5kaW5nIGFuZCBhIGxhdGVyIFguZGVmaW5lKCdDaGlsZCcpXG5cdFx0XHQvLyBsb3NlcyBpdHMgcGFyZW50ICh0aGUgY2hpbGQgbGFuZHMgYXMgYSBiYXJlIGRlZmF1bHQtY29sbGVjdGlvblxuXHRcdFx0Ly8gcm9vdCDigJQgZmF0YWwgZm9yIGN1c3RvbSBjb2xsZWN0aW9ucywgd2hvc2UgZnVsbFBhdGhzIHRoZVxuXHRcdFx0Ly8gbmFtZS1vbmx5IGZhbGxiYWNrIGNhbm5vdCBzZWUpLlxuXHRcdFx0aWYgKHRzLmlzQ2xhc3NMaWtlKGN1cnJlbnQpIHx8IHRzLmlzRnVuY3Rpb25MaWtlKGN1cnJlbnQpKSB7XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGFuIGBpbnN0YW50aWF0aW9uYCB1c2FnZSBmb3IgYSBjb25zdHJ1Y3Rpb24tc2hhcGUgY2FsbFxuXHQgKiAoY2hhaW4gdGlwIC8gY2FsbCAvIGFwcGx5IC8gZm9yayAvIGNsb25lIC8gbWVyZ2Ug4oCUXG5cdCAqIGJ5dGUtaW5kaXN0aW5ndWlzaGFibGUgZnJvbSBgbmV3YCB1bnRpbCB0aGUgZGVmZXJyZWRcblx0ICogbWVjaGFuaXNtLWtpbmQgcmV2aXNpb24pLiBgY29uc3RydWN0b3JUZXh0YCBkZWZhdWx0cyB0byB0aGUgY2FsbGVlXG5cdCAqIGV4cHJlc3Npb24gdGV4dCBzbyB0aGUgc2l0ZSBzdGF5cyByZWFkYWJsZSB3aXRob3V0IG5ldyBmaWVsZHM7XG5cdCAqIGNhbGwvYXBwbHkgb3ZlcnJpZGUgaXQgd2l0aCB0aGUgQ3RvciBhcmd1bWVudCB0ZXh0LlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZSAoXG5cdFx0Y2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0dHlwZVBhdGg6IHN0cmluZyxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdGNvbnN0cnVjdG9yVGV4dD86IHN0cmluZ1xuXHQpOiB2b2lkIHtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0Y2FsbC5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgY3RvclRleHQgPSBjb25zdHJ1Y3RvclRleHQgPz8gY2FsbC5leHByZXNzaW9uLmdldFRleHQoc291cmNlRmlsZSk7XG5cdFx0dGhpcy5hZGRVc2FnZSh0eXBlUGF0aCwge1xuXHRcdFx0bG9jYXRpb24gICAgICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRraW5kICAgICAgICAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRjb2RlICAgICAgICAgICAgOiBjYWxsLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdGNvbnN0cnVjdG9yVGV4dCA6IGN0b3JUZXh0LnNsaWNlKDAsIDEwMCksXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0aGUgdHlwZSBhIGNvbnN0cnVjdGlvbi1jaGFpbiB0aXAgY2FsbCBjb25zdHJ1Y3RzOlxuXHQgKiBgbmV3IFIoLi4uKS5BKC4uLilgIGNvbnN0cnVjdHMgUi5BOyBgYXdhaXQgbmV3IFIoLi4uKS5BKC4uLikuQiguLi4pYFxuXHQgKiBjb25zdHJ1Y3RzIFIuQS5CLiBUaGUgcmVjZWl2ZXIgaXMgdGhlIG5lc3RlZCBjaGFpbiAoTmV3RXhwcmVzc2lvblxuXHQgKiBiYXNlLCB0aGVuIHRpcCBjYWxscyk7IGV4YWN0IGZ1bGxQYXRoIGZpcnN0LCBhbmQgb25seSB3aGVuIHRoZSByb290XG5cdCAqIGl0c2VsZiBpcyB1bmtub3duIGRvZXMgdGhlIHByb3AtbmFtZSBmYWxsYmFjayBsYXcgYXBwbHkgKHNvIHBsYWluXG5cdCAqIG1ldGhvZCBjYWxscyBvbiBmcmVzaCBpbnN0YW5jZXMgbmV2ZXIgcmVjb3JkIGEgY29uc3RydWN0aW9uKS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUNoYWluVGlwVHlwZVBhdGggKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIXRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlY2VpdmVyID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGxldCByb290UGF0aDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdGlmICh0cy5pc05ld0V4cHJlc3Npb24ocmVjZWl2ZXIuZXhwcmVzc2lvbikpIHtcblx0XHRcdGNvbnN0IGlubmVyID0gcmVjZWl2ZXIuZXhwcmVzc2lvbjtcblx0XHRcdHJvb3RQYXRoID0gdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oaW5uZXIuZXhwcmVzc2lvbilcblx0XHRcdFx0PyB0aGlzLnJlc29sdmVUeXBlUGF0aChpbm5lci5leHByZXNzaW9uKVxuXHRcdFx0XHQ6IHRoaXMuZ2V0VHlwZU5hbWVGcm9tRXhwcmVzc2lvbihpbm5lci5leHByZXNzaW9uKTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24ocmVjZWl2ZXIuZXhwcmVzc2lvbikpIHtcblx0XHRcdHJvb3RQYXRoID0gdGhpcy5yZXNvbHZlQ2hhaW5UaXBUeXBlUGF0aChyZWNlaXZlci5leHByZXNzaW9uKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0aWYgKCFyb290UGF0aCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgY2FuZGlkYXRlID0gYCR7cm9vdFBhdGh9LiR7cmVjZWl2ZXIubmFtZS50ZXh0fWA7XG5cdFx0aWYgKHRoaXMuZGVmaW5pdGlvbnMuaGFzKGNhbmRpZGF0ZSkpIHtcblx0XHRcdHJldHVybiBjYW5kaWRhdGU7XG5cdFx0fVxuXHRcdGlmICghdGhpcy5kZWZpbml0aW9ucy5oYXMocm9vdFBhdGgpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5yZXNvbHZlVHlwZVBhdGgocmVjZWl2ZXIpO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFRydWUgd2hlbiBgZXhwcmAgZGVub3RlcyBhIGNvbnN0cnVjdGlvbiBmdW5jdGlvbiBpbXBvcnRlZCBmcm9tXG5cdCAqICdtbmVtb25pY2EnIOKAlCB0aGUgbmFtZWQtaW1wb3J0IGZvcm0gKGBpbXBvcnQgeyBjYWxsIH0gZnJvbVxuXHQgKiAnbW5lbW9uaWNhJ2AsIGFsaWFzZXMgaW5jbHVkZWQpIG9yIGEgbWVtYmVyIG9mIGEgdHJhY2tlZFxuXHQgKiBtb2R1bGUtb2JqZWN0IGFsaWFzIChgbW5lbW9uaWNhLmNhbGxgKS4gVXNlcmxhbmQgY2FsbC9hcHBseS9iaW5kXG5cdCAqIGZ1bmN0aW9ucyBuZXZlciBtYXRjaC5cblx0ICovXG5cdHByaXZhdGUgaXNNbmVtb25pY2FDb25zdHJ1Y3Rpb25GbiAoZXhwcjogdHMuRXhwcmVzc2lvbiwgZm46ICdjYWxsJyB8ICdhcHBseScgfCAnYmluZCcpOiBib29sZWFuIHtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMubW5lbW9uaWNhTmFtZWRJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQoZXhwci50ZXh0KTtcblx0XHRcdGNvbnN0IG1hdGNoZWQgPSBpbXBvcnRlZCA9PT0gZm47XG5cdFx0XHRyZXR1cm4gbWF0Y2hlZDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpICYmIGV4cHIubmFtZS50ZXh0ID09PSBmbikge1xuXHRcdFx0Y29uc3QgbWF0Y2hlZCA9IHRzLmlzSWRlbnRpZmllcihleHByLmV4cHJlc3Npb24pICYmXG5cdFx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhleHByLmV4cHJlc3Npb24udGV4dCk7XG5cdFx0XHRyZXR1cm4gbWF0Y2hlZDtcblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIG1uZW1vbmljYSBjYWxsL2FwcGx5KGVudGl0eSwgQ3RvciwgLi4uKSAvIGJpbmQoZW50aXR5LCBDdG9yKTpcblx0ICogcmVzb2x2ZSB0aGUgQ3RvciBhcmd1bWVudCAoYXJnIDEpIHRvIGEgZ3JhcGggZnVsbFBhdGggdGhyb3VnaCB0aGVcblx0ICogc2FtZSB0aWVycyBhcyB0aGUgYG5ld2AgYnJhbmNoICh2YWx1ZSBzY29wZSBmb3IgaWRlbnRpZmllcnMsXG5cdCAqIGNoYWluIHJlc29sdXRpb24gZm9yIHByb3BlcnR5IGFjY2Vzc2VzKS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUNvbnN0cnVjdGlvbkZuVHlwZVBhdGggKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBjYWxsZWUgPSBjYWxsLmV4cHJlc3Npb247XG5cdFx0Y29uc3QgaXNDYWxsT3JBcHBseSA9IHRoaXMuaXNNbmVtb25pY2FDb25zdHJ1Y3Rpb25GbihjYWxsZWUsICdjYWxsJykgfHxcblx0XHRcdHRoaXMuaXNNbmVtb25pY2FDb25zdHJ1Y3Rpb25GbihjYWxsZWUsICdhcHBseScpO1xuXHRcdGNvbnN0IGlzQmluZCA9IHRoaXMuaXNNbmVtb25pY2FDb25zdHJ1Y3Rpb25GbihjYWxsZWUsICdiaW5kJyk7XG5cdFx0aWYgKCFpc0NhbGxPckFwcGx5ICYmICFpc0JpbmQpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGlmIChjYWxsLmFyZ3VtZW50cy5sZW5ndGggPCAyKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBbICwgY3RvckFyZyBdID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0Y29uc3Qga25vd24gPSB0aGlzLnJlc29sdmVDdG9yQXJnVHlwZVBhdGgoY3RvckFyZyk7XG5cdFx0cmV0dXJuIGtub3duO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYW4gZXhwcmVzc2lvbiBwYXNzZWQgd2hlcmUgYSBjb25zdHJ1Y3RvciBpcyBleHBlY3RlZCAodGhlXG5cdCAqIEN0b3Igb2YgY2FsbC9hcHBseS9iaW5kLCBhIHBsdWdpbiBmYWN0b3J5J3MgY29uc3RydWN0ZWQgdGFyZ2V0KSB0byBhXG5cdCAqIGRlZmluZWQgdHlwZSdzIGZ1bGxQYXRoOiB2YWx1ZSBzY29wZSBmb3IgaWRlbnRpZmllcnMsIGNoYWluXG5cdCAqIHJlc29sdXRpb24gZm9yIHByb3BlcnR5IGFjY2Vzc2VzLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlQ3RvckFyZ1R5cGVQYXRoIChjdG9yQXJnOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgcmVzb2x2ZWQ6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY3RvckFyZykpIHtcblx0XHRcdHJlc29sdmVkID0gdGhpcy5yZXNvbHZlVHlwZVBhdGgoY3RvckFyZyk7XG5cdFx0fSBlbHNlIGlmICh0cy5pc0lkZW50aWZpZXIoY3RvckFyZykpIHtcblx0XHRcdGNvbnN0IGJvdW5kID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQoY3RvckFyZy50ZXh0KTtcblx0XHRcdGlmIChib3VuZCkge1xuXHRcdFx0XHRyZXNvbHZlZCA9IGJvdW5kO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgZ3JhcGhSZXN1bHQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKGN0b3JBcmcudGV4dCk7XG5cdFx0XHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRcdFx0cmVzb2x2ZWQgPSBncmFwaFJlc3VsdC5ub2RlLmZ1bGxQYXRoO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGNvbnN0IGtub3duID0gcmVzb2x2ZWQgJiYgdGhpcy5kZWZpbml0aW9ucy5oYXMocmVzb2x2ZWQpID8gcmVzb2x2ZWQgOiB1bmRlZmluZWQ7XG5cdFx0cmV0dXJuIGtub3duO1xuXHR9XG5cblx0LyoqXG5cdCAqIGluc3RhbmNlLmZvcmsoLi4uKSAvIGluc3RhbmNlLmNsb25lKC4uLikgb24gYSB0cmFja2VkIHZhcmlhYmxlIOKAlFxuXHQgKiBydW50aW1lIHJldHVybnMgYHRoaXNgLCBzbyB0aGUgcmVzdWx0IGNhcnJpZXMgdGhlIHNvdXJjZSB0eXBlLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRm9ya0xpa2VUeXBlUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgbWV0aG9kID0gY2FsbC5leHByZXNzaW9uLm5hbWUudGV4dDtcblx0XHRpZiAobWV0aG9kICE9PSAnZm9yaycgJiYgbWV0aG9kICE9PSAnY2xvbmUnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZWNlaXZlciA9IGNhbGwuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHJlY2VpdmVyKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQocmVjZWl2ZXIudGV4dCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGcmVlIHV0aWxzIGZvcm1zOiB1dGlscy5tZXJnZShhLCBiLCAuLi4pIChhbHNvIHRoZSBkaXJlY3QgbmFtZWRcblx0ICogaW1wb3J0IGBtZXJnZShhLCBiKWApIGFuZCB0aGUgY3VycmllZCB1dGlscy5mb3JrKGluc3RhbmNlKSguLi4pLlxuXHQgKiBUaGUgcmVzdWx0IGJpbmRzIHRvIGFyZyAwJ3MgdHlwZSDigJQgcnVudGltZSByZXR1cm5zIGEncyBsaW5lYWdlIG92ZXJcblx0ICogYidzIGNvbnRleHQ7IGEncyBmdWxsUGF0aCBpcyB0aGUgaG9uZXN0IGFwcHJveGltYXRpb24gd2l0aGluIHRoZVxuXHQgKiBvdXRwdXQgY29udHJhY3QgKGRvY3VtZW50ZWQgaW4gUkVBRE1FKS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVV0aWxzRm5UeXBlUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGNhbGxlZSA9IGNhbGwuZXhwcmVzc2lvbjtcblx0XHRjb25zdCBpc1V0aWxzT3duZXIgPSAob3duZXI6IHRzLkV4cHJlc3Npb24pOiBib29sZWFuID0+IHtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIob3duZXIpKSB7XG5cdFx0XHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChvd25lci50ZXh0KTtcblx0XHRcdFx0cmV0dXJuIGltcG9ydGVkID09PSAndXRpbHMnO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbWF0Y2hlZCA9IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG93bmVyKSAmJiBvd25lci5uYW1lLnRleHQgPT09ICd1dGlscycgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKG93bmVyLmV4cHJlc3Npb24pICYmIHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhvd25lci5leHByZXNzaW9uLnRleHQpO1xuXHRcdFx0cmV0dXJuIG1hdGNoZWQ7XG5cdFx0fTtcblx0XHRsZXQgc3ViamVjdEFyZzogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZDtcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbGVlKSAmJiBpc1V0aWxzT3duZXIoY2FsbGVlLmV4cHJlc3Npb24pICYmXG5cdFx0XHQoY2FsbGVlLm5hbWUudGV4dCA9PT0gJ21lcmdlJyB8fCBjYWxsZWUubmFtZS50ZXh0ID09PSAnZm9yaycpKSB7XG5cdFx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblx0XHRcdHN1YmplY3RBcmcgPSBmaXJzdEFyZztcblx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihjYWxsZWUpKSB7XG5cdFx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMubW5lbW9uaWNhTmFtZWRJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQoY2FsbGVlLnRleHQpO1xuXHRcdFx0aWYgKGltcG9ydGVkID09PSAnbWVyZ2UnIHx8IGltcG9ydGVkID09PSAnZm9yaycpIHtcblx0XHRcdFx0Y29uc3QgWyBmaXJzdEFyZyBdID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0XHRcdHN1YmplY3RBcmcgPSBmaXJzdEFyZztcblx0XHRcdH1cblx0XHR9IGVsc2UgaWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oY2FsbGVlKSAmJiB0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsZWUuZXhwcmVzc2lvbikgJiZcblx0XHRcdGNhbGxlZS5leHByZXNzaW9uLm5hbWUudGV4dCA9PT0gJ2ZvcmsnICYmIGlzVXRpbHNPd25lcihjYWxsZWUuZXhwcmVzc2lvbi5leHByZXNzaW9uKSkge1xuXHRcdFx0Ly8gdXRpbHMuZm9yayhpbnN0YW5jZSkoLi4uYXJncykg4oCUIHRoZSBjdXJyaWVkIGZvcm1cblx0XHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGNhbGxlZS5hcmd1bWVudHM7XG5cdFx0XHRzdWJqZWN0QXJnID0gZmlyc3RBcmc7XG5cdFx0fVxuXHRcdGlmICghc3ViamVjdEFyZyB8fCAhdHMuaXNJZGVudGlmaWVyKHN1YmplY3RBcmcpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChzdWJqZWN0QXJnLnRleHQpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXG5cdC8qKlxuXHRcdCogUHJvY2VzcyBhIEBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHQgKi9cblx0cHJpdmF0ZSBwcm9jZXNzRGVjb3JhdGVEZWNvcmF0b3IgKFxuXHRcdGRlY29yYXRvcjogdHMuRGVjb3JhdG9yLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0Y2xhc3NEZWNsUGFyYW0/OiB0cy5DbGFzc0RlY2xhcmF0aW9uXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRkZWNvcmF0b3IuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXG5cdFx0Ly8gR2V0IHRoZSBjbGFzcyBkZWNsYXJhdGlvbiAtIHVzZSB0aGUgcGFzc2VkIGNvbnRleHQgaWYgcGFyZW50IGlzIG5vdCBzZXRcblx0XHRjb25zdCBjbGFzc0RlY2wgPSBkZWNvcmF0b3IucGFyZW50IGFzIHRzLkNsYXNzRGVjbGFyYXRpb24gfCB1bmRlZmluZWQgfHwgY2xhc3NEZWNsUGFyYW07XG5cdFx0aWYgKCFjbGFzc0RlY2wgfHwgIWNsYXNzRGVjbC5uYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdEZWNvcmF0ZWQgY2xhc3MgaGFzIG5vIG5hbWUnLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHR5cGVOYW1lID0gY2xhc3NEZWNsLm5hbWUudGV4dDtcblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdEZWNvcmF0ZWQgY2xhc3MgaGFzIG5vIG5hbWUnLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFBhcnNlIGRlY29yYXRvciBhcmd1bWVudHM6IEBkZWNvcmF0ZSgpLCBAZGVjb3JhdGUoUGFyZW50KSxcblx0XHQvLyBAZGVjb3JhdGUoeyAuLi4gfSksIEBkZWNvcmF0ZShQYXJlbnQsIHsgLi4uIH0pLFxuXHRcdC8vIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSwgQE15Q29sbGVjdGlvbi5kZWNvcmF0ZSh7IC4uLiB9KVxuXHRcdGxldCBwYXJlbnROb2RlOiBUeXBlTm9kZSB8IHVuZGVmaW5lZDtcblx0XHRsZXQgcGFyZW50RnVsbFBhdGg6IHN0cmluZyB8IG51bGwgPSBudWxsO1xuXHRcdGxldCBjb2xsZWN0aW9uSWQ6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRsZXQgZGVjb3JhdG9yQ29uZmlnOiB7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0gPSB7fTtcblxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGRlY29yYXRvci5leHByZXNzaW9uKSkge1xuXHRcdFx0Y29uc3QgY2FsbEV4cHIgPSBkZWNvcmF0b3IuZXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IGNhbGxlZSA9IGNhbGxFeHByLmV4cHJlc3Npb247XG5cblx0XHRcdC8vIENoZWNrIGZvciBATXlDb2xsZWN0aW9uLmRlY29yYXRlKCkgd2hlcmUgTXlDb2xsZWN0aW9uIGlzIGEgY3VzdG9tIGNvbGxlY3Rpb24uXG5cdFx0XHQvLyBUaGUgZGVjb3JhdGVkIGNsYXNzIGJlY29tZXMgYSByb290IHR5cGUgaW4gdGhhdCBjb2xsZWN0aW9uLlxuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsZWUpICYmXG5cdFx0XHRcdGNhbGxlZS5uYW1lLnRleHQgPT09ICdkZWNvcmF0ZScgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGNhbGxlZS5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGNhbGxlZS5leHByZXNzaW9uLnRleHQpXG5cdFx0XHQpIHtcblx0XHRcdFx0Y29sbGVjdGlvbklkID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChjYWxsZWUuZXhwcmVzc2lvbi50ZXh0KTtcblx0XHRcdFx0aWYgKGNhbGxFeHByLmFyZ3VtZW50cy5sZW5ndGggPT09IDEgJiYgdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihjYWxsRXhwci5hcmd1bWVudHNbIDAgXSkpIHtcblx0XHRcdFx0XHRkZWNvcmF0b3JDb25maWcgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjYWxsRXhwci5hcmd1bWVudHNbIDAgXSk7XG5cdFx0XHRcdH1cblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGNvbnN0IGFyZ3MgPSBjYWxsRXhwci5hcmd1bWVudHM7XG5cdFx0XHRcdGxldCBwYXJlbnRBcmc6IHRzLklkZW50aWZpZXIgfCB1bmRlZmluZWQ7XG5cdFx0XHRcdGxldCBjb25maWdBcmc6IHRzLk9iamVjdExpdGVyYWxFeHByZXNzaW9uIHwgdW5kZWZpbmVkO1xuXG5cdFx0XHRcdGZvciAoY29uc3QgYXJnIG9mIGFyZ3MpIHtcblx0XHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdFx0XHRcdGlmIChwYXJlbnRBcmcpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdFx0XHRcdFx0bWVzc2FnZSA6ICdAZGVjb3JhdGUoKSBhY2NlcHRzIG9ubHkgb25lIHBhcmVudCByZWZlcmVuY2UnLFxuXHRcdFx0XHRcdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0XHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0XHRwYXJlbnRBcmcgPSBhcmc7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdFx0XHRcdGlmIChjb25maWdBcmcpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdFx0XHRcdFx0bWVzc2FnZSA6ICdAZGVjb3JhdGUoKSBhY2NlcHRzIG9ubHkgb25lIGNvbmZpZyBvYmplY3QnLFxuXHRcdFx0XHRcdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0XHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0XHRjb25maWdBcmcgPSBhcmc7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0aWYgKHBhcmVudEFyZykge1xuXHRcdFx0XHRcdHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlJZGVudGlmaWVyKHBhcmVudEFyZy50ZXh0KTtcblx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0XHRcdFx0cGFyZW50RnVsbFBhdGggPSBwYXJlbnROb2RlLmZ1bGxQYXRoO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGlmIChjb25maWdBcmcpIHtcblx0XHRcdFx0XHRkZWNvcmF0b3JDb25maWcgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjb25maWdBcmcpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gQnVpbGQgZnVsbCBwYXRoIOKAlCBhIHJvb3QgZGVjb3JhdGVkIGludG8gYSBjdXN0b20gY29sbGVjdGlvblxuXHRcdC8vIGNhcnJpZXMgdGhlIGNvbGxlY3Rpb25JZDo6IHByZWZpeCwgZXhhY3RseSBsaWtlIHRoZSBncmFwaCBub2RlJ3Ncblx0XHQvLyBmdWxsUGF0aDogZGVmaW5pdGlvbnMuanNvbiBrZXlzIG11c3Qgam9pbiBoaWVyYXJjaHkuanNvbiAodGhlXG5cdFx0Ly8gcHJlZml4IHdhcyBkcm9wcGVkIGhlcmUgYmVmb3JlLCBzbyBhIGRlY29yYXRlZCBjb2xsZWN0aW9uIHJvb3Rcblx0XHQvLyBuZXZlciBqb2luZWQpXG5cdFx0Y29uc3QgZnVsbFBhdGggPSBwYXJlbnROb2RlXG5cdFx0XHQ/IGAke3BhcmVudE5vZGUuZnVsbFBhdGh9LiR7dHlwZU5hbWV9YFxuXHRcdFx0OiBjb2xsZWN0aW9uSWRcblx0XHRcdFx0PyBgJHtjb2xsZWN0aW9uSWR9Ojoke3R5cGVOYW1lfWBcblx0XHRcdFx0OiB0eXBlTmFtZTtcblxuXHRcdC8vIENyZWF0ZSBkZWZpbml0aW9uIGluZm8gZm9yIGRlY29yYXRlXG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IHR5cGVOYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlY29yYXRlJyxcblx0XHRcdHBhcmVudCAgICAgIDogcGFyZW50RnVsbFBhdGgsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IGRlY29yYXRvckNvbmZpZy5zdHJpY3RDaGFpbiA/PyB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBkZWNvcmF0b3JDb25maWcuYmxvY2tFcnJvcnMgPz8gZmFsc2UsXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChmdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdFx0dGhpcy5lZHNTY29wZUJ5Tm9kZS5zZXQoY2xhc3NEZWNsLCBmdWxsUGF0aCk7XG5cblx0XHQvLyBDcmVhdGUgdHlwZSBub2RlXG5cdFx0Y29uc3Qgbm9kZSA9IFR5cGVHcmFwaEltcGwuY3JlYXRlTm9kZShcblx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0cGFyZW50Tm9kZSxcblx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRsaW5lICsgMSxcblx0XHRcdGNoYXJhY3RlciArIDEsXG5cdFx0XHRjb2xsZWN0aW9uSWRcblx0XHQpO1xuXHRcdHRoaXMuYXBwbHlDb2xsZWN0aW9uRW1pc3Npb25JbmZvKG5vZGUsIG5vZGUuY29sbGVjdGlvbklkKTtcblxuXHRcdC8vIFNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZSBkZXRlY3Rpb24gKGhhcmQtZmFpbCBsYXcpXG5cdFx0dGhpcy5yZWNvcmREZWZpbmVTaXRlKFxuXHRcdFx0cGFyZW50Tm9kZSA/IGAke3BhcmVudE5vZGUuZnVsbFBhdGh9LiR7dHlwZU5hbWV9YCA6IGAke2NvbGxlY3Rpb25JZCA/PyAnZGVmYXVsdCd9Ojoke3R5cGVOYW1lfWAsXG5cdFx0XHRgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YFxuXHRcdCk7XG5cblx0XHQvLyBFeHRyYWN0IHByb3BlcnRpZXMgYW5kIGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBjbGFzcyBtZW1iZXJzIOKAlFxuXHRcdC8vIHRoZSBuZXcgbm9kZSBhbmNob3JzIHJlbGF0aXZlLWZpcnN0IGdyYXBoIHJlZmVyZW5jZSByZXNvbHV0aW9uXG5cdFx0Y29uc3QgcHJldmlvdXNBbmNob3IgPSB0aGlzLmN1cnJlbnRHcmFwaEFuY2hvcjtcblx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IG5vZGU7XG5cdFx0dHJ5IHtcblx0XHRcdG5vZGUucHJvcGVydGllcyA9IHRoaXMuZXh0cmFjdENsYXNzUHJvcGVydGllcyhjbGFzc0RlY2wpO1xuXHRcdFx0bm9kZS5jb25zdHJ1Y3RvclBhcmFtcyA9IHRoaXMuZXh0cmFjdENsYXNzQ29uc3RydWN0b3JQYXJhbXMoY2xhc3NEZWNsKTtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBwcmV2aW91c0FuY2hvcjtcblx0XHR9XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGhcblx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChwYXJlbnROb2RlLCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KG5vZGUpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHR5cGUgbmFtZSBmcm9tIGRlZmluZSgpIGNhbGwgYXJndW1lbnRzLlxuXHQgKiBIYW5kbGVzOlxuXHQgKiAgIGRlZmluZSgnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHQgKiAgIGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpICAgLy8gZXhwbGljaXQtc291cmNlIGZvcm1cblx0ICogICBkZWZpbmUoZnVuY3Rpb24gVHlwZU5hbWUoKSB7fSlcblx0ICogICBkZWZpbmUoKCkgPT4gY2xhc3MgVHlwZU5hbWUge30pXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RUeXBlTmFtZSAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGFyZ3MgPSBjYWxsLmFyZ3VtZW50cztcblxuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBhcmdzO1xuXG5cdFx0Ly8gRXhwbGljaXQtc291cmNlIGZvcm06IGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIgJiYgdHMuaXNJZGVudGlmaWVyKGZpcnN0QXJnKSAmJiB0cy5pc1N0cmluZ0xpdGVyYWwoYXJnc1sgMSBdKSkge1xuXHRcdFx0cmV0dXJuIGFyZ3NbIDEgXS50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIFN0cmluZyBsaXRlcmFsOiBkZWZpbmUoJ1R5cGVOYW1lJywgLi4uKVxuXHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoZmlyc3RBcmcpKSB7XG5cdFx0XHRyZXR1cm4gZmlyc3RBcmcudGV4dDtcblx0XHR9XG5cblx0XHQvLyBGdW5jdGlvbiB3aXRoIG5hbWU6IGRlZmluZShmdW5jdGlvbiBUeXBlTmFtZSgpIHt9KVxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihmaXJzdEFyZykgJiYgZmlyc3RBcmcubmFtZSkge1xuXHRcdFx0cmV0dXJuIGZpcnN0QXJnLm5hbWUudGV4dDtcblx0XHR9XG5cblx0XHQvLyBBcnJvdyBmdW5jdGlvbiByZXR1cm5pbmcgY2xhc3M6IGRlZmluZSgoKSA9PiBjbGFzcyBUeXBlTmFtZSB7fSlcblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGZpcnN0QXJnKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBmaXJzdEFyZztcblx0XHRcdGlmICh0cy5pc0NsYXNzRXhwcmVzc2lvbihib2R5KSAmJiBib2R5Lm5hbWUpIHtcblx0XHRcdFx0cmV0dXJuIGJvZHkubmFtZS50ZXh0O1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGNvbXB1dGVkIGRlZmluZSBuYW1lIG9ubHkgd2hlbiBpdCByYW5nZXMgb3ZlciBhIGNsb3NlZCBjb25zdFxuXHQgKiBvYmplY3Qga2V5IHNldC4gQXJiaXRyYXJ5IHN0cmluZ3MgYW5kIHVucmVzb2x2ZWQgdW5pb25zIHN0YXkgb24gdGhlXG5cdCAqIGV4aXN0aW5nIHdhcm5pbmctYW5kLXNraXAgcGF0aC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENvbXB1dGVkVHlwZU5hbWVzIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZ1tdIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblx0XHRpZiAoIWZpcnN0QXJnIHx8ICF0cy5pc0lkZW50aWZpZXIoZmlyc3RBcmcpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBsb29wTmFtZXMgPSB0aGlzLnJlc29sdmVMb29wS2V5TmFtZXMoZmlyc3RBcmcpO1xuXHRcdGlmIChsb29wTmFtZXMgIT09IHVuZGVmaW5lZCkge1xuXHRcdFx0cmV0dXJuIGxvb3BOYW1lcztcblx0XHR9XG5cdFx0Y29uc3QgcGFyYW1ldGVyTmFtZXMgPSB0aGlzLnJlc29sdmVQYXJhbWV0ZXJLZXlOYW1lcyhmaXJzdEFyZywgY2FsbC5nZXRTb3VyY2VGaWxlKCkpO1xuXHRcdHJldHVybiBwYXJhbWV0ZXJOYW1lcztcblx0fVxuXG5cdHByaXZhdGUgcmVzb2x2ZUxvb3BLZXlOYW1lcyAobmFtZTogdHMuSWRlbnRpZmllcik6IHN0cmluZ1tdIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5hbWUucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNGb3JPZlN0YXRlbWVudChjdXJyZW50KSAmJiB0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb25MaXN0KGN1cnJlbnQuaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRcdGNvbnN0IGRlY2xhcmF0aW9uID0gY3VycmVudC5pbml0aWFsaXplci5kZWNsYXJhdGlvbnMuZmluZChjYW5kaWRhdGUgPT5cblx0XHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoY2FuZGlkYXRlLm5hbWUpICYmIGNhbmRpZGF0ZS5uYW1lLnRleHQgPT09IG5hbWUudGV4dCk7XG5cdFx0XHRcdGlmIChkZWNsYXJhdGlvbikge1xuXHRcdFx0XHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMucmVzb2x2ZU9iamVjdEtleXNDYWxsKGN1cnJlbnQuZXhwcmVzc2lvbiwgY3VycmVudC5nZXRTb3VyY2VGaWxlKCkpO1xuXHRcdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdHByaXZhdGUgcmVzb2x2ZU9iamVjdEtleXNDYWxsIChleHByZXNzaW9uOiB0cy5FeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogc3RyaW5nW10gfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihleHByZXNzaW9uKSB8fCAhdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcmVzc2lvbi5leHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgYWNjZXNzID0gZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdGNvbnN0IFsgYXJndW1lbnQgXSA9IGV4cHJlc3Npb24uYXJndW1lbnRzO1xuXHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGFjY2Vzcy5leHByZXNzaW9uKSB8fCBhY2Nlc3MuZXhwcmVzc2lvbi50ZXh0ICE9PSAnT2JqZWN0JyB8fFxuXHRcdFx0YWNjZXNzLm5hbWUudGV4dCAhPT0gJ2tleXMnIHx8ICFhcmd1bWVudCB8fCAhdHMuaXNJZGVudGlmaWVyKGFyZ3VtZW50KSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5yZXNvbHZlQ29uc3RPYmplY3RLZXlzKGFyZ3VtZW50LnRleHQsIHNvdXJjZUZpbGUpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHRwcml2YXRlIHJlc29sdmVQYXJhbWV0ZXJLZXlOYW1lcyAobmFtZTogdHMuSWRlbnRpZmllciwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHN0cmluZ1tdIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5hbWUucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNGdW5jdGlvbkxpa2UoY3VycmVudCkpIHtcblx0XHRcdFx0Y29uc3QgcGFyYW1ldGVyID0gY3VycmVudC5wYXJhbWV0ZXJzLmZpbmQoY2FuZGlkYXRlID0+XG5cdFx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGNhbmRpZGF0ZS5uYW1lKSAmJiBjYW5kaWRhdGUubmFtZS50ZXh0ID09PSBuYW1lLnRleHQpO1xuXHRcdFx0XHRpZiAocGFyYW1ldGVyKSB7XG5cdFx0XHRcdFx0aWYgKCFwYXJhbWV0ZXIudHlwZSkge1xuXHRcdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5yZXNvbHZlS2V5b2ZUeXBlKHBhcmFtZXRlci50eXBlLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHRwcml2YXRlIHJlc29sdmVLZXlvZlR5cGUgKHR5cGVOb2RlOiB0cy5UeXBlTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHN0cmluZ1tdIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNQYXJlbnRoZXNpemVkVHlwZU5vZGUodHlwZU5vZGUpKSB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnJlc29sdmVLZXlvZlR5cGUodHlwZU5vZGUudHlwZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH1cblx0XHRpZiAodHMuaXNUeXBlT3BlcmF0b3JOb2RlKHR5cGVOb2RlKSAmJiB0eXBlTm9kZS5vcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5LZXlPZktleXdvcmQpIHtcblx0XHRcdGNvbnN0IHF1ZXJpZWQgPSB0eXBlTm9kZS50eXBlO1xuXHRcdFx0aWYgKHRzLmlzVHlwZVF1ZXJ5Tm9kZShxdWVyaWVkKSAmJiB0cy5pc0lkZW50aWZpZXIocXVlcmllZC5leHByTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5yZXNvbHZlQ29uc3RPYmplY3RLZXlzKHF1ZXJpZWQuZXhwck5hbWUudGV4dCwgc291cmNlRmlsZSk7XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZSh0eXBlTm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKHR5cGVOb2RlLnR5cGVOYW1lKSkge1xuXHRcdFx0Y29uc3QgcmVmZXJlbmNlZE5hbWUgPSB0eXBlTm9kZS50eXBlTmFtZS50ZXh0O1xuXHRcdFx0Y29uc3QgYWxpYXMgPSBzb3VyY2VGaWxlLnN0YXRlbWVudHMuZmluZCgoc3RhdGVtZW50KTogc3RhdGVtZW50IGlzIHRzLlR5cGVBbGlhc0RlY2xhcmF0aW9uID0+XG5cdFx0XHRcdHRzLmlzVHlwZUFsaWFzRGVjbGFyYXRpb24oc3RhdGVtZW50KSAmJiBzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSByZWZlcmVuY2VkTmFtZSk7XG5cdFx0XHRpZiAoYWxpYXMpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5yZXNvbHZlS2V5b2ZUeXBlKGFsaWFzLnR5cGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0cHJpdmF0ZSByZXNvbHZlQ29uc3RPYmplY3RLZXlzIChuYW1lOiBzdHJpbmcsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiBzdHJpbmdbXSB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc291cmNlRmlsZS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAoIXRzLmlzVmFyaWFibGVTdGF0ZW1lbnQoc3RhdGVtZW50KSB8fFxuXHRcdFx0XHQoc3RhdGVtZW50LmRlY2xhcmF0aW9uTGlzdC5mbGFncyAmIHRzLk5vZGVGbGFncy5Db25zdCkgPT09IDApIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGRlY2xhcmF0aW9uIG9mIHN0YXRlbWVudC5kZWNsYXJhdGlvbkxpc3QuZGVjbGFyYXRpb25zKSB7XG5cdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGRlY2xhcmF0aW9uLm5hbWUpIHx8IGRlY2xhcmF0aW9uLm5hbWUudGV4dCAhPT0gbmFtZSB8fFxuXHRcdFx0XHRcdCFkZWNsYXJhdGlvbi5pbml0aWFsaXplciB8fCAhdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihkZWNsYXJhdGlvbi5pbml0aWFsaXplcikpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBuYW1lczogc3RyaW5nW10gPSBbXTtcblx0XHRcdFx0Zm9yIChjb25zdCBwcm9wZXJ0eSBvZiBkZWNsYXJhdGlvbi5pbml0aWFsaXplci5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdFx0aWYgKCF0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wZXJ0eSkgfHxcblx0XHRcdFx0XHRcdCghdHMuaXNJZGVudGlmaWVyKHByb3BlcnR5Lm5hbWUpICYmICF0cy5pc1N0cmluZ0xpdGVyYWwocHJvcGVydHkubmFtZSkpKSB7XG5cdFx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRuYW1lcy5wdXNoKHByb3BlcnR5Lm5hbWUudGV4dCk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIG5hbWVzO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdGhlIGZ1bGwgZGVmaW5lKCkgY2FsbCBjb250ZXh0OiB0eXBlIG5hbWUsIHBhcmVudCB0eXBlLCBhbmQgY29sbGVjdGlvbi5cblx0ICogSGFuZGxlcyBkaXJlY3QgY2FsbHMsIHByb3BlcnR5LWFjY2VzcyBjYWxscywgY2hhaW5lZCBjYWxscywgYW5kIHRoZVxuXHQgKiBleHBsaWNpdC1zb3VyY2UgZm9ybSBgZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilgLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0RGVmaW5lQ29udGV4dCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHR5cGVOYW1lT3ZlcnJpZGU/OiBzdHJpbmcpOiB7XG5cdFx0dHlwZU5hbWU/OiBzdHJpbmc7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Y29uc3QgdHlwZU5hbWUgPSB0eXBlTmFtZU92ZXJyaWRlID8/IHRoaXMuZXh0cmFjdFR5cGVOYW1lKGNhbGwpO1xuXHRcdGlmICghdHlwZU5hbWUpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IGNhbGw7XG5cblx0XHQvLyBEaXJlY3QgY2FsbDogZGVmaW5lKCdUeXBlTmFtZScsIC4uLikgb3IgZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2RlZmluZScpIHtcblx0XHRcdC8vIEV4cGxpY2l0LXNvdXJjZSBmb3JtOiBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHRcdFx0aWYgKGNhbGwuYXJndW1lbnRzLmxlbmd0aCA+PSAyICYmIHRzLmlzSWRlbnRpZmllcihjYWxsLmFyZ3VtZW50c1sgMCBdKSkge1xuXHRcdFx0XHRjb25zdCBzb3VyY2VOYW1lID0gY2FsbC5hcmd1bWVudHNbIDAgXS50ZXh0O1xuXHRcdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKHNvdXJjZU5hbWUpO1xuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0XHRcdHBhcmVudFR5cGUgICA6IHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSxcblx0XHRcdFx0XHRjb2xsZWN0aW9uSWQgOiBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCxcblx0XHRcdFx0fTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gUGxhaW4gcm9vdCBkZWZpbmUgaW4gZGVmYXVsdCBjb2xsZWN0aW9uXG5cdFx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2VzczogWC5kZWZpbmUoJ1R5cGVOYW1lJywgLi4uKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLm5hbWUudGV4dCA9PT0gJ2RlZmluZScpIHtcblx0XHRcdGNvbnN0IG9iaiA9IGV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblxuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihvYmopKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uob2JqLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0XHRcdHBhcmVudFR5cGUgICA6IHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSxcblx0XHRcdFx0XHRjb2xsZWN0aW9uSWQgOiBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCxcblx0XHRcdFx0fTtcblx0XHRcdH1cblxuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gTmVzdGVkIGFjY2VzczogaW5zdGFuY2UuVHlwZS5kZWZpbmUgLSB0cnkgdG8gcmVzb2x2ZVxuXHRcdFx0XHRjb25zdCBjaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlDaGFpbihvYmopO1xuXHRcdFx0XHRpZiAoY2hhaW4ubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGNoYWluLmpvaW4oJy4nKSk7XG5cdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlIH07XG5cdFx0XHRcdH1cblx0XHRcdH1cblxuXHRcdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBEZXRlcm1pbmUgdGhlIGNvbGxlY3Rpb24gY29udGV4dCBmcm9tIHRoZSByb290IG9mIHRoZSBjaGFpbiBzbyB0aGF0XG5cdFx0XHRcdC8vIGN1c3RvbS1jb2xsZWN0aW9uIHR5cGVzIGRvIG5vdCBnZXQgY29uZnVzZWQgd2l0aCBkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMuXG5cdFx0XHRcdGNvbnN0IHJvb3RJZCA9IHRoaXMuZ2V0Um9vdElkZW50aWZpZXIob2JqLmV4cHJlc3Npb24pO1xuXHRcdFx0XHRjb25zdCBleHBlY3RlZENvbGxlY3Rpb25JZCA9IHJvb3RJZFxuXHRcdFx0XHRcdD8gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKHJvb3RJZC50ZXh0KS5jb2xsZWN0aW9uSWRcblx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblxuXHRcdFx0XHQvLyBDaGFpbmVkIGNhbGw6IGRlZmluZSgnQScpLmRlZmluZSgnQicpIG9yIG1uZW1vbmljYS5kZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKVxuXHRcdFx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwob2JqKSkge1xuXHRcdFx0XHRcdHRoaXMucHJvY2Vzc0RlZmluZUNhbGwob2JqLCBjYWxsLmdldFNvdXJjZUZpbGUoKSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdC8vIEluaGVyaXQgY29sbGVjdGlvbiBmcm9tIHRoZSBwYXJlbnQgdHlwZSAoaWYgYW55KVxuXHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBDaGFpbmVkIGxhenkgY2FsbDogbGF6eSgnQScpLmRlZmluZSgnQicpIG9yIFR5cGUubGF6eSgnQScpLmRlZmluZSgnQicpXG5cdFx0XHRcdGlmICh0aGlzLmlzTGF6eUNhbGwob2JqKSkge1xuXHRcdFx0XHRcdHRoaXMucHJvY2Vzc0xhenlDYWxsKG9iaiwgY2FsbC5nZXRTb3VyY2VGaWxlKCkpO1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudFR5cGVOYW1lID0gdGhpcy5leHRyYWN0TW5lbW9uaWNhVHlwZU5hbWUob2JqKTtcblx0XHRcdFx0XHRpZiAocGFyZW50VHlwZU5hbWUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKHBhcmVudFR5cGVOYW1lLCBleHBlY3RlZENvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIEJ1aWxkZXIgbG9va3VwIGNoYWluOiBBcHAubG9va3VwKCdVc2VyJykuZGVmaW5lKCdBZG1pbicpXG5cdFx0XHRcdGlmICh0aGlzLmlzTG9va3VwQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0Y29uc3QgbG9va2VkVXBQYXRoID0gdGhpcy5yZXNvbHZlTG9va3VwUGF0aChvYmopO1xuXHRcdFx0XHRcdGlmIChsb29rZWRVcFBhdGgpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGxvb2tlZFVwUGF0aCk7XG5cdFx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGUuY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHsgdHlwZU5hbWUgfTtcblx0fVxuXG5cdC8qKlxuXHQgKiBQcmVmaXggYSBkb3R0ZWQgdHlwZSBwYXRoIHdpdGggYSBjb2xsZWN0aW9uIGlkZW50aWZpZXIgc28gY3VzdG9tLWNvbGxlY3Rpb25cblx0ICogdHlwZXMgZG8gbm90IGNvbGxpZGUgd2l0aCBkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMgaW4gdGhlIGdyYXBoLlxuXHQgKi9cblx0cHJpdmF0ZSBwcmVmaXhDb2xsZWN0aW9uUGF0aCAocGF0aDogc3RyaW5nLCBjb2xsZWN0aW9uSWQ6IHN0cmluZyk6IHN0cmluZyB7XG5cdFx0cmV0dXJuIGAke2NvbGxlY3Rpb25JZH06OiR7cGF0aH1gO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSBkZWZpbmUoKSBzb3VyY2UgaWRlbnRpZmllciB0byBlaXRoZXIgYSBwYXJlbnQgdHlwZSwgYSBjb2xsZWN0aW9uLFxuXHQgKiBvciB0aGUgZGVmYXVsdCAobW9kdWxlIG9iamVjdCkgY29sbGVjdGlvbi5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZURlZmluZVNvdXJjZSAoc291cmNlTmFtZTogc3RyaW5nKToge1xuXHRcdHBhcmVudFR5cGU/OiBUeXBlTm9kZTtcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmc7XG5cdH0ge1xuXHRcdC8vIE1vZHVsZSBvYmplY3QgYWxpYXNlcyAtPiByb290IGluIGRlZmF1bHQgY29sbGVjdGlvblxuXHRcdGlmICh0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoc291cmNlTmFtZSkpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHQvLyBDb2xsZWN0aW9uIHZhcmlhYmxlcyAtPiByb290IGluIHRoYXQgY29sbGVjdGlvblxuXHRcdGNvbnN0IGNvbGxlY3Rpb25JZCA9IHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5nZXQoc291cmNlTmFtZSk7XG5cdFx0aWYgKGNvbGxlY3Rpb25JZCkge1xuXHRcdFx0cmV0dXJuIHsgY29sbGVjdGlvbklkIH07XG5cdFx0fVxuXG5cdFx0Ly8gT3RoZXJ3aXNlIHRyZWF0IGFzIGEgdHlwZSB2YXJpYWJsZSByZWZlcmVuY2Vcblx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5SWRlbnRpZmllcihzb3VyY2VOYW1lKTtcblx0XHRyZXR1cm4geyBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdH1cblxuXHQvKipcblx0ICogQ2hlY2sgaWYgYSBjYWxsIGV4cHJlc3Npb24gaXMgYSBsb29rdXAoKSBjYWxsLlxuXHQgKi9cblx0cHJpdmF0ZSBpc0xvb2t1cENhbGwgKG5vZGU6IHRzLkNhbGxFeHByZXNzaW9uKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgZXhwciA9IG5vZGUuZXhwcmVzc2lvbjtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpICYmIGV4cHIudGV4dCA9PT0gJ2xvb2t1cCcpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikgJiYgZXhwci5uYW1lLnRleHQgPT09ICdsb29rdXAnKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSBsb29rdXAoKSBjYWxsIHRvIGEgZG90dGVkIHR5cGUgcGF0aCAoYmVzdCBlZmZvcnQpLlxuXHQgKiBIYW5kbGVzOlxuXHQgKiAgIGxvb2t1cCgnVXNlcicpXG5cdCAqICAgbG9va3VwKHNvdXJjZSwgJ1VzZXInKVxuXHQgKiAgIEFwcC5sb29rdXAoJ1VzZXInKVxuXHQgKiAgIGNvbGxlY3Rpb24ubG9va3VwKCdVc2VyLkFkbWluJylcblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUxvb2t1cFBhdGggKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBhcmdzID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIFNpbmdsZS1hcmcgbG9va3VwOiBsb29rdXAoJ1VzZXInKSBvciBBcHAubG9va3VwKCdVc2VyJylcblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDEpIHtcblx0XHRcdGNvbnN0IFsgYXJnIF0gPSBhcmdzO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChhcmcpIHx8IHRzLmlzTm9TdWJzdGl0dXRpb25UZW1wbGF0ZUxpdGVyYWwoYXJnKSkge1xuXHRcdFx0XHRjb25zdCBwYXRoID0gYXJnLnRleHQ7XG5cdFx0XHRcdC8vIElmIHRoaXMgaXMgYSBtZXRob2QgY2FsbCBvbiBhIHNvdXJjZSwgcmVzb2x2ZSByZWxhdGl2ZSB0byB0aGF0IHNvdXJjZS5cblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRjb25zdCBzb3VyY2VFeHByID0gY2FsbC5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihzb3VyY2VFeHByKSkge1xuXHRcdFx0XHRcdFx0Y29uc3Qgc291cmNlTmFtZSA9IHNvdXJjZUV4cHIudGV4dDtcblx0XHRcdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRcdFx0XHRpZiAoc291cmNlQ29udGV4dC5wYXJlbnRUeXBlKSB7XG5cdFx0XHRcdFx0XHRcdC8vIFR5cGUgbG9va3VwOiByZWxhdGl2ZSBmaXJzdCwgdGhlbiByb290IGZhbGxiYWNrLlxuXHRcdFx0XHRcdFx0XHQvLyBGb3IgYSB0eXBlIGluc2lkZSBhIGN1c3RvbSBjb2xsZWN0aW9uIHRoZSBmYWxsYmFjayByb290IGlzXG5cdFx0XHRcdFx0XHRcdC8vIHRoZSBjb2xsZWN0aW9uIHJvb3QsIG5ldmVyIHRoZSBkZWZhdWx0IGNvbGxlY3Rpb24uXG5cdFx0XHRcdFx0XHRcdGNvbnN0IHJlbGF0aXZlUGF0aCA9IGAke3NvdXJjZUNvbnRleHQucGFyZW50VHlwZS5mdWxsUGF0aH0uJHtwYXRofWA7XG5cdFx0XHRcdFx0XHRcdGlmICh0aGlzLmdyYXBoLmZpbmRUeXBlKHJlbGF0aXZlUGF0aCkpIHtcblx0XHRcdFx0XHRcdFx0XHRyZXR1cm4gcmVsYXRpdmVQYXRoO1xuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRcdGlmIChzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCkge1xuXHRcdFx0XHRcdFx0XHRcdHJldHVybiB0aGlzLnByZWZpeENvbGxlY3Rpb25QYXRoKHBhdGgsIHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdGlmIChzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCkge1xuXHRcdFx0XHRcdFx0XHQvLyBDb2xsZWN0aW9uIGxvb2t1cDogcHJlZml4IHBhdGggd2l0aCB0aGUgY29sbGVjdGlvbiBpZFxuXHRcdFx0XHRcdFx0XHRyZXR1cm4gdGhpcy5wcmVmaXhDb2xsZWN0aW9uUGF0aChwYXRoLCBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiBwYXRoO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBUd28tYXJnIGxvb2t1cDogbG9va3VwKHNvdXJjZSwgJ1VzZXInKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA+PSAyKSB7XG5cdFx0XHRjb25zdCBbIHNvdXJjZUFyZywgcGF0aEFyZyBdID0gYXJncztcblx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHNvdXJjZUFyZykgfHwgIXRzLmlzU3RyaW5nTGl0ZXJhbChwYXRoQXJnKSkge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgc291cmNlTmFtZSA9IHNvdXJjZUFyZy50ZXh0O1xuXHRcdFx0Y29uc3QgcGF0aCA9IHBhdGhBcmcudGV4dDtcblx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRpZiAoc291cmNlQ29udGV4dC5wYXJlbnRUeXBlKSB7XG5cdFx0XHRcdC8vIFNhbWUgcmVsYXRpdmUtZmlyc3QgbGF3IGFzIHRoZSBzaW5nbGUtYXJnIGZvcm07IGNvbGxlY3Rpb25cblx0XHRcdFx0Ly8gbWVtYmVycyBmYWxsIGJhY2sgdG8gdGhlaXIgY29sbGVjdGlvbiByb290LCBub3QgdGhlIGdsb2JhbCBvbmUuXG5cdFx0XHRcdGNvbnN0IHJlbGF0aXZlUGF0aCA9IGAke3NvdXJjZUNvbnRleHQucGFyZW50VHlwZS5mdWxsUGF0aH0uJHtwYXRofWA7XG5cdFx0XHRcdGlmICh0aGlzLmdyYXBoLmZpbmRUeXBlKHJlbGF0aXZlUGF0aCkpIHtcblx0XHRcdFx0XHRyZXR1cm4gcmVsYXRpdmVQYXRoO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCkge1xuXHRcdFx0XHRcdHJldHVybiB0aGlzLnByZWZpeENvbGxlY3Rpb25QYXRoKHBhdGgsIHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdH1cblx0XHRcdGlmIChzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCkge1xuXHRcdFx0XHRyZXR1cm4gdGhpcy5wcmVmaXhDb2xsZWN0aW9uUGF0aChwYXRoLCBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCk7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gcGF0aDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIExvb2t1cC1sYXcgZGVsZWdhdGUgZm9yIHRoZSBsb2NhbC1zY29wZSB3YWxrZXIgKHNjb3Blcy5qc29uIHR5cGVQYXRoXG5cdCAqIG1ldGFkYXRhKTogcmVzb2x2ZSBhIGxvb2t1cCgpIGluaXRpYWxpemVyIGNhbGwgdGhyb3VnaCBleGFjdGx5IHRoZVxuXHQgKiB0aWVycyB0aGUgdXNhZ2VzIHBhc3MgcmVzb2x2ZWQgaXQgYWdhaW5zdCAoc2FtZSBzb3VyY2UgcmVzb2x1dGlvbixcblx0ICogc2FtZSBjb21wbGV0ZSBncmFwaCkuIFRoZSB3YWxrZXIgcnVucyBpdHMgb3duIHNjb3BlLWNoYWluIHZhbHVlLXNjb3BlXG5cdCAqIHRpZXIgYmVmb3JlIGRlbGVnYXRpbmc7IGV2ZXJ5dGhpbmcgYWJvdmUgdmFsdWUgc2NvcGUgbGFuZHMgaGVyZSwgc29cblx0ICogc2NvcGVzLmpzb24gbmV2ZXIgZGlzYWdyZWVzIHdpdGggdGhlIGhhcmQtZmFpbC1sYXcgdmVyZGljdHMuXG5cdCAqL1xuXHRyZXNvbHZlTG9va3VwQ2FsbFBhdGggKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKGNhbGwpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHQqIEZpbmQgYSBwYXJlbnQgdHlwZSBieSBpdHMgbmFtZSwgc2VhcmNoaW5nIGluIHRoZSBncmFwaC5cblx0XHQqIFdoZW4gY29sbGVjdGlvbklkIGlzIHByb3ZpZGVkLCBvbmx5IHR5cGVzIGZyb20gdGhhdCBjb2xsZWN0aW9uIGFyZSBjb25zaWRlcmVkLlxuXHRcdCovXG5cdHByaXZhdGUgZmluZFBhcmVudFR5cGVCeU5hbWUgKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmdcblx0KTogVHlwZU5vZGUgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IG1hdGNoZXNDb2xsZWN0aW9uID0gKHR5cGU6IFR5cGVOb2RlKTogYm9vbGVhbiA9PiB7XG5cdFx0XHRpZiAoY29sbGVjdGlvbklkID09PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0cmV0dXJuIHR5cGUuY29sbGVjdGlvbklkID09PSB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdHlwZS5jb2xsZWN0aW9uSWQgPT09IGNvbGxlY3Rpb25JZDtcblx0XHR9O1xuXG5cdFx0Ly8gRmlyc3QgdHJ5IGV4YWN0IG1hdGNoIChkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMgdXNlIHRoZSBwbGFpbiBkb3R0ZWQgcGF0aClcblx0XHRjb25zdCBleGFjdCA9IHRoaXMuZ3JhcGguZmluZFR5cGUobmFtZSk7XG5cdFx0aWYgKGV4YWN0ICYmIG1hdGNoZXNDb2xsZWN0aW9uKGV4YWN0KSkge1xuXHRcdFx0cmV0dXJuIGV4YWN0O1xuXHRcdH1cblxuXHRcdC8vIFRoZW4gc2VhcmNoIHRocm91Z2ggYWxsIHR5cGVzIGZvciBvbmUgd2l0aCBtYXRjaGluZyBuYW1lIGFuZCBjb2xsZWN0aW9uXG5cdFx0Zm9yIChjb25zdCB0eXBlIG9mIHRoaXMuZ3JhcGguZ2V0QWxsVHlwZXMoKSkge1xuXHRcdFx0aWYgKHR5cGUubmFtZSA9PT0gbmFtZSAmJiBtYXRjaGVzQ29sbGVjdGlvbih0eXBlKSkge1xuXHRcdFx0XHRyZXR1cm4gdHlwZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBGaW5kIGEgcGFyZW50IHR5cGUgZnJvbSBhbiBpZGVudGlmaWVyIHJlZmVyZW5jZS5cblx0XHQqIEhhbmRsZXMgYm90aCBhbGlhc2VkIHZhcmlhYmxlcyAoY29uc3QgVXNlciA9IGRlZmluZSgnVXNlckVudGl0eScsIC4uLikpXG5cdFx0KiBhbmQgZGlyZWN0IGNsYXNzL3R5cGUgbmFtZXMuXG5cdFx0Ki9cblx0cHJpdmF0ZSBmaW5kUGFyZW50VHlwZUJ5SWRlbnRpZmllciAobmFtZTogc3RyaW5nKTogVHlwZU5vZGUgfCB1bmRlZmluZWQge1xuXHRcdC8vIEZpcnN0IGNoZWNrIHZhcmlhYmxlIG1hcHBpbmc6IGNvbnN0IFVzZXIgPSBkZWZpbmUoJ1VzZXJFbnRpdHknLCAuLi4pXG5cdFx0Y29uc3QgbWFwcGVkRnVsbFBhdGggPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChuYW1lKTtcblx0XHRpZiAobWFwcGVkRnVsbFBhdGgpIHtcblx0XHRcdGNvbnN0IG1hcHBlZE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKG1hcHBlZEZ1bGxQYXRoKTtcblx0XHRcdGlmIChtYXBwZWROb2RlKSByZXR1cm4gbWFwcGVkTm9kZTtcblx0XHR9XG5cblx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShuYW1lKTtcblx0XHRyZXR1cm4gcGFyZW50Tm9kZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgdGhlIGxlZnRtb3N0IGlkZW50aWZpZXIgb2YgYSBwcm9wZXJ0eS1hY2Nlc3MgY2hhaW4uXG5cdCAqIEZvciBgQXBwLmRlZmluZSgnVXNlcicpLmRlZmluZSgnQWRtaW4nKWAgdGhpcyByZXR1cm5zIHRoZSBgQXBwYCBpZGVudGlmaWVyLlxuXHQgKi9cblx0cHJpdmF0ZSBnZXRSb290SWRlbnRpZmllciAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHRzLklkZW50aWZpZXIgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5FeHByZXNzaW9uID0gZXhwcjtcblx0XHR3aGlsZSAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY3VycmVudCkpIHtcblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0fVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudCkpIHtcblx0XHRcdHJldHVybiBjdXJyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBHZXQgcHJvcGVydHkgY2hhaW4gZnJvbSBuZXN0ZWQgYWNjZXNzXG5cdFx0Ki9cblx0cHJpdmF0ZSBnZXRQcm9wZXJ0eUNoYWluIChleHByOiB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24gfCB0cy5JZGVudGlmaWVyKTogc3RyaW5nW10ge1xuXHRcdGNvbnN0IGNoYWluOiBzdHJpbmdbXSA9IFtdO1xuXG5cdFx0bGV0IGN1cnJlbnQ6IHRzLkV4cHJlc3Npb24gPSBleHByO1xuXHRcdHdoaWxlICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0aWYgKGN1cnJlbnQubmFtZSkge1xuXHRcdFx0XHRjaGFpbi51bnNoaWZ0KGN1cnJlbnQubmFtZS50ZXh0KTtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0fVxuXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50KSkge1xuXHRcdFx0Y2hhaW4udW5zaGlmdChjdXJyZW50LnRleHQpO1xuXHRcdH1cblxuXHRcdHJldHVybiBjaGFpbjtcblx0fVxuXG5cdHByaXZhdGUgZmluZENvbnN0cnVjdG9ySW5Nb2R1bGUgKFxuXHRcdG1vZHVsZVBhdGg6IHN0cmluZyxcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0ZGVwdGg6IG51bWJlclxuXHQpOiBDb25zdHJ1Y3RvckhhbmRsZXIgfCB1bmRlZmluZWQge1xuXHRcdGlmIChkZXB0aCA+IE1BWF9SRUVYUE9SVF9DSEFTRV9ERVBUSCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBiaW5kaW5ncyA9IHRoaXMuY29uc3RydWN0b3JCaW5kaW5ncy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0Y29uc3QgZGlyZWN0ID0gYmluZGluZ3M/LmdldChuYW1lKTtcblx0XHRpZiAoZGlyZWN0KSB7XG5cdFx0XHRyZXR1cm4gZGlyZWN0O1xuXHRcdH1cblx0XHRjb25zdCBsb2NhbEFsaWFzID0gdGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydEFsaWFzZXMuZ2V0KG1vZHVsZVBhdGgpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGxvY2FsQWxpYXMpIHtcblx0XHRcdGNvbnN0IGFsaWFzZWQgPSBiaW5kaW5ncz8uZ2V0KGxvY2FsQWxpYXMpO1xuXHRcdFx0aWYgKGFsaWFzZWQpIHtcblx0XHRcdFx0cmV0dXJuIGFsaWFzZWQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVFeHBvcnRTcGVjaWZpZXIgPSB0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLmdldChtb2R1bGVQYXRoKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChyZUV4cG9ydFNwZWNpZmllcikge1xuXHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShyZUV4cG9ydFNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRpZiAobmV4dFJlc29sdXRpb24gJiYgIW5leHRSZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRDb25zdHJ1Y3RvckluTW9kdWxlKG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgbmFtZSwgZGVwdGggKyAxKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGlmIChzdGFycykge1xuXHRcdFx0Zm9yIChjb25zdCBzdGFyU3BlY2lmaWVyIG9mIHN0YXJzKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoc3RhclNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRcdGlmICghbmV4dFJlc29sdXRpb24gfHwgbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kQ29uc3RydWN0b3JJbk1vZHVsZShuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIG5hbWUsIGRlcHRoICsgMSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHRwcml2YXRlIHJlc29sdmVIZWxkQ29uc3RydWN0b3IgKG5hbWU6IHN0cmluZywgZnJvbUZpbGU6IHN0cmluZyk6IENvbnN0cnVjdG9ySGFuZGxlciB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBub2RlUGF0aC5yZXNvbHZlKGZyb21GaWxlKTtcblx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldChmaWxlUGF0aCk/LmdldChuYW1lKTtcblx0XHRpZiAoaW1wb3J0ZWQgJiYgIWltcG9ydGVkLmlzTmFtZXNwYWNlKSB7XG5cdFx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoaW1wb3J0ZWQuc3BlY2lmaWVyLCBmaWxlUGF0aCk7XG5cdFx0XHRpZiAocmVzb2x1dGlvbiAmJiAhcmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kQ29uc3RydWN0b3JJbk1vZHVsZShyZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgaW1wb3J0ZWQub3JpZ2luYWxOYW1lLCAwKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGNvbnN0IGxvY2FsID0gdGhpcy5jb25zdHJ1Y3RvckJpbmRpbmdzLmdldChmaWxlUGF0aCk/LmdldChuYW1lKTtcblx0XHRyZXR1cm4gbG9jYWw7XG5cdH1cblxuXHRwcml2YXRlIHVud3JhcENvbnN0cnVjdG9yQXNzZXJ0aW9ucyAoaGFuZGxlcjogQ29uc3RydWN0b3JIYW5kbGVyKTogQ29uc3RydWN0b3JIYW5kbGVyIHtcblx0XHRsZXQgY3VycmVudCA9IGhhbmRsZXI7XG5cdFx0d2hpbGUgKHRzLmlzUGFyZW50aGVzaXplZEV4cHJlc3Npb24oY3VycmVudCkgfHwgdHMuaXNBc0V4cHJlc3Npb24oY3VycmVudCkgfHxcblx0XHRcdHRzLmlzVHlwZUFzc2VydGlvbkV4cHJlc3Npb24oY3VycmVudCkpIHtcblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0fVxuXHRcdHJldHVybiBjdXJyZW50O1xuXHR9XG5cblx0cHJpdmF0ZSByZXNvbHZlQ29uc3RydWN0b3JFeHByZXNzaW9uIChcblx0XHRleHByZXNzaW9uOiB0cy5FeHByZXNzaW9uLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGVcblx0KTogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBjdXJyZW50ID0gdGhpcy51bndyYXBDb25zdHJ1Y3RvckFzc2VydGlvbnMoZXhwcmVzc2lvbik7XG5cdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoY3VycmVudCkpIHtcblx0XHRcdHJldHVybiBjdXJyZW50O1xuXHRcdH1cblx0XHRjb25zdCByZXNvbHZlZCA9IHRoaXMucmVzb2x2ZUhlbGRDb25zdHJ1Y3RvcihjdXJyZW50LnRleHQsIHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXHRcdGlmICghcmVzb2x2ZWQpIHtcblx0XHRcdHJldHVybiBjdXJyZW50O1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnVud3JhcENvbnN0cnVjdG9yQXNzZXJ0aW9ucyhyZXNvbHZlZCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlcm1pbmUgdGhlIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24gZm9yIGVpdGhlciBhIGRlZmluZSgpIG9yIGxhenkoKSBjYWxsLlxuXHQgKiBGb3IgZGVmaW5lKCkgdGhpcyBpcyB0aGUgY29uc3RydWN0IGhhbmRsZXI7IGZvciBsYXp5KCkgaXQgaXMgdGhlIHZhbHVlXG5cdCAqIHJldHVybmVkIGJ5IHRoZSBsYXp5IGdldHRlci4gSWRlbnRpZmllcnMgcmVzb2x2ZSB0byB0aGVpciBkZWNsYXJhdGlvbnMuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24gKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBleHByID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGNvbnN0IG5hbWUgPSB0cy5pc0lkZW50aWZpZXIoZXhwcilcblx0XHRcdD8gZXhwci50ZXh0XG5cdFx0XHQ6IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpXG5cdFx0XHRcdD8gZXhwci5uYW1lLnRleHRcblx0XHRcdFx0OiAnJztcblx0XHRsZXQgaGFuZGxlcjogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZDtcblxuXHRcdGlmIChuYW1lID09PSAnbGF6eScpIHtcblx0XHRcdGNvbnN0IGxhenlBcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdFx0aWYgKGxhenlBcmdzKSB7XG5cdFx0XHRcdGhhbmRsZXIgPSB0aGlzLnVud3JhcExhenlHZXR0ZXIobGF6eUFyZ3MuZ2V0dGVyKTtcblx0XHRcdH1cblx0XHR9IGVsc2Uge1xuXHRcdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChhcmdzWyAwIF0pKSB7XG5cdFx0XHRcdGNvbnN0IFsgLCBtb2Rlcm5IYW5kbGVyIF0gPSBhcmdzO1xuXHRcdFx0XHRoYW5kbGVyID0gbW9kZXJuSGFuZGxlcjtcblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGNvbnN0IFsgbGVnYWN5SGFuZGxlciBdID0gYXJncztcblx0XHRcdFx0aGFuZGxlciA9IGxlZ2FjeUhhbmRsZXI7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0aWYgKCFoYW5kbGVyKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnJlc29sdmVDb25zdHJ1Y3RvckV4cHJlc3Npb24oaGFuZGxlciwgY2FsbC5nZXRTb3VyY2VGaWxlKCkpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRGV0ZWN0IGFuIGFzeW5jIGNvbnN0cnVjdG9yIGhhbmRsZXI6IHRoZSBhc3luYyBtb2RpZmllciBvbiBhXG5cdCAqIGZ1bmN0aW9uIGV4cHJlc3Npb24gb3IgYXJyb3cuIEFzeW5jIENMQVNTRVMgKGEgY2xhc3MgY29uc3RydWN0b3Jcblx0ICogcmV0dXJuaW5nIGEgUHJvbWlzZSkgYXJlIGRlbGliZXJhdGVseSBOT1QgZGV0ZWN0ZWQg4oCUIHRoZSBzeW50YWN0aWNcblx0ICogY2xhc3Mgc2hhcGUgZ2l2ZXMgbm8gcmVsaWFibGUgc2lnbmFsIHdpdGhvdXQgYSB0eXBlIGNoZWNrZXIsIGFuZCB0aGVcblx0ICogb3duZXIgZGVjaWRlZCB0aGV5IGFyZSB0eXBlZCBieSB0aGUgdXNlciBpbiB1c2VybGFuZC5cblx0ICovXG5cdHByaXZhdGUgaXNBc3luY0NvbnN0cnVjdEhhbmRsZXIgKGNvbnN0cnVjdG9yRXhwcjogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkKTogYm9vbGVhbiB7XG5cdFx0aWYgKCFjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Y29uc3QgaXNGbiA9IHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikgfHxcblx0XHRcdHRzLmlzQXJyb3dGdW5jdGlvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdGlmICghaXNGbikge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblx0XHRjb25zdCBtb2RpZmllcnMgPSB0cy5nZXRNb2RpZmllcnMoY29uc3RydWN0b3JFeHByKTtcblx0XHRjb25zdCByZXN1bHQgPSAhIW1vZGlmaWVycyAmJiBtb2RpZmllcnMuc29tZSgobW9kaWZpZXIpID0+IHtcblx0XHRcdHJldHVybiBtb2RpZmllci5raW5kID09PSB0cy5TeW50YXhLaW5kLkFzeW5jS2V5d29yZDtcblx0XHR9KTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGNvbnN0cnVjdG9yIGZ1bmN0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RQcm9wZXJ0aWVzIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yRXhwcmVzc2lvbihjYWxsKTtcblx0XHRpZiAoIWNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0cmV0dXJuIG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cdFx0fVxuXHRcdGNvbnN0IHJlZmVyZW5jaW5nRmlsZSA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSBub2RlUGF0aC5yZXNvbHZlKGNvbnN0cnVjdG9yRXhwci5nZXRTb3VyY2VGaWxlKCkuZmlsZU5hbWUpO1xuXHRcdHRyeSB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzRnJvbUNvbnN0cnVjdG9yKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH0gZmluYWxseSB7XG5cdFx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSByZWZlcmVuY2luZ0ZpbGU7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGEgY29uc3RydWN0b3IgZXhwcmVzc2lvbiAoZnVuY3Rpb24sIGFycm93LCBvciBjbGFzcykuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RQcm9wZXJ0aWVzRnJvbUNvbnN0cnVjdG9yIChjb25zdHJ1Y3RvckV4cHI6IENvbnN0cnVjdG9ySGFuZGxlcik6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Ly8gQnVpbGQgdHlwZSBtYXAgZnJvbSBkYXRhIHBhcmFtZXRlciAoZm9yIHRoaXMueCA9IGRhdGEueCBwYXR0ZXJucylcblx0XHRjb25zdCBkYXRhVHlwZU1hcCA9IHRoaXMuYnVpbGREYXRhVHlwZU1hcChjb25zdHJ1Y3RvckV4cHIpO1xuXG5cdFx0Ly8gSGFuZGxlIGZ1bmN0aW9uIGV4cHJlc3Npb25cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSB8fCB0cy5pc0Fycm93RnVuY3Rpb24oY29uc3RydWN0b3JFeHByKSB8fFxuXHRcdFx0dHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKGNvbnN0cnVjdG9yRXhwcikpIHtcblx0XHRcdGNvbnN0IHsgYm9keSB9ID0gY29uc3RydWN0b3JFeHByO1xuXG5cdFx0XHQvLyBGaXJzdCwgZXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gYHRoaXNgIHBhcmFtZXRlciB0eXBlIGFubm90YXRpb25cblx0XHRcdC8vIFRoaXMgaGFuZGxlcyBwYXR0ZXJucyBsaWtlOiBmdW5jdGlvbih0aGlzOiBTb21lVHlwZSwgZGF0YTogU29tZVR5cGUpIHsgfVxuXHRcdFx0Y29uc3QgdGhpc1BhcmFtUHJvcGVydGllcyA9IHRoaXMuZXh0cmFjdFRoaXNQYXJhbVByb3BlcnRpZXMoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdGZvciAoY29uc3QgWyBuYW1lLCBwcm9wSW5mbyBdIG9mIHRoaXNQYXJhbVByb3BlcnRpZXMpIHtcblx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwgcHJvcEluZm8pO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBBbiBhbm5vdGF0ZWQgdGhpcyBpcyB0aGUgY29tcGxldGUgZGVjbGFyZWQgaW5zdGFuY2UgdHlwZTogYXNzaWdubWVudHNcblx0XHRcdC8vIGJleW9uZCBpdCBhZGQgbm90aGluZy4gQSBnZW5lcmF0ZWQgLnRhY3RpY2Egb3IgZ3JhcGgtbmFtZSBhbm5vdGF0aW9uXG5cdFx0XHQvLyBpcyB0aGUgb3V0cHV0LCBub3QgdGhlIHNvdXJjZSwgc28gdGhvc2UgaGFuZGxlcnMga2VlcCBhc3NpZ25tZW50IGV4dHJhY3Rpb24uXG5cdFx0XHRjb25zdCBoYXNHZW5lcmF0ZWRSZWZlcmVuY2UgPSB0aGlzLmhhc0dlbmVyYXRlZFRoaXNBbm5vdGF0aW9uKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRjb25zdCBoYXNBdXRob3JpdGF0aXZlVGhpc0Fubm90YXRpb24gPSAhaGFzR2VuZXJhdGVkUmVmZXJlbmNlICYmIGNvbnN0cnVjdG9yRXhwci5wYXJhbWV0ZXJzLnNvbWUocGFyYW0gPT4ge1xuXHRcdFx0XHRjb25zdCByZXN1bHQgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgJiYgcGFyYW0ubmFtZS50ZXh0ID09PSAndGhpcycgJiYgcGFyYW0udHlwZSAhPT0gdW5kZWZpbmVkO1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fSk7XG5cdFx0XHRpZiAoIWhhc0F1dGhvcml0YXRpdmVUaGlzQW5ub3RhdGlvbiAmJiBib2R5ICYmIHRzLmlzQmxvY2soYm9keSkpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBzdG10IG9mIGJvZHkuc3RhdGVtZW50cykge1xuXHRcdFx0XHRcdGlmICh0cy5pc0V4cHJlc3Npb25TdGF0ZW1lbnQoc3RtdCkpIHtcblx0XHRcdFx0XHRcdHRoaXMuZXh0cmFjdFByb3BlcnR5RnJvbVN0YXRlbWVudChzdG10LmV4cHJlc3Npb24sIHByb3BlcnRpZXMsIGRhdGFUeXBlTWFwKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBIYW5kbGUgY2xhc3MgZXhwcmVzc2lvblxuXHRcdGlmICh0cy5pc0NsYXNzRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHQvLyBGaXJzdCBwYXNzOiBjb2xsZWN0IGFsbCBwcm9wZXJ0eSB0eXBlcyBmb3IgbWV0aG9kIGluZmVyZW5jZVxuXHRcdFx0Y29uc3QgY2xhc3NQcm9wZXJ0eVR5cGVzID0gdGhpcy5leHRyYWN0Q2xhc3NQcm9wZXJ0eVR5cGVzKGNvbnN0cnVjdG9yRXhwcik7XG5cblx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGNvbnN0cnVjdG9yRXhwci5tZW1iZXJzKSB7XG5cdFx0XHRcdC8vIEhhbmRsZSBwcm9wZXJ0eSBkZWNsYXJhdGlvbnNcblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlEZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lKSB7XG5cdFx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgcHJvcGVydGllc1xuXHRcdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdFx0XHRtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZDtcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cblx0XHRcdFx0XHRjb25zdCBuYW1lID0gdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSA/IG1lbWJlci5uYW1lLnRleHQgOiAnJztcblx0XHRcdFx0XHRpZiAobmFtZSkge1xuXHRcdFx0XHRcdFx0bGV0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0XHRpZiAodHlwZSA9PT0gJ3Vua25vd24nICYmIG1lbWJlci5pbml0aWFsaXplcikge1xuXHRcdFx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIobWVtYmVyLmluaXRpYWxpemVyKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gSGFuZGxlIG1ldGhvZCBkZWNsYXJhdGlvbnNcblx0XHRcdFx0aWYgKHRzLmlzTWV0aG9kRGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgbWV0aG9kc1xuXHRcdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdFx0XHRtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZDtcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cblx0XHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlck1ldGhvZFR5cGUobWVtYmVyLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIEhhbmRsZSBnZXR0ZXIgZGVjbGFyYXRpb25zXG5cdFx0XHRcdGlmICh0cy5pc0dldEFjY2Vzc29yKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIGdldHRlcnNcblx0XHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4ge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHRcdFx0bS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQ7XG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXG5cdFx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Ly8gRmlyc3QgdHJ5IGV4cGxpY2l0IHR5cGUgYW5ub3RhdGlvbiwgdGhlbiBpbmZlciBmcm9tIGdldHRlciBib2R5XG5cdFx0XHRcdFx0bGV0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0aWYgKHR5cGUgPT09ICd1bmtub3duJyAmJiBtZW1iZXIuYm9keSkge1xuXHRcdFx0XHRcdFx0dHlwZSA9IHRoaXMuaW5mZXJSZXR1cm5UeXBlRnJvbUJvZHkobWVtYmVyLmJvZHksIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdHJlYWRvbmx5IDogdHJ1ZSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBwcm9wZXJ0aWVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEJ1aWxkIGEgdHlwZSBtYXAgZnJvbSBhbGwgcGFyYW1ldGVycyB3aXRoIGlubGluZSBvYmplY3QgdHlwZSBhbm5vdGF0aW9uc1xuXHQgKiBSZXR1cm5zIGEgbWFwIG9mIFwicGFyYW1OYW1lLnByb3BlcnR5TmFtZVwiIC0+IHR5cGVcblx0ICovXG5cdHByaXZhdGUgYnVpbGREYXRhVHlwZU1hcCAoaGFuZGxlckFyZzogQ29uc3RydWN0b3JIYW5kbGVyKTogTWFwPHN0cmluZywgc3RyaW5nPiB7XG5cdFx0Y29uc3QgdHlwZU1hcCA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cblx0XHRpZiAoIXRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGhhbmRsZXJBcmcpICYmICF0cy5pc0Fycm93RnVuY3Rpb24oaGFuZGxlckFyZykgJiZcblx0XHRcdCF0cy5pc0Z1bmN0aW9uRGVjbGFyYXRpb24oaGFuZGxlckFyZykpIHtcblx0XHRcdHJldHVybiB0eXBlTWFwO1xuXHRcdH1cblxuXHRcdC8vIEl0ZXJhdGUgb3ZlciBBTEwgcGFyYW1ldGVyc1xuXHRcdGZvciAoY29uc3QgcGFyYW0gb2YgaGFuZGxlckFyZy5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRpZiAoIXBhcmFtLm5hbWUgfHwgIXBhcmFtLnR5cGUpIGNvbnRpbnVlO1xuXG5cdFx0XHQvLyBHZXQgcGFyYW1ldGVyIG5hbWVcblx0XHRcdGxldCBwYXJhbU5hbWUgPSAnJztcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkpIHtcblx0XHRcdFx0cGFyYW1OYW1lID0gcGFyYW0ubmFtZS50ZXh0O1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Ly8gU2tpcCBkZXN0cnVjdHVyZWQgcGFyYW1ldGVycyBmb3Igbm93XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBDaGVjayBpZiBpdCdzIGFuIGlubGluZSBvYmplY3QgdHlwZSBsaXRlcmFsXG5cdFx0XHRpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUocGFyYW0udHlwZSkpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgcGFyYW0udHlwZS5tZW1iZXJzKSB7XG5cdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQoYCR7cGFyYW1OYW1lfS4ke3Byb3BOYW1lfWAsIHR5cGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Ly8gTmFtZWQgdHlwZSByZWZlcmVuY2UgKGFsaWFzL2ludGVyZmFjZS9jbGFzcywgaW1wb3J0ZWQgb3Jcblx0XHRcdFx0Ly8gbG9jYWwg4oCUIEYxNCk6IGRlY29tcG9zZSB0aGUgcmVzb2x2ZWQgZGVjbGFyYXRpb24gaW50b1xuXHRcdFx0XHQvLyBwZXItcHJvcGVydHkgZW50cmllcyB0aHJvdWdoIHRoZSBzYW1lIGltcG9ydC1hd2FyZVxuXHRcdFx0XHQvLyBtYWNoaW5lcnkgYXMgY29uc3RydWN0b3Igc2lnbmF0dXJlcyAoRjEwKSwgaW5jbHVkaW5nIHRoZVxuXHRcdFx0XHQvLyBoZXJpdGFnZSB3YWxrIChGMTMpLiBXaXRob3V0IHRoaXMsIGB0aGlzLnggPSBwYXJhbS55YFxuXHRcdFx0XHQvLyByZWFkIGB1bmtub3duYCBmb3IgbmFtZWQgcGFyYW1zIOKAlCBvbmx5IGlubGluZSBsaXRlcmFsc1xuXHRcdFx0XHQvLyB3ZXJlIGRlY29tcG9zZWQuIFVucmVzb2x2YWJsZSDihpIgd2hvbGUtcGFyYW0gZmFsbGJhY2tcblx0XHRcdFx0Ly8gYmVsb3c7IGEgYmFyZSBuYW1lIGlzIG5ldmVyIGVtaXR0ZWQgZWl0aGVyIHdheVxuXHRcdFx0XHRsZXQgbmFtZWREZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkO1xuXHRcdFx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZShwYXJhbS50eXBlKSAmJiB0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBwYXJhbVR5cGVOYW1lID0gcGFyYW0udHlwZS50eXBlTmFtZS50ZXh0O1xuXHRcdFx0XHRcdG5hbWVkRGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24ocGFyYW1UeXBlTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAobmFtZWREZWNsKSB7XG5cdFx0XHRcdFx0Ly8gbWVtYmVyIHR5cGVzIHJlc29sdmUgYWdhaW5zdCB0aGUgREVDTEFSSU5HIGZpbGVcblx0XHRcdFx0XHRjb25zdCByZWZlcmVuY2luZ0ZpbGUgPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0XHRcdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gbmFtZWREZWNsLmZpbGU7XG5cdFx0XHRcdFx0dHJ5IHtcblx0XHRcdFx0XHRcdGNvbnN0IGRlY2xQcm9wZXJ0aWVzID0gdGhpcy5yZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzKG5hbWVkRGVjbCk7XG5cdFx0XHRcdFx0XHRmb3IgKGNvbnN0IFsgcHJvcE5hbWUsIGluZm8gXSBvZiBkZWNsUHJvcGVydGllcykge1xuXHRcdFx0XHRcdFx0XHR0eXBlTWFwLnNldChgJHtwYXJhbU5hbWV9LiR7cHJvcE5hbWV9YCwgaW5mby50eXBlKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGZpbmFsbHkge1xuXHRcdFx0XHRcdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gcmVmZXJlbmNpbmdGaWxlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHQvLyBrZWVwIHRoZSB3aG9sZS1wYXJhbSBlbnRyeSB0b286IGB0aGlzLnggPSBkYXRhYCAodGhlXG5cdFx0XHRcdFx0Ly8gYmFyZSBwYXJhbWV0ZXIpIGFzc2lnbnMgdGhlIGZ1bGwgZXhwYW5kZWQgc2hhcGUg4oCUXG5cdFx0XHRcdFx0Ly8gdGhlIHNhbWUgc3RyaW5nIGNvbnN0cnVjdG9yLXNpZ25hdHVyZSBlbWlzc2lvbiB1c2VzXG5cdFx0XHRcdFx0Y29uc3Qgd2hvbGVUeXBlID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKG5hbWVkRGVjbCk7XG5cdFx0XHRcdFx0aWYgKHdob2xlVHlwZSAmJiB3aG9sZVR5cGUgIT09ICd1bmtub3duJykge1xuXHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQocGFyYW1OYW1lLCB3aG9sZVR5cGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHQvLyBTdG9yZSBzaW1wbGUgcGFyYW1ldGVyIHR5cGVzIGxpa2UgYGRlY29yYXRlVmFsdWU6IHN0cmluZ2Bcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cdFx0XHRcdFx0aWYgKHR5cGUgIT09ICd1bmtub3duJykge1xuXHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQocGFyYW1OYW1lLCB0eXBlKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdHlwZU1hcDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnR5IGFjY2VzcyBjaGFpbiAoZS5nLiwgXCJkYXRhUmVuYW1lZC5pZFwiIGZyb20gZGF0YVJlbmFtZWQuaWQpXG5cdCAqIEhhbmRsZXMgZmFsbGJhY2tzIGxpa2U6IGRhdGEucGVybWlzc2lvbnMgfHwgW11cblx0ICovXG5cdHByaXZhdGUgZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbiAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gSGFuZGxlIGlkZW50aWZpZXI6IGRhdGFcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci50ZXh0O1xuXHRcdH1cblx0XHQvLyBIYW5kbGUgcHJvcGVydHkgYWNjZXNzOiBkYXRhLnBlcm1pc3Npb25zXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBiYXNlID0gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGV4cHIuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoYmFzZSkge1xuXHRcdFx0XHRyZXR1cm4gYCR7YmFzZX0uJHtleHByLm5hbWUudGV4dH1gO1xuXHRcdFx0fVxuXHRcdH1cblx0XHQvLyBIYW5kbGUgZmFsbGJhY2sgcGF0dGVybjogZGF0YS5wZXJtaXNzaW9ucyB8fCBbXVxuXHRcdGlmICh0cy5pc0JpbmFyeUV4cHJlc3Npb24oZXhwcikgJiZcblx0XHRcdGV4cHIub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkJhckJhclRva2VuKSB7XG5cdFx0XHQvLyBSZXR1cm4gdGhlIGxlZnQgc2lkZSBvZiB8fCBvcGVyYXRvclxuXHRcdFx0cmV0dXJuIHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihleHByLmxlZnQpO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydHkgYXNzaWdubWVudCBmcm9tIHN0YXRlbWVudFxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UHJvcGVydHlGcm9tU3RhdGVtZW50IChcblx0XHRleHByOiB0cy5FeHByZXNzaW9uLFxuXHRcdHByb3BlcnRpZXM6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4sXG5cdFx0ZGF0YVR5cGVNYXA6IE1hcDxzdHJpbmcsIHN0cmluZz4gPSBuZXcgTWFwKClcblx0KTogdm9pZCB7XG5cdFx0Ly8gSGFuZGxlOiB0aGlzLnByb3BlcnR5ID0gdmFsdWVcblx0XHRpZiAodHMuaXNCaW5hcnlFeHByZXNzaW9uKGV4cHIpICYmXG5cdFx0XHRleHByLm9wZXJhdG9yVG9rZW4ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbikge1xuXHRcdFx0Y29uc3QgeyBsZWZ0IH0gPSBleHByO1xuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obGVmdCkpIHtcblx0XHRcdFx0Ly8gQ2hlY2sgaWYgYWNjZXNzaW5nICd0aGlzJyAoVGhpc0tleXdvcmQpXG5cdFx0XHRcdGlmIChsZWZ0LmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBsZWZ0Lm5hbWU/LnRleHQ7XG5cdFx0XHRcdFx0aWYgKG5hbWUpIHtcblx0XHRcdFx0XHRcdC8vIFRyeSB0byBnZXQgdHlwZSBmcm9tIGRhdGFUeXBlTWFwIHVzaW5nIGZ1bGwgYWNjZXNzIGNoYWluIChlLmcuLCBcImRhdGFSZW5hbWVkLmlkXCIpXG5cdFx0XHRcdFx0XHRjb25zdCBhY2Nlc3NDaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihleHByLnJpZ2h0KTtcblx0XHRcdFx0XHRcdGxldCB0eXBlID0gYWNjZXNzQ2hhaW4gPyBkYXRhVHlwZU1hcC5nZXQoYWNjZXNzQ2hhaW4pIDogdW5kZWZpbmVkO1xuXHRcdFx0XHRcdFx0Ly8gSWYgbm90IGZvdW5kIGFuZCBSSFMgaXMgYSBzaW1wbGUgaWRlbnRpZmllciwgdHJ5IGxvb2tpbmcgaXQgdXAgZGlyZWN0bHlcblx0XHRcdFx0XHRcdGlmICghdHlwZSAmJiB0cy5pc0lkZW50aWZpZXIoZXhwci5yaWdodCkpIHtcblx0XHRcdFx0XHRcdFx0dHlwZSA9IGRhdGFUeXBlTWFwLmdldChleHByLnJpZ2h0LnRleHQpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0Ly8gYSBib3VuZCBjb25zdHJ1Y3Rpb24gcmVzdWx0IChuZXcvbG9va3VwL2NoYWluL2ZvcmsvXG5cdFx0XHRcdFx0XHQvLyBtZXJnZS9jYWxsKTogdGhlIHZhbHVlIHNjb3BlIGJpbmRpbmcgc3VwcGxpZXMgdGhlXG5cdFx0XHRcdFx0XHQvLyBncmFwaCB0eXBlIOKAlCBlbWl0dGVkIGJ5IGl0cyBpbnN0YW5jZS10eXBlIG5hbWVcblx0XHRcdFx0XHRcdGlmICghdHlwZSAmJiB0cy5pc0lkZW50aWZpZXIoZXhwci5yaWdodCkpIHtcblx0XHRcdFx0XHRcdFx0Y29uc3QgYm91bmQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChleHByLnJpZ2h0LnRleHQpO1xuXHRcdFx0XHRcdFx0XHRpZiAoYm91bmQpIHtcblx0XHRcdFx0XHRcdFx0XHQvLyBFbWl0IHRoZSBhbGlhcyB0eXBlcy50cyBkZWNsYXJlcyAoT3B0aW9uIEJcblx0XHRcdFx0XHRcdFx0XHQvLyByZWdpc3RyeSBwcmVmaXgpLCBub3QgdGhlIHJhdyBjb2xsZWN0aW9uSWQ6OlxuXHRcdFx0XHRcdFx0XHRcdC8vIGZ1bGxQYXRoOyBuZXZlci1lbWl0dGVkIHR5cGVzIGZhbGwgdGhyb3VnaFxuXHRcdFx0XHRcdFx0XHRcdC8vIHRvIGluaXRpYWxpemVyIGluZmVyZW5jZVxuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IGJvdW5kTm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoYm91bmQpO1xuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IGJvdW5kQWxpYXMgPSBib3VuZE5vZGVcblx0XHRcdFx0XHRcdFx0XHRcdD8gdGhpcy5nZXRFbWl0dGVkSW5zdGFuY2VUeXBlTmFtZShib3VuZE5vZGUpXG5cdFx0XHRcdFx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblx0XHRcdFx0XHRcdFx0XHRpZiAoYm91bmRBbGlhcykge1xuXHRcdFx0XHRcdFx0XHRcdFx0dHlwZSA9IGJvdW5kQWxpYXM7XG5cdFx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRpZiAoIXR5cGUpIHtcblx0XHRcdFx0XHRcdFx0dHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKGV4cHIucmlnaHQsIGRhdGFUeXBlTWFwKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdC8vIERvbid0IG92ZXJ3cml0ZSBhIGtub3duIHR5cGUgZnJvbSBhIGB0aGlzYCBhbm5vdGF0aW9uXG5cdFx0XHRcdFx0XHQvLyB3aXRoIGFuIHVua25vd24tYmVhcmluZyBpbmZlcmVuY2U6IGFuIGVtcHR5LWFycmF5XG5cdFx0XHRcdFx0XHQvLyBpbml0aWFsaXplciBpbmZlcnMgJ0FycmF5PHVua25vd24+Jywgd2hpY2ggbXVzdCBub3Rcblx0XHRcdFx0XHRcdC8vIGNsb2JiZXIgYW4gYW5ub3RhdGVkICdBcnJheTx7IGlkOiBudW1iZXIgfT4nIGVpdGhlci5cblx0XHRcdFx0XHRcdC8vIFwiS25vd25cIiBvbiB0aGUgRVhJU1RJTkcgc2lkZSBtZWFucyB0aGUgd2hvbGUgdHlwZSBJU1xuXHRcdFx0XHRcdFx0Ly8gYHVua25vd25gIChleGFjdCBtYXRjaCkg4oCUIGEgc3Vic3RyaW5nIG1hdGNoIHRyZWF0c1xuXHRcdFx0XHRcdFx0Ly8gYFJlY29yZDxzdHJpbmcsIHVua25vd24+YCBhcyB1bmtub3duLWJlYXJpbmcgYW5kIGxldFxuXHRcdFx0XHRcdFx0Ly8gaW5mZXJlbmNlIGNsb2JiZXIgYSBnb29kIGFubm90YXRpb24gKEYxNClcblx0XHRcdFx0XHRcdGNvbnN0IGV4aXN0aW5nID0gcHJvcGVydGllcy5nZXQobmFtZSk7XG5cdFx0XHRcdFx0XHRjb25zdCB0eXBlSGFzVW5rbm93biA9ICF0eXBlIHx8IHR5cGUuaW5jbHVkZXMoJ3Vua25vd24nKTtcblx0XHRcdFx0XHRcdGNvbnN0IGV4aXN0aW5nSXNLbm93biA9IGV4aXN0aW5nID8gZXhpc3RpbmcudHlwZS50cmltKCkgIT09ICd1bmtub3duJyA6IGZhbHNlO1xuXHRcdFx0XHRcdFx0aWYgKGV4aXN0aW5nSXNLbm93biAmJiB0eXBlSGFzVW5rbm93bikge1xuXHRcdFx0XHRcdFx0XHQvLyBLZWVwIHRoZSBiZXR0ZXIgdHlwZSBmcm9tIGV4cGxpY2l0IGFubm90YXRpb25cblx0XHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBleGlzdGluZyA/IGV4aXN0aW5nLm9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIEhhbmRsZTogT2JqZWN0LmFzc2lnbih0aGlzLCB7IHByb3A6IHZhbHVlIH0pXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdGNvbnN0IGZuID0gZXhwci5leHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGZuKSAmJlxuXHRcdFx0XHRmbi5uYW1lPy50ZXh0ID09PSAnYXNzaWduJyAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoZm4uZXhwcmVzc2lvbikgJiZcblx0XHRcdFx0Zm4uZXhwcmVzc2lvbi50ZXh0ID09PSAnT2JqZWN0Jykge1xuXHRcdFx0XHRjb25zdCBhcmdzID0gZXhwci5hcmd1bWVudHM7XG5cdFx0XHRcdGlmIChhcmdzLmxlbmd0aCA+PSAyICYmIGFyZ3NbIDAgXS5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gdGhlIHNlY29uZCBhcmd1bWVudFxuXHRcdFx0XHRcdGNvbnN0IFsgLCBwcm9wc0FyZyBdID0gYXJncztcblx0XHRcdFx0XHRpZiAodHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihwcm9wc0FyZykpIHtcblx0XHRcdFx0XHRcdGZvciAoY29uc3QgcHJvcCBvZiBwcm9wc0FyZy5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSAmJiB0cy5pc0lkZW50aWZpZXIocHJvcC5uYW1lKSkge1xuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBwcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0XHRcdFx0dHlwZSAgICAgOiB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihwcm9wLmluaXRpYWxpemVyKSxcblx0XHRcdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihwcm9wc0FyZykpIHtcblx0XHRcdFx0XHRcdC8vIE9iamVjdC5hc3NpZ24odGhpcywgZGF0YSkg4oCUIHRoZSBpZGVudGlmaWVyIGZvcm06IGV2ZXJ5XG5cdFx0XHRcdFx0XHQvLyBwZXItcHJvcGVydHkgZW50cnkgdGhlIGRhdGEgcGFyYW1ldGVyIGNvbnRyaWJ1dGVkIHRvXG5cdFx0XHRcdFx0XHQvLyB0aGUgdHlwZSBtYXAgYmVjb21lcyBhbiBvd24gcHJvcGVydHkuIFRoaXMgaXMgd2hhdFxuXHRcdFx0XHRcdFx0Ly8gY2FycmllcyB0aGUgZmllbGRzIGZvciB0aGUgc2VsZi1yZWZlcmVuY2luZ1xuXHRcdFx0XHRcdFx0Ly8gaW50ZXJzZWN0aW9uLWFsaWFzIHJvb3QgcGF0dGVybiAoRjIxKTogdGhlIHRoaXMtYWxpYXNcblx0XHRcdFx0XHRcdC8vIGlzIGVyZ29ub21pYy1vbmx5IGFuZCBpdHMgaW50ZXJzZWN0aW9uIG1lbWJlcnMgYXJlXG5cdFx0XHRcdFx0XHQvLyBuZXZlciBleHBhbmRlZCwgc28gdGhlIGFzc2lnbiBpcyB3aGVyZSB0aGUgcm9vdCdzXG5cdFx0XHRcdFx0XHQvLyBmaWVsZHMgbXVzdCBjb21lIGZyb21cblx0XHRcdFx0XHRcdGNvbnN0IHBhcmFtTmFtZSA9IHByb3BzQXJnLnRleHQ7XG5cdFx0XHRcdFx0XHRmb3IgKGNvbnN0IFsga2V5LCB0eXBlIF0gb2YgZGF0YVR5cGVNYXApIHtcblx0XHRcdFx0XHRcdFx0aWYgKCFrZXkuc3RhcnRzV2l0aChgJHtwYXJhbU5hbWV9LmApKSB7XG5cdFx0XHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdFx0Y29uc3QgbmFtZSA9IGtleS5zbGljZShwYXJhbU5hbWUubGVuZ3RoICsgMSk7XG5cdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGNsYXNzIGRlY2xhcmF0aW9uIChpbmNsdWRpbmcgbWV0aG9kcyBhbmQgZ2V0dGVycylcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENsYXNzUHJvcGVydGllcyAoY2xhc3NEZWNsOiB0cy5DbGFzc0RlY2xhcmF0aW9uKTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjbGFzc0RlY2wubWVtYmVycykge1xuXHRcdFx0Ly8gSGFuZGxlIHByb3BlcnR5IGRlY2xhcmF0aW9uc1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlEZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lKSB7XG5cdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIHByb3BlcnRpZXNcblx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdCAgICAgbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQpO1xuXHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpID8gbWVtYmVyLm5hbWUudGV4dCA6ICcnO1xuXHRcdFx0XHRpZiAobmFtZSkge1xuXHRcdFx0XHRcdC8vIElmIG5vIGV4cGxpY2l0IHR5cGUgYnV0IGhhcyBpbml0aWFsaXplciwgaW5mZXIgZnJvbSBpbml0aWFsaXplclxuXHRcdFx0XHRcdGxldCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdGlmICh0eXBlID09PSAndW5rbm93bicgJiYgbWVtYmVyLmluaXRpYWxpemVyKSB7XG5cdFx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIobWVtYmVyLmluaXRpYWxpemVyKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblxuXHRcdFx0Ly8gSGFuZGxlIG1ldGhvZCBkZWNsYXJhdGlvbnNcblx0XHRcdGlmICh0cy5pc01ldGhvZERlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBtZXRob2RzXG5cdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHQgICAgIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkKTtcblx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJNZXRob2RUeXBlKG1lbWJlcik7XG5cdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEhhbmRsZSBnZXR0ZXIgZGVjbGFyYXRpb25zXG5cdFx0XHRpZiAodHMuaXNHZXRBY2Nlc3NvcihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgZ2V0dGVyc1xuXHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0ICAgICBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZCk7XG5cdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdC8vIEZpcnN0IHRyeSBleHBsaWNpdCB0eXBlIGFubm90YXRpb24sIHRoZW4gaW5mZXIgZnJvbSBnZXR0ZXIgYm9keVxuXHRcdFx0XHRsZXQgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0aWYgKHR5cGUgPT09ICd1bmtub3duJyAmJiBtZW1iZXIuYm9keSkge1xuXHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyUmV0dXJuVHlwZUZyb21Cb2R5KG1lbWJlci5ib2R5KTtcblx0XHRcdFx0fVxuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0cmVhZG9ubHkgOiB0cnVlLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGNsYXNzIHByb3BlcnR5IHR5cGVzIGZvciBtZXRob2QgcmV0dXJuIHR5cGUgaW5mZXJlbmNlXG5cdCAqIE1hcHMgcHJvcGVydHkgbmFtZXMgdG8gdGhlaXIgVHlwZVNjcmlwdCB0eXBlIHN0cmluZ3Ncblx0ICogTm90ZTogSW5jbHVkZXMgcHJpdmF0ZS9wcm90ZWN0ZWQgcHJvcGVydGllcyBmb3IgbWV0aG9kIGluZmVyZW5jZVxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q2xhc3NQcm9wZXJ0eVR5cGVzIChjbGFzc0RlY2w6IENsYXNzQ29uc3RydWN0b3JIYW5kbGVyKTogTWFwPHN0cmluZywgc3RyaW5nPiB7XG5cdFx0Y29uc3QgcHJvcGVydHlUeXBlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjbGFzc0RlY2wubWVtYmVycykge1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlEZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Ly8gSW5jbHVkZSBBTEwgcHJvcGVydGllcyAoZXZlbiBwcml2YXRlKSBmb3IgbWV0aG9kIHJldHVybiB0eXBlIGluZmVyZW5jZVxuXHRcdFx0XHQvLyBUaGUgdmlzaWJpbGl0eSBjaGVjayBpcyBkb25lIHdoZW4gYWRkaW5nIHRvIG91dHB1dCBwcm9wZXJ0aWVzXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRpZiAobWVtYmVyLnR5cGUpIHtcblx0XHRcdFx0XHRwcm9wZXJ0eVR5cGVzLnNldChuYW1lLCB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSkpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnR5VHlwZXM7XG5cdH1cblxuXHQvKipcblx0ICogSW5mZXIgbWV0aG9kIHR5cGUgZnJvbSBtZXRob2QgZGVjbGFyYXRpb25cblx0ICovXG5cdHByaXZhdGUgaW5mZXJNZXRob2RUeXBlIChtZXRob2Q6IHRzLk1ldGhvZERlY2xhcmF0aW9uLCBjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+KTogc3RyaW5nIHtcblx0XHRjb25zdCBwYXJhbXMgPSBtZXRob2QucGFyYW1ldGVycy5tYXAocGFyYW0gPT4ge1xuXHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpID8gcGFyYW0ubmFtZS50ZXh0IDogJ2FyZyc7XG5cdFx0XHRjb25zdCBwYXJhbVR5cGUgPSB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblx0XHRcdHJldHVybiBgJHtwYXJhbU5hbWV9OiAke3BhcmFtVHlwZX1gO1xuXHRcdH0pLmpvaW4oJywgJyk7XG5cblx0XHRjb25zdCByZXR1cm5UeXBlID0gdGhpcy5pbmZlclJldHVyblR5cGUobWV0aG9kLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXG5cdFx0aWYgKHBhcmFtcykge1xuXHRcdFx0cmV0dXJuIGAoJHtwYXJhbXN9KSA9PiAke3JldHVyblR5cGV9YDtcblx0XHR9XG5cdFx0cmV0dXJuIGAoKSA9PiAke3JldHVyblR5cGV9YDtcblx0fVxuXG5cdHByaXZhdGUgaGFzR2VuZXJhdGVkVGhpc0Fubm90YXRpb24gKGhhbmRsZXI6IENvbnN0cnVjdG9ySGFuZGxlcik6IGJvb2xlYW4ge1xuXHRcdGlmICh0aGlzLmhhc0dlbmVyYXRlZFR5cGVSZWZlcmVuY2UoaGFuZGxlcikpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHRpZiAoIXRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGhhbmRsZXIpICYmICF0cy5pc0Fycm93RnVuY3Rpb24oaGFuZGxlcikgJiZcblx0XHRcdCF0cy5pc0Z1bmN0aW9uRGVjbGFyYXRpb24oaGFuZGxlcikpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBoYW5kbGVyLnBhcmFtZXRlcnMpIHtcblx0XHRcdGNvbnN0IGlzVGhpcyA9IHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSAmJiBwYXJhbS5uYW1lLnRleHQgPT09ICd0aGlzJztcblx0XHRcdGlmICghaXNUaGlzIHx8ICFwYXJhbS50eXBlIHx8ICF0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHBhcmFtLnR5cGUpIHx8XG5cdFx0XHRcdCF0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCB0eXBlTmFtZSA9IHBhcmFtLnR5cGUudHlwZU5hbWUudGV4dDtcblx0XHRcdGlmICh0aGlzLmN1cnJlbnRHcmFwaEFuY2hvcj8ubmFtZSA9PT0gdHlwZU5hbWUgfHwgdGhpcy5jdXJyZW50R3JhcGhBbmNob3I/LmZ1bGxQYXRoID09PSB0eXBlTmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGdyYXBoVHlwZSA9IHRoaXMuZ3JhcGguZmluZFR5cGVCeU5hbWUodHlwZU5hbWUpO1xuXHRcdFx0aWYgKGdyYXBoVHlwZSkge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0cHJpdmF0ZSBoYXNBbnlUaGlzQW5ub3RhdGlvbiAoaGFuZGxlcjogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkKTogYm9vbGVhbiB7XG5cdFx0aWYgKCFoYW5kbGVyIHx8ICghdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oaGFuZGxlcikgJiYgIXRzLmlzQXJyb3dGdW5jdGlvbihoYW5kbGVyKSAmJlxuXHRcdFx0IXRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihoYW5kbGVyKSkpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gaGFuZGxlci5wYXJhbWV0ZXJzLnNvbWUocGFyYW0gPT4ge1xuXHRcdFx0Y29uc3QgbWF0Y2hlcyA9IHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSAmJiBwYXJhbS5uYW1lLnRleHQgPT09ICd0aGlzJyAmJlxuXHRcdFx0XHRwYXJhbS50eXBlPy5raW5kID09PSB0cy5TeW50YXhLaW5kLkFueUtleXdvcmQ7XG5cdFx0XHRyZXR1cm4gbWF0Y2hlcztcblx0XHR9KTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBgdGhpc2AgcGFyYW1ldGVyIHR5cGUgYW5ub3RhdGlvblxuXHRcdCogSGFuZGxlcyBwYXR0ZXJucyBsaWtlOiBmdW5jdGlvbih0aGlzOiBTb21lVHlwZSwgZGF0YTogU29tZVR5cGUpIHsgfVxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdFRoaXNQYXJhbVByb3BlcnRpZXMgKGhhbmRsZXJBcmc6IEZ1bmN0aW9uQ29uc3RydWN0b3JIYW5kbGVyKTpcblx0XHRNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCBwcm9wZXJ0aWVzID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblxuXHRcdC8vIEZpbmQgdGhlIGB0aGlzYCBwYXJhbWV0ZXIgKGlmIGFueSlcblx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGhhbmRsZXJBcmcucGFyYW1ldGVycykge1xuXHRcdFx0aWYgKHBhcmFtLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpICYmIHBhcmFtLm5hbWUudGV4dCA9PT0gJ3RoaXMnICYmIHBhcmFtLnR5cGUpIHtcblx0XHRcdFx0Ly8gQ2hlY2sgaWYgaXQncyBhIHR5cGUgcmVmZXJlbmNlIChlLmcuLCBgdGhpczogdXNhZ2VgKVxuXHRcdFx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZShwYXJhbS50eXBlKSkge1xuXHRcdFx0XHRcdGNvbnN0IHR5cGVOYW1lID0gdHMuaXNJZGVudGlmaWVyKHBhcmFtLnR5cGUudHlwZU5hbWUpXG5cdFx0XHRcdFx0XHQ/IHBhcmFtLnR5cGUudHlwZU5hbWUudGV4dFxuXHRcdFx0XHRcdFx0OiAnJztcblxuXHRcdFx0XHRcdC8vIFJlc29sdmUgdGhyb3VnaCB0aGUgcmVmZXJlbmNpbmcgZmlsZSdzIG93biBpbXBvcnRzIGZpcnN0IChGMTApXG5cdFx0XHRcdFx0Y29uc3QgZGVjbCA9IHR5cGVOYW1lXG5cdFx0XHRcdFx0XHQ/IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24odHlwZU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSlcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0XHRcdGlmIChkZWNsKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBkZWNsUHJvcGVydGllcyA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllcyhkZWNsKTtcblx0XHRcdFx0XHRcdGZvciAoY29uc3QgWyBwcm9wTmFtZSwgaW5mbyBdIG9mIGRlY2xQcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KHByb3BOYW1lLCBpbmZvKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gQ2hlY2sgaWYgaXQncyBkaXJlY3RseSBhbiBpbmxpbmUgdHlwZSBsaXRlcmFsIChlLmcuLCBgdGhpczogeyBpZDogc3RyaW5nIH1gKVxuXHRcdFx0XHRlbHNlIGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZShwYXJhbS50eXBlKSkge1xuXHRcdFx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIHBhcmFtLnR5cGUubWVtYmVycykge1xuXHRcdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQocHJvcE5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRuYW1lICAgICA6IHByb3BOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gRm91bmQgdGhlIGB0aGlzYCBwYXJhbWV0ZXIsIG5vIG5lZWQgdG8gY29udGludWVcblx0XHRcdFx0YnJlYWs7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHQvKipcblx0XHQqIEluZmVyIFR5cGVTY3JpcHQgdHlwZSBmcm9tIHR5cGUgbm9kZVxuXHRcdCovXG5cdC8qKlxuXHQgKiBJbmZlciBUeXBlU2NyaXB0IHR5cGUgZnJvbSB0eXBlIG5vZGVcblx0ICovXG5cdHByaXZhdGUgaW5mZXJUeXBlICh0eXBlTm9kZT86IHRzLlR5cGVOb2RlKTogc3RyaW5nIHtcblx0XHRpZiAoIXR5cGVOb2RlKSB7XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblxuXHRcdHN3aXRjaCAodHlwZU5vZGUua2luZCkge1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5TdHJpbmdLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdW1iZXJLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Cb29sZWFuS2V5d29yZDpcblx0XHRcdHJldHVybiAnYm9vbGVhbic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVuZGVmaW5lZEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3VuZGVmaW5lZCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bGxLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdudWxsJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQW55S2V5d29yZDpcblx0XHRcdHJldHVybiAnYW55Jztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5rbm93bktleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Wb2lkS2V5d29yZDpcblx0XHRcdHJldHVybiAndm9pZCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkFycmF5VHlwZTpcblx0XHRcdHJldHVybiBgQXJyYXk8JHsgIHRoaXMuaW5mZXJUeXBlKCh0eXBlTm9kZSBhcyB0cy5BcnJheVR5cGVOb2RlKS5lbGVtZW50VHlwZSkgIH0+YDtcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZUxpdGVyYWw6IHtcblx0XHRcdC8vIElubGluZS1leHBhbmQgdHlwZSBsaXRlcmFscyBpbnN0ZWFkIG9mIGNvbGxhcHNpbmcgdG8gJ29iamVjdCdcblx0XHRcdGNvbnN0IHR5cGVMaXQgPSB0eXBlTm9kZSBhcyB0cy5UeXBlTGl0ZXJhbE5vZGU7XG5cdFx0XHRjb25zdCBwcm9wczogc3RyaW5nW10gPSBbXTtcblx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIHR5cGVMaXQubWVtYmVycykge1xuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Y29uc3Qgb3B0aW9uYWwgPSBtZW1iZXIucXVlc3Rpb25Ub2tlbiA/ICc/JyA6ICcnO1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0cHJvcHMucHVzaChgJHtwcm9wTmFtZX0ke29wdGlvbmFsfTogJHt0eXBlfWApO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gYHsgJHtwcm9wcy5qb2luKCc7ICcpfSB9YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkxpdGVyYWxUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgc3RyaW5nIGxpdGVyYWwgdHlwZXMgbGlrZSAndXNlcicsICdhZG1pbicsIGV0Yy5cblx0XHRcdGNvbnN0IHsgbGl0ZXJhbCB9ID0gKHR5cGVOb2RlIGFzIHRzLkxpdGVyYWxUeXBlTm9kZSk7XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGxpdGVyYWwpKSB7XG5cdFx0XHRcdC8vIFJldHVybiB0aGUgYWN0dWFsIGxpdGVyYWwgdmFsdWUgKGUuZy4sICd1c2VyJyBpbnN0ZWFkIG9mIHN0cmluZylcblx0XHRcdFx0cmV0dXJuIGAnJHtsaXRlcmFsLnRleHR9J2A7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNOdW1lcmljTGl0ZXJhbChsaXRlcmFsKSkge1xuXHRcdFx0XHRyZXR1cm4gbGl0ZXJhbC50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0aWYgKGxpdGVyYWwua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCkge1xuXHRcdFx0XHRyZXR1cm4gJ3RydWUnO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGxpdGVyYWwua2luZCA9PT0gdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQpIHtcblx0XHRcdFx0cmV0dXJuICdmYWxzZSc7XG5cdFx0XHR9XG5cdFx0XHRpZiAobGl0ZXJhbC5raW5kID09PSB0cy5TeW50YXhLaW5kLk51bGxLZXl3b3JkKSB7XG5cdFx0XHRcdHJldHVybiAnbnVsbCc7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZVJlZmVyZW5jZToge1xuXHRcdFx0Ly8gSGFuZGxlIHR5cGUgcmVmZXJlbmNlcyBsaWtlIE1hcDxzdHJpbmcsIG51bWJlcj4sIFByb3BlcnR5SW5mbywgZXRjLlxuXHRcdFx0Y29uc3QgdHlwZVJlZiA9IHR5cGVOb2RlIGFzIHRzLlR5cGVSZWZlcmVuY2VOb2RlO1xuXG5cdFx0XHQvLyBRdWFsaWZpZWQgbmFtZXMgKE5hbWVzcGFjZS5UeXBlKTogcmVzb2x2ZSB0aHJvdWdoIG5hbWVzcGFjZSBpbXBvcnRzXG5cdFx0XHRpZiAodHMuaXNRdWFsaWZpZWROYW1lKHR5cGVSZWYudHlwZU5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHJlc29sdmVkUXVhbGlmaWVkID0gdGhpcy5pbmZlclF1YWxpZmllZFR5cGVSZWZlcmVuY2UodHlwZVJlZik7XG5cdFx0XHRcdGlmIChyZXNvbHZlZFF1YWxpZmllZCAhPT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHJlc29sdmVkUXVhbGlmaWVkO1xuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIHVucmVzb2x2ZWQgcXVhbGlmaWVkIHJlZmVyZW5jZXMgbXVzdCBub3QgbGVhayBhIGJhcmUgbmFtZVxuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXG5cdFx0XHRjb25zdCB0eXBlTmFtZSA9IHRzLmlzSWRlbnRpZmllcih0eXBlUmVmLnR5cGVOYW1lKSA/IHR5cGVSZWYudHlwZU5hbWUudGV4dCA6ICd1bmtub3duJztcblxuXHRcdFx0Ly8gSW1wb3J0LWF3YXJlIHJlZmVyZW5jZWQtdHlwZSByZXNvbHV0aW9uIChGMTApOiBhIGRlY2xhcmF0aW9uXG5cdFx0XHQvLyByZWFjaGVkIHRocm91Z2ggdGhlIGN1cnJlbnQgZmlsZSdzIG93biBpbXBvcnRzIChvciBpdHMgbG9jYWxzLFxuXHRcdFx0Ly8gb3IgYSB1bmlxdWUgcHJvZ3JhbS13aWRlIGRlY2xhcmF0aW9uKSBleHBhbmRzIGlubGluZVxuXHRcdFx0Y29uc3Qgc2ltcGxlUmVmID0gdGhpcy5yZXNvbHZlU2ltcGxlVHlwZVJlZmVyZW5jZSh0eXBlTmFtZSwgdHlwZVJlZi50eXBlQXJndW1lbnRzLCB0eXBlUmVmKTtcblx0XHRcdGlmIChzaW1wbGVSZWYgIT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRyZXR1cm4gc2ltcGxlUmVmO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBCdWlsZCBnZW5lcmljIHR5cGUgYXJndW1lbnRzXG5cdFx0XHRjb25zdCB0eXBlQXJncyA9ICh0eXBlUmVmLnR5cGVBcmd1bWVudHMgPz8gW10pLm1hcChhcmcgPT4gdGhpcy5pbmZlclR5cGUoYXJnKSk7XG5cdFx0XHRyZXR1cm4gYCR7dHlwZU5hbWV9PCR7dHlwZUFyZ3Muam9pbignLCAnKX0+YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVuaW9uVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHVuaW9uIHR5cGVzIGxpa2UgJ2EnIHwgJ2InIHwgJ2MnXG5cdFx0XHRjb25zdCB1bmlvblR5cGUgPSB0eXBlTm9kZSBhcyB0cy5VbmlvblR5cGVOb2RlO1xuXHRcdFx0Y29uc3QgdHlwZXMgPSB1bmlvblR5cGUudHlwZXMubWFwKHQgPT4gdGhpcy5pbmZlclR5cGUodCkpO1xuXHRcdFx0cmV0dXJuIHR5cGVzLmpvaW4oJyB8ICcpO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuSW50ZXJzZWN0aW9uVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIGludGVyc2VjdGlvbiB0eXBlcyBsaWtlIFR5cGVBICYgVHlwZUJcblx0XHRcdGNvbnN0IGludGVyc2VjdGlvblR5cGUgPSB0eXBlTm9kZSBhcyB0cy5JbnRlcnNlY3Rpb25UeXBlTm9kZTtcblx0XHRcdGNvbnN0IHR5cGVzID0gaW50ZXJzZWN0aW9uVHlwZS50eXBlcy5tYXAodCA9PiB0aGlzLmluZmVyVHlwZSh0KSk7XG5cdFx0XHRyZXR1cm4gdHlwZXMuam9pbignICYgJyk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UdXBsZVR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSB0dXBsZSB0eXBlcyBsaWtlIFtzdHJpbmcsIG51bWJlcl1cblx0XHRcdGNvbnN0IHR1cGxlVHlwZSA9IHR5cGVOb2RlIGFzIHRzLlR1cGxlVHlwZU5vZGU7XG5cdFx0XHRjb25zdCBlbGVtZW50cyA9IHR1cGxlVHlwZS5lbGVtZW50cy5tYXAoZWxlbSA9PiB0aGlzLmluZmVyVHlwZShlbGVtIGFzIHRzLlR5cGVOb2RlKSk7XG5cdFx0XHRyZXR1cm4gYFske2VsZW1lbnRzLmpvaW4oJywgJyl9XWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5PcHRpb25hbFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBvcHRpb25hbCBlbGVtZW50IGluIHR1cGxlOiBzdHJpbmc/XG5cdFx0XHRjb25zdCBvcHRpb25hbFR5cGUgPSB0eXBlTm9kZSBhcyB0cy5PcHRpb25hbFR5cGVOb2RlO1xuXHRcdFx0cmV0dXJuIGAke3RoaXMuaW5mZXJUeXBlKG9wdGlvbmFsVHlwZS50eXBlKSAgfT9gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuUmVzdFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSByZXN0IGVsZW1lbnQ6IC4uLlRcblx0XHRcdGNvbnN0IHJlc3RUeXBlID0gdHlwZU5vZGUgYXMgdHMuUmVzdFR5cGVOb2RlO1xuXHRcdFx0cmV0dXJuIGAuLi4keyAgdGhpcy5pbmZlclR5cGUocmVzdFR5cGUudHlwZSl9YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlBhcmVudGhlc2l6ZWRUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgcGFyZW50aGVzaXplZCB0eXBlczogKEEgfCBCKVxuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJUeXBlKCh0eXBlTm9kZSBhcyB0cy5QYXJlbnRoZXNpemVkVHlwZU5vZGUpLnR5cGUpO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuSW5kZXhlZEFjY2Vzc1R5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBpbmRleGVkIGFjY2VzczogVFtLXVxuXHRcdFx0Y29uc3QgaW5kZXhlZCA9IHR5cGVOb2RlIGFzIHRzLkluZGV4ZWRBY2Nlc3NUeXBlTm9kZTtcblx0XHRcdC8vIEYyMzogdW53cmFwIHBhcmVudGhlc2VzIGFyb3VuZCB0aGUgb2JqZWN0IOKAlCBgKHR5cGVvZlxuXHRcdFx0Ly8gbGlzdClbbnVtYmVyXWAgbXVzdCB0YWtlIHRoZSB0eXBlb2YgYnJhbmNoIGxpa2UgdGhlIGJhcmVcblx0XHRcdC8vIHNwZWxsaW5nOyBvdGhlcndpc2UgdGhlIGdlbmVyYWwgcGF0aCBpbmZlcnMgdGhlIHVuaW9uIGFuZFxuXHRcdFx0Ly8gZ2x1ZXMgdGhlIHN1ZmZpeCBvbnRvIHRoZSBMQVNUIG1lbWJlclxuXHRcdFx0Ly8gKGAnYScgfCAnYidbbnVtYmVyXWApXG5cdFx0XHRsZXQgb2JqZWN0Tm9kZTogdHMuVHlwZU5vZGUgPSBpbmRleGVkLm9iamVjdFR5cGU7XG5cdFx0XHR3aGlsZSAodHMuaXNQYXJlbnRoZXNpemVkVHlwZU5vZGUob2JqZWN0Tm9kZSkpIHtcblx0XHRcdFx0b2JqZWN0Tm9kZSA9IG9iamVjdE5vZGUudHlwZTtcblx0XHRcdH1cblx0XHRcdC8vIGB0eXBlb2YgY29uc3RBcnJheVtLXWAg4oCUIGVsZW1lbnQgdHlwZSBvZiBhIHRyYWNrZWQgY29uc3QgYXJyYXk6XG5cdFx0XHQvLyBlbWl0IHRoZSBlbGVtZW50IGxpdGVyYWwgdW5pb24gZGlyZWN0bHkgKGFzc2VtYmxpbmdcblx0XHRcdC8vIGB1bmlvbltLXWAgdGV4dCB3b3VsZCBtaXNyZWFkIHByZWNlZGVuY2UsIGFuZCB3aGVuIHRoZSBjb25zdFxuXHRcdFx0Ly8gaXMgbm90IHN0YXRpY2FsbHkgdmlzaWJsZSB0aGUgaG9uZXN0IGFuc3dlciBpcyBgdW5rbm93bmAsXG5cdFx0XHQvLyBuZXZlciBhIGJhcmUgYHR5cGVvZiBuYW1lYCBxdWVyeSlcblx0XHRcdGlmICh0cy5pc1R5cGVRdWVyeU5vZGUob2JqZWN0Tm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKG9iamVjdE5vZGUuZXhwck5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHF1ZXJ5TmFtZSA9IG9iamVjdE5vZGUuZXhwck5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgYXJyYXlMaXRlcmFsID0gdGhpcy5maW5kUmVmZXJlbmNlZENvbnN0QXJyYXkocXVlcnlOYW1lLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHRjb25zdCBsaXRlcmFscyA9IGFycmF5TGl0ZXJhbCA/IHRoaXMubGl0ZXJhbFR5cGVzT2ZBcnJheShhcnJheUxpdGVyYWwpIDogdW5kZWZpbmVkO1xuXHRcdFx0XHRpZiAoIWxpdGVyYWxzKSB7XG5cdFx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAodHMuaXNMaXRlcmFsVHlwZU5vZGUoaW5kZXhlZC5pbmRleFR5cGUpICYmIHRzLmlzTnVtZXJpY0xpdGVyYWwoaW5kZXhlZC5pbmRleFR5cGUubGl0ZXJhbCkpIHtcblx0XHRcdFx0XHRjb25zdCBlbGVtZW50SW5kZXggPSBwYXJzZUludChpbmRleGVkLmluZGV4VHlwZS5saXRlcmFsLnRleHQsIDEwKTtcblx0XHRcdFx0XHRjb25zdCBlbGVtZW50ID0gbGl0ZXJhbHNbIGVsZW1lbnRJbmRleCBdO1xuXHRcdFx0XHRcdGNvbnN0IGVsZW1lbnRSZXN1bHQgPSBlbGVtZW50ID09PSB1bmRlZmluZWQgPyAndW5rbm93bicgOiBlbGVtZW50O1xuXHRcdFx0XHRcdHJldHVybiBlbGVtZW50UmVzdWx0O1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IHVuaW9uUmVzdWx0ID0gbGl0ZXJhbHMuam9pbignIHwgJyk7XG5cdFx0XHRcdHJldHVybiB1bmlvblJlc3VsdDtcblx0XHRcdH1cblx0XHRcdGxldCBvYmplY3RUeXBlID0gdGhpcy5pbmZlclR5cGUob2JqZWN0Tm9kZSk7XG5cdFx0XHRjb25zdCBpbmRleFR5cGUgPSB0aGlzLmluZmVyVHlwZShpbmRleGVkLmluZGV4VHlwZSk7XG5cdFx0XHQvLyBJZiBvYmplY3RUeXBlIGlzICdvYmplY3QnLCB0cnkgdG8gcmVzb2x2ZSB0aGUgdW5kZXJseWluZyByZWZlcmVuY2VkIHR5cGVcblx0XHRcdGlmIChvYmplY3RUeXBlID09PSAnb2JqZWN0JyAmJiB0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKG9iamVjdE5vZGUpKSB7XG5cdFx0XHRcdGNvbnN0IHJlZk5hbWUgPSB0cy5pc0lkZW50aWZpZXIob2JqZWN0Tm9kZS50eXBlTmFtZSkgPyBvYmplY3ROb2RlLnR5cGVOYW1lLnRleHQgOiAnJztcblx0XHRcdFx0aWYgKHJlZk5hbWUpIHtcblx0XHRcdFx0XHRjb25zdCBkZWNsID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihyZWZOYW1lLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHRcdGlmIChkZWNsKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMuZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihkZWNsKTtcblx0XHRcdFx0XHRcdGlmIChleHBhbmRlZCkge1xuXHRcdFx0XHRcdFx0XHRvYmplY3RUeXBlID0gZXhwYW5kZWQ7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBJbnZhcmlhbnQ6IGFuIGluZGV4IHN1ZmZpeCBtdXN0IE5FVkVSIGJlIGdsdWVkIG9udG8gYW5cblx0XHRcdC8vIHVucmVzb2x2ZWQvZmFsbGJhY2sgdGFyZ2V0IOKAlCBgdW5rbm93bltudW1iZXJdYCAvIGBvYmplY3RbS11gXG5cdFx0XHQvLyBhcmUgaW52YWxpZCBUeXBlU2NyaXB0IGluIHRoZSBnZW5lcmF0ZWQgZmlsZSAoaGFyZCBjb21waWxlXG5cdFx0XHQvLyBicmVhaywgRjE3KS4gV2hlbiBlaXRoZXIgc2lkZSBkaWQgbm90IHJlc29sdmUsIHRoZSBXSE9MRVxuXHRcdFx0Ly8gaW5kZXhlZCBhY2Nlc3MgZGVncmFkZXMgdG8gYHVua25vd25gLlxuXHRcdFx0Y29uc3QgdGFyZ2V0VW5yZXNvbHZlZCA9IG9iamVjdFR5cGUgPT09ICd1bmtub3duJyB8fCBvYmplY3RUeXBlID09PSAnb2JqZWN0Jztcblx0XHRcdGNvbnN0IGluZGV4VW5yZXNvbHZlZCA9IGluZGV4VHlwZSA9PT0gJ3Vua25vd24nO1xuXHRcdFx0aWYgKHRhcmdldFVucmVzb2x2ZWQgfHwgaW5kZXhVbnJlc29sdmVkKSB7XG5cdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gYCR7b2JqZWN0VHlwZX1bJHtpbmRleFR5cGV9XWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlT3BlcmF0b3I6IHtcblx0XHRcdC8vIEhhbmRsZSBrZXlvZiwgcmVhZG9ubHksIHVuaXF1ZSBvcGVyYXRvcnNcblx0XHRcdGNvbnN0IHR5cGVPcCA9IHR5cGVOb2RlIGFzIHRzLlR5cGVPcGVyYXRvck5vZGU7XG5cdFx0XHRjb25zdCBvcGVyYXRvciA9IHRzLlN5bnRheEtpbmRbIHR5cGVPcC5vcGVyYXRvciBdO1xuXHRcdFx0cmV0dXJuIGAke29wZXJhdG9yfSAke3RoaXMuaW5mZXJUeXBlKHR5cGVPcC50eXBlKX1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZVF1ZXJ5OiB7XG5cdFx0XHQvLyBgdHlwZW9mIHhgIGFzIGEgRklFTEQgVFlQRTogdGhlIGdlbmVyYXRlZCBmaWxlIGhhcyBubyBpbXBvcnRzLFxuXHRcdFx0Ly8gc28gYSBiYXJlIGB0eXBlb2YgeGAgd291bGQgYmUgYW4gdW5yZXNvbHZhYmxlIG5hbWUgZG93bnN0cmVhbS5cblx0XHRcdC8vIFdoZW4geCBpcyBhIHRyYWNrZWQgY29uc3QgYXJyYXksIGVtaXQgaXRzIGVsZW1lbnQgbGl0ZXJhbFxuXHRcdFx0Ly8gdW5pb247IG90aGVyd2lzZSBkZWdyYWRlIHRvIGB1bmtub3duYC4gKEluc3RhbmNlVHlwZTx0eXBlb2YgWD5cblx0XHRcdC8vIGdyYXBoIHR5cGVzIGFyZSBoYW5kbGVkIGluIHJlc29sdmVTaW1wbGVUeXBlUmVmZXJlbmNlIGJlZm9yZVxuXHRcdFx0Ly8gaW5mZXJUeXBlIHJ1bnMuKVxuXHRcdFx0Y29uc3QgdHlwZVF1ZXJ5ID0gdHlwZU5vZGUgYXMgdHMuVHlwZVF1ZXJ5Tm9kZTtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIodHlwZVF1ZXJ5LmV4cHJOYW1lKSkge1xuXHRcdFx0XHRjb25zdCB1bmlvbiA9IHRoaXMudHlwZU9mQ29uc3RBcnJheVVuaW9uKHR5cGVRdWVyeS5leHByTmFtZS50ZXh0LCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHRpZiAodW5pb24pIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5pb247XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGRlZmF1bHQ6XG5cdFx0XHQvLyBGb3IgY29tcGxleCB0eXBlcywgcmV0dXJuIHRoZSB0ZXh0IHJlcHJlc2VudGF0aW9uXG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdCogSW5mZXIgcmV0dXJuIHR5cGUgZnJvbSBhIG1ldGhvZCBkZWNsYXJhdGlvblxuXHRcdCogVXNlcyBleHBsaWNpdCByZXR1cm4gdHlwZSBhbm5vdGF0aW9uIG9yIGluZmVycyBmcm9tIHJldHVybiBzdGF0ZW1lbnRzXG5cdFx0Ki9cblx0cHJpdmF0ZSBpbmZlclJldHVyblR5cGUgKG1ldGhvZDogdHMuTWV0aG9kRGVjbGFyYXRpb24sIGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz4pOiBzdHJpbmcge1xuXHRcdC8vIElmIG1ldGhvZCBoYXMgZXhwbGljaXQgcmV0dXJuIHR5cGUgYW5ub3RhdGlvbiwgdXNlIGl0XG5cdFx0aWYgKG1ldGhvZC50eXBlKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclR5cGUobWV0aG9kLnR5cGUpO1xuXHRcdH1cblxuXHRcdC8vIE90aGVyd2lzZSwgdHJ5IHRvIGluZmVyIGZyb20gcmV0dXJuIHN0YXRlbWVudHMgaW4gdGhlIG1ldGhvZCBib2R5XG5cdFx0aWYgKG1ldGhvZC5ib2R5KSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclJldHVyblR5cGVGcm9tQm9keShtZXRob2QuYm9keSwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHR9XG5cblx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBJbmZlciByZXR1cm4gdHlwZSBieSBhbmFseXppbmcgcmV0dXJuIHN0YXRlbWVudHMgaW4gdGhlIG1ldGhvZCBib2R5XG5cdFx0Ki9cblx0cHJpdmF0ZSBpbmZlclJldHVyblR5cGVGcm9tQm9keSAoYm9keTogdHMuQmxvY2ssIGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz4pOiBzdHJpbmcge1xuXHRcdGNvbnN0IHJldHVyblR5cGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cblx0XHRjb25zdCB2aXNpdCA9IChub2RlOiB0cy5Ob2RlKTogdm9pZCA9PiB7XG5cdFx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQobm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihub2RlLmV4cHJlc3Npb24sIHVuZGVmaW5lZCwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0aWYgKHR5cGUgIT09ICd1bmtub3duJykge1xuXHRcdFx0XHRcdHJldHVyblR5cGVzLmFkZCh0eXBlKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIHZpc2l0KTtcblx0XHR9O1xuXG5cdFx0dmlzaXQoYm9keSk7XG5cblx0XHRpZiAocmV0dXJuVHlwZXMuc2l6ZSA9PT0gMCkge1xuXHRcdFx0cmV0dXJuICd2b2lkJztcblx0XHR9XG5cdFx0aWYgKHJldHVyblR5cGVzLnNpemUgPT09IDEpIHtcblx0XHRcdHJldHVybiBBcnJheS5mcm9tKHJldHVyblR5cGVzKVsgMCBdO1xuXHRcdH1cblx0XHRyZXR1cm4gQXJyYXkuZnJvbShyZXR1cm5UeXBlcykuam9pbignIHwgJyk7XG5cdH1cblxuXHQvKipcblx0ICogSW5mZXIgdHlwZSBmcm9tIGluaXRpYWxpemVyXG5cdCAqL1xuXHRwcml2YXRlIGluZmVyVHlwZUZyb21Jbml0aWFsaXplciAoXG5cdFx0aW5pdGlhbGl6ZXI6IHRzLkV4cHJlc3Npb24sXG5cdFx0ZGF0YVR5cGVNYXA/OiBNYXA8c3RyaW5nLCBzdHJpbmc+LFxuXHRcdGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz5cblx0KTogc3RyaW5nIHtcblx0XHRzd2l0Y2ggKGluaXRpYWxpemVyLmtpbmQpIHtcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuU3RyaW5nTGl0ZXJhbDpcblx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVtZXJpY0xpdGVyYWw6XG5cdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkOlxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdWxsS2V5d29yZDpcblx0XHRcdHJldHVybiAnbnVsbCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVuZGVmaW5lZEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3VuZGVmaW5lZCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkFycmF5TGl0ZXJhbEV4cHJlc3Npb246XG5cdFx0XHRyZXR1cm4gJ0FycmF5PHVua25vd24+Jztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb246XG5cdFx0XHRyZXR1cm4gJ29iamVjdCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk5ld0V4cHJlc3Npb246IHtcblx0XHRcdC8vIEhhbmRsZSBuZXcgRGF0ZSgpLCBuZXcgTWFwKCksIGV0Yy5cblx0XHRcdGNvbnN0IG5ld0V4cHIgPSBpbml0aWFsaXplciBhcyB0cy5OZXdFeHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihuZXdFeHByLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IGNvbnN0cnVjdGVkTmFtZSA9IG5ld0V4cHIuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHQvLyBFeHBsaWNpdCB0eXBlIGFyZ3VtZW50cyBzdXJ2aXZlOiBuZXcgTWFwPHN0cmluZywgb2JqZWN0PigpXG5cdFx0XHRcdC8vIGVtaXRzIE1hcDxzdHJpbmcsIG9iamVjdD4g4oCUIGRyb3BwaW5nIHRoZW0gcHJvZHVjZWQgYSBiYXJlXG5cdFx0XHRcdC8vIGdlbmVyaWMsIHdoaWNoIGlzIGludmFsaWQgVFMgaW4gdGhlIGdlbmVyYXRlZCBmaWxlIChUUzIzMTQpXG5cdFx0XHRcdGlmIChuZXdFeHByLnR5cGVBcmd1bWVudHMgJiYgbmV3RXhwci50eXBlQXJndW1lbnRzLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0XHRjb25zdCBhcmdUeXBlcyA9IG5ld0V4cHIudHlwZUFyZ3VtZW50cy5tYXAoYXJnID0+IHRoaXMuaW5mZXJUeXBlKGFyZykpO1xuXHRcdFx0XHRcdHJldHVybiBgJHtjb25zdHJ1Y3RlZE5hbWV9PCR7YXJnVHlwZXMuam9pbignLCAnKX0+YDtcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBObyB0eXBlIGFyZ3VtZW50czogYSBrbm93biBnZW5lcmljIGdsb2JhbCBzdGlsbCBuZWVkcyBpdHNcblx0XHRcdFx0Ly8gcGFyYW1ldGVyIGxpc3Qg4oCUIGZpbGwgaXQgd2l0aCB1bmtub3duIChNYXA8dW5rbm93biwgdW5rbm93bj4pXG5cdFx0XHRcdGNvbnN0IGRlZmF1bHRlZEdlbmVyaWMgPSBHRU5FUklDX0dMT0JBTF9ERUZBVUxUX0FSR1MuZ2V0KGNvbnN0cnVjdGVkTmFtZSk7XG5cdFx0XHRcdGlmIChkZWZhdWx0ZWRHZW5lcmljKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGRlZmF1bHRlZEdlbmVyaWM7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIGNvbnN0cnVjdGVkTmFtZTtcblx0XHRcdH1cblx0XHRcdHJldHVybiAnb2JqZWN0Jztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkJpbmFyeUV4cHJlc3Npb246IHtcblx0XHRcdC8vIEhhbmRsZSBhcml0aG1ldGljIG9wZXJhdGlvbnM6IGEgKiBiLCBhICsgYiwgYSAtIGIsIGEgLyBiXG5cdFx0XHRjb25zdCBiaW5hcnlFeHByID0gaW5pdGlhbGl6ZXIgYXMgdHMuQmluYXJ5RXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IGxlZnRUeXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIoYmluYXJ5RXhwci5sZWZ0LCBkYXRhVHlwZU1hcCwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdGNvbnN0IHJpZ2h0VHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKGJpbmFyeUV4cHIucmlnaHQsIGRhdGFUeXBlTWFwLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0XHRcblx0XHRcdC8vIENoZWNrIGlmIGl0J3MgYW4gYXJpdGhtZXRpYyBvcGVyYXRvclxuXHRcdFx0Y29uc3Qgb3BlcmF0b3IgPSBiaW5hcnlFeHByLm9wZXJhdG9yVG9rZW4ua2luZDtcblx0XHRcdGlmIChvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5Bc3Rlcmlza1Rva2VuIHx8XG5cdFx0XHRcdCAgICBvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5TbGFzaFRva2VuIHx8XG5cdFx0XHRcdCAgICBvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5NaW51c1Rva2VuIHx8XG5cdFx0XHRcdCAgICBvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5QZXJjZW50VG9rZW4pIHtcblx0XHRcdFx0Ly8gQXJpdGhtZXRpYyBvcGVyYXRpb25zIG9uIG51bWJlcnMgcHJvZHVjZSBudW1iZXJzXG5cdFx0XHRcdGlmICgobGVmdFR5cGUgPT09ICdudW1iZXInIHx8IGxlZnRUeXBlID09PSAndW5rbm93bicpICYmXG5cdFx0XHRcdFx0ICAgIChyaWdodFR5cGUgPT09ICdudW1iZXInIHx8IHJpZ2h0VHlwZSA9PT0gJ3Vua25vd24nKSkge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLlBsdXNUb2tlbikge1xuXHRcdFx0XHQvLyBQbHVzIGNhbiBiZSBhZGRpdGlvbiBvciBzdHJpbmcgY29uY2F0ZW5hdGlvblxuXHRcdFx0XHRpZiAobGVmdFR5cGUgPT09ICdzdHJpbmcnIHx8IHJpZ2h0VHlwZSA9PT0gJ3N0cmluZycpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGxlZnRUeXBlID09PSAnbnVtYmVyJyAmJiByaWdodFR5cGUgPT09ICdudW1iZXInKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgcHJvcGVydHkgYWNjZXNzIGxpa2UgZGF0YS52YWx1ZSwgZGF0YS5pZFxuXHRcdFx0aWYgKGRhdGFUeXBlTWFwKSB7XG5cdFx0XHRcdGNvbnN0IGFjY2Vzc0NoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGluaXRpYWxpemVyKTtcblx0XHRcdFx0aWYgKGFjY2Vzc0NoYWluKSB7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IGRhdGFUeXBlTWFwLmdldChhY2Nlc3NDaGFpbik7XG5cdFx0XHRcdFx0aWYgKHR5cGUpIHtcblx0XHRcdFx0XHRcdHJldHVybiB0eXBlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gSGFuZGxlIHRoaXMubWFwLnNpemUgcGF0dGVybiAoTWFwLnNpemUgcmV0dXJucyBudW1iZXIpXG5cdFx0XHRjb25zdCBwcm9wQWNjZXNzID0gaW5pdGlhbGl6ZXIgYXMgdHMuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKHByb3BBY2Nlc3MuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y29uc3Qgb3V0ZXJQcm9wID0gcHJvcEFjY2Vzcy5leHByZXNzaW9uO1xuXHRcdFx0XHQvLyBDaGVjayBmb3IgdGhpcy5tYXAgcGF0dGVyblxuXHRcdFx0XHRsZXQgaW5uZXJOYW1lID0gJyc7XG5cdFx0XHRcdGlmIChvdXRlclByb3AuZXhwcmVzc2lvbi5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0aW5uZXJOYW1lID0gJ3RoaXMnO1xuXHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihvdXRlclByb3AuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRpbm5lck5hbWUgPSBvdXRlclByb3AuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IG1hcFByb3AgPSBvdXRlclByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBmaW5hbFByb3AgPSBwcm9wQWNjZXNzLm5hbWUudGV4dDtcblx0XHRcdFx0Ly8gdGhpcy5tYXAuc2l6ZSAtPiBudW1iZXJcblx0XHRcdFx0aWYgKGlubmVyTmFtZSA9PT0gJ3RoaXMnICYmIG1hcFByb3AgPT09ICdtYXAnICYmIGZpbmFsUHJvcCA9PT0gJ3NpemUnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuSWRlbnRpZmllcjoge1xuXHRcdFx0Ly8gSGFuZGxlIGlkZW50aWZpZXIgcmVmZXJlbmNlcyBpZiBpbiBkYXRhVHlwZU1hcFxuXHRcdFx0aWYgKGRhdGFUeXBlTWFwKSB7XG5cdFx0XHRcdGNvbnN0IG5hbWUgPSAoaW5pdGlhbGl6ZXIgYXMgdHMuSWRlbnRpZmllcikudGV4dDtcblx0XHRcdFx0Y29uc3QgdHlwZSA9IGRhdGFUeXBlTWFwLmdldChuYW1lKTtcblx0XHRcdFx0aWYgKHR5cGUpIHtcblx0XHRcdFx0XHRyZXR1cm4gdHlwZTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkVsZW1lbnRBY2Nlc3NFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBGMjI6IHZhbHVlLWxldmVsIGVsZW1lbnQgYWNjZXNzIG92ZXIgYSBjb25zdC1hc3NlcnRlZFxuXHRcdFx0Ly8gbGl0ZXJhbCBhcnJheSDigJQgYCg8Y29uc3Q+W+KApl0pWzBdYCwgYChb4oCmXSBhcyBjb25zdClbMV1gLCBvclxuXHRcdFx0Ly8gYSB0cmFja2VkIG1vZHVsZSBjb25zdCAoYGNvbnN0IHggPSA8Y29uc3Q+W+KApl1gOyBgeFswXWApIOKAlFxuXHRcdFx0Ly8gaW5mZXJzIHRoZSBlbGVtZW50J3MgbGl0ZXJhbCB0eXBlLCB0aGUgdmFsdWUtbGV2ZWwgdHdpbiBvZlxuXHRcdFx0Ly8gdGhlIHR5cGVvZi1wYXRoIHVuaW9uLiBOb24tbnVtZXJpYyBpbmRleGVzLCBub24tbGl0ZXJhbFxuXHRcdFx0Ly8gZWxlbWVudHMsIGFuZCBnZW5lcmFsIGFzc2VydGlvbnMgc3RheSBgdW5rbm93bmAuXG5cdFx0XHRjb25zdCBlbGVtZW50QWNjZXNzID0gaW5pdGlhbGl6ZXIgYXMgdHMuRWxlbWVudEFjY2Vzc0V4cHJlc3Npb247XG5cdFx0XHRjb25zdCBhcmd1bWVudCA9IGVsZW1lbnRBY2Nlc3MuYXJndW1lbnRFeHByZXNzaW9uO1xuXHRcdFx0aWYgKCFhcmd1bWVudCB8fCAhdHMuaXNOdW1lcmljTGl0ZXJhbChhcmd1bWVudCkpIHtcblx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdH1cblx0XHRcdGNvbnN0IGFycmF5TGl0ZXJhbCA9IHRoaXMuY29uc3RBcnJheUxpdGVyYWxPZihlbGVtZW50QWNjZXNzLmV4cHJlc3Npb24pO1xuXHRcdFx0aWYgKCFhcnJheUxpdGVyYWwpIHtcblx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdH1cblx0XHRcdGNvbnN0IGVsZW1lbnQgPSBhcnJheUxpdGVyYWwuZWxlbWVudHNbIHBhcnNlSW50KGFyZ3VtZW50LnRleHQsIDEwKSBdO1xuXHRcdFx0aWYgKCFlbGVtZW50IHx8IHRzLmlzU3ByZWFkRWxlbWVudChlbGVtZW50KSkge1xuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbGl0ZXJhbCA9IHRoaXMubGl0ZXJhbFR5cGVPZkV4cHJlc3Npb24oZWxlbWVudCk7XG5cdFx0XHRjb25zdCBlbGVtZW50UmVzdWx0ID0gbGl0ZXJhbCA/PyAndW5rbm93bic7XG5cdFx0XHRyZXR1cm4gZWxlbWVudFJlc3VsdDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkNhbGxFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgZnVuY3Rpb24gY2FsbHMgbGlrZSBEYXRlLm5vdygpLCBwYXJzZUludCgpLCBldGMuXG5cdFx0XHRjb25zdCBjYWxsRXhwciA9IGluaXRpYWxpemVyIGFzIHRzLkNhbGxFeHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxFeHByLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IG1ldGhvZE5hbWUgPSBjYWxsRXhwci5leHByZXNzaW9uLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3Qgb2JqTmFtZSA9IHRzLmlzSWRlbnRpZmllcihjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb24pXG5cdFx0XHRcdFx0PyBjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb24udGV4dFxuXHRcdFx0XHRcdDogJyc7XG5cdFx0XHRcdFx0XG5cdFx0XHRcdC8vIERhdGUubm93KCkgLT4gbnVtYmVyXG5cdFx0XHRcdGlmIChvYmpOYW1lID09PSAnRGF0ZScgJiYgbWV0aG9kTmFtZSA9PT0gJ25vdycpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gU3RyaW5nIG1ldGhvZHMgdGhhdCByZXR1cm4gc3RyaW5nXG5cdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAndG9TdHJpbmcnIHx8IG1ldGhvZE5hbWUgPT09ICd2YWx1ZU9mJykge1xuXHRcdFx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBIYW5kbGUgTWFwIHByb3BlcnR5IGFjY2VzcyBvbiBjbGFzcyBpbnN0YW5jZXMgKHRoaXMubWFwLiopXG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0Y29uc3Qgb3V0ZXJQcm9wID0gY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdFx0XHRcdC8vIEhhbmRsZSBib3RoICd0aGlzJyBrZXl3b3JkIGFuZCBpZGVudGlmaWVyIHBhdHRlcm5zXG5cdFx0XHRcdFx0bGV0IGlubmVyTmFtZSA9ICcnO1xuXHRcdFx0XHRcdGlmIChvdXRlclByb3AuZXhwcmVzc2lvbi5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0XHRpbm5lck5hbWUgPSAndGhpcyc7XG5cdFx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc0lkZW50aWZpZXIob3V0ZXJQcm9wLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0XHRpbm5lck5hbWUgPSBvdXRlclByb3AuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCBtYXBQcm9wID0gb3V0ZXJQcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0XHQvLyB0aGlzLm1hcC5YKCkgcGF0dGVybnNcblx0XHRcdFx0XHRpZiAoaW5uZXJOYW1lID09PSAndGhpcycgJiYgbWFwUHJvcCA9PT0gJ21hcCcpIHtcblx0XHRcdFx0XHRcdC8vIFRyeSB0byBnZXQgdGhlIE1hcCdzIHZhbHVlIHR5cGUgZnJvbSBjbGFzcyBwcm9wZXJ0aWVzXG5cdFx0XHRcdFx0XHRsZXQgbWFwVmFsdWVUeXBlID0gJ3Vua25vd24nO1xuXHRcdFx0XHRcdFx0aWYgKGNsYXNzUHJvcGVydHlUeXBlcykge1xuXHRcdFx0XHRcdFx0XHRjb25zdCBtYXBUeXBlID0gY2xhc3NQcm9wZXJ0eVR5cGVzLmdldCgnbWFwJyk7XG5cdFx0XHRcdFx0XHRcdGlmIChtYXBUeXBlICYmIG1hcFR5cGUuc3RhcnRzV2l0aCgnTWFwPCcpKSB7XG5cdFx0XHRcdFx0XHRcdFx0Ly8gUGFyc2UgTWFwPEssIFY+IHRvIGdldCBWXG5cdFx0XHRcdFx0XHRcdFx0Y29uc3QgbWF0Y2ggPSBtYXBUeXBlLm1hdGNoKC9NYXA8W14sXSssXFxzKiguKyk+JC8pO1xuXHRcdFx0XHRcdFx0XHRcdGlmIChtYXRjaCkge1xuXHRcdFx0XHRcdFx0XHRcdFx0WyAsIG1hcFZhbHVlVHlwZSBdID0gbWF0Y2g7XG5cdFx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2hhcycpIHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3NldCcpIHJldHVybiAndGhpcyc7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2dldCcpIHJldHVybiBtYXBWYWx1ZVR5cGU7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2RlbGV0ZScpIHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2NsZWFyJykgcmV0dXJuICd2b2lkJztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAndmFsdWVzJykgcmV0dXJuIGBJdGVyYWJsZUl0ZXJhdG9yPCR7bWFwVmFsdWVUeXBlfT5gO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdrZXlzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPHN0cmluZz4nO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdlbnRyaWVzJykgcmV0dXJuIGBJdGVyYWJsZUl0ZXJhdG9yPFtzdHJpbmcsICR7bWFwVmFsdWVUeXBlfV0+YDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gRGlyZWN0IG1hcC5YKCkgY2FsbHNcblx0XHRcdFx0aWYgKG9iak5hbWUgPT09ICdtYXAnIHx8IG9iak5hbWUgPT09ICdvYmonKSB7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdoYXMnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnc2V0JykgcmV0dXJuICd0aGlzJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2dldCcpIHJldHVybiAndW5rbm93bic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdkZWxldGUnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnY2xlYXInKSByZXR1cm4gJ3ZvaWQnO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAndmFsdWVzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPHVua25vd24+Jztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2tleXMnKSByZXR1cm4gJ0l0ZXJhYmxlSXRlcmF0b3I8c3RyaW5nPic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdlbnRyaWVzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPFtzdHJpbmcsIHVua25vd25dPic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIHBhcnNlSW50LCBwYXJzZUZsb2F0IC0+IG51bWJlclxuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjYWxsRXhwci5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBmbk5hbWUgPSBjYWxsRXhwci5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdwYXJzZUludCcgfHwgZm5OYW1lID09PSAncGFyc2VGbG9hdCcpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ1N0cmluZycpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ051bWJlcicpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ0Jvb2xlYW4nKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlRlbXBsYXRlRXhwcmVzc2lvbjpcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTm9TdWJzdGl0dXRpb25UZW1wbGF0ZUxpdGVyYWw6IHtcblx0XHRcdC8vIFRlbXBsYXRlIGxpdGVyYWxzIGxpa2UgYCR7YmFzZVZhbHVlfS0ke2V4dHJhfWAgYWx3YXlzIHByb2R1Y2Ugc3RyaW5nc1xuXHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdH1cblx0XHRkZWZhdWx0OlxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0KiBDb2xsZWN0IHVzYWdlIGluZm9ybWF0aW9uIGZvciB0eXBlIHJlZmVyZW5jZXNcblx0XHRcdCovXG5cdHByaXZhdGUgY29sbGVjdFVzYWdlIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgZm9yIG5ldyBUeXBlKCkgaW5zdGFudGlhdGlvblxuXHRcdGlmICh0cy5pc05ld0V4cHJlc3Npb24obm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRsZXQgdHlwZU5hbWU6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdHR5cGVOYW1lID0gdGhpcy5yZXNvbHZlVHlwZVBhdGgobm9kZS5leHByZXNzaW9uKTtcblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdHR5cGVOYW1lID0gdGhpcy5nZXRUeXBlTmFtZUZyb21FeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHlwZU5hbWUpIHtcblx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHQpO1xuXHRcdFx0XHR0aGlzLmFkZFVzYWdlKHR5cGVOYW1lLCB7XG5cdFx0XHRcdFx0bG9jYXRpb24gICAgICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0a2luZCAgICAgICAgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0XHRcdGNvZGUgICAgICAgICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdC8vIENvbnN0cnVjdG9yIGV4cHJlc3Npb24gdGV4dCAoJ1RoaW5nJywgJ3VzZXIuQWRtaW5FbnRpdHknLFxuXHRcdFx0XHRcdC8vIGEgbG9va3VwIGFsaWFzKSDigJQgQ3JlYXRpb25BbmNob3IuY29uc3RydWN0b3JUZXh0IChQaGFzZSAzKVxuXHRcdFx0XHRcdGNvbnN0cnVjdG9yVGV4dCA6IG5vZGUuZXhwcmVzc2lvbi5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdH0pO1xuXHRcdFx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50IGZyb20gbmV3IFR5cGUoKSBmb3IgZmxvdyBhbmFseXNpc1xuXHRcdFx0XHR0aGlzLnRyYWNrTmV3QXNzaWdubWVudChub2RlLCB0eXBlTmFtZSk7XG5cdFx0XHRcdC8vIEFsc28gcmVjb3JkIGFzIGZsb3cgZXZlbnRcblx0XHRcdFx0dGhpcy5hZGRGbG93KHR5cGVOYW1lLCB7XG5cdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRraW5kICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdGNvbnRleHQgIDogJ25ldyBleHByZXNzaW9uJyxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcblx0XHQvLyBDaGVjayBmb3IgcHJvcGVydHkgYWNjZXNzIG9uIGluc3RhbmNlcyAodXNlci5BZG1pblR5cGUpXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRjb25zdCBwcm9wTmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0Ly8gaW5zdGFuY2UuY2xvbmUg4oCUIHRoZSBQUk9QRVJUWSBmb3JtIChjb3JlIHR5cGVzIGl0XG5cdFx0XHQvLyBgcmVhZG9ubHkgY2xvbmU6IHRoaXNgKTogdGhlIHJlc3VsdCB2YXJpYWJsZSBiaW5kcyB0byB0aGVcblx0XHRcdC8vIHNvdXJjZSBpbnN0YW5jZSdzIHR5cGUsIHNhbWUgYXMgdGhlIGZvcmsoKS9jbG9uZSgpIGNhbGxcblx0XHRcdC8vIGZvcm1zIChhd2FpdC10cmFuc3BhcmVudCkuIFRoZSBjYWxsIGZvcm0ncyByZWNvcmRpbmcgaGFwcGVuc1xuXHRcdFx0Ly8gaW4gdGhlIENhbGxFeHByZXNzaW9uIGJyYW5jaDsgdGhlIHByb3BlcnR5IGJyYW5jaCBza2lwcyBpdFxuXHRcdFx0Ly8gdG8gYXZvaWQgYSBkdXBsaWNhdGUgZW50cnkgYXQgdGhlIHNhbWUgc2l0ZVxuXHRcdFx0aWYgKHByb3BOYW1lID09PSAnY2xvbmUnICYmIHRzLmlzSWRlbnRpZmllcihub2RlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IGNsb25lZFBhdGggPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChub2RlLmV4cHJlc3Npb24udGV4dCk7XG5cdFx0XHRcdGNvbnN0IGlzQ2FsbEZvcm0gPSB0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUucGFyZW50KSAmJiBub2RlLnBhcmVudC5leHByZXNzaW9uID09PSBub2RlO1xuXHRcdFx0XHRpZiAoY2xvbmVkUGF0aCkge1xuXHRcdFx0XHRcdGlmICghaXNDYWxsRm9ybSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdFx0XHQpO1xuXHRcdFx0XHRcdFx0dGhpcy5hZGRVc2FnZShjbG9uZWRQYXRoLCB7XG5cdFx0XHRcdFx0XHRcdGxvY2F0aW9uICAgICAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdFx0XHRraW5kICAgICAgICAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0XHRcdGNvZGUgICAgICAgICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdFx0XHRjb25zdHJ1Y3RvclRleHQgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShub2RlLCBjbG9uZWRQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gQ2hlY2sgaWYgdGhpcyBsb29rcyBsaWtlIGEgdHlwZSBhY2Nlc3MgcGF0dGVyblxuXHRcdFx0aWYgKHByb3BOYW1lICYmIHRoaXMuaXNMaWtlbHlUeXBlTmFtZShwcm9wTmFtZSkpIHtcblx0XHRcdFx0Ly8gbmV3IHguU3ViKOKApik6IHRoZSBOZXdFeHByZXNzaW9uIGJyYW5jaCBhbHJlYWR5IHJlY29yZGVkXG5cdFx0XHRcdC8vIHRoZSBzaXRlIGFzIGFuIGluc3RhbnRpYXRpb24sIHNvIGEgcHJvcGVydHlBY2Nlc3MgcmVjb3JkXG5cdFx0XHRcdC8vIHdvdWxkIGR1cGxpY2F0ZSBpdCDigJQgb25lIHJlY29yZCBwZXIgc2l0ZSwgdGhlIHNhbWUgbGF3IGFzXG5cdFx0XHRcdC8vIHRoZSBjbG9uZSBndWFyZCBhYm92ZS4gKEEgd2hvbGUtY2FsbGVlLXBhcmVudGhlc2l6ZWRcblx0XHRcdFx0Ly8gbmV3ICh4LlN1YikoKSBuZXZlciBtYXRjaGVzIGhlcmU6IHRoZSBhY2Nlc3MncyBwYXJlbnQgaXNcblx0XHRcdFx0Ly8gdGhlIFBhcmVudGhlc2l6ZWRFeHByZXNzaW9uLCBhbmQgdGhlIGluc3RhbnRpYXRpb24gYnJhbmNoXG5cdFx0XHRcdC8vIGNhbm5vdCByZXNvbHZlIHRoYXQgY2FsbGVlIOKAlCB0aGlzIGFjY2VzcyBzdGF5cyB0aGUgc2l0ZSdzXG5cdFx0XHRcdC8vIG9ubHkgcmVjb3JkLilcblx0XHRcdFx0Y29uc3QgaXNOZXdDYWxsZWUgPSB0cy5pc05ld0V4cHJlc3Npb24obm9kZS5wYXJlbnQpICYmIG5vZGUucGFyZW50LmV4cHJlc3Npb24gPT09IG5vZGU7XG5cdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0XHQvLyBUcnkgdG8gcmVzb2x2ZSBmdWxsIHBhdGhcblx0XHRcdFx0Y29uc3QgZnVsbFBhdGggPSB0aGlzLnJlc29sdmVUeXBlUGF0aChub2RlKTtcblx0XHRcdFx0aWYgKGZ1bGxQYXRoICYmICFpc05ld0NhbGxlZSkge1xuXHRcdFx0XHRcdHRoaXMuYWRkVXNhZ2UoZnVsbFBhdGgsIHtcblx0XHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0XHRraW5kICAgICA6ICdwcm9wZXJ0eUFjY2VzcycsXG5cdFx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcblx0XHQvLyBDaGVjayBmb3IgbG9va3VwKCdUeXBlTmFtZScpIG9yIGxvb2t1cChzb3VyY2UsICdUeXBlTmFtZScpIGNhbGxzXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRjb25zdCBmdW5jTmFtZSA9IHRoaXMuZ2V0RnVuY3Rpb25OYW1lKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoZnVuY05hbWUgPT09ICdsb29rdXAnICYmIG5vZGUuYXJndW1lbnRzLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0Y29uc3QgdHlwZVBhdGggPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKG5vZGUpO1xuXHRcdFx0XHRpZiAodHlwZVBhdGgpIHtcblx0XHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHRcdCk7XG5cdFx0XHRcdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRcdFx0XHR0aGlzLmFkZFVzYWdlKHR5cGVQYXRoLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0XHRcdGtpbmQgOiAnbG9va3VwJyxcblx0XHRcdFx0XHRcdGNvZGUgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50IGZyb20gbG9va3VwIGZvciBpbnN0YW50aWF0aW9uIHRyYWNraW5nXG5cdFx0XHRcdFx0dGhpcy50cmFja0xvb2t1cEFzc2lnbm1lbnQobm9kZSwgdHlwZVBhdGgpO1xuXHRcdFx0XHRcdC8vIFJlY29yZCBmb3IgdGhlIGhhcmQtZmFpbCBsYXcgZXZlbiB3aGVuIGFkZFVzYWdlIGRyb3BwZWRcblx0XHRcdFx0XHQvLyB0aGUgcGF0aCAodW5rbm93biBwYXRocyBhcmUgZXhhY3RseSB0aGUgZmFpbHVyZSBjbGFzcylcblx0XHRcdFx0XHR0aGlzLmxvb2t1cFJlZmVyZW5jZXMucHVzaCh7IHBhdGggOiB0eXBlUGF0aCwgbG9jYXRpb24gfSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblxuXHRcdFx0Ly8gQ2hhaW4tZm9ybSBjb25zdHJ1Y3Rpb246IGBuZXcgUiguLi4pLkEoLi4uKWAgLyB0aGUgYXdhaXRlZFxuXHRcdFx0Ly8gc2luZ2xlLWNoYWluIGBhd2FpdCBuZXcgUiguLi4pLkEoLi4uKS5CKC4uLilgIOKAlCB0aGUgY2FsbCBvblxuXHRcdFx0Ly8gdGhlIGZyZXNoIGluc3RhbmNlIGNvbnN0cnVjdHMgdGhlIGNoYWluIFRJUCAoYXdhaXQgaXNcblx0XHRcdC8vIHRyYW5zcGFyZW50OyB0aGUgTmV3RXhwcmVzc2lvbiBicmFuY2ggYWxyZWFkeSByZWNvcmRlZCB0aGVcblx0XHRcdC8vIGlubmVyIHJvb3QpLiBUaGUgcmVzdWx0IHZhcmlhYmxlIGJpbmRzIHRvIHRoZSB0aXAsIG5vdCB0aGVcblx0XHRcdC8vIHJvb3QgKHRyYWNrTmV3QXNzaWdubWVudCByZXNvbHZlcyB0aGUgc2FtZSB0aXApXG5cdFx0XHRjb25zdCBjaGFpblRpcCA9IHRoaXMucmVzb2x2ZUNoYWluVGlwVHlwZVBhdGgobm9kZSk7XG5cdFx0XHRpZiAoY2hhaW5UaXApIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZShub2RlLCBjaGFpblRpcCwgc291cmNlRmlsZSk7XG5cdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0dGhpcy5hZGRGbG93KGNoYWluVGlwLCB7XG5cdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRraW5kICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdGNvbnRleHQgIDogJ2NoYWluZWQgY29uc3RydWN0aW9uJyxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cblx0XHRcdC8vIG1uZW1vbmljYSBjYWxsL2FwcGx5KGVudGl0eSwgQ3RvciwgLi4uKSAvIGJpbmQoZW50aXR5LCBDdG9yKSDigJRcblx0XHRcdC8vIHR5cGVkIGNvbnN0cnVjdGlvbiB3aXRob3V0IGBuZXdgOiB0aGUgQ3RvciBhcmd1bWVudCAoYXJnIDEpIGlzXG5cdFx0XHQvLyB0aGUgY29uc3RydWN0ZWQgdHlwZS4gSW1wb3J0LWF3YXJlOiBvbmx5IGlkZW50aWZpZXJzIGFjdHVhbGx5XG5cdFx0XHQvLyBpbXBvcnRlZCBmcm9tICdtbmVtb25pY2EnIChvciBtZW1iZXJzIG9mIGEgdHJhY2tlZFxuXHRcdFx0Ly8gbW9kdWxlLW9iamVjdCBhbGlhcykgbWF0Y2gg4oCUIHVzZXJsYW5kIGNhbGwvYXBwbHkvYmluZCBuZXZlclxuXHRcdFx0Ly8gZG8uIGNhbGwvYXBwbHkgcmVjb3JkIHRoZSBjb25zdHJ1Y3Rpb247IGJpbmQoKSBjb25zdHJ1Y3RzXG5cdFx0XHQvLyBub3RoaW5nIOKAlCBpdCBvbmx5IGJpbmRzIHRoZSByZXN1bHQgdmFyaWFibGUgdG8gdGhlIEN0b3Inc1xuXHRcdFx0Ly8gdHlwZSAocnVudGltZSBJbnN0YW5jZVJlc3VsdDxNZXJnZTxFLFQ+PiBhcHByb3hpbWF0ZWQgYnkgVFxuXHRcdFx0Ly8gd2l0aGluIHRoZSBvdXRwdXQgY29udHJhY3QpXG5cdFx0XHRjb25zdCBjb25zdHJ1Y3Rpb25QYXRoID0gdGhpcy5yZXNvbHZlQ29uc3RydWN0aW9uRm5UeXBlUGF0aChub2RlKTtcblx0XHRcdGlmIChjb25zdHJ1Y3Rpb25QYXRoKSB7XG5cdFx0XHRcdGNvbnN0IGlzQmluZEZvcm0gPSB0aGlzLmlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4obm9kZS5leHByZXNzaW9uLCAnYmluZCcpO1xuXHRcdFx0XHRpZiAoIWlzQmluZEZvcm0pIHtcblx0XHRcdFx0XHRjb25zdCBjdG9yQXJnVGV4dCA9IG5vZGUuYXJndW1lbnRzWyAxIF0/LmdldFRleHQoc291cmNlRmlsZSk7XG5cdFx0XHRcdFx0dGhpcy5yZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZShub2RlLCBjb25zdHJ1Y3Rpb25QYXRoLCBzb3VyY2VGaWxlLCBjdG9yQXJnVGV4dCk7XG5cdFx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0XHQpO1xuXHRcdFx0XHRcdHRoaXMuYWRkRmxvdyhjb25zdHJ1Y3Rpb25QYXRoLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdFx0a2luZCAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdFx0Y29udGV4dCAgOiAnY2FsbC9hcHBseSBjb25zdHJ1Y3Rpb24nLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHRoaXMuYmluZFJlc3VsdFZhcmlhYmxlKG5vZGUsIGNvbnN0cnVjdGlvblBhdGgpO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBpbnN0YW5jZS5mb3JrKCkvY2xvbmUoKSDigJQgcnVudGltZSByZS1ydW5zIGNvbnN0cnVjdGlvbiAoaG9va3Ncblx0XHRcdC8vIGZpcmUsIGEgZGlzdGluY3QgaW5zdGFuY2Ugb24gYSBkaXN0aW5jdCBsaW5lKSwgc28gYW5cblx0XHRcdC8vIGBpbnN0YW50aWF0aW9uYCB1c2FnZSByZWNvcmRzIHRoZSBzaXRlIElOIEFERElUSU9OIHRvIHRoZVxuXHRcdFx0Ly8gcmVzdWx0LXZhciBiaW5kaW5nIGFuZCB0aGUgZ2VuZXJpYyBtZXRob2RDYWxsIGZsb3cgKHRoZSBlbnRyeVxuXHRcdFx0Ly8gaXMgYnl0ZS1pbmRpc3Rpbmd1aXNoYWJsZSBmcm9tIGBuZXdgIHVudGlsIHRoZSBkZWZlcnJlZFxuXHRcdFx0Ly8gbWVjaGFuaXNtLWtpbmQgcmV2aXNpb24g4oCUIHRoZSBvd25lcidzIGV4cGxpY2l0IGNhbGwpLiBGcmVlXG5cdFx0XHQvLyB1dGlscy5tZXJnZShhLCBiLCAuLi4pIC8gdXRpbHMuZm9yayhpbnN0YW5jZSkoLi4uKSBhcmVcblx0XHRcdC8vIGNvbnN0cnVjdGlvbiBvZiBhJ3MgdHlwZSB0b28gKG1lcmdlID0gZm9yayhhKSBvdmVyIGInc1xuXHRcdFx0Ly8gY29udGV4dCk7IHRoZSByZXN1bHQgYmluZGluZyBrZWVwcyB0aGUgZG9jdW1lbnRlZCBhcmctMFxuXHRcdFx0Ly8gYXBwcm94aW1hdGlvblxuXHRcdFx0Y29uc3QgZm9ya0xpa2VQYXRoID0gdGhpcy5yZXNvbHZlRm9ya0xpa2VUeXBlUGF0aChub2RlKTtcblx0XHRcdGlmIChmb3JrTGlrZVBhdGgpIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZShub2RlLCBmb3JrTGlrZVBhdGgsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShub2RlLCBmb3JrTGlrZVBhdGgpO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgdXRpbHNQYXRoID0gdGhpcy5yZXNvbHZlVXRpbHNGblR5cGVQYXRoKG5vZGUpO1xuXHRcdFx0aWYgKHV0aWxzUGF0aCkge1xuXHRcdFx0XHR0aGlzLnJlY29yZENvbnN0cnVjdGlvblVzYWdlKG5vZGUsIHV0aWxzUGF0aCwgc291cmNlRmlsZSk7XG5cdFx0XHRcdHRoaXMuYmluZFJlc3VsdFZhcmlhYmxlKG5vZGUsIHV0aWxzUGF0aCk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cdFxuXHQvKipcblx0XHRcdCogR2V0IGZ1bmN0aW9uIG5hbWUgZnJvbSBleHByZXNzaW9uIChpZGVudGlmaWVyIG9yIHByb3BlcnR5IGFjY2Vzcylcblx0XHRcdCovXG5cdHByaXZhdGUgZ2V0RnVuY3Rpb25OYW1lIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci50ZXh0O1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIEFkZCBhIHVzYWdlIHRvIHRoZSBjb2xsZWN0aW9uXG5cdFx0XHQqL1xuXHRwcml2YXRlIGFkZFVzYWdlICh0eXBlUGF0aDogc3RyaW5nLCB1c2FnZTogVXNhZ2VJbmZvKTogdm9pZCB7XG5cdFx0Ly8gT25seSB0cmFjayB1c2FnZXMgb2YgbW5lbW9uaWNhLWRlZmluZWQgdHlwZXNcblx0XHRpZiAoIXRoaXMuZGVmaW5pdGlvbnMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAoIXRoaXMudXNhZ2VzLmhhcyh0eXBlUGF0aCkpIHtcblx0XHRcdHRoaXMudXNhZ2VzLnNldCh0eXBlUGF0aCwgW10pO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBkdXBsaWNhdGVzIGJhc2VkIG9uIGxvY2F0aW9uLCBjb2RlLCBhbmQga2luZFxuXHRcdGNvbnN0IGV4aXN0aW5nVXNhZ2VzID0gdGhpcy51c2FnZXMuZ2V0KHR5cGVQYXRoKSE7XG5cdFx0Y29uc3QgaXNEdXBsaWNhdGUgPSBleGlzdGluZ1VzYWdlcy5zb21lKGV4aXN0aW5nID0+XG5cdFx0XHRleGlzdGluZy5sb2NhdGlvbiA9PT0gdXNhZ2UubG9jYXRpb24gJiZcblx0XHRcdFx0ZXhpc3RpbmcuY29kZSA9PT0gdXNhZ2UuY29kZSAmJlxuXHRcdFx0XHRleGlzdGluZy5raW5kID09PSB1c2FnZS5raW5kKTtcblxuXHRcdGlmICghaXNEdXBsaWNhdGUpIHtcblx0XHRcdGV4aXN0aW5nVXNhZ2VzLnB1c2godXNhZ2UpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IEVEUyAoRXhlY3V0aW9uIERhdGEgU3RvcmFnZSkgdXNhZ2UgaW5mb3JtYXRpb25cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEVEUyAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSB8fCAhbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgZnVuY05hbWUgPSB0aGlzLmdldEZ1bmN0aW9uTmFtZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghZnVuY05hbWUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cdFx0Ly8gRW5jbG9zaW5nIG1uZW1vbmljYSB0eXBlIHBhdGgg4oCUIHdyYXAgYXJncyBhcmUgdXN1YWxseSBsb2NhbFxuXHRcdC8vIGZ1bmN0aW9ucywgc28gdGhlIG93bmluZyBkZWZpbmUoKS9sYXp5KCkgaGFuZGxlciBvciBkZWNvcmF0ZWRcblx0XHQvLyBjbGFzcyBpcyB3aGF0IGVkcy5qc29uIGNvbnN1bWVycyAoR3JhcGhCdWlsZGVyKSBjYW4gam9pbiBvbi5cblx0XHRjb25zdCBzY29wZSA9IHRoaXMucmVzb2x2ZUVEU1Njb3BlKG5vZGUpO1xuXG5cdFx0Ly8gd3JhcChmbiksIHdyYXBDb25zdHJ1Y3RvckFyZyhmbiwgcGFyZW50KSwgdXBncmFkZUNvbnN0cnVjdG9yQXJnKGFyZywgaW5zdCksIHdyYXBJbnN0YW5jZU1ldGhvZHMob2JqKVxuXHRcdGlmIChcblx0XHRcdGZ1bmNOYW1lID09PSAnd3JhcCcgfHxcblx0XHRcdGZ1bmNOYW1lID09PSAnd3JhcENvbnN0cnVjdG9yQXJnJyB8fFxuXHRcdFx0ZnVuY05hbWUgPT09ICd1cGdyYWRlQ29uc3RydWN0b3JBcmcnIHx8XG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3dyYXBJbnN0YW5jZU1ldGhvZHMnXG5cdFx0KSB7XG5cdFx0XHRjb25zdCB0YXJnZXRUeXBlID0gdGhpcy5yZXNvbHZlRURTQXJndW1lbnRUeXBlKG5vZGUuYXJndW1lbnRzWyAwIF0pO1xuXHRcdFx0Ly8gZGl2ZSdzIHdyYXAtZmFtaWx5IHNpZ25hdHVyZXMgKGRpdmUvc3JjL2luZGV4LnRzKTpcblx0XHRcdC8vICAgd3JhcChmbiwgbGFiZWw/KSB8IHdyYXAoZm4sIGNvbnRleHQ/LCBsYWJlbD8pXG5cdFx0XHQvLyAgIHdyYXBDb25zdHJ1Y3RvckFyZyhmbiwgY29udGV4dClcblx0XHRcdC8vICAgdXBncmFkZUNvbnN0cnVjdG9yQXJnKGFyZywgaW5zdGFuY2UpXG5cdFx0XHQvLyAgIHdyYXBJbnN0YW5jZU1ldGhvZHMoaW5zdGFuY2UpXG5cdFx0XHQvLyDigKZzbyB0aGUgaW5zdGFuY2UvY29udGV4dCBhcmcgc2l0cyBhdCBhcmdzWzFdIChhcmdzWzBdIGZvclxuXHRcdFx0Ly8gd3JhcEluc3RhbmNlTWV0aG9kcykgYW5kIGEgc3RyaW5nIGxpdGVyYWwgaW4gYXJnc1sxLi4yXSBpcyB0aGUgbGFiZWxcblx0XHRcdGNvbnN0IGluc3RhbmNlQXJnTm9kZSA9IGZ1bmNOYW1lID09PSAnd3JhcEluc3RhbmNlTWV0aG9kcydcblx0XHRcdFx0PyBub2RlLmFyZ3VtZW50c1sgMCBdXG5cdFx0XHRcdDogbm9kZS5hcmd1bWVudHNbIDEgXTtcblx0XHRcdC8vIEZpcmUtYW5kLWZvcmdldCB3cmFwcGVycyAod2lyZS11cCBoZWxwZXJzLCByZWdpc3RyYXRpb25cblx0XHRcdC8vIGZ1bmN0aW9ucykgc2l0IG91dHNpZGUgYW55IGRlZmluZSgpL2xhenkoKSBoYW5kbGVyLCBzbyB0aGVcblx0XHRcdC8vIGxleGljYWwgc2NvcGUgaXMgYWJzZW50IOKAlCBhdHRyaWJ1dGUgdGhyb3VnaCB0aGUgaW5zdGFuY2UvY29udGV4dFxuXHRcdFx0Ly8gYXJndW1lbnQgaW5zdGVhZDogYSB0cmFja2VkIGFzc2lnbm1lbnQsIGVsc2UgdGhlIGVuY2xvc2luZ1xuXHRcdFx0Ly8gZnVuY3Rpb24ncyBwYXJhbWV0ZXIgYW5ub3RhdGlvbiByZXNvbHZlZCB0aHJvdWdoIHRoZSBncmFwaCBsYXdcblx0XHRcdGNvbnN0IGluc3RhbmNlVHlwZVBhdGggPSBpbnN0YW5jZUFyZ05vZGVcblx0XHRcdFx0PyB0aGlzLnJlc29sdmVXcmFwSW5zdGFuY2VUeXBlUGF0aChpbnN0YW5jZUFyZ05vZGUpXG5cdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0Y29uc3QgZWZmZWN0aXZlU2NvcGUgPSBzY29wZSA/PyBpbnN0YW5jZVR5cGVQYXRoO1xuXHRcdFx0Y29uc3QgaW5mbzogRURTSW5mbyA9IHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAnd3JhcCcsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHRhcmdldFR5cGUgOiB0YXJnZXRUeXBlIHx8IHVuZGVmaW5lZCxcblx0XHRcdFx0c2NvcGUgICAgICA6IGVmZmVjdGl2ZVNjb3BlLFxuXHRcdFx0XHRmbiAgICAgICAgIDogZnVuY05hbWUsXG5cdFx0XHR9O1xuXHRcdFx0aWYgKGluc3RhbmNlQXJnTm9kZSAmJiB0cy5pc0lkZW50aWZpZXIoaW5zdGFuY2VBcmdOb2RlKSkge1xuXHRcdFx0XHRpbmZvLmluc3RhbmNlQXJnID0gaW5zdGFuY2VBcmdOb2RlLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGV4dHJhQXJnIG9mIFsgbm9kZS5hcmd1bWVudHNbIDEgXSwgbm9kZS5hcmd1bWVudHNbIDIgXSBdKSB7XG5cdFx0XHRcdGlmIChleHRyYUFyZyAmJiB0cy5pc1N0cmluZ0xpdGVyYWwoZXh0cmFBcmcpKSB7XG5cdFx0XHRcdFx0aW5mby5sYWJlbCA9IGV4dHJhQXJnLnRleHQ7XG5cdFx0XHRcdFx0YnJlYWs7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIEEgd3JhcCgpIGNhbGwgbmVzdGVkIGluc2lkZSBhbm90aGVyIHdyYXBwZWQgYm9keSBjYXJyaWVzIHRoZVxuXHRcdFx0Ly8gbGluayB0byB0aGUgc2l0ZSB3aG9zZSBydW50aW1lIHdyYXBwaW5nIGNhdXNlZCBpdCDigJQgYW5kLCB3aGVuXG5cdFx0XHQvLyB0aGUgbmVzdGVkIHNpdGUgaGFzIG5vIHNjb3BlIG9mIGl0cyBvd24sIHRoZSBjYXVzaW5nIHNpdGUnc1xuXHRcdFx0Ly8gc2NvcGUgYXR0cmlidXRpb24gdHJhdmVscyB3aXRoIHRoZSBsaW5rXG5cdFx0XHRjb25zdCB2aWFMaW5rID0gdGhpcy5uZXN0ZWRXcmFwVmlhLmdldChub2RlKTtcblx0XHRcdGlmICh2aWFMaW5rKSB7XG5cdFx0XHRcdGluZm8udmlhID0gdmlhTGluay52aWE7XG5cdFx0XHRcdGlmIChpbmZvLnNjb3BlID09PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0XHRpbmZvLnNjb3BlID0gdmlhTGluay5zY29wZTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gZGl2ZSB3cmFwcyByZXR1cm5lZCBmdW5jdGlvbnMgdG9vLCBhbmQgYW55IG1uZW1vbmljYSBpbnN0YW5jZVxuXHRcdFx0Ly8gY3JlYXRlZCBpbnNpZGUgdGhlIHdyYXBwZWQgYm9keSBpcyBhIGd1YXJhbnRlZWQgcGF0aCBoaXQg4oCUXG5cdFx0XHQvLyBib3RoIGFyZSBjYWxjdWxhYmxlIEFvVCwgc28gcmVjb3JkIHRoZW1cblx0XHRcdGNvbnN0IHdyYXBwZWQgPSB0aGlzLnJlc29sdmVGdW5jdGlvbkFyZ3VtZW50KG5vZGUuYXJndW1lbnRzWyAwIF0sIHNvdXJjZUZpbGUpO1xuXHRcdFx0aWYgKHdyYXBwZWQpIHtcblx0XHRcdFx0Ly8gVGhlIHdyYXBwZWQgY2FsbGJhY2sgZ2V0cyBpdHMgb3duIHNjb3BlIGluIHNjb3Blcy5qc29uIGtleWVkIGJ5XG5cdFx0XHRcdC8vIGl0cyBzdGFydCBwb3NpdGlvbiDigJQgcmVjb3JkIHRoYXQgc2NvcGVJZCBzbyBncmFwaCBjb25zdW1lcnMgY2FuXG5cdFx0XHRcdC8vIGpvaW4gYSB3cmFwIGVudHJ5IHRvIHRoZSBjYWxsYmFjaydzIGNyZWF0aW9uIG5vZGVcblx0XHRcdFx0Y29uc3QgY2FsbGJhY2tQb3MgPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdHdyYXBwZWQuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0Y29uc3QgY2FsbGJhY2tGaWxlID0gbm9kZVBhdGgucmVzb2x2ZShzb3VyY2VGaWxlLmZpbGVOYW1lKTtcblx0XHRcdFx0aW5mby5jYWxsYmFja1Njb3BlSWQgPSBgJHtjYWxsYmFja0ZpbGV9OiR7Y2FsbGJhY2tQb3MubGluZSArIDF9OiR7Y2FsbGJhY2tQb3MuY2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0XHRjb25zdCBjcmVhdGVzVHlwZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHRcdFx0dGhpcy5hbmFseXplV3JhcHBlZEJvZHkod3JhcHBlZCwgbG9jYXRpb24sIHNvdXJjZUZpbGUsIDAsIG5ldyBTZXQoKSwgY3JlYXRlc1R5cGVzLCBlZmZlY3RpdmVTY29wZSk7XG5cdFx0XHRcdGlmIChjcmVhdGVzVHlwZXMuc2l6ZSA+IDApIHtcblx0XHRcdFx0XHRpbmZvLmNyZWF0ZXNUeXBlcyA9IEFycmF5LmZyb20oY3JlYXRlc1R5cGVzKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgc3RvcmVkID0gdGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCBlZmZlY3RpdmVTY29wZSB8fCAndW5rbm93bicsIGluZm8pO1xuXHRcdFx0dGhpcy53cmFwRW50cnlCeU5vZGUuc2V0KG5vZGUsIHN0b3JlZCk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gY3VycmVudCgpLCBnZXRFcnJvckluc3RhbmNlKGVyciksIGdldEZsb3codGFyZ2V0Pylcblx0XHRpZiAoZnVuY05hbWUgPT09ICdjdXJyZW50JyB8fCBmdW5jTmFtZSA9PT0gJ2dldEVycm9ySW5zdGFuY2UnIHx8IGZ1bmNOYW1lID09PSAnZ2V0RmxvdycpIHtcblx0XHRcdHRoaXMuYWRkRURTKHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCA6ICdjb250ZXh0Q29uc3VtZScsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHNjb3BlLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gYXR0YWNoSG9va3MoY29sbGVjdGlvbikg4oCUIGZyb20gQG1uZW1vbmljYS9vdGVsLCB3aXJlcyBhXG5cdFx0Ly8gVHlwZXNDb2xsZWN0aW9uIHRvIGRpdmUncyBsaWZlY3ljbGUgdHJhY2luZ1xuXHRcdGlmIChmdW5jTmFtZSA9PT0gJ2F0dGFjaEhvb2tzJyAmJiBub2RlLmFyZ3VtZW50cy5sZW5ndGggPiAwKSB7XG5cdFx0XHRjb25zdCBbIGFyZyBdID0gbm9kZS5hcmd1bWVudHM7XG5cdFx0XHRpZiAodHMuaXNBcnJheUxpdGVyYWxFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGFyZy5lbGVtZW50cykge1xuXHRcdFx0XHRcdGNvbnN0IHRhcmdldFR5cGUgPSB0aGlzLnJlc29sdmVFRFNBcmd1bWVudFR5cGUoZWxlbWVudCk7XG5cdFx0XHRcdFx0dGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCBzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRcdFx0a2luZCAgICAgICA6ICdob29rQXR0YWNoJyxcblx0XHRcdFx0XHRcdGNvZGUsXG5cdFx0XHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdFx0XHRzY29wZSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgdGFyZ2V0VHlwZSA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShhcmcpO1xuXHRcdFx0XHR0aGlzLmFkZEVEUyh0YXJnZXRUeXBlIHx8IHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRcdGtpbmQgICAgICAgOiAnaG9va0F0dGFjaCcsXG5cdFx0XHRcdFx0Y29kZSxcblx0XHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdFx0c2NvcGUsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHR5cGUgZnJvbSBFRFMgY2FsbCBhcmd1bWVudCAoYmVzdCBlZmZvcnQpXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVFRFNBcmd1bWVudFR5cGUgKGFyZzogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCFhcmcpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gSWRlbnRpZmllcjogdmFyaWFibGUgbmFtZVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0Y29uc3QgbWFwcGVkID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQoYXJnLnRleHQpO1xuXHRcdFx0aWYgKG1hcHBlZCkge1xuXHRcdFx0XHRyZXR1cm4gbWFwcGVkO1xuXHRcdFx0fVxuXHRcdFx0Ly8gTWF5YmUgaXQncyBhIHR5cGUgbmFtZSBkaXJlY3RseVxuXHRcdFx0aWYgKHRoaXMuZGVmaW5pdGlvbnMuaGFzKGFyZy50ZXh0KSkge1xuXHRcdFx0XHRyZXR1cm4gYXJnLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBsZXQtaW4tdHJ5OiBhIGxldC92YXIgYmluZGluZyBkZWNsYXJlZCB3aXRob3V0IGEgdHJhY2tlZFxuXHRcdFx0Ly8gaW5pdGlhbGl6ZXIgYW5kIGFzc2lnbmVkIGxhdGVyIGluIHRoZSBTQU1FIHNjb3BlICh0aGVcblx0XHRcdC8vIGZpcmUtYW5kLWZvcmdldCBjYXRjaC1ndWFyZCBwYXR0ZXJuOiBgbGV0IGZuOyB0cnkgeyBmbiA9XG5cdFx0XHQvLyDigKYgfSBjYXRjaCB7IHJldHVybiB9IHdyYXAoZm4sIOKApilgKSDigJQgZm9sbG93IHRoZSBmaXJzdFxuXHRcdFx0Ly8gc3RhdGljYWxseS12aXNpYmxlIGluLXNjb3BlIGFzc2lnbm1lbnQuIE5vIGZsb3cgYW5hbHlzaXM6XG5cdFx0XHQvLyBmdW5jdGlvbi9jbGFzcyBib3VuZGFyaWVzIGFyZSBub3QgY3Jvc3NlZCwgYVxuXHRcdFx0Ly8gbmV2ZXItYXNzaWduZWQgYmluZGluZyBzdGF5cyB1bmtub3duIChGMjAgZGlzY2lwbGluZSkuXG5cdFx0XHQvLyBXaGVuIHRoZSBhc3NpZ25tZW50IHJlc29sdmVzLCBpdHMgZXZpZGVuY2UgV0lOUyBvdmVyIGFueVxuXHRcdFx0Ly8gZGVjbGFyYXRpb24gYW5ub3RhdGlvbiAodGhlIGNvbnN0cnVjdGVkIHN1YnR5cGUgaXMgdGhlIG1vcmVcblx0XHRcdC8vIHNwZWNpZmljIHRydXRoKTsgYW4gdW5yZXNvbHZhYmxlIFJIUyAoYSB1c2VybGFuZCBjYWxsLCBzYXkpXG5cdFx0XHQvLyBmYWxscyB0aHJvdWdoIHRvIHRoZSBhbm5vdGF0aW9uIGNsYWltIGJlbG93LlxuXHRcdFx0Y29uc3QgYXNzaWduZWQgPSB0aGlzLmZvbGxvd1Njb3BlQXNzaWdubWVudChhcmcudGV4dCwgYXJnKTtcblx0XHRcdGlmIChhc3NpZ25lZCkge1xuXHRcdFx0XHRjb25zdCByZXNvbHZlZCA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShhc3NpZ25lZCk7XG5cdFx0XHRcdGlmIChyZXNvbHZlZCkge1xuXHRcdFx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gQW5ub3RhdGlvbiBmYWxsYmFjayDigJQgdGhlIEYyMCBkaXNjaXBsaW5lIG9uZSBhcmd1bWVudCBvdmVyOlxuXHRcdFx0Ly8gYW4gZXhwbGljaXQgZGVjbGFyYXRpb24gb3IgcGFyYW1ldGVyIGFubm90YXRpb24gaXMgYSB1c2VyXG5cdFx0XHQvLyBjbGFpbSB3cml0dGVuIGluIHRoZSBBU1QsIG5vdCBmbG93IGFuYWx5c2lzLiBQYXJhbWV0ZXJcblx0XHRcdC8vIGZpcnN0OiBpdCBzaGFkb3dzIGFuIG91dGVyIGxldCwgc2FtZSBhcyB0aGUgY29udGV4dC1hcmcgcGF0aC5cblx0XHRcdGNvbnN0IGFubm90YXRlZCA9IHRoaXMucmVzb2x2ZVBhcmFtZXRlckFubm90YXRpb25UeXBlUGF0aChhcmcudGV4dCwgYXJnKSA/P1xuXHRcdFx0XHR0aGlzLnJlc29sdmVWYXJpYWJsZUFubm90YXRpb25UeXBlUGF0aChhcmcudGV4dCwgYXJnKTtcblx0XHRcdHJldHVybiBhbm5vdGF0ZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gTmV3RXhwcmVzc2lvbjogdGhlIGNvbnN0cnVjdGVkIHR5cGUg4oCUIHJlYWNoYWJsZSBkaXJlY3RseVxuXHRcdC8vICh3cmFwKG5ldyBUKCksIOKApikpIG9yIHRocm91Z2ggYSBmb2xsb3dlZCBhc3NpZ25tZW50XG5cdFx0aWYgKHRzLmlzTmV3RXhwcmVzc2lvbihhcmcpKSB7XG5cdFx0XHRjb25zdCBjdG9yRXhwciA9IGFyZy5leHByZXNzaW9uO1xuXHRcdFx0Y29uc3QgbmFtZSA9IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGN0b3JFeHByKVxuXHRcdFx0XHQ/IHRoaXMucmVzb2x2ZVR5cGVQYXRoKGN0b3JFeHByKVxuXHRcdFx0XHQ6IHRoaXMuZ2V0VHlwZU5hbWVGcm9tRXhwcmVzc2lvbihjdG9yRXhwcik7XG5cdFx0XHRjb25zdCBrbm93biA9IG5hbWUgJiYgdGhpcy5kZWZpbml0aW9ucy5oYXMobmFtZSkgPyBuYW1lIDogdW5kZWZpbmVkO1xuXHRcdFx0cmV0dXJuIGtub3duO1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2Vzczogb2JqLnByb3Bcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMucmVzb2x2ZVR5cGVQYXRoKGFyZyk7XG5cdFx0fVxuXG5cdFx0Ly8gVGhpcyBleHByZXNzaW9uOiB0aGlzLnNvbWV0aGluZ1xuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcmcpICYmIHRzLmlzSWRlbnRpZmllcihhcmcuZXhwcmVzc2lvbikgJiYgYXJnLmV4cHJlc3Npb24udGV4dCA9PT0gJ3RoaXMnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogbGV0LWluLXRyeTogZmluZCB0aGUgUklHSFQtSEFORCBTSURFIG9mIHRoZSBmaXJzdCBzdGF0aWNhbGx5LXZpc2libGVcblx0ICogYXNzaWdubWVudCB0byBgbmFtZWAgaW4gdGhlIHNjb3BlIHRoYXQgZGVjbGFyZXMgaXQuIFRoZSBkZWNsYXJpbmdcblx0ICogY29udGFpbmVyIGlzIGZvdW5kIGlubmVybW9zdC1vdXQgKGJsb2NrcywgY2FzZSBjbGF1c2VzLCB0aGUgc291cmNlXG5cdCAqIGZpbGUg4oCUIHRoZSBGMjAgd2Fsayk7IHRoZSBzY2FuIHJlY3Vyc2VzIGludG8gbmVzdGVkIGJsb2NrcyAodHJ5L1xuXHQgKiBjYXRjaC9maW5hbGx5LCBpZi9lbHNlLCBsb29wcywgc3dpdGNoIGNhc2VzKSBidXQgTkVWRVIgY3Jvc3Nlc1xuXHQgKiBmdW5jdGlvbiBvciBjbGFzcyBib3VuZGFyaWVzIOKAlCBhbiBhc3NpZ25tZW50IGluc2lkZSBhIGNsb3N1cmUgZG9lc1xuXHQgKiBub3QgYXR0cmlidXRlLiBSZXR1cm5zIHVuZGVmaW5lZCB3aGVuIHRoZSBiaW5kaW5nIGlzIGRlY2xhcmVkIGJ1dFxuXHQgKiBuZXZlciBhc3NpZ25lZCBpbiBzY29wZSAoYW5kIHN0b3BzIHRoZXJlOiBhbiBpbm5lciBkZWNsYXJhdGlvblxuXHQgKiBzaGFkb3dzIGFueSBvdXRlciBiaW5kaW5nKS5cblx0ICovXG5cdHByaXZhdGUgZm9sbG93U2NvcGVBc3NpZ25tZW50IChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IGZyb207XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGNvbnN0IHN0YXRlbWVudHM6IHRzLk5vZGVBcnJheTx0cy5TdGF0ZW1lbnQ+IHwgdW5kZWZpbmVkID1cblx0XHRcdFx0dHMuaXNCbG9jayhjdXJyZW50KSB8fCB0cy5pc01vZHVsZUJsb2NrKGN1cnJlbnQpIHx8IHRzLmlzU291cmNlRmlsZShjdXJyZW50KVxuXHRcdFx0XHRcdD8gY3VycmVudC5zdGF0ZW1lbnRzXG5cdFx0XHRcdFx0OiB0cy5pc0Nhc2VDbGF1c2UoY3VycmVudCkgfHwgdHMuaXNEZWZhdWx0Q2xhdXNlKGN1cnJlbnQpXG5cdFx0XHRcdFx0XHQ/IGN1cnJlbnQuc3RhdGVtZW50c1xuXHRcdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cdFx0XHRpZiAoc3RhdGVtZW50cyAmJiB0aGlzLnN0YXRlbWVudHNEZWNsYXJlVmFyaWFibGUoc3RhdGVtZW50cywgbmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcmhzID0gdGhpcy5maW5kQXNzaWdubWVudFJoc0luU3RhdGVtZW50cyhzdGF0ZW1lbnRzLCBuYW1lKTtcblx0XHRcdFx0cmV0dXJuIHJocztcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBUcnVlIHdoZW4gdGhlIHN0YXRlbWVudCBsaXN0IGNvbnRhaW5zIGEgYGxldGAvYHZhcmAvYGNvbnN0YFxuXHQgKiBkZWNsYXJhdGlvbiBmb3IgYG5hbWVgIChhbnkgaW5pdGlhbGl6ZXIgZm9ybSkuXG5cdCAqL1xuXHRwcml2YXRlIHN0YXRlbWVudHNEZWNsYXJlVmFyaWFibGUgKHN0YXRlbWVudHM6IHJlYWRvbmx5IHRzLlN0YXRlbWVudFtdLCBuYW1lOiBzdHJpbmcpOiBib29sZWFuIHtcblx0XHRmb3IgKGNvbnN0IHN0YXRlbWVudCBvZiBzdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAoIXRzLmlzVmFyaWFibGVTdGF0ZW1lbnQoc3RhdGVtZW50KSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3QgZGVjbGFyYXRpb24gb2Ygc3RhdGVtZW50LmRlY2xhcmF0aW9uTGlzdC5kZWNsYXJhdGlvbnMpIHtcblx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihkZWNsYXJhdGlvbi5uYW1lKSAmJiBkZWNsYXJhdGlvbi5uYW1lLnRleHQgPT09IG5hbWUpIHtcblx0XHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogRmlyc3QgYG5hbWUgPSByaHNgIGFzc2lnbm1lbnQgaW4gdGhlIHN0YXRlbWVudCBsaXN0LCByZWN1cnNpbmdcblx0ICogaW50byBuZXN0ZWQgaW4tc2NvcGUgYmxvY2tzLiBGdW5jdGlvbiBhbmQgY2xhc3MgYm9kaWVzIGFyZVxuXHQgKiBib3VuZGFyaWVzIGFuZCBhcmUgbm90IGVudGVyZWQuXG5cdCAqL1xuXHRwcml2YXRlIGZpbmRBc3NpZ25tZW50UmhzSW5TdGF0ZW1lbnRzIChcblx0XHRzdGF0ZW1lbnRzOiByZWFkb25seSB0cy5TdGF0ZW1lbnRbXSxcblx0XHRuYW1lOiBzdHJpbmdcblx0KTogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc3RhdGVtZW50cykge1xuXHRcdFx0Y29uc3QgZGlyZWN0ID0gdGhpcy5kaXJlY3RBc3NpZ25tZW50UmhzKHN0YXRlbWVudCwgbmFtZSk7XG5cdFx0XHRpZiAoZGlyZWN0KSB7XG5cdFx0XHRcdHJldHVybiBkaXJlY3Q7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IG5lc3RlZCBvZiB0aGlzLm5lc3RlZFNjb3BlQmxvY2tzKHN0YXRlbWVudCkpIHtcblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRBc3NpZ25tZW50UmhzSW5TdGF0ZW1lbnRzKG5lc3RlZCwgbmFtZSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIGBuYW1lID0gcmhzYCBhcyBhIGRpcmVjdCBleHByZXNzaW9uIHN0YXRlbWVudC5cblx0ICovXG5cdHByaXZhdGUgZGlyZWN0QXNzaWdubWVudFJocyAoc3RhdGVtZW50OiB0cy5TdGF0ZW1lbnQsIG5hbWU6IHN0cmluZyk6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHMuaXNFeHByZXNzaW9uU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGV4cHIgPSBzdGF0ZW1lbnQuZXhwcmVzc2lvbjtcblx0XHRpZiAoIXRzLmlzQmluYXJ5RXhwcmVzc2lvbihleHByKSB8fCBleHByLm9wZXJhdG9yVG9rZW4ua2luZCAhPT0gdHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbikge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoZXhwci5sZWZ0KSB8fCBleHByLmxlZnQudGV4dCAhPT0gbmFtZSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmhzID0gZXhwci5yaWdodDtcblx0XHRyZXR1cm4gcmhzO1xuXHR9XG5cblx0LyoqXG5cdCAqIFN0YXRlbWVudCBsaXN0cyBvZiB0aGUgbmVzdGVkIGJsb2NrcyB0aGF0IHN0YXkgSU5TSURFIHRoZSBjdXJyZW50XG5cdCAqIHNjb3BlIOKAlCB0cnkvY2F0Y2gvZmluYWxseSwgaWYvZWxzZSwgbG9vcHMsIHN3aXRjaCBjYXNlcywgbmVzdGVkXG5cdCAqIGJsb2NrcywgbGFiZWxlZCBzdGF0ZW1lbnRzLiBGdW5jdGlvbi1saWtlIGFuZCBjbGFzcyBib2RpZXMgYXJlXG5cdCAqIHNjb3BlIGJvdW5kYXJpZXMgYW5kIHlpZWxkIG5vdGhpbmcuXG5cdCAqL1xuXHRwcml2YXRlIG5lc3RlZFNjb3BlQmxvY2tzIChzdGF0ZW1lbnQ6IHRzLlN0YXRlbWVudCk6IHJlYWRvbmx5IChyZWFkb25seSB0cy5TdGF0ZW1lbnRbXSlbXSB7XG5cdFx0Y29uc3QgYmxvY2tzOiB0cy5TdGF0ZW1lbnRbXVtdID0gW107XG5cdFx0Y29uc3QgcHVzaCA9IChub2RlOiB0cy5TdGF0ZW1lbnQgfCB1bmRlZmluZWQpOiB2b2lkID0+IHtcblx0XHRcdGlmIChub2RlICYmIHRzLmlzQmxvY2sobm9kZSkpIHtcblx0XHRcdFx0YmxvY2tzLnB1c2goWyAuLi5ub2RlLnN0YXRlbWVudHMgXSk7XG5cdFx0XHR9XG5cdFx0fTtcblx0XHRpZiAodHMuaXNCbG9jayhzdGF0ZW1lbnQpKSB7XG5cdFx0XHRibG9ja3MucHVzaChbIC4uLnN0YXRlbWVudC5zdGF0ZW1lbnRzIF0pO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNUcnlTdGF0ZW1lbnQoc3RhdGVtZW50KSkge1xuXHRcdFx0cHVzaChzdGF0ZW1lbnQudHJ5QmxvY2spO1xuXHRcdFx0aWYgKHN0YXRlbWVudC5jYXRjaENsYXVzZSkge1xuXHRcdFx0XHRwdXNoKHN0YXRlbWVudC5jYXRjaENsYXVzZS5ibG9jayk7XG5cdFx0XHR9XG5cdFx0XHRwdXNoKHN0YXRlbWVudC5maW5hbGx5QmxvY2spO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNJZlN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRwdXNoKHN0YXRlbWVudC50aGVuU3RhdGVtZW50KTtcblx0XHRcdHB1c2goc3RhdGVtZW50LmVsc2VTdGF0ZW1lbnQpO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNGb3JTdGF0ZW1lbnQoc3RhdGVtZW50KSB8fCB0cy5pc0ZvckluU3RhdGVtZW50KHN0YXRlbWVudCkgfHxcblx0XHRcdHRzLmlzRm9yT2ZTdGF0ZW1lbnQoc3RhdGVtZW50KSB8fCB0cy5pc1doaWxlU3RhdGVtZW50KHN0YXRlbWVudCkgfHxcblx0XHRcdHRzLmlzRG9TdGF0ZW1lbnQoc3RhdGVtZW50KSB8fCB0cy5pc1dpdGhTdGF0ZW1lbnQoc3RhdGVtZW50KSkge1xuXHRcdFx0cHVzaChzdGF0ZW1lbnQuc3RhdGVtZW50KTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzU3dpdGNoU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdGZvciAoY29uc3QgY2xhdXNlIG9mIHN0YXRlbWVudC5jYXNlQmxvY2suY2xhdXNlcykge1xuXHRcdFx0XHRibG9ja3MucHVzaChbIC4uLmNsYXVzZS5zdGF0ZW1lbnRzIF0pO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSBpZiAodHMuaXNMYWJlbGVkU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdGNvbnN0IG5lc3RlZCA9IHRoaXMubmVzdGVkU2NvcGVCbG9ja3Moc3RhdGVtZW50LnN0YXRlbWVudCk7XG5cdFx0XHRmb3IgKGNvbnN0IGJsb2NrIG9mIG5lc3RlZCkge1xuXHRcdFx0XHRibG9ja3MucHVzaChbIC4uLmJsb2NrIF0pO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBibG9ja3M7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHRoZSBlbmNsb3NpbmcgbW5lbW9uaWNhIHNjb3BlIG9mIGFuIEVEUyBjYWxsIHNpdGUgYnkgd2Fsa2luZ1xuXHQgKiB1cCB0aGUgcGFyZW50IGNoYWluOiBuZWFyZXN0IGRlZmluZSgpL2xhenkoKSBjYWxsIHdob3NlIGhhbmRsZXIgaG9sZHNcblx0ICogdGhlIG5vZGUsIG9yIG5lYXJlc3QgQGRlY29yYXRlKCktZWQgY2xhc3MgZGVjbGFyYXRpb24uIEJlc3QgZWZmb3J0IOKAlFxuXHQgKiByZXR1cm5zIHVuZGVmaW5lZCBmb3IgY2FsbHMgb3V0c2lkZSBhbnkgdHlwZSBzY29wZSAobW9kdWxlIHRvcCBsZXZlbCkuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVFRFNTY29wZSAobm9kZTogdHMuTm9kZSk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBub2RlLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0Y29uc3Qgc2NvcGVQYXRoID0gdGhpcy5lZHNTY29wZUJ5Tm9kZS5nZXQoY3VycmVudCk7XG5cdFx0XHRpZiAoc2NvcGVQYXRoKSB7XG5cdFx0XHRcdHJldHVybiBzY29wZVBhdGg7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHdyYXAgc2l0ZSdzIGluc3RhbmNlL2NvbnRleHQgYXJndW1lbnQgdG8gYSBtbmVtb25pY2EgdHlwZVxuXHQgKiBwYXRoIOKAlCB0aGUgZmlyZS1hbmQtZm9yZ2V0LXdyYXBwZXIgYXR0cmlidXRpb24gZmFsbGJhY2sgd2hlbiB0aGUgY2FsbFxuXHQgKiBzaXRzIG91dHNpZGUgYW55IGRlZmluZSgpL2xhenkoKSBoYW5kbGVyOiBhIHRyYWNrZWQgYXNzaWdubWVudFxuXHQgKiAoYGNvbnN0IGhvbGRlciA9IG5ldyBIb2xkZXIoLi4uKWApLCBlbHNlIHRoZSByb290IGlkZW50aWZpZXInc1xuXHQgKiAocHJvcGVydHktYWNjZXNzIHJvb3RzIGluY2x1ZGVkKSBwYXJhbWV0ZXIgYW5ub3RhdGlvbiByZXNvbHZlZFxuXHQgKiB0aHJvdWdoIHRoZSBncmFwaCBsYXcuIEFtYmlndWl0eSBvciBhYnNlbmNlIHN0YXlzIHNpbGVudCDigJQgdGhpcyBpcyBhXG5cdCAqIG1ldGFkYXRhIGhldXJpc3RpYywgbm90IHRoZSBpZGVudGl0eS1sYXcgc3VyZmFjZS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVdyYXBJbnN0YW5jZVR5cGVQYXRoIChhcmc6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGZyb21CaW5kaW5nID0gKG5hbWU6IHN0cmluZywgZnJvbTogdHMuTm9kZSk6IHN0cmluZyB8IHVuZGVmaW5lZCA9PiB7XG5cdFx0XHRjb25zdCBtYXBwZWQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChuYW1lKTtcblx0XHRcdGlmIChtYXBwZWQpIHtcblx0XHRcdFx0cmV0dXJuIG1hcHBlZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGFubm90YXRpb25UeXBlID0gdGhpcy5yZXNvbHZlUGFyYW1ldGVyQW5ub3RhdGlvblR5cGVQYXRoKG5hbWUsIGZyb20pID8/XG5cdFx0XHRcdC8vIEYyMCBjaGVhcCB0aWVyOiB0aGUgaWRlbnRpZmllciBpcyBib3VuZCB0byBhIGxldC92YXIvY29uc3Rcblx0XHRcdFx0Ly8gd2l0aCBhbiBFWFBMSUNJVCB0eXBlIGFubm90YXRpb24g4oCUIHJlc29sdmUgdGhlIGFubm90YXRpb25cblx0XHRcdFx0Ly8gdGhyb3VnaCB0aGUgZ3JhcGggbGF3LiBObyBmbG93LXNlbnNpdGl2ZSBhc3NpZ25tZW50XG5cdFx0XHRcdC8vIHRyYWNraW5nOiBhbiBVTkFOTk9UQVRFRCBsZXQgc3RpbGwgYnVja2V0cyB1bmtub3duXG5cdFx0XHRcdHRoaXMucmVzb2x2ZVZhcmlhYmxlQW5ub3RhdGlvblR5cGVQYXRoKG5hbWUsIGZyb20pO1xuXHRcdFx0cmV0dXJuIGFubm90YXRpb25UeXBlO1xuXHRcdH07XG5cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGZyb21CaW5kaW5nKGFyZy50ZXh0LCBhcmcpO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdGNvbnN0IHJvb3QgPSB0aGlzLmdldFJvb3RJZGVudGlmaWVyKGFyZyk7XG5cdFx0XHRpZiAocm9vdCkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQgPSBmcm9tQmluZGluZyhyb290LnRleHQsIGFyZyk7XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRW1pc3Npb24tbGF3IGhlbHBlciAoMC4yLjAgcmVzdG9yYXRpb24pOiBpcyBgbmFtZWAgZGVjbGFyZWQgaW4gYW55XG5cdCAqIEFOQUxZWkVEIFBST0pFQ1QgZmlsZT8gRXh0ZXJuYWwvYW1iaWVudCBmaWxlcyAoLmQudHMsIG5vZGVfbW9kdWxlcylcblx0ICogZG8gbm90IGNvdW50LiBBIG5hbWUgd2l0aCBubyBwcm9qZWN0IGRlY2xhcmF0aW9uIGlzIGFuIGFtYmllbnQvbGliXG5cdCAqIGNvbnN0cnVjdCDigJQgc2FmZSB0byBlbWl0IHZlcmJhdGltIGludG8gdGhlIHNlbGYtY29udGFpbmVkIHR5cGVzLnRzO1xuXHQgKiBhIHByb2plY3QtbG9jYWwgbmFtZSBpcyBub3QgKG5vIGltcG9ydHMgaW4gdGhlIGdlbmVyYXRlZCBmaWxlKS5cblx0ICovXG5cdHByaXZhdGUgaXNQcm9qZWN0RGVjbGFyZWRUeXBlTmFtZSAobmFtZTogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0Zm9yIChjb25zdCBbIGZpbGUsIGRlY2xzIF0gb2YgdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzKSB7XG5cdFx0XHRpZiAodGhpcy5pc0V4dGVybmFsRGVjbEZpbGUoZmlsZSkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRpZiAoZGVjbHMuaGFzKG5hbWUpKSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBmYWxzZTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEYyNDogcmVzb2x2ZSBhIGJhcmUtaWRlbnRpZmllciBhbm5vdGF0aW9uIHRvIGEgZ3JhcGggZnVsbFBhdGguIFRoZVxuXHQgKiBhbm5vdGF0aW9uIG1heSBuYW1lIHRoZSB0eXBlIGRpcmVjdGx5IChgTGVkZ2VyVXBkYXRlYCkgb3IgY2Fycnlcblx0ICogdGhlIEdFTkVSQVRFRCBpbnN0YW5jZSBhbGlhcyBvZiBhIG5lc3RlZCB0eXBlXG5cdCAqIChgVXBkYXRlUGF5X1NvbWVUZXJtaW5hbGAsIGltcG9ydGVkIGZyb20gdGhlIGdlbmVyYXRlZCB0eXBlcyBmaWxlXG5cdCAqIHZpYSB0c2NvbmZpZyBwYXRocykg4oCUIG5vdCBhIGdyYXBoIG5vZGUgTkFNRS4gVGhlIG5hbWUgaXMgdHJpZWRcblx0ICogYXMtaXMgZmlyc3QsIHRoZW4gaXRzIHVuZGVyc2NvcmXihpJkb3R0ZWQgZm9ybSAodGhlIGdlbmVyYXRlZCBhbGlhc1xuXHQgKiBuYW1pbmcgbGF3OyB0aGUgc2FtZSBtYXBwaW5nIHNjb3Blcy5qc29uIHVzZXMgZm9yIGFubm90YXRpb25zKS5cblx0ICogQW1iaWd1aXR5IGFuZCBhYnNlbmNlIHlpZWxkIHVuZGVmaW5lZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUFubm90YXRpb25UeXBlUGF0aCAobmFtZTogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBkaXJlY3QgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKG5hbWUpO1xuXHRcdGlmIChkaXJlY3Quc3RhdHVzID09PSAndW5pcXVlJykge1xuXHRcdFx0Y29uc3QgcmVzdWx0ID0gZGlyZWN0Lm5vZGUuZnVsbFBhdGg7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH1cblx0XHRpZiAoIW5hbWUuaW5jbHVkZXMoJ18nKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgYWxpYXNlZCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUobmFtZS5yZXBsYWNlKC9fL2csICcuJykpO1xuXHRcdGlmIChhbGlhc2VkLnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGFsaWFzZWQubm9kZS5mdWxsUGF0aDtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGJhcmUtaWRlbnRpZmllciB0eXBlIGFubm90YXRpb24gb2YgdGhlIG5lYXJlc3QgZW5jbG9zaW5nXG5cdCAqIGZ1bmN0aW9uJ3MgcGFyYW1ldGVyIHRocm91Z2ggdGhlIG1uZW1vbmljYS1ncmFwaCB0aWVycyAodmFsdWUgc2NvcGUsXG5cdCAqIGltcG9ydHMsIHJvb3RzLCBwcm9ncmFtLXdpZGUtdW5pcXVlKS4gTm9uLWlkZW50aWZpZXIgYW5kIGdlbmVyaWNcblx0ICogYW5ub3RhdGlvbnMgYXJlIG5vdCBncmFwaCByZWZlcmVuY2VzOyBhbWJpZ3VpdHkgYW5kIGFic2VuY2UgeWllbGRcblx0ICogdW5kZWZpbmVkLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlUGFyYW1ldGVyQW5ub3RhdGlvblR5cGVQYXRoIChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gZnJvbS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc0Z1bmN0aW9uTGlrZShjdXJyZW50KSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGN1cnJlbnQucGFyYW1ldGVycyA/PyBbXSkge1xuXHRcdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpIHx8IHBhcmFtLm5hbWUudGV4dCAhPT0gbmFtZSB8fCAhcGFyYW0udHlwZSB8fFxuXHRcdFx0XHRcdFx0IXRzLmlzVHlwZVJlZmVyZW5jZU5vZGUocGFyYW0udHlwZSkgfHxcblx0XHRcdFx0XHRcdCF0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSkgfHxcblx0XHRcdFx0XHRcdChwYXJhbS50eXBlLnR5cGVBcmd1bWVudHM/Lmxlbmd0aCA/PyAwKSA+IDApIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCByZXNvbHZlZCA9IHRoaXMucmVzb2x2ZUFubm90YXRpb25UeXBlUGF0aChwYXJhbS50eXBlLnR5cGVOYW1lLnRleHQpO1xuXHRcdFx0XHRcdGlmIChyZXNvbHZlZCkge1xuXHRcdFx0XHRcdFx0cmV0dXJuIHJlc29sdmVkO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEYyMCBjaGVhcCB0aWVyOiB0aGUgd3JhcCBhcmd1bWVudCBpcyBhbiBpZGVudGlmaWVyIGRlY2xhcmVkIHdpdGggYW5cblx0ICogRVhQTElDSVQgdHlwZSBhbm5vdGF0aW9uIChgbGV0IHVwZGF0ZUNvbW1pdHRlZDogTGVkZ2VyVXBkYXRlO2Bcblx0ICogYXNzaWduZWQgbGF0ZXIgaW4gYSBmbG93IHRoZSBhbmFseXplciBkb2VzIG5vdCB0cmFjaykuIFRoZVxuXHQgKiBhbm5vdGF0aW9uIHJlc29sdmVzIHRocm91Z2ggdGhlIHNhbWUgZ3JhcGggdGllcnMgYXMgcGFyYW1ldGVyXG5cdCAqIGFubm90YXRpb25zLiBEZWxpYmVyYXRlbHkgTk9UIGZsb3ctc2Vuc2l0aXZlOiBhbiBVTkFOTk9UQVRFRFxuXHQgKiBsZXQvdmFyIHN0aWxsIGJ1Y2tldHMgdW5rbm93biwgYW5kIGEgY29uc3Qgd2l0aCBhbiBhbmFseXphYmxlXG5cdCAqIGluaXRpYWxpemVyIHN0YXlzIHRoZSByZWNvbW1lbmRlZCBkaXNjaXBsaW5lLiBUaGUgbG9va3VwIHdhbGtzIHRoZVxuXHQgKiBlbmNsb3Npbmcgc3RhdGVtZW50IGNvbnRhaW5lcnMgaW5uZXJtb3N0LW91dCwgc28gYSBzaGFkb3dpbmcgaW5uZXJcblx0ICogZGVjbGFyYXRpb24gd2lucy5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVZhcmlhYmxlQW5ub3RhdGlvblR5cGVQYXRoIChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gZnJvbTtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0Y29uc3Qgc3RhdGVtZW50czogdHMuTm9kZUFycmF5PHRzLlN0YXRlbWVudD4gfCB1bmRlZmluZWQgPVxuXHRcdFx0XHR0cy5pc0Jsb2NrKGN1cnJlbnQpIHx8IHRzLmlzTW9kdWxlQmxvY2soY3VycmVudCkgfHwgdHMuaXNTb3VyY2VGaWxlKGN1cnJlbnQpXG5cdFx0XHRcdFx0PyBjdXJyZW50LnN0YXRlbWVudHNcblx0XHRcdFx0XHQ6IHRzLmlzQ2FzZUNsYXVzZShjdXJyZW50KSB8fCB0cy5pc0RlZmF1bHRDbGF1c2UoY3VycmVudClcblx0XHRcdFx0XHRcdD8gY3VycmVudC5zdGF0ZW1lbnRzXG5cdFx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblx0XHRcdGlmIChzdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdGNvbnN0IHJlc29sdmVkID0gdGhpcy5maW5kQW5ub3RhdGVkVmFyaWFibGVUeXBlUGF0aChzdGF0ZW1lbnRzLCBuYW1lKTtcblx0XHRcdFx0aWYgKHJlc29sdmVkKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHJlc29sdmVkO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmlyc3QgdmFyaWFibGUgZGVjbGFyYXRpb24gY2FycnlpbmcgYW4gZXhwbGljaXQgYmFyZS1pZGVudGlmaWVyIHR5cGVcblx0ICogYW5ub3RhdGlvbiBmb3IgYG5hbWVgIGluIHRoZSBnaXZlbiBzdGF0ZW1lbnQgbGlzdCwgcmVzb2x2ZWQgdGhyb3VnaFxuXHQgKiB0aGUgZ3JhcGggbGF3LlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kQW5ub3RhdGVkVmFyaWFibGVUeXBlUGF0aCAoXG5cdFx0c3RhdGVtZW50czogcmVhZG9ubHkgdHMuU3RhdGVtZW50W10sXG5cdFx0bmFtZTogc3RyaW5nXG5cdCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc3RhdGVtZW50cykge1xuXHRcdFx0aWYgKCF0cy5pc1ZhcmlhYmxlU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGRlY2xhcmF0aW9uIG9mIHN0YXRlbWVudC5kZWNsYXJhdGlvbkxpc3QuZGVjbGFyYXRpb25zKSB7XG5cdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGRlY2xhcmF0aW9uLm5hbWUpIHx8IGRlY2xhcmF0aW9uLm5hbWUudGV4dCAhPT0gbmFtZSB8fFxuXHRcdFx0XHRcdCFkZWNsYXJhdGlvbi50eXBlIHx8XG5cdFx0XHRcdFx0IXRzLmlzVHlwZVJlZmVyZW5jZU5vZGUoZGVjbGFyYXRpb24udHlwZSkgfHxcblx0XHRcdFx0XHQhdHMuaXNJZGVudGlmaWVyKGRlY2xhcmF0aW9uLnR5cGUudHlwZU5hbWUpIHx8XG5cdFx0XHRcdFx0KGRlY2xhcmF0aW9uLnR5cGUudHlwZUFyZ3VtZW50cz8ubGVuZ3RoID8/IDApID4gMCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IHJlc29sdmVkID0gdGhpcy5yZXNvbHZlQW5ub3RhdGlvblR5cGVQYXRoKGRlY2xhcmF0aW9uLnR5cGUudHlwZU5hbWUudGV4dCk7XG5cdFx0XHRcdGlmIChyZXNvbHZlZCkge1xuXHRcdFx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSB3cmFwKCkgYXJndW1lbnQgdG8gaXRzIGZ1bmN0aW9uIG5vZGUgd2l0aG91dCB0aGUgdHlwZVxuXHQgKiBjaGVja2VyOiBkaXJlY3QgZnVuY3Rpb24gZXhwcmVzc2lvbnMvYXJyb3dzLCBvciBzYW1lLWZpbGUgYmluZGluZ3Ncblx0ICogKGBjb25zdCBmbiA9ICgpID0+IC4uLmAsIGBmdW5jdGlvbiBmbigpIC4uLmApLiBCZXN0IGVmZm9ydCDigJQgbWV0aG9kXG5cdCAqIHJlZmVyZW5jZXMsIC5iaW5kKCkgcHJvZHVjdHMgYW5kIGNyb3NzLWZpbGUgaWRlbnRpZmllcnMgc3RheVxuXHQgKiB1bnJlc29sdmVkOyB0aGUgY2FsbHNpdGUgZW50cnkgaXRzZWxmIGlzIHN0aWxsIHJlY29yZGVkLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRnVuY3Rpb25Bcmd1bWVudCAoXG5cdFx0YXJnOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGVcblx0KTogdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGlmICghYXJnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGFyZykgfHwgdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0cmV0dXJuIGFyZztcblx0XHR9XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihhcmcpKSB7XG5cdFx0XHRjb25zdCBrZXkgPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfSMke2FyZy50ZXh0fWA7XG5cdFx0XHRjb25zdCBib3VuZCA9IHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5nZXQoa2V5KTtcblx0XHRcdGlmIChib3VuZCkge1xuXHRcdFx0XHRyZXR1cm4gYm91bmQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogQW5hbHlzZSBhIHdyYXBwZWQgZnVuY3Rpb24ncyBib2R5IGZvciBndWFyYW50ZWVkIHJ1bnRpbWUgcGF0aHM6XG5cdCAqIGRpdmUgd3JhcHMgcmV0dXJuZWQgZnVuY3Rpb25zIGFzIHdlbGwgKHJlY3Vyc2l2ZWx5KSwgc28gZWFjaFxuXHQgKiBmdW5jdGlvbi12YWx1ZWQgcmV0dXJuIGlzIGEgbmVzdGVkIHdyYXAgc2l0ZSwgYW5kIGVhY2ggYG5ldyBUeXBlKClgXG5cdCAqIGluc2lkZSB0aGUgYm9keSBtZWFucyB0aGUgcGF0aCBoaXRzIHRoYXQgdHlwZSdzIGNvbnN0cnVjdG9yICh3aGljaFxuXHQgKiBhdHRhY2hIb29rcyB3cmFwcyB0b28pLiBCb3RoIGZhY3RzIGFyZSAxMDAlIGVuc3VyZWQsIHNvIHRoZXkgYXJlXG5cdCAqIHJlY29yZGVkIEFvVC4gTmVzdGVkIGZ1bmN0aW9uIGJvZGllcyBhcmUgTk9UIHdhbGtlZCBoZXJlIOKAlCB0aGV5XG5cdCAqIGJlbG9uZyB0byB0aGVpciBvd24gd3JhcCBhbmFseXNpcywgcmVhY2hlZCB2aWEgdGhlIHJldHVybiBjaGFpbi5cblx0ICogRGVwdGgtY2FwcGVkIGFuZCBjeWNsZS1ndWFyZGVkLlxuXHQgKi9cblx0cHJpdmF0ZSBhbmFseXplV3JhcHBlZEJvZHkgKFxuXHRcdGZuOiB0cy5GdW5jdGlvbkxpa2VEZWNsYXJhdGlvbixcblx0XHR2aWFMb2NhdGlvbjogc3RyaW5nLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0ZGVwdGg6IG51bWJlcixcblx0XHR2aXNpdGVkOiBTZXQ8dHMuTm9kZT4sXG5cdFx0Y3JlYXRlc1R5cGVzOiBTZXQ8c3RyaW5nPixcblx0XHRmYWxsYmFja1Njb3BlPzogc3RyaW5nXG5cdCk6IHZvaWQge1xuXHRcdGlmIChkZXB0aCA+IDUgfHwgdmlzaXRlZC5oYXMoZm4pIHx8ICFmbi5ib2R5KSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHZpc2l0ZWQuYWRkKGZuKTtcblxuXHRcdC8vIEFycm93IHdpdGggZXhwcmVzc2lvbiBib2R5OiBpbXBsaWNpdCByZXR1cm5cblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGZuKSAmJiAhdHMuaXNCbG9jayhmbi5ib2R5KSkge1xuXHRcdFx0dGhpcy5yZWNvcmRXcmFwcGVkUmV0dXJuKGZuLmJvZHksIHZpYUxvY2F0aW9uLCBzb3VyY2VGaWxlLCBkZXB0aCwgdmlzaXRlZCwgZmFsbGJhY2tTY29wZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3Qgd2FsayA9IChub2RlOiB0cy5Ob2RlKTogdm9pZCA9PiB7XG5cdFx0XHRpZiAobm9kZSAhPT0gZm4uYm9keSAmJiAoXG5cdFx0XHRcdHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKG5vZGUpIHx8XG5cdFx0XHRcdHRzLmlzQXJyb3dGdW5jdGlvbihub2RlKSB8fFxuXHRcdFx0XHR0cy5pc0Z1bmN0aW9uRGVjbGFyYXRpb24obm9kZSkgfHxcblx0XHRcdFx0dHMuaXNNZXRob2REZWNsYXJhdGlvbihub2RlKVxuXHRcdFx0KSkge1xuXHRcdFx0XHQvLyBuZXN0ZWQgZnVuY3Rpb24gYm9kaWVzIGFyZSBhbmFseXNlZCB0aHJvdWdoIHRoZSByZXR1cm4gY2hhaW5cblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0XHR0aGlzLnJlY29yZFdyYXBwZWRSZXR1cm4obm9kZS5leHByZXNzaW9uLCB2aWFMb2NhdGlvbiwgc291cmNlRmlsZSwgZGVwdGgsIHZpc2l0ZWQsIGZhbGxiYWNrU2NvcGUpO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzTmV3RXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0XHRjb25zdCBjcmVhdGVkID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKSB8fFxuXHRcdFx0XHRcdCh0cy5pc0lkZW50aWZpZXIobm9kZS5leHByZXNzaW9uKSAmJiB0aGlzLmRlZmluaXRpb25zLmhhcyhub2RlLmV4cHJlc3Npb24udGV4dClcblx0XHRcdFx0XHRcdD8gbm9kZS5leHByZXNzaW9uLnRleHRcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkKTtcblx0XHRcdFx0aWYgKGNyZWF0ZWQpIHtcblx0XHRcdFx0XHRjcmVhdGVzVHlwZXMuYWRkKGNyZWF0ZWQpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0XHRjb25zdCBuZXN0ZWROYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKTtcblx0XHRcdFx0aWYgKFxuXHRcdFx0XHRcdG5lc3RlZE5hbWUgPT09ICd3cmFwJyB8fFxuXHRcdFx0XHRcdG5lc3RlZE5hbWUgPT09ICd3cmFwQ29uc3RydWN0b3JBcmcnIHx8XG5cdFx0XHRcdFx0bmVzdGVkTmFtZSA9PT0gJ3VwZ3JhZGVDb25zdHJ1Y3RvckFyZycgfHxcblx0XHRcdFx0XHRuZXN0ZWROYW1lID09PSAnd3JhcEluc3RhbmNlTWV0aG9kcydcblx0XHRcdFx0KSB7XG5cdFx0XHRcdFx0Ly8gdGhlIG5lc3RlZCBjYWxsIG1heSBhbHJlYWR5IGJlIGNvbGxlY3RlZCAodmlzaXRlZFxuXHRcdFx0XHRcdC8vIGJlZm9yZSB0aGlzIG91dGVyIHdyYXAgc2l0ZSkg4oCUIGJhY2stcGF0Y2ggaXRzIGVudHJ5LFxuXHRcdFx0XHRcdC8vIG90aGVyd2lzZSBsZWF2ZSB0aGUgbGluayAod2l0aCB0aGlzIHNpdGUncyBzY29wZSkgZm9yXG5cdFx0XHRcdFx0Ly8gY29sbGVjdEVEUyB0byBwaWNrIHVwXG5cdFx0XHRcdFx0Y29uc3QgbmVzdGVkRW50cnkgPSB0aGlzLndyYXBFbnRyeUJ5Tm9kZS5nZXQobm9kZSk7XG5cdFx0XHRcdFx0aWYgKG5lc3RlZEVudHJ5KSB7XG5cdFx0XHRcdFx0XHRuZXN0ZWRFbnRyeS52aWEgPSB2aWFMb2NhdGlvbjtcblx0XHRcdFx0XHRcdGlmIChuZXN0ZWRFbnRyeS5zY29wZSA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdFx0XHRcdG5lc3RlZEVudHJ5LnNjb3BlID0gZmFsbGJhY2tTY29wZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0dGhpcy5uZXN0ZWRXcmFwVmlhLnNldChub2RlLCB7IHZpYSA6IHZpYUxvY2F0aW9uLCBzY29wZSA6IGZhbGxiYWNrU2NvcGUgfSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgd2Fsayk7XG5cdFx0fTtcblx0XHR3YWxrKGZuLmJvZHkpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBvbmUgZnVuY3Rpb24tdmFsdWVkIHJldHVybiBvZiBhIHdyYXBwZWQgYm9keSBhcyBhIG5lc3RlZCB3cmFwXG5cdCAqIHNpdGUgKGB2aWFgID0gdGhlIHNpdGUgd2hvc2Ugd3JhcHBpbmcgY2F1c2VkIGl0KSBhbmQgcmVjdXJzZSBpbnRvXG5cdCAqIGl0cyBvd24gcmV0dXJucy4gUmV0dXJucyB0aHJvdWdoIGlkZW50aWZpZXJzIHJlc29sdmUgdGhyb3VnaCB0aGVcblx0ICogc2FtZS1maWxlIGJpbmRpbmdzIHRhYmxlOyB1bnJlc29sdmFibGUgcmV0dXJucyBhcmUgc2ltcGx5IHNraXBwZWQuXG5cdCAqIEEgcmV0dXJuIGRlY2xhcmVkIG91dHNpZGUgYW55IHR5cGUgc2NvcGUgaW5oZXJpdHMgdGhlIGNhdXNpbmcgd3JhcFxuXHQgKiBzaXRlJ3Mgc2NvcGUgYXR0cmlidXRpb24gKHRoZSBnZW5lcmF0aW9uIGNoYWluIGlzIHRoZSBvbmx5IGhvbGRlcikuXG5cdCAqL1xuXHRwcml2YXRlIHJlY29yZFdyYXBwZWRSZXR1cm4gKFxuXHRcdGV4cHI6IHRzLkV4cHJlc3Npb24sXG5cdFx0dmlhTG9jYXRpb246IHN0cmluZyxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdGRlcHRoOiBudW1iZXIsXG5cdFx0dmlzaXRlZDogU2V0PHRzLk5vZGU+LFxuXHRcdGZhbGxiYWNrU2NvcGU/OiBzdHJpbmdcblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgcmV0dXJuZWQgPSB0aGlzLnJlc29sdmVGdW5jdGlvbkFyZ3VtZW50KGV4cHIsIHNvdXJjZUZpbGUpO1xuXHRcdGlmICghcmV0dXJuZWQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdHJldHVybmVkLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSByZXR1cm5lZC5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cdFx0Y29uc3Qgc2NvcGUgPSB0aGlzLnJlc29sdmVFRFNTY29wZShyZXR1cm5lZCkgPz8gZmFsbGJhY2tTY29wZTtcblx0XHRjb25zdCBlbnRyeSA9IHRoaXMuYWRkRURTKHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kIDogJ3dyYXAnLFxuXHRcdFx0Y29kZSxcblx0XHRcdHNjb3BlLFxuXHRcdFx0dmlhICA6IHZpYUxvY2F0aW9uLFxuXHRcdFx0Ly8gZGl2ZSB3cmFwcyByZXR1cm5lZCBmdW5jdGlvbnMgdGhyb3VnaCB0aGUgc2FtZSB3cmFwIG1hY2hpbmVyeVxuXHRcdFx0Zm4gICA6ICd3cmFwJyxcblx0XHR9KTtcblx0XHQvLyB0aGUgcmV0dXJuZWQgZnVuY3Rpb24ncyBvd24gcmV0dXJucyBhcmUgd3JhcHBlZCBpbiB0dXJuOyBgdmlhYFxuXHRcdC8vIGNoYWlucyB0byB0aGlzIG5lc3RlZCBlbnRyeSdzIGxvY2F0aW9uXG5cdFx0Y29uc3QgbmVzdGVkQ3JlYXRlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdHRoaXMuYW5hbHl6ZVdyYXBwZWRCb2R5KHJldHVybmVkLCBsb2NhdGlvbiwgc291cmNlRmlsZSwgZGVwdGggKyAxLCB2aXNpdGVkLCBuZXN0ZWRDcmVhdGVzLCBzY29wZSk7XG5cdFx0aWYgKG5lc3RlZENyZWF0ZXMuc2l6ZSA+IDApIHtcblx0XHRcdGVudHJ5LmNyZWF0ZXNUeXBlcyA9IEFycmF5LmZyb20obmVzdGVkQ3JlYXRlcyk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhbiBFRFMgdXNhZ2UgdG8gdGhlIGNvbGxlY3Rpb25cblx0ICogUmV0dXJucyB0aGUgc3RvcmVkIGVudHJ5ICh0aGUgZXhpc3Rpbmcgb25lIHdoZW4gdGhpcyBpcyBhIGR1cGxpY2F0ZSksXG5cdCAqIHNvIGNhbGxlcnMgY2FuIGVucmljaCBpdCBhZnRlciBuZXN0ZWQgYm9keSBhbmFseXNpcy5cblx0ICovXG5cdHByaXZhdGUgYWRkRURTICh0eXBlUGF0aDogc3RyaW5nLCBpbmZvOiBFRFNJbmZvKTogRURTSW5mbyB7XG5cdFx0aWYgKCF0aGlzLmVkc1VzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLmVkc1VzYWdlcy5zZXQodHlwZVBhdGgsIFtdKTtcblx0XHR9XG5cblx0XHRjb25zdCBleGlzdGluZyA9IHRoaXMuZWRzVXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGR1cGxpY2F0ZSA9IGV4aXN0aW5nLmZpbmQoZSA9PiB7XG5cdFx0XHRyZXR1cm4gZS5sb2NhdGlvbiA9PT0gaW5mby5sb2NhdGlvbiAmJlxuXHRcdFx0XHRlLmtpbmQgPT09IGluZm8ua2luZCAmJlxuXHRcdFx0XHRlLmNvZGUgPT09IGluZm8uY29kZTtcblx0XHR9KTtcblxuXHRcdGlmIChkdXBsaWNhdGUpIHtcblx0XHRcdHJldHVybiBkdXBsaWNhdGU7XG5cdFx0fVxuXHRcdGV4aXN0aW5nLnB1c2goaW5mbyk7XG5cdFx0cmV0dXJuIGluZm87XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBuYXRpdmUgZmxvdyBwYXR0ZXJucyAoaW5zdGFuY2UgdXNhZ2UgYWZ0ZXIgY3JlYXRpb24pXG5cdCAqIFBoYXNlIDE6IHByb3BlcnR5IGFjY2VzcywgbWV0aG9kIGNhbGxzLCBhcmd1bWVudHMsIHJldHVybiwgZGVzdHJ1Y3R1cmluZywgZXRjLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0RmxvdyAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIFByb3BlcnR5IHJlYWQ6IHVzZXIubmFtZSBvciB1c2VyPy5uYW1lXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93UHJvcGVydHlBY2Nlc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRWxlbWVudCBhY2Nlc3M6IHVzZXJbJ25hbWUnXVxuXHRcdGlmICh0cy5pc0VsZW1lbnRBY2Nlc3NFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93RWxlbWVudEFjY2Vzcyhub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSB3cml0ZTogdXNlci5uYW1lID0gdmFsdWVcblx0XHRpZiAodHMuaXNCaW5hcnlFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkVxdWFsc1Rva2VuKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93QXNzaWdubWVudChub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBNZXRob2QgY2FsbDogdXNlci52YWxpZGF0ZSgpICBBTkQgIGFyZ3VtZW50IHBhc3Npbmc6IHByb2Nlc3NVc2VyKHVzZXIpXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93TWV0aG9kQ2FsbChub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dBcmd1bWVudFBhc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRGVzdHJ1Y3R1cmUgcmVhZDogY29uc3QgeyBuYW1lIH0gPSB1c2VyXG5cdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLmluaXRpYWxpemVyKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93RGVzdHJ1Y3R1cmUobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUmV0dXJuIGluc3RhbmNlOiByZXR1cm4gdXNlclxuXHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dSZXR1cm4obm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gU3ByZWFkOiB7IC4uLnVzZXIgfVxuXHRcdGlmICh0cy5pc1NwcmVhZEVsZW1lbnQobm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dTcHJlYWQobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgcHJvcGVydHkgYWNjZXNzIGZsb3cgKHJlYWQgb3IgY29uZGl0aW9uYWwpXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93UHJvcGVydHlBY2Nlc3MgKG5vZGU6IHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHByb3BOYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0Ly8gU2tpcCBpZiB0aGlzIGlzIGEgdHlwZSBjb25zdHJ1Y3RvciBhY2Nlc3MgKGUuZy4sIFVzZXJUeXBlLmRlZmluZSlcblx0XHRpZiAocHJvcE5hbWUgPT09ICdkZWZpbmUnIHx8IHByb3BOYW1lID09PSAnbGF6eScpIHsgcmV0dXJuOyB9XG5cblx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgICAgOiAncHJvcGVydHlSZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHRwcm9wZXJ0eU5hbWUgOiBwcm9wTmFtZSxcblx0XHRcdHRhcmdldFR5cGUgICA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGVsZW1lbnQgYWNjZXNzIGZsb3c6IHVzZXJbJ25hbWUnXVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0VsZW1lbnRBY2Nlc3MgKG5vZGU6IHRzLkVsZW1lbnRBY2Nlc3NFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3Qgb2JqZWN0VHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0aWYgKCFvYmplY3RUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0dGhpcy5hZGRGbG93KG9iamVjdFR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICA6ICdlbGVtZW50QWNjZXNzJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogb2JqZWN0VHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgYXNzaWdubWVudCBmbG93OiB1c2VyLm5hbWUgPSB2YWx1ZSBvciB1c2VyID0gb3RoZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dBc3NpZ25tZW50IChub2RlOiB0cy5CaW5hcnlFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gUHJvcGVydHkgd3JpdGU6IHVzZXIubmFtZSA9IHZhbHVlXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUubGVmdCkpIHtcblx0XHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmxlZnQuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRcdGNvbnN0IHByb3BOYW1lID0gbm9kZS5sZWZ0Lm5hbWUudGV4dDtcblx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0KTtcblx0XHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgICAgOiAncHJvcGVydHlXcml0ZScsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHByb3BlcnR5TmFtZSA6IHByb3BOYW1lLFxuXHRcdFx0XHR0YXJnZXRUeXBlICAgOiBvYmplY3RUeXBlXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBWYXJpYWJsZSByZWFzc2lnbm1lbnQ6IHVzZXIgPSBvdGhlclxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIobm9kZS5sZWZ0KSkge1xuXHRcdFx0Y29uc3QgdmFyTmFtZSA9IG5vZGUubGVmdC50ZXh0O1xuXHRcdFx0Y29uc3QgbWFwcGVkVHlwZSA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KHZhck5hbWUpO1xuXHRcdFx0aWYgKCFtYXBwZWRUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdCk7XG5cdFx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0XHR0aGlzLmFkZEZsb3cobWFwcGVkVHlwZSwge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCAgICAgICA6ICdyZWFzc2lnbm1lbnQnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHR0YXJnZXRUeXBlIDogbWFwcGVkVHlwZVxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgbWV0aG9kIGNhbGwgZmxvdzogdXNlci52YWxpZGF0ZSgpXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93TWV0aG9kQ2FsbCAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbikpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IG1ldGhvZE5hbWUgPSBub2RlLmV4cHJlc3Npb24ubmFtZS50ZXh0O1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIFNraXAgaWYgdGhpcyBpcyBhIHR5cGUgY29uc3RydWN0b3IgY2FsbCAoZS5nLiwgbmV3IFVzZXJUeXBlKCkpXG5cdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdkZWZpbmUnIHx8IG1ldGhvZE5hbWUgPT09ICdsYXp5JykgeyByZXR1cm47IH1cblxuXHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgICA6ICdtZXRob2RDYWxsJyxcblx0XHRcdGNvZGUsXG5cdFx0XHRwcm9wZXJ0eU5hbWUgOiBtZXRob2ROYW1lLFxuXHRcdFx0dGFyZ2V0VHlwZSAgIDogb2JqZWN0VHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgYXJndW1lbnQgcGFzc2luZyBmbG93OiBwcm9jZXNzVXNlcih1c2VyKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0FyZ3VtZW50UGFzcyAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRjb25zdCBhcmcgPSBub2RlLmFyZ3VtZW50c1sgaSBdO1xuXHRcdFx0Y29uc3QgYXJnVHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKGFyZyk7XG5cdFx0XHRpZiAoIWFyZ1R5cGUpIHsgY29udGludWU7IH1cblxuXHRcdFx0Y29uc3QgZnVuY05hbWUgPSB0aGlzLmdldEZ1bmN0aW9uTmFtZShub2RlLmV4cHJlc3Npb24pIHx8ICdhbm9ueW1vdXMnO1xuXHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHQpO1xuXHRcdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdFx0dGhpcy5hZGRGbG93KGFyZ1R5cGUsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAncGFzc0FzQXJnJyxcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSA6IGFyZ1R5cGUsXG5cdFx0XHRcdGNvbnRleHQgICAgOiBgYXJnICR7aX0gdG8gJHtmdW5jTmFtZX1gXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBkZXN0cnVjdHVyaW5nIGZsb3c6IGNvbnN0IHsgbmFtZSB9ID0gdXNlclxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0Rlc3RydWN0dXJlIChub2RlOiB0cy5WYXJpYWJsZURlY2xhcmF0aW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc09iamVjdEJpbmRpbmdQYXR0ZXJuKG5vZGUubmFtZSkpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBzb3VyY2VUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5pbml0aWFsaXplciEpO1xuXHRcdGlmICghc291cmNlVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIEV4dHJhY3QgZGVzdHJ1Y3R1cmVkIHByb3BlcnR5IG5hbWVzXG5cdFx0Y29uc3QgcHJvcHM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIG5vZGUubmFtZS5lbGVtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihlbGVtZW50Lm5hbWUpKSB7XG5cdFx0XHRcdHByb3BzLnB1c2goZWxlbWVudC5uYW1lLnRleHQpO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHRoaXMuYWRkRmxvdyhzb3VyY2VUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnZGVzdHJ1Y3R1cmVSZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogc291cmNlVHlwZSxcblx0XHRcdGNvbnRleHQgICAgOiBwcm9wcy5qb2luKCcsICcpXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCByZXR1cm4gZmxvdzogcmV0dXJuIHVzZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dSZXR1cm4gKG5vZGU6IHRzLlJldHVyblN0YXRlbWVudCwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHJldHVyblR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24hKTtcblx0XHRpZiAoIXJldHVyblR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHR0aGlzLmFkZEZsb3cocmV0dXJuVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ3JldHVybicsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHJldHVyblR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IHNwcmVhZCBmbG93OiB7IC4uLnVzZXIgfVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd1NwcmVhZCAobm9kZTogdHMuU3ByZWFkRWxlbWVudCwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHNwcmVhZFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghc3ByZWFkVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuYWRkRmxvdyhzcHJlYWRUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnc3ByZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogc3ByZWFkVHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgdHlwZSBmcm9tIGFuIGV4cHJlc3Npb24gKGlkZW50aWZpZXIsIHByb3BlcnR5IGFjY2VzcywgZXRjLilcblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUV4cHJlc3Npb25UeXBlIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBJZGVudGlmaWVyOiB1c2VyXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGV4cHIudGV4dCk7XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiB1c2VyLm5hbWUgKHJldHVybiBvYmplY3QgdHlwZSwgbm90IHByb3BlcnR5IHR5cGUpXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUoZXhwci5leHByZXNzaW9uKTtcblx0XHR9XG5cblx0XHQvLyBFbGVtZW50IGFjY2VzczogdXNlclsnbmFtZSddXG5cdFx0aWYgKHRzLmlzRWxlbWVudEFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdHJldHVybiB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShleHByLmV4cHJlc3Npb24pO1xuXHRcdH1cblxuXHRcdC8vIFRoaXMgZXhwcmVzc2lvbjogdGhpcyAoaWYgaW4gYSBtZXRob2QsIHdlIGNhbid0IHJlc29sdmUgd2l0aG91dCBtb3JlIGNvbnRleHQpXG5cdFx0aWYgKGV4cHIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhIGZsb3cgdXNhZ2UgdG8gdGhlIGNvbGxlY3Rpb25cblx0ICovXG5cdHByaXZhdGUgYWRkRmxvdyAodHlwZVBhdGg6IHN0cmluZywgaW5mbzogRmxvd0luZm8pOiB2b2lkIHtcblx0XHRpZiAoIXRoaXMuZmxvd1VzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLmZsb3dVc2FnZXMuc2V0KHR5cGVQYXRoLCBbXSk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZXhpc3RpbmcgPSB0aGlzLmZsb3dVc2FnZXMuZ2V0KHR5cGVQYXRoKSE7XG5cdFx0Y29uc3QgaXNEdXBsaWNhdGUgPSBleGlzdGluZy5zb21lKGUgPT4ge1xuXHRcdFx0cmV0dXJuIGUubG9jYXRpb24gPT09IGluZm8ubG9jYXRpb24gJiZcblx0XHRcdFx0ZS5raW5kID09PSBpbmZvLmtpbmQgJiZcblx0XHRcdFx0ZS5jb2RlID09PSBpbmZvLmNvZGU7XG5cdFx0fSk7XG5cblx0XHRpZiAoIWlzRHVwbGljYXRlKSB7XG5cdFx0XHRleGlzdGluZy5wdXNoKGluZm8pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdFx0KiBHZXQgdHlwZSBuYW1lIGZyb20gZXhwcmVzc2lvbiAoaWRlbnRpZmllciBvciBwcm9wZXJ0eSBhY2Nlc3MpXG5cdFx0XHQqL1xuXHRwcml2YXRlIGdldFR5cGVOYW1lRnJvbUV4cHJlc3Npb24gKGV4cHI6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdGNvbnN0IG5hbWUgPSBleHByLnRleHQ7XG5cdFx0XHQvLyBDaGVjayBpZiB0aGlzIGlkZW50aWZpZXIgaXMgYSB2YXJpYWJsZSBtYXBwZWQgdG8gYSB0eXBlIChlLmcuLCBmcm9tIGxvb2t1cClcblx0XHRcdGNvbnN0IG1hcHBlZFR5cGUgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChuYW1lKTtcblx0XHRcdGlmIChtYXBwZWRUeXBlKSB7XG5cdFx0XHRcdHJldHVybiBtYXBwZWRUeXBlO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIG5hbWU7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4oZXhwcik7XG5cdFx0XHRyZXR1cm4gY2hhaW4uam9pbignLicpO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cdFxuXHQvKipcblx0ICogVGhlIG9uZSBjYW5kaWRhdGUgd2hvc2UgcGFyZW50IHR5cGUgaXMgZGVmaW5lZCBpbiBgZmlsZU5hbWVgLCBvclxuXHQgKiB1bmRlZmluZWQgd2hlbiBub25lIG9yIHNldmVyYWwgcXVhbGlmeS5cblx0ICovXG5cdHByaXZhdGUgc3VidHlwZU93bmVkQnlGaWxlIChjYW5kaWRhdGVzOiBzdHJpbmdbXSwgZmlsZU5hbWU6IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgZmlsZSA9IG5vZGVQYXRoLnJlc29sdmUoZmlsZU5hbWUpO1xuXHRcdGNvbnN0IG93bmVkID0gY2FuZGlkYXRlcy5maWx0ZXIoKGNhbmRpZGF0ZSkgPT4ge1xuXHRcdFx0Y29uc3QgcGFyZW50ID0gdGhpcy5kZWZpbml0aW9ucy5nZXQoY2FuZGlkYXRlKT8ucGFyZW50O1xuXHRcdFx0Y29uc3QgcGFyZW50TG9jYXRpb24gPSBwYXJlbnQgPyB0aGlzLmRlZmluaXRpb25zLmdldChwYXJlbnQpPy5sb2NhdGlvbiA6IHVuZGVmaW5lZDtcblx0XHRcdGNvbnN0IHBhcmVudEZpbGUgPSBwYXJlbnRMb2NhdGlvbiA/IHBhcmVudExvY2F0aW9uLnJlcGxhY2UoLzpcXGQrOlxcZCskLywgJycpIDogdW5kZWZpbmVkO1xuXHRcdFx0Y29uc3QgaW5GaWxlID0gcGFyZW50RmlsZSAhPT0gdW5kZWZpbmVkICYmIG5vZGVQYXRoLnJlc29sdmUocGFyZW50RmlsZSkgPT09IGZpbGU7XG5cdFx0XHRyZXR1cm4gaW5GaWxlO1xuXHRcdH0pO1xuXHRcdGNvbnN0IHJlc3VsdCA9IG93bmVkLmxlbmd0aCA9PT0gMSA/IG93bmVkWyAwIF0gOiB1bmRlZmluZWQ7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHRcdFx0KiBSZXNvbHZlIGZ1bGwgdHlwZSBwYXRoIGZyb20gcHJvcGVydHkgYWNjZXNzXG5cdFx0XHQqL1xuXHRwcml2YXRlIHJlc29sdmVUeXBlUGF0aCAoZXhwcjogdHMuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBjaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlDaGFpbihleHByKTtcblx0XHRpZiAoY2hhaW4ubGVuZ3RoID09PSAwKSByZXR1cm4gdW5kZWZpbmVkO1xuXHRcblx0XHQvLyBDaGVjayBpZiB0aGlzIGNoYWluIG1hdGNoZXMgYSBrbm93biB0eXBlXG5cdFx0Y29uc3QgZnVsbFBhdGggPSBjaGFpbi5qb2luKCcuJyk7XG5cdFx0aWYgKHRoaXMuZGVmaW5pdGlvbnMuaGFzKGZ1bGxQYXRoKSkge1xuXHRcdFx0cmV0dXJuIGZ1bGxQYXRoO1xuXHRcdH1cblx0XG5cdFx0Ly8gSW5zdGFuY2UgcmVjZWl2ZXI6IGBsZXNzb24uTmF0aXZlYCB3aGVyZSBgbGVzc29uYCBpcyBib3VuZCB0byBhXG5cdFx0Ly8gUnVuLkxlc3NvbiBpbnN0YW5jZSBtZWFucyBSdW4uTGVzc29uLk5hdGl2ZSDigJQgcmVzb2x2ZSB0aHJvdWdoIHRoZVxuXHRcdC8vIHZhcmlhYmxlJ3MgdHlwZSBiZWZvcmUgZmFsbGluZyBiYWNrIHRvIHRoZSBiYXJlIG5hbWVcblx0XHRpZiAoY2hhaW4ubGVuZ3RoID4gMSkge1xuXHRcdFx0Y29uc3QgcmVjZWl2ZXJUeXBlID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQoY2hhaW5bIDAgXSk7XG5cdFx0XHRjb25zdCB2aWFSZWNlaXZlciA9IHJlY2VpdmVyVHlwZSA/IGAke3JlY2VpdmVyVHlwZX0uJHtjaGFpbi5zbGljZSgxKS5qb2luKCcuJyl9YCA6IHVuZGVmaW5lZDtcblx0XHRcdGlmICh2aWFSZWNlaXZlciAmJiB0aGlzLmRlZmluaXRpb25zLmhhcyh2aWFSZWNlaXZlcikpIHtcblx0XHRcdFx0cmV0dXJuIHZpYVJlY2VpdmVyO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIFRyeSBqdXN0IHRoZSBwcm9wZXJ0eSBuYW1lXG5cdFx0Y29uc3QgcHJvcE5hbWUgPSBjaGFpblsgY2hhaW4ubGVuZ3RoIC0gMSBdO1xuXHRcdGNvbnN0IGNhbmRpZGF0ZXM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBbIHBhdGggXSBvZiB0aGlzLmRlZmluaXRpb25zKSB7XG5cdFx0XHRpZiAocGF0aC5lbmRzV2l0aChgLiR7cHJvcE5hbWV9YCkgfHwgcGF0aCA9PT0gcHJvcE5hbWUpIHtcblx0XHRcdFx0Y2FuZGlkYXRlcy5wdXNoKHBhdGgpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHQvLyBTZXZlcmFsIHR5cGVzIHNoYXJlIHRoZSBuYW1lIChDb3JyZWN0LlN0YXRVcGRhdGUgYW5kXG5cdFx0Ly8gTWlzdGFrZS5TdGF0VXBkYXRlKTogYG5ldyB0aGlzLlN0YXRVcGRhdGUoKWAgaW5zaWRlIGEgdHlwZSdzIG93blxuXHRcdC8vIGZpbGUgbWVhbnMgVEhBVCB0eXBlJ3Mgc3VidHlwZSDigJQgcHJlZmVyIHRoZSBjYW5kaWRhdGUgd2hvc2UgcGFyZW50XG5cdFx0Ly8gaXMgZGVmaW5lZCBpbiB0aGUgZmlsZSB0aGUgYWNjZXNzIHNpdHMgaW4gKHRvcG9sb2dpY2E6IG9uZSBmaWxlXG5cdFx0Ly8gcGVyIHR5cGUpLiBPdGhlcndpc2UgdGhlIGZpcnN0IG1hdGNoLCBhcyBiZWZvcmUuXG5cdFx0aWYgKGNhbmRpZGF0ZXMubGVuZ3RoID4gMSkge1xuXHRcdFx0Y29uc3Qgb3duZWQgPSB0aGlzLnN1YnR5cGVPd25lZEJ5RmlsZShjYW5kaWRhdGVzLCBleHByLmdldFNvdXJjZUZpbGUoKS5maWxlTmFtZSk7XG5cdFx0XHRpZiAob3duZWQpIHtcblx0XHRcdFx0cmV0dXJuIG93bmVkO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAoY2FuZGlkYXRlcy5sZW5ndGggPiAwKSB7XG5cdFx0XHRyZXR1cm4gY2FuZGlkYXRlc1sgMCBdO1xuXHRcdH1cblxuXHRcdHJldHVybiBmdWxsUGF0aDtcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQgKiBDaGVjayBpZiBhIG5hbWUgbG9va3MgbGlrZSBhIHR5cGUgKHN0YXJ0cyB3aXRoIHVwcGVyY2FzZSlcblx0XHRcdCAqL1xuXHRwcml2YXRlIGlzTGlrZWx5VHlwZU5hbWUgKG5hbWU6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRcdHJldHVybiBuYW1lWyAwIF0gPj0gJ0EnICYmIG5hbWVbIDAgXSA8PSAnWic7XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0ICogUmVzb2x2ZSBhIGNvbnN0cnVjdG9yIHBhcmFtZXRlciB0eXBlLCBleHBhbmRpbmcgaW5saW5lIG9iamVjdCBsaXRlcmFsc1xuXHRcdFx0ICogYW5kIHR5cGUgYWxpYXNlcyB3aGVyZSBwb3NzaWJsZS5cblx0XHRcdCAqL1xuXHRwcml2YXRlIHJlc29sdmVDb25zdHJ1Y3RvclBhcmFtVHlwZSAodHlwZU5vZGU6IHRzLlR5cGVOb2RlIHwgdW5kZWZpbmVkKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIXR5cGVOb2RlKSByZXR1cm4gdW5kZWZpbmVkO1xuXG5cdFx0Ly8gRGlyZWN0IGlubGluZSB0eXBlIGxpdGVyYWw6IHsgcHJvcDogdHlwZSB9XG5cdFx0aWYgKHRzLmlzVHlwZUxpdGVyYWxOb2RlKHR5cGVOb2RlKSkge1xuXHRcdFx0Y29uc3QgcHJvcHM6IHN0cmluZ1tdID0gW107XG5cdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiB0eXBlTm9kZS5tZW1iZXJzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRjb25zdCBvcHRpb25hbCA9IG1lbWJlci5xdWVzdGlvblRva2VuID8gJz8nIDogJyc7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRwcm9wcy5wdXNoKGAke3Byb3BOYW1lfSR7b3B0aW9uYWx9OiAke3R5cGV9YCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiBgeyAke3Byb3BzLmpvaW4oJzsgJyl9IH1gO1xuXHRcdH1cblxuXHRcdC8vIFR5cGUgcmVmZXJlbmNlOiB1c2FnZSwgVXNlckRhdGEsIGV0Yy4gLSByZXNvbHZlIGltcG9ydC1hd2FyZSBhbmRcblx0XHQvLyBleHBhbmQgdGhlIHJlZmVyZW5jZWQgZGVjbGFyYXRpb24gd2hlcmUgcG9zc2libGUgKEYxMClcblx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZSh0eXBlTm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKHR5cGVOb2RlLnR5cGVOYW1lKSkge1xuXHRcdFx0Y29uc3QgdHlwZU5hbWUgPSB0eXBlTm9kZS50eXBlTmFtZS50ZXh0O1xuXHRcdFx0Y29uc3QgZGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24odHlwZU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRpZiAoZGVjbCkge1xuXHRcdFx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMuZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihkZWNsKTtcblx0XHRcdFx0aWYgKGV4cGFuZGVkKSByZXR1cm4gZXhwYW5kZWQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBtbmVtb25pY2EgZ3JhcGggdHlwZXMga2VlcCB0aGVpciBzaW1wbGUgbmFtZSDigJQgdGhlIGdlbmVyYXRvclxuXHRcdFx0Ly8gdXBncmFkZXMgdGhlbSB0byBmdWxsLXBhdGggaW5zdGFuY2UgdHlwZSBuYW1lcy4gUmVzb2x1dGlvbiBpc1xuXHRcdFx0Ly8gcGF0aC1hd2FyZSAoaGFyZC1mYWlsIGxhdyk6IGFtYmlndWl0eSBiZXR3ZWVuIHJlYWwgZ3JhcGggdHlwZXNcblx0XHRcdC8vIHJlY29yZHMgYSBmYXRhbCBlcnJvciBpbnN0ZWFkIG9mIHNpbGVudGx5IHBpY2tpbmcgb25lLlxuXHRcdFx0Y29uc3QgZ3JhcGhSZXN1bHQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKHR5cGVOYW1lKTtcblx0XHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRcdGNvbnN0IHNpbXBsZVJlc3VsdCA9IHR5cGVOYW1lO1xuXHRcdFx0XHRyZXR1cm4gc2ltcGxlUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0aWYgKGdyYXBoUmVzdWx0LnN0YXR1cyA9PT0gJ2FtYmlndW91cycpIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yKHR5cGVOYW1lLCB0eXBlTm9kZSwgZ3JhcGhSZXN1bHQpO1xuXHRcdFx0XHRjb25zdCB1bmtub3duR3JhcGhSZXN1bHQgPSAndW5rbm93bic7XG5cdFx0XHRcdHJldHVybiB1bmtub3duR3JhcGhSZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBJZiBub3QgYW4gb2JqZWN0IHR5cGUgYWxpYXMsIHJldHVybiB0aGUgdHlwZSBuYW1lIHdpdGggYXJnc1xuXHRcdFx0aWYgKHR5cGVOb2RlLnR5cGVBcmd1bWVudHMgJiYgdHlwZU5vZGUudHlwZUFyZ3VtZW50cy5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdGlmIChLTk9XTl9HTE9CQUxfVFlQRVMuaGFzKHR5cGVOYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IGFyZ3MgPSB0eXBlTm9kZS50eXBlQXJndW1lbnRzLm1hcChhcmcgPT4gdGhpcy5pbmZlclR5cGUoYXJnKSk7XG5cdFx0XHRcdFx0cmV0dXJuIGAke3R5cGVOYW1lICB9PCR7ICBhcmdzLmpvaW4oJywgJykgIH0+YDtcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBnZW5lcmljIHJlZmVyZW5jZSB0byBhIG5vbi1nbG9iYWwsIG5vbi1ncmFwaCB0eXBlIGNhbm5vdCBiZVxuXHRcdFx0XHQvLyBlbWl0dGVkIGJhcmUgaW50byB0aGUgZ2VuZXJhdGVkIGZpbGVcblx0XHRcdFx0dGhpcy5yZWNvcmRQbGFpblR5cGVSZWZlcmVuY2VTaXRlKHR5cGVOYW1lLCB0eXBlTm9kZSk7XG5cdFx0XHRcdGNvbnN0IHVua25vd25HZW5lcmljUmVzdWx0ID0gJ3Vua25vd24nO1xuXHRcdFx0XHRyZXR1cm4gdW5rbm93bkdlbmVyaWNSZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBmYWxsYmFja1Jlc3VsdCA9IHRoaXMudW5yZXNvbHZlZFR5cGVSZWZlcmVuY2VGYWxsYmFjayh0eXBlTmFtZSwgdHlwZU5vZGUpO1xuXHRcdFx0cmV0dXJuIGZhbGxiYWNrUmVzdWx0O1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0XHRcdCAqIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGEgY2xhc3MtbGlrZSBub2RlLlxuXHRcdFx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENsYXNzQ29uc3RydWN0b3JQYXJhbXMgKGNsYXNzTGlrZTogdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHRzLkNsYXNzRXhwcmVzc2lvbik6XG5cdFx0Q29uc3RydWN0b3JQYXJhbUluZm9bXSB7XG5cdFx0Y29uc3QgcGFyYW1zOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdID0gW107XG5cblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjbGFzc0xpa2UubWVtYmVycykge1xuXHRcdFx0aWYgKCF0cy5pc0NvbnN0cnVjdG9yRGVjbGFyYXRpb24obWVtYmVyKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblxuXHRcdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBtZW1iZXIucGFyYW1ldGVycykge1xuXHRcdFx0XHRpZiAoIXBhcmFtLm5hbWUgfHwgIXRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSkgY29udGludWU7XG5cdFx0XHRcdGlmICghcGFyYW0udHlwZSkgY29udGludWU7XG5cblx0XHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gcGFyYW0ubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBleHBhbmRlZFR5cGUgPSB0aGlzLnJlc29sdmVDb25zdHJ1Y3RvclBhcmFtVHlwZShwYXJhbS50eXBlKSB8fCB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblxuXHRcdFx0XHRwYXJhbXMucHVzaCh7XG5cdFx0XHRcdFx0bmFtZSAgICAgOiBwYXJhbU5hbWUsXG5cdFx0XHRcdFx0dHlwZSAgICAgOiBleHBhbmRlZFR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiAhIXBhcmFtLnF1ZXN0aW9uVG9rZW4gfHwgISFwYXJhbS5pbml0aWFsaXplcixcblx0XHRcdFx0XHQvLyByZXN0IG1hcmtlciBmb3IgdGhlIGRlZmluaXRpb25zLmpzb24gYXJncyBjb250cmFjdFxuXHRcdFx0XHRcdC4uLihwYXJhbS5kb3REb3REb3RUb2tlbiA/IHsga2luZCA6ICdyZXN0JyBhcyBjb25zdCB9IDoge30pXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdFx0Ly8gT25seSBwcm9jZXNzIGZpcnN0IGNvbnN0cnVjdG9yXG5cdFx0XHRicmVhaztcblx0XHR9XG5cblx0XHRyZXR1cm4gcGFyYW1zO1xuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBkZWZpbmUoKSBjYWxsXG5cdFx0XHQgKiBUaGlzIGlzIHVzZWQgZm9yIFR5cGVSZWdpc3RyeSBjb25zdHJ1Y3RvciBzaWduYXR1cmVzXG5cdFx0XHQgKiBQcmVzZXJ2ZXMgcGFyYW1ldGVyIG5hbWVzIGFuZCBleHBhbmRzIG9iamVjdCB0eXBlcyB0byB0aGVpciBzdHJ1Y3R1cmVcblx0XHRcdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdIHtcblx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCk7XG5cdFx0aWYgKCFjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdGNvbnN0IGZhbGxiYWNrUGFyYW1zOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdID0gWyB7XG5cdFx0XHRcdG5hbWUgICAgIDogJ2FyZ3MnLFxuXHRcdFx0XHR0eXBlICAgICA6ICd1bmtub3duW10nLFxuXHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRraW5kICAgICA6ICdyZXN0Jyxcblx0XHRcdH0gXTtcblx0XHRcdHJldHVybiBmYWxsYmFja1BhcmFtcztcblx0XHR9XG5cdFx0Y29uc3QgcmVmZXJlbmNpbmdGaWxlID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9IG5vZGVQYXRoLnJlc29sdmUoY29uc3RydWN0b3JFeHByLmdldFNvdXJjZUZpbGUoKS5maWxlTmFtZSk7XG5cdFx0dHJ5IHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zRnJvbUNvbnN0cnVjdG9yKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH0gZmluYWxseSB7XG5cdFx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSByZWZlcmVuY2luZ0ZpbGU7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBhIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24uXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JQYXJhbXNGcm9tQ29uc3RydWN0b3IgKGNvbnN0cnVjdG9yRXhwcjogQ29uc3RydWN0b3JIYW5kbGVyKTogQ29uc3RydWN0b3JQYXJhbUluZm9bXSB7XG5cdFx0Y29uc3QgcGFyYW1zOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdID0gW107XG5cdFxuXHRcdC8vIEhhbmRsZSBmdW5jdGlvbiBleHByZXNzaW9uIG9yIGFycm93IGZ1bmN0aW9uXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikgfHwgdHMuaXNBcnJvd0Z1bmN0aW9uKGNvbnN0cnVjdG9yRXhwcikgfHxcblx0XHRcdHRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHQvLyBMb29rIGZvciBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIChzZWNvbmQgcGFyYW0gYWZ0ZXIgYHRoaXNgKVxuXHRcdFx0Ly8gUGF0dGVybnM6IGZ1bmN0aW9uKHRoaXM6IFR5cGUsIGRhdGE6IHsgLi4uIH0pIG9yICh0aGlzOiBUeXBlLCBkYXRhOiB7IC4uLiB9KSA9PlxuXHRcdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBjb25zdHJ1Y3RvckV4cHIucGFyYW1ldGVycy5sZW5ndGg7IGkrKykge1xuXHRcdFx0XHRjb25zdCBwYXJhbSA9IGNvbnN0cnVjdG9yRXhwci5wYXJhbWV0ZXJzWyBpIF07XG5cdFx0XHRcdGlmICghcGFyYW0udHlwZSkgY29udGludWU7XG5cdFxuXHRcdFx0XHQvLyBTa2lwIGB0aGlzYCBwYXJhbWV0ZXIgKGZpcnN0IHBhcmFtKVxuXHRcdFx0XHRpZiAoXG5cdFx0XHRcdFx0aSA9PT0gMCAmJlxuXHRcdFx0XHRcdHBhcmFtLm5hbWUua2luZCA9PT0gdHMuU3ludGF4S2luZC5JZGVudGlmaWVyICYmXG5cdFx0XHRcdFx0KHBhcmFtLm5hbWUgYXMgdHMuSWRlbnRpZmllcikudGV4dCA9PT0gJ3RoaXMnXG5cdFx0XHRcdCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFxuXHRcdFx0XHQvLyBHZXQgcGFyYW1ldGVyIG5hbWUgYW5kIGV4cGFuZCBpdHMgdHlwZVxuXHRcdFx0XHRjb25zdCBwYXJhbU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgPyBwYXJhbS5uYW1lLnRleHQgOiAnYXJnJztcblx0XHRcdFx0Y29uc3QgZXhwYW5kZWRUeXBlID0gdGhpcy5yZXNvbHZlQ29uc3RydWN0b3JQYXJhbVR5cGUocGFyYW0udHlwZSkgfHwgdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cdFx0XHRcdFx0XG5cdFx0XHRcdHBhcmFtcy5wdXNoKHtcblx0XHRcdFx0XHRuYW1lICAgICA6IHBhcmFtTmFtZSxcblx0XHRcdFx0XHR0eXBlICAgICA6IGV4cGFuZGVkVHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6ICEhcGFyYW0ucXVlc3Rpb25Ub2tlbiB8fCAhIXBhcmFtLmluaXRpYWxpemVyLFxuXHRcdFx0XHRcdC8vIHJlc3QgbWFya2VyIGZvciB0aGUgZGVmaW5pdGlvbnMuanNvbiBhcmdzIGNvbnRyYWN0XG5cdFx0XHRcdFx0Li4uKHBhcmFtLmRvdERvdERvdFRva2VuID8geyBraW5kIDogJ3Jlc3QnIGFzIGNvbnN0IH0gOiB7fSlcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcblx0XHQvLyBIYW5kbGUgY2xhc3MgZXhwcmVzc2lvbiAtIGNoZWNrIGNvbnN0cnVjdG9yIG1ldGhvZFxuXHRcdGlmICh0cy5pc0NsYXNzRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHRjb25zdCBjbGFzc1BhcmFtcyA9IHRoaXMuZXh0cmFjdENsYXNzQ29uc3RydWN0b3JQYXJhbXMoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdGZvciAoY29uc3QgcGFyYW0gb2YgY2xhc3NQYXJhbXMpIHtcblx0XHRcdFx0cGFyYW1zLnB1c2gocGFyYW0pO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBwYXJhbXM7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBmcmFtZXdvcmsgaW5zdHJ1bWVudGF0aW9uIHBvaW50cy4gUHVyZWx5IHN5bnRhY3RpYzogaGVyaXRhZ2Vcblx0ICogY2xhdXNlcywgZGVjb3JhdG9yIGFwcGxpY2F0aW9uIHNpdGVzLCBwcm92aWRlci10b2tlbiBvYmplY3QgbGl0ZXJhbHNcblx0ICogYW5kIGNvbnN1bWVyLmFwcGx5KCkuZm9yUm91dGVzKCkgd2lyaW5nLiBUaGUgdm9jYWJ1bGFyeSBjb21lcyBmcm9tXG5cdCAqIHBsdWdpbnM7IGlkZW50aWZpZXIgdGV4dCBpcyBtYXRjaGVkIGFzLWlzIOKAlCBubyBpbXBvcnQgcmVzb2x1dGlvbixcblx0ICogdGhlIHR5cGUgY2hlY2tlciBzdGF5cyB1bnVzZWQuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb24gKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKG5vZGUpICYmIG5vZGUubmFtZSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uQ2xhc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0RlY29yYXRvcihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uRGVjb3JhdG9yKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0XHRpZiAodHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uUHJvdmlkZXIobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RJbnN0cnVtZW50YXRpb25NaWRkbGV3YXJlKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgYSBuYW1lZCBjbGFzcyBkZWNsYXJhdGlvbiBmb3IgaW5zdHJ1bWVudGF0aW9uIHNpdGUgcmVzb2x1dGlvblxuXHQgKiBhbmQgZGV0ZWN0IGhlcml0YWdlLWJhc2VkIGtpbmRzIChgaW1wbGVtZW50cyA8cGx1Z2luIGludGVyZmFjZT5gKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0SW5zdHJ1bWVudGF0aW9uQ2xhc3MgKG5vZGU6IHRzLkNsYXNzRGVjbGFyYXRpb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIW5vZGUubmFtZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBjbGFzc05hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5uYW1lLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdC8vIEZpcnN0IGxpbmUgb2YgdGhlIGRlY2xhcmF0aW9uLCBsaWtlIEVEUyBgY29kZWAgc25pcHBldHNcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNwbGl0KCdcXG4nKVsgMCBdLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRsZXQga2luZDogSW5zdHJ1bWVudGF0aW9uS2luZCB8IHVuZGVmaW5lZDtcblx0XHRpZiAobm9kZS5oZXJpdGFnZUNsYXVzZXMpIHtcblx0XHRcdGZvciAoY29uc3QgY2xhdXNlIG9mIG5vZGUuaGVyaXRhZ2VDbGF1c2VzKSB7XG5cdFx0XHRcdGlmIChjbGF1c2UudG9rZW4gIT09IHRzLlN5bnRheEtpbmQuSW1wbGVtZW50c0tleXdvcmQpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRmb3IgKGNvbnN0IHR5cGUgb2YgY2xhdXNlLnR5cGVzKSB7XG5cdFx0XHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIodHlwZS5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdGNvbnN0IG1hdGNoZWQgPSB0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkuaW50ZXJmYWNlc1sgdHlwZS5leHByZXNzaW9uLnRleHQgXTtcblx0XHRcdFx0XHRpZiAobWF0Y2hlZCkge1xuXHRcdFx0XHRcdFx0a2luZCA9IG1hdGNoZWQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGVjbDogSW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNsID0ge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRjb2RlLFxuXHRcdH07XG5cdFx0aWYgKGtpbmQpIHtcblx0XHRcdGRlY2wua2luZCA9IGtpbmQ7XG5cdFx0fVxuXHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNscy5zZXQoY2xhc3NOYW1lLCBkZWNsKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgZGVjb3JhdG9yIGFwcGxpY2F0aW9uIHNpdGVzOiBwbHVnaW4tbGlzdGVkIGRlY29yYXRvcnMgYXBwbGllZFxuXHQgKiB3aXRoIGNsYXNzIGFyZ3VtZW50cyBvbiBhIGNsYXNzIG9yIG9uZSBvZiBpdHMgbWV0aG9kcy4gT25lIHNpdGUgcGVyXG5cdCAqIHJlZmVyZW5jZWQgY2xhc3MgaWRlbnRpZmllci5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEluc3RydW1lbnRhdGlvbkRlY29yYXRvciAobm9kZTogdHMuRGVjb3JhdG9yLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihleHByZXNzaW9uKSB8fCAhdHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24uZXhwcmVzc2lvbikpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3Qga2luZCA9IHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS51c2VEZWNvcmF0b3JzWyBleHByZXNzaW9uLmV4cHJlc3Npb24udGV4dCBdO1xuXHRcdGlmICgha2luZCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFRoZSBkZWNvcmF0b3IncyBwYXJlbnQgaXMgdGhlIGRlY29yYXRlZCBub2RlOiBhIGNvbnRyb2xsZXIgY2xhc3MsXG5cdFx0Ly8gb25lIG9mIGl0cyBtZXRob2RzLCBvciBvbmUgb2YgaXRzIG1ldGhvZCBwYXJhbWV0ZXJzXG5cdFx0Ly8gKEBCb2R5KG12cC5mb3JUeXBlKER0bykpIG9uIGEgaGFuZGxlciBhcmd1bWVudClcblx0XHRjb25zdCBkZWNvcmF0ZWQgPSBub2RlLnBhcmVudDtcblx0XHRsZXQgc2NvcGU6IEluc3RydW1lbnRhdGlvblNjb3BlO1xuXHRcdGxldCB0YXJnZXRzOiBzdHJpbmdbXTtcblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKGRlY29yYXRlZCkgJiYgZGVjb3JhdGVkLm5hbWUpIHtcblx0XHRcdHNjb3BlID0gYGNvbnRyb2xsZXI6JHtkZWNvcmF0ZWQubmFtZS50ZXh0fWA7XG5cdFx0XHR0YXJnZXRzID0gWyBkZWNvcmF0ZWQubmFtZS50ZXh0IF07XG5cdFx0fSBlbHNlIGlmIChcblx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24oZGVjb3JhdGVkKSAmJlxuXHRcdFx0dHMuaXNJZGVudGlmaWVyKGRlY29yYXRlZC5uYW1lKSAmJlxuXHRcdFx0dHMuaXNDbGFzc0RlY2xhcmF0aW9uKGRlY29yYXRlZC5wYXJlbnQpICYmXG5cdFx0XHRkZWNvcmF0ZWQucGFyZW50Lm5hbWVcblx0XHQpIHtcblx0XHRcdGNvbnN0IGNsYXNzTmFtZSA9IGRlY29yYXRlZC5wYXJlbnQubmFtZS50ZXh0O1xuXHRcdFx0c2NvcGUgPSBgbWV0aG9kOiR7Y2xhc3NOYW1lfS4ke2RlY29yYXRlZC5uYW1lLnRleHR9YDtcblx0XHRcdHRhcmdldHMgPSBbIGNsYXNzTmFtZSBdO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNQYXJhbWV0ZXIoZGVjb3JhdGVkKSkge1xuXHRcdFx0Ly8gUGFyYW1ldGVyIGRlY29yYXRvcnMgdGFrZSB0aGUgZW5jbG9zaW5nIG1ldGhvZCdzIHNjb3BlIOKAlCB0aGVcblx0XHRcdC8vIGF0dGFjaG1lbnQgcG9pbnQgaXMgdGhlIGhhbmRsZXIsIG5vdCB0aGUgYXJndW1lbnQgbmFtZTsgdGhlXG5cdFx0XHQvLyBzYW1lIG1ldGhvZDpDbGFzcy5tZXRob2QgZm9ybSBhcyBtZXRob2QtbGV2ZWwgc2l0ZXMuIFBhcmFtcyBvZlxuXHRcdFx0Ly8gY29uc3RydWN0b3JzLCBmdW5jdGlvbnMsIGFuZCB1bm5hbWVhYmxlIGhvc3RzIHN0YXkgc2lsZW50LCB0aGVcblx0XHRcdC8vIHNhbWUgY29udmVudGlvbiBhcyBvdGhlciB1bnJlc29sdmFibGUgZGVjb3JhdG9yIHBhcmVudHNcblx0XHRcdGNvbnN0IGhvc3QgPSBkZWNvcmF0ZWQucGFyZW50O1xuXHRcdFx0aWYgKFxuXHRcdFx0XHRob3N0ICYmXG5cdFx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24oaG9zdCkgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGhvc3QubmFtZSkgJiZcblx0XHRcdFx0dHMuaXNDbGFzc0RlY2xhcmF0aW9uKGhvc3QucGFyZW50KSAmJlxuXHRcdFx0XHRob3N0LnBhcmVudC5uYW1lXG5cdFx0XHQpIHtcblx0XHRcdFx0Y29uc3QgY2xhc3NOYW1lID0gaG9zdC5wYXJlbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRzY29wZSA9IGBtZXRob2Q6JHtjbGFzc05hbWV9LiR7aG9zdC5uYW1lLnRleHR9YDtcblx0XHRcdFx0dGFyZ2V0cyA9IFsgY2xhc3NOYW1lIF07XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRyZXR1cm47XG5cdFx0XHR9XG5cdFx0fSBlbHNlIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRmb3IgKGNvbnN0IGFyZyBvZiBleHByZXNzaW9uLmFyZ3VtZW50cykge1xuXHRcdFx0Ly8gQ2xhc3MgcmVmZXJlbmNlOiBAUmVnaXN0ZXIoSW1wbCkgb3IgYW4gaW5saW5lIGluc3RhbmNlOlxuXHRcdFx0Ly8gQFJlZ2lzdGVyKG5ldyBJbXBsKHsgLi4ub3B0aW9ucyB9KSlcblx0XHRcdGxldCBjbGFzc05hbWU6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRcdC8vIHBlci1hcmcga2luZDogZmFjdG9yeS1jYWxsIGFyZ3MgY2FycnkgdGhlaXIgb3duIGNvbmZpZ3VyZWRcblx0XHRcdC8vIGtpbmQsIGV2ZXJ5dGhpbmcgZWxzZSB0YWtlcyB0aGUgZGVjb3JhdG9yJ3Ncblx0XHRcdGxldCBhcmdLaW5kID0ga2luZDtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0XHRjbGFzc05hbWUgPSBhcmcudGV4dDtcblx0XHRcdH0gZWxzZSBpZiAodHMuaXNOZXdFeHByZXNzaW9uKGFyZykgJiYgdHMuaXNJZGVudGlmaWVyKGFyZy5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjbGFzc05hbWUgPSBhcmcuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0fSBlbHNlIGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGFyZykgJiYgdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXJnLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdC8vIFBpcGUtZmFjdG9yeSBzaGFwZTogQFVzZVBpcGVzKG12cC5mb3JUeXBlKER0bykpIOKAlCB0aGVcblx0XHRcdFx0Ly8gY2FsbCdzIG1ldGhvZCBuYW1lIGlzIHBsdWdpbi1saXN0ZWQsIHRoZSB0YXJnZXQgY2xhc3Mgc2l0c1xuXHRcdFx0XHQvLyBpbiB0aGUgY29uZmlndXJlZCBhcmd1bWVudCBwb3NpdGlvbiAoZGVmYXVsdCAwKVxuXHRcdFx0XHRjb25zdCBmYWN0b3J5ID0gdGhpcy5pbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5LmRlY29yYXRvckFyZ0ZhY3Rvcmllc1sgYXJnLmV4cHJlc3Npb24ubmFtZS50ZXh0IF07XG5cdFx0XHRcdGlmIChmYWN0b3J5KSB7XG5cdFx0XHRcdFx0Y29uc3QgdGFyZ2V0QXJnID0gYXJnLmFyZ3VtZW50c1sgZmFjdG9yeS50YXJnZXRBcmcgPz8gMCBdO1xuXHRcdFx0XHRcdGlmICh0YXJnZXRBcmcgJiYgdHMuaXNJZGVudGlmaWVyKHRhcmdldEFyZykpIHtcblx0XHRcdFx0XHRcdGNsYXNzTmFtZSA9IHRhcmdldEFyZy50ZXh0O1xuXHRcdFx0XHRcdFx0YXJnS2luZCA9IGZhY3Rvcnkua2luZDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Ly8gVGhlIHBsdWdpbiBkZWNsYXJlcyB0aGF0IHRoaXMgZmFjdG9yeSBjb25zdHJ1Y3RzIGl0c1xuXHRcdFx0XHRcdC8vIHRhcmdldCBvbiB0aGUgY2FsbGVyJ3MgYmVoYWxmOiB0aGUgY2FsbCBzaXRlIGlzIGFcblx0XHRcdFx0XHQvLyBjb25zdHJ1Y3Rpb24gbGlrZSBgbmV3YCwgcmVjb3JkZWQgYXMgYW4gaW5zdGFudGlhdGlvblxuXHRcdFx0XHRcdGlmICh0YXJnZXRBcmcgJiYgZmFjdG9yeS5pbnN0YW50aWF0aW9uKSB7XG5cdFx0XHRcdFx0XHR0aGlzLnJlY29yZEZhY3RvcnlDb25zdHJ1Y3Rpb24oYXJnLCB0YXJnZXRBcmcsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKCFjbGFzc05hbWUpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHR0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzLnB1c2goe1xuXHRcdFx0XHRraW5kIDogYXJnS2luZCxcblx0XHRcdFx0Y2xhc3NOYW1lLFxuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0c2NvcGUsXG5cdFx0XHRcdHRhcmdldHMsXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQSBwbHVnaW4tbGlzdGVkIGRlY29yYXRvci1hcmcgZmFjdG9yeSB3aXRoIGBpbnN0YW50aWF0aW9uOiB0cnVlYFxuXHQgKiAoYEBCb2R5KG12cC5mb3JUeXBlKEVudGl0eSwgRHRvKSlgKSBjb25zdHJ1Y3RzIHRoZSB0eXBlIGF0IGl0c1xuXHQgKiB0YXJnZXQgYXJndW1lbnQgbGF0ZXIsIGF0IHJ1bnRpbWU6IHJlY29yZCB0aGUgZmFjdG9yeSBjYWxsIGFzIHRoYXRcblx0ICogdHlwZSdzIGBpbnN0YW50aWF0aW9uYCB1c2FnZSBhbmQgZmxvdywgdGhlIHNhbWUgYXMgY2FsbC9hcHBseS4gQVxuXHQgKiB0YXJnZXQgdGhhdCByZXNvbHZlcyB0byBubyBkZWZpbmVkIHR5cGUgcmVjb3JkcyBub3RoaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmRGYWN0b3J5Q29uc3RydWN0aW9uIChcblx0XHRjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHR0YXJnZXRBcmc6IHRzLkV4cHJlc3Npb24sXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZVxuXHQpOiB2b2lkIHtcblx0XHRjb25zdCBjb25zdHJ1Y3RlZFBhdGggPSB0aGlzLnJlc29sdmVDdG9yQXJnVHlwZVBhdGgodGFyZ2V0QXJnKTtcblx0XHRpZiAoIWNvbnN0cnVjdGVkUGF0aCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR0aGlzLnJlY29yZENvbnN0cnVjdGlvblVzYWdlKGNhbGwsIGNvbnN0cnVjdGVkUGF0aCwgc291cmNlRmlsZSwgdGFyZ2V0QXJnLmdldFRleHQoc291cmNlRmlsZSkpO1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRjYWxsLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHR0aGlzLmFkZEZsb3coY29uc3RydWN0ZWRQYXRoLCB7XG5cdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRjb2RlICAgICA6IGNhbGwuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0Y29udGV4dCAgOiAncGx1Z2luIGZhY3RvcnkgY29uc3RydWN0aW9uJyxcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgZ2xvYmFsIHJlZ2lzdHJhdGlvbnM6IG9iamVjdCBsaXRlcmFscyBzaGFwZWQgbGlrZVxuXHQgKiBgeyBwcm92aWRlOiA8cGx1Z2luLWxpc3RlZCB0b2tlbj4sIHVzZUNsYXNzOiBYIH1gLlxuXHQgKiB1c2VFeGlzdGluZy91c2VGYWN0b3J5IHdpdGhvdXQgYSB1c2VDbGFzcyBpZGVudGlmaWVyIGFyZSBub3Rcblx0ICogc3RhdGljYWxseSBvYnZpb3VzIOKAlCBza2lwcGVkIHJhdGhlciB0aGFuIGd1ZXNzZWQuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25Qcm92aWRlciAobm9kZTogdHMuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRsZXQga2luZDogSW5zdHJ1bWVudGF0aW9uS2luZCB8IHVuZGVmaW5lZDtcblx0XHRsZXQgdXNlQ2xhc3NOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cblx0XHRmb3IgKGNvbnN0IHByb3Agb2Ygbm9kZS5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdCF0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSB8fFxuXHRcdFx0XHQhdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkgfHxcblx0XHRcdFx0IXRzLmlzSWRlbnRpZmllcihwcm9wLmluaXRpYWxpemVyKVxuXHRcdFx0KSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHByb3AubmFtZS50ZXh0ID09PSAncHJvdmlkZScpIHtcblx0XHRcdFx0a2luZCA9IHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS5hcHBUb2tlbnNbIHByb3AuaW5pdGlhbGl6ZXIudGV4dCBdO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHByb3AubmFtZS50ZXh0ID09PSAndXNlQ2xhc3MnKSB7XG5cdFx0XHRcdHVzZUNsYXNzTmFtZSA9IHByb3AuaW5pdGlhbGl6ZXIudGV4dDtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRpZiAoIWtpbmQgfHwgIXVzZUNsYXNzTmFtZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uU2l0ZXMucHVzaCh7XG5cdFx0XHRraW5kLFxuXHRcdFx0Y2xhc3NOYW1lIDogdXNlQ2xhc3NOYW1lLFxuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRjb2RlLFxuXHRcdFx0c2NvcGUgICAgIDogJ2dsb2JhbCcsXG5cdFx0XHR0YXJnZXRzICAgOiBbXSxcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgbWlkZGxld2FyZSB3aXJpbmc6IGBjb25zdW1lci5hcHBseShNdzEsIE13MikuZm9yUm91dGVzKC4uLilgXG5cdCAqIGluc2lkZSBhIGNsYXNzJ3MgY29uZmlndXJlKCkgbWV0aG9kLiBUYXJnZXRzIGNvbWUgZnJvbSBmb3JSb3V0ZXNcblx0ICogYXJndW1lbnRzIHdoZW4gc3RhdGljYWxseSByZWFkYWJsZSAoc3RyaW5nIHJvdXRlcyBvciBjb250cm9sbGVyXG5cdCAqIGlkZW50aWZpZXJzKSwgZWxzZSBbXS4gU2hhcGUtYmFzZWQsIHNvIGEgcGx1Z2luIG11c3Qgb3B0IGluIHZpYVxuXHQgKiBgbWlkZGxld2FyZVdpcmluZzogdHJ1ZWAuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25NaWRkbGV3YXJlIChub2RlOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdGhpcy5pbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5Lm1pZGRsZXdhcmVXaXJpbmcpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKFxuXHRcdFx0IXRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbikgfHxcblx0XHRcdG5vZGUuZXhwcmVzc2lvbi5uYW1lLnRleHQgIT09ICdmb3JSb3V0ZXMnXG5cdFx0KSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGFwcGx5Q2FsbCA9IG5vZGUuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdGlmIChcblx0XHRcdCF0cy5pc0NhbGxFeHByZXNzaW9uKGFwcGx5Q2FsbCkgfHxcblx0XHRcdCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcHBseUNhbGwuZXhwcmVzc2lvbikgfHxcblx0XHRcdGFwcGx5Q2FsbC5leHByZXNzaW9uLm5hbWUudGV4dCAhPT0gJ2FwcGx5J1xuXHRcdCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAoIXRoaXMuaXNJbnNpZGVDb25maWd1cmVNZXRob2Qobm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB0YXJnZXRzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgYXJnIG9mIG5vZGUuYXJndW1lbnRzKSB7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykgfHwgdHMuaXNTdHJpbmdMaXRlcmFsKGFyZykpIHtcblx0XHRcdFx0dGFyZ2V0cy5wdXNoKGFyZy50ZXh0KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0YXBwbHlDYWxsLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdGZvciAoY29uc3QgYXJnIG9mIGFwcGx5Q2FsbC5hcmd1bWVudHMpIHtcblx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHR0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzLnB1c2goe1xuXHRcdFx0XHRraW5kICAgICAgOiAnbWlkZGxld2FyZScsXG5cdFx0XHRcdGNsYXNzTmFtZSA6IGFyZy50ZXh0LFxuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0c2NvcGUgICAgIDogJ21vZHVsZScsXG5cdFx0XHRcdHRhcmdldHMsXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogV2FsayB1cCB0aGUgcGFyZW50IGNoYWluIGxvb2tpbmcgZm9yIGFuIGVuY2xvc2luZyBjb25maWd1cmUoKSBtZXRob2Rcblx0ICovXG5cdHByaXZhdGUgaXNJbnNpZGVDb25maWd1cmVNZXRob2QgKG5vZGU6IHRzLk5vZGUpOiBib29sZWFuIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5vZGUucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24oY3VycmVudCkgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGN1cnJlbnQubmFtZSkgJiZcblx0XHRcdFx0Y3VycmVudC5uYW1lLnRleHQgPT09ICdjb25maWd1cmUnXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxufVxuIl19