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
    /**
     * Track imports from 'mnemonica' so aliases of the module object and
     * createTypesCollection are recognized without relying on the type checker.
     */
    trackImports(node) {
        if (!ts.isImportDeclaration(node)) {
            return;
        }
        const { moduleSpecifier } = node;
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
        // Get the type name and source context from arguments
        const defineContext = this.extractDefineContext(call);
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
        // Track variable assignment: const User = define('UserEntity', ...) -> map "User" to "UserEntity"
        // A multi-hop initializer binds the LAST hop: define() returns the
        // defined type's constructor (F18)
        this.trackVariableAssignment(call, parentNode, node.fullPath);
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
        this.trackVariableAssignment(call, parentNode, node.fullPath);
    }
    /**
     * Extract lazy() call arguments into a normalized shape.
     * Handles named/unnamed and explicit-source forms, both as free calls
     * and as method calls.
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
        * Track variable assignments that capture define() results
        * e.g., const User = define('UserEntity', ...) maps "User" -> "UserEntity"
        * For chained calls like const X = define('A').define('B'), we map X -> A (the root type)
        */
    trackVariableAssignment(call, parentNode, fullPath) {
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
     * Extract the full define() call context: type name, parent type, and collection.
     * Handles direct calls, property-access calls, chained calls, and the
     * explicit-source form `define(source, 'TypeName', handler)`.
     */
    extractDefineContext(call) {
        const typeName = this.extractTypeName(call);
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
    /**
     * Determine the constructor expression for either a define() or lazy() call.
     * For define() this is the construct handler; for lazy() it is the value
     * returned by the lazy getter.
     */
    extractConstructorExpression(call) {
        const expr = call.expression;
        const name = ts.isIdentifier(expr)
            ? expr.text
            : ts.isPropertyAccessExpression(expr)
                ? expr.name.text
                : '';
        if (name === 'lazy') {
            const lazyArgs = this.extractLazyCallArgs(call);
            if (!lazyArgs) {
                return undefined;
            }
            return this.unwrapLazyGetter(lazyArgs.getter);
        }
        // define() call
        const args = call.arguments;
        if (args.length === 0) {
            return undefined;
        }
        // Modern form: define('Name', handler, config?)
        if (ts.isStringLiteral(args[0])) {
            return args[1];
        }
        // Legacy form: define(function Name() {}) or define(() => class Name {})
        return args[0];
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
            ts.isArrowFunction(constructorExpr);
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
        const result = this.extractPropertiesFromConstructor(constructorExpr);
        return result;
    }
    /**
     * Extract properties from a constructor expression (function, arrow, or class).
     */
    extractPropertiesFromConstructor(constructorExpr) {
        const properties = new Map();
        // Build type map from data parameter (for this.x = data.x patterns)
        const dataTypeMap = this.buildDataTypeMap(constructorExpr);
        // Handle function expression
        if (ts.isFunctionExpression(constructorExpr) || ts.isArrowFunction(constructorExpr)) {
            const { body } = constructorExpr;
            // First, extract properties from `this` parameter type annotation
            // This handles patterns like: function(this: SomeType, data: SomeType) { }
            const thisParamProperties = this.extractThisParamProperties(constructorExpr);
            for (const [name, propInfo] of thisParamProperties) {
                properties.set(name, propInfo);
            }
            // Function body with statements
            if (ts.isBlock(body)) {
                for (const stmt of body.statements) {
                    if (ts.isExpressionStatement(stmt)) {
                        this.extractPropertyFromStatement(stmt.expression, properties, dataTypeMap);
                    }
                }
            }
        }
        // Handle class expression
        if (ts.isClassExpression(constructorExpr)) {
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
                        properties.set(name, {
                            name,
                            type: this.inferType(member.type),
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
        if (!ts.isFunctionExpression(handlerArg) && !ts.isArrowFunction(handlerArg)) {
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
            return [];
        }
        const result = this.extractConstructorParamsFromConstructor(constructorExpr);
        return result;
    }
    /**
             * Extract constructor parameters from a constructor expression.
             */
    extractConstructorParamsFromConstructor(constructorExpr) {
        const params = [];
        // Handle function expression or arrow function
        if (ts.isFunctionExpression(constructorExpr) || ts.isArrowFunction(constructorExpr)) {
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
        if (ts.isClassExpression(constructorExpr)) {
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYW5hbHl6ZXIuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvYW5hbHl6ZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFFYiwrQ0FBaUM7QUFDakMsK0NBQWlDO0FBT2pDLG1DQUVpQjtBQUNqQix1Q0FFbUI7QUFrRW5COzs7R0FHRztBQUNILE1BQU0sa0JBQWtCLEdBQUcsSUFBSSxHQUFHLENBQUM7SUFDbEMsTUFBTSxFQUFFLFFBQVEsRUFBRSxPQUFPLEVBQUUsV0FBVyxFQUFFLFlBQVksRUFBRSxnQkFBZ0I7SUFDdEUsYUFBYSxFQUFFLFdBQVcsRUFBRSxVQUFVLEVBQUUsZ0JBQWdCO0lBQ3hELEtBQUssRUFBRSxLQUFLLEVBQUUsU0FBUyxFQUFFLFNBQVMsRUFBRSxTQUFTLEVBQUUsc0JBQXNCO0lBQ3JFLFNBQVMsRUFBRSxPQUFPLEVBQUUsZUFBZSxFQUFFLFFBQVEsRUFBRSxTQUFTLEVBQUUsVUFBVTtJQUNwRSxVQUFVLEVBQUUsTUFBTSxFQUFFLE1BQU0sRUFBRSxTQUFTLEVBQUUsU0FBUyxFQUFFLGFBQWE7SUFDL0QsWUFBWSxFQUFFLGNBQWMsRUFBRSxZQUFZLEVBQUUsdUJBQXVCO0lBQ25FLFVBQVUsRUFBRSxtQkFBbUIsRUFBRSxtQkFBbUI7SUFDcEQsV0FBVyxFQUFFLFdBQVcsRUFBRSxZQUFZLEVBQUUsY0FBYztJQUN0RCxRQUFRLEVBQUUsUUFBUSxFQUFFLFNBQVMsRUFBRSxRQUFRLEVBQUUsUUFBUSxFQUFFLFFBQVEsRUFBRSxVQUFVO0lBQ3ZFLFVBQVUsRUFBRSxVQUFVLEVBQUUsV0FBVyxFQUFFLGVBQWUsRUFBRSxlQUFlO0lBQ3JFLGdCQUFnQixFQUFFLGtCQUFrQixFQUFFLHVCQUF1QjtJQUM3RCxhQUFhLEVBQUUsYUFBYSxFQUFFLG1CQUFtQixFQUFFLFVBQVU7SUFDN0QsV0FBVyxFQUFFLFlBQVksRUFBRSxtQkFB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LFFBQVE7Z0JBQ3BCLE9BQU87YUFDUCxDQUFDLENBQUM7UUFDSixDQUFDO0lBQ0YsQ0FBQztJQUVEOztPQUVHO0lBQ0ssdUJBQXVCLENBQUUsSUFBYTtRQUM3QyxJQUFJLE9BQU8sR0FBd0IsSUFBSSxDQUFDLE1BQU0sQ0FBQztRQUMvQyxPQUFPLE9BQU8sRUFBRSxDQUFDO1lBQ2hCLElBQ0MsRUFBRSxDQUFDLG1CQUFtQixDQUFDLE9BQU8sQ0FBQztnQkFDL0IsRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDO2dCQUM3QixPQUFPLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxXQUFXLEVBQ2hDLENBQUM7Z0JBQ0YsT0FBTyxJQUFJLENBQUM7WUFDYixDQUFDO1lBQ0QsT0FBTyxHQUFHLE9BQU8sQ0FBQyxNQUFNLENBQUM7UUFDMUIsQ0FBQztRQUNELE9BQU8sS0FBSyxDQUFDO0lBQ2QsQ0FBQztDQUNEO0FBaHVNRCw4Q0FndU1DIiwic291cmNlc0NvbnRlbnQiOlsiJ3VzZSBzdHJpY3QnO1xuXG5pbXBvcnQgKiBhcyBub2RlUGF0aCBmcm9tICdwYXRoJztcbmltcG9ydCAqIGFzIHRzIGZyb20gJ3R5cGVzY3JpcHQnO1xuaW1wb3J0IHtcblx0VHlwZU5vZGUsIFByb3BlcnR5SW5mbywgQW5hbHl6ZVJlc3VsdCwgQW5hbHl6ZUVycm9yLFxuXHREZWZpbml0aW9uSW5mbywgVXNhZ2VJbmZvLCBDb25zdHJ1Y3RvclBhcmFtSW5mbyxcblx0RURTSW5mbywgRmxvd0luZm8sIEluc3RydW1lbnRhdGlvbktpbmQsIEluc3RydW1lbnRhdGlvblBvaW50LFxuXHRJbnN0cnVtZW50YXRpb25TY29wZSwgUmVzb2x1dGlvbkVycm9yLCBDb2xsZWN0aW9uTWFuaWZlc3RFbnRyeVxufSBmcm9tICcuL3R5cGVzJztcbmltcG9ydCB7XG5cdFR5cGVHcmFwaEltcGwsIHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UsIEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCBcbn0gZnJvbSAnLi9ncmFwaCc7XG5pbXBvcnQge1xuXHRJbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5LCBUYWN0aWNhUGx1Z2luLCBtZXJnZVRhY3RpY2FQbHVnaW5zXG59IGZyb20gJy4vcGx1Z2lucyc7XG5cbmludGVyZmFjZSBDb2xsZWN0aW9uSW5mbyB7XG5cdHZhcmlhYmxlTmFtZTogc3RyaW5nO1xuXHRzb3VyY2VGaWxlOiBzdHJpbmc7XG5cdHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZT86IHN0cmluZztcblx0LyoqIDEtYmFzZWQgcG9zaXRpb24gb2YgdGhlIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIHZhcmlhYmxlIGRlY2xhcmF0aW9uICovXG5cdGxpbmU6IG51bWJlcjtcblx0Y29sdW1uOiBudW1iZXI7XG59XG5cbi8qKlxuICogTG9jYXRpb24vY29kZSBjYXB0dXJlZCBhdCBhIGNsYXNzIGRlY2xhcmF0aW9uLCB1c2VkIHRvIHJlc29sdmVcbiAqIGluc3RydW1lbnRhdGlvbiByZWdpc3RyYXRpb24gc2l0ZXMgdG8gdGhlIGRlY2xhcmVkIGNsYXNzXG4gKi9cbmludGVyZmFjZSBJbnN0cnVtZW50YXRpb25DbGFzc0RlY2wge1xuXHRraW5kPzogSW5zdHJ1bWVudGF0aW9uS2luZDtcblx0bG9jYXRpb246IHN0cmluZztcblx0Y29kZTogc3RyaW5nO1xufVxuXG4vKipcbiAqIFJhdyByZWdpc3RyYXRpb24gc2l0ZSAoZGVjb3JhdG9yLCBBUFBfKiBwcm92aWRlciwgY29uc3VtZXIuYXBwbHkpLlxuICogTG9jYXRpb24vY29kZSBhcmUgdGhlIHNpdGUncyBvd247IGdldEluc3RydW1lbnRhdGlvblBvaW50cygpIHJld3JpdGVzXG4gKiB0aGVtIHRvIHRoZSBjbGFzcyBkZWNsYXJhdGlvbiB3aGVuIHRoZSBjbGFzcyBpcyBkZWNsYXJlZCBpbi1wcm9qZWN0LlxuICovXG5pbnRlcmZhY2UgSW5zdHJ1bWVudGF0aW9uU2l0ZSB7XG5cdGtpbmQ6IEluc3RydW1lbnRhdGlvbktpbmQ7XG5cdGNsYXNzTmFtZTogc3RyaW5nO1xuXHRsb2NhdGlvbjogc3RyaW5nO1xuXHRjb2RlOiBzdHJpbmc7XG5cdHNjb3BlOiBJbnN0cnVtZW50YXRpb25TY29wZTtcblx0dGFyZ2V0czogc3RyaW5nW107XG59XG5cbi8qKlxuICogQSBuYW1lZCByZWZlcmVuY2VkLXR5cGUgZGVjbGFyYXRpb24gKHR5cGUgYWxpYXMsIGNsYXNzLCBvciBpbnRlcmZhY2UpXG4gKiByZWNvcmRlZCBwZXIgZmlsZSwgc28gcmVmZXJlbmNlcyBjYW4gYmUgcmVzb2x2ZWQgdGhyb3VnaCB0aGUgaW1wb3J0aW5nXG4gKiBmaWxlJ3Mgb3duIGltcG9ydHMgaW5zdGVhZCBvZiBhIHByb2dyYW0td2lkZSBsYXN0LXdpbnMgbmFtZSBtYXAgKEYxMCkuXG4gKi9cbmludGVyZmFjZSBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHtcblx0a2luZDogJ2FsaWFzJyB8ICdjbGFzcycgfCAnaW50ZXJmYWNlJztcblx0bm9kZTogdHMuVHlwZUFsaWFzRGVjbGFyYXRpb24gfCB0cy5DbGFzc0RlY2xhcmF0aW9uIHwgdHMuSW50ZXJmYWNlRGVjbGFyYXRpb247XG5cdC8qKiBmaWxlIHRoYXQgZGVjbGFyZXMgdGhlIHR5cGUg4oCUIG5lc3RlZCByZWZlcmVuY2VzIHJlc29sdmUgYWdhaW5zdCBpdCAqL1xuXHRmaWxlOiBzdHJpbmc7XG59XG5cbi8qKlxuICogT25lIGltcG9ydCBiaW5kaW5nIG9mIGEgcmVmZXJlbmNlZCB0eXBlOiB0aGUgbG9jYWwgbmFtZSB1bmRlciB3aGljaCB0aGVcbiAqIGZpbGUga25vd3MgaXQsIHRoZSBvcmlnaW5hbCBleHBvcnRlZCBuYW1lIGluIHRoZSBzb3VyY2UgbW9kdWxlLCBhbmQgdGhlXG4gKiBzcGVjaWZpZXIgaXQgY2FtZSBmcm9tLlxuICovXG5pbnRlcmZhY2UgUmVmZXJlbmNlZFR5cGVJbXBvcnQge1xuXHRvcmlnaW5hbE5hbWU6IHN0cmluZztcblx0c3BlY2lmaWVyOiBzdHJpbmc7XG5cdGlzTmFtZXNwYWNlOiBib29sZWFuO1xufVxuXG4vKipcbiAqIFJlc3VsdCBvZiByZXNvbHZpbmcgb25lIG1vZHVsZSBzcGVjaWZpZXIgZnJvbSBvbmUgY29udGFpbmluZyBmaWxlLlxuICovXG5pbnRlcmZhY2UgUmVmZXJlbmNlZFR5cGVSZXNvbHV0aW9uIHtcblx0cmVzb2x2ZWRQYXRoOiBzdHJpbmc7XG5cdGlzRXh0ZXJuYWw6IGJvb2xlYW47XG59XG5cbi8qKlxuICogR2xvYmFsL2J1aWx0aW4gdHlwZSBuYW1lcyB0aGF0IGFyZSBzYWZlIHRvIGVtaXQgYmFyZSBpbnRvIGdlbmVyYXRlZCBmaWxlc1xuICog4oCUIHRoZXkgcmVzb2x2ZSBpbiBhbnkgVHlwZVNjcmlwdCBjb21waWxhdGlvbiB3aXRob3V0IGFuIGltcG9ydC5cbiAqL1xuY29uc3QgS05PV05fR0xPQkFMX1RZUEVTID0gbmV3IFNldChbXG5cdCdEYXRlJywgJ1JlZ0V4cCcsICdFcnJvcicsICdFdmFsRXJyb3InLCAnUmFuZ2VFcnJvcicsICdSZWZlcmVuY2VFcnJvcicsXG5cdCdTeW50YXhFcnJvcicsICdUeXBlRXJyb3InLCAnVVJJRXJyb3InLCAnQWdncmVnYXRlRXJyb3InLFxuXHQnTWFwJywgJ1NldCcsICdXZWFrTWFwJywgJ1dlYWtTZXQnLCAnV2Vha1JlZicsICdGaW5hbGl6YXRpb25SZWdpc3RyeScsXG5cdCdQcm9taXNlJywgJ0FycmF5JywgJ1JlYWRvbmx5QXJyYXknLCAnUmVjb3JkJywgJ1BhcnRpYWwnLCAnUmVxdWlyZWQnLFxuXHQnUmVhZG9ubHknLCAnUGljaycsICdPbWl0JywgJ0V4Y2x1ZGUnLCAnRXh0cmFjdCcsICdOb25OdWxsYWJsZScsXG5cdCdSZXR1cm5UeXBlJywgJ0luc3RhbmNlVHlwZScsICdQYXJhbWV0ZXJzJywgJ0NvbnN0cnVjdG9yUGFyYW1ldGVycycsXG5cdCdUaGlzVHlwZScsICdUaGlzUGFyYW1ldGVyVHlwZScsICdPbWl0VGhpc1BhcmFtZXRlcicsXG5cdCdVcHBlcmNhc2UnLCAnTG93ZXJjYXNlJywgJ0NhcGl0YWxpemUnLCAnVW5jYXBpdGFsaXplJyxcblx0J1N0cmluZycsICdOdW1iZXInLCAnQm9vbGVhbicsICdTeW1ib2wnLCAnQmlnSW50JywgJ09iamVjdCcsICdGdW5jdGlvbicsXG5cdCdJdGVyYWJsZScsICdJdGVyYXRvcicsICdHZW5lcmF0b3InLCAnQXN5bmNJdGVyYWJsZScsICdBc3luY0l0ZXJhdG9yJyxcblx0J0FzeW5jR2VuZXJhdG9yJywgJ0l0ZXJhYmxlSXRlcmF0b3InLCAnQXN5bmNJdGVyYWJsZUl0ZXJhdG9yJyxcblx0J1Byb3BlcnR5S2V5JywgJ0FycmF5QnVmZmVyJywgJ1NoYXJlZEFycmF5QnVmZmVyJywgJ0RhdGFWaWV3Jyxcblx0J0ludDhBcnJheScsICdVaW50OEFycmF5JywgJ1VpbnQ4Q2xhbXBlZEFycmF5JywgJ0ludDE2QXJyYXknLFxuXHQnVWludDE2QXJyYXknLCAnSW50MzJBcnJheScsICdVaW50MzJBcnJheScsICdGbG9hdDMyQXJyYXknLFxuXHQnRmxvYXQ2NEFycmF5JywgJ0JpZ0ludDY0QXJyYXknLCAnQmlnVWludDY0QXJyYXknLCAnSW50bCdcbl0pO1xuXG4vLyBHZW5lcmljIGdsb2JhbHMgd2hvc2UgYmFyZSBlbWlzc2lvbiB3b3VsZCBiZSBpbnZhbGlkIFRTIChUUzIzMTQpOlxuLy8gYG5ldyBNYXAoKWAgY2FycmllcyBubyB0eXBlIGFyZ3VtZW50cywgc28gdGhlIGZpZWxkIHR5cGUgZmlsbHMgdGhlbVxuLy8gd2l0aCB1bmtub3duLiBLZXlzIG11c3QgYWxzbyBiZSBtZW1iZXJzIG9mIEtOT1dOX0dMT0JBTF9UWVBFUy5cbmNvbnN0IEdFTkVSSUNfR0xPQkFMX0RFRkFVTFRfQVJHUyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KFtcblx0WyAnTWFwJywgJ01hcDx1bmtub3duLCB1bmtub3duPicgXSxcblx0WyAnV2Vha01hcCcsICdXZWFrTWFwPG9iamVjdCwgdW5rbm93bj4nIF0sXG5cdFsgJ1NldCcsICdTZXQ8dW5rbm93bj4nIF0sXG5cdFsgJ1dlYWtTZXQnLCAnV2Vha1NldDxvYmplY3Q+JyBdLFxuXHRbICdXZWFrUmVmJywgJ1dlYWtSZWY8b2JqZWN0PicgXSxcblx0WyAnRmluYWxpemF0aW9uUmVnaXN0cnknLCAnRmluYWxpemF0aW9uUmVnaXN0cnk8dW5rbm93bj4nIF0sXG5cdFsgJ1Byb21pc2UnLCAnUHJvbWlzZTx1bmtub3duPicgXSxcblx0WyAnQXJyYXknLCAnQXJyYXk8dW5rbm93bj4nIF0sXG5cdFsgJ1JlYWRvbmx5QXJyYXknLCAnUmVhZG9ubHlBcnJheTx1bmtub3duPicgXVxuXSk7XG5cbi8vIEJvdW5kIGZvciBjaGFzaW5nIHJlLWV4cG9ydCBiYXJyZWxzIChleHBvcnQgeyBYIH0gZnJvbSAn4oCmJywgZXhwb3J0ICogZnJvbSAn4oCmJylcbmNvbnN0IE1BWF9SRUVYUE9SVF9DSEFTRV9ERVBUSCA9IDU7XG4vLyBCb3VuZCBmb3Igd2Fsa2luZyBjbGFzcy9pbnRlcmZhY2UgZXh0ZW5kcyBjaGFpbnMgZHVyaW5nIHJlZmVyZW5jZWQtdHlwZVxuLy8gZXhwYW5zaW9uIChpbmhlcml0ZWQgbWVtYmVycyBtZXJnZSBpbnRvIHRoZSBleHBhbmRlZCBmaWVsZHMpXG5jb25zdCBNQVhfSEVSSVRBR0VfREVQVEggPSA4O1xuXG4vKipcbiAqIEFTVCBBbmFseXplciBmb3IgZmluZGluZyBNbmVtb25pY2EgZGVmaW5lKCkgYW5kIGRlY29yYXRlKCkgY2FsbHNcbiAqXG4gKiBGcmFtZXdvcmstYmxpbmQgYnkgY29uc3RydWN0aW9uOiBpbnN0cnVtZW50YXRpb24gZGV0ZWN0aW9uIHZvY2FidWxhcnlcbiAqIChpbnRlcmZhY2UgbmFtZXMsIGRlY29yYXRvciBuYW1lcywgcHJvdmlkZXIgdG9rZW5zLCBtaWRkbGV3YXJlIHdpcmluZylcbiAqIGNvbWVzIGVudGlyZWx5IGZyb20gcGx1Z2lucyDigJQgd2l0aCBub25lIGxvYWRlZCwgemVybyBwb2ludHMgYXJlIGNvbGxlY3RlZC5cbiAqL1xuZXhwb3J0IGNsYXNzIE1uZW1vbmljYUFuYWx5emVyIHtcblx0cHJpdmF0ZSBlcnJvcnM6IEFuYWx5emVFcnJvcltdID0gW107XG5cdHByaXZhdGUgZ3JhcGggPSBuZXcgVHlwZUdyYXBoSW1wbCgpO1xuXHRwcml2YXRlIGRlZmluaXRpb25zID0gbmV3IE1hcDxzdHJpbmcsIERlZmluaXRpb25JbmZvPigpO1xuXHRwcml2YXRlIHVzYWdlcyA9IG5ldyBNYXA8c3RyaW5nLCBVc2FnZUluZm9bXT4oKTtcblx0cHJpdmF0ZSBlZHNVc2FnZXMgPSBuZXcgTWFwPHN0cmluZywgRURTSW5mb1tdPigpO1xuXHRwcml2YXRlIGZsb3dVc2FnZXMgPSBuZXcgTWFwPHN0cmluZywgRmxvd0luZm9bXT4oKTtcblx0Ly8gRW5jbG9zaW5nIG1uZW1vbmljYSBzY29wZSBmb3IgRURTIGtleWluZzogZGVmaW5lKCkvbGF6eSgpIGNhbGwgbm9kZVxuXHQvLyBvciBAZGVjb3JhdGUoKS1lZCBjbGFzcyBkZWNsYXJhdGlvbiAtPiBmdWxsUGF0aCBvZiB0aGUgdHlwZSBpdCBvd25zLlxuXHQvLyBQb3B1bGF0ZWQgb24gdGhlIGRlZmluaXRpb25zIHBhc3M7IEFTVCBub2RlcyBwZXJzaXN0IGFjcm9zcyBwYXNzZXMsXG5cdC8vIHNvIGVudHJpZXMgc3RheSB2YWxpZCBhZnRlciByZXNldFVzYWdlcygpLlxuXHRwcml2YXRlIGVkc1Njb3BlQnlOb2RlID0gbmV3IE1hcDx0cy5Ob2RlLCBzdHJpbmc+KCk7XG5cdC8vIFNhbWUtZmlsZSBmdW5jdGlvbiBiaW5kaW5ncyAoYGZpbGVOYW1lI25hbWVgIC0+IGZ1bmN0aW9uIG5vZGUpIGZvclxuXHQvLyByZXNvbHZpbmcgd3JhcChmbikgYXJndW1lbnRzIHN5bnRhY3RpY2FsbHkg4oCUIHRoZSBjaGVja2VyIHN0YXlzIHVudXNlZFxuXHRwcml2YXRlIGZ1bmN0aW9uQmluZGluZ3MgPSBuZXcgTWFwPHN0cmluZywgdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb24+KCk7XG5cdC8vIHdyYXAgY2FsbCBub2RlIC0+IGxvY2F0aW9uIG9mIHRoZSBlbmNsb3Npbmcgd3JhcCBzaXRlIChwbHVzIHRoYXRcblx0Ly8gc2l0ZSdzIHNjb3BlIGF0dHJpYnV0aW9uKSwgc28gbmVzdGVkIHdyYXAoKSBjYWxscyBpbnNpZGUgYSB3cmFwcGVkXG5cdC8vIGJvZHkgY2FycnkgdGhlIGB2aWFgIGxpbmsg4oCUIGFuZCBpbmhlcml0IHRoZSBzY29wZSB3aGVuIHRoZXkgaGF2ZVxuXHQvLyBub25lIG9mIHRoZWlyIG93blxuXHRwcml2YXRlIG5lc3RlZFdyYXBWaWEgPSBuZXcgTWFwPHRzLk5vZGUsIHsgdmlhOiBzdHJpbmc7IHNjb3BlPzogc3RyaW5nIH0+KCk7XG5cdC8vIHdyYXAgY2FsbCBub2RlIC0+IGl0cyBjb2xsZWN0ZWQgZW50cnksIHNvIGEgbGV4aWNhbGx5IG5lc3RlZCB3cmFwXG5cdC8vICh2aXNpdGVkIEJFRk9SRSB0aGUgb3V0ZXIgd3JhcCBjYWxsLCBwZXIgc291cmNlIG9yZGVyKSBnZXRzIGl0c1xuXHQvLyBgdmlhYCBiYWNrLXBhdGNoZWQgd2hlbiB0aGUgb3V0ZXIgYm9keSBpcyBhbmFseXNlZFxuXHRwcml2YXRlIHdyYXBFbnRyeUJ5Tm9kZSA9IG5ldyBNYXA8dHMuTm9kZSwgRURTSW5mbz4oKTtcblx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHM6IHZhcmlhYmxlTmFtZSAtPiBmdWxsUGF0aCBvZiB0aGUgdHlwZSBpdCBob2xkc1xuXHRwcml2YXRlIHZhcmlhYmxlVG9UeXBlTWFwID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0Ly8gVHJhY2sgbW5lbW9uaWNhIG1vZHVsZS1vYmplY3QgdmFyaWFibGVzIChlLmcuLCBpbXBvcnQgeyBtbmVtb25pY2EgfSBmcm9tICdtbmVtb25pY2EnOyBjb25zdCBtID0gbW5lbW9uaWNhKVxuXHRwcml2YXRlIG1vZHVsZU9iamVjdFZhcmlhYmxlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHQvLyBmaWxlIC0+IChsb2NhbCBuYW1lIC0+IGltcG9ydGVkIG5hbWUpIGZvciBuYW1lZCBpbXBvcnRzIGZyb21cblx0Ly8gJ21uZW1vbmljYScg4oCUIGltcG9ydC1hd2FyZW5lc3MgZm9yIHRoZSBjb25zdHJ1Y3Rpb24tZnVuY3Rpb25cblx0Ly8gcmVjb2duaXRpb24gKGNhbGwvYXBwbHkvYmluZCkgYW5kIHRoZSB1dGlscyBmb3JtcyAobWVyZ2UvZm9yayk6XG5cdC8vIHVzZXJsYW5kIGZ1bmN0aW9ucyB3aXRoIHRob3NlIG5hbWVzIG11c3QgbmV2ZXIgbWF0Y2hcblx0cHJpdmF0ZSBtbmVtb25pY2FOYW1lZEltcG9ydHMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgc3RyaW5nPj4oKTtcblx0Ly8gVHJhY2sgaW1wb3J0ZWQgYWxpYXNlcyBvZiBjcmVhdGVUeXBlc0NvbGxlY3Rpb24gKGUuZy4sIGltcG9ydCB7IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbiBhcyBjdGMgfSlcblx0cHJpdmF0ZSBjcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0Ly8gVHJhY2sgY3VzdG9tIGNvbGxlY3Rpb24gdmFyaWFibGVzOiB2YXJpYWJsZU5hbWUgLT4gY29sbGVjdGlvbklkXG5cdHByaXZhdGUgY29sbGVjdGlvblZhcmlhYmxlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdC8vIFRyYWNrIGN1c3RvbSBjb2xsZWN0aW9uIG1ldGFkYXRhIGZvciBPcHRpb24gQiByZWdpc3RyeSBlbWlzc2lvblxuXHRwcml2YXRlIGNvbGxlY3Rpb25JbmZvID0gbmV3IE1hcDxzdHJpbmcsIENvbGxlY3Rpb25JbmZvPigpO1xuXHRwcml2YXRlIGNvbGxlY3Rpb25Db3VudGVyID0gMDtcblx0Ly8gSW5zdHJ1bWVudGF0aW9uIGNvbGxlY3Rpb24gKHN5bnRhY3RpYyBvbmx5IOKAlCBubyB0eXBlIGNoZWNrZXIpOlxuXHQvLyBldmVyeSBuYW1lZCBjbGFzcyBkZWNsYXJhdGlvbiBieSBzaW1wbGUgbmFtZSwgZm9yIHJlc29sdmluZ1xuXHQvLyByZWdpc3RyYXRpb24gc2l0ZXMgdG8gZGVjbGFyYXRpb24gbG9jYXRpb25zIChiZXN0IGVmZm9ydCwgbGFzdCB3aW5zKVxuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMgPSBuZXcgTWFwPHN0cmluZywgSW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNsPigpO1xuXHQvLyBSZWdpc3RyYXRpb24gc2l0ZXM6IGRlY29yYXRvciBhcHBsaWNhdGlvbnMsIHByb3ZpZGVyLXRva2VuIG9iamVjdFxuXHQvLyBsaXRlcmFscywgY29uc3VtZXIuYXBwbHkoKSBtaWRkbGV3YXJlIHdpcmluZ1xuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvblNpdGVzOiBJbnN0cnVtZW50YXRpb25TaXRlW10gPSBbXTtcblx0Ly8gTWVyZ2VkIHBsdWdpbiB2b2NhYnVsYXJ5IGZvciBpbnN0cnVtZW50YXRpb24gZGV0ZWN0aW9uIChlbXB0eSB3aGVuXG5cdC8vIG5vIHBsdWdpbnMgd2VyZSBwYXNzZWQg4oCUIHRoZSBhbmFseXplciB0aGVuIGNvbGxlY3RzIG5vIHBvaW50cylcblx0cHJpdmF0ZSBpbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5OiBJbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5O1xuXHQvLyBSZWZlcmVuY2VkLXR5cGUgcmVzb2x1dGlvbiAoRjEwKTogcGVyLWZpbGUgZGVjbGFyYXRpb25zIGFuZCBpbXBvcnRzLlxuXHQvLyBBIHR5cGUgbmFtZSB1c2VkIGluIGZpbGUgWCByZXNvbHZlcyB0aHJvdWdoIFgncyBvd24gaW1wb3J0IHN0YXRlbWVudHNcblx0Ly8gZmlyc3QgKHJlbGF0aXZlICsgdHNjb25maWctcGF0aHMsIHZpYSB0cy5yZXNvbHZlTW9kdWxlTmFtZSksIHRoZW5cblx0Ly8gWCdzIGxvY2FsIGRlY2xhcmF0aW9ucywgdGhlbiDigJQgb25seSB3aGVuIG5vdGhpbmcgaW1wb3J0cyBvciBkZWNsYXJlc1xuXHQvLyB0aGUgbmFtZSDigJQgdGhlIHVuaXF1ZSBzYW1lLW5hbWVkIGRlY2xhcmF0aW9uIGFjcm9zcyBzY2FubmVkIGZpbGVzLlxuXHQvLyBHZW51aW5lIGFtYmlndWl0eSBvciBhbiB1bnJlc29sdmFibGUgcmVmZXJlbmNlIHlpZWxkcyBgdW5rbm93bmAsIG5ldmVyXG5cdC8vIGEgYmFyZSBlbWl0dGVkIG5hbWU6IGdlbmVyYXRlZCB0eXBlcy50cyBjYXJyaWVzIG5vIGltcG9ydHMgb2YgaXRzIG93bi5cblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZURlY2xzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24+PigpO1xuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlSW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZUltcG9ydD4+KCk7XG5cdC8vIGZpbGUgLT4gKGV4cG9ydGVkIG5hbWUgLT4gcmUtZXhwb3J0IHNwZWNpZmllcikgZm9yIGBleHBvcnQgeyBYIH0gZnJvbSAn4oCmJ2Bcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZVJlRXhwb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBmaWxlIC0+IHNwZWNpZmllcnMgb2YgYGV4cG9ydCAqIGZyb20gJ+KApidgXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmdbXT4oKTtcblx0Ly8gZmlsZSAtPiAoZXhwb3J0ZWQgbmFtZSAtPiBsb2NhbCBuYW1lKSBmb3IgYGV4cG9ydCB7IFggYXMgWSB9YFxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBmaWxlIC0+IChuYW1lc3BhY2UgbmFtZSAtPiBuYW1lc3BhY2UgZGVjbGFyYXRpb24pIOKAlCBtaWRkbGUgc2VnbWVudHNcblx0Ly8gb2YgcXVhbGlmaWVkIHJlZmVyZW5jZXMgKG1vZGVscy5Jbm5lci5DcmF0ZSkgZGVzY2VuZCB0aHJvdWdoIHRoZXNlXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHRzLk1vZHVsZURlY2xhcmF0aW9uPj4oKTtcblx0Ly8gZmlsZSAtPiAobmFtZXNwYWNlIG5hbWUgLT4gc3BlY2lmaWVyKSBmb3IgYGV4cG9ydCAqIGFzIG5zIGZyb20gJ+KApidgXG5cdC8vIGJhcnJlbHMg4oCUIGEgbmVzdGVkIG1vZHVsZSBuYW1lc3BhY2Ugb25lIHNlZ21lbnQgZGVlcFxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlU3RhcnMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgc3RyaW5nPj4oKTtcblx0Ly8gYCR7Y29udGFpbmluZ0ZpbGV9Ojoke3NwZWNpZmllcn1gIC0+IHJlc29sdXRpb24gKHVuZGVmaW5lZCA9IGZhaWxlZClcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZVJlc29sdXRpb25DYWNoZSA9IG5ldyBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZVJlc29sdXRpb24gfCB1bmRlZmluZWQ+KCk7XG5cdC8vIGZpbGUgLT4gKGNvbnN0IG5hbWUgLT4gYXJyYXkgbGl0ZXJhbCkgZm9yIGNvbnN0cyB3aXRoIGFycmF5LWxpdGVyYWxcblx0Ly8gaW5pdGlhbGl6ZXJzIChgYXMgY29uc3RgIC8gYHNhdGlzZmllc2AgdW53cmFwcGVkKSwgc28gYVxuXHQvLyBgdHlwZW9mIHN0YXR1c0xpc3RbbnVtYmVyXWAgZmllbGQgdHlwZSBleHBhbmRzIHRvIHRoZSBlbGVtZW50IGxpdGVyYWxcblx0Ly8gdW5pb24gaW5zdGVhZCBvZiBsZWFraW5nIGEgYmFyZSB1bnJlc29sdmFibGUgYHR5cGVvZmAgcXVlcnkgaW50byB0aGVcblx0Ly8gZ2VuZXJhdGVkIGZpbGUuIERlY2xhcmF0aW9ucyBwZXJzaXN0IGFjcm9zcyBwYXNzZXMg4oCUIGVudHJpZXMgc3RheVxuXHQvLyB2YWxpZCBhZnRlciByZXNldFVzYWdlcygpLCBzYW1lIGFzIHJlZmVyZW5jZWRUeXBlRGVjbHNcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24+PigpO1xuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlQ29tcGlsZXJPcHRpb25zOiB0cy5Db21waWxlck9wdGlvbnM7XG5cdC8vIEZpbGUgd2hvc2UgQVNUIGlzIGN1cnJlbnRseSBiZWluZyB2aXNpdGVkOyByZWZlcmVuY2VzIHJlc29sdmUgYWdhaW5zdCBpdFxuXHRwcml2YXRlIGN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSAnJztcblx0Ly8gQWxpYXMgbmFtZXMgY3VycmVudGx5IGJlaW5nIGV4cGFuZGVkIChjeWNsZSBndWFyZClcblx0cHJpdmF0ZSBleHBhbmRpbmdSZWZlcmVuY2VkQWxpYXNlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHQvLyBNbmVtb25pY2EtZ3JhcGggaWRlbnRpdHkgbGF3IChoYXJkIGZhaWwpOiBldmVyeSBkZWZpbmUoKS9sYXp5KCkvXG5cdC8vIEBkZWNvcmF0ZSgpIHNpdGUga2V5ZWQgYnkgaXRzIHJ1bnRpbWUgbmFtZXNwYWNlIChjb2xsZWN0aW9uIHJvb3RzOlxuXHQvLyBgPGNvbGxlY3Rpb24+Ojo8bmFtZT5gOyBzdWJ0eXBlczogYDxwYXJlbnRGdWxsUGF0aD4uPG5hbWU+YCkuIFR3b1xuXHQvLyBzaXRlcyBpbiBvbmUgbmFtZXNwYWNlIGFyZSBhIHNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZSDigJQgdGhlIHJ1bnRpbWVcblx0Ly8gdGhyb3dzIEFMUkVBRFlfREVDTEFSRUQg4oCUIGFuZCBtdXN0IGFib3J0IGdlbmVyYXRpb24uXG5cdHByaXZhdGUgZGVmaW5lU2l0ZXMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nW10+KCk7XG5cdC8vIE1uZW1vbmljYS1ncmFwaCByZWZlcmVuY2VzIHRoYXQgc3RheWVkIGFtYmlndW91cyBhZnRlciBwYXRoLWF3YXJlXG5cdC8vIHJlc29sdXRpb24gb3IgcmVzb2x2ZWQgdG8gbm90aGluZyAoaGFyZC1mYWlsIGNsYXNzIDIpXG5cdHByaXZhdGUgZ3JhcGhSZWZlcmVuY2VFcnJvcnM6IFJlc29sdXRpb25FcnJvcltdID0gW107XG5cdC8vIEd1YXJkcyBsb29rdXAoKS1wYXRoIHZhbGlkYXRpb24gc28gaXQgcnVucyBvbmNlIHBlciB1c2FnZXMgcGFzc1xuXHQvLyAoZ2V0UmVzb2x1dGlvbkVycm9ycyBtYXkgYmUgY2FsbGVkIHJlcGVhdGVkbHkpOyByZXNldFVzYWdlcyByZS1hcm1zIGl0XG5cdHByaXZhdGUgbG9va3VwUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHQvLyBMaXRlcmFsIGxvb2t1cCgpIGNhbGwgc2l0ZXMgd2l0aCB0aGVpciByZXNvbHZlZCBwYXRocy4gS2VwdCBhcGFydCBmcm9tXG5cdC8vIHRoZSB1c2FnZXMgbWFwIG9uIHB1cnBvc2U6IGFkZFVzYWdlIGRyb3BzIHBhdGhzIHRoZSBncmFwaCBkb2VzIG5vdFxuXHQvLyBrbm93ICh1c2FnZXMuanNvbiBpbmRleGVzIHJlZmVyZW5jZXMgdG8gS05PV04gdHlwZXMpLCBidXQgYW4gdW5rbm93blxuXHQvLyBsb29rdXAgcGF0aCBpcyBleGFjdGx5IHRoZSBoYXJkLWZhaWwgY2FzZSDigJQgdGhlIHJ1bnRpbWUgcmV0dXJuc1xuXHQvLyB1bmRlZmluZWQgdGhlcmUgYW5kIHRoZSBUeXBlRXJyb3IgYXJyaXZlcyBvbmUgbGluZSBsYXRlclxuXHRwcml2YXRlIGxvb2t1cFJlZmVyZW5jZXM6IHsgcGF0aDogc3RyaW5nOyBsb2NhdGlvbjogc3RyaW5nIH1bXSA9IFtdO1xuXHQvLyBHdWFyZHMgcGxhaW4tVFMgcmVmZXJlbmNlIHZhbGlkYXRpb24gc28gaXQgcnVucyBvbmNlIHBlciB1c2FnZXMgcGFzc1xuXHQvLyAoZ2V0UmVzb2x1dGlvbkVycm9ycyBtYXkgYmUgY2FsbGVkIHJlcGVhdGVkbHkpOyByZXNldFVzYWdlcyByZS1hcm1zIGl0XG5cdHByaXZhdGUgcGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHQvLyBQbGFpbi1UUyB0eXBlIHJlZmVyZW5jZSBzaXRlcyB3aG9zZSByZXNvbHV0aW9uIGZlbGwgdGhyb3VnaCBpbXBvcnRzLFxuXHQvLyBsb2NhbHMsIHRoZSBwcm9ncmFtLXdpZGUgc2NhbiwgYW5kIHRoZSBncmFwaCB0byBhIHNvZnQgYHVua25vd25gLlxuXHQvLyBWYWxpZGF0ZWQgbGF6aWx5IGZyb20gZ2V0UmVzb2x1dGlvbkVycm9ycyBhZ2FpbnN0IHRoZSBjb21wbGV0ZVxuXHQvLyBkZWNsYXJhdGlvbiBtYXA6IGEgbmFtZSBzZXZlcmFsIHByb2plY3Qtc291cmNlIGZpbGVzIGRlY2xhcmUg4oCUIHdpdGhcblx0Ly8gbm8gaW1wb3J0IGluIHRoZSByZWZlcmVuY2luZyBmaWxlIHRvIGFuY2hvciBpdCDigJQgaXMgdGhlIHBsYWluLVRTXG5cdC8vIGFtYmlndWl0eSBoYXJkLWZhaWwgY2xhc3MgKG9uZSB0aWVyIGJlbG93IHRoZSBncmFwaCBpZGVudGl0eSBsYXcpO1xuXHQvLyBhYnNlbmNlIChnaG9zdCBuYW1lcykgc3RheXMgc29mdC4gUmVjb3JkaW5nIGhhcHBlbnMgb24gZXZlcnkgcGFzcyxcblx0Ly8gdGhlIHZlcmRpY3Qgb25seSBoZXJlIOKAlCBwYXNzIDEgc2VlcyBhbiBpbmNvbXBsZXRlIGRlY2xhcmF0aW9uIG1hcCxcblx0Ly8gc28gb25seSB0aGUgdXNhZ2VzIHBhc3MgaXMgYXV0aG9yaXRhdGl2ZSAobWlycm9ycyBsb29rdXAgcmVmZXJlbmNlcylcblx0cHJpdmF0ZSBwbGFpblR5cGVSZWZlcmVuY2VzOiB7IG5hbWU6IHN0cmluZzsgbG9jYXRpb246IHN0cmluZzsgZmlsZTogc3RyaW5nIH1bXSA9IFtdO1xuXHQvLyBQZXItZmlsZSB0b3AtbGV2ZWwgdmFyaWFibGUgLT4gbW5lbW9uaWNhIGZ1bGxQYXRoIGJpbmRpbmdzICh2YWx1ZVxuXHQvLyBzY29wZSk6IGBjb25zdCBBZGRyZXNzID0gVXNlci5kZWZpbmUoJ0FkZHJlc3MnLCDigKYpYCBtYWtlcyBgQWRkcmVzc2Bcblx0Ly8gZGVub3RlIFVzZXIuQWRkcmVzcyB3aGVyZXZlciB0aGF0IGZpbGUncyByZWZlcmVuY2VzIGFyZSByZXNvbHZlZFxuXHRwcml2YXRlIGZpbGVHcmFwaEJpbmRpbmdzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHN0cmluZz4+KCk7XG5cdC8vIFRoZSBncmFwaCB0eXBlIHdob3NlIGNvbnN0cnVjdG9yIGlzIGN1cnJlbnRseSBiZWluZyBleHRyYWN0ZWQ7XG5cdC8vIGFuY2hvcnMgcmVsYXRpdmUtZmlyc3QgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb25cblx0cHJpdmF0ZSBjdXJyZW50R3JhcGhBbmNob3I6IFR5cGVOb2RlIHwgdW5kZWZpbmVkO1xuXHQvLyBkZWZpbmUoKS9sYXp5KCkgY2FsbHMgYWxyZWFkeSBleHRyYWN0ZWQgdGhpcyBwYXNzLiBUaGUgQ0xJIHJlLWFuYWx5emVzXG5cdC8vIGV2ZXJ5IGZpbGUgYWZ0ZXIgcmVzZXRVc2FnZXMoKTsgY2xlYXJpbmcgdGhlIHNldCBsZXRzIHRoZSBzZWNvbmQgcGFzc1xuXHQvLyByZS1leHRyYWN0IGV2ZXJ5IGNvbnN0cnVjdG9yIGFnYWluc3QgdGhlIENPTVBMRVRFIGdyYXBoIOKAlCBwYXNzIDEgc2Vlc1xuXHQvLyBmb3J3YXJkIHJlZmVyZW5jZXMgYXMgYG5vbmVgIChzb2Z0IHVua25vd24pIGJlY2F1c2UgbGF0ZXIgZmlsZXMgaGF2ZVxuXHQvLyBub3QgYmVlbiB2aXNpdGVkIHlldCwgc28gb25seSBwYXNzLTIgcmVzb2x1dGlvbiBpcyBhdXRob3JpdGF0aXZlIGZvclxuXHQvLyB0aGUgaGFyZC1mYWlsIGlkZW50aXR5IGxhdy4gVGhlIHN0YW1wIGxpdmVzIGhlcmUgcmF0aGVyIHRoYW4gb24gdGhlXG5cdC8vIEFTVCBub2RlIHNvIGl0IGNhbiBhY3R1YWxseSBiZSBjbGVhcmVkLiAoQ2hhaW5lZCBjYWxscyB2aXNpdCB0aGUgc2FtZVxuXHQvLyBub2RlIHR3aWNlIHdpdGhpbiBvbmUgcGFzczsgdGhlIGluLXBhc3MgZGVkdXAgYmVsb3cgc3RheXMuKVxuXHRwcml2YXRlIHByb2Nlc3NlZENhbGxzID0gbmV3IFNldDx0cy5DYWxsRXhwcmVzc2lvbj4oKTtcblxuXHRjb25zdHJ1Y3RvciAocHJvZ3JhbT86IHRzLlByb2dyYW0sIHBsdWdpbnM6IFRhY3RpY2FQbHVnaW5bXSA9IFtdKSB7XG5cdFx0Ly8gQ29tcGlsZXIgb3B0aW9ucyBkcml2ZSB0cy5yZXNvbHZlTW9kdWxlTmFtZSBmb3IgaW1wb3J0LWF3YXJlXG5cdFx0Ly8gcmVmZXJlbmNlZC10eXBlIHJlc29sdXRpb24gKHRzY29uZmlnIGBwYXRoc2AsIGV4dGVuc2lvbmxlc3Ncblx0XHQvLyBpbXBvcnRzKTsgdGhlIHR5cGUgY2hlY2tlciBpdHNlbGYgc3RheXMgdW51c2VkLlxuXHRcdHRoaXMucmVmZXJlbmNlZFR5cGVDb21waWxlck9wdGlvbnMgPSBwcm9ncmFtPy5nZXRDb21waWxlck9wdGlvbnMoKSA/PyB7fTtcblx0XHR0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkgPSBtZXJnZVRhY3RpY2FQbHVnaW5zKHBsdWdpbnMpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc2V0IHVzYWdlLXJlbGF0ZWQgc3RhdGUgZm9yIGEgZnJlc2ggcGFzcy5cblx0ICogQ2FsbCBiZWZvcmUgdGhlIHVzYWdlLWNvbGxlY3Rpb24gcGFzcyB0byBhdm9pZCBkdXBsaWNhdGVzIGZyb20gZGVmaW5pdGlvbiBwYXNzLlxuXHQgKi9cblx0cmVzZXRVc2FnZXMgKCk6IHZvaWQge1xuXHRcdHRoaXMudXNhZ2VzLmNsZWFyKCk7XG5cdFx0dGhpcy5lZHNVc2FnZXMuY2xlYXIoKTtcblx0XHR0aGlzLmZsb3dVc2FnZXMuY2xlYXIoKTtcblx0XHR0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmNsZWFyKCk7XG5cdFx0Ly8gRURTIGVudHJ5IHJlZmVyZW5jZXMgZ28gc3RhbGUgd2l0aCBlZHNVc2FnZXM7IHZpYSBsaW5rcyBhcmVcblx0XHQvLyByZS1kZXJpdmVkIG9uIHRoZSBuZXh0IHBhc3Ncblx0XHR0aGlzLndyYXBFbnRyeUJ5Tm9kZS5jbGVhcigpO1xuXHRcdHRoaXMubmVzdGVkV3JhcFZpYS5jbGVhcigpO1xuXHRcdC8vIE5vdGU6IG1vZHVsZU9iamVjdFZhcmlhYmxlcyBhbmQgY29sbGVjdGlvblZhcmlhYmxlcyBpbnRlbnRpb25hbGx5IHBlcnNpc3Rcblx0XHQvLyBhY3Jvc3MgZGVmaW5pdGlvbiBhbmQgdXNhZ2UgcGFzc2VzLlxuXHRcdC8vIFJlLWV4dHJhY3Rpb24gaW4gdGhlIHVzYWdlcyBwYXNzIGlzIHdoYXQgbWFrZXMgZ3JhcGggcmVmZXJlbmNlXG5cdFx0Ly8gcmVzb2x1dGlvbiBhdXRob3JpdGF0aXZlOiBwYXNzIDEgcmVzb2x2ZXMgYWdhaW5zdCBhbiBpbmNvbXBsZXRlXG5cdFx0Ly8gZ3JhcGggKGZvcndhcmQgcmVmZXJlbmNlcyByZWFkIGFzIGBub25lYCksIHBhc3MgMiBhZ2FpbnN0IGFsbCBvZiBpdC5cblx0XHR0aGlzLnByb2Nlc3NlZENhbGxzLmNsZWFyKCk7XG5cdFx0Ly8gbG9va3VwKCktcGF0aCB2YWxpZGF0aW9uIHJ1bnMgYWdhaW5zdCB0aGUgcmVjb3JkZWQgc2l0ZXM7IGEgZnJlc2hcblx0XHQvLyBwYXNzIG11c3QgcmUtcmVjb3JkIGFuZCByZS12YWxpZGF0ZSAocGFzcy0xIHJlc3VsdHMgd291bGQgYmVcblx0XHQvLyBwcmVtYXR1cmUg4oCUIHRoZSBncmFwaCBpcyBzdGlsbCBpbmNvbXBsZXRlKVxuXHRcdHRoaXMubG9va3VwUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHRcdHRoaXMubG9va3VwUmVmZXJlbmNlcyA9IFtdO1xuXHRcdHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHRcdHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlcyA9IFtdO1xuXHR9XG5cblx0LyoqXG5cdCAqIEFuYWx5emUgYSBzb3VyY2UgZmlsZSBmb3IgTW5lbW9uaWNhIHR5cGUgZGVmaW5pdGlvbnNcblx0ICovXG5cdGFuYWx5emVGaWxlIChzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogQW5hbHl6ZVJlc3VsdCB7XG5cdFx0dGhpcy5lcnJvcnMgPSBbXTtcblx0XHQvLyBSZWZlcmVuY2VkLXR5cGUgbmFtZXMgaW4gdGhpcyBmaWxlIHJlc29sdmUgYWdhaW5zdCBpdHMgb3duIGltcG9ydHNcblx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSBub2RlUGF0aC5yZXNvbHZlKHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXHRcdC8vIEVuc3VyZSBwYXJlbnQgbm9kZXMgYXJlIHNldCBmb3IgQVNUIHRyYXZlcnNhbFxuXHRcdHRoaXMuc2V0UGFyZW50Tm9kZXNJblNvdXJjZUZpbGUoc291cmNlRmlsZSk7XG5cdFx0dGhpcy52aXNpdE5vZGUoc291cmNlRmlsZSwgc291cmNlRmlsZSk7XG5cblx0XHRyZXR1cm4ge1xuXHRcdFx0dHlwZXMgIDogdGhpcy5ncmFwaC5nZXRBbGxUeXBlcygpLFxuXHRcdFx0ZXJyb3JzIDogdGhpcy5lcnJvcnMsXG5cdFx0fTtcblx0fVxuXG5cdC8qKlxuXHQgKiBBbmFseXplIHNvdXJjZSBjb2RlIHN0cmluZ1xuXHQgKi9cblx0YW5hbHl6ZVNvdXJjZSAoc291cmNlQ29kZTogc3RyaW5nLCBmaWxlTmFtZSA9ICd0ZW1wLnRzJyk6IEFuYWx5emVSZXN1bHQge1xuXHRcdGNvbnN0IHNvdXJjZUZpbGUgPSB0cy5jcmVhdGVTb3VyY2VGaWxlKFxuXHRcdFx0ZmlsZU5hbWUsXG5cdFx0XHRzb3VyY2VDb2RlLFxuXHRcdFx0dHMuU2NyaXB0VGFyZ2V0LkxhdGVzdCxcblx0XHRcdHRydWVcblx0XHQpO1xuXHRcdHJldHVybiB0aGlzLmFuYWx5emVGaWxlKHNvdXJjZUZpbGUpO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCB0aGUgdHlwZSBncmFwaFxuXHQgKi9cblx0Z2V0R3JhcGggKCk6IFR5cGVHcmFwaEltcGwge1xuXHRcdHJldHVybiB0aGlzLmdyYXBoO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBjb2xsZWN0ZWQgZGVmaW5pdGlvbnNcblx0ICovXG5cdGdldERlZmluaXRpb25zICgpOiBNYXA8c3RyaW5nLCBEZWZpbml0aW9uSW5mbz4ge1xuXHRcdHJldHVybiB0aGlzLmRlZmluaXRpb25zO1xuXHR9XG5cblx0LyoqXG5cdCAqIFRoZSBjb2xsZWN0aW9ucy5qc29uIG1hbmlmZXN0OiBvbmUgZW50cnkgcGVyIG1pbnRlZCBjb2xsZWN0aW9uLCBpblxuXHQgKiBtaW50aW5nIG9yZGVyLCBwcmVjZWRlZCBieSB0aGUgZGVmYXVsdC1jb2xsZWN0aW9uIGVudHJ5IHdoZW5ldmVyXG5cdCAqIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcyBleGlzdC4gVGhlIGRlZmF1bHQgZW50cnkgaGFzIG5vIGlkL2xvY2F0aW9uXG5cdCAqICh0aGVyZSBpcyBubyBjYWxsIHNpdGUg4oCUIHVucHJlZml4ZWQgZnVsbFBhdGhzIGFyZSBpdHMgaWRlbnRpdHkpLlxuXHQgKiBGb3JtYXQgMS4yOiB0aGUgcmVnaXN0cnkgaW50ZXJmYWNlIGlzIE5PVCBlbWl0dGVkIChpdCBpcyBhXG5cdCAqIFR5cGVTY3JpcHQtb25seSBjb25jZXJuIOKAlCB0aGUgaW4tbWVtb3J5IHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSB0aGF0XG5cdCAqIHR5cGVzLnRzL3JlZ2lzdHJ5LnRzIGFyZSBnZW5lcmF0ZWQgZnJvbSBzdGF5cyBvbiB0aGUgVHlwZU5vZGUpLlxuXHQgKi9cblx0Z2V0Q29sbGVjdGlvbnNNYW5pZmVzdCAoKTogQ29sbGVjdGlvbk1hbmlmZXN0RW50cnlbXSB7XG5cdFx0Y29uc3QgZW50cmllczogQ29sbGVjdGlvbk1hbmlmZXN0RW50cnlbXSA9IFtdO1xuXHRcdGNvbnN0IGhhc0RlZmF1bHRUeXBlcyA9IHRoaXMuZ3JhcGguZ2V0QWxsVHlwZXMoKS5zb21lKHQgPT4gdC5jb2xsZWN0aW9uSWQgPT09IHVuZGVmaW5lZCk7XG5cdFx0aWYgKGhhc0RlZmF1bHRUeXBlcykge1xuXHRcdFx0ZW50cmllcy5wdXNoKHtcblx0XHRcdFx0aWQgICAgICAgOiBudWxsLFxuXHRcdFx0XHRuYW1lICAgICA6ICdkZWZhdWx0VHlwZXMnLFxuXHRcdFx0XHRsb2NhdGlvbiA6IG51bGwsXG5cdFx0XHRcdGxhbmd1YWdlIDogJ3R5cGVzY3JpcHQnXG5cdFx0XHR9KTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBbIGlkLCBpbmZvIF0gb2YgdGhpcy5jb2xsZWN0aW9uSW5mbykge1xuXHRcdFx0Y29uc3QgZW50cnk6IENvbGxlY3Rpb25NYW5pZmVzdEVudHJ5ID0ge1xuXHRcdFx0XHRpZCxcblx0XHRcdFx0bmFtZSAgICAgOiBpbmZvLnZhcmlhYmxlTmFtZSxcblx0XHRcdFx0bG9jYXRpb24gOiBgJHtpbmZvLnNvdXJjZUZpbGV9OiR7aW5mby5saW5lfToke2luZm8uY29sdW1ufWAsXG5cdFx0XHRcdGxhbmd1YWdlIDogJ3R5cGVzY3JpcHQnXG5cdFx0XHR9O1xuXHRcdFx0ZW50cmllcy5wdXNoKGVudHJ5KTtcblx0XHR9XG5cdFx0cmV0dXJuIGVudHJpZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCB1c2FnZXNcblx0ICovXG5cdGdldFVzYWdlcyAoKTogTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+IHtcblx0XHRyZXR1cm4gdGhpcy51c2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBFRFMgdXNhZ2VzXG5cdCAqL1xuXHRnZXRFRFNVc2FnZXMgKCk6IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4ge1xuXHRcdHJldHVybiB0aGlzLmVkc1VzYWdlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGZsb3cgdXNhZ2VzXG5cdCAqL1xuXHRnZXRGbG93VXNhZ2VzICgpOiBNYXA8c3RyaW5nLCBGbG93SW5mb1tdPiB7XG5cdFx0cmV0dXJuIHRoaXMuZmxvd1VzYWdlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGluc3RydW1lbnRhdGlvbiBwb2ludHMuXG5cdCAqIFJlZ2lzdHJhdGlvbiBzaXRlcyByZWZlcmVuY2luZyBhIGNsYXNzIGRlY2xhcmVkIGluIHRoZSBzYW1lIHByb2plY3Rcblx0ICogcmVzb2x2ZSB0byB0aGUgY2xhc3MgZGVjbGFyYXRpb24ncyBsb2NhdGlvbi9jb2RlOyBleHRlcm5hbCBjbGFzc2VzXG5cdCAqIChlLmcuLCBhIGZyYW1ld29yay1idWlsdGluIGltcGxlbWVudGF0aW9uIGZyb20gbm9kZV9tb2R1bGVzKSBrZWVwXG5cdCAqIHRoZSByZWdpc3RyYXRpb24gc2l0ZS5cblx0ICogRGVkdXBlZCBieSBraW5kK2NsYXNzTmFtZStsb2NhdGlvbitzY29wZSB3aXRoIHRhcmdldHMgbWVyZ2VkIOKAlCBhXG5cdCAqIGNsYXNzIGRldGVjdGVkIGJ5IGhlcml0YWdlIEFORCBieSBhIGRlY29yYXRvciBzaXRlIHlpZWxkcyBzZXBhcmF0ZVxuXHQgKiBlbnRyaWVzIHdpdGggZGlzdGluY3Qgc2NvcGVzIChzZWUgSW5zdHJ1bWVudGF0aW9uUG9pbnQgaW4gdHlwZXMudHMpLlxuXHQgKi9cblx0Z2V0SW5zdHJ1bWVudGF0aW9uUG9pbnRzICgpOiBJbnN0cnVtZW50YXRpb25Qb2ludFtdIHtcblx0XHRjb25zdCBwb2ludHMgPSBuZXcgTWFwPHN0cmluZywgSW5zdHJ1bWVudGF0aW9uUG9pbnQ+KCk7XG5cblx0XHRjb25zdCBhZGRQb2ludCA9IChwb2ludDogSW5zdHJ1bWVudGF0aW9uUG9pbnQpOiB2b2lkID0+IHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3BvaW50LmtpbmR9fCR7cG9pbnQuY2xhc3NOYW1lfXwke3BvaW50LmxvY2F0aW9ufXwke3BvaW50LnNjb3BlfWA7XG5cdFx0XHRjb25zdCBleGlzdGluZyA9IHBvaW50cy5nZXQoa2V5KTtcblx0XHRcdGlmIChleGlzdGluZykge1xuXHRcdFx0XHRjb25zdCBtZXJnZWQgPSBuZXcgU2V0KFsgLi4uZXhpc3RpbmcudGFyZ2V0cywgLi4ucG9pbnQudGFyZ2V0cyBdKTtcblx0XHRcdFx0ZXhpc3RpbmcudGFyZ2V0cyA9IEFycmF5LmZyb20obWVyZ2VkKTtcblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0cG9pbnRzLnNldChrZXksIHBvaW50KTtcblx0XHR9O1xuXG5cdFx0Zm9yIChjb25zdCBzaXRlIG9mIHRoaXMuaW5zdHJ1bWVudGF0aW9uU2l0ZXMpIHtcblx0XHRcdGNvbnN0IGRlY2wgPSB0aGlzLmluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMuZ2V0KHNpdGUuY2xhc3NOYW1lKTtcblx0XHRcdGNvbnN0IHBvaW50OiBJbnN0cnVtZW50YXRpb25Qb2ludCA9IHtcblx0XHRcdFx0a2luZCAgICAgIDogc2l0ZS5raW5kLFxuXHRcdFx0XHRjbGFzc05hbWUgOiBzaXRlLmNsYXNzTmFtZSxcblx0XHRcdFx0bG9jYXRpb24gIDogZGVjbCA/IGRlY2wubG9jYXRpb24gOiBzaXRlLmxvY2F0aW9uLFxuXHRcdFx0XHRjb2RlICAgICAgOiBkZWNsID8gZGVjbC5jb2RlIDogc2l0ZS5jb2RlLFxuXHRcdFx0XHRzY29wZSAgICAgOiBzaXRlLnNjb3BlLFxuXHRcdFx0XHR0YXJnZXRzICAgOiBzaXRlLnRhcmdldHMsXG5cdFx0XHR9O1xuXHRcdFx0YWRkUG9pbnQocG9pbnQpO1xuXHRcdH1cblxuXHRcdC8vIEhlcml0YWdlLWRlY2xhcmVkIGNsYXNzZXMgYWx3YXlzIGVtaXQgYSBkZWNsYXJhdGlvbiBwb2ludCB3aXRoXG5cdFx0Ly8gc2NvcGUgJ21vZHVsZScgKGF0dGFjaG1lbnQgc3RhdGljYWxseSB1bmtub3duKTsgcmVnaXN0cmF0aW9uXG5cdFx0Ly8gc2l0ZXMgYWJvdmUgY2FycnkgdGhlIG5hcnJvd2VyIHNjb3BlcyBhcyBzZXBhcmF0ZSBlbnRyaWVzXG5cdFx0Zm9yIChjb25zdCBbIGNsYXNzTmFtZSwgZGVjbCBdIG9mIHRoaXMuaW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNscykge1xuXHRcdFx0aWYgKCFkZWNsLmtpbmQpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBwb2ludDogSW5zdHJ1bWVudGF0aW9uUG9pbnQgPSB7XG5cdFx0XHRcdGtpbmQgICAgICA6IGRlY2wua2luZCxcblx0XHRcdFx0Y2xhc3NOYW1lIDogY2xhc3NOYW1lLFxuXHRcdFx0XHRsb2NhdGlvbiAgOiBkZWNsLmxvY2F0aW9uLFxuXHRcdFx0XHRjb2RlICAgICAgOiBkZWNsLmNvZGUsXG5cdFx0XHRcdHNjb3BlICAgICA6ICdtb2R1bGUnLFxuXHRcdFx0XHR0YXJnZXRzICAgOiBbXSxcblx0XHRcdH07XG5cdFx0XHRhZGRQb2ludChwb2ludCk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVzdWx0ID0gQXJyYXkuZnJvbShwb2ludHMudmFsdWVzKCkpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogQWRkIGEgdG9wb2xvZ2ljYSB0eXBlIHRvIHRoZSBhbmFseXplciBmb3IgdXNhZ2UgdHJhY2tpbmcuXG5cdCAqIFRoaXMgYWxsb3dzIHRoZSBhbmFseXplciB0byByZWNvZ25pemUgdG9wb2xvZ2ljYSB0eXBlcyB3aGVuIGNvbGxlY3RpbmcgdXNhZ2VzLlxuXHQgKi9cblx0YWRkVG9wb2xvZ2ljYVR5cGUgKGZ1bGxQYXRoOiBzdHJpbmcsIG5vZGU6IGltcG9ydCgnLi90eXBlcycpLlR5cGVOb2RlKTogdm9pZCB7XG5cdFx0Ly8gU2tpcCBpZiBhbHJlYWR5IGV4aXN0c1xuXHRcdGlmICh0aGlzLmdyYXBoLmFsbFR5cGVzLmhhcyhmdWxsUGF0aCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGggc28gaXQgY2FuIGJlIGZvdW5kIGR1cmluZyB1c2FnZSBjb2xsZWN0aW9uXG5cdFx0aWYgKG5vZGUucGFyZW50KSB7XG5cdFx0XHQvLyBBZGQgYXMgY2hpbGQgb2YgcGFyZW50XG5cdFx0XHR0aGlzLmdyYXBoLmFkZENoaWxkKG5vZGUucGFyZW50LCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0Ly8gQWRkIGFzIHJvb3Rcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cblx0XHQvLyBBbHNvIGFkZCB0byBkZWZpbml0aW9ucyBzbyBpdCdzIHJlY29nbml6ZWQgYXMgYSBrbm93biB0eXBlXG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IG5vZGUubmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7bm9kZS5zb3VyY2VGaWxlfToke25vZGUubGluZX06JHtub2RlLmNvbHVtbn1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogbm9kZS5wYXJlbnQgPyBub2RlLnBhcmVudC5mdWxsUGF0aCA6IG51bGwsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IHRydWUsXG5cdFx0XHRibG9ja0Vycm9ycyA6IGZhbHNlXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChmdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdH1cblxuXHQvKipcblx0ICogU2V0IHBhcmVudCBub2RlcyBpbiBhIHNvdXJjZSBmaWxlIHRvIGVuYWJsZSBBU1QgdHJhdmVyc2FsIHVwXG5cdCAqL1xuXHRwcml2YXRlIHNldFBhcmVudE5vZGVzSW5Tb3VyY2VGaWxlIChzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3Qgc2V0UGFyZW50ID0gKG5vZGU6IHRzLk5vZGUsIHBhcmVudD86IHRzLk5vZGUpID0+IHtcblx0XHRcdC8vIFR5cGVTY3JpcHQgZG9lc24ndCBleHBvc2UgcGFyZW50IGFzIHdyaXRhYmxlLCBidXQgd2UgbmVlZCBpdFxuXHRcdFx0Ly8gZXNsaW50LWRpc2FibGUtbmV4dC1saW5lIEB0eXBlc2NyaXB0LWVzbGludC9uby1leHBsaWNpdC1hbnlcblx0XHRcdChub2RlIGFzIGFueSkucGFyZW50ID0gcGFyZW50O1xuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHNldFBhcmVudChjaGlsZCwgbm9kZSkpO1xuXHRcdH07XG5cdFx0c2V0UGFyZW50KHNvdXJjZUZpbGUpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFZpc2l0IGEgbm9kZSBpbiB0aGUgQVNUXG5cdCAqL1xuXHRwcml2YXRlIHZpc2l0Tm9kZSAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSwgY3VycmVudENsYXNzPzogdHMuQ2xhc3NEZWNsYXJhdGlvbik6IHZvaWQge1xuXHRcdC8vIFRyYWNrIG1uZW1vbmljYSBtb2R1bGUtb2JqZWN0IGFsaWFzZXMgYW5kIGN1c3RvbSBjb2xsZWN0aW9uIHZhcmlhYmxlc1xuXHRcdC8vIGJlZm9yZSBwcm9jZXNzaW5nIGRlZmluZSgpL2xvb2t1cCgpIGNhbGxzIHNvIHNvdXJjZSByZXNvbHV0aW9uIHdvcmtzLlxuXHRcdHRoaXMudHJhY2tJbXBvcnRzKG5vZGUpO1xuXHRcdHRoaXMudHJhY2tNb2R1bGVPYmplY3RBbGlhc2VzKG5vZGUpO1xuXHRcdHRoaXMudHJhY2tDb2xsZWN0aW9uQWxpYXNlcyhub2RlLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIENoZWNrIGZvciBkZWZpbmUoKSBjYWxsc1xuXHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChub2RlKSkge1xuXHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ2FsbChub2RlIGFzIHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgbGF6eSgpIGNhbGxzXG5cdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChub2RlKSkge1xuXHRcdFx0dGhpcy5wcm9jZXNzTGF6eUNhbGwobm9kZSBhcyB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIGRlY29yYXRlKCkgZGVjb3JhdG9yXG5cdFx0aWYgKHRoaXMuaXNEZWNvcmF0ZURlY29yYXRvcihub2RlKSkge1xuXHRcdFx0dGhpcy5wcm9jZXNzRGVjb3JhdGVEZWNvcmF0b3Iobm9kZSBhcyB0cy5EZWNvcmF0b3IsIHNvdXJjZUZpbGUsIGN1cnJlbnRDbGFzcyk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIHR5cGUgdXNhZ2VzIChuZXcgVHlwZSgpLCB0eXBlIGFubm90YXRpb25zLCBldGMuKVxuXHRcdHRoaXMuY29sbGVjdFVzYWdlKG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIEVEUyBwYXR0ZXJucyAod3JhcCwgY3VycmVudCwgZ2V0RmxvdywgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RFRFMobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgbmF0aXZlIGZsb3cgcGF0dGVybnMgKHByb3BlcnR5IGFjY2VzcywgbWV0aG9kIGNhbGxzLCBldGMuKVxuXHRcdHRoaXMuY29sbGVjdEZsb3cobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgZnJhbWV3b3JrIGluc3RydW1lbnRhdGlvbiBwb2ludHMgKHZvY2FidWxhcnkgc3VwcGxpZWRcblx0XHQvLyBieSBwbHVnaW5zOyBzeW50YWN0aWMgb25seSDigJQgbm8gdHlwZSBjaGVja2VyKVxuXHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbihub2RlLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIENvbGxlY3QgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9ucyAoYWxpYXNlcywgY2xhc3NlcywgaW50ZXJmYWNlcylcblx0XHQvLyBwZXIgZmlsZSwgYW5kIHRoZSBmaWxlJ3MgaW1wb3J0IHdpcmluZywgZm9yIGltcG9ydC1hd2FyZSByZXNvbHV0aW9uXG5cdFx0dGhpcy50cmFja1JlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24obm9kZSk7XG5cdFx0dGhpcy50cmFja1JlZmVyZW5jZWRUeXBlSW1wb3J0KG5vZGUpO1xuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZVJlRXhwb3J0KG5vZGUpO1xuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXkobm9kZSk7XG5cblx0XHQvLyBUcmFjayBzYW1lLWZpbGUgZnVuY3Rpb24gYmluZGluZ3Mgc28gRURTIGNhbiByZXNvbHZlIHdyYXAoZm4pXG5cdFx0Ly8gYXJndW1lbnRzIHdpdGhvdXQgdGhlIHR5cGUgY2hlY2tlciAoYmVzdCBlZmZvcnQsIGxhc3Qgd2lucylcblx0XHRpZiAodHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKG5vZGUpICYmIG5vZGUubmFtZSkge1xuXHRcdFx0Y29uc3Qga2V5ID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX0jJHtub2RlLm5hbWUudGV4dH1gO1xuXHRcdFx0dGhpcy5mdW5jdGlvbkJpbmRpbmdzLnNldChrZXksIG5vZGUpO1xuXHRcdH1cblx0XHRpZiAoXG5cdFx0XHR0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpICYmXG5cdFx0XHRub2RlLmluaXRpYWxpemVyICYmXG5cdFx0XHQodHMuaXNBcnJvd0Z1bmN0aW9uKG5vZGUuaW5pdGlhbGl6ZXIpIHx8IHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKG5vZGUuaW5pdGlhbGl6ZXIpKVxuXHRcdCkge1xuXHRcdFx0Y29uc3Qga2V5ID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX0jJHtub2RlLm5hbWUudGV4dH1gO1xuXHRcdFx0dGhpcy5mdW5jdGlvbkJpbmRpbmdzLnNldChrZXksIG5vZGUuaW5pdGlhbGl6ZXIpO1xuXHRcdH1cblxuXHRcdC8vIFRyYWNrIGNsYXNzIGRlY2xhcmF0aW9ucyBmb3IgZGVjb3JhdG9yIHBhcmVudCBsb29rdXBcblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHQvLyBWaXNpdCBjaGlsZHJlbiB3aXRoIHRoaXMgY2xhc3MgYXMgdGhlIGN1cnJlbnQgY29udGV4dFxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHRoaXMudmlzaXROb2RlKGNoaWxkLCBzb3VyY2VGaWxlLCBub2RlKSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdC8vIFJlY3Vyc2l2ZWx5IHZpc2l0IGNoaWxkcmVuXG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgY2hpbGQgPT4gdGhpcy52aXNpdE5vZGUoY2hpbGQsIHNvdXJjZUZpbGUsIGN1cnJlbnRDbGFzcykpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBUcmFjayBpbXBvcnRzIGZyb20gJ21uZW1vbmljYScgc28gYWxpYXNlcyBvZiB0aGUgbW9kdWxlIG9iamVjdCBhbmRcblx0ICogY3JlYXRlVHlwZXNDb2xsZWN0aW9uIGFyZSByZWNvZ25pemVkIHdpdGhvdXQgcmVseWluZyBvbiB0aGUgdHlwZSBjaGVja2VyLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja0ltcG9ydHMgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzSW1wb3J0RGVjbGFyYXRpb24obm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IG1vZHVsZVNwZWNpZmllciB9ID0gbm9kZTtcblx0XHRpZiAoIXRzLmlzU3RyaW5nTGl0ZXJhbChtb2R1bGVTcGVjaWZpZXIpIHx8IG1vZHVsZVNwZWNpZmllci50ZXh0ICE9PSAnbW5lbW9uaWNhJykge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IGNsYXVzZSA9IG5vZGUuaW1wb3J0Q2xhdXNlO1xuXHRcdGlmICghY2xhdXNlKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0IHsgbW5lbW9uaWNhLCBjcmVhdGVUeXBlc0NvbGxlY3Rpb24gfSBmcm9tICdtbmVtb25pY2EnXG5cdFx0aWYgKGNsYXVzZS5uYW1lZEJpbmRpbmdzICYmIHRzLmlzTmFtZWRJbXBvcnRzKGNsYXVzZS5uYW1lZEJpbmRpbmdzKSkge1xuXHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGNsYXVzZS5uYW1lZEJpbmRpbmdzLmVsZW1lbnRzKSB7XG5cdFx0XHRcdGNvbnN0IGxvY2FsTmFtZSA9IGVsZW1lbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBpbXBvcnRlZE5hbWUgPSBlbGVtZW50LnByb3BlcnR5TmFtZVxuXHRcdFx0XHRcdD8gZWxlbWVudC5wcm9wZXJ0eU5hbWUudGV4dFxuXHRcdFx0XHRcdDogbG9jYWxOYW1lO1xuXHRcdFx0XHRpZiAoaW1wb3J0ZWROYW1lID09PSAnbW5lbW9uaWNhJykge1xuXHRcdFx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChsb2NhbE5hbWUpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChpbXBvcnRlZE5hbWUgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nKSB7XG5cdFx0XHRcdFx0dGhpcy5jcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMuYWRkKGxvY2FsTmFtZSk7XG5cdFx0XHRcdH1cblx0XHRcdFx0bGV0IGZpbGVJbXBvcnRzID0gdGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRcdGlmICghZmlsZUltcG9ydHMpIHtcblx0XHRcdFx0XHRmaWxlSW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHRcdFx0dGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuc2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSwgZmlsZUltcG9ydHMpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGZpbGVJbXBvcnRzLnNldChsb2NhbE5hbWUsIGltcG9ydGVkTmFtZSk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0ICogYXMgbW5lbW9uaWNhIGZyb20gJ21uZW1vbmljYSdcblx0XHRpZiAoY2xhdXNlLm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lc3BhY2VJbXBvcnQoY2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQoY2xhdXNlLm5hbWVkQmluZGluZ3MubmFtZS50ZXh0KTtcblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgbW5lbW9uaWNhIGZyb20gJ21uZW1vbmljYScgKGRlZmF1bHQgaW1wb3J0KSDigJQgdHJlYXQgYXMgbW9kdWxlIG9iamVjdCB0b29cblx0XHRpZiAoY2xhdXNlLm5hbWUpIHtcblx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChjbGF1c2UubmFtZS50ZXh0KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGEgbmFtZWQgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9uICh0eXBlIGFsaWFzLCBjbGFzcywgb3Jcblx0ICogaW50ZXJmYWNlKSBmb3IgdGhlIGZpbGUgY3VycmVudGx5IGJlaW5nIHZpc2l0ZWQuXG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdC8vIE5hbWVzcGFjZXMgYXJlIHRoZSBtaWRkbGUgc2VnbWVudHMgb2YgcXVhbGlmaWVkIHJlZmVyZW5jZXNcblx0XHQvLyAobW9kZWxzLklubmVyLkNyYXRlKSDigJQgcmVjb3JkZWQgc2VwYXJhdGVseSBmcm9tIHRoZSBwbGFpbi1uYW1lXG5cdFx0Ly8gZGVjbGFyYXRpb24gdGFibGUgKHN0cmluZy1uYW1lZCBgbW9kdWxlICfigKYnYCBkZWNsYXJhdGlvbnMgYXJlXG5cdFx0Ly8gYW1iaWVudCBleHRlcm5hbHMgYW5kIHN0YXkgb3V0KVxuXHRcdGlmICh0cy5pc01vZHVsZURlY2xhcmF0aW9uKG5vZGUpICYmIHRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpICYmXG5cdFx0XHRub2RlLmJvZHkgJiYgdHMuaXNNb2R1bGVCbG9jayhub2RlLmJvZHkpKSB7XG5cdFx0XHRjb25zdCBuYW1lc3BhY2VGaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRcdGxldCBuYW1lc3BhY2VzID0gdGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMuZ2V0KG5hbWVzcGFjZUZpbGVQYXRoKTtcblx0XHRcdGlmICghbmFtZXNwYWNlcykge1xuXHRcdFx0XHRuYW1lc3BhY2VzID0gbmV3IE1hcDxzdHJpbmcsIHRzLk1vZHVsZURlY2xhcmF0aW9uPigpO1xuXHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlcy5zZXQobmFtZXNwYWNlRmlsZVBhdGgsIG5hbWVzcGFjZXMpO1xuXHRcdFx0fVxuXHRcdFx0bmFtZXNwYWNlcy5zZXQobm9kZS5uYW1lLnRleHQsIG5vZGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGxldCBuYW1lID0gJyc7XG5cdFx0bGV0IGtpbmQ6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25bJ2tpbmQnXSB8IHVuZGVmaW5lZDtcblx0XHRsZXQgZGVjbE5vZGU6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25bJ25vZGUnXSB8IHVuZGVmaW5lZDtcblxuXHRcdGlmICh0cy5pc1R5cGVBbGlhc0RlY2xhcmF0aW9uKG5vZGUpICYmIHRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpKSB7XG5cdFx0XHRuYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0XHRraW5kID0gJ2FsaWFzJztcblx0XHRcdGRlY2xOb2RlID0gbm9kZTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdG5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRcdGtpbmQgPSAnY2xhc3MnO1xuXHRcdFx0ZGVjbE5vZGUgPSBub2RlO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNJbnRlcmZhY2VEZWNsYXJhdGlvbihub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSkge1xuXHRcdFx0bmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0a2luZCA9ICdpbnRlcmZhY2UnO1xuXHRcdFx0ZGVjbE5vZGUgPSBub2RlO1xuXHRcdH1cblxuXHRcdGlmICgha2luZCB8fCAhZGVjbE5vZGUgfHwgIW5hbWUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRsZXQgZGVjbHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRGVjbHMuZ2V0KGZpbGVQYXRoKTtcblx0XHRpZiAoIWRlY2xzKSB7XG5cdFx0XHRkZWNscyA9IG5ldyBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uPigpO1xuXHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLnNldChmaWxlUGF0aCwgZGVjbHMpO1xuXHRcdH1cblx0XHRjb25zdCBlbnRyeTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiA9IHsga2luZCwgbm9kZSA6IGRlY2xOb2RlLCBmaWxlIDogZmlsZVBhdGggfTtcblx0XHRkZWNscy5zZXQobmFtZSwgZW50cnkpO1xuXG5cdFx0Ly8gYGV4cG9ydCBkZWZhdWx0IGNsYXNzIEZvbyB7fWAgaXMgYWxzbyByZWFjaGFibGUgdW5kZXIgdGhlICdkZWZhdWx0J1xuXHRcdC8vIGJpbmRpbmcgZm9yIGRlZmF1bHQgaW1wb3J0ZXJzXG5cdFx0aWYgKGtpbmQgPT09ICdjbGFzcycpIHtcblx0XHRcdGNvbnN0IGNsYXNzTm9kZSA9IGRlY2xOb2RlIGFzIHRzLkNsYXNzRGVjbGFyYXRpb247XG5cdFx0XHRjb25zdCBpc0V4cG9ydGVkID0gY2xhc3NOb2RlLm1vZGlmaWVycz8uc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FeHBvcnRLZXl3b3JkKSA/PyBmYWxzZTtcblx0XHRcdGNvbnN0IGlzRGVmYXVsdCA9IGNsYXNzTm9kZS5tb2RpZmllcnM/LnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRGVmYXVsdEtleXdvcmQpID8/IGZhbHNlO1xuXHRcdFx0aWYgKGlzRXhwb3J0ZWQgJiYgaXNEZWZhdWx0KSB7XG5cdFx0XHRcdGRlY2xzLnNldCgnZGVmYXVsdCcsIGVudHJ5KTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGNvbnN0cyBpbml0aWFsaXplZCB3aXRoIGFuIGFycmF5IGxpdGVyYWwgKG9wdGlvbmFsbHkgd3JhcHBlZCBpblxuXHQgKiBgYXMgY29uc3RgIC8gYHNhdGlzZmllc2ApLCBzbyBhIGB0eXBlb2Ygc3RhdHVzTGlzdFtudW1iZXJdYCBmaWVsZCB0eXBlXG5cdCAqIGV4cGFuZHMgdG8gdGhlIGVsZW1lbnQgbGl0ZXJhbCB1bmlvbiDigJQgdGhlIGdlbmVyYXRlZCBmaWxlIGNhcnJpZXMgbm9cblx0ICogaW1wb3J0cywgc28gZW1pdHRpbmcgdGhlIGJhcmUgYHR5cGVvZiBzdGF0dXNMaXN0YCBxdWVyeSB3b3VsZCBiZSBhblxuXHQgKiB1bnJlc29sdmFibGUgbmFtZSBkb3duc3RyZWFtLiBGaXJzdCBiaW5kaW5nIHdpbnM6IGEgbmVzdGVkIHNoYWRvd1xuXHQgKiBtdXN0IG5vdCByZXBsYWNlIHRoZSBtb2R1bGUtbGV2ZWwgY29uc3QgdGhlIHR5cGVvZiByZWZlcnMgdG8uXG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrUmVmZXJlbmNlZFR5cGVDb25zdEFycmF5IChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgfHwgIXRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpIHx8ICFub2RlLmluaXRpYWxpemVyKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHsgaW5pdGlhbGl6ZXI6IHJhd0luaXRpYWxpemVyIH0gPSBub2RlO1xuXHRcdGxldCBpbml0aWFsaXplcjogdHMuRXhwcmVzc2lvbiA9IHJhd0luaXRpYWxpemVyO1xuXHRcdHdoaWxlIChcblx0XHRcdHRzLmlzQXNFeHByZXNzaW9uKGluaXRpYWxpemVyKSB8fFxuXHRcdFx0dHMuaXNTYXRpc2ZpZXNFeHByZXNzaW9uKGluaXRpYWxpemVyKSB8fFxuXHRcdFx0Ly8gdGhlIGFuZ2xlLWJyYWNrZXQgYXNzZXJ0aW9uIHNwZWxsaW5nIChgPGNvbnN0PlvigKZdYCkgaXMgdGhlXG5cdFx0XHQvLyBzYW1lIGNvbnN0LWFycmF5IG1hcmtlciBhcyB0aGUgYGFzIGNvbnN0YCBmb3JtIChGMTcpXG5cdFx0XHR0cy5pc1R5cGVBc3NlcnRpb25FeHByZXNzaW9uKGluaXRpYWxpemVyKVxuXHRcdCkge1xuXHRcdFx0aW5pdGlhbGl6ZXIgPSBpbml0aWFsaXplci5leHByZXNzaW9uO1xuXHRcdH1cblx0XHRpZiAoIXRzLmlzQXJyYXlMaXRlcmFsRXhwcmVzc2lvbihpbml0aWFsaXplcikpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0bGV0IGNvbnN0cyA9IHRoaXMucmVmZXJlbmNlZFR5cGVDb25zdEFycmF5cy5nZXQoZmlsZVBhdGgpO1xuXHRcdGlmICghY29uc3RzKSB7XG5cdFx0XHRjb25zdHMgPSBuZXcgTWFwPHN0cmluZywgdHMuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbj4oKTtcblx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVDb25zdEFycmF5cy5zZXQoZmlsZVBhdGgsIGNvbnN0cyk7XG5cdFx0fVxuXHRcdGlmICghY29uc3RzLmhhcyhub2RlLm5hbWUudGV4dCkpIHtcblx0XHRcdGNvbnN0cy5zZXQobm9kZS5uYW1lLnRleHQsIGluaXRpYWxpemVyKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRmluZCB0aGUgYXJyYXkgbGl0ZXJhbCBiZWhpbmQgYSBtb2R1bGUgY29uc3QgcmVmZXJlbmNlZCB0aHJvdWdoXG5cdCAqIGB0eXBlb2ZgOiB0aGUgZGVjbGFyaW5nIGZpbGUncyBvd24gY29uc3RzIGZpcnN0ICh0aGUgRjEzIGNhc2UgaXMgYVxuXHQgKiBOT04tZXhwb3J0ZWQgY29uc3QgaW4gdGhlIHNhbWUgbW9kdWxlIGFzIHRoZSBleHBhbmRlZCBjbGFzcyksIHRoZW4g4oCUXG5cdCAqIHdoZW4gdGhlIGZpbGUgaW1wb3J0cyB0aGUgbmFtZSDigJQgdGhlIGltcG9ydGVkIG1vZHVsZSdzIGNvbnN0cy5cblx0ICogRXh0ZXJuYWwgbW9kdWxlcyBhcmUgbmV2ZXIgYW5hbHl6ZWQsIHNvIHRob3NlIHlpZWxkIG5vdGhpbmcuXG5cdCAqL1xuXHRwcml2YXRlIGZpbmRSZWZlcmVuY2VkQ29uc3RBcnJheSAoXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdGZyb21GaWxlOiBzdHJpbmdcblx0KTogdHMuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgbG9jYWwgPSB0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuZ2V0KGZyb21GaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChsb2NhbCkge1xuXHRcdFx0cmV0dXJuIGxvY2FsO1xuXHRcdH1cblx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldChmcm9tRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAoIWltcG9ydGVkIHx8IGltcG9ydGVkLmlzTmFtZXNwYWNlKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoaW1wb3J0ZWQuc3BlY2lmaWVyLCBmcm9tRmlsZSk7XG5cdFx0aWYgKCFyZXNvbHV0aW9uIHx8IHJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgZm91bmQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuZ2V0KHJlc29sdXRpb24ucmVzb2x2ZWRQYXRoKT8uZ2V0KGltcG9ydGVkLm9yaWdpbmFsTmFtZSk7XG5cdFx0cmV0dXJuIGZvdW5kO1xuXHR9XG5cblx0LyoqXG5cdCAqIEVsZW1lbnQgbGl0ZXJhbCB0eXBlcyBvZiBhIHRyYWNrZWQgY29uc3QgYXJyYXk6IGV2ZXJ5IGVsZW1lbnQgbXVzdCBiZVxuXHQgKiBhIHBsYWluIGxpdGVyYWwgKG9wdGlvbmFsbHkgd3JhcHBlZCBpbiBgYXMgY29uc3RgIC8gYHNhdGlzZmllc2AgL1xuXHQgKiBgPGNvbnN0PmAgYXNzZXJ0aW9ucykg4oCUIHN0cmluZywgbnVtZXJpYyAodW5hcnkgYC1gL2ArYCBwcmVzZXJ2ZWQpLFxuXHQgKiBib29sZWFuLCBvciBudWxsLiBTcHJlYWRzLCBpZGVudGlmaWVycywgYW5kIG5lc3RlZCBhcnJheXMgbWVhbiB0aGVcblx0ICogdW5pb24gaXMgbm90IHN0YXRpY2FsbHkgdmlzaWJsZSBhbmQgeWllbGQgdW5kZWZpbmVkLCBzbyB0aGUgY2FsbGVyXG5cdCAqIGRlZ3JhZGVzIHRoZSBmaWVsZCB0byBgdW5rbm93bmAgcmF0aGVyIHRoYW4gZ3Vlc3NpbmcuXG5cdCAqL1xuXHRwcml2YXRlIGxpdGVyYWxUeXBlc09mQXJyYXkgKGFycmF5TGl0ZXJhbDogdHMuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbik6IHN0cmluZ1tdIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBsaXRlcmFsczogc3RyaW5nW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2YgYXJyYXlMaXRlcmFsLmVsZW1lbnRzKSB7XG5cdFx0XHRpZiAodHMuaXNTcHJlYWRFbGVtZW50KGVsZW1lbnQpKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBsaXRlcmFsID0gdGhpcy5saXRlcmFsVHlwZU9mRXhwcmVzc2lvbihlbGVtZW50KTtcblx0XHRcdGlmIChsaXRlcmFsID09PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGxpdGVyYWxzLnB1c2gobGl0ZXJhbCk7XG5cdFx0fVxuXHRcdGlmIChsaXRlcmFscy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGxpdGVyYWxzO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogVGhlIGxpdGVyYWwgdHlwZSBvZiBvbmUgYXJyYXkgZWxlbWVudDogYSBwbGFpbiBsaXRlcmFsIChvcHRpb25hbGx5XG5cdCAqIHdyYXBwZWQgaW4gYGFzIGNvbnN0YCAvIGBzYXRpc2ZpZXNgIC8gYXNzZXJ0aW9uIGV4cHJlc3Npb25zKSDigJRcblx0ICogc3RyaW5nLCBudW1lcmljICh1bmFyeSBgLWAvYCtgIHByZXNlcnZlZCksIGJvb2xlYW4sIG9yIG51bGwuXG5cdCAqIEFueXRoaW5nIGVsc2UgeWllbGRzIHVuZGVmaW5lZC5cblx0ICovXG5cdHByaXZhdGUgbGl0ZXJhbFR5cGVPZkV4cHJlc3Npb24gKGV4cHI6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBpbm5lcjogdHMuRXhwcmVzc2lvbiA9IGV4cHI7XG5cdFx0d2hpbGUgKHRzLmlzQXNFeHByZXNzaW9uKGlubmVyKSB8fCB0cy5pc1NhdGlzZmllc0V4cHJlc3Npb24oaW5uZXIpIHx8IHRzLmlzVHlwZUFzc2VydGlvbkV4cHJlc3Npb24oaW5uZXIpKSB7XG5cdFx0XHRpbm5lciA9IGlubmVyLmV4cHJlc3Npb247XG5cdFx0fVxuXHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoaW5uZXIpIHx8IHRzLmlzTm9TdWJzdGl0dXRpb25UZW1wbGF0ZUxpdGVyYWwoaW5uZXIpKSB7XG5cdFx0XHRjb25zdCBsaXRlcmFsID0gYCcke2lubmVyLnRleHR9J2A7XG5cdFx0XHRyZXR1cm4gbGl0ZXJhbDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJlZml4VW5hcnlFeHByZXNzaW9uKGlubmVyKSAmJiB0cy5pc051bWVyaWNMaXRlcmFsKGlubmVyLm9wZXJhbmQpKSB7XG5cdFx0XHRpZiAoaW5uZXIub3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuTWludXNUb2tlbikge1xuXHRcdFx0XHRjb25zdCBuZWdhdGl2ZSA9IGAtJHtpbm5lci5vcGVyYW5kLnRleHR9YDtcblx0XHRcdFx0cmV0dXJuIG5lZ2F0aXZlO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGlubmVyLm9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLlBsdXNUb2tlbikge1xuXHRcdFx0XHRyZXR1cm4gaW5uZXIub3BlcmFuZC50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzTnVtZXJpY0xpdGVyYWwoaW5uZXIpKSB7XG5cdFx0XHRyZXR1cm4gaW5uZXIudGV4dDtcblx0XHR9XG5cdFx0aWYgKGlubmVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVHJ1ZUtleXdvcmQpIHtcblx0XHRcdHJldHVybiAndHJ1ZSc7XG5cdFx0fVxuXHRcdGlmIChpbm5lci5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0cmV0dXJuICdmYWxzZSc7XG5cdFx0fVxuXHRcdGlmIChpbm5lci5raW5kID09PSB0cy5TeW50YXhLaW5kLk51bGxLZXl3b3JkKSB7XG5cdFx0XHRyZXR1cm4gJ251bGwnO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEYyMjogdGhlIGNvbnN0LWFzc2VydGlvbiBjaGVjayBzaGFyZWQgYnkgdGhlIHZhbHVlLWxldmVsIGFuZFxuXHQgKiBkZWNsYXJhdGlvbi1sZXZlbCBwYXRocyDigJQgYGV4cHIgYXMgY29uc3RgIGFuZCBgPGNvbnN0PmV4cHJgIHBhcnNlXG5cdCAqIGlkZW50aWNhbGx5IChhIFR5cGVSZWZlcmVuY2VOb2RlIG5hbWVkICdjb25zdCcpLiBHZW5lcmFsIGA8VD5leHByYFxuXHQgKiBhc3NlcnRpb25zIG5ldmVyIG1hdGNoLlxuXHQgKi9cblx0cHJpdmF0ZSBpc0NvbnN0QXNzZXJ0aW9uVHlwZSAodHlwZTogdHMuVHlwZU5vZGUpOiBib29sZWFuIHtcblx0XHRjb25zdCBjb25zdEFzc2VydGlvbiA9IHRzLmlzVHlwZVJlZmVyZW5jZU5vZGUodHlwZSkgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcih0eXBlLnR5cGVOYW1lKSAmJlxuXHRcdFx0dHlwZS50eXBlTmFtZS50ZXh0ID09PSAnY29uc3QnO1xuXHRcdHJldHVybiBjb25zdEFzc2VydGlvbjtcblx0fVxuXG5cdC8qKlxuXHQgKiBUaGUgYXJyYXkgbGl0ZXJhbCBiZWhpbmQgYSB2YWx1ZS1sZXZlbCBlbGVtZW50IGFjY2VzczogaW5saW5lXG5cdCAqIChgKDxjb25zdD5b4oCmXSlbMF1gLCBgKFvigKZdIGFzIGNvbnN0KVsxXWApLCBwYXJlbnRoZXNpemVkLCBvciBhXG5cdCAqIHRyYWNrZWQgbW9kdWxlIGNvbnN0IGFycmF5IChgY29uc3QgeCA9IDxjb25zdD5b4oCmXWAgLyBgeFswXWAsIEYxN1xuXHQgKiB0cmFja2luZykuIE9ubHkgY29uc3QgYXNzZXJ0aW9ucyBhcmUgdW53cmFwcGVkIOKAlCBnZW5lcmFsXG5cdCAqIGFzc2VydGlvbnMgc3RheSB1bmtub3duIChGMjIgc2NvcGUgYm91bmRhcnkpLlxuXHQgKi9cblx0cHJpdmF0ZSBjb25zdEFycmF5TGl0ZXJhbE9mIChleHByOiB0cy5FeHByZXNzaW9uKTogdHMuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLkV4cHJlc3Npb24gPSBleHByO1xuXHRcdHdoaWxlICh0cy5pc1BhcmVudGhlc2l6ZWRFeHByZXNzaW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5leHByZXNzaW9uO1xuXHRcdH1cblx0XHRpZiAodHMuaXNBcnJheUxpdGVyYWxFeHByZXNzaW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRyZXR1cm4gY3VycmVudDtcblx0XHR9XG5cdFx0aWYgKCh0cy5pc0FzRXhwcmVzc2lvbihjdXJyZW50KSB8fCB0cy5pc1R5cGVBc3NlcnRpb25FeHByZXNzaW9uKGN1cnJlbnQpKSAmJlxuXHRcdFx0dGhpcy5pc0NvbnN0QXNzZXJ0aW9uVHlwZShjdXJyZW50LnR5cGUpKSB7XG5cdFx0XHRjb25zdCBpbm5lciA9IGN1cnJlbnQuZXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IGxpdGVyYWwgPSB0cy5pc0FycmF5TGl0ZXJhbEV4cHJlc3Npb24oaW5uZXIpID8gaW5uZXIgOiB1bmRlZmluZWQ7XG5cdFx0XHRyZXR1cm4gbGl0ZXJhbDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50KSkge1xuXHRcdFx0Y29uc3QgdHJhY2tlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVDb25zdEFycmF5cy5nZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKT8uZ2V0KGN1cnJlbnQudGV4dCk7XG5cdFx0XHRyZXR1cm4gdHJhY2tlZDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFbWl0LXR5cGUgZm9yIGB0eXBlb2YgbmFtZWAgd2hlbiBgbmFtZWAgaXMgYSB0cmFja2VkIGNvbnN0IGFycmF5OiB0aGVcblx0ICogdW5pb24gb2YgaXRzIGVsZW1lbnQgbGl0ZXJhbCB0eXBlcyAoYCdhY3RpdmUnIHwgJ2Nsb3NlZCdgKS4gRXZlcnlcblx0ICogb3RoZXIgdHlwZW9mIHNvdXJjZSDigJQgbm9uLWFycmF5IGNvbnN0cywgZnVuY3Rpb25zLCBjbGFzc2VzLCBuYW1lcyBub3Rcblx0ICogdHJhY2tlZCBhdCBhbGwg4oCUIHlpZWxkcyB1bmRlZmluZWQsIHNvIHRoZSBjYWxsZXIgZGVncmFkZXMgdGhlIGZpZWxkXG5cdCAqIHRvIGB1bmtub3duYDogYSBiYXJlIGB0eXBlb2YgbmFtZWAgZW1pdHRlZCBpbnRvIHR5cGVzLnRzIGhhcyBub1xuXHQgKiBpbXBvcnQgdG8gcmVzb2x2ZSBhZ2FpbnN0IGRvd25zdHJlYW0uXG5cdCAqL1xuXHRwcml2YXRlIHR5cGVPZkNvbnN0QXJyYXlVbmlvbiAobmFtZTogc3RyaW5nLCBmcm9tRmlsZTogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBhcnJheUxpdGVyYWwgPSB0aGlzLmZpbmRSZWZlcmVuY2VkQ29uc3RBcnJheShuYW1lLCBmcm9tRmlsZSk7XG5cdFx0aWYgKCFhcnJheUxpdGVyYWwpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGxpdGVyYWxzID0gdGhpcy5saXRlcmFsVHlwZXNPZkFycmF5KGFycmF5TGl0ZXJhbCk7XG5cdFx0aWYgKCFsaXRlcmFscykge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgdW5pb24gPSBsaXRlcmFscy5qb2luKCcgfCAnKTtcblx0XHRyZXR1cm4gdW5pb247XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIHRoZSBpbXBvcnRpbmcgZmlsZSdzIG5hbWVkL25hbWVzcGFjZS9kZWZhdWx0IGltcG9ydCBiaW5kaW5ncyBzb1xuXHQgKiByZWZlcmVuY2VkLXR5cGUgbmFtZXMgcmVzb2x2ZSB0aHJvdWdoIHRoZSBmaWxlJ3Mgb3duIGltcG9ydCBzdGF0ZW1lbnRzXG5cdCAqIChGMTApIHJhdGhlciB0aGFuIGEgcHJvZ3JhbS13aWRlIG5hbWUgbWFwLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlSW1wb3J0IChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc0ltcG9ydERlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHsgbW9kdWxlU3BlY2lmaWVyIH0gPSBub2RlO1xuXHRcdGlmICghdHMuaXNTdHJpbmdMaXRlcmFsKG1vZHVsZVNwZWNpZmllcikpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgY2xhdXNlID0gbm9kZS5pbXBvcnRDbGF1c2U7XG5cdFx0aWYgKCFjbGF1c2UpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRsZXQgaW1wb3J0cyA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldChmaWxlUGF0aCk7XG5cdFx0aWYgKCFpbXBvcnRzKSB7XG5cdFx0XHRpbXBvcnRzID0gbmV3IE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlSW1wb3J0PigpO1xuXHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuc2V0KGZpbGVQYXRoLCBpbXBvcnRzKTtcblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgeyBTaGFyZWRTaGFwZSB9IGZyb20gJ+KApicgLyBpbXBvcnQgeyBTaGFyZWRTaGFwZSBhcyBTIH0gZnJvbSAn4oCmJ1xuXHRcdGlmIChjbGF1c2UubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVkSW1wb3J0cyhjbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBjbGF1c2UubmFtZWRCaW5kaW5ncy5lbGVtZW50cykge1xuXHRcdFx0XHRjb25zdCBsb2NhbE5hbWUgPSBlbGVtZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3Qgb3JpZ2luYWxOYW1lID0gZWxlbWVudC5wcm9wZXJ0eU5hbWUgPyBlbGVtZW50LnByb3BlcnR5TmFtZS50ZXh0IDogbG9jYWxOYW1lO1xuXHRcdFx0XHRpbXBvcnRzLnNldChsb2NhbE5hbWUsIHtcblx0XHRcdFx0XHRvcmlnaW5hbE5hbWUsXG5cdFx0XHRcdFx0c3BlY2lmaWVyICAgOiBtb2R1bGVTcGVjaWZpZXIudGV4dCxcblx0XHRcdFx0XHRpc05hbWVzcGFjZSA6IGZhbHNlXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIGltcG9ydCAqIGFzIG1vZGVscyBmcm9tICfigKYnIOKAlCByZXNvbHZlZCB3aGVuIGEgcXVhbGlmaWVkIG5hbWVcblx0XHQvLyAobW9kZWxzLlNoYXJlZFNoYXBlKSBpcyBlbmNvdW50ZXJlZFxuXHRcdGlmIChjbGF1c2UubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVzcGFjZUltcG9ydChjbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdGltcG9ydHMuc2V0KGNsYXVzZS5uYW1lZEJpbmRpbmdzLm5hbWUudGV4dCwge1xuXHRcdFx0XHRvcmlnaW5hbE5hbWUgOiAnJyxcblx0XHRcdFx0c3BlY2lmaWVyICAgIDogbW9kdWxlU3BlY2lmaWVyLnRleHQsXG5cdFx0XHRcdGlzTmFtZXNwYWNlICA6IHRydWVcblx0XHRcdH0pO1xuXHRcdH1cblxuXHRcdC8vIGltcG9ydCBTaGFyZWRTaGFwZSBmcm9tICfigKYnIChkZWZhdWx0IGltcG9ydClcblx0XHRpZiAoY2xhdXNlLm5hbWUpIHtcblx0XHRcdGltcG9ydHMuc2V0KGNsYXVzZS5uYW1lLnRleHQsIHtcblx0XHRcdFx0b3JpZ2luYWxOYW1lIDogJ2RlZmF1bHQnLFxuXHRcdFx0XHRzcGVjaWZpZXIgICAgOiBtb2R1bGVTcGVjaWZpZXIudGV4dCxcblx0XHRcdFx0aXNOYW1lc3BhY2UgIDogZmFsc2Vcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgcmUtZXhwb3J0IHdpcmluZyAoYGV4cG9ydCB7IFggfSBmcm9tICfigKYnYCwgYGV4cG9ydCAqIGZyb20gJ+KApidgLFxuXHQgKiBgZXhwb3J0IHsgWCBhcyBZIH1gKSBzbyByZXNvbHV0aW9uIGNhbiBjaGFzZSBiYXJyZWxzIHRvIHRoZSBvcmlnaW5cblx0ICogbW9kdWxlLiBNaXJyb3JzIE1vZHVsZUdyYXBoQnVpbGRlci5yZXNvbHZlT3JpZ2luLCBuYW1lLWJhc2VkIG9ubHkuXG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrUmVmZXJlbmNlZFR5cGVSZUV4cG9ydCAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNFeHBvcnREZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRjb25zdCB7IG1vZHVsZVNwZWNpZmllciB9ID0gbm9kZTtcblx0XHRjb25zdCBzcGVjaWZpZXJUZXh0ID0gbW9kdWxlU3BlY2lmaWVyICYmIHRzLmlzU3RyaW5nTGl0ZXJhbChtb2R1bGVTcGVjaWZpZXIpXG5cdFx0XHQ/IG1vZHVsZVNwZWNpZmllci50ZXh0XG5cdFx0XHQ6IHVuZGVmaW5lZDtcblxuXHRcdGlmIChub2RlLmV4cG9ydENsYXVzZSAmJiB0cy5pc05hbWVkRXhwb3J0cyhub2RlLmV4cG9ydENsYXVzZSkpIHtcblx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBub2RlLmV4cG9ydENsYXVzZS5lbGVtZW50cykge1xuXHRcdFx0XHRjb25zdCBleHBvcnRlZE5hbWUgPSBlbGVtZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgbG9jYWxOYW1lID0gZWxlbWVudC5wcm9wZXJ0eU5hbWUgPyBlbGVtZW50LnByb3BlcnR5TmFtZS50ZXh0IDogZXhwb3J0ZWROYW1lO1xuXHRcdFx0XHRpZiAoc3BlY2lmaWVyVGV4dCkge1xuXHRcdFx0XHRcdC8vIGV4cG9ydCB7IFggfSBmcm9tICfigKYnIC8gZXhwb3J0IHsgWCBhcyBZIH0gZnJvbSAn4oCmJ1xuXHRcdFx0XHRcdGxldCByZUV4cG9ydHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLmdldChmaWxlUGF0aCk7XG5cdFx0XHRcdFx0aWYgKCFyZUV4cG9ydHMpIHtcblx0XHRcdFx0XHRcdHJlRXhwb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLnNldChmaWxlUGF0aCwgcmVFeHBvcnRzKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0cmVFeHBvcnRzLnNldChleHBvcnRlZE5hbWUsIHNwZWNpZmllclRleHQpO1xuXHRcdFx0XHR9IGVsc2UgaWYgKGxvY2FsTmFtZSAhPT0gZXhwb3J0ZWROYW1lKSB7XG5cdFx0XHRcdFx0Ly8gZXhwb3J0IHsgWCBhcyBZIH0g4oCUIHNhbWUtZmlsZSBhbGlhcyBvZiBhIGxvY2FsIGRlY2xhcmF0aW9uXG5cdFx0XHRcdFx0bGV0IGFsaWFzZXMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0XHRcdGlmICghYWxpYXNlcykge1xuXHRcdFx0XHRcdFx0YWxpYXNlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcy5zZXQoZmlsZVBhdGgsIGFsaWFzZXMpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRhbGlhc2VzLnNldChleHBvcnRlZE5hbWUsIGxvY2FsTmFtZSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAobm9kZS5leHBvcnRDbGF1c2UgJiYgdHMuaXNOYW1lc3BhY2VFeHBvcnQobm9kZS5leHBvcnRDbGF1c2UpKSB7XG5cdFx0XHQvLyBgZXhwb3J0ICogYXMgbnMgZnJvbSAn4oCmJ2Ag4oCUIGEgbmVzdGVkIG1vZHVsZSBuYW1lc3BhY2U7IG1pZGRsZVxuXHRcdFx0Ly8gc2VnbWVudHMgb2YgcXVhbGlmaWVkIHJlZmVyZW5jZXMgKGJhcnJlbC5EZWVwLkdhZGdldCkgY2hhc2UgaXRcblx0XHRcdGlmIChzcGVjaWZpZXJUZXh0KSB7XG5cdFx0XHRcdGxldCBzdGFycyA9IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VTdGFycy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0XHRpZiAoIXN0YXJzKSB7XG5cdFx0XHRcdFx0c3RhcnMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VTdGFycy5zZXQoZmlsZVBhdGgsIHN0YXJzKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRzdGFycy5zZXQobm9kZS5leHBvcnRDbGF1c2UubmFtZS50ZXh0LCBzcGVjaWZpZXJUZXh0KTtcblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAoIW5vZGUuZXhwb3J0Q2xhdXNlICYmIHNwZWNpZmllclRleHQpIHtcblx0XHRcdC8vIGV4cG9ydCAqIGZyb20gJ+KApidcblx0XHRcdGxldCBzdGFycyA9IHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0aWYgKCFzdGFycykge1xuXHRcdFx0XHRzdGFycyA9IFtdO1xuXHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuc2V0KGZpbGVQYXRoLCBzdGFycyk7XG5cdFx0XHR9XG5cdFx0XHRzdGFycy5wdXNoKHNwZWNpZmllclRleHQpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgbW9kdWxlIHNwZWNpZmllciBmcm9tIGEgY29udGFpbmluZyBmaWxlIHdpdGggdGhlIHByb2dyYW0nc1xuXHQgKiBjb21waWxlck9wdGlvbnMgKHRzY29uZmlnIGBwYXRoc2AsIGV4dGVuc2lvbmxlc3MgaW1wb3J0cywgaW5kZXggZmlsZXMpLlxuXHQgKiBNb2R1bGUgcmVzb2x1dGlvbiBvbmx5IOKAlCB0aGUgbm8tZ2V0VHlwZUNoZWNrZXIoKSBwcmVjZWRlbnQgc3RheXMuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZSAoc3BlY2lmaWVyOiBzdHJpbmcsIGNvbnRhaW5pbmdGaWxlOiBzdHJpbmcpOlxuXHRcdFJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2FjaGVLZXkgPSBgJHtjb250YWluaW5nRmlsZX06OiR7c3BlY2lmaWVyfWA7XG5cdFx0aWYgKHRoaXMucmVmZXJlbmNlZFR5cGVSZXNvbHV0aW9uQ2FjaGUuaGFzKGNhY2hlS2V5KSkge1xuXHRcdFx0Y29uc3QgY2FjaGVkID0gdGhpcy5yZWZlcmVuY2VkVHlwZVJlc29sdXRpb25DYWNoZS5nZXQoY2FjaGVLZXkpO1xuXHRcdFx0cmV0dXJuIGNhY2hlZCA9PT0gdW5kZWZpbmVkID8gdW5kZWZpbmVkIDogY2FjaGVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlc29sdXRpb24gPSB0cy5yZXNvbHZlTW9kdWxlTmFtZShcblx0XHRcdHNwZWNpZmllcixcblx0XHRcdGNvbnRhaW5pbmdGaWxlLFxuXHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUNvbXBpbGVyT3B0aW9ucyxcblx0XHRcdHRzLnN5c1xuXHRcdCkucmVzb2x2ZWRNb2R1bGU7XG5cblx0XHRjb25zdCByZXN1bHQ6IFJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbiB8IHVuZGVmaW5lZCA9IHJlc29sdXRpb25cblx0XHRcdD8ge1xuXHRcdFx0XHRyZXNvbHZlZFBhdGggOiBub2RlUGF0aC5yZXNvbHZlKHJlc29sdXRpb24ucmVzb2x2ZWRGaWxlTmFtZSksXG5cdFx0XHRcdGlzRXh0ZXJuYWwgICA6ICEhcmVzb2x1dGlvbi5pc0V4dGVybmFsTGlicmFyeUltcG9ydFxuXHRcdFx0fVxuXHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbkNhY2hlLnNldChjYWNoZUtleSwgcmVzdWx0KTtcblx0XHRjb25zdCBmaW5hbFJlc3VsdCA9IHJlc3VsdDtcblx0XHRyZXR1cm4gZmluYWxSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogTG9vayB1cCBhIG5hbWUgaW4gb25lIHJlc29sdmVkIG1vZHVsZSwgY2hhc2luZyByZS1leHBvcnQgYmFycmVscyB3aXRoIGFcblx0ICogYm91bmRlZCBkZXB0aC4gRXh0ZXJuYWwgKG5vZGVfbW9kdWxlcykgbW9kdWxlcyBob2xkIG5vIGluLXByb2plY3Rcblx0ICogZGVjbGFyYXRpb25zIGFuZCBzdG9wIHRoZSBjaGFzZS5cblx0ICovXG5cdHByaXZhdGUgZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUgKFxuXHRcdG1vZHVsZVBhdGg6IHN0cmluZyxcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0ZGVwdGg6IG51bWJlclxuXHQpOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoZGVwdGggPiBNQVhfUkVFWFBPUlRfQ0hBU0VfREVQVEgpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGVjbHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRGVjbHMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGNvbnN0IGRpcmVjdCA9IGRlY2xzPy5nZXQobmFtZSk7XG5cdFx0aWYgKGRpcmVjdCkge1xuXHRcdFx0cmV0dXJuIGRpcmVjdDtcblx0XHR9XG5cdFx0Ly8gZXhwb3J0IHsgWCBhcyBZIH0g4oCUIHJlc29sdmUgdGhyb3VnaCB0aGUgbG9jYWwgbmFtZVxuXHRcdGNvbnN0IGxvY2FsQWxpYXMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcy5nZXQobW9kdWxlUGF0aCk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWxBbGlhcykge1xuXHRcdFx0Y29uc3QgYWxpYXNlZCA9IGRlY2xzPy5nZXQobG9jYWxBbGlhcyk7XG5cdFx0XHRpZiAoYWxpYXNlZCkge1xuXHRcdFx0XHRyZXR1cm4gYWxpYXNlZDtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCByZUV4cG9ydHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLmdldChtb2R1bGVQYXRoKTtcblx0XHRjb25zdCByZUV4cG9ydFNwZWNpZmllciA9IHJlRXhwb3J0cz8uZ2V0KG5hbWUpO1xuXHRcdGlmIChyZUV4cG9ydFNwZWNpZmllcikge1xuXHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShyZUV4cG9ydFNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRpZiAobmV4dFJlc29sdXRpb24gJiYgIW5leHRSZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgbmFtZSwgZGVwdGggKyAxKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGlmIChzdGFycykge1xuXHRcdFx0Zm9yIChjb25zdCBzdGFyU3BlY2lmaWVyIG9mIHN0YXJzKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoc3RhclNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRcdGlmICghbmV4dFJlc29sdXRpb24gfHwgbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZShuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIG5hbWUsIGRlcHRoICsgMSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHJlZmVyZW5jZWQgdHlwZSBuYW1lIGFzIHVzZWQgaW4gZnJvbUZpbGUsIGltcG9ydC1hd2FyZTpcblx0ICogICAxLiB0aGUgZmlsZSdzIG93biBpbXBvcnQgc3RhdGVtZW50cyAocmVsYXRpdmUgKyB0c2NvbmZpZyBwYXRocyxcblx0ICogICAgICBjaGFzZWQgdGhyb3VnaCByZS1leHBvcnQgYmFycmVscyksXG5cdCAqICAgMi4gdGhlIGZpbGUncyBsb2NhbCBkZWNsYXJhdGlvbnMsXG5cdCAqICAgMy4gdGhlIHVuaXF1ZSBzYW1lLW5hbWVkIGRlY2xhcmF0aW9uIGFjcm9zcyBzY2FubmVkIGZpbGVzLlxuXHQgKiBSZXR1cm5zIHVuZGVmaW5lZCB3aGVuIG5vdGhpbmcgbWF0Y2hlcyAob3IgdGhlIG1hdGNoIGlzIGFtYmlndW91cyksXG5cdCAqIGluIHdoaWNoIGNhc2UgdGhlIGNhbGxlciBmYWxscyBiYWNrIHRvIGB1bmtub3duYC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRmcm9tRmlsZTogc3RyaW5nXG5cdCk6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdC8vIDEuIHRoZSBmaWxlJ3Mgb3duIGltcG9ydHMgd2luIOKAlCBhbiBpbXBvcnQgaXMgbmV2ZXIgc2hhZG93ZWQgYnkgYVxuXHRcdC8vIHNhbWUtbmFtZWQgbG9jYWwgZGVjbGFyYXRpb24gZWxzZXdoZXJlIGluIHRoZSBwcm9ncmFtIChGMTApXG5cdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoZnJvbUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGltcG9ydGVkICYmICFpbXBvcnRlZC5pc05hbWVzcGFjZSkge1xuXHRcdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKGltcG9ydGVkLnNwZWNpZmllciwgZnJvbUZpbGUpO1xuXHRcdFx0aWYgKHJlc29sdXRpb24gJiYgIXJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRjb25zdCBmb3VuZCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUocmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIGltcG9ydGVkLm9yaWdpbmFsTmFtZSwgMCk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIDIuIGxvY2FsIGRlY2xhcmF0aW9uIGluIHRoZSByZWZlcmVuY2luZyBmaWxlIGl0c2VsZlxuXHRcdGNvbnN0IGxvY2FsID0gdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLmdldChmcm9tRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWwpIHtcblx0XHRcdHJldHVybiBsb2NhbDtcblx0XHR9XG5cblx0XHQvLyAzLiBwcm9ncmFtLXdpZGUgZmFsbGJhY2ssIHVuaXF1ZSBkZWNsYXJhdGlvbiBvbmx5IOKAlCBhbWJpZ3VpdHkgYW5kXG5cdFx0Ly8gYWJzZW5jZSBib3RoIHlpZWxkIHVuZGVmaW5lZCAodGhlIGNhbGxlciBlbWl0cyBgdW5rbm93bmApLlxuXHRcdC8vIEV4dGVybmFsL2FtYmllbnQgZGVjbGFyYXRpb25zICguZC50cywgbm9kZV9tb2R1bGVzKSBkbyBub3Rcblx0XHQvLyBwYXJ0aWNpcGF0ZTogYSB1c2VyLWxvY2FsIGRlY2xhcmF0aW9uIGFsd2F5cyB3aW5zIG92ZXIgYVxuXHRcdC8vIHBhY2thZ2UtZGVjbGFyZWQgc2FtZS1uYW1lZCB0eXBlICh0aGUgcGxhaW4tVFMgdGllciBvZiB0aGVcblx0XHQvLyBpZGVudGl0eSBsYXc7IGFtYmlndWl0eSBhbW9uZyB0aGUgcmVtYWluaW5nIGRlY2xhcmF0aW9ucyBpc1xuXHRcdC8vIHZhbGlkYXRlZCBzZXBhcmF0ZWx5IGFzIGEgaGFyZCBmYWlsKVxuXHRcdGxldCB1bmlxdWU6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQ7XG5cdFx0bGV0IGNvdW50ID0gMDtcblx0XHRmb3IgKGNvbnN0IFsgZmlsZVBhdGgsIGRlY2xzIF0gb2YgdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzKSB7XG5cdFx0XHRpZiAodGhpcy5pc0V4dGVybmFsRGVjbEZpbGUoZmlsZVBhdGgpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgY2FuZGlkYXRlID0gZGVjbHMuZ2V0KG5hbWUpO1xuXHRcdFx0aWYgKGNhbmRpZGF0ZSkge1xuXHRcdFx0XHRjb3VudCsrO1xuXHRcdFx0XHR1bmlxdWUgPSBjYW5kaWRhdGU7XG5cdFx0XHRcdGlmIChjb3VudCA+IDEpIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVzdWx0ID0gY291bnQgPT09IDEgPyB1bmlxdWUgOiB1bmRlZmluZWQ7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRlcm5hbC9hbWJpZW50IGRlY2xhcmF0aW9uIGZpbGVzICguZC50cywgYW55dGhpbmcgdW5kZXJcblx0ICogbm9kZV9tb2R1bGVzKSBuZXZlciBwYXJ0aWNpcGF0ZSBpbiBwbGFpbi1UUyByZWZlcmVuY2VkLXR5cGVcblx0ICogcmVzb2x1dGlvbiBvciB0aGUgYW1iaWd1aXR5IGxhdzogdGhleSBhcmUgbm90IHByb2plY3Qgc291cmNlLCB0aGVcblx0ICogQ0xJIG5ldmVyIGFuYWx5emVzIHRoZW0sIGFuZCBhIHVzZXItbG9jYWwgZGVjbGFyYXRpb24gYWx3YXlzIHdpbnNcblx0ICogb3ZlciBhIHBhY2thZ2UtZGVjbGFyZWQgc2FtZS1uYW1lZCB0eXBlLlxuXHQgKi9cblx0cHJpdmF0ZSBpc0V4dGVybmFsRGVjbEZpbGUgKGZpbGU6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRcdGNvbnN0IGV4dGVybmFsID0gZmlsZS5lbmRzV2l0aCgnLmQudHMnKSB8fFxuXHRcdFx0ZmlsZS5pbmNsdWRlcyhgJHtub2RlUGF0aC5zZXB9bm9kZV9tb2R1bGVzJHtub2RlUGF0aC5zZXB9YCk7XG5cdFx0cmV0dXJuIGV4dGVybmFsO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb3BlcnRpZXMgb2YgYSByZWZlcmVuY2VkIGNsYXNzL2ludGVyZmFjZS9hbGlhcy1vZi1saXRlcmFsIGRlY2xhcmF0aW9uLFxuXHQgKiBzaGFyZWQgYnkgYHRoaXM6YC1wYXJhbWV0ZXIgZXhwYW5zaW9uIGFuZCBpbmxpbmUgdHlwZSBlbWlzc2lvbi5cblx0ICogSW5oZXJpdGVkIG1lbWJlcnMgYXJlIGluY2x1ZGVkOiB0aGUgZXh0ZW5kcyBjaGFpbiBpcyB3YWxrZWRcblx0ICogKGRlcHRoLWNhcHBlZCwgY3ljbGUtZ3VhcmRlZCkgYW5kIHBhcmVudCBmaWVsZHMgbWVyZ2UgZmlyc3QsIHRoZVxuXHQgKiBkZWNsYXJhdGlvbidzIG93biBmaWVsZHMgb3ZlcnJpZGluZyBvbiBuYW1lIGNsYXNoLlxuXHQgKi9cblx0cHJpdmF0ZSByZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzIChkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKTpcblx0XHRNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCB2aXNpdGVkID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllc0lubmVyKGRlY2wsIHZpc2l0ZWQsIDApO1xuXHRcdHJldHVybiBwcm9wZXJ0aWVzO1xuXHR9XG5cblx0cHJpdmF0ZSByZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzSW5uZXIgKFxuXHRcdGRlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24sXG5cdFx0dmlzaXRlZDogU2V0PHN0cmluZz4sXG5cdFx0ZGVwdGg6IG51bWJlclxuXHQpOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCBvd25Qcm9wZXJ0aWVzID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblx0XHRjb25zdCBkZWNsTm9kZSA9IGRlY2wubm9kZSBhcyB0cy5DbGFzc0RlY2xhcmF0aW9uIHwgdHMuSW50ZXJmYWNlRGVjbGFyYXRpb247XG5cdFx0Y29uc3QgZGVjbE5hbWUgPSBkZWNsTm9kZS5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihkZWNsTm9kZS5uYW1lKSA/IGRlY2xOb2RlLm5hbWUudGV4dCA6ICcnO1xuXHRcdGNvbnN0IHZpc2l0S2V5ID0gYCR7ZGVjbC5raW5kfToke2RlY2wuZmlsZX06JHtkZWNsTmFtZX1gO1xuXHRcdGlmIChkZXB0aCA+IE1BWF9IRVJJVEFHRV9ERVBUSCB8fCB2aXNpdGVkLmhhcyh2aXNpdEtleSkpIHtcblx0XHRcdHJldHVybiBvd25Qcm9wZXJ0aWVzO1xuXHRcdH1cblx0XHR2aXNpdGVkLmFkZCh2aXNpdEtleSk7XG5cblx0XHRpZiAoZGVjbC5raW5kID09PSAnY2xhc3MnKSB7XG5cdFx0XHRjb25zdCBjbGFzc1Byb3BzID0gdGhpcy5leHRyYWN0Q2xhc3NQcm9wZXJ0aWVzKGRlY2wubm9kZSBhcyB0cy5DbGFzc0RlY2xhcmF0aW9uKTtcblx0XHRcdGZvciAoY29uc3QgWyBuYW1lLCBpbmZvIF0gb2YgY2xhc3NQcm9wcykge1xuXHRcdFx0XHRvd25Qcm9wZXJ0aWVzLnNldChuYW1lLCBpbmZvKTtcblx0XHRcdH1cblx0XHR9IGVsc2UgaWYgKGRlY2wua2luZCA9PT0gJ2ludGVyZmFjZScpIHtcblx0XHRcdGNvbnN0IGlmYWNlID0gZGVjbC5ub2RlIGFzIHRzLkludGVyZmFjZURlY2xhcmF0aW9uO1xuXHRcdFx0dGhpcy5jb2xsZWN0VHlwZUVsZW1lbnRQcm9wZXJ0aWVzKFsgLi4uaWZhY2UubWVtYmVycyBdLCBvd25Qcm9wZXJ0aWVzKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0Y29uc3QgYWxpYXNUeXBlID0gKGRlY2wubm9kZSBhcyB0cy5UeXBlQWxpYXNEZWNsYXJhdGlvbikudHlwZTtcblx0XHRcdGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZShhbGlhc1R5cGUpKSB7XG5cdFx0XHRcdHRoaXMuY29sbGVjdFR5cGVFbGVtZW50UHJvcGVydGllcyhbIC4uLmFsaWFzVHlwZS5tZW1iZXJzIF0sIG93blByb3BlcnRpZXMpO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0cmV0dXJuIG93blByb3BlcnRpZXM7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gaGVyaXRhZ2UgbWVyZ2VzIHBhcmVudCBmaWVsZHMgZmlyc3Q7IHRoZSBkZWNsYXJhdGlvbidzIG93biBmaWVsZHNcblx0XHQvLyBvdmVycmlkZSBvbiBuYW1lIGNsYXNoIChsYXRlciBiYXNlcyBvdmVycmlkZSBlYXJsaWVyIG9uZXMpXG5cdFx0Y29uc3QgbWVyZ2VkID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblx0XHRmb3IgKGNvbnN0IGJhc2VEZWNsIG9mIHRoaXMucmVzb2x2ZUhlcml0YWdlRGVjbGFyYXRpb25zKGRlY2wpKSB7XG5cdFx0XHRjb25zdCBiYXNlUHJvcHMgPSB0aGlzLnJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXNJbm5lcihiYXNlRGVjbCwgdmlzaXRlZCwgZGVwdGggKyAxKTtcblx0XHRcdGZvciAoY29uc3QgWyBuYW1lLCBpbmZvIF0gb2YgYmFzZVByb3BzKSB7XG5cdFx0XHRcdG1lcmdlZC5zZXQobmFtZSwgaW5mbyk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGZvciAoY29uc3QgWyBuYW1lLCBpbmZvIF0gb2Ygb3duUHJvcGVydGllcykge1xuXHRcdFx0bWVyZ2VkLnNldChuYW1lLCBpbmZvKTtcblx0XHR9XG5cdFx0cmV0dXJuIG1lcmdlZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBQcm9wZXJ0eSBzaWduYXR1cmVzIG9mIGludGVyZmFjZS9hbGlhcyB0eXBlLWxpdGVyYWwgbWVtYmVycywgaW50b1xuXHQgKiB0aGUgZ2l2ZW4gbWFwLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0VHlwZUVsZW1lbnRQcm9wZXJ0aWVzIChcblx0XHRtZW1iZXJzOiByZWFkb25seSB0cy5UeXBlRWxlbWVudFtdLFxuXHRcdHByb3BlcnRpZXM6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz5cblx0KTogdm9pZCB7XG5cdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgbWVtYmVycykge1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0cHJvcGVydGllcy5zZXQocHJvcE5hbWUsIHtcblx0XHRcdFx0XHRuYW1lICAgICA6IHByb3BOYW1lLFxuXHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0aGUgaGVyaXRhZ2UgY2xhdXNlIG9mIGEgY2xhc3MgKGBleHRlbmRzIEJhc2VgKSBvciBpbnRlcmZhY2Vcblx0ICogKGBleHRlbmRzIEEsIEJgKSB0byByZWZlcmVuY2VkLXR5cGUgZGVjbGFyYXRpb25zIHRocm91Z2ggdGhlIFNBTUVcblx0ICogaW1wb3J0LWF3YXJlIG1hY2hpbmVyeSBhcyBwbGFpbiByZWZlcmVuY2VzICh0aGUgZGVjbGFyaW5nIGZpbGUncyBvd25cblx0ICogaW1wb3J0cyBmaXJzdCwgdGhlbiBpdHMgbG9jYWxzLCB0aGVuIHRoZSB1bmlxdWUgcHJvZ3JhbS13aWRlXG5cdCAqIGRlY2xhcmF0aW9uKS4gVW5yZXNvbHZhYmxlIG9yIGV4dGVybmFsIGJhc2VzIHlpZWxkIG5vdGhpbmcg4oCUIHRoZWlyXG5cdCAqIGluaGVyaXRlZCBmaWVsZHMgc2ltcGx5IHN0YXkgYWJzZW50LCBzYW1lIGFzIGJlZm9yZSB0aGlzIHdhbGtcblx0ICogZXhpc3RlZC4gTWl4aW4gY2FsbHMgKGBleHRlbmRzIG1peGluKFgpYCkgYW5kIG5hbWVzcGFjZSBhY2Nlc3MgYXJlXG5cdCAqIG5vdCBmb2xsb3dlZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUhlcml0YWdlRGVjbGFyYXRpb25zIChkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbltdIHtcblx0XHRjb25zdCB7IGhlcml0YWdlQ2xhdXNlcyB9ID0gKGRlY2wubm9kZSBhcyB0cy5DbGFzc0RlY2xhcmF0aW9uIHwgdHMuSW50ZXJmYWNlRGVjbGFyYXRpb24pO1xuXHRcdGlmICghaGVyaXRhZ2VDbGF1c2VzKSB7XG5cdFx0XHRyZXR1cm4gW107XG5cdFx0fVxuXHRcdGNvbnN0IGJhc2VzOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IGNsYXVzZSBvZiBoZXJpdGFnZUNsYXVzZXMpIHtcblx0XHRcdGlmIChjbGF1c2UudG9rZW4gIT09IHRzLlN5bnRheEtpbmQuRXh0ZW5kc0tleXdvcmQpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGhlcml0YWdlVHlwZSBvZiBjbGF1c2UudHlwZXMpIHtcblx0XHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoaGVyaXRhZ2VUeXBlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgYmFzZU5hbWUgPSBoZXJpdGFnZVR5cGUuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHRjb25zdCBiYXNlRGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oYmFzZU5hbWUsIGRlY2wuZmlsZSk7XG5cdFx0XHRcdGlmIChiYXNlRGVjbCkge1xuXHRcdFx0XHRcdGJhc2VzLnB1c2goYmFzZURlY2wpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGJhc2VzO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRXhwYW5kIGEgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9uIHRvIGEgc2VsZi1jb250YWluZWQgdHlwZSBzdHJpbmdcblx0ICogZm9yIGVtaXNzaW9uIGludG8gZ2VuZXJhdGVkIGZpbGVzOiB0eXBlIGFsaWFzZXMgdGhyb3VnaCBpbmZlclR5cGUsXG5cdCAqIGNsYXNzZXMgYW5kIGludGVyZmFjZXMgdGhyb3VnaCB0aGVpciAocHVibGljLCBub24tbWV0aG9kKSBmaWVsZHMuXG5cdCAqIE5lc3RlZCByZWZlcmVuY2VzIHJlc29sdmUgYWdhaW5zdCB0aGUgZGVjbGFyaW5nIGZpbGUgd2hpbGUgZXhwYW5kaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBleHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIChkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCByZWZlcmVuY2luZ0ZpbGUgPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gZGVjbC5maWxlO1xuXHRcdHRyeSB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25Jbm5lcihkZWNsKTtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fSBmaW5hbGx5IHtcblx0XHRcdHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9IHJlZmVyZW5jaW5nRmlsZTtcblx0XHR9XG5cdH1cblxuXHRwcml2YXRlIGV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25Jbm5lciAoZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKGRlY2wua2luZCA9PT0gJ2FsaWFzJykge1xuXHRcdFx0Y29uc3QgYWxpYXNOb2RlID0gZGVjbC5ub2RlIGFzIHRzLlR5cGVBbGlhc0RlY2xhcmF0aW9uO1xuXHRcdFx0Y29uc3QgYWxpYXNOYW1lID0gdHMuaXNJZGVudGlmaWVyKGFsaWFzTm9kZS5uYW1lKSA/IGFsaWFzTm9kZS5uYW1lLnRleHQgOiAnJztcblx0XHRcdGlmIChhbGlhc05hbWUgJiYgdGhpcy5leHBhbmRpbmdSZWZlcmVuY2VkQWxpYXNlcy5oYXMoYWxpYXNOYW1lKSkge1xuXHRcdFx0XHQvLyBTZWxmLXJlZmVyZW50aWFsIGFsaWFzIGNoYWluIOKAlCBiYWlsIG91dFxuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGFsaWFzTmFtZSkge1xuXHRcdFx0XHR0aGlzLmV4cGFuZGluZ1JlZmVyZW5jZWRBbGlhc2VzLmFkZChhbGlhc05hbWUpO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmluZmVyVHlwZShhbGlhc05vZGUudHlwZSk7XG5cdFx0XHRpZiAoYWxpYXNOYW1lKSB7XG5cdFx0XHRcdHRoaXMuZXhwYW5kaW5nUmVmZXJlbmNlZEFsaWFzZXMuZGVsZXRlKGFsaWFzTmFtZSk7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gZXhwYW5kZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGVjbFByb3BlcnRpZXMgPSB0aGlzLnJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXMoZGVjbCk7XG5cdFx0Y29uc3QgcHJvcHMgPSBBcnJheS5mcm9tKGRlY2xQcm9wZXJ0aWVzLmVudHJpZXMoKSkubWFwKChbIHByb3BOYW1lLCBpbmZvIF0pID0+IHtcblx0XHRcdGNvbnN0IG9wdGlvbmFsID0gaW5mby5vcHRpb25hbCA/ICc/JyA6ICcnO1xuXHRcdFx0cmV0dXJuIGAke3Byb3BOYW1lfSR7b3B0aW9uYWx9OiAke2luZm8udHlwZX1gO1xuXHRcdH0pO1xuXG5cdFx0Y29uc3QgcmVzdWx0ID0gYHsgJHtwcm9wcy5qb2luKCc7ICcpfSB9YDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEVtaXR0ZWQgaW5zdGFuY2UtdHlwZSBhbGlhcyBmb3IgYSBncmFwaCBub2RlIOKAlCB0aGUgbmFtZSB0eXBlcy50cyAvXG5cdCAqIHJlZ2lzdHJ5LnRzIGFjdHVhbGx5IGRlY2xhcmUuIE9wdGlvbiBCIGNvbGxlY3Rpb24gdHlwZXMgY2FycnkgdGhlaXJcblx0ICogcmVnaXN0cnkgaW50ZXJmYWNlIHByZWZpeDsgY29sbGVjdGlvbiB0eXBlcyBXSVRIT1VUIGEgcmVnaXN0cnlcblx0ICogaW50ZXJmYWNlIGFyZSBuZXZlciBlbWl0dGVkLCBzbyBubyB2YWxpZCBhbGlhcyBleGlzdHMgZm9yIHRoZW1cblx0ICogKHVuZGVmaW5lZCDigJQgY2FsbGVycyBkZWdyYWRlIHRvIGB1bmtub3duYCwgbmV2ZXIgYSBiYXJlIG5hbWUpLlxuXHQgKi9cblx0cHJpdmF0ZSBnZXRFbWl0dGVkSW5zdGFuY2VUeXBlTmFtZSAobm9kZTogVHlwZU5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmIChub2RlLmNvbGxlY3Rpb25JZCAmJiAhbm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWUpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGRvdHRlZCA9IG5vZGUuY29sbGVjdGlvbklkXG5cdFx0XHQ/IG5vZGUuZnVsbFBhdGguc2xpY2Uobm9kZS5jb2xsZWN0aW9uSWQubGVuZ3RoICsgMilcblx0XHRcdDogbm9kZS5mdWxsUGF0aDtcblx0XHRjb25zdCBwcmVmaXggPSBub2RlLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA/IGAke25vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lfV9gIDogJyc7XG5cdFx0Y29uc3QgcmVzdWx0ID0gYCR7cHJlZml4fSR7ZG90dGVkLnJlcGxhY2UoL1xcLi9nLCAnXycpfWA7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgc2ltcGxlIChub24tcXVhbGlmaWVkKSB0eXBlIHJlZmVyZW5jZTogaW1wb3J0LWF3YXJlXG5cdCAqIGRlY2xhcmF0aW9uIGV4cGFuc2lvbiBmaXJzdCwgdGhlbiB0aGUgSW5zdGFuY2VUeXBlPHR5cGVvZiBYPiBwYXR0ZXJuLFxuXHQgKiB0aGVuIG1uZW1vbmljYSBncmFwaCB0eXBlczsga25vd24gZ2xvYmFscyBrZWVwIHRoZWlyIGJhcmUgbmFtZSBhbmRcblx0ICogYW55dGhpbmcgZWxzZSBmYWxscyBiYWNrIHRvIGB1bmtub3duYCBzbyBnZW5lcmF0ZWQgZmlsZXMgbmV2ZXIgY2Fycnlcblx0ICogYW4gdW5yZXNvbHZhYmxlIGJhcmUgbmFtZS4gUmV0dXJucyB1bmRlZmluZWQgd2hlbiB0aGUgY2FsbGVyIHNob3VsZFxuXHQgKiBrZWVwIHRoZSBnZW5lcmljIHNwZWxsaW5nIChoYW5kbGVkIHNlcGFyYXRlbHkpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlU2ltcGxlVHlwZVJlZmVyZW5jZSAoXG5cdFx0dHlwZU5hbWU6IHN0cmluZyxcblx0XHR0eXBlQXJncz86IHRzLk5vZGVBcnJheTx0cy5UeXBlTm9kZT4sXG5cdFx0cmVmTm9kZT86IHRzLk5vZGVcblx0KTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBJbXBvcnQtYXdhcmUgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9uIChGMTApXG5cdFx0Y29uc3QgZGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24odHlwZU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0aWYgKGRlY2wpIHtcblx0XHRcdGNvbnN0IGV4cGFuZGVkID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKGRlY2wpO1xuXHRcdFx0aWYgKGV4cGFuZGVkICE9PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0cmV0dXJuIGV4cGFuZGVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgdW5rbm93blJlc3VsdCA9ICd1bmtub3duJztcblx0XHRcdHJldHVybiB1bmtub3duUmVzdWx0O1xuXHRcdH1cblxuXHRcdC8vIEluc3RhbmNlVHlwZTx0eXBlb2YgWD4gbGF3ICgwLjIuMCBiZWhhdmlvciwgcmVzdG9yZWQpOiB0aGVcblx0XHQvLyBnZW5lcmF0ZWQgYWxpYXMgYWxyZWFkeSBJUyB0aGUgaW5zdGFuY2UgdHlwZSDigJQgcmVzb2x2ZSBYIHRocm91Z2hcblx0XHQvLyB0aGUgZ3JhcGggdGllcnMgYW5kIGRyb3AgdGhlIHdyYXBwZXIuIE11c3QgcnVuIEJFRk9SRSB0aGUgZ3JhcGhcblx0XHQvLyByZXNvbHV0aW9uOiAnSW5zdGFuY2VUeXBlJyBpcyBhbiBhbWJpZW50IGdsb2JhbCwgbmV2ZXIgYSBncmFwaFxuXHRcdC8vIHR5cGUgKHRoZSBvbGQgc3BlY2lhbCBjYXNlIGJlbG93IHNhdCBpbnNpZGUgdGhlIGdyYXBoLXVuaXF1ZVxuXHRcdC8vIGJyYW5jaCBhbmQgd2FzIGRlYWQgY29kZSkuIFdoZW4gWCBkb2VzIG5vdCByZXNvbHZlLCB0aGUgV0hPTEVcblx0XHQvLyBleHByZXNzaW9uIGRlZ3JhZGVzIHRvIGB1bmtub3duYCDigJQgbmV2ZXIgZW1pdFxuXHRcdC8vIGBJbnN0YW5jZVR5cGU8dW5rbm93bj5gOiBpbnZhbGlkIFRTIChUUzIzNDQsICd1bmtub3duJyBkb2VzIG5vdFxuXHRcdC8vIHNhdGlzZnkgdGhlIGNvbnN0cnVjdG9yIGNvbnN0cmFpbnQpLiBSZWFjaGVkIGRpcmVjdGx5IG9yIHRocm91Z2hcblx0XHQvLyBhIGxvY2FsIGFsaWFzIChgWEluc3RhbmNlID0gSW5zdGFuY2VUeXBlPHR5cGVvZiBYPmApLlxuXHRcdGlmICh0eXBlTmFtZSA9PT0gJ0luc3RhbmNlVHlwZScgJiYgdHlwZUFyZ3MgJiYgdHlwZUFyZ3MubGVuZ3RoID09PSAxKSB7XG5cdFx0XHRjb25zdCBbIGluc3RhbmNlQXJnIF0gPSB0eXBlQXJncztcblx0XHRcdGlmIChpbnN0YW5jZUFyZyAmJiB0cy5pc1R5cGVRdWVyeU5vZGUoaW5zdGFuY2VBcmcpICYmIHRzLmlzSWRlbnRpZmllcihpbnN0YW5jZUFyZy5leHByTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcXVlcnlSZXN1bHQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKGluc3RhbmNlQXJnLmV4cHJOYW1lLnRleHQpO1xuXHRcdFx0XHRpZiAocXVlcnlSZXN1bHQuc3RhdHVzID09PSAndW5pcXVlJykge1xuXHRcdFx0XHRcdC8vIHVuZGVmaW5lZCB3aGVuIHRoZSB0eXBlIGlzIG5ldmVyIGVtaXR0ZWQgKGNvbGxlY3Rpb25cblx0XHRcdFx0XHQvLyB3aXRob3V0IGEgcmVnaXN0cnkgaW50ZXJmYWNlKSDigJQgZGVncmFkZSwgbmV2ZXIgYmFyZVxuXHRcdFx0XHRcdGNvbnN0IGFsaWFzUmVzdWx0ID0gdGhpcy5nZXRFbWl0dGVkSW5zdGFuY2VUeXBlTmFtZShxdWVyeVJlc3VsdC5ub2RlKSA/PyAndW5rbm93bic7XG5cdFx0XHRcdFx0cmV0dXJuIGFsaWFzUmVzdWx0O1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChxdWVyeVJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHRcdFx0dGhpcy5yZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yKGluc3RhbmNlQXJnLmV4cHJOYW1lLnRleHQsIGluc3RhbmNlQXJnLCBxdWVyeVJlc3VsdCk7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgZGVncmFkZWRSZXN1bHQgPSAndW5rbm93bic7XG5cdFx0XHRcdHJldHVybiBkZWdyYWRlZFJlc3VsdDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGluZmVycmVkQXJnID0gdGhpcy5pbmZlclR5cGUoaW5zdGFuY2VBcmcpO1xuXHRcdFx0aWYgKGluZmVycmVkQXJnID09PSAndW5rbm93bicpIHtcblx0XHRcdFx0Y29uc3QgZGVncmFkZWRXcmFwcGVyID0gJ3Vua25vd24nO1xuXHRcdFx0XHRyZXR1cm4gZGVncmFkZWRXcmFwcGVyO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgd3JhcHBlZFJlc3VsdCA9IGBJbnN0YW5jZVR5cGU8JHtpbmZlcnJlZEFyZ30+YDtcblx0XHRcdHJldHVybiB3cmFwcGVkUmVzdWx0O1xuXHRcdH1cblxuXHRcdC8vIE1uZW1vbmljYS1ncmFwaCBpZGVudGl0eSBsYXc6IHBhdGgtYXdhcmUgcmVzb2x1dGlvbiAodmFsdWUgc2NvcGUsXG5cdFx0Ly8gaW1wb3J0cywgbmVhcmVzdC1jaGFpbiwgcm9vdCwgcHJvZ3JhbS13aWRlKS4gQW1iaWd1aXR5IGJldHdlZW5cblx0XHQvLyByZWFsIGdyYXBoIHR5cGVzIGlzIGEgaGFyZCBmYWlsdXJlOyBhIG5hbWUgbm8gZ3JhcGggdHlwZSBjYXJyaWVzXG5cdFx0Ly8gc3RheXMgaW4gdGhlIHBsYWluLVRTIHNvZnQgc2NvcGUgYW5kIGZhbGxzIHRvIGB1bmtub3duYC5cblx0XHRjb25zdCBncmFwaFJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUodHlwZU5hbWUpO1xuXHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHQvLyBIYW5kbGUgSW5zdGFuY2VUeXBlPHR5cGVvZiBYPiBwYXR0ZXJuIC0+IGNvbnZlcnQgdG8gUGFyZW50X1hcblx0XHRcdGlmICh0eXBlTmFtZSA9PT0gJ0luc3RhbmNlVHlwZScgJiYgdHlwZUFyZ3MgJiYgdHlwZUFyZ3MubGVuZ3RoID09PSAxKSB7XG5cdFx0XHRcdGNvbnN0IFsgYXJnIF0gPSB0eXBlQXJncztcblx0XHRcdFx0aWYgKGFyZy5raW5kID09PSB0cy5TeW50YXhLaW5kLlR5cGVRdWVyeSkge1xuXHRcdFx0XHRcdGNvbnN0IHR5cGVRdWVyeSA9IGFyZyBhcyB0cy5UeXBlUXVlcnlOb2RlO1xuXHRcdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIodHlwZVF1ZXJ5LmV4cHJOYW1lKSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcXVlcnlSZXN1bHQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKHR5cGVRdWVyeS5leHByTmFtZS50ZXh0KTtcblx0XHRcdFx0XHRcdGlmIChxdWVyeVJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRcdFx0XHRcdC8vIEVtaXR0ZWQgYWxpYXM6IFVzYWdlcy5Vc2FnZUVudHJ5IC0+IFVzYWdlc19Vc2FnZUVudHJ5XG5cdFx0XHRcdFx0XHRcdC8vIChPcHRpb24gQiBjb2xsZWN0aW9ucyBjYXJyeSB0aGUgcmVnaXN0cnkgcHJlZml4O1xuXHRcdFx0XHRcdFx0XHQvLyB1bmRlZmluZWQgd2hlbiBuZXZlciBlbWl0dGVkIOKAlCBkZWdyYWRlKVxuXHRcdFx0XHRcdFx0XHRjb25zdCBxdWVyeUFsaWFzID0gdGhpcy5nZXRFbWl0dGVkSW5zdGFuY2VUeXBlTmFtZShxdWVyeVJlc3VsdC5ub2RlKSA/PyAndW5rbm93bic7XG5cdFx0XHRcdFx0XHRcdHJldHVybiBxdWVyeUFsaWFzO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKHF1ZXJ5UmVzdWx0LnN0YXR1cyA9PT0gJ2FtYmlndW91cycpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5yZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yKHR5cGVRdWVyeS5leHByTmFtZS50ZXh0LCB0eXBlUXVlcnksIHF1ZXJ5UmVzdWx0KTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdC8vIE5vdCBhIGtub3duIG1uZW1vbmljYSB0eXBlIOKAlCBubyBiYXJlIGVtaXNzaW9uXG5cdFx0XHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKCF0eXBlQXJncyB8fCB0eXBlQXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdFx0Ly8gRW1pdHRlZCBhbGlhczogVXNhZ2VzLlVzYWdlRW50cnkgLT4gVXNhZ2VzX1VzYWdlRW50cnlcblx0XHRcdFx0Ly8gKE9wdGlvbiBCIGNvbGxlY3Rpb25zIGNhcnJ5IHRoZSByZWdpc3RyeSBwcmVmaXg7XG5cdFx0XHRcdC8vIHVuZGVmaW5lZCB3aGVuIG5ldmVyIGVtaXR0ZWQg4oCUIGRlZ3JhZGUpXG5cdFx0XHRcdGNvbnN0IGdyYXBoQWxpYXMgPSB0aGlzLmdldEVtaXR0ZWRJbnN0YW5jZVR5cGVOYW1lKGdyYXBoUmVzdWx0Lm5vZGUpID8/ICd1bmtub3duJztcblx0XHRcdFx0cmV0dXJuIGdyYXBoQWxpYXM7XG5cdFx0XHR9XG5cdFx0XHQvLyBHZW5lcmljIHVzZSBvZiBhIGdyYXBoIHR5cGUga2VlcHMgaXRzIHNpbXBsZSBuYW1lOyB0aGVcblx0XHRcdC8vIGdlbmVyYXRvciB1cGdyYWRlcyBpdCB0byB0aGUgZnVsbC1wYXRoIGluc3RhbmNlIHR5cGUgbmFtZVxuXHRcdFx0cmV0dXJuIGAke3R5cGVOYW1lfTwke3R5cGVBcmdzLm1hcChhID0+IHRoaXMuaW5mZXJUeXBlKGEpKS5qb2luKCcsICcpfT5gO1xuXHRcdH1cblx0XHRpZiAoZ3JhcGhSZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0dGhpcy5yZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yKHR5cGVOYW1lLCByZWZOb2RlID8/IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSwgZ3JhcGhSZXN1bHQpO1xuXHRcdH1cblxuXHRcdGlmICh0eXBlQXJncyAmJiB0eXBlQXJncy5sZW5ndGggPiAwKSB7XG5cdFx0XHRpZiAoS05PV05fR0xPQkFMX1RZUEVTLmhhcyh0eXBlTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgZ2VuZXJpY1Jlc3VsdCA9IGAke3R5cGVOYW1lfTwke3R5cGVBcmdzLm1hcChhID0+IHRoaXMuaW5mZXJUeXBlKGEpKS5qb2luKCcsICcpfT5gO1xuXHRcdFx0XHRyZXR1cm4gZ2VuZXJpY1Jlc3VsdDtcblx0XHRcdH1cblx0XHRcdC8vIEVtaXNzaW9uIHJlc3RvcmF0aW9uICgwLjIuMCBiZWhhdmlvcik6IGEgbm9uLWdyYXBoIG91dGVyXG5cdFx0XHQvLyBnZW5lcmljIHRoYXQgaXMgTk9UIGRlY2xhcmVkIGluIGFueSBhbmFseXplZCBwcm9qZWN0IGZpbGUgaXNcblx0XHRcdC8vIGFuIGFtYmllbnQvbGliIGNvbnN0cnVjdCAoTWFwSXRlcmF0b3IsIGxpYiBoZWxwZXJzKSDigJQgaXRcblx0XHRcdC8vIHJlc29sdmVzIGluIGV2ZXJ5IGNvbnN1bWVyIGNvbXBpbGF0aW9uIHdpdGhvdXQgYW4gaW1wb3J0LCBzb1xuXHRcdFx0Ly8gZW1pdCBpdCBWRVJCQVRJTSB3aXRoIGlubmVyIGdyYXBoIGFsaWFzZXMgcmVzb2x2ZWQuIEEgbmFtZVxuXHRcdFx0Ly8gZGVjbGFyZWQgaW4gcHJvamVjdCBmaWxlcyBzdGF5cyB1bmtub3duOiB0aGUgc2VsZi1jb250YWluZWRcblx0XHRcdC8vIHR5cGVzLnRzIGNhbiBjYXJyeSBuZWl0aGVyIHRoZSBiYXJlIG5hbWUgbm9yIGFuIGltcG9ydC5cblx0XHRcdGlmICghdGhpcy5pc1Byb2plY3REZWNsYXJlZFR5cGVOYW1lKHR5cGVOYW1lKSkge1xuXHRcdFx0XHRjb25zdCB2ZXJiYXRpbVJlc3VsdCA9IGAke3R5cGVOYW1lfTwke3R5cGVBcmdzLm1hcChhID0+IHRoaXMuaW5mZXJUeXBlKGEpKS5qb2luKCcsICcpfT5gO1xuXHRcdFx0XHRyZXR1cm4gdmVyYmF0aW1SZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBHZW5lcmljIHJlZmVyZW5jZSB0byBhIG5vbi1nbG9iYWwsIG5vbi1ncmFwaCBQUk9KRUNULUxPQ0FMXG5cdFx0XHQvLyB0eXBlIGNhbm5vdCBiZSBlbWl0dGVkIGJhcmUgaW50byB0aGUgZ2VuZXJhdGVkIGZpbGVcblx0XHRcdGlmIChyZWZOb2RlKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSh0eXBlTmFtZSwgcmVmTm9kZSk7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZhbGxiYWNrUmVzdWx0ID0gdGhpcy51bnJlc29sdmVkVHlwZVJlZmVyZW5jZUZhbGxiYWNrKHR5cGVOYW1lLCByZWZOb2RlKTtcblx0XHRyZXR1cm4gZmFsbGJhY2tSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHF1YWxpZmllZCB0eXBlIHJlZmVyZW5jZSAobW9kZWxzLklubmVyLkNyYXRlKSB0aHJvdWdoIHRoZVxuXHQgKiBjdXJyZW50IGZpbGUncyBuYW1lc3BhY2UgaW1wb3J0cy4gVGhlIGNoYWluJ3MgaGVhZCBtdXN0IGJlIGEgbmFtZXNwYWNlXG5cdCAqIGltcG9ydDsgbWlkZGxlIHNlZ21lbnRzIGRlc2NlbmQgdGhyb3VnaCBuYW1lc3BhY2UgZGVjbGFyYXRpb25zLCBuYW1lZFxuXHQgKiByZS1leHBvcnRzIG9mIG5hbWVzcGFjZXMsIGFuZCBgZXhwb3J0ICogYXMgbnMgZnJvbSAn4oCmJ2AgYmFycmVscyAoZWFjaFxuXHQgKiBzZWdtZW50IGNvbnN1bWVkIGV4YWN0bHkgb25jZSwgc28gdGhlIHdhbGsgY2Fubm90IGN5Y2xlKTsgdGhlIGZpbmFsXG5cdCAqIHNlZ21lbnQgcmVzb2x2ZXMgdG8gYSBkZWNsYXJhdGlvbiB3aGljaCBpcyBleHBhbmRlZCBpbmxpbmUuIFdoZW4gdGhlXG5cdCAqIHByZWNpc2Ugd2FsayBmaW5kcyBub3RoaW5nLCB0aGUgbGVnYWN5IHJpZ2h0bW9zdC1uYW1lIGxvb2t1cCBpbiB0aGVcblx0ICogaGVhZCBtb2R1bGUga2VlcHMgb25lLWxldmVsIGZvcm1zIChtb2RlbHMuVHlwZSkgd29ya2luZyDigJQgbmVzdGVkXG5cdCAqIGRlY2xhcmF0aW9ucyBhcmUgcmVjb3JkZWQgYnkgcGxhaW4gbmFtZSB0aGVyZSB0b28uIFJldHVybnMgdW5kZWZpbmVkXG5cdCAqIHdoZW4gdGhlIGhlYWQgaXMgbm90IGEgbmFtZXNwYWNlIGltcG9ydCBvciBub3RoaW5nIHJlc29sdmVzLlxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlclF1YWxpZmllZFR5cGVSZWZlcmVuY2UgKHR5cGVSZWY6IHRzLlR5cGVSZWZlcmVuY2VOb2RlKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIXRzLmlzUXVhbGlmaWVkTmFtZSh0eXBlUmVmLnR5cGVOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBmbGF0dGVuIHRoZSBxdWFsaWZpZWQgbmFtZSBjaGFpbjogbW9kZWxzLklubmVyLkNyYXRlIOKGkiBbJ21vZGVscycsICdJbm5lcicsICdDcmF0ZSddXG5cdFx0Y29uc3Qgc2VnbWVudHM6IHN0cmluZ1tdID0gW107XG5cdFx0bGV0IGNoYWluOiB0cy5FbnRpdHlOYW1lID0gdHlwZVJlZi50eXBlTmFtZTtcblx0XHR3aGlsZSAodHMuaXNRdWFsaWZpZWROYW1lKGNoYWluKSkge1xuXHRcdFx0c2VnbWVudHMudW5zaGlmdChjaGFpbi5yaWdodC50ZXh0KTtcblx0XHRcdGNoYWluID0gY2hhaW4ubGVmdDtcblx0XHR9XG5cdFx0c2VnbWVudHMudW5zaGlmdChjaGFpbi50ZXh0KTtcblxuXHRcdGNvbnN0IG5hbWVzcGFjZUltcG9ydCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQoc2VnbWVudHNbIDAgXSk7XG5cdFx0aWYgKCFuYW1lc3BhY2VJbXBvcnQgfHwgIW5hbWVzcGFjZUltcG9ydC5pc05hbWVzcGFjZSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUobmFtZXNwYWNlSW1wb3J0LnNwZWNpZmllciwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRpZiAoIXJlc29sdXRpb24gfHwgcmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIGRlc2NlbmQgdGhlIG1pZGRsZSBzZWdtZW50czogYSBtb2R1bGUgY29udGV4dCByZXNvbHZlcyB0aGUgc2VnbWVudFxuXHRcdC8vIGFzIGEgbmFtZXNwYWNlIGRlY2xhcmF0aW9uIC8gbmFtZXNwYWNlIHJlLWV4cG9ydDsgYSBuYW1lc3BhY2UtYmxvY2tcblx0XHQvLyBjb250ZXh0IHJlc29sdmVzIGl0IGFzIGEgbmVzdGVkIG5hbWVzcGFjZSBkZWNsYXJhdGlvblxuXHRcdGxldCBxdWFsaWZpZXI6IHsgbW9kdWxlUGF0aDogc3RyaW5nOyBibG9jaz86IHRzLk1vZHVsZUJsb2NrIH0gfCB1bmRlZmluZWQgPSB7XG5cdFx0XHRtb2R1bGVQYXRoIDogcmVzb2x1dGlvbi5yZXNvbHZlZFBhdGhcblx0XHR9O1xuXHRcdGZvciAobGV0IGkgPSAxOyBpIDwgc2VnbWVudHMubGVuZ3RoIC0gMSAmJiBxdWFsaWZpZXI7IGkrKykge1xuXHRcdFx0Y29uc3Qgc2VnbWVudCA9IHNlZ21lbnRzWyBpIF07XG5cdFx0XHRpZiAocXVhbGlmaWVyLmJsb2NrKSB7XG5cdFx0XHRcdGNvbnN0IG5lc3RlZCA9IHRoaXMuZmluZE5hbWVzcGFjZUluQmxvY2socXVhbGlmaWVyLmJsb2NrLCBzZWdtZW50KTtcblx0XHRcdFx0aWYgKG5lc3RlZD8uYm9keSAmJiB0cy5pc01vZHVsZUJsb2NrKG5lc3RlZC5ib2R5KSkge1xuXHRcdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IHF1YWxpZmllci5tb2R1bGVQYXRoLCBibG9jayA6IG5lc3RlZC5ib2R5IH07XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0cXVhbGlmaWVyID0gdW5kZWZpbmVkO1xuXHRcdFx0XHRicmVhaztcblx0XHRcdH1cblx0XHRcdGNvbnN0IG5hbWVzcGFjZURlY2w6IHRzLk1vZHVsZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkID1cblx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMuZ2V0KHF1YWxpZmllci5tb2R1bGVQYXRoKT8uZ2V0KHNlZ21lbnQpO1xuXHRcdFx0aWYgKG5hbWVzcGFjZURlY2w/LmJvZHkgJiYgdHMuaXNNb2R1bGVCbG9jayhuYW1lc3BhY2VEZWNsLmJvZHkpKSB7XG5cdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IHF1YWxpZmllci5tb2R1bGVQYXRoLCBibG9jayA6IG5hbWVzcGFjZURlY2wuYm9keSB9O1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHN0YXJTcGVjaWZpZXIgPSB0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlU3RhcnMuZ2V0KHF1YWxpZmllci5tb2R1bGVQYXRoKT8uZ2V0KHNlZ21lbnQpO1xuXHRcdFx0aWYgKHN0YXJTcGVjaWZpZXIpIHtcblx0XHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShzdGFyU3BlY2lmaWVyLCBxdWFsaWZpZXIubW9kdWxlUGF0aCk7XG5cdFx0XHRcdGlmIChuZXh0UmVzb2x1dGlvbiAmJiAhbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCB9O1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRjb25zdCByZUV4cG9ydFNwZWNpZmllciA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuZ2V0KHF1YWxpZmllci5tb2R1bGVQYXRoKT8uZ2V0KHNlZ21lbnQpO1xuXHRcdFx0aWYgKHJlRXhwb3J0U3BlY2lmaWVyKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUocmVFeHBvcnRTcGVjaWZpZXIsIHF1YWxpZmllci5tb2R1bGVQYXRoKTtcblx0XHRcdFx0Y29uc3QgcmVFeHBvcnRlZDogdHMuTW9kdWxlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQgPVxuXHRcdFx0XHRcdG5leHRSZXNvbHV0aW9uICYmICFuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsXG5cdFx0XHRcdFx0XHQ/IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzLmdldChuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgpPy5nZXQoc2VnbWVudClcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0XHRpZiAocmVFeHBvcnRlZD8uYm9keSAmJiB0cy5pc01vZHVsZUJsb2NrKHJlRXhwb3J0ZWQuYm9keSkpIHtcblx0XHRcdFx0XHRxdWFsaWZpZXIgPSB7IG1vZHVsZVBhdGggOiBuZXh0UmVzb2x1dGlvbiEucmVzb2x2ZWRQYXRoLCBibG9jayA6IHJlRXhwb3J0ZWQuYm9keSB9O1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRxdWFsaWZpZXIgPSB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmluYWxOYW1lID0gc2VnbWVudHNbIHNlZ21lbnRzLmxlbmd0aCAtIDEgXTtcblx0XHRsZXQgZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZDtcblx0XHRpZiAocXVhbGlmaWVyPy5ibG9jaykge1xuXHRcdFx0ZGVjbCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5CbG9jayhxdWFsaWZpZXIuYmxvY2ssIHF1YWxpZmllci5tb2R1bGVQYXRoLCBmaW5hbE5hbWUpO1xuXHRcdH0gZWxzZSBpZiAocXVhbGlmaWVyKSB7XG5cdFx0XHRkZWNsID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZShxdWFsaWZpZXIubW9kdWxlUGF0aCwgZmluYWxOYW1lLCAwKTtcblx0XHR9XG5cdFx0Ly8gbGVnYWN5IGZhbGxiYWNrOiByaWdodG1vc3QgbmFtZSBhbnl3aGVyZSBpbiB0aGUgaGVhZCBtb2R1bGVcblx0XHQvLyAobmFtZXNwYWNlLW5lc3RlZCBkZWNsYXJhdGlvbnMgYXJlIGFsc28gcmVjb3JkZWQgYnkgcGxhaW4gbmFtZSlcblx0XHRpZiAoIWRlY2wpIHtcblx0XHRcdGRlY2wgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKHJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBmaW5hbE5hbWUsIDApO1xuXHRcdH1cblx0XHRpZiAoIWRlY2wpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oZGVjbCk7XG5cdFx0cmV0dXJuIGV4cGFuZGVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpbmQgYSBuYW1lc3BhY2UgZGVjbGFyYXRpb24gYnkgbmFtZSBkaXJlY3RseSBpbnNpZGUgYSBtb2R1bGUgYmxvY2suXG5cdCAqL1xuXHRwcml2YXRlIGZpbmROYW1lc3BhY2VJbkJsb2NrIChibG9jazogdHMuTW9kdWxlQmxvY2ssIG5hbWU6IHN0cmluZyk6IHRzLk1vZHVsZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRmb3IgKGNvbnN0IHN0YXRlbWVudCBvZiBibG9jay5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAodHMuaXNNb2R1bGVEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmIHRzLmlzSWRlbnRpZmllcihzdGF0ZW1lbnQubmFtZSkgJiZcblx0XHRcdFx0c3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZSkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQgPSBzdGF0ZW1lbnQ7XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmluZCBhIG5hbWVkIHR5cGUgZGVjbGFyYXRpb24gKGFsaWFzLCBjbGFzcywgaW50ZXJmYWNlKSBkaXJlY3RseSBpbnNpZGVcblx0ICogYSBuYW1lc3BhY2UgYmxvY2sg4oCUIHRoZSBmaW5hbCBzZWdtZW50IG9mIGEgZGVzY2VuZGVkIHF1YWxpZmllZCBjaGFpbi5cblx0ICovXG5cdHByaXZhdGUgZmluZFJlZmVyZW5jZWRUeXBlSW5CbG9jayAoXG5cdFx0YmxvY2s6IHRzLk1vZHVsZUJsb2NrLFxuXHRcdGZpbGVQYXRoOiBzdHJpbmcsXG5cdFx0bmFtZTogc3RyaW5nXG5cdCk6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIGJsb2NrLnN0YXRlbWVudHMpIHtcblx0XHRcdGlmICh0cy5pc1R5cGVBbGlhc0RlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiYgdHMuaXNJZGVudGlmaWVyKHN0YXRlbWVudC5uYW1lKSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiA9IHsga2luZCA6ICdhbGlhcycsIG5vZGUgOiBzdGF0ZW1lbnQsIGZpbGUgOiBmaWxlUGF0aCB9O1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmIHN0YXRlbWVudC5uYW1lICYmIHN0YXRlbWVudC5uYW1lLnRleHQgPT09IG5hbWUpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0OiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uID0geyBraW5kIDogJ2NsYXNzJywgbm9kZSA6IHN0YXRlbWVudCwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNJbnRlcmZhY2VEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmIHRzLmlzSWRlbnRpZmllcihzdGF0ZW1lbnQubmFtZSkgJiZcblx0XHRcdFx0c3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZSkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQ6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gPSB7IGtpbmQgOiAnaW50ZXJmYWNlJywgbm9kZSA6IHN0YXRlbWVudCwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmFsbGJhY2sgZm9yIGEgdHlwZS1yZWZlcmVuY2UgbmFtZSB0aGF0IHJlc29sdmVzIHRvIG5vIGRlY2xhcmF0aW9uIGFuZFxuXHQgKiBubyBncmFwaCB0eXBlOiBrbm93biBnbG9iYWxzIGtlZXAgdGhlaXIgYmFyZSBuYW1lICh0aGV5IHJlc29sdmUgd2l0aG91dFxuXHQgKiBhbiBpbXBvcnQpOyBldmVyeXRoaW5nIGVsc2UgYmVjb21lcyBgdW5rbm93bmAgc28gZ2VuZXJhdGVkIHR5cGVzLnRzXG5cdCAqIG5ldmVyIGNhcnJpZXMgYW4gdW5yZXNvbHZhYmxlIGJhcmUgbmFtZSAoUkVBRE1FJ3MgZG9jdW1lbnRlZCBiZWhhdmlvcilcblx0ICogYW5kIHRoZSBzaXRlIGlzIHJlY29yZGVkIGZvciB0aGUgcGxhaW4tVFMgYW1iaWd1aXR5IHZhbGlkYXRpb24uXG5cdCAqL1xuXHRwcml2YXRlIHVucmVzb2x2ZWRUeXBlUmVmZXJlbmNlRmFsbGJhY2sgKHR5cGVOYW1lOiBzdHJpbmcsIHJlZk5vZGU/OiB0cy5Ob2RlKTogc3RyaW5nIHtcblx0XHRpZiAoS05PV05fR0xPQkFMX1RZUEVTLmhhcyh0eXBlTmFtZSkpIHtcblx0XHRcdHJldHVybiB0eXBlTmFtZTtcblx0XHR9XG5cdFx0aWYgKHJlZk5vZGUpIHtcblx0XHRcdHRoaXMucmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSh0eXBlTmFtZSwgcmVmTm9kZSk7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9ICd1bmtub3duJztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBvbmUgZGVmaW5lKCkvbGF6eSgpL0BkZWNvcmF0ZSgpIHNpdGUgdW5kZXIgaXRzIHJ1bnRpbWVcblx0ICogbmFtZXNwYWNlIGtleS4gVHdvIHNpdGVzIGluIG9uZSBuYW1lc3BhY2UgYXJlIGEgc2FtZS1uYW1lc3BhY2Vcblx0ICogZHVwbGljYXRlICh0aGUgcnVudGltZSB0aHJvd3MgQUxSRUFEWV9ERUNMQVJFRCk7IGV2ZXJ5IHNpdGUgaXMga2VwdFxuXHQgKiBzbyB0aGUgZmFpbHVyZSBjYW4gcmVwb3J0IGFsbCBsb2NhdGlvbnMuXG5cdCAqL1xuXHRwcml2YXRlIHJlY29yZERlZmluZVNpdGUgKG5hbWVzcGFjZUtleTogc3RyaW5nLCBsb2NhdGlvbjogc3RyaW5nKTogdm9pZCB7XG5cdFx0bGV0IHNpdGVzID0gdGhpcy5kZWZpbmVTaXRlcy5nZXQobmFtZXNwYWNlS2V5KTtcblx0XHRpZiAoIXNpdGVzKSB7XG5cdFx0XHRzaXRlcyA9IFtdO1xuXHRcdFx0dGhpcy5kZWZpbmVTaXRlcy5zZXQobmFtZXNwYWNlS2V5LCBzaXRlcyk7XG5cdFx0fVxuXHRcdGlmICghc2l0ZXMuaW5jbHVkZXMobG9jYXRpb24pKSB7XG5cdFx0XHRzaXRlcy5wdXNoKGxvY2F0aW9uKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRmF0YWwgcmVzb2x1dGlvbiBmYWlsdXJlcyAoaGFyZC1mYWlsIGxhdyk6IHNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZVxuXHQgKiBtbmVtb25pY2EgZGVmaW5pdGlvbnMgcGx1cyBhbWJpZ3VvdXMvdW5yZXNvbHZlZCBtbmVtb25pY2EtZ3JhcGhcblx0ICogcmVmZXJlbmNlcy4gVGhlIENMSSBwcmludHMgZXZlcnkgbG9jYXRpb24gYW5kIHdyaXRlcyBubyBvdXRwdXQuXG5cdCAqL1xuXHRnZXRSZXNvbHV0aW9uRXJyb3JzICgpOiBSZXNvbHV0aW9uRXJyb3JbXSB7XG5cdFx0dGhpcy52YWxpZGF0ZUxvb2t1cFJlZmVyZW5jZXMoKTtcblx0XHR0aGlzLnZhbGlkYXRlUGxhaW5UeXBlUmVmZXJlbmNlcygpO1xuXHRcdGNvbnN0IGVycm9yczogUmVzb2x1dGlvbkVycm9yW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IFsgbmFtZXNwYWNlS2V5LCBzaXRlcyBdIG9mIHRoaXMuZGVmaW5lU2l0ZXMpIHtcblx0XHRcdGlmIChzaXRlcy5sZW5ndGggPCAyKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZGlzcGxheU5hbWUgPSBuYW1lc3BhY2VLZXkucmVwbGFjZSgvXlteOl0rOjovLCAnJyk7XG5cdFx0XHRjb25zdCBtZXNzYWdlID0gYER1cGxpY2F0ZSBkZWZpbml0aW9uIG9mICcke2Rpc3BsYXlOYW1lfScgaW4gb25lIG5hbWVzcGFjZSDigJQgYCArXG5cdFx0XHRcdCd0aGUgbW5lbW9uaWNhIHJ1bnRpbWUgd291bGQgdGhyb3cgQUxSRUFEWV9ERUNMQVJFRCc7XG5cdFx0XHRlcnJvcnMucHVzaCh7IG1lc3NhZ2UsIGxvY2F0aW9ucyA6IFsgLi4uc2l0ZXMgXSB9KTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBlcnJvciBvZiB0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzKSB7XG5cdFx0XHRlcnJvcnMucHVzaChlcnJvcik7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGVycm9ycztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSByZWZlcmVuY2UgdG8gYSBtbmVtb25pY2EgZ3JhcGggdHlwZSBuYW1lLCBpbXBvcnQtYXdhcmUgYW5kXG5cdCAqIHBhdGgtYXdhcmUgKHRoZSBoYXJkLWZhaWwgaWRlbnRpdHkgbGF3LCBtaXJyb3JpbmcgdGhlIHJ1bnRpbWUpOlxuXHQgKiAgIDEuIHZhbHVlIHNjb3BlIOKAlCBhIHRyYWNrZWQgdG9wLWxldmVsIGJpbmRpbmcgaW4gdGhlIHJlZmVyZW5jaW5nIGZpbGVcblx0ICogICAgICAoYGNvbnN0IEFkZHJlc3MgPSBVc2VyLmRlZmluZSgnQWRkcmVzcycsIOKApilgKSxcblx0ICogICAyLiBpbXBvcnQgc2NvcGUg4oCUIGEgYmluZGluZyBleHBvcnRlZCBmcm9tIGEgbW9kdWxlIHRoaXMgZmlsZSBpbXBvcnRzXG5cdCAqICAgICAgKGJhcnJlbHMgY2hhc2VkKSxcblx0ICogICAzLiBuZWFyZXN0LWNoYWluIOKAlCB0aGUgYW5jaG9yIHR5cGUncyBvd24gc3VidHlwZXMgZmlyc3QsIHRoZW4gZWFjaFxuXHQgKiAgICAgIGFuY2VzdG9yIGxldmVsIChyZWxhdGl2ZS1maXJzdCksXG5cdCAqICAgNC4gcm9vdCDigJQgcm9vdHMgb2YgdGhlIGFuY2hvcidzIGNvbGxlY3Rpb24sXG5cdCAqICAgNS4gcHJvZ3JhbS13aWRlIOKAlCBvbmx5IHdoZW4gZXhhY3RseSBvbmUgdHlwZSBjYXJyaWVzIHRoZSBuYW1lLlxuXHQgKiBBbWJpZ3VpdHkgKHNldmVyYWwgY2FuZGlkYXRlcyBhbmQgbm90aGluZyBkaXNhbWJpZ3VhdGVzKSBhbmQgYWJzZW5jZVxuXHQgKiBhcmUgYm90aCByZXR1cm5lZCBhcyBzdWNoIOKAlCB0aGUgY2FsbGVyIHJlY29yZHMgYSBoYXJkIGZhaWx1cmU7IGEgYmFyZVxuXHQgKiBmaXJzdC1tYXRjaCBuYW1lIGlzIG5ldmVyIGVtaXR0ZWQuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVHcmFwaFR5cGVOYW1lIChuYW1lOiBzdHJpbmcpOiBHcmFwaFR5cGVSZWZlcmVuY2VSZXN1bHQge1xuXHRcdC8vIDEuIHZhbHVlIHNjb3BlIGluIHRoZSByZWZlcmVuY2luZyBmaWxlIGl0c2VsZlxuXHRcdGNvbnN0IGxvY2FsQmluZGluZyA9IHRoaXMuZmlsZUdyYXBoQmluZGluZ3MuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWxCaW5kaW5nKSB7XG5cdFx0XHRjb25zdCBub2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShsb2NhbEJpbmRpbmcpO1xuXHRcdFx0aWYgKG5vZGUpIHtcblx0XHRcdFx0Y29uc3QgdmFsdWVSZXN1bHQ6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCA9IHsgc3RhdHVzIDogJ3VuaXF1ZScsIG5vZGUgfTtcblx0XHRcdFx0cmV0dXJuIHZhbHVlUmVzdWx0O1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIDIuIGltcG9ydCBzY29wZSDigJQgdGhlIGltcG9ydGVkIG1vZHVsZSdzIGV4cG9ydGVkIGJpbmRpbmdcblx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGltcG9ydGVkICYmICFpbXBvcnRlZC5pc05hbWVzcGFjZSkge1xuXHRcdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKGltcG9ydGVkLnNwZWNpZmllciwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdGlmIChyZXNvbHV0aW9uICYmICFyZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0Y29uc3QgZnVsbFBhdGggPSB0aGlzLmZpbmRHcmFwaEJpbmRpbmdJbk1vZHVsZShyZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgaW1wb3J0ZWQub3JpZ2luYWxOYW1lLCAwKTtcblx0XHRcdFx0aWYgKGZ1bGxQYXRoKSB7XG5cdFx0XHRcdFx0Y29uc3Qgbm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoZnVsbFBhdGgpO1xuXHRcdFx0XHRcdGlmIChub2RlKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBpbXBvcnRSZXN1bHQ6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCA9IHsgc3RhdHVzIDogJ3VuaXF1ZScsIG5vZGUgfTtcblx0XHRcdFx0XHRcdHJldHVybiBpbXBvcnRSZXN1bHQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gMy01LiBjaGFpbiAvIHJvb3QgLyBwcm9ncmFtLXdpZGUgdGllcnNcblx0XHRjb25zdCByZXN1bHQgPSByZXNvbHZlR3JhcGhUeXBlUmVmZXJlbmNlKHRoaXMuZ3JhcGgsIG5hbWUsIHRoaXMuY3VycmVudEdyYXBoQW5jaG9yKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpbmQgYSBncmFwaCBjb25zdHJ1Y3RvciBiaW5kaW5nIGV4cG9ydGVkIGJ5IGEgcmVzb2x2ZWQgbW9kdWxlLFxuXHQgKiBjaGFzaW5nIHJlLWV4cG9ydCBiYXJyZWxzIHdpdGggYSBib3VuZGVkIGRlcHRoLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kR3JhcGhCaW5kaW5nSW5Nb2R1bGUgKG1vZHVsZVBhdGg6IHN0cmluZywgbmFtZTogc3RyaW5nLCBkZXB0aDogbnVtYmVyKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoZGVwdGggPiBNQVhfUkVFWFBPUlRfQ0hBU0VfREVQVEgpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGlyZWN0ID0gdGhpcy5maWxlR3JhcGhCaW5kaW5ncy5nZXQobW9kdWxlUGF0aCk/LmdldChuYW1lKTtcblx0XHRpZiAoZGlyZWN0KSB7XG5cdFx0XHRyZXR1cm4gZGlyZWN0O1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlRXhwb3J0cyA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGNvbnN0IHJlRXhwb3J0U3BlY2lmaWVyID0gcmVFeHBvcnRzPy5nZXQobmFtZSk7XG5cdFx0aWYgKHJlRXhwb3J0U3BlY2lmaWVyKSB7XG5cdFx0XHRjb25zdCBuZXh0UmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKHJlRXhwb3J0U3BlY2lmaWVyLCBtb2R1bGVQYXRoKTtcblx0XHRcdGlmIChuZXh0UmVzb2x1dGlvbiAmJiAhbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRjb25zdCBmb3VuZCA9IHRoaXMuZmluZEdyYXBoQmluZGluZ0luTW9kdWxlKG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgbmFtZSwgZGVwdGggKyAxKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGlmIChzdGFycykge1xuXHRcdFx0Zm9yIChjb25zdCBzdGFyU3BlY2lmaWVyIG9mIHN0YXJzKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoc3RhclNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRcdGlmICghbmV4dFJlc29sdXRpb24gfHwgbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kR3JhcGhCaW5kaW5nSW5Nb2R1bGUobmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBuYW1lLCBkZXB0aCArIDEpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFZhbGlkYXRlIGxpdGVyYWwgbG9va3VwKCkgcGF0aHMgcmVjb3JkZWQgZHVyaW5nIHRoZSB1c2FnZXMgcGFzc1xuXHQgKiBhZ2FpbnN0IHRoZSBjb21wbGV0ZSBncmFwaC4gQSBsb29rdXAgcGF0aCBtYXRjaGluZyBubyB0eXBlIGlzIHdoYXQgdGhlXG5cdCAqIHJ1bnRpbWUgYW5zd2VycyB3aXRoIGB1bmRlZmluZWRgIOKAlCB0aGUgVHlwZUVycm9yIGFycml2ZXMgb25lIGxpbmVcblx0ICogbGF0ZXIgYXQgdGhlIGBuZXdgIOKAlCBzbyBpdCBqb2lucyB0aGUgaGFyZC1mYWlsIGxhdy4gVGhlIHJlbGF0aXZlLWZpcnN0XG5cdCAqIHN0ZXAgYWxyZWFkeSByYW4gaW5zaWRlIHJlc29sdmVMb29rdXBQYXRoOyB3aGF0ZXZlciB3YXMgcmVjb3JkZWQgaXNcblx0ICogdGhlIHJvb3QtcmVzb2x1dGlvbiByZXN1bHQsIHNvIGEgcGxhaW4gZmluZFR5cGUgY2hlY2sgaXMgdGhlIGV4YWN0XG5cdCAqIHJ1bnRpbWUgbGF3LiBTYW1lLW5hbWVkIHR5cGVzIGVsc2V3aGVyZSBpbiB0aGUgZ3JhcGggYXJlIGxpc3RlZCBhc1xuXHQgKiBkaWQteW91LW1lYW4gY2FuZGlkYXRlcy4gUnVucyBvbmNlIHBlciB1c2FnZXMgcGFzcyAocmUtYXJtZWQgYnlcblx0ICogcmVzZXRVc2FnZXMpOyBub24tbGl0ZXJhbCBsb29rdXAgYXJndW1lbnRzIGFyZSBuZXZlciByZWNvcmRlZCBhbmRcblx0ICogc3RheSBiZXN0LWVmZm9ydC5cblx0ICovXG5cdHByaXZhdGUgdmFsaWRhdGVMb29rdXBSZWZlcmVuY2VzICgpOiB2b2lkIHtcblx0XHRpZiAodGhpcy5sb29rdXBSZWZlcmVuY2VzVmFsaWRhdGVkKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHRoaXMubG9va3VwUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IHRydWU7XG5cdFx0Ly8gZ3JvdXAgc2l0ZXMgYnkgcGF0aDogZXZlcnkgZmFpbGluZyBzaXRlIG9mIHRoZSBzYW1lIHBhdGggaXMgbGlzdGVkXG5cdFx0Y29uc3Qgc2l0ZXNCeVBhdGggPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nW10+KCk7XG5cdFx0Zm9yIChjb25zdCByZWYgb2YgdGhpcy5sb29rdXBSZWZlcmVuY2VzKSB7XG5cdFx0XHRjb25zdCBzaXRlcyA9IHNpdGVzQnlQYXRoLmdldChyZWYucGF0aCkgPz8gW107XG5cdFx0XHRzaXRlcy5wdXNoKHJlZi5sb2NhdGlvbik7XG5cdFx0XHRzaXRlc0J5UGF0aC5zZXQocmVmLnBhdGgsIHNpdGVzKTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBbIHR5cGVQYXRoLCBzaXRlcyBdIG9mIHNpdGVzQnlQYXRoKSB7XG5cdFx0XHRpZiAodGhpcy5ncmFwaC5maW5kVHlwZSh0eXBlUGF0aCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHQvLyBkaWQteW91LW1lYW46IHR5cGVzIGNhcnJ5aW5nIHRoZSBzYW1lIG5hbWUgYW55d2hlcmUgaW4gdGhlXG5cdFx0XHQvLyBncmFwaCAobmV2ZXIgYSBmaXJzdC1tYXRjaCBwaWNrIOKAlCB0aGUgZnVsbCBsaXN0IG9ubHkpXG5cdFx0XHRjb25zdCB1bnByZWZpeGVkID0gdHlwZVBhdGgucmVwbGFjZSgvXlteOl0rOjovLCAnJyk7XG5cdFx0XHRjb25zdCBsYXN0U2VnbWVudCA9IHVucHJlZml4ZWQuc3BsaXQoJy4nKS5wb3AoKSA/PyB1bnByZWZpeGVkO1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlcyA9IHRoaXMuZ3JhcGguZ2V0QWxsVHlwZXMoKS5maWx0ZXIodCA9PiB0Lm5hbWUgPT09IGxhc3RTZWdtZW50KTtcblx0XHRcdGlmIChjYW5kaWRhdGVzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHRjb25zdCBub25lRXJyb3I6IFJlc29sdXRpb25FcnJvciA9IHtcblx0XHRcdFx0XHRtZXNzYWdlIDogYFVucmVzb2x2ZWQgbG9va3VwIG9mIG1uZW1vbmljYSB0eXBlICcke3R5cGVQYXRofSc6IG5vIHR5cGUgYXQgdGhhdCBwYXRoIOKAlCBgICtcblx0XHRcdFx0XHRcdCd0aGUgcnVudGltZSB3b3VsZCByZXR1cm4gdW5kZWZpbmVkJyxcblx0XHRcdFx0XHRsb2NhdGlvbnMgOiBzaXRlcyxcblx0XHRcdFx0fTtcblx0XHRcdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKG5vbmVFcnJvcik7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgY2FuZGlkYXRlTG9jYXRpb25zID0gY2FuZGlkYXRlcy5tYXAobiA9PiBgJHtuLnNvdXJjZUZpbGV9OiR7bi5saW5lfToke24uY29sdW1ufWApO1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlUGF0aHMgPSBjYW5kaWRhdGVzLm1hcChuID0+IG4uZnVsbFBhdGgpLmpvaW4oJywgJyk7XG5cdFx0XHRjb25zdCBhbWJpZ3VvdXNFcnJvcjogUmVzb2x1dGlvbkVycm9yID0ge1xuXHRcdFx0XHRtZXNzYWdlIDogYFVucmVzb2x2ZWQgbG9va3VwIG9mIG1uZW1vbmljYSB0eXBlICcke3R5cGVQYXRofSc6IHRoZSBydW50aW1lIHdvdWxkIHJldHVybiBgICtcblx0XHRcdFx0XHRgdW5kZWZpbmVkIOKAlCAke2NhbmRpZGF0ZXMubGVuZ3RofSBncmFwaCB0eXBlKHMpIGNhcnJ5IHRoZSBuYW1lIGAgK1xuXHRcdFx0XHRcdGBvZmYtcm9vdCAoJHtjYW5kaWRhdGVQYXRoc30pOyB1c2UgdGhlIGZ1bGwgZG90dGVkIHBhdGhgLFxuXHRcdFx0XHRsb2NhdGlvbnMgOiBbIC4uLnNpdGVzLCAuLi5jYW5kaWRhdGVMb2NhdGlvbnMgXSxcblx0XHRcdH07XG5cdFx0XHR0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzLnB1c2goYW1iaWd1b3VzRXJyb3IpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgYSBwbGFpbi1UUyB0eXBlIHJlZmVyZW5jZSBzaXRlIHRoYXQgcmVzb2x2ZWQgdG8gbm90aGluZyBhbmRcblx0ICogZmVsbCBiYWNrIHRvIGB1bmtub3duYCwgZm9yIHRoZSBsYXppbHktcnVuIGFtYmlndWl0eSB2YWxpZGF0aW9uLlxuXHQgKiBEZWR1cGVkIGJ5IChuYW1lLCBsb2NhdGlvbik6IGluZmVyVHlwZSBjYW4gdmlzaXQgdGhlIHNhbWUgbm9kZSBtb3JlXG5cdCAqIHRoYW4gb25jZSBwZXIgcGFzcyAoY29uc3RydWN0b3IgcGFyYW1zICsgcHJvcGVydHkgaW5mZXJlbmNlKS5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSAobmFtZTogc3RyaW5nLCByZWZOb2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSB0aGlzLm5vZGVMb2NhdGlvbihyZWZOb2RlKTtcblx0XHRjb25zdCBmaWxlID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGNvbnN0IGFscmVhZHkgPSB0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXMuc29tZSgocmVmKSA9PiByZWYubmFtZSA9PT0gbmFtZSAmJiByZWYubG9jYXRpb24gPT09IGxvY2F0aW9uKTtcblx0XHRpZiAoYWxyZWFkeSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXMucHVzaCh7IG5hbWUsIGxvY2F0aW9uLCBmaWxlIH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb2plY3Qtc291cmNlIGRlY2xhcmF0aW9uIGZpbGVzIGNhcnJ5aW5nIGBuYW1lYCDigJQgb25lIGVudHJ5IHBlclxuXHQgKiBmaWxlLCBzbyBzYW1lLWZpbGUgaW50ZXJmYWNlIG1lcmdpbmcgY291bnRzIG9uY2UgKG5vdCBhbWJpZ3VvdXMpLlxuXHQgKiBFeHRlcm5hbC9hbWJpZW50IGRlY2xhcmF0aW9ucyAoLmQudHMsIGFueXRoaW5nIHVuZGVyIG5vZGVfbW9kdWxlcylcblx0ICogbmV2ZXIgY291bnQ6IGEgdXNlci1sb2NhbCBkZWNsYXJhdGlvbiBhbHdheXMgd2lucyBvdmVyIGEgcGFja2FnZS1cblx0ICogZGVjbGFyZWQgc2FtZS1uYW1lZCB0eXBlLCBzbyBhbiBleHRlcm5hbCBjb2xsaXNpb24gc3RheXMgc29mdC5cblx0ICovXG5cdHByaXZhdGUgcGxhaW5UeXBlRGVjbGFyYXRpb25GaWxlcyAobmFtZTogc3RyaW5nKTogc3RyaW5nW10ge1xuXHRcdGNvbnN0IGZpbGVzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgWyBmaWxlLCBkZWNscyBdIG9mIHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscykge1xuXHRcdFx0aWYgKCF0aGlzLmlzRXh0ZXJuYWxEZWNsRmlsZShmaWxlKSAmJiBkZWNscy5oYXMobmFtZSkpIHtcblx0XHRcdFx0ZmlsZXMucHVzaChmaWxlKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIGZpbGVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIFZhbGlkYXRlIHBsYWluLVRTIHR5cGUgcmVmZXJlbmNlIHNpdGVzIHJlY29yZGVkIGR1cmluZyB0aGUgdXNhZ2VzXG5cdCAqIHBhc3MgYWdhaW5zdCB0aGUgY29tcGxldGUgZGVjbGFyYXRpb24gbWFwLiBBIG5hbWUgZGVjbGFyZWQgaW5cblx0ICogc2V2ZXJhbCBwcm9qZWN0LXNvdXJjZSBmaWxlcyDigJQgd2l0aCBubyBpbXBvcnQgaW4gdGhlIHJlZmVyZW5jaW5nXG5cdCAqIGZpbGUgdG8gYW5jaG9yIGl0IOKAlCBpcyBhbWJpZ3VvdXM6IHNpbGVudGx5IGVtaXR0aW5nIGB1bmtub3duYCB3b3VsZFxuXHQgKiBoaWRlIGEgcmVhbCB0eXBlIHRoZSBhdXRob3IgbWVhbnQsIHNvIGl0IGpvaW5zIHRoZSBoYXJkLWZhaWwgbGF3XG5cdCAqICh0aGUgcGxhaW4tVFMgdGllciBvZiB0aGUgc2FtZSBpZGVudGl0eSBsYXcgYXMgZ3JhcGggcmVmZXJlbmNlcykuXG5cdCAqIEFic2VuY2UgKGdob3N0IG5hbWVzKSBhbmQgZXh0ZXJuYWwgY29sbGlzaW9ucyBzdGF5IHNvZnQgYHVua25vd25gLlxuXHQgKiBSdW5zIG9uY2UgcGVyIHVzYWdlcyBwYXNzIChyZS1hcm1lZCBieSByZXNldFVzYWdlcyksIG1pcnJvcmluZ1xuXHQgKiB2YWxpZGF0ZUxvb2t1cFJlZmVyZW5jZXM6IHJlY29yZGluZyBoYXBwZW5zIG9uIGV2ZXJ5IHBhc3MsIGJ1dCBvbmx5XG5cdCAqIHRoZSB1c2FnZXMgcGFzcyBzZWVzIHRoZSBjb21wbGV0ZSBkZWNsYXJhdGlvbiBtYXAuXG5cdCAqL1xuXHRwcml2YXRlIHZhbGlkYXRlUGxhaW5UeXBlUmVmZXJlbmNlcyAoKTogdm9pZCB7XG5cdFx0aWYgKHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXNWYWxpZGF0ZWQgPSB0cnVlO1xuXHRcdGNvbnN0IHNpdGVzQnlOYW1lID0gbmV3IE1hcDxzdHJpbmcsIHsgbmFtZTogc3RyaW5nOyBsb2NhdGlvbjogc3RyaW5nOyBmaWxlOiBzdHJpbmcgfVtdPigpO1xuXHRcdGZvciAoY29uc3QgcmVmIG9mIHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlcykge1xuXHRcdFx0Y29uc3Qgc2l0ZXMgPSBzaXRlc0J5TmFtZS5nZXQocmVmLm5hbWUpID8/IFtdO1xuXHRcdFx0c2l0ZXMucHVzaChyZWYpO1xuXHRcdFx0c2l0ZXNCeU5hbWUuc2V0KHJlZi5uYW1lLCBzaXRlcyk7XG5cdFx0fVxuXHRcdGZvciAoY29uc3QgWyBuYW1lLCBzaXRlcyBdIG9mIHNpdGVzQnlOYW1lKSB7XG5cdFx0XHQvLyBhbiBpbXBvcnQgYmluZGluZyBpbiB0aGUgcmVmZXJlbmNpbmcgZmlsZSBhbmNob3JzIHRoZSBuYW1lIOKAlFxuXHRcdFx0Ly8gdGhlIGF1dGhvciBhbHJlYWR5IGRpc2FtYmlndWF0ZWQgKHRoZSBpbXBvcnQgbWF5IGp1c3QgcG9pbnRcblx0XHRcdC8vIGF0IGFuIHVuYW5hbHl6YWJsZSBleHRlcm5hbCBtb2R1bGUsIHdoaWNoIHN0YXlzIHNvZnQpXG5cdFx0XHRjb25zdCB1bmFuY2hvcmVkID0gc2l0ZXMuZmlsdGVyKChzaXRlKSA9PiAhdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KHNpdGUuZmlsZSk/LmhhcyhuYW1lKSk7XG5cdFx0XHRpZiAodW5hbmNob3JlZC5sZW5ndGggPT09IDApIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBkZWNsRmlsZXMgPSB0aGlzLnBsYWluVHlwZURlY2xhcmF0aW9uRmlsZXMobmFtZSk7XG5cdFx0XHRpZiAoZGVjbEZpbGVzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBtZXNzYWdlID0gYEFtYmlndW91cyByZWZlcmVuY2UgdG8gdHlwZSAnJHtuYW1lfSc6ICR7ZGVjbEZpbGVzLmxlbmd0aH0gZGVjbGFyYXRpb25zIGAgK1xuXHRcdFx0XHQnc2hhcmUgdGhlIG5hbWUgYW5kIG5vIGltcG9ydCBkaXNhbWJpZ3VhdGVzIOKAlCBpbXBvcnQgdGhlIG9uZSB5b3UgbWVhbic7XG5cdFx0XHRjb25zdCBkZWNsTG9jYXRpb25zID0gZGVjbEZpbGVzLm1hcCgoZmlsZSkgPT4gdGhpcy5wbGFpbkRlY2xMb2NhdGlvbihmaWxlLCBuYW1lKSk7XG5cdFx0XHRjb25zdCBlcnJvcjogUmVzb2x1dGlvbkVycm9yID0ge1xuXHRcdFx0XHRtZXNzYWdlLFxuXHRcdFx0XHRsb2NhdGlvbnMgOiBbIC4uLnVuYW5jaG9yZWQubWFwKChzaXRlKSA9PiBzaXRlLmxvY2F0aW9uKSwgLi4uZGVjbExvY2F0aW9ucyBdXG5cdFx0XHR9O1xuXHRcdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKGVycm9yKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogYGZpbGU6bGluZTpjb2x1bW5gIG9mIGEgcmVjb3JkZWQgZGVjbGFyYXRpb24sIGZvciB0aGUgYW1iaWd1aXR5XG5cdCAqIHJlcG9ydC4gTm9kZXMgcmVjb3JkZWQgZHVyaW5nIHRyYXZlcnNhbCBrZWVwIHRoZWlyIHBvc2l0aW9uczsgYVxuXHQgKiBzeW50aGV0aWMvdW5wb3NpdGlvbmVkIG5vZGUgZmFsbHMgYmFjayB0byB0aGUgZmlsZSBpdHNlbGYuXG5cdCAqL1xuXHRwcml2YXRlIHBsYWluRGVjbExvY2F0aW9uIChmaWxlOiBzdHJpbmcsIG5hbWU6IHN0cmluZyk6IHN0cmluZyB7XG5cdFx0Y29uc3QgZGVjbCA9IHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscy5nZXQoZmlsZSk/LmdldChuYW1lKTtcblx0XHRjb25zdCBub2RlID0gZGVjbD8ubm9kZTtcblx0XHRsZXQgbG9jYXRpb24gPSBgJHtmaWxlfToxOjFgO1xuXHRcdGlmIChub2RlICYmIG5vZGUucG9zID49IDApIHtcblx0XHRcdGNvbnN0IHNvdXJjZUZpbGUgPSBub2RlLmdldFNvdXJjZUZpbGUoKTtcblx0XHRcdGNvbnN0IGxpbmUgPSBzb3VyY2VGaWxlLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKG5vZGUuZ2V0U3RhcnQoKSkubGluZSArIDE7XG5cdFx0XHRjb25zdCBjb2x1bW4gPSBzb3VyY2VGaWxlLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKG5vZGUuZ2V0U3RhcnQoKSkuY2hhcmFjdGVyICsgMTtcblx0XHRcdGxvY2F0aW9uID0gYCR7ZmlsZX06JHtsaW5lfToke2NvbHVtbn1gO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBsb2NhdGlvbjtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhIGhhcmQtZmFpbCBncmFwaCByZWZlcmVuY2UgZXJyb3Igd2l0aCB0aGUgcmVmZXJlbmNlIHNpdGUgYW5kXG5cdCAqIGV2ZXJ5IGNhbmRpZGF0ZSBsb2NhdGlvbi5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkR3JhcGhSZWZlcmVuY2VFcnJvciAoXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdHJlZk5vZGU6IHRzLk5vZGUgfCBzdHJpbmcsXG5cdFx0cmVzdWx0OiBFeHRyYWN0PEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCwgeyBzdGF0dXM6ICdhbWJpZ3VvdXMnIHwgJ25vbmUnIH0+XG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gdHlwZW9mIHJlZk5vZGUgPT09ICdzdHJpbmcnID8gcmVmTm9kZSA6IHRoaXMubm9kZUxvY2F0aW9uKHJlZk5vZGUpO1xuXHRcdGlmIChyZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlTG9jYXRpb25zID0gcmVzdWx0LmNhbmRpZGF0ZXMubWFwKG4gPT4gYCR7bi5zb3VyY2VGaWxlfToke24ubGluZX06JHtuLmNvbHVtbn1gKTtcblx0XHRcdGNvbnN0IGFtYmlndW91c01lc3NhZ2UgPSBgQW1iaWd1b3VzIHJlZmVyZW5jZSB0byBtbmVtb25pY2EgdHlwZSAnJHtuYW1lfSc6IGAgK1xuXHRcdFx0XHRgJHtyZXN1bHQuY2FuZGlkYXRlcy5sZW5ndGh9IHR5cGVzIHNoYXJlIHRoZSBuYW1lIGFuZCBuZWl0aGVyIHRoZSBwYXJlbnQgY2hhaW4gYCArXG5cdFx0XHRcdCdub3IgdGhlIGltcG9ydHMgZGlzYW1iaWd1YXRlJztcblx0XHRcdGNvbnN0IGFtYmlndW91c0Vycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7XG5cdFx0XHRcdG1lc3NhZ2UgICA6IGFtYmlndW91c01lc3NhZ2UsXG5cdFx0XHRcdGxvY2F0aW9ucyA6IFsgbG9jYXRpb24sIC4uLmNhbmRpZGF0ZUxvY2F0aW9ucyBdLFxuXHRcdFx0fTtcblx0XHRcdHRoaXMuZ3JhcGhSZWZlcmVuY2VFcnJvcnMucHVzaChhbWJpZ3VvdXNFcnJvcik7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHVucmVzb2x2ZWRNZXNzYWdlID0gYFVucmVzb2x2ZWQgcmVmZXJlbmNlIHRvIG1uZW1vbmljYSB0eXBlICcke25hbWV9Jzogbm8gdHlwZSBtYXRjaGVzIGAgK1xuXHRcdFx0J2J5IHZhbHVlIHNjb3BlLCBpbXBvcnRzLCBwYXJlbnQgY2hhaW4sIG9yIHJvb3QgcGF0aCc7XG5cdFx0Y29uc3QgdW5yZXNvbHZlZEVycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7IG1lc3NhZ2UgOiB1bnJlc29sdmVkTWVzc2FnZSwgbG9jYXRpb25zIDogWyBsb2NhdGlvbiBdIH07XG5cdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKHVucmVzb2x2ZWRFcnJvcik7XG5cdH1cblxuXHQvKipcblx0ICogTG9jYXRpb24gKGBmaWxlOmxpbmU6Y29sdW1uYCkgb2YgYW4gQVNUIG5vZGUsIGRlcml2ZWQgd2l0aG91dCBwYXJlbnRcblx0ICogcG9pbnRlcnMgd2hlbiBuZWNlc3NhcnkuXG5cdCAqL1xuXHRwcml2YXRlIG5vZGVMb2NhdGlvbiAobm9kZTogdHMuTm9kZSk6IHN0cmluZyB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBub2RlO1xuXHRcdHdoaWxlIChjdXJyZW50ICYmICF0cy5pc1NvdXJjZUZpbGUoY3VycmVudCkpIHtcblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0aWYgKCFjdXJyZW50KSB7XG5cdFx0XHRjb25zdCBmYWxsYmFjayA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRcdHJldHVybiBmYWxsYmFjaztcblx0XHR9XG5cdFx0Y29uc3Qgc3RhcnQgPSBub2RlLmdldFN0YXJ0KGN1cnJlbnQpO1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihjdXJyZW50LCBzdGFydCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtjdXJyZW50LmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRyZXR1cm4gbG9jYXRpb247XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgYWxpYXNlcyBvZiB0aGUgbW5lbW9uaWNhIG1vZHVsZSBvYmplY3QsIGUuZy46XG5cdCAqICAgY29uc3QgbSA9IG1uZW1vbmljYTtcblx0ICogICBjb25zdCBBcHAgPSBtO1xuXHQgKi9cblx0cHJpdmF0ZSB0cmFja01vZHVsZU9iamVjdEFsaWFzZXMgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSB8fCAhdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGluaXRpYWxpemVyIH0gPSBub2RlO1xuXHRcdGlmICghaW5pdGlhbGl6ZXIpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGluaXRpYWxpemVyKSAmJiB0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoaW5pdGlhbGl6ZXIudGV4dCkpIHtcblx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChub2RlLm5hbWUudGV4dCk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFRyYWNrIGN1c3RvbSBjb2xsZWN0aW9uIHZhcmlhYmxlcywgZS5nLjpcblx0ICogICBjb25zdCBNeUNvbGxlY3Rpb24gPSBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKTtcblx0ICogICBjb25zdCBPdGhlciA9IE15Q29sbGVjdGlvbjtcblx0ICpcblx0ICogQWxzbyBkZXRlY3RzIE9wdGlvbiBCIHVzZXItcHJvdmlkZWQgcmVnaXN0cnkgaW50ZXJmYWNlczpcblx0ICogICBleHBvcnQgaW50ZXJmYWNlIE15Q29sbGVjdGlvblJlZ2lzdHJ5IHt9XG5cdCAqICAgY29uc3QgTXlDb2xsZWN0aW9uID0gY3JlYXRlVHlwZXNDb2xsZWN0aW9uPE15Q29sbGVjdGlvblJlZ2lzdHJ5PigpO1xuXHQgKi9cblx0cHJpdmF0ZSB0cmFja0NvbGxlY3Rpb25BbGlhc2VzIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgfHwgIXRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBpbml0aWFsaXplciB9ID0gbm9kZTtcblx0XHRpZiAoIWluaXRpYWxpemVyKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRGlyZWN0IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIGNhbGxcblx0XHRpZiAodGhpcy5pc0NyZWF0ZVR5cGVzQ29sbGVjdGlvbkNhbGwoaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHQvLyBUaGUgQ0xJIHJlLWFuYWx5emVzIGV2ZXJ5IGZpbGUgb24gdGhlIHVzYWdlcyBwYXNzIChzZWUgcmVzZXRVc2FnZXMpOlxuXHRcdFx0Ly8gbWludGluZyBhIGZyZXNoIGlkIGhlcmUgd291bGQgcmUtcmVnaXN0ZXIgdGhlIGNvbGxlY3Rpb24ncyB0eXBlc1xuXHRcdFx0Ly8gdW5kZXIgYSBzZWNvbmQgYGNvbGxlY3Rpb25JZDo6YCBwcmVmaXggYW5kIGR1cGxpY2F0ZSBldmVyeSBlbWlzc2lvbi5cblx0XHRcdGNvbnN0IGNvbGxlY3Rpb25JZCA9IHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5nZXQobm9kZS5uYW1lLnRleHQpID8/IHRoaXMubmV4dENvbGxlY3Rpb25JZCgpO1xuXHRcdFx0dGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLnNldChub2RlLm5hbWUudGV4dCwgY29sbGVjdGlvbklkKTtcblxuXHRcdFx0Y29uc3QgcmVnaXN0cnlJbnRlcmZhY2VOYW1lID0gdGhpcy5leHRyYWN0UmVnaXN0cnlJbnRlcmZhY2VOYW1lKFxuXHRcdFx0XHRpbml0aWFsaXplciBhcyB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHRcdFx0c291cmNlRmlsZVxuXHRcdFx0KTtcblx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihzb3VyY2VGaWxlLCBub2RlLmdldFN0YXJ0KCkpO1xuXHRcdFx0dGhpcy5jb2xsZWN0aW9uSW5mby5zZXQoY29sbGVjdGlvbklkLCB7XG5cdFx0XHRcdHZhcmlhYmxlTmFtZSAgICAgICAgICA6IG5vZGUubmFtZS50ZXh0LFxuXHRcdFx0XHRzb3VyY2VGaWxlICAgICAgICAgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRyZWdpc3RyeUludGVyZmFjZU5hbWUgOiByZWdpc3RyeUludGVyZmFjZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgICAgICAgICAgICAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gICAgICAgICAgICAgICAgOiBjaGFyYWN0ZXIgKyAxXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBBbGlhcyBvZiBhbm90aGVyIGNvbGxlY3Rpb24gdmFyaWFibGVcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGluaXRpYWxpemVyKSkge1xuXHRcdFx0Y29uc3QgZXhpc3RpbmcgPSB0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuZ2V0KGluaXRpYWxpemVyLnRleHQpO1xuXHRcdFx0aWYgKGV4aXN0aW5nKSB7XG5cdFx0XHRcdHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5zZXQobm9kZS5uYW1lLnRleHQsIGV4aXN0aW5nKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0aGUgcmVnaXN0cnkgaW50ZXJmYWNlIG5hbWUgZnJvbSBjcmVhdGVUeXBlc0NvbGxlY3Rpb248UmVnaXN0cnk+KClcblx0ICogd2hlbiB0aGUgaW50ZXJmYWNlIGlzIGRlY2xhcmVkIGluIHRoZSBzYW1lIHNvdXJjZSBmaWxlLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UmVnaXN0cnlJbnRlcmZhY2VOYW1lIChcblx0XHRjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlXG5cdCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgdHlwZUFyZ3MgPSBjYWxsLnR5cGVBcmd1bWVudHM7XG5cdFx0aWYgKCF0eXBlQXJncyB8fCB0eXBlQXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgWyBmaXJzdFR5cGVBcmcgXSA9IHR5cGVBcmdzO1xuXHRcdGlmICghdHMuaXNUeXBlUmVmZXJlbmNlTm9kZShmaXJzdFR5cGVBcmcpIHx8ICF0cy5pc0lkZW50aWZpZXIoZmlyc3RUeXBlQXJnLnR5cGVOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBuYW1lID0gZmlyc3RUeXBlQXJnLnR5cGVOYW1lLnRleHQ7XG5cblx0XHQvLyBDb25maXJtIHRoZSBpbnRlcmZhY2UgZXhpc3RzIGluIHRoZSBzYW1lIHNvdXJjZSBmaWxlLlxuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIHNvdXJjZUZpbGUuc3RhdGVtZW50cykge1xuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc0ludGVyZmFjZURlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiZcblx0XHRcdFx0c3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZVxuXHRcdFx0KSB7XG5cdFx0XHRcdHJldHVybiBuYW1lO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogU3RhbXAgYSBub2RlIHdpdGggaXRzIGNvbGxlY3Rpb24ncyBlbWlzc2lvbiBpbmZvOiB0aGUgT3B0aW9uIEIgcmVnaXN0cnlcblx0ICogaW50ZXJmYWNlIG5hbWUgYW5kIHRoZSBjb2xsZWN0aW9uJ3MgaG9tZSBmaWxlIOKAlCB0aGUgbW9kdWxlIHRoZSBnZW5lcmF0ZWRcblx0ICogYXVnbWVudGF0aW9uIG11c3QgdGFyZ2V0ICh0aGUgaW50ZXJmYWNlIGlzIGNvbmZpcm1lZCBkZWNsYXJlZCB0aGVyZSkuXG5cdCAqIEEgdHlwZSdzIG93biBzb3VyY2VGaWxlIGlzIE5PVCB0aGUgdGFyZ2V0OiBtdWx0aS1maWxlIGNvbGxlY3Rpb25zIGRlZmluZVxuXHQgKiB0eXBlcyBhY3Jvc3MgbWFueSBtb2R1bGVzIHdoaWxlIHRoZSBpbnRlcmZhY2UgbGl2ZXMgYXQgdGhlXG5cdCAqIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIGNhbGwgc2l0ZS5cblx0ICovXG5cdHByaXZhdGUgYXBwbHlDb2xsZWN0aW9uRW1pc3Npb25JbmZvIChub2RlOiBUeXBlTm9kZSwgY29sbGVjdGlvbklkPzogc3RyaW5nKTogdm9pZCB7XG5cdFx0aWYgKCFjb2xsZWN0aW9uSWQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgaW5mbyA9IHRoaXMuY29sbGVjdGlvbkluZm8uZ2V0KGNvbGxlY3Rpb25JZCk7XG5cdFx0aWYgKCFpbmZvKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdG5vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lID0gaW5mby5yZWdpc3RyeUludGVyZmFjZU5hbWU7XG5cdFx0bm9kZS5jb2xsZWN0aW9uU291cmNlRmlsZSA9IGluZm8uc291cmNlRmlsZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhbiBleHByZXNzaW9uIGlzIGEgY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgY2FsbC5cblx0ICogSGFuZGxlczpcblx0ICogICBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKVxuXHQgKiAgIGN0YygpIC8vIGFsaWFzZWQgaW1wb3J0XG5cdCAqICAgbW5lbW9uaWNhLmNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIC8vIG1vZHVsZSBvYmplY3QgbWV0aG9kXG5cdCAqICAgbS5jcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSAvLyBhbGlhc2VkIG1vZHVsZSBvYmplY3Rcblx0ICovXG5cdHByaXZhdGUgaXNDcmVhdGVUeXBlc0NvbGxlY3Rpb25DYWxsIChub2RlOiB0cy5Ob2RlKTogbm9kZSBpcyB0cy5DYWxsRXhwcmVzc2lvbiB7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXHRcdGNvbnN0IGV4cHIgPSBub2RlLmV4cHJlc3Npb247XG5cblx0XHQvLyBEaXJlY3QgY2FsbCBvciBhbGlhc2VkIGltcG9ydDogY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgLyBjdGMoKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLnRleHQgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nIHx8XG5cdFx0XHRcdHRoaXMuY3JlYXRlVHlwZXNDb2xsZWN0aW9uVmFyaWFibGVzLmhhcyhleHByLnRleHQpO1xuXHRcdH1cblxuXHRcdC8vIE1vZHVsZSBvYmplY3QgbWV0aG9kOiBtbmVtb25pY2EuY3JlYXRlVHlwZXNDb2xsZWN0aW9uKClcblx0XHRpZiAoXG5cdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSAmJlxuXHRcdFx0ZXhwci5uYW1lLnRleHQgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIoZXhwci5leHByZXNzaW9uKSAmJlxuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuaGFzKGV4cHIuZXhwcmVzc2lvbi50ZXh0KVxuXHRcdCkge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdlbmVyYXRlIGEgdW5pcXVlIGNvbGxlY3Rpb24gaWRlbnRpZmllci5cblx0ICovXG5cdHByaXZhdGUgbmV4dENvbGxlY3Rpb25JZCAoKTogc3RyaW5nIHtcblx0XHR0aGlzLmNvbGxlY3Rpb25Db3VudGVyKys7XG5cdFx0Y29uc3QgcmVzdWx0ID0gYGNvbGxlY3Rpb25fJHt0aGlzLmNvbGxlY3Rpb25Db3VudGVyfWA7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhIG5vZGUgaXMgYSBkZWZpbmUoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGlzRGVmaW5lQ2FsbCAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuQ2FsbEV4cHJlc3Npb24ge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBkaXJlY3QgY2FsbDogZGVmaW5lKCdUeXBlTmFtZScsIC4uLilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2RlZmluZScpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBtZXRob2QgY2FsbDogU29tZVR5cGUuZGVmaW5lKCdTdWJUeXBlJywgLi4uKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuIGV4cHJlc3Npb24ubmFtZT8udGV4dCA9PT0gJ2RlZmluZSc7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGEgbm9kZSBpcyBhIGxhenkoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGlzTGF6eUNhbGwgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkNhbGxFeHByZXNzaW9uIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IG5vZGU7XG5cblx0XHQvLyBDaGVjayBmb3IgZGlyZWN0IGNhbGw6IGxhenkoJ1R5cGVOYW1lJywgZ2V0dGVyLCAuLi4pXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLnRleHQgPT09ICdsYXp5Jykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIG1ldGhvZCBjYWxsOiBTb21lVHlwZS5sYXp5KCdTdWJUeXBlJywgZ2V0dGVyLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gZXhwcmVzc2lvbi5uYW1lPy50ZXh0ID09PSAnbGF6eSc7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IGNvbmZpZyBvcHRpb25zIGZyb20gYW4gb2JqZWN0IGxpdGVyYWxcblx0XHQqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbCAoY29uZmlnQXJnOiB0cy5PYmplY3RMaXRlcmFsRXhwcmVzc2lvbik6XG5cdFx0eyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9IHtcblx0XHRjb25zdCBjb25maWc6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSA9IHt9O1xuXG5cdFx0Zm9yIChjb25zdCBwcm9wIG9mIGNvbmZpZ0FyZy5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFzc2lnbm1lbnQocHJvcCkgJiYgdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBwcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0aWYgKHByb3BOYW1lID09PSAnc3RyaWN0Q2hhaW4nICYmIHByb3AuaW5pdGlhbGl6ZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5zdHJpY3RDaGFpbiA9IHRydWU7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdzdHJpY3RDaGFpbicgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5zdHJpY3RDaGFpbiA9IGZhbHNlO1xuXHRcdFx0XHR9IGVsc2UgaWYgKHByb3BOYW1lID09PSAnYmxvY2tFcnJvcnMnICYmIHByb3AuaW5pdGlhbGl6ZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5ibG9ja0Vycm9ycyA9IHRydWU7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdibG9ja0Vycm9ycycgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5ibG9ja0Vycm9ycyA9IGZhbHNlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGNvbmZpZztcblx0fVxuXG5cdC8qKlxuXHRcdCogRXh0cmFjdCBjb25maWcgb3B0aW9ucyBmcm9tIGRlZmluZSgpIGNhbGxcblx0XHQqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25maWcgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogeyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9IHtcblx0XHQvLyBDb25maWcgaXMgdGhlIHRoaXJkIGFyZ3VtZW50OiBkZWZpbmUoJ05hbWUnLCBoYW5kbGVyLCBjb25maWcpXG5cdFx0Y29uc3QgWyAsICwgY29uZmlnQXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblx0XHRpZiAoIWNvbmZpZ0FyZyB8fCAhdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihjb25maWdBcmcpKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgY29uZmlnUmVzdWx0ID0gdGhpcy5leHRyYWN0Q29uZmlnRnJvbU9iamVjdExpdGVyYWwoY29uZmlnQXJnKTtcblx0XHRyZXR1cm4gY29uZmlnUmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0KiBDaGVjayBpZiBhIG5vZGUgaXMgYSBAZGVjb3JhdGUoKSBkZWNvcmF0b3Jcblx0XHQqL1xuXHRwcml2YXRlIGlzRGVjb3JhdGVEZWNvcmF0b3IgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkRlY29yYXRvciB7XG5cdFx0aWYgKCF0cy5pc0RlY29yYXRvcihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBAZGVjb3JhdGVcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2RlY29yYXRlJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIEBkZWNvcmF0ZSgpIG9yIEBkZWNvcmF0ZShQYXJlbnRUeXBlKVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRjb25zdCBmbk5hbWUgPSBleHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGZuTmFtZSkgJiYgZm5OYW1lLnRleHQgPT09ICdkZWNvcmF0ZScpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cblx0XHRcdC8vIENoZWNrIGZvciBATXlDb2xsZWN0aW9uLmRlY29yYXRlKCkgd2hlcmUgTXlDb2xsZWN0aW9uIGlzIGEgY3VzdG9tIGNvbGxlY3Rpb25cblx0XHRcdGlmIChcblx0XHRcdFx0dHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZm5OYW1lKSAmJlxuXHRcdFx0XHRmbk5hbWUubmFtZS50ZXh0ID09PSAnZGVjb3JhdGUnICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihmbk5hbWUuZXhwcmVzc2lvbikgJiZcblx0XHRcdFx0dGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmhhcyhmbk5hbWUuZXhwcmVzc2lvbi50ZXh0KVxuXHRcdFx0KSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBNYXJrIGEgY2FsbCBleHByZXNzaW9uIGFzIHByb2Nlc3NlZCBhbmQgcmV0dXJuIHdoZXRoZXIgaXQgYWxyZWFkeSB3YXMuXG5cdCAqL1xuXHRwcml2YXRlIG1hcmtQcm9jZXNzZWQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogYm9vbGVhbiB7XG5cdFx0aWYgKHRoaXMucHJvY2Vzc2VkQ2FsbHMuaGFzKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cdFx0dGhpcy5wcm9jZXNzZWRDYWxscy5hZGQoY2FsbCk7XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb2Nlc3MgYSBkZWZpbmUoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NEZWZpbmVDYWxsIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGlmIHRoaXMgZXhhY3QgY2FsbCBoYXMgYWxyZWFkeSBiZWVuIHByb2Nlc3NlZCAocHJldmVudHMgZHVwbGljYXRlcyBmcm9tIGNoYWluZWQgY2FsbHMpXG5cdFx0aWYgKHRoaXMubWFya1Byb2Nlc3NlZChjYWxsKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEdldCB0aGUgdHlwZSBuYW1lIGFuZCBzb3VyY2UgY29udGV4dCBmcm9tIGFyZ3VtZW50c1xuXHRcdGNvbnN0IGRlZmluZUNvbnRleHQgPSB0aGlzLmV4dHJhY3REZWZpbmVDb250ZXh0KGNhbGwpO1xuXG5cdFx0Ly8gRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBkZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKSwgd2Ugd2FudCB0aGUgcG9zaXRpb24gb2YgdGhlIC5kZWZpbmUoJ0InKSBwYXJ0XG5cdFx0Ly8gbm90IHRoZSBzdGFydCBvZiB0aGUgZW50aXJlIGV4cHJlc3Npb25cblx0XHRsZXQgcG9zaXRpb25Ob2RlOiB0cy5Ob2RlID0gY2FsbDtcblxuXHRcdC8vIElmIHRoaXMgaXMgYSBjaGFpbmVkIGNhbGwsIGdldCB0aGUgcG9zaXRpb24gb2YgdGhlIHByb3BlcnR5IGFjY2VzcyBleHByZXNzaW9uXG5cdFx0Ly8gd2hpY2ggaXMgdGhlIC5kZWZpbmUgcGFydFxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHQvLyBUaGUgZXhwcmVzc2lvbiBpcyB0aGUgcHJvcGVydHkgYWNjZXNzOiAoZGVmaW5lKCdSb290QXN5bmMnLCAuLi4pKS5kZWZpbmVcblx0XHRcdC8vIFdlIHdhbnQgdGhlIHBvc2l0aW9uIG9mIGp1c3QgdGhlIC5kZWZpbmUgcGFydFxuXHRcdFx0Ly8gVGhpcyBpcyB0aGUgJ2RlZmluZScgaWRlbnRpZmllclxuXHRcdFx0cG9zaXRpb25Ob2RlID0gY2FsbC5leHByZXNzaW9uLm5hbWU7XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnRQb3MgPSBwb3NpdGlvbk5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSk7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKHNvdXJjZUZpbGUsIHN0YXJ0UG9zKTtcblxuXHRcdGlmICghZGVmaW5lQ29udGV4dC50eXBlTmFtZSkge1xuXHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdG1lc3NhZ2UgOiAnQ291bGQgbm90IGV4dHJhY3QgdHlwZSBuYW1lIGZyb20gZGVmaW5lKCkgY2FsbCcsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyB0eXBlTmFtZSB9ID0gZGVmaW5lQ29udGV4dDtcblxuXHRcdC8vIERldGVybWluZSBwYXJlbnQgdHlwZSBhbmQgY29sbGVjdGlvbiBiYXNlZCBvbiB0aGUgY2FsbCBzb3VyY2UuXG5cdFx0Y29uc3QgcGFyZW50Tm9kZSA9IGRlZmluZUNvbnRleHQucGFyZW50VHlwZTtcblx0XHRjb25zdCB7IGNvbGxlY3Rpb25JZCB9ID0gZGVmaW5lQ29udGV4dDtcblxuXHRcdC8vIEV4dHJhY3QgY29uZmlnIG9wdGlvbnNcblx0XHRjb25zdCBjb25maWcgPSB0aGlzLmV4dHJhY3RDb25maWcoY2FsbCk7XG5cblx0XHQvLyBDcmVhdGUgdHlwZSBub2RlIGZpcnN0IHNvIGl0cyBpbnRlcm5hbCBmdWxsUGF0aCAoaW5jbHVkaW5nIGFueSBjb2xsZWN0aW9uIHByZWZpeCkgaXMgcmVzb2x2ZWQuXG5cdFx0Y29uc3Qgbm9kZSA9IFR5cGVHcmFwaEltcGwuY3JlYXRlTm9kZShcblx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0cGFyZW50Tm9kZSxcblx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRsaW5lICsgMSxcblx0XHRcdGNoYXJhY3RlciArIDEsXG5cdFx0XHRjb2xsZWN0aW9uSWRcblx0XHQpO1xuXHRcdHRoaXMuYXBwbHlDb2xsZWN0aW9uRW1pc3Npb25JbmZvKG5vZGUsIGNvbGxlY3Rpb25JZCk7XG5cblx0XHQvLyBTYW1lLW5hbWVzcGFjZSBkdXBsaWNhdGUgZGV0ZWN0aW9uIChoYXJkLWZhaWwgbGF3KToga2V5IGJ5IHRoZVxuXHRcdC8vIHJ1bnRpbWUgbmFtZXNwYWNlIOKAlCBjb2xsZWN0aW9uIHJvb3RzIGA8Y29sbGVjdGlvbj46OjxuYW1lPmAsIG9yXG5cdFx0Ly8gYDxwYXJlbnRGdWxsUGF0aD4uPG5hbWU+YCBmb3Igc3VidHlwZXNcblx0XHR0aGlzLnJlY29yZERlZmluZVNpdGUoXG5cdFx0XHRwYXJlbnROb2RlID8gYCR7cGFyZW50Tm9kZS5mdWxsUGF0aH0uJHt0eXBlTmFtZX1gIDogYCR7Y29sbGVjdGlvbklkID8/ICdkZWZhdWx0J306OiR7dHlwZU5hbWV9YCxcblx0XHRcdGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gXG5cdFx0KTtcblxuXHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGNvbnN0cnVjdG9yIGZ1bmN0aW9uIOKAlCB0aGUgbmV3IG5vZGUgYW5jaG9yc1xuXHRcdC8vIHJlbGF0aXZlLWZpcnN0IGdyYXBoIHJlZmVyZW5jZSByZXNvbHV0aW9uIHdoaWxlIGl0cyBvd24gc2lnbmF0dXJlXG5cdFx0Ly8gaXMgYmVpbmcgcmVhZFxuXHRcdGNvbnN0IHByZXZpb3VzQW5jaG9yID0gdGhpcy5jdXJyZW50R3JhcGhBbmNob3I7XG5cdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBub2RlO1xuXHRcdHRyeSB7XG5cdFx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzKGNhbGwpO1xuXG5cdFx0XHQvLyBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZm9yIFR5cGVSZWdpc3RyeSBzaWduYXR1cmVcblx0XHRcdG5vZGUuY29uc3RydWN0b3JQYXJhbXMgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyhjYWxsKTtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBwcmV2aW91c0FuY2hvcjtcblx0XHR9XG5cblx0XHQvLyBBc3luYyBjb25zdHJ1Y3RvciBkZXRlY3Rpb24gKGFzeW5jIG1vZGlmaWVyLCBzeW50YWN0aWMgb25seSlcblx0XHRub2RlLmlzQXN5bmMgPSB0aGlzLmlzQXN5bmNDb25zdHJ1Y3RIYW5kbGVyKHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yRXhwcmVzc2lvbihjYWxsKSk7XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGhcblx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChwYXJlbnROb2RlLCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KG5vZGUpO1xuXHRcdH1cblxuXHRcdC8vIENyZWF0ZSBkZWZpbml0aW9uIGluZm8gdXNpbmcgdGhlIG5vZGUncyByZXNvbHZlZCBmdWxsUGF0aFxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiBwYXJlbnROb2RlID8gcGFyZW50Tm9kZS5mdWxsUGF0aCA6IG51bGwsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IGNvbmZpZy5zdHJpY3RDaGFpbiA/PyB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBjb25maWcuYmxvY2tFcnJvcnMgPz8gZmFsc2UsXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChub2RlLmZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0XHR0aGlzLmVkc1Njb3BlQnlOb2RlLnNldChjYWxsLCBub2RlLmZ1bGxQYXRoKTtcblxuXHRcdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnQ6IGNvbnN0IFVzZXIgPSBkZWZpbmUoJ1VzZXJFbnRpdHknLCAuLi4pIC0+IG1hcCBcIlVzZXJcIiB0byBcIlVzZXJFbnRpdHlcIlxuXHRcdC8vIEEgbXVsdGktaG9wIGluaXRpYWxpemVyIGJpbmRzIHRoZSBMQVNUIGhvcDogZGVmaW5lKCkgcmV0dXJucyB0aGVcblx0XHQvLyBkZWZpbmVkIHR5cGUncyBjb25zdHJ1Y3RvciAoRjE4KVxuXHRcdHRoaXMudHJhY2tWYXJpYWJsZUFzc2lnbm1lbnQoY2FsbCwgcGFyZW50Tm9kZSwgbm9kZS5mdWxsUGF0aCk7XG5cdH1cblxuXHQvKipcblx0ICogUHJvY2VzcyBhIGxhenkoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NMYXp5Q2FsbCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHQvLyBDaGVjayBpZiB0aGlzIGV4YWN0IGNhbGwgaGFzIGFscmVhZHkgYmVlbiBwcm9jZXNzZWQgKHByZXZlbnRzIGR1cGxpY2F0ZXMgZnJvbSBjaGFpbmVkIGNhbGxzKVxuXHRcdGlmICh0aGlzLm1hcmtQcm9jZXNzZWQoY2FsbCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBHZXQgdGhlIHR5cGUgbmFtZSBhbmQgc291cmNlIGNvbnRleHQgZnJvbSBhcmd1bWVudHNcblx0XHRjb25zdCBsYXp5Q29udGV4dCA9IHRoaXMuZXh0cmFjdExhenlDb250ZXh0KGNhbGwsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBkZWZpbmUoJ0EnKS5sYXp5KCdCJyksIHdlIHdhbnQgdGhlIHBvc2l0aW9uIG9mIHRoZSAubGF6eSgnQicpIHBhcnRcblx0XHQvLyBub3QgdGhlIHN0YXJ0IG9mIHRoZSBlbnRpcmUgZXhwcmVzc2lvblxuXHRcdGxldCBwb3NpdGlvbk5vZGU6IHRzLk5vZGUgPSBjYWxsO1xuXG5cdFx0Ly8gSWYgdGhpcyBpcyBhIGNoYWluZWQgY2FsbCwgZ2V0IHRoZSBwb3NpdGlvbiBvZiB0aGUgcHJvcGVydHkgYWNjZXNzIGV4cHJlc3Npb25cblx0XHQvLyB3aGljaCBpcyB0aGUgLmxhenkgcGFydFxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHQvLyBUaGUgZXhwcmVzc2lvbiBpcyB0aGUgcHJvcGVydHkgYWNjZXNzOiAoZGVmaW5lKCdSb290QXN5bmMnLCAuLi4pKS5sYXp5XG5cdFx0XHQvLyBXZSB3YW50IHRoZSBwb3NpdGlvbiBvZiBqdXN0IHRoZSAubGF6eSBwYXJ0XG5cdFx0XHQvLyBUaGlzIGlzIHRoZSAnbGF6eScgaWRlbnRpZmllclxuXHRcdFx0cG9zaXRpb25Ob2RlID0gY2FsbC5leHByZXNzaW9uLm5hbWU7XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnRQb3MgPSBwb3NpdGlvbk5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSk7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKHNvdXJjZUZpbGUsIHN0YXJ0UG9zKTtcblxuXHRcdGlmICghbGF6eUNvbnRleHQudHlwZU5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0NvdWxkIG5vdCBleHRyYWN0IHR5cGUgbmFtZSBmcm9tIGxhenkoKSBjYWxsJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IHR5cGVOYW1lIH0gPSBsYXp5Q29udGV4dDtcblxuXHRcdC8vIERldGVybWluZSBwYXJlbnQgdHlwZSBhbmQgY29sbGVjdGlvbiBiYXNlZCBvbiB0aGUgY2FsbCBzb3VyY2UuXG5cdFx0Y29uc3QgcGFyZW50Tm9kZSA9IGxhenlDb250ZXh0LnBhcmVudFR5cGU7XG5cdFx0Y29uc3QgeyBjb2xsZWN0aW9uSWQgfSA9IGxhenlDb250ZXh0O1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25maWcgb3B0aW9uc1xuXHRcdGNvbnN0IGNvbmZpZyA9IHRoaXMuZXh0cmFjdExhenlDb25maWcoY2FsbCk7XG5cblx0XHQvLyBDcmVhdGUgdHlwZSBub2RlIGZpcnN0IHNvIGl0cyBpbnRlcm5hbCBmdWxsUGF0aCAoaW5jbHVkaW5nIGFueSBjb2xsZWN0aW9uIHByZWZpeCkgaXMgcmVzb2x2ZWQuXG5cdFx0Y29uc3Qgbm9kZSA9IFR5cGVHcmFwaEltcGwuY3JlYXRlTm9kZShcblx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0cGFyZW50Tm9kZSxcblx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRsaW5lICsgMSxcblx0XHRcdGNoYXJhY3RlciArIDEsXG5cdFx0XHRjb2xsZWN0aW9uSWRcblx0XHQpO1xuXHRcdHRoaXMuYXBwbHlDb2xsZWN0aW9uRW1pc3Npb25JbmZvKG5vZGUsIGNvbGxlY3Rpb25JZCk7XG5cblx0XHQvLyBTYW1lLW5hbWVzcGFjZSBkdXBsaWNhdGUgZGV0ZWN0aW9uIChoYXJkLWZhaWwgbGF3KVxuXHRcdHRoaXMucmVjb3JkRGVmaW5lU2l0ZShcblx0XHRcdHBhcmVudE5vZGUgPyBgJHtwYXJlbnROb2RlLmZ1bGxQYXRofS4ke3R5cGVOYW1lfWAgOiBgJHtjb2xsZWN0aW9uSWQgPz8gJ2RlZmF1bHQnfTo6JHt0eXBlTmFtZX1gLFxuXHRcdFx0YCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWBcblx0XHQpO1xuXG5cdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gdGhlIGNvbnN0cnVjdG9yIHJldHVybmVkIGJ5IHRoZSBsYXp5IGdldHRlclxuXHRcdC8vIOKAlCB0aGUgbmV3IG5vZGUgYW5jaG9ycyByZWxhdGl2ZS1maXJzdCBncmFwaCByZWZlcmVuY2UgcmVzb2x1dGlvblxuXHRcdGNvbnN0IHByZXZpb3VzQW5jaG9yID0gdGhpcy5jdXJyZW50R3JhcGhBbmNob3I7XG5cdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBub2RlO1xuXHRcdHRyeSB7XG5cdFx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzKGNhbGwpO1xuXG5cdFx0XHQvLyBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZm9yIFR5cGVSZWdpc3RyeSBzaWduYXR1cmVcblx0XHRcdG5vZGUuY29uc3RydWN0b3JQYXJhbXMgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyhjYWxsKTtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBwcmV2aW91c0FuY2hvcjtcblx0XHR9XG5cblx0XHQvLyBBc3luYyBjb25zdHJ1Y3RvciBkZXRlY3Rpb24gKGFzeW5jIG1vZGlmaWVyLCBzeW50YWN0aWMgb25seSlcblx0XHRub2RlLmlzQXN5bmMgPSB0aGlzLmlzQXN5bmNDb25zdHJ1Y3RIYW5kbGVyKHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yRXhwcmVzc2lvbihjYWxsKSk7XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGhcblx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChwYXJlbnROb2RlLCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KG5vZGUpO1xuXHRcdH1cblxuXHRcdC8vIENyZWF0ZSBkZWZpbml0aW9uIGluZm8gdXNpbmcgdGhlIG5vZGUncyByZXNvbHZlZCBmdWxsUGF0aFxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiBwYXJlbnROb2RlID8gcGFyZW50Tm9kZS5mdWxsUGF0aCA6IG51bGwsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IGNvbmZpZy5zdHJpY3RDaGFpbiA/PyB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBjb25maWcuYmxvY2tFcnJvcnMgPz8gZmFsc2UsXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChub2RlLmZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0XHR0aGlzLmVkc1Njb3BlQnlOb2RlLnNldChjYWxsLCBub2RlLmZ1bGxQYXRoKTtcblxuXHRcdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnQ6IGNvbnN0IExhenlUeXBlID0gbGF6eSgnTGF6eVR5cGUnLCAuLi4pIC0+IG1hcCBcIkxhenlUeXBlXCIgLT4gXCJMYXp5VHlwZVwiXG5cdFx0Ly8gRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBjb25zdCBYID0gbGF6eSgnQScpLmRlZmluZSgnQicpLCB3ZSB3YW50IHRvIG1hcCBYIC0+IEEgKHRoZSByb290KVxuXHRcdHRoaXMudHJhY2tWYXJpYWJsZUFzc2lnbm1lbnQoY2FsbCwgcGFyZW50Tm9kZSwgbm9kZS5mdWxsUGF0aCk7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBsYXp5KCkgY2FsbCBhcmd1bWVudHMgaW50byBhIG5vcm1hbGl6ZWQgc2hhcGUuXG5cdCAqIEhhbmRsZXMgbmFtZWQvdW5uYW1lZCBhbmQgZXhwbGljaXQtc291cmNlIGZvcm1zLCBib3RoIGFzIGZyZWUgY2FsbHNcblx0ICogYW5kIGFzIG1ldGhvZCBjYWxscy5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdExhenlDYWxsQXJncyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7XG5cdFx0c291cmNlPzogdHMuRXhwcmVzc2lvbjtcblx0XHRuYW1lPzogc3RyaW5nO1xuXHRcdGdldHRlcjogdHMuRXhwcmVzc2lvbjtcblx0XHRjb25maWc/OiB0cy5FeHByZXNzaW9uO1xuXHR9IHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBhcmdzID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0Y29uc3QgaXNNZXRob2RDYWxsID0gdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKTtcblxuXHRcdGlmIChpc01ldGhvZENhbGwpIHtcblx0XHRcdC8vIFNvdXJjZSBpcyB0aGUgb2JqZWN0IG9mIHRoZSBwcm9wZXJ0eSBhY2Nlc3M6IFR5cGUubGF6eSguLi4pXG5cdFx0XHRjb25zdCBzb3VyY2UgPSBjYWxsLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgWyBtZXRob2RGaXJzdEFyZyBdID0gYXJncztcblx0XHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwobWV0aG9kRmlyc3RBcmcpKSB7XG5cdFx0XHRcdC8vIFR5cGUubGF6eSgnTmFtZScsIGdldHRlciwgY29uZmlnPylcblx0XHRcdFx0aWYgKGFyZ3MubGVuZ3RoIDwgMikge1xuXHRcdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHRzb3VyY2UsXG5cdFx0XHRcdFx0bmFtZSAgIDogbWV0aG9kRmlyc3RBcmcudGV4dCxcblx0XHRcdFx0XHRnZXR0ZXIgOiBhcmdzWyAxIF0sXG5cdFx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMiBdLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXHRcdFx0Ly8gVHlwZS5sYXp5KGdldHRlciwgY29uZmlnPylcblx0XHRcdHJldHVybiB7XG5cdFx0XHRcdHNvdXJjZSxcblx0XHRcdFx0Z2V0dGVyIDogbWV0aG9kRmlyc3RBcmcsXG5cdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDEgXSxcblx0XHRcdH07XG5cdFx0fVxuXG5cdFx0Ly8gRnJlZSBjYWxsOiBsYXp5KC4uLilcblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgWyBmaXJzdEFyZyBdID0gYXJncztcblxuXHRcdC8vIEV4cGxpY2l0LXNvdXJjZSBmb3JtOiBsYXp5KHNvdXJjZSwgJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0Ly8gb3IgbGF6eShzb3VyY2UsIGdldHRlciwgY29uZmlnPylcblx0XHRpZiAoYXJncy5sZW5ndGggPj0gMiAmJiB0cy5pc0lkZW50aWZpZXIoZmlyc3RBcmcpKSB7XG5cdFx0XHRjb25zdCBbICwgc2Vjb25kQXJnIF0gPSBhcmdzO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChzZWNvbmRBcmcpKSB7XG5cdFx0XHRcdC8vIGxhenkoc291cmNlLCAnTmFtZScsIGdldHRlciwgY29uZmlnPylcblx0XHRcdFx0aWYgKGFyZ3MubGVuZ3RoIDwgMykge1xuXHRcdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHRzb3VyY2UgOiBmaXJzdEFyZyxcblx0XHRcdFx0XHRuYW1lICAgOiBzZWNvbmRBcmcudGV4dCxcblx0XHRcdFx0XHRnZXR0ZXIgOiBhcmdzWyAyIF0sXG5cdFx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMyBdLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXHRcdFx0Ly8gbGF6eShzb3VyY2UsIGdldHRlciwgY29uZmlnPylcblx0XHRcdHJldHVybiB7XG5cdFx0XHRcdHNvdXJjZSA6IGZpcnN0QXJnLFxuXHRcdFx0XHRnZXR0ZXIgOiBzZWNvbmRBcmcsXG5cdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDIgXSxcblx0XHRcdH07XG5cdFx0fVxuXG5cdFx0Ly8gTmFtZWQgcm9vdCBmb3JtOiBsYXp5KCdOYW1lJywgZ2V0dGVyLCBjb25maWc/KVxuXHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoZmlyc3RBcmcpKSB7XG5cdFx0XHRpZiAoYXJncy5sZW5ndGggPCAyKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRuYW1lICAgOiBmaXJzdEFyZy50ZXh0LFxuXHRcdFx0XHRnZXR0ZXIgOiBhcmdzWyAxIF0sXG5cdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDIgXSxcblx0XHRcdH07XG5cdFx0fVxuXG5cdFx0Ly8gVW5uYW1lZCByb290IGZvcm06IGxhenkoZ2V0dGVyLCBjb25maWc/KVxuXHRcdHJldHVybiB7XG5cdFx0XHRnZXR0ZXIgOiBmaXJzdEFyZyxcblx0XHRcdGNvbmZpZyA6IGFyZ3NbIDEgXSxcblx0XHR9O1xuXHR9XG5cblx0LyoqXG5cdCAqIFVud3JhcCB0aGUgY29uc3RydWN0b3IgcmV0dXJuZWQgYnkgYSBsYXp5IGdldHRlci5cblx0ICogU3VwcG9ydHM6XG5cdCAqICAgKCkgPT4gY2xhc3MgTmFtZSB7fVxuXHQgKiAgICgpID0+IGZ1bmN0aW9uIE5hbWUoKSB7fVxuXHQgKiAgICgpID0+IHsgcmV0dXJuIGNsYXNzIE5hbWUge307IH1cblx0ICogICBmdW5jdGlvbiAoKSB7IHJldHVybiBmdW5jdGlvbiBOYW1lKCkge307IH1cblx0ICovXG5cdHByaXZhdGUgdW53cmFwTGF6eUdldHRlciAoZ2V0dGVyRXhwcjogdHMuRXhwcmVzc2lvbik6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc0Fycm93RnVuY3Rpb24oZ2V0dGVyRXhwcikpIHtcblx0XHRcdGNvbnN0IHsgYm9keSB9ID0gZ2V0dGVyRXhwcjtcblx0XHRcdGlmICghdHMuaXNCbG9jayhib2R5KSkge1xuXHRcdFx0XHRyZXR1cm4gYm9keTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3Qgc3RtdCBvZiBib2R5LnN0YXRlbWVudHMpIHtcblx0XHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KHN0bXQpICYmIHN0bXQuZXhwcmVzc2lvbikge1xuXHRcdFx0XHRcdHJldHVybiBzdG10LmV4cHJlc3Npb247XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGdldHRlckV4cHIpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGdldHRlckV4cHI7XG5cdFx0XHRmb3IgKGNvbnN0IHN0bXQgb2YgYm9keS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChzdG10KSAmJiBzdG10LmV4cHJlc3Npb24pIHtcblx0XHRcdFx0XHRyZXR1cm4gc3RtdC5leHByZXNzaW9uO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIE5vdCBhIHJlY29nbml6ZWQgZ2V0dGVyIHBhdHRlcm5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgYSBjb25zdHJ1Y3RvciBuYW1lIGZyb20gYSBjbGFzcyBleHByZXNzaW9uLCBjbGFzcyBkZWNsYXJhdGlvbixcblx0ICogb3IgbmFtZWQgZnVuY3Rpb24gZXhwcmVzc2lvbi5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENvbnN0cnVjdG9yTmFtZSAoY29uc3RydWN0b3JFeHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSAmJiBjb25zdHJ1Y3RvckV4cHIubmFtZSkge1xuXHRcdFx0cmV0dXJuIGNvbnN0cnVjdG9yRXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0NsYXNzRGVjbGFyYXRpb24oY29uc3RydWN0b3JFeHByKSAmJiBjb25zdHJ1Y3RvckV4cHIubmFtZSkge1xuXHRcdFx0cmV0dXJuIGNvbnN0cnVjdG9yRXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpICYmIGNvbnN0cnVjdG9yRXhwci5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gY29uc3RydWN0b3JFeHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSB0eXBlIG5hbWUgZnJvbSBlaXRoZXIgYSBkZWZpbmUoKSBvciBsYXp5KCkgY2FsbC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRoaXMuaXNEZWZpbmVDYWxsKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5leHRyYWN0VHlwZU5hbWUoY2FsbCk7XG5cdFx0fVxuXHRcdGlmICh0aGlzLmlzTGF6eUNhbGwoY2FsbCkpIHtcblx0XHRcdGNvbnN0IGFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0XHRpZiAoIWFyZ3MpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGlmIChhcmdzLm5hbWUpIHtcblx0XHRcdFx0cmV0dXJuIGFyZ3MubmFtZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMudW53cmFwTGF6eUdldHRlcihhcmdzLmdldHRlcik7XG5cdFx0XHRpZiAoY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRcdHJldHVybiB0aGlzLmV4dHJhY3RDb25zdHJ1Y3Rvck5hbWUoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSBmdWxsIGxhenkoKSBjYWxsIGNvbnRleHQ6IHR5cGUgbmFtZSwgcGFyZW50IHR5cGUsIGFuZCBjb2xsZWN0aW9uLlxuXHQgKiBIYW5kbGVzIGRpcmVjdCBjYWxscywgcHJvcGVydHktYWNjZXNzIGNhbGxzLCBjaGFpbmVkIGNhbGxzLCBhbmQgdGhlXG5cdCAqIGV4cGxpY2l0LXNvdXJjZSBmb3JtIGBsYXp5KHNvdXJjZSwgJ1R5cGVOYW1lJywgZ2V0dGVyKWAuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q29udGV4dCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB7XG5cdFx0dHlwZU5hbWU/OiBzdHJpbmc7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Y29uc3QgYXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRpZiAoIWFyZ3MpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRsZXQgdHlwZU5hbWU6IHN0cmluZyB8IHVuZGVmaW5lZCA9IGFyZ3MubmFtZTtcblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLnVud3JhcExhenlHZXR0ZXIoYXJncy5nZXR0ZXIpO1xuXHRcdFx0aWYgKGNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0XHR0eXBlTmFtZSA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yTmFtZShjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBjYWxsO1xuXG5cdFx0Ly8gRGlyZWN0IGNhbGw6IGxhenkoJ1R5cGVOYW1lJywgLi4uKSBvciBsYXp5KHNvdXJjZSwgJ1R5cGVOYW1lJywgZ2V0dGVyKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnbGF6eScpIHtcblx0XHRcdGlmIChhcmdzLnNvdXJjZSAmJiB0cy5pc0lkZW50aWZpZXIoYXJncy5zb3VyY2UpKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2UoYXJncy5zb3VyY2UudGV4dCk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXHRcdFx0Ly8gUGxhaW4gcm9vdCBsYXp5IGluIGRlZmF1bHQgY29sbGVjdGlvblxuXHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUgfTtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSBhY2Nlc3M6IFgubGF6eSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnbGF6eScpIHtcblx0XHRcdGNvbnN0IG9iaiA9IGV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblxuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihvYmopKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uob2JqLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0XHRcdHBhcmVudFR5cGUgICA6IHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSxcblx0XHRcdFx0XHRjb2xsZWN0aW9uSWQgOiBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCxcblx0XHRcdFx0fTtcblx0XHRcdH1cblxuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gTmVzdGVkIGFjY2VzczogaW5zdGFuY2UuVHlwZS5sYXp5IC0gdHJ5IHRvIHJlc29sdmVcblx0XHRcdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4ob2JqKTtcblx0XHRcdFx0aWYgKGNoYWluLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShjaGFpbi5qb2luKCcuJykpO1xuXHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSB9O1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gRGV0ZXJtaW5lIHRoZSBjb2xsZWN0aW9uIGNvbnRleHQgZnJvbSB0aGUgcm9vdCBvZiB0aGUgY2hhaW4gc28gdGhhdFxuXHRcdFx0XHQvLyBjdXN0b20tY29sbGVjdGlvbiB0eXBlcyBkbyBub3QgZ2V0IGNvbmZ1c2VkIHdpdGggZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzLlxuXHRcdFx0XHRjb25zdCByb290SWQgPSB0aGlzLmdldFJvb3RJZGVudGlmaWVyKG9iai5leHByZXNzaW9uKTtcblx0XHRcdFx0Y29uc3QgZXhwZWN0ZWRDb2xsZWN0aW9uSWQgPSByb290SWRcblx0XHRcdFx0XHQ/IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShyb290SWQudGV4dCkuY29sbGVjdGlvbklkXG5cdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHRcdFx0Ly8gQ2hhaW5lZCBjYWxsOiBkZWZpbmUoJ0EnKS5sYXp5KCdCJykgb3IgbGF6eSgnQScpLmxhenkoJ0InKVxuXHRcdFx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwob2JqKSkge1xuXHRcdFx0XHRcdHRoaXMucHJvY2Vzc0RlZmluZUNhbGwob2JqLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRpZiAodGhpcy5pc0xhenlDYWxsKG9iaikpIHtcblx0XHRcdFx0XHR0aGlzLnByb2Nlc3NMYXp5Q2FsbChvYmosIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudFR5cGVOYW1lID0gdGhpcy5leHRyYWN0TW5lbW9uaWNhVHlwZU5hbWUob2JqKTtcblx0XHRcdFx0XHRpZiAocGFyZW50VHlwZU5hbWUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKHBhcmVudFR5cGVOYW1lLCBleHBlY3RlZENvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIEJ1aWxkZXIgbG9va3VwIGNoYWluOiBBcHAubG9va3VwKCdVc2VyJykubGF6eSgnQWRtaW4nKVxuXHRcdFx0XHRpZiAodGhpcy5pc0xvb2t1cENhbGwob2JqKSkge1xuXHRcdFx0XHRcdGNvbnN0IGxvb2tlZFVwUGF0aCA9IHRoaXMucmVzb2x2ZUxvb2t1cFBhdGgob2JqKTtcblx0XHRcdFx0XHRpZiAobG9va2VkVXBQYXRoKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShsb29rZWRVcFBhdGgpO1xuXHRcdFx0XHRcdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlLmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBjb25maWcgb3B0aW9ucyBmcm9tIGxhenkoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q29uZmlnIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSB7XG5cdFx0Y29uc3QgYXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRpZiAoIWFyZ3MgfHwgIWFyZ3MuY29uZmlnIHx8ICF0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGFyZ3MuY29uZmlnKSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IGNvbmZpZ1Jlc3VsdCA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGFyZ3MuY29uZmlnKTtcblx0XHRyZXR1cm4gY29uZmlnUmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0KiBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50cyB0aGF0IGNhcHR1cmUgZGVmaW5lKCkgcmVzdWx0c1xuXHRcdCogZS5nLiwgY29uc3QgVXNlciA9IGRlZmluZSgnVXNlckVudGl0eScsIC4uLikgbWFwcyBcIlVzZXJcIiAtPiBcIlVzZXJFbnRpdHlcIlxuXHRcdCogRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBjb25zdCBYID0gZGVmaW5lKCdBJykuZGVmaW5lKCdCJyksIHdlIG1hcCBYIC0+IEEgKHRoZSByb290IHR5cGUpXG5cdFx0Ki9cblx0cHJpdmF0ZSB0cmFja1ZhcmlhYmxlQXNzaWdubWVudCAoXG5cdFx0Y2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0cGFyZW50Tm9kZTogVHlwZU5vZGUgfCB1bmRlZmluZWQsXG5cdFx0ZnVsbFBhdGg6IHN0cmluZ1xuXHQpOiB2b2lkIHtcblx0XHQvLyBDaGVjayBpZiB0aGlzIGNhbGwgaXMgdGhlIHJpZ2h0LWhhbmQgc2lkZSBvZiBhIHZhcmlhYmxlIGRlY2xhcmF0aW9uXG5cdFx0Ly8gV2FsayB1cCB0aGUgdHJlZSB0byBmaW5kIFZhcmlhYmxlRGVjbGFyYXRpb25cblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IGNhbGwucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRcdC8vIEZvdW5kOiBjb25zdCBYID0gZGVmaW5lKC4uLilcblx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50Lm5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgdmFyTmFtZSA9IGN1cnJlbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRcdC8vIEYxODogZGVmaW5lKCkgcmV0dXJucyB0aGUgREVGSU5FRCB0eXBlJ3MgY29uc3RydWN0b3IsXG5cdFx0XHRcdFx0Ly8gc28gYSBjb25zdCBob2xkaW5nIGEgbXVsdGktaG9wIGluaXRpYWxpemVyXG5cdFx0XHRcdFx0Ly8gKGBjb25zdCBYID0gQS5kZWZpbmUoJ0InKS5kZWZpbmUoJ0MnKWApIGJpbmRzIHRoZSBMQVNUXG5cdFx0XHRcdFx0Ly8gaG9wIOKAlCBhIGRlZXBlciBob3AgbXVzdCBub3QgYmluZCwgYW5kIHRoZSBvdXRlcm1vc3Rcblx0XHRcdFx0XHQvLyBob3AgYmluZHMgdW5jb25kaXRpb25hbGx5ICh2aXNpdC1vcmRlciBpbmRlcGVuZGVudClcblx0XHRcdFx0XHRpZiAodGhpcy5pc0RlZXBlckRlZmluZUhvcChjYWxsKSkge1xuXHRcdFx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHQvLyBGb3IgY2hhaW5lZCBsYXp5IGNhbGxzIGxpa2UgY29uc3QgWCA9IGRlZmluZSgnQScpLmxhenkoJ0InKSxcblx0XHRcdFx0XHQvLyB0aGUgZmlyc3QgY2FsbCBpbiB0aGUgY2hhaW4gc2V0cyB0aGUgbWFwcGluZyAobGF6eSBob3Bcblx0XHRcdFx0XHQvLyBrZWVwcyBpdCDigJQgcGlubmVkIGJlaGF2aW9yKVxuXHRcdFx0XHRcdGlmIChwYXJlbnROb2RlICYmIHRoaXMudmFyaWFibGVUb1R5cGVNYXAuaGFzKHZhck5hbWUpKSB7XG5cdFx0XHRcdFx0XHRyZXR1cm47XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdHRoaXMudmFyaWFibGVUb1R5cGVNYXAuc2V0KHZhck5hbWUsIGZ1bGxQYXRoKTtcblx0XHRcdFx0XHR0aGlzLnRyYWNrRmlsZUdyYXBoQmluZGluZyh2YXJOYW1lLCBmdWxsUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBBIGAuZGVmaW5lKC4uLilgIGhvcCB3cmFwcGVkIGJ5IGFub3RoZXIgYC5kZWZpbmUoLi4uKWAgY2FsbCBpcyBub3Rcblx0ICogdGhlIHZhbHVlIGl0cyBjb25zdCBlbmRzIHVwIGhvbGRpbmcg4oCUIHRoZSBPVVRFUk1PU1QgaG9wIG9mIHRoZVxuXHQgKiBpbml0aWFsaXplciBjaGFpbiBpcyAoZGVmaW5lKCkgcmV0dXJucyB0aGUgZGVmaW5lZCB0eXBlJ3Ncblx0ICogY29uc3RydWN0b3IpLiBPbmx5IHRoZSBvdXRlcm1vc3QgaG9wIG1heSBiaW5kIHRoZSB2YXJpYWJsZS5cblx0ICovXG5cdHByaXZhdGUgaXNEZWVwZXJEZWZpbmVIb3AgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgeyBwYXJlbnQgfSA9IGNhbGw7XG5cdFx0Y29uc3QgZGVlcGVyID0gISFwYXJlbnQgJiZcblx0XHRcdHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKHBhcmVudCkgJiZcblx0XHRcdHBhcmVudC5uYW1lLnRleHQgPT09ICdkZWZpbmUnICYmXG5cdFx0XHR0cy5pc0NhbGxFeHByZXNzaW9uKHBhcmVudC5wYXJlbnQpICYmXG5cdFx0XHRwYXJlbnQucGFyZW50LmV4cHJlc3Npb24gPT09IHBhcmVudDtcblx0XHRyZXR1cm4gZGVlcGVyO1xuXHR9XG5cblx0LyoqXG5cdCAqIE1pcnJvciBhIHZhcmlhYmxlIC0+IG1uZW1vbmljYSBmdWxsUGF0aCBiaW5kaW5nIGludG8gdGhlIHBlci1maWxlXG5cdCAqIHZhbHVlLXNjb3BlIG1hcCAoZ3JhcGggaWRlbnRpdHkgbGF3OiBgdHlwZW9mIFhgIGFuZCBiYXJlIHJlZmVyZW5jZXNcblx0ICogcmVzb2x2ZSB0aHJvdWdoIHRoZSBmaWxlJ3Mgb3duIGJpbmRpbmdzIGZpcnN0KS5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tGaWxlR3JhcGhCaW5kaW5nICh2YXJOYW1lOiBzdHJpbmcsIGZ1bGxQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRsZXQgYmluZGluZ3MgPSB0aGlzLmZpbGVHcmFwaEJpbmRpbmdzLmdldChmaWxlUGF0aCk7XG5cdFx0aWYgKCFiaW5kaW5ncykge1xuXHRcdFx0YmluZGluZ3MgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0dGhpcy5maWxlR3JhcGhCaW5kaW5ncy5zZXQoZmlsZVBhdGgsIGJpbmRpbmdzKTtcblx0XHR9XG5cdFx0YmluZGluZ3Muc2V0KHZhck5hbWUsIGZ1bGxQYXRoKTtcblx0fVxuXHRcblx0LyoqXG5cdFx0KiBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50cyBmcm9tIGxvb2t1cCgpIGNhbGxzXG5cdFx0KiBlLmcuLCBjb25zdCBTZW50aWVuY2VDb25zdHJ1Y3RvciA9IGxvb2t1cCgnU2VudGllbmNlJykgbWFwcyBcIlNlbnRpZW5jZUNvbnN0cnVjdG9yXCIgLT4gXCJTZW50aWVuY2VcIlxuXHRcdCovXG5cdHByaXZhdGUgdHJhY2tMb29rdXBBc3NpZ25tZW50IChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgdHlwZVBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdHRoaXMuYmluZFJlc3VsdFZhcmlhYmxlKGNhbGwsIHR5cGVQYXRoKTtcblx0fVxuXG5cdC8qKlxuXHRcdCogVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHMgZnJvbSBuZXcgVHlwZSgpIGNhbGxzXG5cdFx0KiBlLmcuLCBjb25zdCB1c2VyID0gbmV3IFVzZXJUeXBlKCkgbWFwcyBcInVzZXJcIiAtPiBcIlVzZXJUeXBlXCJcblx0XHQqL1xuXHRwcml2YXRlIHRyYWNrTmV3QXNzaWdubWVudCAobmV3RXhwcjogdHMuTmV3RXhwcmVzc2lvbiwgdHlwZVBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdGxldCBlZmZlY3RpdmVQYXRoID0gdHlwZVBhdGg7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBuZXdFeHByLnBhcmVudDtcblx0XHQvLyBDaGFpbi1mb3JtIGNvbnN0cnVjdGlvbjogbmV3IFIoKS5BKCkuQigpIOKAlCB0aGUgcmVzdWx0IHZhcmlhYmxlXG5cdFx0Ly8gaG9sZHMgdGhlIE9VVEVSTU9TVCB0aXAncyBpbnN0YW5jZSAoYXdhaXQtdHJhbnNwYXJlbnQpLCBub3QgdGhlXG5cdFx0Ly8gaW5uZXIgbmV3J3MgdHlwZS4gV2FsayB0aGUgY2hhaW4sIGtlZXBpbmcgdGhlIGxhc3QgcmVzb2x2YWJsZSB0aXAuXG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdXJyZW50KSAmJlxuXHRcdFx0XHR0cy5pc0NhbGxFeHByZXNzaW9uKGN1cnJlbnQucGFyZW50KSAmJlxuXHRcdFx0XHRjdXJyZW50LnBhcmVudC5leHByZXNzaW9uID09PSBjdXJyZW50KSB7XG5cdFx0XHRcdGNvbnN0IHRpcCA9IHRoaXMucmVzb2x2ZUNoYWluVGlwVHlwZVBhdGgoY3VycmVudC5wYXJlbnQpO1xuXHRcdFx0XHRpZiAodGlwKSB7XG5cdFx0XHRcdFx0ZWZmZWN0aXZlUGF0aCA9IHRpcDtcblx0XHRcdFx0fVxuXHRcdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQucGFyZW50O1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGJyZWFrO1xuXHRcdH1cblx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShuZXdFeHByLCBlZmZlY3RpdmVQYXRoKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBCaW5kIHRoZSBuZWFyZXN0IGVuY2xvc2luZyBgY29uc3QvbGV0L3ZhciBYID0g4oCmYCB0byBhIG1uZW1vbmljYVxuXHQgKiBmdWxsUGF0aCDigJQgdGhlIHNoYXJlZCByZXN1bHQtdmFyaWFibGUgd2Fsa2VyIGJlaGluZCBuZXcvbG9va3VwL1xuXHQgKiBjaGFpbi9mb3JrL21lcmdlL2NhbGwgdHJhY2tpbmcgKHZhbHVlIHNjb3BlOiBkb3duc3RyZWFtIHJlZmVyZW5jZXNcblx0ICogYW5kIGB0aGlzLnggPSB4YCBhc3NpZ25tZW50cyByZXNvbHZlIHRocm91Z2ggdGhlIHNhbWUgYmluZGluZykuXG5cdCAqL1xuXHRwcml2YXRlIGJpbmRSZXN1bHRWYXJpYWJsZSAoZnJvbTogdHMuTm9kZSwgdHlwZVBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gZnJvbS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24oY3VycmVudCkpIHtcblx0XHRcdFx0Ly8gRm91bmQ6IGNvbnN0IFggPSA8Y29uc3RydWN0aW9uPlxuXHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCB2YXJOYW1lID0gY3VycmVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0dGhpcy52YXJpYWJsZVRvVHlwZU1hcC5zZXQodmFyTmFtZSwgdHlwZVBhdGgpO1xuXHRcdFx0XHRcdHRoaXMudHJhY2tGaWxlR3JhcGhCaW5kaW5nKHZhck5hbWUsIHR5cGVQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm47XG5cdFx0XHR9XG5cdFx0XHQvLyBTY29wZSBib3VuZGFyeTogYSBjb25zdHJ1Y3Rpb24gaW5zaWRlIGEgbmVzdGVkIGNsYXNzL2Z1bmN0aW9uXG5cdFx0XHQvLyBib2R5IGRvZXMgbm90IGJpbmQgdGhlIG91dGVyIHZhcmlhYmxlIOKAlFxuXHRcdFx0Ly8gYGNvbnN0IFggPSBkZWZpbmUoJ1gnLCBjbGFzcyB7IG0gPSBuZXcgTWFwKCkgfSlgIGhvbGRzIHRoZVxuXHRcdFx0Ly8gZGVmaW5lZCBjb25zdHJ1Y3Rvciwgbm90IGEgTWFwLiBXaXRob3V0IHRoaXMgc3RvcCB0aGUgY2xhc3MtYm9keVxuXHRcdFx0Ly8gaW5zdGFudGlhdGlvbiBjbG9iYmVycyBYJ3MgYmluZGluZyBhbmQgYSBsYXRlciBYLmRlZmluZSgnQ2hpbGQnKVxuXHRcdFx0Ly8gbG9zZXMgaXRzIHBhcmVudCAodGhlIGNoaWxkIGxhbmRzIGFzIGEgYmFyZSBkZWZhdWx0LWNvbGxlY3Rpb25cblx0XHRcdC8vIHJvb3Qg4oCUIGZhdGFsIGZvciBjdXN0b20gY29sbGVjdGlvbnMsIHdob3NlIGZ1bGxQYXRocyB0aGVcblx0XHRcdC8vIG5hbWUtb25seSBmYWxsYmFjayBjYW5ub3Qgc2VlKS5cblx0XHRcdGlmICh0cy5pc0NsYXNzTGlrZShjdXJyZW50KSB8fCB0cy5pc0Z1bmN0aW9uTGlrZShjdXJyZW50KSkge1xuXHRcdFx0XHRyZXR1cm47XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhbiBgaW5zdGFudGlhdGlvbmAgdXNhZ2UgZm9yIGEgY29uc3RydWN0aW9uLXNoYXBlIGNhbGxcblx0ICogKGNoYWluIHRpcCAvIGNhbGwgLyBhcHBseSAvIGZvcmsgLyBjbG9uZSAvIG1lcmdlIOKAlFxuXHQgKiBieXRlLWluZGlzdGluZ3Vpc2hhYmxlIGZyb20gYG5ld2AgdW50aWwgdGhlIGRlZmVycmVkXG5cdCAqIG1lY2hhbmlzbS1raW5kIHJldmlzaW9uKS4gYGNvbnN0cnVjdG9yVGV4dGAgZGVmYXVsdHMgdG8gdGhlIGNhbGxlZVxuXHQgKiBleHByZXNzaW9uIHRleHQgc28gdGhlIHNpdGUgc3RheXMgcmVhZGFibGUgd2l0aG91dCBuZXcgZmllbGRzO1xuXHQgKiBjYWxsL2FwcGx5IG92ZXJyaWRlIGl0IHdpdGggdGhlIEN0b3IgYXJndW1lbnQgdGV4dC5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkQ29uc3RydWN0aW9uVXNhZ2UgKFxuXHRcdGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLFxuXHRcdHR5cGVQYXRoOiBzdHJpbmcsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRjb25zdHJ1Y3RvclRleHQ/OiBzdHJpbmdcblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdGNhbGwuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGN0b3JUZXh0ID0gY29uc3RydWN0b3JUZXh0ID8/IGNhbGwuZXhwcmVzc2lvbi5nZXRUZXh0KHNvdXJjZUZpbGUpO1xuXHRcdHRoaXMuYWRkVXNhZ2UodHlwZVBhdGgsIHtcblx0XHRcdGxvY2F0aW9uICAgICAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0Y29kZSAgICAgICAgICAgIDogY2FsbC5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRjb25zdHJ1Y3RvclRleHQgOiBjdG9yVGV4dC5zbGljZSgwLCAxMDApLFxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgdGhlIHR5cGUgYSBjb25zdHJ1Y3Rpb24tY2hhaW4gdGlwIGNhbGwgY29uc3RydWN0czpcblx0ICogYG5ldyBSKC4uLikuQSguLi4pYCBjb25zdHJ1Y3RzIFIuQTsgYGF3YWl0IG5ldyBSKC4uLikuQSguLi4pLkIoLi4uKWBcblx0ICogY29uc3RydWN0cyBSLkEuQi4gVGhlIHJlY2VpdmVyIGlzIHRoZSBuZXN0ZWQgY2hhaW4gKE5ld0V4cHJlc3Npb25cblx0ICogYmFzZSwgdGhlbiB0aXAgY2FsbHMpOyBleGFjdCBmdWxsUGF0aCBmaXJzdCwgYW5kIG9ubHkgd2hlbiB0aGUgcm9vdFxuXHQgKiBpdHNlbGYgaXMgdW5rbm93biBkb2VzIHRoZSBwcm9wLW5hbWUgZmFsbGJhY2sgbGF3IGFwcGx5IChzbyBwbGFpblxuXHQgKiBtZXRob2QgY2FsbHMgb24gZnJlc2ggaW5zdGFuY2VzIG5ldmVyIHJlY29yZCBhIGNvbnN0cnVjdGlvbikuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVDaGFpblRpcFR5cGVQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZWNlaXZlciA9IGNhbGwuZXhwcmVzc2lvbjtcblx0XHRsZXQgcm9vdFBhdGg6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRpZiAodHMuaXNOZXdFeHByZXNzaW9uKHJlY2VpdmVyLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRjb25zdCBpbm5lciA9IHJlY2VpdmVyLmV4cHJlc3Npb247XG5cdFx0XHRyb290UGF0aCA9IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGlubmVyLmV4cHJlc3Npb24pXG5cdFx0XHRcdD8gdGhpcy5yZXNvbHZlVHlwZVBhdGgoaW5uZXIuZXhwcmVzc2lvbilcblx0XHRcdFx0OiB0aGlzLmdldFR5cGVOYW1lRnJvbUV4cHJlc3Npb24oaW5uZXIuZXhwcmVzc2lvbik7XG5cdFx0fSBlbHNlIGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKHJlY2VpdmVyLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyb290UGF0aCA9IHRoaXMucmVzb2x2ZUNoYWluVGlwVHlwZVBhdGgocmVjZWl2ZXIuZXhwcmVzc2lvbik7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGlmICghcm9vdFBhdGgpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGNhbmRpZGF0ZSA9IGAke3Jvb3RQYXRofS4ke3JlY2VpdmVyLm5hbWUudGV4dH1gO1xuXHRcdGlmICh0aGlzLmRlZmluaXRpb25zLmhhcyhjYW5kaWRhdGUpKSB7XG5cdFx0XHRyZXR1cm4gY2FuZGlkYXRlO1xuXHRcdH1cblx0XHRpZiAoIXRoaXMuZGVmaW5pdGlvbnMuaGFzKHJvb3RQYXRoKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMucmVzb2x2ZVR5cGVQYXRoKHJlY2VpdmVyKTtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBUcnVlIHdoZW4gYGV4cHJgIGRlbm90ZXMgYSBjb25zdHJ1Y3Rpb24gZnVuY3Rpb24gaW1wb3J0ZWQgZnJvbVxuXHQgKiAnbW5lbW9uaWNhJyDigJQgdGhlIG5hbWVkLWltcG9ydCBmb3JtIChgaW1wb3J0IHsgY2FsbCB9IGZyb21cblx0ICogJ21uZW1vbmljYSdgLCBhbGlhc2VzIGluY2x1ZGVkKSBvciBhIG1lbWJlciBvZiBhIHRyYWNrZWRcblx0ICogbW9kdWxlLW9iamVjdCBhbGlhcyAoYG1uZW1vbmljYS5jYWxsYCkuIFVzZXJsYW5kIGNhbGwvYXBwbHkvYmluZFxuXHQgKiBmdW5jdGlvbnMgbmV2ZXIgbWF0Y2guXG5cdCAqL1xuXHRwcml2YXRlIGlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4gKGV4cHI6IHRzLkV4cHJlc3Npb24sIGZuOiAnY2FsbCcgfCAnYXBwbHknIHwgJ2JpbmQnKTogYm9vbGVhbiB7XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLm1uZW1vbmljYU5hbWVkSW1wb3J0cy5nZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKT8uZ2V0KGV4cHIudGV4dCk7XG5cdFx0XHRjb25zdCBtYXRjaGVkID0gaW1wb3J0ZWQgPT09IGZuO1xuXHRcdFx0cmV0dXJuIG1hdGNoZWQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSAmJiBleHByLm5hbWUudGV4dCA9PT0gZm4pIHtcblx0XHRcdGNvbnN0IG1hdGNoZWQgPSB0cy5pc0lkZW50aWZpZXIoZXhwci5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoZXhwci5leHByZXNzaW9uLnRleHQpO1xuXHRcdFx0cmV0dXJuIG1hdGNoZWQ7XG5cdFx0fVxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBtbmVtb25pY2EgY2FsbC9hcHBseShlbnRpdHksIEN0b3IsIC4uLikgLyBiaW5kKGVudGl0eSwgQ3Rvcik6XG5cdCAqIHJlc29sdmUgdGhlIEN0b3IgYXJndW1lbnQgKGFyZyAxKSB0byBhIGdyYXBoIGZ1bGxQYXRoIHRocm91Z2ggdGhlXG5cdCAqIHNhbWUgdGllcnMgYXMgdGhlIGBuZXdgIGJyYW5jaCAodmFsdWUgc2NvcGUgZm9yIGlkZW50aWZpZXJzLFxuXHQgKiBjaGFpbiByZXNvbHV0aW9uIGZvciBwcm9wZXJ0eSBhY2Nlc3NlcykuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVDb25zdHJ1Y3Rpb25GblR5cGVQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2FsbGVlID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGNvbnN0IGlzQ2FsbE9yQXBwbHkgPSB0aGlzLmlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4oY2FsbGVlLCAnY2FsbCcpIHx8XG5cdFx0XHR0aGlzLmlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4oY2FsbGVlLCAnYXBwbHknKTtcblx0XHRjb25zdCBpc0JpbmQgPSB0aGlzLmlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4oY2FsbGVlLCAnYmluZCcpO1xuXHRcdGlmICghaXNDYWxsT3JBcHBseSAmJiAhaXNCaW5kKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRpZiAoY2FsbC5hcmd1bWVudHMubGVuZ3RoIDwgMikge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgWyAsIGN0b3JBcmcgXSA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGxldCByZXNvbHZlZDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdG9yQXJnKSkge1xuXHRcdFx0cmVzb2x2ZWQgPSB0aGlzLnJlc29sdmVUeXBlUGF0aChjdG9yQXJnKTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihjdG9yQXJnKSkge1xuXHRcdFx0Y29uc3QgYm91bmQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChjdG9yQXJnLnRleHQpO1xuXHRcdFx0aWYgKGJvdW5kKSB7XG5cdFx0XHRcdHJlc29sdmVkID0gYm91bmQ7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRjb25zdCBncmFwaFJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUoY3RvckFyZy50ZXh0KTtcblx0XHRcdFx0aWYgKGdyYXBoUmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdFx0XHRyZXNvbHZlZCA9IGdyYXBoUmVzdWx0Lm5vZGUuZnVsbFBhdGg7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc3Qga25vd24gPSByZXNvbHZlZCAmJiB0aGlzLmRlZmluaXRpb25zLmhhcyhyZXNvbHZlZCkgPyByZXNvbHZlZCA6IHVuZGVmaW5lZDtcblx0XHRyZXR1cm4ga25vd247XG5cdH1cblxuXHQvKipcblx0ICogaW5zdGFuY2UuZm9yayguLi4pIC8gaW5zdGFuY2UuY2xvbmUoLi4uKSBvbiBhIHRyYWNrZWQgdmFyaWFibGUg4oCUXG5cdCAqIHJ1bnRpbWUgcmV0dXJucyBgdGhpc2AsIHNvIHRoZSByZXN1bHQgY2FycmllcyB0aGUgc291cmNlIHR5cGUuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVGb3JrTGlrZVR5cGVQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBtZXRob2QgPSBjYWxsLmV4cHJlc3Npb24ubmFtZS50ZXh0O1xuXHRcdGlmIChtZXRob2QgIT09ICdmb3JrJyAmJiBtZXRob2QgIT09ICdjbG9uZScpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlY2VpdmVyID0gY2FsbC5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIocmVjZWl2ZXIpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChyZWNlaXZlci50ZXh0KTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEZyZWUgdXRpbHMgZm9ybXM6IHV0aWxzLm1lcmdlKGEsIGIsIC4uLikgKGFsc28gdGhlIGRpcmVjdCBuYW1lZFxuXHQgKiBpbXBvcnQgYG1lcmdlKGEsIGIpYCkgYW5kIHRoZSBjdXJyaWVkIHV0aWxzLmZvcmsoaW5zdGFuY2UpKC4uLikuXG5cdCAqIFRoZSByZXN1bHQgYmluZHMgdG8gYXJnIDAncyB0eXBlIOKAlCBydW50aW1lIHJldHVybnMgYSdzIGxpbmVhZ2Ugb3ZlclxuXHQgKiBiJ3MgY29udGV4dDsgYSdzIGZ1bGxQYXRoIGlzIHRoZSBob25lc3QgYXBwcm94aW1hdGlvbiB3aXRoaW4gdGhlXG5cdCAqIG91dHB1dCBjb250cmFjdCAoZG9jdW1lbnRlZCBpbiBSRUFETUUpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlVXRpbHNGblR5cGVQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2FsbGVlID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGNvbnN0IGlzVXRpbHNPd25lciA9IChvd25lcjogdHMuRXhwcmVzc2lvbik6IGJvb2xlYW4gPT4ge1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihvd25lcikpIHtcblx0XHRcdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLm1uZW1vbmljYU5hbWVkSW1wb3J0cy5nZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKT8uZ2V0KG93bmVyLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4gaW1wb3J0ZWQgPT09ICd1dGlscyc7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBtYXRjaGVkID0gdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ob3duZXIpICYmIG93bmVyLm5hbWUudGV4dCA9PT0gJ3V0aWxzJyAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIob3duZXIuZXhwcmVzc2lvbikgJiYgdGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuaGFzKG93bmVyLmV4cHJlc3Npb24udGV4dCk7XG5cdFx0XHRyZXR1cm4gbWF0Y2hlZDtcblx0XHR9O1xuXHRcdGxldCBzdWJqZWN0QXJnOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkO1xuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsZWUpICYmIGlzVXRpbHNPd25lcihjYWxsZWUuZXhwcmVzc2lvbikgJiZcblx0XHRcdChjYWxsZWUubmFtZS50ZXh0ID09PSAnbWVyZ2UnIHx8IGNhbGxlZS5uYW1lLnRleHQgPT09ICdmb3JrJykpIHtcblx0XHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdFx0c3ViamVjdEFyZyA9IGZpcnN0QXJnO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNJZGVudGlmaWVyKGNhbGxlZSkpIHtcblx0XHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChjYWxsZWUudGV4dCk7XG5cdFx0XHRpZiAoaW1wb3J0ZWQgPT09ICdtZXJnZScgfHwgaW1wb3J0ZWQgPT09ICdmb3JrJykge1xuXHRcdFx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblx0XHRcdFx0c3ViamVjdEFyZyA9IGZpcnN0QXJnO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSBpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihjYWxsZWUpICYmIHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxlZS5leHByZXNzaW9uKSAmJlxuXHRcdFx0Y2FsbGVlLmV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnZm9yaycgJiYgaXNVdGlsc093bmVyKGNhbGxlZS5leHByZXNzaW9uLmV4cHJlc3Npb24pKSB7XG5cdFx0XHQvLyB1dGlscy5mb3JrKGluc3RhbmNlKSguLi5hcmdzKSDigJQgdGhlIGN1cnJpZWQgZm9ybVxuXHRcdFx0Y29uc3QgWyBmaXJzdEFyZyBdID0gY2FsbGVlLmFyZ3VtZW50cztcblx0XHRcdHN1YmplY3RBcmcgPSBmaXJzdEFyZztcblx0XHR9XG5cdFx0aWYgKCFzdWJqZWN0QXJnIHx8ICF0cy5pc0lkZW50aWZpZXIoc3ViamVjdEFyZykpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KHN1YmplY3RBcmcudGV4dCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cblx0LyoqXG5cdFx0KiBQcm9jZXNzIGEgQGRlY29yYXRlKCkgZGVjb3JhdG9yXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NEZWNvcmF0ZURlY29yYXRvciAoXG5cdFx0ZGVjb3JhdG9yOiB0cy5EZWNvcmF0b3IsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRjbGFzc0RlY2xQYXJhbT86IHRzLkNsYXNzRGVjbGFyYXRpb25cblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdGRlY29yYXRvci5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cblx0XHQvLyBHZXQgdGhlIGNsYXNzIGRlY2xhcmF0aW9uIC0gdXNlIHRoZSBwYXNzZWQgY29udGV4dCBpZiBwYXJlbnQgaXMgbm90IHNldFxuXHRcdGNvbnN0IGNsYXNzRGVjbCA9IGRlY29yYXRvci5wYXJlbnQgYXMgdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCB8fCBjbGFzc0RlY2xQYXJhbTtcblx0XHRpZiAoIWNsYXNzRGVjbCB8fCAhY2xhc3NEZWNsLm5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0RlY29yYXRlZCBjbGFzcyBoYXMgbm8gbmFtZScsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgdHlwZU5hbWUgPSBjbGFzc0RlY2wubmFtZS50ZXh0O1xuXHRcdGlmICghdHlwZU5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0RlY29yYXRlZCBjbGFzcyBoYXMgbm8gbmFtZScsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUGFyc2UgZGVjb3JhdG9yIGFyZ3VtZW50czogQGRlY29yYXRlKCksIEBkZWNvcmF0ZShQYXJlbnQpLFxuXHRcdC8vIEBkZWNvcmF0ZSh7IC4uLiB9KSwgQGRlY29yYXRlKFBhcmVudCwgeyAuLi4gfSksXG5cdFx0Ly8gQE15Q29sbGVjdGlvbi5kZWNvcmF0ZSgpLCBATXlDb2xsZWN0aW9uLmRlY29yYXRlKHsgLi4uIH0pXG5cdFx0bGV0IHBhcmVudE5vZGU6IFR5cGVOb2RlIHwgdW5kZWZpbmVkO1xuXHRcdGxldCBwYXJlbnRGdWxsUGF0aDogc3RyaW5nIHwgbnVsbCA9IG51bGw7XG5cdFx0bGV0IGNvbGxlY3Rpb25JZDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdGxldCBkZWNvcmF0b3JDb25maWc6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSA9IHt9O1xuXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZGVjb3JhdG9yLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRjb25zdCBjYWxsRXhwciA9IGRlY29yYXRvci5leHByZXNzaW9uO1xuXHRcdFx0Y29uc3QgY2FsbGVlID0gY2FsbEV4cHIuZXhwcmVzc2lvbjtcblxuXHRcdFx0Ly8gQ2hlY2sgZm9yIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSB3aGVyZSBNeUNvbGxlY3Rpb24gaXMgYSBjdXN0b20gY29sbGVjdGlvbi5cblx0XHRcdC8vIFRoZSBkZWNvcmF0ZWQgY2xhc3MgYmVjb21lcyBhIHJvb3QgdHlwZSBpbiB0aGF0IGNvbGxlY3Rpb24uXG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxlZSkgJiZcblx0XHRcdFx0Y2FsbGVlLm5hbWUudGV4dCA9PT0gJ2RlY29yYXRlJyAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoY2FsbGVlLmV4cHJlc3Npb24pICYmXG5cdFx0XHRcdHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5oYXMoY2FsbGVlLmV4cHJlc3Npb24udGV4dClcblx0XHRcdCkge1xuXHRcdFx0XHRjb2xsZWN0aW9uSWQgPSB0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuZ2V0KGNhbGxlZS5leHByZXNzaW9uLnRleHQpO1xuXHRcdFx0XHRpZiAoY2FsbEV4cHIuYXJndW1lbnRzLmxlbmd0aCA9PT0gMSAmJiB0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGNhbGxFeHByLmFyZ3VtZW50c1sgMCBdKSkge1xuXHRcdFx0XHRcdGRlY29yYXRvckNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGNhbGxFeHByLmFyZ3VtZW50c1sgMCBdKTtcblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgYXJncyA9IGNhbGxFeHByLmFyZ3VtZW50cztcblx0XHRcdFx0bGV0IHBhcmVudEFyZzogdHMuSWRlbnRpZmllciB8IHVuZGVmaW5lZDtcblx0XHRcdFx0bGV0IGNvbmZpZ0FyZzogdHMuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24gfCB1bmRlZmluZWQ7XG5cblx0XHRcdFx0Zm9yIChjb25zdCBhcmcgb2YgYXJncykge1xuXHRcdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0XHRcdFx0aWYgKHBhcmVudEFyZykge1xuXHRcdFx0XHRcdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0XHRcdFx0XHRtZXNzYWdlIDogJ0BkZWNvcmF0ZSgpIGFjY2VwdHMgb25seSBvbmUgcGFyZW50IHJlZmVyZW5jZScsXG5cdFx0XHRcdFx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRcdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHRcdHBhcmVudEFyZyA9IGFyZztcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0XHRcdFx0aWYgKGNvbmZpZ0FyZykge1xuXHRcdFx0XHRcdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0XHRcdFx0XHRtZXNzYWdlIDogJ0BkZWNvcmF0ZSgpIGFjY2VwdHMgb25seSBvbmUgY29uZmlnIG9iamVjdCcsXG5cdFx0XHRcdFx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRcdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHRcdGNvbmZpZ0FyZyA9IGFyZztcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRpZiAocGFyZW50QXJnKSB7XG5cdFx0XHRcdFx0cGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeUlkZW50aWZpZXIocGFyZW50QXJnLnRleHQpO1xuXHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHRwYXJlbnRGdWxsUGF0aCA9IHBhcmVudE5vZGUuZnVsbFBhdGg7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0aWYgKGNvbmZpZ0FyZykge1xuXHRcdFx0XHRcdGRlY29yYXRvckNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGNvbmZpZ0FyZyk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBCdWlsZCBmdWxsIHBhdGgg4oCUIGEgcm9vdCBkZWNvcmF0ZWQgaW50byBhIGN1c3RvbSBjb2xsZWN0aW9uXG5cdFx0Ly8gY2FycmllcyB0aGUgY29sbGVjdGlvbklkOjogcHJlZml4LCBleGFjdGx5IGxpa2UgdGhlIGdyYXBoIG5vZGUnc1xuXHRcdC8vIGZ1bGxQYXRoOiBkZWZpbml0aW9ucy5qc29uIGtleXMgbXVzdCBqb2luIGhpZXJhcmNoeS5qc29uICh0aGVcblx0XHQvLyBwcmVmaXggd2FzIGRyb3BwZWQgaGVyZSBiZWZvcmUsIHNvIGEgZGVjb3JhdGVkIGNvbGxlY3Rpb24gcm9vdFxuXHRcdC8vIG5ldmVyIGpvaW5lZClcblx0XHRjb25zdCBmdWxsUGF0aCA9IHBhcmVudE5vZGVcblx0XHRcdD8gYCR7cGFyZW50Tm9kZS5mdWxsUGF0aH0uJHt0eXBlTmFtZX1gXG5cdFx0XHQ6IGNvbGxlY3Rpb25JZFxuXHRcdFx0XHQ/IGAke2NvbGxlY3Rpb25JZH06OiR7dHlwZU5hbWV9YFxuXHRcdFx0XHQ6IHR5cGVOYW1lO1xuXG5cdFx0Ly8gQ3JlYXRlIGRlZmluaXRpb24gaW5mbyBmb3IgZGVjb3JhdGVcblx0XHRjb25zdCBkZWZpbml0aW9uOiBEZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVjb3JhdGUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiBwYXJlbnRGdWxsUGF0aCxcblx0XHRcdHN0cmljdENoYWluIDogZGVjb3JhdG9yQ29uZmlnLnN0cmljdENoYWluID8/IHRydWUsXG5cdFx0XHRibG9ja0Vycm9ycyA6IGRlY29yYXRvckNvbmZpZy5ibG9ja0Vycm9ycyA/PyBmYWxzZSxcblx0XHR9O1xuXHRcdHRoaXMuZGVmaW5pdGlvbnMuc2V0KGZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0XHR0aGlzLmVkc1Njb3BlQnlOb2RlLnNldChjbGFzc0RlY2wsIGZ1bGxQYXRoKTtcblxuXHRcdC8vIENyZWF0ZSB0eXBlIG5vZGVcblx0XHRjb25zdCBub2RlID0gVHlwZUdyYXBoSW1wbC5jcmVhdGVOb2RlKFxuXHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRwYXJlbnROb2RlLFxuXHRcdFx0c291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdGxpbmUgKyAxLFxuXHRcdFx0Y2hhcmFjdGVyICsgMSxcblx0XHRcdGNvbGxlY3Rpb25JZFxuXHRcdCk7XG5cdFx0dGhpcy5hcHBseUNvbGxlY3Rpb25FbWlzc2lvbkluZm8obm9kZSwgbm9kZS5jb2xsZWN0aW9uSWQpO1xuXG5cdFx0Ly8gU2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlIGRldGVjdGlvbiAoaGFyZC1mYWlsIGxhdylcblx0XHR0aGlzLnJlY29yZERlZmluZVNpdGUoXG5cdFx0XHRwYXJlbnROb2RlID8gYCR7cGFyZW50Tm9kZS5mdWxsUGF0aH0uJHt0eXBlTmFtZX1gIDogYCR7Y29sbGVjdGlvbklkID8/ICdkZWZhdWx0J306OiR7dHlwZU5hbWV9YCxcblx0XHRcdGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gXG5cdFx0KTtcblxuXHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBhbmQgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGNsYXNzIG1lbWJlcnMg4oCUXG5cdFx0Ly8gdGhlIG5ldyBub2RlIGFuY2hvcnMgcmVsYXRpdmUtZmlyc3QgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb25cblx0XHRjb25zdCBwcmV2aW91c0FuY2hvciA9IHRoaXMuY3VycmVudEdyYXBoQW5jaG9yO1xuXHRcdHRoaXMuY3VycmVudEdyYXBoQW5jaG9yID0gbm9kZTtcblx0XHR0cnkge1xuXHRcdFx0bm9kZS5wcm9wZXJ0aWVzID0gdGhpcy5leHRyYWN0Q2xhc3NQcm9wZXJ0aWVzKGNsYXNzRGVjbCk7XG5cdFx0XHRub2RlLmNvbnN0cnVjdG9yUGFyYW1zID0gdGhpcy5leHRyYWN0Q2xhc3NDb25zdHJ1Y3RvclBhcmFtcyhjbGFzc0RlY2wpO1xuXHRcdH0gZmluYWxseSB7XG5cdFx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IHByZXZpb3VzQW5jaG9yO1xuXHRcdH1cblxuXHRcdC8vIEFkZCB0byBncmFwaFxuXHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZENoaWxkKHBhcmVudE5vZGUsIG5vZGUpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZFJvb3Qobm9kZSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdHlwZSBuYW1lIGZyb20gZGVmaW5lKCkgY2FsbCBhcmd1bWVudHMuXG5cdCAqIEhhbmRsZXM6XG5cdCAqICAgZGVmaW5lKCdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdCAqICAgZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcikgICAvLyBleHBsaWNpdC1zb3VyY2UgZm9ybVxuXHQgKiAgIGRlZmluZShmdW5jdGlvbiBUeXBlTmFtZSgpIHt9KVxuXHQgKiAgIGRlZmluZSgoKSA9PiBjbGFzcyBUeXBlTmFtZSB7fSlcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFR5cGVOYW1lIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGFyZ3M7XG5cblx0XHQvLyBFeHBsaWNpdC1zb3VyY2UgZm9ybTogZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilcblx0XHRpZiAoYXJncy5sZW5ndGggPj0gMiAmJiB0cy5pc0lkZW50aWZpZXIoZmlyc3RBcmcpICYmIHRzLmlzU3RyaW5nTGl0ZXJhbChhcmdzWyAxIF0pKSB7XG5cdFx0XHRyZXR1cm4gYXJnc1sgMSBdLnRleHQ7XG5cdFx0fVxuXG5cdFx0Ly8gU3RyaW5nIGxpdGVyYWw6IGRlZmluZSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChmaXJzdEFyZykpIHtcblx0XHRcdHJldHVybiBmaXJzdEFyZy50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIEZ1bmN0aW9uIHdpdGggbmFtZTogZGVmaW5lKGZ1bmN0aW9uIFR5cGVOYW1lKCkge30pXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGZpcnN0QXJnKSAmJiBmaXJzdEFyZy5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gZmlyc3RBcmcubmFtZS50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIEFycm93IGZ1bmN0aW9uIHJldHVybmluZyBjbGFzczogZGVmaW5lKCgpID0+IGNsYXNzIFR5cGVOYW1lIHt9KVxuXHRcdGlmICh0cy5pc0Fycm93RnVuY3Rpb24oZmlyc3RBcmcpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGZpcnN0QXJnO1xuXHRcdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGJvZHkpICYmIGJvZHkubmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gYm9keS5uYW1lLnRleHQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSBmdWxsIGRlZmluZSgpIGNhbGwgY29udGV4dDogdHlwZSBuYW1lLCBwYXJlbnQgdHlwZSwgYW5kIGNvbGxlY3Rpb24uXG5cdCAqIEhhbmRsZXMgZGlyZWN0IGNhbGxzLCBwcm9wZXJ0eS1hY2Nlc3MgY2FsbHMsIGNoYWluZWQgY2FsbHMsIGFuZCB0aGVcblx0ICogZXhwbGljaXQtc291cmNlIGZvcm0gYGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpYC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdERlZmluZUNvbnRleHQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKToge1xuXHRcdHR5cGVOYW1lPzogc3RyaW5nO1xuXHRcdHBhcmVudFR5cGU/OiBUeXBlTm9kZTtcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmc7XG5cdH0ge1xuXHRcdGNvbnN0IHR5cGVOYW1lID0gdGhpcy5leHRyYWN0VHlwZU5hbWUoY2FsbCk7XG5cdFx0aWYgKCF0eXBlTmFtZSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gY2FsbDtcblxuXHRcdC8vIERpcmVjdCBjYWxsOiBkZWZpbmUoJ1R5cGVOYW1lJywgLi4uKSBvciBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0Ly8gRXhwbGljaXQtc291cmNlIGZvcm06IGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdFx0XHRpZiAoY2FsbC5hcmd1bWVudHMubGVuZ3RoID49IDIgJiYgdHMuaXNJZGVudGlmaWVyKGNhbGwuYXJndW1lbnRzWyAwIF0pKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZU5hbWUgPSBjYWxsLmFyZ3VtZW50c1sgMCBdLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBQbGFpbiByb290IGRlZmluZSBpbiBkZWZhdWx0IGNvbGxlY3Rpb25cblx0XHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiBYLmRlZmluZSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0Y29uc3Qgb2JqID0gZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG9iaikpIHtcblx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShvYmoudGV4dCk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBOZXN0ZWQgYWNjZXNzOiBpbnN0YW5jZS5UeXBlLmRlZmluZSAtIHRyeSB0byByZXNvbHZlXG5cdFx0XHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKG9iaik7XG5cdFx0XHRcdGlmIChjaGFpbi5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoY2hhaW4uam9pbignLicpKTtcblx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUgfTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihvYmopKSB7XG5cdFx0XHRcdC8vIERldGVybWluZSB0aGUgY29sbGVjdGlvbiBjb250ZXh0IGZyb20gdGhlIHJvb3Qgb2YgdGhlIGNoYWluIHNvIHRoYXRcblx0XHRcdFx0Ly8gY3VzdG9tLWNvbGxlY3Rpb24gdHlwZXMgZG8gbm90IGdldCBjb25mdXNlZCB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcy5cblx0XHRcdFx0Y29uc3Qgcm9vdElkID0gdGhpcy5nZXRSb290SWRlbnRpZmllcihvYmouZXhwcmVzc2lvbik7XG5cdFx0XHRcdGNvbnN0IGV4cGVjdGVkQ29sbGVjdGlvbklkID0gcm9vdElkXG5cdFx0XHRcdFx0PyB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uocm9vdElkLnRleHQpLmNvbGxlY3Rpb25JZFxuXHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXG5cdFx0XHRcdC8vIENoYWluZWQgY2FsbDogZGVmaW5lKCdBJykuZGVmaW5lKCdCJykgb3IgbW5lbW9uaWNhLmRlZmluZSgnQScpLmRlZmluZSgnQicpXG5cdFx0XHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ2FsbChvYmosIGNhbGwuZ2V0U291cmNlRmlsZSgpKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdFR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0Ly8gSW5oZXJpdCBjb2xsZWN0aW9uIGZyb20gdGhlIHBhcmVudCB0eXBlIChpZiBhbnkpXG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIENoYWluZWQgbGF6eSBjYWxsOiBsYXp5KCdBJykuZGVmaW5lKCdCJykgb3IgVHlwZS5sYXp5KCdBJykuZGVmaW5lKCdCJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzTGF6eUNhbGwob2JqLCBjYWxsLmdldFNvdXJjZUZpbGUoKSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gQnVpbGRlciBsb29rdXAgY2hhaW46IEFwcC5sb29rdXAoJ1VzZXInKS5kZWZpbmUoJ0FkbWluJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMb29rdXBDYWxsKG9iaikpIHtcblx0XHRcdFx0XHRjb25zdCBsb29rZWRVcFBhdGggPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKG9iaik7XG5cdFx0XHRcdFx0aWYgKGxvb2tlZFVwUGF0aCkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUobG9va2VkVXBQYXRoKTtcblx0XHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZS5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHR9XG5cblx0LyoqXG5cdCAqIFByZWZpeCBhIGRvdHRlZCB0eXBlIHBhdGggd2l0aCBhIGNvbGxlY3Rpb24gaWRlbnRpZmllciBzbyBjdXN0b20tY29sbGVjdGlvblxuXHQgKiB0eXBlcyBkbyBub3QgY29sbGlkZSB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcyBpbiB0aGUgZ3JhcGguXG5cdCAqL1xuXHRwcml2YXRlIHByZWZpeENvbGxlY3Rpb25QYXRoIChwYXRoOiBzdHJpbmcsIGNvbGxlY3Rpb25JZDogc3RyaW5nKTogc3RyaW5nIHtcblx0XHRyZXR1cm4gYCR7Y29sbGVjdGlvbklkfTo6JHtwYXRofWA7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGRlZmluZSgpIHNvdXJjZSBpZGVudGlmaWVyIHRvIGVpdGhlciBhIHBhcmVudCB0eXBlLCBhIGNvbGxlY3Rpb24sXG5cdCAqIG9yIHRoZSBkZWZhdWx0IChtb2R1bGUgb2JqZWN0KSBjb2xsZWN0aW9uLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRGVmaW5lU291cmNlIChzb3VyY2VOYW1lOiBzdHJpbmcpOiB7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Ly8gTW9kdWxlIG9iamVjdCBhbGlhc2VzIC0+IHJvb3QgaW4gZGVmYXVsdCBjb2xsZWN0aW9uXG5cdFx0aWYgKHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhzb3VyY2VOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdC8vIENvbGxlY3Rpb24gdmFyaWFibGVzIC0+IHJvb3QgaW4gdGhhdCBjb2xsZWN0aW9uXG5cdFx0Y29uc3QgY29sbGVjdGlvbklkID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChzb3VyY2VOYW1lKTtcblx0XHRpZiAoY29sbGVjdGlvbklkKSB7XG5cdFx0XHRyZXR1cm4geyBjb2xsZWN0aW9uSWQgfTtcblx0XHR9XG5cblx0XHQvLyBPdGhlcndpc2UgdHJlYXQgYXMgYSB0eXBlIHZhcmlhYmxlIHJlZmVyZW5jZVxuXHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlJZGVudGlmaWVyKHNvdXJjZU5hbWUpO1xuXHRcdHJldHVybiB7IHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhIGNhbGwgZXhwcmVzc2lvbiBpcyBhIGxvb2t1cCgpIGNhbGwuXG5cdCAqL1xuXHRwcml2YXRlIGlzTG9va3VwQ2FsbCAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24pOiBib29sZWFuIHtcblx0XHRjb25zdCBleHByID0gbm9kZS5leHByZXNzaW9uO1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikgJiYgZXhwci50ZXh0ID09PSAnbG9va3VwJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSAmJiBleHByLm5hbWUudGV4dCA9PT0gJ2xvb2t1cCcpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGxvb2t1cCgpIGNhbGwgdG8gYSBkb3R0ZWQgdHlwZSBwYXRoIChiZXN0IGVmZm9ydCkuXG5cdCAqIEhhbmRsZXM6XG5cdCAqICAgbG9va3VwKCdVc2VyJylcblx0ICogICBsb29rdXAoc291cmNlLCAnVXNlcicpXG5cdCAqICAgQXBwLmxvb2t1cCgnVXNlcicpXG5cdCAqICAgY29sbGVjdGlvbi5sb29rdXAoJ1VzZXIuQWRtaW4nKVxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlTG9va3VwUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGFyZ3MgPSBjYWxsLmFyZ3VtZW50cztcblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gU2luZ2xlLWFyZyBsb29rdXA6IGxvb2t1cCgnVXNlcicpIG9yIEFwcC5sb29rdXAoJ1VzZXInKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMSkge1xuXHRcdFx0Y29uc3QgWyBhcmcgXSA9IGFyZ3M7XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGFyZykgfHwgdHMuaXNOb1N1YnN0aXR1dGlvblRlbXBsYXRlTGl0ZXJhbChhcmcpKSB7XG5cdFx0XHRcdGNvbnN0IHBhdGggPSBhcmcudGV4dDtcblx0XHRcdFx0Ly8gSWYgdGhpcyBpcyBhIG1ldGhvZCBjYWxsIG9uIGEgc291cmNlLCByZXNvbHZlIHJlbGF0aXZlIHRvIHRoYXQgc291cmNlLlxuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdGNvbnN0IHNvdXJjZUV4cHIgPSBjYWxsLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKHNvdXJjZUV4cHIpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBzb3VyY2VOYW1lID0gc291cmNlRXhwci50ZXh0O1xuXHRcdFx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShzb3VyY2VOYW1lKTtcblx0XHRcdFx0XHRcdGlmIChzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUpIHtcblx0XHRcdFx0XHRcdFx0Ly8gVHlwZSBsb29rdXA6IHJlbGF0aXZlIGZpcnN0LCB0aGVuIHJvb3QgZmFsbGJhY2suXG5cdFx0XHRcdFx0XHRcdC8vIEZvciBhIHR5cGUgaW5zaWRlIGEgY3VzdG9tIGNvbGxlY3Rpb24gdGhlIGZhbGxiYWNrIHJvb3QgaXNcblx0XHRcdFx0XHRcdFx0Ly8gdGhlIGNvbGxlY3Rpb24gcm9vdCwgbmV2ZXIgdGhlIGRlZmF1bHQgY29sbGVjdGlvbi5cblx0XHRcdFx0XHRcdFx0Y29uc3QgcmVsYXRpdmVQYXRoID0gYCR7c291cmNlQ29udGV4dC5wYXJlbnRUeXBlLmZ1bGxQYXRofS4ke3BhdGh9YDtcblx0XHRcdFx0XHRcdFx0aWYgKHRoaXMuZ3JhcGguZmluZFR5cGUocmVsYXRpdmVQYXRoKSkge1xuXHRcdFx0XHRcdFx0XHRcdHJldHVybiByZWxhdGl2ZVBhdGg7XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdFx0aWYgKHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKSB7XG5cdFx0XHRcdFx0XHRcdFx0cmV0dXJuIHRoaXMucHJlZml4Q29sbGVjdGlvblBhdGgocGF0aCwgc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRcdHJldHVybiBwYXRoO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKSB7XG5cdFx0XHRcdFx0XHRcdC8vIENvbGxlY3Rpb24gbG9va3VwOiBwcmVmaXggcGF0aCB3aXRoIHRoZSBjb2xsZWN0aW9uIGlkXG5cdFx0XHRcdFx0XHRcdHJldHVybiB0aGlzLnByZWZpeENvbGxlY3Rpb25QYXRoKHBhdGgsIHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHBhdGg7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIFR3by1hcmcgbG9va3VwOiBsb29rdXAoc291cmNlLCAnVXNlcicpXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIpIHtcblx0XHRcdGNvbnN0IFsgc291cmNlQXJnLCBwYXRoQXJnIF0gPSBhcmdzO1xuXHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoc291cmNlQXJnKSB8fCAhdHMuaXNTdHJpbmdMaXRlcmFsKHBhdGhBcmcpKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBzb3VyY2VOYW1lID0gc291cmNlQXJnLnRleHQ7XG5cdFx0XHRjb25zdCBwYXRoID0gcGF0aEFyZy50ZXh0O1xuXHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShzb3VyY2VOYW1lKTtcblx0XHRcdGlmIChzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUpIHtcblx0XHRcdFx0Ly8gU2FtZSByZWxhdGl2ZS1maXJzdCBsYXcgYXMgdGhlIHNpbmdsZS1hcmcgZm9ybTsgY29sbGVjdGlvblxuXHRcdFx0XHQvLyBtZW1iZXJzIGZhbGwgYmFjayB0byB0aGVpciBjb2xsZWN0aW9uIHJvb3QsIG5vdCB0aGUgZ2xvYmFsIG9uZS5cblx0XHRcdFx0Y29uc3QgcmVsYXRpdmVQYXRoID0gYCR7c291cmNlQ29udGV4dC5wYXJlbnRUeXBlLmZ1bGxQYXRofS4ke3BhdGh9YDtcblx0XHRcdFx0aWYgKHRoaXMuZ3JhcGguZmluZFR5cGUocmVsYXRpdmVQYXRoKSkge1xuXHRcdFx0XHRcdHJldHVybiByZWxhdGl2ZVBhdGg7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHRoaXMucHJlZml4Q29sbGVjdGlvblBhdGgocGF0aCwgc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiBwYXRoO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKSB7XG5cdFx0XHRcdHJldHVybiB0aGlzLnByZWZpeENvbGxlY3Rpb25QYXRoKHBhdGgsIHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKTtcblx0XHRcdH1cblx0XHRcdHJldHVybiBwYXRoO1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogTG9va3VwLWxhdyBkZWxlZ2F0ZSBmb3IgdGhlIGxvY2FsLXNjb3BlIHdhbGtlciAoc2NvcGVzLmpzb24gdHlwZVBhdGhcblx0ICogbWV0YWRhdGEpOiByZXNvbHZlIGEgbG9va3VwKCkgaW5pdGlhbGl6ZXIgY2FsbCB0aHJvdWdoIGV4YWN0bHkgdGhlXG5cdCAqIHRpZXJzIHRoZSB1c2FnZXMgcGFzcyByZXNvbHZlZCBpdCBhZ2FpbnN0IChzYW1lIHNvdXJjZSByZXNvbHV0aW9uLFxuXHQgKiBzYW1lIGNvbXBsZXRlIGdyYXBoKS4gVGhlIHdhbGtlciBydW5zIGl0cyBvd24gc2NvcGUtY2hhaW4gdmFsdWUtc2NvcGVcblx0ICogdGllciBiZWZvcmUgZGVsZWdhdGluZzsgZXZlcnl0aGluZyBhYm92ZSB2YWx1ZSBzY29wZSBsYW5kcyBoZXJlLCBzb1xuXHQgKiBzY29wZXMuanNvbiBuZXZlciBkaXNhZ3JlZXMgd2l0aCB0aGUgaGFyZC1mYWlsLWxhdyB2ZXJkaWN0cy5cblx0ICovXG5cdHJlc29sdmVMb29rdXBDYWxsUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMucmVzb2x2ZUxvb2t1cFBhdGgoY2FsbCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHRcdCogRmluZCBhIHBhcmVudCB0eXBlIGJ5IGl0cyBuYW1lLCBzZWFyY2hpbmcgaW4gdGhlIGdyYXBoLlxuXHRcdCogV2hlbiBjb2xsZWN0aW9uSWQgaXMgcHJvdmlkZWQsIG9ubHkgdHlwZXMgZnJvbSB0aGF0IGNvbGxlY3Rpb24gYXJlIGNvbnNpZGVyZWQuXG5cdFx0Ki9cblx0cHJpdmF0ZSBmaW5kUGFyZW50VHlwZUJ5TmFtZSAoXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZ1xuXHQpOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgbWF0Y2hlc0NvbGxlY3Rpb24gPSAodHlwZTogVHlwZU5vZGUpOiBib29sZWFuID0+IHtcblx0XHRcdGlmIChjb2xsZWN0aW9uSWQgPT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRyZXR1cm4gdHlwZS5jb2xsZWN0aW9uSWQgPT09IHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB0eXBlLmNvbGxlY3Rpb25JZCA9PT0gY29sbGVjdGlvbklkO1xuXHRcdH07XG5cblx0XHQvLyBGaXJzdCB0cnkgZXhhY3QgbWF0Y2ggKGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcyB1c2UgdGhlIHBsYWluIGRvdHRlZCBwYXRoKVxuXHRcdGNvbnN0IGV4YWN0ID0gdGhpcy5ncmFwaC5maW5kVHlwZShuYW1lKTtcblx0XHRpZiAoZXhhY3QgJiYgbWF0Y2hlc0NvbGxlY3Rpb24oZXhhY3QpKSB7XG5cdFx0XHRyZXR1cm4gZXhhY3Q7XG5cdFx0fVxuXG5cdFx0Ly8gVGhlbiBzZWFyY2ggdGhyb3VnaCBhbGwgdHlwZXMgZm9yIG9uZSB3aXRoIG1hdGNoaW5nIG5hbWUgYW5kIGNvbGxlY3Rpb25cblx0XHRmb3IgKGNvbnN0IHR5cGUgb2YgdGhpcy5ncmFwaC5nZXRBbGxUeXBlcygpKSB7XG5cdFx0XHRpZiAodHlwZS5uYW1lID09PSBuYW1lICYmIG1hdGNoZXNDb2xsZWN0aW9uKHR5cGUpKSB7XG5cdFx0XHRcdHJldHVybiB0eXBlO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0XHQqIEZpbmQgYSBwYXJlbnQgdHlwZSBmcm9tIGFuIGlkZW50aWZpZXIgcmVmZXJlbmNlLlxuXHRcdCogSGFuZGxlcyBib3RoIGFsaWFzZWQgdmFyaWFibGVzIChjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKSlcblx0XHQqIGFuZCBkaXJlY3QgY2xhc3MvdHlwZSBuYW1lcy5cblx0XHQqL1xuXHRwcml2YXRlIGZpbmRQYXJlbnRUeXBlQnlJZGVudGlmaWVyIChuYW1lOiBzdHJpbmcpOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gRmlyc3QgY2hlY2sgdmFyaWFibGUgbWFwcGluZzogY29uc3QgVXNlciA9IGRlZmluZSgnVXNlckVudGl0eScsIC4uLilcblx0XHRjb25zdCBtYXBwZWRGdWxsUGF0aCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KG5hbWUpO1xuXHRcdGlmIChtYXBwZWRGdWxsUGF0aCkge1xuXHRcdFx0Y29uc3QgbWFwcGVkTm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUobWFwcGVkRnVsbFBhdGgpO1xuXHRcdFx0aWYgKG1hcHBlZE5vZGUpIHJldHVybiBtYXBwZWROb2RlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKG5hbWUpO1xuXHRcdHJldHVybiBwYXJlbnROb2RlO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCB0aGUgbGVmdG1vc3QgaWRlbnRpZmllciBvZiBhIHByb3BlcnR5LWFjY2VzcyBjaGFpbi5cblx0ICogRm9yIGBBcHAuZGVmaW5lKCdVc2VyJykuZGVmaW5lKCdBZG1pbicpYCB0aGlzIHJldHVybnMgdGhlIGBBcHBgIGlkZW50aWZpZXIuXG5cdCAqL1xuXHRwcml2YXRlIGdldFJvb3RJZGVudGlmaWVyIChleHByOiB0cy5FeHByZXNzaW9uKTogdHMuSWRlbnRpZmllciB8IHVuZGVmaW5lZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLkV4cHJlc3Npb24gPSBleHByO1xuXHRcdHdoaWxlICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50KSkge1xuXHRcdFx0cmV0dXJuIGN1cnJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0XHQqIEdldCBwcm9wZXJ0eSBjaGFpbiBmcm9tIG5lc3RlZCBhY2Nlc3Ncblx0XHQqL1xuXHRwcml2YXRlIGdldFByb3BlcnR5Q2hhaW4gKGV4cHI6IHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbiB8IHRzLklkZW50aWZpZXIpOiBzdHJpbmdbXSB7XG5cdFx0Y29uc3QgY2hhaW46IHN0cmluZ1tdID0gW107XG5cblx0XHRsZXQgY3VycmVudDogdHMuRXhwcmVzc2lvbiA9IGV4cHI7XG5cdFx0d2hpbGUgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRpZiAoY3VycmVudC5uYW1lKSB7XG5cdFx0XHRcdGNoYWluLnVuc2hpZnQoY3VycmVudC5uYW1lLnRleHQpO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQuZXhwcmVzc2lvbjtcblx0XHR9XG5cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQpKSB7XG5cdFx0XHRjaGFpbi51bnNoaWZ0KGN1cnJlbnQudGV4dCk7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGNoYWluO1xuXHR9XG5cblx0LyoqXG5cdCAqIERldGVybWluZSB0aGUgY29uc3RydWN0b3IgZXhwcmVzc2lvbiBmb3IgZWl0aGVyIGEgZGVmaW5lKCkgb3IgbGF6eSgpIGNhbGwuXG5cdCAqIEZvciBkZWZpbmUoKSB0aGlzIGlzIHRoZSBjb25zdHJ1Y3QgaGFuZGxlcjsgZm9yIGxhenkoKSBpdCBpcyB0aGUgdmFsdWVcblx0ICogcmV0dXJuZWQgYnkgdGhlIGxhenkgZ2V0dGVyLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGV4cHIgPSBjYWxsLmV4cHJlc3Npb247XG5cdFx0Y29uc3QgbmFtZSA9IHRzLmlzSWRlbnRpZmllcihleHByKVxuXHRcdFx0PyBleHByLnRleHRcblx0XHRcdDogdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcilcblx0XHRcdFx0PyBleHByLm5hbWUudGV4dFxuXHRcdFx0XHQ6ICcnO1xuXG5cdFx0aWYgKG5hbWUgPT09ICdsYXp5Jykge1xuXHRcdFx0Y29uc3QgbGF6eUFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0XHRpZiAoIWxhenlBcmdzKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdGhpcy51bndyYXBMYXp5R2V0dGVyKGxhenlBcmdzLmdldHRlcik7XG5cdFx0fVxuXG5cdFx0Ly8gZGVmaW5lKCkgY2FsbFxuXHRcdGNvbnN0IGFyZ3MgPSBjYWxsLmFyZ3VtZW50cztcblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gTW9kZXJuIGZvcm06IGRlZmluZSgnTmFtZScsIGhhbmRsZXIsIGNvbmZpZz8pXG5cdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChhcmdzWyAwIF0pKSB7XG5cdFx0XHRyZXR1cm4gYXJnc1sgMSBdO1xuXHRcdH1cblxuXHRcdC8vIExlZ2FjeSBmb3JtOiBkZWZpbmUoZnVuY3Rpb24gTmFtZSgpIHt9KSBvciBkZWZpbmUoKCkgPT4gY2xhc3MgTmFtZSB7fSlcblx0XHRyZXR1cm4gYXJnc1sgMCBdO1xuXHR9XG5cblx0LyoqXG5cdCAqIERldGVjdCBhbiBhc3luYyBjb25zdHJ1Y3RvciBoYW5kbGVyOiB0aGUgYXN5bmMgbW9kaWZpZXIgb24gYVxuXHQgKiBmdW5jdGlvbiBleHByZXNzaW9uIG9yIGFycm93LiBBc3luYyBDTEFTU0VTIChhIGNsYXNzIGNvbnN0cnVjdG9yXG5cdCAqIHJldHVybmluZyBhIFByb21pc2UpIGFyZSBkZWxpYmVyYXRlbHkgTk9UIGRldGVjdGVkIOKAlCB0aGUgc3ludGFjdGljXG5cdCAqIGNsYXNzIHNoYXBlIGdpdmVzIG5vIHJlbGlhYmxlIHNpZ25hbCB3aXRob3V0IGEgdHlwZSBjaGVja2VyLCBhbmQgdGhlXG5cdCAqIG93bmVyIGRlY2lkZWQgdGhleSBhcmUgdHlwZWQgYnkgdGhlIHVzZXIgaW4gdXNlcmxhbmQuXG5cdCAqL1xuXHRwcml2YXRlIGlzQXN5bmNDb25zdHJ1Y3RIYW5kbGVyIChjb25zdHJ1Y3RvckV4cHI6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQpOiBib29sZWFuIHtcblx0XHRpZiAoIWNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblx0XHRjb25zdCBpc0ZuID0gdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSB8fFxuXHRcdFx0dHMuaXNBcnJvd0Z1bmN0aW9uKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0aWYgKCFpc0ZuKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXHRcdGNvbnN0IG1vZGlmaWVycyA9IHRzLmdldE1vZGlmaWVycyhjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdGNvbnN0IHJlc3VsdCA9ICEhbW9kaWZpZXJzICYmIG1vZGlmaWVycy5zb21lKChtb2RpZmllcikgPT4ge1xuXHRcdFx0cmV0dXJuIG1vZGlmaWVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuQXN5bmNLZXl3b3JkO1xuXHRcdH0pO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gY29uc3RydWN0b3IgZnVuY3Rpb25cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFByb3BlcnRpZXMgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpO1xuXHRcdGlmICghY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRyZXR1cm4gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5leHRyYWN0UHJvcGVydGllc0Zyb21Db25zdHJ1Y3Rvcihjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gYSBjb25zdHJ1Y3RvciBleHByZXNzaW9uIChmdW5jdGlvbiwgYXJyb3csIG9yIGNsYXNzKS5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFByb3BlcnRpZXNGcm9tQ29uc3RydWN0b3IgKGNvbnN0cnVjdG9yRXhwcjogdHMuRXhwcmVzc2lvbik6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Ly8gQnVpbGQgdHlwZSBtYXAgZnJvbSBkYXRhIHBhcmFtZXRlciAoZm9yIHRoaXMueCA9IGRhdGEueCBwYXR0ZXJucylcblx0XHRjb25zdCBkYXRhVHlwZU1hcCA9IHRoaXMuYnVpbGREYXRhVHlwZU1hcChjb25zdHJ1Y3RvckV4cHIpO1xuXG5cdFx0Ly8gSGFuZGxlIGZ1bmN0aW9uIGV4cHJlc3Npb25cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSB8fCB0cy5pc0Fycm93RnVuY3Rpb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBjb25zdHJ1Y3RvckV4cHI7XG5cblx0XHRcdC8vIEZpcnN0LCBleHRyYWN0IHByb3BlcnRpZXMgZnJvbSBgdGhpc2AgcGFyYW1ldGVyIHR5cGUgYW5ub3RhdGlvblxuXHRcdFx0Ly8gVGhpcyBoYW5kbGVzIHBhdHRlcm5zIGxpa2U6IGZ1bmN0aW9uKHRoaXM6IFNvbWVUeXBlLCBkYXRhOiBTb21lVHlwZSkgeyB9XG5cdFx0XHRjb25zdCB0aGlzUGFyYW1Qcm9wZXJ0aWVzID0gdGhpcy5leHRyYWN0VGhpc1BhcmFtUHJvcGVydGllcyhjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0Zm9yIChjb25zdCBbIG5hbWUsIHByb3BJbmZvIF0gb2YgdGhpc1BhcmFtUHJvcGVydGllcykge1xuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCBwcm9wSW5mbyk7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEZ1bmN0aW9uIGJvZHkgd2l0aCBzdGF0ZW1lbnRzXG5cdFx0XHRpZiAodHMuaXNCbG9jayhib2R5KSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IHN0bXQgb2YgYm9keS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdFx0aWYgKHRzLmlzRXhwcmVzc2lvblN0YXRlbWVudChzdG10KSkge1xuXHRcdFx0XHRcdFx0dGhpcy5leHRyYWN0UHJvcGVydHlGcm9tU3RhdGVtZW50KHN0bXQuZXhwcmVzc2lvbiwgcHJvcGVydGllcywgZGF0YVR5cGVNYXApO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIEhhbmRsZSBjbGFzcyBleHByZXNzaW9uXG5cdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikpIHtcblx0XHRcdC8vIEZpcnN0IHBhc3M6IGNvbGxlY3QgYWxsIHByb3BlcnR5IHR5cGVzIGZvciBtZXRob2QgaW5mZXJlbmNlXG5cdFx0XHRjb25zdCBjbGFzc1Byb3BlcnR5VHlwZXMgPSB0aGlzLmV4dHJhY3RDbGFzc1Byb3BlcnR5VHlwZXMoY29uc3RydWN0b3JFeHByKTtcblxuXHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgY29uc3RydWN0b3JFeHByLm1lbWJlcnMpIHtcblx0XHRcdFx0Ly8gSGFuZGxlIHByb3BlcnR5IGRlY2xhcmF0aW9uc1xuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eURlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUpIHtcblx0XHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBwcm9wZXJ0aWVzXG5cdFx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0XHRcdG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkO1xuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblxuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpID8gbWVtYmVyLm5hbWUudGV4dCA6ICcnO1xuXHRcdFx0XHRcdGlmIChuYW1lKSB7XG5cdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHRcdHR5cGUgICAgIDogdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpLFxuXHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBIYW5kbGUgbWV0aG9kIGRlY2xhcmF0aW9uc1xuXHRcdFx0XHRpZiAodHMuaXNNZXRob2REZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBtZXRob2RzXG5cdFx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0XHRcdG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkO1xuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblxuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyTWV0aG9kVHlwZShtZW1iZXIsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gSGFuZGxlIGdldHRlciBkZWNsYXJhdGlvbnNcblx0XHRcdFx0aWYgKHRzLmlzR2V0QWNjZXNzb3IobWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgZ2V0dGVyc1xuXHRcdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdFx0XHRtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZDtcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cblx0XHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHQvLyBGaXJzdCB0cnkgZXhwbGljaXQgdHlwZSBhbm5vdGF0aW9uLCB0aGVuIGluZmVyIGZyb20gZ2V0dGVyIGJvZHlcblx0XHRcdFx0XHRsZXQgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRpZiAodHlwZSA9PT0gJ3Vua25vd24nICYmIG1lbWJlci5ib2R5KSB7XG5cdFx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclJldHVyblR5cGVGcm9tQm9keShtZW1iZXIuYm9keSwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0cmVhZG9ubHkgOiB0cnVlLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHQvKipcblx0ICogQnVpbGQgYSB0eXBlIG1hcCBmcm9tIGFsbCBwYXJhbWV0ZXJzIHdpdGggaW5saW5lIG9iamVjdCB0eXBlIGFubm90YXRpb25zXG5cdCAqIFJldHVybnMgYSBtYXAgb2YgXCJwYXJhbU5hbWUucHJvcGVydHlOYW1lXCIgLT4gdHlwZVxuXHQgKi9cblx0cHJpdmF0ZSBidWlsZERhdGFUeXBlTWFwIChoYW5kbGVyQXJnOiB0cy5FeHByZXNzaW9uKTogTWFwPHN0cmluZywgc3RyaW5nPiB7XG5cdFx0Y29uc3QgdHlwZU1hcCA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cblx0XHRpZiAoIXRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGhhbmRsZXJBcmcpICYmICF0cy5pc0Fycm93RnVuY3Rpb24oaGFuZGxlckFyZykpIHtcblx0XHRcdHJldHVybiB0eXBlTWFwO1xuXHRcdH1cblxuXHRcdC8vIEl0ZXJhdGUgb3ZlciBBTEwgcGFyYW1ldGVyc1xuXHRcdGZvciAoY29uc3QgcGFyYW0gb2YgaGFuZGxlckFyZy5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRpZiAoIXBhcmFtLm5hbWUgfHwgIXBhcmFtLnR5cGUpIGNvbnRpbnVlO1xuXG5cdFx0XHQvLyBHZXQgcGFyYW1ldGVyIG5hbWVcblx0XHRcdGxldCBwYXJhbU5hbWUgPSAnJztcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkpIHtcblx0XHRcdFx0cGFyYW1OYW1lID0gcGFyYW0ubmFtZS50ZXh0O1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Ly8gU2tpcCBkZXN0cnVjdHVyZWQgcGFyYW1ldGVycyBmb3Igbm93XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBDaGVjayBpZiBpdCdzIGFuIGlubGluZSBvYmplY3QgdHlwZSBsaXRlcmFsXG5cdFx0XHRpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUocGFyYW0udHlwZSkpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgcGFyYW0udHlwZS5tZW1iZXJzKSB7XG5cdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQoYCR7cGFyYW1OYW1lfS4ke3Byb3BOYW1lfWAsIHR5cGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Ly8gTmFtZWQgdHlwZSByZWZlcmVuY2UgKGFsaWFzL2ludGVyZmFjZS9jbGFzcywgaW1wb3J0ZWQgb3Jcblx0XHRcdFx0Ly8gbG9jYWwg4oCUIEYxNCk6IGRlY29tcG9zZSB0aGUgcmVzb2x2ZWQgZGVjbGFyYXRpb24gaW50b1xuXHRcdFx0XHQvLyBwZXItcHJvcGVydHkgZW50cmllcyB0aHJvdWdoIHRoZSBzYW1lIGltcG9ydC1hd2FyZVxuXHRcdFx0XHQvLyBtYWNoaW5lcnkgYXMgY29uc3RydWN0b3Igc2lnbmF0dXJlcyAoRjEwKSwgaW5jbHVkaW5nIHRoZVxuXHRcdFx0XHQvLyBoZXJpdGFnZSB3YWxrIChGMTMpLiBXaXRob3V0IHRoaXMsIGB0aGlzLnggPSBwYXJhbS55YFxuXHRcdFx0XHQvLyByZWFkIGB1bmtub3duYCBmb3IgbmFtZWQgcGFyYW1zIOKAlCBvbmx5IGlubGluZSBsaXRlcmFsc1xuXHRcdFx0XHQvLyB3ZXJlIGRlY29tcG9zZWQuIFVucmVzb2x2YWJsZSDihpIgd2hvbGUtcGFyYW0gZmFsbGJhY2tcblx0XHRcdFx0Ly8gYmVsb3c7IGEgYmFyZSBuYW1lIGlzIG5ldmVyIGVtaXR0ZWQgZWl0aGVyIHdheVxuXHRcdFx0XHRsZXQgbmFtZWREZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkO1xuXHRcdFx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZShwYXJhbS50eXBlKSAmJiB0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBwYXJhbVR5cGVOYW1lID0gcGFyYW0udHlwZS50eXBlTmFtZS50ZXh0O1xuXHRcdFx0XHRcdG5hbWVkRGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24ocGFyYW1UeXBlTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAobmFtZWREZWNsKSB7XG5cdFx0XHRcdFx0Ly8gbWVtYmVyIHR5cGVzIHJlc29sdmUgYWdhaW5zdCB0aGUgREVDTEFSSU5HIGZpbGVcblx0XHRcdFx0XHRjb25zdCByZWZlcmVuY2luZ0ZpbGUgPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0XHRcdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gbmFtZWREZWNsLmZpbGU7XG5cdFx0XHRcdFx0dHJ5IHtcblx0XHRcdFx0XHRcdGNvbnN0IGRlY2xQcm9wZXJ0aWVzID0gdGhpcy5yZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzKG5hbWVkRGVjbCk7XG5cdFx0XHRcdFx0XHRmb3IgKGNvbnN0IFsgcHJvcE5hbWUsIGluZm8gXSBvZiBkZWNsUHJvcGVydGllcykge1xuXHRcdFx0XHRcdFx0XHR0eXBlTWFwLnNldChgJHtwYXJhbU5hbWV9LiR7cHJvcE5hbWV9YCwgaW5mby50eXBlKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGZpbmFsbHkge1xuXHRcdFx0XHRcdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gcmVmZXJlbmNpbmdGaWxlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHQvLyBrZWVwIHRoZSB3aG9sZS1wYXJhbSBlbnRyeSB0b286IGB0aGlzLnggPSBkYXRhYCAodGhlXG5cdFx0XHRcdFx0Ly8gYmFyZSBwYXJhbWV0ZXIpIGFzc2lnbnMgdGhlIGZ1bGwgZXhwYW5kZWQgc2hhcGUg4oCUXG5cdFx0XHRcdFx0Ly8gdGhlIHNhbWUgc3RyaW5nIGNvbnN0cnVjdG9yLXNpZ25hdHVyZSBlbWlzc2lvbiB1c2VzXG5cdFx0XHRcdFx0Y29uc3Qgd2hvbGVUeXBlID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKG5hbWVkRGVjbCk7XG5cdFx0XHRcdFx0aWYgKHdob2xlVHlwZSAmJiB3aG9sZVR5cGUgIT09ICd1bmtub3duJykge1xuXHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQocGFyYW1OYW1lLCB3aG9sZVR5cGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHQvLyBTdG9yZSBzaW1wbGUgcGFyYW1ldGVyIHR5cGVzIGxpa2UgYGRlY29yYXRlVmFsdWU6IHN0cmluZ2Bcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cdFx0XHRcdFx0aWYgKHR5cGUgIT09ICd1bmtub3duJykge1xuXHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQocGFyYW1OYW1lLCB0eXBlKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdHlwZU1hcDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnR5IGFjY2VzcyBjaGFpbiAoZS5nLiwgXCJkYXRhUmVuYW1lZC5pZFwiIGZyb20gZGF0YVJlbmFtZWQuaWQpXG5cdCAqIEhhbmRsZXMgZmFsbGJhY2tzIGxpa2U6IGRhdGEucGVybWlzc2lvbnMgfHwgW11cblx0ICovXG5cdHByaXZhdGUgZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbiAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gSGFuZGxlIGlkZW50aWZpZXI6IGRhdGFcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci50ZXh0O1xuXHRcdH1cblx0XHQvLyBIYW5kbGUgcHJvcGVydHkgYWNjZXNzOiBkYXRhLnBlcm1pc3Npb25zXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBiYXNlID0gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGV4cHIuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoYmFzZSkge1xuXHRcdFx0XHRyZXR1cm4gYCR7YmFzZX0uJHtleHByLm5hbWUudGV4dH1gO1xuXHRcdFx0fVxuXHRcdH1cblx0XHQvLyBIYW5kbGUgZmFsbGJhY2sgcGF0dGVybjogZGF0YS5wZXJtaXNzaW9ucyB8fCBbXVxuXHRcdGlmICh0cy5pc0JpbmFyeUV4cHJlc3Npb24oZXhwcikgJiZcblx0XHRcdGV4cHIub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkJhckJhclRva2VuKSB7XG5cdFx0XHQvLyBSZXR1cm4gdGhlIGxlZnQgc2lkZSBvZiB8fCBvcGVyYXRvclxuXHRcdFx0cmV0dXJuIHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihleHByLmxlZnQpO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydHkgYXNzaWdubWVudCBmcm9tIHN0YXRlbWVudFxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UHJvcGVydHlGcm9tU3RhdGVtZW50IChcblx0XHRleHByOiB0cy5FeHByZXNzaW9uLFxuXHRcdHByb3BlcnRpZXM6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4sXG5cdFx0ZGF0YVR5cGVNYXA6IE1hcDxzdHJpbmcsIHN0cmluZz4gPSBuZXcgTWFwKClcblx0KTogdm9pZCB7XG5cdFx0Ly8gSGFuZGxlOiB0aGlzLnByb3BlcnR5ID0gdmFsdWVcblx0XHRpZiAodHMuaXNCaW5hcnlFeHByZXNzaW9uKGV4cHIpICYmXG5cdFx0XHRleHByLm9wZXJhdG9yVG9rZW4ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbikge1xuXHRcdFx0Y29uc3QgeyBsZWZ0IH0gPSBleHByO1xuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obGVmdCkpIHtcblx0XHRcdFx0Ly8gQ2hlY2sgaWYgYWNjZXNzaW5nICd0aGlzJyAoVGhpc0tleXdvcmQpXG5cdFx0XHRcdGlmIChsZWZ0LmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBsZWZ0Lm5hbWU/LnRleHQ7XG5cdFx0XHRcdFx0aWYgKG5hbWUpIHtcblx0XHRcdFx0XHRcdC8vIFRyeSB0byBnZXQgdHlwZSBmcm9tIGRhdGFUeXBlTWFwIHVzaW5nIGZ1bGwgYWNjZXNzIGNoYWluIChlLmcuLCBcImRhdGFSZW5hbWVkLmlkXCIpXG5cdFx0XHRcdFx0XHRjb25zdCBhY2Nlc3NDaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihleHByLnJpZ2h0KTtcblx0XHRcdFx0XHRcdGxldCB0eXBlID0gYWNjZXNzQ2hhaW4gPyBkYXRhVHlwZU1hcC5nZXQoYWNjZXNzQ2hhaW4pIDogdW5kZWZpbmVkO1xuXHRcdFx0XHRcdFx0Ly8gSWYgbm90IGZvdW5kIGFuZCBSSFMgaXMgYSBzaW1wbGUgaWRlbnRpZmllciwgdHJ5IGxvb2tpbmcgaXQgdXAgZGlyZWN0bHlcblx0XHRcdFx0XHRcdGlmICghdHlwZSAmJiB0cy5pc0lkZW50aWZpZXIoZXhwci5yaWdodCkpIHtcblx0XHRcdFx0XHRcdFx0dHlwZSA9IGRhdGFUeXBlTWFwLmdldChleHByLnJpZ2h0LnRleHQpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0Ly8gYSBib3VuZCBjb25zdHJ1Y3Rpb24gcmVzdWx0IChuZXcvbG9va3VwL2NoYWluL2ZvcmsvXG5cdFx0XHRcdFx0XHQvLyBtZXJnZS9jYWxsKTogdGhlIHZhbHVlIHNjb3BlIGJpbmRpbmcgc3VwcGxpZXMgdGhlXG5cdFx0XHRcdFx0XHQvLyBncmFwaCB0eXBlIOKAlCBlbWl0dGVkIGJ5IGl0cyBpbnN0YW5jZS10eXBlIG5hbWVcblx0XHRcdFx0XHRcdGlmICghdHlwZSAmJiB0cy5pc0lkZW50aWZpZXIoZXhwci5yaWdodCkpIHtcblx0XHRcdFx0XHRcdFx0Y29uc3QgYm91bmQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChleHByLnJpZ2h0LnRleHQpO1xuXHRcdFx0XHRcdFx0XHRpZiAoYm91bmQpIHtcblx0XHRcdFx0XHRcdFx0XHQvLyBFbWl0IHRoZSBhbGlhcyB0eXBlcy50cyBkZWNsYXJlcyAoT3B0aW9uIEJcblx0XHRcdFx0XHRcdFx0XHQvLyByZWdpc3RyeSBwcmVmaXgpLCBub3QgdGhlIHJhdyBjb2xsZWN0aW9uSWQ6OlxuXHRcdFx0XHRcdFx0XHRcdC8vIGZ1bGxQYXRoOyBuZXZlci1lbWl0dGVkIHR5cGVzIGZhbGwgdGhyb3VnaFxuXHRcdFx0XHRcdFx0XHRcdC8vIHRvIGluaXRpYWxpemVyIGluZmVyZW5jZVxuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IGJvdW5kTm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoYm91bmQpO1xuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IGJvdW5kQWxpYXMgPSBib3VuZE5vZGVcblx0XHRcdFx0XHRcdFx0XHRcdD8gdGhpcy5nZXRFbWl0dGVkSW5zdGFuY2VUeXBlTmFtZShib3VuZE5vZGUpXG5cdFx0XHRcdFx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblx0XHRcdFx0XHRcdFx0XHRpZiAoYm91bmRBbGlhcykge1xuXHRcdFx0XHRcdFx0XHRcdFx0dHlwZSA9IGJvdW5kQWxpYXM7XG5cdFx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRpZiAoIXR5cGUpIHtcblx0XHRcdFx0XHRcdFx0dHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKGV4cHIucmlnaHQsIGRhdGFUeXBlTWFwKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdC8vIERvbid0IG92ZXJ3cml0ZSBhIGtub3duIHR5cGUgZnJvbSBhIGB0aGlzYCBhbm5vdGF0aW9uXG5cdFx0XHRcdFx0XHQvLyB3aXRoIGFuIHVua25vd24tYmVhcmluZyBpbmZlcmVuY2U6IGFuIGVtcHR5LWFycmF5XG5cdFx0XHRcdFx0XHQvLyBpbml0aWFsaXplciBpbmZlcnMgJ0FycmF5PHVua25vd24+Jywgd2hpY2ggbXVzdCBub3Rcblx0XHRcdFx0XHRcdC8vIGNsb2JiZXIgYW4gYW5ub3RhdGVkICdBcnJheTx7IGlkOiBudW1iZXIgfT4nIGVpdGhlci5cblx0XHRcdFx0XHRcdC8vIFwiS25vd25cIiBvbiB0aGUgRVhJU1RJTkcgc2lkZSBtZWFucyB0aGUgd2hvbGUgdHlwZSBJU1xuXHRcdFx0XHRcdFx0Ly8gYHVua25vd25gIChleGFjdCBtYXRjaCkg4oCUIGEgc3Vic3RyaW5nIG1hdGNoIHRyZWF0c1xuXHRcdFx0XHRcdFx0Ly8gYFJlY29yZDxzdHJpbmcsIHVua25vd24+YCBhcyB1bmtub3duLWJlYXJpbmcgYW5kIGxldFxuXHRcdFx0XHRcdFx0Ly8gaW5mZXJlbmNlIGNsb2JiZXIgYSBnb29kIGFubm90YXRpb24gKEYxNClcblx0XHRcdFx0XHRcdGNvbnN0IGV4aXN0aW5nID0gcHJvcGVydGllcy5nZXQobmFtZSk7XG5cdFx0XHRcdFx0XHRjb25zdCB0eXBlSGFzVW5rbm93biA9ICF0eXBlIHx8IHR5cGUuaW5jbHVkZXMoJ3Vua25vd24nKTtcblx0XHRcdFx0XHRcdGNvbnN0IGV4aXN0aW5nSXNLbm93biA9IGV4aXN0aW5nID8gZXhpc3RpbmcudHlwZS50cmltKCkgIT09ICd1bmtub3duJyA6IGZhbHNlO1xuXHRcdFx0XHRcdFx0aWYgKGV4aXN0aW5nSXNLbm93biAmJiB0eXBlSGFzVW5rbm93bikge1xuXHRcdFx0XHRcdFx0XHQvLyBLZWVwIHRoZSBiZXR0ZXIgdHlwZSBmcm9tIGV4cGxpY2l0IGFubm90YXRpb25cblx0XHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBleGlzdGluZyA/IGV4aXN0aW5nLm9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIEhhbmRsZTogT2JqZWN0LmFzc2lnbih0aGlzLCB7IHByb3A6IHZhbHVlIH0pXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdGNvbnN0IGZuID0gZXhwci5leHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGZuKSAmJlxuXHRcdFx0XHRmbi5uYW1lPy50ZXh0ID09PSAnYXNzaWduJyAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoZm4uZXhwcmVzc2lvbikgJiZcblx0XHRcdFx0Zm4uZXhwcmVzc2lvbi50ZXh0ID09PSAnT2JqZWN0Jykge1xuXHRcdFx0XHRjb25zdCBhcmdzID0gZXhwci5hcmd1bWVudHM7XG5cdFx0XHRcdGlmIChhcmdzLmxlbmd0aCA+PSAyICYmIGFyZ3NbIDAgXS5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gdGhlIHNlY29uZCBhcmd1bWVudFxuXHRcdFx0XHRcdGNvbnN0IFsgLCBwcm9wc0FyZyBdID0gYXJncztcblx0XHRcdFx0XHRpZiAodHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihwcm9wc0FyZykpIHtcblx0XHRcdFx0XHRcdGZvciAoY29uc3QgcHJvcCBvZiBwcm9wc0FyZy5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSAmJiB0cy5pc0lkZW50aWZpZXIocHJvcC5uYW1lKSkge1xuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBwcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0XHRcdFx0dHlwZSAgICAgOiB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihwcm9wLmluaXRpYWxpemVyKSxcblx0XHRcdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihwcm9wc0FyZykpIHtcblx0XHRcdFx0XHRcdC8vIE9iamVjdC5hc3NpZ24odGhpcywgZGF0YSkg4oCUIHRoZSBpZGVudGlmaWVyIGZvcm06IGV2ZXJ5XG5cdFx0XHRcdFx0XHQvLyBwZXItcHJvcGVydHkgZW50cnkgdGhlIGRhdGEgcGFyYW1ldGVyIGNvbnRyaWJ1dGVkIHRvXG5cdFx0XHRcdFx0XHQvLyB0aGUgdHlwZSBtYXAgYmVjb21lcyBhbiBvd24gcHJvcGVydHkuIFRoaXMgaXMgd2hhdFxuXHRcdFx0XHRcdFx0Ly8gY2FycmllcyB0aGUgZmllbGRzIGZvciB0aGUgc2VsZi1yZWZlcmVuY2luZ1xuXHRcdFx0XHRcdFx0Ly8gaW50ZXJzZWN0aW9uLWFsaWFzIHJvb3QgcGF0dGVybiAoRjIxKTogdGhlIHRoaXMtYWxpYXNcblx0XHRcdFx0XHRcdC8vIGlzIGVyZ29ub21pYy1vbmx5IGFuZCBpdHMgaW50ZXJzZWN0aW9uIG1lbWJlcnMgYXJlXG5cdFx0XHRcdFx0XHQvLyBuZXZlciBleHBhbmRlZCwgc28gdGhlIGFzc2lnbiBpcyB3aGVyZSB0aGUgcm9vdCdzXG5cdFx0XHRcdFx0XHQvLyBmaWVsZHMgbXVzdCBjb21lIGZyb21cblx0XHRcdFx0XHRcdGNvbnN0IHBhcmFtTmFtZSA9IHByb3BzQXJnLnRleHQ7XG5cdFx0XHRcdFx0XHRmb3IgKGNvbnN0IFsga2V5LCB0eXBlIF0gb2YgZGF0YVR5cGVNYXApIHtcblx0XHRcdFx0XHRcdFx0aWYgKCFrZXkuc3RhcnRzV2l0aChgJHtwYXJhbU5hbWV9LmApKSB7XG5cdFx0XHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdFx0Y29uc3QgbmFtZSA9IGtleS5zbGljZShwYXJhbU5hbWUubGVuZ3RoICsgMSk7XG5cdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGNsYXNzIGRlY2xhcmF0aW9uIChpbmNsdWRpbmcgbWV0aG9kcyBhbmQgZ2V0dGVycylcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENsYXNzUHJvcGVydGllcyAoY2xhc3NEZWNsOiB0cy5DbGFzc0RlY2xhcmF0aW9uKTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjbGFzc0RlY2wubWVtYmVycykge1xuXHRcdFx0Ly8gSGFuZGxlIHByb3BlcnR5IGRlY2xhcmF0aW9uc1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlEZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lKSB7XG5cdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIHByb3BlcnRpZXNcblx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdCAgICAgbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQpO1xuXHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpID8gbWVtYmVyLm5hbWUudGV4dCA6ICcnO1xuXHRcdFx0XHRpZiAobmFtZSkge1xuXHRcdFx0XHRcdC8vIElmIG5vIGV4cGxpY2l0IHR5cGUgYnV0IGhhcyBpbml0aWFsaXplciwgaW5mZXIgZnJvbSBpbml0aWFsaXplclxuXHRcdFx0XHRcdGxldCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdGlmICh0eXBlID09PSAndW5rbm93bicgJiYgbWVtYmVyLmluaXRpYWxpemVyKSB7XG5cdFx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIobWVtYmVyLmluaXRpYWxpemVyKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblxuXHRcdFx0Ly8gSGFuZGxlIG1ldGhvZCBkZWNsYXJhdGlvbnNcblx0XHRcdGlmICh0cy5pc01ldGhvZERlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBtZXRob2RzXG5cdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHQgICAgIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkKTtcblx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJNZXRob2RUeXBlKG1lbWJlcik7XG5cdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEhhbmRsZSBnZXR0ZXIgZGVjbGFyYXRpb25zXG5cdFx0XHRpZiAodHMuaXNHZXRBY2Nlc3NvcihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgZ2V0dGVyc1xuXHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0ICAgICBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZCk7XG5cdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdC8vIEZpcnN0IHRyeSBleHBsaWNpdCB0eXBlIGFubm90YXRpb24sIHRoZW4gaW5mZXIgZnJvbSBnZXR0ZXIgYm9keVxuXHRcdFx0XHRsZXQgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0aWYgKHR5cGUgPT09ICd1bmtub3duJyAmJiBtZW1iZXIuYm9keSkge1xuXHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyUmV0dXJuVHlwZUZyb21Cb2R5KG1lbWJlci5ib2R5KTtcblx0XHRcdFx0fVxuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0cmVhZG9ubHkgOiB0cnVlLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGNsYXNzIHByb3BlcnR5IHR5cGVzIGZvciBtZXRob2QgcmV0dXJuIHR5cGUgaW5mZXJlbmNlXG5cdCAqIE1hcHMgcHJvcGVydHkgbmFtZXMgdG8gdGhlaXIgVHlwZVNjcmlwdCB0eXBlIHN0cmluZ3Ncblx0ICogTm90ZTogSW5jbHVkZXMgcHJpdmF0ZS9wcm90ZWN0ZWQgcHJvcGVydGllcyBmb3IgbWV0aG9kIGluZmVyZW5jZVxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q2xhc3NQcm9wZXJ0eVR5cGVzIChjbGFzc0RlY2w6IHRzLkNsYXNzRXhwcmVzc2lvbik6IE1hcDxzdHJpbmcsIHN0cmluZz4ge1xuXHRcdGNvbnN0IHByb3BlcnR5VHlwZXMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXG5cdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgY2xhc3NEZWNsLm1lbWJlcnMpIHtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5RGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdC8vIEluY2x1ZGUgQUxMIHByb3BlcnRpZXMgKGV2ZW4gcHJpdmF0ZSkgZm9yIG1ldGhvZCByZXR1cm4gdHlwZSBpbmZlcmVuY2Vcblx0XHRcdFx0Ly8gVGhlIHZpc2liaWxpdHkgY2hlY2sgaXMgZG9uZSB3aGVuIGFkZGluZyB0byBvdXRwdXQgcHJvcGVydGllc1xuXHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0aWYgKG1lbWJlci50eXBlKSB7XG5cdFx0XHRcdFx0cHJvcGVydHlUeXBlcy5zZXQobmFtZSwgdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBwcm9wZXJ0eVR5cGVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEluZmVyIG1ldGhvZCB0eXBlIGZyb20gbWV0aG9kIGRlY2xhcmF0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGluZmVyTWV0aG9kVHlwZSAobWV0aG9kOiB0cy5NZXRob2REZWNsYXJhdGlvbiwgY2xhc3NQcm9wZXJ0eVR5cGVzPzogTWFwPHN0cmluZywgc3RyaW5nPik6IHN0cmluZyB7XG5cdFx0Y29uc3QgcGFyYW1zID0gbWV0aG9kLnBhcmFtZXRlcnMubWFwKHBhcmFtID0+IHtcblx0XHRcdGNvbnN0IHBhcmFtTmFtZSA9IHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSA/IHBhcmFtLm5hbWUudGV4dCA6ICdhcmcnO1xuXHRcdFx0Y29uc3QgcGFyYW1UeXBlID0gdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cdFx0XHRyZXR1cm4gYCR7cGFyYW1OYW1lfTogJHtwYXJhbVR5cGV9YDtcblx0XHR9KS5qb2luKCcsICcpO1xuXG5cdFx0Y29uc3QgcmV0dXJuVHlwZSA9IHRoaXMuaW5mZXJSZXR1cm5UeXBlKG1ldGhvZCwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblxuXHRcdGlmIChwYXJhbXMpIHtcblx0XHRcdHJldHVybiBgKCR7cGFyYW1zfSkgPT4gJHtyZXR1cm5UeXBlfWA7XG5cdFx0fVxuXHRcdHJldHVybiBgKCkgPT4gJHtyZXR1cm5UeXBlfWA7XG5cdH1cblxuXHQvKipcblx0XHQqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGB0aGlzYCBwYXJhbWV0ZXIgdHlwZSBhbm5vdGF0aW9uXG5cdFx0KiBIYW5kbGVzIHBhdHRlcm5zIGxpa2U6IGZ1bmN0aW9uKHRoaXM6IFNvbWVUeXBlLCBkYXRhOiBTb21lVHlwZSkgeyB9XG5cdFx0Ki9cblx0cHJpdmF0ZSBleHRyYWN0VGhpc1BhcmFtUHJvcGVydGllcyAoaGFuZGxlckFyZzogdHMuRnVuY3Rpb25FeHByZXNzaW9uIHwgdHMuQXJyb3dGdW5jdGlvbik6XG5cdFx0TWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cblx0XHQvLyBGaW5kIHRoZSBgdGhpc2AgcGFyYW1ldGVyIChpZiBhbnkpXG5cdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBoYW5kbGVyQXJnLnBhcmFtZXRlcnMpIHtcblx0XHRcdGlmIChwYXJhbS5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSAmJiBwYXJhbS5uYW1lLnRleHQgPT09ICd0aGlzJyAmJiBwYXJhbS50eXBlKSB7XG5cdFx0XHRcdC8vIENoZWNrIGlmIGl0J3MgYSB0eXBlIHJlZmVyZW5jZSAoZS5nLiwgYHRoaXM6IHVzYWdlYClcblx0XHRcdFx0aWYgKHRzLmlzVHlwZVJlZmVyZW5jZU5vZGUocGFyYW0udHlwZSkpIHtcblx0XHRcdFx0XHRjb25zdCB0eXBlTmFtZSA9IHRzLmlzSWRlbnRpZmllcihwYXJhbS50eXBlLnR5cGVOYW1lKVxuXHRcdFx0XHRcdFx0PyBwYXJhbS50eXBlLnR5cGVOYW1lLnRleHRcblx0XHRcdFx0XHRcdDogJyc7XG5cblx0XHRcdFx0XHQvLyBSZXNvbHZlIHRocm91Z2ggdGhlIHJlZmVyZW5jaW5nIGZpbGUncyBvd24gaW1wb3J0cyBmaXJzdCAoRjEwKVxuXHRcdFx0XHRcdGNvbnN0IGRlY2wgPSB0eXBlTmFtZVxuXHRcdFx0XHRcdFx0PyB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKHR5cGVOYW1lLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpXG5cdFx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblx0XHRcdFx0XHRpZiAoZGVjbCkge1xuXHRcdFx0XHRcdFx0Y29uc3QgZGVjbFByb3BlcnRpZXMgPSB0aGlzLnJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXMoZGVjbCk7XG5cdFx0XHRcdFx0XHRmb3IgKGNvbnN0IFsgcHJvcE5hbWUsIGluZm8gXSBvZiBkZWNsUHJvcGVydGllcykge1xuXHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChwcm9wTmFtZSwgaW5mbyk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIENoZWNrIGlmIGl0J3MgZGlyZWN0bHkgYW4gaW5saW5lIHR5cGUgbGl0ZXJhbCAoZS5nLiwgYHRoaXM6IHsgaWQ6IHN0cmluZyB9YClcblx0XHRcdFx0ZWxzZSBpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUocGFyYW0udHlwZSkpIHtcblx0XHRcdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBwYXJhbS50eXBlLm1lbWJlcnMpIHtcblx0XHRcdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KHByb3BOYW1lLCB7XG5cdFx0XHRcdFx0XHRcdFx0bmFtZSAgICAgOiBwcm9wTmFtZSxcblx0XHRcdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogISFtZW1iZXIucXVlc3Rpb25Ub2tlbixcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIEZvdW5kIHRoZSBgdGhpc2AgcGFyYW1ldGVyLCBubyBuZWVkIHRvIGNvbnRpbnVlXG5cdFx0XHRcdGJyZWFrO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBwcm9wZXJ0aWVzO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBJbmZlciBUeXBlU2NyaXB0IHR5cGUgZnJvbSB0eXBlIG5vZGVcblx0XHQqL1xuXHQvKipcblx0ICogSW5mZXIgVHlwZVNjcmlwdCB0eXBlIGZyb20gdHlwZSBub2RlXG5cdCAqL1xuXHRwcml2YXRlIGluZmVyVHlwZSAodHlwZU5vZGU/OiB0cy5UeXBlTm9kZSk6IHN0cmluZyB7XG5cdFx0aWYgKCF0eXBlTm9kZSkge1xuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cblx0XHRzd2l0Y2ggKHR5cGVOb2RlLmtpbmQpIHtcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuU3RyaW5nS2V5d29yZDpcblx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVtYmVyS2V5d29yZDpcblx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQm9vbGVhbktleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5VbmRlZmluZWRLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICd1bmRlZmluZWQnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdWxsS2V5d29yZDpcblx0XHRcdHJldHVybiAnbnVsbCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkFueUtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ2FueSc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVua25vd25LZXl3b3JkOlxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVm9pZEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3ZvaWQnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5BcnJheVR5cGU6XG5cdFx0XHRyZXR1cm4gYEFycmF5PCR7ICB0aGlzLmluZmVyVHlwZSgodHlwZU5vZGUgYXMgdHMuQXJyYXlUeXBlTm9kZSkuZWxlbWVudFR5cGUpICB9PmA7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR5cGVMaXRlcmFsOiB7XG5cdFx0XHQvLyBJbmxpbmUtZXhwYW5kIHR5cGUgbGl0ZXJhbHMgaW5zdGVhZCBvZiBjb2xsYXBzaW5nIHRvICdvYmplY3QnXG5cdFx0XHRjb25zdCB0eXBlTGl0ID0gdHlwZU5vZGUgYXMgdHMuVHlwZUxpdGVyYWxOb2RlO1xuXHRcdFx0Y29uc3QgcHJvcHM6IHN0cmluZ1tdID0gW107XG5cdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiB0eXBlTGl0Lm1lbWJlcnMpIHtcblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdGNvbnN0IG9wdGlvbmFsID0gbWVtYmVyLnF1ZXN0aW9uVG9rZW4gPyAnPycgOiAnJztcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdHByb3BzLnB1c2goYCR7cHJvcE5hbWV9JHtvcHRpb25hbH06ICR7dHlwZX1gKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGB7ICR7cHJvcHMuam9pbignOyAnKX0gfWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5MaXRlcmFsVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHN0cmluZyBsaXRlcmFsIHR5cGVzIGxpa2UgJ3VzZXInLCAnYWRtaW4nLCBldGMuXG5cdFx0XHRjb25zdCB7IGxpdGVyYWwgfSA9ICh0eXBlTm9kZSBhcyB0cy5MaXRlcmFsVHlwZU5vZGUpO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChsaXRlcmFsKSkge1xuXHRcdFx0XHQvLyBSZXR1cm4gdGhlIGFjdHVhbCBsaXRlcmFsIHZhbHVlIChlLmcuLCAndXNlcicgaW5zdGVhZCBvZiBzdHJpbmcpXG5cdFx0XHRcdHJldHVybiBgJyR7bGl0ZXJhbC50ZXh0fSdgO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzTnVtZXJpY0xpdGVyYWwobGl0ZXJhbCkpIHtcblx0XHRcdFx0cmV0dXJuIGxpdGVyYWwudGV4dDtcblx0XHRcdH1cblx0XHRcdGlmIChsaXRlcmFsLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVHJ1ZUtleXdvcmQpIHtcblx0XHRcdFx0cmV0dXJuICd0cnVlJztcblx0XHRcdH1cblx0XHRcdGlmIChsaXRlcmFsLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkKSB7XG5cdFx0XHRcdHJldHVybiAnZmFsc2UnO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGxpdGVyYWwua2luZCA9PT0gdHMuU3ludGF4S2luZC5OdWxsS2V5d29yZCkge1xuXHRcdFx0XHRyZXR1cm4gJ251bGwnO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR5cGVSZWZlcmVuY2U6IHtcblx0XHRcdC8vIEhhbmRsZSB0eXBlIHJlZmVyZW5jZXMgbGlrZSBNYXA8c3RyaW5nLCBudW1iZXI+LCBQcm9wZXJ0eUluZm8sIGV0Yy5cblx0XHRcdGNvbnN0IHR5cGVSZWYgPSB0eXBlTm9kZSBhcyB0cy5UeXBlUmVmZXJlbmNlTm9kZTtcblxuXHRcdFx0Ly8gUXVhbGlmaWVkIG5hbWVzIChOYW1lc3BhY2UuVHlwZSk6IHJlc29sdmUgdGhyb3VnaCBuYW1lc3BhY2UgaW1wb3J0c1xuXHRcdFx0aWYgKHRzLmlzUXVhbGlmaWVkTmFtZSh0eXBlUmVmLnR5cGVOYW1lKSkge1xuXHRcdFx0XHRjb25zdCByZXNvbHZlZFF1YWxpZmllZCA9IHRoaXMuaW5mZXJRdWFsaWZpZWRUeXBlUmVmZXJlbmNlKHR5cGVSZWYpO1xuXHRcdFx0XHRpZiAocmVzb2x2ZWRRdWFsaWZpZWQgIT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRcdHJldHVybiByZXNvbHZlZFF1YWxpZmllZDtcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyB1bnJlc29sdmVkIHF1YWxpZmllZCByZWZlcmVuY2VzIG11c3Qgbm90IGxlYWsgYSBiYXJlIG5hbWVcblx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdH1cblxuXHRcdFx0Y29uc3QgdHlwZU5hbWUgPSB0cy5pc0lkZW50aWZpZXIodHlwZVJlZi50eXBlTmFtZSkgPyB0eXBlUmVmLnR5cGVOYW1lLnRleHQgOiAndW5rbm93bic7XG5cblx0XHRcdC8vIEltcG9ydC1hd2FyZSByZWZlcmVuY2VkLXR5cGUgcmVzb2x1dGlvbiAoRjEwKTogYSBkZWNsYXJhdGlvblxuXHRcdFx0Ly8gcmVhY2hlZCB0aHJvdWdoIHRoZSBjdXJyZW50IGZpbGUncyBvd24gaW1wb3J0cyAob3IgaXRzIGxvY2Fscyxcblx0XHRcdC8vIG9yIGEgdW5pcXVlIHByb2dyYW0td2lkZSBkZWNsYXJhdGlvbikgZXhwYW5kcyBpbmxpbmVcblx0XHRcdGNvbnN0IHNpbXBsZVJlZiA9IHRoaXMucmVzb2x2ZVNpbXBsZVR5cGVSZWZlcmVuY2UodHlwZU5hbWUsIHR5cGVSZWYudHlwZUFyZ3VtZW50cywgdHlwZVJlZik7XG5cdFx0XHRpZiAoc2ltcGxlUmVmICE9PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0cmV0dXJuIHNpbXBsZVJlZjtcblx0XHRcdH1cblxuXHRcdFx0Ly8gQnVpbGQgZ2VuZXJpYyB0eXBlIGFyZ3VtZW50c1xuXHRcdFx0Y29uc3QgdHlwZUFyZ3MgPSAodHlwZVJlZi50eXBlQXJndW1lbnRzID8/IFtdKS5tYXAoYXJnID0+IHRoaXMuaW5mZXJUeXBlKGFyZykpO1xuXHRcdFx0cmV0dXJuIGAke3R5cGVOYW1lfTwke3R5cGVBcmdzLmpvaW4oJywgJyl9PmA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5VbmlvblR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSB1bmlvbiB0eXBlcyBsaWtlICdhJyB8ICdiJyB8ICdjJ1xuXHRcdFx0Y29uc3QgdW5pb25UeXBlID0gdHlwZU5vZGUgYXMgdHMuVW5pb25UeXBlTm9kZTtcblx0XHRcdGNvbnN0IHR5cGVzID0gdW5pb25UeXBlLnR5cGVzLm1hcCh0ID0+IHRoaXMuaW5mZXJUeXBlKHQpKTtcblx0XHRcdHJldHVybiB0eXBlcy5qb2luKCcgfCAnKTtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkludGVyc2VjdGlvblR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBpbnRlcnNlY3Rpb24gdHlwZXMgbGlrZSBUeXBlQSAmIFR5cGVCXG5cdFx0XHRjb25zdCBpbnRlcnNlY3Rpb25UeXBlID0gdHlwZU5vZGUgYXMgdHMuSW50ZXJzZWN0aW9uVHlwZU5vZGU7XG5cdFx0XHRjb25zdCB0eXBlcyA9IGludGVyc2VjdGlvblR5cGUudHlwZXMubWFwKHQgPT4gdGhpcy5pbmZlclR5cGUodCkpO1xuXHRcdFx0cmV0dXJuIHR5cGVzLmpvaW4oJyAmICcpO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHVwbGVUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgdHVwbGUgdHlwZXMgbGlrZSBbc3RyaW5nLCBudW1iZXJdXG5cdFx0XHRjb25zdCB0dXBsZVR5cGUgPSB0eXBlTm9kZSBhcyB0cy5UdXBsZVR5cGVOb2RlO1xuXHRcdFx0Y29uc3QgZWxlbWVudHMgPSB0dXBsZVR5cGUuZWxlbWVudHMubWFwKGVsZW0gPT4gdGhpcy5pbmZlclR5cGUoZWxlbSBhcyB0cy5UeXBlTm9kZSkpO1xuXHRcdFx0cmV0dXJuIGBbJHtlbGVtZW50cy5qb2luKCcsICcpfV1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuT3B0aW9uYWxUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgb3B0aW9uYWwgZWxlbWVudCBpbiB0dXBsZTogc3RyaW5nP1xuXHRcdFx0Y29uc3Qgb3B0aW9uYWxUeXBlID0gdHlwZU5vZGUgYXMgdHMuT3B0aW9uYWxUeXBlTm9kZTtcblx0XHRcdHJldHVybiBgJHt0aGlzLmluZmVyVHlwZShvcHRpb25hbFR5cGUudHlwZSkgIH0/YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlJlc3RUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgcmVzdCBlbGVtZW50OiAuLi5UXG5cdFx0XHRjb25zdCByZXN0VHlwZSA9IHR5cGVOb2RlIGFzIHRzLlJlc3RUeXBlTm9kZTtcblx0XHRcdHJldHVybiBgLi4uJHsgIHRoaXMuaW5mZXJUeXBlKHJlc3RUeXBlLnR5cGUpfWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5QYXJlbnRoZXNpemVkVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHBhcmVudGhlc2l6ZWQgdHlwZXM6IChBIHwgQilcblx0XHRcdHJldHVybiB0aGlzLmluZmVyVHlwZSgodHlwZU5vZGUgYXMgdHMuUGFyZW50aGVzaXplZFR5cGVOb2RlKS50eXBlKTtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkluZGV4ZWRBY2Nlc3NUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgaW5kZXhlZCBhY2Nlc3M6IFRbS11cblx0XHRcdGNvbnN0IGluZGV4ZWQgPSB0eXBlTm9kZSBhcyB0cy5JbmRleGVkQWNjZXNzVHlwZU5vZGU7XG5cdFx0XHQvLyBGMjM6IHVud3JhcCBwYXJlbnRoZXNlcyBhcm91bmQgdGhlIG9iamVjdCDigJQgYCh0eXBlb2Zcblx0XHRcdC8vIGxpc3QpW251bWJlcl1gIG11c3QgdGFrZSB0aGUgdHlwZW9mIGJyYW5jaCBsaWtlIHRoZSBiYXJlXG5cdFx0XHQvLyBzcGVsbGluZzsgb3RoZXJ3aXNlIHRoZSBnZW5lcmFsIHBhdGggaW5mZXJzIHRoZSB1bmlvbiBhbmRcblx0XHRcdC8vIGdsdWVzIHRoZSBzdWZmaXggb250byB0aGUgTEFTVCBtZW1iZXJcblx0XHRcdC8vIChgJ2EnIHwgJ2InW251bWJlcl1gKVxuXHRcdFx0bGV0IG9iamVjdE5vZGU6IHRzLlR5cGVOb2RlID0gaW5kZXhlZC5vYmplY3RUeXBlO1xuXHRcdFx0d2hpbGUgKHRzLmlzUGFyZW50aGVzaXplZFR5cGVOb2RlKG9iamVjdE5vZGUpKSB7XG5cdFx0XHRcdG9iamVjdE5vZGUgPSBvYmplY3ROb2RlLnR5cGU7XG5cdFx0XHR9XG5cdFx0XHQvLyBgdHlwZW9mIGNvbnN0QXJyYXlbS11gIOKAlCBlbGVtZW50IHR5cGUgb2YgYSB0cmFja2VkIGNvbnN0IGFycmF5OlxuXHRcdFx0Ly8gZW1pdCB0aGUgZWxlbWVudCBsaXRlcmFsIHVuaW9uIGRpcmVjdGx5IChhc3NlbWJsaW5nXG5cdFx0XHQvLyBgdW5pb25bS11gIHRleHQgd291bGQgbWlzcmVhZCBwcmVjZWRlbmNlLCBhbmQgd2hlbiB0aGUgY29uc3Rcblx0XHRcdC8vIGlzIG5vdCBzdGF0aWNhbGx5IHZpc2libGUgdGhlIGhvbmVzdCBhbnN3ZXIgaXMgYHVua25vd25gLFxuXHRcdFx0Ly8gbmV2ZXIgYSBiYXJlIGB0eXBlb2YgbmFtZWAgcXVlcnkpXG5cdFx0XHRpZiAodHMuaXNUeXBlUXVlcnlOb2RlKG9iamVjdE5vZGUpICYmIHRzLmlzSWRlbnRpZmllcihvYmplY3ROb2RlLmV4cHJOYW1lKSkge1xuXHRcdFx0XHRjb25zdCBxdWVyeU5hbWUgPSBvYmplY3ROb2RlLmV4cHJOYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IGFycmF5TGl0ZXJhbCA9IHRoaXMuZmluZFJlZmVyZW5jZWRDb25zdEFycmF5KHF1ZXJ5TmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdFx0Y29uc3QgbGl0ZXJhbHMgPSBhcnJheUxpdGVyYWwgPyB0aGlzLmxpdGVyYWxUeXBlc09mQXJyYXkoYXJyYXlMaXRlcmFsKSA6IHVuZGVmaW5lZDtcblx0XHRcdFx0aWYgKCFsaXRlcmFscykge1xuXHRcdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKHRzLmlzTGl0ZXJhbFR5cGVOb2RlKGluZGV4ZWQuaW5kZXhUeXBlKSAmJiB0cy5pc051bWVyaWNMaXRlcmFsKGluZGV4ZWQuaW5kZXhUeXBlLmxpdGVyYWwpKSB7XG5cdFx0XHRcdFx0Y29uc3QgZWxlbWVudEluZGV4ID0gcGFyc2VJbnQoaW5kZXhlZC5pbmRleFR5cGUubGl0ZXJhbC50ZXh0LCAxMCk7XG5cdFx0XHRcdFx0Y29uc3QgZWxlbWVudCA9IGxpdGVyYWxzWyBlbGVtZW50SW5kZXggXTtcblx0XHRcdFx0XHRjb25zdCBlbGVtZW50UmVzdWx0ID0gZWxlbWVudCA9PT0gdW5kZWZpbmVkID8gJ3Vua25vd24nIDogZWxlbWVudDtcblx0XHRcdFx0XHRyZXR1cm4gZWxlbWVudFJlc3VsdDtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCB1bmlvblJlc3VsdCA9IGxpdGVyYWxzLmpvaW4oJyB8ICcpO1xuXHRcdFx0XHRyZXR1cm4gdW5pb25SZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRsZXQgb2JqZWN0VHlwZSA9IHRoaXMuaW5mZXJUeXBlKG9iamVjdE5vZGUpO1xuXHRcdFx0Y29uc3QgaW5kZXhUeXBlID0gdGhpcy5pbmZlclR5cGUoaW5kZXhlZC5pbmRleFR5cGUpO1xuXHRcdFx0Ly8gSWYgb2JqZWN0VHlwZSBpcyAnb2JqZWN0JywgdHJ5IHRvIHJlc29sdmUgdGhlIHVuZGVybHlpbmcgcmVmZXJlbmNlZCB0eXBlXG5cdFx0XHRpZiAob2JqZWN0VHlwZSA9PT0gJ29iamVjdCcgJiYgdHMuaXNUeXBlUmVmZXJlbmNlTm9kZShvYmplY3ROb2RlKSkge1xuXHRcdFx0XHRjb25zdCByZWZOYW1lID0gdHMuaXNJZGVudGlmaWVyKG9iamVjdE5vZGUudHlwZU5hbWUpID8gb2JqZWN0Tm9kZS50eXBlTmFtZS50ZXh0IDogJyc7XG5cdFx0XHRcdGlmIChyZWZOYW1lKSB7XG5cdFx0XHRcdFx0Y29uc3QgZGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24ocmVmTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdFx0XHRpZiAoZGVjbCkge1xuXHRcdFx0XHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oZGVjbCk7XG5cdFx0XHRcdFx0XHRpZiAoZXhwYW5kZWQpIHtcblx0XHRcdFx0XHRcdFx0b2JqZWN0VHlwZSA9IGV4cGFuZGVkO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gSW52YXJpYW50OiBhbiBpbmRleCBzdWZmaXggbXVzdCBORVZFUiBiZSBnbHVlZCBvbnRvIGFuXG5cdFx0XHQvLyB1bnJlc29sdmVkL2ZhbGxiYWNrIHRhcmdldCDigJQgYHVua25vd25bbnVtYmVyXWAgLyBgb2JqZWN0W0tdYFxuXHRcdFx0Ly8gYXJlIGludmFsaWQgVHlwZVNjcmlwdCBpbiB0aGUgZ2VuZXJhdGVkIGZpbGUgKGhhcmQgY29tcGlsZVxuXHRcdFx0Ly8gYnJlYWssIEYxNykuIFdoZW4gZWl0aGVyIHNpZGUgZGlkIG5vdCByZXNvbHZlLCB0aGUgV0hPTEVcblx0XHRcdC8vIGluZGV4ZWQgYWNjZXNzIGRlZ3JhZGVzIHRvIGB1bmtub3duYC5cblx0XHRcdGNvbnN0IHRhcmdldFVucmVzb2x2ZWQgPSBvYmplY3RUeXBlID09PSAndW5rbm93bicgfHwgb2JqZWN0VHlwZSA9PT0gJ29iamVjdCc7XG5cdFx0XHRjb25zdCBpbmRleFVucmVzb2x2ZWQgPSBpbmRleFR5cGUgPT09ICd1bmtub3duJztcblx0XHRcdGlmICh0YXJnZXRVbnJlc29sdmVkIHx8IGluZGV4VW5yZXNvbHZlZCkge1xuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGAke29iamVjdFR5cGV9WyR7aW5kZXhUeXBlfV1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZU9wZXJhdG9yOiB7XG5cdFx0XHQvLyBIYW5kbGUga2V5b2YsIHJlYWRvbmx5LCB1bmlxdWUgb3BlcmF0b3JzXG5cdFx0XHRjb25zdCB0eXBlT3AgPSB0eXBlTm9kZSBhcyB0cy5UeXBlT3BlcmF0b3JOb2RlO1xuXHRcdFx0Y29uc3Qgb3BlcmF0b3IgPSB0cy5TeW50YXhLaW5kWyB0eXBlT3Aub3BlcmF0b3IgXTtcblx0XHRcdHJldHVybiBgJHtvcGVyYXRvcn0gJHt0aGlzLmluZmVyVHlwZSh0eXBlT3AudHlwZSl9YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR5cGVRdWVyeToge1xuXHRcdFx0Ly8gYHR5cGVvZiB4YCBhcyBhIEZJRUxEIFRZUEU6IHRoZSBnZW5lcmF0ZWQgZmlsZSBoYXMgbm8gaW1wb3J0cyxcblx0XHRcdC8vIHNvIGEgYmFyZSBgdHlwZW9mIHhgIHdvdWxkIGJlIGFuIHVucmVzb2x2YWJsZSBuYW1lIGRvd25zdHJlYW0uXG5cdFx0XHQvLyBXaGVuIHggaXMgYSB0cmFja2VkIGNvbnN0IGFycmF5LCBlbWl0IGl0cyBlbGVtZW50IGxpdGVyYWxcblx0XHRcdC8vIHVuaW9uOyBvdGhlcndpc2UgZGVncmFkZSB0byBgdW5rbm93bmAuIChJbnN0YW5jZVR5cGU8dHlwZW9mIFg+XG5cdFx0XHQvLyBncmFwaCB0eXBlcyBhcmUgaGFuZGxlZCBpbiByZXNvbHZlU2ltcGxlVHlwZVJlZmVyZW5jZSBiZWZvcmVcblx0XHRcdC8vIGluZmVyVHlwZSBydW5zLilcblx0XHRcdGNvbnN0IHR5cGVRdWVyeSA9IHR5cGVOb2RlIGFzIHRzLlR5cGVRdWVyeU5vZGU7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKHR5cGVRdWVyeS5leHByTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgdW5pb24gPSB0aGlzLnR5cGVPZkNvbnN0QXJyYXlVbmlvbih0eXBlUXVlcnkuZXhwck5hbWUudGV4dCwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdFx0aWYgKHVuaW9uKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHVuaW9uO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRkZWZhdWx0OlxuXHRcdFx0Ly8gRm9yIGNvbXBsZXggdHlwZXMsIHJldHVybiB0aGUgdGV4dCByZXByZXNlbnRhdGlvblxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHQqIEluZmVyIHJldHVybiB0eXBlIGZyb20gYSBtZXRob2QgZGVjbGFyYXRpb25cblx0XHQqIFVzZXMgZXhwbGljaXQgcmV0dXJuIHR5cGUgYW5ub3RhdGlvbiBvciBpbmZlcnMgZnJvbSByZXR1cm4gc3RhdGVtZW50c1xuXHRcdCovXG5cdHByaXZhdGUgaW5mZXJSZXR1cm5UeXBlIChtZXRob2Q6IHRzLk1ldGhvZERlY2xhcmF0aW9uLCBjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+KTogc3RyaW5nIHtcblx0XHQvLyBJZiBtZXRob2QgaGFzIGV4cGxpY2l0IHJldHVybiB0eXBlIGFubm90YXRpb24sIHVzZSBpdFxuXHRcdGlmIChtZXRob2QudHlwZSkge1xuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJUeXBlKG1ldGhvZC50eXBlKTtcblx0XHR9XG5cblx0XHQvLyBPdGhlcndpc2UsIHRyeSB0byBpbmZlciBmcm9tIHJldHVybiBzdGF0ZW1lbnRzIGluIHRoZSBtZXRob2QgYm9keVxuXHRcdGlmIChtZXRob2QuYm9keSkge1xuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJSZXR1cm5UeXBlRnJvbUJvZHkobWV0aG9kLmJvZHksIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0fVxuXG5cdFx0cmV0dXJuICd1bmtub3duJztcblx0fVxuXG5cdC8qKlxuXHRcdCogSW5mZXIgcmV0dXJuIHR5cGUgYnkgYW5hbHl6aW5nIHJldHVybiBzdGF0ZW1lbnRzIGluIHRoZSBtZXRob2QgYm9keVxuXHRcdCovXG5cdHByaXZhdGUgaW5mZXJSZXR1cm5UeXBlRnJvbUJvZHkgKGJvZHk6IHRzLkJsb2NrLCBjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+KTogc3RyaW5nIHtcblx0XHRjb25zdCByZXR1cm5UeXBlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXG5cdFx0Y29uc3QgdmlzaXQgPSAobm9kZTogdHMuTm9kZSk6IHZvaWQgPT4ge1xuXHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIobm9kZS5leHByZXNzaW9uLCB1bmRlZmluZWQsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdGlmICh0eXBlICE9PSAndW5rbm93bicpIHtcblx0XHRcdFx0XHRyZXR1cm5UeXBlcy5hZGQodHlwZSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCB2aXNpdCk7XG5cdFx0fTtcblxuXHRcdHZpc2l0KGJvZHkpO1xuXG5cdFx0aWYgKHJldHVyblR5cGVzLnNpemUgPT09IDApIHtcblx0XHRcdHJldHVybiAndm9pZCc7XG5cdFx0fVxuXHRcdGlmIChyZXR1cm5UeXBlcy5zaXplID09PSAxKSB7XG5cdFx0XHRyZXR1cm4gQXJyYXkuZnJvbShyZXR1cm5UeXBlcylbIDAgXTtcblx0XHR9XG5cdFx0cmV0dXJuIEFycmF5LmZyb20ocmV0dXJuVHlwZXMpLmpvaW4oJyB8ICcpO1xuXHR9XG5cblx0LyoqXG5cdCAqIEluZmVyIHR5cGUgZnJvbSBpbml0aWFsaXplclxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIgKFxuXHRcdGluaXRpYWxpemVyOiB0cy5FeHByZXNzaW9uLFxuXHRcdGRhdGFUeXBlTWFwPzogTWFwPHN0cmluZywgc3RyaW5nPixcblx0XHRjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+XG5cdCk6IHN0cmluZyB7XG5cdFx0c3dpdGNoIChpbml0aWFsaXplci5raW5kKSB7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlN0cmluZ0xpdGVyYWw6XG5cdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bWVyaWNMaXRlcmFsOlxuXHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZDpcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bGwnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5VbmRlZmluZWRLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICd1bmRlZmluZWQnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5BcnJheUxpdGVyYWxFeHByZXNzaW9uOlxuXHRcdFx0cmV0dXJuICdBcnJheTx1bmtub3duPic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk9iamVjdExpdGVyYWxFeHByZXNzaW9uOlxuXHRcdFx0cmV0dXJuICdvYmplY3QnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OZXdFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgbmV3IERhdGUoKSwgbmV3IE1hcCgpLCBldGMuXG5cdFx0XHRjb25zdCBuZXdFeHByID0gaW5pdGlhbGl6ZXIgYXMgdHMuTmV3RXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIobmV3RXhwci5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBjb25zdHJ1Y3RlZE5hbWUgPSBuZXdFeHByLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdFx0Ly8gRXhwbGljaXQgdHlwZSBhcmd1bWVudHMgc3Vydml2ZTogbmV3IE1hcDxzdHJpbmcsIG9iamVjdD4oKVxuXHRcdFx0XHQvLyBlbWl0cyBNYXA8c3RyaW5nLCBvYmplY3Q+IOKAlCBkcm9wcGluZyB0aGVtIHByb2R1Y2VkIGEgYmFyZVxuXHRcdFx0XHQvLyBnZW5lcmljLCB3aGljaCBpcyBpbnZhbGlkIFRTIGluIHRoZSBnZW5lcmF0ZWQgZmlsZSAoVFMyMzE0KVxuXHRcdFx0XHRpZiAobmV3RXhwci50eXBlQXJndW1lbnRzICYmIG5ld0V4cHIudHlwZUFyZ3VtZW50cy5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdFx0Y29uc3QgYXJnVHlwZXMgPSBuZXdFeHByLnR5cGVBcmd1bWVudHMubWFwKGFyZyA9PiB0aGlzLmluZmVyVHlwZShhcmcpKTtcblx0XHRcdFx0XHRyZXR1cm4gYCR7Y29uc3RydWN0ZWROYW1lfTwke2FyZ1R5cGVzLmpvaW4oJywgJyl9PmA7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gTm8gdHlwZSBhcmd1bWVudHM6IGEga25vd24gZ2VuZXJpYyBnbG9iYWwgc3RpbGwgbmVlZHMgaXRzXG5cdFx0XHRcdC8vIHBhcmFtZXRlciBsaXN0IOKAlCBmaWxsIGl0IHdpdGggdW5rbm93biAoTWFwPHVua25vd24sIHVua25vd24+KVxuXHRcdFx0XHRjb25zdCBkZWZhdWx0ZWRHZW5lcmljID0gR0VORVJJQ19HTE9CQUxfREVGQVVMVF9BUkdTLmdldChjb25zdHJ1Y3RlZE5hbWUpO1xuXHRcdFx0XHRpZiAoZGVmYXVsdGVkR2VuZXJpYykge1xuXHRcdFx0XHRcdHJldHVybiBkZWZhdWx0ZWRHZW5lcmljO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiBjb25zdHJ1Y3RlZE5hbWU7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ29iamVjdCc7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5CaW5hcnlFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgYXJpdGhtZXRpYyBvcGVyYXRpb25zOiBhICogYiwgYSArIGIsIGEgLSBiLCBhIC8gYlxuXHRcdFx0Y29uc3QgYmluYXJ5RXhwciA9IGluaXRpYWxpemVyIGFzIHRzLkJpbmFyeUV4cHJlc3Npb247XG5cdFx0XHRjb25zdCBsZWZ0VHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKGJpbmFyeUV4cHIubGVmdCwgZGF0YVR5cGVNYXAsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRjb25zdCByaWdodFR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihiaW5hcnlFeHByLnJpZ2h0LCBkYXRhVHlwZU1hcCwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0XG5cdFx0XHQvLyBDaGVjayBpZiBpdCdzIGFuIGFyaXRobWV0aWMgb3BlcmF0b3Jcblx0XHRcdGNvbnN0IG9wZXJhdG9yID0gYmluYXJ5RXhwci5vcGVyYXRvclRva2VuLmtpbmQ7XG5cdFx0XHRpZiAob3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuQXN0ZXJpc2tUb2tlbiB8fFxuXHRcdFx0XHQgICAgb3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuU2xhc2hUb2tlbiB8fFxuXHRcdFx0XHQgICAgb3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuTWludXNUb2tlbiB8fFxuXHRcdFx0XHQgICAgb3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuUGVyY2VudFRva2VuKSB7XG5cdFx0XHRcdC8vIEFyaXRobWV0aWMgb3BlcmF0aW9ucyBvbiBudW1iZXJzIHByb2R1Y2UgbnVtYmVyc1xuXHRcdFx0XHRpZiAoKGxlZnRUeXBlID09PSAnbnVtYmVyJyB8fCBsZWZ0VHlwZSA9PT0gJ3Vua25vd24nKSAmJlxuXHRcdFx0XHRcdCAgICAocmlnaHRUeXBlID09PSAnbnVtYmVyJyB8fCByaWdodFR5cGUgPT09ICd1bmtub3duJykpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGlmIChvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5QbHVzVG9rZW4pIHtcblx0XHRcdFx0Ly8gUGx1cyBjYW4gYmUgYWRkaXRpb24gb3Igc3RyaW5nIGNvbmNhdGVuYXRpb25cblx0XHRcdFx0aWYgKGxlZnRUeXBlID09PSAnc3RyaW5nJyB8fCByaWdodFR5cGUgPT09ICdzdHJpbmcnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChsZWZ0VHlwZSA9PT0gJ251bWJlcicgJiYgcmlnaHRUeXBlID09PSAnbnVtYmVyJykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gSGFuZGxlIHByb3BlcnR5IGFjY2VzcyBsaWtlIGRhdGEudmFsdWUsIGRhdGEuaWRcblx0XHRcdGlmIChkYXRhVHlwZU1hcCkge1xuXHRcdFx0XHRjb25zdCBhY2Nlc3NDaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihpbml0aWFsaXplcik7XG5cdFx0XHRcdGlmIChhY2Nlc3NDaGFpbikge1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSBkYXRhVHlwZU1hcC5nZXQoYWNjZXNzQ2hhaW4pO1xuXHRcdFx0XHRcdGlmICh0eXBlKSB7XG5cdFx0XHRcdFx0XHRyZXR1cm4gdHlwZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIEhhbmRsZSB0aGlzLm1hcC5zaXplIHBhdHRlcm4gKE1hcC5zaXplIHJldHVybnMgbnVtYmVyKVxuXHRcdFx0Y29uc3QgcHJvcEFjY2VzcyA9IGluaXRpYWxpemVyIGFzIHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihwcm9wQWNjZXNzLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IG91dGVyUHJvcCA9IHByb3BBY2Nlc3MuZXhwcmVzc2lvbjtcblx0XHRcdFx0Ly8gQ2hlY2sgZm9yIHRoaXMubWFwIHBhdHRlcm5cblx0XHRcdFx0bGV0IGlubmVyTmFtZSA9ICcnO1xuXHRcdFx0XHRpZiAob3V0ZXJQcm9wLmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdGlubmVyTmFtZSA9ICd0aGlzJztcblx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc0lkZW50aWZpZXIob3V0ZXJQcm9wLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0aW5uZXJOYW1lID0gb3V0ZXJQcm9wLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBtYXBQcm9wID0gb3V0ZXJQcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgZmluYWxQcm9wID0gcHJvcEFjY2Vzcy5uYW1lLnRleHQ7XG5cdFx0XHRcdC8vIHRoaXMubWFwLnNpemUgLT4gbnVtYmVyXG5cdFx0XHRcdGlmIChpbm5lck5hbWUgPT09ICd0aGlzJyAmJiBtYXBQcm9wID09PSAnbWFwJyAmJiBmaW5hbFByb3AgPT09ICdzaXplJykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLklkZW50aWZpZXI6IHtcblx0XHRcdC8vIEhhbmRsZSBpZGVudGlmaWVyIHJlZmVyZW5jZXMgaWYgaW4gZGF0YVR5cGVNYXBcblx0XHRcdGlmIChkYXRhVHlwZU1hcCkge1xuXHRcdFx0XHRjb25zdCBuYW1lID0gKGluaXRpYWxpemVyIGFzIHRzLklkZW50aWZpZXIpLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHR5cGUgPSBkYXRhVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0XHRcdGlmICh0eXBlKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHR5cGU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5FbGVtZW50QWNjZXNzRXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gRjIyOiB2YWx1ZS1sZXZlbCBlbGVtZW50IGFjY2VzcyBvdmVyIGEgY29uc3QtYXNzZXJ0ZWRcblx0XHRcdC8vIGxpdGVyYWwgYXJyYXkg4oCUIGAoPGNvbnN0PlvigKZdKVswXWAsIGAoW+KApl0gYXMgY29uc3QpWzFdYCwgb3Jcblx0XHRcdC8vIGEgdHJhY2tlZCBtb2R1bGUgY29uc3QgKGBjb25zdCB4ID0gPGNvbnN0PlvigKZdYDsgYHhbMF1gKSDigJRcblx0XHRcdC8vIGluZmVycyB0aGUgZWxlbWVudCdzIGxpdGVyYWwgdHlwZSwgdGhlIHZhbHVlLWxldmVsIHR3aW4gb2Zcblx0XHRcdC8vIHRoZSB0eXBlb2YtcGF0aCB1bmlvbi4gTm9uLW51bWVyaWMgaW5kZXhlcywgbm9uLWxpdGVyYWxcblx0XHRcdC8vIGVsZW1lbnRzLCBhbmQgZ2VuZXJhbCBhc3NlcnRpb25zIHN0YXkgYHVua25vd25gLlxuXHRcdFx0Y29uc3QgZWxlbWVudEFjY2VzcyA9IGluaXRpYWxpemVyIGFzIHRzLkVsZW1lbnRBY2Nlc3NFeHByZXNzaW9uO1xuXHRcdFx0Y29uc3QgYXJndW1lbnQgPSBlbGVtZW50QWNjZXNzLmFyZ3VtZW50RXhwcmVzc2lvbjtcblx0XHRcdGlmICghYXJndW1lbnQgfHwgIXRzLmlzTnVtZXJpY0xpdGVyYWwoYXJndW1lbnQpKSB7XG5cdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBhcnJheUxpdGVyYWwgPSB0aGlzLmNvbnN0QXJyYXlMaXRlcmFsT2YoZWxlbWVudEFjY2Vzcy5leHByZXNzaW9uKTtcblx0XHRcdGlmICghYXJyYXlMaXRlcmFsKSB7XG5cdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBlbGVtZW50ID0gYXJyYXlMaXRlcmFsLmVsZW1lbnRzWyBwYXJzZUludChhcmd1bWVudC50ZXh0LCAxMCkgXTtcblx0XHRcdGlmICghZWxlbWVudCB8fCB0cy5pc1NwcmVhZEVsZW1lbnQoZWxlbWVudCkpIHtcblx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdH1cblx0XHRcdGNvbnN0IGxpdGVyYWwgPSB0aGlzLmxpdGVyYWxUeXBlT2ZFeHByZXNzaW9uKGVsZW1lbnQpO1xuXHRcdFx0Y29uc3QgZWxlbWVudFJlc3VsdCA9IGxpdGVyYWwgPz8gJ3Vua25vd24nO1xuXHRcdFx0cmV0dXJuIGVsZW1lbnRSZXN1bHQ7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5DYWxsRXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gSGFuZGxlIGZ1bmN0aW9uIGNhbGxzIGxpa2UgRGF0ZS5ub3coKSwgcGFyc2VJbnQoKSwgZXRjLlxuXHRcdFx0Y29uc3QgY2FsbEV4cHIgPSBpbml0aWFsaXplciBhcyB0cy5DYWxsRXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsRXhwci5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBtZXRob2ROYW1lID0gY2FsbEV4cHIuZXhwcmVzc2lvbi5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IG9iak5hbWUgPSB0cy5pc0lkZW50aWZpZXIoY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uKVxuXHRcdFx0XHRcdD8gY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uLnRleHRcblx0XHRcdFx0XHQ6ICcnO1xuXHRcdFx0XHRcdFxuXHRcdFx0XHQvLyBEYXRlLm5vdygpIC0+IG51bWJlclxuXHRcdFx0XHRpZiAob2JqTmFtZSA9PT0gJ0RhdGUnICYmIG1ldGhvZE5hbWUgPT09ICdub3cnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIFN0cmluZyBtZXRob2RzIHRoYXQgcmV0dXJuIHN0cmluZ1xuXHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3RvU3RyaW5nJyB8fCBtZXRob2ROYW1lID09PSAndmFsdWVPZicpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gSGFuZGxlIE1hcCBwcm9wZXJ0eSBhY2Nlc3Mgb24gY2xhc3MgaW5zdGFuY2VzICh0aGlzLm1hcC4qKVxuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdGNvbnN0IG91dGVyUHJvcCA9IGNhbGxFeHByLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdFx0XHQvLyBIYW5kbGUgYm90aCAndGhpcycga2V5d29yZCBhbmQgaWRlbnRpZmllciBwYXR0ZXJuc1xuXHRcdFx0XHRcdGxldCBpbm5lck5hbWUgPSAnJztcblx0XHRcdFx0XHRpZiAob3V0ZXJQcm9wLmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdFx0aW5uZXJOYW1lID0gJ3RoaXMnO1xuXHRcdFx0XHRcdH0gZWxzZSBpZiAodHMuaXNJZGVudGlmaWVyKG91dGVyUHJvcC5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdFx0aW5uZXJOYW1lID0gb3V0ZXJQcm9wLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Y29uc3QgbWFwUHJvcCA9IG91dGVyUHJvcC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Ly8gdGhpcy5tYXAuWCgpIHBhdHRlcm5zXG5cdFx0XHRcdFx0aWYgKGlubmVyTmFtZSA9PT0gJ3RoaXMnICYmIG1hcFByb3AgPT09ICdtYXAnKSB7XG5cdFx0XHRcdFx0XHQvLyBUcnkgdG8gZ2V0IHRoZSBNYXAncyB2YWx1ZSB0eXBlIGZyb20gY2xhc3MgcHJvcGVydGllc1xuXHRcdFx0XHRcdFx0bGV0IG1hcFZhbHVlVHlwZSA9ICd1bmtub3duJztcblx0XHRcdFx0XHRcdGlmIChjbGFzc1Byb3BlcnR5VHlwZXMpIHtcblx0XHRcdFx0XHRcdFx0Y29uc3QgbWFwVHlwZSA9IGNsYXNzUHJvcGVydHlUeXBlcy5nZXQoJ21hcCcpO1xuXHRcdFx0XHRcdFx0XHRpZiAobWFwVHlwZSAmJiBtYXBUeXBlLnN0YXJ0c1dpdGgoJ01hcDwnKSkge1xuXHRcdFx0XHRcdFx0XHRcdC8vIFBhcnNlIE1hcDxLLCBWPiB0byBnZXQgVlxuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IG1hdGNoID0gbWFwVHlwZS5tYXRjaCgvTWFwPFteLF0rLFxccyooLispPiQvKTtcblx0XHRcdFx0XHRcdFx0XHRpZiAobWF0Y2gpIHtcblx0XHRcdFx0XHRcdFx0XHRcdFsgLCBtYXBWYWx1ZVR5cGUgXSA9IG1hdGNoO1xuXHRcdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdoYXMnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdzZXQnKSByZXR1cm4gJ3RoaXMnO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdnZXQnKSByZXR1cm4gbWFwVmFsdWVUeXBlO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdkZWxldGUnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdjbGVhcicpIHJldHVybiAndm9pZCc7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3ZhbHVlcycpIHJldHVybiBgSXRlcmFibGVJdGVyYXRvcjwke21hcFZhbHVlVHlwZX0+YDtcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAna2V5cycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjxzdHJpbmc+Jztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZW50cmllcycpIHJldHVybiBgSXRlcmFibGVJdGVyYXRvcjxbc3RyaW5nLCAke21hcFZhbHVlVHlwZX1dPmA7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIERpcmVjdCBtYXAuWCgpIGNhbGxzXG5cdFx0XHRcdGlmIChvYmpOYW1lID09PSAnbWFwJyB8fCBvYmpOYW1lID09PSAnb2JqJykge1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnaGFzJykgcmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3NldCcpIHJldHVybiAndGhpcyc7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdnZXQnKSByZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZGVsZXRlJykgcmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2NsZWFyJykgcmV0dXJuICd2b2lkJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3ZhbHVlcycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjx1bmtub3duPic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdrZXlzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPHN0cmluZz4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZW50cmllcycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjxbc3RyaW5nLCB1bmtub3duXT4nO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBwYXJzZUludCwgcGFyc2VGbG9hdCAtPiBudW1iZXJcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY2FsbEV4cHIuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y29uc3QgZm5OYW1lID0gY2FsbEV4cHIuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHRpZiAoZm5OYW1lID09PSAncGFyc2VJbnQnIHx8IGZuTmFtZSA9PT0gJ3BhcnNlRmxvYXQnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdTdHJpbmcnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdOdW1iZXInKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdCb29sZWFuJykge1xuXHRcdFx0XHRcdHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UZW1wbGF0ZUV4cHJlc3Npb246XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk5vU3Vic3RpdHV0aW9uVGVtcGxhdGVMaXRlcmFsOiB7XG5cdFx0XHQvLyBUZW1wbGF0ZSBsaXRlcmFscyBsaWtlIGAke2Jhc2VWYWx1ZX0tJHtleHRyYX1gIGFsd2F5cyBwcm9kdWNlIHN0cmluZ3Ncblx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHR9XG5cdFx0ZGVmYXVsdDpcblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHR9XG5cdFxuXHQvKipcblx0XHRcdCogQ29sbGVjdCB1c2FnZSBpbmZvcm1hdGlvbiBmb3IgdHlwZSByZWZlcmVuY2VzXG5cdFx0XHQqL1xuXHRwcml2YXRlIGNvbGxlY3RVc2FnZSAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGZvciBuZXcgVHlwZSgpIGluc3RhbnRpYXRpb25cblx0XHRpZiAodHMuaXNOZXdFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0bGV0IHR5cGVOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obm9kZS5leHByZXNzaW9uKSkge1xuXHRcdFx0XHR0eXBlTmFtZSA9IHRoaXMucmVzb2x2ZVR5cGVQYXRoKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHR0eXBlTmFtZSA9IHRoaXMuZ2V0VHlwZU5hbWVGcm9tRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHR5cGVOYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0dGhpcy5hZGRVc2FnZSh0eXBlTmFtZSwge1xuXHRcdFx0XHRcdGxvY2F0aW9uICAgICAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdGtpbmQgICAgICAgICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRjb2RlICAgICAgICAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHQvLyBDb25zdHJ1Y3RvciBleHByZXNzaW9uIHRleHQgKCdUaGluZycsICd1c2VyLkFkbWluRW50aXR5Jyxcblx0XHRcdFx0XHQvLyBhIGxvb2t1cCBhbGlhcykg4oCUIENyZWF0aW9uQW5jaG9yLmNvbnN0cnVjdG9yVGV4dCAoUGhhc2UgMylcblx0XHRcdFx0XHRjb25zdHJ1Y3RvclRleHQgOiBub2RlLmV4cHJlc3Npb24uZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHR9KTtcblx0XHRcdFx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudCBmcm9tIG5ldyBUeXBlKCkgZm9yIGZsb3cgYW5hbHlzaXNcblx0XHRcdFx0dGhpcy50cmFja05ld0Fzc2lnbm1lbnQobm9kZSwgdHlwZU5hbWUpO1xuXHRcdFx0XHQvLyBBbHNvIHJlY29yZCBhcyBmbG93IGV2ZW50XG5cdFx0XHRcdHRoaXMuYWRkRmxvdyh0eXBlTmFtZSwge1xuXHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0a2luZCAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRjb250ZXh0ICA6ICduZXcgZXhwcmVzc2lvbicsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0Ly8gQ2hlY2sgZm9yIHByb3BlcnR5IGFjY2VzcyBvbiBpbnN0YW5jZXMgKHVzZXIuQWRtaW5UeXBlKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRcdC8vIGluc3RhbmNlLmNsb25lIOKAlCB0aGUgUFJPUEVSVFkgZm9ybSAoY29yZSB0eXBlcyBpdFxuXHRcdFx0Ly8gYHJlYWRvbmx5IGNsb25lOiB0aGlzYCk6IHRoZSByZXN1bHQgdmFyaWFibGUgYmluZHMgdG8gdGhlXG5cdFx0XHQvLyBzb3VyY2UgaW5zdGFuY2UncyB0eXBlLCBzYW1lIGFzIHRoZSBmb3JrKCkvY2xvbmUoKSBjYWxsXG5cdFx0XHQvLyBmb3JtcyAoYXdhaXQtdHJhbnNwYXJlbnQpLiBUaGUgY2FsbCBmb3JtJ3MgcmVjb3JkaW5nIGhhcHBlbnNcblx0XHRcdC8vIGluIHRoZSBDYWxsRXhwcmVzc2lvbiBicmFuY2g7IHRoZSBwcm9wZXJ0eSBicmFuY2ggc2tpcHMgaXRcblx0XHRcdC8vIHRvIGF2b2lkIGEgZHVwbGljYXRlIGVudHJ5IGF0IHRoZSBzYW1lIHNpdGVcblx0XHRcdGlmIChwcm9wTmFtZSA9PT0gJ2Nsb25lJyAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBjbG9uZWRQYXRoID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQobm9kZS5leHByZXNzaW9uLnRleHQpO1xuXHRcdFx0XHRjb25zdCBpc0NhbGxGb3JtID0gdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlLnBhcmVudCkgJiYgbm9kZS5wYXJlbnQuZXhwcmVzc2lvbiA9PT0gbm9kZTtcblx0XHRcdFx0aWYgKGNsb25lZFBhdGgpIHtcblx0XHRcdFx0XHRpZiAoIWlzQ2FsbEZvcm0pIHtcblx0XHRcdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHRcdFx0KTtcblx0XHRcdFx0XHRcdHRoaXMuYWRkVXNhZ2UoY2xvbmVkUGF0aCwge1xuXHRcdFx0XHRcdFx0XHRsb2NhdGlvbiAgICAgICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRcdFx0a2luZCAgICAgICAgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0XHRcdFx0XHRjb2RlICAgICAgICAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRcdFx0Y29uc3RydWN0b3JUZXh0IDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0dGhpcy5iaW5kUmVzdWx0VmFyaWFibGUobm9kZSwgY2xvbmVkUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIENoZWNrIGlmIHRoaXMgbG9va3MgbGlrZSBhIHR5cGUgYWNjZXNzIHBhdHRlcm5cblx0XHRcdGlmIChwcm9wTmFtZSAmJiB0aGlzLmlzTGlrZWx5VHlwZU5hbWUocHJvcE5hbWUpKSB7XG5cdFx0XHRcdC8vIG5ldyB4LlN1YijigKYpOiB0aGUgTmV3RXhwcmVzc2lvbiBicmFuY2ggYWxyZWFkeSByZWNvcmRlZFxuXHRcdFx0XHQvLyB0aGUgc2l0ZSBhcyBhbiBpbnN0YW50aWF0aW9uLCBzbyBhIHByb3BlcnR5QWNjZXNzIHJlY29yZFxuXHRcdFx0XHQvLyB3b3VsZCBkdXBsaWNhdGUgaXQg4oCUIG9uZSByZWNvcmQgcGVyIHNpdGUsIHRoZSBzYW1lIGxhdyBhc1xuXHRcdFx0XHQvLyB0aGUgY2xvbmUgZ3VhcmQgYWJvdmUuIChBIHdob2xlLWNhbGxlZS1wYXJlbnRoZXNpemVkXG5cdFx0XHRcdC8vIG5ldyAoeC5TdWIpKCkgbmV2ZXIgbWF0Y2hlcyBoZXJlOiB0aGUgYWNjZXNzJ3MgcGFyZW50IGlzXG5cdFx0XHRcdC8vIHRoZSBQYXJlbnRoZXNpemVkRXhwcmVzc2lvbiwgYW5kIHRoZSBpbnN0YW50aWF0aW9uIGJyYW5jaFxuXHRcdFx0XHQvLyBjYW5ub3QgcmVzb2x2ZSB0aGF0IGNhbGxlZSDigJQgdGhpcyBhY2Nlc3Mgc3RheXMgdGhlIHNpdGUnc1xuXHRcdFx0XHQvLyBvbmx5IHJlY29yZC4pXG5cdFx0XHRcdGNvbnN0IGlzTmV3Q2FsbGVlID0gdHMuaXNOZXdFeHByZXNzaW9uKG5vZGUucGFyZW50KSAmJiBub2RlLnBhcmVudC5leHByZXNzaW9uID09PSBub2RlO1xuXHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdCk7XG5cdFx0XHRcdFx0Ly8gVHJ5IHRvIHJlc29sdmUgZnVsbCBwYXRoXG5cdFx0XHRcdGNvbnN0IGZ1bGxQYXRoID0gdGhpcy5yZXNvbHZlVHlwZVBhdGgobm9kZSk7XG5cdFx0XHRcdGlmIChmdWxsUGF0aCAmJiAhaXNOZXdDYWxsZWUpIHtcblx0XHRcdFx0XHR0aGlzLmFkZFVzYWdlKGZ1bGxQYXRoLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdFx0a2luZCAgICAgOiAncHJvcGVydHlBY2Nlc3MnLFxuXHRcdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0Ly8gQ2hlY2sgZm9yIGxvb2t1cCgnVHlwZU5hbWUnKSBvciBsb29rdXAoc291cmNlLCAnVHlwZU5hbWUnKSBjYWxsc1xuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0Y29uc3QgZnVuY05hbWUgPSB0aGlzLmdldEZ1bmN0aW9uTmFtZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdFx0aWYgKGZ1bmNOYW1lID09PSAnbG9va3VwJyAmJiBub2RlLmFyZ3VtZW50cy5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdGNvbnN0IHR5cGVQYXRoID0gdGhpcy5yZXNvbHZlTG9va3VwUGF0aChub2RlKTtcblx0XHRcdFx0aWYgKHR5cGVQYXRoKSB7XG5cdFx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0XHQpO1xuXHRcdFx0XHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRcdFx0dGhpcy5hZGRVc2FnZSh0eXBlUGF0aCwge1xuXHRcdFx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdFx0XHRraW5kIDogJ2xvb2t1cCcsXG5cdFx0XHRcdFx0XHRjb2RlIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudCBmcm9tIGxvb2t1cCBmb3IgaW5zdGFudGlhdGlvbiB0cmFja2luZ1xuXHRcdFx0XHRcdHRoaXMudHJhY2tMb29rdXBBc3NpZ25tZW50KG5vZGUsIHR5cGVQYXRoKTtcblx0XHRcdFx0XHQvLyBSZWNvcmQgZm9yIHRoZSBoYXJkLWZhaWwgbGF3IGV2ZW4gd2hlbiBhZGRVc2FnZSBkcm9wcGVkXG5cdFx0XHRcdFx0Ly8gdGhlIHBhdGggKHVua25vd24gcGF0aHMgYXJlIGV4YWN0bHkgdGhlIGZhaWx1cmUgY2xhc3MpXG5cdFx0XHRcdFx0dGhpcy5sb29rdXBSZWZlcmVuY2VzLnB1c2goeyBwYXRoIDogdHlwZVBhdGgsIGxvY2F0aW9uIH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdC8vIENoYWluLWZvcm0gY29uc3RydWN0aW9uOiBgbmV3IFIoLi4uKS5BKC4uLilgIC8gdGhlIGF3YWl0ZWRcblx0XHRcdC8vIHNpbmdsZS1jaGFpbiBgYXdhaXQgbmV3IFIoLi4uKS5BKC4uLikuQiguLi4pYCDigJQgdGhlIGNhbGwgb25cblx0XHRcdC8vIHRoZSBmcmVzaCBpbnN0YW5jZSBjb25zdHJ1Y3RzIHRoZSBjaGFpbiBUSVAgKGF3YWl0IGlzXG5cdFx0XHQvLyB0cmFuc3BhcmVudDsgdGhlIE5ld0V4cHJlc3Npb24gYnJhbmNoIGFscmVhZHkgcmVjb3JkZWQgdGhlXG5cdFx0XHQvLyBpbm5lciByb290KS4gVGhlIHJlc3VsdCB2YXJpYWJsZSBiaW5kcyB0byB0aGUgdGlwLCBub3QgdGhlXG5cdFx0XHQvLyByb290ICh0cmFja05ld0Fzc2lnbm1lbnQgcmVzb2x2ZXMgdGhlIHNhbWUgdGlwKVxuXHRcdFx0Y29uc3QgY2hhaW5UaXAgPSB0aGlzLnJlc29sdmVDaGFpblRpcFR5cGVQYXRoKG5vZGUpO1xuXHRcdFx0aWYgKGNoYWluVGlwKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkQ29uc3RydWN0aW9uVXNhZ2Uobm9kZSwgY2hhaW5UaXAsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdCk7XG5cdFx0XHRcdHRoaXMuYWRkRmxvdyhjaGFpblRpcCwge1xuXHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0a2luZCAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRjb250ZXh0ICA6ICdjaGFpbmVkIGNvbnN0cnVjdGlvbicsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBtbmVtb25pY2EgY2FsbC9hcHBseShlbnRpdHksIEN0b3IsIC4uLikgLyBiaW5kKGVudGl0eSwgQ3Rvcikg4oCUXG5cdFx0XHQvLyB0eXBlZCBjb25zdHJ1Y3Rpb24gd2l0aG91dCBgbmV3YDogdGhlIEN0b3IgYXJndW1lbnQgKGFyZyAxKSBpc1xuXHRcdFx0Ly8gdGhlIGNvbnN0cnVjdGVkIHR5cGUuIEltcG9ydC1hd2FyZTogb25seSBpZGVudGlmaWVycyBhY3R1YWxseVxuXHRcdFx0Ly8gaW1wb3J0ZWQgZnJvbSAnbW5lbW9uaWNhJyAob3IgbWVtYmVycyBvZiBhIHRyYWNrZWRcblx0XHRcdC8vIG1vZHVsZS1vYmplY3QgYWxpYXMpIG1hdGNoIOKAlCB1c2VybGFuZCBjYWxsL2FwcGx5L2JpbmQgbmV2ZXJcblx0XHRcdC8vIGRvLiBjYWxsL2FwcGx5IHJlY29yZCB0aGUgY29uc3RydWN0aW9uOyBiaW5kKCkgY29uc3RydWN0c1xuXHRcdFx0Ly8gbm90aGluZyDigJQgaXQgb25seSBiaW5kcyB0aGUgcmVzdWx0IHZhcmlhYmxlIHRvIHRoZSBDdG9yJ3Ncblx0XHRcdC8vIHR5cGUgKHJ1bnRpbWUgSW5zdGFuY2VSZXN1bHQ8TWVyZ2U8RSxUPj4gYXBwcm94aW1hdGVkIGJ5IFRcblx0XHRcdC8vIHdpdGhpbiB0aGUgb3V0cHV0IGNvbnRyYWN0KVxuXHRcdFx0Y29uc3QgY29uc3RydWN0aW9uUGF0aCA9IHRoaXMucmVzb2x2ZUNvbnN0cnVjdGlvbkZuVHlwZVBhdGgobm9kZSk7XG5cdFx0XHRpZiAoY29uc3RydWN0aW9uUGF0aCkge1xuXHRcdFx0XHRjb25zdCBpc0JpbmRGb3JtID0gdGhpcy5pc01uZW1vbmljYUNvbnN0cnVjdGlvbkZuKG5vZGUuZXhwcmVzc2lvbiwgJ2JpbmQnKTtcblx0XHRcdFx0aWYgKCFpc0JpbmRGb3JtKSB7XG5cdFx0XHRcdFx0Y29uc3QgY3RvckFyZ1RleHQgPSBub2RlLmFyZ3VtZW50c1sgMSBdPy5nZXRUZXh0KHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRcdHRoaXMucmVjb3JkQ29uc3RydWN0aW9uVXNhZ2Uobm9kZSwgY29uc3RydWN0aW9uUGF0aCwgc291cmNlRmlsZSwgY3RvckFyZ1RleHQpO1xuXHRcdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdFx0KTtcblx0XHRcdFx0XHR0aGlzLmFkZEZsb3coY29uc3RydWN0aW9uUGF0aCwge1xuXHRcdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRcdGtpbmQgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRcdGNvbnRleHQgIDogJ2NhbGwvYXBwbHkgY29uc3RydWN0aW9uJyxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShub2RlLCBjb25zdHJ1Y3Rpb25QYXRoKTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gaW5zdGFuY2UuZm9yaygpL2Nsb25lKCkg4oCUIHJ1bnRpbWUgcmUtcnVucyBjb25zdHJ1Y3Rpb24gKGhvb2tzXG5cdFx0XHQvLyBmaXJlLCBhIGRpc3RpbmN0IGluc3RhbmNlIG9uIGEgZGlzdGluY3QgbGluZSksIHNvIGFuXG5cdFx0XHQvLyBgaW5zdGFudGlhdGlvbmAgdXNhZ2UgcmVjb3JkcyB0aGUgc2l0ZSBJTiBBRERJVElPTiB0byB0aGVcblx0XHRcdC8vIHJlc3VsdC12YXIgYmluZGluZyBhbmQgdGhlIGdlbmVyaWMgbWV0aG9kQ2FsbCBmbG93ICh0aGUgZW50cnlcblx0XHRcdC8vIGlzIGJ5dGUtaW5kaXN0aW5ndWlzaGFibGUgZnJvbSBgbmV3YCB1bnRpbCB0aGUgZGVmZXJyZWRcblx0XHRcdC8vIG1lY2hhbmlzbS1raW5kIHJldmlzaW9uIOKAlCB0aGUgb3duZXIncyBleHBsaWNpdCBjYWxsKS4gRnJlZVxuXHRcdFx0Ly8gdXRpbHMubWVyZ2UoYSwgYiwgLi4uKSAvIHV0aWxzLmZvcmsoaW5zdGFuY2UpKC4uLikgYXJlXG5cdFx0XHQvLyBjb25zdHJ1Y3Rpb24gb2YgYSdzIHR5cGUgdG9vIChtZXJnZSA9IGZvcmsoYSkgb3ZlciBiJ3Ncblx0XHRcdC8vIGNvbnRleHQpOyB0aGUgcmVzdWx0IGJpbmRpbmcga2VlcHMgdGhlIGRvY3VtZW50ZWQgYXJnLTBcblx0XHRcdC8vIGFwcHJveGltYXRpb25cblx0XHRcdGNvbnN0IGZvcmtMaWtlUGF0aCA9IHRoaXMucmVzb2x2ZUZvcmtMaWtlVHlwZVBhdGgobm9kZSk7XG5cdFx0XHRpZiAoZm9ya0xpa2VQYXRoKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkQ29uc3RydWN0aW9uVXNhZ2Uobm9kZSwgZm9ya0xpa2VQYXRoLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0dGhpcy5iaW5kUmVzdWx0VmFyaWFibGUobm9kZSwgZm9ya0xpa2VQYXRoKTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHV0aWxzUGF0aCA9IHRoaXMucmVzb2x2ZVV0aWxzRm5UeXBlUGF0aChub2RlKTtcblx0XHRcdGlmICh1dGlsc1BhdGgpIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZShub2RlLCB1dGlsc1BhdGgsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShub2RlLCB1dGlsc1BhdGgpO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIEdldCBmdW5jdGlvbiBuYW1lIGZyb20gZXhwcmVzc2lvbiAoaWRlbnRpZmllciBvciBwcm9wZXJ0eSBhY2Nlc3MpXG5cdFx0XHQqL1xuXHRwcml2YXRlIGdldEZ1bmN0aW9uTmFtZSAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIGV4cHIudGV4dDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0KiBBZGQgYSB1c2FnZSB0byB0aGUgY29sbGVjdGlvblxuXHRcdFx0Ki9cblx0cHJpdmF0ZSBhZGRVc2FnZSAodHlwZVBhdGg6IHN0cmluZywgdXNhZ2U6IFVzYWdlSW5mbyk6IHZvaWQge1xuXHRcdC8vIE9ubHkgdHJhY2sgdXNhZ2VzIG9mIG1uZW1vbmljYS1kZWZpbmVkIHR5cGVzXG5cdFx0aWYgKCF0aGlzLmRlZmluaXRpb25zLmhhcyh0eXBlUGF0aCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKCF0aGlzLnVzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLnVzYWdlcy5zZXQodHlwZVBhdGgsIFtdKTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgZHVwbGljYXRlcyBiYXNlZCBvbiBsb2NhdGlvbiwgY29kZSwgYW5kIGtpbmRcblx0XHRjb25zdCBleGlzdGluZ1VzYWdlcyA9IHRoaXMudXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGlzRHVwbGljYXRlID0gZXhpc3RpbmdVc2FnZXMuc29tZShleGlzdGluZyA9PlxuXHRcdFx0ZXhpc3RpbmcubG9jYXRpb24gPT09IHVzYWdlLmxvY2F0aW9uICYmXG5cdFx0XHRcdGV4aXN0aW5nLmNvZGUgPT09IHVzYWdlLmNvZGUgJiZcblx0XHRcdFx0ZXhpc3Rpbmcua2luZCA9PT0gdXNhZ2Uua2luZCk7XG5cblx0XHRpZiAoIWlzRHVwbGljYXRlKSB7XG5cdFx0XHRleGlzdGluZ1VzYWdlcy5wdXNoKHVzYWdlKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBFRFMgKEV4ZWN1dGlvbiBEYXRhIFN0b3JhZ2UpIHVzYWdlIGluZm9ybWF0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RFRFMgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkgfHwgIW5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZ1bmNOYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIWZ1bmNOYW1lKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXHRcdC8vIEVuY2xvc2luZyBtbmVtb25pY2EgdHlwZSBwYXRoIOKAlCB3cmFwIGFyZ3MgYXJlIHVzdWFsbHkgbG9jYWxcblx0XHQvLyBmdW5jdGlvbnMsIHNvIHRoZSBvd25pbmcgZGVmaW5lKCkvbGF6eSgpIGhhbmRsZXIgb3IgZGVjb3JhdGVkXG5cdFx0Ly8gY2xhc3MgaXMgd2hhdCBlZHMuanNvbiBjb25zdW1lcnMgKEdyYXBoQnVpbGRlcikgY2FuIGpvaW4gb24uXG5cdFx0Y29uc3Qgc2NvcGUgPSB0aGlzLnJlc29sdmVFRFNTY29wZShub2RlKTtcblxuXHRcdC8vIHdyYXAoZm4pLCB3cmFwQ29uc3RydWN0b3JBcmcoZm4sIHBhcmVudCksIHVwZ3JhZGVDb25zdHJ1Y3RvckFyZyhhcmcsIGluc3QpLCB3cmFwSW5zdGFuY2VNZXRob2RzKG9iailcblx0XHRpZiAoXG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3dyYXAnIHx8XG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3dyYXBDb25zdHJ1Y3RvckFyZycgfHxcblx0XHRcdGZ1bmNOYW1lID09PSAndXBncmFkZUNvbnN0cnVjdG9yQXJnJyB8fFxuXHRcdFx0ZnVuY05hbWUgPT09ICd3cmFwSW5zdGFuY2VNZXRob2RzJ1xuXHRcdCkge1xuXHRcdFx0Y29uc3QgdGFyZ2V0VHlwZSA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShub2RlLmFyZ3VtZW50c1sgMCBdKTtcblx0XHRcdC8vIGRpdmUncyB3cmFwLWZhbWlseSBzaWduYXR1cmVzIChkaXZlL3NyYy9pbmRleC50cyk6XG5cdFx0XHQvLyAgIHdyYXAoZm4sIGxhYmVsPykgfCB3cmFwKGZuLCBjb250ZXh0PywgbGFiZWw/KVxuXHRcdFx0Ly8gICB3cmFwQ29uc3RydWN0b3JBcmcoZm4sIGNvbnRleHQpXG5cdFx0XHQvLyAgIHVwZ3JhZGVDb25zdHJ1Y3RvckFyZyhhcmcsIGluc3RhbmNlKVxuXHRcdFx0Ly8gICB3cmFwSW5zdGFuY2VNZXRob2RzKGluc3RhbmNlKVxuXHRcdFx0Ly8g4oCmc28gdGhlIGluc3RhbmNlL2NvbnRleHQgYXJnIHNpdHMgYXQgYXJnc1sxXSAoYXJnc1swXSBmb3Jcblx0XHRcdC8vIHdyYXBJbnN0YW5jZU1ldGhvZHMpIGFuZCBhIHN0cmluZyBsaXRlcmFsIGluIGFyZ3NbMS4uMl0gaXMgdGhlIGxhYmVsXG5cdFx0XHRjb25zdCBpbnN0YW5jZUFyZ05vZGUgPSBmdW5jTmFtZSA9PT0gJ3dyYXBJbnN0YW5jZU1ldGhvZHMnXG5cdFx0XHRcdD8gbm9kZS5hcmd1bWVudHNbIDAgXVxuXHRcdFx0XHQ6IG5vZGUuYXJndW1lbnRzWyAxIF07XG5cdFx0XHQvLyBGaXJlLWFuZC1mb3JnZXQgd3JhcHBlcnMgKHdpcmUtdXAgaGVscGVycywgcmVnaXN0cmF0aW9uXG5cdFx0XHQvLyBmdW5jdGlvbnMpIHNpdCBvdXRzaWRlIGFueSBkZWZpbmUoKS9sYXp5KCkgaGFuZGxlciwgc28gdGhlXG5cdFx0XHQvLyBsZXhpY2FsIHNjb3BlIGlzIGFic2VudCDigJQgYXR0cmlidXRlIHRocm91Z2ggdGhlIGluc3RhbmNlL2NvbnRleHRcblx0XHRcdC8vIGFyZ3VtZW50IGluc3RlYWQ6IGEgdHJhY2tlZCBhc3NpZ25tZW50LCBlbHNlIHRoZSBlbmNsb3Npbmdcblx0XHRcdC8vIGZ1bmN0aW9uJ3MgcGFyYW1ldGVyIGFubm90YXRpb24gcmVzb2x2ZWQgdGhyb3VnaCB0aGUgZ3JhcGggbGF3XG5cdFx0XHRjb25zdCBpbnN0YW5jZVR5cGVQYXRoID0gaW5zdGFuY2VBcmdOb2RlXG5cdFx0XHRcdD8gdGhpcy5yZXNvbHZlV3JhcEluc3RhbmNlVHlwZVBhdGgoaW5zdGFuY2VBcmdOb2RlKVxuXHRcdFx0XHQ6IHVuZGVmaW5lZDtcblx0XHRcdGNvbnN0IGVmZmVjdGl2ZVNjb3BlID0gc2NvcGUgPz8gaW5zdGFuY2VUeXBlUGF0aDtcblx0XHRcdGNvbnN0IGluZm86IEVEU0luZm8gPSB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgIDogJ3dyYXAnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdHNjb3BlICAgICAgOiBlZmZlY3RpdmVTY29wZSxcblx0XHRcdFx0Zm4gICAgICAgICA6IGZ1bmNOYW1lLFxuXHRcdFx0fTtcblx0XHRcdGlmIChpbnN0YW5jZUFyZ05vZGUgJiYgdHMuaXNJZGVudGlmaWVyKGluc3RhbmNlQXJnTm9kZSkpIHtcblx0XHRcdFx0aW5mby5pbnN0YW5jZUFyZyA9IGluc3RhbmNlQXJnTm9kZS50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBleHRyYUFyZyBvZiBbIG5vZGUuYXJndW1lbnRzWyAxIF0sIG5vZGUuYXJndW1lbnRzWyAyIF0gXSkge1xuXHRcdFx0XHRpZiAoZXh0cmFBcmcgJiYgdHMuaXNTdHJpbmdMaXRlcmFsKGV4dHJhQXJnKSkge1xuXHRcdFx0XHRcdGluZm8ubGFiZWwgPSBleHRyYUFyZy50ZXh0O1xuXHRcdFx0XHRcdGJyZWFrO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBBIHdyYXAoKSBjYWxsIG5lc3RlZCBpbnNpZGUgYW5vdGhlciB3cmFwcGVkIGJvZHkgY2FycmllcyB0aGVcblx0XHRcdC8vIGxpbmsgdG8gdGhlIHNpdGUgd2hvc2UgcnVudGltZSB3cmFwcGluZyBjYXVzZWQgaXQg4oCUIGFuZCwgd2hlblxuXHRcdFx0Ly8gdGhlIG5lc3RlZCBzaXRlIGhhcyBubyBzY29wZSBvZiBpdHMgb3duLCB0aGUgY2F1c2luZyBzaXRlJ3Ncblx0XHRcdC8vIHNjb3BlIGF0dHJpYnV0aW9uIHRyYXZlbHMgd2l0aCB0aGUgbGlua1xuXHRcdFx0Y29uc3QgdmlhTGluayA9IHRoaXMubmVzdGVkV3JhcFZpYS5nZXQobm9kZSk7XG5cdFx0XHRpZiAodmlhTGluaykge1xuXHRcdFx0XHRpbmZvLnZpYSA9IHZpYUxpbmsudmlhO1xuXHRcdFx0XHRpZiAoaW5mby5zY29wZSA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdFx0aW5mby5zY29wZSA9IHZpYUxpbmsuc2NvcGU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIGRpdmUgd3JhcHMgcmV0dXJuZWQgZnVuY3Rpb25zIHRvbywgYW5kIGFueSBtbmVtb25pY2EgaW5zdGFuY2Vcblx0XHRcdC8vIGNyZWF0ZWQgaW5zaWRlIHRoZSB3cmFwcGVkIGJvZHkgaXMgYSBndWFyYW50ZWVkIHBhdGggaGl0IOKAlFxuXHRcdFx0Ly8gYm90aCBhcmUgY2FsY3VsYWJsZSBBb1QsIHNvIHJlY29yZCB0aGVtXG5cdFx0XHRjb25zdCB3cmFwcGVkID0gdGhpcy5yZXNvbHZlRnVuY3Rpb25Bcmd1bWVudChub2RlLmFyZ3VtZW50c1sgMCBdLCBzb3VyY2VGaWxlKTtcblx0XHRcdGlmICh3cmFwcGVkKSB7XG5cdFx0XHRcdC8vIFRoZSB3cmFwcGVkIGNhbGxiYWNrIGdldHMgaXRzIG93biBzY29wZSBpbiBzY29wZXMuanNvbiBrZXllZCBieVxuXHRcdFx0XHQvLyBpdHMgc3RhcnQgcG9zaXRpb24g4oCUIHJlY29yZCB0aGF0IHNjb3BlSWQgc28gZ3JhcGggY29uc3VtZXJzIGNhblxuXHRcdFx0XHQvLyBqb2luIGEgd3JhcCBlbnRyeSB0byB0aGUgY2FsbGJhY2sncyBjcmVhdGlvbiBub2RlXG5cdFx0XHRcdGNvbnN0IGNhbGxiYWNrUG9zID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHR3cmFwcGVkLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdCk7XG5cdFx0XHRcdGNvbnN0IGNhbGxiYWNrRmlsZSA9IG5vZGVQYXRoLnJlc29sdmUoc291cmNlRmlsZS5maWxlTmFtZSk7XG5cdFx0XHRcdGluZm8uY2FsbGJhY2tTY29wZUlkID0gYCR7Y2FsbGJhY2tGaWxlfToke2NhbGxiYWNrUG9zLmxpbmUgKyAxfToke2NhbGxiYWNrUG9zLmNoYXJhY3RlciArIDF9YDtcblx0XHRcdFx0Y29uc3QgY3JlYXRlc1R5cGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0XHRcdHRoaXMuYW5hbHl6ZVdyYXBwZWRCb2R5KHdyYXBwZWQsIGxvY2F0aW9uLCBzb3VyY2VGaWxlLCAwLCBuZXcgU2V0KCksIGNyZWF0ZXNUeXBlcywgZWZmZWN0aXZlU2NvcGUpO1xuXHRcdFx0XHRpZiAoY3JlYXRlc1R5cGVzLnNpemUgPiAwKSB7XG5cdFx0XHRcdFx0aW5mby5jcmVhdGVzVHlwZXMgPSBBcnJheS5mcm9tKGNyZWF0ZXNUeXBlcyk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGNvbnN0IHN0b3JlZCA9IHRoaXMuYWRkRURTKHRhcmdldFR5cGUgfHwgZWZmZWN0aXZlU2NvcGUgfHwgJ3Vua25vd24nLCBpbmZvKTtcblx0XHRcdHRoaXMud3JhcEVudHJ5QnlOb2RlLnNldChub2RlLCBzdG9yZWQpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGN1cnJlbnQoKSwgZ2V0RXJyb3JJbnN0YW5jZShlcnIpLCBnZXRGbG93KHRhcmdldD8pXG5cdFx0aWYgKGZ1bmNOYW1lID09PSAnY3VycmVudCcgfHwgZnVuY05hbWUgPT09ICdnZXRFcnJvckluc3RhbmNlJyB8fCBmdW5jTmFtZSA9PT0gJ2dldEZsb3cnKSB7XG5cdFx0XHR0aGlzLmFkZEVEUyhzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgOiAnY29udGV4dENvbnN1bWUnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRzY29wZSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGF0dGFjaEhvb2tzKGNvbGxlY3Rpb24pIOKAlCBmcm9tIEBtbmVtb25pY2Evb3RlbCwgd2lyZXMgYVxuXHRcdC8vIFR5cGVzQ29sbGVjdGlvbiB0byBkaXZlJ3MgbGlmZWN5Y2xlIHRyYWNpbmdcblx0XHRpZiAoZnVuY05hbWUgPT09ICdhdHRhY2hIb29rcycgJiYgbm9kZS5hcmd1bWVudHMubGVuZ3RoID4gMCkge1xuXHRcdFx0Y29uc3QgWyBhcmcgXSA9IG5vZGUuYXJndW1lbnRzO1xuXHRcdFx0aWYgKHRzLmlzQXJyYXlMaXRlcmFsRXhwcmVzc2lvbihhcmcpKSB7XG5cdFx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBhcmcuZWxlbWVudHMpIHtcblx0XHRcdFx0XHRjb25zdCB0YXJnZXRUeXBlID0gdGhpcy5yZXNvbHZlRURTQXJndW1lbnRUeXBlKGVsZW1lbnQpO1xuXHRcdFx0XHRcdHRoaXMuYWRkRURTKHRhcmdldFR5cGUgfHwgc2NvcGUgfHwgJ3Vua25vd24nLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0XHRcdGtpbmQgICAgICAgOiAnaG9va0F0dGFjaCcsXG5cdFx0XHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRcdFx0dGFyZ2V0VHlwZSA6IHRhcmdldFR5cGUgfHwgdW5kZWZpbmVkLFxuXHRcdFx0XHRcdFx0c2NvcGUsXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGNvbnN0IHRhcmdldFR5cGUgPSB0aGlzLnJlc29sdmVFRFNBcmd1bWVudFR5cGUoYXJnKTtcblx0XHRcdFx0dGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCBzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0XHRraW5kICAgICAgIDogJ2hvb2tBdHRhY2gnLFxuXHRcdFx0XHRcdGNvZGUsXG5cdFx0XHRcdFx0dGFyZ2V0VHlwZSA6IHRhcmdldFR5cGUgfHwgdW5kZWZpbmVkLFxuXHRcdFx0XHRcdHNjb3BlLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0eXBlIGZyb20gRURTIGNhbGwgYXJndW1lbnQgKGJlc3QgZWZmb3J0KVxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRURTQXJndW1lbnRUeXBlIChhcmc6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghYXJnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIElkZW50aWZpZXI6IHZhcmlhYmxlIG5hbWVcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdGNvbnN0IG1hcHBlZCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGFyZy50ZXh0KTtcblx0XHRcdGlmIChtYXBwZWQpIHtcblx0XHRcdFx0cmV0dXJuIG1hcHBlZDtcblx0XHRcdH1cblx0XHRcdC8vIE1heWJlIGl0J3MgYSB0eXBlIG5hbWUgZGlyZWN0bHlcblx0XHRcdGlmICh0aGlzLmRlZmluaXRpb25zLmhhcyhhcmcudGV4dCkpIHtcblx0XHRcdFx0cmV0dXJuIGFyZy50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0Ly8gbGV0LWluLXRyeTogYSBsZXQvdmFyIGJpbmRpbmcgZGVjbGFyZWQgd2l0aG91dCBhIHRyYWNrZWRcblx0XHRcdC8vIGluaXRpYWxpemVyIGFuZCBhc3NpZ25lZCBsYXRlciBpbiB0aGUgU0FNRSBzY29wZSAodGhlXG5cdFx0XHQvLyBmaXJlLWFuZC1mb3JnZXQgY2F0Y2gtZ3VhcmQgcGF0dGVybjogYGxldCBmbjsgdHJ5IHsgZm4gPVxuXHRcdFx0Ly8g4oCmIH0gY2F0Y2ggeyByZXR1cm4gfSB3cmFwKGZuLCDigKYpYCkg4oCUIGZvbGxvdyB0aGUgZmlyc3Rcblx0XHRcdC8vIHN0YXRpY2FsbHktdmlzaWJsZSBpbi1zY29wZSBhc3NpZ25tZW50LiBObyBmbG93IGFuYWx5c2lzOlxuXHRcdFx0Ly8gZnVuY3Rpb24vY2xhc3MgYm91bmRhcmllcyBhcmUgbm90IGNyb3NzZWQsIGFcblx0XHRcdC8vIG5ldmVyLWFzc2lnbmVkIGJpbmRpbmcgc3RheXMgdW5rbm93biAoRjIwIGRpc2NpcGxpbmUpLlxuXHRcdFx0Ly8gV2hlbiB0aGUgYXNzaWdubWVudCByZXNvbHZlcywgaXRzIGV2aWRlbmNlIFdJTlMgb3ZlciBhbnlcblx0XHRcdC8vIGRlY2xhcmF0aW9uIGFubm90YXRpb24gKHRoZSBjb25zdHJ1Y3RlZCBzdWJ0eXBlIGlzIHRoZSBtb3JlXG5cdFx0XHQvLyBzcGVjaWZpYyB0cnV0aCk7IGFuIHVucmVzb2x2YWJsZSBSSFMgKGEgdXNlcmxhbmQgY2FsbCwgc2F5KVxuXHRcdFx0Ly8gZmFsbHMgdGhyb3VnaCB0byB0aGUgYW5ub3RhdGlvbiBjbGFpbSBiZWxvdy5cblx0XHRcdGNvbnN0IGFzc2lnbmVkID0gdGhpcy5mb2xsb3dTY29wZUFzc2lnbm1lbnQoYXJnLnRleHQsIGFyZyk7XG5cdFx0XHRpZiAoYXNzaWduZWQpIHtcblx0XHRcdFx0Y29uc3QgcmVzb2x2ZWQgPSB0aGlzLnJlc29sdmVFRFNBcmd1bWVudFR5cGUoYXNzaWduZWQpO1xuXHRcdFx0XHRpZiAocmVzb2x2ZWQpIHtcblx0XHRcdFx0XHRyZXR1cm4gcmVzb2x2ZWQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIEFubm90YXRpb24gZmFsbGJhY2sg4oCUIHRoZSBGMjAgZGlzY2lwbGluZSBvbmUgYXJndW1lbnQgb3Zlcjpcblx0XHRcdC8vIGFuIGV4cGxpY2l0IGRlY2xhcmF0aW9uIG9yIHBhcmFtZXRlciBhbm5vdGF0aW9uIGlzIGEgdXNlclxuXHRcdFx0Ly8gY2xhaW0gd3JpdHRlbiBpbiB0aGUgQVNULCBub3QgZmxvdyBhbmFseXNpcy4gUGFyYW1ldGVyXG5cdFx0XHQvLyBmaXJzdDogaXQgc2hhZG93cyBhbiBvdXRlciBsZXQsIHNhbWUgYXMgdGhlIGNvbnRleHQtYXJnIHBhdGguXG5cdFx0XHRjb25zdCBhbm5vdGF0ZWQgPSB0aGlzLnJlc29sdmVQYXJhbWV0ZXJBbm5vdGF0aW9uVHlwZVBhdGgoYXJnLnRleHQsIGFyZykgPz9cblx0XHRcdFx0dGhpcy5yZXNvbHZlVmFyaWFibGVBbm5vdGF0aW9uVHlwZVBhdGgoYXJnLnRleHQsIGFyZyk7XG5cdFx0XHRyZXR1cm4gYW5ub3RhdGVkO1xuXHRcdH1cblxuXHRcdC8vIE5ld0V4cHJlc3Npb246IHRoZSBjb25zdHJ1Y3RlZCB0eXBlIOKAlCByZWFjaGFibGUgZGlyZWN0bHlcblx0XHQvLyAod3JhcChuZXcgVCgpLCDigKYpKSBvciB0aHJvdWdoIGEgZm9sbG93ZWQgYXNzaWdubWVudFxuXHRcdGlmICh0cy5pc05ld0V4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0Y29uc3QgY3RvckV4cHIgPSBhcmcuZXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IG5hbWUgPSB0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdG9yRXhwcilcblx0XHRcdFx0PyB0aGlzLnJlc29sdmVUeXBlUGF0aChjdG9yRXhwcilcblx0XHRcdFx0OiB0aGlzLmdldFR5cGVOYW1lRnJvbUV4cHJlc3Npb24oY3RvckV4cHIpO1xuXHRcdFx0Y29uc3Qga25vd24gPSBuYW1lICYmIHRoaXMuZGVmaW5pdGlvbnMuaGFzKG5hbWUpID8gbmFtZSA6IHVuZGVmaW5lZDtcblx0XHRcdHJldHVybiBrbm93bjtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSBhY2Nlc3M6IG9iai5wcm9wXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdHJldHVybiB0aGlzLnJlc29sdmVUeXBlUGF0aChhcmcpO1xuXHRcdH1cblxuXHRcdC8vIFRoaXMgZXhwcmVzc2lvbjogdGhpcy5zb21ldGhpbmdcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXJnKSAmJiB0cy5pc0lkZW50aWZpZXIoYXJnLmV4cHJlc3Npb24pICYmIGFyZy5leHByZXNzaW9uLnRleHQgPT09ICd0aGlzJykge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIGxldC1pbi10cnk6IGZpbmQgdGhlIFJJR0hULUhBTkQgU0lERSBvZiB0aGUgZmlyc3Qgc3RhdGljYWxseS12aXNpYmxlXG5cdCAqIGFzc2lnbm1lbnQgdG8gYG5hbWVgIGluIHRoZSBzY29wZSB0aGF0IGRlY2xhcmVzIGl0LiBUaGUgZGVjbGFyaW5nXG5cdCAqIGNvbnRhaW5lciBpcyBmb3VuZCBpbm5lcm1vc3Qtb3V0IChibG9ja3MsIGNhc2UgY2xhdXNlcywgdGhlIHNvdXJjZVxuXHQgKiBmaWxlIOKAlCB0aGUgRjIwIHdhbGspOyB0aGUgc2NhbiByZWN1cnNlcyBpbnRvIG5lc3RlZCBibG9ja3MgKHRyeS9cblx0ICogY2F0Y2gvZmluYWxseSwgaWYvZWxzZSwgbG9vcHMsIHN3aXRjaCBjYXNlcykgYnV0IE5FVkVSIGNyb3NzZXNcblx0ICogZnVuY3Rpb24gb3IgY2xhc3MgYm91bmRhcmllcyDigJQgYW4gYXNzaWdubWVudCBpbnNpZGUgYSBjbG9zdXJlIGRvZXNcblx0ICogbm90IGF0dHJpYnV0ZS4gUmV0dXJucyB1bmRlZmluZWQgd2hlbiB0aGUgYmluZGluZyBpcyBkZWNsYXJlZCBidXRcblx0ICogbmV2ZXIgYXNzaWduZWQgaW4gc2NvcGUgKGFuZCBzdG9wcyB0aGVyZTogYW4gaW5uZXIgZGVjbGFyYXRpb25cblx0ICogc2hhZG93cyBhbnkgb3V0ZXIgYmluZGluZykuXG5cdCAqL1xuXHRwcml2YXRlIGZvbGxvd1Njb3BlQXNzaWdubWVudCAobmFtZTogc3RyaW5nLCBmcm9tOiB0cy5Ob2RlKTogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBmcm9tO1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRjb25zdCBzdGF0ZW1lbnRzOiB0cy5Ob2RlQXJyYXk8dHMuU3RhdGVtZW50PiB8IHVuZGVmaW5lZCA9XG5cdFx0XHRcdHRzLmlzQmxvY2soY3VycmVudCkgfHwgdHMuaXNNb2R1bGVCbG9jayhjdXJyZW50KSB8fCB0cy5pc1NvdXJjZUZpbGUoY3VycmVudClcblx0XHRcdFx0XHQ/IGN1cnJlbnQuc3RhdGVtZW50c1xuXHRcdFx0XHRcdDogdHMuaXNDYXNlQ2xhdXNlKGN1cnJlbnQpIHx8IHRzLmlzRGVmYXVsdENsYXVzZShjdXJyZW50KVxuXHRcdFx0XHRcdFx0PyBjdXJyZW50LnN0YXRlbWVudHNcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0aWYgKHN0YXRlbWVudHMgJiYgdGhpcy5zdGF0ZW1lbnRzRGVjbGFyZVZhcmlhYmxlKHN0YXRlbWVudHMsIG5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHJocyA9IHRoaXMuZmluZEFzc2lnbm1lbnRSaHNJblN0YXRlbWVudHMoc3RhdGVtZW50cywgbmFtZSk7XG5cdFx0XHRcdHJldHVybiByaHM7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogVHJ1ZSB3aGVuIHRoZSBzdGF0ZW1lbnQgbGlzdCBjb250YWlucyBhIGBsZXRgL2B2YXJgL2Bjb25zdGBcblx0ICogZGVjbGFyYXRpb24gZm9yIGBuYW1lYCAoYW55IGluaXRpYWxpemVyIGZvcm0pLlxuXHQgKi9cblx0cHJpdmF0ZSBzdGF0ZW1lbnRzRGVjbGFyZVZhcmlhYmxlIChzdGF0ZW1lbnRzOiByZWFkb25seSB0cy5TdGF0ZW1lbnRbXSwgbmFtZTogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc3RhdGVtZW50cykge1xuXHRcdFx0aWYgKCF0cy5pc1ZhcmlhYmxlU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGRlY2xhcmF0aW9uIG9mIHN0YXRlbWVudC5kZWNsYXJhdGlvbkxpc3QuZGVjbGFyYXRpb25zKSB7XG5cdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZGVjbGFyYXRpb24ubmFtZSkgJiYgZGVjbGFyYXRpb24ubmFtZS50ZXh0ID09PSBuYW1lKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpcnN0IGBuYW1lID0gcmhzYCBhc3NpZ25tZW50IGluIHRoZSBzdGF0ZW1lbnQgbGlzdCwgcmVjdXJzaW5nXG5cdCAqIGludG8gbmVzdGVkIGluLXNjb3BlIGJsb2Nrcy4gRnVuY3Rpb24gYW5kIGNsYXNzIGJvZGllcyBhcmVcblx0ICogYm91bmRhcmllcyBhbmQgYXJlIG5vdCBlbnRlcmVkLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kQXNzaWdubWVudFJoc0luU3RhdGVtZW50cyAoXG5cdFx0c3RhdGVtZW50czogcmVhZG9ubHkgdHMuU3RhdGVtZW50W10sXG5cdFx0bmFtZTogc3RyaW5nXG5cdCk6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIHN0YXRlbWVudHMpIHtcblx0XHRcdGNvbnN0IGRpcmVjdCA9IHRoaXMuZGlyZWN0QXNzaWdubWVudFJocyhzdGF0ZW1lbnQsIG5hbWUpO1xuXHRcdFx0aWYgKGRpcmVjdCkge1xuXHRcdFx0XHRyZXR1cm4gZGlyZWN0O1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBuZXN0ZWQgb2YgdGhpcy5uZXN0ZWRTY29wZUJsb2NrcyhzdGF0ZW1lbnQpKSB7XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kQXNzaWdubWVudFJoc0luU3RhdGVtZW50cyhuZXN0ZWQsIG5hbWUpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBgbmFtZSA9IHJoc2AgYXMgYSBkaXJlY3QgZXhwcmVzc2lvbiBzdGF0ZW1lbnQuXG5cdCAqL1xuXHRwcml2YXRlIGRpcmVjdEFzc2lnbm1lbnRSaHMgKHN0YXRlbWVudDogdHMuU3RhdGVtZW50LCBuYW1lOiBzdHJpbmcpOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIXRzLmlzRXhwcmVzc2lvblN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBleHByID0gc3RhdGVtZW50LmV4cHJlc3Npb247XG5cdFx0aWYgKCF0cy5pc0JpbmFyeUV4cHJlc3Npb24oZXhwcikgfHwgZXhwci5vcGVyYXRvclRva2VuLmtpbmQgIT09IHRzLlN5bnRheEtpbmQuRXF1YWxzVG9rZW4pIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGV4cHIubGVmdCkgfHwgZXhwci5sZWZ0LnRleHQgIT09IG5hbWUpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJocyA9IGV4cHIucmlnaHQ7XG5cdFx0cmV0dXJuIHJocztcblx0fVxuXG5cdC8qKlxuXHQgKiBTdGF0ZW1lbnQgbGlzdHMgb2YgdGhlIG5lc3RlZCBibG9ja3MgdGhhdCBzdGF5IElOU0lERSB0aGUgY3VycmVudFxuXHQgKiBzY29wZSDigJQgdHJ5L2NhdGNoL2ZpbmFsbHksIGlmL2Vsc2UsIGxvb3BzLCBzd2l0Y2ggY2FzZXMsIG5lc3RlZFxuXHQgKiBibG9ja3MsIGxhYmVsZWQgc3RhdGVtZW50cy4gRnVuY3Rpb24tbGlrZSBhbmQgY2xhc3MgYm9kaWVzIGFyZVxuXHQgKiBzY29wZSBib3VuZGFyaWVzIGFuZCB5aWVsZCBub3RoaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBuZXN0ZWRTY29wZUJsb2NrcyAoc3RhdGVtZW50OiB0cy5TdGF0ZW1lbnQpOiByZWFkb25seSAocmVhZG9ubHkgdHMuU3RhdGVtZW50W10pW10ge1xuXHRcdGNvbnN0IGJsb2NrczogdHMuU3RhdGVtZW50W11bXSA9IFtdO1xuXHRcdGNvbnN0IHB1c2ggPSAobm9kZTogdHMuU3RhdGVtZW50IHwgdW5kZWZpbmVkKTogdm9pZCA9PiB7XG5cdFx0XHRpZiAobm9kZSAmJiB0cy5pc0Jsb2NrKG5vZGUpKSB7XG5cdFx0XHRcdGJsb2Nrcy5wdXNoKFsgLi4ubm9kZS5zdGF0ZW1lbnRzIF0pO1xuXHRcdFx0fVxuXHRcdH07XG5cdFx0aWYgKHRzLmlzQmxvY2soc3RhdGVtZW50KSkge1xuXHRcdFx0YmxvY2tzLnB1c2goWyAuLi5zdGF0ZW1lbnQuc3RhdGVtZW50cyBdKTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzVHJ5U3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdHB1c2goc3RhdGVtZW50LnRyeUJsb2NrKTtcblx0XHRcdGlmIChzdGF0ZW1lbnQuY2F0Y2hDbGF1c2UpIHtcblx0XHRcdFx0cHVzaChzdGF0ZW1lbnQuY2F0Y2hDbGF1c2UuYmxvY2spO1xuXHRcdFx0fVxuXHRcdFx0cHVzaChzdGF0ZW1lbnQuZmluYWxseUJsb2NrKTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzSWZTdGF0ZW1lbnQoc3RhdGVtZW50KSkge1xuXHRcdFx0cHVzaChzdGF0ZW1lbnQudGhlblN0YXRlbWVudCk7XG5cdFx0XHRwdXNoKHN0YXRlbWVudC5lbHNlU3RhdGVtZW50KTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzRm9yU3RhdGVtZW50KHN0YXRlbWVudCkgfHwgdHMuaXNGb3JJblN0YXRlbWVudChzdGF0ZW1lbnQpIHx8XG5cdFx0XHR0cy5pc0Zvck9mU3RhdGVtZW50KHN0YXRlbWVudCkgfHwgdHMuaXNXaGlsZVN0YXRlbWVudChzdGF0ZW1lbnQpIHx8XG5cdFx0XHR0cy5pc0RvU3RhdGVtZW50KHN0YXRlbWVudCkgfHwgdHMuaXNXaXRoU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdHB1c2goc3RhdGVtZW50LnN0YXRlbWVudCk7XG5cdFx0fSBlbHNlIGlmICh0cy5pc1N3aXRjaFN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGNsYXVzZSBvZiBzdGF0ZW1lbnQuY2FzZUJsb2NrLmNsYXVzZXMpIHtcblx0XHRcdFx0YmxvY2tzLnB1c2goWyAuLi5jbGF1c2Uuc3RhdGVtZW50cyBdKTtcblx0XHRcdH1cblx0XHR9IGVsc2UgaWYgKHRzLmlzTGFiZWxlZFN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRjb25zdCBuZXN0ZWQgPSB0aGlzLm5lc3RlZFNjb3BlQmxvY2tzKHN0YXRlbWVudC5zdGF0ZW1lbnQpO1xuXHRcdFx0Zm9yIChjb25zdCBibG9jayBvZiBuZXN0ZWQpIHtcblx0XHRcdFx0YmxvY2tzLnB1c2goWyAuLi5ibG9jayBdKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gYmxvY2tzO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0aGUgZW5jbG9zaW5nIG1uZW1vbmljYSBzY29wZSBvZiBhbiBFRFMgY2FsbCBzaXRlIGJ5IHdhbGtpbmdcblx0ICogdXAgdGhlIHBhcmVudCBjaGFpbjogbmVhcmVzdCBkZWZpbmUoKS9sYXp5KCkgY2FsbCB3aG9zZSBoYW5kbGVyIGhvbGRzXG5cdCAqIHRoZSBub2RlLCBvciBuZWFyZXN0IEBkZWNvcmF0ZSgpLWVkIGNsYXNzIGRlY2xhcmF0aW9uLiBCZXN0IGVmZm9ydCDigJRcblx0ICogcmV0dXJucyB1bmRlZmluZWQgZm9yIGNhbGxzIG91dHNpZGUgYW55IHR5cGUgc2NvcGUgKG1vZHVsZSB0b3AgbGV2ZWwpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRURTU2NvcGUgKG5vZGU6IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbm9kZS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGNvbnN0IHNjb3BlUGF0aCA9IHRoaXMuZWRzU2NvcGVCeU5vZGUuZ2V0KGN1cnJlbnQpO1xuXHRcdFx0aWYgKHNjb3BlUGF0aCkge1xuXHRcdFx0XHRyZXR1cm4gc2NvcGVQYXRoO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSB3cmFwIHNpdGUncyBpbnN0YW5jZS9jb250ZXh0IGFyZ3VtZW50IHRvIGEgbW5lbW9uaWNhIHR5cGVcblx0ICogcGF0aCDigJQgdGhlIGZpcmUtYW5kLWZvcmdldC13cmFwcGVyIGF0dHJpYnV0aW9uIGZhbGxiYWNrIHdoZW4gdGhlIGNhbGxcblx0ICogc2l0cyBvdXRzaWRlIGFueSBkZWZpbmUoKS9sYXp5KCkgaGFuZGxlcjogYSB0cmFja2VkIGFzc2lnbm1lbnRcblx0ICogKGBjb25zdCBob2xkZXIgPSBuZXcgSG9sZGVyKC4uLilgKSwgZWxzZSB0aGUgcm9vdCBpZGVudGlmaWVyJ3Ncblx0ICogKHByb3BlcnR5LWFjY2VzcyByb290cyBpbmNsdWRlZCkgcGFyYW1ldGVyIGFubm90YXRpb24gcmVzb2x2ZWRcblx0ICogdGhyb3VnaCB0aGUgZ3JhcGggbGF3LiBBbWJpZ3VpdHkgb3IgYWJzZW5jZSBzdGF5cyBzaWxlbnQg4oCUIHRoaXMgaXMgYVxuXHQgKiBtZXRhZGF0YSBoZXVyaXN0aWMsIG5vdCB0aGUgaWRlbnRpdHktbGF3IHN1cmZhY2UuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVXcmFwSW5zdGFuY2VUeXBlUGF0aCAoYXJnOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBmcm9tQmluZGluZyA9IChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQgPT4ge1xuXHRcdFx0Y29uc3QgbWFwcGVkID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0XHRpZiAobWFwcGVkKSB7XG5cdFx0XHRcdHJldHVybiBtYXBwZWQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBhbm5vdGF0aW9uVHlwZSA9IHRoaXMucmVzb2x2ZVBhcmFtZXRlckFubm90YXRpb25UeXBlUGF0aChuYW1lLCBmcm9tKSA/P1xuXHRcdFx0XHQvLyBGMjAgY2hlYXAgdGllcjogdGhlIGlkZW50aWZpZXIgaXMgYm91bmQgdG8gYSBsZXQvdmFyL2NvbnN0XG5cdFx0XHRcdC8vIHdpdGggYW4gRVhQTElDSVQgdHlwZSBhbm5vdGF0aW9uIOKAlCByZXNvbHZlIHRoZSBhbm5vdGF0aW9uXG5cdFx0XHRcdC8vIHRocm91Z2ggdGhlIGdyYXBoIGxhdy4gTm8gZmxvdy1zZW5zaXRpdmUgYXNzaWdubWVudFxuXHRcdFx0XHQvLyB0cmFja2luZzogYW4gVU5BTk5PVEFURUQgbGV0IHN0aWxsIGJ1Y2tldHMgdW5rbm93blxuXHRcdFx0XHR0aGlzLnJlc29sdmVWYXJpYWJsZUFubm90YXRpb25UeXBlUGF0aChuYW1lLCBmcm9tKTtcblx0XHRcdHJldHVybiBhbm5vdGF0aW9uVHlwZTtcblx0XHR9O1xuXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihhcmcpKSB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSBmcm9tQmluZGluZyhhcmcudGV4dCwgYXJnKTtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcmcpKSB7XG5cdFx0XHRjb25zdCByb290ID0gdGhpcy5nZXRSb290SWRlbnRpZmllcihhcmcpO1xuXHRcdFx0aWYgKHJvb3QpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0ID0gZnJvbUJpbmRpbmcocm9vdC50ZXh0LCBhcmcpO1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEVtaXNzaW9uLWxhdyBoZWxwZXIgKDAuMi4wIHJlc3RvcmF0aW9uKTogaXMgYG5hbWVgIGRlY2xhcmVkIGluIGFueVxuXHQgKiBBTkFMWVpFRCBQUk9KRUNUIGZpbGU/IEV4dGVybmFsL2FtYmllbnQgZmlsZXMgKC5kLnRzLCBub2RlX21vZHVsZXMpXG5cdCAqIGRvIG5vdCBjb3VudC4gQSBuYW1lIHdpdGggbm8gcHJvamVjdCBkZWNsYXJhdGlvbiBpcyBhbiBhbWJpZW50L2xpYlxuXHQgKiBjb25zdHJ1Y3Qg4oCUIHNhZmUgdG8gZW1pdCB2ZXJiYXRpbSBpbnRvIHRoZSBzZWxmLWNvbnRhaW5lZCB0eXBlcy50cztcblx0ICogYSBwcm9qZWN0LWxvY2FsIG5hbWUgaXMgbm90IChubyBpbXBvcnRzIGluIHRoZSBnZW5lcmF0ZWQgZmlsZSkuXG5cdCAqL1xuXHRwcml2YXRlIGlzUHJvamVjdERlY2xhcmVkVHlwZU5hbWUgKG5hbWU6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRcdGZvciAoY29uc3QgWyBmaWxlLCBkZWNscyBdIG9mIHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscykge1xuXHRcdFx0aWYgKHRoaXMuaXNFeHRlcm5hbERlY2xGaWxlKGZpbGUpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGRlY2xzLmhhcyhuYW1lKSkge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gZmFsc2U7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGMjQ6IHJlc29sdmUgYSBiYXJlLWlkZW50aWZpZXIgYW5ub3RhdGlvbiB0byBhIGdyYXBoIGZ1bGxQYXRoLiBUaGVcblx0ICogYW5ub3RhdGlvbiBtYXkgbmFtZSB0aGUgdHlwZSBkaXJlY3RseSAoYExlZGdlclVwZGF0ZWApIG9yIGNhcnJ5XG5cdCAqIHRoZSBHRU5FUkFURUQgaW5zdGFuY2UgYWxpYXMgb2YgYSBuZXN0ZWQgdHlwZVxuXHQgKiAoYFVwZGF0ZVBheV9Tb21lVGVybWluYWxgLCBpbXBvcnRlZCBmcm9tIHRoZSBnZW5lcmF0ZWQgdHlwZXMgZmlsZVxuXHQgKiB2aWEgdHNjb25maWcgcGF0aHMpIOKAlCBub3QgYSBncmFwaCBub2RlIE5BTUUuIFRoZSBuYW1lIGlzIHRyaWVkXG5cdCAqIGFzLWlzIGZpcnN0LCB0aGVuIGl0cyB1bmRlcnNjb3Jl4oaSZG90dGVkIGZvcm0gKHRoZSBnZW5lcmF0ZWQgYWxpYXNcblx0ICogbmFtaW5nIGxhdzsgdGhlIHNhbWUgbWFwcGluZyBzY29wZXMuanNvbiB1c2VzIGZvciBhbm5vdGF0aW9ucykuXG5cdCAqIEFtYmlndWl0eSBhbmQgYWJzZW5jZSB5aWVsZCB1bmRlZmluZWQuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVBbm5vdGF0aW9uVHlwZVBhdGggKG5hbWU6IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgZGlyZWN0ID0gdGhpcy5yZXNvbHZlR3JhcGhUeXBlTmFtZShuYW1lKTtcblx0XHRpZiAoZGlyZWN0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGRpcmVjdC5ub2RlLmZ1bGxQYXRoO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9XG5cdFx0aWYgKCFuYW1lLmluY2x1ZGVzKCdfJykpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGFsaWFzZWQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKG5hbWUucmVwbGFjZSgvXy9nLCAnLicpKTtcblx0XHRpZiAoYWxpYXNlZC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSBhbGlhc2VkLm5vZGUuZnVsbFBhdGg7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSBiYXJlLWlkZW50aWZpZXIgdHlwZSBhbm5vdGF0aW9uIG9mIHRoZSBuZWFyZXN0IGVuY2xvc2luZ1xuXHQgKiBmdW5jdGlvbidzIHBhcmFtZXRlciB0aHJvdWdoIHRoZSBtbmVtb25pY2EtZ3JhcGggdGllcnMgKHZhbHVlIHNjb3BlLFxuXHQgKiBpbXBvcnRzLCByb290cywgcHJvZ3JhbS13aWRlLXVuaXF1ZSkuIE5vbi1pZGVudGlmaWVyIGFuZCBnZW5lcmljXG5cdCAqIGFubm90YXRpb25zIGFyZSBub3QgZ3JhcGggcmVmZXJlbmNlczsgYW1iaWd1aXR5IGFuZCBhYnNlbmNlIHlpZWxkXG5cdCAqIHVuZGVmaW5lZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVBhcmFtZXRlckFubm90YXRpb25UeXBlUGF0aCAobmFtZTogc3RyaW5nLCBmcm9tOiB0cy5Ob2RlKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IGZyb20ucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNGdW5jdGlvbkxpa2UoY3VycmVudCkpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBjdXJyZW50LnBhcmFtZXRlcnMgPz8gW10pIHtcblx0XHRcdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSB8fCBwYXJhbS5uYW1lLnRleHQgIT09IG5hbWUgfHwgIXBhcmFtLnR5cGUgfHxcblx0XHRcdFx0XHRcdCF0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHBhcmFtLnR5cGUpIHx8XG5cdFx0XHRcdFx0XHQhdHMuaXNJZGVudGlmaWVyKHBhcmFtLnR5cGUudHlwZU5hbWUpIHx8XG5cdFx0XHRcdFx0XHQocGFyYW0udHlwZS50eXBlQXJndW1lbnRzPy5sZW5ndGggPz8gMCkgPiAwKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Y29uc3QgcmVzb2x2ZWQgPSB0aGlzLnJlc29sdmVBbm5vdGF0aW9uVHlwZVBhdGgocGFyYW0udHlwZS50eXBlTmFtZS50ZXh0KTtcblx0XHRcdFx0XHRpZiAocmVzb2x2ZWQpIHtcblx0XHRcdFx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGMjAgY2hlYXAgdGllcjogdGhlIHdyYXAgYXJndW1lbnQgaXMgYW4gaWRlbnRpZmllciBkZWNsYXJlZCB3aXRoIGFuXG5cdCAqIEVYUExJQ0lUIHR5cGUgYW5ub3RhdGlvbiAoYGxldCB1cGRhdGVDb21taXR0ZWQ6IExlZGdlclVwZGF0ZTtgXG5cdCAqIGFzc2lnbmVkIGxhdGVyIGluIGEgZmxvdyB0aGUgYW5hbHl6ZXIgZG9lcyBub3QgdHJhY2spLiBUaGVcblx0ICogYW5ub3RhdGlvbiByZXNvbHZlcyB0aHJvdWdoIHRoZSBzYW1lIGdyYXBoIHRpZXJzIGFzIHBhcmFtZXRlclxuXHQgKiBhbm5vdGF0aW9ucy4gRGVsaWJlcmF0ZWx5IE5PVCBmbG93LXNlbnNpdGl2ZTogYW4gVU5BTk5PVEFURURcblx0ICogbGV0L3ZhciBzdGlsbCBidWNrZXRzIHVua25vd24sIGFuZCBhIGNvbnN0IHdpdGggYW4gYW5hbHl6YWJsZVxuXHQgKiBpbml0aWFsaXplciBzdGF5cyB0aGUgcmVjb21tZW5kZWQgZGlzY2lwbGluZS4gVGhlIGxvb2t1cCB3YWxrcyB0aGVcblx0ICogZW5jbG9zaW5nIHN0YXRlbWVudCBjb250YWluZXJzIGlubmVybW9zdC1vdXQsIHNvIGEgc2hhZG93aW5nIGlubmVyXG5cdCAqIGRlY2xhcmF0aW9uIHdpbnMuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVWYXJpYWJsZUFubm90YXRpb25UeXBlUGF0aCAobmFtZTogc3RyaW5nLCBmcm9tOiB0cy5Ob2RlKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IGZyb207XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGNvbnN0IHN0YXRlbWVudHM6IHRzLk5vZGVBcnJheTx0cy5TdGF0ZW1lbnQ+IHwgdW5kZWZpbmVkID1cblx0XHRcdFx0dHMuaXNCbG9jayhjdXJyZW50KSB8fCB0cy5pc01vZHVsZUJsb2NrKGN1cnJlbnQpIHx8IHRzLmlzU291cmNlRmlsZShjdXJyZW50KVxuXHRcdFx0XHRcdD8gY3VycmVudC5zdGF0ZW1lbnRzXG5cdFx0XHRcdFx0OiB0cy5pc0Nhc2VDbGF1c2UoY3VycmVudCkgfHwgdHMuaXNEZWZhdWx0Q2xhdXNlKGN1cnJlbnQpXG5cdFx0XHRcdFx0XHQ/IGN1cnJlbnQuc3RhdGVtZW50c1xuXHRcdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cdFx0XHRpZiAoc3RhdGVtZW50cykge1xuXHRcdFx0XHRjb25zdCByZXNvbHZlZCA9IHRoaXMuZmluZEFubm90YXRlZFZhcmlhYmxlVHlwZVBhdGgoc3RhdGVtZW50cywgbmFtZSk7XG5cdFx0XHRcdGlmIChyZXNvbHZlZCkge1xuXHRcdFx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpcnN0IHZhcmlhYmxlIGRlY2xhcmF0aW9uIGNhcnJ5aW5nIGFuIGV4cGxpY2l0IGJhcmUtaWRlbnRpZmllciB0eXBlXG5cdCAqIGFubm90YXRpb24gZm9yIGBuYW1lYCBpbiB0aGUgZ2l2ZW4gc3RhdGVtZW50IGxpc3QsIHJlc29sdmVkIHRocm91Z2hcblx0ICogdGhlIGdyYXBoIGxhdy5cblx0ICovXG5cdHByaXZhdGUgZmluZEFubm90YXRlZFZhcmlhYmxlVHlwZVBhdGggKFxuXHRcdHN0YXRlbWVudHM6IHJlYWRvbmx5IHRzLlN0YXRlbWVudFtdLFxuXHRcdG5hbWU6IHN0cmluZ1xuXHQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIHN0YXRlbWVudHMpIHtcblx0XHRcdGlmICghdHMuaXNWYXJpYWJsZVN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBkZWNsYXJhdGlvbiBvZiBzdGF0ZW1lbnQuZGVjbGFyYXRpb25MaXN0LmRlY2xhcmF0aW9ucykge1xuXHRcdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihkZWNsYXJhdGlvbi5uYW1lKSB8fCBkZWNsYXJhdGlvbi5uYW1lLnRleHQgIT09IG5hbWUgfHxcblx0XHRcdFx0XHQhZGVjbGFyYXRpb24udHlwZSB8fFxuXHRcdFx0XHRcdCF0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKGRlY2xhcmF0aW9uLnR5cGUpIHx8XG5cdFx0XHRcdFx0IXRzLmlzSWRlbnRpZmllcihkZWNsYXJhdGlvbi50eXBlLnR5cGVOYW1lKSB8fFxuXHRcdFx0XHRcdChkZWNsYXJhdGlvbi50eXBlLnR5cGVBcmd1bWVudHM/Lmxlbmd0aCA/PyAwKSA+IDApIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCByZXNvbHZlZCA9IHRoaXMucmVzb2x2ZUFubm90YXRpb25UeXBlUGF0aChkZWNsYXJhdGlvbi50eXBlLnR5cGVOYW1lLnRleHQpO1xuXHRcdFx0XHRpZiAocmVzb2x2ZWQpIHtcblx0XHRcdFx0XHRyZXR1cm4gcmVzb2x2ZWQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgd3JhcCgpIGFyZ3VtZW50IHRvIGl0cyBmdW5jdGlvbiBub2RlIHdpdGhvdXQgdGhlIHR5cGVcblx0ICogY2hlY2tlcjogZGlyZWN0IGZ1bmN0aW9uIGV4cHJlc3Npb25zL2Fycm93cywgb3Igc2FtZS1maWxlIGJpbmRpbmdzXG5cdCAqIChgY29uc3QgZm4gPSAoKSA9PiAuLi5gLCBgZnVuY3Rpb24gZm4oKSAuLi5gKS4gQmVzdCBlZmZvcnQg4oCUIG1ldGhvZFxuXHQgKiByZWZlcmVuY2VzLCAuYmluZCgpIHByb2R1Y3RzIGFuZCBjcm9zcy1maWxlIGlkZW50aWZpZXJzIHN0YXlcblx0ICogdW5yZXNvbHZlZDsgdGhlIGNhbGxzaXRlIGVudHJ5IGl0c2VsZiBpcyBzdGlsbCByZWNvcmRlZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUZ1bmN0aW9uQXJndW1lbnQgKFxuXHRcdGFyZzogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlXG5cdCk6IHRzLkZ1bmN0aW9uTGlrZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIWFyZykge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihhcmcpIHx8IHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdHJldHVybiBhcmc7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0Y29uc3Qga2V5ID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX0jJHthcmcudGV4dH1gO1xuXHRcdFx0Y29uc3QgYm91bmQgPSB0aGlzLmZ1bmN0aW9uQmluZGluZ3MuZ2V0KGtleSk7XG5cdFx0XHRpZiAoYm91bmQpIHtcblx0XHRcdFx0cmV0dXJuIGJvdW5kO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEFuYWx5c2UgYSB3cmFwcGVkIGZ1bmN0aW9uJ3MgYm9keSBmb3IgZ3VhcmFudGVlZCBydW50aW1lIHBhdGhzOlxuXHQgKiBkaXZlIHdyYXBzIHJldHVybmVkIGZ1bmN0aW9ucyBhcyB3ZWxsIChyZWN1cnNpdmVseSksIHNvIGVhY2hcblx0ICogZnVuY3Rpb24tdmFsdWVkIHJldHVybiBpcyBhIG5lc3RlZCB3cmFwIHNpdGUsIGFuZCBlYWNoIGBuZXcgVHlwZSgpYFxuXHQgKiBpbnNpZGUgdGhlIGJvZHkgbWVhbnMgdGhlIHBhdGggaGl0cyB0aGF0IHR5cGUncyBjb25zdHJ1Y3RvciAod2hpY2hcblx0ICogYXR0YWNoSG9va3Mgd3JhcHMgdG9vKS4gQm90aCBmYWN0cyBhcmUgMTAwJSBlbnN1cmVkLCBzbyB0aGV5IGFyZVxuXHQgKiByZWNvcmRlZCBBb1QuIE5lc3RlZCBmdW5jdGlvbiBib2RpZXMgYXJlIE5PVCB3YWxrZWQgaGVyZSDigJQgdGhleVxuXHQgKiBiZWxvbmcgdG8gdGhlaXIgb3duIHdyYXAgYW5hbHlzaXMsIHJlYWNoZWQgdmlhIHRoZSByZXR1cm4gY2hhaW4uXG5cdCAqIERlcHRoLWNhcHBlZCBhbmQgY3ljbGUtZ3VhcmRlZC5cblx0ICovXG5cdHByaXZhdGUgYW5hbHl6ZVdyYXBwZWRCb2R5IChcblx0XHRmbjogdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb24sXG5cdFx0dmlhTG9jYXRpb246IHN0cmluZyxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdGRlcHRoOiBudW1iZXIsXG5cdFx0dmlzaXRlZDogU2V0PHRzLk5vZGU+LFxuXHRcdGNyZWF0ZXNUeXBlczogU2V0PHN0cmluZz4sXG5cdFx0ZmFsbGJhY2tTY29wZT86IHN0cmluZ1xuXHQpOiB2b2lkIHtcblx0XHRpZiAoZGVwdGggPiA1IHx8IHZpc2l0ZWQuaGFzKGZuKSB8fCAhZm4uYm9keSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR2aXNpdGVkLmFkZChmbik7XG5cblx0XHQvLyBBcnJvdyB3aXRoIGV4cHJlc3Npb24gYm9keTogaW1wbGljaXQgcmV0dXJuXG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihmbikgJiYgIXRzLmlzQmxvY2soZm4uYm9keSkpIHtcblx0XHRcdHRoaXMucmVjb3JkV3JhcHBlZFJldHVybihmbi5ib2R5LCB2aWFMb2NhdGlvbiwgc291cmNlRmlsZSwgZGVwdGgsIHZpc2l0ZWQsIGZhbGxiYWNrU2NvcGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHdhbGsgPSAobm9kZTogdHMuTm9kZSk6IHZvaWQgPT4ge1xuXHRcdFx0aWYgKG5vZGUgIT09IGZuLmJvZHkgJiYgKFxuXHRcdFx0XHR0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihub2RlKSB8fFxuXHRcdFx0XHR0cy5pc0Fycm93RnVuY3Rpb24obm9kZSkgfHxcblx0XHRcdFx0dHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKG5vZGUpIHx8XG5cdFx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24obm9kZSlcblx0XHRcdCkpIHtcblx0XHRcdFx0Ly8gbmVzdGVkIGZ1bmN0aW9uIGJvZGllcyBhcmUgYW5hbHlzZWQgdGhyb3VnaCB0aGUgcmV0dXJuIGNoYWluXG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRXcmFwcGVkUmV0dXJuKG5vZGUuZXhwcmVzc2lvbiwgdmlhTG9jYXRpb24sIHNvdXJjZUZpbGUsIGRlcHRoLCB2aXNpdGVkLCBmYWxsYmFja1Njb3BlKTtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc05ld0V4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdFx0Y29uc3QgY3JlYXRlZCA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbikgfHxcblx0XHRcdFx0XHQodHMuaXNJZGVudGlmaWVyKG5vZGUuZXhwcmVzc2lvbikgJiYgdGhpcy5kZWZpbml0aW9ucy5oYXMobm9kZS5leHByZXNzaW9uLnRleHQpXG5cdFx0XHRcdFx0XHQ/IG5vZGUuZXhwcmVzc2lvbi50ZXh0XG5cdFx0XHRcdFx0XHQ6IHVuZGVmaW5lZCk7XG5cdFx0XHRcdGlmIChjcmVhdGVkKSB7XG5cdFx0XHRcdFx0Y3JlYXRlc1R5cGVzLmFkZChjcmVhdGVkKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdFx0Y29uc3QgbmVzdGVkTmFtZSA9IHRoaXMuZ2V0RnVuY3Rpb25OYW1lKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHRcdGlmIChcblx0XHRcdFx0XHRuZXN0ZWROYW1lID09PSAnd3JhcCcgfHxcblx0XHRcdFx0XHRuZXN0ZWROYW1lID09PSAnd3JhcENvbnN0cnVjdG9yQXJnJyB8fFxuXHRcdFx0XHRcdG5lc3RlZE5hbWUgPT09ICd1cGdyYWRlQ29uc3RydWN0b3JBcmcnIHx8XG5cdFx0XHRcdFx0bmVzdGVkTmFtZSA9PT0gJ3dyYXBJbnN0YW5jZU1ldGhvZHMnXG5cdFx0XHRcdCkge1xuXHRcdFx0XHRcdC8vIHRoZSBuZXN0ZWQgY2FsbCBtYXkgYWxyZWFkeSBiZSBjb2xsZWN0ZWQgKHZpc2l0ZWRcblx0XHRcdFx0XHQvLyBiZWZvcmUgdGhpcyBvdXRlciB3cmFwIHNpdGUpIOKAlCBiYWNrLXBhdGNoIGl0cyBlbnRyeSxcblx0XHRcdFx0XHQvLyBvdGhlcndpc2UgbGVhdmUgdGhlIGxpbmsgKHdpdGggdGhpcyBzaXRlJ3Mgc2NvcGUpIGZvclxuXHRcdFx0XHRcdC8vIGNvbGxlY3RFRFMgdG8gcGljayB1cFxuXHRcdFx0XHRcdGNvbnN0IG5lc3RlZEVudHJ5ID0gdGhpcy53cmFwRW50cnlCeU5vZGUuZ2V0KG5vZGUpO1xuXHRcdFx0XHRcdGlmIChuZXN0ZWRFbnRyeSkge1xuXHRcdFx0XHRcdFx0bmVzdGVkRW50cnkudmlhID0gdmlhTG9jYXRpb247XG5cdFx0XHRcdFx0XHRpZiAobmVzdGVkRW50cnkuc2NvcGUgPT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRcdFx0XHRuZXN0ZWRFbnRyeS5zY29wZSA9IGZhbGxiYWNrU2NvcGU7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHRcdHRoaXMubmVzdGVkV3JhcFZpYS5zZXQobm9kZSwgeyB2aWEgOiB2aWFMb2NhdGlvbiwgc2NvcGUgOiBmYWxsYmFja1Njb3BlIH0pO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIHdhbGspO1xuXHRcdH07XG5cdFx0d2Fsayhmbi5ib2R5KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgb25lIGZ1bmN0aW9uLXZhbHVlZCByZXR1cm4gb2YgYSB3cmFwcGVkIGJvZHkgYXMgYSBuZXN0ZWQgd3JhcFxuXHQgKiBzaXRlIChgdmlhYCA9IHRoZSBzaXRlIHdob3NlIHdyYXBwaW5nIGNhdXNlZCBpdCkgYW5kIHJlY3Vyc2UgaW50b1xuXHQgKiBpdHMgb3duIHJldHVybnMuIFJldHVybnMgdGhyb3VnaCBpZGVudGlmaWVycyByZXNvbHZlIHRocm91Z2ggdGhlXG5cdCAqIHNhbWUtZmlsZSBiaW5kaW5ncyB0YWJsZTsgdW5yZXNvbHZhYmxlIHJldHVybnMgYXJlIHNpbXBseSBza2lwcGVkLlxuXHQgKiBBIHJldHVybiBkZWNsYXJlZCBvdXRzaWRlIGFueSB0eXBlIHNjb3BlIGluaGVyaXRzIHRoZSBjYXVzaW5nIHdyYXBcblx0ICogc2l0ZSdzIHNjb3BlIGF0dHJpYnV0aW9uICh0aGUgZ2VuZXJhdGlvbiBjaGFpbiBpcyB0aGUgb25seSBob2xkZXIpLlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmRXcmFwcGVkUmV0dXJuIChcblx0XHRleHByOiB0cy5FeHByZXNzaW9uLFxuXHRcdHZpYUxvY2F0aW9uOiBzdHJpbmcsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRkZXB0aDogbnVtYmVyLFxuXHRcdHZpc2l0ZWQ6IFNldDx0cy5Ob2RlPixcblx0XHRmYWxsYmFja1Njb3BlPzogc3RyaW5nXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IHJldHVybmVkID0gdGhpcy5yZXNvbHZlRnVuY3Rpb25Bcmd1bWVudChleHByLCBzb3VyY2VGaWxlKTtcblx0XHRpZiAoIXJldHVybmVkKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRyZXR1cm5lZC5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gcmV0dXJuZWQuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXHRcdGNvbnN0IHNjb3BlID0gdGhpcy5yZXNvbHZlRURTU2NvcGUocmV0dXJuZWQpID8/IGZhbGxiYWNrU2NvcGU7XG5cdFx0Y29uc3QgZW50cnkgPSB0aGlzLmFkZEVEUyhzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCA6ICd3cmFwJyxcblx0XHRcdGNvZGUsXG5cdFx0XHRzY29wZSxcblx0XHRcdHZpYSAgOiB2aWFMb2NhdGlvbixcblx0XHRcdC8vIGRpdmUgd3JhcHMgcmV0dXJuZWQgZnVuY3Rpb25zIHRocm91Z2ggdGhlIHNhbWUgd3JhcCBtYWNoaW5lcnlcblx0XHRcdGZuICAgOiAnd3JhcCcsXG5cdFx0fSk7XG5cdFx0Ly8gdGhlIHJldHVybmVkIGZ1bmN0aW9uJ3Mgb3duIHJldHVybnMgYXJlIHdyYXBwZWQgaW4gdHVybjsgYHZpYWBcblx0XHQvLyBjaGFpbnMgdG8gdGhpcyBuZXN0ZWQgZW50cnkncyBsb2NhdGlvblxuXHRcdGNvbnN0IG5lc3RlZENyZWF0ZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHR0aGlzLmFuYWx5emVXcmFwcGVkQm9keShyZXR1cm5lZCwgbG9jYXRpb24sIHNvdXJjZUZpbGUsIGRlcHRoICsgMSwgdmlzaXRlZCwgbmVzdGVkQ3JlYXRlcywgc2NvcGUpO1xuXHRcdGlmIChuZXN0ZWRDcmVhdGVzLnNpemUgPiAwKSB7XG5cdFx0XHRlbnRyeS5jcmVhdGVzVHlwZXMgPSBBcnJheS5mcm9tKG5lc3RlZENyZWF0ZXMpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBBZGQgYW4gRURTIHVzYWdlIHRvIHRoZSBjb2xsZWN0aW9uXG5cdCAqIFJldHVybnMgdGhlIHN0b3JlZCBlbnRyeSAodGhlIGV4aXN0aW5nIG9uZSB3aGVuIHRoaXMgaXMgYSBkdXBsaWNhdGUpLFxuXHQgKiBzbyBjYWxsZXJzIGNhbiBlbnJpY2ggaXQgYWZ0ZXIgbmVzdGVkIGJvZHkgYW5hbHlzaXMuXG5cdCAqL1xuXHRwcml2YXRlIGFkZEVEUyAodHlwZVBhdGg6IHN0cmluZywgaW5mbzogRURTSW5mbyk6IEVEU0luZm8ge1xuXHRcdGlmICghdGhpcy5lZHNVc2FnZXMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0dGhpcy5lZHNVc2FnZXMuc2V0KHR5cGVQYXRoLCBbXSk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZXhpc3RpbmcgPSB0aGlzLmVkc1VzYWdlcy5nZXQodHlwZVBhdGgpITtcblx0XHRjb25zdCBkdXBsaWNhdGUgPSBleGlzdGluZy5maW5kKGUgPT4ge1xuXHRcdFx0cmV0dXJuIGUubG9jYXRpb24gPT09IGluZm8ubG9jYXRpb24gJiZcblx0XHRcdFx0ZS5raW5kID09PSBpbmZvLmtpbmQgJiZcblx0XHRcdFx0ZS5jb2RlID09PSBpbmZvLmNvZGU7XG5cdFx0fSk7XG5cblx0XHRpZiAoZHVwbGljYXRlKSB7XG5cdFx0XHRyZXR1cm4gZHVwbGljYXRlO1xuXHRcdH1cblx0XHRleGlzdGluZy5wdXNoKGluZm8pO1xuXHRcdHJldHVybiBpbmZvO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgbmF0aXZlIGZsb3cgcGF0dGVybnMgKGluc3RhbmNlIHVzYWdlIGFmdGVyIGNyZWF0aW9uKVxuXHQgKiBQaGFzZSAxOiBwcm9wZXJ0eSBhY2Nlc3MsIG1ldGhvZCBjYWxscywgYXJndW1lbnRzLCByZXR1cm4sIGRlc3RydWN0dXJpbmcsIGV0Yy5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3cgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHQvLyBQcm9wZXJ0eSByZWFkOiB1c2VyLm5hbWUgb3IgdXNlcj8ubmFtZVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd1Byb3BlcnR5QWNjZXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEVsZW1lbnQgYWNjZXNzOiB1c2VyWyduYW1lJ11cblx0XHRpZiAodHMuaXNFbGVtZW50QWNjZXNzRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0VsZW1lbnRBY2Nlc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgd3JpdGU6IHVzZXIubmFtZSA9IHZhbHVlXG5cdFx0aWYgKHRzLmlzQmluYXJ5RXhwcmVzc2lvbihub2RlKSAmJiBub2RlLm9wZXJhdG9yVG9rZW4ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0Fzc2lnbm1lbnQobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gTWV0aG9kIGNhbGw6IHVzZXIudmFsaWRhdGUoKSAgQU5EICBhcmd1bWVudCBwYXNzaW5nOiBwcm9jZXNzVXNlcih1c2VyKVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd01ldGhvZENhbGwobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93QXJndW1lbnRQYXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIERlc3RydWN0dXJlIHJlYWQ6IGNvbnN0IHsgbmFtZSB9ID0gdXNlclxuXHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgJiYgbm9kZS5pbml0aWFsaXplcikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0Rlc3RydWN0dXJlKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFJldHVybiBpbnN0YW5jZTogcmV0dXJuIHVzZXJcblx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQobm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93UmV0dXJuKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFNwcmVhZDogeyAuLi51c2VyIH1cblx0XHRpZiAodHMuaXNTcHJlYWRFbGVtZW50KG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93U3ByZWFkKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IHByb3BlcnR5IGFjY2VzcyBmbG93IChyZWFkIG9yIGNvbmRpdGlvbmFsKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd1Byb3BlcnR5QWNjZXNzIChub2RlOiB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBwcm9wTmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIFNraXAgaWYgdGhpcyBpcyBhIHR5cGUgY29uc3RydWN0b3IgYWNjZXNzIChlLmcuLCBVc2VyVHlwZS5kZWZpbmUpXG5cdFx0aWYgKHByb3BOYW1lID09PSAnZGVmaW5lJyB8fCBwcm9wTmFtZSA9PT0gJ2xhenknKSB7IHJldHVybjsgfVxuXG5cdFx0dGhpcy5hZGRGbG93KG9iamVjdFR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICAgIDogJ3Byb3BlcnR5UmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0cHJvcGVydHlOYW1lIDogcHJvcE5hbWUsXG5cdFx0XHR0YXJnZXRUeXBlICAgOiBvYmplY3RUeXBlXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBlbGVtZW50IGFjY2VzcyBmbG93OiB1c2VyWyduYW1lJ11cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dFbGVtZW50QWNjZXNzIChub2RlOiB0cy5FbGVtZW50QWNjZXNzRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnZWxlbWVudEFjY2VzcycsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGFzc2lnbm1lbnQgZmxvdzogdXNlci5uYW1lID0gdmFsdWUgb3IgdXNlciA9IG90aGVyXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93QXNzaWdubWVudCAobm9kZTogdHMuQmluYXJ5RXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIFByb3BlcnR5IHdyaXRlOiB1c2VyLm5hbWUgPSB2YWx1ZVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmxlZnQpKSB7XG5cdFx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5sZWZ0LmV4cHJlc3Npb24pO1xuXHRcdFx0aWYgKCFvYmplY3RUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0XHRjb25zdCBwcm9wTmFtZSA9IG5vZGUubGVmdC5uYW1lLnRleHQ7XG5cdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdCk7XG5cdFx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCAgICAgICAgIDogJ3Byb3BlcnR5V3JpdGUnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRwcm9wZXJ0eU5hbWUgOiBwcm9wTmFtZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSAgIDogb2JqZWN0VHlwZVxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gVmFyaWFibGUgcmVhc3NpZ25tZW50OiB1c2VyID0gb3RoZXJcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG5vZGUubGVmdCkpIHtcblx0XHRcdGNvbnN0IHZhck5hbWUgPSBub2RlLmxlZnQudGV4dDtcblx0XHRcdGNvbnN0IG1hcHBlZFR5cGUgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldCh2YXJOYW1lKTtcblx0XHRcdGlmICghbWFwcGVkVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHQpO1xuXHRcdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdFx0dGhpcy5hZGRGbG93KG1hcHBlZFR5cGUsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAncmVhc3NpZ25tZW50Jyxcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSA6IG1hcHBlZFR5cGVcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IG1ldGhvZCBjYWxsIGZsb3c6IHVzZXIudmFsaWRhdGUoKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd01ldGhvZENhbGwgKG5vZGU6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3Qgb2JqZWN0VHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbi5leHByZXNzaW9uKTtcblx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBtZXRob2ROYW1lID0gbm9kZS5leHByZXNzaW9uLm5hbWUudGV4dDtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHQvLyBTa2lwIGlmIHRoaXMgaXMgYSB0eXBlIGNvbnN0cnVjdG9yIGNhbGwgKGUuZy4sIG5ldyBVc2VyVHlwZSgpKVxuXHRcdGlmIChtZXRob2ROYW1lID09PSAnZGVmaW5lJyB8fCBtZXRob2ROYW1lID09PSAnbGF6eScpIHsgcmV0dXJuOyB9XG5cblx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgICAgOiAnbWV0aG9kQ2FsbCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0cHJvcGVydHlOYW1lIDogbWV0aG9kTmFtZSxcblx0XHRcdHRhcmdldFR5cGUgICA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGFyZ3VtZW50IHBhc3NpbmcgZmxvdzogcHJvY2Vzc1VzZXIodXNlcilcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dBcmd1bWVudFBhc3MgKG5vZGU6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuXHRcdFx0Y29uc3QgYXJnID0gbm9kZS5hcmd1bWVudHNbIGkgXTtcblx0XHRcdGNvbnN0IGFyZ1R5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShhcmcpO1xuXHRcdFx0aWYgKCFhcmdUeXBlKSB7IGNvbnRpbnVlOyB9XG5cblx0XHRcdGNvbnN0IGZ1bmNOYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKSB8fCAnYW5vbnltb3VzJztcblx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0KTtcblx0XHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRcdHRoaXMuYWRkRmxvdyhhcmdUeXBlLCB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgIDogJ3Bhc3NBc0FyZycsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHRhcmdldFR5cGUgOiBhcmdUeXBlLFxuXHRcdFx0XHRjb250ZXh0ICAgIDogYGFyZyAke2l9IHRvICR7ZnVuY05hbWV9YFxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgZGVzdHJ1Y3R1cmluZyBmbG93OiBjb25zdCB7IG5hbWUgfSA9IHVzZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dEZXN0cnVjdHVyZSAobm9kZTogdHMuVmFyaWFibGVEZWNsYXJhdGlvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNPYmplY3RCaW5kaW5nUGF0dGVybihub2RlLm5hbWUpKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3Qgc291cmNlVHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuaW5pdGlhbGl6ZXIhKTtcblx0XHRpZiAoIXNvdXJjZVR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHQvLyBFeHRyYWN0IGRlc3RydWN0dXJlZCBwcm9wZXJ0eSBuYW1lc1xuXHRcdGNvbnN0IHByb3BzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBub2RlLm5hbWUuZWxlbWVudHMpIHtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZWxlbWVudC5uYW1lKSkge1xuXHRcdFx0XHRwcm9wcy5wdXNoKGVsZW1lbnQubmFtZS50ZXh0KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHR0aGlzLmFkZEZsb3coc291cmNlVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ2Rlc3RydWN0dXJlUmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHNvdXJjZVR5cGUsXG5cdFx0XHRjb250ZXh0ICAgIDogcHJvcHMuam9pbignLCAnKVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgcmV0dXJuIGZsb3c6IHJldHVybiB1c2VyXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93UmV0dXJuIChub2RlOiB0cy5SZXR1cm5TdGF0ZW1lbnQsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCByZXR1cm5UeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uISk7XG5cdFx0aWYgKCFyZXR1cm5UeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0dGhpcy5hZGRGbG93KHJldHVyblR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICA6ICdyZXR1cm4nLFxuXHRcdFx0Y29kZSxcblx0XHRcdHRhcmdldFR5cGUgOiByZXR1cm5UeXBlXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBzcHJlYWQgZmxvdzogeyAuLi51c2VyIH1cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dTcHJlYWQgKG5vZGU6IHRzLlNwcmVhZEVsZW1lbnQsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCBzcHJlYWRUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIXNwcmVhZFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHR0aGlzLmFkZEZsb3coc3ByZWFkVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ3NwcmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHNwcmVhZFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHR5cGUgZnJvbSBhbiBleHByZXNzaW9uIChpZGVudGlmaWVyLCBwcm9wZXJ0eSBhY2Nlc3MsIGV0Yy4pXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVFeHByZXNzaW9uVHlwZSAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gSWRlbnRpZmllcjogdXNlclxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChleHByLnRleHQpO1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2VzczogdXNlci5uYW1lIChyZXR1cm4gb2JqZWN0IHR5cGUsIG5vdCBwcm9wZXJ0eSB0eXBlKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKGV4cHIuZXhwcmVzc2lvbik7XG5cdFx0fVxuXG5cdFx0Ly8gRWxlbWVudCBhY2Nlc3M6IHVzZXJbJ25hbWUnXVxuXHRcdGlmICh0cy5pc0VsZW1lbnRBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUoZXhwci5leHByZXNzaW9uKTtcblx0XHR9XG5cblx0XHQvLyBUaGlzIGV4cHJlc3Npb246IHRoaXMgKGlmIGluIGEgbWV0aG9kLCB3ZSBjYW4ndCByZXNvbHZlIHdpdGhvdXQgbW9yZSBjb250ZXh0KVxuXHRcdGlmIChleHByLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBBZGQgYSBmbG93IHVzYWdlIHRvIHRoZSBjb2xsZWN0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGFkZEZsb3cgKHR5cGVQYXRoOiBzdHJpbmcsIGluZm86IEZsb3dJbmZvKTogdm9pZCB7XG5cdFx0aWYgKCF0aGlzLmZsb3dVc2FnZXMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0dGhpcy5mbG93VXNhZ2VzLnNldCh0eXBlUGF0aCwgW10pO1xuXHRcdH1cblxuXHRcdGNvbnN0IGV4aXN0aW5nID0gdGhpcy5mbG93VXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGlzRHVwbGljYXRlID0gZXhpc3Rpbmcuc29tZShlID0+IHtcblx0XHRcdHJldHVybiBlLmxvY2F0aW9uID09PSBpbmZvLmxvY2F0aW9uICYmXG5cdFx0XHRcdGUua2luZCA9PT0gaW5mby5raW5kICYmXG5cdFx0XHRcdGUuY29kZSA9PT0gaW5mby5jb2RlO1xuXHRcdH0pO1xuXG5cdFx0aWYgKCFpc0R1cGxpY2F0ZSkge1xuXHRcdFx0ZXhpc3RpbmcucHVzaChpbmZvKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHRcdCogR2V0IHR5cGUgbmFtZSBmcm9tIGV4cHJlc3Npb24gKGlkZW50aWZpZXIgb3IgcHJvcGVydHkgYWNjZXNzKVxuXHRcdFx0Ki9cblx0cHJpdmF0ZSBnZXRUeXBlTmFtZUZyb21FeHByZXNzaW9uIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBuYW1lID0gZXhwci50ZXh0O1xuXHRcdFx0Ly8gQ2hlY2sgaWYgdGhpcyBpZGVudGlmaWVyIGlzIGEgdmFyaWFibGUgbWFwcGVkIHRvIGEgdHlwZSAoZS5nLiwgZnJvbSBsb29rdXApXG5cdFx0XHRjb25zdCBtYXBwZWRUeXBlID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0XHRpZiAobWFwcGVkVHlwZSkge1xuXHRcdFx0XHRyZXR1cm4gbWFwcGVkVHlwZTtcblx0XHRcdH1cblx0XHRcdHJldHVybiBuYW1lO1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKGV4cHIpO1xuXHRcdFx0cmV0dXJuIGNoYWluLmpvaW4oJy4nKTtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXHRcblx0LyoqXG5cdCAqIFRoZSBvbmUgY2FuZGlkYXRlIHdob3NlIHBhcmVudCB0eXBlIGlzIGRlZmluZWQgaW4gYGZpbGVOYW1lYCwgb3Jcblx0ICogdW5kZWZpbmVkIHdoZW4gbm9uZSBvciBzZXZlcmFsIHF1YWxpZnkuXG5cdCAqL1xuXHRwcml2YXRlIHN1YnR5cGVPd25lZEJ5RmlsZSAoY2FuZGlkYXRlczogc3RyaW5nW10sIGZpbGVOYW1lOiBzdHJpbmcpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGZpbGUgPSBub2RlUGF0aC5yZXNvbHZlKGZpbGVOYW1lKTtcblx0XHRjb25zdCBvd25lZCA9IGNhbmRpZGF0ZXMuZmlsdGVyKChjYW5kaWRhdGUpID0+IHtcblx0XHRcdGNvbnN0IHBhcmVudCA9IHRoaXMuZGVmaW5pdGlvbnMuZ2V0KGNhbmRpZGF0ZSk/LnBhcmVudDtcblx0XHRcdGNvbnN0IHBhcmVudExvY2F0aW9uID0gcGFyZW50ID8gdGhpcy5kZWZpbml0aW9ucy5nZXQocGFyZW50KT8ubG9jYXRpb24gOiB1bmRlZmluZWQ7XG5cdFx0XHRjb25zdCBwYXJlbnRGaWxlID0gcGFyZW50TG9jYXRpb24gPyBwYXJlbnRMb2NhdGlvbi5yZXBsYWNlKC86XFxkKzpcXGQrJC8sICcnKSA6IHVuZGVmaW5lZDtcblx0XHRcdGNvbnN0IGluRmlsZSA9IHBhcmVudEZpbGUgIT09IHVuZGVmaW5lZCAmJiBub2RlUGF0aC5yZXNvbHZlKHBhcmVudEZpbGUpID09PSBmaWxlO1xuXHRcdFx0cmV0dXJuIGluRmlsZTtcblx0XHR9KTtcblx0XHRjb25zdCByZXN1bHQgPSBvd25lZC5sZW5ndGggPT09IDEgPyBvd25lZFsgMCBdIDogdW5kZWZpbmVkO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHRcdCogUmVzb2x2ZSBmdWxsIHR5cGUgcGF0aCBmcm9tIHByb3BlcnR5IGFjY2Vzc1xuXHRcdFx0Ki9cblx0cHJpdmF0ZSByZXNvbHZlVHlwZVBhdGggKGV4cHI6IHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4oZXhwcik7XG5cdFx0aWYgKGNoYWluLmxlbmd0aCA9PT0gMCkgcmV0dXJuIHVuZGVmaW5lZDtcblx0XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBjaGFpbiBtYXRjaGVzIGEga25vd24gdHlwZVxuXHRcdGNvbnN0IGZ1bGxQYXRoID0gY2hhaW4uam9pbignLicpO1xuXHRcdGlmICh0aGlzLmRlZmluaXRpb25zLmhhcyhmdWxsUGF0aCkpIHtcblx0XHRcdHJldHVybiBmdWxsUGF0aDtcblx0XHR9XG5cdFxuXHRcdC8vIEluc3RhbmNlIHJlY2VpdmVyOiBgbGVzc29uLk5hdGl2ZWAgd2hlcmUgYGxlc3NvbmAgaXMgYm91bmQgdG8gYVxuXHRcdC8vIFJ1bi5MZXNzb24gaW5zdGFuY2UgbWVhbnMgUnVuLkxlc3Nvbi5OYXRpdmUg4oCUIHJlc29sdmUgdGhyb3VnaCB0aGVcblx0XHQvLyB2YXJpYWJsZSdzIHR5cGUgYmVmb3JlIGZhbGxpbmcgYmFjayB0byB0aGUgYmFyZSBuYW1lXG5cdFx0aWYgKGNoYWluLmxlbmd0aCA+IDEpIHtcblx0XHRcdGNvbnN0IHJlY2VpdmVyVHlwZSA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGNoYWluWyAwIF0pO1xuXHRcdFx0Y29uc3QgdmlhUmVjZWl2ZXIgPSByZWNlaXZlclR5cGUgPyBgJHtyZWNlaXZlclR5cGV9LiR7Y2hhaW4uc2xpY2UoMSkuam9pbignLicpfWAgOiB1bmRlZmluZWQ7XG5cdFx0XHRpZiAodmlhUmVjZWl2ZXIgJiYgdGhpcy5kZWZpbml0aW9ucy5oYXModmlhUmVjZWl2ZXIpKSB7XG5cdFx0XHRcdHJldHVybiB2aWFSZWNlaXZlcjtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBUcnkganVzdCB0aGUgcHJvcGVydHkgbmFtZVxuXHRcdGNvbnN0IHByb3BOYW1lID0gY2hhaW5bIGNoYWluLmxlbmd0aCAtIDEgXTtcblx0XHRjb25zdCBjYW5kaWRhdGVzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgWyBwYXRoIF0gb2YgdGhpcy5kZWZpbml0aW9ucykge1xuXHRcdFx0aWYgKHBhdGguZW5kc1dpdGgoYC4ke3Byb3BOYW1lfWApIHx8IHBhdGggPT09IHByb3BOYW1lKSB7XG5cdFx0XHRcdGNhbmRpZGF0ZXMucHVzaChwYXRoKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0Ly8gU2V2ZXJhbCB0eXBlcyBzaGFyZSB0aGUgbmFtZSAoQ29ycmVjdC5TdGF0VXBkYXRlIGFuZFxuXHRcdC8vIE1pc3Rha2UuU3RhdFVwZGF0ZSk6IGBuZXcgdGhpcy5TdGF0VXBkYXRlKClgIGluc2lkZSBhIHR5cGUncyBvd25cblx0XHQvLyBmaWxlIG1lYW5zIFRIQVQgdHlwZSdzIHN1YnR5cGUg4oCUIHByZWZlciB0aGUgY2FuZGlkYXRlIHdob3NlIHBhcmVudFxuXHRcdC8vIGlzIGRlZmluZWQgaW4gdGhlIGZpbGUgdGhlIGFjY2VzcyBzaXRzIGluICh0b3BvbG9naWNhOiBvbmUgZmlsZVxuXHRcdC8vIHBlciB0eXBlKS4gT3RoZXJ3aXNlIHRoZSBmaXJzdCBtYXRjaCwgYXMgYmVmb3JlLlxuXHRcdGlmIChjYW5kaWRhdGVzLmxlbmd0aCA+IDEpIHtcblx0XHRcdGNvbnN0IG93bmVkID0gdGhpcy5zdWJ0eXBlT3duZWRCeUZpbGUoY2FuZGlkYXRlcywgZXhwci5nZXRTb3VyY2VGaWxlKCkuZmlsZU5hbWUpO1xuXHRcdFx0aWYgKG93bmVkKSB7XG5cdFx0XHRcdHJldHVybiBvd25lZDtcblx0XHRcdH1cblx0XHR9XG5cdFx0aWYgKGNhbmRpZGF0ZXMubGVuZ3RoID4gMCkge1xuXHRcdFx0cmV0dXJuIGNhbmRpZGF0ZXNbIDAgXTtcblx0XHR9XG5cblx0XHRyZXR1cm4gZnVsbFBhdGg7XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0ICogQ2hlY2sgaWYgYSBuYW1lIGxvb2tzIGxpa2UgYSB0eXBlIChzdGFydHMgd2l0aCB1cHBlcmNhc2UpXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBpc0xpa2VseVR5cGVOYW1lIChuYW1lOiBzdHJpbmcpOiBib29sZWFuIHtcblx0XHRyZXR1cm4gbmFtZVsgMCBdID49ICdBJyAmJiBuYW1lWyAwIF0gPD0gJ1onO1xuXHR9XG5cdFxuXHQvKipcblx0XHRcdCAqIFJlc29sdmUgYSBjb25zdHJ1Y3RvciBwYXJhbWV0ZXIgdHlwZSwgZXhwYW5kaW5nIGlubGluZSBvYmplY3QgbGl0ZXJhbHNcblx0XHRcdCAqIGFuZCB0eXBlIGFsaWFzZXMgd2hlcmUgcG9zc2libGUuXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlQ29uc3RydWN0b3JQYXJhbVR5cGUgKHR5cGVOb2RlOiB0cy5UeXBlTm9kZSB8IHVuZGVmaW5lZCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCF0eXBlTm9kZSkgcmV0dXJuIHVuZGVmaW5lZDtcblxuXHRcdC8vIERpcmVjdCBpbmxpbmUgdHlwZSBsaXRlcmFsOiB7IHByb3A6IHR5cGUgfVxuXHRcdGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZSh0eXBlTm9kZSkpIHtcblx0XHRcdGNvbnN0IHByb3BzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgdHlwZU5vZGUubWVtYmVycykge1xuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Y29uc3Qgb3B0aW9uYWwgPSBtZW1iZXIucXVlc3Rpb25Ub2tlbiA/ICc/JyA6ICcnO1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0cHJvcHMucHVzaChgJHtwcm9wTmFtZX0ke29wdGlvbmFsfTogJHt0eXBlfWApO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gYHsgJHtwcm9wcy5qb2luKCc7ICcpfSB9YDtcblx0XHR9XG5cblx0XHQvLyBUeXBlIHJlZmVyZW5jZTogdXNhZ2UsIFVzZXJEYXRhLCBldGMuIC0gcmVzb2x2ZSBpbXBvcnQtYXdhcmUgYW5kXG5cdFx0Ly8gZXhwYW5kIHRoZSByZWZlcmVuY2VkIGRlY2xhcmF0aW9uIHdoZXJlIHBvc3NpYmxlIChGMTApXG5cdFx0aWYgKHRzLmlzVHlwZVJlZmVyZW5jZU5vZGUodHlwZU5vZGUpICYmIHRzLmlzSWRlbnRpZmllcih0eXBlTm9kZS50eXBlTmFtZSkpIHtcblx0XHRcdGNvbnN0IHR5cGVOYW1lID0gdHlwZU5vZGUudHlwZU5hbWUudGV4dDtcblx0XHRcdGNvbnN0IGRlY2wgPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKHR5cGVOYW1lLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0aWYgKGRlY2wpIHtcblx0XHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oZGVjbCk7XG5cdFx0XHRcdGlmIChleHBhbmRlZCkgcmV0dXJuIGV4cGFuZGVkO1xuXHRcdFx0fVxuXHRcdFx0Ly8gbW5lbW9uaWNhIGdyYXBoIHR5cGVzIGtlZXAgdGhlaXIgc2ltcGxlIG5hbWUg4oCUIHRoZSBnZW5lcmF0b3Jcblx0XHRcdC8vIHVwZ3JhZGVzIHRoZW0gdG8gZnVsbC1wYXRoIGluc3RhbmNlIHR5cGUgbmFtZXMuIFJlc29sdXRpb24gaXNcblx0XHRcdC8vIHBhdGgtYXdhcmUgKGhhcmQtZmFpbCBsYXcpOiBhbWJpZ3VpdHkgYmV0d2VlbiByZWFsIGdyYXBoIHR5cGVzXG5cdFx0XHQvLyByZWNvcmRzIGEgZmF0YWwgZXJyb3IgaW5zdGVhZCBvZiBzaWxlbnRseSBwaWNraW5nIG9uZS5cblx0XHRcdGNvbnN0IGdyYXBoUmVzdWx0ID0gdGhpcy5yZXNvbHZlR3JhcGhUeXBlTmFtZSh0eXBlTmFtZSk7XG5cdFx0XHRpZiAoZ3JhcGhSZXN1bHQuc3RhdHVzID09PSAndW5pcXVlJykge1xuXHRcdFx0XHRjb25zdCBzaW1wbGVSZXN1bHQgPSB0eXBlTmFtZTtcblx0XHRcdFx0cmV0dXJuIHNpbXBsZVJlc3VsdDtcblx0XHRcdH1cblx0XHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkR3JhcGhSZWZlcmVuY2VFcnJvcih0eXBlTmFtZSwgdHlwZU5vZGUsIGdyYXBoUmVzdWx0KTtcblx0XHRcdFx0Y29uc3QgdW5rbm93bkdyYXBoUmVzdWx0ID0gJ3Vua25vd24nO1xuXHRcdFx0XHRyZXR1cm4gdW5rbm93bkdyYXBoUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0Ly8gSWYgbm90IGFuIG9iamVjdCB0eXBlIGFsaWFzLCByZXR1cm4gdGhlIHR5cGUgbmFtZSB3aXRoIGFyZ3Ncblx0XHRcdGlmICh0eXBlTm9kZS50eXBlQXJndW1lbnRzICYmIHR5cGVOb2RlLnR5cGVBcmd1bWVudHMubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRpZiAoS05PV05fR0xPQkFMX1RZUEVTLmhhcyh0eXBlTmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBhcmdzID0gdHlwZU5vZGUudHlwZUFyZ3VtZW50cy5tYXAoYXJnID0+IHRoaXMuaW5mZXJUeXBlKGFyZykpO1xuXHRcdFx0XHRcdHJldHVybiBgJHt0eXBlTmFtZSAgfTwkeyAgYXJncy5qb2luKCcsICcpICB9PmA7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gZ2VuZXJpYyByZWZlcmVuY2UgdG8gYSBub24tZ2xvYmFsLCBub24tZ3JhcGggdHlwZSBjYW5ub3QgYmVcblx0XHRcdFx0Ly8gZW1pdHRlZCBiYXJlIGludG8gdGhlIGdlbmVyYXRlZCBmaWxlXG5cdFx0XHRcdHRoaXMucmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSh0eXBlTmFtZSwgdHlwZU5vZGUpO1xuXHRcdFx0XHRjb25zdCB1bmtub3duR2VuZXJpY1Jlc3VsdCA9ICd1bmtub3duJztcblx0XHRcdFx0cmV0dXJuIHVua25vd25HZW5lcmljUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZmFsbGJhY2tSZXN1bHQgPSB0aGlzLnVucmVzb2x2ZWRUeXBlUmVmZXJlbmNlRmFsbGJhY2sodHlwZU5hbWUsIHR5cGVOb2RlKTtcblx0XHRcdHJldHVybiBmYWxsYmFja1Jlc3VsdDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBhIGNsYXNzLWxpa2Ugbm9kZS5cblx0XHRcdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDbGFzc0NvbnN0cnVjdG9yUGFyYW1zIChjbGFzc0xpa2U6IHRzLkNsYXNzRGVjbGFyYXRpb24gfCB0cy5DbGFzc0V4cHJlc3Npb24pOlxuXHRcdENvbnN0cnVjdG9yUGFyYW1JbmZvW10ge1xuXHRcdGNvbnN0IHBhcmFtczogQ29uc3RydWN0b3JQYXJhbUluZm9bXSA9IFtdO1xuXG5cdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgY2xhc3NMaWtlLm1lbWJlcnMpIHtcblx0XHRcdGlmICghdHMuaXNDb25zdHJ1Y3RvckRlY2xhcmF0aW9uKG1lbWJlcikpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cblx0XHRcdGZvciAoY29uc3QgcGFyYW0gb2YgbWVtYmVyLnBhcmFtZXRlcnMpIHtcblx0XHRcdFx0aWYgKCFwYXJhbS5uYW1lIHx8ICF0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkpIGNvbnRpbnVlO1xuXHRcdFx0XHRpZiAoIXBhcmFtLnR5cGUpIGNvbnRpbnVlO1xuXG5cdFx0XHRcdGNvbnN0IHBhcmFtTmFtZSA9IHBhcmFtLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgZXhwYW5kZWRUeXBlID0gdGhpcy5yZXNvbHZlQ29uc3RydWN0b3JQYXJhbVR5cGUocGFyYW0udHlwZSkgfHwgdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cblx0XHRcdFx0cGFyYW1zLnB1c2goe1xuXHRcdFx0XHRcdG5hbWUgICAgIDogcGFyYW1OYW1lLFxuXHRcdFx0XHRcdHR5cGUgICAgIDogZXhwYW5kZWRUeXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogISFwYXJhbS5xdWVzdGlvblRva2VuIHx8ICEhcGFyYW0uaW5pdGlhbGl6ZXIsXG5cdFx0XHRcdFx0Ly8gcmVzdCBtYXJrZXIgZm9yIHRoZSBkZWZpbml0aW9ucy5qc29uIGFyZ3MgY29udHJhY3Rcblx0XHRcdFx0XHQuLi4ocGFyYW0uZG90RG90RG90VG9rZW4gPyB7IGtpbmQgOiAncmVzdCcgYXMgY29uc3QgfSA6IHt9KVxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHRcdC8vIE9ubHkgcHJvY2VzcyBmaXJzdCBjb25zdHJ1Y3RvclxuXHRcdFx0YnJlYWs7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHBhcmFtcztcblx0fVxuXG5cdC8qKlxuXHRcdFx0ICogRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZyb20gZGVmaW5lKCkgY2FsbFxuXHRcdFx0ICogVGhpcyBpcyB1c2VkIGZvciBUeXBlUmVnaXN0cnkgY29uc3RydWN0b3Igc2lnbmF0dXJlc1xuXHRcdFx0ICogUHJlc2VydmVzIHBhcmFtZXRlciBuYW1lcyBhbmQgZXhwYW5kcyBvYmplY3QgdHlwZXMgdG8gdGhlaXIgc3RydWN0dXJlXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JQYXJhbXMgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogQ29uc3RydWN0b3JQYXJhbUluZm9bXSB7XG5cdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpO1xuXHRcdGlmICghY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRyZXR1cm4gW107XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zRnJvbUNvbnN0cnVjdG9yKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHRcdFx0ICogRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZyb20gYSBjb25zdHJ1Y3RvciBleHByZXNzaW9uLlxuXHRcdFx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zRnJvbUNvbnN0cnVjdG9yIChjb25zdHJ1Y3RvckV4cHI6IHRzLkV4cHJlc3Npb24pOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdIHtcblx0XHRjb25zdCBwYXJhbXM6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10gPSBbXTtcblx0XG5cdFx0Ly8gSGFuZGxlIGZ1bmN0aW9uIGV4cHJlc3Npb24gb3IgYXJyb3cgZnVuY3Rpb25cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSB8fCB0cy5pc0Fycm93RnVuY3Rpb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Ly8gTG9vayBmb3IgY29uc3RydWN0b3IgcGFyYW1ldGVycyAoc2Vjb25kIHBhcmFtIGFmdGVyIGB0aGlzYClcblx0XHRcdC8vIFBhdHRlcm5zOiBmdW5jdGlvbih0aGlzOiBUeXBlLCBkYXRhOiB7IC4uLiB9KSBvciAodGhpczogVHlwZSwgZGF0YTogeyAuLi4gfSkgPT5cblx0XHRcdGZvciAobGV0IGkgPSAwOyBpIDwgY29uc3RydWN0b3JFeHByLnBhcmFtZXRlcnMubGVuZ3RoOyBpKyspIHtcblx0XHRcdFx0Y29uc3QgcGFyYW0gPSBjb25zdHJ1Y3RvckV4cHIucGFyYW1ldGVyc1sgaSBdO1xuXHRcdFx0XHRpZiAoIXBhcmFtLnR5cGUpIGNvbnRpbnVlO1xuXHRcblx0XHRcdFx0Ly8gU2tpcCBgdGhpc2AgcGFyYW1ldGVyIChmaXJzdCBwYXJhbSlcblx0XHRcdFx0aWYgKFxuXHRcdFx0XHRcdGkgPT09IDAgJiZcblx0XHRcdFx0XHRwYXJhbS5uYW1lLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuSWRlbnRpZmllciAmJlxuXHRcdFx0XHRcdChwYXJhbS5uYW1lIGFzIHRzLklkZW50aWZpZXIpLnRleHQgPT09ICd0aGlzJ1xuXHRcdFx0XHQpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcblx0XHRcdFx0Ly8gR2V0IHBhcmFtZXRlciBuYW1lIGFuZCBleHBhbmQgaXRzIHR5cGVcblx0XHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpID8gcGFyYW0ubmFtZS50ZXh0IDogJ2FyZyc7XG5cdFx0XHRcdGNvbnN0IGV4cGFuZGVkVHlwZSA9IHRoaXMucmVzb2x2ZUNvbnN0cnVjdG9yUGFyYW1UeXBlKHBhcmFtLnR5cGUpIHx8IHRoaXMuaW5mZXJUeXBlKHBhcmFtLnR5cGUpO1xuXHRcdFx0XHRcdFxuXHRcdFx0XHRwYXJhbXMucHVzaCh7XG5cdFx0XHRcdFx0bmFtZSAgICAgOiBwYXJhbU5hbWUsXG5cdFx0XHRcdFx0dHlwZSAgICAgOiBleHBhbmRlZFR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiAhIXBhcmFtLnF1ZXN0aW9uVG9rZW4gfHwgISFwYXJhbS5pbml0aWFsaXplcixcblx0XHRcdFx0XHQvLyByZXN0IG1hcmtlciBmb3IgdGhlIGRlZmluaXRpb25zLmpzb24gYXJncyBjb250cmFjdFxuXHRcdFx0XHRcdC4uLihwYXJhbS5kb3REb3REb3RUb2tlbiA/IHsga2luZCA6ICdyZXN0JyBhcyBjb25zdCB9IDoge30pXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0Ly8gSGFuZGxlIGNsYXNzIGV4cHJlc3Npb24gLSBjaGVjayBjb25zdHJ1Y3RvciBtZXRob2Rcblx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Y29uc3QgY2xhc3NQYXJhbXMgPSB0aGlzLmV4dHJhY3RDbGFzc0NvbnN0cnVjdG9yUGFyYW1zKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGNsYXNzUGFyYW1zKSB7XG5cdFx0XHRcdHBhcmFtcy5wdXNoKHBhcmFtKTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcGFyYW1zO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgZnJhbWV3b3JrIGluc3RydW1lbnRhdGlvbiBwb2ludHMuIFB1cmVseSBzeW50YWN0aWM6IGhlcml0YWdlXG5cdCAqIGNsYXVzZXMsIGRlY29yYXRvciBhcHBsaWNhdGlvbiBzaXRlcywgcHJvdmlkZXItdG9rZW4gb2JqZWN0IGxpdGVyYWxzXG5cdCAqIGFuZCBjb25zdW1lci5hcHBseSgpLmZvclJvdXRlcygpIHdpcmluZy4gVGhlIHZvY2FidWxhcnkgY29tZXMgZnJvbVxuXHQgKiBwbHVnaW5zOyBpZGVudGlmaWVyIHRleHQgaXMgbWF0Y2hlZCBhcy1pcyDigJQgbm8gaW1wb3J0IHJlc29sdXRpb24sXG5cdCAqIHRoZSB0eXBlIGNoZWNrZXIgc3RheXMgdW51c2VkLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0SW5zdHJ1bWVudGF0aW9uIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbkNsYXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0XHRpZiAodHMuaXNEZWNvcmF0b3Iobm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbkRlY29yYXRvcihub2RlLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cdFx0aWYgKHRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvblByb3ZpZGVyKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uTWlkZGxld2FyZShub2RlLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGEgbmFtZWQgY2xhc3MgZGVjbGFyYXRpb24gZm9yIGluc3RydW1lbnRhdGlvbiBzaXRlIHJlc29sdXRpb25cblx0ICogYW5kIGRldGVjdCBoZXJpdGFnZS1iYXNlZCBraW5kcyAoYGltcGxlbWVudHMgPHBsdWdpbiBpbnRlcmZhY2U+YClcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEluc3RydW1lbnRhdGlvbkNsYXNzIChub2RlOiB0cy5DbGFzc0RlY2xhcmF0aW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCFub2RlLm5hbWUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgY2xhc3NOYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUubmFtZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHQvLyBGaXJzdCBsaW5lIG9mIHRoZSBkZWNsYXJhdGlvbiwgbGlrZSBFRFMgYGNvZGVgIHNuaXBwZXRzXG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zcGxpdCgnXFxuJylbIDAgXS5zbGljZSgwLCAxMDApO1xuXG5cdFx0bGV0IGtpbmQ6IEluc3RydW1lbnRhdGlvbktpbmQgfCB1bmRlZmluZWQ7XG5cdFx0aWYgKG5vZGUuaGVyaXRhZ2VDbGF1c2VzKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGNsYXVzZSBvZiBub2RlLmhlcml0YWdlQ2xhdXNlcykge1xuXHRcdFx0XHRpZiAoY2xhdXNlLnRva2VuICE9PSB0cy5TeW50YXhLaW5kLkltcGxlbWVudHNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Zm9yIChjb25zdCB0eXBlIG9mIGNsYXVzZS50eXBlcykge1xuXHRcdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHR5cGUuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCBtYXRjaGVkID0gdGhpcy5pbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5LmludGVyZmFjZXNbIHR5cGUuZXhwcmVzc2lvbi50ZXh0IF07XG5cdFx0XHRcdFx0aWYgKG1hdGNoZWQpIHtcblx0XHRcdFx0XHRcdGtpbmQgPSBtYXRjaGVkO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGNvbnN0IGRlY2w6IEluc3RydW1lbnRhdGlvbkNsYXNzRGVjbCA9IHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0Y29kZSxcblx0XHR9O1xuXHRcdGlmIChraW5kKSB7XG5cdFx0XHRkZWNsLmtpbmQgPSBraW5kO1xuXHRcdH1cblx0XHR0aGlzLmluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMuc2V0KGNsYXNzTmFtZSwgZGVjbCk7XG5cdH1cblxuXHQvKipcblx0ICogRGV0ZWN0IGRlY29yYXRvciBhcHBsaWNhdGlvbiBzaXRlczogcGx1Z2luLWxpc3RlZCBkZWNvcmF0b3JzIGFwcGxpZWRcblx0ICogd2l0aCBjbGFzcyBhcmd1bWVudHMgb24gYSBjbGFzcyBvciBvbmUgb2YgaXRzIG1ldGhvZHMuIE9uZSBzaXRlIHBlclxuXHQgKiByZWZlcmVuY2VkIGNsYXNzIGlkZW50aWZpZXIuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25EZWNvcmF0b3IgKG5vZGU6IHRzLkRlY29yYXRvciwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24oZXhwcmVzc2lvbikgfHwgIXRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGtpbmQgPSB0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkudXNlRGVjb3JhdG9yc1sgZXhwcmVzc2lvbi5leHByZXNzaW9uLnRleHQgXTtcblx0XHRpZiAoIWtpbmQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBUaGUgZGVjb3JhdG9yJ3MgcGFyZW50IGlzIHRoZSBkZWNvcmF0ZWQgbm9kZTogYSBjb250cm9sbGVyIGNsYXNzLFxuXHRcdC8vIG9uZSBvZiBpdHMgbWV0aG9kcywgb3Igb25lIG9mIGl0cyBtZXRob2QgcGFyYW1ldGVyc1xuXHRcdC8vIChAQm9keShtdnAuZm9yVHlwZShEdG8pKSBvbiBhIGhhbmRsZXIgYXJndW1lbnQpXG5cdFx0Y29uc3QgZGVjb3JhdGVkID0gbm9kZS5wYXJlbnQ7XG5cdFx0bGV0IHNjb3BlOiBJbnN0cnVtZW50YXRpb25TY29wZTtcblx0XHRsZXQgdGFyZ2V0czogc3RyaW5nW107XG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihkZWNvcmF0ZWQpICYmIGRlY29yYXRlZC5uYW1lKSB7XG5cdFx0XHRzY29wZSA9IGBjb250cm9sbGVyOiR7ZGVjb3JhdGVkLm5hbWUudGV4dH1gO1xuXHRcdFx0dGFyZ2V0cyA9IFsgZGVjb3JhdGVkLm5hbWUudGV4dCBdO1xuXHRcdH0gZWxzZSBpZiAoXG5cdFx0XHR0cy5pc01ldGhvZERlY2xhcmF0aW9uKGRlY29yYXRlZCkgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcihkZWNvcmF0ZWQubmFtZSkgJiZcblx0XHRcdHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihkZWNvcmF0ZWQucGFyZW50KSAmJlxuXHRcdFx0ZGVjb3JhdGVkLnBhcmVudC5uYW1lXG5cdFx0KSB7XG5cdFx0XHRjb25zdCBjbGFzc05hbWUgPSBkZWNvcmF0ZWQucGFyZW50Lm5hbWUudGV4dDtcblx0XHRcdHNjb3BlID0gYG1ldGhvZDoke2NsYXNzTmFtZX0uJHtkZWNvcmF0ZWQubmFtZS50ZXh0fWA7XG5cdFx0XHR0YXJnZXRzID0gWyBjbGFzc05hbWUgXTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzUGFyYW1ldGVyKGRlY29yYXRlZCkpIHtcblx0XHRcdC8vIFBhcmFtZXRlciBkZWNvcmF0b3JzIHRha2UgdGhlIGVuY2xvc2luZyBtZXRob2QncyBzY29wZSDigJQgdGhlXG5cdFx0XHQvLyBhdHRhY2htZW50IHBvaW50IGlzIHRoZSBoYW5kbGVyLCBub3QgdGhlIGFyZ3VtZW50IG5hbWU7IHRoZVxuXHRcdFx0Ly8gc2FtZSBtZXRob2Q6Q2xhc3MubWV0aG9kIGZvcm0gYXMgbWV0aG9kLWxldmVsIHNpdGVzLiBQYXJhbXMgb2Zcblx0XHRcdC8vIGNvbnN0cnVjdG9ycywgZnVuY3Rpb25zLCBhbmQgdW5uYW1lYWJsZSBob3N0cyBzdGF5IHNpbGVudCwgdGhlXG5cdFx0XHQvLyBzYW1lIGNvbnZlbnRpb24gYXMgb3RoZXIgdW5yZXNvbHZhYmxlIGRlY29yYXRvciBwYXJlbnRzXG5cdFx0XHRjb25zdCBob3N0ID0gZGVjb3JhdGVkLnBhcmVudDtcblx0XHRcdGlmIChcblx0XHRcdFx0aG9zdCAmJlxuXHRcdFx0XHR0cy5pc01ldGhvZERlY2xhcmF0aW9uKGhvc3QpICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihob3N0Lm5hbWUpICYmXG5cdFx0XHRcdHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihob3N0LnBhcmVudCkgJiZcblx0XHRcdFx0aG9zdC5wYXJlbnQubmFtZVxuXHRcdFx0KSB7XG5cdFx0XHRcdGNvbnN0IGNsYXNzTmFtZSA9IGhvc3QucGFyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0c2NvcGUgPSBgbWV0aG9kOiR7Y2xhc3NOYW1lfS4ke2hvc3QubmFtZS50ZXh0fWA7XG5cdFx0XHRcdHRhcmdldHMgPSBbIGNsYXNzTmFtZSBdO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0Zm9yIChjb25zdCBhcmcgb2YgZXhwcmVzc2lvbi5hcmd1bWVudHMpIHtcblx0XHRcdC8vIENsYXNzIHJlZmVyZW5jZTogQFJlZ2lzdGVyKEltcGwpIG9yIGFuIGlubGluZSBpbnN0YW5jZTpcblx0XHRcdC8vIEBSZWdpc3RlcihuZXcgSW1wbCh7IC4uLm9wdGlvbnMgfSkpXG5cdFx0XHRsZXQgY2xhc3NOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdFx0XHQvLyBwZXItYXJnIGtpbmQ6IGZhY3RvcnktY2FsbCBhcmdzIGNhcnJ5IHRoZWlyIG93biBjb25maWd1cmVkXG5cdFx0XHQvLyBraW5kLCBldmVyeXRoaW5nIGVsc2UgdGFrZXMgdGhlIGRlY29yYXRvcidzXG5cdFx0XHRsZXQgYXJnS2luZCA9IGtpbmQ7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdFx0Y2xhc3NOYW1lID0gYXJnLnRleHQ7XG5cdFx0XHR9IGVsc2UgaWYgKHRzLmlzTmV3RXhwcmVzc2lvbihhcmcpICYmIHRzLmlzSWRlbnRpZmllcihhcmcuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y2xhc3NOYW1lID0gYXJnLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdH0gZWxzZSBpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihhcmcpICYmIHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFyZy5leHByZXNzaW9uKSkge1xuXHRcdFx0XHQvLyBQaXBlLWZhY3Rvcnkgc2hhcGU6IEBVc2VQaXBlcyhtdnAuZm9yVHlwZShEdG8pKSDigJQgdGhlXG5cdFx0XHRcdC8vIGNhbGwncyBtZXRob2QgbmFtZSBpcyBwbHVnaW4tbGlzdGVkLCB0aGUgdGFyZ2V0IGNsYXNzIHNpdHNcblx0XHRcdFx0Ly8gaW4gdGhlIGNvbmZpZ3VyZWQgYXJndW1lbnQgcG9zaXRpb24gKGRlZmF1bHQgMClcblx0XHRcdFx0Y29uc3QgZmFjdG9yeSA9IHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS5kZWNvcmF0b3JBcmdGYWN0b3JpZXNbIGFyZy5leHByZXNzaW9uLm5hbWUudGV4dCBdO1xuXHRcdFx0XHRpZiAoZmFjdG9yeSkge1xuXHRcdFx0XHRcdGNvbnN0IHRhcmdldEFyZyA9IGFyZy5hcmd1bWVudHNbIGZhY3RvcnkudGFyZ2V0QXJnID8/IDAgXTtcblx0XHRcdFx0XHRpZiAodGFyZ2V0QXJnICYmIHRzLmlzSWRlbnRpZmllcih0YXJnZXRBcmcpKSB7XG5cdFx0XHRcdFx0XHRjbGFzc05hbWUgPSB0YXJnZXRBcmcudGV4dDtcblx0XHRcdFx0XHRcdGFyZ0tpbmQgPSBmYWN0b3J5LmtpbmQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAoIWNsYXNzTmFtZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uU2l0ZXMucHVzaCh7XG5cdFx0XHRcdGtpbmQgOiBhcmdLaW5kLFxuXHRcdFx0XHRjbGFzc05hbWUsXG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRzY29wZSxcblx0XHRcdFx0dGFyZ2V0cyxcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgZ2xvYmFsIHJlZ2lzdHJhdGlvbnM6IG9iamVjdCBsaXRlcmFscyBzaGFwZWQgbGlrZVxuXHQgKiBgeyBwcm92aWRlOiA8cGx1Z2luLWxpc3RlZCB0b2tlbj4sIHVzZUNsYXNzOiBYIH1gLlxuXHQgKiB1c2VFeGlzdGluZy91c2VGYWN0b3J5IHdpdGhvdXQgYSB1c2VDbGFzcyBpZGVudGlmaWVyIGFyZSBub3Rcblx0ICogc3RhdGljYWxseSBvYnZpb3VzIOKAlCBza2lwcGVkIHJhdGhlciB0aGFuIGd1ZXNzZWQuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25Qcm92aWRlciAobm9kZTogdHMuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRsZXQga2luZDogSW5zdHJ1bWVudGF0aW9uS2luZCB8IHVuZGVmaW5lZDtcblx0XHRsZXQgdXNlQ2xhc3NOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cblx0XHRmb3IgKGNvbnN0IHByb3Agb2Ygbm9kZS5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdCF0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSB8fFxuXHRcdFx0XHQhdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkgfHxcblx0XHRcdFx0IXRzLmlzSWRlbnRpZmllcihwcm9wLmluaXRpYWxpemVyKVxuXHRcdFx0KSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHByb3AubmFtZS50ZXh0ID09PSAncHJvdmlkZScpIHtcblx0XHRcdFx0a2luZCA9IHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS5hcHBUb2tlbnNbIHByb3AuaW5pdGlhbGl6ZXIudGV4dCBdO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHByb3AubmFtZS50ZXh0ID09PSAndXNlQ2xhc3MnKSB7XG5cdFx0XHRcdHVzZUNsYXNzTmFtZSA9IHByb3AuaW5pdGlhbGl6ZXIudGV4dDtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRpZiAoIWtpbmQgfHwgIXVzZUNsYXNzTmFtZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uU2l0ZXMucHVzaCh7XG5cdFx0XHRraW5kLFxuXHRcdFx0Y2xhc3NOYW1lIDogdXNlQ2xhc3NOYW1lLFxuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRjb2RlLFxuXHRcdFx0c2NvcGUgICAgIDogJ2dsb2JhbCcsXG5cdFx0XHR0YXJnZXRzICAgOiBbXSxcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgbWlkZGxld2FyZSB3aXJpbmc6IGBjb25zdW1lci5hcHBseShNdzEsIE13MikuZm9yUm91dGVzKC4uLilgXG5cdCAqIGluc2lkZSBhIGNsYXNzJ3MgY29uZmlndXJlKCkgbWV0aG9kLiBUYXJnZXRzIGNvbWUgZnJvbSBmb3JSb3V0ZXNcblx0ICogYXJndW1lbnRzIHdoZW4gc3RhdGljYWxseSByZWFkYWJsZSAoc3RyaW5nIHJvdXRlcyBvciBjb250cm9sbGVyXG5cdCAqIGlkZW50aWZpZXJzKSwgZWxzZSBbXS4gU2hhcGUtYmFzZWQsIHNvIGEgcGx1Z2luIG11c3Qgb3B0IGluIHZpYVxuXHQgKiBgbWlkZGxld2FyZVdpcmluZzogdHJ1ZWAuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25NaWRkbGV3YXJlIChub2RlOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdGhpcy5pbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5Lm1pZGRsZXdhcmVXaXJpbmcpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKFxuXHRcdFx0IXRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbikgfHxcblx0XHRcdG5vZGUuZXhwcmVzc2lvbi5uYW1lLnRleHQgIT09ICdmb3JSb3V0ZXMnXG5cdFx0KSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGFwcGx5Q2FsbCA9IG5vZGUuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdGlmIChcblx0XHRcdCF0cy5pc0NhbGxFeHByZXNzaW9uKGFwcGx5Q2FsbCkgfHxcblx0XHRcdCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcHBseUNhbGwuZXhwcmVzc2lvbikgfHxcblx0XHRcdGFwcGx5Q2FsbC5leHByZXNzaW9uLm5hbWUudGV4dCAhPT0gJ2FwcGx5J1xuXHRcdCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAoIXRoaXMuaXNJbnNpZGVDb25maWd1cmVNZXRob2Qobm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB0YXJnZXRzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgYXJnIG9mIG5vZGUuYXJndW1lbnRzKSB7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykgfHwgdHMuaXNTdHJpbmdMaXRlcmFsKGFyZykpIHtcblx0XHRcdFx0dGFyZ2V0cy5wdXNoKGFyZy50ZXh0KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0YXBwbHlDYWxsLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdGZvciAoY29uc3QgYXJnIG9mIGFwcGx5Q2FsbC5hcmd1bWVudHMpIHtcblx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHR0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzLnB1c2goe1xuXHRcdFx0XHRraW5kICAgICAgOiAnbWlkZGxld2FyZScsXG5cdFx0XHRcdGNsYXNzTmFtZSA6IGFyZy50ZXh0LFxuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0c2NvcGUgICAgIDogJ21vZHVsZScsXG5cdFx0XHRcdHRhcmdldHMsXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogV2FsayB1cCB0aGUgcGFyZW50IGNoYWluIGxvb2tpbmcgZm9yIGFuIGVuY2xvc2luZyBjb25maWd1cmUoKSBtZXRob2Rcblx0ICovXG5cdHByaXZhdGUgaXNJbnNpZGVDb25maWd1cmVNZXRob2QgKG5vZGU6IHRzLk5vZGUpOiBib29sZWFuIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5vZGUucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24oY3VycmVudCkgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGN1cnJlbnQubmFtZSkgJiZcblx0XHRcdFx0Y3VycmVudC5uYW1lLnRleHQgPT09ICdjb25maWd1cmUnXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxufVxuIl19