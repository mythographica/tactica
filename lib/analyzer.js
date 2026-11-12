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
    getBuilderValues() {
        const result = [];
        const seen = new Set();
        for (const candidate of this.builderCandidates) {
            if (candidate.excluded) {
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
     * Track imports from 'mnemonica' so aliases of the module object and
     * createTypesCollection are recognized without relying on the type checker.
     */
    trackImports(node) {
        if (!ts.isImportDeclaration(node)) {
            return;
        }
        const { moduleSpecifier } = node;
        if (ts.isStringLiteral(moduleSpecifier) && moduleSpecifier.text.includes('.tactica')) {
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
    hasGeneratedTypeReference(handler) {
        if (!handler) {
            return false;
        }
        const imports = this.generatedTypeImports.get(this.currentReferencedTypeFile);
        if (!imports || imports.size === 0) {
            return false;
        }
        let found = false;
        const visit = (node) => {
            if (found) {
                return;
            }
            if (ts.isIdentifier(node) && imports.has(node.text)) {
                found = true;
                return;
            }
            ts.forEachChild(node, visit);
        };
        visit(handler);
        return found;
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYW5hbHl6ZXIuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvYW5hbHl6ZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFFYiwrQ0FBaUM7QUFDakMsK0NBQWlDO0FBT2pDLG1DQUVpQjtBQUNqQix1Q0FFbUI7QUFxRm5COzs7R0FHRztBQUNILE1BQU0sa0JBQWtCLEdBQUcsSUFBSSxHQUFHLENBQUM7SUFDbEMsTUFBTSxFQUFFLFFBQVEsRUFBRSxPQUFPLEVBQUUsV0FBVyxFQUFFLFlBQVksRUFBRSxnQkFBZ0I7SUFDdEUsYUFBYSxFQUFFLFdBQVcsRUFBRSxVQUFVLEVBQUUsZ0JBQWdCO0lBQ3hELEtBQUssRUFBRSxLQUFLLEVBQUUsU0FBUyxFQUFFLFNBQVMsRUFBRSxTQUFTLEVBQUUsc0JBQXNCO0lBQ3JFLFNBQVMsRUFBRSxPQUFPLEVBQUUsZUFBZSxFQUFFLFFBQVEsRUFBRSxTQUFTLEVBQUUsVUFBVTtJQUNwRSxVQUFVLEVBQUUsTUFBTSxFQUFFLE1BQU0sRUFBRSxTQUFTLEVBQUUsU0FBUyxFQUFFLGFBQWE7SUFDL0QsWUFBWSxFQUFFLGNBQWMsRUFBRSxZQUFZLEVBQUUsdUJBQXVCO0lBQ25FLFVBQVUsRUFBRSxtQkFBbUIsRUFBRSxtQkFBbUI7SUFDcEQsV0FBVyxFQUFFLFdBQVcsRUFBRSxZQUFZLEVBQUUsY0FBYztJQUN0RCxRQUFRLEVBQUUsUUFBUSxFQUFFLFNBQVMsRUFBRSxRQUFRLEVBQUUsUUFBUSxFQUFFLFFBQVEsRUFBRSxVQUFVO0lBQ3ZFLFVBQVUsRUFBRSxVQUFVLEVBQUUsV0FBVyxFQUFFLGVBQWUsRUFBRSxlQUFlO0lBQ3JFLGdCQUFnQixFQUFFLGtCQUFrQixFQUFFLHVCQUF1QjtJQUM3RCxhQUFhLEVBQUUsYUFBYSxFQUFFLG1CQUFtQixFQUFFLFVBQVU7SUFDN0QsV0FBVyxFQUFFLFlBQVksRUFBRSxtQkFBbUIsRUFBRSxZQUFZO0lBQzVELGFBQWEsRUFBRSxZQUFZLEVBQUUsYUFBYSxFQUFFLGNBQWM7SUFDMUQsY0FBYyxFQUFFLGVBQWUsRUFBRSxnQkFBZ0IsRUFBRSxNQUFNO0NBQ3pELENBQUMsQ0FBQztBQUVILG9FQUFvRTtBQUNwRSxzRUFBc0U7QUFDdEUsaUVBQWlFO0FBQ2pFLE1BQU0sMkJBQTJCLEdBQUcsSUFBSSxHQUFHLENBQWlCO0lBQzNELENBQUUsS0FBSyxFQUFFLHVCQUF1QixDQUFFO0lBQ2xDLENBQUUsU0FBUyxFQUFFLDBCQUEwQixDQUFFO0lBQ3pDLENBQUUsS0FBSyxFQUFFLGNBQWMsQ0FBRTtJQUN6QixDQUFFLFNBQVMsRUFBRSxpQkFBaUIsQ0FBRTtJQUNoQyxDQUFFLFNBQVMsRUFBRSxpQkFBaUIsQ0FBRTtJQUNoQyxDQUFFLHNCQUFzQixFQUFFLCtCQUErQixDQUFFO0lBQzNELENBQUUsU0FBUyxFQUFFLGtCQUFrQixDQUFFO0lBQ2pDLENBQUUsT0FBTyxFQUFFLGdCQUFnQixDQUFFO0lBQzdCLENBQUUsZUFBZSxFQUFFLHdCQUF3QixDQUFFO0NBQzdDLENBQUMsQ0FBQztBQUVILGlGQUFpRjtBQUNqRixNQUFNLHdCQUF3QixHQUFHLENBQUMsQ0FBQztBQUNuQywwRUFBMEU7QUFDMUUsK0RBQStEO0FBQy9ELE1BQU0sa0JBQWtCLEdBQUcsQ0FBQyxDQUFDO0FBRTdCOzs7Ozs7R0FNRztBQUNILE1BQWEsaUJBQWlCO0lBNEk3QixZQUFhLE9BQW9CLEVBQUUsVUFBMkIsRUFBRTtRQTNJeEQsV0FBTSxHQUFtQixFQUFFLENBQUM7UUFDNUIsVUFBSyxHQUFHLElBQUkscUJBQWEsRUFBRSxDQUFDO1FBQzVCLGdCQUFXLEdBQUcsSUFBSSxHQUFHLEVBQTBCLENBQUM7UUFDaEQsV0FBTSxHQUFHLElBQUksR0FBRyxFQUF1QixDQUFDO1FBQ3hDLGNBQVMsR0FBRyxJQUFJLEdBQUcsRUFBcUIsQ0FBQztRQUN6QyxlQUFVLEdBQUcsSUFBSSxHQUFHLEVBQXNCLENBQUM7UUFDbkQsc0VBQXNFO1FBQ3RFLHVFQUF1RTtRQUN2RSxzRUFBc0U7UUFDdEUsNkNBQTZDO1FBQ3JDLG1CQUFjLEdBQUcsSUFBSSxHQUFHLEVBQW1CLENBQUM7UUFDcEQscUVBQXFFO1FBQ3JFLHdFQUF3RTtRQUNoRSxxQkFBZ0IsR0FBRyxJQUFJLEdBQUcsRUFBc0MsQ0FBQztRQUN6RSwyRUFBMkU7UUFDM0UsNkVBQTZFO1FBQ3JFLHdCQUFtQixHQUFHLElBQUksR0FBRyxFQUEyQyxDQUFDO1FBQ2pGLG1FQUFtRTtRQUNuRSxxRUFBcUU7UUFDckUsbUVBQW1FO1FBQ25FLG9CQUFvQjtRQUNaLGtCQUFhLEdBQUcsSUFBSSxHQUFHLEVBQTRDLENBQUM7UUFDNUUsb0VBQW9FO1FBQ3BFLGtFQUFrRTtRQUNsRSxxREFBcUQ7UUFDN0Msb0JBQWUsR0FBRyxJQUFJLEdBQUcsRUFBb0IsQ0FBQztRQUN0RCw0RUFBNEU7UUFDcEUsc0JBQWlCLEdBQUcsSUFBSSxHQUFHLEVBQWtCLENBQUM7UUFDdEQsMEVBQTBFO1FBQ2xFLHNCQUFpQixHQUF1QixFQUFFLENBQUM7UUFDM0Msc0JBQWlCLEdBQUcsSUFBSSxHQUFHLEVBQVUsQ0FBQztRQUN0Qyx5QkFBb0IsR0FBRyxJQUFJLEdBQUcsRUFBdUIsQ0FBQztRQUM5RCw2R0FBNkc7UUFDckcsMEJBQXFCLEdBQUcsSUFBSSxHQUFHLEVBQVUsQ0FBQztRQUNsRCwrREFBK0Q7UUFDL0QsK0RBQStEO1FBQy9ELGtFQUFrRTtRQUNsRSx1REFBdUQ7UUFDL0MsMEJBQXFCLEdBQUcsSUFBSSxHQUFHLEVBQStCLENBQUM7UUFDdkUsa0dBQWtHO1FBQzFGLG1DQUE4QixHQUFHLElBQUksR0FBRyxFQUFVLENBQUM7UUFDM0Qsa0VBQWtFO1FBQzFELHdCQUFtQixHQUFHLElBQUksR0FBRyxFQUFrQixDQUFDO1FBQ3hELGtFQUFrRTtRQUMxRCxtQkFBYyxHQUFHLElBQUksR0FBRyxFQUEwQixDQUFDO1FBQ25ELHNCQUFpQixHQUFHLENBQUMsQ0FBQztRQUM5QixpRUFBaUU7UUFDakUsOERBQThEO1FBQzlELHVFQUF1RTtRQUMvRCw4QkFBeUIsR0FBRyxJQUFJLEdBQUcsRUFBb0MsQ0FBQztRQUNoRixvRUFBb0U7UUFDcEUsK0NBQStDO1FBQ3ZDLHlCQUFvQixHQUEwQixFQUFFLENBQUM7UUFJekQsdUVBQXVFO1FBQ3ZFLHdFQUF3RTtRQUN4RSxvRUFBb0U7UUFDcEUsdUVBQXVFO1FBQ3ZFLHFFQUFxRTtRQUNyRSx5RUFBeUU7UUFDekUseUVBQXlFO1FBQ2pFLHdCQUFtQixHQUFHLElBQUksR0FBRyxFQUFrRCxDQUFDO1FBQ2hGLDBCQUFxQixHQUFHLElBQUksR0FBRyxFQUE2QyxDQUFDO1FBQ3JGLDZFQUE2RTtRQUNyRSw0QkFBdUIsR0FBRyxJQUFJLEdBQUcsRUFBK0IsQ0FBQztRQUN6RSw0Q0FBNEM7UUFDcEMsOEJBQXlCLEdBQUcsSUFBSSxHQUFHLEVBQW9CLENBQUM7UUFDaEUsZ0VBQWdFO1FBQ3hELGdDQUEyQixHQUFHLElBQUksR0FBRyxFQUErQixDQUFDO1FBQzdFLHNFQUFzRTtRQUN0RSxxRUFBcUU7UUFDN0QsNkJBQXdCLEdBQUcsSUFBSSxHQUFHLEVBQTZDLENBQUM7UUFDeEYsc0VBQXNFO1FBQ3RFLHVEQUF1RDtRQUMvQyxpQ0FBNEIsR0FBRyxJQUFJLEdBQUcsRUFBK0IsQ0FBQztRQUM5RSx1RUFBdUU7UUFDL0Qsa0NBQTZCLEdBQUcsSUFBSSxHQUFHLEVBQWdELENBQUM7UUFDaEcsc0VBQXNFO1FBQ3RFLDBEQUEwRDtRQUMxRCx3RUFBd0U7UUFDeEUsdUVBQXVFO1FBQ3ZFLG9FQUFvRTtRQUNwRSx5REFBeUQ7UUFDakQsOEJBQXlCLEdBQUcsSUFBSSxHQUFHLEVBQWtELENBQUM7UUFFOUYsMkVBQTJFO1FBQ25FLDhCQUF5QixHQUFHLEVBQUUsQ0FBQztRQUN2QyxxREFBcUQ7UUFDN0MsK0JBQTBCLEdBQUcsSUFBSSxHQUFHLEVBQVUsQ0FBQztRQUN2RCxtRUFBbUU7UUFDbkUscUVBQXFFO1FBQ3JFLG9FQUFvRTtRQUNwRSxzRUFBc0U7UUFDdEUsdURBQXVEO1FBQy9DLGdCQUFXLEdBQUcsSUFBSSxHQUFHLEVBQW9CLENBQUM7UUFDbEQsb0VBQW9FO1FBQ3BFLHdEQUF3RDtRQUNoRCx5QkFBb0IsR0FBc0IsRUFBRSxDQUFDO1FBQ3JELGtFQUFrRTtRQUNsRSx5RUFBeUU7UUFDakUsOEJBQXlCLEdBQUcsS0FBSyxDQUFDO1FBQzFDLHlFQUF5RTtRQUN6RSxxRUFBcUU7UUFDckUsdUVBQXVFO1FBQ3ZFLGtFQUFrRTtRQUNsRSwyREFBMkQ7UUFDbkQscUJBQWdCLEdBQXlDLEVBQUUsQ0FBQztRQUNwRSx1RUFBdUU7UUFDdkUseUVBQXlFO1FBQ2pFLGlDQUE0QixHQUFHLEtBQUssQ0FBQztRQUM3Qyx1RUFBdUU7UUFDdkUsb0VBQW9FO1FBQ3BFLGlFQUFpRTtRQUNqRSxzRUFBc0U7UUFDdEUsbUVBQW1FO1FBQ25FLHFFQUFxRTtRQUNyRSxxRUFBcUU7UUFDckUscUVBQXFFO1FBQ3JFLHVFQUF1RTtRQUMvRCx3QkFBbUIsR0FBdUQsRUFBRSxDQUFDO1FBQ3JGLG9FQUFvRTtRQUNwRSxzRUFBc0U7UUFDdEUsbUVBQW1FO1FBQzNELHNCQUFpQixHQUFHLElBQUksR0FBRyxFQUErQixDQUFDO1FBSW5FLHlFQUF5RTtRQUN6RSx3RUFBd0U7UUFDeEUsd0VBQXdFO1FBQ3hFLHVFQUF1RTtRQUN2RSx1RUFBdUU7UUFDdkUsc0VBQXNFO1FBQ3RFLHdFQUF3RTtRQUN4RSw4REFBOEQ7UUFDdEQsbUJBQWMsR0FBRyxJQUFJLEdBQUcsRUFBcUIsQ0FBQztRQUdyRCwrREFBK0Q7UUFDL0QsOERBQThEO1FBQzlELGtEQUFrRDtRQUNsRCxJQUFJLENBQUMsNkJBQTZCLEdBQUcsT0FBTyxFQUFFLGtCQUFrQixFQUFFLElBQUksRUFBRSxDQUFDO1FBQ3pFLElBQUksQ0FBQyx5QkFBeUIsR0FBRyxJQUFBLDZCQUFtQixFQUFDLE9BQU8sQ0FBQyxDQUFDO0lBQy9ELENBQUM7SUFFRDs7O09BR0c7SUFDSCxXQUFXO1FBQ1YsSUFBSSxDQUFDLE1BQU0sQ0FBQyxLQUFLLEVBQUUsQ0FBQztRQUNwQixJQUFJLENBQUMsU0FBUyxDQUFDLEtBQUssRUFBRSxDQUFDO1FBQ3ZCLElBQUksQ0FBQyxVQUFVLENBQUMsS0FBSyxFQUFFLENBQUM7UUFDeEIsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEtBQUssRUFBRSxDQUFDO1FBQy9CLDhEQUE4RDtRQUM5RCw4QkFBOEI7UUFDOUIsSUFBSSxDQUFDLGVBQWUsQ0FBQyxLQUFLLEVBQUUsQ0FBQztRQUM3QixJQUFJLENBQUMsYUFBYSxDQUFDLEtBQUssRUFBRSxDQUFDO1FBQzNCLDRFQUE0RTtRQUM1RSxzQ0FBc0M7UUFDdEMsaUVBQWlFO1FBQ2pFLGtFQUFrRTtRQUNsRSx1RUFBdUU7UUFDdkUsSUFBSSxDQUFDLGNBQWMsQ0FBQyxLQUFLLEVBQUUsQ0FBQztRQUM1QixvRUFBb0U7UUFDcEUsK0RBQStEO1FBQy9ELDZDQUE2QztRQUM3QyxJQUFJLENBQUMseUJBQXlCLEdBQUcsS0FBSyxDQUFDO1FBQ3ZDLElBQUksQ0FBQyxnQkFBZ0IsR0FBRyxFQUFFLENBQUM7UUFDM0IsSUFBSSxDQUFDLDRCQUE0QixHQUFHLEtBQUssQ0FBQztRQUMxQyxJQUFJLENBQUMsbUJBQW1CLEdBQUcsRUFBRSxDQUFDO0lBQy9CLENBQUM7SUFFRDs7T0FFRztJQUNILFdBQVcsQ0FBRSxVQUF5QjtRQUNyQyxJQUFJLENBQUMsTUFBTSxHQUFHLEVBQUUsQ0FBQztRQUNqQixxRUFBcUU7UUFDckUsSUFBSSxDQUFDLHlCQUF5QixHQUFHLFFBQVEsQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLFFBQVEsQ0FBQyxDQUFDO1FBQ3ZFLGdEQUFnRDtRQUNoRCxJQUFJLENBQUMsMEJBQTBCLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDNUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxVQUFVLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFFdkMsT0FBTztZQUNOLEtBQUssRUFBSSxJQUFJLENBQUMsS0FBSyxDQUFDLFdBQVcsRUFBRTtZQUNqQyxNQUFNLEVBQUcsSUFBSSxDQUFDLE1BQU07U0FDcEIsQ0FBQztJQUNILENBQUM7SUFFRDs7T0FFRztJQUNILGFBQWEsQ0FBRSxVQUFrQixFQUFFLFFBQVEsR0FBRyxTQUFTO1FBQ3RELE1BQU0sVUFBVSxHQUFHLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FDckMsUUFBUSxFQUNSLFVBQVUsRUFDVixFQUFFLENBQUMsWUFBWSxDQUFDLE1BQU0sRUFDdEIsSUFBSSxDQUNKLENBQUM7UUFDRixPQUFPLElBQUksQ0FBQyxXQUFXLENBQUMsVUFBVSxDQUFDLENBQUM7SUFDckMsQ0FBQztJQUVEOztPQUVHO0lBQ0gsUUFBUTtRQUNQLE9BQU8sSUFBSSxDQUFDLEtBQUssQ0FBQztJQUNuQixDQUFDO0lBRUQsZ0JBQWdCO1FBQ2YsTUFBTSxNQUFNLEdBQW1CLEVBQUUsQ0FBQztRQUNsQyxNQUFNLElBQUksR0FBRyxJQUFJLEdBQUcsRUFBVSxDQUFDO1FBQy9CLEtBQUssTUFBTSxTQUFTLElBQUksSUFBSSxDQUFDLGlCQUFpQixFQUFFLENBQUM7WUFDaEQsSUFBSSxTQUFTLENBQUMsUUFBUSxFQUFFLENBQUM7Z0JBQ3hCLFNBQVM7WUFDVixDQUFDO1lBQ0QsS0FBSyxNQUFNLFFBQVEsSUFBSSxTQUFTLENBQUMsT0FBTyxFQUFFLENBQUM7Z0JBQzFDLE1BQU0sR0FBRyxHQUFHLEdBQUcsU0FBUyxDQUFDLElBQUksSUFBSSxRQUFRLENBQUMsVUFBVSxJQUFJLFFBQVEsQ0FBQyxJQUFJLElBQUksU0FBUyxDQUFDLFFBQVEsRUFBRSxDQUFDO2dCQUM5RixJQUFJLElBQUksQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztvQkFDbkIsU0FBUztnQkFDVixDQUFDO2dCQUNELElBQUksQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLENBQUM7Z0JBQ2QsTUFBTSxDQUFDLElBQUksQ0FBQztvQkFDWCxJQUFJLEVBQVksUUFBUSxDQUFDLElBQUk7b0JBQzdCLFVBQVUsRUFBTSxRQUFRLENBQUMsVUFBVTtvQkFDbkMsSUFBSSxFQUFZLFNBQVMsQ0FBQyxJQUFJO29CQUM5QixRQUFRLEVBQVEsU0FBUyxDQUFDLFFBQVE7b0JBQ2xDLGFBQWEsRUFBRyxRQUFRLENBQUMsYUFBYTtpQkFDdEMsQ0FBQyxDQUFDO1lBQ0osQ0FBQztRQUNGLENBQUM7UUFDRCxPQUFPLE1BQU0sQ0FBQztJQUNmLENBQUM7SUFFRDs7T0FFRztJQUNILGNBQWM7UUFDYixPQUFPLElBQUksQ0FBQyxXQUFXLENBQUM7SUFDekIsQ0FBQztJQUVEOzs7Ozs7OztPQVFHO0lBQ0gsc0JBQXNCO1FBQ3JCLE1BQU0sT0FBTyxHQUE4QixFQUFFLENBQUM7UUFDOUMsTUFBTSxlQUFlLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxXQUFXLEVBQUUsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsWUFBWSxLQUFLLFNBQVMsQ0FBQyxDQUFDO1FBQ3pGLElBQUksZUFBZSxFQUFFLENBQUM7WUFDckIsT0FBTyxDQUFDLElBQUksQ0FBQztnQkFDWixFQUFFLEVBQVMsSUFBSTtnQkFDZixJQUFJLEVBQU8sY0FBYztnQkFDekIsUUFBUSxFQUFHLElBQUk7Z0JBQ2YsUUFBUSxFQUFHLFlBQVk7YUFDdkIsQ0FBQyxDQUFDO1FBQ0osQ0FBQztRQUNELEtBQUssTUFBTSxDQUFFLEVBQUUsRUFBRSxJQUFJLENBQUUsSUFBSSxJQUFJLENBQUMsY0FBYyxFQUFFLENBQUM7WUFDaEQsTUFBTSxLQUFLLEdBQTRCO2dCQUN0QyxFQUFFO2dCQUNGLElBQUksRUFBTyxJQUFJLENBQUMsWUFBWTtnQkFDNUIsUUFBUSxFQUFHLEdBQUcsSUFBSSxDQUFDLFVBQVUsSUFBSSxJQUFJLENBQUMsSUFBSSxJQUFJLElBQUksQ0FBQyxNQUFNLEVBQUU7Z0JBQzNELFFBQVEsRUFBRyxZQUFZO2FBQ3ZCLENBQUM7WUFDRixPQUFPLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxDQUFDO1FBQ3JCLENBQUM7UUFDRCxPQUFPLE9BQU8sQ0FBQztJQUNoQixDQUFDO0lBRUQ7O09BRUc7SUFDSCxTQUFTO1FBQ1IsT0FBTyxJQUFJLENBQUMsTUFBTSxDQUFDO0lBQ3BCLENBQUM7SUFFRDs7T0FFRztJQUNILFlBQVk7UUFDWCxPQUFPLElBQUksQ0FBQyxTQUFTLENBQUM7SUFDdkIsQ0FBQztJQUVEOztPQUVHO0lBQ0gsYUFBYTtRQUNaLE9BQU8sSUFBSSxDQUFDLFVBQVUsQ0FBQztJQUN4QixDQUFDO0lBRUQ7Ozs7Ozs7OztPQVNHO0lBQ0gsd0JBQXdCO1FBQ3ZCLE1BQU0sTUFBTSxHQUFHLElBQUksR0FBRyxFQUFnQyxDQUFDO1FBRXZELE1BQU0sUUFBUSxHQUFHLENBQUMsS0FBMkIsRUFBUSxFQUFFO1lBQ3RELE1BQU0sR0FBRyxHQUFHLEdBQUcsS0FBSyxDQUFDLElBQUksSUFBSSxLQUFLLENBQUMsU0FBUyxJQUFJLEtBQUssQ0FBQyxRQUFRLElBQUksS0FBSyxDQUFDLEtBQUssRUFBRSxDQUFDO1lBQ2hGLE1BQU0sUUFBUSxHQUFHLE1BQU0sQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLENBQUM7WUFDakMsSUFBSSxRQUFRLEVBQUUsQ0FBQztnQkFDZCxNQUFNLE1BQU0sR0FBRyxJQUFJLEdBQUcsQ0FBQyxDQUFFLEdBQUcsUUFBUSxDQUFDLE9BQU8sRUFBRSxHQUFHLEtBQUssQ0FBQyxPQUFPLENBQUUsQ0FBQyxDQUFDO2dCQUNsRSxRQUFRLENBQUMsT0FBTyxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLENBQUM7Z0JBQ3RDLE9BQU87WUFDUixDQUFDO1lBQ0QsTUFBTSxDQUFDLEdBQUcsQ0FBQyxHQUFHLEVBQUUsS0FBSyxDQUFDLENBQUM7UUFDeEIsQ0FBQyxDQUFDO1FBRUYsS0FBSyxNQUFNLElBQUksSUFBSSxJQUFJLENBQUMsb0JBQW9CLEVBQUUsQ0FBQztZQUM5QyxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsQ0FBQztZQUNoRSxNQUFNLEtBQUssR0FBeUI7Z0JBQ25DLElBQUksRUFBUSxJQUFJLENBQUMsSUFBSTtnQkFDckIsU0FBUyxFQUFHLElBQUksQ0FBQyxTQUFTO2dCQUMxQixRQUFRLEVBQUksSUFBSSxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsUUFBUTtnQkFDaEQsSUFBSSxFQUFRLElBQUksQ0FBQyxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUk7Z0JBQ3hDLEtBQUssRUFBTyxJQUFJLENBQUMsS0FBSztnQkFDdEIsT0FBTyxFQUFLLElBQUksQ0FBQyxPQUFPO2FBQ3hCLENBQUM7WUFDRixRQUFRLENBQUMsS0FBSyxDQUFDLENBQUM7UUFDakIsQ0FBQztRQUVELGlFQUFpRTtRQUNqRSwrREFBK0Q7UUFDL0QsNERBQTREO1FBQzVELEtBQUssTUFBTSxDQUFFLFNBQVMsRUFBRSxJQUFJLENBQUUsSUFBSSxJQUFJLENBQUMseUJBQXlCLEVBQUUsQ0FBQztZQUNsRSxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO2dCQUNoQixTQUFTO1lBQ1YsQ0FBQztZQUNELE1BQU0sS0FBSyxHQUF5QjtnQkFDbkMsSUFBSSxFQUFRLElBQUksQ0FBQyxJQUFJO2dCQUNyQixTQUFTLEVBQUcsU0FBUztnQkFDckIsUUFBUSxFQUFJLElBQUksQ0FBQyxRQUFRO2dCQUN6QixJQUFJLEVBQVEsSUFBSSxDQUFDLElBQUk7Z0JBQ3JCLEtBQUssRUFBTyxRQUFRO2dCQUNwQixPQUFPLEVBQUssRUFBRTthQUNkLENBQUM7WUFDRixRQUFRLENBQUMsS0FBSyxDQUFDLENBQUM7UUFDakIsQ0FBQztRQUVELE1BQU0sTUFBTSxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLE1BQU0sRUFBRSxDQUFDLENBQUM7UUFDM0MsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7OztPQUdHO0lBQ0gsaUJBQWlCLENBQUUsUUFBZ0IsRUFBRSxJQUFnQztRQUNwRSx5QkFBeUI7UUFDekIsSUFBSSxJQUFJLENBQUMsS0FBSyxDQUFDLFFBQVEsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUN2QyxPQUFPO1FBQ1IsQ0FBQztRQUVELDBEQUEwRDtRQUMxRCxJQUFJLElBQUksQ0FBQyxNQUFNLEVBQUUsQ0FBQztZQUNqQix5QkFBeUI7WUFDekIsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsSUFBSSxDQUFDLE1BQU0sRUFBRSxJQUFJLENBQUMsQ0FBQztRQUN4QyxDQUFDO2FBQU0sQ0FBQztZQUNQLGNBQWM7WUFDZCxJQUFJLENBQUMsS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUMxQixDQUFDO1FBRUQsNkRBQTZEO1FBQzdELE1BQU0sVUFBVSxHQUFtQjtZQUNsQyxJQUFJLEVBQVUsSUFBSSxDQUFDLElBQUk7WUFDdkIsUUFBUSxFQUFNLEdBQUcsSUFBSSxDQUFDLFVBQVUsSUFBSSxJQUFJLENBQUMsSUFBSSxJQUFJLElBQUksQ0FBQyxNQUFNLEVBQUU7WUFDOUQsSUFBSSxFQUFVLFFBQVE7WUFDdEIsTUFBTSxFQUFRLElBQUksQ0FBQyxNQUFNLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxNQUFNLENBQUMsUUFBUSxDQUFDLENBQUMsQ0FBQyxJQUFJO1lBQ3ZELFdBQVcsRUFBRyxJQUFJO1lBQ2xCLFdBQVcsRUFBRyxLQUFLO1NBQ25CLENBQUM7UUFDRixJQUFJLENBQUMsV0FBVyxDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsVUFBVSxDQUFDLENBQUM7SUFDNUMsQ0FBQztJQUVEOztPQUVHO0lBQ0ssMEJBQTBCLENBQUUsVUFBeUI7UUFDNUQsTUFBTSxTQUFTLEdBQUcsQ0FBQyxJQUFhLEVBQUUsTUFBZ0IsRUFBRSxFQUFFO1lBQ3JELCtEQUErRDtZQUMvRCw4REFBOEQ7WUFDN0QsSUFBWSxDQUFDLE1BQU0sR0FBRyxNQUFNLENBQUM7WUFDOUIsRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLEVBQUUsS0FBSyxDQUFDLEVBQUUsQ0FBQyxTQUFTLENBQUMsS0FBSyxFQUFFLElBQUksQ0FBQyxDQUFDLENBQUM7UUFDeEQsQ0FBQyxDQUFDO1FBQ0YsU0FBUyxDQUFDLFVBQVUsQ0FBQyxDQUFDO0lBQ3ZCLENBQUM7SUFFRDs7T0FFRztJQUNLLFNBQVMsQ0FBRSxJQUFhLEVBQUUsVUFBeUIsRUFBRSxZQUFrQztRQUM5Rix3RUFBd0U7UUFDeEUsd0VBQXdFO1FBQ3hFLElBQUksQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDeEIsSUFBSSxDQUFDLHdCQUF3QixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ3BDLElBQUksQ0FBQyxzQkFBc0IsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFDOUMsSUFBSSxDQUFDLDRCQUE0QixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ3hDLElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUVuQywyQkFBMkI7UUFDM0IsSUFBSSxJQUFJLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDN0IsSUFBSSxDQUFDLGlCQUFpQixDQUFDLElBQXlCLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFDL0QsQ0FBQztRQUVELHlCQUF5QjtRQUN6QixJQUFJLElBQUksQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUMzQixJQUFJLENBQUMsZUFBZSxDQUFDLElBQXlCLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFDN0QsQ0FBQztRQUVELGlDQUFpQztRQUNqQyxJQUFJLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ3BDLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxJQUFvQixFQUFFLFVBQVUsRUFBRSxZQUFZLENBQUMsQ0FBQztRQUMvRSxDQUFDO1FBRUQsNkRBQTZEO1FBQzdELElBQUksQ0FBQyxZQUFZLENBQUMsSUFBSSxFQUFFLFVBQVUsQ0FBQyxDQUFDO1FBRXBDLHdEQUF3RDtRQUN4RCxJQUFJLENBQUMsVUFBVSxDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsQ0FBQztRQUVsQyx1RUFBdUU7UUFDdkUsSUFBSSxDQUFDLFdBQVcsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFFbkMsa0VBQWtFO1FBQ2xFLGdEQUFnRDtRQUNoRCxJQUFJLENBQUMsc0JBQXNCLENBQUMsSUFBSSxFQUFFLFVBQVUsQ0FBQyxDQUFDO1FBRTlDLHNFQUFzRTtRQUN0RSxzRUFBc0U7UUFDdEUsSUFBSSxDQUFDLDhCQUE4QixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzFDLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNyQyxJQUFJLENBQUMsMkJBQTJCLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDdkMsSUFBSSxDQUFDLDZCQUE2QixDQUFDLElBQUksQ0FBQyxDQUFDO1FBRXpDLGdFQUFnRTtRQUNoRSw4REFBOEQ7UUFDOUQsSUFBSSxFQUFFLENBQUMscUJBQXFCLENBQUMsSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ2pELE1BQU0sR0FBRyxHQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ3ZELElBQUksQ0FBQyxnQkFBZ0IsQ0FBQyxHQUFHLENBQUMsR0FBRyxFQUFFLElBQUksQ0FBQyxDQUFDO1FBQ3RDLENBQUM7UUFDRCxJQUNDLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLENBQUM7WUFDOUIsRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1lBQzFCLElBQUksQ0FBQyxXQUFXO1lBQ2hCLENBQUMsRUFBRSxDQUFDLGVBQWUsQ0FBQyxJQUFJLENBQUMsV0FBVyxDQUFDLElBQUksRUFBRSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQyxXQUFXLENBQUMsQ0FBQyxFQUNsRixDQUFDO1lBQ0YsTUFBTSxHQUFHLEdBQUcsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDdkQsSUFBSSxDQUFDLGdCQUFnQixDQUFDLEdBQUcsQ0FBQyxHQUFHLEVBQUUsSUFBSSxDQUFDLFdBQVcsQ0FBQyxDQUFDO1FBQ2xELENBQUM7UUFFRCx1REFBdUQ7UUFDdkQsSUFBSSxFQUFFLENBQUMsa0JBQWtCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUNqQyx3REFBd0Q7WUFDeEQsRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLEVBQUUsS0FBSyxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLEtBQUssRUFBRSxVQUFVLEVBQUUsSUFBSSxDQUFDLENBQUMsQ0FBQztRQUN6RSxDQUFDO2FBQU0sQ0FBQztZQUNQLDZCQUE2QjtZQUM3QixFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksRUFBRSxLQUFLLENBQUMsRUFBRSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsS0FBSyxFQUFFLFVBQVUsRUFBRSxZQUFZLENBQUMsQ0FBQyxDQUFDO1FBQ2pGLENBQUM7SUFDRixDQUFDO0lBRU8sdUJBQXVCLENBQUUsSUFBYTtRQUM3QyxJQUFJLElBQXdCLENBQUM7UUFDN0IsSUFBSSxPQUF1QyxDQUFDO1FBQzVDLElBQUksRUFBRSxDQUFDLHFCQUFxQixDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxXQUFXLEVBQUUsQ0FBQztZQUN0RixJQUFJLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7WUFDdEIsT0FBTyxHQUFHLElBQUksQ0FBQyxXQUFXLENBQUM7UUFDNUIsQ0FBQzthQUFNLElBQUksQ0FBQyxFQUFFLENBQUMscUJBQXFCLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDLGtCQUFrQixDQUFDLElBQUksQ0FBQyxDQUFDLElBQUksSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ3pGLElBQUksR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztZQUN0QixPQUFPLEdBQUcsSUFBSSxDQUFDO1FBQ2hCLENBQUM7UUFDRCxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsT0FBTyxFQUFFLENBQUM7WUFDdkIsT0FBTztRQUNSLENBQUM7UUFDRCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUM7UUFDaEQsSUFBSSxRQUFRLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsQ0FBQztRQUN0RCxJQUFJLENBQUMsUUFBUSxFQUFFLENBQUM7WUFDZixRQUFRLEdBQUcsSUFBSSxHQUFHLEVBQThCLENBQUM7WUFDakQsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsUUFBUSxDQUFDLENBQUM7UUFDbEQsQ0FBQztRQUNELFFBQVEsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLE9BQU8sQ0FBQyxDQUFDO0lBQzdCLENBQUM7SUFFRDs7O09BR0c7SUFDSyxZQUFZLENBQUUsSUFBYTtRQUNsQyxJQUFJLENBQUMsRUFBRSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDbkMsT0FBTztRQUNSLENBQUM7UUFFRCxNQUFNLEVBQUUsZUFBZSxFQUFFLEdBQUcsSUFBSSxDQUFDO1FBQ2pDLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxlQUFlLENBQUMsSUFBSSxlQUFlLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQ3RGLElBQUksT0FBTyxHQUFHLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLHlCQUF5QixDQUFDLENBQUM7WUFDNUUsSUFBSSxDQUFDLE9BQU8sRUFBRSxDQUFDO2dCQUNkLE9BQU8sR0FBRyxJQUFJLEdBQUcsRUFBVSxDQUFDO2dCQUM1QixJQUFJLENBQUMsb0JBQW9CLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyx5QkFBeUIsRUFBRSxPQUFPLENBQUMsQ0FBQztZQUN4RSxDQUFDO1lBQ0QsTUFBTSxlQUFlLEdBQUcsSUFBSSxDQUFDLFlBQVksQ0FBQztZQUMxQyxJQUFJLGVBQWUsRUFBRSxJQUFJLEVBQUUsQ0FBQztnQkFDM0IsT0FBTyxDQUFDLEdBQUcsQ0FBQyxlQUFlLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ3hDLENBQUM7WUFDRCxJQUFJLGVBQWUsRUFBRSxhQUFhLElBQUksRUFBRSxDQUFDLGNBQWMsQ0FBQyxlQUFlLENBQUMsYUFBYSxDQUFDLEVBQUUsQ0FBQztnQkFDeEYsS0FBSyxNQUFNLE9BQU8sSUFBSSxlQUFlLENBQUMsYUFBYSxDQUFDLFFBQVEsRUFBRSxDQUFDO29CQUM5RCxPQUFPLENBQUMsR0FBRyxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7Z0JBQ2hDLENBQUM7WUFDRixDQUFDO1lBQ0QsSUFBSSxlQUFlLEVBQUUsYUFBYSxJQUFJLEVBQUUsQ0FBQyxpQkFBaUIsQ0FBQyxlQUFlLENBQUMsYUFBYSxDQUFDLEVBQUUsQ0FBQztnQkFDM0YsT0FBTyxDQUFDLEdBQUcsQ0FBQyxlQUFlLENBQUMsYUFBYSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUN0RCxDQUFDO1FBQ0YsQ0FBQztRQUNELElBQUksQ0FBQyxFQUFFLENBQUMsZUFBZSxDQUFDLGVBQWUsQ0FBQyxJQUFJLGVBQWUsQ0FBQyxJQUFJLEtBQUssV0FBVyxFQUFFLENBQUM7WUFDbEYsT0FBTztRQUNSLENBQUM7UUFFRCxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsWUFBWSxDQUFDO1FBQ2pDLElBQUksQ0FBQyxNQUFNLEVBQUUsQ0FBQztZQUNiLE9BQU87UUFDUixDQUFDO1FBRUQsK0RBQStEO1FBQy9ELElBQUksTUFBTSxDQUFDLGFBQWEsSUFBSSxFQUFFLENBQUMsY0FBYyxDQUFDLE1BQU0sQ0FBQyxhQUFhLENBQUMsRUFBRSxDQUFDO1lBQ3JFLEtBQUssTUFBTSxPQUFPLElBQUksTUFBTSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsQ0FBQztnQkFDckQsTUFBTSxTQUFTLEdBQUcsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7Z0JBQ3BDLE1BQU0sWUFBWSxHQUFHLE9BQU8sQ0FBQyxZQUFZO29CQUN4QyxDQUFDLENBQUMsT0FBTyxDQUFDLFlBQVksQ0FBQyxJQUFJO29CQUMzQixDQUFDLENBQUMsU0FBUyxDQUFDO2dCQUNiLElBQUksWUFBWSxLQUFLLFdBQVcsRUFBRSxDQUFDO29CQUNsQyxJQUFJLENBQUMscUJBQXFCLENBQUMsR0FBRyxDQUFDLFNBQVMsQ0FBQyxDQUFDO2dCQUMzQyxDQUFDO2dCQUNELElBQUksWUFBWSxLQUFLLHVCQUF1QixFQUFFLENBQUM7b0JBQzlDLElBQUksQ0FBQyw4QkFBOEIsQ0FBQyxHQUFHLENBQUMsU0FBUyxDQUFDLENBQUM7Z0JBQ3BELENBQUM7Z0JBQ0QsSUFBSSxXQUFXLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMseUJBQXlCLENBQUMsQ0FBQztnQkFDakYsSUFBSSxDQUFDLFdBQVcsRUFBRSxDQUFDO29CQUNsQixXQUFXLEdBQUcsSUFBSSxHQUFHLEVBQWtCLENBQUM7b0JBQ3hDLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLHlCQUF5QixFQUFFLFdBQVcsQ0FBQyxDQUFDO2dCQUM3RSxDQUFDO2dCQUNELFdBQVcsQ0FBQyxHQUFHLENBQUMsU0FBUyxFQUFFLFlBQVksQ0FBQyxDQUFDO1lBQzFDLENBQUM7UUFDRixDQUFDO1FBRUQseUNBQXlDO1FBQ3pDLElBQUksTUFBTSxDQUFDLGFBQWEsSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsTUFBTSxDQUFDLGFBQWEsQ0FBQyxFQUFFLENBQUM7WUFDeEUsSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxNQUFNLENBQUMsYUFBYSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNoRSxDQUFDO1FBRUQsa0ZBQWtGO1FBQ2xGLElBQUksTUFBTSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ2pCLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNsRCxDQUFDO0lBQ0YsQ0FBQztJQUVEOzs7T0FHRztJQUNLLDhCQUE4QixDQUFFLElBQWE7UUFDcEQsNkRBQTZEO1FBQzdELGlFQUFpRTtRQUNqRSxnRUFBZ0U7UUFDaEUsa0NBQWtDO1FBQ2xDLElBQUksRUFBRSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztZQUM3RCxJQUFJLENBQUMsSUFBSSxJQUFJLEVBQUUsQ0FBQyxhQUFhLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDM0MsTUFBTSxpQkFBaUIsR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUM7WUFDekQsSUFBSSxVQUFVLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLEdBQUcsQ0FBQyxpQkFBaUIsQ0FBQyxDQUFDO1lBQ3RFLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztnQkFDakIsVUFBVSxHQUFHLElBQUksR0FBRyxFQUFnQyxDQUFDO2dCQUNyRCxJQUFJLENBQUMsd0JBQXdCLENBQUMsR0FBRyxDQUFDLGlCQUFpQixFQUFFLFVBQVUsQ0FBQyxDQUFDO1lBQ2xFLENBQUM7WUFDRCxVQUFVLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxDQUFDO1lBQ3JDLE9BQU87UUFDUixDQUFDO1FBRUQsSUFBSSxJQUFJLEdBQUcsRUFBRSxDQUFDO1FBQ2QsSUFBSSxJQUFtRCxDQUFDO1FBQ3hELElBQUksUUFBdUQsQ0FBQztRQUU1RCxJQUFJLEVBQUUsQ0FBQyxzQkFBc0IsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ25FLElBQUksR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztZQUN0QixJQUFJLEdBQUcsT0FBTyxDQUFDO1lBQ2YsUUFBUSxHQUFHLElBQUksQ0FBQztRQUNqQixDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsa0JBQWtCLENBQUMsSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ3JELElBQUksR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztZQUN0QixJQUFJLEdBQUcsT0FBTyxDQUFDO1lBQ2YsUUFBUSxHQUFHLElBQUksQ0FBQztRQUNqQixDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsc0JBQXNCLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUMxRSxJQUFJLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7WUFDdEIsSUFBSSxHQUFHLFdBQVcsQ0FBQztZQUNuQixRQUFRLEdBQUcsSUFBSSxDQUFDO1FBQ2pCLENBQUM7UUFFRCxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsUUFBUSxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDakMsT0FBTztRQUNSLENBQUM7UUFFRCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUM7UUFDaEQsSUFBSSxLQUFLLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsQ0FBQztRQUNuRCxJQUFJLENBQUMsS0FBSyxFQUFFLENBQUM7WUFDWixLQUFLLEdBQUcsSUFBSSxHQUFHLEVBQXFDLENBQUM7WUFDckQsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsS0FBSyxDQUFDLENBQUM7UUFDL0MsQ0FBQztRQUNELE1BQU0sS0FBSyxHQUE4QixFQUFFLElBQUksRUFBRSxJQUFJLEVBQUcsUUFBUSxFQUFFLElBQUksRUFBRyxRQUFRLEVBQUUsQ0FBQztRQUNwRixLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxLQUFLLENBQUMsQ0FBQztRQUV2QixzRUFBc0U7UUFDdEUsZ0NBQWdDO1FBQ2hDLElBQUksSUFBSSxLQUFLLE9BQU8sRUFBRSxDQUFDO1lBQ3RCLE1BQU0sU0FBUyxHQUFHLFFBQStCLENBQUM7WUFDbEQsTUFBTSxVQUFVLEdBQUcsU0FBUyxDQUFDLFNBQVMsRUFBRSxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsYUFBYSxDQUFDLElBQUksS0FBSyxDQUFDO1lBQ25HLE1BQU0sU0FBUyxHQUFHLFNBQVMsQ0FBQyxTQUFTLEVBQUUsSUFBSSxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGNBQWMsQ0FBQyxJQUFJLEtBQUssQ0FBQztZQUNuRyxJQUFJLFVBQVUsSUFBSSxTQUFTLEVBQUUsQ0FBQztnQkFDN0IsS0FBSyxDQUFDLEdBQUcsQ0FBQyxTQUFTLEVBQUUsS0FBSyxDQUFDLENBQUM7WUFDN0IsQ0FBQztRQUNGLENBQUM7SUFDRixDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNLLDZCQUE2QixDQUFFLElBQWE7UUFDbkQsSUFBSSxDQUFDLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLFdBQVcsRUFBRSxDQUFDO1lBQ3pGLE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxFQUFFLFdBQVcsRUFBRSxjQUFjLEVBQUUsR0FBRyxJQUFJLENBQUM7UUFDN0MsSUFBSSxXQUFXLEdBQWtCLGNBQWMsQ0FBQztRQUNoRCxPQUNDLEVBQUUsQ0FBQyxjQUFjLENBQUMsV0FBVyxDQUFDO1lBQzlCLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxXQUFXLENBQUM7WUFDckMsNkRBQTZEO1lBQzdELHVEQUF1RDtZQUN2RCxFQUFFLENBQUMseUJBQXlCLENBQUMsV0FBVyxDQUFDLEVBQ3hDLENBQUM7WUFDRixXQUFXLEdBQUcsV0FBVyxDQUFDLFVBQVUsQ0FBQztRQUN0QyxDQUFDO1FBQ0QsSUFBSSxDQUFDLEVBQUUsQ0FBQyx3QkFBd0IsQ0FBQyxXQUFXLENBQUMsRUFBRSxDQUFDO1lBQy9DLE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDO1FBQ2hELElBQUksTUFBTSxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLENBQUM7UUFDMUQsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDO1lBQ2IsTUFBTSxHQUFHLElBQUksR0FBRyxFQUFxQyxDQUFDO1lBQ3RELElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxFQUFFLE1BQU0sQ0FBQyxDQUFDO1FBQ3RELENBQUM7UUFDRCxJQUFJLENBQUMsTUFBTSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDakMsTUFBTSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxXQUFXLENBQUMsQ0FBQztRQUN6QyxDQUFDO0lBQ0YsQ0FBQztJQUVEOzs7Ozs7T0FNRztJQUNLLHdCQUF3QixDQUMvQixJQUFZLEVBQ1osUUFBZ0I7UUFFaEIsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsRUFBRSxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDdEUsSUFBSSxLQUFLLEVBQUUsQ0FBQztZQUNYLE9BQU8sS0FBSyxDQUFDO1FBQ2QsQ0FBQztRQUNELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ3JFLElBQUksQ0FBQyxRQUFRLElBQUksUUFBUSxDQUFDLFdBQVcsRUFBRSxDQUFDO1lBQ3ZDLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsMkJBQTJCLENBQUMsUUFBUSxDQUFDLFNBQVMsRUFBRSxRQUFRLENBQUMsQ0FBQztRQUNsRixJQUFJLENBQUMsVUFBVSxJQUFJLFVBQVUsQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUMxQyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBQ0QsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsWUFBWSxDQUFDLEVBQUUsR0FBRyxDQUFDLFFBQVEsQ0FBQyxZQUFZLENBQUMsQ0FBQztRQUN0RyxPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7SUFFRDs7Ozs7OztPQU9HO0lBQ0ssbUJBQW1CLENBQUUsWUFBdUM7UUFDbkUsTUFBTSxRQUFRLEdBQWEsRUFBRSxDQUFDO1FBQzlCLEtBQUssTUFBTSxPQUFPLElBQUksWUFBWSxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQzdDLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO2dCQUNqQyxPQUFPLFNBQVMsQ0FBQztZQUNsQixDQUFDO1lBQ0QsTUFBTSxPQUFPLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLE9BQU8sQ0FBQyxDQUFDO1lBQ3RELElBQUksT0FBTyxLQUFLLFNBQVMsRUFBRSxDQUFDO2dCQUMzQixPQUFPLFNBQVMsQ0FBQztZQUNsQixDQUFDO1lBQ0QsUUFBUSxDQUFDLElBQUksQ0FBQyxPQUFPLENBQUMsQ0FBQztRQUN4QixDQUFDO1FBQ0QsSUFBSSxRQUFRLENBQUMsTUFBTSxLQUFLLENBQUMsRUFBRSxDQUFDO1lBQzNCLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLE1BQU0sR0FBRyxRQUFRLENBQUM7UUFDeEIsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7Ozs7O09BS0c7SUFDSyx1QkFBdUIsQ0FBRSxJQUFtQjtRQUNuRCxJQUFJLEtBQUssR0FBa0IsSUFBSSxDQUFDO1FBQ2hDLE9BQU8sRUFBRSxDQUFDLGNBQWMsQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLENBQUMscUJBQXFCLENBQUMsS0FBSyxDQUFDLElBQUksRUFBRSxDQUFDLHlCQUF5QixDQUFDLEtBQUssQ0FBQyxFQUFFLENBQUM7WUFDM0csS0FBSyxHQUFHLEtBQUssQ0FBQyxVQUFVLENBQUM7UUFDMUIsQ0FBQztRQUNELElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLENBQUMsK0JBQStCLENBQUMsS0FBSyxDQUFDLEVBQUUsQ0FBQztZQUM1RSxNQUFNLE9BQU8sR0FBRyxJQUFJLEtBQUssQ0FBQyxJQUFJLEdBQUcsQ0FBQztZQUNsQyxPQUFPLE9BQU8sQ0FBQztRQUNoQixDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsdUJBQXVCLENBQUMsS0FBSyxDQUFDLElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLEtBQUssQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO1lBQzdFLElBQUksS0FBSyxDQUFDLFFBQVEsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFVBQVUsRUFBRSxDQUFDO2dCQUNqRCxNQUFNLFFBQVEsR0FBRyxJQUFJLEtBQUssQ0FBQyxPQUFPLENBQUMsSUFBSSxFQUFFLENBQUM7Z0JBQzFDLE9BQU8sUUFBUSxDQUFDO1lBQ2pCLENBQUM7WUFDRCxJQUFJLEtBQUssQ0FBQyxRQUFRLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxTQUFTLEVBQUUsQ0FBQztnQkFDaEQsT0FBTyxLQUFLLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQztZQUMzQixDQUFDO1lBQ0QsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLEtBQUssQ0FBQyxFQUFFLENBQUM7WUFDaEMsT0FBTyxLQUFLLENBQUMsSUFBSSxDQUFDO1FBQ25CLENBQUM7UUFDRCxJQUFJLEtBQUssQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxXQUFXLEVBQUUsQ0FBQztZQUM5QyxPQUFPLE1BQU0sQ0FBQztRQUNmLENBQUM7UUFDRCxJQUFJLEtBQUssQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxZQUFZLEVBQUUsQ0FBQztZQUMvQyxPQUFPLE9BQU8sQ0FBQztRQUNoQixDQUFDO1FBQ0QsSUFBSSxLQUFLLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVyxFQUFFLENBQUM7WUFDOUMsT0FBTyxNQUFNLENBQUM7UUFDZixDQUFDO1FBQ0QsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7OztPQUtHO0lBQ0ssb0JBQW9CLENBQUUsSUFBaUI7UUFDOUMsTUFBTSxjQUFjLEdBQUcsRUFBRSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQztZQUNsRCxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUM7WUFDOUIsSUFBSSxDQUFDLFFBQVEsQ0FBQyxJQUFJLEtBQUssT0FBTyxDQUFDO1FBQ2hDLE9BQU8sY0FBYyxDQUFDO0lBQ3ZCLENBQUM7SUFFRDs7Ozs7O09BTUc7SUFDSyxtQkFBbUIsQ0FBRSxJQUFtQjtRQUMvQyxJQUFJLE9BQU8sR0FBa0IsSUFBSSxDQUFDO1FBQ2xDLE9BQU8sRUFBRSxDQUFDLHlCQUF5QixDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7WUFDOUMsT0FBTyxHQUFHLE9BQU8sQ0FBQyxVQUFVLENBQUM7UUFDOUIsQ0FBQztRQUNELElBQUksRUFBRSxDQUFDLHdCQUF3QixDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7WUFDMUMsT0FBTyxPQUFPLENBQUM7UUFDaEIsQ0FBQztRQUNELElBQUksQ0FBQyxFQUFFLENBQUMsY0FBYyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsQ0FBQyx5QkFBeUIsQ0FBQyxPQUFPLENBQUMsQ0FBQztZQUN4RSxJQUFJLENBQUMsb0JBQW9CLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDMUMsTUFBTSxLQUFLLEdBQUcsT0FBTyxDQUFDLFVBQVUsQ0FBQztZQUNqQyxNQUFNLE9BQU8sR0FBRyxFQUFFLENBQUMsd0JBQXdCLENBQUMsS0FBSyxDQUFDLENBQUMsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLENBQUMsU0FBUyxDQUFDO1lBQ3ZFLE9BQU8sT0FBTyxDQUFDO1FBQ2hCLENBQUM7UUFDRCxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsT0FBTyxDQUFDLEVBQUUsQ0FBQztZQUM5QixNQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDdEcsT0FBTyxPQUFPLENBQUM7UUFDaEIsQ0FBQztRQUNELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7Ozs7OztPQU9HO0lBQ0sscUJBQXFCLENBQUUsSUFBWSxFQUFFLFFBQWdCO1FBQzVELE1BQU0sWUFBWSxHQUFHLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxJQUFJLEVBQUUsUUFBUSxDQUFDLENBQUM7UUFDbkUsSUFBSSxDQUFDLFlBQVksRUFBRSxDQUFDO1lBQ25CLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsWUFBWSxDQUFDLENBQUM7UUFDeEQsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQ2YsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELE1BQU0sS0FBSyxHQUFHLFFBQVEsQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7UUFDbkMsT0FBTyxLQUFLLENBQUM7SUFDZCxDQUFDO0lBRUQ7Ozs7T0FJRztJQUNLLHlCQUF5QixDQUFFLElBQWE7UUFDL0MsSUFBSSxDQUFDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ25DLE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxFQUFFLGVBQWUsRUFBRSxHQUFHLElBQUksQ0FBQztRQUNqQyxJQUFJLENBQUMsRUFBRSxDQUFDLGVBQWUsQ0FBQyxlQUFlLENBQUMsRUFBRSxDQUFDO1lBQzFDLE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLFlBQVksQ0FBQztRQUNqQyxJQUFJLENBQUMsTUFBTSxFQUFFLENBQUM7WUFDYixPQUFPO1FBQ1IsQ0FBQztRQUVELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQztRQUNoRCxJQUFJLE9BQU8sR0FBRyxJQUFJLENBQUMscUJBQXFCLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxDQUFDO1FBQ3ZELElBQUksQ0FBQyxPQUFPLEVBQUUsQ0FBQztZQUNkLE9BQU8sR0FBRyxJQUFJLEdBQUcsRUFBZ0MsQ0FBQztZQUNsRCxJQUFJLENBQUMscUJBQXFCLENBQUMsR0FBRyxDQUFDLFFBQVEsRUFBRSxPQUFPLENBQUMsQ0FBQztRQUNuRCxDQUFDO1FBRUQseUVBQXlFO1FBQ3pFLElBQUksTUFBTSxDQUFDLGFBQWEsSUFBSSxFQUFFLENBQUMsY0FBYyxDQUFDLE1BQU0sQ0FBQyxhQUFhLENBQUMsRUFBRSxDQUFDO1lBQ3JFLEtBQUssTUFBTSxPQUFPLElBQUksTUFBTSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsQ0FBQztnQkFDckQsTUFBTSxTQUFTLEdBQUcsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7Z0JBQ3BDLE1BQU0sWUFBWSxHQUFHLE9BQU8sQ0FBQyxZQUFZLENBQUMsQ0FBQyxDQUFDLE9BQU8sQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUM7Z0JBQ2xGLE9BQU8sQ0FBQyxHQUFHLENBQUMsU0FBUyxFQUFFO29CQUN0QixZQUFZO29CQUNaLFNBQVMsRUFBSyxlQUFlLENBQUMsSUFBSTtvQkFDbEMsV0FBVyxFQUFHLEtBQUs7aUJBQ25CLENBQUMsQ0FBQztZQUNKLENBQUM7UUFDRixDQUFDO1FBRUQsK0RBQStEO1FBQy9ELHNDQUFzQztRQUN0QyxJQUFJLE1BQU0sQ0FBQyxhQUFhLElBQUksRUFBRSxDQUFDLGlCQUFpQixDQUFDLE1BQU0sQ0FBQyxhQUFhLENBQUMsRUFBRSxDQUFDO1lBQ3hFLE9BQU8sQ0FBQyxHQUFHLENBQUMsTUFBTSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFO2dCQUMzQyxZQUFZLEVBQUcsRUFBRTtnQkFDakIsU0FBUyxFQUFNLGVBQWUsQ0FBQyxJQUFJO2dCQUNuQyxXQUFXLEVBQUksSUFBSTthQUNuQixDQUFDLENBQUM7UUFDSixDQUFDO1FBRUQsK0NBQStDO1FBQy9DLElBQUksTUFBTSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ2pCLE9BQU8sQ0FBQyxHQUFHLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUU7Z0JBQzdCLFlBQVksRUFBRyxTQUFTO2dCQUN4QixTQUFTLEVBQU0sZUFBZSxDQUFDLElBQUk7Z0JBQ25DLFdBQVcsRUFBSSxLQUFLO2FBQ3BCLENBQUMsQ0FBQztRQUNKLENBQUM7SUFDRixDQUFDO0lBRUQ7Ozs7T0FJRztJQUNLLDJCQUEyQixDQUFFLElBQWE7UUFDakQsSUFBSSxDQUFDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ25DLE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDO1FBQ2hELE1BQU0sRUFBRSxlQUFlLEVBQUUsR0FBRyxJQUFJLENBQUM7UUFDakMsTUFBTSxhQUFhLEdBQUcsZUFBZSxJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsZUFBZSxDQUFDO1lBQzNFLENBQUMsQ0FBQyxlQUFlLENBQUMsSUFBSTtZQUN0QixDQUFDLENBQUMsU0FBUyxDQUFDO1FBRWIsSUFBSSxJQUFJLENBQUMsWUFBWSxJQUFJLEVBQUUsQ0FBQyxjQUFjLENBQUMsSUFBSSxDQUFDLFlBQVksQ0FBQyxFQUFFLENBQUM7WUFDL0QsS0FBSyxNQUFNLE9BQU8sSUFBSSxJQUFJLENBQUMsWUFBWSxDQUFDLFFBQVEsRUFBRSxDQUFDO2dCQUNsRCxNQUFNLFlBQVksR0FBRyxPQUFPLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztnQkFDdkMsTUFBTSxTQUFTLEdBQUcsT0FBTyxDQUFDLFlBQVksQ0FBQyxDQUFDLENBQUMsT0FBTyxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLFlBQVksQ0FBQztnQkFDbEYsSUFBSSxDQUFDLGlCQUFpQixDQUFDLFlBQVksRUFBRSxTQUFTLEVBQUUsUUFBUSxFQUFFLGFBQWEsQ0FBQyxDQUFDO2dCQUN6RSxJQUFJLGFBQWEsRUFBRSxDQUFDO29CQUNuQixxREFBcUQ7b0JBQ3JELElBQUksU0FBUyxHQUFHLElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLENBQUM7b0JBQzNELElBQUksQ0FBQyxTQUFTLEVBQUUsQ0FBQzt3QkFDaEIsU0FBUyxHQUFHLElBQUksR0FBRyxFQUFrQixDQUFDO3dCQUN0QyxJQUFJLENBQUMsdUJBQXVCLENBQUMsR0FBRyxDQUFDLFFBQVEsRUFBRSxTQUFTLENBQUMsQ0FBQztvQkFDdkQsQ0FBQztvQkFDRCxTQUFTLENBQUMsR0FBRyxDQUFDLFlBQVksRUFBRSxhQUFhLENBQUMsQ0FBQztnQkFDNUMsQ0FBQztxQkFBTSxJQUFJLFNBQVMsS0FBSyxZQUFZLEVBQUUsQ0FBQztvQkFDdkMsNkRBQTZEO29CQUM3RCxJQUFJLE9BQU8sR0FBRyxJQUFJLENBQUMsMkJBQTJCLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxDQUFDO29CQUM3RCxJQUFJLENBQUMsT0FBTyxFQUFFLENBQUM7d0JBQ2QsT0FBTyxHQUFHLElBQUksR0FBRyxFQUFrQixDQUFDO3dCQUNwQyxJQUFJLENBQUMsMkJBQTJCLENBQUMsR0FBRyxDQUFDLFFBQVEsRUFBRSxPQUFPLENBQUMsQ0FBQztvQkFDekQsQ0FBQztvQkFDRCxPQUFPLENBQUMsR0FBRyxDQUFDLFlBQVksRUFBRSxTQUFTLENBQUMsQ0FBQztnQkFDdEMsQ0FBQztZQUNGLENBQUM7WUFDRCxPQUFPO1FBQ1IsQ0FBQztRQUVELElBQUksSUFBSSxDQUFDLFlBQVksSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsSUFBSSxDQUFDLFlBQVksQ0FBQyxFQUFFLENBQUM7WUFDbEUsZ0VBQWdFO1lBQ2hFLGlFQUFpRTtZQUNqRSxJQUFJLGFBQWEsRUFBRSxDQUFDO2dCQUNuQixJQUFJLEtBQUssR0FBRyxJQUFJLENBQUMsNEJBQTRCLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxDQUFDO2dCQUM1RCxJQUFJLENBQUMsS0FBSyxFQUFFLENBQUM7b0JBQ1osS0FBSyxHQUFHLElBQUksR0FBRyxFQUFrQixDQUFDO29CQUNsQyxJQUFJLENBQUMsNEJBQTRCLENBQUMsR0FBRyxDQUFDLFFBQVEsRUFBRSxLQUFLLENBQUMsQ0FBQztnQkFDeEQsQ0FBQztnQkFDRCxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxhQUFhLENBQUMsQ0FBQztZQUN2RCxDQUFDO1lBQ0QsT0FBTztRQUNSLENBQUM7UUFFRCxJQUFJLENBQUMsSUFBSSxDQUFDLFlBQVksSUFBSSxhQUFhLEVBQUUsQ0FBQztZQUN6QyxvQkFBb0I7WUFDcEIsSUFBSSxLQUFLLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsQ0FBQztZQUN6RCxJQUFJLENBQUMsS0FBSyxFQUFFLENBQUM7Z0JBQ1osS0FBSyxHQUFHLEVBQUUsQ0FBQztnQkFDWCxJQUFJLENBQUMseUJBQXlCLENBQUMsR0FBRyxDQUFDLFFBQVEsRUFBRSxLQUFLLENBQUMsQ0FBQztZQUNyRCxDQUFDO1lBQ0QsS0FBSyxDQUFDLElBQUksQ0FBQyxhQUFhLENBQUMsQ0FBQztRQUMzQixDQUFDO0lBQ0YsQ0FBQztJQUVEOzs7O09BSUc7SUFDSywyQkFBMkIsQ0FBRSxTQUFpQixFQUFFLGNBQXNCO1FBRTdFLE1BQU0sUUFBUSxHQUFHLEdBQUcsY0FBYyxLQUFLLFNBQVMsRUFBRSxDQUFDO1FBQ25ELElBQUksSUFBSSxDQUFDLDZCQUE2QixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO1lBQ3RELE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyw2QkFBNkIsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLENBQUM7WUFDaEUsT0FBTyxNQUFNLEtBQUssU0FBUyxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUMsQ0FBQyxDQUFDLE1BQU0sQ0FBQztRQUNsRCxDQUFDO1FBRUQsTUFBTSxVQUFVLEdBQUcsRUFBRSxDQUFDLGlCQUFpQixDQUN0QyxTQUFTLEVBQ1QsY0FBYyxFQUNkLElBQUksQ0FBQyw2QkFBNkIsRUFDbEMsRUFBRSxDQUFDLEdBQUcsQ0FDTixDQUFDLGNBQWMsQ0FBQztRQUVqQixNQUFNLE1BQU0sR0FBeUMsVUFBVTtZQUM5RCxDQUFDLENBQUM7Z0JBQ0QsWUFBWSxFQUFHLFFBQVEsQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLGdCQUFnQixDQUFDO2dCQUM1RCxVQUFVLEVBQUssQ0FBQyxDQUFDLFVBQVUsQ0FBQyx1QkFBdUI7YUFDbkQ7WUFDRCxDQUFDLENBQUMsU0FBUyxDQUFDO1FBRWIsSUFBSSxDQUFDLDZCQUE2QixDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsTUFBTSxDQUFDLENBQUM7UUFDekQsTUFBTSxXQUFXLEdBQUcsTUFBTSxDQUFDO1FBQzNCLE9BQU8sV0FBVyxDQUFDO0lBQ3BCLENBQUM7SUFFRDs7OztPQUlHO0lBQ0ssMEJBQTBCLENBQ2pDLFVBQWtCLEVBQ2xCLElBQVksRUFDWixLQUFhO1FBRWIsSUFBSSxLQUFLLEdBQUcsd0JBQXdCLEVBQUUsQ0FBQztZQUN0QyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsQ0FBQztRQUN2RCxNQUFNLE1BQU0sR0FBRyxLQUFLLEVBQUUsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ2hDLElBQUksTUFBTSxFQUFFLENBQUM7WUFDWixPQUFPLE1BQU0sQ0FBQztRQUNmLENBQUM7UUFDRCxxREFBcUQ7UUFDckQsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLDJCQUEyQixDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsRUFBRSxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDL0UsSUFBSSxVQUFVLEVBQUUsQ0FBQztZQUNoQixNQUFNLE9BQU8sR0FBRyxLQUFLLEVBQUUsR0FBRyxDQUFDLFVBQVUsQ0FBQyxDQUFDO1lBQ3ZDLElBQUksT0FBTyxFQUFFLENBQUM7Z0JBQ2IsT0FBTyxPQUFPLENBQUM7WUFDaEIsQ0FBQztRQUNGLENBQUM7UUFFRCxNQUFNLFNBQVMsR0FBRyxJQUFJLENBQUMsdUJBQXVCLENBQUMsR0FBRyxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQy9ELE1BQU0saUJBQWlCLEdBQUcsU0FBUyxFQUFFLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUMvQyxJQUFJLGlCQUFpQixFQUFFLENBQUM7WUFDdkIsTUFBTSxjQUFjLEdBQUcsSUFBSSxDQUFDLDJCQUEyQixDQUFDLGlCQUFpQixFQUFFLFVBQVUsQ0FBQyxDQUFDO1lBQ3ZGLElBQUksY0FBYyxJQUFJLENBQUMsY0FBYyxDQUFDLFVBQVUsRUFBRSxDQUFDO2dCQUNsRCxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMsMEJBQTBCLENBQUMsY0FBYyxDQUFDLFlBQVksRUFBRSxJQUFJLEVBQUUsS0FBSyxHQUFHLENBQUMsQ0FBQyxDQUFDO2dCQUM1RixJQUFJLEtBQUssRUFBRSxDQUFDO29CQUNYLE9BQU8sS0FBSyxDQUFDO2dCQUNkLENBQUM7WUFDRixDQUFDO1FBQ0YsQ0FBQztRQUVELE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxHQUFHLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDN0QsSUFBSSxLQUFLLEVBQUUsQ0FBQztZQUNYLEtBQUssTUFBTSxhQUFhLElBQUksS0FBSyxFQUFFLENBQUM7Z0JBQ25DLE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxhQUFhLEVBQUUsVUFBVSxDQUFDLENBQUM7Z0JBQ25GLElBQUksQ0FBQyxjQUFjLElBQUksY0FBYyxDQUFDLFVBQVUsRUFBRSxDQUFDO29CQUNsRCxTQUFTO2dCQUNWLENBQUM7Z0JBQ0QsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLDBCQUEwQixDQUFDLGNBQWMsQ0FBQyxZQUFZLEVBQUUsSUFBSSxFQUFFLEtBQUssR0FBRyxDQUFDLENBQUMsQ0FBQztnQkFDNUYsSUFBSSxLQUFLLEVBQUUsQ0FBQztvQkFDWCxPQUFPLEtBQUssQ0FBQztnQkFDZCxDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFFRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7Ozs7Ozs7O09BUUc7SUFDSyxnQ0FBZ0MsQ0FDdkMsSUFBWSxFQUNaLFFBQWdCO1FBRWhCLG1FQUFtRTtRQUNuRSw4REFBOEQ7UUFDOUQsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsRUFBRSxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDckUsSUFBSSxRQUFRLElBQUksQ0FBQyxRQUFRLENBQUMsV0FBVyxFQUFFLENBQUM7WUFDdkMsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLDJCQUEyQixDQUFDLFFBQVEsQ0FBQyxTQUFTLEVBQUUsUUFBUSxDQUFDLENBQUM7WUFDbEYsSUFBSSxVQUFVLElBQUksQ0FBQyxVQUFVLENBQUMsVUFBVSxFQUFFLENBQUM7Z0JBQzFDLE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQywwQkFBMEIsQ0FBQyxVQUFVLENBQUMsWUFBWSxFQUFFLFFBQVEsQ0FBQyxZQUFZLEVBQUUsQ0FBQyxDQUFDLENBQUM7Z0JBQ2pHLElBQUksS0FBSyxFQUFFLENBQUM7b0JBQ1gsT0FBTyxLQUFLLENBQUM7Z0JBQ2QsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsc0RBQXNEO1FBQ3RELE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ2hFLElBQUksS0FBSyxFQUFFLENBQUM7WUFDWCxPQUFPLEtBQUssQ0FBQztRQUNkLENBQUM7UUFFRCxvRUFBb0U7UUFDcEUsNkRBQTZEO1FBQzdELDZEQUE2RDtRQUM3RCwyREFBMkQ7UUFDM0QsNkRBQTZEO1FBQzdELDhEQUE4RDtRQUM5RCx1Q0FBdUM7UUFDdkMsSUFBSSxNQUE2QyxDQUFDO1FBQ2xELElBQUksS0FBSyxHQUFHLENBQUMsQ0FBQztRQUNkLEtBQUssTUFBTSxDQUFFLFFBQVEsRUFBRSxLQUFLLENBQUUsSUFBSSxJQUFJLENBQUMsbUJBQW1CLEVBQUUsQ0FBQztZQUM1RCxJQUFJLElBQUksQ0FBQyxrQkFBa0IsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO2dCQUN2QyxTQUFTO1lBQ1YsQ0FBQztZQUNELE1BQU0sU0FBUyxHQUFHLEtBQUssQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDbEMsSUFBSSxTQUFTLEVBQUUsQ0FBQztnQkFDZixLQUFLLEVBQUUsQ0FBQztnQkFDUixNQUFNLEdBQUcsU0FBUyxDQUFDO2dCQUNuQixJQUFJLEtBQUssR0FBRyxDQUFDLEVBQUUsQ0FBQztvQkFDZixPQUFPLFNBQVMsQ0FBQztnQkFDbEIsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsTUFBTSxNQUFNLEdBQUcsS0FBSyxLQUFLLENBQUMsQ0FBQyxDQUFDLENBQUMsTUFBTSxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUM7UUFDaEQsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7Ozs7OztPQU1HO0lBQ0ssa0JBQWtCLENBQUUsSUFBWTtRQUN2QyxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsUUFBUSxDQUFDLE9BQU8sQ0FBQztZQUN0QyxJQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsUUFBUSxDQUFDLEdBQUcsZUFBZSxRQUFRLENBQUMsR0FBRyxFQUFFLENBQUMsQ0FBQztRQUM3RCxPQUFPLFFBQVEsQ0FBQztJQUNqQixDQUFDO0lBRUQ7Ozs7OztPQU1HO0lBQ0ssK0JBQStCLENBQUUsSUFBK0I7UUFFdkUsTUFBTSxPQUFPLEdBQUcsSUFBSSxHQUFHLEVBQVUsQ0FBQztRQUNsQyxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsb0NBQW9DLENBQUMsSUFBSSxFQUFFLE9BQU8sRUFBRSxDQUFDLENBQUMsQ0FBQztRQUMvRSxPQUFPLFVBQVUsQ0FBQztJQUNuQixDQUFDO0lBRU8sb0NBQW9DLENBQzNDLElBQStCLEVBQy9CLE9BQW9CLEVBQ3BCLEtBQWE7UUFFYixNQUFNLGFBQWEsR0FBRyxJQUFJLEdBQUcsRUFBd0IsQ0FBQztRQUN0RCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsSUFBcUQsQ0FBQztRQUM1RSxNQUFNLFFBQVEsR0FBRyxRQUFRLENBQUMsSUFBSSxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxRQUFRLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDO1FBQzNGLE1BQU0sUUFBUSxHQUFHLEdBQUcsSUFBSSxDQUFDLElBQUksSUFBSSxJQUFJLENBQUMsSUFBSSxJQUFJLFFBQVEsRUFBRSxDQUFDO1FBQ3pELElBQUksS0FBSyxHQUFHLGtCQUFrQixJQUFJLE9BQU8sQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUN6RCxPQUFPLGFBQWEsQ0FBQztRQUN0QixDQUFDO1FBQ0QsT0FBTyxDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsQ0FBQztRQUV0QixJQUFJLElBQUksQ0FBQyxJQUFJLEtBQUssT0FBTyxFQUFFLENBQUM7WUFDM0IsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLHNCQUFzQixDQUFDLElBQUksQ0FBQyxJQUEyQixDQUFDLENBQUM7WUFDakYsS0FBSyxNQUFNLENBQUUsSUFBSSxFQUFFLElBQUksQ0FBRSxJQUFJLFVBQVUsRUFBRSxDQUFDO2dCQUN6QyxhQUFhLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsQ0FBQztZQUMvQixDQUFDO1FBQ0YsQ0FBQzthQUFNLElBQUksSUFBSSxDQUFDLElBQUksS0FBSyxXQUFXLEVBQUUsQ0FBQztZQUN0QyxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMsSUFBK0IsQ0FBQztZQUNuRCxJQUFJLENBQUMsNEJBQTRCLENBQUMsQ0FBRSxHQUFHLEtBQUssQ0FBQyxPQUFPLENBQUUsRUFBRSxhQUFhLENBQUMsQ0FBQztRQUN4RSxDQUFDO2FBQU0sQ0FBQztZQUNQLE1BQU0sU0FBUyxHQUFJLElBQUksQ0FBQyxJQUFnQyxDQUFDLElBQUksQ0FBQztZQUM5RCxJQUFJLEVBQUUsQ0FBQyxpQkFBaUIsQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUFDO2dCQUNyQyxJQUFJLENBQUMsNEJBQTRCLENBQUMsQ0FBRSxHQUFHLFNBQVMsQ0FBQyxPQUFPLENBQUUsRUFBRSxhQUFhLENBQUMsQ0FBQztZQUM1RSxDQUFDO2lCQUFNLENBQUM7Z0JBQ1AsT0FBTyxhQUFhLENBQUM7WUFDdEIsQ0FBQztRQUNGLENBQUM7UUFFRCxvRUFBb0U7UUFDcEUsNkRBQTZEO1FBQzdELE1BQU0sTUFBTSxHQUFHLElBQUksR0FBRyxFQUF3QixDQUFDO1FBQy9DLEtBQUssTUFBTSxRQUFRLElBQUksSUFBSSxDQUFDLDJCQUEyQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDL0QsTUFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLG9DQUFvQyxDQUFDLFFBQVEsRUFBRSxPQUFPLEVBQUUsS0FBSyxHQUFHLENBQUMsQ0FBQyxDQUFDO1lBQzFGLEtBQUssTUFBTSxDQUFFLElBQUksRUFBRSxJQUFJLENBQUUsSUFBSSxTQUFTLEVBQUUsQ0FBQztnQkFDeEMsTUFBTSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLENBQUM7WUFDeEIsQ0FBQztRQUNGLENBQUM7UUFDRCxLQUFLLE1BQU0sQ0FBRSxJQUFJLEVBQUUsSUFBSSxDQUFFLElBQUksYUFBYSxFQUFFLENBQUM7WUFDNUMsTUFBTSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLENBQUM7UUFDeEIsQ0FBQztRQUNELE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7T0FHRztJQUNLLDRCQUE0QixDQUNuQyxPQUFrQyxFQUNsQyxVQUFxQztRQUVyQyxLQUFLLE1BQU0sTUFBTSxJQUFJLE9BQU8sRUFBRSxDQUFDO1lBQzlCLElBQUksRUFBRSxDQUFDLG1CQUFtQixDQUFDLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQ3BFLE1BQU0sUUFBUSxHQUFHLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO2dCQUNsQyxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsU0FBUyxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDekMsVUFBVSxDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUU7b0JBQ3hCLElBQUksRUFBTyxRQUFRO29CQUNuQixJQUFJO29CQUNKLFFBQVEsRUFBRyxDQUFDLENBQUMsTUFBTSxDQUFDLGFBQWE7aUJBQ2pDLENBQUMsQ0FBQztZQUNKLENBQUM7UUFDRixDQUFDO0lBQ0YsQ0FBQztJQUVEOzs7Ozs7Ozs7T0FTRztJQUNLLDJCQUEyQixDQUFFLElBQStCO1FBQ25FLE1BQU0sRUFBRSxlQUFlLEVBQUUsR0FBSSxJQUFJLENBQUMsSUFBc0QsQ0FBQztRQUN6RixJQUFJLENBQUMsZUFBZSxFQUFFLENBQUM7WUFDdEIsT0FBTyxFQUFFLENBQUM7UUFDWCxDQUFDO1FBQ0QsTUFBTSxLQUFLLEdBQWdDLEVBQUUsQ0FBQztRQUM5QyxLQUFLLE1BQU0sTUFBTSxJQUFJLGVBQWUsRUFBRSxDQUFDO1lBQ3RDLElBQUksTUFBTSxDQUFDLEtBQUssS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGNBQWMsRUFBRSxDQUFDO2dCQUNuRCxTQUFTO1lBQ1YsQ0FBQztZQUNELEtBQUssTUFBTSxZQUFZLElBQUksTUFBTSxDQUFDLEtBQUssRUFBRSxDQUFDO2dCQUN6QyxJQUFJLENBQUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxZQUFZLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztvQkFDL0MsU0FBUztnQkFDVixDQUFDO2dCQUNELE1BQU0sUUFBUSxHQUFHLFlBQVksQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDO2dCQUM5QyxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsZ0NBQWdDLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDNUUsSUFBSSxRQUFRLEVBQUUsQ0FBQztvQkFDZCxLQUFLLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDO2dCQUN0QixDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFDRCxNQUFNLE1BQU0sR0FBRyxLQUFLLENBQUM7UUFDckIsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7Ozs7O09BS0c7SUFDSywrQkFBK0IsQ0FBRSxJQUErQjtRQUN2RSxNQUFNLGVBQWUsR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUM7UUFDdkQsSUFBSSxDQUFDLHlCQUF5QixHQUFHLElBQUksQ0FBQyxJQUFJLENBQUM7UUFDM0MsSUFBSSxDQUFDO1lBQ0osTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLG9DQUFvQyxDQUFDLElBQUksQ0FBQyxDQUFDO1lBQy9ELE9BQU8sTUFBTSxDQUFDO1FBQ2YsQ0FBQztnQkFBUyxDQUFDO1lBQ1YsSUFBSSxDQUFDLHlCQUF5QixHQUFHLGVBQWUsQ0FBQztRQUNsRCxDQUFDO0lBQ0YsQ0FBQztJQUVPLG9DQUFvQyxDQUFFLElBQStCO1FBQzVFLElBQUksSUFBSSxDQUFDLElBQUksS0FBSyxPQUFPLEVBQUUsQ0FBQztZQUMzQixNQUFNLFNBQVMsR0FBRyxJQUFJLENBQUMsSUFBK0IsQ0FBQztZQUN2RCxNQUFNLFNBQVMsR0FBRyxFQUFFLENBQUMsWUFBWSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQztZQUM3RSxJQUFJLFNBQVMsSUFBSSxJQUFJLENBQUMsMEJBQTBCLENBQUMsR0FBRyxDQUFDLFNBQVMsQ0FBQyxFQUFFLENBQUM7Z0JBQ2pFLDBDQUEwQztnQkFDMUMsT0FBTyxTQUFTLENBQUM7WUFDbEIsQ0FBQztZQUNELElBQUksU0FBUyxFQUFFLENBQUM7Z0JBQ2YsSUFBSSxDQUFDLDBCQUEwQixDQUFDLEdBQUcsQ0FBQyxTQUFTLENBQUMsQ0FBQztZQUNoRCxDQUFDO1lBQ0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDaEQsSUFBSSxTQUFTLEVBQUUsQ0FBQztnQkFDZixJQUFJLENBQUMsMEJBQTBCLENBQUMsTUFBTSxDQUFDLFNBQVMsQ0FBQyxDQUFDO1lBQ25ELENBQUM7WUFDRCxPQUFPLFFBQVEsQ0FBQztRQUNqQixDQUFDO1FBRUQsTUFBTSxjQUFjLEdBQUcsSUFBSSxDQUFDLCtCQUErQixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ2xFLE1BQU0sS0FBSyxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsY0FBYyxDQUFDLE9BQU8sRUFBRSxDQUFDLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBRSxRQUFRLEVBQUUsSUFBSSxDQUFFLEVBQUUsRUFBRTtZQUM3RSxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsUUFBUSxDQUFDLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQztZQUMxQyxPQUFPLEdBQUcsUUFBUSxHQUFHLFFBQVEsS0FBSyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7UUFDL0MsQ0FBQyxDQUFDLENBQUM7UUFFSCxNQUFNLE1BQU0sR0FBRyxLQUFLLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztRQUN6QyxPQUFPLE1BQU0sQ0FBQztJQUNmLENBQUM7SUFFRDs7Ozs7O09BTUc7SUFDSywwQkFBMEIsQ0FBRSxJQUFjO1FBQ2pELElBQUksSUFBSSxDQUFDLFlBQVksSUFBSSxDQUFDLElBQUksQ0FBQyxxQkFBcUIsRUFBRSxDQUFDO1lBQ3RELE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsWUFBWTtZQUMvQixDQUFDLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLFlBQVksQ0FBQyxNQUFNLEdBQUcsQ0FBQyxDQUFDO1lBQ25ELENBQUMsQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDO1FBQ2pCLE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxDQUFDLENBQUMsR0FBRyxJQUFJLENBQUMscUJBQXFCLEdBQUcsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDO1FBQ2xGLE1BQU0sTUFBTSxHQUFHLEdBQUcsTUFBTSxHQUFHLE1BQU0sQ0FBQyxPQUFPLENBQUMsS0FBSyxFQUFFLEdBQUcsQ0FBQyxFQUFFLENBQUM7UUFDeEQsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNLLDBCQUEwQixDQUNqQyxRQUFnQixFQUNoQixRQUFvQyxFQUNwQyxPQUFpQjtRQUVqQixpREFBaUQ7UUFDakQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLGdDQUFnQyxDQUFDLFFBQVEsRUFBRSxJQUFJLENBQUMseUJBQXlCLENBQUMsQ0FBQztRQUM3RixJQUFJLElBQUksRUFBRSxDQUFDO1lBQ1YsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLCtCQUErQixDQUFDLElBQUksQ0FBQyxDQUFDO1lBQzVELElBQUksUUFBUSxLQUFLLFNBQVMsRUFBRSxDQUFDO2dCQUM1QixPQUFPLFFBQVEsQ0FBQztZQUNqQixDQUFDO1lBQ0QsTUFBTSxhQUFhLEdBQUcsU0FBUyxDQUFDO1lBQ2hDLE9BQU8sYUFBYSxDQUFDO1FBQ3RCLENBQUM7UUFFRCw2REFBNkQ7UUFDN0QsbUVBQW1FO1FBQ25FLGtFQUFrRTtRQUNsRSxpRUFBaUU7UUFDakUsK0RBQStEO1FBQy9ELGdFQUFnRTtRQUNoRSxnREFBZ0Q7UUFDaEQsa0VBQWtFO1FBQ2xFLG1FQUFtRTtRQUNuRSx3REFBd0Q7UUFDeEQsSUFBSSxRQUFRLEtBQUssY0FBYyxJQUFJLFFBQVEsSUFBSSxRQUFRLENBQUMsTUFBTSxLQUFLLENBQUMsRUFBRSxDQUFDO1lBQ3RFLE1BQU0sQ0FBRSxXQUFXLENBQUUsR0FBRyxRQUFRLENBQUM7WUFDakMsSUFBSSxXQUFXLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxXQUFXLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFdBQVcsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO2dCQUM3RixNQUFNLFdBQVcsR0FBRyxJQUFJLENBQUMsb0JBQW9CLENBQUMsV0FBVyxDQUFDLFFBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDekUsSUFBSSxXQUFXLENBQUMsTUFBTSxLQUFLLFFBQVEsRUFBRSxDQUFDO29CQUNyQyx1REFBdUQ7b0JBQ3ZELHNEQUFzRDtvQkFDdEQsTUFBTSxXQUFXLEdBQUcsSUFBSSxDQUFDLDBCQUEwQixDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsSUFBSSxTQUFTLENBQUM7b0JBQ25GLE9BQU8sV0FBVyxDQUFDO2dCQUNwQixDQUFDO2dCQUNELElBQUksV0FBVyxDQUFDLE1BQU0sS0FBSyxXQUFXLEVBQUUsQ0FBQztvQkFDeEMsSUFBSSxDQUFDLHlCQUF5QixDQUFDLFdBQVcsQ0FBQyxRQUFRLENBQUMsSUFBSSxFQUFFLFdBQVcsRUFBRSxXQUFXLENBQUMsQ0FBQztnQkFDckYsQ0FBQztnQkFDRCxNQUFNLGNBQWMsR0FBRyxTQUFTLENBQUM7Z0JBQ2pDLE9BQU8sY0FBYyxDQUFDO1lBQ3ZCLENBQUM7WUFDRCxNQUFNLFdBQVcsR0FBRyxJQUFJLENBQUMsU0FBUyxDQUFDLFdBQVcsQ0FBQyxDQUFDO1lBQ2hELElBQUksV0FBVyxLQUFLLFNBQVMsRUFBRSxDQUFDO2dCQUMvQixNQUFNLGVBQWUsR0FBRyxTQUFTLENBQUM7Z0JBQ2xDLE9BQU8sZUFBZSxDQUFDO1lBQ3hCLENBQUM7WUFDRCxNQUFNLGFBQWEsR0FBRyxnQkFBZ0IsV0FBVyxHQUFHLENBQUM7WUFDckQsT0FBTyxhQUFhLENBQUM7UUFDdEIsQ0FBQztRQUVELG9FQUFvRTtRQUNwRSxpRUFBaUU7UUFDakUsbUVBQW1FO1FBQ25FLDJEQUEyRDtRQUMzRCxNQUFNLFdBQVcsR0FBRyxJQUFJLENBQUMsb0JBQW9CLENBQUMsUUFBUSxDQUFDLENBQUM7UUFDeEQsSUFBSSxXQUFXLENBQUMsTUFBTSxLQUFLLFFBQVEsRUFBRSxDQUFDO1lBQ3JDLCtEQUErRDtZQUMvRCxJQUFJLFFBQVEsS0FBSyxjQUFjLElBQUksUUFBUSxJQUFJLFFBQVEsQ0FBQyxNQUFNLEtBQUssQ0FBQyxFQUFFLENBQUM7Z0JBQ3RFLE1BQU0sQ0FBRSxHQUFHLENBQUUsR0FBRyxRQUFRLENBQUM7Z0JBQ3pCLElBQUksR0FBRyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFNBQVMsRUFBRSxDQUFDO29CQUMxQyxNQUFNLFNBQVMsR0FBRyxHQUF1QixDQUFDO29CQUMxQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsU0FBUyxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7d0JBQ3pDLE1BQU0sV0FBVyxHQUFHLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxTQUFTLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQyxDQUFDO3dCQUN2RSxJQUFJLFdBQVcsQ0FBQyxNQUFNLEtBQUssUUFBUSxFQUFFLENBQUM7NEJBQ3JDLHdEQUF3RDs0QkFDeEQsbURBQW1EOzRCQUNuRCwwQ0FBMEM7NEJBQzFDLE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQywwQkFBMEIsQ0FBQyxXQUFXLENBQUMsSUFBSSxDQUFDLElBQUksU0FBUyxDQUFDOzRCQUNsRixPQUFPLFVBQVUsQ0FBQzt3QkFDbkIsQ0FBQzt3QkFDRCxJQUFJLFdBQVcsQ0FBQyxNQUFNLEtBQUssV0FBVyxFQUFFLENBQUM7NEJBQ3hDLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxTQUFTLENBQUMsUUFBUSxDQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsV0FBVyxDQUFDLENBQUM7d0JBQ2pGLENBQUM7d0JBQ0QsZ0RBQWdEO3dCQUNoRCxPQUFPLFNBQVMsQ0FBQztvQkFDbEIsQ0FBQztnQkFDRixDQUFDO1lBQ0YsQ0FBQztZQUNELElBQUksQ0FBQyxRQUFRLElBQUksUUFBUSxDQUFDLE1BQU0sS0FBSyxDQUFDLEVBQUUsQ0FBQztnQkFDeEMsd0RBQXdEO2dCQUN4RCxtREFBbUQ7Z0JBQ25ELDBDQUEwQztnQkFDMUMsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLDBCQUEwQixDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsSUFBSSxTQUFTLENBQUM7Z0JBQ2xGLE9BQU8sVUFBVSxDQUFDO1lBQ25CLENBQUM7WUFDRCx5REFBeUQ7WUFDekQsNERBQTREO1lBQzVELE9BQU8sR0FBRyxRQUFRLElBQUksUUFBUSxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQztRQUMxRSxDQUFDO1FBQ0QsSUFBSSxXQUFXLENBQUMsTUFBTSxLQUFLLFdBQVcsRUFBRSxDQUFDO1lBQ3hDLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxRQUFRLEVBQUUsT0FBTyxJQUFJLElBQUksQ0FBQyx5QkFBeUIsRUFBRSxXQUFXLENBQUMsQ0FBQztRQUNsRyxDQUFDO1FBRUQsSUFBSSxRQUFRLElBQUksUUFBUSxDQUFDLE1BQU0sR0FBRyxDQUFDLEVBQUUsQ0FBQztZQUNyQyxJQUFJLGtCQUFrQixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO2dCQUN0QyxNQUFNLGFBQWEsR0FBRyxHQUFHLFFBQVEsSUFBSSxRQUFRLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDO2dCQUN4RixPQUFPLGFBQWEsQ0FBQztZQUN0QixDQUFDO1lBQ0QsMkRBQTJEO1lBQzNELCtEQUErRDtZQUMvRCwyREFBMkQ7WUFDM0QsK0RBQStEO1lBQy9ELDZEQUE2RDtZQUM3RCw4REFBOEQ7WUFDOUQsMERBQTBEO1lBQzFELElBQUksQ0FBQyxJQUFJLENBQUMseUJBQXlCLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztnQkFDL0MsTUFBTSxjQUFjLEdBQUcsR0FBRyxRQUFRLElBQUksUUFBUSxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQztnQkFDekYsT0FBTyxjQUFjLENBQUM7WUFDdkIsQ0FBQztZQUNELDZEQUE2RDtZQUM3RCxzREFBc0Q7WUFDdEQsSUFBSSxPQUFPLEVBQUUsQ0FBQztnQkFDYixJQUFJLENBQUMsNEJBQTRCLENBQUMsUUFBUSxFQUFFLE9BQU8sQ0FBQyxDQUFDO1lBQ3RELENBQUM7WUFDRCxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQsTUFBTSxjQUFjLEdBQUcsSUFBSSxDQUFDLCtCQUErQixDQUFDLFFBQVEsRUFBRSxPQUFPLENBQUMsQ0FBQztRQUMvRSxPQUFPLGNBQWMsQ0FBQztJQUN2QixDQUFDO0lBRUQ7Ozs7Ozs7Ozs7O09BV0c7SUFDSywyQkFBMkIsQ0FBRSxPQUE2QjtRQUNqRSxJQUFJLENBQUMsRUFBRSxDQUFDLGVBQWUsQ0FBQyxPQUFPLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUMzQyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQsc0ZBQXNGO1FBQ3RGLE1BQU0sUUFBUSxHQUFhLEVBQUUsQ0FBQztRQUM5QixJQUFJLEtBQUssR0FBa0IsT0FBTyxDQUFDLFFBQVEsQ0FBQztRQUM1QyxPQUFPLEVBQUUsQ0FBQyxlQUFlLENBQUMsS0FBSyxDQUFDLEVBQUUsQ0FBQztZQUNsQyxRQUFRLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDbkMsS0FBSyxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUM7UUFDcEIsQ0FBQztRQUNELFFBQVEsQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBRTdCLE1BQU0sZUFBZSxHQUFHLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEVBQUUsR0FBRyxDQUFDLFFBQVEsQ0FBRSxDQUFDLENBQUUsQ0FBQyxDQUFDO1FBQzNHLElBQUksQ0FBQyxlQUFlLElBQUksQ0FBQyxlQUFlLENBQUMsV0FBVyxFQUFFLENBQUM7WUFDdEQsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxlQUFlLENBQUMsU0FBUyxFQUFFLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxDQUFDO1FBQy9HLElBQUksQ0FBQyxVQUFVLElBQUksVUFBVSxDQUFDLFVBQVUsRUFBRSxDQUFDO1lBQzFDLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFFRCxxRUFBcUU7UUFDckUsc0VBQXNFO1FBQ3RFLHdEQUF3RDtRQUN4RCxJQUFJLFNBQVMsR0FBK0Q7WUFDM0UsVUFBVSxFQUFHLFVBQVUsQ0FBQyxZQUFZO1NBQ3BDLENBQUM7UUFDRixLQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsUUFBUSxDQUFDLE1BQU0sR0FBRyxDQUFDLElBQUksU0FBUyxFQUFFLENBQUMsRUFBRSxFQUFFLENBQUM7WUFDM0QsTUFBTSxPQUFPLEdBQUcsUUFBUSxDQUFFLENBQUMsQ0FBRSxDQUFDO1lBQzlCLElBQUksU0FBUyxDQUFDLEtBQUssRUFBRSxDQUFDO2dCQUNyQixNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsb0JBQW9CLENBQUMsU0FBUyxDQUFDLEtBQUssRUFBRSxPQUFPLENBQUMsQ0FBQztnQkFDbkUsSUFBSSxNQUFNLEVBQUUsSUFBSSxJQUFJLEVBQUUsQ0FBQyxhQUFhLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7b0JBQ25ELFNBQVMsR0FBRyxFQUFFLFVBQVUsRUFBRyxTQUFTLENBQUMsVUFBVSxFQUFFLEtBQUssRUFBRyxNQUFNLENBQUMsSUFBSSxFQUFFLENBQUM7b0JBQ3ZFLFNBQVM7Z0JBQ1YsQ0FBQztnQkFDRCxTQUFTLEdBQUcsU0FBUyxDQUFDO2dCQUN0QixNQUFNO1lBQ1AsQ0FBQztZQUNELE1BQU0sYUFBYSxHQUNsQixJQUFJLENBQUMsd0JBQXdCLENBQUMsR0FBRyxDQUFDLFNBQVMsQ0FBQyxVQUFVLENBQUMsRUFBRSxHQUFHLENBQUMsT0FBTyxDQUFDLENBQUM7WUFDdkUsSUFBSSxhQUFhLEVBQUUsSUFBSSxJQUFJLEVBQUUsQ0FBQyxhQUFhLENBQUMsYUFBYSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQ2pFLFNBQVMsR0FBRyxFQUFFLFVBQVUsRUFBRyxTQUFTLENBQUMsVUFBVSxFQUFFLEtBQUssRUFBRyxhQUFhLENBQUMsSUFBSSxFQUFFLENBQUM7Z0JBQzlFLFNBQVM7WUFDVixDQUFDO1lBQ0QsTUFBTSxhQUFhLEdBQUcsSUFBSSxDQUFDLDRCQUE0QixDQUFDLEdBQUcsQ0FBQyxTQUFTLENBQUMsVUFBVSxDQUFDLEVBQUUsR0FBRyxDQUFDLE9BQU8sQ0FBQyxDQUFDO1lBQ2hHLElBQUksYUFBYSxFQUFFLENBQUM7Z0JBQ25CLE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxhQUFhLEVBQUUsU0FBUyxDQUFDLFVBQVUsQ0FBQyxDQUFDO2dCQUM3RixJQUFJLGNBQWMsSUFBSSxDQUFDLGNBQWMsQ0FBQyxVQUFVLEVBQUUsQ0FBQztvQkFDbEQsU0FBUyxHQUFHLEVBQUUsVUFBVSxFQUFHLGNBQWMsQ0FBQyxZQUFZLEVBQUUsQ0FBQztvQkFDekQsU0FBUztnQkFDVixDQUFDO1lBQ0YsQ0FBQztZQUNELE1BQU0saUJBQWlCLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLEdBQUcsQ0FBQyxTQUFTLENBQUMsVUFBVSxDQUFDLEVBQUUsR0FBRyxDQUFDLE9BQU8sQ0FBQyxDQUFDO1lBQy9GLElBQUksaUJBQWlCLEVBQUUsQ0FBQztnQkFDdkIsTUFBTSxjQUFjLEdBQUcsSUFBSSxDQUFDLDJCQUEyQixDQUFDLGlCQUFpQixFQUFFLFNBQVMsQ0FBQyxVQUFVLENBQUMsQ0FBQztnQkFDakcsTUFBTSxVQUFVLEdBQ2YsY0FBYyxJQUFJLENBQUMsY0FBYyxDQUFDLFVBQVU7b0JBQzNDLENBQUMsQ0FBQyxJQUFJLENBQUMsd0JBQXdCLENBQUMsR0FBRyxDQUFDLGNBQWMsQ0FBQyxZQUFZLENBQUMsRUFBRSxHQUFHLENBQUMsT0FBTyxDQUFDO29CQUM5RSxDQUFDLENBQUMsU0FBUyxDQUFDO2dCQUNkLElBQUksVUFBVSxFQUFFLElBQUksSUFBSSxFQUFFLENBQUMsYUFBYSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO29CQUMzRCxTQUFTLEdBQUcsRUFBRSxVQUFVLEVBQUcsY0FBZSxDQUFDLFlBQVksRUFBRSxLQUFLLEVBQUcsVUFBVSxDQUFDLElBQUksRUFBRSxDQUFDO29CQUNuRixTQUFTO2dCQUNWLENBQUM7WUFDRixDQUFDO1lBQ0QsU0FBUyxHQUFHLFNBQVMsQ0FBQztRQUN2QixDQUFDO1FBRUQsTUFBTSxTQUFTLEdBQUcsUUFBUSxDQUFFLFFBQVEsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxDQUFFLENBQUM7UUFDbEQsSUFBSSxJQUEyQyxDQUFDO1FBQ2hELElBQUksU0FBUyxFQUFFLEtBQUssRUFBRSxDQUFDO1lBQ3RCLElBQUksR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUMsU0FBUyxDQUFDLEtBQUssRUFBRSxTQUFTLENBQUMsVUFBVSxFQUFFLFNBQVMsQ0FBQyxDQUFDO1FBQ3pGLENBQUM7YUFBTSxJQUFJLFNBQVMsRUFBRSxDQUFDO1lBQ3RCLElBQUksR0FBRyxJQUFJLENBQUMsMEJBQTBCLENBQUMsU0FBUyxDQUFDLFVBQVUsRUFBRSxTQUFTLEVBQUUsQ0FBQyxDQUFDLENBQUM7UUFDNUUsQ0FBQztRQUNELDhEQUE4RDtRQUM5RCxrRUFBa0U7UUFDbEUsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ1gsSUFBSSxHQUFHLElBQUksQ0FBQywwQkFBMEIsQ0FBQyxVQUFVLENBQUMsWUFBWSxFQUFFLFNBQVMsRUFBRSxDQUFDLENBQUMsQ0FBQztRQUMvRSxDQUFDO1FBQ0QsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ1gsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQywrQkFBK0IsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUM1RCxPQUFPLFFBQVEsQ0FBQztJQUNqQixDQUFDO0lBRUQ7O09BRUc7SUFDSyxvQkFBb0IsQ0FBRSxLQUFxQixFQUFFLElBQVk7UUFDaEUsS0FBSyxNQUFNLFNBQVMsSUFBSSxLQUFLLENBQUMsVUFBVSxFQUFFLENBQUM7WUFDMUMsSUFBSSxFQUFFLENBQUMsbUJBQW1CLENBQUMsU0FBUyxDQUFDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDO2dCQUN2RSxTQUFTLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxJQUFJLEVBQUUsQ0FBQztnQkFDL0IsTUFBTSxNQUFNLEdBQUcsU0FBUyxDQUFDO2dCQUN6QixPQUFPLE1BQU0sQ0FBQztZQUNmLENBQUM7UUFDRixDQUFDO1FBQ0QsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7T0FHRztJQUNLLHlCQUF5QixDQUNoQyxLQUFxQixFQUNyQixRQUFnQixFQUNoQixJQUFZO1FBRVosS0FBSyxNQUFNLFNBQVMsSUFBSSxLQUFLLENBQUMsVUFBVSxFQUFFLENBQUM7WUFDMUMsSUFBSSxFQUFFLENBQUMsc0JBQXNCLENBQUMsU0FBUyxDQUFDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDO2dCQUMxRSxTQUFTLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxJQUFJLEVBQUUsQ0FBQztnQkFDL0IsTUFBTSxNQUFNLEdBQThCLEVBQUUsSUFBSSxFQUFHLE9BQU8sRUFBRSxJQUFJLEVBQUcsU0FBUyxFQUFFLElBQUksRUFBRyxRQUFRLEVBQUUsQ0FBQztnQkFDaEcsT0FBTyxNQUFNLENBQUM7WUFDZixDQUFDO1lBQ0QsSUFBSSxFQUFFLENBQUMsa0JBQWtCLENBQUMsU0FBUyxDQUFDLElBQUksU0FBUyxDQUFDLElBQUksSUFBSSxTQUFTLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxJQUFJLEVBQUUsQ0FBQztnQkFDeEYsTUFBTSxNQUFNLEdBQThCLEVBQUUsSUFBSSxFQUFHLE9BQU8sRUFBRSxJQUFJLEVBQUcsU0FBUyxFQUFFLElBQUksRUFBRyxRQUFRLEVBQUUsQ0FBQztnQkFDaEcsT0FBTyxNQUFNLENBQUM7WUFDZixDQUFDO1lBQ0QsSUFBSSxFQUFFLENBQUMsc0JBQXNCLENBQUMsU0FBUyxDQUFDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDO2dCQUMxRSxTQUFTLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxJQUFJLEVBQUUsQ0FBQztnQkFDL0IsTUFBTSxNQUFNLEdBQThCLEVBQUUsSUFBSSxFQUFHLFdBQVcsRUFBRSxJQUFJLEVBQUcsU0FBUyxFQUFFLElBQUksRUFBRyxRQUFRLEVBQUUsQ0FBQztnQkFDcEcsT0FBTyxNQUFNLENBQUM7WUFDZixDQUFDO1FBQ0YsQ0FBQztRQUNELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7Ozs7O09BTUc7SUFDSywrQkFBK0IsQ0FBRSxRQUFnQixFQUFFLE9BQWlCO1FBQzNFLElBQUksa0JBQWtCLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDdEMsT0FBTyxRQUFRLENBQUM7UUFDakIsQ0FBQztRQUNELElBQUksT0FBTyxFQUFFLENBQUM7WUFDYixJQUFJLENBQUMsNEJBQTRCLENBQUMsUUFBUSxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQ3RELENBQUM7UUFDRCxNQUFNLE1BQU0sR0FBRyxTQUFTLENBQUM7UUFDekIsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7Ozs7O09BS0c7SUFDSyxnQkFBZ0IsQ0FBRSxZQUFvQixFQUFFLFFBQWdCO1FBQy9ELElBQUksS0FBSyxHQUFHLElBQUksQ0FBQyxXQUFXLENBQUMsR0FBRyxDQUFDLFlBQVksQ0FBQyxDQUFDO1FBQy9DLElBQUksQ0FBQyxLQUFLLEVBQUUsQ0FBQztZQUNaLEtBQUssR0FBRyxFQUFFLENBQUM7WUFDWCxJQUFJLENBQUMsV0FBVyxDQUFDLEdBQUcsQ0FBQyxZQUFZLEVBQUUsS0FBSyxDQUFDLENBQUM7UUFDM0MsQ0FBQztRQUNELElBQUksQ0FBQyxLQUFLLENBQUMsUUFBUSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDL0IsS0FBSyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQztRQUN0QixDQUFDO0lBQ0YsQ0FBQztJQUVEOzs7O09BSUc7SUFDSCxtQkFBbUI7UUFDbEIsSUFBSSxDQUFDLHdCQUF3QixFQUFFLENBQUM7UUFDaEMsSUFBSSxDQUFDLDJCQUEyQixFQUFFLENBQUM7UUFDbkMsTUFBTSxNQUFNLEdBQXNCLEVBQUUsQ0FBQztRQUNyQyxLQUFLLE1BQU0sQ0FBRSxZQUFZLEVBQUUsS0FBSyxDQUFFLElBQUksSUFBSSxDQUFDLFdBQVcsRUFBRSxDQUFDO1lBQ3hELElBQUksS0FBSyxDQUFDLE1BQU0sR0FBRyxDQUFDLEVBQUUsQ0FBQztnQkFDdEIsU0FBUztZQUNWLENBQUM7WUFDRCxNQUFNLFdBQVcsR0FBRyxZQUFZLENBQUMsT0FBTyxDQUFDLFVBQVUsRUFBRSxFQUFFLENBQUMsQ0FBQztZQUN6RCxNQUFNLE9BQU8sR0FBRyw0QkFBNEIsV0FBVyx1QkFBdUI7Z0JBQzdFLG9EQUFvRCxDQUFDO1lBQ3RELE1BQU0sQ0FBQyxJQUFJLENBQUMsRUFBRSxPQUFPLEVBQUUsU0FBUyxFQUFHLENBQUUsR0FBRyxLQUFLLENBQUUsRUFBRSxDQUFDLENBQUM7UUFDcEQsQ0FBQztRQUNELEtBQUssTUFBTSxLQUFLLElBQUksSUFBSSxDQUFDLG9CQUFvQixFQUFFLENBQUM7WUFDL0MsTUFBTSxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQztRQUNwQixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsTUFBTSxDQUFDO1FBQ3RCLE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7Ozs7Ozs7Ozs7OztPQWNHO0lBQ0ssb0JBQW9CLENBQUUsSUFBWTtRQUN6QyxnREFBZ0Q7UUFDaEQsTUFBTSxZQUFZLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMseUJBQXlCLENBQUMsRUFBRSxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDM0YsSUFBSSxZQUFZLEVBQUUsQ0FBQztZQUNsQixNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDLFFBQVEsQ0FBQyxZQUFZLENBQUMsQ0FBQztZQUMvQyxJQUFJLElBQUksRUFBRSxDQUFDO2dCQUNWLE1BQU0sV0FBVyxHQUE2QixFQUFFLE1BQU0sRUFBRyxRQUFRLEVBQUUsSUFBSSxFQUFFLENBQUM7Z0JBQzFFLE9BQU8sV0FBVyxDQUFDO1lBQ3BCLENBQUM7UUFDRixDQUFDO1FBRUQsMkRBQTJEO1FBQzNELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEVBQUUsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzNGLElBQUksUUFBUSxJQUFJLENBQUMsUUFBUSxDQUFDLFdBQVcsRUFBRSxDQUFDO1lBQ3ZDLE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxRQUFRLENBQUMsU0FBUyxFQUFFLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxDQUFDO1lBQ3hHLElBQUksVUFBVSxJQUFJLENBQUMsVUFBVSxDQUFDLFVBQVUsRUFBRSxDQUFDO2dCQUMxQyxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsd0JBQXdCLENBQUMsVUFBVSxDQUFDLFlBQVksRUFBRSxRQUFRLENBQUMsWUFBWSxFQUFFLENBQUMsQ0FBQyxDQUFDO2dCQUNsRyxJQUFJLFFBQVEsRUFBRSxDQUFDO29CQUNkLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxLQUFLLENBQUMsUUFBUSxDQUFDLFFBQVEsQ0FBQyxDQUFDO29CQUMzQyxJQUFJLElBQUksRUFBRSxDQUFDO3dCQUNWLE1BQU0sWUFBWSxHQUE2QixFQUFFLE1BQU0sRUFBRyxRQUFRLEVBQUUsSUFBSSxFQUFFLENBQUM7d0JBQzNFLE9BQU8sWUFBWSxDQUFDO29CQUNyQixDQUFDO2dCQUNGLENBQUM7WUFDRixDQUFDO1FBQ0YsQ0FBQztRQUVELHlDQUF5QztRQUN6QyxNQUFNLE1BQU0sR0FBRyxJQUFBLGlDQUF5QixFQUFDLElBQUksQ0FBQyxLQUFLLEVBQUUsSUFBSSxFQUFFLElBQUksQ0FBQyxrQkFBa0IsQ0FBQyxDQUFDO1FBQ3BGLE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7T0FHRztJQUNLLHdCQUF3QixDQUFFLFVBQWtCLEVBQUUsSUFBWSxFQUFFLEtBQWE7UUFDaEYsSUFBSSxLQUFLLEdBQUcsd0JBQXdCLEVBQUUsQ0FBQztZQUN0QyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsRUFBRSxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDakUsSUFBSSxNQUFNLEVBQUUsQ0FBQztZQUNaLE9BQU8sTUFBTSxDQUFDO1FBQ2YsQ0FBQztRQUVELE1BQU0sU0FBUyxHQUFHLElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxHQUFHLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDL0QsTUFBTSxpQkFBaUIsR0FBRyxTQUFTLEVBQUUsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQy9DLElBQUksaUJBQWlCLEVBQUUsQ0FBQztZQUN2QixNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsMkJBQTJCLENBQUMsaUJBQWlCLEVBQUUsVUFBVSxDQUFDLENBQUM7WUFDdkYsSUFBSSxjQUFjLElBQUksQ0FBQyxjQUFjLENBQUMsVUFBVSxFQUFFLENBQUM7Z0JBQ2xELE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxjQUFjLENBQUMsWUFBWSxFQUFFLElBQUksRUFBRSxLQUFLLEdBQUcsQ0FBQyxDQUFDLENBQUM7Z0JBQzFGLElBQUksS0FBSyxFQUFFLENBQUM7b0JBQ1gsT0FBTyxLQUFLLENBQUM7Z0JBQ2QsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsQ0FBQztRQUM3RCxJQUFJLEtBQUssRUFBRSxDQUFDO1lBQ1gsS0FBSyxNQUFNLGFBQWEsSUFBSSxLQUFLLEVBQUUsQ0FBQztnQkFDbkMsTUFBTSxjQUFjLEdBQUcsSUFBSSxDQUFDLDJCQUEyQixDQUFDLGFBQWEsRUFBRSxVQUFVLENBQUMsQ0FBQztnQkFDbkYsSUFBSSxDQUFDLGNBQWMsSUFBSSxjQUFjLENBQUMsVUFBVSxFQUFFLENBQUM7b0JBQ2xELFNBQVM7Z0JBQ1YsQ0FBQztnQkFDRCxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMsd0JBQXdCLENBQUMsY0FBYyxDQUFDLFlBQVksRUFBRSxJQUFJLEVBQUUsS0FBSyxHQUFHLENBQUMsQ0FBQyxDQUFDO2dCQUMxRixJQUFJLEtBQUssRUFBRSxDQUFDO29CQUNYLE9BQU8sS0FBSyxDQUFDO2dCQUNkLENBQUM7WUFDRixDQUFDO1FBQ0YsQ0FBQztRQUVELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7Ozs7Ozs7Ozs7T0FXRztJQUNLLHdCQUF3QjtRQUMvQixJQUFJLElBQUksQ0FBQyx5QkFBeUIsRUFBRSxDQUFDO1lBQ3BDLE9BQU87UUFDUixDQUFDO1FBQ0QsSUFBSSxDQUFDLHlCQUF5QixHQUFHLElBQUksQ0FBQztRQUN0QyxxRUFBcUU7UUFDckUsTUFBTSxXQUFXLEdBQUcsSUFBSSxHQUFHLEVBQW9CLENBQUM7UUFDaEQsS0FBSyxNQUFNLEdBQUcsSUFBSSxJQUFJLENBQUMsZ0JBQWdCLEVBQUUsQ0FBQztZQUN6QyxNQUFNLEtBQUssR0FBRyxXQUFXLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDOUMsS0FBSyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLENBQUM7WUFDekIsV0FBVyxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLEtBQUssQ0FBQyxDQUFDO1FBQ2xDLENBQUM7UUFDRCxLQUFLLE1BQU0sQ0FBRSxRQUFRLEVBQUUsS0FBSyxDQUFFLElBQUksV0FBVyxFQUFFLENBQUM7WUFDL0MsSUFBSSxJQUFJLENBQUMsS0FBSyxDQUFDLFFBQVEsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO2dCQUNuQyxTQUFTO1lBQ1YsQ0FBQztZQUNELDZEQUE2RDtZQUM3RCx3REFBd0Q7WUFDeEQsTUFBTSxVQUFVLEdBQUcsUUFBUSxDQUFDLE9BQU8sQ0FBQyxVQUFVLEVBQUUsRUFBRSxDQUFDLENBQUM7WUFDcEQsTUFBTSxXQUFXLEdBQUcsVUFBVSxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsQ0FBQyxHQUFHLEVBQUUsSUFBSSxVQUFVLENBQUM7WUFDOUQsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxXQUFXLEVBQUUsQ0FBQyxNQUFNLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsSUFBSSxLQUFLLFdBQVcsQ0FBQyxDQUFDO1lBQ2hGLElBQUksVUFBVSxDQUFDLE1BQU0sS0FBSyxDQUFDLEVBQUUsQ0FBQztnQkFDN0IsTUFBTSxTQUFTLEdBQW9CO29CQUNsQyxPQUFPLEVBQUcsd0NBQXdDLFFBQVEsNEJBQTRCO3dCQUNyRixvQ0FBb0M7b0JBQ3JDLFNBQVMsRUFBRyxLQUFLO2lCQUNqQixDQUFDO2dCQUNGLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUM7Z0JBQzFDLFNBQVM7WUFDVixDQUFDO1lBQ0QsTUFBTSxrQkFBa0IsR0FBRyxVQUFVLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLENBQUMsVUFBVSxJQUFJLENBQUMsQ0FBQyxJQUFJLElBQUksQ0FBQyxDQUFDLE1BQU0sRUFBRSxDQUFDLENBQUM7WUFDeEYsTUFBTSxjQUFjLEdBQUcsVUFBVSxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxRQUFRLENBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDbEUsTUFBTSxjQUFjLEdBQW9CO2dCQUN2QyxPQUFPLEVBQUcsd0NBQXdDLFFBQVEsOEJBQThCO29CQUN2RixlQUFlLFVBQVUsQ0FBQyxNQUFNLGdDQUFnQztvQkFDaEUsYUFBYSxjQUFjLDZCQUE2QjtnQkFDekQsU0FBUyxFQUFHLENBQUUsR0FBRyxLQUFLLEVBQUUsR0FBRyxrQkFBa0IsQ0FBRTthQUMvQyxDQUFDO1lBQ0YsSUFBSSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQyxjQUFjLENBQUMsQ0FBQztRQUNoRCxDQUFDO0lBQ0YsQ0FBQztJQUVEOzs7OztPQUtHO0lBQ0ssNEJBQTRCLENBQUUsSUFBWSxFQUFFLE9BQWdCO1FBQ25FLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxZQUFZLENBQUMsT0FBTyxDQUFDLENBQUM7UUFDNUMsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDO1FBQzVDLE1BQU0sT0FBTyxHQUFHLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsQ0FBQyxHQUFHLEVBQUUsRUFBRSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEtBQUssSUFBSSxJQUFJLEdBQUcsQ0FBQyxRQUFRLEtBQUssUUFBUSxDQUFDLENBQUM7UUFDdkcsSUFBSSxPQUFPLEVBQUUsQ0FBQztZQUNiLE9BQU87UUFDUixDQUFDO1FBQ0QsSUFBSSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQyxFQUFFLElBQUksRUFBRSxRQUFRLEVBQUUsSUFBSSxFQUFFLENBQUMsQ0FBQztJQUN6RCxDQUFDO0lBRUQ7Ozs7OztPQU1HO0lBQ0sseUJBQXlCLENBQUUsSUFBWTtRQUM5QyxNQUFNLEtBQUssR0FBYSxFQUFFLENBQUM7UUFDM0IsS0FBSyxNQUFNLENBQUUsSUFBSSxFQUFFLEtBQUssQ0FBRSxJQUFJLElBQUksQ0FBQyxtQkFBbUIsRUFBRSxDQUFDO1lBQ3hELElBQUksQ0FBQyxJQUFJLENBQUMsa0JBQWtCLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUN2RCxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ2xCLENBQUM7UUFDRixDQUFDO1FBQ0QsT0FBTyxLQUFLLENBQUM7SUFDZCxDQUFDO0lBRUQ7Ozs7Ozs7Ozs7O09BV0c7SUFDSywyQkFBMkI7UUFDbEMsSUFBSSxJQUFJLENBQUMsNEJBQTRCLEVBQUUsQ0FBQztZQUN2QyxPQUFPO1FBQ1IsQ0FBQztRQUNELElBQUksQ0FBQyw0QkFBNEIsR0FBRyxJQUFJLENBQUM7UUFDekMsTUFBTSxXQUFXLEdBQUcsSUFBSSxHQUFHLEVBQThELENBQUM7UUFDMUYsS0FBSyxNQUFNLEdBQUcsSUFBSSxJQUFJLENBQUMsbUJBQW1CLEVBQUUsQ0FBQztZQUM1QyxNQUFNLEtBQUssR0FBRyxXQUFXLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDOUMsS0FBSyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQztZQUNoQixXQUFXLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsS0FBSyxDQUFDLENBQUM7UUFDbEMsQ0FBQztRQUNELEtBQUssTUFBTSxDQUFFLElBQUksRUFBRSxLQUFLLENBQUUsSUFBSSxXQUFXLEVBQUUsQ0FBQztZQUMzQywrREFBK0Q7WUFDL0QsOERBQThEO1lBQzlELHdEQUF3RDtZQUN4RCxNQUFNLFVBQVUsR0FBRyxLQUFLLENBQUMsTUFBTSxDQUFDLENBQUMsSUFBSSxFQUFFLEVBQUUsQ0FBQyxDQUFDLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDO1lBQ2pHLElBQUksVUFBVSxDQUFDLE1BQU0sS0FBSyxDQUFDLEVBQUUsQ0FBQztnQkFDN0IsU0FBUztZQUNWLENBQUM7WUFDRCxNQUFNLFNBQVMsR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDdkQsSUFBSSxTQUFTLENBQUMsTUFBTSxHQUFHLENBQUMsRUFBRSxDQUFDO2dCQUMxQixTQUFTO1lBQ1YsQ0FBQztZQUNELE1BQU0sT0FBTyxHQUFHLGdDQUFnQyxJQUFJLE1BQU0sU0FBUyxDQUFDLE1BQU0sZ0JBQWdCO2dCQUN6RixzRUFBc0UsQ0FBQztZQUN4RSxNQUFNLGFBQWEsR0FBRyxTQUFTLENBQUMsR0FBRyxDQUFDLENBQUMsSUFBSSxFQUFFLEVBQUUsQ0FBQyxJQUFJLENBQUMsaUJBQWlCLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxDQUFDLENBQUM7WUFDbEYsTUFBTSxLQUFLLEdBQW9CO2dCQUM5QixPQUFPO2dCQUNQLFNBQVMsRUFBRyxDQUFFLEdBQUcsVUFBVSxDQUFDLEdBQUcsQ0FBQyxDQUFDLElBQUksRUFBRSxFQUFFLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxFQUFFLEdBQUcsYUFBYSxDQUFFO2FBQzVFLENBQUM7WUFDRixJQUFJLENBQUMsb0JBQW9CLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxDQUFDO1FBQ3ZDLENBQUM7SUFDRixDQUFDO0lBRUQ7Ozs7T0FJRztJQUNLLGlCQUFpQixDQUFFLElBQVksRUFBRSxJQUFZO1FBQ3BELE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLEVBQUUsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzNELE1BQU0sSUFBSSxHQUFHLElBQUksRUFBRSxJQUFJLENBQUM7UUFDeEIsSUFBSSxRQUFRLEdBQUcsR0FBRyxJQUFJLE1BQU0sQ0FBQztRQUM3QixJQUFJLElBQUksSUFBSSxJQUFJLENBQUMsR0FBRyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQzNCLE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQyxhQUFhLEVBQUUsQ0FBQztZQUN4QyxNQUFNLElBQUksR0FBRyxVQUFVLENBQUMsNkJBQTZCLENBQUMsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDLENBQUMsSUFBSSxHQUFHLENBQUMsQ0FBQztZQUNoRixNQUFNLE1BQU0sR0FBRyxVQUFVLENBQUMsNkJBQTZCLENBQUMsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDLENBQUMsU0FBUyxHQUFHLENBQUMsQ0FBQztZQUN2RixRQUFRLEdBQUcsR0FBRyxJQUFJLElBQUksSUFBSSxJQUFJLE1BQU0sRUFBRSxDQUFDO1FBQ3hDLENBQUM7UUFDRCxNQUFNLE1BQU0sR0FBRyxRQUFRLENBQUM7UUFDeEIsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7OztPQUdHO0lBQ0sseUJBQXlCLENBQ2hDLElBQVksRUFDWixPQUF5QixFQUN6QixNQUEyRTtRQUUzRSxNQUFNLFFBQVEsR0FBRyxPQUFPLE9BQU8sS0FBSyxRQUFRLENBQUMsQ0FBQyxDQUFDLE9BQU8sQ0FBQyxDQUFDLENBQUMsSUFBSSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsQ0FBQztRQUNwRixJQUFJLE1BQU0sQ0FBQyxNQUFNLEtBQUssV0FBVyxFQUFFLENBQUM7WUFDbkMsTUFBTSxrQkFBa0IsR0FBRyxNQUFNLENBQUMsVUFBVSxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxDQUFDLFVBQVUsSUFBSSxDQUFDLENBQUMsSUFBSSxJQUFJLENBQUMsQ0FBQyxNQUFNLEVBQUUsQ0FBQyxDQUFDO1lBQy9GLE1BQU0sZ0JBQWdCLEdBQUcsMENBQTBDLElBQUksS0FBSztnQkFDM0UsR0FBRyxNQUFNLENBQUMsVUFBVSxDQUFDLE1BQU0scURBQXFEO2dCQUNoRiw4QkFBOEIsQ0FBQztZQUNoQyxNQUFNLGNBQWMsR0FBb0I7Z0JBQ3ZDLE9BQU8sRUFBSyxnQkFBZ0I7Z0JBQzVCLFNBQVMsRUFBRyxDQUFFLFFBQVEsRUFBRSxHQUFHLGtCQUFrQixDQUFFO2FBQy9DLENBQUM7WUFDRixJQUFJLENBQUMsb0JBQW9CLENBQUMsSUFBSSxDQUFDLGNBQWMsQ0FBQyxDQUFDO1lBQy9DLE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxpQkFBaUIsR0FBRywyQ0FBMkMsSUFBSSxxQkFBcUI7WUFDN0YscURBQXFELENBQUM7UUFDdkQsTUFBTSxlQUFlLEdBQW9CLEVBQUUsT0FBTyxFQUFHLGlCQUFpQixFQUFFLFNBQVMsRUFBRyxDQUFFLFFBQVEsQ0FBRSxFQUFFLENBQUM7UUFDbkcsSUFBSSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQyxlQUFlLENBQUMsQ0FBQztJQUNqRCxDQUFDO0lBRUQ7OztPQUdHO0lBQ0ssWUFBWSxDQUFFLElBQWE7UUFDbEMsSUFBSSxPQUFPLEdBQXdCLElBQUksQ0FBQztRQUN4QyxPQUFPLE9BQU8sSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsT0FBTyxDQUFDLEVBQUUsQ0FBQztZQUM3QyxPQUFPLEdBQUcsT0FBTyxDQUFDLE1BQU0sQ0FBQztRQUMxQixDQUFDO1FBQ0QsSUFBSSxDQUFDLE9BQU8sRUFBRSxDQUFDO1lBQ2QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDO1lBQ2hELE9BQU8sUUFBUSxDQUFDO1FBQ2pCLENBQUM7UUFDRCxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMsUUFBUSxDQUFDLE9BQU8sQ0FBQyxDQUFDO1FBQ3JDLE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUFDLE9BQU8sRUFBRSxLQUFLLENBQUMsQ0FBQztRQUM3RSxNQUFNLFFBQVEsR0FBRyxHQUFHLE9BQU8sQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7UUFDcEUsT0FBTyxRQUFRLENBQUM7SUFDakIsQ0FBQztJQUVEOzs7O09BSUc7SUFDSyx3QkFBd0IsQ0FBRSxJQUFhO1FBQzlDLElBQUksQ0FBQyxFQUFFLENBQUMscUJBQXFCLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ3BFLE9BQU87UUFDUixDQUFDO1FBRUQsTUFBTSxFQUFFLFdBQVcsRUFBRSxHQUFHLElBQUksQ0FBQztRQUM3QixJQUFJLENBQUMsV0FBVyxFQUFFLENBQUM7WUFDbEIsT0FBTztRQUNSLENBQUM7UUFFRCxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsV0FBVyxDQUFDLElBQUksSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxXQUFXLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUN0RixJQUFJLENBQUMscUJBQXFCLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDaEQsQ0FBQztJQUNGLENBQUM7SUFFRDs7Ozs7Ozs7T0FRRztJQUNLLHNCQUFzQixDQUFFLElBQWEsRUFBRSxVQUF5QjtRQUN2RSxJQUFJLENBQUMsRUFBRSxDQUFDLHFCQUFxQixDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUNwRSxPQUFPO1FBQ1IsQ0FBQztRQUVELE1BQU0sRUFBRSxXQUFXLEVBQUUsR0FBRyxJQUFJLENBQUM7UUFDN0IsSUFBSSxDQUFDLFdBQVcsRUFBRSxDQUFDO1lBQ2xCLE9BQU87UUFDUixDQUFDO1FBRUQsc0NBQXNDO1FBQ3RDLElBQUksSUFBSSxDQUFDLDJCQUEyQixDQUFDLFdBQVcsQ0FBQyxFQUFFLENBQUM7WUFDbkQsdUVBQXVFO1lBQ3ZFLG1FQUFtRTtZQUNuRSx1RUFBdUU7WUFDdkUsTUFBTSxZQUFZLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxnQkFBZ0IsRUFBRSxDQUFDO1lBQzdGLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsWUFBWSxDQUFDLENBQUM7WUFFM0QsTUFBTSxxQkFBcUIsR0FBRyxJQUFJLENBQUMsNEJBQTRCLENBQzlELFdBQWdDLEVBQ2hDLFVBQVUsQ0FDVixDQUFDO1lBQ0YsTUFBTSxFQUFFLElBQUksRUFBRSxTQUFTLEVBQUUsR0FBRyxFQUFFLENBQUMsNkJBQTZCLENBQUMsVUFBVSxFQUFFLElBQUksQ0FBQyxRQUFRLEVBQUUsQ0FBQyxDQUFDO1lBQzFGLElBQUksQ0FBQyxjQUFjLENBQUMsR0FBRyxDQUFDLFlBQVksRUFBRTtnQkFDckMsWUFBWSxFQUFZLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSTtnQkFDdEMsVUFBVSxFQUFjLFVBQVUsQ0FBQyxRQUFRO2dCQUMzQyxxQkFBcUIsRUFBRyxxQkFBcUI7Z0JBQzdDLElBQUksRUFBb0IsSUFBSSxHQUFHLENBQUM7Z0JBQ2hDLE1BQU0sRUFBa0IsU0FBUyxHQUFHLENBQUM7YUFDckMsQ0FBQyxDQUFDO1lBQ0gsT0FBTztRQUNSLENBQUM7UUFFRCx1Q0FBdUM7UUFDdkMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFdBQVcsQ0FBQyxFQUFFLENBQUM7WUFDbEMsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxXQUFXLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDaEUsSUFBSSxRQUFRLEVBQUUsQ0FBQztnQkFDZCxJQUFJLENBQUMsbUJBQW1CLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLFFBQVEsQ0FBQyxDQUFDO1lBQ3hELENBQUM7UUFDRixDQUFDO0lBQ0YsQ0FBQztJQUVEOzs7T0FHRztJQUNLLDRCQUE0QixDQUNuQyxJQUF1QixFQUN2QixVQUF5QjtRQUV6QixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsYUFBYSxDQUFDO1FBQ3BDLElBQUksQ0FBQyxRQUFRLElBQUksUUFBUSxDQUFDLE1BQU0sS0FBSyxDQUFDLEVBQUUsQ0FBQztZQUN4QyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQsTUFBTSxDQUFFLFlBQVksQ0FBRSxHQUFHLFFBQVEsQ0FBQztRQUNsQyxJQUFJLENBQUMsRUFBRSxDQUFDLG1CQUFtQixDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxZQUFZLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUN0RixPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQsTUFBTSxJQUFJLEdBQUcsWUFBWSxDQUFDLFFBQVEsQ0FBQyxJQUFJLENBQUM7UUFFeEMsd0RBQXdEO1FBQ3hELEtBQUssTUFBTSxTQUFTLElBQUksVUFBVSxDQUFDLFVBQVUsRUFBRSxDQUFDO1lBQy9DLElBQ0MsRUFBRSxDQUFDLHNCQUFzQixDQUFDLFNBQVMsQ0FBQztnQkFDcEMsU0FBUyxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssSUFBSSxFQUMzQixDQUFDO2dCQUNGLE9BQU8sSUFBSSxDQUFDO1lBQ2IsQ0FBQztRQUNGLENBQUM7UUFFRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNLLDJCQUEyQixDQUFFLElBQWMsRUFBRSxZQUFxQjtRQUN6RSxJQUFJLENBQUMsWUFBWSxFQUFFLENBQUM7WUFDbkIsT0FBTztRQUNSLENBQUM7UUFDRCxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsY0FBYyxDQUFDLEdBQUcsQ0FBQyxZQUFZLENBQUMsQ0FBQztRQUNuRCxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDWCxPQUFPO1FBQ1IsQ0FBQztRQUNELElBQUksQ0FBQyxxQkFBcUIsR0FBRyxJQUFJLENBQUMscUJBQXFCLENBQUM7UUFDeEQsSUFBSSxDQUFDLG9CQUFvQixHQUFHLElBQUksQ0FBQyxVQUFVLENBQUM7SUFDN0MsQ0FBQztJQUVEOzs7Ozs7O09BT0c7SUFDSywyQkFBMkIsQ0FBRSxJQUFhO1FBQ2pELElBQUksQ0FBQyxFQUFFLENBQUMsZ0JBQWdCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUNoQyxPQUFPLEtBQUssQ0FBQztRQUNkLENBQUM7UUFDRCxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsVUFBVSxDQUFDO1FBRTdCLGlFQUFpRTtRQUNqRSxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUMzQixPQUFPLElBQUksQ0FBQyxJQUFJLEtBQUssdUJBQXVCO2dCQUMzQyxJQUFJLENBQUMsOEJBQThCLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNyRCxDQUFDO1FBRUQsMERBQTBEO1FBQzFELElBQ0MsRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQztZQUNuQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyx1QkFBdUI7WUFDMUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDO1lBQ2hDLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsRUFDbkQsQ0FBQztZQUNGLE9BQU8sSUFBSSxDQUFDO1FBQ2IsQ0FBQztRQUVELE9BQU8sS0FBSyxDQUFDO0lBQ2QsQ0FBQztJQUVEOztPQUVHO0lBQ0ssZ0JBQWdCO1FBQ3ZCLElBQUksQ0FBQyxpQkFBaUIsRUFBRSxDQUFDO1FBQ3pCLE1BQU0sTUFBTSxHQUFHLGNBQWMsSUFBSSxDQUFDLGlCQUFpQixFQUFFLENBQUM7UUFDdEQsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7O09BRUc7SUFDSyxZQUFZLENBQUUsSUFBYTtRQUNsQyxJQUFJLENBQUMsRUFBRSxDQUFDLGdCQUFnQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDaEMsT0FBTyxLQUFLLENBQUM7UUFDZCxDQUFDO1FBRUQsTUFBTSxFQUFFLFVBQVUsRUFBRSxHQUFHLElBQUksQ0FBQztRQUU1QixpREFBaUQ7UUFDakQsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFVBQVUsQ0FBQyxJQUFJLFVBQVUsQ0FBQyxJQUFJLEtBQUssUUFBUSxFQUFFLENBQUM7WUFDakUsT0FBTyxJQUFJLENBQUM7UUFDYixDQUFDO1FBRUQseURBQXlEO1FBQ3pELElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7WUFDL0MsT0FBTyxVQUFVLENBQUMsSUFBSSxFQUFFLElBQUksS0FBSyxRQUFRLENBQUM7UUFDM0MsQ0FBQztRQUVELE9BQU8sS0FBSyxDQUFDO0lBQ2QsQ0FBQztJQUVEOztPQUVHO0lBQ0ssVUFBVSxDQUFFLElBQWE7UUFDaEMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ2hDLE9BQU8sS0FBSyxDQUFDO1FBQ2QsQ0FBQztRQUVELE1BQU0sRUFBRSxVQUFVLEVBQUUsR0FBRyxJQUFJLENBQUM7UUFFNUIsdURBQXVEO1FBQ3ZELElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxVQUFVLENBQUMsSUFBSSxVQUFVLENBQUMsSUFBSSxLQUFLLE1BQU0sRUFBRSxDQUFDO1lBQy9ELE9BQU8sSUFBSSxDQUFDO1FBQ2IsQ0FBQztRQUVELCtEQUErRDtRQUMvRCxJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQy9DLE9BQU8sVUFBVSxDQUFDLElBQUksRUFBRSxJQUFJLEtBQUssTUFBTSxDQUFDO1FBQ3pDLENBQUM7UUFFRCxPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7SUFFRDs7VUFFRztJQUNLLDhCQUE4QixDQUFFLFNBQXFDO1FBRTVFLE1BQU0sTUFBTSxHQUFxRCxFQUFFLENBQUM7UUFFcEUsS0FBSyxNQUFNLElBQUksSUFBSSxTQUFTLENBQUMsVUFBVSxFQUFFLENBQUM7WUFDekMsSUFBSSxFQUFFLENBQUMsb0JBQW9CLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztnQkFDakUsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7Z0JBQ2hDLElBQUksUUFBUSxLQUFLLGFBQWEsSUFBSSxJQUFJLENBQUMsV0FBVyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFdBQVcsRUFBRSxDQUFDO29CQUN2RixNQUFNLENBQUMsV0FBVyxHQUFHLElBQUksQ0FBQztnQkFDM0IsQ0FBQztxQkFBTSxJQUFJLFFBQVEsS0FBSyxhQUFhLElBQUksSUFBSSxDQUFDLFdBQVcsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxZQUFZLEVBQUUsQ0FBQztvQkFDL0YsTUFBTSxDQUFDLFdBQVcsR0FBRyxLQUFLLENBQUM7Z0JBQzVCLENBQUM7cUJBQU0sSUFBSSxRQUFRLEtBQUssYUFBYSxJQUFJLElBQUksQ0FBQyxXQUFXLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVyxFQUFFLENBQUM7b0JBQzlGLE1BQU0sQ0FBQyxXQUFXLEdBQUcsSUFBSSxDQUFDO2dCQUMzQixDQUFDO3FCQUFNLElBQUksUUFBUSxLQUFLLGFBQWEsSUFBSSxJQUFJLENBQUMsV0FBVyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFlBQVksRUFBRSxDQUFDO29CQUMvRixNQUFNLENBQUMsV0FBVyxHQUFHLEtBQUssQ0FBQztnQkFDNUIsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7O1VBRUc7SUFDSyxhQUFhLENBQUUsSUFBdUI7UUFDN0MsZ0VBQWdFO1FBQ2hFLE1BQU0sQ0FBRSxBQUFELEVBQUcsQUFBRCxFQUFHLFNBQVMsQ0FBRSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUM7UUFDekMsSUFBSSxDQUFDLFNBQVMsSUFBSSxDQUFDLEVBQUUsQ0FBQyx5QkFBeUIsQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUFDO1lBQzVELE9BQU8sRUFBRSxDQUFDO1FBQ1gsQ0FBQztRQUVELE1BQU0sWUFBWSxHQUFHLElBQUksQ0FBQyw4QkFBOEIsQ0FBQyxTQUFTLENBQUMsQ0FBQztRQUNwRSxPQUFPLFlBQVksQ0FBQztJQUNyQixDQUFDO0lBRUQ7O1VBRUc7SUFDSyxtQkFBbUIsQ0FBRSxJQUFhO1FBQ3pDLElBQUksQ0FBQyxFQUFFLENBQUMsV0FBVyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDM0IsT0FBTyxLQUFLLENBQUM7UUFDZCxDQUFDO1FBRUQsTUFBTSxFQUFFLFVBQVUsRUFBRSxHQUFHLElBQUksQ0FBQztRQUU1QixzQkFBc0I7UUFDdEIsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFVBQVUsQ0FBQyxJQUFJLFVBQVUsQ0FBQyxJQUFJLEtBQUssVUFBVSxFQUFFLENBQUM7WUFDbkUsT0FBTyxJQUFJLENBQUM7UUFDYixDQUFDO1FBRUQsaURBQWlEO1FBQ2pELElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7WUFDckMsTUFBTSxNQUFNLEdBQUcsVUFBVSxDQUFDLFVBQVUsQ0FBQztZQUNyQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLElBQUksTUFBTSxDQUFDLElBQUksS0FBSyxVQUFVLEVBQUUsQ0FBQztnQkFDM0QsT0FBTyxJQUFJLENBQUM7WUFDYixDQUFDO1lBRUQsK0VBQStFO1lBQy9FLElBQ0MsRUFBRSxDQUFDLDBCQUEwQixDQUFDLE1BQU0sQ0FBQztnQkFDckMsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssVUFBVTtnQkFDL0IsRUFBRSxDQUFDLFlBQVksQ0FBQyxNQUFNLENBQUMsVUFBVSxDQUFDO2dCQUNsQyxJQUFJLENBQUMsbUJBQW1CLENBQUMsR0FBRyxDQUFDLE1BQU0sQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLEVBQ25ELENBQUM7Z0JBQ0YsT0FBTyxJQUFJLENBQUM7WUFDYixDQUFDO1FBQ0YsQ0FBQztRQUVELE9BQU8sS0FBSyxDQUFDO0lBQ2QsQ0FBQztJQUVEOztPQUVHO0lBQ0ssYUFBYSxDQUFFLElBQXVCO1FBQzdDLElBQUksSUFBSSxDQUFDLGNBQWMsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUNuQyxPQUFPLElBQUksQ0FBQztRQUNiLENBQUM7UUFDRCxJQUFJLENBQUMsY0FBYyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUM5QixPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7SUFFRDs7T0FFRztJQUNLLGlCQUFpQixDQUFFLElBQXVCLEVBQUUsVUFBeUI7UUFDNUUsK0ZBQStGO1FBQy9GLElBQUksSUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQzlCLE9BQU87UUFDUixDQUFDO1FBRUQsTUFBTSxhQUFhLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzFELElBQUksYUFBYSxLQUFLLFNBQVMsRUFBRSxDQUFDO1lBQ2pDLEtBQUssTUFBTSxRQUFRLElBQUksYUFBYSxFQUFFLENBQUM7Z0JBQ3RDLE1BQU0sZUFBZSxHQUFHLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLEVBQUUsUUFBUSxDQUFDLENBQUM7Z0JBQ2xFLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLEVBQUUsVUFBVSxFQUFFLGVBQWUsRUFBRSxJQUFJLENBQUMsQ0FBQztZQUNwRSxDQUFDO1lBQ0QsT0FBTztRQUNSLENBQUM7UUFFRCxzREFBc0Q7UUFDdEQsTUFBTSxhQUFhLEdBQUcsSUFBSSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ3RELElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLEVBQUUsVUFBVSxFQUFFLGFBQWEsRUFBRSxLQUFLLENBQUMsQ0FBQztJQUNuRSxDQUFDO0lBRU8sb0JBQW9CLENBQzNCLElBQXVCLEVBQ3ZCLFVBQXlCLEVBQ3pCLGFBSUMsRUFDRCxZQUFxQjtRQUVyQixnR0FBZ0c7UUFDaEcseUNBQXlDO1FBQ3pDLElBQUksWUFBWSxHQUFZLElBQUksQ0FBQztRQUVqQyxnRkFBZ0Y7UUFDaEYsNEJBQTRCO1FBQzVCLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQ3BELDJFQUEyRTtZQUMzRSxnREFBZ0Q7WUFDaEQsa0NBQWtDO1lBQ2xDLFlBQVksR0FBRyxJQUFJLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQztRQUNyQyxDQUFDO1FBRUQsTUFBTSxRQUFRLEdBQUcsWUFBWSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FBQztRQUNuRCxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FBQyxVQUFVLEVBQUUsUUFBUSxDQUFDLENBQUM7UUFFbkYsSUFBSSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsQ0FBQztZQUM3QixJQUFJLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQztnQkFDaEIsT0FBTyxFQUFHLGdEQUFnRDtnQkFDMUQsSUFBSSxFQUFNLFVBQVUsQ0FBQyxRQUFRO2dCQUM3QixJQUFJLEVBQU0sSUFBSSxHQUFHLENBQUM7Z0JBQ2xCLE1BQU0sRUFBSSxTQUFTLEdBQUcsQ0FBQzthQUN2QixDQUFDLENBQUM7WUFDSCxPQUFPO1FBQ1IsQ0FBQztRQUVELE1BQU0sRUFBRSxRQUFRLEVBQUUsR0FBRyxhQUFhLENBQUM7UUFFbkMsaUVBQWlFO1FBQ2pFLE1BQU0sVUFBVSxHQUFHLGFBQWEsQ0FBQyxVQUFVLENBQUM7UUFDNUMsTUFBTSxFQUFFLFlBQVksRUFBRSxHQUFHLGFBQWEsQ0FBQztRQUV2Qyx5QkFBeUI7UUFDekIsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUV4QyxpR0FBaUc7UUFDakcsTUFBTSxJQUFJLEdBQUcscUJBQWEsQ0FBQyxVQUFVLENBQ3BDLFFBQVEsRUFDUixVQUFVLEVBQ1YsVUFBVSxDQUFDLFFBQVEsRUFDbkIsSUFBSSxHQUFHLENBQUMsRUFDUixTQUFTLEdBQUcsQ0FBQyxFQUNiLFlBQVksQ0FDWixDQUFDO1FBQ0YsSUFBSSxDQUFDLDJCQUEyQixDQUFDLElBQUksRUFBRSxZQUFZLENBQUMsQ0FBQztRQUNyRCxJQUFJLENBQUMsWUFBWSxHQUFHLFlBQVksQ0FBQztRQUVqQyxpRUFBaUU7UUFDakUsa0VBQWtFO1FBQ2xFLHlDQUF5QztRQUN6QyxJQUFJLENBQUMsZ0JBQWdCLENBQ3BCLFVBQVUsQ0FBQyxDQUFDLENBQUMsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLFFBQVEsRUFBRSxDQUFDLENBQUMsQ0FBQyxHQUFHLFlBQVksSUFBSSxTQUFTLEtBQUssUUFBUSxFQUFFLEVBQy9GLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FDckQsQ0FBQztRQUVGLHNFQUFzRTtRQUN0RSxvRUFBb0U7UUFDcEUsZ0JBQWdCO1FBQ2hCLE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQyxrQkFBa0IsQ0FBQztRQUMvQyxJQUFJLENBQUMsa0JBQWtCLEdBQUcsSUFBSSxDQUFDO1FBQy9CLElBQUksQ0FBQztZQUNKLElBQUksQ0FBQyxVQUFVLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLElBQUksQ0FBQyxDQUFDO1lBRS9DLDREQUE0RDtZQUM1RCxJQUFJLENBQUMsaUJBQWlCLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzlELENBQUM7Z0JBQVMsQ0FBQztZQUNWLElBQUksQ0FBQyxrQkFBa0IsR0FBRyxjQUFjLENBQUM7UUFDMUMsQ0FBQztRQUVELE1BQU0sZUFBZSxHQUFHLElBQUksQ0FBQyw0QkFBNEIsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNoRSxJQUFJLENBQUMsb0JBQW9CLEdBQUcsSUFBSSxDQUFDLG9CQUFvQixDQUFDLGVBQWUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQztRQUMzRiwrREFBK0Q7UUFDL0QsSUFBSSxDQUFDLE9BQU8sR0FBRyxJQUFJLENBQUMsdUJBQXVCLENBQUMsSUFBSSxDQUFDLDRCQUE0QixDQUFDLElBQUksQ0FBQyxDQUFDLENBQUM7UUFFckYsZUFBZTtRQUNmLElBQUksVUFBVSxFQUFFLENBQUM7WUFDaEIsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsVUFBVSxFQUFFLElBQUksQ0FBQyxDQUFDO1FBQ3ZDLENBQUM7YUFBTSxDQUFDO1lBQ1AsSUFBSSxDQUFDLEtBQUssQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDMUIsQ0FBQztRQUVELDREQUE0RDtRQUM1RCxNQUFNLFVBQVUsR0FBbUI7WUFDbEMsSUFBSSxFQUFVLFFBQVE7WUFDdEIsUUFBUSxFQUFNLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUU7WUFDbkUsSUFBSSxFQUFVLFFBQVE7WUFDdEIsTUFBTSxFQUFRLFVBQVUsQ0FBQyxDQUFDLENBQUMsVUFBVSxDQUFDLFFBQVEsQ0FBQyxDQUFDLENBQUMsSUFBSTtZQUNyRCxXQUFXLEVBQUcsTUFBTSxDQUFDLFdBQVcsSUFBSSxJQUFJO1lBQ3hDLFdBQVcsRUFBRyxNQUFNLENBQUMsV0FBVyxJQUFJLEtBQUs7U0FDekMsQ0FBQztRQUNGLElBQUksQ0FBQyxXQUFXLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxRQUFRLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFDaEQsSUFBSSxDQUFDLFlBQVksRUFBRSxDQUFDO1lBQ25CLElBQUksQ0FBQyxjQUFjLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsUUFBUSxDQUFDLENBQUM7WUFFN0Msa0dBQWtHO1lBQ2xHLG1FQUFtRTtZQUNuRSxtQ0FBbUM7WUFDbkMsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksRUFBRSxVQUFVLEVBQUUsSUFBSSxDQUFDLFFBQVEsRUFBRSxVQUFVLENBQUMsQ0FBQztRQUMzRSxDQUFDO0lBQ0YsQ0FBQztJQUVEOztPQUVHO0lBQ0ssZUFBZSxDQUFFLElBQXVCLEVBQUUsVUFBeUI7UUFDMUUsK0ZBQStGO1FBQy9GLElBQUksSUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQzlCLE9BQU87UUFDUixDQUFDO1FBRUQsc0RBQXNEO1FBQ3RELE1BQU0sV0FBVyxHQUFHLElBQUksQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFFOUQsNEZBQTRGO1FBQzVGLHlDQUF5QztRQUN6QyxJQUFJLFlBQVksR0FBWSxJQUFJLENBQUM7UUFFakMsZ0ZBQWdGO1FBQ2hGLDBCQUEwQjtRQUMxQixJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztZQUNwRCx5RUFBeUU7WUFDekUsOENBQThDO1lBQzlDLGdDQUFnQztZQUNoQyxZQUFZLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUM7UUFDckMsQ0FBQztRQUVELE1BQU0sUUFBUSxHQUFHLFlBQVksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDbkQsTUFBTSxFQUFFLElBQUksRUFBRSxTQUFTLEVBQUUsR0FBRyxFQUFFLENBQUMsNkJBQTZCLENBQUMsVUFBVSxFQUFFLFFBQVEsQ0FBQyxDQUFDO1FBRW5GLGdFQUFnRTtRQUNoRSxxRUFBcUU7UUFDckUsZ0VBQWdFO1FBQ2hFLG9FQUFvRTtRQUNwRSxnRUFBZ0U7UUFDaEUsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ2hELElBQUksUUFBUSxJQUFJLFFBQVEsQ0FBQyxJQUFJLEtBQUssU0FBUyxFQUFFLENBQUM7WUFDN0MsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUM7Z0JBQ2hCLE9BQU8sRUFBRyxxREFBcUQ7Z0JBQy9ELElBQUksRUFBTSxVQUFVLENBQUMsUUFBUTtnQkFDN0IsSUFBSSxFQUFNLElBQUksR0FBRyxDQUFDO2dCQUNsQixNQUFNLEVBQUksU0FBUyxHQUFHLENBQUM7YUFDdkIsQ0FBQyxDQUFDO1lBQ0gsT0FBTztRQUNSLENBQUM7UUFFRCxJQUFJLENBQUMsV0FBVyxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQzNCLElBQUksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDO2dCQUNoQixPQUFPLEVBQUcsOENBQThDO2dCQUN4RCxJQUFJLEVBQU0sVUFBVSxDQUFDLFFBQVE7Z0JBQzdCLElBQUksRUFBTSxJQUFJLEdBQUcsQ0FBQztnQkFDbEIsTUFBTSxFQUFJLFNBQVMsR0FBRyxDQUFDO2FBQ3ZCLENBQUMsQ0FBQztZQUNILE9BQU87UUFDUixDQUFDO1FBRUQsTUFBTSxFQUFFLFFBQVEsRUFBRSxHQUFHLFdBQVcsQ0FBQztRQUVqQyxpRUFBaUU7UUFDakUsTUFBTSxVQUFVLEdBQUcsV0FBVyxDQUFDLFVBQVUsQ0FBQztRQUMxQyxNQUFNLEVBQUUsWUFBWSxFQUFFLEdBQUcsV0FBVyxDQUFDO1FBRXJDLHlCQUF5QjtRQUN6QixNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsSUFBSSxDQUFDLENBQUM7UUFFNUMsaUdBQWlHO1FBQ2pHLE1BQU0sSUFBSSxHQUFHLHFCQUFhLENBQUMsVUFBVSxDQUNwQyxRQUFRLEVBQ1IsVUFBVSxFQUNWLFVBQVUsQ0FBQyxRQUFRLEVBQ25CLElBQUksR0FBRyxDQUFDLEVBQ1IsU0FBUyxHQUFHLENBQUMsRUFDYixZQUFZLENBQ1osQ0FBQztRQUNGLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxJQUFJLEVBQUUsWUFBWSxDQUFDLENBQUM7UUFFckQscURBQXFEO1FBQ3JELElBQUksQ0FBQyxnQkFBZ0IsQ0FDcEIsVUFBVSxDQUFDLENBQUMsQ0FBQyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksUUFBUSxFQUFFLENBQUMsQ0FBQyxDQUFDLEdBQUcsWUFBWSxJQUFJLFNBQVMsS0FBSyxRQUFRLEVBQUUsRUFDL0YsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsRUFBRSxDQUNyRCxDQUFDO1FBRUYsc0VBQXNFO1FBQ3RFLG1FQUFtRTtRQUNuRSxNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsa0JBQWtCLENBQUM7UUFDL0MsSUFBSSxDQUFDLGtCQUFrQixHQUFHLElBQUksQ0FBQztRQUMvQixJQUFJLENBQUM7WUFDSixJQUFJLENBQUMsVUFBVSxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUUvQyw0REFBNEQ7WUFDNUQsSUFBSSxDQUFDLGlCQUFpQixHQUFHLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUM5RCxDQUFDO2dCQUFTLENBQUM7WUFDVixJQUFJLENBQUMsa0JBQWtCLEdBQUcsY0FBYyxDQUFDO1FBQzFDLENBQUM7UUFFRCxNQUFNLGVBQWUsR0FBRyxJQUFJLENBQUMsNEJBQTRCLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDaEUsSUFBSSxDQUFDLG9CQUFvQixHQUFHLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxlQUFlLENBQUMsQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUM7UUFDM0YsK0RBQStEO1FBQy9ELElBQUksQ0FBQyxPQUFPLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksQ0FBQyw0QkFBNEIsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDO1FBRXJGLGVBQWU7UUFDZixJQUFJLFVBQVUsRUFBRSxDQUFDO1lBQ2hCLElBQUksQ0FBQyxLQUFLLENBQUMsUUFBUSxDQUFDLFVBQVUsRUFBRSxJQUFJLENBQUMsQ0FBQztRQUN2QyxDQUFDO2FBQU0sQ0FBQztZQUNQLElBQUksQ0FBQyxLQUFLLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzFCLENBQUM7UUFFRCw0REFBNEQ7UUFDNUQsTUFBTSxVQUFVLEdBQW1CO1lBQ2xDLElBQUksRUFBVSxRQUFRO1lBQ3RCLFFBQVEsRUFBTSxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFO1lBQ25FLElBQUksRUFBVSxRQUFRO1lBQ3RCLE1BQU0sRUFBUSxVQUFVLENBQUMsQ0FBQyxDQUFDLFVBQVUsQ0FBQyxRQUFRLENBQUMsQ0FBQyxDQUFDLElBQUk7WUFDckQsV0FBVyxFQUFHLE1BQU0sQ0FBQyxXQUFXLElBQUksSUFBSTtZQUN4QyxXQUFXLEVBQUcsTUFBTSxDQUFDLFdBQVcsSUFBSSxLQUFLO1NBQ3pDLENBQUM7UUFDRixJQUFJLENBQUMsV0FBVyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLFVBQVUsQ0FBQyxDQUFDO1FBQ2hELElBQUksQ0FBQyxjQUFjLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsUUFBUSxDQUFDLENBQUM7UUFFN0Msb0dBQW9HO1FBQ3BHLDJGQUEyRjtRQUMzRixJQUFJLENBQUMsdUJBQXVCLENBQUMsSUFBSSxFQUFFLFVBQVUsRUFBRSxJQUFJLENBQUMsUUFBUSxFQUFFLFVBQVUsQ0FBQyxDQUFDO0lBQzNFLENBQUM7SUFFRDs7Ozs7O09BTUc7SUFDSyxtQkFBbUIsQ0FBRSxJQUF1QjtRQU1uRCxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsU0FBUyxDQUFDO1FBQzVCLE1BQU0sWUFBWSxHQUFHLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLENBQUM7UUFFcEUsSUFBSSxZQUFZLEVBQUUsQ0FBQztZQUNsQiw4REFBOEQ7WUFDOUQsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQyxVQUFVLENBQUM7WUFDMUMsSUFBSSxJQUFJLENBQUMsTUFBTSxLQUFLLENBQUMsRUFBRSxDQUFDO2dCQUN2QixPQUFPLFNBQVMsQ0FBQztZQUNsQixDQUFDO1lBQ0QsTUFBTSxDQUFFLGNBQWMsQ0FBRSxHQUFHLElBQUksQ0FBQztZQUNoQyxJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsY0FBYyxDQUFDLEVBQUUsQ0FBQztnQkFDeEMscUNBQXFDO2dCQUNyQyxJQUFJLElBQUksQ0FBQyxNQUFNLEdBQUcsQ0FBQyxFQUFFLENBQUM7b0JBQ3JCLE9BQU8sU0FBUyxDQUFDO2dCQUNsQixDQUFDO2dCQUNELE9BQU87b0JBQ04sTUFBTTtvQkFDTixJQUFJLEVBQUssY0FBYyxDQUFDLElBQUk7b0JBQzVCLE1BQU0sRUFBRyxJQUFJLENBQUUsQ0FBQyxDQUFFO29CQUNsQixNQUFNLEVBQUcsSUFBSSxDQUFFLENBQUMsQ0FBRTtpQkFDbEIsQ0FBQztZQUNILENBQUM7WUFDRCw2QkFBNkI7WUFDN0IsT0FBTztnQkFDTixNQUFNO2dCQUNOLE1BQU0sRUFBRyxjQUFjO2dCQUN2QixNQUFNLEVBQUcsSUFBSSxDQUFFLENBQUMsQ0FBRTthQUNsQixDQUFDO1FBQ0gsQ0FBQztRQUVELHVCQUF1QjtRQUN2QixJQUFJLElBQUksQ0FBQyxNQUFNLEtBQUssQ0FBQyxFQUFFLENBQUM7WUFDdkIsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELE1BQU0sQ0FBRSxRQUFRLENBQUUsR0FBRyxJQUFJLENBQUM7UUFFMUIsOERBQThEO1FBQzlELG1DQUFtQztRQUNuQyxJQUFJLElBQUksQ0FBQyxNQUFNLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUNuRCxNQUFNLENBQUUsQUFBRCxFQUFHLFNBQVMsQ0FBRSxHQUFHLElBQUksQ0FBQztZQUM3QixJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsU0FBUyxDQUFDLEVBQUUsQ0FBQztnQkFDbkMsd0NBQXdDO2dCQUN4QyxJQUFJLElBQUksQ0FBQyxNQUFNLEdBQUcsQ0FBQyxFQUFFLENBQUM7b0JBQ3JCLE9BQU8sU0FBUyxDQUFDO2dCQUNsQixDQUFDO2dCQUNELE9BQU87b0JBQ04sTUFBTSxFQUFHLFFBQVE7b0JBQ2pCLElBQUksRUFBSyxTQUFTLENBQUMsSUFBSTtvQkFDdkIsTUFBTSxFQUFHLElBQUksQ0FBRSxDQUFDLENBQUU7b0JBQ2xCLE1BQU0sRUFBRyxJQUFJLENBQUUsQ0FBQyxDQUFFO2lCQUNsQixDQUFDO1lBQ0gsQ0FBQztZQUNELGdDQUFnQztZQUNoQyxPQUFPO2dCQUNOLE1BQU0sRUFBRyxRQUFRO2dCQUNqQixNQUFNLEVBQUcsU0FBUztnQkFDbEIsTUFBTSxFQUFHLElBQUksQ0FBRSxDQUFDLENBQUU7YUFDbEIsQ0FBQztRQUNILENBQUM7UUFFRCxpREFBaUQ7UUFDakQsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDbEMsSUFBSSxJQUFJLENBQUMsTUFBTSxHQUFHLENBQUMsRUFBRSxDQUFDO2dCQUNyQixPQUFPLFNBQVMsQ0FBQztZQUNsQixDQUFDO1lBQ0QsT0FBTztnQkFDTixJQUFJLEVBQUssUUFBUSxDQUFDLElBQUk7Z0JBQ3RCLE1BQU0sRUFBRyxJQUFJLENBQUUsQ0FBQyxDQUFFO2dCQUNsQixNQUFNLEVBQUcsSUFBSSxDQUFFLENBQUMsQ0FBRTthQUNsQixDQUFDO1FBQ0gsQ0FBQztRQUVELDJDQUEyQztRQUMzQyxPQUFPO1lBQ04sTUFBTSxFQUFHLFFBQVE7WUFDakIsTUFBTSxFQUFHLElBQUksQ0FBRSxDQUFDLENBQUU7U0FDbEIsQ0FBQztJQUNILENBQUM7SUFFRDs7Ozs7OztPQU9HO0lBQ0ssZ0JBQWdCLENBQUUsVUFBeUI7UUFDbEQsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7WUFDcEMsTUFBTSxFQUFFLElBQUksRUFBRSxHQUFHLFVBQVUsQ0FBQztZQUM1QixJQUFJLENBQUMsRUFBRSxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUN2QixPQUFPLElBQUksQ0FBQztZQUNiLENBQUM7WUFDRCxLQUFLLE1BQU0sSUFBSSxJQUFJLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztnQkFDcEMsSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLFVBQVUsRUFBRSxDQUFDO29CQUNuRCxPQUFPLElBQUksQ0FBQyxVQUFVLENBQUM7Z0JBQ3hCLENBQUM7WUFDRixDQUFDO1lBQ0QsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELElBQUksRUFBRSxDQUFDLG9CQUFvQixDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7WUFDekMsTUFBTSxFQUFFLElBQUksRUFBRSxHQUFHLFVBQVUsQ0FBQztZQUM1QixLQUFLLE1BQU0sSUFBSSxJQUFJLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztnQkFDcEMsSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLFVBQVUsRUFBRSxDQUFDO29CQUNuRCxPQUFPLElBQUksQ0FBQyxVQUFVLENBQUM7Z0JBQ3hCLENBQUM7WUFDRixDQUFDO1lBQ0QsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELGtDQUFrQztRQUNsQyxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7OztPQUdHO0lBQ0ssc0JBQXNCLENBQUUsZUFBbUM7UUFDbEUsSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsZUFBZSxDQUFDLElBQUksZUFBZSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ25FLE9BQU8sZUFBZSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7UUFDbEMsQ0FBQztRQUNELElBQUksRUFBRSxDQUFDLGtCQUFrQixDQUFDLGVBQWUsQ0FBQyxJQUFJLGVBQWUsQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUNwRSxPQUFPLGVBQWUsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1FBQ2xDLENBQUM7UUFDRCxJQUFJLEVBQUUsQ0FBQyxvQkFBb0IsQ0FBQyxlQUFlLENBQUMsSUFBSSxlQUFlLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDdEUsT0FBTyxlQUFlLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztRQUNsQyxDQUFDO1FBQ0QsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOztPQUVHO0lBQ0ssd0JBQXdCLENBQUUsSUFBdUI7UUFDeEQsSUFBSSxJQUFJLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDN0IsT0FBTyxJQUFJLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ25DLENBQUM7UUFDRCxJQUFJLElBQUksQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUMzQixNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDNUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO2dCQUNYLE9BQU8sU0FBUyxDQUFDO1lBQ2xCLENBQUM7WUFDRCxJQUFJLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQztnQkFDZixPQUFPLElBQUksQ0FBQyxJQUFJLENBQUM7WUFDbEIsQ0FBQztZQUNELE1BQU0sZUFBZSxHQUFHLElBQUksQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLENBQUM7WUFDM0QsSUFBSSxlQUFlLEVBQUUsQ0FBQztnQkFDckIsT0FBTyxJQUFJLENBQUMsc0JBQXNCLENBQUMsZUFBZSxDQUFDLENBQUM7WUFDckQsQ0FBQztRQUNGLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7Ozs7T0FJRztJQUNLLGtCQUFrQixDQUFFLElBQXVCLEVBQUUsVUFBeUI7UUFLN0UsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzVDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUNYLE9BQU8sRUFBRSxDQUFDO1FBQ1gsQ0FBQztRQUVELElBQUksUUFBUSxHQUF1QixJQUFJLENBQUMsSUFBSSxDQUFDO1FBQzdDLElBQUksQ0FBQyxRQUFRLEVBQUUsQ0FBQztZQUNmLE1BQU0sZUFBZSxHQUFHLElBQUksQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLENBQUM7WUFDM0QsSUFBSSxlQUFlLEVBQUUsQ0FBQztnQkFDckIsUUFBUSxHQUFHLElBQUksQ0FBQyxzQkFBc0IsQ0FBQyxlQUFlLENBQUMsQ0FBQztZQUN6RCxDQUFDO1FBQ0YsQ0FBQztRQUNELElBQUksQ0FBQyxRQUFRLEVBQUUsQ0FBQztZQUNmLE9BQU8sRUFBRSxDQUFDO1FBQ1gsQ0FBQztRQUVELE1BQU0sRUFBRSxVQUFVLEVBQUUsR0FBRyxJQUFJLENBQUM7UUFFNUIseUVBQXlFO1FBQ3pFLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxVQUFVLENBQUMsSUFBSSxVQUFVLENBQUMsSUFBSSxLQUFLLE1BQU0sRUFBRSxDQUFDO1lBQy9ELElBQUksSUFBSSxDQUFDLE1BQU0sSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxNQUFNLENBQUMsRUFBRSxDQUFDO2dCQUNqRCxNQUFNLGFBQWEsR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDakUsT0FBTztvQkFDTixRQUFRO29CQUNSLFVBQVUsRUFBSyxhQUFhLENBQUMsVUFBVTtvQkFDdkMsWUFBWSxFQUFHLGFBQWEsQ0FBQyxZQUFZO2lCQUN6QyxDQUFDO1lBQ0gsQ0FBQztZQUNELHdDQUF3QztZQUN4QyxPQUFPLEVBQUUsUUFBUSxFQUFFLENBQUM7UUFDckIsQ0FBQztRQUVELDJDQUEyQztRQUMzQyxJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxVQUFVLENBQUMsSUFBSSxVQUFVLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxNQUFNLEVBQUUsQ0FBQztZQUNsRixNQUFNLEdBQUcsR0FBRyxVQUFVLENBQUMsVUFBVSxDQUFDO1lBRWxDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO2dCQUMxQixNQUFNLGFBQWEsR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO2dCQUN6RCxPQUFPO29CQUNOLFFBQVE7b0JBQ1IsVUFBVSxFQUFLLGFBQWEsQ0FBQyxVQUFVO29CQUN2QyxZQUFZLEVBQUcsYUFBYSxDQUFDLFlBQVk7aUJBQ3pDLENBQUM7WUFDSCxDQUFDO1lBRUQsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztnQkFDeEMscURBQXFEO2dCQUNyRCxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMsZ0JBQWdCLENBQUMsR0FBRyxDQUFDLENBQUM7Z0JBQ3pDLElBQUksS0FBSyxDQUFDLE1BQU0sR0FBRyxDQUFDLEVBQUUsQ0FBQztvQkFDdEIsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDO29CQUN4RCxPQUFPLEVBQUUsUUFBUSxFQUFFLFVBQVUsRUFBRyxVQUFVLEVBQUUsQ0FBQztnQkFDOUMsQ0FBQztZQUNGLENBQUM7WUFFRCxJQUFJLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO2dCQUM5QixzRUFBc0U7Z0JBQ3RFLDZFQUE2RTtnQkFDN0UsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsQ0FBQztnQkFDdEQsTUFBTSxvQkFBb0IsR0FBRyxNQUFNO29CQUNsQyxDQUFDLENBQUMsSUFBSSxDQUFDLG1CQUFtQixDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBQyxZQUFZO29CQUNwRCxDQUFDLENBQUMsU0FBUyxDQUFDO2dCQUViLDZEQUE2RDtnQkFDN0QsSUFBSSxJQUFJLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7b0JBQzVCLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLEVBQUUsVUFBVSxDQUFDLENBQUM7b0JBQ3hDLE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxHQUFHLENBQUMsQ0FBQztvQkFDMUQsSUFBSSxjQUFjLEVBQUUsQ0FBQzt3QkFDcEIsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLG9CQUFvQixDQUFDLGNBQWMsRUFBRSxvQkFBb0IsQ0FBQyxDQUFDO3dCQUNuRixPQUFPLEVBQUUsUUFBUSxFQUFFLFVBQVUsRUFBRyxVQUFVLEVBQUUsWUFBWSxFQUFHLFVBQVUsRUFBRSxZQUFZLEVBQUUsQ0FBQztvQkFDdkYsQ0FBQztnQkFDRixDQUFDO2dCQUVELElBQUksSUFBSSxDQUFDLFVBQVUsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO29CQUMxQixJQUFJLENBQUMsZUFBZSxDQUFDLEdBQUcsRUFBRSxVQUFVLENBQUMsQ0FBQztvQkFDdEMsTUFBTSxjQUFjLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLEdBQUcsQ0FBQyxDQUFDO29CQUMxRCxJQUFJLGNBQWMsRUFBRSxDQUFDO3dCQUNwQixNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsb0JBQW9CLENBQUMsY0FBYyxFQUFFLG9CQUFvQixDQUFDLENBQUM7d0JBQ25GLE9BQU8sRUFBRSxRQUFRLEVBQUUsVUFBVSxFQUFHLFVBQVUsRUFBRSxZQUFZLEVBQUcsVUFBVSxFQUFFLFlBQVksRUFBRSxDQUFDO29CQUN2RixDQUFDO2dCQUNGLENBQUM7Z0JBRUQseURBQXlEO2dCQUN6RCxJQUFJLElBQUksQ0FBQyxZQUFZLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztvQkFDNUIsTUFBTSxZQUFZLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxDQUFDO29CQUNqRCxJQUFJLFlBQVksRUFBRSxDQUFDO3dCQUNsQixNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDLFFBQVEsQ0FBQyxZQUFZLENBQUMsQ0FBQzt3QkFDckQsSUFBSSxVQUFVLEVBQUUsQ0FBQzs0QkFDaEIsT0FBTyxFQUFFLFFBQVEsRUFBRSxVQUFVLEVBQUcsVUFBVSxFQUFFLFlBQVksRUFBRyxVQUFVLENBQUMsWUFBWSxFQUFFLENBQUM7d0JBQ3RGLENBQUM7b0JBQ0YsQ0FBQztnQkFDRixDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFFRCxPQUFPLEVBQUUsUUFBUSxFQUFFLENBQUM7SUFDckIsQ0FBQztJQUVEOztPQUVHO0lBQ0ssaUJBQWlCLENBQUUsSUFBdUI7UUFDakQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzVDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsTUFBTSxJQUFJLENBQUMsRUFBRSxDQUFDLHlCQUF5QixDQUFDLElBQUksQ0FBQyxNQUFNLENBQUMsRUFBRSxDQUFDO1lBQ3pFLE9BQU8sRUFBRSxDQUFDO1FBQ1gsQ0FBQztRQUVELE1BQU0sWUFBWSxHQUFHLElBQUksQ0FBQyw4QkFBOEIsQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLENBQUM7UUFDdEUsT0FBTyxZQUFZLENBQUM7SUFDckIsQ0FBQztJQUVPLHlCQUF5QixDQUFFLE9BQXVDO1FBQ3pFLElBQUksQ0FBQyxPQUFPLEVBQUUsQ0FBQztZQUNkLE9BQU8sS0FBSyxDQUFDO1FBQ2QsQ0FBQztRQUNELE1BQU0sT0FBTyxHQUFHLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLHlCQUF5QixDQUFDLENBQUM7UUFDOUUsSUFBSSxDQUFDLE9BQU8sSUFBSSxPQUFPLENBQUMsSUFBSSxLQUFLLENBQUMsRUFBRSxDQUFDO1lBQ3BDLE9BQU8sS0FBSyxDQUFDO1FBQ2QsQ0FBQztRQUNELElBQUksS0FBSyxHQUFHLEtBQUssQ0FBQztRQUNsQixNQUFNLEtBQUssR0FBRyxDQUFDLElBQWEsRUFBUSxFQUFFO1lBQ3JDLElBQUksS0FBSyxFQUFFLENBQUM7Z0JBQ1gsT0FBTztZQUNSLENBQUM7WUFDRCxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksT0FBTyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztnQkFDckQsS0FBSyxHQUFHLElBQUksQ0FBQztnQkFDYixPQUFPO1lBQ1IsQ0FBQztZQUNELEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxFQUFFLEtBQUssQ0FBQyxDQUFDO1FBQzlCLENBQUMsQ0FBQztRQUNGLEtBQUssQ0FBQyxPQUFPLENBQUMsQ0FBQztRQUNmLE9BQU8sS0FBSyxDQUFDO0lBQ2QsQ0FBQztJQUVPLHFCQUFxQixDQUFFLE9BQXVDLEVBQUUsUUFBZ0I7UUFDdkYsSUFBSSxDQUFDLE9BQU8sSUFBSSxDQUFDLEVBQUUsQ0FBQyxjQUFjLENBQUMsT0FBTyxDQUFDLEVBQUUsQ0FBQztZQUM3QyxPQUFPLEtBQUssQ0FBQztRQUNkLENBQUM7UUFDRCxNQUFNLFFBQVEsR0FBRyxRQUFRLENBQUMsS0FBSyxDQUFDLEdBQUcsQ0FBQyxDQUFDLEdBQUcsRUFBRSxDQUFDO1FBQzNDLEtBQUssTUFBTSxTQUFTLElBQUksT0FBTyxDQUFDLFVBQVUsRUFBRSxDQUFDO1lBQzVDLElBQUksQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsSUFBSSxTQUFTLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxNQUFNLElBQUksQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLENBQUM7Z0JBQzNGLFNBQVM7WUFDVixDQUFDO1lBQ0QsTUFBTSxVQUFVLEdBQUcsU0FBUyxDQUFDLElBQUksQ0FBQyxPQUFPLEVBQUUsQ0FBQztZQUM1QyxNQUFNLE1BQU0sR0FBRyxVQUFVLEtBQUssUUFBUSxJQUFJLFVBQVUsQ0FBQyxRQUFRLENBQUMsSUFBSSxRQUFRLEVBQUUsQ0FBQztnQkFDNUUsVUFBVSxLQUFLLHVCQUF1QixRQUFRLEdBQUcsQ0FBQztZQUNuRCxPQUFPLE1BQU0sQ0FBQztRQUNmLENBQUM7UUFDRCxPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7SUFFTyxzQkFBc0IsQ0FDN0IsSUFBWSxFQUNaLFFBQWdCLEVBQ2hCLElBQTZCLEVBQzdCLFVBQXlCLEVBQ3pCLFdBQW1DLEVBQ25DLFFBQWlCO1FBRWpCLE1BQU0sU0FBUyxHQUFxQjtZQUNuQyxJQUFJO1lBQ0osVUFBVSxFQUFHLFVBQVUsQ0FBQyxRQUFRO1lBQ2hDLElBQUk7WUFDSixRQUFRO1lBQ1IsT0FBTyxFQUFNLEVBQUU7WUFDZixRQUFRO1NBQ1IsQ0FBQztRQUNGLE1BQU0sU0FBUyxHQUFHLFdBQVcsQ0FBQyxNQUFNLENBQUMsTUFBTSxDQUFDO1FBQzVDLE1BQU0sU0FBUyxHQUFHLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxTQUFTLENBQUMsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQztRQUM1RixNQUFNLFNBQVMsR0FBRyxTQUFTLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUMsUUFBUSxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGNBQWMsQ0FBQyxDQUFDO1FBQzdGLE1BQU0sVUFBVSxHQUFHLFNBQVMsQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQyxRQUFRLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsYUFBYSxDQUFDLENBQUM7UUFDN0YsSUFBSSxVQUFVLEVBQUUsQ0FBQztZQUNoQixTQUFTLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQztnQkFDdEIsSUFBSSxFQUFZLElBQUk7Z0JBQ3BCLFVBQVUsRUFBTSxVQUFVLENBQUMsUUFBUTtnQkFDbkMsYUFBYSxFQUFHLFNBQVM7YUFDekIsQ0FBQyxDQUFDO1FBQ0osQ0FBQztRQUNELElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUM7SUFDeEMsQ0FBQztJQUVPLGlCQUFpQixDQUN4QixZQUFvQixFQUNwQixZQUFvQixFQUNwQixRQUFnQixFQUNoQixlQUF3QjtRQUV4QixJQUFJLENBQUMsZUFBZSxFQUFFLENBQUM7WUFDdEIsS0FBSyxNQUFNLFNBQVMsSUFBSSxJQUFJLENBQUMsaUJBQWlCLEVBQUUsQ0FBQztnQkFDaEQsTUFBTSxnQkFBZ0IsR0FBRyxRQUFRLENBQUMsT0FBTyxDQUFDLFNBQVMsQ0FBQyxVQUFVLENBQUMsS0FBSyxRQUFRLENBQUMsT0FBTyxDQUFDLFFBQVEsQ0FBQzt1QkFDMUYsU0FBUyxDQUFDLElBQUksS0FBSyxZQUFZO3VCQUMvQixDQUFDLFNBQVMsQ0FBQyxRQUFRLENBQUM7Z0JBQ3hCLElBQUksZ0JBQWdCLEVBQUUsQ0FBQztvQkFDdEIsU0FBUyxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsRUFBRSxJQUFJLEVBQUcsWUFBWSxFQUFFLFVBQVUsRUFBRyxRQUFRLEVBQUUsQ0FBQyxDQUFDO2dCQUN4RSxDQUFDO1lBQ0YsQ0FBQztZQUNELE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLDJCQUEyQixDQUFDLGVBQWUsRUFBRSxRQUFRLENBQUMsQ0FBQztRQUMvRSxJQUFJLFVBQVUsRUFBRSxVQUFVLEVBQUUsQ0FBQztZQUM1QixPQUFPO1FBQ1IsQ0FBQztRQUNELE1BQU0sWUFBWSxHQUFHLGVBQWUsQ0FBQyxRQUFRLENBQUMsS0FBSyxDQUFDO1lBQ25ELENBQUMsQ0FBQyxRQUFRLENBQUMsT0FBTyxDQUFDLFFBQVEsQ0FBQyxPQUFPLENBQUMsUUFBUSxDQUFDLEVBQUUsZUFBZSxDQUFDO1lBQy9ELENBQUMsQ0FBQyxHQUFHLFFBQVEsQ0FBQyxPQUFPLENBQUMsUUFBUSxDQUFDLE9BQU8sQ0FBQyxRQUFRLENBQUMsRUFBRSxlQUFlLENBQUMsS0FBSyxDQUFDO1FBQ3pFLE1BQU0sWUFBWSxHQUFHLFVBQVUsRUFBRSxZQUFZLElBQUksWUFBWSxDQUFDO1FBQzlELEtBQUssTUFBTSxTQUFTLElBQUksSUFBSSxDQUFDLGlCQUFpQixFQUFFLENBQUM7WUFDaEQsSUFBSSxRQUFRLENBQUMsT0FBTyxDQUFDLFNBQVMsQ0FBQyxVQUFVLENBQUMsS0FBSyxRQUFRLENBQUMsT0FBTyxDQUFDLFlBQVksQ0FBQyxJQUFJLFNBQVMsQ0FBQyxRQUFRLEVBQUUsQ0FBQztnQkFDckcsU0FBUztZQUNWLENBQUM7WUFDRCxNQUFNLFdBQVcsR0FBRyxZQUFZLEtBQUssU0FBUztnQkFDN0MsQ0FBQyxDQUFDLFNBQVMsQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUMsUUFBUSxDQUFDLElBQUksS0FBSyxTQUFTLENBQUM7Z0JBQ2pFLENBQUMsQ0FBQyxTQUFTLENBQUMsSUFBSSxLQUFLLFlBQVksQ0FBQztZQUNuQyxJQUFJLFdBQVcsRUFBRSxDQUFDO2dCQUNqQixTQUFTLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQztvQkFDdEIsSUFBSSxFQUFZLFlBQVk7b0JBQzVCLFVBQVUsRUFBTSxRQUFRO29CQUN4QixhQUFhLEVBQUcsWUFBWSxLQUFLLFNBQVM7aUJBQzFDLENBQUMsQ0FBQztZQUNKLENBQUM7UUFDRixDQUFDO0lBQ0YsQ0FBQztJQUVPLDRCQUE0QixDQUFFLElBQWE7UUFDbEQsSUFBSSxDQUFDLEVBQUUsQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7WUFDdkUsT0FBTztRQUNSLENBQUM7UUFDRCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUM7UUFDaEQsS0FBSyxNQUFNLFNBQVMsSUFBSSxJQUFJLENBQUMsaUJBQWlCLEVBQUUsQ0FBQztZQUNoRCxNQUFNLGdCQUFnQixHQUFHLFFBQVEsQ0FBQyxPQUFPLENBQUMsU0FBUyxDQUFDLFVBQVUsQ0FBQyxLQUFLLFFBQVEsQ0FBQyxPQUFPLENBQUMsUUFBUSxDQUFDO21CQUMxRixTQUFTLENBQUMsSUFBSSxLQUFLLElBQUksQ0FBQyxVQUFVLENBQUMsSUFBSTttQkFDdkMsQ0FBQyxTQUFTLENBQUMsUUFBUSxDQUFDO1lBQ3hCLElBQUksZ0JBQWdCLEVBQUUsQ0FBQztnQkFDdEIsU0FBUyxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsRUFBRSxJQUFJLEVBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLEVBQUUsVUFBVSxFQUFHLFFBQVEsRUFBRSxhQUFhLEVBQUcsSUFBSSxFQUFFLENBQUMsQ0FBQztZQUN0RyxDQUFDO1FBQ0YsQ0FBQztJQUNGLENBQUM7SUFFRDs7OztVQUlHO0lBQ0ssdUJBQXVCLENBQzlCLElBQXVCLEVBQ3ZCLFVBQWdDLEVBQ2hDLFFBQWdCLEVBQ2hCLFVBQXlCO1FBRXpCLHNFQUFzRTtRQUN0RSwrQ0FBK0M7UUFDL0MsSUFBSSxPQUFPLEdBQXdCLElBQUksQ0FBQyxNQUFNLENBQUM7UUFDL0MsT0FBTyxPQUFPLEVBQUUsQ0FBQztZQUNoQixJQUFJLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO2dCQUN2QywrQkFBK0I7Z0JBQy9CLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztvQkFDbkMsTUFBTSxPQUFPLEdBQUcsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7b0JBQ2xDLHdEQUF3RDtvQkFDeEQsNkNBQTZDO29CQUM3Qyx5REFBeUQ7b0JBQ3pELHNEQUFzRDtvQkFDdEQsc0RBQXNEO29CQUN0RCxJQUFJLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO3dCQUNsQyxPQUFPO29CQUNSLENBQUM7b0JBQ0QsK0RBQStEO29CQUMvRCx5REFBeUQ7b0JBQ3pELDhCQUE4QjtvQkFDOUIsSUFBSSxVQUFVLElBQUksSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO3dCQUN2RCxPQUFPO29CQUNSLENBQUM7b0JBQ0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsUUFBUSxDQUFDLENBQUM7b0JBQy9DLElBQUksUUFBUSxFQUFFLFlBQVksS0FBSyxTQUFTLEVBQUUsQ0FBQzt3QkFDMUMsTUFBTSxhQUFhLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLElBQUksQ0FBQyw0QkFBNEIsQ0FBQyxJQUFJLENBQUMsQ0FBQzs0QkFDN0YsSUFBSSxDQUFDLHFCQUFxQixDQUFDLElBQUksQ0FBQyw0QkFBNEIsQ0FBQyxJQUFJLENBQUMsRUFBRSxRQUFRLENBQUMsQ0FBQzt3QkFDOUUsTUFBTSxRQUFRLEdBQUcsYUFBYSxJQUFJLENBQ2pDLFVBQVUsS0FBSyxTQUFTLElBQUksSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsUUFBUSxDQUFDLENBQzNFLENBQUM7d0JBQ0YsSUFBSSxRQUFRLEVBQUUsQ0FBQzs0QkFDZCxJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxDQUFDO3dCQUN0QyxDQUFDO3dCQUNELE1BQU0sSUFBSSxHQUFHLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxRQUFRLENBQUMsQ0FBQyxDQUFDLFlBQVksQ0FBQzt3QkFDeEUsSUFBSSxDQUFDLHNCQUFzQixDQUFDLE9BQU8sRUFBRSxRQUFRLEVBQUUsSUFBSSxFQUFFLFVBQVUsRUFBRSxPQUFPLEVBQUUsUUFBUSxDQUFDLENBQUM7b0JBQ3JGLENBQUM7b0JBQ0QsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxPQUFPLEVBQUUsUUFBUSxDQUFDLENBQUM7b0JBQzlDLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxPQUFPLEVBQUUsUUFBUSxDQUFDLENBQUM7Z0JBQy9DLENBQUM7Z0JBQ0QsT0FBTztZQUNSLENBQUM7WUFDRCxPQUFPLEdBQUcsT0FBTyxDQUFDLE1BQU0sQ0FBQztRQUMxQixDQUFDO0lBQ0YsQ0FBQztJQUVEOzs7OztPQUtHO0lBQ0ssaUJBQWlCLENBQUUsSUFBdUI7UUFDakQsTUFBTSxFQUFFLE1BQU0sRUFBRSxHQUFHLElBQUksQ0FBQztRQUN4QixNQUFNLE1BQU0sR0FBRyxDQUFDLENBQUMsTUFBTTtZQUN0QixFQUFFLENBQUMsMEJBQTBCLENBQUMsTUFBTSxDQUFDO1lBQ3JDLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLFFBQVE7WUFDN0IsRUFBRSxDQUFDLGdCQUFnQixDQUFDLE1BQU0sQ0FBQyxNQUFNLENBQUM7WUFDbEMsTUFBTSxDQUFDLE1BQU0sQ0FBQyxVQUFVLEtBQUssTUFBTSxDQUFDO1FBQ3JDLE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7O09BSUc7SUFDSyxxQkFBcUIsQ0FBRSxPQUFlLEVBQUUsUUFBZ0I7UUFDL0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDO1FBQ2hELElBQUksUUFBUSxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLENBQUM7UUFDcEQsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQ2YsUUFBUSxHQUFHLElBQUksR0FBRyxFQUFrQixDQUFDO1lBQ3JDLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxFQUFFLFFBQVEsQ0FBQyxDQUFDO1FBQ2hELENBQUM7UUFDRCxRQUFRLENBQUMsR0FBRyxDQUFDLE9BQU8sRUFBRSxRQUFRLENBQUMsQ0FBQztJQUNqQyxDQUFDO0lBRUQ7OztVQUdHO0lBQ0sscUJBQXFCLENBQUUsSUFBdUIsRUFBRSxRQUFnQjtRQUN2RSxJQUFJLENBQUMsa0JBQWtCLENBQUMsSUFBSSxFQUFFLFFBQVEsQ0FBQyxDQUFDO0lBQ3pDLENBQUM7SUFFRDs7O1VBR0c7SUFDSyxrQkFBa0IsQ0FBRSxPQUF5QixFQUFFLFFBQWdCO1FBQ3RFLElBQUksYUFBYSxHQUFHLFFBQVEsQ0FBQztRQUM3QixJQUFJLE9BQU8sR0FBd0IsT0FBTyxDQUFDLE1BQU0sQ0FBQztRQUNsRCxpRUFBaUU7UUFDakUsa0VBQWtFO1FBQ2xFLHFFQUFxRTtRQUNyRSxPQUFPLE9BQU8sRUFBRSxDQUFDO1lBQ2hCLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLE9BQU8sQ0FBQztnQkFDekMsRUFBRSxDQUFDLGdCQUFnQixDQUFDLE9BQU8sQ0FBQyxNQUFNLENBQUM7Z0JBQ25DLE9BQU8sQ0FBQyxNQUFNLENBQUMsVUFBVSxLQUFLLE9BQU8sRUFBRSxDQUFDO2dCQUN4QyxNQUFNLEdBQUcsR0FBRyxJQUFJLENBQUMsdUJBQXVCLENBQUMsT0FBTyxDQUFDLE1BQU0sQ0FBQyxDQUFDO2dCQUN6RCxJQUFJLEdBQUcsRUFBRSxDQUFDO29CQUNULGFBQWEsR0FBRyxHQUFHLENBQUM7Z0JBQ3JCLENBQUM7Z0JBQ0QsT0FBTyxHQUFHLE9BQU8sQ0FBQyxNQUFNLENBQUMsTUFBTSxDQUFDO2dCQUNoQyxTQUFTO1lBQ1YsQ0FBQztZQUNELE1BQU07UUFDUCxDQUFDO1FBQ0QsSUFBSSxDQUFDLGtCQUFrQixDQUFDLE9BQU8sRUFBRSxhQUFhLENBQUMsQ0FBQztJQUNqRCxDQUFDO0lBRUQ7Ozs7O09BS0c7SUFDSyxrQkFBa0IsQ0FBRSxJQUFhLEVBQUUsUUFBZ0I7UUFDMUQsSUFBSSxPQUFPLEdBQXdCLElBQUksQ0FBQyxNQUFNLENBQUM7UUFDL0MsT0FBTyxPQUFPLEVBQUUsQ0FBQztZQUNoQixJQUFJLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO2dCQUN2QyxrQ0FBa0M7Z0JBQ2xDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztvQkFDbkMsTUFBTSxPQUFPLEdBQUcsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7b0JBQ2xDLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUMsT0FBTyxFQUFFLFFBQVEsQ0FBQyxDQUFDO29CQUM5QyxJQUFJLENBQUMscUJBQXFCLENBQUMsT0FBTyxFQUFFLFFBQVEsQ0FBQyxDQUFDO2dCQUMvQyxDQUFDO2dCQUNELE9BQU87WUFDUixDQUFDO1lBQ0QsZ0VBQWdFO1lBQ2hFLDBDQUEwQztZQUMxQyw2REFBNkQ7WUFDN0QsbUVBQW1FO1lBQ25FLG1FQUFtRTtZQUNuRSxpRUFBaUU7WUFDakUsMkRBQTJEO1lBQzNELGtDQUFrQztZQUNsQyxJQUFJLEVBQUUsQ0FBQyxXQUFXLENBQUMsT0FBTyxDQUFDLElBQUksRUFBRSxDQUFDLGNBQWMsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO2dCQUMzRCxPQUFPO1lBQ1IsQ0FBQztZQUNELE9BQU8sR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDO1FBQzFCLENBQUM7SUFDRixDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNLLHVCQUF1QixDQUM5QixJQUF1QixFQUN2QixRQUFnQixFQUNoQixVQUF5QixFQUN6QixlQUF3QjtRQUV4QixNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7UUFDRixNQUFNLFFBQVEsR0FBRyxlQUFlLElBQUksSUFBSSxDQUFDLFVBQVUsQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDeEUsSUFBSSxDQUFDLFFBQVEsQ0FBQyxRQUFRLEVBQUU7WUFDdkIsUUFBUSxFQUFVLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUU7WUFDdkUsSUFBSSxFQUFjLGVBQWU7WUFDakMsSUFBSSxFQUFjLElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsRUFBRSxHQUFHLENBQUM7WUFDeEQsZUFBZSxFQUFHLFFBQVEsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQztTQUN4QyxDQUFDLENBQUM7SUFDSixDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNLLHVCQUF1QixDQUFFLElBQXVCO1FBQ3ZELElBQUksQ0FBQyxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7WUFDckQsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUM7UUFDakMsSUFBSSxRQUE0QixDQUFDO1FBQ2pDLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztZQUM3QyxNQUFNLEtBQUssR0FBRyxRQUFRLENBQUMsVUFBVSxDQUFDO1lBQ2xDLFFBQVEsR0FBRyxFQUFFLENBQUMsMEJBQTBCLENBQUMsS0FBSyxDQUFDLFVBQVUsQ0FBQztnQkFDekQsQ0FBQyxDQUFDLElBQUksQ0FBQyxlQUFlLENBQUMsS0FBSyxDQUFDLFVBQVUsQ0FBQztnQkFDeEMsQ0FBQyxDQUFDLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxLQUFLLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDckQsQ0FBQzthQUFNLElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQ3JELFFBQVEsR0FBRyxJQUFJLENBQUMsdUJBQXVCLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQzlELENBQUM7YUFBTSxDQUFDO1lBQ1AsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELElBQUksQ0FBQyxRQUFRLEVBQUUsQ0FBQztZQUNmLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLFNBQVMsR0FBRyxHQUFHLFFBQVEsSUFBSSxRQUFRLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO1FBQ3RELElBQUksSUFBSSxDQUFDLFdBQVcsQ0FBQyxHQUFHLENBQUMsU0FBUyxDQUFDLEVBQUUsQ0FBQztZQUNyQyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBQ0QsSUFBSSxDQUFDLElBQUksQ0FBQyxXQUFXLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDckMsT0FBTyxJQUFJLENBQUMsZUFBZSxDQUFDLFFBQVEsQ0FBQyxDQUFDO1FBQ3ZDLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7Ozs7OztPQU1HO0lBQ0sseUJBQXlCLENBQUUsSUFBbUIsRUFBRSxFQUE2QjtRQUNwRixJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUMzQixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMscUJBQXFCLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDaEcsTUFBTSxPQUFPLEdBQUcsUUFBUSxLQUFLLEVBQUUsQ0FBQztZQUNoQyxPQUFPLE9BQU8sQ0FBQztRQUNoQixDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssRUFBRSxFQUFFLENBQUM7WUFDbEUsTUFBTSxPQUFPLEdBQUcsRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDO2dCQUMvQyxJQUFJLENBQUMscUJBQXFCLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDdEQsT0FBTyxPQUFPLENBQUM7UUFDaEIsQ0FBQztRQUNELE9BQU8sS0FBSyxDQUFDO0lBQ2QsQ0FBQztJQUVEOzs7OztPQUtHO0lBQ0ssNkJBQTZCLENBQUUsSUFBdUI7UUFDN0QsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQztRQUMvQixNQUFNLGFBQWEsR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUMsTUFBTSxFQUFFLE1BQU0sQ0FBQztZQUNuRSxJQUFJLENBQUMseUJBQXlCLENBQUMsTUFBTSxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQ2pELE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxNQUFNLEVBQUUsTUFBTSxDQUFDLENBQUM7UUFDOUQsSUFBSSxDQUFDLGFBQWEsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDO1lBQy9CLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxJQUFJLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxHQUFHLENBQUMsRUFBRSxDQUFDO1lBQy9CLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLENBQUUsQUFBRCxFQUFHLE9BQU8sQ0FBRSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUM7UUFDckMsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLHNCQUFzQixDQUFDLE9BQU8sQ0FBQyxDQUFDO1FBQ25ELE9BQU8sS0FBSyxDQUFDO0lBQ2QsQ0FBQztJQUVEOzs7OztPQUtHO0lBQ0ssc0JBQXNCLENBQUUsT0FBc0I7UUFDckQsSUFBSSxRQUE0QixDQUFDO1FBQ2pDLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7WUFDNUMsUUFBUSxHQUFHLElBQUksQ0FBQyxlQUFlLENBQUMsT0FBTyxDQUFDLENBQUM7UUFDMUMsQ0FBQzthQUFNLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO1lBQ3JDLE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ3ZELElBQUksS0FBSyxFQUFFLENBQUM7Z0JBQ1gsUUFBUSxHQUFHLEtBQUssQ0FBQztZQUNsQixDQUFDO2lCQUFNLENBQUM7Z0JBQ1AsTUFBTSxXQUFXLEdBQUcsSUFBSSxDQUFDLG9CQUFvQixDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDNUQsSUFBSSxXQUFXLENBQUMsTUFBTSxLQUFLLFFBQVEsRUFBRSxDQUFDO29CQUNyQyxRQUFRLEdBQUcsV0FBVyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUM7Z0JBQ3RDLENBQUM7WUFDRixDQUFDO1FBQ0YsQ0FBQztRQUNELE1BQU0sS0FBSyxHQUFHLFFBQVEsSUFBSSxJQUFJLENBQUMsV0FBVyxDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsQ0FBQyxDQUFDLENBQUMsUUFBUSxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUM7UUFDaEYsT0FBTyxLQUFLLENBQUM7SUFDZCxDQUFDO0lBRUQ7OztPQUdHO0lBQ0ssdUJBQXVCLENBQUUsSUFBdUI7UUFDdkQsSUFBSSxDQUFDLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztZQUNyRCxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1FBQ3pDLElBQUksTUFBTSxLQUFLLE1BQU0sSUFBSSxNQUFNLEtBQUssT0FBTyxFQUFFLENBQUM7WUFDN0MsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUMsVUFBVSxDQUFDO1FBQzVDLElBQUksQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDaEMsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ3pELE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7Ozs7T0FNRztJQUNLLHNCQUFzQixDQUFFLElBQXVCO1FBQ3RELE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUM7UUFDL0IsTUFBTSxZQUFZLEdBQUcsQ0FBQyxLQUFvQixFQUFXLEVBQUU7WUFDdEQsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLEtBQUssQ0FBQyxFQUFFLENBQUM7Z0JBQzVCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEVBQUUsR0FBRyxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDakcsT0FBTyxRQUFRLEtBQUssT0FBTyxDQUFDO1lBQzdCLENBQUM7WUFDRCxNQUFNLE9BQU8sR0FBRyxFQUFFLENBQUMsMEJBQTBCLENBQUMsS0FBSyxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssT0FBTztnQkFDbEYsRUFBRSxDQUFDLFlBQVksQ0FBQyxLQUFLLENBQUMsVUFBVSxDQUFDLElBQUksSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxLQUFLLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxDQUFDO1lBQzVGLE9BQU8sT0FBTyxDQUFDO1FBQ2hCLENBQUMsQ0FBQztRQUNGLElBQUksVUFBcUMsQ0FBQztRQUMxQyxJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxNQUFNLENBQUMsSUFBSSxZQUFZLENBQUMsTUFBTSxDQUFDLFVBQVUsQ0FBQztZQUMzRSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLE9BQU8sSUFBSSxNQUFNLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxNQUFNLENBQUMsRUFBRSxDQUFDO1lBQ2hFLE1BQU0sQ0FBRSxRQUFRLENBQUUsR0FBRyxJQUFJLENBQUMsU0FBUyxDQUFDO1lBQ3BDLFVBQVUsR0FBRyxRQUFRLENBQUM7UUFDdkIsQ0FBQzthQUFNLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxNQUFNLENBQUMsRUFBRSxDQUFDO1lBQ3BDLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEVBQUUsR0FBRyxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUNsRyxJQUFJLFFBQVEsS0FBSyxPQUFPLElBQUksUUFBUSxLQUFLLE1BQU0sRUFBRSxDQUFDO2dCQUNqRCxNQUFNLENBQUUsUUFBUSxDQUFFLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQztnQkFDcEMsVUFBVSxHQUFHLFFBQVEsQ0FBQztZQUN2QixDQUFDO1FBQ0YsQ0FBQzthQUFNLElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxNQUFNLENBQUMsVUFBVSxDQUFDO1lBQ3pGLE1BQU0sQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxNQUFNLElBQUksWUFBWSxDQUFDLE1BQU0sQ0FBQyxVQUFVLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztZQUN2RixtREFBbUQ7WUFDbkQsTUFBTSxDQUFFLFFBQVEsQ0FBRSxHQUFHLE1BQU0sQ0FBQyxTQUFTLENBQUM7WUFDdEMsVUFBVSxHQUFHLFFBQVEsQ0FBQztRQUN2QixDQUFDO1FBQ0QsSUFBSSxDQUFDLFVBQVUsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztZQUNqRCxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDM0QsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBR0Q7O09BRUc7SUFDSyx3QkFBd0IsQ0FDL0IsU0FBdUIsRUFDdkIsVUFBeUIsRUFDekIsY0FBb0M7UUFFcEMsTUFBTSxFQUFFLElBQUksRUFBRSxTQUFTLEVBQUUsR0FBRyxFQUFFLENBQUMsNkJBQTZCLENBQzNELFVBQVUsRUFDVixTQUFTLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxDQUM5QixDQUFDO1FBRUYsMEVBQTBFO1FBQzFFLE1BQU0sU0FBUyxHQUFHLFNBQVMsQ0FBQyxNQUF5QyxJQUFJLGNBQWMsQ0FBQztRQUN4RixJQUFJLENBQUMsU0FBUyxJQUFJLENBQUMsU0FBUyxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ25DLElBQUksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDO2dCQUNoQixPQUFPLEVBQUcsNkJBQTZCO2dCQUN2QyxJQUFJLEVBQU0sVUFBVSxDQUFDLFFBQVE7Z0JBQzdCLElBQUksRUFBTSxJQUFJLEdBQUcsQ0FBQztnQkFDbEIsTUFBTSxFQUFJLFNBQVMsR0FBRyxDQUFDO2FBQ3ZCLENBQUMsQ0FBQztZQUNILE9BQU87UUFDUixDQUFDO1FBRUQsTUFBTSxRQUFRLEdBQUcsU0FBUyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7UUFDckMsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQ2YsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUM7Z0JBQ2hCLE9BQU8sRUFBRyw2QkFBNkI7Z0JBQ3ZDLElBQUksRUFBTSxVQUFVLENBQUMsUUFBUTtnQkFDN0IsSUFBSSxFQUFNLElBQUksR0FBRyxDQUFDO2dCQUNsQixNQUFNLEVBQUksU0FBUyxHQUFHLENBQUM7YUFDdkIsQ0FBQyxDQUFDO1lBQ0gsT0FBTztRQUNSLENBQUM7UUFFRCw2REFBNkQ7UUFDN0Qsa0RBQWtEO1FBQ2xELDREQUE0RDtRQUM1RCxJQUFJLFVBQWdDLENBQUM7UUFDckMsSUFBSSxjQUFjLEdBQWtCLElBQUksQ0FBQztRQUN6QyxJQUFJLFlBQWdDLENBQUM7UUFDckMsSUFBSSxlQUFlLEdBQXFELEVBQUUsQ0FBQztRQUUzRSxJQUFJLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxTQUFTLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztZQUMvQyxNQUFNLFFBQVEsR0FBRyxTQUFTLENBQUMsVUFBVSxDQUFDO1lBQ3RDLE1BQU0sTUFBTSxHQUFHLFFBQVEsQ0FBQyxVQUFVLENBQUM7WUFFbkMsZ0ZBQWdGO1lBQ2hGLDhEQUE4RDtZQUM5RCxJQUNDLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxNQUFNLENBQUM7Z0JBQ3JDLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLFVBQVU7Z0JBQy9CLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLFVBQVUsQ0FBQztnQkFDbEMsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxNQUFNLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxFQUNuRCxDQUFDO2dCQUNGLFlBQVksR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsR0FBRyxDQUFDLE1BQU0sQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLENBQUM7Z0JBQ3BFLElBQUksUUFBUSxDQUFDLFNBQVMsQ0FBQyxNQUFNLEtBQUssQ0FBQyxJQUFJLEVBQUUsQ0FBQyx5QkFBeUIsQ0FBQyxRQUFRLENBQUMsU0FBUyxDQUFFLENBQUMsQ0FBRSxDQUFDLEVBQUUsQ0FBQztvQkFDOUYsZUFBZSxHQUFHLElBQUksQ0FBQyw4QkFBOEIsQ0FBQyxRQUFRLENBQUMsU0FBUyxDQUFFLENBQUMsQ0FBRSxDQUFDLENBQUM7Z0JBQ2hGLENBQUM7WUFDRixDQUFDO2lCQUFNLENBQUM7Z0JBQ1AsTUFBTSxJQUFJLEdBQUcsUUFBUSxDQUFDLFNBQVMsQ0FBQztnQkFDaEMsSUFBSSxTQUFvQyxDQUFDO2dCQUN6QyxJQUFJLFNBQWlELENBQUM7Z0JBRXRELEtBQUssTUFBTSxHQUFHLElBQUksSUFBSSxFQUFFLENBQUM7b0JBQ3hCLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO3dCQUMxQixJQUFJLFNBQVMsRUFBRSxDQUFDOzRCQUNmLElBQUksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDO2dDQUNoQixPQUFPLEVBQUcsK0NBQStDO2dDQUN6RCxJQUFJLEVBQU0sVUFBVSxDQUFDLFFBQVE7Z0NBQzdCLElBQUksRUFBTSxJQUFJLEdBQUcsQ0FBQztnQ0FDbEIsTUFBTSxFQUFJLFNBQVMsR0FBRyxDQUFDOzZCQUN2QixDQUFDLENBQUM7d0JBQ0osQ0FBQzs2QkFBTSxDQUFDOzRCQUNQLFNBQVMsR0FBRyxHQUFHLENBQUM7d0JBQ2pCLENBQUM7b0JBQ0YsQ0FBQzt5QkFBTSxJQUFJLEVBQUUsQ0FBQyx5QkFBeUIsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO3dCQUM5QyxJQUFJLFNBQVMsRUFBRSxDQUFDOzRCQUNmLElBQUksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDO2dDQUNoQixPQUFPLEVBQUcsNENBQTRDO2dDQUN0RCxJQUFJLEVBQU0sVUFBVSxDQUFDLFFBQVE7Z0NBQzdCLElBQUksRUFBTSxJQUFJLEdBQUcsQ0FBQztnQ0FDbEIsTUFBTSxFQUFJLFNBQVMsR0FBRyxDQUFDOzZCQUN2QixDQUFDLENBQUM7d0JBQ0osQ0FBQzs2QkFBTSxDQUFDOzRCQUNQLFNBQVMsR0FBRyxHQUFHLENBQUM7d0JBQ2pCLENBQUM7b0JBQ0YsQ0FBQztnQkFDRixDQUFDO2dCQUVELElBQUksU0FBUyxFQUFFLENBQUM7b0JBQ2YsVUFBVSxHQUFHLElBQUksQ0FBQywwQkFBMEIsQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLENBQUM7b0JBQzdELElBQUksVUFBVSxFQUFFLENBQUM7d0JBQ2hCLGNBQWMsR0FBRyxVQUFVLENBQUMsUUFBUSxDQUFDO29CQUN0QyxDQUFDO2dCQUNGLENBQUM7Z0JBRUQsSUFBSSxTQUFTLEVBQUUsQ0FBQztvQkFDZixlQUFlLEdBQUcsSUFBSSxDQUFDLDhCQUE4QixDQUFDLFNBQVMsQ0FBQyxDQUFDO2dCQUNsRSxDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFFRCw4REFBOEQ7UUFDOUQsbUVBQW1FO1FBQ25FLGdFQUFnRTtRQUNoRSxpRUFBaUU7UUFDakUsZ0JBQWdCO1FBQ2hCLE1BQU0sUUFBUSxHQUFHLFVBQVU7WUFDMUIsQ0FBQyxDQUFDLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxRQUFRLEVBQUU7WUFDdEMsQ0FBQyxDQUFDLFlBQVk7Z0JBQ2IsQ0FBQyxDQUFDLEdBQUcsWUFBWSxLQUFLLFFBQVEsRUFBRTtnQkFDaEMsQ0FBQyxDQUFDLFFBQVEsQ0FBQztRQUViLHNDQUFzQztRQUN0QyxNQUFNLFVBQVUsR0FBbUI7WUFDbEMsSUFBSSxFQUFVLFFBQVE7WUFDdEIsUUFBUSxFQUFNLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUU7WUFDbkUsSUFBSSxFQUFVLFVBQVU7WUFDeEIsTUFBTSxFQUFRLGNBQWM7WUFDNUIsV0FBVyxFQUFHLGVBQWUsQ0FBQyxXQUFXLElBQUksSUFBSTtZQUNqRCxXQUFXLEVBQUcsZUFBZSxDQUFDLFdBQVcsSUFBSSxLQUFLO1NBQ2xELENBQUM7UUFDRixJQUFJLENBQUMsV0FBVyxDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFDM0MsSUFBSSxDQUFDLGNBQWMsQ0FBQyxHQUFHLENBQUMsU0FBUyxFQUFFLFFBQVEsQ0FBQyxDQUFDO1FBRTdDLG1CQUFtQjtRQUNuQixNQUFNLElBQUksR0FBRyxxQkFBYSxDQUFDLFVBQVUsQ0FDcEMsUUFBUSxFQUNSLFVBQVUsRUFDVixVQUFVLENBQUMsUUFBUSxFQUNuQixJQUFJLEdBQUcsQ0FBQyxFQUNSLFNBQVMsR0FBRyxDQUFDLEVBQ2IsWUFBWSxDQUNaLENBQUM7UUFDRixJQUFJLENBQUMsMkJBQTJCLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxZQUFZLENBQUMsQ0FBQztRQUUxRCxxREFBcUQ7UUFDckQsSUFBSSxDQUFDLGdCQUFnQixDQUNwQixVQUFVLENBQUMsQ0FBQyxDQUFDLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxRQUFRLEVBQUUsQ0FBQyxDQUFDLENBQUMsR0FBRyxZQUFZLElBQUksU0FBUyxLQUFLLFFBQVEsRUFBRSxFQUMvRixHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQ3JELENBQUM7UUFFRixxRUFBcUU7UUFDckUsaUVBQWlFO1FBQ2pFLE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQyxrQkFBa0IsQ0FBQztRQUMvQyxJQUFJLENBQUMsa0JBQWtCLEdBQUcsSUFBSSxDQUFDO1FBQy9CLElBQUksQ0FBQztZQUNKLElBQUksQ0FBQyxVQUFVLEdBQUcsSUFBSSxDQUFDLHNCQUFzQixDQUFDLFNBQVMsQ0FBQyxDQUFDO1lBQ3pELElBQUksQ0FBQyxpQkFBaUIsR0FBRyxJQUFJLENBQUMsNkJBQTZCLENBQUMsU0FBUyxDQUFDLENBQUM7UUFDeEUsQ0FBQztnQkFBUyxDQUFDO1lBQ1YsSUFBSSxDQUFDLGtCQUFrQixHQUFHLGNBQWMsQ0FBQztRQUMxQyxDQUFDO1FBRUQsZUFBZTtRQUNmLElBQUksVUFBVSxFQUFFLENBQUM7WUFDaEIsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsVUFBVSxFQUFFLElBQUksQ0FBQyxDQUFDO1FBQ3ZDLENBQUM7YUFBTSxDQUFDO1lBQ1AsSUFBSSxDQUFDLEtBQUssQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDMUIsQ0FBQztJQUNGLENBQUM7SUFFRDs7Ozs7OztPQU9HO0lBQ0ssZUFBZSxDQUFFLElBQXVCO1FBQy9DLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUM7UUFFNUIsSUFBSSxJQUFJLENBQUMsTUFBTSxLQUFLLENBQUMsRUFBRSxDQUFDO1lBQ3ZCLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFFRCxNQUFNLENBQUUsUUFBUSxDQUFFLEdBQUcsSUFBSSxDQUFDO1FBRTFCLDREQUE0RDtRQUM1RCxJQUFJLElBQUksQ0FBQyxNQUFNLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsUUFBUSxDQUFDLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxJQUFJLENBQUUsQ0FBQyxDQUFFLENBQUMsRUFBRSxDQUFDO1lBQ3BGLE9BQU8sSUFBSSxDQUFFLENBQUMsQ0FBRSxDQUFDLElBQUksQ0FBQztRQUN2QixDQUFDO1FBRUQsMENBQTBDO1FBQzFDLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO1lBQ2xDLE9BQU8sUUFBUSxDQUFDLElBQUksQ0FBQztRQUN0QixDQUFDO1FBRUQscURBQXFEO1FBQ3JELElBQUksRUFBRSxDQUFDLG9CQUFvQixDQUFDLFFBQVEsQ0FBQyxJQUFJLFFBQVEsQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUN4RCxPQUFPLFFBQVEsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1FBQzNCLENBQUM7UUFFRCxrRUFBa0U7UUFDbEUsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDbEMsTUFBTSxFQUFFLElBQUksRUFBRSxHQUFHLFFBQVEsQ0FBQztZQUMxQixJQUFJLEVBQUUsQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7Z0JBQzdDLE9BQU8sSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7WUFDdkIsQ0FBQztRQUNGLENBQUM7UUFFRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7Ozs7T0FJRztJQUNLLHdCQUF3QixDQUFFLElBQXVCO1FBQ3hELE1BQU0sQ0FBRSxRQUFRLENBQUUsR0FBRyxJQUFJLENBQUMsU0FBUyxDQUFDO1FBQ3BDLElBQUksQ0FBQyxRQUFRLElBQUksQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDN0MsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELE1BQU0sU0FBUyxHQUFHLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxRQUFRLENBQUMsQ0FBQztRQUNyRCxJQUFJLFNBQVMsS0FBSyxTQUFTLEVBQUUsQ0FBQztZQUM3QixPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBQ0QsTUFBTSxjQUFjLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLFFBQVEsRUFBRSxJQUFJLENBQUMsYUFBYSxFQUFFLENBQUMsQ0FBQztRQUNyRixPQUFPLGNBQWMsQ0FBQztJQUN2QixDQUFDO0lBRU8sbUJBQW1CLENBQUUsSUFBbUI7UUFDL0MsSUFBSSxPQUFPLEdBQXdCLElBQUksQ0FBQyxNQUFNLENBQUM7UUFDL0MsT0FBTyxPQUFPLEVBQUUsQ0FBQztZQUNoQixJQUFJLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxPQUFPLENBQUMsSUFBSSxFQUFFLENBQUMseUJBQXlCLENBQUMsT0FBTyxDQUFDLFdBQVcsQ0FBQyxFQUFFLENBQUM7Z0JBQ3ZGLE1BQU0sV0FBVyxHQUFHLE9BQU8sQ0FBQyxXQUFXLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUNyRSxFQUFFLENBQUMsWUFBWSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsSUFBSSxTQUFTLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7Z0JBQ3ZFLElBQUksV0FBVyxFQUFFLENBQUM7b0JBQ2pCLE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxPQUFPLENBQUMsVUFBVSxFQUFFLE9BQU8sQ0FBQyxhQUFhLEVBQUUsQ0FBQyxDQUFDO29CQUN2RixPQUFPLE1BQU0sQ0FBQztnQkFDZixDQUFDO1lBQ0YsQ0FBQztZQUNELE9BQU8sR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDO1FBQzFCLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRU8scUJBQXFCLENBQUUsVUFBeUIsRUFBRSxVQUF5QjtRQUNsRixJQUFJLENBQUMsRUFBRSxDQUFDLGdCQUFnQixDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLDBCQUEwQixDQUFDLFVBQVUsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQy9GLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLE1BQU0sR0FBRyxVQUFVLENBQUMsVUFBVSxDQUFDO1FBQ3JDLE1BQU0sQ0FBRSxRQUFRLENBQUUsR0FBRyxVQUFVLENBQUMsU0FBUyxDQUFDO1FBQzFDLElBQUksQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLE1BQU0sQ0FBQyxVQUFVLENBQUMsSUFBSSxNQUFNLENBQUMsVUFBVSxDQUFDLElBQUksS0FBSyxRQUFRO1lBQzdFLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLE1BQU0sSUFBSSxDQUFDLFFBQVEsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUN6RSxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLHNCQUFzQixDQUFDLFFBQVEsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFDdEUsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRU8sd0JBQXdCLENBQUUsSUFBbUIsRUFBRSxVQUF5QjtRQUMvRSxJQUFJLE9BQU8sR0FBd0IsSUFBSSxDQUFDLE1BQU0sQ0FBQztRQUMvQyxPQUFPLE9BQU8sRUFBRSxDQUFDO1lBQ2hCLElBQUksRUFBRSxDQUFDLGNBQWMsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO2dCQUNoQyxNQUFNLFNBQVMsR0FBRyxPQUFPLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUNyRCxFQUFFLENBQUMsWUFBWSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsSUFBSSxTQUFTLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7Z0JBQ3ZFLElBQUksU0FBUyxFQUFFLENBQUM7b0JBQ2YsSUFBSSxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsQ0FBQzt3QkFDckIsT0FBTyxTQUFTLENBQUM7b0JBQ2xCLENBQUM7b0JBQ0QsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLGdCQUFnQixDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7b0JBQ2pFLE9BQU8sTUFBTSxDQUFDO2dCQUNmLENBQUM7WUFDRixDQUFDO1lBQ0QsT0FBTyxHQUFHLE9BQU8sQ0FBQyxNQUFNLENBQUM7UUFDMUIsQ0FBQztRQUNELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFTyxnQkFBZ0IsQ0FBRSxRQUFxQixFQUFFLFVBQXlCO1FBQ3pFLElBQUksRUFBRSxDQUFDLHVCQUF1QixDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDMUMsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLGdCQUFnQixDQUFDLFFBQVEsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7WUFDaEUsT0FBTyxNQUFNLENBQUM7UUFDZixDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsa0JBQWtCLENBQUMsUUFBUSxDQUFDLElBQUksUUFBUSxDQUFDLFFBQVEsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFlBQVksRUFBRSxDQUFDO1lBQ3pGLE1BQU0sT0FBTyxHQUFHLFFBQVEsQ0FBQyxJQUFJLENBQUM7WUFDOUIsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsT0FBTyxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7Z0JBQ3RFLE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxzQkFBc0IsQ0FBQyxPQUFPLENBQUMsUUFBUSxDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsQ0FBQztnQkFDOUUsT0FBTyxNQUFNLENBQUM7WUFDZixDQUFDO1lBQ0QsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELElBQUksRUFBRSxDQUFDLG1CQUFtQixDQUFDLFFBQVEsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsUUFBUSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDNUUsTUFBTSxjQUFjLEdBQUcsUUFBUSxDQUFDLFFBQVEsQ0FBQyxJQUFJLENBQUM7WUFDOUMsTUFBTSxLQUFLLEdBQUcsVUFBVSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsQ0FBQyxTQUFTLEVBQXdDLEVBQUUsQ0FDNUYsRUFBRSxDQUFDLHNCQUFzQixDQUFDLFNBQVMsQ0FBQyxJQUFJLFNBQVMsQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLGNBQWMsQ0FBQyxDQUFDO1lBQ2pGLElBQUksS0FBSyxFQUFFLENBQUM7Z0JBQ1gsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLGdCQUFnQixDQUFDLEtBQUssQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7Z0JBQzdELE9BQU8sTUFBTSxDQUFDO1lBQ2YsQ0FBQztRQUNGLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRU8sc0JBQXNCLENBQUUsSUFBWSxFQUFFLFVBQXlCO1FBQ3RFLEtBQUssTUFBTSxTQUFTLElBQUksVUFBVSxDQUFDLFVBQVUsRUFBRSxDQUFDO1lBQy9DLElBQUksQ0FBQyxFQUFFLENBQUMsbUJBQW1CLENBQUMsU0FBUyxDQUFDO2dCQUNyQyxDQUFDLFNBQVMsQ0FBQyxlQUFlLENBQUMsS0FBSyxHQUFHLEVBQUUsQ0FBQyxTQUFTLENBQUMsS0FBSyxDQUFDLEtBQUssQ0FBQyxFQUFFLENBQUM7Z0JBQy9ELFNBQVM7WUFDVixDQUFDO1lBQ0QsS0FBSyxNQUFNLFdBQVcsSUFBSSxTQUFTLENBQUMsZUFBZSxDQUFDLFlBQVksRUFBRSxDQUFDO2dCQUNsRSxJQUFJLENBQUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxXQUFXLENBQUMsSUFBSSxDQUFDLElBQUksV0FBVyxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssSUFBSTtvQkFDdkUsQ0FBQyxXQUFXLENBQUMsV0FBVyxJQUFJLENBQUMsRUFBRSxDQUFDLHlCQUF5QixDQUFDLFdBQVcsQ0FBQyxXQUFXLENBQUMsRUFBRSxDQUFDO29CQUNyRixTQUFTO2dCQUNWLENBQUM7Z0JBQ0QsTUFBTSxLQUFLLEdBQWEsRUFBRSxDQUFDO2dCQUMzQixLQUFLLE1BQU0sUUFBUSxJQUFJLFdBQVcsQ0FBQyxXQUFXLENBQUMsVUFBVSxFQUFFLENBQUM7b0JBQzNELElBQUksQ0FBQyxFQUFFLENBQUMsb0JBQW9CLENBQUMsUUFBUSxDQUFDO3dCQUNyQyxDQUFDLENBQUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxRQUFRLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsZUFBZSxDQUFDLFFBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQyxFQUFFLENBQUM7d0JBQzFFLE9BQU8sU0FBUyxDQUFDO29CQUNsQixDQUFDO29CQUNELEtBQUssQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDaEMsQ0FBQztnQkFDRCxPQUFPLEtBQUssQ0FBQztZQUNkLENBQUM7UUFDRixDQUFDO1FBQ0QsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7O09BSUc7SUFDSyxvQkFBb0IsQ0FBRSxJQUF1QixFQUFFLGdCQUF5QjtRQUsvRSxNQUFNLFFBQVEsR0FBRyxnQkFBZ0IsSUFBSSxJQUFJLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ2hFLElBQUksQ0FBQyxRQUFRLEVBQUUsQ0FBQztZQUNmLE9BQU8sRUFBRSxDQUFDO1FBQ1gsQ0FBQztRQUVELE1BQU0sRUFBRSxVQUFVLEVBQUUsR0FBRyxJQUFJLENBQUM7UUFFNUIsOEVBQThFO1FBQzlFLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxVQUFVLENBQUMsSUFBSSxVQUFVLENBQUMsSUFBSSxLQUFLLFFBQVEsRUFBRSxDQUFDO1lBQ2pFLDREQUE0RDtZQUM1RCxJQUFJLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUUsQ0FBQyxDQUFFLENBQUMsRUFBRSxDQUFDO2dCQUN4RSxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsU0FBUyxDQUFFLENBQUMsQ0FBRSxDQUFDLElBQUksQ0FBQztnQkFDNUMsTUFBTSxhQUFhLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLFVBQVUsQ0FBQyxDQUFDO2dCQUMzRCxPQUFPO29CQUNOLFFBQVE7b0JBQ1IsVUFBVSxFQUFLLGFBQWEsQ0FBQyxVQUFVO29CQUN2QyxZQUFZLEVBQUcsYUFBYSxDQUFDLFlBQVk7aUJBQ3pDLENBQUM7WUFDSCxDQUFDO1lBRUQsMENBQTBDO1lBQzFDLE9BQU8sRUFBRSxRQUFRLEVBQUUsQ0FBQztRQUNyQixDQUFDO1FBRUQsNkNBQTZDO1FBQzdDLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLFVBQVUsQ0FBQyxJQUFJLFVBQVUsQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLFFBQVEsRUFBRSxDQUFDO1lBQ3BGLE1BQU0sR0FBRyxHQUFHLFVBQVUsQ0FBQyxVQUFVLENBQUM7WUFFbEMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQzFCLE1BQU0sYUFBYSxHQUFHLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7Z0JBQ3pELE9BQU87b0JBQ04sUUFBUTtvQkFDUixVQUFVLEVBQUssYUFBYSxDQUFDLFVBQVU7b0JBQ3ZDLFlBQVksRUFBRyxhQUFhLENBQUMsWUFBWTtpQkFDekMsQ0FBQztZQUNILENBQUM7WUFFRCxJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO2dCQUN4Qyx1REFBdUQ7Z0JBQ3ZELE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyxnQkFBZ0IsQ0FBQyxHQUFHLENBQUMsQ0FBQztnQkFDekMsSUFBSSxLQUFLLENBQUMsTUFBTSxHQUFHLENBQUMsRUFBRSxDQUFDO29CQUN0QixNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDLFFBQVEsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUM7b0JBQ3hELE9BQU8sRUFBRSxRQUFRLEVBQUUsVUFBVSxFQUFHLFVBQVUsRUFBRSxDQUFDO2dCQUM5QyxDQUFDO1lBQ0YsQ0FBQztZQUVELElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQzlCLHNFQUFzRTtnQkFDdEUsNkVBQTZFO2dCQUM3RSxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLFVBQVUsQ0FBQyxDQUFDO2dCQUN0RCxNQUFNLG9CQUFvQixHQUFHLE1BQU07b0JBQ2xDLENBQUMsQ0FBQyxJQUFJLENBQUMsbUJBQW1CLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxDQUFDLFlBQVk7b0JBQ3BELENBQUMsQ0FBQyxTQUFTLENBQUM7Z0JBRWIsNkVBQTZFO2dCQUM3RSxJQUFJLElBQUksQ0FBQyxZQUFZLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztvQkFDNUIsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsRUFBRSxJQUFJLENBQUMsYUFBYSxFQUFFLENBQUMsQ0FBQztvQkFDbEQsTUFBTSxjQUFjLEdBQUcsSUFBSSxDQUFDLGVBQWUsQ0FBQyxHQUFHLENBQUMsQ0FBQztvQkFDakQsSUFBSSxjQUFjLEVBQUUsQ0FBQzt3QkFDcEIsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLG9CQUFvQixDQUFDLGNBQWMsRUFBRSxvQkFBb0IsQ0FBQyxDQUFDO3dCQUNuRixtREFBbUQ7d0JBQ25ELE9BQU8sRUFBRSxRQUFRLEVBQUUsVUFBVSxFQUFHLFVBQVUsRUFBRSxZQUFZLEVBQUcsVUFBVSxFQUFFLFlBQVksRUFBRSxDQUFDO29CQUN2RixDQUFDO2dCQUNGLENBQUM7Z0JBRUQseUVBQXlFO2dCQUN6RSxJQUFJLElBQUksQ0FBQyxVQUFVLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztvQkFDMUIsSUFBSSxDQUFDLGVBQWUsQ0FBQyxHQUFHLEVBQUUsSUFBSSxDQUFDLGFBQWEsRUFBRSxDQUFDLENBQUM7b0JBQ2hELE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxHQUFHLENBQUMsQ0FBQztvQkFDMUQsSUFBSSxjQUFjLEVBQUUsQ0FBQzt3QkFDcEIsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLG9CQUFvQixDQUFDLGNBQWMsRUFBRSxvQkFBb0IsQ0FBQyxDQUFDO3dCQUNuRixPQUFPLEVBQUUsUUFBUSxFQUFFLFVBQVUsRUFBRyxVQUFVLEVBQUUsWUFBWSxFQUFHLFVBQVUsRUFBRSxZQUFZLEVBQUUsQ0FBQztvQkFDdkYsQ0FBQztnQkFDRixDQUFDO2dCQUVELDJEQUEyRDtnQkFDM0QsSUFBSSxJQUFJLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7b0JBQzVCLE1BQU0sWUFBWSxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUMsQ0FBQztvQkFDakQsSUFBSSxZQUFZLEVBQUUsQ0FBQzt3QkFDbEIsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsWUFBWSxDQUFDLENBQUM7d0JBQ3JELElBQUksVUFBVSxFQUFFLENBQUM7NEJBQ2hCLE9BQU8sRUFBRSxRQUFRLEVBQUUsVUFBVSxFQUFHLFVBQVUsRUFBRSxZQUFZLEVBQUcsVUFBVSxDQUFDLFlBQVksRUFBRSxDQUFDO3dCQUN0RixDQUFDO29CQUNGLENBQUM7Z0JBQ0YsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxFQUFFLFFBQVEsRUFBRSxDQUFDO0lBQ3JCLENBQUM7SUFFRDs7O09BR0c7SUFDSyxvQkFBb0IsQ0FBRSxJQUFZLEVBQUUsWUFBb0I7UUFDL0QsT0FBTyxHQUFHLFlBQVksS0FBSyxJQUFJLEVBQUUsQ0FBQztJQUNuQyxDQUFDO0lBRUQ7OztPQUdHO0lBQ0ssbUJBQW1CLENBQUUsVUFBa0I7UUFJOUMsc0RBQXNEO1FBQ3RELElBQUksSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQ2hELE9BQU8sRUFBRSxDQUFDO1FBQ1gsQ0FBQztRQUVELGtEQUFrRDtRQUNsRCxNQUFNLFlBQVksR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsR0FBRyxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQzlELElBQUksWUFBWSxFQUFFLENBQUM7WUFDbEIsT0FBTyxFQUFFLFlBQVksRUFBRSxDQUFDO1FBQ3pCLENBQUM7UUFFRCwrQ0FBK0M7UUFDL0MsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLDBCQUEwQixDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQy9ELE9BQU8sRUFBRSxVQUFVLEVBQUcsVUFBVSxFQUFFLFlBQVksRUFBRyxVQUFVLEVBQUUsWUFBWSxFQUFFLENBQUM7SUFDN0UsQ0FBQztJQUVEOztPQUVHO0lBQ0ssWUFBWSxDQUFFLElBQXVCO1FBQzVDLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUM7UUFDN0IsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxJQUFJLEtBQUssUUFBUSxFQUFFLENBQUM7WUFDckQsT0FBTyxJQUFJLENBQUM7UUFDYixDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssUUFBUSxFQUFFLENBQUM7WUFDeEUsT0FBTyxJQUFJLENBQUM7UUFDYixDQUFDO1FBQ0QsT0FBTyxLQUFLLENBQUM7SUFDZCxDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNLLGlCQUFpQixDQUFFLElBQXVCO1FBQ2pELE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUM7UUFDNUIsSUFBSSxJQUFJLENBQUMsTUFBTSxLQUFLLENBQUMsRUFBRSxDQUFDO1lBQ3ZCLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFFRCwwREFBMEQ7UUFDMUQsSUFBSSxJQUFJLENBQUMsTUFBTSxLQUFLLENBQUMsRUFBRSxDQUFDO1lBQ3ZCLE1BQU0sQ0FBRSxHQUFHLENBQUUsR0FBRyxJQUFJLENBQUM7WUFDckIsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsQ0FBQywrQkFBK0IsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO2dCQUN4RSxNQUFNLElBQUksR0FBRyxHQUFHLENBQUMsSUFBSSxDQUFDO2dCQUN0Qix5RUFBeUU7Z0JBQ3pFLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO29CQUNwRCxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsVUFBVSxDQUFDLFVBQVUsQ0FBQztvQkFDOUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7d0JBQ2pDLE1BQU0sVUFBVSxHQUFHLFVBQVUsQ0FBQyxJQUFJLENBQUM7d0JBQ25DLE1BQU0sYUFBYSxHQUFHLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxVQUFVLENBQUMsQ0FBQzt3QkFDM0QsSUFBSSxhQUFhLENBQUMsVUFBVSxFQUFFLENBQUM7NEJBQzlCLG1EQUFtRDs0QkFDbkQsNkRBQTZEOzRCQUM3RCxxREFBcUQ7NEJBQ3JELE1BQU0sWUFBWSxHQUFHLEdBQUcsYUFBYSxDQUFDLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxFQUFFLENBQUM7NEJBQ3BFLElBQUksSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsWUFBWSxDQUFDLEVBQUUsQ0FBQztnQ0FDdkMsT0FBTyxZQUFZLENBQUM7NEJBQ3JCLENBQUM7NEJBQ0QsSUFBSSxhQUFhLENBQUMsWUFBWSxFQUFFLENBQUM7Z0NBQ2hDLE9BQU8sSUFBSSxDQUFDLG9CQUFvQixDQUFDLElBQUksRUFBRSxhQUFhLENBQUMsWUFBWSxDQUFDLENBQUM7NEJBQ3BFLENBQUM7NEJBQ0QsT0FBTyxJQUFJLENBQUM7d0JBQ2IsQ0FBQzt3QkFDRCxJQUFJLGFBQWEsQ0FBQyxZQUFZLEVBQUUsQ0FBQzs0QkFDaEMsd0RBQXdEOzRCQUN4RCxPQUFPLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLEVBQUUsYUFBYSxDQUFDLFlBQVksQ0FBQyxDQUFDO3dCQUNwRSxDQUFDO29CQUNGLENBQUM7Z0JBQ0YsQ0FBQztnQkFDRCxPQUFPLElBQUksQ0FBQztZQUNiLENBQUM7WUFDRCxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQseUNBQXlDO1FBQ3pDLElBQUksSUFBSSxDQUFDLE1BQU0sSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUN0QixNQUFNLENBQUUsU0FBUyxFQUFFLE9BQU8sQ0FBRSxHQUFHLElBQUksQ0FBQztZQUNwQyxJQUFJLENBQUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxlQUFlLENBQUMsT0FBTyxDQUFDLEVBQUUsQ0FBQztnQkFDakUsT0FBTyxTQUFTLENBQUM7WUFDbEIsQ0FBQztZQUNELE1BQU0sVUFBVSxHQUFHLFNBQVMsQ0FBQyxJQUFJLENBQUM7WUFDbEMsTUFBTSxJQUFJLEdBQUcsT0FBTyxDQUFDLElBQUksQ0FBQztZQUMxQixNQUFNLGFBQWEsR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsVUFBVSxDQUFDLENBQUM7WUFDM0QsSUFBSSxhQUFhLENBQUMsVUFBVSxFQUFFLENBQUM7Z0JBQzlCLDZEQUE2RDtnQkFDN0Qsa0VBQWtFO2dCQUNsRSxNQUFNLFlBQVksR0FBRyxHQUFHLGFBQWEsQ0FBQyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksRUFBRSxDQUFDO2dCQUNwRSxJQUFJLElBQUksQ0FBQyxLQUFLLENBQUMsUUFBUSxDQUFDLFlBQVksQ0FBQyxFQUFFLENBQUM7b0JBQ3ZDLE9BQU8sWUFBWSxDQUFDO2dCQUNyQixDQUFDO2dCQUNELElBQUksYUFBYSxDQUFDLFlBQVksRUFBRSxDQUFDO29CQUNoQyxPQUFPLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLEVBQUUsYUFBYSxDQUFDLFlBQVksQ0FBQyxDQUFDO2dCQUNwRSxDQUFDO2dCQUNELE9BQU8sSUFBSSxDQUFDO1lBQ2IsQ0FBQztZQUNELElBQUksYUFBYSxDQUFDLFlBQVksRUFBRSxDQUFDO2dCQUNoQyxPQUFPLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLEVBQUUsYUFBYSxDQUFDLFlBQVksQ0FBQyxDQUFDO1lBQ3BFLENBQUM7WUFDRCxPQUFPLElBQUksQ0FBQztRQUNiLENBQUM7UUFFRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNILHFCQUFxQixDQUFFLElBQXVCO1FBQzdDLE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUM1QyxPQUFPLE1BQU0sQ0FBQztJQUNmLENBQUM7SUFFRDs7O1VBR0c7SUFDSyxvQkFBb0IsQ0FDM0IsSUFBWSxFQUNaLFlBQXFCO1FBRXJCLE1BQU0saUJBQWlCLEdBQUcsQ0FBQyxJQUFjLEVBQVcsRUFBRTtZQUNyRCxJQUFJLFlBQVksS0FBSyxTQUFTLEVBQUUsQ0FBQztnQkFDaEMsT0FBTyxJQUFJLENBQUMsWUFBWSxLQUFLLFNBQVMsQ0FBQztZQUN4QyxDQUFDO1lBQ0QsT0FBTyxJQUFJLENBQUMsWUFBWSxLQUFLLFlBQVksQ0FBQztRQUMzQyxDQUFDLENBQUM7UUFFRiw2RUFBNkU7UUFDN0UsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDeEMsSUFBSSxLQUFLLElBQUksaUJBQWlCLENBQUMsS0FBSyxDQUFDLEVBQUUsQ0FBQztZQUN2QyxPQUFPLEtBQUssQ0FBQztRQUNkLENBQUM7UUFFRCwwRUFBMEU7UUFDMUUsS0FBSyxNQUFNLElBQUksSUFBSSxJQUFJLENBQUMsS0FBSyxDQUFDLFdBQVcsRUFBRSxFQUFFLENBQUM7WUFDN0MsSUFBSSxJQUFJLENBQUMsSUFBSSxLQUFLLElBQUksSUFBSSxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUNuRCxPQUFPLElBQUksQ0FBQztZQUNiLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7O1VBSUc7SUFDSywwQkFBMEIsQ0FBRSxJQUFZO1FBQy9DLHVFQUF1RTtRQUN2RSxNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ3hELElBQUksY0FBYyxFQUFFLENBQUM7WUFDcEIsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsY0FBYyxDQUFDLENBQUM7WUFDdkQsSUFBSSxVQUFVO2dCQUFFLE9BQU8sVUFBVSxDQUFDO1FBQ25DLENBQUM7UUFFRCxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsb0JBQW9CLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDbkQsT0FBTyxVQUFVLENBQUM7SUFDbkIsQ0FBQztJQUVEOzs7T0FHRztJQUNLLGlCQUFpQixDQUFFLElBQW1CO1FBQzdDLElBQUksT0FBTyxHQUFrQixJQUFJLENBQUM7UUFDbEMsT0FBTyxFQUFFLENBQUMsMEJBQTBCLENBQUMsT0FBTyxDQUFDLEVBQUUsQ0FBQztZQUMvQyxPQUFPLEdBQUcsT0FBTyxDQUFDLFVBQVUsQ0FBQztRQUM5QixDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7WUFDOUIsT0FBTyxPQUFPLENBQUM7UUFDaEIsQ0FBQztRQUNELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7VUFFRztJQUNLLGdCQUFnQixDQUFFLElBQWlEO1FBQzFFLE1BQU0sS0FBSyxHQUFhLEVBQUUsQ0FBQztRQUUzQixJQUFJLE9BQU8sR0FBa0IsSUFBSSxDQUFDO1FBQ2xDLE9BQU8sRUFBRSxDQUFDLDBCQUEwQixDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7WUFDL0MsSUFBSSxPQUFPLENBQUMsSUFBSSxFQUFFLENBQUM7Z0JBQ2xCLEtBQUssQ0FBQyxPQUFPLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUNsQyxDQUFDO1lBQ0QsT0FBTyxHQUFHLE9BQU8sQ0FBQyxVQUFVLENBQUM7UUFDOUIsQ0FBQztRQUVELElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO1lBQzlCLEtBQUssQ0FBQyxPQUFPLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzdCLENBQUM7UUFFRCxPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7SUFFTyx1QkFBdUIsQ0FDOUIsVUFBa0IsRUFDbEIsSUFBWSxFQUNaLEtBQWE7UUFFYixJQUFJLEtBQUssR0FBRyx3QkFBd0IsRUFBRSxDQUFDO1lBQ3RDLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFFRCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsR0FBRyxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQzFELE1BQU0sTUFBTSxHQUFHLFFBQVEsRUFBRSxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDbkMsSUFBSSxNQUFNLEVBQUUsQ0FBQztZQUNaLE9BQU8sTUFBTSxDQUFDO1FBQ2YsQ0FBQztRQUNELE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxHQUFHLENBQUMsVUFBVSxDQUFDLEVBQUUsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQy9FLElBQUksVUFBVSxFQUFFLENBQUM7WUFDaEIsTUFBTSxPQUFPLEdBQUcsUUFBUSxFQUFFLEdBQUcsQ0FBQyxVQUFVLENBQUMsQ0FBQztZQUMxQyxJQUFJLE9BQU8sRUFBRSxDQUFDO2dCQUNiLE9BQU8sT0FBTyxDQUFDO1lBQ2hCLENBQUM7UUFDRixDQUFDO1FBRUQsTUFBTSxpQkFBaUIsR0FBRyxJQUFJLENBQUMsdUJBQXVCLENBQUMsR0FBRyxDQUFDLFVBQVUsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNsRixJQUFJLGlCQUFpQixFQUFFLENBQUM7WUFDdkIsTUFBTSxjQUFjLEdBQUcsSUFBSSxDQUFDLDJCQUEyQixDQUFDLGlCQUFpQixFQUFFLFVBQVUsQ0FBQyxDQUFDO1lBQ3ZGLElBQUksY0FBYyxJQUFJLENBQUMsY0FBYyxDQUFDLFVBQVUsRUFBRSxDQUFDO2dCQUNsRCxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMsdUJBQXVCLENBQUMsY0FBYyxDQUFDLFlBQVksRUFBRSxJQUFJLEVBQUUsS0FBSyxHQUFHLENBQUMsQ0FBQyxDQUFDO2dCQUN6RixJQUFJLEtBQUssRUFBRSxDQUFDO29CQUNYLE9BQU8sS0FBSyxDQUFDO2dCQUNkLENBQUM7WUFDRixDQUFDO1FBQ0YsQ0FBQztRQUVELE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxHQUFHLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDN0QsSUFBSSxLQUFLLEVBQUUsQ0FBQztZQUNYLEtBQUssTUFBTSxhQUFhLElBQUksS0FBSyxFQUFFLENBQUM7Z0JBQ25DLE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxhQUFhLEVBQUUsVUFBVSxDQUFDLENBQUM7Z0JBQ25GLElBQUksQ0FBQyxjQUFjLElBQUksY0FBYyxDQUFDLFVBQVUsRUFBRSxDQUFDO29CQUNsRCxTQUFTO2dCQUNWLENBQUM7Z0JBQ0QsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLGNBQWMsQ0FBQyxZQUFZLEVBQUUsSUFBSSxFQUFFLEtBQUssR0FBRyxDQUFDLENBQUMsQ0FBQztnQkFDekYsSUFBSSxLQUFLLEVBQUUsQ0FBQztvQkFDWCxPQUFPLEtBQUssQ0FBQztnQkFDZCxDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFFRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRU8sc0JBQXNCLENBQUUsSUFBWSxFQUFFLFFBQWdCO1FBQzdELE1BQU0sUUFBUSxHQUFHLFFBQVEsQ0FBQyxPQUFPLENBQUMsUUFBUSxDQUFDLENBQUM7UUFDNUMsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsRUFBRSxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDckUsSUFBSSxRQUFRLElBQUksQ0FBQyxRQUFRLENBQUMsV0FBVyxFQUFFLENBQUM7WUFDdkMsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLDJCQUEyQixDQUFDLFFBQVEsQ0FBQyxTQUFTLEVBQUUsUUFBUSxDQUFDLENBQUM7WUFDbEYsSUFBSSxVQUFVLElBQUksQ0FBQyxVQUFVLENBQUMsVUFBVSxFQUFFLENBQUM7Z0JBQzFDLE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxVQUFVLENBQUMsWUFBWSxFQUFFLFFBQVEsQ0FBQyxZQUFZLEVBQUUsQ0FBQyxDQUFDLENBQUM7Z0JBQzlGLElBQUksS0FBSyxFQUFFLENBQUM7b0JBQ1gsT0FBTyxLQUFLLENBQUM7Z0JBQ2QsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBQ0QsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsRUFBRSxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDaEUsT0FBTyxLQUFLLENBQUM7SUFDZCxDQUFDO0lBRU8sMkJBQTJCLENBQUUsT0FBMkI7UUFDL0QsSUFBSSxPQUFPLEdBQUcsT0FBTyxDQUFDO1FBQ3RCLE9BQU8sRUFBRSxDQUFDLHlCQUF5QixDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxjQUFjLENBQUMsT0FBTyxDQUFDO1lBQ3pFLEVBQUUsQ0FBQyx5QkFBeUIsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO1lBQ3hDLE9BQU8sR0FBRyxPQUFPLENBQUMsVUFBVSxDQUFDO1FBQzlCLENBQUM7UUFDRCxPQUFPLE9BQU8sQ0FBQztJQUNoQixDQUFDO0lBRU8sNEJBQTRCLENBQ25DLFVBQXlCLEVBQ3pCLFVBQXlCO1FBRXpCLE1BQU0sT0FBTyxHQUFHLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxVQUFVLENBQUMsQ0FBQztRQUM3RCxJQUFJLENBQUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO1lBQy9CLE9BQU8sT0FBTyxDQUFDO1FBQ2hCLENBQUM7UUFDRCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsc0JBQXNCLENBQUMsT0FBTyxDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsUUFBUSxDQUFDLENBQUM7UUFDaEYsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQ2YsT0FBTyxPQUFPLENBQUM7UUFDaEIsQ0FBQztRQUNELE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxRQUFRLENBQUMsQ0FBQztRQUMxRCxPQUFPLE1BQU0sQ0FBQztJQUNmLENBQUM7SUFFRDs7OztPQUlHO0lBQ0ssNEJBQTRCLENBQUUsSUFBdUI7UUFDNUQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQztRQUM3QixNQUFNLElBQUksR0FBRyxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQztZQUNqQyxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUk7WUFDWCxDQUFDLENBQUMsRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQztnQkFDcEMsQ0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSTtnQkFDaEIsQ0FBQyxDQUFDLEVBQUUsQ0FBQztRQUNQLElBQUksT0FBa0MsQ0FBQztRQUV2QyxJQUFJLElBQUksS0FBSyxNQUFNLEVBQUUsQ0FBQztZQUNyQixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDaEQsSUFBSSxRQUFRLEVBQUUsQ0FBQztnQkFDZCxPQUFPLEdBQUcsSUFBSSxDQUFDLGdCQUFnQixDQUFDLFFBQVEsQ0FBQyxNQUFNLENBQUMsQ0FBQztZQUNsRCxDQUFDO1FBQ0YsQ0FBQzthQUFNLENBQUM7WUFDUCxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsU0FBUyxDQUFDO1lBQzVCLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxJQUFJLENBQUUsQ0FBQyxDQUFFLENBQUMsRUFBRSxDQUFDO2dCQUNuQyxNQUFNLENBQUUsQUFBRCxFQUFHLGFBQWEsQ0FBRSxHQUFHLElBQUksQ0FBQztnQkFDakMsT0FBTyxHQUFHLGFBQWEsQ0FBQztZQUN6QixDQUFDO2lCQUFNLENBQUM7Z0JBQ1AsTUFBTSxDQUFFLGFBQWEsQ0FBRSxHQUFHLElBQUksQ0FBQztnQkFDL0IsT0FBTyxHQUFHLGFBQWEsQ0FBQztZQUN6QixDQUFDO1FBQ0YsQ0FBQztRQUVELElBQUksQ0FBQyxPQUFPLEVBQUUsQ0FBQztZQUNkLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsNEJBQTRCLENBQUMsT0FBTyxFQUFFLElBQUksQ0FBQyxhQUFhLEVBQUUsQ0FBQyxDQUFDO1FBQ2hGLE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7Ozs7T0FNRztJQUNLLHVCQUF1QixDQUFFLGVBQStDO1FBQy9FLElBQUksQ0FBQyxlQUFlLEVBQUUsQ0FBQztZQUN0QixPQUFPLEtBQUssQ0FBQztRQUNkLENBQUM7UUFDRCxNQUFNLElBQUksR0FBRyxFQUFFLENBQUMsb0JBQW9CLENBQUMsZUFBZSxDQUFDO1lBQ3BELEVBQUUsQ0FBQyxlQUFlLENBQUMsZUFBZSxDQUFDLElBQUksRUFBRSxDQUFDLHFCQUFxQixDQUFDLGVBQWUsQ0FBQyxDQUFDO1FBQ2xGLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUNYLE9BQU8sS0FBSyxDQUFDO1FBQ2QsQ0FBQztRQUNELE1BQU0sU0FBUyxHQUFHLEVBQUUsQ0FBQyxZQUFZLENBQUMsZUFBZSxDQUFDLENBQUM7UUFDbkQsTUFBTSxNQUFNLEdBQUcsQ0FBQyxDQUFDLFNBQVMsSUFBSSxTQUFTLENBQUMsSUFBSSxDQUFDLENBQUMsUUFBUSxFQUFFLEVBQUU7WUFDekQsT0FBTyxRQUFRLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsWUFBWSxDQUFDO1FBQ3JELENBQUMsQ0FBQyxDQUFDO1FBQ0gsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7O09BRUc7SUFDSyxpQkFBaUIsQ0FBRSxJQUF1QjtRQUNqRCxNQUFNLGVBQWUsR0FBRyxJQUFJLENBQUMsNEJBQTRCLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDaEUsSUFBSSxDQUFDLGVBQWUsRUFBRSxDQUFDO1lBQ3RCLE9BQU8sSUFBSSxHQUFHLEVBQXdCLENBQUM7UUFDeEMsQ0FBQztRQUNELE1BQU0sZUFBZSxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQztRQUN2RCxJQUFJLENBQUMseUJBQXlCLEdBQUcsUUFBUSxDQUFDLE9BQU8sQ0FBQyxlQUFlLENBQUMsYUFBYSxFQUFFLENBQUMsUUFBUSxDQUFDLENBQUM7UUFDNUYsSUFBSSxDQUFDO1lBQ0osTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLGdDQUFnQyxDQUFDLGVBQWUsQ0FBQyxDQUFDO1lBQ3RFLE9BQU8sTUFBTSxDQUFDO1FBQ2YsQ0FBQztnQkFBUyxDQUFDO1lBQ1YsSUFBSSxDQUFDLHlCQUF5QixHQUFHLGVBQWUsQ0FBQztRQUNsRCxDQUFDO0lBQ0YsQ0FBQztJQUVEOztPQUVHO0lBQ0ssZ0NBQWdDLENBQUUsZUFBbUM7UUFDNUUsTUFBTSxVQUFVLEdBQUcsSUFBSSxHQUFHLEVBQXdCLENBQUM7UUFFbkQsb0VBQW9FO1FBQ3BFLE1BQU0sV0FBVyxHQUFHLElBQUksQ0FBQyxnQkFBZ0IsQ0FBQyxlQUFlLENBQUMsQ0FBQztRQUUzRCw2QkFBNkI7UUFDN0IsSUFBSSxFQUFFLENBQUMsb0JBQW9CLENBQUMsZUFBZSxDQUFDLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxlQUFlLENBQUM7WUFDbEYsRUFBRSxDQUFDLHFCQUFxQixDQUFDLGVBQWUsQ0FBQyxFQUFFLENBQUM7WUFDNUMsTUFBTSxFQUFFLElBQUksRUFBRSxHQUFHLGVBQWUsQ0FBQztZQUVqQyxrRUFBa0U7WUFDbEUsMkVBQTJFO1lBQzNFLE1BQU0sbUJBQW1CLEdBQUcsSUFBSSxDQUFDLDBCQUEwQixDQUFDLGVBQWUsQ0FBQyxDQUFDO1lBQzdFLEtBQUssTUFBTSxDQUFFLElBQUksRUFBRSxRQUFRLENBQUUsSUFBSSxtQkFBbUIsRUFBRSxDQUFDO2dCQUN0RCxVQUFVLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxRQUFRLENBQUMsQ0FBQztZQUNoQyxDQUFDO1lBRUQsd0VBQXdFO1lBQ3hFLHVFQUF1RTtZQUN2RSwrRUFBK0U7WUFDL0UsTUFBTSxxQkFBcUIsR0FBRyxJQUFJLENBQUMsMEJBQTBCLENBQUMsZUFBZSxDQUFDLENBQUM7WUFDL0UsTUFBTSw4QkFBOEIsR0FBRyxDQUFDLHFCQUFxQixJQUFJLGVBQWUsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxFQUFFO2dCQUN4RyxNQUFNLE1BQU0sR0FBRyxFQUFFLENBQUMsWUFBWSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxNQUFNLElBQUksS0FBSyxDQUFDLElBQUksS0FBSyxTQUFTLENBQUM7Z0JBQ3JHLE9BQU8sTUFBTSxDQUFDO1lBQ2YsQ0FBQyxDQUFDLENBQUM7WUFDSCxJQUFJLENBQUMsOEJBQThCLElBQUksSUFBSSxJQUFJLEVBQUUsQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztnQkFDakUsS0FBSyxNQUFNLElBQUksSUFBSSxJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7b0JBQ3BDLElBQUksRUFBRSxDQUFDLHFCQUFxQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7d0JBQ3BDLElBQUksQ0FBQyw0QkFBNEIsQ0FBQyxJQUFJLENBQUMsVUFBVSxFQUFFLFVBQVUsRUFBRSxXQUFXLENBQUMsQ0FBQztvQkFDN0UsQ0FBQztnQkFDRixDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFFRCwwQkFBMEI7UUFDMUIsSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsZUFBZSxDQUFDLElBQUksRUFBRSxDQUFDLGtCQUFrQixDQUFDLGVBQWUsQ0FBQyxFQUFFLENBQUM7WUFDckYsOERBQThEO1lBQzlELE1BQU0sa0JBQWtCLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLGVBQWUsQ0FBQyxDQUFDO1lBRTNFLEtBQUssTUFBTSxNQUFNLElBQUksZUFBZSxDQUFDLE9BQU8sRUFBRSxDQUFDO2dCQUM5QywrQkFBK0I7Z0JBQy9CLElBQUksRUFBRSxDQUFDLHFCQUFxQixDQUFDLE1BQU0sQ0FBQyxJQUFJLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQztvQkFDckQsd0NBQXdDO29CQUN4QyxJQUFJLE1BQU0sQ0FBQyxTQUFTLEVBQUUsQ0FBQzt3QkFDdEIsTUFBTSxxQkFBcUIsR0FBRyxNQUFNLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsRUFBRTs0QkFDdkQsT0FBTyxDQUFDLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsY0FBYztnQ0FDN0MsQ0FBQyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGdCQUFnQixDQUFDO3dCQUM1QyxDQUFDLENBQUMsQ0FBQzt3QkFDSCxJQUFJLHFCQUFxQixFQUFFLENBQUM7NEJBQzNCLFNBQVM7d0JBQ1YsQ0FBQztvQkFDRixDQUFDO29CQUVELE1BQU0sSUFBSSxHQUFHLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDO29CQUNsRSxJQUFJLElBQUksRUFBRSxDQUFDO3dCQUNWLElBQUksSUFBSSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxDQUFDO3dCQUN2QyxJQUFJLElBQUksS0FBSyxTQUFTLElBQUksTUFBTSxDQUFDLFdBQVcsRUFBRSxDQUFDOzRCQUM5QyxJQUFJLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLE1BQU0sQ0FBQyxXQUFXLENBQUMsQ0FBQzt3QkFDMUQsQ0FBQzt3QkFDRCxVQUFVLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRTs0QkFDcEIsSUFBSTs0QkFDSixJQUFJOzRCQUNKLFFBQVEsRUFBRyxDQUFDLENBQUMsTUFBTSxDQUFDLGFBQWE7eUJBQ2pDLENBQUMsQ0FBQztvQkFDSixDQUFDO2dCQUNGLENBQUM7Z0JBRUQsNkJBQTZCO2dCQUM3QixJQUFJLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxNQUFNLENBQUMsSUFBSSxNQUFNLENBQUMsSUFBSSxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7b0JBQ25GLHFDQUFxQztvQkFDckMsSUFBSSxNQUFNLENBQUMsU0FBUyxFQUFFLENBQUM7d0JBQ3RCLE1BQU0scUJBQXFCLEdBQUcsTUFBTSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUU7NEJBQ3ZELE9BQU8sQ0FBQyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGNBQWM7Z0NBQzdDLENBQUMsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxnQkFBZ0IsQ0FBQzt3QkFDNUMsQ0FBQyxDQUFDLENBQUM7d0JBQ0gsSUFBSSxxQkFBcUIsRUFBRSxDQUFDOzRCQUMzQixTQUFTO3dCQUNWLENBQUM7b0JBQ0YsQ0FBQztvQkFFRCxNQUFNLElBQUksR0FBRyxNQUFNLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztvQkFDOUIsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLGVBQWUsQ0FBQyxNQUFNLEVBQUUsa0JBQWtCLENBQUMsQ0FBQztvQkFDOUQsVUFBVSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUU7d0JBQ3BCLElBQUk7d0JBQ0osSUFBSTt3QkFDSixRQUFRLEVBQUcsS0FBSztxQkFDaEIsQ0FBQyxDQUFDO2dCQUNKLENBQUM7Z0JBRUQsNkJBQTZCO2dCQUM3QixJQUFJLEVBQUUsQ0FBQyxhQUFhLENBQUMsTUFBTSxDQUFDLElBQUksTUFBTSxDQUFDLElBQUksSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO29CQUM3RSxxQ0FBcUM7b0JBQ3JDLElBQUksTUFBTSxDQUFDLFNBQVMsRUFBRSxDQUFDO3dCQUN0QixNQUFNLHFCQUFxQixHQUFHLE1BQU0sQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxFQUFFOzRCQUN2RCxPQUFPLENBQUMsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxjQUFjO2dDQUM3QyxDQUFDLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsZ0JBQWdCLENBQUM7d0JBQzVDLENBQUMsQ0FBQyxDQUFDO3dCQUNILElBQUkscUJBQXFCLEVBQUUsQ0FBQzs0QkFDM0IsU0FBUzt3QkFDVixDQUFDO29CQUNGLENBQUM7b0JBRUQsTUFBTSxJQUFJLEdBQUcsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7b0JBQzlCLGtFQUFrRTtvQkFDbEUsSUFBSSxJQUFJLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7b0JBQ3ZDLElBQUksSUFBSSxLQUFLLFNBQVMsSUFBSSxNQUFNLENBQUMsSUFBSSxFQUFFLENBQUM7d0JBQ3ZDLElBQUksR0FBRyxJQUFJLENBQUMsdUJBQXVCLENBQUMsTUFBTSxDQUFDLElBQUksRUFBRSxrQkFBa0IsQ0FBQyxDQUFDO29CQUN0RSxDQUFDO29CQUNELFVBQVUsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFO3dCQUNwQixJQUFJO3dCQUNKLElBQUk7d0JBQ0osUUFBUSxFQUFHLEtBQUs7d0JBQ2hCLFFBQVEsRUFBRyxJQUFJO3FCQUNmLENBQUMsQ0FBQztnQkFDSixDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFFRCxPQUFPLFVBQVUsQ0FBQztJQUNuQixDQUFDO0lBRUQ7OztPQUdHO0lBQ0ssZ0JBQWdCLENBQUUsVUFBOEI7UUFDdkQsTUFBTSxPQUFPLEdBQUcsSUFBSSxHQUFHLEVBQWtCLENBQUM7UUFFMUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxvQkFBb0IsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxlQUFlLENBQUMsVUFBVSxDQUFDO1lBQzFFLENBQUMsRUFBRSxDQUFDLHFCQUFxQixDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7WUFDeEMsT0FBTyxPQUFPLENBQUM7UUFDaEIsQ0FBQztRQUVELDhCQUE4QjtRQUM5QixLQUFLLE1BQU0sS0FBSyxJQUFJLFVBQVUsQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUMzQyxJQUFJLENBQUMsS0FBSyxDQUFDLElBQUksSUFBSSxDQUFDLEtBQUssQ0FBQyxJQUFJO2dCQUFFLFNBQVM7WUFFekMscUJBQXFCO1lBQ3JCLElBQUksU0FBUyxHQUFHLEVBQUUsQ0FBQztZQUNuQixJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQ2pDLFNBQVMsR0FBRyxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztZQUM3QixDQUFDO2lCQUFNLENBQUM7Z0JBQ1AsdUNBQXVDO2dCQUN2QyxTQUFTO1lBQ1YsQ0FBQztZQUVELDhDQUE4QztZQUM5QyxJQUFJLEVBQUUsQ0FBQyxpQkFBaUIsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztnQkFDdEMsS0FBSyxNQUFNLE1BQU0sSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLE9BQU8sRUFBRSxDQUFDO29CQUN6QyxJQUFJLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxNQUFNLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO3dCQUNwRSxNQUFNLFFBQVEsR0FBRyxNQUFNLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQzt3QkFDbEMsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7d0JBQ3pDLE9BQU8sQ0FBQyxHQUFHLENBQUMsR0FBRyxTQUFTLElBQUksUUFBUSxFQUFFLEVBQUUsSUFBSSxDQUFDLENBQUM7b0JBQy9DLENBQUM7Z0JBQ0YsQ0FBQztZQUNGLENBQUM7aUJBQU0sQ0FBQztnQkFDUCwyREFBMkQ7Z0JBQzNELHdEQUF3RDtnQkFDeEQscURBQXFEO2dCQUNyRCwyREFBMkQ7Z0JBQzNELHdEQUF3RDtnQkFDeEQseURBQXlEO2dCQUN6RCx1REFBdUQ7Z0JBQ3ZELGlEQUFpRDtnQkFDakQsSUFBSSxTQUFnRCxDQUFDO2dCQUNyRCxJQUFJLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7b0JBQ2hGLE1BQU0sYUFBYSxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQztvQkFDL0MsU0FBUyxHQUFHLElBQUksQ0FBQyxnQ0FBZ0MsQ0FBQyxhQUFhLEVBQUUsSUFBSSxDQUFDLHlCQUF5QixDQUFDLENBQUM7Z0JBQ2xHLENBQUM7Z0JBQ0QsSUFBSSxTQUFTLEVBQUUsQ0FBQztvQkFDZixrREFBa0Q7b0JBQ2xELE1BQU0sZUFBZSxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQztvQkFDdkQsSUFBSSxDQUFDLHlCQUF5QixHQUFHLFNBQVMsQ0FBQyxJQUFJLENBQUM7b0JBQ2hELElBQUksQ0FBQzt3QkFDSixNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsK0JBQStCLENBQUMsU0FBUyxDQUFDLENBQUM7d0JBQ3ZFLEtBQUssTUFBTSxDQUFFLFFBQVEsRUFBRSxJQUFJLENBQUUsSUFBSSxjQUFjLEVBQUUsQ0FBQzs0QkFDakQsT0FBTyxDQUFDLEdBQUcsQ0FBQyxHQUFHLFNBQVMsSUFBSSxRQUFRLEVBQUUsRUFBRSxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7d0JBQ3BELENBQUM7b0JBQ0YsQ0FBQzs0QkFBUyxDQUFDO3dCQUNWLElBQUksQ0FBQyx5QkFBeUIsR0FBRyxlQUFlLENBQUM7b0JBQ2xELENBQUM7b0JBQ0QsdURBQXVEO29CQUN2RCxvREFBb0Q7b0JBQ3BELHNEQUFzRDtvQkFDdEQsTUFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLCtCQUErQixDQUFDLFNBQVMsQ0FBQyxDQUFDO29CQUNsRSxJQUFJLFNBQVMsSUFBSSxTQUFTLEtBQUssU0FBUyxFQUFFLENBQUM7d0JBQzFDLE9BQU8sQ0FBQyxHQUFHLENBQUMsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDO29CQUNuQyxDQUFDO2dCQUNGLENBQUM7cUJBQU0sQ0FBQztvQkFDUCw0REFBNEQ7b0JBQzVELE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxDQUFDO29CQUN4QyxJQUFJLElBQUksS0FBSyxTQUFTLEVBQUUsQ0FBQzt3QkFDeEIsT0FBTyxDQUFDLEdBQUcsQ0FBQyxTQUFTLEVBQUUsSUFBSSxDQUFDLENBQUM7b0JBQzlCLENBQUM7Z0JBQ0YsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxPQUFPLENBQUM7SUFDaEIsQ0FBQztJQUVEOzs7T0FHRztJQUNLLHNCQUFzQixDQUFFLElBQW1CO1FBQ2xELDBCQUEwQjtRQUMxQixJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUMzQixPQUFPLElBQUksQ0FBQyxJQUFJLENBQUM7UUFDbEIsQ0FBQztRQUNELDJDQUEyQztRQUMzQyxJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ3pDLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxzQkFBc0IsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLENBQUM7WUFDMUQsSUFBSSxJQUFJLEVBQUUsQ0FBQztnQkFDVixPQUFPLEdBQUcsSUFBSSxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDcEMsQ0FBQztRQUNGLENBQUM7UUFDRCxrREFBa0Q7UUFDbEQsSUFBSSxFQUFFLENBQUMsa0JBQWtCLENBQUMsSUFBSSxDQUFDO1lBQzlCLElBQUksQ0FBQyxhQUFhLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVyxFQUFFLENBQUM7WUFDeEQsc0NBQXNDO1lBQ3RDLE9BQU8sSUFBSSxDQUFDLHNCQUFzQixDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUMvQyxDQUFDO1FBQ0QsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOztPQUVHO0lBQ0ssNEJBQTRCLENBQ25DLElBQW1CLEVBQ25CLFVBQXFDLEVBQ3JDLGNBQW1DLElBQUksR0FBRyxFQUFFO1FBRTVDLGdDQUFnQztRQUNoQyxJQUFJLEVBQUUsQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLENBQUM7WUFDOUIsSUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxXQUFXLEVBQUUsQ0FBQztZQUN4RCxNQUFNLEVBQUUsSUFBSSxFQUFFLEdBQUcsSUFBSSxDQUFDO1lBRXRCLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQ3pDLDBDQUEwQztnQkFDMUMsSUFBSSxJQUFJLENBQUMsVUFBVSxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFdBQVcsRUFBRSxDQUFDO29CQUN4RCxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQztvQkFDN0IsSUFBSSxJQUFJLEVBQUUsQ0FBQzt3QkFDVixvRkFBb0Y7d0JBQ3BGLE1BQU0sV0FBVyxHQUFHLElBQUksQ0FBQyxzQkFBc0IsQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7d0JBQzVELElBQUksSUFBSSxHQUFHLFdBQVcsQ0FBQyxDQUFDLENBQUMsV0FBVyxDQUFDLEdBQUcsQ0FBQyxXQUFXLENBQUMsQ0FBQyxDQUFDLENBQUMsU0FBUyxDQUFDO3dCQUNsRSwwRUFBMEU7d0JBQzFFLElBQUksQ0FBQyxJQUFJLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLEVBQUUsQ0FBQzs0QkFDMUMsSUFBSSxHQUFHLFdBQVcsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsQ0FBQzt3QkFDekMsQ0FBQzt3QkFDRCxzREFBc0Q7d0JBQ3RELG9EQUFvRDt3QkFDcEQsaURBQWlEO3dCQUNqRCxJQUFJLENBQUMsSUFBSSxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxFQUFFLENBQUM7NEJBQzFDLE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsQ0FBQzs0QkFDMUQsSUFBSSxLQUFLLEVBQUUsQ0FBQztnQ0FDWCw2Q0FBNkM7Z0NBQzdDLCtDQUErQztnQ0FDL0MsNkNBQTZDO2dDQUM3QywyQkFBMkI7Z0NBQzNCLE1BQU0sU0FBUyxHQUFHLElBQUksQ0FBQyxLQUFLLENBQUMsUUFBUSxDQUFDLEtBQUssQ0FBQyxDQUFDO2dDQUM3QyxNQUFNLFVBQVUsR0FBRyxTQUFTO29DQUMzQixDQUFDLENBQUMsSUFBSSxDQUFDLDBCQUEwQixDQUFDLFNBQVMsQ0FBQztvQ0FDNUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQztnQ0FDYixJQUFJLFVBQVUsRUFBRSxDQUFDO29DQUNoQixJQUFJLEdBQUcsVUFBVSxDQUFDO2dDQUNuQixDQUFDOzRCQUNGLENBQUM7d0JBQ0YsQ0FBQzt3QkFDRCxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7NEJBQ1gsSUFBSSxHQUFHLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxJQUFJLENBQUMsS0FBSyxFQUFFLFdBQVcsQ0FBQyxDQUFDO3dCQUMvRCxDQUFDO3dCQUNELHdEQUF3RDt3QkFDeEQsb0RBQW9EO3dCQUNwRCxzREFBc0Q7d0JBQ3RELHVEQUF1RDt3QkFDdkQsdURBQXVEO3dCQUN2RCxxREFBcUQ7d0JBQ3JELHVEQUF1RDt3QkFDdkQsNENBQTRDO3dCQUM1QyxNQUFNLFFBQVEsR0FBRyxVQUFVLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO3dCQUN0QyxNQUFNLGNBQWMsR0FBRyxDQUFDLElBQUksSUFBSSxJQUFJLENBQUMsUUFBUSxDQUFDLFNBQVMsQ0FBQyxDQUFDO3dCQUN6RCxNQUFNLGVBQWUsR0FBRyxRQUFRLENBQUMsQ0FBQyxDQUFDLFFBQVEsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLEtBQUssU0FBUyxDQUFDLENBQUMsQ0FBQyxLQUFLLENBQUM7d0JBQzlFLElBQUksZUFBZSxJQUFJLGNBQWMsRUFBRSxDQUFDOzRCQUN2QyxnREFBZ0Q7d0JBQ2pELENBQUM7NkJBQU0sQ0FBQzs0QkFDUCxVQUFVLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRTtnQ0FDcEIsSUFBSTtnQ0FDSixJQUFJO2dDQUNKLFFBQVEsRUFBRyxRQUFRLENBQUMsQ0FBQyxDQUFDLFFBQVEsQ0FBQyxRQUFRLENBQUMsQ0FBQyxDQUFDLEtBQUs7NkJBQy9DLENBQUMsQ0FBQzt3QkFDSixDQUFDO29CQUNGLENBQUM7Z0JBQ0YsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsK0NBQStDO1FBQy9DLElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDL0IsTUFBTSxFQUFFLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQztZQUMzQixJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxFQUFFLENBQUM7Z0JBQ3BDLEVBQUUsQ0FBQyxJQUFJLEVBQUUsSUFBSSxLQUFLLFFBQVE7Z0JBQzFCLEVBQUUsQ0FBQyxZQUFZLENBQUMsRUFBRSxDQUFDLFVBQVUsQ0FBQztnQkFDOUIsRUFBRSxDQUFDLFVBQVUsQ0FBQyxJQUFJLEtBQUssUUFBUSxFQUFFLENBQUM7Z0JBQ2xDLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUM7Z0JBQzVCLElBQUksSUFBSSxDQUFDLE1BQU0sSUFBSSxDQUFDLElBQUksSUFBSSxDQUFFLENBQUMsQ0FBRSxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFdBQVcsRUFBRSxDQUFDO29CQUN0RSw4Q0FBOEM7b0JBQzlDLE1BQU0sQ0FBRSxBQUFELEVBQUcsUUFBUSxDQUFFLEdBQUcsSUFBSSxDQUFDO29CQUM1QixJQUFJLEVBQUUsQ0FBQyx5QkFBeUIsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO3dCQUM1QyxLQUFLLE1BQU0sSUFBSSxJQUFJLFFBQVEsQ0FBQyxVQUFVLEVBQUUsQ0FBQzs0QkFDeEMsSUFBSSxFQUFFLENBQUMsb0JBQW9CLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztnQ0FDakUsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7Z0NBQzVCLFVBQVUsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFO29DQUNwQixJQUFJO29DQUNKLElBQUksRUFBTyxJQUFJLENBQUMsd0JBQXdCLENBQUMsSUFBSSxDQUFDLFdBQVcsQ0FBQztvQ0FDMUQsUUFBUSxFQUFHLEtBQUs7aUNBQ2hCLENBQUMsQ0FBQzs0QkFDSixDQUFDO3dCQUNGLENBQUM7b0JBQ0YsQ0FBQzt5QkFBTSxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQzt3QkFDdEMseURBQXlEO3dCQUN6RCx1REFBdUQ7d0JBQ3ZELHFEQUFxRDt3QkFDckQsOENBQThDO3dCQUM5Qyx3REFBd0Q7d0JBQ3hELHFEQUFxRDt3QkFDckQsb0RBQW9EO3dCQUNwRCx3QkFBd0I7d0JBQ3hCLE1BQU0sU0FBUyxHQUFHLFFBQVEsQ0FBQyxJQUFJLENBQUM7d0JBQ2hDLEtBQUssTUFBTSxDQUFFLEdBQUcsRUFBRSxJQUFJLENBQUUsSUFBSSxXQUFXLEVBQUUsQ0FBQzs0QkFDekMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsR0FBRyxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0NBQ3RDLFNBQVM7NEJBQ1YsQ0FBQzs0QkFDRCxNQUFNLElBQUksR0FBRyxHQUFHLENBQUMsS0FBSyxDQUFDLFNBQVMsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxDQUFDLENBQUM7NEJBQzdDLFVBQVUsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFO2dDQUNwQixJQUFJO2dDQUNKLElBQUk7Z0NBQ0osUUFBUSxFQUFHLEtBQUs7NkJBQ2hCLENBQUMsQ0FBQzt3QkFDSixDQUFDO29CQUNGLENBQUM7Z0JBQ0YsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO0lBQ0YsQ0FBQztJQUVEOztPQUVHO0lBQ0ssc0JBQXNCLENBQUUsU0FBOEI7UUFDN0QsTUFBTSxVQUFVLEdBQUcsSUFBSSxHQUFHLEVBQXdCLENBQUM7UUFFbkQsS0FBSyxNQUFNLE1BQU0sSUFBSSxTQUFTLENBQUMsT0FBTyxFQUFFLENBQUM7WUFDeEMsK0JBQStCO1lBQy9CLElBQUksRUFBRSxDQUFDLHFCQUFxQixDQUFDLE1BQU0sQ0FBQyxJQUFJLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQztnQkFDckQsd0NBQXdDO2dCQUN4QyxJQUFJLE1BQU0sQ0FBQyxTQUFTLEVBQUUsQ0FBQztvQkFDdEIsTUFBTSxxQkFBcUIsR0FBRyxNQUFNLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxjQUFjO3dCQUMxRixDQUFDLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsZ0JBQWdCLENBQUMsQ0FBQztvQkFDakQsSUFBSSxxQkFBcUIsRUFBRSxDQUFDO3dCQUMzQixTQUFTO29CQUNWLENBQUM7Z0JBQ0YsQ0FBQztnQkFFRCxNQUFNLElBQUksR0FBRyxFQUFFLENBQUMsWUFBWSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQztnQkFDbEUsSUFBSSxJQUFJLEVBQUUsQ0FBQztvQkFDVixrRUFBa0U7b0JBQ2xFLElBQUksSUFBSSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxDQUFDO29CQUN2QyxJQUFJLElBQUksS0FBSyxTQUFTLElBQUksTUFBTSxDQUFDLFdBQVcsRUFBRSxDQUFDO3dCQUM5QyxJQUFJLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLE1BQU0sQ0FBQyxXQUFXLENBQUMsQ0FBQztvQkFDMUQsQ0FBQztvQkFDRCxVQUFVLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRTt3QkFDcEIsSUFBSTt3QkFDSixJQUFJO3dCQUNKLFFBQVEsRUFBRyxDQUFDLENBQUMsTUFBTSxDQUFDLGFBQWE7cUJBQ2pDLENBQUMsQ0FBQztnQkFDSixDQUFDO1lBQ0YsQ0FBQztZQUVELDZCQUE2QjtZQUM3QixJQUFJLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxNQUFNLENBQUMsSUFBSSxNQUFNLENBQUMsSUFBSSxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQ25GLHFDQUFxQztnQkFDckMsSUFBSSxNQUFNLENBQUMsU0FBUyxFQUFFLENBQUM7b0JBQ3RCLE1BQU0scUJBQXFCLEdBQUcsTUFBTSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsY0FBYzt3QkFDMUYsQ0FBQyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGdCQUFnQixDQUFDLENBQUM7b0JBQ2pELElBQUkscUJBQXFCLEVBQUUsQ0FBQzt3QkFDM0IsU0FBUztvQkFDVixDQUFDO2dCQUNGLENBQUM7Z0JBRUQsTUFBTSxJQUFJLEdBQUcsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7Z0JBQzlCLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxlQUFlLENBQUMsTUFBTSxDQUFDLENBQUM7Z0JBQzFDLFVBQVUsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFO29CQUNwQixJQUFJO29CQUNKLElBQUk7b0JBQ0osUUFBUSxFQUFHLEtBQUs7aUJBQ2hCLENBQUMsQ0FBQztZQUNKLENBQUM7WUFFRCw2QkFBNkI7WUFDN0IsSUFBSSxFQUFFLENBQUMsYUFBYSxDQUFDLE1BQU0sQ0FBQyxJQUFJLE1BQU0sQ0FBQyxJQUFJLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztnQkFDN0UscUNBQXFDO2dCQUNyQyxJQUFJLE1BQU0sQ0FBQyxTQUFTLEVBQUUsQ0FBQztvQkFDdEIsTUFBTSxxQkFBcUIsR0FBRyxNQUFNLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxjQUFjO3dCQUMxRixDQUFDLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsZ0JBQWdCLENBQUMsQ0FBQztvQkFDakQsSUFBSSxxQkFBcUIsRUFBRSxDQUFDO3dCQUMzQixTQUFTO29CQUNWLENBQUM7Z0JBQ0YsQ0FBQztnQkFFRCxNQUFNLElBQUksR0FBRyxNQUFNLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztnQkFDOUIsa0VBQWtFO2dCQUNsRSxJQUFJLElBQUksR0FBRyxJQUFJLENBQUMsU0FBUyxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDdkMsSUFBSSxJQUFJLEtBQUssU0FBUyxJQUFJLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQztvQkFDdkMsSUFBSSxHQUFHLElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7Z0JBQ2xELENBQUM7Z0JBQ0QsVUFBVSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUU7b0JBQ3BCLElBQUk7b0JBQ0osSUFBSTtvQkFDSixRQUFRLEVBQUcsS0FBSztvQkFDaEIsUUFBUSxFQUFHLElBQUk7aUJBQ2YsQ0FBQyxDQUFDO1lBQ0osQ0FBQztRQUNGLENBQUM7UUFFRCxPQUFPLFVBQVUsQ0FBQztJQUNuQixDQUFDO0lBRUQ7Ozs7T0FJRztJQUNLLHlCQUF5QixDQUFFLFNBQWtDO1FBQ3BFLE1BQU0sYUFBYSxHQUFHLElBQUksR0FBRyxFQUFrQixDQUFDO1FBRWhELEtBQUssTUFBTSxNQUFNLElBQUksU0FBUyxDQUFDLE9BQU8sRUFBRSxDQUFDO1lBQ3hDLElBQUksRUFBRSxDQUFDLHFCQUFxQixDQUFDLE1BQU0sQ0FBQyxJQUFJLE1BQU0sQ0FBQyxJQUFJLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztnQkFDckYseUVBQXlFO2dCQUN6RSxnRUFBZ0U7Z0JBQ2hFLE1BQU0sSUFBSSxHQUFHLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO2dCQUM5QixJQUFJLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQztvQkFDakIsYUFBYSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQztnQkFDdEQsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxhQUFhLENBQUM7SUFDdEIsQ0FBQztJQUVEOztPQUVHO0lBQ0ssZUFBZSxDQUFFLE1BQTRCLEVBQUUsa0JBQXdDO1FBQzlGLE1BQU0sTUFBTSxHQUFHLE1BQU0sQ0FBQyxVQUFVLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxFQUFFO1lBQzVDLE1BQU0sU0FBUyxHQUFHLEVBQUUsQ0FBQyxZQUFZLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDO1lBQ3hFLE1BQU0sU0FBUyxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxDQUFDO1lBQzdDLE9BQU8sR0FBRyxTQUFTLEtBQUssU0FBUyxFQUFFLENBQUM7UUFDckMsQ0FBQyxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO1FBRWQsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLGVBQWUsQ0FBQyxNQUFNLEVBQUUsa0JBQWtCLENBQUMsQ0FBQztRQUVwRSxJQUFJLE1BQU0sRUFBRSxDQUFDO1lBQ1osT0FBTyxJQUFJLE1BQU0sUUFBUSxVQUFVLEVBQUUsQ0FBQztRQUN2QyxDQUFDO1FBQ0QsT0FBTyxTQUFTLFVBQVUsRUFBRSxDQUFDO0lBQzlCLENBQUM7SUFFTywwQkFBMEIsQ0FBRSxPQUEyQjtRQUM5RCxJQUFJLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO1lBQzdDLE9BQU8sSUFBSSxDQUFDO1FBQ2IsQ0FBQztRQUNELElBQUksQ0FBQyxFQUFFLENBQUMsb0JBQW9CLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsZUFBZSxDQUFDLE9BQU8sQ0FBQztZQUNwRSxDQUFDLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO1lBQ3JDLE9BQU8sS0FBSyxDQUFDO1FBQ2QsQ0FBQztRQUNELEtBQUssTUFBTSxLQUFLLElBQUksT0FBTyxDQUFDLFVBQVUsRUFBRSxDQUFDO1lBQ3hDLE1BQU0sTUFBTSxHQUFHLEVBQUUsQ0FBQyxZQUFZLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLE1BQU0sQ0FBQztZQUN6RSxJQUFJLENBQUMsTUFBTSxJQUFJLENBQUMsS0FBSyxDQUFDLElBQUksSUFBSSxDQUFDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDO2dCQUNoRSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO2dCQUN4QyxTQUFTO1lBQ1YsQ0FBQztZQUNELE1BQU0sUUFBUSxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQztZQUMxQyxJQUFJLElBQUksQ0FBQyxrQkFBa0IsRUFBRSxJQUFJLEtBQUssUUFBUSxJQUFJLElBQUksQ0FBQyxrQkFBa0IsRUFBRSxRQUFRLEtBQUssUUFBUSxFQUFFLENBQUM7Z0JBQ2xHLE9BQU8sSUFBSSxDQUFDO1lBQ2IsQ0FBQztZQUNELE1BQU0sU0FBUyxHQUFHLElBQUksQ0FBQyxLQUFLLENBQUMsY0FBYyxDQUFDLFFBQVEsQ0FBQyxDQUFDO1lBQ3RELElBQUksU0FBUyxFQUFFLENBQUM7Z0JBQ2YsT0FBTyxJQUFJLENBQUM7WUFDYixDQUFDO1FBQ0YsQ0FBQztRQUNELE9BQU8sS0FBSyxDQUFDO0lBQ2QsQ0FBQztJQUVPLG9CQUFvQixDQUFFLE9BQXVDO1FBQ3BFLElBQUksQ0FBQyxPQUFPLElBQUksQ0FBQyxDQUFDLEVBQUUsQ0FBQyxvQkFBb0IsQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxlQUFlLENBQUMsT0FBTyxDQUFDO1lBQ2pGLENBQUMsRUFBRSxDQUFDLHFCQUFxQixDQUFDLE9BQU8sQ0FBQyxDQUFDLEVBQUUsQ0FBQztZQUN0QyxPQUFPLEtBQUssQ0FBQztRQUNkLENBQUM7UUFDRCxNQUFNLE1BQU0sR0FBRyxPQUFPLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsRUFBRTtZQUM5QyxNQUFNLE9BQU8sR0FBRyxFQUFFLENBQUMsWUFBWSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxNQUFNO2dCQUN4RSxLQUFLLENBQUMsSUFBSSxFQUFFLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFVBQVUsQ0FBQztZQUMvQyxPQUFPLE9BQU8sQ0FBQztRQUNoQixDQUFDLENBQUMsQ0FBQztRQUNILE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7VUFHRztJQUNLLDBCQUEwQixDQUFFLFVBQXNDO1FBRXpFLE1BQU0sVUFBVSxHQUFHLElBQUksR0FBRyxFQUF3QixDQUFDO1FBRW5ELHFDQUFxQztRQUNyQyxLQUFLLE1BQU0sS0FBSyxJQUFJLFVBQVUsQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUMzQyxJQUFJLEtBQUssQ0FBQyxJQUFJLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssTUFBTSxJQUFJLEtBQUssQ0FBQyxJQUFJLEVBQUUsQ0FBQztnQkFDM0YsdURBQXVEO2dCQUN2RCxJQUFJLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztvQkFDeEMsTUFBTSxRQUFRLEdBQUcsRUFBRSxDQUFDLFlBQVksQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQzt3QkFDcEQsQ0FBQyxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUk7d0JBQzFCLENBQUMsQ0FBQyxFQUFFLENBQUM7b0JBRU4saUVBQWlFO29CQUNqRSxNQUFNLElBQUksR0FBRyxRQUFRO3dCQUNwQixDQUFDLENBQUMsSUFBSSxDQUFDLGdDQUFnQyxDQUFDLFFBQVEsRUFBRSxJQUFJLENBQUMseUJBQXlCLENBQUM7d0JBQ2pGLENBQUMsQ0FBQyxTQUFTLENBQUM7b0JBQ2IsSUFBSSxJQUFJLEVBQUUsQ0FBQzt3QkFDVixNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsK0JBQStCLENBQUMsSUFBSSxDQUFDLENBQUM7d0JBQ2xFLEtBQUssTUFBTSxDQUFFLFFBQVEsRUFBRSxJQUFJLENBQUUsSUFBSSxjQUFjLEVBQUUsQ0FBQzs0QkFDakQsVUFBVSxDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLENBQUM7d0JBQ2hDLENBQUM7b0JBQ0YsQ0FBQztnQkFDRixDQUFDO2dCQUNELCtFQUErRTtxQkFDMUUsSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7b0JBQzNDLEtBQUssTUFBTSxNQUFNLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxPQUFPLEVBQUUsQ0FBQzt3QkFDekMsSUFBSSxFQUFFLENBQUMsbUJBQW1CLENBQUMsTUFBTSxDQUFDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQzs0QkFDcEUsTUFBTSxRQUFRLEdBQUcsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7NEJBQ2xDLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxDQUFDOzRCQUN6QyxVQUFVLENBQUMsR0FBRyxDQUFDLFFBQVEsRUFBRTtnQ0FDeEIsSUFBSSxFQUFPLFFBQVE7Z0NBQ25CLElBQUk7Z0NBQ0osUUFBUSxFQUFHLENBQUMsQ0FBQyxNQUFNLENBQUMsYUFBYTs2QkFDakMsQ0FBQyxDQUFDO3dCQUNKLENBQUM7b0JBQ0YsQ0FBQztnQkFDRixDQUFDO2dCQUNELGtEQUFrRDtnQkFDbEQsTUFBTTtZQUNQLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxVQUFVLENBQUM7SUFDbkIsQ0FBQztJQUVEOztVQUVHO0lBQ0g7O09BRUc7SUFDSyxTQUFTLENBQUUsUUFBc0I7UUFDeEMsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQ2YsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELFFBQVEsUUFBUSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ3hCLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxhQUFhO2dCQUMvQixPQUFPLFFBQVEsQ0FBQztZQUNqQixLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsYUFBYTtnQkFDL0IsT0FBTyxRQUFRLENBQUM7WUFDakIsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGNBQWM7Z0JBQ2hDLE9BQU8sU0FBUyxDQUFDO1lBQ2xCLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxnQkFBZ0I7Z0JBQ2xDLE9BQU8sV0FBVyxDQUFDO1lBQ3BCLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxXQUFXO2dCQUM3QixPQUFPLE1BQU0sQ0FBQztZQUNmLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxVQUFVO2dCQUM1QixPQUFPLEtBQUssQ0FBQztZQUNkLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxjQUFjO2dCQUNoQyxPQUFPLFNBQVMsQ0FBQztZQUNsQixLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVztnQkFDN0IsT0FBTyxNQUFNLENBQUM7WUFDZixLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsU0FBUztnQkFDM0IsT0FBTyxTQUFXLElBQUksQ0FBQyxTQUFTLENBQUUsUUFBNkIsQ0FBQyxXQUFXLENBQUcsR0FBRyxDQUFDO1lBQ25GLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxXQUFXLENBQUMsQ0FBQyxDQUFDO2dCQUNoQyxnRUFBZ0U7Z0JBQ2hFLE1BQU0sT0FBTyxHQUFHLFFBQThCLENBQUM7Z0JBQy9DLE1BQU0sS0FBSyxHQUFhLEVBQUUsQ0FBQztnQkFDM0IsS0FBSyxNQUFNLE1BQU0sSUFBSSxPQUFPLENBQUMsT0FBTyxFQUFFLENBQUM7b0JBQ3RDLElBQUksRUFBRSxDQUFDLG1CQUFtQixDQUFDLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7d0JBQ3BFLE1BQU0sUUFBUSxHQUFHLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO3dCQUNsQyxNQUFNLFFBQVEsR0FBRyxNQUFNLENBQUMsYUFBYSxDQUFDLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQzt3QkFDakQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7d0JBQ3pDLEtBQUssQ0FBQyxJQUFJLENBQUMsR0FBRyxRQUFRLEdBQUcsUUFBUSxLQUFLLElBQUksRUFBRSxDQUFDLENBQUM7b0JBQy9DLENBQUM7Z0JBQ0YsQ0FBQztnQkFDRCxPQUFPLEtBQUssS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1lBQ2xDLENBQUM7WUFDRCxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVyxDQUFDLENBQUMsQ0FBQztnQkFDaEMseURBQXlEO2dCQUN6RCxNQUFNLEVBQUUsT0FBTyxFQUFFLEdBQUksUUFBK0IsQ0FBQztnQkFDckQsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7b0JBQ2pDLG1FQUFtRTtvQkFDbkUsT0FBTyxJQUFJLE9BQU8sQ0FBQyxJQUFJLEdBQUcsQ0FBQztnQkFDNUIsQ0FBQztnQkFDRCxJQUFJLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO29CQUNsQyxPQUFPLE9BQU8sQ0FBQyxJQUFJLENBQUM7Z0JBQ3JCLENBQUM7Z0JBQ0QsSUFBSSxPQUFPLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVyxFQUFFLENBQUM7b0JBQ2hELE9BQU8sTUFBTSxDQUFDO2dCQUNmLENBQUM7Z0JBQ0QsSUFBSSxPQUFPLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsWUFBWSxFQUFFLENBQUM7b0JBQ2pELE9BQU8sT0FBTyxDQUFDO2dCQUNoQixDQUFDO2dCQUNELElBQUksT0FBTyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFdBQVcsRUFBRSxDQUFDO29CQUNoRCxPQUFPLE1BQU0sQ0FBQztnQkFDZixDQUFDO2dCQUNELE9BQU8sU0FBUyxDQUFDO1lBQ2xCLENBQUM7WUFDRCxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsYUFBYSxDQUFDLENBQUMsQ0FBQztnQkFDbEMsc0VBQXNFO2dCQUN0RSxNQUFNLE9BQU8sR0FBRyxRQUFnQyxDQUFDO2dCQUVqRCxzRUFBc0U7Z0JBQ3RFLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxPQUFPLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztvQkFDMUMsTUFBTSxpQkFBaUIsR0FBRyxJQUFJLENBQUMsMkJBQTJCLENBQUMsT0FBTyxDQUFDLENBQUM7b0JBQ3BFLElBQUksaUJBQWlCLEtBQUssU0FBUyxFQUFFLENBQUM7d0JBQ3JDLE9BQU8saUJBQWlCLENBQUM7b0JBQzFCLENBQUM7b0JBQ0QsNERBQTREO29CQUM1RCxPQUFPLFNBQVMsQ0FBQztnQkFDbEIsQ0FBQztnQkFFRCxNQUFNLFFBQVEsR0FBRyxFQUFFLENBQUMsWUFBWSxDQUFDLE9BQU8sQ0FBQyxRQUFRLENBQUMsQ0FBQyxDQUFDLENBQUMsT0FBTyxDQUFDLFFBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQztnQkFFdkYsK0RBQStEO2dCQUMvRCxpRUFBaUU7Z0JBQ2pFLHVEQUF1RDtnQkFDdkQsTUFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLDBCQUEwQixDQUFDLFFBQVEsRUFBRSxPQUFPLENBQUMsYUFBYSxFQUFFLE9BQU8sQ0FBQyxDQUFDO2dCQUM1RixJQUFJLFNBQVMsS0FBSyxTQUFTLEVBQUUsQ0FBQztvQkFDN0IsT0FBTyxTQUFTLENBQUM7Z0JBQ2xCLENBQUM7Z0JBRUQsK0JBQStCO2dCQUMvQixNQUFNLFFBQVEsR0FBRyxDQUFDLE9BQU8sQ0FBQyxhQUFhLElBQUksRUFBRSxDQUFDLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDO2dCQUMvRSxPQUFPLEdBQUcsUUFBUSxJQUFJLFFBQVEsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQztZQUM5QyxDQUFDO1lBQ0QsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFNBQVMsQ0FBQyxDQUFDLENBQUM7Z0JBQzlCLDBDQUEwQztnQkFDMUMsTUFBTSxTQUFTLEdBQUcsUUFBNEIsQ0FBQztnQkFDL0MsTUFBTSxLQUFLLEdBQUcsU0FBUyxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7Z0JBQzFELE9BQU8sS0FBSyxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQztZQUMxQixDQUFDO1lBQ0QsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGdCQUFnQixDQUFDLENBQUMsQ0FBQztnQkFDckMsK0NBQStDO2dCQUMvQyxNQUFNLGdCQUFnQixHQUFHLFFBQW1DLENBQUM7Z0JBQzdELE1BQU0sS0FBSyxHQUFHLGdCQUFnQixDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7Z0JBQ2pFLE9BQU8sS0FBSyxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQztZQUMxQixDQUFDO1lBQ0QsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFNBQVMsQ0FBQyxDQUFDLENBQUM7Z0JBQzlCLDJDQUEyQztnQkFDM0MsTUFBTSxTQUFTLEdBQUcsUUFBNEIsQ0FBQztnQkFDL0MsTUFBTSxRQUFRLEdBQUcsU0FBUyxDQUFDLFFBQVEsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLElBQW1CLENBQUMsQ0FBQyxDQUFDO2dCQUNyRixPQUFPLElBQUksUUFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDO1lBQ25DLENBQUM7WUFDRCxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsWUFBWSxDQUFDLENBQUMsQ0FBQztnQkFDakMsNENBQTRDO2dCQUM1QyxNQUFNLFlBQVksR0FBRyxRQUErQixDQUFDO2dCQUNyRCxPQUFPLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFHLEdBQUcsQ0FBQztZQUNsRCxDQUFDO1lBQ0QsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFFBQVEsQ0FBQyxDQUFDLENBQUM7Z0JBQzdCLDRCQUE0QjtnQkFDNUIsTUFBTSxRQUFRLEdBQUcsUUFBMkIsQ0FBQztnQkFDN0MsT0FBTyxNQUFRLElBQUksQ0FBQyxTQUFTLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDaEQsQ0FBQztZQUNELEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxpQkFBaUIsQ0FBQyxDQUFDLENBQUM7Z0JBQ3RDLHNDQUFzQztnQkFDdEMsT0FBTyxJQUFJLENBQUMsU0FBUyxDQUFFLFFBQXFDLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDcEUsQ0FBQztZQUNELEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxpQkFBaUIsQ0FBQyxDQUFDLENBQUM7Z0JBQ3RDLDhCQUE4QjtnQkFDOUIsTUFBTSxPQUFPLEdBQUcsUUFBb0MsQ0FBQztnQkFDckQsdURBQXVEO2dCQUN2RCwyREFBMkQ7Z0JBQzNELDREQUE0RDtnQkFDNUQsd0NBQXdDO2dCQUN4Qyx3QkFBd0I7Z0JBQ3hCLElBQUksVUFBVSxHQUFnQixPQUFPLENBQUMsVUFBVSxDQUFDO2dCQUNqRCxPQUFPLEVBQUUsQ0FBQyx1QkFBdUIsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO29CQUMvQyxVQUFVLEdBQUcsVUFBVSxDQUFDLElBQUksQ0FBQztnQkFDOUIsQ0FBQztnQkFDRCxrRUFBa0U7Z0JBQ2xFLHNEQUFzRDtnQkFDdEQsK0RBQStEO2dCQUMvRCw0REFBNEQ7Z0JBQzVELG9DQUFvQztnQkFDcEMsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLFVBQVUsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsVUFBVSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7b0JBQzVFLE1BQU0sU0FBUyxHQUFHLFVBQVUsQ0FBQyxRQUFRLENBQUMsSUFBSSxDQUFDO29CQUMzQyxNQUFNLFlBQVksR0FBRyxJQUFJLENBQUMsd0JBQXdCLENBQUMsU0FBUyxFQUFFLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxDQUFDO29CQUM5RixNQUFNLFFBQVEsR0FBRyxZQUFZLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxZQUFZLENBQUMsQ0FBQyxDQUFDLENBQUMsU0FBUyxDQUFDO29CQUNuRixJQUFJLENBQUMsUUFBUSxFQUFFLENBQUM7d0JBQ2YsT0FBTyxTQUFTLENBQUM7b0JBQ2xCLENBQUM7b0JBQ0QsSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsT0FBTyxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxPQUFPLENBQUMsU0FBUyxDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7d0JBQy9GLE1BQU0sWUFBWSxHQUFHLFFBQVEsQ0FBQyxPQUFPLENBQUMsU0FBUyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUM7d0JBQ2xFLE1BQU0sT0FBTyxHQUFHLFFBQVEsQ0FBRSxZQUFZLENBQUUsQ0FBQzt3QkFDekMsTUFBTSxhQUFhLEdBQUcsT0FBTyxLQUFLLFNBQVMsQ0FBQyxDQUFDLENBQUMsU0FBUyxDQUFDLENBQUMsQ0FBQyxPQUFPLENBQUM7d0JBQ2xFLE9BQU8sYUFBYSxDQUFDO29CQUN0QixDQUFDO29CQUNELE1BQU0sV0FBVyxHQUFHLFFBQVEsQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7b0JBQ3pDLE9BQU8sV0FBVyxDQUFDO2dCQUNwQixDQUFDO2dCQUNELElBQUksVUFBVSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsVUFBVSxDQUFDLENBQUM7Z0JBQzVDLE1BQU0sU0FBUyxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsT0FBTyxDQUFDLFNBQVMsQ0FBQyxDQUFDO2dCQUNwRCwyRUFBMkU7Z0JBQzNFLElBQUksVUFBVSxLQUFLLFFBQVEsSUFBSSxFQUFFLENBQUMsbUJBQW1CLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztvQkFDbkUsTUFBTSxPQUFPLEdBQUcsRUFBRSxDQUFDLFlBQVksQ0FBQyxVQUFVLENBQUMsUUFBUSxDQUFDLENBQUMsQ0FBQyxDQUFDLFVBQVUsQ0FBQyxRQUFRLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUM7b0JBQ3JGLElBQUksT0FBTyxFQUFFLENBQUM7d0JBQ2IsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLGdDQUFnQyxDQUFDLE9BQU8sRUFBRSxJQUFJLENBQUMseUJBQXlCLENBQUMsQ0FBQzt3QkFDNUYsSUFBSSxJQUFJLEVBQUUsQ0FBQzs0QkFDVixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsK0JBQStCLENBQUMsSUFBSSxDQUFDLENBQUM7NEJBQzVELElBQUksUUFBUSxFQUFFLENBQUM7Z0NBQ2QsVUFBVSxHQUFHLFFBQVEsQ0FBQzs0QkFDdkIsQ0FBQzt3QkFDRixDQUFDO29CQUNGLENBQUM7Z0JBQ0YsQ0FBQztnQkFDRCx5REFBeUQ7Z0JBQ3pELCtEQUErRDtnQkFDL0QsNkRBQTZEO2dCQUM3RCwyREFBMkQ7Z0JBQzNELHdDQUF3QztnQkFDeEMsTUFBTSxnQkFBZ0IsR0FBRyxVQUFVLEtBQUssU0FBUyxJQUFJLFVBQVUsS0FBSyxRQUFRLENBQUM7Z0JBQzdFLE1BQU0sZUFBZSxHQUFHLFNBQVMsS0FBSyxTQUFTLENBQUM7Z0JBQ2hELElBQUksZ0JBQWdCLElBQUksZUFBZSxFQUFFLENBQUM7b0JBQ3pDLE9BQU8sU0FBUyxDQUFDO2dCQUNsQixDQUFDO2dCQUNELE9BQU8sR0FBRyxVQUFVLElBQUksU0FBUyxHQUFHLENBQUM7WUFDdEMsQ0FBQztZQUNELEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxZQUFZLENBQUMsQ0FBQyxDQUFDO2dCQUNqQywyQ0FBMkM7Z0JBQzNDLE1BQU0sTUFBTSxHQUFHLFFBQStCLENBQUM7Z0JBQy9DLE1BQU0sUUFBUSxHQUFHLEVBQUUsQ0FBQyxVQUFVLENBQUUsTUFBTSxDQUFDLFFBQVEsQ0FBRSxDQUFDO2dCQUNsRCxPQUFPLEdBQUcsUUFBUSxJQUFJLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDckQsQ0FBQztZQUNELEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxTQUFTLENBQUMsQ0FBQyxDQUFDO2dCQUM5QixpRUFBaUU7Z0JBQ2pFLGlFQUFpRTtnQkFDakUsNERBQTREO2dCQUM1RCxpRUFBaUU7Z0JBQ2pFLCtEQUErRDtnQkFDL0QsbUJBQW1CO2dCQUNuQixNQUFNLFNBQVMsR0FBRyxRQUE0QixDQUFDO2dCQUMvQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsU0FBUyxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7b0JBQ3pDLE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxTQUFTLENBQUMsUUFBUSxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMseUJBQXlCLENBQUMsQ0FBQztvQkFDbEcsSUFBSSxLQUFLLEVBQUUsQ0FBQzt3QkFDWCxPQUFPLEtBQUssQ0FBQztvQkFDZCxDQUFDO2dCQUNGLENBQUM7Z0JBQ0QsT0FBTyxTQUFTLENBQUM7WUFDbEIsQ0FBQztZQUNEO2dCQUNDLG9EQUFvRDtnQkFDcEQsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztJQUNGLENBQUM7SUFFRDs7O1VBR0c7SUFDSyxlQUFlLENBQUUsTUFBNEIsRUFBRSxrQkFBd0M7UUFDOUYsd0RBQXdEO1FBQ3hELElBQUksTUFBTSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ2pCLE9BQU8sSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDcEMsQ0FBQztRQUVELG9FQUFvRTtRQUNwRSxJQUFJLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUNqQixPQUFPLElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxNQUFNLENBQUMsSUFBSSxFQUFFLGtCQUFrQixDQUFDLENBQUM7UUFDdEUsQ0FBQztRQUVELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7VUFFRztJQUNLLHVCQUF1QixDQUFFLElBQWMsRUFBRSxrQkFBd0M7UUFDeEYsTUFBTSxXQUFXLEdBQUcsSUFBSSxHQUFHLEVBQVUsQ0FBQztRQUV0QyxNQUFNLEtBQUssR0FBRyxDQUFDLElBQWEsRUFBUSxFQUFFO1lBQ3JDLElBQUksRUFBRSxDQUFDLGlCQUFpQixDQUFDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztnQkFDbkQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLElBQUksQ0FBQyxVQUFVLEVBQUUsU0FBUyxFQUFFLGtCQUFrQixDQUFDLENBQUM7Z0JBQzNGLElBQUksSUFBSSxLQUFLLFNBQVMsRUFBRSxDQUFDO29CQUN4QixXQUFXLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO2dCQUN2QixDQUFDO1lBQ0YsQ0FBQztZQUNELEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxFQUFFLEtBQUssQ0FBQyxDQUFDO1FBQzlCLENBQUMsQ0FBQztRQUVGLEtBQUssQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUVaLElBQUksV0FBVyxDQUFDLElBQUksS0FBSyxDQUFDLEVBQUUsQ0FBQztZQUM1QixPQUFPLE1BQU0sQ0FBQztRQUNmLENBQUM7UUFDRCxJQUFJLFdBQVcsQ0FBQyxJQUFJLEtBQUssQ0FBQyxFQUFFLENBQUM7WUFDNUIsT0FBTyxLQUFLLENBQUMsSUFBSSxDQUFDLFdBQVcsQ0FBQyxDQUFFLENBQUMsQ0FBRSxDQUFDO1FBQ3JDLENBQUM7UUFDRCxPQUFPLEtBQUssQ0FBQyxJQUFJLENBQUMsV0FBVyxDQUFDLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxDQUFDO0lBQzVDLENBQUM7SUFFRDs7T0FFRztJQUNLLHdCQUF3QixDQUMvQixXQUEwQixFQUMxQixXQUFpQyxFQUNqQyxrQkFBd0M7UUFFeEMsUUFBUSxXQUFXLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDM0IsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGFBQWE7Z0JBQy9CLE9BQU8sUUFBUSxDQUFDO1lBQ2pCLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxjQUFjO2dCQUNoQyxPQUFPLFFBQVEsQ0FBQztZQUNqQixLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVyxDQUFDO1lBQy9CLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxZQUFZO2dCQUM5QixPQUFPLFNBQVMsQ0FBQztZQUNsQixLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVztnQkFDN0IsT0FBTyxNQUFNLENBQUM7WUFDZixLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsZ0JBQWdCO2dCQUNsQyxPQUFPLFdBQVcsQ0FBQztZQUNwQixLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsc0JBQXNCO2dCQUN4QyxPQUFPLGdCQUFnQixDQUFDO1lBQ3pCLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyx1QkFBdUI7Z0JBQ3pDLE9BQU8sUUFBUSxDQUFDO1lBQ2pCLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxhQUFhLENBQUMsQ0FBQyxDQUFDO2dCQUNsQyxxQ0FBcUM7Z0JBQ3JDLE1BQU0sT0FBTyxHQUFHLFdBQStCLENBQUM7Z0JBQ2hELElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztvQkFDekMsTUFBTSxlQUFlLEdBQUcsT0FBTyxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUM7b0JBQ2hELDZEQUE2RDtvQkFDN0QsNERBQTREO29CQUM1RCw4REFBOEQ7b0JBQzlELElBQUksT0FBTyxDQUFDLGFBQWEsSUFBSSxPQUFPLENBQUMsYUFBYSxDQUFDLE1BQU0sR0FBRyxDQUFDLEVBQUUsQ0FBQzt3QkFDL0QsTUFBTSxRQUFRLEdBQUcsT0FBTyxDQUFDLGFBQWEsQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUM7d0JBQ3ZFLE9BQU8sR0FBRyxlQUFlLElBQUksUUFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDO29CQUNyRCxDQUFDO29CQUNELDREQUE0RDtvQkFDNUQsZ0VBQWdFO29CQUNoRSxNQUFNLGdCQUFnQixHQUFHLDJCQUEyQixDQUFDLEdBQUcsQ0FBQyxlQUFlLENBQUMsQ0FBQztvQkFDMUUsSUFBSSxnQkFBZ0IsRUFBRSxDQUFDO3dCQUN0QixPQUFPLGdCQUFnQixDQUFDO29CQUN6QixDQUFDO29CQUNELE9BQU8sZUFBZSxDQUFDO2dCQUN4QixDQUFDO2dCQUNELE9BQU8sUUFBUSxDQUFDO1lBQ2pCLENBQUM7WUFDRCxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsZ0JBQWdCLENBQUMsQ0FBQyxDQUFDO2dCQUNyQywyREFBMkQ7Z0JBQzNELE1BQU0sVUFBVSxHQUFHLFdBQWtDLENBQUM7Z0JBQ3RELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxVQUFVLENBQUMsSUFBSSxFQUFFLFdBQVcsRUFBRSxrQkFBa0IsQ0FBQyxDQUFDO2dCQUNqRyxNQUFNLFNBQVMsR0FBRyxJQUFJLENBQUMsd0JBQXdCLENBQUMsVUFBVSxDQUFDLEtBQUssRUFBRSxXQUFXLEVBQUUsa0JBQWtCLENBQUMsQ0FBQztnQkFFbkcsdUNBQXVDO2dCQUN2QyxNQUFNLFFBQVEsR0FBRyxVQUFVLENBQUMsYUFBYSxDQUFDLElBQUksQ0FBQztnQkFDL0MsSUFBSSxRQUFRLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxhQUFhO29CQUN2QyxRQUFRLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxVQUFVO29CQUNyQyxRQUFRLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxVQUFVO29CQUNyQyxRQUFRLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxZQUFZLEVBQUUsQ0FBQztvQkFDOUMsbURBQW1EO29CQUNuRCxJQUFJLENBQUMsUUFBUSxLQUFLLFFBQVEsSUFBSSxRQUFRLEtBQUssU0FBUyxDQUFDO3dCQUNoRCxDQUFDLFNBQVMsS0FBSyxRQUFRLElBQUksU0FBUyxLQUFLLFNBQVMsQ0FBQyxFQUFFLENBQUM7d0JBQzFELE9BQU8sUUFBUSxDQUFDO29CQUNqQixDQUFDO2dCQUNGLENBQUM7Z0JBQ0QsSUFBSSxRQUFRLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxTQUFTLEVBQUUsQ0FBQztvQkFDMUMsK0NBQStDO29CQUMvQyxJQUFJLFFBQVEsS0FBSyxRQUFRLElBQUksU0FBUyxLQUFLLFFBQVEsRUFBRSxDQUFDO3dCQUNyRCxPQUFPLFFBQVEsQ0FBQztvQkFDakIsQ0FBQztvQkFDRCxJQUFJLFFBQVEsS0FBSyxRQUFRLElBQUksU0FBUyxLQUFLLFFBQVEsRUFBRSxDQUFDO3dCQUNyRCxPQUFPLFFBQVEsQ0FBQztvQkFDakIsQ0FBQztnQkFDRixDQUFDO2dCQUNELE9BQU8sU0FBUyxDQUFDO1lBQ2xCLENBQUM7WUFDRCxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsd0JBQXdCLENBQUMsQ0FBQyxDQUFDO2dCQUM3QyxrREFBa0Q7Z0JBQ2xELElBQUksV0FBVyxFQUFFLENBQUM7b0JBQ2pCLE1BQU0sV0FBVyxHQUFHLElBQUksQ0FBQyxzQkFBc0IsQ0FBQyxXQUFXLENBQUMsQ0FBQztvQkFDN0QsSUFBSSxXQUFXLEVBQUUsQ0FBQzt3QkFDakIsTUFBTSxJQUFJLEdBQUcsV0FBVyxDQUFDLEdBQUcsQ0FBQyxXQUFXLENBQUMsQ0FBQzt3QkFDMUMsSUFBSSxJQUFJLEVBQUUsQ0FBQzs0QkFDVixPQUFPLElBQUksQ0FBQzt3QkFDYixDQUFDO29CQUNGLENBQUM7Z0JBQ0YsQ0FBQztnQkFDRCx5REFBeUQ7Z0JBQ3pELE1BQU0sVUFBVSxHQUFHLFdBQTBDLENBQUM7Z0JBQzlELElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLFVBQVUsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO29CQUMxRCxNQUFNLFNBQVMsR0FBRyxVQUFVLENBQUMsVUFBVSxDQUFDO29CQUN4Qyw2QkFBNkI7b0JBQzdCLElBQUksU0FBUyxHQUFHLEVBQUUsQ0FBQztvQkFDbkIsSUFBSSxTQUFTLENBQUMsVUFBVSxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFdBQVcsRUFBRSxDQUFDO3dCQUM3RCxTQUFTLEdBQUcsTUFBTSxDQUFDO29CQUNwQixDQUFDO3lCQUFNLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxTQUFTLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQzt3QkFDbEQsU0FBUyxHQUFHLFNBQVMsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDO29CQUN2QyxDQUFDO29CQUNELE1BQU0sT0FBTyxHQUFHLFNBQVMsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO29CQUNwQyxNQUFNLFNBQVMsR0FBRyxVQUFVLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztvQkFDdkMsMEJBQTBCO29CQUMxQixJQUFJLFNBQVMsS0FBSyxNQUFNLElBQUksT0FBTyxLQUFLLEtBQUssSUFBSSxTQUFTLEtBQUssTUFBTSxFQUFFLENBQUM7d0JBQ3ZFLE9BQU8sUUFBUSxDQUFDO29CQUNqQixDQUFDO2dCQUNGLENBQUM7Z0JBQ0QsT0FBTyxTQUFTLENBQUM7WUFDbEIsQ0FBQztZQUNELEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxVQUFVLENBQUMsQ0FBQyxDQUFDO2dCQUMvQixpREFBaUQ7Z0JBQ2pELElBQUksV0FBVyxFQUFFLENBQUM7b0JBQ2pCLE1BQU0sSUFBSSxHQUFJLFdBQTZCLENBQUMsSUFBSSxDQUFDO29CQUNqRCxNQUFNLElBQUksR0FBRyxXQUFXLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO29CQUNuQyxJQUFJLElBQUksRUFBRSxDQUFDO3dCQUNWLE9BQU8sSUFBSSxDQUFDO29CQUNiLENBQUM7Z0JBQ0YsQ0FBQztnQkFDRCxPQUFPLFNBQVMsQ0FBQztZQUNsQixDQUFDO1lBQ0QsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLHVCQUF1QixDQUFDLENBQUMsQ0FBQztnQkFDNUMsd0RBQXdEO2dCQUN4RCw2REFBNkQ7Z0JBQzdELDREQUE0RDtnQkFDNUQsNkRBQTZEO2dCQUM3RCwwREFBMEQ7Z0JBQzFELG1EQUFtRDtnQkFDbkQsTUFBTSxhQUFhLEdBQUcsV0FBeUMsQ0FBQztnQkFDaEUsTUFBTSxRQUFRLEdBQUcsYUFBYSxDQUFDLGtCQUFrQixDQUFDO2dCQUNsRCxJQUFJLENBQUMsUUFBUSxJQUFJLENBQUMsRUFBRSxDQUFDLGdCQUFnQixDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7b0JBQ2pELE9BQU8sU0FBUyxDQUFDO2dCQUNsQixDQUFDO2dCQUNELE1BQU0sWUFBWSxHQUFHLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxhQUFhLENBQUMsVUFBVSxDQUFDLENBQUM7Z0JBQ3hFLElBQUksQ0FBQyxZQUFZLEVBQUUsQ0FBQztvQkFDbkIsT0FBTyxTQUFTLENBQUM7Z0JBQ2xCLENBQUM7Z0JBQ0QsTUFBTSxPQUFPLEdBQUcsWUFBWSxDQUFDLFFBQVEsQ0FBRSxRQUFRLENBQUMsUUFBUSxDQUFDLElBQUksRUFBRSxFQUFFLENBQUMsQ0FBRSxDQUFDO2dCQUNyRSxJQUFJLENBQUMsT0FBTyxJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsT0FBTyxDQUFDLEVBQUUsQ0FBQztvQkFDN0MsT0FBTyxTQUFTLENBQUM7Z0JBQ2xCLENBQUM7Z0JBQ0QsTUFBTSxPQUFPLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLE9BQU8sQ0FBQyxDQUFDO2dCQUN0RCxNQUFNLGFBQWEsR0FBRyxPQUFPLElBQUksU0FBUyxDQUFDO2dCQUMzQyxPQUFPLGFBQWEsQ0FBQztZQUN0QixDQUFDO1lBQ0QsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGNBQWMsQ0FBQyxDQUFDLENBQUM7Z0JBQ25DLDBEQUEwRDtnQkFDMUQsTUFBTSxRQUFRLEdBQUcsV0FBZ0MsQ0FBQztnQkFDbEQsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7b0JBQ3hELE1BQU0sVUFBVSxHQUFHLFFBQVEsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztvQkFDakQsTUFBTSxPQUFPLEdBQUcsRUFBRSxDQUFDLFlBQVksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLFVBQVUsQ0FBQzt3QkFDOUQsQ0FBQyxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsVUFBVSxDQUFDLElBQUk7d0JBQ3JDLENBQUMsQ0FBQyxFQUFFLENBQUM7b0JBRU4sdUJBQXVCO29CQUN2QixJQUFJLE9BQU8sS0FBSyxNQUFNLElBQUksVUFBVSxLQUFLLEtBQUssRUFBRSxDQUFDO3dCQUNoRCxPQUFPLFFBQVEsQ0FBQztvQkFDakIsQ0FBQztvQkFDRCxvQ0FBb0M7b0JBQ3BDLElBQUksVUFBVSxLQUFLLFVBQVUsSUFBSSxVQUFVLEtBQUssU0FBUyxFQUFFLENBQUM7d0JBQzNELE9BQU8sUUFBUSxDQUFDO29CQUNqQixDQUFDO29CQUNELDZEQUE2RDtvQkFDN0QsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO3dCQUNuRSxNQUFNLFNBQVMsR0FBRyxRQUFRLENBQUMsVUFBVSxDQUFDLFVBQVUsQ0FBQzt3QkFDakQscURBQXFEO3dCQUNyRCxJQUFJLFNBQVMsR0FBRyxFQUFFLENBQUM7d0JBQ25CLElBQUksU0FBUyxDQUFDLFVBQVUsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxXQUFXLEVBQUUsQ0FBQzs0QkFDN0QsU0FBUyxHQUFHLE1BQU0sQ0FBQzt3QkFDcEIsQ0FBQzs2QkFBTSxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsU0FBUyxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7NEJBQ2xELFNBQVMsR0FBRyxTQUFTLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQzt3QkFDdkMsQ0FBQzt3QkFDRCxNQUFNLE9BQU8sR0FBRyxTQUFTLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQzt3QkFDcEMsd0JBQXdCO3dCQUN4QixJQUFJLFNBQVMsS0FBSyxNQUFNLElBQUksT0FBTyxLQUFLLEtBQUssRUFBRSxDQUFDOzRCQUMvQyx3REFBd0Q7NEJBQ3hELElBQUksWUFBWSxHQUFHLFNBQVMsQ0FBQzs0QkFDN0IsSUFBSSxrQkFBa0IsRUFBRSxDQUFDO2dDQUN4QixNQUFNLE9BQU8sR0FBRyxrQkFBa0IsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLENBQUM7Z0NBQzlDLElBQUksT0FBTyxJQUFJLE9BQU8sQ0FBQyxVQUFVLENBQUMsTUFBTSxDQUFDLEVBQUUsQ0FBQztvQ0FDM0MsMkJBQTJCO29DQUMzQixNQUFNLEtBQUssR0FBRyxPQUFPLENBQUMsS0FBSyxDQUFDLHFCQUFxQixDQUFDLENBQUM7b0NBQ25ELElBQUksS0FBSyxFQUFFLENBQUM7d0NBQ1gsQ0FBRSxBQUFELEVBQUcsWUFBWSxDQUFFLEdBQUcsS0FBSyxDQUFDO29DQUM1QixDQUFDO2dDQUNGLENBQUM7NEJBQ0YsQ0FBQzs0QkFDRCxJQUFJLFVBQVUsS0FBSyxLQUFLO2dDQUFFLE9BQU8sU0FBUyxDQUFDOzRCQUMzQyxJQUFJLFVBQVUsS0FBSyxLQUFLO2dDQUFFLE9BQU8sTUFBTSxDQUFDOzRCQUN4QyxJQUFJLFVBQVUsS0FBSyxLQUFLO2dDQUFFLE9BQU8sWUFBWSxDQUFDOzRCQUM5QyxJQUFJLFVBQVUsS0FBSyxRQUFRO2dDQUFFLE9BQU8sU0FBUyxDQUFDOzRCQUM5QyxJQUFJLFVBQVUsS0FBSyxPQUFPO2dDQUFFLE9BQU8sTUFBTSxDQUFDOzRCQUMxQyxJQUFJLFVBQVUsS0FBSyxRQUFRO2dDQUFFLE9BQU8sb0JBQW9CLFlBQVksR0FBRyxDQUFDOzRCQUN4RSxJQUFJLFVBQVUsS0FBSyxNQUFNO2dDQUFFLE9BQU8sMEJBQTBCLENBQUM7NEJBQzdELElBQUksVUFBVSxLQUFLLFNBQVM7Z0NBQUUsT0FBTyw2QkFBNkIsWUFBWSxJQUFJLENBQUM7d0JBQ3BGLENBQUM7b0JBQ0YsQ0FBQztvQkFDRCx1QkFBdUI7b0JBQ3ZCLElBQUksT0FBTyxLQUFLLEtBQUssSUFBSSxPQUFPLEtBQUssS0FBSyxFQUFFLENBQUM7d0JBQzVDLElBQUksVUFBVSxLQUFLLEtBQUs7NEJBQUUsT0FBTyxTQUFTLENBQUM7d0JBQzNDLElBQUksVUFBVSxLQUFLLEtBQUs7NEJBQUUsT0FBTyxNQUFNLENBQUM7d0JBQ3hDLElBQUksVUFBVSxLQUFLLEtBQUs7NEJBQUUsT0FBTyxTQUFTLENBQUM7d0JBQzNDLElBQUksVUFBVSxLQUFLLFFBQVE7NEJBQUUsT0FBTyxTQUFTLENBQUM7d0JBQzlDLElBQUksVUFBVSxLQUFLLE9BQU87NEJBQUUsT0FBTyxNQUFNLENBQUM7d0JBQzFDLElBQUksVUFBVSxLQUFLLFFBQVE7NEJBQUUsT0FBTywyQkFBMkIsQ0FBQzt3QkFDaEUsSUFBSSxVQUFVLEtBQUssTUFBTTs0QkFBRSxPQUFPLDBCQUEwQixDQUFDO3dCQUM3RCxJQUFJLFVBQVUsS0FBSyxTQUFTOzRCQUFFLE9BQU8scUNBQXFDLENBQUM7b0JBQzVFLENBQUM7Z0JBQ0YsQ0FBQztnQkFDRCxpQ0FBaUM7Z0JBQ2pDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztvQkFDMUMsTUFBTSxNQUFNLEdBQUcsUUFBUSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUM7b0JBQ3hDLElBQUksTUFBTSxLQUFLLFVBQVUsSUFBSSxNQUFNLEtBQUssWUFBWSxFQUFFLENBQUM7d0JBQ3RELE9BQU8sUUFBUSxDQUFDO29CQUNqQixDQUFDO29CQUNELElBQUksTUFBTSxLQUFLLFFBQVEsRUFBRSxDQUFDO3dCQUN6QixPQUFPLFFBQVEsQ0FBQztvQkFDakIsQ0FBQztvQkFDRCxJQUFJLE1BQU0sS0FBSyxRQUFRLEVBQUUsQ0FBQzt3QkFDekIsT0FBTyxRQUFRLENBQUM7b0JBQ2pCLENBQUM7b0JBQ0QsSUFBSSxNQUFNLEtBQUssU0FBUyxFQUFFLENBQUM7d0JBQzFCLE9BQU8sU0FBUyxDQUFDO29CQUNsQixDQUFDO2dCQUNGLENBQUM7Z0JBQ0QsT0FBTyxTQUFTLENBQUM7WUFDbEIsQ0FBQztZQUNELEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxrQkFBa0IsQ0FBQztZQUN0QyxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsNkJBQTZCLENBQUMsQ0FBQyxDQUFDO2dCQUNsRCx3RUFBd0U7Z0JBQ3hFLE9BQU8sUUFBUSxDQUFDO1lBQ2pCLENBQUM7WUFDRDtnQkFDQyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO0lBQ0YsQ0FBQztJQUVEOztjQUVJO0lBQ0ksWUFBWSxDQUFFLElBQWEsRUFBRSxVQUF5QjtRQUM3RCxxQ0FBcUM7UUFDckMsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUNqRCxJQUFJLFFBQTRCLENBQUM7WUFDakMsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7Z0JBQ3BELFFBQVEsR0FBRyxJQUFJLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsQ0FBQztZQUNsRCxDQUFDO2lCQUFNLENBQUM7Z0JBQ1AsUUFBUSxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLENBQUM7WUFDNUQsQ0FBQztZQUNELElBQUksUUFBUSxFQUFFLENBQUM7Z0JBQ2QsTUFBTSxFQUFFLElBQUksRUFBRSxTQUFTLEVBQUUsR0FBRyxFQUFFLENBQUMsNkJBQTZCLENBQzNELFVBQVUsRUFDVixJQUFJLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxDQUN6QixDQUFDO2dCQUNGLElBQUksQ0FBQyxRQUFRLENBQUMsUUFBUSxFQUFFO29CQUN2QixRQUFRLEVBQVUsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsRUFBRTtvQkFDdkUsSUFBSSxFQUFjLGVBQWU7b0JBQ2pDLElBQUksRUFBYyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDO29CQUN4RCw0REFBNEQ7b0JBQzVELDZEQUE2RDtvQkFDN0QsZUFBZSxFQUFHLElBQUksQ0FBQyxVQUFVLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDO2lCQUNuRSxDQUFDLENBQUM7Z0JBQ0gsOERBQThEO2dCQUM5RCxJQUFJLENBQUMsa0JBQWtCLENBQUMsSUFBSSxFQUFFLFFBQVEsQ0FBQyxDQUFDO2dCQUN4Qyw0QkFBNEI7Z0JBQzVCLElBQUksQ0FBQyxPQUFPLENBQUMsUUFBUSxFQUFFO29CQUN0QixRQUFRLEVBQUcsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsRUFBRTtvQkFDaEUsSUFBSSxFQUFPLGVBQWU7b0JBQzFCLElBQUksRUFBTyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDO29CQUNqRCxPQUFPLEVBQUksZ0JBQWdCO2lCQUMzQixDQUFDLENBQUM7WUFDSixDQUFDO1FBQ0YsQ0FBQztRQUVELDBEQUEwRDtRQUMxRCxJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ3pDLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1lBQ2hDLG9EQUFvRDtZQUNwRCw0REFBNEQ7WUFDNUQsMERBQTBEO1lBQzFELCtEQUErRDtZQUMvRCw2REFBNkQ7WUFDN0QsOENBQThDO1lBQzlDLElBQUksUUFBUSxLQUFLLE9BQU8sSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO2dCQUM5RCxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLENBQUM7Z0JBQ3BFLE1BQU0sVUFBVSxHQUFHLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLElBQUksSUFBSSxDQUFDLE1BQU0sQ0FBQyxVQUFVLEtBQUssSUFBSSxDQUFDO2dCQUN2RixJQUFJLFVBQVUsRUFBRSxDQUFDO29CQUNoQixJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7d0JBQ2pCLE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQzt3QkFDRixJQUFJLENBQUMsUUFBUSxDQUFDLFVBQVUsRUFBRTs0QkFDekIsUUFBUSxFQUFVLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUU7NEJBQ3ZFLElBQUksRUFBYyxlQUFlOzRCQUNqQyxJQUFJLEVBQWMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQzs0QkFDeEQsZUFBZSxFQUFHLElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsRUFBRSxHQUFHLENBQUM7eUJBQ3hELENBQUMsQ0FBQztvQkFDSixDQUFDO29CQUNELElBQUksQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7Z0JBQzNDLENBQUM7WUFDRixDQUFDO1lBQ0QsaURBQWlEO1lBQ2pELElBQUksUUFBUSxJQUFJLElBQUksQ0FBQyxnQkFBZ0IsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO2dCQUNqRCwwREFBMEQ7Z0JBQzFELDJEQUEyRDtnQkFDM0QsNERBQTREO2dCQUM1RCx1REFBdUQ7Z0JBQ3ZELDJEQUEyRDtnQkFDM0QsNERBQTREO2dCQUM1RCw0REFBNEQ7Z0JBQzVELGdCQUFnQjtnQkFDaEIsTUFBTSxXQUFXLEdBQUcsRUFBRSxDQUFDLGVBQWUsQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLElBQUksSUFBSSxDQUFDLE1BQU0sQ0FBQyxVQUFVLEtBQUssSUFBSSxDQUFDO2dCQUN2RixNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7Z0JBQ0QsMkJBQTJCO2dCQUM1QixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxDQUFDO2dCQUM1QyxJQUFJLFFBQVEsSUFBSSxDQUFDLFdBQVcsRUFBRSxDQUFDO29CQUM5QixJQUFJLENBQUMsUUFBUSxDQUFDLFFBQVEsRUFBRTt3QkFDdkIsUUFBUSxFQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUU7d0JBQ2hFLElBQUksRUFBTyxnQkFBZ0I7d0JBQzNCLElBQUksRUFBTyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDO3FCQUNqRCxDQUFDLENBQUM7Z0JBQ0osQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsbUVBQW1FO1FBQ25FLElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUNsRCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsQ0FBQztZQUN2RCxJQUFJLFFBQVEsS0FBSyxRQUFRLElBQUksSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQ3hELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDOUMsSUFBSSxRQUFRLEVBQUUsQ0FBQztvQkFDZCxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7b0JBQ0YsTUFBTSxRQUFRLEdBQUcsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsRUFBRSxDQUFDO29CQUN2RSxJQUFJLENBQUMsUUFBUSxDQUFDLFFBQVEsRUFBRTt3QkFDdkIsUUFBUTt3QkFDUixJQUFJLEVBQUcsUUFBUTt3QkFDZixJQUFJLEVBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQztxQkFDN0MsQ0FBQyxDQUFDO29CQUNILG1FQUFtRTtvQkFDbkUsSUFBSSxDQUFDLHFCQUFxQixDQUFDLElBQUksRUFBRSxRQUFRLENBQUMsQ0FBQztvQkFDM0MsMERBQTBEO29CQUMxRCx5REFBeUQ7b0JBQ3pELElBQUksQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLENBQUMsRUFBRSxJQUFJLEVBQUcsUUFBUSxFQUFFLFFBQVEsRUFBRSxDQUFDLENBQUM7Z0JBQzNELENBQUM7WUFDRixDQUFDO1lBRUQsNkRBQTZEO1lBQzdELDhEQUE4RDtZQUM5RCx3REFBd0Q7WUFDeEQsNkRBQTZEO1lBQzdELDZEQUE2RDtZQUM3RCxrREFBa0Q7WUFDbEQsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ3BELElBQUksUUFBUSxFQUFFLENBQUM7Z0JBQ2QsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksRUFBRSxRQUFRLEVBQUUsVUFBVSxDQUFDLENBQUM7Z0JBQ3pELE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztnQkFDRixJQUFJLENBQUMsT0FBTyxDQUFDLFFBQVEsRUFBRTtvQkFDdEIsUUFBUSxFQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUU7b0JBQ2hFLElBQUksRUFBTyxlQUFlO29CQUMxQixJQUFJLEVBQU8sSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQztvQkFDakQsT0FBTyxFQUFJLHNCQUFzQjtpQkFDakMsQ0FBQyxDQUFDO1lBQ0osQ0FBQztZQUVELGlFQUFpRTtZQUNqRSxpRUFBaUU7WUFDakUsZ0VBQWdFO1lBQ2hFLHFEQUFxRDtZQUNyRCw4REFBOEQ7WUFDOUQsNERBQTREO1lBQzVELDREQUE0RDtZQUM1RCw2REFBNkQ7WUFDN0QsOEJBQThCO1lBQzlCLE1BQU0sZ0JBQWdCLEdBQUcsSUFBSSxDQUFDLDZCQUE2QixDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ2xFLElBQUksZ0JBQWdCLEVBQUUsQ0FBQztnQkFDdEIsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLElBQUksQ0FBQyxVQUFVLEVBQUUsTUFBTSxDQUFDLENBQUM7Z0JBQzNFLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztvQkFDakIsTUFBTSxXQUFXLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBRSxDQUFDLENBQUUsRUFBRSxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUM7b0JBQzdELElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxJQUFJLEVBQUUsZ0JBQWdCLEVBQUUsVUFBVSxFQUFFLFdBQVcsQ0FBQyxDQUFDO29CQUM5RSxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7b0JBQ0YsSUFBSSxDQUFDLE9BQU8sQ0FBQyxnQkFBZ0IsRUFBRTt3QkFDOUIsUUFBUSxFQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUU7d0JBQ2hFLElBQUksRUFBTyxlQUFlO3dCQUMxQixJQUFJLEVBQU8sSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQzt3QkFDakQsT0FBTyxFQUFJLHlCQUF5QjtxQkFDcEMsQ0FBQyxDQUFDO2dCQUNKLENBQUM7Z0JBQ0QsSUFBSSxDQUFDLGtCQUFrQixDQUFDLElBQUksRUFBRSxnQkFBZ0IsQ0FBQyxDQUFDO1lBQ2pELENBQUM7WUFFRCxnRUFBZ0U7WUFDaEUsdURBQXVEO1lBQ3ZELDREQUE0RDtZQUM1RCxnRUFBZ0U7WUFDaEUsMERBQTBEO1lBQzFELDZEQUE2RDtZQUM3RCx5REFBeUQ7WUFDekQseURBQXlEO1lBQ3pELDBEQUEwRDtZQUMxRCxnQkFBZ0I7WUFDaEIsTUFBTSxZQUFZLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ3hELElBQUksWUFBWSxFQUFFLENBQUM7Z0JBQ2xCLElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxJQUFJLEVBQUUsWUFBWSxFQUFFLFVBQVUsQ0FBQyxDQUFDO2dCQUM3RCxJQUFJLENBQUMsa0JBQWtCLENBQUMsSUFBSSxFQUFFLFlBQVksQ0FBQyxDQUFDO1lBQzdDLENBQUM7WUFDRCxNQUFNLFNBQVMsR0FBRyxJQUFJLENBQUMsc0JBQXNCLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDcEQsSUFBSSxTQUFTLEVBQUUsQ0FBQztnQkFDZixJQUFJLENBQUMsdUJBQXVCLENBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxVQUFVLENBQUMsQ0FBQztnQkFDMUQsSUFBSSxDQUFDLGtCQUFrQixDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsQ0FBQztZQUMxQyxDQUFDO1FBQ0YsQ0FBQztJQUNGLENBQUM7SUFFRDs7Y0FFSTtJQUNJLGVBQWUsQ0FBRSxJQUFtQjtRQUMzQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUMzQixPQUFPLElBQUksQ0FBQyxJQUFJLENBQUM7UUFDbEIsQ0FBQztRQUNELElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDekMsT0FBTyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztRQUN2QixDQUFDO1FBQ0QsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOztjQUVJO0lBQ0ksUUFBUSxDQUFFLFFBQWdCLEVBQUUsS0FBZ0I7UUFDbkQsK0NBQStDO1FBQy9DLElBQUksQ0FBQyxJQUFJLENBQUMsV0FBVyxDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO1lBQ3JDLE9BQU87UUFDUixDQUFDO1FBQ0QsSUFBSSxDQUFDLElBQUksQ0FBQyxNQUFNLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDaEMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxHQUFHLENBQUMsUUFBUSxFQUFFLEVBQUUsQ0FBQyxDQUFDO1FBQy9CLENBQUM7UUFFRCx5REFBeUQ7UUFDekQsTUFBTSxjQUFjLEdBQUcsSUFBSSxDQUFDLE1BQU0sQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFFLENBQUM7UUFDbEQsTUFBTSxXQUFXLEdBQUcsY0FBYyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUNsRCxRQUFRLENBQUMsUUFBUSxLQUFLLEtBQUssQ0FBQyxRQUFRO1lBQ25DLFFBQVEsQ0FBQyxJQUFJLEtBQUssS0FBSyxDQUFDLElBQUk7WUFDNUIsUUFBUSxDQUFDLElBQUksS0FBSyxLQUFLLENBQUMsSUFBSSxDQUFDLENBQUM7UUFFaEMsSUFBSSxDQUFDLFdBQVcsRUFBRSxDQUFDO1lBQ2xCLGNBQWMsQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7UUFDNUIsQ0FBQztJQUNGLENBQUM7SUFFRDs7T0FFRztJQUNLLFVBQVUsQ0FBRSxJQUFhLEVBQUUsVUFBeUI7UUFDM0QsSUFBSSxDQUFDLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUNwRCxPQUFPO1FBQ1IsQ0FBQztRQUVELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxlQUFlLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQ3ZELElBQUksQ0FBQyxRQUFRLEVBQUUsQ0FBQztZQUNmLE9BQU87UUFDUixDQUFDO1FBRUQsTUFBTSxFQUFFLElBQUksRUFBRSxTQUFTLEVBQUUsR0FBRyxFQUFFLENBQUMsNkJBQTZCLENBQzNELFVBQVUsRUFDVixJQUFJLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxDQUN6QixDQUFDO1FBQ0YsTUFBTSxRQUFRLEdBQUcsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsRUFBRSxDQUFDO1FBQ3ZFLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsRUFBRSxHQUFHLENBQUMsQ0FBQztRQUNwRCw4REFBOEQ7UUFDOUQsZ0VBQWdFO1FBQ2hFLCtEQUErRDtRQUMvRCxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxDQUFDO1FBRXpDLHVHQUF1RztRQUN2RyxJQUNDLFFBQVEsS0FBSyxNQUFNO1lBQ25CLFFBQVEsS0FBSyxvQkFBb0I7WUFDakMsUUFBUSxLQUFLLHVCQUF1QjtZQUNwQyxRQUFRLEtBQUsscUJBQXFCLEVBQ2pDLENBQUM7WUFDRixNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsc0JBQXNCLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBRSxDQUFDLENBQUUsQ0FBQyxDQUFDO1lBQ3BFLHFEQUFxRDtZQUNyRCxrREFBa0Q7WUFDbEQsb0NBQW9DO1lBQ3BDLHlDQUF5QztZQUN6QyxrQ0FBa0M7WUFDbEMsNERBQTREO1lBQzVELHVFQUF1RTtZQUN2RSxNQUFNLGVBQWUsR0FBRyxRQUFRLEtBQUsscUJBQXFCO2dCQUN6RCxDQUFDLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBRSxDQUFDLENBQUU7Z0JBQ3JCLENBQUMsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFFLENBQUMsQ0FBRSxDQUFDO1lBQ3ZCLDBEQUEwRDtZQUMxRCw2REFBNkQ7WUFDN0QsbUVBQW1FO1lBQ25FLDZEQUE2RDtZQUM3RCxpRUFBaUU7WUFDakUsTUFBTSxnQkFBZ0IsR0FBRyxlQUFlO2dCQUN2QyxDQUFDLENBQUMsSUFBSSxDQUFDLDJCQUEyQixDQUFDLGVBQWUsQ0FBQztnQkFDbkQsQ0FBQyxDQUFDLFNBQVMsQ0FBQztZQUNiLE1BQU0sY0FBYyxHQUFHLEtBQUssSUFBSSxnQkFBZ0IsQ0FBQztZQUNqRCxNQUFNLElBQUksR0FBWTtnQkFDckIsUUFBUTtnQkFDUixJQUFJLEVBQVMsTUFBTTtnQkFDbkIsSUFBSTtnQkFDSixVQUFVLEVBQUcsVUFBVSxJQUFJLFNBQVM7Z0JBQ3BDLEtBQUssRUFBUSxjQUFjO2dCQUMzQixFQUFFLEVBQVcsUUFBUTthQUNyQixDQUFDO1lBQ0YsSUFBSSxlQUFlLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxlQUFlLENBQUMsRUFBRSxDQUFDO2dCQUN6RCxJQUFJLENBQUMsV0FBVyxHQUFHLGVBQWUsQ0FBQyxJQUFJLENBQUM7WUFDekMsQ0FBQztZQUNELEtBQUssTUFBTSxRQUFRLElBQUksQ0FBRSxJQUFJLENBQUMsU0FBUyxDQUFFLENBQUMsQ0FBRSxFQUFFLElBQUksQ0FBQyxTQUFTLENBQUUsQ0FBQyxDQUFFLENBQUUsRUFBRSxDQUFDO2dCQUNyRSxJQUFJLFFBQVEsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7b0JBQzlDLElBQUksQ0FBQyxLQUFLLEdBQUcsUUFBUSxDQUFDLElBQUksQ0FBQztvQkFDM0IsTUFBTTtnQkFDUCxDQUFDO1lBQ0YsQ0FBQztZQUNELCtEQUErRDtZQUMvRCxnRUFBZ0U7WUFDaEUsOERBQThEO1lBQzlELDBDQUEwQztZQUMxQyxNQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMsYUFBYSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUM3QyxJQUFJLE9BQU8sRUFBRSxDQUFDO2dCQUNiLElBQUksQ0FBQyxHQUFHLEdBQUcsT0FBTyxDQUFDLEdBQUcsQ0FBQztnQkFDdkIsSUFBSSxJQUFJLENBQUMsS0FBSyxLQUFLLFNBQVMsRUFBRSxDQUFDO29CQUM5QixJQUFJLENBQUMsS0FBSyxHQUFHLE9BQU8sQ0FBQyxLQUFLLENBQUM7Z0JBQzVCLENBQUM7WUFDRixDQUFDO1lBQ0QsZ0VBQWdFO1lBQ2hFLDZEQUE2RDtZQUM3RCwwQ0FBMEM7WUFDMUMsTUFBTSxPQUFPLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksQ0FBQyxTQUFTLENBQUUsQ0FBQyxDQUFFLEVBQUUsVUFBVSxDQUFDLENBQUM7WUFDOUUsSUFBSSxPQUFPLEVBQUUsQ0FBQztnQkFDYixrRUFBa0U7Z0JBQ2xFLGtFQUFrRTtnQkFDbEUsb0RBQW9EO2dCQUNwRCxNQUFNLFdBQVcsR0FBRyxFQUFFLENBQUMsNkJBQTZCLENBQ25ELFVBQVUsRUFDVixPQUFPLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxDQUM1QixDQUFDO2dCQUNGLE1BQU0sWUFBWSxHQUFHLFFBQVEsQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLFFBQVEsQ0FBQyxDQUFDO2dCQUMzRCxJQUFJLENBQUMsZUFBZSxHQUFHLEdBQUcsWUFBWSxJQUFJLFdBQVcsQ0FBQyxJQUFJLEdBQUcsQ0FBQyxJQUFJLFdBQVcsQ0FBQyxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQzlGLE1BQU0sWUFBWSxHQUFHLElBQUksR0FBRyxFQUFVLENBQUM7Z0JBQ3ZDLElBQUksQ0FBQyxrQkFBa0IsQ0FBQyxPQUFPLEVBQUUsUUFBUSxFQUFFLFVBQVUsRUFBRSxDQUFDLEVBQUUsSUFBSSxHQUFHLEVBQUUsRUFBRSxZQUFZLEVBQUUsY0FBYyxDQUFDLENBQUM7Z0JBQ25HLElBQUksWUFBWSxDQUFDLElBQUksR0FBRyxDQUFDLEVBQUUsQ0FBQztvQkFDM0IsSUFBSSxDQUFDLFlBQVksR0FBRyxLQUFLLENBQUMsSUFBSSxDQUFDLFlBQVksQ0FBQyxDQUFDO2dCQUM5QyxDQUFDO1lBQ0YsQ0FBQztZQUNELE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxNQUFNLENBQUMsVUFBVSxJQUFJLGNBQWMsSUFBSSxTQUFTLEVBQUUsSUFBSSxDQUFDLENBQUM7WUFDNUUsSUFBSSxDQUFDLGVBQWUsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLE1BQU0sQ0FBQyxDQUFDO1lBQ3ZDLE9BQU87UUFDUixDQUFDO1FBRUQscURBQXFEO1FBQ3JELElBQUksUUFBUSxLQUFLLFNBQVMsSUFBSSxRQUFRLEtBQUssa0JBQWtCLElBQUksUUFBUSxLQUFLLFNBQVMsRUFBRSxDQUFDO1lBQ3pGLElBQUksQ0FBQyxNQUFNLENBQUMsS0FBSyxJQUFJLFNBQVMsRUFBRTtnQkFDL0IsUUFBUTtnQkFDUixJQUFJLEVBQUcsZ0JBQWdCO2dCQUN2QixJQUFJO2dCQUNKLEtBQUs7YUFDTCxDQUFDLENBQUM7WUFDSCxPQUFPO1FBQ1IsQ0FBQztRQUVELDBEQUEwRDtRQUMxRCw4Q0FBOEM7UUFDOUMsSUFBSSxRQUFRLEtBQUssYUFBYSxJQUFJLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxHQUFHLENBQUMsRUFBRSxDQUFDO1lBQzdELE1BQU0sQ0FBRSxHQUFHLENBQUUsR0FBRyxJQUFJLENBQUMsU0FBUyxDQUFDO1lBQy9CLElBQUksRUFBRSxDQUFDLHdCQUF3QixDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQ3RDLEtBQUssTUFBTSxPQUFPLElBQUksR0FBRyxDQUFDLFFBQVEsRUFBRSxDQUFDO29CQUNwQyxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsc0JBQXNCLENBQUMsT0FBTyxDQUFDLENBQUM7b0JBQ3hELElBQUksQ0FBQyxNQUFNLENBQUMsVUFBVSxJQUFJLEtBQUssSUFBSSxTQUFTLEVBQUU7d0JBQzdDLFFBQVE7d0JBQ1IsSUFBSSxFQUFTLFlBQVk7d0JBQ3pCLElBQUk7d0JBQ0osVUFBVSxFQUFHLFVBQVUsSUFBSSxTQUFTO3dCQUNwQyxLQUFLO3FCQUNMLENBQUMsQ0FBQztnQkFDSixDQUFDO1lBQ0YsQ0FBQztpQkFBTSxDQUFDO2dCQUNQLE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQyxzQkFBc0IsQ0FBQyxHQUFHLENBQUMsQ0FBQztnQkFDcEQsSUFBSSxDQUFDLE1BQU0sQ0FBQyxVQUFVLElBQUksS0FBSyxJQUFJLFNBQVMsRUFBRTtvQkFDN0MsUUFBUTtvQkFDUixJQUFJLEVBQVMsWUFBWTtvQkFDekIsSUFBSTtvQkFDSixVQUFVLEVBQUcsVUFBVSxJQUFJLFNBQVM7b0JBQ3BDLEtBQUs7aUJBQ0wsQ0FBQyxDQUFDO1lBQ0osQ0FBQztZQUNELE9BQU87UUFDUixDQUFDO0lBQ0YsQ0FBQztJQUVEOztPQUVHO0lBQ0ssc0JBQXNCLENBQUUsR0FBOEI7UUFDN0QsSUFBSSxDQUFDLEdBQUcsRUFBRSxDQUFDO1lBQ1YsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELDRCQUE0QjtRQUM1QixJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztZQUMxQixNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUNwRCxJQUFJLE1BQU0sRUFBRSxDQUFDO2dCQUNaLE9BQU8sTUFBTSxDQUFDO1lBQ2YsQ0FBQztZQUNELGtDQUFrQztZQUNsQyxJQUFJLElBQUksQ0FBQyxXQUFXLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUNwQyxPQUFPLEdBQUcsQ0FBQyxJQUFJLENBQUM7WUFDakIsQ0FBQztZQUNELDJEQUEyRDtZQUMzRCx3REFBd0Q7WUFDeEQsMkRBQTJEO1lBQzNELHdEQUF3RDtZQUN4RCw0REFBNEQ7WUFDNUQsK0NBQStDO1lBQy9DLHlEQUF5RDtZQUN6RCwyREFBMkQ7WUFDM0QsOERBQThEO1lBQzlELDhEQUE4RDtZQUM5RCwrQ0FBK0M7WUFDL0MsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsR0FBRyxDQUFDLENBQUM7WUFDM0QsSUFBSSxRQUFRLEVBQUUsQ0FBQztnQkFDZCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsc0JBQXNCLENBQUMsUUFBUSxDQUFDLENBQUM7Z0JBQ3ZELElBQUksUUFBUSxFQUFFLENBQUM7b0JBQ2QsT0FBTyxRQUFRLENBQUM7Z0JBQ2pCLENBQUM7WUFDRixDQUFDO1lBQ0QsOERBQThEO1lBQzlELDREQUE0RDtZQUM1RCx5REFBeUQ7WUFDekQsZ0VBQWdFO1lBQ2hFLE1BQU0sU0FBUyxHQUFHLElBQUksQ0FBQyxrQ0FBa0MsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLEdBQUcsQ0FBQztnQkFDdkUsSUFBSSxDQUFDLGlDQUFpQyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsR0FBRyxDQUFDLENBQUM7WUFDdkQsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELDJEQUEyRDtRQUMzRCxzREFBc0Q7UUFDdEQsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7WUFDN0IsTUFBTSxRQUFRLEdBQUcsR0FBRyxDQUFDLFVBQVUsQ0FBQztZQUNoQyxNQUFNLElBQUksR0FBRyxFQUFFLENBQUMsMEJBQTBCLENBQUMsUUFBUSxDQUFDO2dCQUNuRCxDQUFDLENBQUMsSUFBSSxDQUFDLGVBQWUsQ0FBQyxRQUFRLENBQUM7Z0JBQ2hDLENBQUMsQ0FBQyxJQUFJLENBQUMseUJBQXlCLENBQUMsUUFBUSxDQUFDLENBQUM7WUFDNUMsTUFBTSxLQUFLLEdBQUcsSUFBSSxJQUFJLElBQUksQ0FBQyxXQUFXLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQztZQUNwRSxPQUFPLEtBQUssQ0FBQztRQUNkLENBQUM7UUFFRCw0QkFBNEI7UUFDNUIsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztZQUN4QyxPQUFPLElBQUksQ0FBQyxlQUFlLENBQUMsR0FBRyxDQUFDLENBQUM7UUFDbEMsQ0FBQztRQUVELGtDQUFrQztRQUNsQyxJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsSUFBSSxHQUFHLENBQUMsVUFBVSxDQUFDLElBQUksS0FBSyxNQUFNLEVBQUUsQ0FBQztZQUM3RyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7Ozs7Ozs7O09BVUc7SUFDSyxxQkFBcUIsQ0FBRSxJQUFZLEVBQUUsSUFBYTtRQUN6RCxJQUFJLE9BQU8sR0FBd0IsSUFBSSxDQUFDO1FBQ3hDLE9BQU8sT0FBTyxFQUFFLENBQUM7WUFDaEIsTUFBTSxVQUFVLEdBQ2YsRUFBRSxDQUFDLE9BQU8sQ0FBQyxPQUFPLENBQUMsSUFBSSxFQUFFLENBQUMsYUFBYSxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsT0FBTyxDQUFDO2dCQUMzRSxDQUFDLENBQUMsT0FBTyxDQUFDLFVBQVU7Z0JBQ3BCLENBQUMsQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsT0FBTyxDQUFDO29CQUN4RCxDQUFDLENBQUMsT0FBTyxDQUFDLFVBQVU7b0JBQ3BCLENBQUMsQ0FBQyxTQUFTLENBQUM7WUFDZixJQUFJLFVBQVUsSUFBSSxJQUFJLENBQUMseUJBQXlCLENBQUMsVUFBVSxFQUFFLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQ3BFLE1BQU0sR0FBRyxHQUFHLElBQUksQ0FBQyw2QkFBNkIsQ0FBQyxVQUFVLEVBQUUsSUFBSSxDQUFDLENBQUM7Z0JBQ2pFLE9BQU8sR0FBRyxDQUFDO1lBQ1osQ0FBQztZQUNELE9BQU8sR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDO1FBQzFCLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7OztPQUdHO0lBQ0sseUJBQXlCLENBQUUsVUFBbUMsRUFBRSxJQUFZO1FBQ25GLEtBQUssTUFBTSxTQUFTLElBQUksVUFBVSxFQUFFLENBQUM7WUFDcEMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUFDO2dCQUN4QyxTQUFTO1lBQ1YsQ0FBQztZQUNELEtBQUssTUFBTSxXQUFXLElBQUksU0FBUyxDQUFDLGVBQWUsQ0FBQyxZQUFZLEVBQUUsQ0FBQztnQkFDbEUsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsSUFBSSxXQUFXLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxJQUFJLEVBQUUsQ0FBQztvQkFDekUsT0FBTyxJQUFJLENBQUM7Z0JBQ2IsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBQ0QsT0FBTyxLQUFLLENBQUM7SUFDZCxDQUFDO0lBRUQ7Ozs7T0FJRztJQUNLLDZCQUE2QixDQUNwQyxVQUFtQyxFQUNuQyxJQUFZO1FBRVosS0FBSyxNQUFNLFNBQVMsSUFBSSxVQUFVLEVBQUUsQ0FBQztZQUNwQyxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsU0FBUyxFQUFFLElBQUksQ0FBQyxDQUFDO1lBQ3pELElBQUksTUFBTSxFQUFFLENBQUM7Z0JBQ1osT0FBTyxNQUFNLENBQUM7WUFDZixDQUFDO1lBQ0QsS0FBSyxNQUFNLE1BQU0sSUFBSSxJQUFJLENBQUMsaUJBQWlCLENBQUMsU0FBUyxDQUFDLEVBQUUsQ0FBQztnQkFDeEQsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLDZCQUE2QixDQUFDLE1BQU0sRUFBRSxJQUFJLENBQUMsQ0FBQztnQkFDL0QsSUFBSSxLQUFLLEVBQUUsQ0FBQztvQkFDWCxPQUFPLEtBQUssQ0FBQztnQkFDZCxDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7O09BRUc7SUFDSyxtQkFBbUIsQ0FBRSxTQUF1QixFQUFFLElBQVk7UUFDakUsSUFBSSxDQUFDLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUFDO1lBQzFDLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLElBQUksR0FBRyxTQUFTLENBQUMsVUFBVSxDQUFDO1FBQ2xDLElBQUksQ0FBQyxFQUFFLENBQUMsa0JBQWtCLENBQUMsSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxXQUFXLEVBQUUsQ0FBQztZQUMzRixPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBQ0QsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLElBQUksRUFBRSxDQUFDO1lBQzVELE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLEdBQUcsR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDO1FBQ3ZCLE9BQU8sR0FBRyxDQUFDO0lBQ1osQ0FBQztJQUVEOzs7OztPQUtHO0lBQ0ssaUJBQWlCLENBQUUsU0FBdUI7UUFDakQsTUFBTSxNQUFNLEdBQXFCLEVBQUUsQ0FBQztRQUNwQyxNQUFNLElBQUksR0FBRyxDQUFDLElBQThCLEVBQVEsRUFBRTtZQUNyRCxJQUFJLElBQUksSUFBSSxFQUFFLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQzlCLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBRSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUUsQ0FBQyxDQUFDO1lBQ3JDLENBQUM7UUFDRixDQUFDLENBQUM7UUFDRixJQUFJLEVBQUUsQ0FBQyxPQUFPLENBQUMsU0FBUyxDQUFDLEVBQUUsQ0FBQztZQUMzQixNQUFNLENBQUMsSUFBSSxDQUFDLENBQUUsR0FBRyxTQUFTLENBQUMsVUFBVSxDQUFFLENBQUMsQ0FBQztRQUMxQyxDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsY0FBYyxDQUFDLFNBQVMsQ0FBQyxFQUFFLENBQUM7WUFDekMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxRQUFRLENBQUMsQ0FBQztZQUN6QixJQUFJLFNBQVMsQ0FBQyxXQUFXLEVBQUUsQ0FBQztnQkFDM0IsSUFBSSxDQUFDLFNBQVMsQ0FBQyxXQUFXLENBQUMsS0FBSyxDQUFDLENBQUM7WUFDbkMsQ0FBQztZQUNELElBQUksQ0FBQyxTQUFTLENBQUMsWUFBWSxDQUFDLENBQUM7UUFDOUIsQ0FBQzthQUFNLElBQUksRUFBRSxDQUFDLGFBQWEsQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUFDO1lBQ3hDLElBQUksQ0FBQyxTQUFTLENBQUMsYUFBYSxDQUFDLENBQUM7WUFDOUIsSUFBSSxDQUFDLFNBQVMsQ0FBQyxhQUFhLENBQUMsQ0FBQztRQUMvQixDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsY0FBYyxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxTQUFTLENBQUM7WUFDeEUsRUFBRSxDQUFDLGdCQUFnQixDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxTQUFTLENBQUM7WUFDaEUsRUFBRSxDQUFDLGFBQWEsQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLFNBQVMsQ0FBQyxFQUFFLENBQUM7WUFDL0QsSUFBSSxDQUFDLFNBQVMsQ0FBQyxTQUFTLENBQUMsQ0FBQztRQUMzQixDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsU0FBUyxDQUFDLEVBQUUsQ0FBQztZQUM1QyxLQUFLLE1BQU0sTUFBTSxJQUFJLFNBQVMsQ0FBQyxTQUFTLENBQUMsT0FBTyxFQUFFLENBQUM7Z0JBQ2xELE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBRSxHQUFHLE1BQU0sQ0FBQyxVQUFVLENBQUUsQ0FBQyxDQUFDO1lBQ3ZDLENBQUM7UUFDRixDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsa0JBQWtCLENBQUMsU0FBUyxDQUFDLEVBQUUsQ0FBQztZQUM3QyxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsU0FBUyxDQUFDLFNBQVMsQ0FBQyxDQUFDO1lBQzNELEtBQUssTUFBTSxLQUFLLElBQUksTUFBTSxFQUFFLENBQUM7Z0JBQzVCLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBRSxHQUFHLEtBQUssQ0FBRSxDQUFDLENBQUM7WUFDM0IsQ0FBQztRQUNGLENBQUM7UUFDRCxNQUFNLE1BQU0sR0FBRyxNQUFNLENBQUM7UUFDdEIsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7Ozs7O09BS0c7SUFDSyxlQUFlLENBQUUsSUFBYTtRQUNyQyxJQUFJLE9BQU8sR0FBd0IsSUFBSSxDQUFDLE1BQU0sQ0FBQztRQUMvQyxPQUFPLE9BQU8sRUFBRSxDQUFDO1lBQ2hCLE1BQU0sU0FBUyxHQUFHLElBQUksQ0FBQyxjQUFjLENBQUMsR0FBRyxDQUFDLE9BQU8sQ0FBQyxDQUFDO1lBQ25ELElBQUksU0FBUyxFQUFFLENBQUM7Z0JBQ2YsT0FBTyxTQUFTLENBQUM7WUFDbEIsQ0FBQztZQUNELE9BQU8sR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDO1FBQzFCLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7Ozs7Ozs7O09BUUc7SUFDSywyQkFBMkIsQ0FBRSxHQUFrQjtRQUN0RCxNQUFNLFdBQVcsR0FBRyxDQUFDLElBQVksRUFBRSxJQUFhLEVBQXNCLEVBQUU7WUFDdkUsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUNoRCxJQUFJLE1BQU0sRUFBRSxDQUFDO2dCQUNaLE9BQU8sTUFBTSxDQUFDO1lBQ2YsQ0FBQztZQUNELE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQyxrQ0FBa0MsQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDO2dCQUN6RSw2REFBNkQ7Z0JBQzdELDREQUE0RDtnQkFDNUQsc0RBQXNEO2dCQUN0RCxxREFBcUQ7Z0JBQ3JELElBQUksQ0FBQyxpQ0FBaUMsQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLENBQUM7WUFDcEQsT0FBTyxjQUFjLENBQUM7UUFDdkIsQ0FBQyxDQUFDO1FBRUYsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7WUFDMUIsTUFBTSxNQUFNLEdBQUcsV0FBVyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsR0FBRyxDQUFDLENBQUM7WUFDMUMsT0FBTyxNQUFNLENBQUM7UUFDZixDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztZQUN4QyxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLENBQUM7WUFDekMsSUFBSSxJQUFJLEVBQUUsQ0FBQztnQkFDVixNQUFNLE1BQU0sR0FBRyxXQUFXLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxHQUFHLENBQUMsQ0FBQztnQkFDM0MsT0FBTyxNQUFNLENBQUM7WUFDZixDQUFDO1FBQ0YsQ0FBQztRQUNELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7Ozs7O09BTUc7SUFDSyx5QkFBeUIsQ0FBRSxJQUFZO1FBQzlDLEtBQUssTUFBTSxDQUFFLElBQUksRUFBRSxLQUFLLENBQUUsSUFBSSxJQUFJLENBQUMsbUJBQW1CLEVBQUUsQ0FBQztZQUN4RCxJQUFJLElBQUksQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUNuQyxTQUFTO1lBQ1YsQ0FBQztZQUNELElBQUksS0FBSyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUNyQixPQUFPLElBQUksQ0FBQztZQUNiLENBQUM7UUFDRixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsS0FBSyxDQUFDO1FBQ3JCLE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7Ozs7Ozs7T0FTRztJQUNLLHlCQUF5QixDQUFFLElBQVk7UUFDOUMsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQy9DLElBQUksTUFBTSxDQUFDLE1BQU0sS0FBSyxRQUFRLEVBQUUsQ0FBQztZQUNoQyxNQUFNLE1BQU0sR0FBRyxNQUFNLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQztZQUNwQyxPQUFPLE1BQU0sQ0FBQztRQUNmLENBQUM7UUFDRCxJQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO1lBQ3pCLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMsb0JBQW9CLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsR0FBRyxDQUFDLENBQUMsQ0FBQztRQUNuRSxJQUFJLE9BQU8sQ0FBQyxNQUFNLEtBQUssUUFBUSxFQUFFLENBQUM7WUFDakMsTUFBTSxNQUFNLEdBQUcsT0FBTyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUM7WUFDckMsT0FBTyxNQUFNLENBQUM7UUFDZixDQUFDO1FBQ0QsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7Ozs7T0FNRztJQUNLLGtDQUFrQyxDQUFFLElBQVksRUFBRSxJQUFhO1FBQ3RFLElBQUksT0FBTyxHQUF3QixJQUFJLENBQUMsTUFBTSxDQUFDO1FBQy9DLE9BQU8sT0FBTyxFQUFFLENBQUM7WUFDaEIsSUFBSSxFQUFFLENBQUMsY0FBYyxDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7Z0JBQ2hDLEtBQUssTUFBTSxLQUFLLElBQUksT0FBTyxDQUFDLFVBQVUsSUFBSSxFQUFFLEVBQUUsQ0FBQztvQkFDOUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLElBQUksSUFBSSxDQUFDLEtBQUssQ0FBQyxJQUFJO3dCQUMxRSxDQUFDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDO3dCQUNuQyxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUM7d0JBQ3JDLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxhQUFhLEVBQUUsTUFBTSxJQUFJLENBQUMsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO3dCQUM5QyxTQUFTO29CQUNWLENBQUM7b0JBQ0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQyxDQUFDO29CQUMxRSxJQUFJLFFBQVEsRUFBRSxDQUFDO3dCQUNkLE9BQU8sUUFBUSxDQUFDO29CQUNqQixDQUFDO2dCQUNGLENBQUM7Z0JBQ0QsT0FBTyxTQUFTLENBQUM7WUFDbEIsQ0FBQztZQUNELE9BQU8sR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDO1FBQzFCLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7Ozs7Ozs7Ozs7T0FVRztJQUNLLGlDQUFpQyxDQUFFLElBQVksRUFBRSxJQUFhO1FBQ3JFLElBQUksT0FBTyxHQUF3QixJQUFJLENBQUM7UUFDeEMsT0FBTyxPQUFPLEVBQUUsQ0FBQztZQUNoQixNQUFNLFVBQVUsR0FDZixFQUFFLENBQUMsT0FBTyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxhQUFhLENBQUMsT0FBTyxDQUFDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUM7Z0JBQzNFLENBQUMsQ0FBQyxPQUFPLENBQUMsVUFBVTtnQkFDcEIsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsT0FBTyxDQUFDLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxPQUFPLENBQUM7b0JBQ3hELENBQUMsQ0FBQyxPQUFPLENBQUMsVUFBVTtvQkFDcEIsQ0FBQyxDQUFDLFNBQVMsQ0FBQztZQUNmLElBQUksVUFBVSxFQUFFLENBQUM7Z0JBQ2hCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyw2QkFBNkIsQ0FBQyxVQUFVLEVBQUUsSUFBSSxDQUFDLENBQUM7Z0JBQ3RFLElBQUksUUFBUSxFQUFFLENBQUM7b0JBQ2QsT0FBTyxRQUFRLENBQUM7Z0JBQ2pCLENBQUM7WUFDRixDQUFDO1lBQ0QsT0FBTyxHQUFHLE9BQU8sQ0FBQyxNQUFNLENBQUM7UUFDMUIsQ0FBQztRQUNELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7OztPQUlHO0lBQ0ssNkJBQTZCLENBQ3BDLFVBQW1DLEVBQ25DLElBQVk7UUFFWixLQUFLLE1BQU0sU0FBUyxJQUFJLFVBQVUsRUFBRSxDQUFDO1lBQ3BDLElBQUksQ0FBQyxFQUFFLENBQUMsbUJBQW1CLENBQUMsU0FBUyxDQUFDLEVBQUUsQ0FBQztnQkFDeEMsU0FBUztZQUNWLENBQUM7WUFDRCxLQUFLLE1BQU0sV0FBVyxJQUFJLFNBQVMsQ0FBQyxlQUFlLENBQUMsWUFBWSxFQUFFLENBQUM7Z0JBQ2xFLElBQUksQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsSUFBSSxXQUFXLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxJQUFJO29CQUN2RSxDQUFDLFdBQVcsQ0FBQyxJQUFJO29CQUNqQixDQUFDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxXQUFXLENBQUMsSUFBSSxDQUFDO29CQUN6QyxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsV0FBVyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUM7b0JBQzNDLENBQUMsV0FBVyxDQUFDLElBQUksQ0FBQyxhQUFhLEVBQUUsTUFBTSxJQUFJLENBQUMsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO29CQUNwRCxTQUFTO2dCQUNWLENBQUM7Z0JBQ0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQyxDQUFDO2dCQUNoRixJQUFJLFFBQVEsRUFBRSxDQUFDO29CQUNkLE9BQU8sUUFBUSxDQUFDO2dCQUNqQixDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7Ozs7OztPQU1HO0lBQ0ssdUJBQXVCLENBQzlCLEdBQThCLEVBQzlCLFVBQXlCO1FBRXpCLElBQUksQ0FBQyxHQUFHLEVBQUUsQ0FBQztZQUNWLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxDQUFDLG9CQUFvQixDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7WUFDN0QsT0FBTyxHQUFHLENBQUM7UUFDWixDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7WUFDMUIsTUFBTSxHQUFHLEdBQUcsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLEdBQUcsQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUNqRCxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMsZ0JBQWdCLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDO1lBQzdDLElBQUksS0FBSyxFQUFFLENBQUM7Z0JBQ1gsT0FBTyxLQUFLLENBQUM7WUFDZCxDQUFDO1FBQ0YsQ0FBQztRQUNELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7Ozs7Ozs7O09BU0c7SUFDSyxrQkFBa0IsQ0FDekIsRUFBOEIsRUFDOUIsV0FBbUIsRUFDbkIsVUFBeUIsRUFDekIsS0FBYSxFQUNiLE9BQXFCLEVBQ3JCLFlBQXlCLEVBQ3pCLGFBQXNCO1FBRXRCLElBQUksS0FBSyxHQUFHLENBQUMsSUFBSSxPQUFPLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQzlDLE9BQU87UUFDUixDQUFDO1FBQ0QsT0FBTyxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsQ0FBQztRQUVoQiw4Q0FBOEM7UUFDOUMsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUNwRCxJQUFJLENBQUMsbUJBQW1CLENBQUMsRUFBRSxDQUFDLElBQUksRUFBRSxXQUFXLEVBQUUsVUFBVSxFQUFFLEtBQUssRUFBRSxPQUFPLEVBQUUsYUFBYSxDQUFDLENBQUM7WUFDMUYsT0FBTztRQUNSLENBQUM7UUFFRCxNQUFNLElBQUksR0FBRyxDQUFDLElBQWEsRUFBUSxFQUFFO1lBQ3BDLElBQUksSUFBSSxLQUFLLEVBQUUsQ0FBQyxJQUFJLElBQUksQ0FDdkIsRUFBRSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQztnQkFDN0IsRUFBRSxDQUFDLGVBQWUsQ0FBQyxJQUFJLENBQUM7Z0JBQ3hCLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLENBQUM7Z0JBQzlCLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsQ0FDNUIsRUFBRSxDQUFDO2dCQUNILCtEQUErRDtnQkFDL0QsT0FBTztZQUNSLENBQUM7WUFDRCxJQUFJLEVBQUUsQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7Z0JBQ25ELElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsVUFBVSxFQUFFLFdBQVcsRUFBRSxVQUFVLEVBQUUsS0FBSyxFQUFFLE9BQU8sRUFBRSxhQUFhLENBQUMsQ0FBQztZQUNuRyxDQUFDO1lBQ0QsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQzlCLE1BQU0sT0FBTyxHQUFHLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDO29CQUMxRCxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLElBQUksQ0FBQyxXQUFXLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDO3dCQUM5RSxDQUFDLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJO3dCQUN0QixDQUFDLENBQUMsU0FBUyxDQUFDLENBQUM7Z0JBQ2YsSUFBSSxPQUFPLEVBQUUsQ0FBQztvQkFDYixZQUFZLENBQUMsR0FBRyxDQUFDLE9BQU8sQ0FBQyxDQUFDO2dCQUMzQixDQUFDO1lBQ0YsQ0FBQztZQUNELElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQy9CLE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQyxlQUFlLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDO2dCQUN6RCxJQUNDLFVBQVUsS0FBSyxNQUFNO29CQUNyQixVQUFVLEtBQUssb0JBQW9CO29CQUNuQyxVQUFVLEtBQUssdUJBQXVCO29CQUN0QyxVQUFVLEtBQUsscUJBQXFCLEVBQ25DLENBQUM7b0JBQ0Ysb0RBQW9EO29CQUNwRCx1REFBdUQ7b0JBQ3ZELHdEQUF3RDtvQkFDeEQsd0JBQXdCO29CQUN4QixNQUFNLFdBQVcsR0FBRyxJQUFJLENBQUMsZUFBZSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztvQkFDbkQsSUFBSSxXQUFXLEVBQUUsQ0FBQzt3QkFDakIsV0FBVyxDQUFDLEdBQUcsR0FBRyxXQUFXLENBQUM7d0JBQzlCLElBQUksV0FBVyxDQUFDLEtBQUssS0FBSyxTQUFTLEVBQUUsQ0FBQzs0QkFDckMsV0FBVyxDQUFDLEtBQUssR0FBRyxhQUFhLENBQUM7d0JBQ25DLENBQUM7b0JBQ0YsQ0FBQzt5QkFBTSxDQUFDO3dCQUNQLElBQUksQ0FBQyxhQUFhLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxFQUFFLEdBQUcsRUFBRyxXQUFXLEVBQUUsS0FBSyxFQUFHLGFBQWEsRUFBRSxDQUFDLENBQUM7b0JBQzVFLENBQUM7Z0JBQ0YsQ0FBQztZQUNGLENBQUM7WUFDRCxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsQ0FBQztRQUM3QixDQUFDLENBQUM7UUFDRixJQUFJLENBQUMsRUFBRSxDQUFDLElBQUksQ0FBQyxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7Ozs7O09BT0c7SUFDSyxtQkFBbUIsQ0FDMUIsSUFBbUIsRUFDbkIsV0FBbUIsRUFDbkIsVUFBeUIsRUFDekIsS0FBYSxFQUNiLE9BQXFCLEVBQ3JCLGFBQXNCO1FBRXRCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFDaEUsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQ2YsT0FBTztRQUNSLENBQUM7UUFDRCxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLFFBQVEsQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQzdCLENBQUM7UUFDRixNQUFNLFFBQVEsR0FBRyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7UUFDdkUsTUFBTSxJQUFJLEdBQUcsUUFBUSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxDQUFDO1FBQ3hELE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyxlQUFlLENBQUMsUUFBUSxDQUFDLElBQUksYUFBYSxDQUFDO1FBQzlELE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyxNQUFNLENBQUMsS0FBSyxJQUFJLFNBQVMsRUFBRTtZQUM3QyxRQUFRO1lBQ1IsSUFBSSxFQUFHLE1BQU07WUFDYixJQUFJO1lBQ0osS0FBSztZQUNMLEdBQUcsRUFBSSxXQUFXO1lBQ2xCLGdFQUFnRTtZQUNoRSxFQUFFLEVBQUssTUFBTTtTQUNiLENBQUMsQ0FBQztRQUNILGlFQUFpRTtRQUNqRSx5Q0FBeUM7UUFDekMsTUFBTSxhQUFhLEdBQUcsSUFBSSxHQUFHLEVBQVUsQ0FBQztRQUN4QyxJQUFJLENBQUMsa0JBQWtCLENBQUMsUUFBUSxFQUFFLFFBQVEsRUFBRSxVQUFVLEVBQUUsS0FBSyxHQUFHLENBQUMsRUFBRSxPQUFPLEVBQUUsYUFBYSxFQUFFLEtBQUssQ0FBQyxDQUFDO1FBQ2xHLElBQUksYUFBYSxDQUFDLElBQUksR0FBRyxDQUFDLEVBQUUsQ0FBQztZQUM1QixLQUFLLENBQUMsWUFBWSxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsYUFBYSxDQUFDLENBQUM7UUFDaEQsQ0FBQztJQUNGLENBQUM7SUFFRDs7OztPQUlHO0lBQ0ssTUFBTSxDQUFFLFFBQWdCLEVBQUUsSUFBYTtRQUM5QyxJQUFJLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUNuQyxJQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsRUFBRSxDQUFDLENBQUM7UUFDbEMsQ0FBQztRQUVELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBRSxDQUFDO1FBQy9DLE1BQU0sU0FBUyxHQUFHLFFBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUU7WUFDbkMsT0FBTyxDQUFDLENBQUMsUUFBUSxLQUFLLElBQUksQ0FBQyxRQUFRO2dCQUNsQyxDQUFDLENBQUMsSUFBSSxLQUFLLElBQUksQ0FBQyxJQUFJO2dCQUNwQixDQUFDLENBQUMsSUFBSSxLQUFLLElBQUksQ0FBQyxJQUFJLENBQUM7UUFDdkIsQ0FBQyxDQUFDLENBQUM7UUFFSCxJQUFJLFNBQVMsRUFBRSxDQUFDO1lBQ2YsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELFFBQVEsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDcEIsT0FBTyxJQUFJLENBQUM7SUFDYixDQUFDO0lBRUQ7OztPQUdHO0lBQ0ssV0FBVyxDQUFFLElBQWEsRUFBRSxVQUF5QjtRQUM1RCx5Q0FBeUM7UUFDekMsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUN6QyxJQUFJLENBQUMseUJBQXlCLENBQUMsSUFBSSxFQUFFLFVBQVUsQ0FBQyxDQUFDO1lBQ2pELE9BQU87UUFDUixDQUFDO1FBRUQsK0JBQStCO1FBQy9CLElBQUksRUFBRSxDQUFDLHlCQUF5QixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDeEMsSUFBSSxDQUFDLHdCQUF3QixDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsQ0FBQztZQUNoRCxPQUFPO1FBQ1IsQ0FBQztRQUVELG9DQUFvQztRQUNwQyxJQUFJLEVBQUUsQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsYUFBYSxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFdBQVcsRUFBRSxDQUFDO1lBQzFGLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7WUFDN0MsT0FBTztRQUNSLENBQUM7UUFFRCx5RUFBeUU7UUFDekUsSUFBSSxFQUFFLENBQUMsZ0JBQWdCLENBQUMsSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLFVBQVUsRUFBRSxDQUFDO1lBQ2xELElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7WUFDN0MsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsQ0FBQztZQUMvQyxPQUFPO1FBQ1IsQ0FBQztRQUVELDBDQUEwQztRQUMxQyxJQUFJLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsV0FBVyxFQUFFLENBQUM7WUFDeEQsSUFBSSxDQUFDLHNCQUFzQixDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsQ0FBQztZQUM5QyxPQUFPO1FBQ1IsQ0FBQztRQUVELCtCQUErQjtRQUMvQixJQUFJLEVBQUUsQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7WUFDbkQsSUFBSSxDQUFDLGlCQUFpQixDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsQ0FBQztZQUN6QyxPQUFPO1FBQ1IsQ0FBQztRQUVELHNCQUFzQjtRQUN0QixJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUM5QixJQUFJLENBQUMsaUJBQWlCLENBQUMsSUFBSSxFQUFFLFVBQVUsQ0FBQyxDQUFDO1lBQ3pDLE9BQU87UUFDUixDQUFDO0lBQ0YsQ0FBQztJQUVEOztPQUVHO0lBQ0sseUJBQXlCLENBQUUsSUFBaUMsRUFBRSxVQUF5QjtRQUM5RixNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMscUJBQXFCLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQy9ELElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUFDLE9BQU87UUFBQyxDQUFDO1FBRTVCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1FBQ2hDLE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztRQUNGLE1BQU0sUUFBUSxHQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FBQztRQUN2RSxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDLENBQUM7UUFFcEQsb0VBQW9FO1FBQ3BFLElBQUksUUFBUSxLQUFLLFFBQVEsSUFBSSxRQUFRLEtBQUssTUFBTSxFQUFFLENBQUM7WUFBQyxPQUFPO1FBQUMsQ0FBQztRQUU3RCxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsRUFBRTtZQUN4QixRQUFRO1lBQ1IsSUFBSSxFQUFXLGNBQWM7WUFDN0IsSUFBSTtZQUNKLFlBQVksRUFBRyxRQUFRO1lBQ3ZCLFVBQVUsRUFBSyxVQUFVO1NBQ3pCLENBQUMsQ0FBQztJQUNKLENBQUM7SUFFRDs7T0FFRztJQUNLLHdCQUF3QixDQUFFLElBQWdDLEVBQUUsVUFBeUI7UUFDNUYsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsQ0FBQztRQUMvRCxJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7WUFBQyxPQUFPO1FBQUMsQ0FBQztRQUU1QixNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7UUFDRixNQUFNLFFBQVEsR0FBRyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7UUFDdkUsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxDQUFDO1FBRXBELElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxFQUFFO1lBQ3hCLFFBQVE7WUFDUixJQUFJLEVBQVMsZUFBZTtZQUM1QixJQUFJO1lBQ0osVUFBVSxFQUFHLFVBQVU7U0FDdkIsQ0FBQyxDQUFDO0lBQ0osQ0FBQztJQUVEOztPQUVHO0lBQ0sscUJBQXFCLENBQUUsSUFBeUIsRUFBRSxVQUF5QjtRQUNsRixvQ0FBb0M7UUFDcEMsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDOUMsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLENBQUM7WUFDcEUsSUFBSSxDQUFDLFVBQVUsRUFBRSxDQUFDO2dCQUFDLE9BQU87WUFBQyxDQUFDO1lBRTVCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztZQUNyQyxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7WUFDRixNQUFNLFFBQVEsR0FBRyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7WUFDdkUsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxDQUFDO1lBRXBELElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxFQUFFO2dCQUN4QixRQUFRO2dCQUNSLElBQUksRUFBVyxlQUFlO2dCQUM5QixJQUFJO2dCQUNKLFlBQVksRUFBRyxRQUFRO2dCQUN2QixVQUFVLEVBQUssVUFBVTthQUN6QixDQUFDLENBQUM7WUFDSCxPQUFPO1FBQ1IsQ0FBQztRQUVELHNDQUFzQztRQUN0QyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDaEMsTUFBTSxPQUFPLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7WUFDL0IsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxPQUFPLENBQUMsQ0FBQztZQUN2RCxJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7Z0JBQUMsT0FBTztZQUFDLENBQUM7WUFFNUIsTUFBTSxFQUFFLElBQUksRUFBRSxTQUFTLEVBQUUsR0FBRyxFQUFFLENBQUMsNkJBQTZCLENBQzNELFVBQVUsRUFDVixJQUFJLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxDQUN6QixDQUFDO1lBQ0YsTUFBTSxRQUFRLEdBQUcsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsRUFBRSxDQUFDO1lBQ3ZFLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsRUFBRSxHQUFHLENBQUMsQ0FBQztZQUVwRCxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsRUFBRTtnQkFDeEIsUUFBUTtnQkFDUixJQUFJLEVBQVMsY0FBYztnQkFDM0IsSUFBSTtnQkFDSixVQUFVLEVBQUcsVUFBVTthQUN2QixDQUFDLENBQUM7UUFDSixDQUFDO0lBQ0YsQ0FBQztJQUVEOztPQUVHO0lBQ0sscUJBQXFCLENBQUUsSUFBdUIsRUFBRSxVQUF5QjtRQUNoRixJQUFJLENBQUMsRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQUMsT0FBTztRQUFDLENBQUM7UUFFaEUsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDMUUsSUFBSSxDQUFDLFVBQVUsRUFBRSxDQUFDO1lBQUMsT0FBTztRQUFDLENBQUM7UUFFNUIsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1FBQzdDLE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztRQUNGLE1BQU0sUUFBUSxHQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FBQztRQUN2RSxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDLENBQUM7UUFFcEQsaUVBQWlFO1FBQ2pFLElBQUksVUFBVSxLQUFLLFFBQVEsSUFBSSxVQUFVLEtBQUssTUFBTSxFQUFFLENBQUM7WUFBQyxPQUFPO1FBQUMsQ0FBQztRQUVqRSxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsRUFBRTtZQUN4QixRQUFRO1lBQ1IsSUFBSSxFQUFXLFlBQVk7WUFDM0IsSUFBSTtZQUNKLFlBQVksRUFBRyxVQUFVO1lBQ3pCLFVBQVUsRUFBSyxVQUFVO1NBQ3pCLENBQUMsQ0FBQztJQUNKLENBQUM7SUFFRDs7T0FFRztJQUNLLHVCQUF1QixDQUFFLElBQXVCLEVBQUUsVUFBeUI7UUFDbEYsS0FBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFLENBQUM7WUFDaEQsTUFBTSxHQUFHLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBRSxDQUFDLENBQUUsQ0FBQztZQUNoQyxNQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMscUJBQXFCLENBQUMsR0FBRyxDQUFDLENBQUM7WUFDaEQsSUFBSSxDQUFDLE9BQU8sRUFBRSxDQUFDO2dCQUFDLFNBQVM7WUFBQyxDQUFDO1lBRTNCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxlQUFlLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLFdBQVcsQ0FBQztZQUN0RSxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7WUFDRixNQUFNLFFBQVEsR0FBRyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7WUFDdkUsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxDQUFDO1lBRXBELElBQUksQ0FBQyxPQUFPLENBQUMsT0FBTyxFQUFFO2dCQUNyQixRQUFRO2dCQUNSLElBQUksRUFBUyxXQUFXO2dCQUN4QixJQUFJO2dCQUNKLFVBQVUsRUFBRyxPQUFPO2dCQUNwQixPQUFPLEVBQU0sT0FBTyxDQUFDLE9BQU8sUUFBUSxFQUFFO2FBQ3RDLENBQUMsQ0FBQztRQUNKLENBQUM7SUFDRixDQUFDO0lBRUQ7O09BRUc7SUFDSyxzQkFBc0IsQ0FBRSxJQUE0QixFQUFFLFVBQXlCO1FBQ3RGLElBQUksQ0FBQyxFQUFFLENBQUMsc0JBQXNCLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFBQyxPQUFPO1FBQUMsQ0FBQztRQUV0RCxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMscUJBQXFCLENBQUMsSUFBSSxDQUFDLFdBQVksQ0FBQyxDQUFDO1FBQ2pFLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUFDLE9BQU87UUFBQyxDQUFDO1FBRTVCLE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztRQUNGLE1BQU0sUUFBUSxHQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FBQztRQUN2RSxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDLENBQUM7UUFFcEQsc0NBQXNDO1FBQ3RDLE1BQU0sS0FBSyxHQUFhLEVBQUUsQ0FBQztRQUMzQixLQUFLLE1BQU0sT0FBTyxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLENBQUM7WUFDMUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUNuQyxLQUFLLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDL0IsQ0FBQztRQUNGLENBQUM7UUFFRCxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsRUFBRTtZQUN4QixRQUFRO1lBQ1IsSUFBSSxFQUFTLGlCQUFpQjtZQUM5QixJQUFJO1lBQ0osVUFBVSxFQUFHLFVBQVU7WUFDdkIsT0FBTyxFQUFNLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1NBQzdCLENBQUMsQ0FBQztJQUNKLENBQUM7SUFFRDs7T0FFRztJQUNLLGlCQUFpQixDQUFFLElBQXdCLEVBQUUsVUFBeUI7UUFDN0UsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLElBQUksQ0FBQyxVQUFXLENBQUMsQ0FBQztRQUNoRSxJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7WUFBQyxPQUFPO1FBQUMsQ0FBQztRQUU1QixNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7UUFDRixNQUFNLFFBQVEsR0FBRyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7UUFDdkUsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxDQUFDO1FBRXBELElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxFQUFFO1lBQ3hCLFFBQVE7WUFDUixJQUFJLEVBQVMsUUFBUTtZQUNyQixJQUFJO1lBQ0osVUFBVSxFQUFHLFVBQVU7U0FDdkIsQ0FBQyxDQUFDO0lBQ0osQ0FBQztJQUVEOztPQUVHO0lBQ0ssaUJBQWlCLENBQUUsSUFBc0IsRUFBRSxVQUF5QjtRQUMzRSxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMscUJBQXFCLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQy9ELElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUFDLE9BQU87UUFBQyxDQUFDO1FBRTVCLE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztRQUNGLE1BQU0sUUFBUSxHQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FBQztRQUN2RSxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDLENBQUM7UUFFcEQsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLEVBQUU7WUFDeEIsUUFBUTtZQUNSLElBQUksRUFBUyxRQUFRO1lBQ3JCLElBQUk7WUFDSixVQUFVLEVBQUcsVUFBVTtTQUN2QixDQUFDLENBQUM7SUFDSixDQUFDO0lBRUQ7O09BRUc7SUFDSyxxQkFBcUIsQ0FBRSxJQUFtQjtRQUNqRCxtQkFBbUI7UUFDbkIsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDM0IsT0FBTyxJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUM5QyxDQUFDO1FBRUQscUVBQXFFO1FBQ3JFLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDekMsT0FBTyxJQUFJLENBQUMscUJBQXFCLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQ3BELENBQUM7UUFFRCwrQkFBK0I7UUFDL0IsSUFBSSxFQUFFLENBQUMseUJBQXlCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUN4QyxPQUFPLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDcEQsQ0FBQztRQUVELGdGQUFnRjtRQUNoRixJQUFJLElBQUksQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxXQUFXLEVBQUUsQ0FBQztZQUM3QyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOztPQUVHO0lBQ0ssT0FBTyxDQUFFLFFBQWdCLEVBQUUsSUFBYztRQUNoRCxJQUFJLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUNwQyxJQUFJLENBQUMsVUFBVSxDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsRUFBRSxDQUFDLENBQUM7UUFDbkMsQ0FBQztRQUVELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBRSxDQUFDO1FBQ2hELE1BQU0sV0FBVyxHQUFHLFFBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUU7WUFDckMsT0FBTyxDQUFDLENBQUMsUUFBUSxLQUFLLElBQUksQ0FBQyxRQUFRO2dCQUNsQyxDQUFDLENBQUMsSUFBSSxLQUFLLElBQUksQ0FBQyxJQUFJO2dCQUNwQixDQUFDLENBQUMsSUFBSSxLQUFLLElBQUksQ0FBQyxJQUFJLENBQUM7UUFDdkIsQ0FBQyxDQUFDLENBQUM7UUFFSCxJQUFJLENBQUMsV0FBVyxFQUFFLENBQUM7WUFDbEIsUUFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNyQixDQUFDO0lBQ0YsQ0FBQztJQUVEOztjQUVJO0lBQ0kseUJBQXlCLENBQUUsSUFBbUI7UUFDckQsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDM0IsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQztZQUN2Qiw4RUFBOEU7WUFDOUUsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUNwRCxJQUFJLFVBQVUsRUFBRSxDQUFDO2dCQUNoQixPQUFPLFVBQVUsQ0FBQztZQUNuQixDQUFDO1lBQ0QsT0FBTyxJQUFJLENBQUM7UUFDYixDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUN6QyxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMsZ0JBQWdCLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDMUMsT0FBTyxLQUFLLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDO1FBQ3hCLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7OztPQUdHO0lBQ0ssa0JBQWtCLENBQUUsVUFBb0IsRUFBRSxRQUFnQjtRQUNqRSxNQUFNLElBQUksR0FBRyxRQUFRLENBQUMsT0FBTyxDQUFDLFFBQVEsQ0FBQyxDQUFDO1FBQ3hDLE1BQU0sS0FBSyxHQUFHLFVBQVUsQ0FBQyxNQUFNLENBQUMsQ0FBQyxTQUFTLEVBQUUsRUFBRTtZQUM3QyxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsV0FBVyxDQUFDLEdBQUcsQ0FBQyxTQUFTLENBQUMsRUFBRSxNQUFNLENBQUM7WUFDdkQsTUFBTSxjQUFjLEdBQUcsTUFBTSxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsV0FBVyxDQUFDLEdBQUcsQ0FBQyxNQUFNLENBQUMsRUFBRSxRQUFRLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQztZQUNuRixNQUFNLFVBQVUsR0FBRyxjQUFjLENBQUMsQ0FBQyxDQUFDLGNBQWMsQ0FBQyxPQUFPLENBQUMsV0FBVyxFQUFFLEVBQUUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUM7WUFDeEYsTUFBTSxNQUFNLEdBQUcsVUFBVSxLQUFLLFNBQVMsSUFBSSxRQUFRLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxLQUFLLElBQUksQ0FBQztZQUNqRixPQUFPLE1BQU0sQ0FBQztRQUNmLENBQUMsQ0FBQyxDQUFDO1FBQ0gsTUFBTSxNQUFNLEdBQUcsS0FBSyxDQUFDLE1BQU0sS0FBSyxDQUFDLENBQUMsQ0FBQyxDQUFDLEtBQUssQ0FBRSxDQUFDLENBQUUsQ0FBQyxDQUFDLENBQUMsU0FBUyxDQUFDO1FBQzNELE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOztjQUVJO0lBQ0ksZUFBZSxDQUFFLElBQWlDO1FBQ3pELE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUMxQyxJQUFJLEtBQUssQ0FBQyxNQUFNLEtBQUssQ0FBQztZQUFFLE9BQU8sU0FBUyxDQUFDO1FBRXpDLDJDQUEyQztRQUMzQyxNQUFNLFFBQVEsR0FBRyxLQUFLLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDO1FBQ2pDLElBQUksSUFBSSxDQUFDLFdBQVcsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUNwQyxPQUFPLFFBQVEsQ0FBQztRQUNqQixDQUFDO1FBRUQsa0VBQWtFO1FBQ2xFLG9FQUFvRTtRQUNwRSx1REFBdUQ7UUFDdkQsSUFBSSxLQUFLLENBQUMsTUFBTSxHQUFHLENBQUMsRUFBRSxDQUFDO1lBQ3RCLE1BQU0sWUFBWSxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFFLENBQUMsQ0FBRSxDQUFDLENBQUM7WUFDNUQsTUFBTSxXQUFXLEdBQUcsWUFBWSxDQUFDLENBQUMsQ0FBQyxHQUFHLFlBQVksSUFBSSxLQUFLLENBQUMsS0FBSyxDQUFDLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUM7WUFDN0YsSUFBSSxXQUFXLElBQUksSUFBSSxDQUFDLFdBQVcsQ0FBQyxHQUFHLENBQUMsV0FBVyxDQUFDLEVBQUUsQ0FBQztnQkFDdEQsT0FBTyxXQUFXLENBQUM7WUFDcEIsQ0FBQztRQUNGLENBQUM7UUFFRCw2QkFBNkI7UUFDN0IsTUFBTSxRQUFRLEdBQUcsS0FBSyxDQUFFLEtBQUssQ0FBQyxNQUFNLEdBQUcsQ0FBQyxDQUFFLENBQUM7UUFDM0MsTUFBTSxVQUFVLEdBQWEsRUFBRSxDQUFDO1FBQ2hDLEtBQUssTUFBTSxDQUFFLElBQUksQ0FBRSxJQUFJLElBQUksQ0FBQyxXQUFXLEVBQUUsQ0FBQztZQUN6QyxJQUFJLElBQUksQ0FBQyxRQUFRLENBQUMsSUFBSSxRQUFRLEVBQUUsQ0FBQyxJQUFJLElBQUksS0FBSyxRQUFRLEVBQUUsQ0FBQztnQkFDeEQsVUFBVSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUN2QixDQUFDO1FBQ0YsQ0FBQztRQUNELHVEQUF1RDtRQUN2RCxtRUFBbUU7UUFDbkUscUVBQXFFO1FBQ3JFLGtFQUFrRTtRQUNsRSxtREFBbUQ7UUFDbkQsSUFBSSxVQUFVLENBQUMsTUFBTSxHQUFHLENBQUMsRUFBRSxDQUFDO1lBQzNCLE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyxrQkFBa0IsQ0FBQyxVQUFVLEVBQUUsSUFBSSxDQUFDLGFBQWEsRUFBRSxDQUFDLFFBQVEsQ0FBQyxDQUFDO1lBQ2pGLElBQUksS0FBSyxFQUFFLENBQUM7Z0JBQ1gsT0FBTyxLQUFLLENBQUM7WUFDZCxDQUFDO1FBQ0YsQ0FBQztRQUNELElBQUksVUFBVSxDQUFDLE1BQU0sR0FBRyxDQUFDLEVBQUUsQ0FBQztZQUMzQixPQUFPLFVBQVUsQ0FBRSxDQUFDLENBQUUsQ0FBQztRQUN4QixDQUFDO1FBRUQsT0FBTyxRQUFRLENBQUM7SUFDakIsQ0FBQztJQUVEOztlQUVLO0lBQ0csZ0JBQWdCLENBQUUsSUFBWTtRQUNyQyxPQUFPLElBQUksQ0FBRSxDQUFDLENBQUUsSUFBSSxHQUFHLElBQUksSUFBSSxDQUFFLENBQUMsQ0FBRSxJQUFJLEdBQUcsQ0FBQztJQUM3QyxDQUFDO0lBRUQ7OztlQUdLO0lBQ0csMkJBQTJCLENBQUUsUUFBaUM7UUFDckUsSUFBSSxDQUFDLFFBQVE7WUFBRSxPQUFPLFNBQVMsQ0FBQztRQUVoQyw2Q0FBNkM7UUFDN0MsSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUNwQyxNQUFNLEtBQUssR0FBYSxFQUFFLENBQUM7WUFDM0IsS0FBSyxNQUFNLE1BQU0sSUFBSSxRQUFRLENBQUMsT0FBTyxFQUFFLENBQUM7Z0JBQ3ZDLElBQUksRUFBRSxDQUFDLG1CQUFtQixDQUFDLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7b0JBQ3BFLE1BQU0sUUFBUSxHQUFHLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO29CQUNsQyxNQUFNLFFBQVEsR0FBRyxNQUFNLENBQUMsYUFBYSxDQUFDLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQztvQkFDakQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7b0JBQ3pDLEtBQUssQ0FBQyxJQUFJLENBQUMsR0FBRyxRQUFRLEdBQUcsUUFBUSxLQUFLLElBQUksRUFBRSxDQUFDLENBQUM7Z0JBQy9DLENBQUM7WUFDRixDQUFDO1lBQ0QsT0FBTyxLQUFLLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztRQUNsQyxDQUFDO1FBRUQsbUVBQW1FO1FBQ25FLHlEQUF5RDtRQUN6RCxJQUFJLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxRQUFRLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFFBQVEsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO1lBQzVFLE1BQU0sUUFBUSxHQUFHLFFBQVEsQ0FBQyxRQUFRLENBQUMsSUFBSSxDQUFDO1lBQ3hDLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxnQ0FBZ0MsQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLHlCQUF5QixDQUFDLENBQUM7WUFDN0YsSUFBSSxJQUFJLEVBQUUsQ0FBQztnQkFDVixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsK0JBQStCLENBQUMsSUFBSSxDQUFDLENBQUM7Z0JBQzVELElBQUksUUFBUTtvQkFBRSxPQUFPLFFBQVEsQ0FBQztZQUMvQixDQUFDO1lBQ0QsK0RBQStEO1lBQy9ELGdFQUFnRTtZQUNoRSxpRUFBaUU7WUFDakUseURBQXlEO1lBQ3pELE1BQU0sV0FBVyxHQUFHLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxRQUFRLENBQUMsQ0FBQztZQUN4RCxJQUFJLFdBQVcsQ0FBQyxNQUFNLEtBQUssUUFBUSxFQUFFLENBQUM7Z0JBQ3JDLE1BQU0sWUFBWSxHQUFHLFFBQVEsQ0FBQztnQkFDOUIsT0FBTyxZQUFZLENBQUM7WUFDckIsQ0FBQztZQUNELElBQUksV0FBVyxDQUFDLE1BQU0sS0FBSyxXQUFXLEVBQUUsQ0FBQztnQkFDeEMsSUFBSSxDQUFDLHlCQUF5QixDQUFDLFFBQVEsRUFBRSxRQUFRLEVBQUUsV0FBVyxDQUFDLENBQUM7Z0JBQ2hFLE1BQU0sa0JBQWtCLEdBQUcsU0FBUyxDQUFDO2dCQUNyQyxPQUFPLGtCQUFrQixDQUFDO1lBQzNCLENBQUM7WUFDRCw4REFBOEQ7WUFDOUQsSUFBSSxRQUFRLENBQUMsYUFBYSxJQUFJLFFBQVEsQ0FBQyxhQUFhLENBQUMsTUFBTSxHQUFHLENBQUMsRUFBRSxDQUFDO2dCQUNqRSxJQUFJLGtCQUFrQixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO29CQUN0QyxNQUFNLElBQUksR0FBRyxRQUFRLENBQUMsYUFBYSxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQztvQkFDcEUsT0FBTyxHQUFHLFFBQVUsSUFBTSxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBRyxHQUFHLENBQUM7Z0JBQ2hELENBQUM7Z0JBQ0QsOERBQThEO2dCQUM5RCx1Q0FBdUM7Z0JBQ3ZDLElBQUksQ0FBQyw0QkFBNEIsQ0FBQyxRQUFRLEVBQUUsUUFBUSxDQUFDLENBQUM7Z0JBQ3RELE1BQU0sb0JBQW9CLEdBQUcsU0FBUyxDQUFDO2dCQUN2QyxPQUFPLG9CQUFvQixDQUFDO1lBQzdCLENBQUM7WUFDRCxNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsK0JBQStCLENBQUMsUUFBUSxFQUFFLFFBQVEsQ0FBQyxDQUFDO1lBQ2hGLE9BQU8sY0FBYyxDQUFDO1FBQ3ZCLENBQUM7UUFFRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7O2VBRUs7SUFDRyw2QkFBNkIsQ0FBRSxTQUFtRDtRQUV6RixNQUFNLE1BQU0sR0FBMkIsRUFBRSxDQUFDO1FBRTFDLEtBQUssTUFBTSxNQUFNLElBQUksU0FBUyxDQUFDLE9BQU8sRUFBRSxDQUFDO1lBQ3hDLElBQUksQ0FBQyxFQUFFLENBQUMsd0JBQXdCLENBQUMsTUFBTSxDQUFDLEVBQUUsQ0FBQztnQkFDMUMsU0FBUztZQUNWLENBQUM7WUFFRCxLQUFLLE1BQU0sS0FBSyxJQUFJLE1BQU0sQ0FBQyxVQUFVLEVBQUUsQ0FBQztnQkFDdkMsSUFBSSxDQUFDLEtBQUssQ0FBQyxJQUFJLElBQUksQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUM7b0JBQUUsU0FBUztnQkFDMUQsSUFBSSxDQUFDLEtBQUssQ0FBQyxJQUFJO29CQUFFLFNBQVM7Z0JBRTFCLE1BQU0sU0FBUyxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO2dCQUNsQyxNQUFNLFlBQVksR0FBRyxJQUFJLENBQUMsMkJBQTJCLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxTQUFTLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxDQUFDO2dCQUVoRyxNQUFNLENBQUMsSUFBSSxDQUFDO29CQUNYLElBQUksRUFBTyxTQUFTO29CQUNwQixJQUFJLEVBQU8sWUFBWTtvQkFDdkIsUUFBUSxFQUFHLENBQUMsQ0FBQyxLQUFLLENBQUMsYUFBYSxJQUFJLENBQUMsQ0FBQyxLQUFLLENBQUMsV0FBVztvQkFDdkQscURBQXFEO29CQUNyRCxHQUFHLENBQUMsS0FBSyxDQUFDLGNBQWMsQ0FBQyxDQUFDLENBQUMsRUFBRSxJQUFJLEVBQUcsTUFBZSxFQUFFLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQztpQkFDM0QsQ0FBQyxDQUFDO1lBQ0osQ0FBQztZQUNELGlDQUFpQztZQUNqQyxNQUFNO1FBQ1AsQ0FBQztRQUVELE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7O2VBSUs7SUFDRyx3QkFBd0IsQ0FBRSxJQUF1QjtRQUN4RCxNQUFNLGVBQWUsR0FBRyxJQUFJLENBQUMsNEJBQTRCLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDaEUsSUFBSSxDQUFDLGVBQWUsRUFBRSxDQUFDO1lBQ3RCLE1BQU0sY0FBYyxHQUEyQixDQUFFO29CQUNoRCxJQUFJLEVBQU8sTUFBTTtvQkFDakIsSUFBSSxFQUFPLFdBQVc7b0JBQ3RCLFFBQVEsRUFBRyxLQUFLO29CQUNoQixJQUFJLEVBQU8sTUFBTTtpQkFDakIsQ0FBRSxDQUFDO1lBQ0osT0FBTyxjQUFjLENBQUM7UUFDdkIsQ0FBQztRQUNELE1BQU0sZUFBZSxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQztRQUN2RCxJQUFJLENBQUMseUJBQXlCLEdBQUcsUUFBUSxDQUFDLE9BQU8sQ0FBQyxlQUFlLENBQUMsYUFBYSxFQUFFLENBQUMsUUFBUSxDQUFDLENBQUM7UUFDNUYsSUFBSSxDQUFDO1lBQ0osTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLHVDQUF1QyxDQUFDLGVBQWUsQ0FBQyxDQUFDO1lBQzdFLE9BQU8sTUFBTSxDQUFDO1FBQ2YsQ0FBQztnQkFBUyxDQUFDO1lBQ1YsSUFBSSxDQUFDLHlCQUF5QixHQUFHLGVBQWUsQ0FBQztRQUNsRCxDQUFDO0lBQ0YsQ0FBQztJQUVEOztlQUVLO0lBQ0csdUNBQXVDLENBQUUsZUFBbUM7UUFDbkYsTUFBTSxNQUFNLEdBQTJCLEVBQUUsQ0FBQztRQUUxQywrQ0FBK0M7UUFDL0MsSUFBSSxFQUFFLENBQUMsb0JBQW9CLENBQUMsZUFBZSxDQUFDLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxlQUFlLENBQUM7WUFDbEYsRUFBRSxDQUFDLHFCQUFxQixDQUFDLGVBQWUsQ0FBQyxFQUFFLENBQUM7WUFDNUMsOERBQThEO1lBQzlELGtGQUFrRjtZQUNsRixLQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsZUFBZSxDQUFDLFVBQVUsQ0FBQyxNQUFNLEVBQUUsQ0FBQyxFQUFFLEVBQUUsQ0FBQztnQkFDNUQsTUFBTSxLQUFLLEdBQUcsZUFBZSxDQUFDLFVBQVUsQ0FBRSxDQUFDLENBQUUsQ0FBQztnQkFDOUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxJQUFJO29CQUFFLFNBQVM7Z0JBRTFCLHNDQUFzQztnQkFDdEMsSUFDQyxDQUFDLEtBQUssQ0FBQztvQkFDUCxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFVBQVU7b0JBQzNDLEtBQUssQ0FBQyxJQUFzQixDQUFDLElBQUksS0FBSyxNQUFNLEVBQzVDLENBQUM7b0JBQ0YsU0FBUztnQkFDVixDQUFDO2dCQUVELHlDQUF5QztnQkFDekMsTUFBTSxTQUFTLEdBQUcsRUFBRSxDQUFDLFlBQVksQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxLQUFLLENBQUM7Z0JBQ3hFLE1BQU0sWUFBWSxHQUFHLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLFNBQVMsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLENBQUM7Z0JBRWhHLE1BQU0sQ0FBQyxJQUFJLENBQUM7b0JBQ1gsSUFBSSxFQUFPLFNBQVM7b0JBQ3BCLElBQUksRUFBTyxZQUFZO29CQUN2QixRQUFRLEVBQUcsQ0FBQyxDQUFDLEtBQUssQ0FBQyxhQUFhLElBQUksQ0FBQyxDQUFDLEtBQUssQ0FBQyxXQUFXO29CQUN2RCxxREFBcUQ7b0JBQ3JELEdBQUcsQ0FBQyxLQUFLLENBQUMsY0FBYyxDQUFDLENBQUMsQ0FBQyxFQUFFLElBQUksRUFBRyxNQUFlLEVBQUUsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDO2lCQUMzRCxDQUFDLENBQUM7WUFDSixDQUFDO1FBQ0YsQ0FBQztRQUVELHFEQUFxRDtRQUNyRCxJQUFJLEVBQUUsQ0FBQyxpQkFBaUIsQ0FBQyxlQUFlLENBQUMsSUFBSSxFQUFFLENBQUMsa0JBQWtCLENBQUMsZUFBZSxDQUFDLEVBQUUsQ0FBQztZQUNyRixNQUFNLFdBQVcsR0FBRyxJQUFJLENBQUMsNkJBQTZCLENBQUMsZUFBZSxDQUFDLENBQUM7WUFDeEUsS0FBSyxNQUFNLEtBQUssSUFBSSxXQUFXLEVBQUUsQ0FBQztnQkFDakMsTUFBTSxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQztZQUNwQixDQUFDO1FBQ0YsQ0FBQztRQUVELE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7Ozs7T0FNRztJQUNLLHNCQUFzQixDQUFFLElBQWEsRUFBRSxVQUF5QjtRQUN2RSxJQUFJLEVBQUUsQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDOUMsSUFBSSxDQUFDLDJCQUEyQixDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsQ0FBQztRQUNwRCxDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsV0FBVyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDMUIsSUFBSSxDQUFDLCtCQUErQixDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsQ0FBQztRQUN4RCxDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMseUJBQXlCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUN4QyxJQUFJLENBQUMsOEJBQThCLENBQUMsSUFBSSxFQUFFLFVBQVUsQ0FBQyxDQUFDO1FBQ3ZELENBQUM7UUFDRCxJQUFJLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQy9CLElBQUksQ0FBQyxnQ0FBZ0MsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFDekQsQ0FBQztJQUNGLENBQUM7SUFFRDs7O09BR0c7SUFDSywyQkFBMkIsQ0FBRSxJQUF5QixFQUFFLFVBQXlCO1FBQ3hGLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDaEIsT0FBTztRQUNSLENBQUM7UUFDRCxNQUFNLFNBQVMsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztRQUNqQyxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxDQUM5QixDQUFDO1FBQ0YsTUFBTSxRQUFRLEdBQUcsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsRUFBRSxDQUFDO1FBQ3ZFLDBEQUEwRDtRQUMxRCxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsQ0FBRSxDQUFDLENBQUUsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxDQUFDO1FBRXJFLElBQUksSUFBcUMsQ0FBQztRQUMxQyxJQUFJLElBQUksQ0FBQyxlQUFlLEVBQUUsQ0FBQztZQUMxQixLQUFLLE1BQU0sTUFBTSxJQUFJLElBQUksQ0FBQyxlQUFlLEVBQUUsQ0FBQztnQkFDM0MsSUFBSSxNQUFNLENBQUMsS0FBSyxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsaUJBQWlCLEVBQUUsQ0FBQztvQkFDdEQsU0FBUztnQkFDVixDQUFDO2dCQUNELEtBQUssTUFBTSxJQUFJLElBQUksTUFBTSxDQUFDLEtBQUssRUFBRSxDQUFDO29CQUNqQyxJQUFJLENBQUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQzt3QkFDdkMsU0FBUztvQkFDVixDQUFDO29CQUNELE1BQU0sT0FBTyxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxVQUFVLENBQUUsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUUsQ0FBQztvQkFDbEYsSUFBSSxPQUFPLEVBQUUsQ0FBQzt3QkFDYixJQUFJLEdBQUcsT0FBTyxDQUFDO29CQUNoQixDQUFDO2dCQUNGLENBQUM7WUFDRixDQUFDO1FBQ0YsQ0FBQztRQUVELE1BQU0sSUFBSSxHQUE2QjtZQUN0QyxRQUFRO1lBQ1IsSUFBSTtTQUNKLENBQUM7UUFDRixJQUFJLElBQUksRUFBRSxDQUFDO1lBQ1YsSUFBSSxDQUFDLElBQUksR0FBRyxJQUFJLENBQUM7UUFDbEIsQ0FBQztRQUNELElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxHQUFHLENBQUMsU0FBUyxFQUFFLElBQUksQ0FBQyxDQUFDO0lBQ3JELENBQUM7SUFFRDs7OztPQUlHO0lBQ0ssK0JBQStCLENBQUUsSUFBa0IsRUFBRSxVQUF5QjtRQUNyRixNQUFNLEVBQUUsVUFBVSxFQUFFLEdBQUcsSUFBSSxDQUFDO1FBQzVCLElBQUksQ0FBQyxFQUFFLENBQUMsZ0JBQWdCLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLFVBQVUsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQ2pGLE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLGFBQWEsQ0FBRSxVQUFVLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBRSxDQUFDO1FBQ3hGLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUNYLE9BQU87UUFDUixDQUFDO1FBRUQsb0VBQW9FO1FBQ3BFLHNEQUFzRDtRQUN0RCxrREFBa0Q7UUFDbEQsTUFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLE1BQU0sQ0FBQztRQUM5QixJQUFJLEtBQTJCLENBQUM7UUFDaEMsSUFBSSxPQUFpQixDQUFDO1FBQ3RCLElBQUksRUFBRSxDQUFDLGtCQUFrQixDQUFDLFNBQVMsQ0FBQyxJQUFJLFNBQVMsQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUN4RCxLQUFLLEdBQUcsY0FBYyxTQUFTLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQzVDLE9BQU8sR0FBRyxDQUFFLFNBQVMsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFFLENBQUM7UUFDbkMsQ0FBQzthQUFNLElBQ04sRUFBRSxDQUFDLG1CQUFtQixDQUFDLFNBQVMsQ0FBQztZQUNqQyxFQUFFLENBQUMsWUFBWSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUM7WUFDL0IsRUFBRSxDQUFDLGtCQUFrQixDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUM7WUFDdkMsU0FBUyxDQUFDLE1BQU0sQ0FBQyxJQUFJLEVBQ3BCLENBQUM7WUFDRixNQUFNLFNBQVMsR0FBRyxTQUFTLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7WUFDN0MsS0FBSyxHQUFHLFVBQVUsU0FBUyxJQUFJLFNBQVMsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDckQsT0FBTyxHQUFHLENBQUUsU0FBUyxDQUFFLENBQUM7UUFDekIsQ0FBQzthQUFNLElBQUksRUFBRSxDQUFDLFdBQVcsQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUFDO1lBQ3RDLCtEQUErRDtZQUMvRCw4REFBOEQ7WUFDOUQsaUVBQWlFO1lBQ2pFLGlFQUFpRTtZQUNqRSwwREFBMEQ7WUFDMUQsTUFBTSxJQUFJLEdBQUcsU0FBUyxDQUFDLE1BQU0sQ0FBQztZQUM5QixJQUNDLElBQUk7Z0JBQ0osRUFBRSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQztnQkFDNUIsRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO2dCQUMxQixFQUFFLENBQUMsa0JBQWtCLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQztnQkFDbEMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLEVBQ2YsQ0FBQztnQkFDRixNQUFNLFNBQVMsR0FBRyxJQUFJLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7Z0JBQ3hDLEtBQUssR0FBRyxVQUFVLFNBQVMsSUFBSSxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO2dCQUNoRCxPQUFPLEdBQUcsQ0FBRSxTQUFTLENBQUUsQ0FBQztZQUN6QixDQUFDO2lCQUFNLENBQUM7Z0JBQ1AsT0FBTztZQUNSLENBQUM7UUFDRixDQUFDO2FBQU0sQ0FBQztZQUNQLE9BQU87UUFDUixDQUFDO1FBRUQsTUFBTSxFQUFFLElBQUksRUFBRSxTQUFTLEVBQUUsR0FBRyxFQUFFLENBQUMsNkJBQTZCLENBQzNELFVBQVUsRUFDVixJQUFJLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxDQUN6QixDQUFDO1FBQ0YsTUFBTSxRQUFRLEdBQUcsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsRUFBRSxDQUFDO1FBQ3ZFLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsRUFBRSxHQUFHLENBQUMsQ0FBQztRQUVwRCxLQUFLLE1BQU0sR0FBRyxJQUFJLFVBQVUsQ0FBQyxTQUFTLEVBQUUsQ0FBQztZQUN4QywwREFBMEQ7WUFDMUQsc0NBQXNDO1lBQ3RDLElBQUksU0FBNkIsQ0FBQztZQUNsQyw2REFBNkQ7WUFDN0QsOENBQThDO1lBQzlDLElBQUksT0FBTyxHQUFHLElBQUksQ0FBQztZQUNuQixJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztnQkFDMUIsU0FBUyxHQUFHLEdBQUcsQ0FBQyxJQUFJLENBQUM7WUFDdEIsQ0FBQztpQkFBTSxJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxHQUFHLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztnQkFDdkUsU0FBUyxHQUFHLEdBQUcsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDO1lBQ2pDLENBQUM7aUJBQU0sSUFBSSxFQUFFLENBQUMsZ0JBQWdCLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO2dCQUN0Rix3REFBd0Q7Z0JBQ3hELDZEQUE2RDtnQkFDN0Qsa0RBQWtEO2dCQUNsRCxNQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUMscUJBQXFCLENBQUUsR0FBRyxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFFLENBQUM7Z0JBQ2pHLElBQUksT0FBTyxFQUFFLENBQUM7b0JBQ2IsTUFBTSxTQUFTLEdBQUcsR0FBRyxDQUFDLFNBQVMsQ0FBRSxPQUFPLENBQUMsU0FBUyxJQUFJLENBQUMsQ0FBRSxDQUFDO29CQUMxRCxJQUFJLFNBQVMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFNBQVMsQ0FBQyxFQUFFLENBQUM7d0JBQzdDLFNBQVMsR0FBRyxTQUFTLENBQUMsSUFBSSxDQUFDO3dCQUMzQixPQUFPLEdBQUcsT0FBTyxDQUFDLElBQUksQ0FBQztvQkFDeEIsQ0FBQztvQkFDRCx1REFBdUQ7b0JBQ3ZELG9EQUFvRDtvQkFDcEQsd0RBQXdEO29CQUN4RCxJQUFJLFNBQVMsSUFBSSxPQUFPLENBQUMsYUFBYSxFQUFFLENBQUM7d0JBQ3hDLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxHQUFHLEVBQUUsU0FBUyxFQUFFLFVBQVUsQ0FBQyxDQUFDO29CQUM1RCxDQUFDO2dCQUNGLENBQUM7WUFDRixDQUFDO1lBQ0QsSUFBSSxDQUFDLFNBQVMsRUFBRSxDQUFDO2dCQUNoQixTQUFTO1lBQ1YsQ0FBQztZQUNELElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLENBQUM7Z0JBQzlCLElBQUksRUFBRyxPQUFPO2dCQUNkLFNBQVM7Z0JBQ1QsUUFBUTtnQkFDUixJQUFJO2dCQUNKLEtBQUs7Z0JBQ0wsT0FBTzthQUNQLENBQUMsQ0FBQztRQUNKLENBQUM7SUFDRixDQUFDO0lBRUQ7Ozs7OztPQU1HO0lBQ0sseUJBQXlCLENBQ2hDLElBQXVCLEVBQ3ZCLFNBQXdCLEVBQ3hCLFVBQXlCO1FBRXpCLE1BQU0sZUFBZSxHQUFHLElBQUksQ0FBQyxzQkFBc0IsQ0FBQyxTQUFTLENBQUMsQ0FBQztRQUMvRCxJQUFJLENBQUMsZUFBZSxFQUFFLENBQUM7WUFDdEIsT0FBTztRQUNSLENBQUM7UUFDRCxJQUFJLENBQUMsdUJBQXVCLENBQUMsSUFBSSxFQUFFLGVBQWUsRUFBRSxVQUFVLEVBQUUsU0FBUyxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxDQUFDO1FBQy9GLE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztRQUNGLElBQUksQ0FBQyxPQUFPLENBQUMsZUFBZSxFQUFFO1lBQzdCLFFBQVEsRUFBRyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFO1lBQ2hFLElBQUksRUFBTyxlQUFlO1lBQzFCLElBQUksRUFBTyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDO1lBQ2pELE9BQU8sRUFBSSw2QkFBNkI7U0FDeEMsQ0FBQyxDQUFDO0lBQ0osQ0FBQztJQUVEOzs7OztPQUtHO0lBQ0ssOEJBQThCLENBQUUsSUFBZ0MsRUFBRSxVQUF5QjtRQUNsRyxJQUFJLElBQXFDLENBQUM7UUFDMUMsSUFBSSxZQUFnQyxDQUFDO1FBRXJDLEtBQUssTUFBTSxJQUFJLElBQUksSUFBSSxDQUFDLFVBQVUsRUFBRSxDQUFDO1lBQ3BDLElBQ0MsQ0FBQyxFQUFFLENBQUMsb0JBQW9CLENBQUMsSUFBSSxDQUFDO2dCQUM5QixDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztnQkFDM0IsQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxXQUFXLENBQUMsRUFDakMsQ0FBQztnQkFDRixTQUFTO1lBQ1YsQ0FBQztZQUNELElBQUksSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssU0FBUyxFQUFFLENBQUM7Z0JBQ2xDLElBQUksR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUMsU0FBUyxDQUFFLElBQUksQ0FBQyxXQUFXLENBQUMsSUFBSSxDQUFFLENBQUM7WUFDMUUsQ0FBQztZQUNELElBQUksSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssVUFBVSxFQUFFLENBQUM7Z0JBQ25DLFlBQVksR0FBRyxJQUFJLENBQUMsV0FBVyxDQUFDLElBQUksQ0FBQztZQUN0QyxDQUFDO1FBQ0YsQ0FBQztRQUVELElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxZQUFZLEVBQUUsQ0FBQztZQUM1QixPQUFPO1FBQ1IsQ0FBQztRQUVELE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztRQUNGLE1BQU0sUUFBUSxHQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FBQztRQUN2RSxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDLENBQUM7UUFFcEQsSUFBSSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQztZQUM5QixJQUFJO1lBQ0osU0FBUyxFQUFHLFlBQVk7WUFDeEIsUUFBUTtZQUNSLElBQUk7WUFDSixLQUFLLEVBQU8sUUFBUTtZQUNwQixPQUFPLEVBQUssRUFBRTtTQUNkLENBQUMsQ0FBQztJQUNKLENBQUM7SUFFRDs7Ozs7O09BTUc7SUFDSyxnQ0FBZ0MsQ0FBRSxJQUF1QixFQUFFLFVBQXlCO1FBQzNGLElBQUksQ0FBQyxJQUFJLENBQUMseUJBQXlCLENBQUMsZ0JBQWdCLEVBQUUsQ0FBQztZQUN0RCxPQUFPO1FBQ1IsQ0FBQztRQUNELElBQ0MsQ0FBQyxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQztZQUMvQyxJQUFJLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssV0FBVyxFQUN4QyxDQUFDO1lBQ0YsT0FBTztRQUNSLENBQUM7UUFDRCxNQUFNLFNBQVMsR0FBRyxJQUFJLENBQUMsVUFBVSxDQUFDLFVBQVUsQ0FBQztRQUM3QyxJQUNDLENBQUMsRUFBRSxDQUFDLGdCQUFnQixDQUFDLFNBQVMsQ0FBQztZQUMvQixDQUFDLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxTQUFTLENBQUMsVUFBVSxDQUFDO1lBQ3BELFNBQVMsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxPQUFPLEVBQ3pDLENBQUM7WUFDRixPQUFPO1FBQ1IsQ0FBQztRQUNELElBQUksQ0FBQyxJQUFJLENBQUMsdUJBQXVCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUN6QyxPQUFPO1FBQ1IsQ0FBQztRQUVELE1BQU0sT0FBTyxHQUFhLEVBQUUsQ0FBQztRQUM3QixLQUFLLE1BQU0sR0FBRyxJQUFJLElBQUksQ0FBQyxTQUFTLEVBQUUsQ0FBQztZQUNsQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO2dCQUNyRCxPQUFPLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUN4QixDQUFDO1FBQ0YsQ0FBQztRQUVELE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsU0FBUyxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDOUIsQ0FBQztRQUNGLE1BQU0sUUFBUSxHQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FBQztRQUN2RSxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDLENBQUM7UUFFcEQsS0FBSyxNQUFNLEdBQUcsSUFBSSxTQUFTLENBQUMsU0FBUyxFQUFFLENBQUM7WUFDdkMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztnQkFDM0IsU0FBUztZQUNWLENBQUM7WUFDRCxJQUFJLENBQUMsb0JBQW9CLENBQUMsSUFBSSxDQUFDO2dCQUM5QixJQUFJLEVBQVEsWUFBWTtnQkFDeEIsU0FBUyxFQUFHLEdBQUcsQ0FBQyxJQUFJO2dCQUNwQixRQUFRO2dCQUNSLElBQUk7Z0JBQ0osS0FBSyxFQUFPLFFBQVE7Z0JBQ3BCLE9BQU87YUFDUCxDQUFDLENBQUM7UUFDSixDQUFDO0lBQ0YsQ0FBQztJQUVEOztPQUVHO0lBQ0ssdUJBQXVCLENBQUUsSUFBYTtRQUM3QyxJQUFJLE9BQU8sR0FBd0IsSUFBSSxDQUFDLE1BQU0sQ0FBQztRQUMvQyxPQUFPLE9BQU8sRUFBRSxDQUFDO1lBQ2hCLElBQ0MsRUFBRSxDQUFDLG1CQUFtQixDQUFDLE9BQU8sQ0FBQztnQkFDL0IsRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDO2dCQUM3QixPQUFPLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxXQUFXLEVBQ2hDLENBQUM7Z0JBQ0YsT0FBTyxJQUFJLENBQUM7WUFDYixDQUFDO1lBQ0QsT0FBTyxHQUFHLE9BQU8sQ0FBQyxNQUFNLENBQUM7UUFDMUIsQ0FBQztRQUNELE9BQU8sS0FBSyxDQUFDO0lBQ2QsQ0FBQztDQUNEO0FBN3lORCw4Q0E2eU5DIiwic291cmNlc0NvbnRlbnQiOlsiJ3VzZSBzdHJpY3QnO1xuXG5pbXBvcnQgKiBhcyBub2RlUGF0aCBmcm9tICdwYXRoJztcbmltcG9ydCAqIGFzIHRzIGZyb20gJ3R5cGVzY3JpcHQnO1xuaW1wb3J0IHtcblx0VHlwZU5vZGUsIFByb3BlcnR5SW5mbywgQW5hbHl6ZVJlc3VsdCwgQW5hbHl6ZUVycm9yLFxuXHREZWZpbml0aW9uSW5mbywgVXNhZ2VJbmZvLCBDb25zdHJ1Y3RvclBhcmFtSW5mbyxcblx0RURTSW5mbywgRmxvd0luZm8sIEluc3RydW1lbnRhdGlvbktpbmQsIEluc3RydW1lbnRhdGlvblBvaW50LFxuXHRJbnN0cnVtZW50YXRpb25TY29wZSwgUmVzb2x1dGlvbkVycm9yLCBDb2xsZWN0aW9uTWFuaWZlc3RFbnRyeSwgQnVpbGRlclZhbHVlXG59IGZyb20gJy4vdHlwZXMnO1xuaW1wb3J0IHtcblx0VHlwZUdyYXBoSW1wbCwgcmVzb2x2ZUdyYXBoVHlwZVJlZmVyZW5jZSwgR3JhcGhUeXBlUmVmZXJlbmNlUmVzdWx0IFxufSBmcm9tICcuL2dyYXBoJztcbmltcG9ydCB7XG5cdEluc3RydW1lbnRhdGlvblZvY2FidWxhcnksIFRhY3RpY2FQbHVnaW4sIG1lcmdlVGFjdGljYVBsdWdpbnNcbn0gZnJvbSAnLi9wbHVnaW5zJztcblxuaW50ZXJmYWNlIENvbGxlY3Rpb25JbmZvIHtcblx0dmFyaWFibGVOYW1lOiBzdHJpbmc7XG5cdHNvdXJjZUZpbGU6IHN0cmluZztcblx0cmVnaXN0cnlJbnRlcmZhY2VOYW1lPzogc3RyaW5nO1xuXHQvKiogMS1iYXNlZCBwb3NpdGlvbiBvZiB0aGUgY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgdmFyaWFibGUgZGVjbGFyYXRpb24gKi9cblx0bGluZTogbnVtYmVyO1xuXHRjb2x1bW46IG51bWJlcjtcbn1cblxuaW50ZXJmYWNlIEJ1aWxkZXJFeHBvcnQge1xuXHRuYW1lOiBzdHJpbmc7XG5cdHNvdXJjZUZpbGU6IHN0cmluZztcblx0ZGVmYXVsdEltcG9ydD86IGJvb2xlYW47XG59XG5cbmludGVyZmFjZSBCdWlsZGVyQ2FuZGlkYXRlIHtcblx0bmFtZTogc3RyaW5nO1xuXHRzb3VyY2VGaWxlOiBzdHJpbmc7XG5cdGtpbmQ6ICdyZWdpc3RyeU9mJyB8ICd0eXBlb2YnO1xuXHRmdWxsUGF0aDogc3RyaW5nO1xuXHRleHBvcnRzOiBCdWlsZGVyRXhwb3J0W107XG5cdGV4Y2x1ZGVkOiBib29sZWFuO1xufVxuXG4vKipcbiAqIExvY2F0aW9uL2NvZGUgY2FwdHVyZWQgYXQgYSBjbGFzcyBkZWNsYXJhdGlvbiwgdXNlZCB0byByZXNvbHZlXG4gKiBpbnN0cnVtZW50YXRpb24gcmVnaXN0cmF0aW9uIHNpdGVzIHRvIHRoZSBkZWNsYXJlZCBjbGFzc1xuICovXG5pbnRlcmZhY2UgSW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNsIHtcblx0a2luZD86IEluc3RydW1lbnRhdGlvbktpbmQ7XG5cdGxvY2F0aW9uOiBzdHJpbmc7XG5cdGNvZGU6IHN0cmluZztcbn1cblxuLyoqXG4gKiBSYXcgcmVnaXN0cmF0aW9uIHNpdGUgKGRlY29yYXRvciwgQVBQXyogcHJvdmlkZXIsIGNvbnN1bWVyLmFwcGx5KS5cbiAqIExvY2F0aW9uL2NvZGUgYXJlIHRoZSBzaXRlJ3Mgb3duOyBnZXRJbnN0cnVtZW50YXRpb25Qb2ludHMoKSByZXdyaXRlc1xuICogdGhlbSB0byB0aGUgY2xhc3MgZGVjbGFyYXRpb24gd2hlbiB0aGUgY2xhc3MgaXMgZGVjbGFyZWQgaW4tcHJvamVjdC5cbiAqL1xuaW50ZXJmYWNlIEluc3RydW1lbnRhdGlvblNpdGUge1xuXHRraW5kOiBJbnN0cnVtZW50YXRpb25LaW5kO1xuXHRjbGFzc05hbWU6IHN0cmluZztcblx0bG9jYXRpb246IHN0cmluZztcblx0Y29kZTogc3RyaW5nO1xuXHRzY29wZTogSW5zdHJ1bWVudGF0aW9uU2NvcGU7XG5cdHRhcmdldHM6IHN0cmluZ1tdO1xufVxuXG4vKipcbiAqIEEgbmFtZWQgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9uICh0eXBlIGFsaWFzLCBjbGFzcywgb3IgaW50ZXJmYWNlKVxuICogcmVjb3JkZWQgcGVyIGZpbGUsIHNvIHJlZmVyZW5jZXMgY2FuIGJlIHJlc29sdmVkIHRocm91Z2ggdGhlIGltcG9ydGluZ1xuICogZmlsZSdzIG93biBpbXBvcnRzIGluc3RlYWQgb2YgYSBwcm9ncmFtLXdpZGUgbGFzdC13aW5zIG5hbWUgbWFwIChGMTApLlxuICovXG5pbnRlcmZhY2UgUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB7XG5cdGtpbmQ6ICdhbGlhcycgfCAnY2xhc3MnIHwgJ2ludGVyZmFjZSc7XG5cdG5vZGU6IHRzLlR5cGVBbGlhc0RlY2xhcmF0aW9uIHwgdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHRzLkludGVyZmFjZURlY2xhcmF0aW9uO1xuXHQvKiogZmlsZSB0aGF0IGRlY2xhcmVzIHRoZSB0eXBlIOKAlCBuZXN0ZWQgcmVmZXJlbmNlcyByZXNvbHZlIGFnYWluc3QgaXQgKi9cblx0ZmlsZTogc3RyaW5nO1xufVxuXG4vKipcbiAqIE9uZSBpbXBvcnQgYmluZGluZyBvZiBhIHJlZmVyZW5jZWQgdHlwZTogdGhlIGxvY2FsIG5hbWUgdW5kZXIgd2hpY2ggdGhlXG4gKiBmaWxlIGtub3dzIGl0LCB0aGUgb3JpZ2luYWwgZXhwb3J0ZWQgbmFtZSBpbiB0aGUgc291cmNlIG1vZHVsZSwgYW5kIHRoZVxuICogc3BlY2lmaWVyIGl0IGNhbWUgZnJvbS5cbiAqL1xuaW50ZXJmYWNlIFJlZmVyZW5jZWRUeXBlSW1wb3J0IHtcblx0b3JpZ2luYWxOYW1lOiBzdHJpbmc7XG5cdHNwZWNpZmllcjogc3RyaW5nO1xuXHRpc05hbWVzcGFjZTogYm9vbGVhbjtcbn1cblxuLyoqXG4gKiBSZXN1bHQgb2YgcmVzb2x2aW5nIG9uZSBtb2R1bGUgc3BlY2lmaWVyIGZyb20gb25lIGNvbnRhaW5pbmcgZmlsZS5cbiAqL1xuaW50ZXJmYWNlIFJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbiB7XG5cdHJlc29sdmVkUGF0aDogc3RyaW5nO1xuXHRpc0V4dGVybmFsOiBib29sZWFuO1xufVxuXG50eXBlIENvbnN0cnVjdG9ySGFuZGxlciA9IHRzLkV4cHJlc3Npb24gfCB0cy5GdW5jdGlvbkRlY2xhcmF0aW9uIHwgdHMuQ2xhc3NEZWNsYXJhdGlvbjtcbnR5cGUgRnVuY3Rpb25Db25zdHJ1Y3RvckhhbmRsZXIgPSB0cy5GdW5jdGlvbkV4cHJlc3Npb24gfCB0cy5BcnJvd0Z1bmN0aW9uIHwgdHMuRnVuY3Rpb25EZWNsYXJhdGlvbjtcbnR5cGUgQ2xhc3NDb25zdHJ1Y3RvckhhbmRsZXIgPSB0cy5DbGFzc0V4cHJlc3Npb24gfCB0cy5DbGFzc0RlY2xhcmF0aW9uO1xuXG4vKipcbiAqIEdsb2JhbC9idWlsdGluIHR5cGUgbmFtZXMgdGhhdCBhcmUgc2FmZSB0byBlbWl0IGJhcmUgaW50byBnZW5lcmF0ZWQgZmlsZXNcbiAqIOKAlCB0aGV5IHJlc29sdmUgaW4gYW55IFR5cGVTY3JpcHQgY29tcGlsYXRpb24gd2l0aG91dCBhbiBpbXBvcnQuXG4gKi9cbmNvbnN0IEtOT1dOX0dMT0JBTF9UWVBFUyA9IG5ldyBTZXQoW1xuXHQnRGF0ZScsICdSZWdFeHAnLCAnRXJyb3InLCAnRXZhbEVycm9yJywgJ1JhbmdlRXJyb3InLCAnUmVmZXJlbmNlRXJyb3InLFxuXHQnU3ludGF4RXJyb3InLCAnVHlwZUVycm9yJywgJ1VSSUVycm9yJywgJ0FnZ3JlZ2F0ZUVycm9yJyxcblx0J01hcCcsICdTZXQnLCAnV2Vha01hcCcsICdXZWFrU2V0JywgJ1dlYWtSZWYnLCAnRmluYWxpemF0aW9uUmVnaXN0cnknLFxuXHQnUHJvbWlzZScsICdBcnJheScsICdSZWFkb25seUFycmF5JywgJ1JlY29yZCcsICdQYXJ0aWFsJywgJ1JlcXVpcmVkJyxcblx0J1JlYWRvbmx5JywgJ1BpY2snLCAnT21pdCcsICdFeGNsdWRlJywgJ0V4dHJhY3QnLCAnTm9uTnVsbGFibGUnLFxuXHQnUmV0dXJuVHlwZScsICdJbnN0YW5jZVR5cGUnLCAnUGFyYW1ldGVycycsICdDb25zdHJ1Y3RvclBhcmFtZXRlcnMnLFxuXHQnVGhpc1R5cGUnLCAnVGhpc1BhcmFtZXRlclR5cGUnLCAnT21pdFRoaXNQYXJhbWV0ZXInLFxuXHQnVXBwZXJjYXNlJywgJ0xvd2VyY2FzZScsICdDYXBpdGFsaXplJywgJ1VuY2FwaXRhbGl6ZScsXG5cdCdTdHJpbmcnLCAnTnVtYmVyJywgJ0Jvb2xlYW4nLCAnU3ltYm9sJywgJ0JpZ0ludCcsICdPYmplY3QnLCAnRnVuY3Rpb24nLFxuXHQnSXRlcmFibGUnLCAnSXRlcmF0b3InLCAnR2VuZXJhdG9yJywgJ0FzeW5jSXRlcmFibGUnLCAnQXN5bmNJdGVyYXRvcicsXG5cdCdBc3luY0dlbmVyYXRvcicsICdJdGVyYWJsZUl0ZXJhdG9yJywgJ0FzeW5jSXRlcmFibGVJdGVyYXRvcicsXG5cdCdQcm9wZXJ0eUtleScsICdBcnJheUJ1ZmZlcicsICdTaGFyZWRBcnJheUJ1ZmZlcicsICdEYXRhVmlldycsXG5cdCdJbnQ4QXJyYXknLCAnVWludDhBcnJheScsICdVaW50OENsYW1wZWRBcnJheScsICdJbnQxNkFycmF5Jyxcblx0J1VpbnQxNkFycmF5JywgJ0ludDMyQXJyYXknLCAnVWludDMyQXJyYXknLCAnRmxvYXQzMkFycmF5Jyxcblx0J0Zsb2F0NjRBcnJheScsICdCaWdJbnQ2NEFycmF5JywgJ0JpZ1VpbnQ2NEFycmF5JywgJ0ludGwnXG5dKTtcblxuLy8gR2VuZXJpYyBnbG9iYWxzIHdob3NlIGJhcmUgZW1pc3Npb24gd291bGQgYmUgaW52YWxpZCBUUyAoVFMyMzE0KTpcbi8vIGBuZXcgTWFwKClgIGNhcnJpZXMgbm8gdHlwZSBhcmd1bWVudHMsIHNvIHRoZSBmaWVsZCB0eXBlIGZpbGxzIHRoZW1cbi8vIHdpdGggdW5rbm93bi4gS2V5cyBtdXN0IGFsc28gYmUgbWVtYmVycyBvZiBLTk9XTl9HTE9CQUxfVFlQRVMuXG5jb25zdCBHRU5FUklDX0dMT0JBTF9ERUZBVUxUX0FSR1MgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPihbXG5cdFsgJ01hcCcsICdNYXA8dW5rbm93biwgdW5rbm93bj4nIF0sXG5cdFsgJ1dlYWtNYXAnLCAnV2Vha01hcDxvYmplY3QsIHVua25vd24+JyBdLFxuXHRbICdTZXQnLCAnU2V0PHVua25vd24+JyBdLFxuXHRbICdXZWFrU2V0JywgJ1dlYWtTZXQ8b2JqZWN0PicgXSxcblx0WyAnV2Vha1JlZicsICdXZWFrUmVmPG9iamVjdD4nIF0sXG5cdFsgJ0ZpbmFsaXphdGlvblJlZ2lzdHJ5JywgJ0ZpbmFsaXphdGlvblJlZ2lzdHJ5PHVua25vd24+JyBdLFxuXHRbICdQcm9taXNlJywgJ1Byb21pc2U8dW5rbm93bj4nIF0sXG5cdFsgJ0FycmF5JywgJ0FycmF5PHVua25vd24+JyBdLFxuXHRbICdSZWFkb25seUFycmF5JywgJ1JlYWRvbmx5QXJyYXk8dW5rbm93bj4nIF1cbl0pO1xuXG4vLyBCb3VuZCBmb3IgY2hhc2luZyByZS1leHBvcnQgYmFycmVscyAoZXhwb3J0IHsgWCB9IGZyb20gJ+KApicsIGV4cG9ydCAqIGZyb20gJ+KApicpXG5jb25zdCBNQVhfUkVFWFBPUlRfQ0hBU0VfREVQVEggPSA1O1xuLy8gQm91bmQgZm9yIHdhbGtpbmcgY2xhc3MvaW50ZXJmYWNlIGV4dGVuZHMgY2hhaW5zIGR1cmluZyByZWZlcmVuY2VkLXR5cGVcbi8vIGV4cGFuc2lvbiAoaW5oZXJpdGVkIG1lbWJlcnMgbWVyZ2UgaW50byB0aGUgZXhwYW5kZWQgZmllbGRzKVxuY29uc3QgTUFYX0hFUklUQUdFX0RFUFRIID0gODtcblxuLyoqXG4gKiBBU1QgQW5hbHl6ZXIgZm9yIGZpbmRpbmcgTW5lbW9uaWNhIGRlZmluZSgpIGFuZCBkZWNvcmF0ZSgpIGNhbGxzXG4gKlxuICogRnJhbWV3b3JrLWJsaW5kIGJ5IGNvbnN0cnVjdGlvbjogaW5zdHJ1bWVudGF0aW9uIGRldGVjdGlvbiB2b2NhYnVsYXJ5XG4gKiAoaW50ZXJmYWNlIG5hbWVzLCBkZWNvcmF0b3IgbmFtZXMsIHByb3ZpZGVyIHRva2VucywgbWlkZGxld2FyZSB3aXJpbmcpXG4gKiBjb21lcyBlbnRpcmVseSBmcm9tIHBsdWdpbnMg4oCUIHdpdGggbm9uZSBsb2FkZWQsIHplcm8gcG9pbnRzIGFyZSBjb2xsZWN0ZWQuXG4gKi9cbmV4cG9ydCBjbGFzcyBNbmVtb25pY2FBbmFseXplciB7XG5cdHByaXZhdGUgZXJyb3JzOiBBbmFseXplRXJyb3JbXSA9IFtdO1xuXHRwcml2YXRlIGdyYXBoID0gbmV3IFR5cGVHcmFwaEltcGwoKTtcblx0cHJpdmF0ZSBkZWZpbml0aW9ucyA9IG5ldyBNYXA8c3RyaW5nLCBEZWZpbml0aW9uSW5mbz4oKTtcblx0cHJpdmF0ZSB1c2FnZXMgPSBuZXcgTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+KCk7XG5cdHByaXZhdGUgZWRzVXNhZ2VzID0gbmV3IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4oKTtcblx0cHJpdmF0ZSBmbG93VXNhZ2VzID0gbmV3IE1hcDxzdHJpbmcsIEZsb3dJbmZvW10+KCk7XG5cdC8vIEVuY2xvc2luZyBtbmVtb25pY2Egc2NvcGUgZm9yIEVEUyBrZXlpbmc6IGRlZmluZSgpL2xhenkoKSBjYWxsIG5vZGVcblx0Ly8gb3IgQGRlY29yYXRlKCktZWQgY2xhc3MgZGVjbGFyYXRpb24gLT4gZnVsbFBhdGggb2YgdGhlIHR5cGUgaXQgb3ducy5cblx0Ly8gUG9wdWxhdGVkIG9uIHRoZSBkZWZpbml0aW9ucyBwYXNzOyBBU1Qgbm9kZXMgcGVyc2lzdCBhY3Jvc3MgcGFzc2VzLFxuXHQvLyBzbyBlbnRyaWVzIHN0YXkgdmFsaWQgYWZ0ZXIgcmVzZXRVc2FnZXMoKS5cblx0cHJpdmF0ZSBlZHNTY29wZUJ5Tm9kZSA9IG5ldyBNYXA8dHMuTm9kZSwgc3RyaW5nPigpO1xuXHQvLyBTYW1lLWZpbGUgZnVuY3Rpb24gYmluZGluZ3MgKGBmaWxlTmFtZSNuYW1lYCAtPiBmdW5jdGlvbiBub2RlKSBmb3Jcblx0Ly8gcmVzb2x2aW5nIHdyYXAoZm4pIGFyZ3VtZW50cyBzeW50YWN0aWNhbGx5IOKAlCB0aGUgY2hlY2tlciBzdGF5cyB1bnVzZWRcblx0cHJpdmF0ZSBmdW5jdGlvbkJpbmRpbmdzID0gbmV3IE1hcDxzdHJpbmcsIHRzLkZ1bmN0aW9uTGlrZURlY2xhcmF0aW9uPigpO1xuXHQvLyBDb25zdHJ1Y3RvciB2YWx1ZXMgYnkgZGVjbGFyaW5nIGZpbGUgYW5kIGV4cG9ydGVkL2xvY2FsIG5hbWUuIFJlc29sdXRpb25cblx0Ly8gdXNlcyB0aGUgc2FtZSBpbXBvcnQgYW5kIHJlLWV4cG9ydCB3aXJpbmcgYXMgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9ucy5cblx0cHJpdmF0ZSBjb25zdHJ1Y3RvckJpbmRpbmdzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIENvbnN0cnVjdG9ySGFuZGxlcj4+KCk7XG5cdC8vIHdyYXAgY2FsbCBub2RlIC0+IGxvY2F0aW9uIG9mIHRoZSBlbmNsb3Npbmcgd3JhcCBzaXRlIChwbHVzIHRoYXRcblx0Ly8gc2l0ZSdzIHNjb3BlIGF0dHJpYnV0aW9uKSwgc28gbmVzdGVkIHdyYXAoKSBjYWxscyBpbnNpZGUgYSB3cmFwcGVkXG5cdC8vIGJvZHkgY2FycnkgdGhlIGB2aWFgIGxpbmsg4oCUIGFuZCBpbmhlcml0IHRoZSBzY29wZSB3aGVuIHRoZXkgaGF2ZVxuXHQvLyBub25lIG9mIHRoZWlyIG93blxuXHRwcml2YXRlIG5lc3RlZFdyYXBWaWEgPSBuZXcgTWFwPHRzLk5vZGUsIHsgdmlhOiBzdHJpbmc7IHNjb3BlPzogc3RyaW5nIH0+KCk7XG5cdC8vIHdyYXAgY2FsbCBub2RlIC0+IGl0cyBjb2xsZWN0ZWQgZW50cnksIHNvIGEgbGV4aWNhbGx5IG5lc3RlZCB3cmFwXG5cdC8vICh2aXNpdGVkIEJFRk9SRSB0aGUgb3V0ZXIgd3JhcCBjYWxsLCBwZXIgc291cmNlIG9yZGVyKSBnZXRzIGl0c1xuXHQvLyBgdmlhYCBiYWNrLXBhdGNoZWQgd2hlbiB0aGUgb3V0ZXIgYm9keSBpcyBhbmFseXNlZFxuXHRwcml2YXRlIHdyYXBFbnRyeUJ5Tm9kZSA9IG5ldyBNYXA8dHMuTm9kZSwgRURTSW5mbz4oKTtcblx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHM6IHZhcmlhYmxlTmFtZSAtPiBmdWxsUGF0aCBvZiB0aGUgdHlwZSBpdCBob2xkc1xuXHRwcml2YXRlIHZhcmlhYmxlVG9UeXBlTWFwID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0Ly8gRXhwb3J0ZWQgYnVpbGRlciB2YWx1ZXMgYW5kIHRoZWlyIHRyYW5zaXRpdmUgc2VsZi1yZWZlcmVuY2UgZXhjbHVzaW9ucy5cblx0cHJpdmF0ZSBidWlsZGVyQ2FuZGlkYXRlczogQnVpbGRlckNhbmRpZGF0ZVtdID0gW107XG5cdHByaXZhdGUgZXhjbHVkZWRUeXBlUGF0aHMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0cHJpdmF0ZSBnZW5lcmF0ZWRUeXBlSW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBTZXQ8c3RyaW5nPj4oKTtcblx0Ly8gVHJhY2sgbW5lbW9uaWNhIG1vZHVsZS1vYmplY3QgdmFyaWFibGVzIChlLmcuLCBpbXBvcnQgeyBtbmVtb25pY2EgfSBmcm9tICdtbmVtb25pY2EnOyBjb25zdCBtID0gbW5lbW9uaWNhKVxuXHRwcml2YXRlIG1vZHVsZU9iamVjdFZhcmlhYmxlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHQvLyBmaWxlIC0+IChsb2NhbCBuYW1lIC0+IGltcG9ydGVkIG5hbWUpIGZvciBuYW1lZCBpbXBvcnRzIGZyb21cblx0Ly8gJ21uZW1vbmljYScg4oCUIGltcG9ydC1hd2FyZW5lc3MgZm9yIHRoZSBjb25zdHJ1Y3Rpb24tZnVuY3Rpb25cblx0Ly8gcmVjb2duaXRpb24gKGNhbGwvYXBwbHkvYmluZCkgYW5kIHRoZSB1dGlscyBmb3JtcyAobWVyZ2UvZm9yayk6XG5cdC8vIHVzZXJsYW5kIGZ1bmN0aW9ucyB3aXRoIHRob3NlIG5hbWVzIG11c3QgbmV2ZXIgbWF0Y2hcblx0cHJpdmF0ZSBtbmVtb25pY2FOYW1lZEltcG9ydHMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgc3RyaW5nPj4oKTtcblx0Ly8gVHJhY2sgaW1wb3J0ZWQgYWxpYXNlcyBvZiBjcmVhdGVUeXBlc0NvbGxlY3Rpb24gKGUuZy4sIGltcG9ydCB7IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbiBhcyBjdGMgfSlcblx0cHJpdmF0ZSBjcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0Ly8gVHJhY2sgY3VzdG9tIGNvbGxlY3Rpb24gdmFyaWFibGVzOiB2YXJpYWJsZU5hbWUgLT4gY29sbGVjdGlvbklkXG5cdHByaXZhdGUgY29sbGVjdGlvblZhcmlhYmxlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdC8vIFRyYWNrIGN1c3RvbSBjb2xsZWN0aW9uIG1ldGFkYXRhIGZvciBPcHRpb24gQiByZWdpc3RyeSBlbWlzc2lvblxuXHRwcml2YXRlIGNvbGxlY3Rpb25JbmZvID0gbmV3IE1hcDxzdHJpbmcsIENvbGxlY3Rpb25JbmZvPigpO1xuXHRwcml2YXRlIGNvbGxlY3Rpb25Db3VudGVyID0gMDtcblx0Ly8gSW5zdHJ1bWVudGF0aW9uIGNvbGxlY3Rpb24gKHN5bnRhY3RpYyBvbmx5IOKAlCBubyB0eXBlIGNoZWNrZXIpOlxuXHQvLyBldmVyeSBuYW1lZCBjbGFzcyBkZWNsYXJhdGlvbiBieSBzaW1wbGUgbmFtZSwgZm9yIHJlc29sdmluZ1xuXHQvLyByZWdpc3RyYXRpb24gc2l0ZXMgdG8gZGVjbGFyYXRpb24gbG9jYXRpb25zIChiZXN0IGVmZm9ydCwgbGFzdCB3aW5zKVxuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMgPSBuZXcgTWFwPHN0cmluZywgSW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNsPigpO1xuXHQvLyBSZWdpc3RyYXRpb24gc2l0ZXM6IGRlY29yYXRvciBhcHBsaWNhdGlvbnMsIHByb3ZpZGVyLXRva2VuIG9iamVjdFxuXHQvLyBsaXRlcmFscywgY29uc3VtZXIuYXBwbHkoKSBtaWRkbGV3YXJlIHdpcmluZ1xuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvblNpdGVzOiBJbnN0cnVtZW50YXRpb25TaXRlW10gPSBbXTtcblx0Ly8gTWVyZ2VkIHBsdWdpbiB2b2NhYnVsYXJ5IGZvciBpbnN0cnVtZW50YXRpb24gZGV0ZWN0aW9uIChlbXB0eSB3aGVuXG5cdC8vIG5vIHBsdWdpbnMgd2VyZSBwYXNzZWQg4oCUIHRoZSBhbmFseXplciB0aGVuIGNvbGxlY3RzIG5vIHBvaW50cylcblx0cHJpdmF0ZSBpbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5OiBJbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5O1xuXHQvLyBSZWZlcmVuY2VkLXR5cGUgcmVzb2x1dGlvbiAoRjEwKTogcGVyLWZpbGUgZGVjbGFyYXRpb25zIGFuZCBpbXBvcnRzLlxuXHQvLyBBIHR5cGUgbmFtZSB1c2VkIGluIGZpbGUgWCByZXNvbHZlcyB0aHJvdWdoIFgncyBvd24gaW1wb3J0IHN0YXRlbWVudHNcblx0Ly8gZmlyc3QgKHJlbGF0aXZlICsgdHNjb25maWctcGF0aHMsIHZpYSB0cy5yZXNvbHZlTW9kdWxlTmFtZSksIHRoZW5cblx0Ly8gWCdzIGxvY2FsIGRlY2xhcmF0aW9ucywgdGhlbiDigJQgb25seSB3aGVuIG5vdGhpbmcgaW1wb3J0cyBvciBkZWNsYXJlc1xuXHQvLyB0aGUgbmFtZSDigJQgdGhlIHVuaXF1ZSBzYW1lLW5hbWVkIGRlY2xhcmF0aW9uIGFjcm9zcyBzY2FubmVkIGZpbGVzLlxuXHQvLyBHZW51aW5lIGFtYmlndWl0eSBvciBhbiB1bnJlc29sdmFibGUgcmVmZXJlbmNlIHlpZWxkcyBgdW5rbm93bmAsIG5ldmVyXG5cdC8vIGEgYmFyZSBlbWl0dGVkIG5hbWU6IGdlbmVyYXRlZCB0eXBlcy50cyBjYXJyaWVzIG5vIGltcG9ydHMgb2YgaXRzIG93bi5cblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZURlY2xzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24+PigpO1xuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlSW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZUltcG9ydD4+KCk7XG5cdC8vIGZpbGUgLT4gKGV4cG9ydGVkIG5hbWUgLT4gcmUtZXhwb3J0IHNwZWNpZmllcikgZm9yIGBleHBvcnQgeyBYIH0gZnJvbSAn4oCmJ2Bcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZVJlRXhwb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBmaWxlIC0+IHNwZWNpZmllcnMgb2YgYGV4cG9ydCAqIGZyb20gJ+KApidgXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmdbXT4oKTtcblx0Ly8gZmlsZSAtPiAoZXhwb3J0ZWQgbmFtZSAtPiBsb2NhbCBuYW1lKSBmb3IgYGV4cG9ydCB7IFggYXMgWSB9YFxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBmaWxlIC0+IChuYW1lc3BhY2UgbmFtZSAtPiBuYW1lc3BhY2UgZGVjbGFyYXRpb24pIOKAlCBtaWRkbGUgc2VnbWVudHNcblx0Ly8gb2YgcXVhbGlmaWVkIHJlZmVyZW5jZXMgKG1vZGVscy5Jbm5lci5DcmF0ZSkgZGVzY2VuZCB0aHJvdWdoIHRoZXNlXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHRzLk1vZHVsZURlY2xhcmF0aW9uPj4oKTtcblx0Ly8gZmlsZSAtPiAobmFtZXNwYWNlIG5hbWUgLT4gc3BlY2lmaWVyKSBmb3IgYGV4cG9ydCAqIGFzIG5zIGZyb20gJ+KApidgXG5cdC8vIGJhcnJlbHMg4oCUIGEgbmVzdGVkIG1vZHVsZSBuYW1lc3BhY2Ugb25lIHNlZ21lbnQgZGVlcFxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlU3RhcnMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgc3RyaW5nPj4oKTtcblx0Ly8gYCR7Y29udGFpbmluZ0ZpbGV9Ojoke3NwZWNpZmllcn1gIC0+IHJlc29sdXRpb24gKHVuZGVmaW5lZCA9IGZhaWxlZClcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZVJlc29sdXRpb25DYWNoZSA9IG5ldyBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZVJlc29sdXRpb24gfCB1bmRlZmluZWQ+KCk7XG5cdC8vIGZpbGUgLT4gKGNvbnN0IG5hbWUgLT4gYXJyYXkgbGl0ZXJhbCkgZm9yIGNvbnN0cyB3aXRoIGFycmF5LWxpdGVyYWxcblx0Ly8gaW5pdGlhbGl6ZXJzIChgYXMgY29uc3RgIC8gYHNhdGlzZmllc2AgdW53cmFwcGVkKSwgc28gYVxuXHQvLyBgdHlwZW9mIHN0YXR1c0xpc3RbbnVtYmVyXWAgZmllbGQgdHlwZSBleHBhbmRzIHRvIHRoZSBlbGVtZW50IGxpdGVyYWxcblx0Ly8gdW5pb24gaW5zdGVhZCBvZiBsZWFraW5nIGEgYmFyZSB1bnJlc29sdmFibGUgYHR5cGVvZmAgcXVlcnkgaW50byB0aGVcblx0Ly8gZ2VuZXJhdGVkIGZpbGUuIERlY2xhcmF0aW9ucyBwZXJzaXN0IGFjcm9zcyBwYXNzZXMg4oCUIGVudHJpZXMgc3RheVxuXHQvLyB2YWxpZCBhZnRlciByZXNldFVzYWdlcygpLCBzYW1lIGFzIHJlZmVyZW5jZWRUeXBlRGVjbHNcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24+PigpO1xuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlQ29tcGlsZXJPcHRpb25zOiB0cy5Db21waWxlck9wdGlvbnM7XG5cdC8vIEZpbGUgd2hvc2UgQVNUIGlzIGN1cnJlbnRseSBiZWluZyB2aXNpdGVkOyByZWZlcmVuY2VzIHJlc29sdmUgYWdhaW5zdCBpdFxuXHRwcml2YXRlIGN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSAnJztcblx0Ly8gQWxpYXMgbmFtZXMgY3VycmVudGx5IGJlaW5nIGV4cGFuZGVkIChjeWNsZSBndWFyZClcblx0cHJpdmF0ZSBleHBhbmRpbmdSZWZlcmVuY2VkQWxpYXNlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHQvLyBNbmVtb25pY2EtZ3JhcGggaWRlbnRpdHkgbGF3IChoYXJkIGZhaWwpOiBldmVyeSBkZWZpbmUoKS9sYXp5KCkvXG5cdC8vIEBkZWNvcmF0ZSgpIHNpdGUga2V5ZWQgYnkgaXRzIHJ1bnRpbWUgbmFtZXNwYWNlIChjb2xsZWN0aW9uIHJvb3RzOlxuXHQvLyBgPGNvbGxlY3Rpb24+Ojo8bmFtZT5gOyBzdWJ0eXBlczogYDxwYXJlbnRGdWxsUGF0aD4uPG5hbWU+YCkuIFR3b1xuXHQvLyBzaXRlcyBpbiBvbmUgbmFtZXNwYWNlIGFyZSBhIHNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZSDigJQgdGhlIHJ1bnRpbWVcblx0Ly8gdGhyb3dzIEFMUkVBRFlfREVDTEFSRUQg4oCUIGFuZCBtdXN0IGFib3J0IGdlbmVyYXRpb24uXG5cdHByaXZhdGUgZGVmaW5lU2l0ZXMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nW10+KCk7XG5cdC8vIE1uZW1vbmljYS1ncmFwaCByZWZlcmVuY2VzIHRoYXQgc3RheWVkIGFtYmlndW91cyBhZnRlciBwYXRoLWF3YXJlXG5cdC8vIHJlc29sdXRpb24gb3IgcmVzb2x2ZWQgdG8gbm90aGluZyAoaGFyZC1mYWlsIGNsYXNzIDIpXG5cdHByaXZhdGUgZ3JhcGhSZWZlcmVuY2VFcnJvcnM6IFJlc29sdXRpb25FcnJvcltdID0gW107XG5cdC8vIEd1YXJkcyBsb29rdXAoKS1wYXRoIHZhbGlkYXRpb24gc28gaXQgcnVucyBvbmNlIHBlciB1c2FnZXMgcGFzc1xuXHQvLyAoZ2V0UmVzb2x1dGlvbkVycm9ycyBtYXkgYmUgY2FsbGVkIHJlcGVhdGVkbHkpOyByZXNldFVzYWdlcyByZS1hcm1zIGl0XG5cdHByaXZhdGUgbG9va3VwUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHQvLyBMaXRlcmFsIGxvb2t1cCgpIGNhbGwgc2l0ZXMgd2l0aCB0aGVpciByZXNvbHZlZCBwYXRocy4gS2VwdCBhcGFydCBmcm9tXG5cdC8vIHRoZSB1c2FnZXMgbWFwIG9uIHB1cnBvc2U6IGFkZFVzYWdlIGRyb3BzIHBhdGhzIHRoZSBncmFwaCBkb2VzIG5vdFxuXHQvLyBrbm93ICh1c2FnZXMuanNvbiBpbmRleGVzIHJlZmVyZW5jZXMgdG8gS05PV04gdHlwZXMpLCBidXQgYW4gdW5rbm93blxuXHQvLyBsb29rdXAgcGF0aCBpcyBleGFjdGx5IHRoZSBoYXJkLWZhaWwgY2FzZSDigJQgdGhlIHJ1bnRpbWUgcmV0dXJuc1xuXHQvLyB1bmRlZmluZWQgdGhlcmUgYW5kIHRoZSBUeXBlRXJyb3IgYXJyaXZlcyBvbmUgbGluZSBsYXRlclxuXHRwcml2YXRlIGxvb2t1cFJlZmVyZW5jZXM6IHsgcGF0aDogc3RyaW5nOyBsb2NhdGlvbjogc3RyaW5nIH1bXSA9IFtdO1xuXHQvLyBHdWFyZHMgcGxhaW4tVFMgcmVmZXJlbmNlIHZhbGlkYXRpb24gc28gaXQgcnVucyBvbmNlIHBlciB1c2FnZXMgcGFzc1xuXHQvLyAoZ2V0UmVzb2x1dGlvbkVycm9ycyBtYXkgYmUgY2FsbGVkIHJlcGVhdGVkbHkpOyByZXNldFVzYWdlcyByZS1hcm1zIGl0XG5cdHByaXZhdGUgcGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHQvLyBQbGFpbi1UUyB0eXBlIHJlZmVyZW5jZSBzaXRlcyB3aG9zZSByZXNvbHV0aW9uIGZlbGwgdGhyb3VnaCBpbXBvcnRzLFxuXHQvLyBsb2NhbHMsIHRoZSBwcm9ncmFtLXdpZGUgc2NhbiwgYW5kIHRoZSBncmFwaCB0byBhIHNvZnQgYHVua25vd25gLlxuXHQvLyBWYWxpZGF0ZWQgbGF6aWx5IGZyb20gZ2V0UmVzb2x1dGlvbkVycm9ycyBhZ2FpbnN0IHRoZSBjb21wbGV0ZVxuXHQvLyBkZWNsYXJhdGlvbiBtYXA6IGEgbmFtZSBzZXZlcmFsIHByb2plY3Qtc291cmNlIGZpbGVzIGRlY2xhcmUg4oCUIHdpdGhcblx0Ly8gbm8gaW1wb3J0IGluIHRoZSByZWZlcmVuY2luZyBmaWxlIHRvIGFuY2hvciBpdCDigJQgaXMgdGhlIHBsYWluLVRTXG5cdC8vIGFtYmlndWl0eSBoYXJkLWZhaWwgY2xhc3MgKG9uZSB0aWVyIGJlbG93IHRoZSBncmFwaCBpZGVudGl0eSBsYXcpO1xuXHQvLyBhYnNlbmNlIChnaG9zdCBuYW1lcykgc3RheXMgc29mdC4gUmVjb3JkaW5nIGhhcHBlbnMgb24gZXZlcnkgcGFzcyxcblx0Ly8gdGhlIHZlcmRpY3Qgb25seSBoZXJlIOKAlCBwYXNzIDEgc2VlcyBhbiBpbmNvbXBsZXRlIGRlY2xhcmF0aW9uIG1hcCxcblx0Ly8gc28gb25seSB0aGUgdXNhZ2VzIHBhc3MgaXMgYXV0aG9yaXRhdGl2ZSAobWlycm9ycyBsb29rdXAgcmVmZXJlbmNlcylcblx0cHJpdmF0ZSBwbGFpblR5cGVSZWZlcmVuY2VzOiB7IG5hbWU6IHN0cmluZzsgbG9jYXRpb246IHN0cmluZzsgZmlsZTogc3RyaW5nIH1bXSA9IFtdO1xuXHQvLyBQZXItZmlsZSB0b3AtbGV2ZWwgdmFyaWFibGUgLT4gbW5lbW9uaWNhIGZ1bGxQYXRoIGJpbmRpbmdzICh2YWx1ZVxuXHQvLyBzY29wZSk6IGBjb25zdCBBZGRyZXNzID0gVXNlci5kZWZpbmUoJ0FkZHJlc3MnLCDigKYpYCBtYWtlcyBgQWRkcmVzc2Bcblx0Ly8gZGVub3RlIFVzZXIuQWRkcmVzcyB3aGVyZXZlciB0aGF0IGZpbGUncyByZWZlcmVuY2VzIGFyZSByZXNvbHZlZFxuXHRwcml2YXRlIGZpbGVHcmFwaEJpbmRpbmdzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHN0cmluZz4+KCk7XG5cdC8vIFRoZSBncmFwaCB0eXBlIHdob3NlIGNvbnN0cnVjdG9yIGlzIGN1cnJlbnRseSBiZWluZyBleHRyYWN0ZWQ7XG5cdC8vIGFuY2hvcnMgcmVsYXRpdmUtZmlyc3QgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb25cblx0cHJpdmF0ZSBjdXJyZW50R3JhcGhBbmNob3I6IFR5cGVOb2RlIHwgdW5kZWZpbmVkO1xuXHQvLyBkZWZpbmUoKS9sYXp5KCkgY2FsbHMgYWxyZWFkeSBleHRyYWN0ZWQgdGhpcyBwYXNzLiBUaGUgQ0xJIHJlLWFuYWx5emVzXG5cdC8vIGV2ZXJ5IGZpbGUgYWZ0ZXIgcmVzZXRVc2FnZXMoKTsgY2xlYXJpbmcgdGhlIHNldCBsZXRzIHRoZSBzZWNvbmQgcGFzc1xuXHQvLyByZS1leHRyYWN0IGV2ZXJ5IGNvbnN0cnVjdG9yIGFnYWluc3QgdGhlIENPTVBMRVRFIGdyYXBoIOKAlCBwYXNzIDEgc2Vlc1xuXHQvLyBmb3J3YXJkIHJlZmVyZW5jZXMgYXMgYG5vbmVgIChzb2Z0IHVua25vd24pIGJlY2F1c2UgbGF0ZXIgZmlsZXMgaGF2ZVxuXHQvLyBub3QgYmVlbiB2aXNpdGVkIHlldCwgc28gb25seSBwYXNzLTIgcmVzb2x1dGlvbiBpcyBhdXRob3JpdGF0aXZlIGZvclxuXHQvLyB0aGUgaGFyZC1mYWlsIGlkZW50aXR5IGxhdy4gVGhlIHN0YW1wIGxpdmVzIGhlcmUgcmF0aGVyIHRoYW4gb24gdGhlXG5cdC8vIEFTVCBub2RlIHNvIGl0IGNhbiBhY3R1YWxseSBiZSBjbGVhcmVkLiAoQ2hhaW5lZCBjYWxscyB2aXNpdCB0aGUgc2FtZVxuXHQvLyBub2RlIHR3aWNlIHdpdGhpbiBvbmUgcGFzczsgdGhlIGluLXBhc3MgZGVkdXAgYmVsb3cgc3RheXMuKVxuXHRwcml2YXRlIHByb2Nlc3NlZENhbGxzID0gbmV3IFNldDx0cy5DYWxsRXhwcmVzc2lvbj4oKTtcblxuXHRjb25zdHJ1Y3RvciAocHJvZ3JhbT86IHRzLlByb2dyYW0sIHBsdWdpbnM6IFRhY3RpY2FQbHVnaW5bXSA9IFtdKSB7XG5cdFx0Ly8gQ29tcGlsZXIgb3B0aW9ucyBkcml2ZSB0cy5yZXNvbHZlTW9kdWxlTmFtZSBmb3IgaW1wb3J0LWF3YXJlXG5cdFx0Ly8gcmVmZXJlbmNlZC10eXBlIHJlc29sdXRpb24gKHRzY29uZmlnIGBwYXRoc2AsIGV4dGVuc2lvbmxlc3Ncblx0XHQvLyBpbXBvcnRzKTsgdGhlIHR5cGUgY2hlY2tlciBpdHNlbGYgc3RheXMgdW51c2VkLlxuXHRcdHRoaXMucmVmZXJlbmNlZFR5cGVDb21waWxlck9wdGlvbnMgPSBwcm9ncmFtPy5nZXRDb21waWxlck9wdGlvbnMoKSA/PyB7fTtcblx0XHR0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkgPSBtZXJnZVRhY3RpY2FQbHVnaW5zKHBsdWdpbnMpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc2V0IHVzYWdlLXJlbGF0ZWQgc3RhdGUgZm9yIGEgZnJlc2ggcGFzcy5cblx0ICogQ2FsbCBiZWZvcmUgdGhlIHVzYWdlLWNvbGxlY3Rpb24gcGFzcyB0byBhdm9pZCBkdXBsaWNhdGVzIGZyb20gZGVmaW5pdGlvbiBwYXNzLlxuXHQgKi9cblx0cmVzZXRVc2FnZXMgKCk6IHZvaWQge1xuXHRcdHRoaXMudXNhZ2VzLmNsZWFyKCk7XG5cdFx0dGhpcy5lZHNVc2FnZXMuY2xlYXIoKTtcblx0XHR0aGlzLmZsb3dVc2FnZXMuY2xlYXIoKTtcblx0XHR0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmNsZWFyKCk7XG5cdFx0Ly8gRURTIGVudHJ5IHJlZmVyZW5jZXMgZ28gc3RhbGUgd2l0aCBlZHNVc2FnZXM7IHZpYSBsaW5rcyBhcmVcblx0XHQvLyByZS1kZXJpdmVkIG9uIHRoZSBuZXh0IHBhc3Ncblx0XHR0aGlzLndyYXBFbnRyeUJ5Tm9kZS5jbGVhcigpO1xuXHRcdHRoaXMubmVzdGVkV3JhcFZpYS5jbGVhcigpO1xuXHRcdC8vIE5vdGU6IG1vZHVsZU9iamVjdFZhcmlhYmxlcyBhbmQgY29sbGVjdGlvblZhcmlhYmxlcyBpbnRlbnRpb25hbGx5IHBlcnNpc3Rcblx0XHQvLyBhY3Jvc3MgZGVmaW5pdGlvbiBhbmQgdXNhZ2UgcGFzc2VzLlxuXHRcdC8vIFJlLWV4dHJhY3Rpb24gaW4gdGhlIHVzYWdlcyBwYXNzIGlzIHdoYXQgbWFrZXMgZ3JhcGggcmVmZXJlbmNlXG5cdFx0Ly8gcmVzb2x1dGlvbiBhdXRob3JpdGF0aXZlOiBwYXNzIDEgcmVzb2x2ZXMgYWdhaW5zdCBhbiBpbmNvbXBsZXRlXG5cdFx0Ly8gZ3JhcGggKGZvcndhcmQgcmVmZXJlbmNlcyByZWFkIGFzIGBub25lYCksIHBhc3MgMiBhZ2FpbnN0IGFsbCBvZiBpdC5cblx0XHR0aGlzLnByb2Nlc3NlZENhbGxzLmNsZWFyKCk7XG5cdFx0Ly8gbG9va3VwKCktcGF0aCB2YWxpZGF0aW9uIHJ1bnMgYWdhaW5zdCB0aGUgcmVjb3JkZWQgc2l0ZXM7IGEgZnJlc2hcblx0XHQvLyBwYXNzIG11c3QgcmUtcmVjb3JkIGFuZCByZS12YWxpZGF0ZSAocGFzcy0xIHJlc3VsdHMgd291bGQgYmVcblx0XHQvLyBwcmVtYXR1cmUg4oCUIHRoZSBncmFwaCBpcyBzdGlsbCBpbmNvbXBsZXRlKVxuXHRcdHRoaXMubG9va3VwUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHRcdHRoaXMubG9va3VwUmVmZXJlbmNlcyA9IFtdO1xuXHRcdHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHRcdHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlcyA9IFtdO1xuXHR9XG5cblx0LyoqXG5cdCAqIEFuYWx5emUgYSBzb3VyY2UgZmlsZSBmb3IgTW5lbW9uaWNhIHR5cGUgZGVmaW5pdGlvbnNcblx0ICovXG5cdGFuYWx5emVGaWxlIChzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogQW5hbHl6ZVJlc3VsdCB7XG5cdFx0dGhpcy5lcnJvcnMgPSBbXTtcblx0XHQvLyBSZWZlcmVuY2VkLXR5cGUgbmFtZXMgaW4gdGhpcyBmaWxlIHJlc29sdmUgYWdhaW5zdCBpdHMgb3duIGltcG9ydHNcblx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSBub2RlUGF0aC5yZXNvbHZlKHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXHRcdC8vIEVuc3VyZSBwYXJlbnQgbm9kZXMgYXJlIHNldCBmb3IgQVNUIHRyYXZlcnNhbFxuXHRcdHRoaXMuc2V0UGFyZW50Tm9kZXNJblNvdXJjZUZpbGUoc291cmNlRmlsZSk7XG5cdFx0dGhpcy52aXNpdE5vZGUoc291cmNlRmlsZSwgc291cmNlRmlsZSk7XG5cblx0XHRyZXR1cm4ge1xuXHRcdFx0dHlwZXMgIDogdGhpcy5ncmFwaC5nZXRBbGxUeXBlcygpLFxuXHRcdFx0ZXJyb3JzIDogdGhpcy5lcnJvcnMsXG5cdFx0fTtcblx0fVxuXG5cdC8qKlxuXHQgKiBBbmFseXplIHNvdXJjZSBjb2RlIHN0cmluZ1xuXHQgKi9cblx0YW5hbHl6ZVNvdXJjZSAoc291cmNlQ29kZTogc3RyaW5nLCBmaWxlTmFtZSA9ICd0ZW1wLnRzJyk6IEFuYWx5emVSZXN1bHQge1xuXHRcdGNvbnN0IHNvdXJjZUZpbGUgPSB0cy5jcmVhdGVTb3VyY2VGaWxlKFxuXHRcdFx0ZmlsZU5hbWUsXG5cdFx0XHRzb3VyY2VDb2RlLFxuXHRcdFx0dHMuU2NyaXB0VGFyZ2V0LkxhdGVzdCxcblx0XHRcdHRydWVcblx0XHQpO1xuXHRcdHJldHVybiB0aGlzLmFuYWx5emVGaWxlKHNvdXJjZUZpbGUpO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCB0aGUgdHlwZSBncmFwaFxuXHQgKi9cblx0Z2V0R3JhcGggKCk6IFR5cGVHcmFwaEltcGwge1xuXHRcdHJldHVybiB0aGlzLmdyYXBoO1xuXHR9XG5cblx0Z2V0QnVpbGRlclZhbHVlcyAoKTogQnVpbGRlclZhbHVlW10ge1xuXHRcdGNvbnN0IHJlc3VsdDogQnVpbGRlclZhbHVlW10gPSBbXTtcblx0XHRjb25zdCBzZWVuID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0Zm9yIChjb25zdCBjYW5kaWRhdGUgb2YgdGhpcy5idWlsZGVyQ2FuZGlkYXRlcykge1xuXHRcdFx0aWYgKGNhbmRpZGF0ZS5leGNsdWRlZCkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3QgZXhwb3J0ZWQgb2YgY2FuZGlkYXRlLmV4cG9ydHMpIHtcblx0XHRcdFx0Y29uc3Qga2V5ID0gYCR7Y2FuZGlkYXRlLmtpbmR9fCR7ZXhwb3J0ZWQuc291cmNlRmlsZX18JHtleHBvcnRlZC5uYW1lfXwke2NhbmRpZGF0ZS5mdWxsUGF0aH1gO1xuXHRcdFx0XHRpZiAoc2Vlbi5oYXMoa2V5KSkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHNlZW4uYWRkKGtleSk7XG5cdFx0XHRcdHJlc3VsdC5wdXNoKHtcblx0XHRcdFx0XHRuYW1lICAgICAgICAgIDogZXhwb3J0ZWQubmFtZSxcblx0XHRcdFx0XHRzb3VyY2VGaWxlICAgIDogZXhwb3J0ZWQuc291cmNlRmlsZSxcblx0XHRcdFx0XHRraW5kICAgICAgICAgIDogY2FuZGlkYXRlLmtpbmQsXG5cdFx0XHRcdFx0ZnVsbFBhdGggICAgICA6IGNhbmRpZGF0ZS5mdWxsUGF0aCxcblx0XHRcdFx0XHRkZWZhdWx0SW1wb3J0IDogZXhwb3J0ZWQuZGVmYXVsdEltcG9ydFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGRlZmluaXRpb25zXG5cdCAqL1xuXHRnZXREZWZpbml0aW9ucyAoKTogTWFwPHN0cmluZywgRGVmaW5pdGlvbkluZm8+IHtcblx0XHRyZXR1cm4gdGhpcy5kZWZpbml0aW9ucztcblx0fVxuXG5cdC8qKlxuXHQgKiBUaGUgY29sbGVjdGlvbnMuanNvbiBtYW5pZmVzdDogb25lIGVudHJ5IHBlciBtaW50ZWQgY29sbGVjdGlvbiwgaW5cblx0ICogbWludGluZyBvcmRlciwgcHJlY2VkZWQgYnkgdGhlIGRlZmF1bHQtY29sbGVjdGlvbiBlbnRyeSB3aGVuZXZlclxuXHQgKiBkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMgZXhpc3QuIFRoZSBkZWZhdWx0IGVudHJ5IGhhcyBubyBpZC9sb2NhdGlvblxuXHQgKiAodGhlcmUgaXMgbm8gY2FsbCBzaXRlIOKAlCB1bnByZWZpeGVkIGZ1bGxQYXRocyBhcmUgaXRzIGlkZW50aXR5KS5cblx0ICogRm9ybWF0IDEuMjogdGhlIHJlZ2lzdHJ5IGludGVyZmFjZSBpcyBOT1QgZW1pdHRlZCAoaXQgaXMgYVxuXHQgKiBUeXBlU2NyaXB0LW9ubHkgY29uY2VybiDigJQgdGhlIGluLW1lbW9yeSByZWdpc3RyeUludGVyZmFjZU5hbWUgdGhhdFxuXHQgKiB0eXBlcy50cy9yZWdpc3RyeS50cyBhcmUgZ2VuZXJhdGVkIGZyb20gc3RheXMgb24gdGhlIFR5cGVOb2RlKS5cblx0ICovXG5cdGdldENvbGxlY3Rpb25zTWFuaWZlc3QgKCk6IENvbGxlY3Rpb25NYW5pZmVzdEVudHJ5W10ge1xuXHRcdGNvbnN0IGVudHJpZXM6IENvbGxlY3Rpb25NYW5pZmVzdEVudHJ5W10gPSBbXTtcblx0XHRjb25zdCBoYXNEZWZhdWx0VHlwZXMgPSB0aGlzLmdyYXBoLmdldEFsbFR5cGVzKCkuc29tZSh0ID0+IHQuY29sbGVjdGlvbklkID09PSB1bmRlZmluZWQpO1xuXHRcdGlmIChoYXNEZWZhdWx0VHlwZXMpIHtcblx0XHRcdGVudHJpZXMucHVzaCh7XG5cdFx0XHRcdGlkICAgICAgIDogbnVsbCxcblx0XHRcdFx0bmFtZSAgICAgOiAnZGVmYXVsdFR5cGVzJyxcblx0XHRcdFx0bG9jYXRpb24gOiBudWxsLFxuXHRcdFx0XHRsYW5ndWFnZSA6ICd0eXBlc2NyaXB0J1xuXHRcdFx0fSk7XG5cdFx0fVxuXHRcdGZvciAoY29uc3QgWyBpZCwgaW5mbyBdIG9mIHRoaXMuY29sbGVjdGlvbkluZm8pIHtcblx0XHRcdGNvbnN0IGVudHJ5OiBDb2xsZWN0aW9uTWFuaWZlc3RFbnRyeSA9IHtcblx0XHRcdFx0aWQsXG5cdFx0XHRcdG5hbWUgICAgIDogaW5mby52YXJpYWJsZU5hbWUsXG5cdFx0XHRcdGxvY2F0aW9uIDogYCR7aW5mby5zb3VyY2VGaWxlfToke2luZm8ubGluZX06JHtpbmZvLmNvbHVtbn1gLFxuXHRcdFx0XHRsYW5ndWFnZSA6ICd0eXBlc2NyaXB0J1xuXHRcdFx0fTtcblx0XHRcdGVudHJpZXMucHVzaChlbnRyeSk7XG5cdFx0fVxuXHRcdHJldHVybiBlbnRyaWVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBjb2xsZWN0ZWQgdXNhZ2VzXG5cdCAqL1xuXHRnZXRVc2FnZXMgKCk6IE1hcDxzdHJpbmcsIFVzYWdlSW5mb1tdPiB7XG5cdFx0cmV0dXJuIHRoaXMudXNhZ2VzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBjb2xsZWN0ZWQgRURTIHVzYWdlc1xuXHQgKi9cblx0Z2V0RURTVXNhZ2VzICgpOiBNYXA8c3RyaW5nLCBFRFNJbmZvW10+IHtcblx0XHRyZXR1cm4gdGhpcy5lZHNVc2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBmbG93IHVzYWdlc1xuXHQgKi9cblx0Z2V0Rmxvd1VzYWdlcyAoKTogTWFwPHN0cmluZywgRmxvd0luZm9bXT4ge1xuXHRcdHJldHVybiB0aGlzLmZsb3dVc2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBpbnN0cnVtZW50YXRpb24gcG9pbnRzLlxuXHQgKiBSZWdpc3RyYXRpb24gc2l0ZXMgcmVmZXJlbmNpbmcgYSBjbGFzcyBkZWNsYXJlZCBpbiB0aGUgc2FtZSBwcm9qZWN0XG5cdCAqIHJlc29sdmUgdG8gdGhlIGNsYXNzIGRlY2xhcmF0aW9uJ3MgbG9jYXRpb24vY29kZTsgZXh0ZXJuYWwgY2xhc3Nlc1xuXHQgKiAoZS5nLiwgYSBmcmFtZXdvcmstYnVpbHRpbiBpbXBsZW1lbnRhdGlvbiBmcm9tIG5vZGVfbW9kdWxlcykga2VlcFxuXHQgKiB0aGUgcmVnaXN0cmF0aW9uIHNpdGUuXG5cdCAqIERlZHVwZWQgYnkga2luZCtjbGFzc05hbWUrbG9jYXRpb24rc2NvcGUgd2l0aCB0YXJnZXRzIG1lcmdlZCDigJQgYVxuXHQgKiBjbGFzcyBkZXRlY3RlZCBieSBoZXJpdGFnZSBBTkQgYnkgYSBkZWNvcmF0b3Igc2l0ZSB5aWVsZHMgc2VwYXJhdGVcblx0ICogZW50cmllcyB3aXRoIGRpc3RpbmN0IHNjb3BlcyAoc2VlIEluc3RydW1lbnRhdGlvblBvaW50IGluIHR5cGVzLnRzKS5cblx0ICovXG5cdGdldEluc3RydW1lbnRhdGlvblBvaW50cyAoKTogSW5zdHJ1bWVudGF0aW9uUG9pbnRbXSB7XG5cdFx0Y29uc3QgcG9pbnRzID0gbmV3IE1hcDxzdHJpbmcsIEluc3RydW1lbnRhdGlvblBvaW50PigpO1xuXG5cdFx0Y29uc3QgYWRkUG9pbnQgPSAocG9pbnQ6IEluc3RydW1lbnRhdGlvblBvaW50KTogdm9pZCA9PiB7XG5cdFx0XHRjb25zdCBrZXkgPSBgJHtwb2ludC5raW5kfXwke3BvaW50LmNsYXNzTmFtZX18JHtwb2ludC5sb2NhdGlvbn18JHtwb2ludC5zY29wZX1gO1xuXHRcdFx0Y29uc3QgZXhpc3RpbmcgPSBwb2ludHMuZ2V0KGtleSk7XG5cdFx0XHRpZiAoZXhpc3RpbmcpIHtcblx0XHRcdFx0Y29uc3QgbWVyZ2VkID0gbmV3IFNldChbIC4uLmV4aXN0aW5nLnRhcmdldHMsIC4uLnBvaW50LnRhcmdldHMgXSk7XG5cdFx0XHRcdGV4aXN0aW5nLnRhcmdldHMgPSBBcnJheS5mcm9tKG1lcmdlZCk7XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdHBvaW50cy5zZXQoa2V5LCBwb2ludCk7XG5cdFx0fTtcblxuXHRcdGZvciAoY29uc3Qgc2l0ZSBvZiB0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzKSB7XG5cdFx0XHRjb25zdCBkZWNsID0gdGhpcy5pbnN0cnVtZW50YXRpb25DbGFzc0RlY2xzLmdldChzaXRlLmNsYXNzTmFtZSk7XG5cdFx0XHRjb25zdCBwb2ludDogSW5zdHJ1bWVudGF0aW9uUG9pbnQgPSB7XG5cdFx0XHRcdGtpbmQgICAgICA6IHNpdGUua2luZCxcblx0XHRcdFx0Y2xhc3NOYW1lIDogc2l0ZS5jbGFzc05hbWUsXG5cdFx0XHRcdGxvY2F0aW9uICA6IGRlY2wgPyBkZWNsLmxvY2F0aW9uIDogc2l0ZS5sb2NhdGlvbixcblx0XHRcdFx0Y29kZSAgICAgIDogZGVjbCA/IGRlY2wuY29kZSA6IHNpdGUuY29kZSxcblx0XHRcdFx0c2NvcGUgICAgIDogc2l0ZS5zY29wZSxcblx0XHRcdFx0dGFyZ2V0cyAgIDogc2l0ZS50YXJnZXRzLFxuXHRcdFx0fTtcblx0XHRcdGFkZFBvaW50KHBvaW50KTtcblx0XHR9XG5cblx0XHQvLyBIZXJpdGFnZS1kZWNsYXJlZCBjbGFzc2VzIGFsd2F5cyBlbWl0IGEgZGVjbGFyYXRpb24gcG9pbnQgd2l0aFxuXHRcdC8vIHNjb3BlICdtb2R1bGUnIChhdHRhY2htZW50IHN0YXRpY2FsbHkgdW5rbm93bik7IHJlZ2lzdHJhdGlvblxuXHRcdC8vIHNpdGVzIGFib3ZlIGNhcnJ5IHRoZSBuYXJyb3dlciBzY29wZXMgYXMgc2VwYXJhdGUgZW50cmllc1xuXHRcdGZvciAoY29uc3QgWyBjbGFzc05hbWUsIGRlY2wgXSBvZiB0aGlzLmluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMpIHtcblx0XHRcdGlmICghZGVjbC5raW5kKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgcG9pbnQ6IEluc3RydW1lbnRhdGlvblBvaW50ID0ge1xuXHRcdFx0XHRraW5kICAgICAgOiBkZWNsLmtpbmQsXG5cdFx0XHRcdGNsYXNzTmFtZSA6IGNsYXNzTmFtZSxcblx0XHRcdFx0bG9jYXRpb24gIDogZGVjbC5sb2NhdGlvbixcblx0XHRcdFx0Y29kZSAgICAgIDogZGVjbC5jb2RlLFxuXHRcdFx0XHRzY29wZSAgICAgOiAnbW9kdWxlJyxcblx0XHRcdFx0dGFyZ2V0cyAgIDogW10sXG5cdFx0XHR9O1xuXHRcdFx0YWRkUG9pbnQocG9pbnQpO1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlc3VsdCA9IEFycmF5LmZyb20ocG9pbnRzLnZhbHVlcygpKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhIHRvcG9sb2dpY2EgdHlwZSB0byB0aGUgYW5hbHl6ZXIgZm9yIHVzYWdlIHRyYWNraW5nLlxuXHQgKiBUaGlzIGFsbG93cyB0aGUgYW5hbHl6ZXIgdG8gcmVjb2duaXplIHRvcG9sb2dpY2EgdHlwZXMgd2hlbiBjb2xsZWN0aW5nIHVzYWdlcy5cblx0ICovXG5cdGFkZFRvcG9sb2dpY2FUeXBlIChmdWxsUGF0aDogc3RyaW5nLCBub2RlOiBpbXBvcnQoJy4vdHlwZXMnKS5UeXBlTm9kZSk6IHZvaWQge1xuXHRcdC8vIFNraXAgaWYgYWxyZWFkeSBleGlzdHNcblx0XHRpZiAodGhpcy5ncmFwaC5hbGxUeXBlcy5oYXMoZnVsbFBhdGgpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoIHNvIGl0IGNhbiBiZSBmb3VuZCBkdXJpbmcgdXNhZ2UgY29sbGVjdGlvblxuXHRcdGlmIChub2RlLnBhcmVudCkge1xuXHRcdFx0Ly8gQWRkIGFzIGNoaWxkIG9mIHBhcmVudFxuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChub2RlLnBhcmVudCwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdC8vIEFkZCBhcyByb290XG5cdFx0XHR0aGlzLmdyYXBoLmFkZFJvb3Qobm9kZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQWxzbyBhZGQgdG8gZGVmaW5pdGlvbnMgc28gaXQncyByZWNvZ25pemVkIGFzIGEga25vd24gdHlwZVxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiBub2RlLm5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke25vZGUuc291cmNlRmlsZX06JHtub2RlLmxpbmV9OiR7bm9kZS5jb2x1bW59YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlZmluZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IG5vZGUucGFyZW50ID8gbm9kZS5wYXJlbnQuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBmYWxzZVxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQoZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFNldCBwYXJlbnQgbm9kZXMgaW4gYSBzb3VyY2UgZmlsZSB0byBlbmFibGUgQVNUIHRyYXZlcnNhbCB1cFxuXHQgKi9cblx0cHJpdmF0ZSBzZXRQYXJlbnROb2Rlc0luU291cmNlRmlsZSAoc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHNldFBhcmVudCA9IChub2RlOiB0cy5Ob2RlLCBwYXJlbnQ/OiB0cy5Ob2RlKSA9PiB7XG5cdFx0XHQvLyBUeXBlU2NyaXB0IGRvZXNuJ3QgZXhwb3NlIHBhcmVudCBhcyB3cml0YWJsZSwgYnV0IHdlIG5lZWQgaXRcblx0XHRcdC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBAdHlwZXNjcmlwdC1lc2xpbnQvbm8tZXhwbGljaXQtYW55XG5cdFx0XHQobm9kZSBhcyBhbnkpLnBhcmVudCA9IHBhcmVudDtcblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCBjaGlsZCA9PiBzZXRQYXJlbnQoY2hpbGQsIG5vZGUpKTtcblx0XHR9O1xuXHRcdHNldFBhcmVudChzb3VyY2VGaWxlKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBWaXNpdCBhIG5vZGUgaW4gdGhlIEFTVFxuXHQgKi9cblx0cHJpdmF0ZSB2aXNpdE5vZGUgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsIGN1cnJlbnRDbGFzcz86IHRzLkNsYXNzRGVjbGFyYXRpb24pOiB2b2lkIHtcblx0XHQvLyBUcmFjayBtbmVtb25pY2EgbW9kdWxlLW9iamVjdCBhbGlhc2VzIGFuZCBjdXN0b20gY29sbGVjdGlvbiB2YXJpYWJsZXNcblx0XHQvLyBiZWZvcmUgcHJvY2Vzc2luZyBkZWZpbmUoKS9sb29rdXAoKSBjYWxscyBzbyBzb3VyY2UgcmVzb2x1dGlvbiB3b3Jrcy5cblx0XHR0aGlzLnRyYWNrSW1wb3J0cyhub2RlKTtcblx0XHR0aGlzLnRyYWNrTW9kdWxlT2JqZWN0QWxpYXNlcyhub2RlKTtcblx0XHR0aGlzLnRyYWNrQ29sbGVjdGlvbkFsaWFzZXMobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0dGhpcy50cmFja0J1aWxkZXJFeHBvcnRBc3NpZ25tZW50KG5vZGUpO1xuXHRcdHRoaXMudHJhY2tDb25zdHJ1Y3RvckJpbmRpbmcobm9kZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgZGVmaW5lKCkgY2FsbHNcblx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0RlZmluZUNhbGwobm9kZSBhcyB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIGxhenkoKSBjYWxsc1xuXHRcdGlmICh0aGlzLmlzTGF6eUNhbGwobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0xhenlDYWxsKG5vZGUgYXMgdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGUpO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHRcdGlmICh0aGlzLmlzRGVjb3JhdGVEZWNvcmF0b3Iobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0RlY29yYXRlRGVjb3JhdG9yKG5vZGUgYXMgdHMuRGVjb3JhdG9yLCBzb3VyY2VGaWxlLCBjdXJyZW50Q2xhc3MpO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciB0eXBlIHVzYWdlcyAobmV3IFR5cGUoKSwgdHlwZSBhbm5vdGF0aW9ucywgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RVc2FnZShub2RlLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIENoZWNrIGZvciBFRFMgcGF0dGVybnMgKHdyYXAsIGN1cnJlbnQsIGdldEZsb3csIGV0Yy4pXG5cdFx0dGhpcy5jb2xsZWN0RURTKG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIG5hdGl2ZSBmbG93IHBhdHRlcm5zIChwcm9wZXJ0eSBhY2Nlc3MsIG1ldGhvZCBjYWxscywgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RGbG93KG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIGZyYW1ld29yayBpbnN0cnVtZW50YXRpb24gcG9pbnRzICh2b2NhYnVsYXJ5IHN1cHBsaWVkXG5cdFx0Ly8gYnkgcGx1Z2luczsgc3ludGFjdGljIG9ubHkg4oCUIG5vIHR5cGUgY2hlY2tlcilcblx0XHR0aGlzLmNvbGxlY3RJbnN0cnVtZW50YXRpb24obm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDb2xsZWN0IHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbnMgKGFsaWFzZXMsIGNsYXNzZXMsIGludGVyZmFjZXMpXG5cdFx0Ly8gcGVyIGZpbGUsIGFuZCB0aGUgZmlsZSdzIGltcG9ydCB3aXJpbmcsIGZvciBpbXBvcnQtYXdhcmUgcmVzb2x1dGlvblxuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKG5vZGUpO1xuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZUltcG9ydChub2RlKTtcblx0XHR0aGlzLnRyYWNrUmVmZXJlbmNlZFR5cGVSZUV4cG9ydChub2RlKTtcblx0XHR0aGlzLnRyYWNrUmVmZXJlbmNlZFR5cGVDb25zdEFycmF5KG5vZGUpO1xuXG5cdFx0Ly8gVHJhY2sgc2FtZS1maWxlIGZ1bmN0aW9uIGJpbmRpbmdzIHNvIEVEUyBjYW4gcmVzb2x2ZSB3cmFwKGZuKVxuXHRcdC8vIGFyZ3VtZW50cyB3aXRob3V0IHRoZSB0eXBlIGNoZWNrZXIgKGJlc3QgZWZmb3J0LCBsYXN0IHdpbnMpXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9IyR7bm9kZS5uYW1lLnRleHR9YDtcblx0XHRcdHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5zZXQoa2V5LCBub2RlKTtcblx0XHR9XG5cdFx0aWYgKFxuXHRcdFx0dHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSAmJlxuXHRcdFx0bm9kZS5pbml0aWFsaXplciAmJlxuXHRcdFx0KHRzLmlzQXJyb3dGdW5jdGlvbihub2RlLmluaXRpYWxpemVyKSB8fCB0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihub2RlLmluaXRpYWxpemVyKSlcblx0XHQpIHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9IyR7bm9kZS5uYW1lLnRleHR9YDtcblx0XHRcdHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5zZXQoa2V5LCBub2RlLmluaXRpYWxpemVyKTtcblx0XHR9XG5cblx0XHQvLyBUcmFjayBjbGFzcyBkZWNsYXJhdGlvbnMgZm9yIGRlY29yYXRvciBwYXJlbnQgbG9va3VwXG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0Ly8gVmlzaXQgY2hpbGRyZW4gd2l0aCB0aGlzIGNsYXNzIGFzIHRoZSBjdXJyZW50IGNvbnRleHRcblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCBjaGlsZCA9PiB0aGlzLnZpc2l0Tm9kZShjaGlsZCwgc291cmNlRmlsZSwgbm9kZSkpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHQvLyBSZWN1cnNpdmVseSB2aXNpdCBjaGlsZHJlblxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHRoaXMudmlzaXROb2RlKGNoaWxkLCBzb3VyY2VGaWxlLCBjdXJyZW50Q2xhc3MpKTtcblx0XHR9XG5cdH1cblxuXHRwcml2YXRlIHRyYWNrQ29uc3RydWN0b3JCaW5kaW5nIChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0bGV0IG5hbWU6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRsZXQgaGFuZGxlcjogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkO1xuXHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkgJiYgbm9kZS5pbml0aWFsaXplcikge1xuXHRcdFx0bmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0aGFuZGxlciA9IG5vZGUuaW5pdGlhbGl6ZXI7XG5cdFx0fSBlbHNlIGlmICgodHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKG5vZGUpIHx8IHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSkgJiYgbm9kZS5uYW1lKSB7XG5cdFx0XHRuYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0XHRoYW5kbGVyID0gbm9kZTtcblx0XHR9XG5cdFx0aWYgKCFuYW1lIHx8ICFoYW5kbGVyKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGZpbGVQYXRoID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGxldCBiaW5kaW5ncyA9IHRoaXMuY29uc3RydWN0b3JCaW5kaW5ncy5nZXQoZmlsZVBhdGgpO1xuXHRcdGlmICghYmluZGluZ3MpIHtcblx0XHRcdGJpbmRpbmdzID0gbmV3IE1hcDxzdHJpbmcsIENvbnN0cnVjdG9ySGFuZGxlcj4oKTtcblx0XHRcdHRoaXMuY29uc3RydWN0b3JCaW5kaW5ncy5zZXQoZmlsZVBhdGgsIGJpbmRpbmdzKTtcblx0XHR9XG5cdFx0YmluZGluZ3Muc2V0KG5hbWUsIGhhbmRsZXIpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFRyYWNrIGltcG9ydHMgZnJvbSAnbW5lbW9uaWNhJyBzbyBhbGlhc2VzIG9mIHRoZSBtb2R1bGUgb2JqZWN0IGFuZFxuXHQgKiBjcmVhdGVUeXBlc0NvbGxlY3Rpb24gYXJlIHJlY29nbml6ZWQgd2l0aG91dCByZWx5aW5nIG9uIHRoZSB0eXBlIGNoZWNrZXIuXG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrSW1wb3J0cyAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNJbXBvcnREZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgbW9kdWxlU3BlY2lmaWVyIH0gPSBub2RlO1xuXHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwobW9kdWxlU3BlY2lmaWVyKSAmJiBtb2R1bGVTcGVjaWZpZXIudGV4dC5pbmNsdWRlcygnLnRhY3RpY2EnKSkge1xuXHRcdFx0bGV0IGltcG9ydHMgPSB0aGlzLmdlbmVyYXRlZFR5cGVJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0aWYgKCFpbXBvcnRzKSB7XG5cdFx0XHRcdGltcG9ydHMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHRcdFx0dGhpcy5nZW5lcmF0ZWRUeXBlSW1wb3J0cy5zZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlLCBpbXBvcnRzKTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGdlbmVyYXRlZENsYXVzZSA9IG5vZGUuaW1wb3J0Q2xhdXNlO1xuXHRcdFx0aWYgKGdlbmVyYXRlZENsYXVzZT8ubmFtZSkge1xuXHRcdFx0XHRpbXBvcnRzLmFkZChnZW5lcmF0ZWRDbGF1c2UubmFtZS50ZXh0KTtcblx0XHRcdH1cblx0XHRcdGlmIChnZW5lcmF0ZWRDbGF1c2U/Lm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lZEltcG9ydHMoZ2VuZXJhdGVkQ2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBnZW5lcmF0ZWRDbGF1c2UubmFtZWRCaW5kaW5ncy5lbGVtZW50cykge1xuXHRcdFx0XHRcdGltcG9ydHMuYWRkKGVsZW1lbnQubmFtZS50ZXh0KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKGdlbmVyYXRlZENsYXVzZT8ubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVzcGFjZUltcG9ydChnZW5lcmF0ZWRDbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdFx0aW1wb3J0cy5hZGQoZ2VuZXJhdGVkQ2xhdXNlLm5hbWVkQmluZGluZ3MubmFtZS50ZXh0KTtcblx0XHRcdH1cblx0XHR9XG5cdFx0aWYgKCF0cy5pc1N0cmluZ0xpdGVyYWwobW9kdWxlU3BlY2lmaWVyKSB8fCBtb2R1bGVTcGVjaWZpZXIudGV4dCAhPT0gJ21uZW1vbmljYScpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCBjbGF1c2UgPSBub2RlLmltcG9ydENsYXVzZTtcblx0XHRpZiAoIWNsYXVzZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGltcG9ydCB7IG1uZW1vbmljYSwgY3JlYXRlVHlwZXNDb2xsZWN0aW9uIH0gZnJvbSAnbW5lbW9uaWNhJ1xuXHRcdGlmIChjbGF1c2UubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVkSW1wb3J0cyhjbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBjbGF1c2UubmFtZWRCaW5kaW5ncy5lbGVtZW50cykge1xuXHRcdFx0XHRjb25zdCBsb2NhbE5hbWUgPSBlbGVtZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgaW1wb3J0ZWROYW1lID0gZWxlbWVudC5wcm9wZXJ0eU5hbWVcblx0XHRcdFx0XHQ/IGVsZW1lbnQucHJvcGVydHlOYW1lLnRleHRcblx0XHRcdFx0XHQ6IGxvY2FsTmFtZTtcblx0XHRcdFx0aWYgKGltcG9ydGVkTmFtZSA9PT0gJ21uZW1vbmljYScpIHtcblx0XHRcdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQobG9jYWxOYW1lKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoaW1wb3J0ZWROYW1lID09PSAnY3JlYXRlVHlwZXNDb2xsZWN0aW9uJykge1xuXHRcdFx0XHRcdHRoaXMuY3JlYXRlVHlwZXNDb2xsZWN0aW9uVmFyaWFibGVzLmFkZChsb2NhbE5hbWUpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGxldCBmaWxlSW1wb3J0cyA9IHRoaXMubW5lbW9uaWNhTmFtZWRJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHRpZiAoIWZpbGVJbXBvcnRzKSB7XG5cdFx0XHRcdFx0ZmlsZUltcG9ydHMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0XHRcdHRoaXMubW5lbW9uaWNhTmFtZWRJbXBvcnRzLnNldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUsIGZpbGVJbXBvcnRzKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRmaWxlSW1wb3J0cy5zZXQobG9jYWxOYW1lLCBpbXBvcnRlZE5hbWUpO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIGltcG9ydCAqIGFzIG1uZW1vbmljYSBmcm9tICdtbmVtb25pY2EnXG5cdFx0aWYgKGNsYXVzZS5uYW1lZEJpbmRpbmdzICYmIHRzLmlzTmFtZXNwYWNlSW1wb3J0KGNsYXVzZS5uYW1lZEJpbmRpbmdzKSkge1xuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuYWRkKGNsYXVzZS5uYW1lZEJpbmRpbmdzLm5hbWUudGV4dCk7XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0IG1uZW1vbmljYSBmcm9tICdtbmVtb25pY2EnIChkZWZhdWx0IGltcG9ydCkg4oCUIHRyZWF0IGFzIG1vZHVsZSBvYmplY3QgdG9vXG5cdFx0aWYgKGNsYXVzZS5uYW1lKSB7XG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQoY2xhdXNlLm5hbWUudGV4dCk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhIG5hbWVkIHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbiAodHlwZSBhbGlhcywgY2xhc3MsIG9yXG5cdCAqIGludGVyZmFjZSkgZm9yIHRoZSBmaWxlIGN1cnJlbnRseSBiZWluZyB2aXNpdGVkLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHQvLyBOYW1lc3BhY2VzIGFyZSB0aGUgbWlkZGxlIHNlZ21lbnRzIG9mIHF1YWxpZmllZCByZWZlcmVuY2VzXG5cdFx0Ly8gKG1vZGVscy5Jbm5lci5DcmF0ZSkg4oCUIHJlY29yZGVkIHNlcGFyYXRlbHkgZnJvbSB0aGUgcGxhaW4tbmFtZVxuXHRcdC8vIGRlY2xhcmF0aW9uIHRhYmxlIChzdHJpbmctbmFtZWQgYG1vZHVsZSAn4oCmJ2AgZGVjbGFyYXRpb25zIGFyZVxuXHRcdC8vIGFtYmllbnQgZXh0ZXJuYWxzIGFuZCBzdGF5IG91dClcblx0XHRpZiAodHMuaXNNb2R1bGVEZWNsYXJhdGlvbihub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSAmJlxuXHRcdFx0bm9kZS5ib2R5ICYmIHRzLmlzTW9kdWxlQmxvY2sobm9kZS5ib2R5KSkge1xuXHRcdFx0Y29uc3QgbmFtZXNwYWNlRmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0XHRsZXQgbmFtZXNwYWNlcyA9IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzLmdldChuYW1lc3BhY2VGaWxlUGF0aCk7XG5cdFx0XHRpZiAoIW5hbWVzcGFjZXMpIHtcblx0XHRcdFx0bmFtZXNwYWNlcyA9IG5ldyBNYXA8c3RyaW5nLCB0cy5Nb2R1bGVEZWNsYXJhdGlvbj4oKTtcblx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMuc2V0KG5hbWVzcGFjZUZpbGVQYXRoLCBuYW1lc3BhY2VzKTtcblx0XHRcdH1cblx0XHRcdG5hbWVzcGFjZXMuc2V0KG5vZGUubmFtZS50ZXh0LCBub2RlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRsZXQgbmFtZSA9ICcnO1xuXHRcdGxldCBraW5kOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uWydraW5kJ10gfCB1bmRlZmluZWQ7XG5cdFx0bGV0IGRlY2xOb2RlOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uWydub2RlJ10gfCB1bmRlZmluZWQ7XG5cblx0XHRpZiAodHMuaXNUeXBlQWxpYXNEZWNsYXJhdGlvbihub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSkge1xuXHRcdFx0bmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0a2luZCA9ICdhbGlhcyc7XG5cdFx0XHRkZWNsTm9kZSA9IG5vZGU7XG5cdFx0fSBlbHNlIGlmICh0cy5pc0NsYXNzRGVjbGFyYXRpb24obm9kZSkgJiYgbm9kZS5uYW1lKSB7XG5cdFx0XHRuYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0XHRraW5kID0gJ2NsYXNzJztcblx0XHRcdGRlY2xOb2RlID0gbm9kZTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzSW50ZXJmYWNlRGVjbGFyYXRpb24obm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdG5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRcdGtpbmQgPSAnaW50ZXJmYWNlJztcblx0XHRcdGRlY2xOb2RlID0gbm9kZTtcblx0XHR9XG5cblx0XHRpZiAoIWtpbmQgfHwgIWRlY2xOb2RlIHx8ICFuYW1lKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0bGV0IGRlY2xzID0gdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLmdldChmaWxlUGF0aCk7XG5cdFx0aWYgKCFkZWNscykge1xuXHRcdFx0ZGVjbHMgPSBuZXcgTWFwPHN0cmluZywgUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbj4oKTtcblx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscy5zZXQoZmlsZVBhdGgsIGRlY2xzKTtcblx0XHR9XG5cdFx0Y29uc3QgZW50cnk6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gPSB7IGtpbmQsIG5vZGUgOiBkZWNsTm9kZSwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0ZGVjbHMuc2V0KG5hbWUsIGVudHJ5KTtcblxuXHRcdC8vIGBleHBvcnQgZGVmYXVsdCBjbGFzcyBGb28ge31gIGlzIGFsc28gcmVhY2hhYmxlIHVuZGVyIHRoZSAnZGVmYXVsdCdcblx0XHQvLyBiaW5kaW5nIGZvciBkZWZhdWx0IGltcG9ydGVyc1xuXHRcdGlmIChraW5kID09PSAnY2xhc3MnKSB7XG5cdFx0XHRjb25zdCBjbGFzc05vZGUgPSBkZWNsTm9kZSBhcyB0cy5DbGFzc0RlY2xhcmF0aW9uO1xuXHRcdFx0Y29uc3QgaXNFeHBvcnRlZCA9IGNsYXNzTm9kZS5tb2RpZmllcnM/LnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRXhwb3J0S2V5d29yZCkgPz8gZmFsc2U7XG5cdFx0XHRjb25zdCBpc0RlZmF1bHQgPSBjbGFzc05vZGUubW9kaWZpZXJzPy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLkRlZmF1bHRLZXl3b3JkKSA/PyBmYWxzZTtcblx0XHRcdGlmIChpc0V4cG9ydGVkICYmIGlzRGVmYXVsdCkge1xuXHRcdFx0XHRkZWNscy5zZXQoJ2RlZmF1bHQnLCBlbnRyeSk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBjb25zdHMgaW5pdGlhbGl6ZWQgd2l0aCBhbiBhcnJheSBsaXRlcmFsIChvcHRpb25hbGx5IHdyYXBwZWQgaW5cblx0ICogYGFzIGNvbnN0YCAvIGBzYXRpc2ZpZXNgKSwgc28gYSBgdHlwZW9mIHN0YXR1c0xpc3RbbnVtYmVyXWAgZmllbGQgdHlwZVxuXHQgKiBleHBhbmRzIHRvIHRoZSBlbGVtZW50IGxpdGVyYWwgdW5pb24g4oCUIHRoZSBnZW5lcmF0ZWQgZmlsZSBjYXJyaWVzIG5vXG5cdCAqIGltcG9ydHMsIHNvIGVtaXR0aW5nIHRoZSBiYXJlIGB0eXBlb2Ygc3RhdHVzTGlzdGAgcXVlcnkgd291bGQgYmUgYW5cblx0ICogdW5yZXNvbHZhYmxlIG5hbWUgZG93bnN0cmVhbS4gRmlyc3QgYmluZGluZyB3aW5zOiBhIG5lc3RlZCBzaGFkb3dcblx0ICogbXVzdCBub3QgcmVwbGFjZSB0aGUgbW9kdWxlLWxldmVsIGNvbnN0IHRoZSB0eXBlb2YgcmVmZXJzIHRvLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlQ29uc3RBcnJheSAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpIHx8ICF0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSB8fCAhbm9kZS5pbml0aWFsaXplcikge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCB7IGluaXRpYWxpemVyOiByYXdJbml0aWFsaXplciB9ID0gbm9kZTtcblx0XHRsZXQgaW5pdGlhbGl6ZXI6IHRzLkV4cHJlc3Npb24gPSByYXdJbml0aWFsaXplcjtcblx0XHR3aGlsZSAoXG5cdFx0XHR0cy5pc0FzRXhwcmVzc2lvbihpbml0aWFsaXplcikgfHxcblx0XHRcdHRzLmlzU2F0aXNmaWVzRXhwcmVzc2lvbihpbml0aWFsaXplcikgfHxcblx0XHRcdC8vIHRoZSBhbmdsZS1icmFja2V0IGFzc2VydGlvbiBzcGVsbGluZyAoYDxjb25zdD5b4oCmXWApIGlzIHRoZVxuXHRcdFx0Ly8gc2FtZSBjb25zdC1hcnJheSBtYXJrZXIgYXMgdGhlIGBhcyBjb25zdGAgZm9ybSAoRjE3KVxuXHRcdFx0dHMuaXNUeXBlQXNzZXJ0aW9uRXhwcmVzc2lvbihpbml0aWFsaXplcilcblx0XHQpIHtcblx0XHRcdGluaXRpYWxpemVyID0gaW5pdGlhbGl6ZXIuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0aWYgKCF0cy5pc0FycmF5TGl0ZXJhbEV4cHJlc3Npb24oaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGZpbGVQYXRoID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGxldCBjb25zdHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuZ2V0KGZpbGVQYXRoKTtcblx0XHRpZiAoIWNvbnN0cykge1xuXHRcdFx0Y29uc3RzID0gbmV3IE1hcDxzdHJpbmcsIHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24+KCk7XG5cdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuc2V0KGZpbGVQYXRoLCBjb25zdHMpO1xuXHRcdH1cblx0XHRpZiAoIWNvbnN0cy5oYXMobm9kZS5uYW1lLnRleHQpKSB7XG5cdFx0XHRjb25zdHMuc2V0KG5vZGUubmFtZS50ZXh0LCBpbml0aWFsaXplcik7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEZpbmQgdGhlIGFycmF5IGxpdGVyYWwgYmVoaW5kIGEgbW9kdWxlIGNvbnN0IHJlZmVyZW5jZWQgdGhyb3VnaFxuXHQgKiBgdHlwZW9mYDogdGhlIGRlY2xhcmluZyBmaWxlJ3Mgb3duIGNvbnN0cyBmaXJzdCAodGhlIEYxMyBjYXNlIGlzIGFcblx0ICogTk9OLWV4cG9ydGVkIGNvbnN0IGluIHRoZSBzYW1lIG1vZHVsZSBhcyB0aGUgZXhwYW5kZWQgY2xhc3MpLCB0aGVuIOKAlFxuXHQgKiB3aGVuIHRoZSBmaWxlIGltcG9ydHMgdGhlIG5hbWUg4oCUIHRoZSBpbXBvcnRlZCBtb2R1bGUncyBjb25zdHMuXG5cdCAqIEV4dGVybmFsIG1vZHVsZXMgYXJlIG5ldmVyIGFuYWx5emVkLCBzbyB0aG9zZSB5aWVsZCBub3RoaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kUmVmZXJlbmNlZENvbnN0QXJyYXkgKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRmcm9tRmlsZTogc3RyaW5nXG5cdCk6IHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGxvY2FsID0gdGhpcy5yZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzLmdldChmcm9tRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWwpIHtcblx0XHRcdHJldHVybiBsb2NhbDtcblx0XHR9XG5cdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoZnJvbUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKCFpbXBvcnRlZCB8fCBpbXBvcnRlZC5pc05hbWVzcGFjZSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKGltcG9ydGVkLnNwZWNpZmllciwgZnJvbUZpbGUpO1xuXHRcdGlmICghcmVzb2x1dGlvbiB8fCByZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGZvdW5kID0gdGhpcy5yZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzLmdldChyZXNvbHV0aW9uLnJlc29sdmVkUGF0aCk/LmdldChpbXBvcnRlZC5vcmlnaW5hbE5hbWUpO1xuXHRcdHJldHVybiBmb3VuZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFbGVtZW50IGxpdGVyYWwgdHlwZXMgb2YgYSB0cmFja2VkIGNvbnN0IGFycmF5OiBldmVyeSBlbGVtZW50IG11c3QgYmVcblx0ICogYSBwbGFpbiBsaXRlcmFsIChvcHRpb25hbGx5IHdyYXBwZWQgaW4gYGFzIGNvbnN0YCAvIGBzYXRpc2ZpZXNgIC9cblx0ICogYDxjb25zdD5gIGFzc2VydGlvbnMpIOKAlCBzdHJpbmcsIG51bWVyaWMgKHVuYXJ5IGAtYC9gK2AgcHJlc2VydmVkKSxcblx0ICogYm9vbGVhbiwgb3IgbnVsbC4gU3ByZWFkcywgaWRlbnRpZmllcnMsIGFuZCBuZXN0ZWQgYXJyYXlzIG1lYW4gdGhlXG5cdCAqIHVuaW9uIGlzIG5vdCBzdGF0aWNhbGx5IHZpc2libGUgYW5kIHlpZWxkIHVuZGVmaW5lZCwgc28gdGhlIGNhbGxlclxuXHQgKiBkZWdyYWRlcyB0aGUgZmllbGQgdG8gYHVua25vd25gIHJhdGhlciB0aGFuIGd1ZXNzaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBsaXRlcmFsVHlwZXNPZkFycmF5IChhcnJheUxpdGVyYWw6IHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24pOiBzdHJpbmdbXSB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgbGl0ZXJhbHM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGFycmF5TGl0ZXJhbC5lbGVtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzU3ByZWFkRWxlbWVudChlbGVtZW50KSkge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbGl0ZXJhbCA9IHRoaXMubGl0ZXJhbFR5cGVPZkV4cHJlc3Npb24oZWxlbWVudCk7XG5cdFx0XHRpZiAobGl0ZXJhbCA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRsaXRlcmFscy5wdXNoKGxpdGVyYWwpO1xuXHRcdH1cblx0XHRpZiAobGl0ZXJhbHMubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBsaXRlcmFscztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFRoZSBsaXRlcmFsIHR5cGUgb2Ygb25lIGFycmF5IGVsZW1lbnQ6IGEgcGxhaW4gbGl0ZXJhbCAob3B0aW9uYWxseVxuXHQgKiB3cmFwcGVkIGluIGBhcyBjb25zdGAgLyBgc2F0aXNmaWVzYCAvIGFzc2VydGlvbiBleHByZXNzaW9ucykg4oCUXG5cdCAqIHN0cmluZywgbnVtZXJpYyAodW5hcnkgYC1gL2ArYCBwcmVzZXJ2ZWQpLCBib29sZWFuLCBvciBudWxsLlxuXHQgKiBBbnl0aGluZyBlbHNlIHlpZWxkcyB1bmRlZmluZWQuXG5cdCAqL1xuXHRwcml2YXRlIGxpdGVyYWxUeXBlT2ZFeHByZXNzaW9uIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgaW5uZXI6IHRzLkV4cHJlc3Npb24gPSBleHByO1xuXHRcdHdoaWxlICh0cy5pc0FzRXhwcmVzc2lvbihpbm5lcikgfHwgdHMuaXNTYXRpc2ZpZXNFeHByZXNzaW9uKGlubmVyKSB8fCB0cy5pc1R5cGVBc3NlcnRpb25FeHByZXNzaW9uKGlubmVyKSkge1xuXHRcdFx0aW5uZXIgPSBpbm5lci5leHByZXNzaW9uO1xuXHRcdH1cblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGlubmVyKSB8fCB0cy5pc05vU3Vic3RpdHV0aW9uVGVtcGxhdGVMaXRlcmFsKGlubmVyKSkge1xuXHRcdFx0Y29uc3QgbGl0ZXJhbCA9IGAnJHtpbm5lci50ZXh0fSdgO1xuXHRcdFx0cmV0dXJuIGxpdGVyYWw7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1ByZWZpeFVuYXJ5RXhwcmVzc2lvbihpbm5lcikgJiYgdHMuaXNOdW1lcmljTGl0ZXJhbChpbm5lci5vcGVyYW5kKSkge1xuXHRcdFx0aWYgKGlubmVyLm9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLk1pbnVzVG9rZW4pIHtcblx0XHRcdFx0Y29uc3QgbmVnYXRpdmUgPSBgLSR7aW5uZXIub3BlcmFuZC50ZXh0fWA7XG5cdFx0XHRcdHJldHVybiBuZWdhdGl2ZTtcblx0XHRcdH1cblx0XHRcdGlmIChpbm5lci5vcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5QbHVzVG9rZW4pIHtcblx0XHRcdFx0cmV0dXJuIGlubmVyLm9wZXJhbmQudGV4dDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc051bWVyaWNMaXRlcmFsKGlubmVyKSkge1xuXHRcdFx0cmV0dXJuIGlubmVyLnRleHQ7XG5cdFx0fVxuXHRcdGlmIChpbm5lci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRyZXR1cm4gJ3RydWUnO1xuXHRcdH1cblx0XHRpZiAoaW5uZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQpIHtcblx0XHRcdHJldHVybiAnZmFsc2UnO1xuXHRcdH1cblx0XHRpZiAoaW5uZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5OdWxsS2V5d29yZCkge1xuXHRcdFx0cmV0dXJuICdudWxsJztcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGMjI6IHRoZSBjb25zdC1hc3NlcnRpb24gY2hlY2sgc2hhcmVkIGJ5IHRoZSB2YWx1ZS1sZXZlbCBhbmRcblx0ICogZGVjbGFyYXRpb24tbGV2ZWwgcGF0aHMg4oCUIGBleHByIGFzIGNvbnN0YCBhbmQgYDxjb25zdD5leHByYCBwYXJzZVxuXHQgKiBpZGVudGljYWxseSAoYSBUeXBlUmVmZXJlbmNlTm9kZSBuYW1lZCAnY29uc3QnKS4gR2VuZXJhbCBgPFQ+ZXhwcmBcblx0ICogYXNzZXJ0aW9ucyBuZXZlciBtYXRjaC5cblx0ICovXG5cdHByaXZhdGUgaXNDb25zdEFzc2VydGlvblR5cGUgKHR5cGU6IHRzLlR5cGVOb2RlKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgY29uc3RBc3NlcnRpb24gPSB0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHR5cGUpICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIodHlwZS50eXBlTmFtZSkgJiZcblx0XHRcdHR5cGUudHlwZU5hbWUudGV4dCA9PT0gJ2NvbnN0Jztcblx0XHRyZXR1cm4gY29uc3RBc3NlcnRpb247XG5cdH1cblxuXHQvKipcblx0ICogVGhlIGFycmF5IGxpdGVyYWwgYmVoaW5kIGEgdmFsdWUtbGV2ZWwgZWxlbWVudCBhY2Nlc3M6IGlubGluZVxuXHQgKiAoYCg8Y29uc3Q+W+KApl0pWzBdYCwgYChb4oCmXSBhcyBjb25zdClbMV1gKSwgcGFyZW50aGVzaXplZCwgb3IgYVxuXHQgKiB0cmFja2VkIG1vZHVsZSBjb25zdCBhcnJheSAoYGNvbnN0IHggPSA8Y29uc3Q+W+KApl1gIC8gYHhbMF1gLCBGMTdcblx0ICogdHJhY2tpbmcpLiBPbmx5IGNvbnN0IGFzc2VydGlvbnMgYXJlIHVud3JhcHBlZCDigJQgZ2VuZXJhbFxuXHQgKiBhc3NlcnRpb25zIHN0YXkgdW5rbm93biAoRjIyIHNjb3BlIGJvdW5kYXJ5KS5cblx0ICovXG5cdHByaXZhdGUgY29uc3RBcnJheUxpdGVyYWxPZiAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5FeHByZXNzaW9uID0gZXhwcjtcblx0XHR3aGlsZSAodHMuaXNQYXJlbnRoZXNpemVkRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0aWYgKHRzLmlzQXJyYXlMaXRlcmFsRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0cmV0dXJuIGN1cnJlbnQ7XG5cdFx0fVxuXHRcdGlmICgodHMuaXNBc0V4cHJlc3Npb24oY3VycmVudCkgfHwgdHMuaXNUeXBlQXNzZXJ0aW9uRXhwcmVzc2lvbihjdXJyZW50KSkgJiZcblx0XHRcdHRoaXMuaXNDb25zdEFzc2VydGlvblR5cGUoY3VycmVudC50eXBlKSkge1xuXHRcdFx0Y29uc3QgaW5uZXIgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0XHRjb25zdCBsaXRlcmFsID0gdHMuaXNBcnJheUxpdGVyYWxFeHByZXNzaW9uKGlubmVyKSA/IGlubmVyIDogdW5kZWZpbmVkO1xuXHRcdFx0cmV0dXJuIGxpdGVyYWw7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudCkpIHtcblx0XHRcdGNvbnN0IHRyYWNrZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChjdXJyZW50LnRleHQpO1xuXHRcdFx0cmV0dXJuIHRyYWNrZWQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRW1pdC10eXBlIGZvciBgdHlwZW9mIG5hbWVgIHdoZW4gYG5hbWVgIGlzIGEgdHJhY2tlZCBjb25zdCBhcnJheTogdGhlXG5cdCAqIHVuaW9uIG9mIGl0cyBlbGVtZW50IGxpdGVyYWwgdHlwZXMgKGAnYWN0aXZlJyB8ICdjbG9zZWQnYCkuIEV2ZXJ5XG5cdCAqIG90aGVyIHR5cGVvZiBzb3VyY2Ug4oCUIG5vbi1hcnJheSBjb25zdHMsIGZ1bmN0aW9ucywgY2xhc3NlcywgbmFtZXMgbm90XG5cdCAqIHRyYWNrZWQgYXQgYWxsIOKAlCB5aWVsZHMgdW5kZWZpbmVkLCBzbyB0aGUgY2FsbGVyIGRlZ3JhZGVzIHRoZSBmaWVsZFxuXHQgKiB0byBgdW5rbm93bmA6IGEgYmFyZSBgdHlwZW9mIG5hbWVgIGVtaXR0ZWQgaW50byB0eXBlcy50cyBoYXMgbm9cblx0ICogaW1wb3J0IHRvIHJlc29sdmUgYWdhaW5zdCBkb3duc3RyZWFtLlxuXHQgKi9cblx0cHJpdmF0ZSB0eXBlT2ZDb25zdEFycmF5VW5pb24gKG5hbWU6IHN0cmluZywgZnJvbUZpbGU6IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJyYXlMaXRlcmFsID0gdGhpcy5maW5kUmVmZXJlbmNlZENvbnN0QXJyYXkobmFtZSwgZnJvbUZpbGUpO1xuXHRcdGlmICghYXJyYXlMaXRlcmFsKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBsaXRlcmFscyA9IHRoaXMubGl0ZXJhbFR5cGVzT2ZBcnJheShhcnJheUxpdGVyYWwpO1xuXHRcdGlmICghbGl0ZXJhbHMpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHVuaW9uID0gbGl0ZXJhbHMuam9pbignIHwgJyk7XG5cdFx0cmV0dXJuIHVuaW9uO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCB0aGUgaW1wb3J0aW5nIGZpbGUncyBuYW1lZC9uYW1lc3BhY2UvZGVmYXVsdCBpbXBvcnQgYmluZGluZ3Mgc29cblx0ICogcmVmZXJlbmNlZC10eXBlIG5hbWVzIHJlc29sdmUgdGhyb3VnaCB0aGUgZmlsZSdzIG93biBpbXBvcnQgc3RhdGVtZW50c1xuXHQgKiAoRjEwKSByYXRoZXIgdGhhbiBhIHByb2dyYW0td2lkZSBuYW1lIG1hcC5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tSZWZlcmVuY2VkVHlwZUltcG9ydCAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNJbXBvcnREZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCB7IG1vZHVsZVNwZWNpZmllciB9ID0gbm9kZTtcblx0XHRpZiAoIXRzLmlzU3RyaW5nTGl0ZXJhbChtb2R1bGVTcGVjaWZpZXIpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGNsYXVzZSA9IG5vZGUuaW1wb3J0Q2xhdXNlO1xuXHRcdGlmICghY2xhdXNlKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0bGV0IGltcG9ydHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoZmlsZVBhdGgpO1xuXHRcdGlmICghaW1wb3J0cykge1xuXHRcdFx0aW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZUltcG9ydD4oKTtcblx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLnNldChmaWxlUGF0aCwgaW1wb3J0cyk7XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0IHsgU2hhcmVkU2hhcGUgfSBmcm9tICfigKYnIC8gaW1wb3J0IHsgU2hhcmVkU2hhcGUgYXMgUyB9IGZyb20gJ+KApidcblx0XHRpZiAoY2xhdXNlLm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lZEltcG9ydHMoY2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2YgY2xhdXNlLm5hbWVkQmluZGluZ3MuZWxlbWVudHMpIHtcblx0XHRcdFx0Y29uc3QgbG9jYWxOYW1lID0gZWxlbWVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IG9yaWdpbmFsTmFtZSA9IGVsZW1lbnQucHJvcGVydHlOYW1lID8gZWxlbWVudC5wcm9wZXJ0eU5hbWUudGV4dCA6IGxvY2FsTmFtZTtcblx0XHRcdFx0aW1wb3J0cy5zZXQobG9jYWxOYW1lLCB7XG5cdFx0XHRcdFx0b3JpZ2luYWxOYW1lLFxuXHRcdFx0XHRcdHNwZWNpZmllciAgIDogbW9kdWxlU3BlY2lmaWVyLnRleHQsXG5cdFx0XHRcdFx0aXNOYW1lc3BhY2UgOiBmYWxzZVxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgKiBhcyBtb2RlbHMgZnJvbSAn4oCmJyDigJQgcmVzb2x2ZWQgd2hlbiBhIHF1YWxpZmllZCBuYW1lXG5cdFx0Ly8gKG1vZGVscy5TaGFyZWRTaGFwZSkgaXMgZW5jb3VudGVyZWRcblx0XHRpZiAoY2xhdXNlLm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lc3BhY2VJbXBvcnQoY2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHRpbXBvcnRzLnNldChjbGF1c2UubmFtZWRCaW5kaW5ncy5uYW1lLnRleHQsIHtcblx0XHRcdFx0b3JpZ2luYWxOYW1lIDogJycsXG5cdFx0XHRcdHNwZWNpZmllciAgICA6IG1vZHVsZVNwZWNpZmllci50ZXh0LFxuXHRcdFx0XHRpc05hbWVzcGFjZSAgOiB0cnVlXG5cdFx0XHR9KTtcblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgU2hhcmVkU2hhcGUgZnJvbSAn4oCmJyAoZGVmYXVsdCBpbXBvcnQpXG5cdFx0aWYgKGNsYXVzZS5uYW1lKSB7XG5cdFx0XHRpbXBvcnRzLnNldChjbGF1c2UubmFtZS50ZXh0LCB7XG5cdFx0XHRcdG9yaWdpbmFsTmFtZSA6ICdkZWZhdWx0Jyxcblx0XHRcdFx0c3BlY2lmaWVyICAgIDogbW9kdWxlU3BlY2lmaWVyLnRleHQsXG5cdFx0XHRcdGlzTmFtZXNwYWNlICA6IGZhbHNlXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIHJlLWV4cG9ydCB3aXJpbmcgKGBleHBvcnQgeyBYIH0gZnJvbSAn4oCmJ2AsIGBleHBvcnQgKiBmcm9tICfigKYnYCxcblx0ICogYGV4cG9ydCB7IFggYXMgWSB9YCkgc28gcmVzb2x1dGlvbiBjYW4gY2hhc2UgYmFycmVscyB0byB0aGUgb3JpZ2luXG5cdCAqIG1vZHVsZS4gTWlycm9ycyBNb2R1bGVHcmFwaEJ1aWxkZXIucmVzb2x2ZU9yaWdpbiwgbmFtZS1iYXNlZCBvbmx5LlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlUmVFeHBvcnQgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzRXhwb3J0RGVjbGFyYXRpb24obm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0Y29uc3QgeyBtb2R1bGVTcGVjaWZpZXIgfSA9IG5vZGU7XG5cdFx0Y29uc3Qgc3BlY2lmaWVyVGV4dCA9IG1vZHVsZVNwZWNpZmllciAmJiB0cy5pc1N0cmluZ0xpdGVyYWwobW9kdWxlU3BlY2lmaWVyKVxuXHRcdFx0PyBtb2R1bGVTcGVjaWZpZXIudGV4dFxuXHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHRpZiAobm9kZS5leHBvcnRDbGF1c2UgJiYgdHMuaXNOYW1lZEV4cG9ydHMobm9kZS5leHBvcnRDbGF1c2UpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2Ygbm9kZS5leHBvcnRDbGF1c2UuZWxlbWVudHMpIHtcblx0XHRcdFx0Y29uc3QgZXhwb3J0ZWROYW1lID0gZWxlbWVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IGxvY2FsTmFtZSA9IGVsZW1lbnQucHJvcGVydHlOYW1lID8gZWxlbWVudC5wcm9wZXJ0eU5hbWUudGV4dCA6IGV4cG9ydGVkTmFtZTtcblx0XHRcdFx0dGhpcy5tYXJrQnVpbGRlckV4cG9ydChleHBvcnRlZE5hbWUsIGxvY2FsTmFtZSwgZmlsZVBhdGgsIHNwZWNpZmllclRleHQpO1xuXHRcdFx0XHRpZiAoc3BlY2lmaWVyVGV4dCkge1xuXHRcdFx0XHRcdC8vIGV4cG9ydCB7IFggfSBmcm9tICfigKYnIC8gZXhwb3J0IHsgWCBhcyBZIH0gZnJvbSAn4oCmJ1xuXHRcdFx0XHRcdGxldCByZUV4cG9ydHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLmdldChmaWxlUGF0aCk7XG5cdFx0XHRcdFx0aWYgKCFyZUV4cG9ydHMpIHtcblx0XHRcdFx0XHRcdHJlRXhwb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLnNldChmaWxlUGF0aCwgcmVFeHBvcnRzKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0cmVFeHBvcnRzLnNldChleHBvcnRlZE5hbWUsIHNwZWNpZmllclRleHQpO1xuXHRcdFx0XHR9IGVsc2UgaWYgKGxvY2FsTmFtZSAhPT0gZXhwb3J0ZWROYW1lKSB7XG5cdFx0XHRcdFx0Ly8gZXhwb3J0IHsgWCBhcyBZIH0g4oCUIHNhbWUtZmlsZSBhbGlhcyBvZiBhIGxvY2FsIGRlY2xhcmF0aW9uXG5cdFx0XHRcdFx0bGV0IGFsaWFzZXMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0XHRcdGlmICghYWxpYXNlcykge1xuXHRcdFx0XHRcdFx0YWxpYXNlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcy5zZXQoZmlsZVBhdGgsIGFsaWFzZXMpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRhbGlhc2VzLnNldChleHBvcnRlZE5hbWUsIGxvY2FsTmFtZSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAobm9kZS5leHBvcnRDbGF1c2UgJiYgdHMuaXNOYW1lc3BhY2VFeHBvcnQobm9kZS5leHBvcnRDbGF1c2UpKSB7XG5cdFx0XHQvLyBgZXhwb3J0ICogYXMgbnMgZnJvbSAn4oCmJ2Ag4oCUIGEgbmVzdGVkIG1vZHVsZSBuYW1lc3BhY2U7IG1pZGRsZVxuXHRcdFx0Ly8gc2VnbWVudHMgb2YgcXVhbGlmaWVkIHJlZmVyZW5jZXMgKGJhcnJlbC5EZWVwLkdhZGdldCkgY2hhc2UgaXRcblx0XHRcdGlmIChzcGVjaWZpZXJUZXh0KSB7XG5cdFx0XHRcdGxldCBzdGFycyA9IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VTdGFycy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0XHRpZiAoIXN0YXJzKSB7XG5cdFx0XHRcdFx0c3RhcnMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VTdGFycy5zZXQoZmlsZVBhdGgsIHN0YXJzKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRzdGFycy5zZXQobm9kZS5leHBvcnRDbGF1c2UubmFtZS50ZXh0LCBzcGVjaWZpZXJUZXh0KTtcblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAoIW5vZGUuZXhwb3J0Q2xhdXNlICYmIHNwZWNpZmllclRleHQpIHtcblx0XHRcdC8vIGV4cG9ydCAqIGZyb20gJ+KApidcblx0XHRcdGxldCBzdGFycyA9IHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0aWYgKCFzdGFycykge1xuXHRcdFx0XHRzdGFycyA9IFtdO1xuXHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuc2V0KGZpbGVQYXRoLCBzdGFycyk7XG5cdFx0XHR9XG5cdFx0XHRzdGFycy5wdXNoKHNwZWNpZmllclRleHQpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgbW9kdWxlIHNwZWNpZmllciBmcm9tIGEgY29udGFpbmluZyBmaWxlIHdpdGggdGhlIHByb2dyYW0nc1xuXHQgKiBjb21waWxlck9wdGlvbnMgKHRzY29uZmlnIGBwYXRoc2AsIGV4dGVuc2lvbmxlc3MgaW1wb3J0cywgaW5kZXggZmlsZXMpLlxuXHQgKiBNb2R1bGUgcmVzb2x1dGlvbiBvbmx5IOKAlCB0aGUgbm8tZ2V0VHlwZUNoZWNrZXIoKSBwcmVjZWRlbnQgc3RheXMuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZSAoc3BlY2lmaWVyOiBzdHJpbmcsIGNvbnRhaW5pbmdGaWxlOiBzdHJpbmcpOlxuXHRcdFJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2FjaGVLZXkgPSBgJHtjb250YWluaW5nRmlsZX06OiR7c3BlY2lmaWVyfWA7XG5cdFx0aWYgKHRoaXMucmVmZXJlbmNlZFR5cGVSZXNvbHV0aW9uQ2FjaGUuaGFzKGNhY2hlS2V5KSkge1xuXHRcdFx0Y29uc3QgY2FjaGVkID0gdGhpcy5yZWZlcmVuY2VkVHlwZVJlc29sdXRpb25DYWNoZS5nZXQoY2FjaGVLZXkpO1xuXHRcdFx0cmV0dXJuIGNhY2hlZCA9PT0gdW5kZWZpbmVkID8gdW5kZWZpbmVkIDogY2FjaGVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlc29sdXRpb24gPSB0cy5yZXNvbHZlTW9kdWxlTmFtZShcblx0XHRcdHNwZWNpZmllcixcblx0XHRcdGNvbnRhaW5pbmdGaWxlLFxuXHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUNvbXBpbGVyT3B0aW9ucyxcblx0XHRcdHRzLnN5c1xuXHRcdCkucmVzb2x2ZWRNb2R1bGU7XG5cblx0XHRjb25zdCByZXN1bHQ6IFJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbiB8IHVuZGVmaW5lZCA9IHJlc29sdXRpb25cblx0XHRcdD8ge1xuXHRcdFx0XHRyZXNvbHZlZFBhdGggOiBub2RlUGF0aC5yZXNvbHZlKHJlc29sdXRpb24ucmVzb2x2ZWRGaWxlTmFtZSksXG5cdFx0XHRcdGlzRXh0ZXJuYWwgICA6ICEhcmVzb2x1dGlvbi5pc0V4dGVybmFsTGlicmFyeUltcG9ydFxuXHRcdFx0fVxuXHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbkNhY2hlLnNldChjYWNoZUtleSwgcmVzdWx0KTtcblx0XHRjb25zdCBmaW5hbFJlc3VsdCA9IHJlc3VsdDtcblx0XHRyZXR1cm4gZmluYWxSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogTG9vayB1cCBhIG5hbWUgaW4gb25lIHJlc29sdmVkIG1vZHVsZSwgY2hhc2luZyByZS1leHBvcnQgYmFycmVscyB3aXRoIGFcblx0ICogYm91bmRlZCBkZXB0aC4gRXh0ZXJuYWwgKG5vZGVfbW9kdWxlcykgbW9kdWxlcyBob2xkIG5vIGluLXByb2plY3Rcblx0ICogZGVjbGFyYXRpb25zIGFuZCBzdG9wIHRoZSBjaGFzZS5cblx0ICovXG5cdHByaXZhdGUgZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUgKFxuXHRcdG1vZHVsZVBhdGg6IHN0cmluZyxcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0ZGVwdGg6IG51bWJlclxuXHQpOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoZGVwdGggPiBNQVhfUkVFWFBPUlRfQ0hBU0VfREVQVEgpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGVjbHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRGVjbHMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGNvbnN0IGRpcmVjdCA9IGRlY2xzPy5nZXQobmFtZSk7XG5cdFx0aWYgKGRpcmVjdCkge1xuXHRcdFx0cmV0dXJuIGRpcmVjdDtcblx0XHR9XG5cdFx0Ly8gZXhwb3J0IHsgWCBhcyBZIH0g4oCUIHJlc29sdmUgdGhyb3VnaCB0aGUgbG9jYWwgbmFtZVxuXHRcdGNvbnN0IGxvY2FsQWxpYXMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcy5nZXQobW9kdWxlUGF0aCk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWxBbGlhcykge1xuXHRcdFx0Y29uc3QgYWxpYXNlZCA9IGRlY2xzPy5nZXQobG9jYWxBbGlhcyk7XG5cdFx0XHRpZiAoYWxpYXNlZCkge1xuXHRcdFx0XHRyZXR1cm4gYWxpYXNlZDtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCByZUV4cG9ydHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLmdldChtb2R1bGVQYXRoKTtcblx0XHRjb25zdCByZUV4cG9ydFNwZWNpZmllciA9IHJlRXhwb3J0cz8uZ2V0KG5hbWUpO1xuXHRcdGlmIChyZUV4cG9ydFNwZWNpZmllcikge1xuXHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShyZUV4cG9ydFNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRpZiAobmV4dFJlc29sdXRpb24gJiYgIW5leHRSZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgbmFtZSwgZGVwdGggKyAxKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGlmIChzdGFycykge1xuXHRcdFx0Zm9yIChjb25zdCBzdGFyU3BlY2lmaWVyIG9mIHN0YXJzKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoc3RhclNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRcdGlmICghbmV4dFJlc29sdXRpb24gfHwgbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZShuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIG5hbWUsIGRlcHRoICsgMSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHJlZmVyZW5jZWQgdHlwZSBuYW1lIGFzIHVzZWQgaW4gZnJvbUZpbGUsIGltcG9ydC1hd2FyZTpcblx0ICogICAxLiB0aGUgZmlsZSdzIG93biBpbXBvcnQgc3RhdGVtZW50cyAocmVsYXRpdmUgKyB0c2NvbmZpZyBwYXRocyxcblx0ICogICAgICBjaGFzZWQgdGhyb3VnaCByZS1leHBvcnQgYmFycmVscyksXG5cdCAqICAgMi4gdGhlIGZpbGUncyBsb2NhbCBkZWNsYXJhdGlvbnMsXG5cdCAqICAgMy4gdGhlIHVuaXF1ZSBzYW1lLW5hbWVkIGRlY2xhcmF0aW9uIGFjcm9zcyBzY2FubmVkIGZpbGVzLlxuXHQgKiBSZXR1cm5zIHVuZGVmaW5lZCB3aGVuIG5vdGhpbmcgbWF0Y2hlcyAob3IgdGhlIG1hdGNoIGlzIGFtYmlndW91cyksXG5cdCAqIGluIHdoaWNoIGNhc2UgdGhlIGNhbGxlciBmYWxscyBiYWNrIHRvIGB1bmtub3duYC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRmcm9tRmlsZTogc3RyaW5nXG5cdCk6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdC8vIDEuIHRoZSBmaWxlJ3Mgb3duIGltcG9ydHMgd2luIOKAlCBhbiBpbXBvcnQgaXMgbmV2ZXIgc2hhZG93ZWQgYnkgYVxuXHRcdC8vIHNhbWUtbmFtZWQgbG9jYWwgZGVjbGFyYXRpb24gZWxzZXdoZXJlIGluIHRoZSBwcm9ncmFtIChGMTApXG5cdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoZnJvbUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGltcG9ydGVkICYmICFpbXBvcnRlZC5pc05hbWVzcGFjZSkge1xuXHRcdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKGltcG9ydGVkLnNwZWNpZmllciwgZnJvbUZpbGUpO1xuXHRcdFx0aWYgKHJlc29sdXRpb24gJiYgIXJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRjb25zdCBmb3VuZCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUocmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIGltcG9ydGVkLm9yaWdpbmFsTmFtZSwgMCk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIDIuIGxvY2FsIGRlY2xhcmF0aW9uIGluIHRoZSByZWZlcmVuY2luZyBmaWxlIGl0c2VsZlxuXHRcdGNvbnN0IGxvY2FsID0gdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLmdldChmcm9tRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWwpIHtcblx0XHRcdHJldHVybiBsb2NhbDtcblx0XHR9XG5cblx0XHQvLyAzLiBwcm9ncmFtLXdpZGUgZmFsbGJhY2ssIHVuaXF1ZSBkZWNsYXJhdGlvbiBvbmx5IOKAlCBhbWJpZ3VpdHkgYW5kXG5cdFx0Ly8gYWJzZW5jZSBib3RoIHlpZWxkIHVuZGVmaW5lZCAodGhlIGNhbGxlciBlbWl0cyBgdW5rbm93bmApLlxuXHRcdC8vIEV4dGVybmFsL2FtYmllbnQgZGVjbGFyYXRpb25zICguZC50cywgbm9kZV9tb2R1bGVzKSBkbyBub3Rcblx0XHQvLyBwYXJ0aWNpcGF0ZTogYSB1c2VyLWxvY2FsIGRlY2xhcmF0aW9uIGFsd2F5cyB3aW5zIG92ZXIgYVxuXHRcdC8vIHBhY2thZ2UtZGVjbGFyZWQgc2FtZS1uYW1lZCB0eXBlICh0aGUgcGxhaW4tVFMgdGllciBvZiB0aGVcblx0XHQvLyBpZGVudGl0eSBsYXc7IGFtYmlndWl0eSBhbW9uZyB0aGUgcmVtYWluaW5nIGRlY2xhcmF0aW9ucyBpc1xuXHRcdC8vIHZhbGlkYXRlZCBzZXBhcmF0ZWx5IGFzIGEgaGFyZCBmYWlsKVxuXHRcdGxldCB1bmlxdWU6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQ7XG5cdFx0bGV0IGNvdW50ID0gMDtcblx0XHRmb3IgKGNvbnN0IFsgZmlsZVBhdGgsIGRlY2xzIF0gb2YgdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzKSB7XG5cdFx0XHRpZiAodGhpcy5pc0V4dGVybmFsRGVjbEZpbGUoZmlsZVBhdGgpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgY2FuZGlkYXRlID0gZGVjbHMuZ2V0KG5hbWUpO1xuXHRcdFx0aWYgKGNhbmRpZGF0ZSkge1xuXHRcdFx0XHRjb3VudCsrO1xuXHRcdFx0XHR1bmlxdWUgPSBjYW5kaWRhdGU7XG5cdFx0XHRcdGlmIChjb3VudCA+IDEpIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVzdWx0ID0gY291bnQgPT09IDEgPyB1bmlxdWUgOiB1bmRlZmluZWQ7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRlcm5hbC9hbWJpZW50IGRlY2xhcmF0aW9uIGZpbGVzICguZC50cywgYW55dGhpbmcgdW5kZXJcblx0ICogbm9kZV9tb2R1bGVzKSBuZXZlciBwYXJ0aWNpcGF0ZSBpbiBwbGFpbi1UUyByZWZlcmVuY2VkLXR5cGVcblx0ICogcmVzb2x1dGlvbiBvciB0aGUgYW1iaWd1aXR5IGxhdzogdGhleSBhcmUgbm90IHByb2plY3Qgc291cmNlLCB0aGVcblx0ICogQ0xJIG5ldmVyIGFuYWx5emVzIHRoZW0sIGFuZCBhIHVzZXItbG9jYWwgZGVjbGFyYXRpb24gYWx3YXlzIHdpbnNcblx0ICogb3ZlciBhIHBhY2thZ2UtZGVjbGFyZWQgc2FtZS1uYW1lZCB0eXBlLlxuXHQgKi9cblx0cHJpdmF0ZSBpc0V4dGVybmFsRGVjbEZpbGUgKGZpbGU6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRcdGNvbnN0IGV4dGVybmFsID0gZmlsZS5lbmRzV2l0aCgnLmQudHMnKSB8fFxuXHRcdFx0ZmlsZS5pbmNsdWRlcyhgJHtub2RlUGF0aC5zZXB9bm9kZV9tb2R1bGVzJHtub2RlUGF0aC5zZXB9YCk7XG5cdFx0cmV0dXJuIGV4dGVybmFsO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb3BlcnRpZXMgb2YgYSByZWZlcmVuY2VkIGNsYXNzL2ludGVyZmFjZS9hbGlhcy1vZi1saXRlcmFsIGRlY2xhcmF0aW9uLFxuXHQgKiBzaGFyZWQgYnkgYHRoaXM6YC1wYXJhbWV0ZXIgZXhwYW5zaW9uIGFuZCBpbmxpbmUgdHlwZSBlbWlzc2lvbi5cblx0ICogSW5oZXJpdGVkIG1lbWJlcnMgYXJlIGluY2x1ZGVkOiB0aGUgZXh0ZW5kcyBjaGFpbiBpcyB3YWxrZWRcblx0ICogKGRlcHRoLWNhcHBlZCwgY3ljbGUtZ3VhcmRlZCkgYW5kIHBhcmVudCBmaWVsZHMgbWVyZ2UgZmlyc3QsIHRoZVxuXHQgKiBkZWNsYXJhdGlvbidzIG93biBmaWVsZHMgb3ZlcnJpZGluZyBvbiBuYW1lIGNsYXNoLlxuXHQgKi9cblx0cHJpdmF0ZSByZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzIChkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKTpcblx0XHRNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCB2aXNpdGVkID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllc0lubmVyKGRlY2wsIHZpc2l0ZWQsIDApO1xuXHRcdHJldHVybiBwcm9wZXJ0aWVzO1xuXHR9XG5cblx0cHJpdmF0ZSByZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzSW5uZXIgKFxuXHRcdGRlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24sXG5cdFx0dmlzaXRlZDogU2V0PHN0cmluZz4sXG5cdFx0ZGVwdGg6IG51bWJlclxuXHQpOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCBvd25Qcm9wZXJ0aWVzID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblx0XHRjb25zdCBkZWNsTm9kZSA9IGRlY2wubm9kZSBhcyB0cy5DbGFzc0RlY2xhcmF0aW9uIHwgdHMuSW50ZXJmYWNlRGVjbGFyYXRpb247XG5cdFx0Y29uc3QgZGVjbE5hbWUgPSBkZWNsTm9kZS5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihkZWNsTm9kZS5uYW1lKSA/IGRlY2xOb2RlLm5hbWUudGV4dCA6ICcnO1xuXHRcdGNvbnN0IHZpc2l0S2V5ID0gYCR7ZGVjbC5raW5kfToke2RlY2wuZmlsZX06JHtkZWNsTmFtZX1gO1xuXHRcdGlmIChkZXB0aCA+IE1BWF9IRVJJVEFHRV9ERVBUSCB8fCB2aXNpdGVkLmhhcyh2aXNpdEtleSkpIHtcblx0XHRcdHJldHVybiBvd25Qcm9wZXJ0aWVzO1xuXHRcdH1cblx0XHR2aXNpdGVkLmFkZCh2aXNpdEtleSk7XG5cblx0XHRpZiAoZGVjbC5raW5kID09PSAnY2xhc3MnKSB7XG5cdFx0XHRjb25zdCBjbGFzc1Byb3BzID0gdGhpcy5leHRyYWN0Q2xhc3NQcm9wZXJ0aWVzKGRlY2wubm9kZSBhcyB0cy5DbGFzc0RlY2xhcmF0aW9uKTtcblx0XHRcdGZvciAoY29uc3QgWyBuYW1lLCBpbmZvIF0gb2YgY2xhc3NQcm9wcykge1xuXHRcdFx0XHRvd25Qcm9wZXJ0aWVzLnNldChuYW1lLCBpbmZvKTtcblx0XHRcdH1cblx0XHR9IGVsc2UgaWYgKGRlY2wua2luZCA9PT0gJ2ludGVyZmFjZScpIHtcblx0XHRcdGNvbnN0IGlmYWNlID0gZGVjbC5ub2RlIGFzIHRzLkludGVyZmFjZURlY2xhcmF0aW9uO1xuXHRcdFx0dGhpcy5jb2xsZWN0VHlwZUVsZW1lbnRQcm9wZXJ0aWVzKFsgLi4uaWZhY2UubWVtYmVycyBdLCBvd25Qcm9wZXJ0aWVzKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0Y29uc3QgYWxpYXNUeXBlID0gKGRlY2wubm9kZSBhcyB0cy5UeXBlQWxpYXNEZWNsYXJhdGlvbikudHlwZTtcblx0XHRcdGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZShhbGlhc1R5cGUpKSB7XG5cdFx0XHRcdHRoaXMuY29sbGVjdFR5cGVFbGVtZW50UHJvcGVydGllcyhbIC4uLmFsaWFzVHlwZS5tZW1iZXJzIF0sIG93blByb3BlcnRpZXMpO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0cmV0dXJuIG93blByb3BlcnRpZXM7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gaGVyaXRhZ2UgbWVyZ2VzIHBhcmVudCBmaWVsZHMgZmlyc3Q7IHRoZSBkZWNsYXJhdGlvbidzIG93biBmaWVsZHNcblx0XHQvLyBvdmVycmlkZSBvbiBuYW1lIGNsYXNoIChsYXRlciBiYXNlcyBvdmVycmlkZSBlYXJsaWVyIG9uZXMpXG5cdFx0Y29uc3QgbWVyZ2VkID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblx0XHRmb3IgKGNvbnN0IGJhc2VEZWNsIG9mIHRoaXMucmVzb2x2ZUhlcml0YWdlRGVjbGFyYXRpb25zKGRlY2wpKSB7XG5cdFx0XHRjb25zdCBiYXNlUHJvcHMgPSB0aGlzLnJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXNJbm5lcihiYXNlRGVjbCwgdmlzaXRlZCwgZGVwdGggKyAxKTtcblx0XHRcdGZvciAoY29uc3QgWyBuYW1lLCBpbmZvIF0gb2YgYmFzZVByb3BzKSB7XG5cdFx0XHRcdG1lcmdlZC5zZXQobmFtZSwgaW5mbyk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGZvciAoY29uc3QgWyBuYW1lLCBpbmZvIF0gb2Ygb3duUHJvcGVydGllcykge1xuXHRcdFx0bWVyZ2VkLnNldChuYW1lLCBpbmZvKTtcblx0XHR9XG5cdFx0cmV0dXJuIG1lcmdlZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBQcm9wZXJ0eSBzaWduYXR1cmVzIG9mIGludGVyZmFjZS9hbGlhcyB0eXBlLWxpdGVyYWwgbWVtYmVycywgaW50b1xuXHQgKiB0aGUgZ2l2ZW4gbWFwLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0VHlwZUVsZW1lbnRQcm9wZXJ0aWVzIChcblx0XHRtZW1iZXJzOiByZWFkb25seSB0cy5UeXBlRWxlbWVudFtdLFxuXHRcdHByb3BlcnRpZXM6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz5cblx0KTogdm9pZCB7XG5cdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgbWVtYmVycykge1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0cHJvcGVydGllcy5zZXQocHJvcE5hbWUsIHtcblx0XHRcdFx0XHRuYW1lICAgICA6IHByb3BOYW1lLFxuXHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0aGUgaGVyaXRhZ2UgY2xhdXNlIG9mIGEgY2xhc3MgKGBleHRlbmRzIEJhc2VgKSBvciBpbnRlcmZhY2Vcblx0ICogKGBleHRlbmRzIEEsIEJgKSB0byByZWZlcmVuY2VkLXR5cGUgZGVjbGFyYXRpb25zIHRocm91Z2ggdGhlIFNBTUVcblx0ICogaW1wb3J0LWF3YXJlIG1hY2hpbmVyeSBhcyBwbGFpbiByZWZlcmVuY2VzICh0aGUgZGVjbGFyaW5nIGZpbGUncyBvd25cblx0ICogaW1wb3J0cyBmaXJzdCwgdGhlbiBpdHMgbG9jYWxzLCB0aGVuIHRoZSB1bmlxdWUgcHJvZ3JhbS13aWRlXG5cdCAqIGRlY2xhcmF0aW9uKS4gVW5yZXNvbHZhYmxlIG9yIGV4dGVybmFsIGJhc2VzIHlpZWxkIG5vdGhpbmcg4oCUIHRoZWlyXG5cdCAqIGluaGVyaXRlZCBmaWVsZHMgc2ltcGx5IHN0YXkgYWJzZW50LCBzYW1lIGFzIGJlZm9yZSB0aGlzIHdhbGtcblx0ICogZXhpc3RlZC4gTWl4aW4gY2FsbHMgKGBleHRlbmRzIG1peGluKFgpYCkgYW5kIG5hbWVzcGFjZSBhY2Nlc3MgYXJlXG5cdCAqIG5vdCBmb2xsb3dlZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUhlcml0YWdlRGVjbGFyYXRpb25zIChkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbltdIHtcblx0XHRjb25zdCB7IGhlcml0YWdlQ2xhdXNlcyB9ID0gKGRlY2wubm9kZSBhcyB0cy5DbGFzc0RlY2xhcmF0aW9uIHwgdHMuSW50ZXJmYWNlRGVjbGFyYXRpb24pO1xuXHRcdGlmICghaGVyaXRhZ2VDbGF1c2VzKSB7XG5cdFx0XHRyZXR1cm4gW107XG5cdFx0fVxuXHRcdGNvbnN0IGJhc2VzOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IGNsYXVzZSBvZiBoZXJpdGFnZUNsYXVzZXMpIHtcblx0XHRcdGlmIChjbGF1c2UudG9rZW4gIT09IHRzLlN5bnRheEtpbmQuRXh0ZW5kc0tleXdvcmQpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGhlcml0YWdlVHlwZSBvZiBjbGF1c2UudHlwZXMpIHtcblx0XHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoaGVyaXRhZ2VUeXBlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgYmFzZU5hbWUgPSBoZXJpdGFnZVR5cGUuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHRjb25zdCBiYXNlRGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oYmFzZU5hbWUsIGRlY2wuZmlsZSk7XG5cdFx0XHRcdGlmIChiYXNlRGVjbCkge1xuXHRcdFx0XHRcdGJhc2VzLnB1c2goYmFzZURlY2wpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGJhc2VzO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRXhwYW5kIGEgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9uIHRvIGEgc2VsZi1jb250YWluZWQgdHlwZSBzdHJpbmdcblx0ICogZm9yIGVtaXNzaW9uIGludG8gZ2VuZXJhdGVkIGZpbGVzOiB0eXBlIGFsaWFzZXMgdGhyb3VnaCBpbmZlclR5cGUsXG5cdCAqIGNsYXNzZXMgYW5kIGludGVyZmFjZXMgdGhyb3VnaCB0aGVpciAocHVibGljLCBub24tbWV0aG9kKSBmaWVsZHMuXG5cdCAqIE5lc3RlZCByZWZlcmVuY2VzIHJlc29sdmUgYWdhaW5zdCB0aGUgZGVjbGFyaW5nIGZpbGUgd2hpbGUgZXhwYW5kaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBleHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIChkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCByZWZlcmVuY2luZ0ZpbGUgPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gZGVjbC5maWxlO1xuXHRcdHRyeSB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25Jbm5lcihkZWNsKTtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fSBmaW5hbGx5IHtcblx0XHRcdHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9IHJlZmVyZW5jaW5nRmlsZTtcblx0XHR9XG5cdH1cblxuXHRwcml2YXRlIGV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25Jbm5lciAoZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKGRlY2wua2luZCA9PT0gJ2FsaWFzJykge1xuXHRcdFx0Y29uc3QgYWxpYXNOb2RlID0gZGVjbC5ub2RlIGFzIHRzLlR5cGVBbGlhc0RlY2xhcmF0aW9uO1xuXHRcdFx0Y29uc3QgYWxpYXNOYW1lID0gdHMuaXNJZGVudGlmaWVyKGFsaWFzTm9kZS5uYW1lKSA/IGFsaWFzTm9kZS5uYW1lLnRleHQgOiAnJztcblx0XHRcdGlmIChhbGlhc05hbWUgJiYgdGhpcy5leHBhbmRpbmdSZWZlcmVuY2VkQWxpYXNlcy5oYXMoYWxpYXNOYW1lKSkge1xuXHRcdFx0XHQvLyBTZWxmLXJlZmVyZW50aWFsIGFsaWFzIGNoYWluIOKAlCBiYWlsIG91dFxuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGFsaWFzTmFtZSkge1xuXHRcdFx0XHR0aGlzLmV4cGFuZGluZ1JlZmVyZW5jZWRBbGlhc2VzLmFkZChhbGlhc05hbWUpO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmluZmVyVHlwZShhbGlhc05vZGUudHlwZSk7XG5cdFx0XHRpZiAoYWxpYXNOYW1lKSB7XG5cdFx0XHRcdHRoaXMuZXhwYW5kaW5nUmVmZXJlbmNlZEFsaWFzZXMuZGVsZXRlKGFsaWFzTmFtZSk7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gZXhwYW5kZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGVjbFByb3BlcnRpZXMgPSB0aGlzLnJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXMoZGVjbCk7XG5cdFx0Y29uc3QgcHJvcHMgPSBBcnJheS5mcm9tKGRlY2xQcm9wZXJ0aWVzLmVudHJpZXMoKSkubWFwKChbIHByb3BOYW1lLCBpbmZvIF0pID0+IHtcblx0XHRcdGNvbnN0IG9wdGlvbmFsID0gaW5mby5vcHRpb25hbCA/ICc/JyA6ICcnO1xuXHRcdFx0cmV0dXJuIGAke3Byb3BOYW1lfSR7b3B0aW9uYWx9OiAke2luZm8udHlwZX1gO1xuXHRcdH0pO1xuXG5cdFx0Y29uc3QgcmVzdWx0ID0gYHsgJHtwcm9wcy5qb2luKCc7ICcpfSB9YDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEVtaXR0ZWQgaW5zdGFuY2UtdHlwZSBhbGlhcyBmb3IgYSBncmFwaCBub2RlIOKAlCB0aGUgbmFtZSB0eXBlcy50cyAvXG5cdCAqIHJlZ2lzdHJ5LnRzIGFjdHVhbGx5IGRlY2xhcmUuIE9wdGlvbiBCIGNvbGxlY3Rpb24gdHlwZXMgY2FycnkgdGhlaXJcblx0ICogcmVnaXN0cnkgaW50ZXJmYWNlIHByZWZpeDsgY29sbGVjdGlvbiB0eXBlcyBXSVRIT1VUIGEgcmVnaXN0cnlcblx0ICogaW50ZXJmYWNlIGFyZSBuZXZlciBlbWl0dGVkLCBzbyBubyB2YWxpZCBhbGlhcyBleGlzdHMgZm9yIHRoZW1cblx0ICogKHVuZGVmaW5lZCDigJQgY2FsbGVycyBkZWdyYWRlIHRvIGB1bmtub3duYCwgbmV2ZXIgYSBiYXJlIG5hbWUpLlxuXHQgKi9cblx0cHJpdmF0ZSBnZXRFbWl0dGVkSW5zdGFuY2VUeXBlTmFtZSAobm9kZTogVHlwZU5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmIChub2RlLmNvbGxlY3Rpb25JZCAmJiAhbm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWUpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGRvdHRlZCA9IG5vZGUuY29sbGVjdGlvbklkXG5cdFx0XHQ/IG5vZGUuZnVsbFBhdGguc2xpY2Uobm9kZS5jb2xsZWN0aW9uSWQubGVuZ3RoICsgMilcblx0XHRcdDogbm9kZS5mdWxsUGF0aDtcblx0XHRjb25zdCBwcmVmaXggPSBub2RlLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA/IGAke25vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lfV9gIDogJyc7XG5cdFx0Y29uc3QgcmVzdWx0ID0gYCR7cHJlZml4fSR7ZG90dGVkLnJlcGxhY2UoL1xcLi9nLCAnXycpfWA7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgc2ltcGxlIChub24tcXVhbGlmaWVkKSB0eXBlIHJlZmVyZW5jZTogaW1wb3J0LWF3YXJlXG5cdCAqIGRlY2xhcmF0aW9uIGV4cGFuc2lvbiBmaXJzdCwgdGhlbiB0aGUgSW5zdGFuY2VUeXBlPHR5cGVvZiBYPiBwYXR0ZXJuLFxuXHQgKiB0aGVuIG1uZW1vbmljYSBncmFwaCB0eXBlczsga25vd24gZ2xvYmFscyBrZWVwIHRoZWlyIGJhcmUgbmFtZSBhbmRcblx0ICogYW55dGhpbmcgZWxzZSBmYWxscyBiYWNrIHRvIGB1bmtub3duYCBzbyBnZW5lcmF0ZWQgZmlsZXMgbmV2ZXIgY2Fycnlcblx0ICogYW4gdW5yZXNvbHZhYmxlIGJhcmUgbmFtZS4gUmV0dXJucyB1bmRlZmluZWQgd2hlbiB0aGUgY2FsbGVyIHNob3VsZFxuXHQgKiBrZWVwIHRoZSBnZW5lcmljIHNwZWxsaW5nIChoYW5kbGVkIHNlcGFyYXRlbHkpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlU2ltcGxlVHlwZVJlZmVyZW5jZSAoXG5cdFx0dHlwZU5hbWU6IHN0cmluZyxcblx0XHR0eXBlQXJncz86IHRzLk5vZGVBcnJheTx0cy5UeXBlTm9kZT4sXG5cdFx0cmVmTm9kZT86IHRzLk5vZGVcblx0KTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBJbXBvcnQtYXdhcmUgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9uIChGMTApXG5cdFx0Y29uc3QgZGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24odHlwZU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0aWYgKGRlY2wpIHtcblx0XHRcdGNvbnN0IGV4cGFuZGVkID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKGRlY2wpO1xuXHRcdFx0aWYgKGV4cGFuZGVkICE9PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0cmV0dXJuIGV4cGFuZGVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgdW5rbm93blJlc3VsdCA9ICd1bmtub3duJztcblx0XHRcdHJldHVybiB1bmtub3duUmVzdWx0O1xuXHRcdH1cblxuXHRcdC8vIEluc3RhbmNlVHlwZTx0eXBlb2YgWD4gbGF3ICgwLjIuMCBiZWhhdmlvciwgcmVzdG9yZWQpOiB0aGVcblx0XHQvLyBnZW5lcmF0ZWQgYWxpYXMgYWxyZWFkeSBJUyB0aGUgaW5zdGFuY2UgdHlwZSDigJQgcmVzb2x2ZSBYIHRocm91Z2hcblx0XHQvLyB0aGUgZ3JhcGggdGllcnMgYW5kIGRyb3AgdGhlIHdyYXBwZXIuIE11c3QgcnVuIEJFRk9SRSB0aGUgZ3JhcGhcblx0XHQvLyByZXNvbHV0aW9uOiAnSW5zdGFuY2VUeXBlJyBpcyBhbiBhbWJpZW50IGdsb2JhbCwgbmV2ZXIgYSBncmFwaFxuXHRcdC8vIHR5cGUgKHRoZSBvbGQgc3BlY2lhbCBjYXNlIGJlbG93IHNhdCBpbnNpZGUgdGhlIGdyYXBoLXVuaXF1ZVxuXHRcdC8vIGJyYW5jaCBhbmQgd2FzIGRlYWQgY29kZSkuIFdoZW4gWCBkb2VzIG5vdCByZXNvbHZlLCB0aGUgV0hPTEVcblx0XHQvLyBleHByZXNzaW9uIGRlZ3JhZGVzIHRvIGB1bmtub3duYCDigJQgbmV2ZXIgZW1pdFxuXHRcdC8vIGBJbnN0YW5jZVR5cGU8dW5rbm93bj5gOiBpbnZhbGlkIFRTIChUUzIzNDQsICd1bmtub3duJyBkb2VzIG5vdFxuXHRcdC8vIHNhdGlzZnkgdGhlIGNvbnN0cnVjdG9yIGNvbnN0cmFpbnQpLiBSZWFjaGVkIGRpcmVjdGx5IG9yIHRocm91Z2hcblx0XHQvLyBhIGxvY2FsIGFsaWFzIChgWEluc3RhbmNlID0gSW5zdGFuY2VUeXBlPHR5cGVvZiBYPmApLlxuXHRcdGlmICh0eXBlTmFtZSA9PT0gJ0luc3RhbmNlVHlwZScgJiYgdHlwZUFyZ3MgJiYgdHlwZUFyZ3MubGVuZ3RoID09PSAxKSB7XG5cdFx0XHRjb25zdCBbIGluc3RhbmNlQXJnIF0gPSB0eXBlQXJncztcblx0XHRcdGlmIChpbnN0YW5jZUFyZyAmJiB0cy5pc1R5cGVRdWVyeU5vZGUoaW5zdGFuY2VBcmcpICYmIHRzLmlzSWRlbnRpZmllcihpbnN0YW5jZUFyZy5leHByTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcXVlcnlSZXN1bHQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKGluc3RhbmNlQXJnLmV4cHJOYW1lLnRleHQpO1xuXHRcdFx0XHRpZiAocXVlcnlSZXN1bHQuc3RhdHVzID09PSAndW5pcXVlJykge1xuXHRcdFx0XHRcdC8vIHVuZGVmaW5lZCB3aGVuIHRoZSB0eXBlIGlzIG5ldmVyIGVtaXR0ZWQgKGNvbGxlY3Rpb25cblx0XHRcdFx0XHQvLyB3aXRob3V0IGEgcmVnaXN0cnkgaW50ZXJmYWNlKSDigJQgZGVncmFkZSwgbmV2ZXIgYmFyZVxuXHRcdFx0XHRcdGNvbnN0IGFsaWFzUmVzdWx0ID0gdGhpcy5nZXRFbWl0dGVkSW5zdGFuY2VUeXBlTmFtZShxdWVyeVJlc3VsdC5ub2RlKSA/PyAndW5rbm93bic7XG5cdFx0XHRcdFx0cmV0dXJuIGFsaWFzUmVzdWx0O1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChxdWVyeVJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHRcdFx0dGhpcy5yZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yKGluc3RhbmNlQXJnLmV4cHJOYW1lLnRleHQsIGluc3RhbmNlQXJnLCBxdWVyeVJlc3VsdCk7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgZGVncmFkZWRSZXN1bHQgPSAndW5rbm93bic7XG5cdFx0XHRcdHJldHVybiBkZWdyYWRlZFJlc3VsdDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGluZmVycmVkQXJnID0gdGhpcy5pbmZlclR5cGUoaW5zdGFuY2VBcmcpO1xuXHRcdFx0aWYgKGluZmVycmVkQXJnID09PSAndW5rbm93bicpIHtcblx0XHRcdFx0Y29uc3QgZGVncmFkZWRXcmFwcGVyID0gJ3Vua25vd24nO1xuXHRcdFx0XHRyZXR1cm4gZGVncmFkZWRXcmFwcGVyO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgd3JhcHBlZFJlc3VsdCA9IGBJbnN0YW5jZVR5cGU8JHtpbmZlcnJlZEFyZ30+YDtcblx0XHRcdHJldHVybiB3cmFwcGVkUmVzdWx0O1xuXHRcdH1cblxuXHRcdC8vIE1uZW1vbmljYS1ncmFwaCBpZGVudGl0eSBsYXc6IHBhdGgtYXdhcmUgcmVzb2x1dGlvbiAodmFsdWUgc2NvcGUsXG5cdFx0Ly8gaW1wb3J0cywgbmVhcmVzdC1jaGFpbiwgcm9vdCwgcHJvZ3JhbS13aWRlKS4gQW1iaWd1aXR5IGJldHdlZW5cblx0XHQvLyByZWFsIGdyYXBoIHR5cGVzIGlzIGEgaGFyZCBmYWlsdXJlOyBhIG5hbWUgbm8gZ3JhcGggdHlwZSBjYXJyaWVzXG5cdFx0Ly8gc3RheXMgaW4gdGhlIHBsYWluLVRTIHNvZnQgc2NvcGUgYW5kIGZhbGxzIHRvIGB1bmtub3duYC5cblx0XHRjb25zdCBncmFwaFJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUodHlwZU5hbWUpO1xuXHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHQvLyBIYW5kbGUgSW5zdGFuY2VUeXBlPHR5cGVvZiBYPiBwYXR0ZXJuIC0+IGNvbnZlcnQgdG8gUGFyZW50X1hcblx0XHRcdGlmICh0eXBlTmFtZSA9PT0gJ0luc3RhbmNlVHlwZScgJiYgdHlwZUFyZ3MgJiYgdHlwZUFyZ3MubGVuZ3RoID09PSAxKSB7XG5cdFx0XHRcdGNvbnN0IFsgYXJnIF0gPSB0eXBlQXJncztcblx0XHRcdFx0aWYgKGFyZy5raW5kID09PSB0cy5TeW50YXhLaW5kLlR5cGVRdWVyeSkge1xuXHRcdFx0XHRcdGNvbnN0IHR5cGVRdWVyeSA9IGFyZyBhcyB0cy5UeXBlUXVlcnlOb2RlO1xuXHRcdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIodHlwZVF1ZXJ5LmV4cHJOYW1lKSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcXVlcnlSZXN1bHQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKHR5cGVRdWVyeS5leHByTmFtZS50ZXh0KTtcblx0XHRcdFx0XHRcdGlmIChxdWVyeVJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRcdFx0XHRcdC8vIEVtaXR0ZWQgYWxpYXM6IFVzYWdlcy5Vc2FnZUVudHJ5IC0+IFVzYWdlc19Vc2FnZUVudHJ5XG5cdFx0XHRcdFx0XHRcdC8vIChPcHRpb24gQiBjb2xsZWN0aW9ucyBjYXJyeSB0aGUgcmVnaXN0cnkgcHJlZml4O1xuXHRcdFx0XHRcdFx0XHQvLyB1bmRlZmluZWQgd2hlbiBuZXZlciBlbWl0dGVkIOKAlCBkZWdyYWRlKVxuXHRcdFx0XHRcdFx0XHRjb25zdCBxdWVyeUFsaWFzID0gdGhpcy5nZXRFbWl0dGVkSW5zdGFuY2VUeXBlTmFtZShxdWVyeVJlc3VsdC5ub2RlKSA/PyAndW5rbm93bic7XG5cdFx0XHRcdFx0XHRcdHJldHVybiBxdWVyeUFsaWFzO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKHF1ZXJ5UmVzdWx0LnN0YXR1cyA9PT0gJ2FtYmlndW91cycpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5yZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yKHR5cGVRdWVyeS5leHByTmFtZS50ZXh0LCB0eXBlUXVlcnksIHF1ZXJ5UmVzdWx0KTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdC8vIE5vdCBhIGtub3duIG1uZW1vbmljYSB0eXBlIOKAlCBubyBiYXJlIGVtaXNzaW9uXG5cdFx0XHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKCF0eXBlQXJncyB8fCB0eXBlQXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdFx0Ly8gRW1pdHRlZCBhbGlhczogVXNhZ2VzLlVzYWdlRW50cnkgLT4gVXNhZ2VzX1VzYWdlRW50cnlcblx0XHRcdFx0Ly8gKE9wdGlvbiBCIGNvbGxlY3Rpb25zIGNhcnJ5IHRoZSByZWdpc3RyeSBwcmVmaXg7XG5cdFx0XHRcdC8vIHVuZGVmaW5lZCB3aGVuIG5ldmVyIGVtaXR0ZWQg4oCUIGRlZ3JhZGUpXG5cdFx0XHRcdGNvbnN0IGdyYXBoQWxpYXMgPSB0aGlzLmdldEVtaXR0ZWRJbnN0YW5jZVR5cGVOYW1lKGdyYXBoUmVzdWx0Lm5vZGUpID8/ICd1bmtub3duJztcblx0XHRcdFx0cmV0dXJuIGdyYXBoQWxpYXM7XG5cdFx0XHR9XG5cdFx0XHQvLyBHZW5lcmljIHVzZSBvZiBhIGdyYXBoIHR5cGUga2VlcHMgaXRzIHNpbXBsZSBuYW1lOyB0aGVcblx0XHRcdC8vIGdlbmVyYXRvciB1cGdyYWRlcyBpdCB0byB0aGUgZnVsbC1wYXRoIGluc3RhbmNlIHR5cGUgbmFtZVxuXHRcdFx0cmV0dXJuIGAke3R5cGVOYW1lfTwke3R5cGVBcmdzLm1hcChhID0+IHRoaXMuaW5mZXJUeXBlKGEpKS5qb2luKCcsICcpfT5gO1xuXHRcdH1cblx0XHRpZiAoZ3JhcGhSZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0dGhpcy5yZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yKHR5cGVOYW1lLCByZWZOb2RlID8/IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSwgZ3JhcGhSZXN1bHQpO1xuXHRcdH1cblxuXHRcdGlmICh0eXBlQXJncyAmJiB0eXBlQXJncy5sZW5ndGggPiAwKSB7XG5cdFx0XHRpZiAoS05PV05fR0xPQkFMX1RZUEVTLmhhcyh0eXBlTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgZ2VuZXJpY1Jlc3VsdCA9IGAke3R5cGVOYW1lfTwke3R5cGVBcmdzLm1hcChhID0+IHRoaXMuaW5mZXJUeXBlKGEpKS5qb2luKCcsICcpfT5gO1xuXHRcdFx0XHRyZXR1cm4gZ2VuZXJpY1Jlc3VsdDtcblx0XHRcdH1cblx0XHRcdC8vIEVtaXNzaW9uIHJlc3RvcmF0aW9uICgwLjIuMCBiZWhhdmlvcik6IGEgbm9uLWdyYXBoIG91dGVyXG5cdFx0XHQvLyBnZW5lcmljIHRoYXQgaXMgTk9UIGRlY2xhcmVkIGluIGFueSBhbmFseXplZCBwcm9qZWN0IGZpbGUgaXNcblx0XHRcdC8vIGFuIGFtYmllbnQvbGliIGNvbnN0cnVjdCAoTWFwSXRlcmF0b3IsIGxpYiBoZWxwZXJzKSDigJQgaXRcblx0XHRcdC8vIHJlc29sdmVzIGluIGV2ZXJ5IGNvbnN1bWVyIGNvbXBpbGF0aW9uIHdpdGhvdXQgYW4gaW1wb3J0LCBzb1xuXHRcdFx0Ly8gZW1pdCBpdCBWRVJCQVRJTSB3aXRoIGlubmVyIGdyYXBoIGFsaWFzZXMgcmVzb2x2ZWQuIEEgbmFtZVxuXHRcdFx0Ly8gZGVjbGFyZWQgaW4gcHJvamVjdCBmaWxlcyBzdGF5cyB1bmtub3duOiB0aGUgc2VsZi1jb250YWluZWRcblx0XHRcdC8vIHR5cGVzLnRzIGNhbiBjYXJyeSBuZWl0aGVyIHRoZSBiYXJlIG5hbWUgbm9yIGFuIGltcG9ydC5cblx0XHRcdGlmICghdGhpcy5pc1Byb2plY3REZWNsYXJlZFR5cGVOYW1lKHR5cGVOYW1lKSkge1xuXHRcdFx0XHRjb25zdCB2ZXJiYXRpbVJlc3VsdCA9IGAke3R5cGVOYW1lfTwke3R5cGVBcmdzLm1hcChhID0+IHRoaXMuaW5mZXJUeXBlKGEpKS5qb2luKCcsICcpfT5gO1xuXHRcdFx0XHRyZXR1cm4gdmVyYmF0aW1SZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBHZW5lcmljIHJlZmVyZW5jZSB0byBhIG5vbi1nbG9iYWwsIG5vbi1ncmFwaCBQUk9KRUNULUxPQ0FMXG5cdFx0XHQvLyB0eXBlIGNhbm5vdCBiZSBlbWl0dGVkIGJhcmUgaW50byB0aGUgZ2VuZXJhdGVkIGZpbGVcblx0XHRcdGlmIChyZWZOb2RlKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSh0eXBlTmFtZSwgcmVmTm9kZSk7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZhbGxiYWNrUmVzdWx0ID0gdGhpcy51bnJlc29sdmVkVHlwZVJlZmVyZW5jZUZhbGxiYWNrKHR5cGVOYW1lLCByZWZOb2RlKTtcblx0XHRyZXR1cm4gZmFsbGJhY2tSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHF1YWxpZmllZCB0eXBlIHJlZmVyZW5jZSAobW9kZWxzLklubmVyLkNyYXRlKSB0aHJvdWdoIHRoZVxuXHQgKiBjdXJyZW50IGZpbGUncyBuYW1lc3BhY2UgaW1wb3J0cy4gVGhlIGNoYWluJ3MgaGVhZCBtdXN0IGJlIGEgbmFtZXNwYWNlXG5cdCAqIGltcG9ydDsgbWlkZGxlIHNlZ21lbnRzIGRlc2NlbmQgdGhyb3VnaCBuYW1lc3BhY2UgZGVjbGFyYXRpb25zLCBuYW1lZFxuXHQgKiByZS1leHBvcnRzIG9mIG5hbWVzcGFjZXMsIGFuZCBgZXhwb3J0ICogYXMgbnMgZnJvbSAn4oCmJ2AgYmFycmVscyAoZWFjaFxuXHQgKiBzZWdtZW50IGNvbnN1bWVkIGV4YWN0bHkgb25jZSwgc28gdGhlIHdhbGsgY2Fubm90IGN5Y2xlKTsgdGhlIGZpbmFsXG5cdCAqIHNlZ21lbnQgcmVzb2x2ZXMgdG8gYSBkZWNsYXJhdGlvbiB3aGljaCBpcyBleHBhbmRlZCBpbmxpbmUuIFdoZW4gdGhlXG5cdCAqIHByZWNpc2Ugd2FsayBmaW5kcyBub3RoaW5nLCB0aGUgbGVnYWN5IHJpZ2h0bW9zdC1uYW1lIGxvb2t1cCBpbiB0aGVcblx0ICogaGVhZCBtb2R1bGUga2VlcHMgb25lLWxldmVsIGZvcm1zIChtb2RlbHMuVHlwZSkgd29ya2luZyDigJQgbmVzdGVkXG5cdCAqIGRlY2xhcmF0aW9ucyBhcmUgcmVjb3JkZWQgYnkgcGxhaW4gbmFtZSB0aGVyZSB0b28uIFJldHVybnMgdW5kZWZpbmVkXG5cdCAqIHdoZW4gdGhlIGhlYWQgaXMgbm90IGEgbmFtZXNwYWNlIGltcG9ydCBvciBub3RoaW5nIHJlc29sdmVzLlxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlclF1YWxpZmllZFR5cGVSZWZlcmVuY2UgKHR5cGVSZWY6IHRzLlR5cGVSZWZlcmVuY2VOb2RlKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIXRzLmlzUXVhbGlmaWVkTmFtZSh0eXBlUmVmLnR5cGVOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBmbGF0dGVuIHRoZSBxdWFsaWZpZWQgbmFtZSBjaGFpbjogbW9kZWxzLklubmVyLkNyYXRlIOKGkiBbJ21vZGVscycsICdJbm5lcicsICdDcmF0ZSddXG5cdFx0Y29uc3Qgc2VnbWVudHM6IHN0cmluZ1tdID0gW107XG5cdFx0bGV0IGNoYWluOiB0cy5FbnRpdHlOYW1lID0gdHlwZVJlZi50eXBlTmFtZTtcblx0XHR3aGlsZSAodHMuaXNRdWFsaWZpZWROYW1lKGNoYWluKSkge1xuXHRcdFx0c2VnbWVudHMudW5zaGlmdChjaGFpbi5yaWdodC50ZXh0KTtcblx0XHRcdGNoYWluID0gY2hhaW4ubGVmdDtcblx0XHR9XG5cdFx0c2VnbWVudHMudW5zaGlmdChjaGFpbi50ZXh0KTtcblxuXHRcdGNvbnN0IG5hbWVzcGFjZUltcG9ydCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQoc2VnbWVudHNbIDAgXSk7XG5cdFx0aWYgKCFuYW1lc3BhY2VJbXBvcnQgfHwgIW5hbWVzcGFjZUltcG9ydC5pc05hbWVzcGFjZSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUobmFtZXNwYWNlSW1wb3J0LnNwZWNpZmllciwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRpZiAoIXJlc29sdXRpb24gfHwgcmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIGRlc2NlbmQgdGhlIG1pZGRsZSBzZWdtZW50czogYSBtb2R1bGUgY29udGV4dCByZXNvbHZlcyB0aGUgc2VnbWVudFxuXHRcdC8vIGFzIGEgbmFtZXNwYWNlIGRlY2xhcmF0aW9uIC8gbmFtZXNwYWNlIHJlLWV4cG9ydDsgYSBuYW1lc3BhY2UtYmxvY2tcblx0XHQvLyBjb250ZXh0IHJlc29sdmVzIGl0IGFzIGEgbmVzdGVkIG5hbWVzcGFjZSBkZWNsYXJhdGlvblxuXHRcdGxldCBxdWFsaWZpZXI6IHsgbW9kdWxlUGF0aDogc3RyaW5nOyBibG9jaz86IHRzLk1vZHVsZUJsb2NrIH0gfCB1bmRlZmluZWQgPSB7XG5cdFx0XHRtb2R1bGVQYXRoIDogcmVzb2x1dGlvbi5yZXNvbHZlZFBhdGhcblx0XHR9O1xuXHRcdGZvciAobGV0IGkgPSAxOyBpIDwgc2VnbWVudHMubGVuZ3RoIC0gMSAmJiBxdWFsaWZpZXI7IGkrKykge1xuXHRcdFx0Y29uc3Qgc2VnbWVudCA9IHNlZ21lbnRzWyBpIF07XG5cdFx0XHRpZiAocXVhbGlmaWVyLmJsb2NrKSB7XG5cdFx0XHRcdGNvbnN0IG5lc3RlZCA9IHRoaXMuZmluZE5hbWVzcGFjZUluQmxvY2socXVhbGlmaWVyLmJsb2NrLCBzZWdtZW50KTtcblx0XHRcdFx0aWYgKG5lc3RlZD8uYm9keSAmJiB0cy5pc01vZHVsZUJsb2NrKG5lc3RlZC5ib2R5KSkge1xuXHRcdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IHF1YWxpZmllci5tb2R1bGVQYXRoLCBibG9jayA6IG5lc3RlZC5ib2R5IH07XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0cXVhbGlmaWVyID0gdW5kZWZpbmVkO1xuXHRcdFx0XHRicmVhaztcblx0XHRcdH1cblx0XHRcdGNvbnN0IG5hbWVzcGFjZURlY2w6IHRzLk1vZHVsZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkID1cblx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMuZ2V0KHF1YWxpZmllci5tb2R1bGVQYXRoKT8uZ2V0KHNlZ21lbnQpO1xuXHRcdFx0aWYgKG5hbWVzcGFjZURlY2w/LmJvZHkgJiYgdHMuaXNNb2R1bGVCbG9jayhuYW1lc3BhY2VEZWNsLmJvZHkpKSB7XG5cdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IHF1YWxpZmllci5tb2R1bGVQYXRoLCBibG9jayA6IG5hbWVzcGFjZURlY2wuYm9keSB9O1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHN0YXJTcGVjaWZpZXIgPSB0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlU3RhcnMuZ2V0KHF1YWxpZmllci5tb2R1bGVQYXRoKT8uZ2V0KHNlZ21lbnQpO1xuXHRcdFx0aWYgKHN0YXJTcGVjaWZpZXIpIHtcblx0XHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShzdGFyU3BlY2lmaWVyLCBxdWFsaWZpZXIubW9kdWxlUGF0aCk7XG5cdFx0XHRcdGlmIChuZXh0UmVzb2x1dGlvbiAmJiAhbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCB9O1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRjb25zdCByZUV4cG9ydFNwZWNpZmllciA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuZ2V0KHF1YWxpZmllci5tb2R1bGVQYXRoKT8uZ2V0KHNlZ21lbnQpO1xuXHRcdFx0aWYgKHJlRXhwb3J0U3BlY2lmaWVyKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUocmVFeHBvcnRTcGVjaWZpZXIsIHF1YWxpZmllci5tb2R1bGVQYXRoKTtcblx0XHRcdFx0Y29uc3QgcmVFeHBvcnRlZDogdHMuTW9kdWxlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQgPVxuXHRcdFx0XHRcdG5leHRSZXNvbHV0aW9uICYmICFuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsXG5cdFx0XHRcdFx0XHQ/IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzLmdldChuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgpPy5nZXQoc2VnbWVudClcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0XHRpZiAocmVFeHBvcnRlZD8uYm9keSAmJiB0cy5pc01vZHVsZUJsb2NrKHJlRXhwb3J0ZWQuYm9keSkpIHtcblx0XHRcdFx0XHRxdWFsaWZpZXIgPSB7IG1vZHVsZVBhdGggOiBuZXh0UmVzb2x1dGlvbiEucmVzb2x2ZWRQYXRoLCBibG9jayA6IHJlRXhwb3J0ZWQuYm9keSB9O1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRxdWFsaWZpZXIgPSB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmluYWxOYW1lID0gc2VnbWVudHNbIHNlZ21lbnRzLmxlbmd0aCAtIDEgXTtcblx0XHRsZXQgZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZDtcblx0XHRpZiAocXVhbGlmaWVyPy5ibG9jaykge1xuXHRcdFx0ZGVjbCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5CbG9jayhxdWFsaWZpZXIuYmxvY2ssIHF1YWxpZmllci5tb2R1bGVQYXRoLCBmaW5hbE5hbWUpO1xuXHRcdH0gZWxzZSBpZiAocXVhbGlmaWVyKSB7XG5cdFx0XHRkZWNsID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZShxdWFsaWZpZXIubW9kdWxlUGF0aCwgZmluYWxOYW1lLCAwKTtcblx0XHR9XG5cdFx0Ly8gbGVnYWN5IGZhbGxiYWNrOiByaWdodG1vc3QgbmFtZSBhbnl3aGVyZSBpbiB0aGUgaGVhZCBtb2R1bGVcblx0XHQvLyAobmFtZXNwYWNlLW5lc3RlZCBkZWNsYXJhdGlvbnMgYXJlIGFsc28gcmVjb3JkZWQgYnkgcGxhaW4gbmFtZSlcblx0XHRpZiAoIWRlY2wpIHtcblx0XHRcdGRlY2wgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKHJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBmaW5hbE5hbWUsIDApO1xuXHRcdH1cblx0XHRpZiAoIWRlY2wpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oZGVjbCk7XG5cdFx0cmV0dXJuIGV4cGFuZGVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpbmQgYSBuYW1lc3BhY2UgZGVjbGFyYXRpb24gYnkgbmFtZSBkaXJlY3RseSBpbnNpZGUgYSBtb2R1bGUgYmxvY2suXG5cdCAqL1xuXHRwcml2YXRlIGZpbmROYW1lc3BhY2VJbkJsb2NrIChibG9jazogdHMuTW9kdWxlQmxvY2ssIG5hbWU6IHN0cmluZyk6IHRzLk1vZHVsZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRmb3IgKGNvbnN0IHN0YXRlbWVudCBvZiBibG9jay5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAodHMuaXNNb2R1bGVEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmIHRzLmlzSWRlbnRpZmllcihzdGF0ZW1lbnQubmFtZSkgJiZcblx0XHRcdFx0c3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZSkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQgPSBzdGF0ZW1lbnQ7XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmluZCBhIG5hbWVkIHR5cGUgZGVjbGFyYXRpb24gKGFsaWFzLCBjbGFzcywgaW50ZXJmYWNlKSBkaXJlY3RseSBpbnNpZGVcblx0ICogYSBuYW1lc3BhY2UgYmxvY2sg4oCUIHRoZSBmaW5hbCBzZWdtZW50IG9mIGEgZGVzY2VuZGVkIHF1YWxpZmllZCBjaGFpbi5cblx0ICovXG5cdHByaXZhdGUgZmluZFJlZmVyZW5jZWRUeXBlSW5CbG9jayAoXG5cdFx0YmxvY2s6IHRzLk1vZHVsZUJsb2NrLFxuXHRcdGZpbGVQYXRoOiBzdHJpbmcsXG5cdFx0bmFtZTogc3RyaW5nXG5cdCk6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIGJsb2NrLnN0YXRlbWVudHMpIHtcblx0XHRcdGlmICh0cy5pc1R5cGVBbGlhc0RlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiYgdHMuaXNJZGVudGlmaWVyKHN0YXRlbWVudC5uYW1lKSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiA9IHsga2luZCA6ICdhbGlhcycsIG5vZGUgOiBzdGF0ZW1lbnQsIGZpbGUgOiBmaWxlUGF0aCB9O1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmIHN0YXRlbWVudC5uYW1lICYmIHN0YXRlbWVudC5uYW1lLnRleHQgPT09IG5hbWUpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0OiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uID0geyBraW5kIDogJ2NsYXNzJywgbm9kZSA6IHN0YXRlbWVudCwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNJbnRlcmZhY2VEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmIHRzLmlzSWRlbnRpZmllcihzdGF0ZW1lbnQubmFtZSkgJiZcblx0XHRcdFx0c3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZSkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQ6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gPSB7IGtpbmQgOiAnaW50ZXJmYWNlJywgbm9kZSA6IHN0YXRlbWVudCwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmFsbGJhY2sgZm9yIGEgdHlwZS1yZWZlcmVuY2UgbmFtZSB0aGF0IHJlc29sdmVzIHRvIG5vIGRlY2xhcmF0aW9uIGFuZFxuXHQgKiBubyBncmFwaCB0eXBlOiBrbm93biBnbG9iYWxzIGtlZXAgdGhlaXIgYmFyZSBuYW1lICh0aGV5IHJlc29sdmUgd2l0aG91dFxuXHQgKiBhbiBpbXBvcnQpOyBldmVyeXRoaW5nIGVsc2UgYmVjb21lcyBgdW5rbm93bmAgc28gZ2VuZXJhdGVkIHR5cGVzLnRzXG5cdCAqIG5ldmVyIGNhcnJpZXMgYW4gdW5yZXNvbHZhYmxlIGJhcmUgbmFtZSAoUkVBRE1FJ3MgZG9jdW1lbnRlZCBiZWhhdmlvcilcblx0ICogYW5kIHRoZSBzaXRlIGlzIHJlY29yZGVkIGZvciB0aGUgcGxhaW4tVFMgYW1iaWd1aXR5IHZhbGlkYXRpb24uXG5cdCAqL1xuXHRwcml2YXRlIHVucmVzb2x2ZWRUeXBlUmVmZXJlbmNlRmFsbGJhY2sgKHR5cGVOYW1lOiBzdHJpbmcsIHJlZk5vZGU/OiB0cy5Ob2RlKTogc3RyaW5nIHtcblx0XHRpZiAoS05PV05fR0xPQkFMX1RZUEVTLmhhcyh0eXBlTmFtZSkpIHtcblx0XHRcdHJldHVybiB0eXBlTmFtZTtcblx0XHR9XG5cdFx0aWYgKHJlZk5vZGUpIHtcblx0XHRcdHRoaXMucmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSh0eXBlTmFtZSwgcmVmTm9kZSk7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9ICd1bmtub3duJztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBvbmUgZGVmaW5lKCkvbGF6eSgpL0BkZWNvcmF0ZSgpIHNpdGUgdW5kZXIgaXRzIHJ1bnRpbWVcblx0ICogbmFtZXNwYWNlIGtleS4gVHdvIHNpdGVzIGluIG9uZSBuYW1lc3BhY2UgYXJlIGEgc2FtZS1uYW1lc3BhY2Vcblx0ICogZHVwbGljYXRlICh0aGUgcnVudGltZSB0aHJvd3MgQUxSRUFEWV9ERUNMQVJFRCk7IGV2ZXJ5IHNpdGUgaXMga2VwdFxuXHQgKiBzbyB0aGUgZmFpbHVyZSBjYW4gcmVwb3J0IGFsbCBsb2NhdGlvbnMuXG5cdCAqL1xuXHRwcml2YXRlIHJlY29yZERlZmluZVNpdGUgKG5hbWVzcGFjZUtleTogc3RyaW5nLCBsb2NhdGlvbjogc3RyaW5nKTogdm9pZCB7XG5cdFx0bGV0IHNpdGVzID0gdGhpcy5kZWZpbmVTaXRlcy5nZXQobmFtZXNwYWNlS2V5KTtcblx0XHRpZiAoIXNpdGVzKSB7XG5cdFx0XHRzaXRlcyA9IFtdO1xuXHRcdFx0dGhpcy5kZWZpbmVTaXRlcy5zZXQobmFtZXNwYWNlS2V5LCBzaXRlcyk7XG5cdFx0fVxuXHRcdGlmICghc2l0ZXMuaW5jbHVkZXMobG9jYXRpb24pKSB7XG5cdFx0XHRzaXRlcy5wdXNoKGxvY2F0aW9uKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRmF0YWwgcmVzb2x1dGlvbiBmYWlsdXJlcyAoaGFyZC1mYWlsIGxhdyk6IHNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZVxuXHQgKiBtbmVtb25pY2EgZGVmaW5pdGlvbnMgcGx1cyBhbWJpZ3VvdXMvdW5yZXNvbHZlZCBtbmVtb25pY2EtZ3JhcGhcblx0ICogcmVmZXJlbmNlcy4gVGhlIENMSSBwcmludHMgZXZlcnkgbG9jYXRpb24gYW5kIHdyaXRlcyBubyBvdXRwdXQuXG5cdCAqL1xuXHRnZXRSZXNvbHV0aW9uRXJyb3JzICgpOiBSZXNvbHV0aW9uRXJyb3JbXSB7XG5cdFx0dGhpcy52YWxpZGF0ZUxvb2t1cFJlZmVyZW5jZXMoKTtcblx0XHR0aGlzLnZhbGlkYXRlUGxhaW5UeXBlUmVmZXJlbmNlcygpO1xuXHRcdGNvbnN0IGVycm9yczogUmVzb2x1dGlvbkVycm9yW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IFsgbmFtZXNwYWNlS2V5LCBzaXRlcyBdIG9mIHRoaXMuZGVmaW5lU2l0ZXMpIHtcblx0XHRcdGlmIChzaXRlcy5sZW5ndGggPCAyKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZGlzcGxheU5hbWUgPSBuYW1lc3BhY2VLZXkucmVwbGFjZSgvXlteOl0rOjovLCAnJyk7XG5cdFx0XHRjb25zdCBtZXNzYWdlID0gYER1cGxpY2F0ZSBkZWZpbml0aW9uIG9mICcke2Rpc3BsYXlOYW1lfScgaW4gb25lIG5hbWVzcGFjZSDigJQgYCArXG5cdFx0XHRcdCd0aGUgbW5lbW9uaWNhIHJ1bnRpbWUgd291bGQgdGhyb3cgQUxSRUFEWV9ERUNMQVJFRCc7XG5cdFx0XHRlcnJvcnMucHVzaCh7IG1lc3NhZ2UsIGxvY2F0aW9ucyA6IFsgLi4uc2l0ZXMgXSB9KTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBlcnJvciBvZiB0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzKSB7XG5cdFx0XHRlcnJvcnMucHVzaChlcnJvcik7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGVycm9ycztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSByZWZlcmVuY2UgdG8gYSBtbmVtb25pY2EgZ3JhcGggdHlwZSBuYW1lLCBpbXBvcnQtYXdhcmUgYW5kXG5cdCAqIHBhdGgtYXdhcmUgKHRoZSBoYXJkLWZhaWwgaWRlbnRpdHkgbGF3LCBtaXJyb3JpbmcgdGhlIHJ1bnRpbWUpOlxuXHQgKiAgIDEuIHZhbHVlIHNjb3BlIOKAlCBhIHRyYWNrZWQgdG9wLWxldmVsIGJpbmRpbmcgaW4gdGhlIHJlZmVyZW5jaW5nIGZpbGVcblx0ICogICAgICAoYGNvbnN0IEFkZHJlc3MgPSBVc2VyLmRlZmluZSgnQWRkcmVzcycsIOKApilgKSxcblx0ICogICAyLiBpbXBvcnQgc2NvcGUg4oCUIGEgYmluZGluZyBleHBvcnRlZCBmcm9tIGEgbW9kdWxlIHRoaXMgZmlsZSBpbXBvcnRzXG5cdCAqICAgICAgKGJhcnJlbHMgY2hhc2VkKSxcblx0ICogICAzLiBuZWFyZXN0LWNoYWluIOKAlCB0aGUgYW5jaG9yIHR5cGUncyBvd24gc3VidHlwZXMgZmlyc3QsIHRoZW4gZWFjaFxuXHQgKiAgICAgIGFuY2VzdG9yIGxldmVsIChyZWxhdGl2ZS1maXJzdCksXG5cdCAqICAgNC4gcm9vdCDigJQgcm9vdHMgb2YgdGhlIGFuY2hvcidzIGNvbGxlY3Rpb24sXG5cdCAqICAgNS4gcHJvZ3JhbS13aWRlIOKAlCBvbmx5IHdoZW4gZXhhY3RseSBvbmUgdHlwZSBjYXJyaWVzIHRoZSBuYW1lLlxuXHQgKiBBbWJpZ3VpdHkgKHNldmVyYWwgY2FuZGlkYXRlcyBhbmQgbm90aGluZyBkaXNhbWJpZ3VhdGVzKSBhbmQgYWJzZW5jZVxuXHQgKiBhcmUgYm90aCByZXR1cm5lZCBhcyBzdWNoIOKAlCB0aGUgY2FsbGVyIHJlY29yZHMgYSBoYXJkIGZhaWx1cmU7IGEgYmFyZVxuXHQgKiBmaXJzdC1tYXRjaCBuYW1lIGlzIG5ldmVyIGVtaXR0ZWQuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVHcmFwaFR5cGVOYW1lIChuYW1lOiBzdHJpbmcpOiBHcmFwaFR5cGVSZWZlcmVuY2VSZXN1bHQge1xuXHRcdC8vIDEuIHZhbHVlIHNjb3BlIGluIHRoZSByZWZlcmVuY2luZyBmaWxlIGl0c2VsZlxuXHRcdGNvbnN0IGxvY2FsQmluZGluZyA9IHRoaXMuZmlsZUdyYXBoQmluZGluZ3MuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWxCaW5kaW5nKSB7XG5cdFx0XHRjb25zdCBub2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShsb2NhbEJpbmRpbmcpO1xuXHRcdFx0aWYgKG5vZGUpIHtcblx0XHRcdFx0Y29uc3QgdmFsdWVSZXN1bHQ6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCA9IHsgc3RhdHVzIDogJ3VuaXF1ZScsIG5vZGUgfTtcblx0XHRcdFx0cmV0dXJuIHZhbHVlUmVzdWx0O1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIDIuIGltcG9ydCBzY29wZSDigJQgdGhlIGltcG9ydGVkIG1vZHVsZSdzIGV4cG9ydGVkIGJpbmRpbmdcblx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGltcG9ydGVkICYmICFpbXBvcnRlZC5pc05hbWVzcGFjZSkge1xuXHRcdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKGltcG9ydGVkLnNwZWNpZmllciwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdGlmIChyZXNvbHV0aW9uICYmICFyZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0Y29uc3QgZnVsbFBhdGggPSB0aGlzLmZpbmRHcmFwaEJpbmRpbmdJbk1vZHVsZShyZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgaW1wb3J0ZWQub3JpZ2luYWxOYW1lLCAwKTtcblx0XHRcdFx0aWYgKGZ1bGxQYXRoKSB7XG5cdFx0XHRcdFx0Y29uc3Qgbm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoZnVsbFBhdGgpO1xuXHRcdFx0XHRcdGlmIChub2RlKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBpbXBvcnRSZXN1bHQ6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCA9IHsgc3RhdHVzIDogJ3VuaXF1ZScsIG5vZGUgfTtcblx0XHRcdFx0XHRcdHJldHVybiBpbXBvcnRSZXN1bHQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gMy01LiBjaGFpbiAvIHJvb3QgLyBwcm9ncmFtLXdpZGUgdGllcnNcblx0XHRjb25zdCByZXN1bHQgPSByZXNvbHZlR3JhcGhUeXBlUmVmZXJlbmNlKHRoaXMuZ3JhcGgsIG5hbWUsIHRoaXMuY3VycmVudEdyYXBoQW5jaG9yKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpbmQgYSBncmFwaCBjb25zdHJ1Y3RvciBiaW5kaW5nIGV4cG9ydGVkIGJ5IGEgcmVzb2x2ZWQgbW9kdWxlLFxuXHQgKiBjaGFzaW5nIHJlLWV4cG9ydCBiYXJyZWxzIHdpdGggYSBib3VuZGVkIGRlcHRoLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kR3JhcGhCaW5kaW5nSW5Nb2R1bGUgKG1vZHVsZVBhdGg6IHN0cmluZywgbmFtZTogc3RyaW5nLCBkZXB0aDogbnVtYmVyKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoZGVwdGggPiBNQVhfUkVFWFBPUlRfQ0hBU0VfREVQVEgpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGlyZWN0ID0gdGhpcy5maWxlR3JhcGhCaW5kaW5ncy5nZXQobW9kdWxlUGF0aCk/LmdldChuYW1lKTtcblx0XHRpZiAoZGlyZWN0KSB7XG5cdFx0XHRyZXR1cm4gZGlyZWN0O1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlRXhwb3J0cyA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGNvbnN0IHJlRXhwb3J0U3BlY2lmaWVyID0gcmVFeHBvcnRzPy5nZXQobmFtZSk7XG5cdFx0aWYgKHJlRXhwb3J0U3BlY2lmaWVyKSB7XG5cdFx0XHRjb25zdCBuZXh0UmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKHJlRXhwb3J0U3BlY2lmaWVyLCBtb2R1bGVQYXRoKTtcblx0XHRcdGlmIChuZXh0UmVzb2x1dGlvbiAmJiAhbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRjb25zdCBmb3VuZCA9IHRoaXMuZmluZEdyYXBoQmluZGluZ0luTW9kdWxlKG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgbmFtZSwgZGVwdGggKyAxKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGlmIChzdGFycykge1xuXHRcdFx0Zm9yIChjb25zdCBzdGFyU3BlY2lmaWVyIG9mIHN0YXJzKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoc3RhclNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRcdGlmICghbmV4dFJlc29sdXRpb24gfHwgbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kR3JhcGhCaW5kaW5nSW5Nb2R1bGUobmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBuYW1lLCBkZXB0aCArIDEpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFZhbGlkYXRlIGxpdGVyYWwgbG9va3VwKCkgcGF0aHMgcmVjb3JkZWQgZHVyaW5nIHRoZSB1c2FnZXMgcGFzc1xuXHQgKiBhZ2FpbnN0IHRoZSBjb21wbGV0ZSBncmFwaC4gQSBsb29rdXAgcGF0aCBtYXRjaGluZyBubyB0eXBlIGlzIHdoYXQgdGhlXG5cdCAqIHJ1bnRpbWUgYW5zd2VycyB3aXRoIGB1bmRlZmluZWRgIOKAlCB0aGUgVHlwZUVycm9yIGFycml2ZXMgb25lIGxpbmVcblx0ICogbGF0ZXIgYXQgdGhlIGBuZXdgIOKAlCBzbyBpdCBqb2lucyB0aGUgaGFyZC1mYWlsIGxhdy4gVGhlIHJlbGF0aXZlLWZpcnN0XG5cdCAqIHN0ZXAgYWxyZWFkeSByYW4gaW5zaWRlIHJlc29sdmVMb29rdXBQYXRoOyB3aGF0ZXZlciB3YXMgcmVjb3JkZWQgaXNcblx0ICogdGhlIHJvb3QtcmVzb2x1dGlvbiByZXN1bHQsIHNvIGEgcGxhaW4gZmluZFR5cGUgY2hlY2sgaXMgdGhlIGV4YWN0XG5cdCAqIHJ1bnRpbWUgbGF3LiBTYW1lLW5hbWVkIHR5cGVzIGVsc2V3aGVyZSBpbiB0aGUgZ3JhcGggYXJlIGxpc3RlZCBhc1xuXHQgKiBkaWQteW91LW1lYW4gY2FuZGlkYXRlcy4gUnVucyBvbmNlIHBlciB1c2FnZXMgcGFzcyAocmUtYXJtZWQgYnlcblx0ICogcmVzZXRVc2FnZXMpOyBub24tbGl0ZXJhbCBsb29rdXAgYXJndW1lbnRzIGFyZSBuZXZlciByZWNvcmRlZCBhbmRcblx0ICogc3RheSBiZXN0LWVmZm9ydC5cblx0ICovXG5cdHByaXZhdGUgdmFsaWRhdGVMb29rdXBSZWZlcmVuY2VzICgpOiB2b2lkIHtcblx0XHRpZiAodGhpcy5sb29rdXBSZWZlcmVuY2VzVmFsaWRhdGVkKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHRoaXMubG9va3VwUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IHRydWU7XG5cdFx0Ly8gZ3JvdXAgc2l0ZXMgYnkgcGF0aDogZXZlcnkgZmFpbGluZyBzaXRlIG9mIHRoZSBzYW1lIHBhdGggaXMgbGlzdGVkXG5cdFx0Y29uc3Qgc2l0ZXNCeVBhdGggPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nW10+KCk7XG5cdFx0Zm9yIChjb25zdCByZWYgb2YgdGhpcy5sb29rdXBSZWZlcmVuY2VzKSB7XG5cdFx0XHRjb25zdCBzaXRlcyA9IHNpdGVzQnlQYXRoLmdldChyZWYucGF0aCkgPz8gW107XG5cdFx0XHRzaXRlcy5wdXNoKHJlZi5sb2NhdGlvbik7XG5cdFx0XHRzaXRlc0J5UGF0aC5zZXQocmVmLnBhdGgsIHNpdGVzKTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBbIHR5cGVQYXRoLCBzaXRlcyBdIG9mIHNpdGVzQnlQYXRoKSB7XG5cdFx0XHRpZiAodGhpcy5ncmFwaC5maW5kVHlwZSh0eXBlUGF0aCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHQvLyBkaWQteW91LW1lYW46IHR5cGVzIGNhcnJ5aW5nIHRoZSBzYW1lIG5hbWUgYW55d2hlcmUgaW4gdGhlXG5cdFx0XHQvLyBncmFwaCAobmV2ZXIgYSBmaXJzdC1tYXRjaCBwaWNrIOKAlCB0aGUgZnVsbCBsaXN0IG9ubHkpXG5cdFx0XHRjb25zdCB1bnByZWZpeGVkID0gdHlwZVBhdGgucmVwbGFjZSgvXlteOl0rOjovLCAnJyk7XG5cdFx0XHRjb25zdCBsYXN0U2VnbWVudCA9IHVucHJlZml4ZWQuc3BsaXQoJy4nKS5wb3AoKSA/PyB1bnByZWZpeGVkO1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlcyA9IHRoaXMuZ3JhcGguZ2V0QWxsVHlwZXMoKS5maWx0ZXIodCA9PiB0Lm5hbWUgPT09IGxhc3RTZWdtZW50KTtcblx0XHRcdGlmIChjYW5kaWRhdGVzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHRjb25zdCBub25lRXJyb3I6IFJlc29sdXRpb25FcnJvciA9IHtcblx0XHRcdFx0XHRtZXNzYWdlIDogYFVucmVzb2x2ZWQgbG9va3VwIG9mIG1uZW1vbmljYSB0eXBlICcke3R5cGVQYXRofSc6IG5vIHR5cGUgYXQgdGhhdCBwYXRoIOKAlCBgICtcblx0XHRcdFx0XHRcdCd0aGUgcnVudGltZSB3b3VsZCByZXR1cm4gdW5kZWZpbmVkJyxcblx0XHRcdFx0XHRsb2NhdGlvbnMgOiBzaXRlcyxcblx0XHRcdFx0fTtcblx0XHRcdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKG5vbmVFcnJvcik7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgY2FuZGlkYXRlTG9jYXRpb25zID0gY2FuZGlkYXRlcy5tYXAobiA9PiBgJHtuLnNvdXJjZUZpbGV9OiR7bi5saW5lfToke24uY29sdW1ufWApO1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlUGF0aHMgPSBjYW5kaWRhdGVzLm1hcChuID0+IG4uZnVsbFBhdGgpLmpvaW4oJywgJyk7XG5cdFx0XHRjb25zdCBhbWJpZ3VvdXNFcnJvcjogUmVzb2x1dGlvbkVycm9yID0ge1xuXHRcdFx0XHRtZXNzYWdlIDogYFVucmVzb2x2ZWQgbG9va3VwIG9mIG1uZW1vbmljYSB0eXBlICcke3R5cGVQYXRofSc6IHRoZSBydW50aW1lIHdvdWxkIHJldHVybiBgICtcblx0XHRcdFx0XHRgdW5kZWZpbmVkIOKAlCAke2NhbmRpZGF0ZXMubGVuZ3RofSBncmFwaCB0eXBlKHMpIGNhcnJ5IHRoZSBuYW1lIGAgK1xuXHRcdFx0XHRcdGBvZmYtcm9vdCAoJHtjYW5kaWRhdGVQYXRoc30pOyB1c2UgdGhlIGZ1bGwgZG90dGVkIHBhdGhgLFxuXHRcdFx0XHRsb2NhdGlvbnMgOiBbIC4uLnNpdGVzLCAuLi5jYW5kaWRhdGVMb2NhdGlvbnMgXSxcblx0XHRcdH07XG5cdFx0XHR0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzLnB1c2goYW1iaWd1b3VzRXJyb3IpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgYSBwbGFpbi1UUyB0eXBlIHJlZmVyZW5jZSBzaXRlIHRoYXQgcmVzb2x2ZWQgdG8gbm90aGluZyBhbmRcblx0ICogZmVsbCBiYWNrIHRvIGB1bmtub3duYCwgZm9yIHRoZSBsYXppbHktcnVuIGFtYmlndWl0eSB2YWxpZGF0aW9uLlxuXHQgKiBEZWR1cGVkIGJ5IChuYW1lLCBsb2NhdGlvbik6IGluZmVyVHlwZSBjYW4gdmlzaXQgdGhlIHNhbWUgbm9kZSBtb3JlXG5cdCAqIHRoYW4gb25jZSBwZXIgcGFzcyAoY29uc3RydWN0b3IgcGFyYW1zICsgcHJvcGVydHkgaW5mZXJlbmNlKS5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSAobmFtZTogc3RyaW5nLCByZWZOb2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSB0aGlzLm5vZGVMb2NhdGlvbihyZWZOb2RlKTtcblx0XHRjb25zdCBmaWxlID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGNvbnN0IGFscmVhZHkgPSB0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXMuc29tZSgocmVmKSA9PiByZWYubmFtZSA9PT0gbmFtZSAmJiByZWYubG9jYXRpb24gPT09IGxvY2F0aW9uKTtcblx0XHRpZiAoYWxyZWFkeSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXMucHVzaCh7IG5hbWUsIGxvY2F0aW9uLCBmaWxlIH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb2plY3Qtc291cmNlIGRlY2xhcmF0aW9uIGZpbGVzIGNhcnJ5aW5nIGBuYW1lYCDigJQgb25lIGVudHJ5IHBlclxuXHQgKiBmaWxlLCBzbyBzYW1lLWZpbGUgaW50ZXJmYWNlIG1lcmdpbmcgY291bnRzIG9uY2UgKG5vdCBhbWJpZ3VvdXMpLlxuXHQgKiBFeHRlcm5hbC9hbWJpZW50IGRlY2xhcmF0aW9ucyAoLmQudHMsIGFueXRoaW5nIHVuZGVyIG5vZGVfbW9kdWxlcylcblx0ICogbmV2ZXIgY291bnQ6IGEgdXNlci1sb2NhbCBkZWNsYXJhdGlvbiBhbHdheXMgd2lucyBvdmVyIGEgcGFja2FnZS1cblx0ICogZGVjbGFyZWQgc2FtZS1uYW1lZCB0eXBlLCBzbyBhbiBleHRlcm5hbCBjb2xsaXNpb24gc3RheXMgc29mdC5cblx0ICovXG5cdHByaXZhdGUgcGxhaW5UeXBlRGVjbGFyYXRpb25GaWxlcyAobmFtZTogc3RyaW5nKTogc3RyaW5nW10ge1xuXHRcdGNvbnN0IGZpbGVzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgWyBmaWxlLCBkZWNscyBdIG9mIHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscykge1xuXHRcdFx0aWYgKCF0aGlzLmlzRXh0ZXJuYWxEZWNsRmlsZShmaWxlKSAmJiBkZWNscy5oYXMobmFtZSkpIHtcblx0XHRcdFx0ZmlsZXMucHVzaChmaWxlKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIGZpbGVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIFZhbGlkYXRlIHBsYWluLVRTIHR5cGUgcmVmZXJlbmNlIHNpdGVzIHJlY29yZGVkIGR1cmluZyB0aGUgdXNhZ2VzXG5cdCAqIHBhc3MgYWdhaW5zdCB0aGUgY29tcGxldGUgZGVjbGFyYXRpb24gbWFwLiBBIG5hbWUgZGVjbGFyZWQgaW5cblx0ICogc2V2ZXJhbCBwcm9qZWN0LXNvdXJjZSBmaWxlcyDigJQgd2l0aCBubyBpbXBvcnQgaW4gdGhlIHJlZmVyZW5jaW5nXG5cdCAqIGZpbGUgdG8gYW5jaG9yIGl0IOKAlCBpcyBhbWJpZ3VvdXM6IHNpbGVudGx5IGVtaXR0aW5nIGB1bmtub3duYCB3b3VsZFxuXHQgKiBoaWRlIGEgcmVhbCB0eXBlIHRoZSBhdXRob3IgbWVhbnQsIHNvIGl0IGpvaW5zIHRoZSBoYXJkLWZhaWwgbGF3XG5cdCAqICh0aGUgcGxhaW4tVFMgdGllciBvZiB0aGUgc2FtZSBpZGVudGl0eSBsYXcgYXMgZ3JhcGggcmVmZXJlbmNlcykuXG5cdCAqIEFic2VuY2UgKGdob3N0IG5hbWVzKSBhbmQgZXh0ZXJuYWwgY29sbGlzaW9ucyBzdGF5IHNvZnQgYHVua25vd25gLlxuXHQgKiBSdW5zIG9uY2UgcGVyIHVzYWdlcyBwYXNzIChyZS1hcm1lZCBieSByZXNldFVzYWdlcyksIG1pcnJvcmluZ1xuXHQgKiB2YWxpZGF0ZUxvb2t1cFJlZmVyZW5jZXM6IHJlY29yZGluZyBoYXBwZW5zIG9uIGV2ZXJ5IHBhc3MsIGJ1dCBvbmx5XG5cdCAqIHRoZSB1c2FnZXMgcGFzcyBzZWVzIHRoZSBjb21wbGV0ZSBkZWNsYXJhdGlvbiBtYXAuXG5cdCAqL1xuXHRwcml2YXRlIHZhbGlkYXRlUGxhaW5UeXBlUmVmZXJlbmNlcyAoKTogdm9pZCB7XG5cdFx0aWYgKHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXNWYWxpZGF0ZWQgPSB0cnVlO1xuXHRcdGNvbnN0IHNpdGVzQnlOYW1lID0gbmV3IE1hcDxzdHJpbmcsIHsgbmFtZTogc3RyaW5nOyBsb2NhdGlvbjogc3RyaW5nOyBmaWxlOiBzdHJpbmcgfVtdPigpO1xuXHRcdGZvciAoY29uc3QgcmVmIG9mIHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlcykge1xuXHRcdFx0Y29uc3Qgc2l0ZXMgPSBzaXRlc0J5TmFtZS5nZXQocmVmLm5hbWUpID8/IFtdO1xuXHRcdFx0c2l0ZXMucHVzaChyZWYpO1xuXHRcdFx0c2l0ZXNCeU5hbWUuc2V0KHJlZi5uYW1lLCBzaXRlcyk7XG5cdFx0fVxuXHRcdGZvciAoY29uc3QgWyBuYW1lLCBzaXRlcyBdIG9mIHNpdGVzQnlOYW1lKSB7XG5cdFx0XHQvLyBhbiBpbXBvcnQgYmluZGluZyBpbiB0aGUgcmVmZXJlbmNpbmcgZmlsZSBhbmNob3JzIHRoZSBuYW1lIOKAlFxuXHRcdFx0Ly8gdGhlIGF1dGhvciBhbHJlYWR5IGRpc2FtYmlndWF0ZWQgKHRoZSBpbXBvcnQgbWF5IGp1c3QgcG9pbnRcblx0XHRcdC8vIGF0IGFuIHVuYW5hbHl6YWJsZSBleHRlcm5hbCBtb2R1bGUsIHdoaWNoIHN0YXlzIHNvZnQpXG5cdFx0XHRjb25zdCB1bmFuY2hvcmVkID0gc2l0ZXMuZmlsdGVyKChzaXRlKSA9PiAhdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KHNpdGUuZmlsZSk/LmhhcyhuYW1lKSk7XG5cdFx0XHRpZiAodW5hbmNob3JlZC5sZW5ndGggPT09IDApIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBkZWNsRmlsZXMgPSB0aGlzLnBsYWluVHlwZURlY2xhcmF0aW9uRmlsZXMobmFtZSk7XG5cdFx0XHRpZiAoZGVjbEZpbGVzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBtZXNzYWdlID0gYEFtYmlndW91cyByZWZlcmVuY2UgdG8gdHlwZSAnJHtuYW1lfSc6ICR7ZGVjbEZpbGVzLmxlbmd0aH0gZGVjbGFyYXRpb25zIGAgK1xuXHRcdFx0XHQnc2hhcmUgdGhlIG5hbWUgYW5kIG5vIGltcG9ydCBkaXNhbWJpZ3VhdGVzIOKAlCBpbXBvcnQgdGhlIG9uZSB5b3UgbWVhbic7XG5cdFx0XHRjb25zdCBkZWNsTG9jYXRpb25zID0gZGVjbEZpbGVzLm1hcCgoZmlsZSkgPT4gdGhpcy5wbGFpbkRlY2xMb2NhdGlvbihmaWxlLCBuYW1lKSk7XG5cdFx0XHRjb25zdCBlcnJvcjogUmVzb2x1dGlvbkVycm9yID0ge1xuXHRcdFx0XHRtZXNzYWdlLFxuXHRcdFx0XHRsb2NhdGlvbnMgOiBbIC4uLnVuYW5jaG9yZWQubWFwKChzaXRlKSA9PiBzaXRlLmxvY2F0aW9uKSwgLi4uZGVjbExvY2F0aW9ucyBdXG5cdFx0XHR9O1xuXHRcdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKGVycm9yKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogYGZpbGU6bGluZTpjb2x1bW5gIG9mIGEgcmVjb3JkZWQgZGVjbGFyYXRpb24sIGZvciB0aGUgYW1iaWd1aXR5XG5cdCAqIHJlcG9ydC4gTm9kZXMgcmVjb3JkZWQgZHVyaW5nIHRyYXZlcnNhbCBrZWVwIHRoZWlyIHBvc2l0aW9uczsgYVxuXHQgKiBzeW50aGV0aWMvdW5wb3NpdGlvbmVkIG5vZGUgZmFsbHMgYmFjayB0byB0aGUgZmlsZSBpdHNlbGYuXG5cdCAqL1xuXHRwcml2YXRlIHBsYWluRGVjbExvY2F0aW9uIChmaWxlOiBzdHJpbmcsIG5hbWU6IHN0cmluZyk6IHN0cmluZyB7XG5cdFx0Y29uc3QgZGVjbCA9IHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscy5nZXQoZmlsZSk/LmdldChuYW1lKTtcblx0XHRjb25zdCBub2RlID0gZGVjbD8ubm9kZTtcblx0XHRsZXQgbG9jYXRpb24gPSBgJHtmaWxlfToxOjFgO1xuXHRcdGlmIChub2RlICYmIG5vZGUucG9zID49IDApIHtcblx0XHRcdGNvbnN0IHNvdXJjZUZpbGUgPSBub2RlLmdldFNvdXJjZUZpbGUoKTtcblx0XHRcdGNvbnN0IGxpbmUgPSBzb3VyY2VGaWxlLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKG5vZGUuZ2V0U3RhcnQoKSkubGluZSArIDE7XG5cdFx0XHRjb25zdCBjb2x1bW4gPSBzb3VyY2VGaWxlLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKG5vZGUuZ2V0U3RhcnQoKSkuY2hhcmFjdGVyICsgMTtcblx0XHRcdGxvY2F0aW9uID0gYCR7ZmlsZX06JHtsaW5lfToke2NvbHVtbn1gO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBsb2NhdGlvbjtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhIGhhcmQtZmFpbCBncmFwaCByZWZlcmVuY2UgZXJyb3Igd2l0aCB0aGUgcmVmZXJlbmNlIHNpdGUgYW5kXG5cdCAqIGV2ZXJ5IGNhbmRpZGF0ZSBsb2NhdGlvbi5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkR3JhcGhSZWZlcmVuY2VFcnJvciAoXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdHJlZk5vZGU6IHRzLk5vZGUgfCBzdHJpbmcsXG5cdFx0cmVzdWx0OiBFeHRyYWN0PEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCwgeyBzdGF0dXM6ICdhbWJpZ3VvdXMnIHwgJ25vbmUnIH0+XG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gdHlwZW9mIHJlZk5vZGUgPT09ICdzdHJpbmcnID8gcmVmTm9kZSA6IHRoaXMubm9kZUxvY2F0aW9uKHJlZk5vZGUpO1xuXHRcdGlmIChyZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlTG9jYXRpb25zID0gcmVzdWx0LmNhbmRpZGF0ZXMubWFwKG4gPT4gYCR7bi5zb3VyY2VGaWxlfToke24ubGluZX06JHtuLmNvbHVtbn1gKTtcblx0XHRcdGNvbnN0IGFtYmlndW91c01lc3NhZ2UgPSBgQW1iaWd1b3VzIHJlZmVyZW5jZSB0byBtbmVtb25pY2EgdHlwZSAnJHtuYW1lfSc6IGAgK1xuXHRcdFx0XHRgJHtyZXN1bHQuY2FuZGlkYXRlcy5sZW5ndGh9IHR5cGVzIHNoYXJlIHRoZSBuYW1lIGFuZCBuZWl0aGVyIHRoZSBwYXJlbnQgY2hhaW4gYCArXG5cdFx0XHRcdCdub3IgdGhlIGltcG9ydHMgZGlzYW1iaWd1YXRlJztcblx0XHRcdGNvbnN0IGFtYmlndW91c0Vycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7XG5cdFx0XHRcdG1lc3NhZ2UgICA6IGFtYmlndW91c01lc3NhZ2UsXG5cdFx0XHRcdGxvY2F0aW9ucyA6IFsgbG9jYXRpb24sIC4uLmNhbmRpZGF0ZUxvY2F0aW9ucyBdLFxuXHRcdFx0fTtcblx0XHRcdHRoaXMuZ3JhcGhSZWZlcmVuY2VFcnJvcnMucHVzaChhbWJpZ3VvdXNFcnJvcik7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHVucmVzb2x2ZWRNZXNzYWdlID0gYFVucmVzb2x2ZWQgcmVmZXJlbmNlIHRvIG1uZW1vbmljYSB0eXBlICcke25hbWV9Jzogbm8gdHlwZSBtYXRjaGVzIGAgK1xuXHRcdFx0J2J5IHZhbHVlIHNjb3BlLCBpbXBvcnRzLCBwYXJlbnQgY2hhaW4sIG9yIHJvb3QgcGF0aCc7XG5cdFx0Y29uc3QgdW5yZXNvbHZlZEVycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7IG1lc3NhZ2UgOiB1bnJlc29sdmVkTWVzc2FnZSwgbG9jYXRpb25zIDogWyBsb2NhdGlvbiBdIH07XG5cdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKHVucmVzb2x2ZWRFcnJvcik7XG5cdH1cblxuXHQvKipcblx0ICogTG9jYXRpb24gKGBmaWxlOmxpbmU6Y29sdW1uYCkgb2YgYW4gQVNUIG5vZGUsIGRlcml2ZWQgd2l0aG91dCBwYXJlbnRcblx0ICogcG9pbnRlcnMgd2hlbiBuZWNlc3NhcnkuXG5cdCAqL1xuXHRwcml2YXRlIG5vZGVMb2NhdGlvbiAobm9kZTogdHMuTm9kZSk6IHN0cmluZyB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBub2RlO1xuXHRcdHdoaWxlIChjdXJyZW50ICYmICF0cy5pc1NvdXJjZUZpbGUoY3VycmVudCkpIHtcblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0aWYgKCFjdXJyZW50KSB7XG5cdFx0XHRjb25zdCBmYWxsYmFjayA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRcdHJldHVybiBmYWxsYmFjaztcblx0XHR9XG5cdFx0Y29uc3Qgc3RhcnQgPSBub2RlLmdldFN0YXJ0KGN1cnJlbnQpO1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihjdXJyZW50LCBzdGFydCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtjdXJyZW50LmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRyZXR1cm4gbG9jYXRpb247XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgYWxpYXNlcyBvZiB0aGUgbW5lbW9uaWNhIG1vZHVsZSBvYmplY3QsIGUuZy46XG5cdCAqICAgY29uc3QgbSA9IG1uZW1vbmljYTtcblx0ICogICBjb25zdCBBcHAgPSBtO1xuXHQgKi9cblx0cHJpdmF0ZSB0cmFja01vZHVsZU9iamVjdEFsaWFzZXMgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSB8fCAhdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGluaXRpYWxpemVyIH0gPSBub2RlO1xuXHRcdGlmICghaW5pdGlhbGl6ZXIpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGluaXRpYWxpemVyKSAmJiB0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoaW5pdGlhbGl6ZXIudGV4dCkpIHtcblx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChub2RlLm5hbWUudGV4dCk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFRyYWNrIGN1c3RvbSBjb2xsZWN0aW9uIHZhcmlhYmxlcywgZS5nLjpcblx0ICogICBjb25zdCBNeUNvbGxlY3Rpb24gPSBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKTtcblx0ICogICBjb25zdCBPdGhlciA9IE15Q29sbGVjdGlvbjtcblx0ICpcblx0ICogQWxzbyBkZXRlY3RzIE9wdGlvbiBCIHVzZXItcHJvdmlkZWQgcmVnaXN0cnkgaW50ZXJmYWNlczpcblx0ICogICBleHBvcnQgaW50ZXJmYWNlIE15Q29sbGVjdGlvblJlZ2lzdHJ5IHt9XG5cdCAqICAgY29uc3QgTXlDb2xsZWN0aW9uID0gY3JlYXRlVHlwZXNDb2xsZWN0aW9uPE15Q29sbGVjdGlvblJlZ2lzdHJ5PigpO1xuXHQgKi9cblx0cHJpdmF0ZSB0cmFja0NvbGxlY3Rpb25BbGlhc2VzIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgfHwgIXRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBpbml0aWFsaXplciB9ID0gbm9kZTtcblx0XHRpZiAoIWluaXRpYWxpemVyKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRGlyZWN0IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIGNhbGxcblx0XHRpZiAodGhpcy5pc0NyZWF0ZVR5cGVzQ29sbGVjdGlvbkNhbGwoaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHQvLyBUaGUgQ0xJIHJlLWFuYWx5emVzIGV2ZXJ5IGZpbGUgb24gdGhlIHVzYWdlcyBwYXNzIChzZWUgcmVzZXRVc2FnZXMpOlxuXHRcdFx0Ly8gbWludGluZyBhIGZyZXNoIGlkIGhlcmUgd291bGQgcmUtcmVnaXN0ZXIgdGhlIGNvbGxlY3Rpb24ncyB0eXBlc1xuXHRcdFx0Ly8gdW5kZXIgYSBzZWNvbmQgYGNvbGxlY3Rpb25JZDo6YCBwcmVmaXggYW5kIGR1cGxpY2F0ZSBldmVyeSBlbWlzc2lvbi5cblx0XHRcdGNvbnN0IGNvbGxlY3Rpb25JZCA9IHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5nZXQobm9kZS5uYW1lLnRleHQpID8/IHRoaXMubmV4dENvbGxlY3Rpb25JZCgpO1xuXHRcdFx0dGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLnNldChub2RlLm5hbWUudGV4dCwgY29sbGVjdGlvbklkKTtcblxuXHRcdFx0Y29uc3QgcmVnaXN0cnlJbnRlcmZhY2VOYW1lID0gdGhpcy5leHRyYWN0UmVnaXN0cnlJbnRlcmZhY2VOYW1lKFxuXHRcdFx0XHRpbml0aWFsaXplciBhcyB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHRcdFx0c291cmNlRmlsZVxuXHRcdFx0KTtcblx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihzb3VyY2VGaWxlLCBub2RlLmdldFN0YXJ0KCkpO1xuXHRcdFx0dGhpcy5jb2xsZWN0aW9uSW5mby5zZXQoY29sbGVjdGlvbklkLCB7XG5cdFx0XHRcdHZhcmlhYmxlTmFtZSAgICAgICAgICA6IG5vZGUubmFtZS50ZXh0LFxuXHRcdFx0XHRzb3VyY2VGaWxlICAgICAgICAgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRyZWdpc3RyeUludGVyZmFjZU5hbWUgOiByZWdpc3RyeUludGVyZmFjZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgICAgICAgICAgICAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gICAgICAgICAgICAgICAgOiBjaGFyYWN0ZXIgKyAxXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBBbGlhcyBvZiBhbm90aGVyIGNvbGxlY3Rpb24gdmFyaWFibGVcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGluaXRpYWxpemVyKSkge1xuXHRcdFx0Y29uc3QgZXhpc3RpbmcgPSB0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuZ2V0KGluaXRpYWxpemVyLnRleHQpO1xuXHRcdFx0aWYgKGV4aXN0aW5nKSB7XG5cdFx0XHRcdHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5zZXQobm9kZS5uYW1lLnRleHQsIGV4aXN0aW5nKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0aGUgcmVnaXN0cnkgaW50ZXJmYWNlIG5hbWUgZnJvbSBjcmVhdGVUeXBlc0NvbGxlY3Rpb248UmVnaXN0cnk+KClcblx0ICogd2hlbiB0aGUgaW50ZXJmYWNlIGlzIGRlY2xhcmVkIGluIHRoZSBzYW1lIHNvdXJjZSBmaWxlLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UmVnaXN0cnlJbnRlcmZhY2VOYW1lIChcblx0XHRjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlXG5cdCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgdHlwZUFyZ3MgPSBjYWxsLnR5cGVBcmd1bWVudHM7XG5cdFx0aWYgKCF0eXBlQXJncyB8fCB0eXBlQXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgWyBmaXJzdFR5cGVBcmcgXSA9IHR5cGVBcmdzO1xuXHRcdGlmICghdHMuaXNUeXBlUmVmZXJlbmNlTm9kZShmaXJzdFR5cGVBcmcpIHx8ICF0cy5pc0lkZW50aWZpZXIoZmlyc3RUeXBlQXJnLnR5cGVOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBuYW1lID0gZmlyc3RUeXBlQXJnLnR5cGVOYW1lLnRleHQ7XG5cblx0XHQvLyBDb25maXJtIHRoZSBpbnRlcmZhY2UgZXhpc3RzIGluIHRoZSBzYW1lIHNvdXJjZSBmaWxlLlxuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIHNvdXJjZUZpbGUuc3RhdGVtZW50cykge1xuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc0ludGVyZmFjZURlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiZcblx0XHRcdFx0c3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZVxuXHRcdFx0KSB7XG5cdFx0XHRcdHJldHVybiBuYW1lO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogU3RhbXAgYSBub2RlIHdpdGggaXRzIGNvbGxlY3Rpb24ncyBlbWlzc2lvbiBpbmZvOiB0aGUgT3B0aW9uIEIgcmVnaXN0cnlcblx0ICogaW50ZXJmYWNlIG5hbWUgYW5kIHRoZSBjb2xsZWN0aW9uJ3MgaG9tZSBmaWxlIOKAlCB0aGUgbW9kdWxlIHRoZSBnZW5lcmF0ZWRcblx0ICogYXVnbWVudGF0aW9uIG11c3QgdGFyZ2V0ICh0aGUgaW50ZXJmYWNlIGlzIGNvbmZpcm1lZCBkZWNsYXJlZCB0aGVyZSkuXG5cdCAqIEEgdHlwZSdzIG93biBzb3VyY2VGaWxlIGlzIE5PVCB0aGUgdGFyZ2V0OiBtdWx0aS1maWxlIGNvbGxlY3Rpb25zIGRlZmluZVxuXHQgKiB0eXBlcyBhY3Jvc3MgbWFueSBtb2R1bGVzIHdoaWxlIHRoZSBpbnRlcmZhY2UgbGl2ZXMgYXQgdGhlXG5cdCAqIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIGNhbGwgc2l0ZS5cblx0ICovXG5cdHByaXZhdGUgYXBwbHlDb2xsZWN0aW9uRW1pc3Npb25JbmZvIChub2RlOiBUeXBlTm9kZSwgY29sbGVjdGlvbklkPzogc3RyaW5nKTogdm9pZCB7XG5cdFx0aWYgKCFjb2xsZWN0aW9uSWQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgaW5mbyA9IHRoaXMuY29sbGVjdGlvbkluZm8uZ2V0KGNvbGxlY3Rpb25JZCk7XG5cdFx0aWYgKCFpbmZvKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdG5vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lID0gaW5mby5yZWdpc3RyeUludGVyZmFjZU5hbWU7XG5cdFx0bm9kZS5jb2xsZWN0aW9uU291cmNlRmlsZSA9IGluZm8uc291cmNlRmlsZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhbiBleHByZXNzaW9uIGlzIGEgY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgY2FsbC5cblx0ICogSGFuZGxlczpcblx0ICogICBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKVxuXHQgKiAgIGN0YygpIC8vIGFsaWFzZWQgaW1wb3J0XG5cdCAqICAgbW5lbW9uaWNhLmNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIC8vIG1vZHVsZSBvYmplY3QgbWV0aG9kXG5cdCAqICAgbS5jcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSAvLyBhbGlhc2VkIG1vZHVsZSBvYmplY3Rcblx0ICovXG5cdHByaXZhdGUgaXNDcmVhdGVUeXBlc0NvbGxlY3Rpb25DYWxsIChub2RlOiB0cy5Ob2RlKTogbm9kZSBpcyB0cy5DYWxsRXhwcmVzc2lvbiB7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXHRcdGNvbnN0IGV4cHIgPSBub2RlLmV4cHJlc3Npb247XG5cblx0XHQvLyBEaXJlY3QgY2FsbCBvciBhbGlhc2VkIGltcG9ydDogY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgLyBjdGMoKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLnRleHQgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nIHx8XG5cdFx0XHRcdHRoaXMuY3JlYXRlVHlwZXNDb2xsZWN0aW9uVmFyaWFibGVzLmhhcyhleHByLnRleHQpO1xuXHRcdH1cblxuXHRcdC8vIE1vZHVsZSBvYmplY3QgbWV0aG9kOiBtbmVtb25pY2EuY3JlYXRlVHlwZXNDb2xsZWN0aW9uKClcblx0XHRpZiAoXG5cdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSAmJlxuXHRcdFx0ZXhwci5uYW1lLnRleHQgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIoZXhwci5leHByZXNzaW9uKSAmJlxuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuaGFzKGV4cHIuZXhwcmVzc2lvbi50ZXh0KVxuXHRcdCkge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdlbmVyYXRlIGEgdW5pcXVlIGNvbGxlY3Rpb24gaWRlbnRpZmllci5cblx0ICovXG5cdHByaXZhdGUgbmV4dENvbGxlY3Rpb25JZCAoKTogc3RyaW5nIHtcblx0XHR0aGlzLmNvbGxlY3Rpb25Db3VudGVyKys7XG5cdFx0Y29uc3QgcmVzdWx0ID0gYGNvbGxlY3Rpb25fJHt0aGlzLmNvbGxlY3Rpb25Db3VudGVyfWA7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhIG5vZGUgaXMgYSBkZWZpbmUoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGlzRGVmaW5lQ2FsbCAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuQ2FsbEV4cHJlc3Npb24ge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBkaXJlY3QgY2FsbDogZGVmaW5lKCdUeXBlTmFtZScsIC4uLilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2RlZmluZScpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBtZXRob2QgY2FsbDogU29tZVR5cGUuZGVmaW5lKCdTdWJUeXBlJywgLi4uKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuIGV4cHJlc3Npb24ubmFtZT8udGV4dCA9PT0gJ2RlZmluZSc7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGEgbm9kZSBpcyBhIGxhenkoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGlzTGF6eUNhbGwgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkNhbGxFeHByZXNzaW9uIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IG5vZGU7XG5cblx0XHQvLyBDaGVjayBmb3IgZGlyZWN0IGNhbGw6IGxhenkoJ1R5cGVOYW1lJywgZ2V0dGVyLCAuLi4pXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLnRleHQgPT09ICdsYXp5Jykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIG1ldGhvZCBjYWxsOiBTb21lVHlwZS5sYXp5KCdTdWJUeXBlJywgZ2V0dGVyLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gZXhwcmVzc2lvbi5uYW1lPy50ZXh0ID09PSAnbGF6eSc7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IGNvbmZpZyBvcHRpb25zIGZyb20gYW4gb2JqZWN0IGxpdGVyYWxcblx0XHQqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbCAoY29uZmlnQXJnOiB0cy5PYmplY3RMaXRlcmFsRXhwcmVzc2lvbik6XG5cdFx0eyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9IHtcblx0XHRjb25zdCBjb25maWc6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSA9IHt9O1xuXG5cdFx0Zm9yIChjb25zdCBwcm9wIG9mIGNvbmZpZ0FyZy5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFzc2lnbm1lbnQocHJvcCkgJiYgdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBwcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0aWYgKHByb3BOYW1lID09PSAnc3RyaWN0Q2hhaW4nICYmIHByb3AuaW5pdGlhbGl6ZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5zdHJpY3RDaGFpbiA9IHRydWU7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdzdHJpY3RDaGFpbicgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5zdHJpY3RDaGFpbiA9IGZhbHNlO1xuXHRcdFx0XHR9IGVsc2UgaWYgKHByb3BOYW1lID09PSAnYmxvY2tFcnJvcnMnICYmIHByb3AuaW5pdGlhbGl6ZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5ibG9ja0Vycm9ycyA9IHRydWU7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdibG9ja0Vycm9ycycgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5ibG9ja0Vycm9ycyA9IGZhbHNlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGNvbmZpZztcblx0fVxuXG5cdC8qKlxuXHRcdCogRXh0cmFjdCBjb25maWcgb3B0aW9ucyBmcm9tIGRlZmluZSgpIGNhbGxcblx0XHQqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25maWcgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogeyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9IHtcblx0XHQvLyBDb25maWcgaXMgdGhlIHRoaXJkIGFyZ3VtZW50OiBkZWZpbmUoJ05hbWUnLCBoYW5kbGVyLCBjb25maWcpXG5cdFx0Y29uc3QgWyAsICwgY29uZmlnQXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblx0XHRpZiAoIWNvbmZpZ0FyZyB8fCAhdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihjb25maWdBcmcpKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgY29uZmlnUmVzdWx0ID0gdGhpcy5leHRyYWN0Q29uZmlnRnJvbU9iamVjdExpdGVyYWwoY29uZmlnQXJnKTtcblx0XHRyZXR1cm4gY29uZmlnUmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0KiBDaGVjayBpZiBhIG5vZGUgaXMgYSBAZGVjb3JhdGUoKSBkZWNvcmF0b3Jcblx0XHQqL1xuXHRwcml2YXRlIGlzRGVjb3JhdGVEZWNvcmF0b3IgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkRlY29yYXRvciB7XG5cdFx0aWYgKCF0cy5pc0RlY29yYXRvcihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBAZGVjb3JhdGVcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2RlY29yYXRlJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIEBkZWNvcmF0ZSgpIG9yIEBkZWNvcmF0ZShQYXJlbnRUeXBlKVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRjb25zdCBmbk5hbWUgPSBleHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGZuTmFtZSkgJiYgZm5OYW1lLnRleHQgPT09ICdkZWNvcmF0ZScpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cblx0XHRcdC8vIENoZWNrIGZvciBATXlDb2xsZWN0aW9uLmRlY29yYXRlKCkgd2hlcmUgTXlDb2xsZWN0aW9uIGlzIGEgY3VzdG9tIGNvbGxlY3Rpb25cblx0XHRcdGlmIChcblx0XHRcdFx0dHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZm5OYW1lKSAmJlxuXHRcdFx0XHRmbk5hbWUubmFtZS50ZXh0ID09PSAnZGVjb3JhdGUnICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihmbk5hbWUuZXhwcmVzc2lvbikgJiZcblx0XHRcdFx0dGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmhhcyhmbk5hbWUuZXhwcmVzc2lvbi50ZXh0KVxuXHRcdFx0KSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBNYXJrIGEgY2FsbCBleHByZXNzaW9uIGFzIHByb2Nlc3NlZCBhbmQgcmV0dXJuIHdoZXRoZXIgaXQgYWxyZWFkeSB3YXMuXG5cdCAqL1xuXHRwcml2YXRlIG1hcmtQcm9jZXNzZWQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogYm9vbGVhbiB7XG5cdFx0aWYgKHRoaXMucHJvY2Vzc2VkQ2FsbHMuaGFzKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cdFx0dGhpcy5wcm9jZXNzZWRDYWxscy5hZGQoY2FsbCk7XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb2Nlc3MgYSBkZWZpbmUoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NEZWZpbmVDYWxsIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGlmIHRoaXMgZXhhY3QgY2FsbCBoYXMgYWxyZWFkeSBiZWVuIHByb2Nlc3NlZCAocHJldmVudHMgZHVwbGljYXRlcyBmcm9tIGNoYWluZWQgY2FsbHMpXG5cdFx0aWYgKHRoaXMubWFya1Byb2Nlc3NlZChjYWxsKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IGNvbXB1dGVkTmFtZXMgPSB0aGlzLmV4dHJhY3RDb21wdXRlZFR5cGVOYW1lcyhjYWxsKTtcblx0XHRpZiAoY29tcHV0ZWROYW1lcyAhPT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRmb3IgKGNvbnN0IHR5cGVOYW1lIG9mIGNvbXB1dGVkTmFtZXMpIHtcblx0XHRcdFx0Y29uc3QgY29tcHV0ZWRDb250ZXh0ID0gdGhpcy5leHRyYWN0RGVmaW5lQ29udGV4dChjYWxsLCB0eXBlTmFtZSk7XG5cdFx0XHRcdHRoaXMucHJvY2Vzc0RlZmluZUNvbnRleHQoY2FsbCwgc291cmNlRmlsZSwgY29tcHV0ZWRDb250ZXh0LCB0cnVlKTtcblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBHZXQgdGhlIHR5cGUgbmFtZSBhbmQgc291cmNlIGNvbnRleHQgZnJvbSBhcmd1bWVudHNcblx0XHRjb25zdCBkZWZpbmVDb250ZXh0ID0gdGhpcy5leHRyYWN0RGVmaW5lQ29udGV4dChjYWxsKTtcblx0XHR0aGlzLnByb2Nlc3NEZWZpbmVDb250ZXh0KGNhbGwsIHNvdXJjZUZpbGUsIGRlZmluZUNvbnRleHQsIGZhbHNlKTtcblx0fVxuXG5cdHByaXZhdGUgcHJvY2Vzc0RlZmluZUNvbnRleHQgKFxuXHRcdGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0ZGVmaW5lQ29udGV4dDoge1xuXHRcdFx0dHlwZU5hbWU/OiBzdHJpbmc7XG5cdFx0XHRwYXJlbnRUeXBlPzogVHlwZU5vZGU7XG5cdFx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmc7XG5cdFx0fSxcblx0XHRtZXRhZGF0YU9ubHk6IGJvb2xlYW5cblx0KTogdm9pZCB7XG5cdFx0Ly8gRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBkZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKSwgd2Ugd2FudCB0aGUgcG9zaXRpb24gb2YgdGhlIC5kZWZpbmUoJ0InKSBwYXJ0XG5cdFx0Ly8gbm90IHRoZSBzdGFydCBvZiB0aGUgZW50aXJlIGV4cHJlc3Npb25cblx0XHRsZXQgcG9zaXRpb25Ob2RlOiB0cy5Ob2RlID0gY2FsbDtcblxuXHRcdC8vIElmIHRoaXMgaXMgYSBjaGFpbmVkIGNhbGwsIGdldCB0aGUgcG9zaXRpb24gb2YgdGhlIHByb3BlcnR5IGFjY2VzcyBleHByZXNzaW9uXG5cdFx0Ly8gd2hpY2ggaXMgdGhlIC5kZWZpbmUgcGFydFxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHQvLyBUaGUgZXhwcmVzc2lvbiBpcyB0aGUgcHJvcGVydHkgYWNjZXNzOiAoZGVmaW5lKCdSb290QXN5bmMnLCAuLi4pKS5kZWZpbmVcblx0XHRcdC8vIFdlIHdhbnQgdGhlIHBvc2l0aW9uIG9mIGp1c3QgdGhlIC5kZWZpbmUgcGFydFxuXHRcdFx0Ly8gVGhpcyBpcyB0aGUgJ2RlZmluZScgaWRlbnRpZmllclxuXHRcdFx0cG9zaXRpb25Ob2RlID0gY2FsbC5leHByZXNzaW9uLm5hbWU7XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnRQb3MgPSBwb3NpdGlvbk5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSk7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKHNvdXJjZUZpbGUsIHN0YXJ0UG9zKTtcblxuXHRcdGlmICghZGVmaW5lQ29udGV4dC50eXBlTmFtZSkge1xuXHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdG1lc3NhZ2UgOiAnQ291bGQgbm90IGV4dHJhY3QgdHlwZSBuYW1lIGZyb20gZGVmaW5lKCkgY2FsbCcsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyB0eXBlTmFtZSB9ID0gZGVmaW5lQ29udGV4dDtcblxuXHRcdC8vIERldGVybWluZSBwYXJlbnQgdHlwZSBhbmQgY29sbGVjdGlvbiBiYXNlZCBvbiB0aGUgY2FsbCBzb3VyY2UuXG5cdFx0Y29uc3QgcGFyZW50Tm9kZSA9IGRlZmluZUNvbnRleHQucGFyZW50VHlwZTtcblx0XHRjb25zdCB7IGNvbGxlY3Rpb25JZCB9ID0gZGVmaW5lQ29udGV4dDtcblxuXHRcdC8vIEV4dHJhY3QgY29uZmlnIG9wdGlvbnNcblx0XHRjb25zdCBjb25maWcgPSB0aGlzLmV4dHJhY3RDb25maWcoY2FsbCk7XG5cblx0XHQvLyBDcmVhdGUgdHlwZSBub2RlIGZpcnN0IHNvIGl0cyBpbnRlcm5hbCBmdWxsUGF0aCAoaW5jbHVkaW5nIGFueSBjb2xsZWN0aW9uIHByZWZpeCkgaXMgcmVzb2x2ZWQuXG5cdFx0Y29uc3Qgbm9kZSA9IFR5cGVHcmFwaEltcGwuY3JlYXRlTm9kZShcblx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0cGFyZW50Tm9kZSxcblx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRsaW5lICsgMSxcblx0XHRcdGNoYXJhY3RlciArIDEsXG5cdFx0XHRjb2xsZWN0aW9uSWRcblx0XHQpO1xuXHRcdHRoaXMuYXBwbHlDb2xsZWN0aW9uRW1pc3Npb25JbmZvKG5vZGUsIGNvbGxlY3Rpb25JZCk7XG5cdFx0bm9kZS5tZXRhZGF0YU9ubHkgPSBtZXRhZGF0YU9ubHk7XG5cblx0XHQvLyBTYW1lLW5hbWVzcGFjZSBkdXBsaWNhdGUgZGV0ZWN0aW9uIChoYXJkLWZhaWwgbGF3KToga2V5IGJ5IHRoZVxuXHRcdC8vIHJ1bnRpbWUgbmFtZXNwYWNlIOKAlCBjb2xsZWN0aW9uIHJvb3RzIGA8Y29sbGVjdGlvbj46OjxuYW1lPmAsIG9yXG5cdFx0Ly8gYDxwYXJlbnRGdWxsUGF0aD4uPG5hbWU+YCBmb3Igc3VidHlwZXNcblx0XHR0aGlzLnJlY29yZERlZmluZVNpdGUoXG5cdFx0XHRwYXJlbnROb2RlID8gYCR7cGFyZW50Tm9kZS5mdWxsUGF0aH0uJHt0eXBlTmFtZX1gIDogYCR7Y29sbGVjdGlvbklkID8/ICdkZWZhdWx0J306OiR7dHlwZU5hbWV9YCxcblx0XHRcdGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gXG5cdFx0KTtcblxuXHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGNvbnN0cnVjdG9yIGZ1bmN0aW9uIOKAlCB0aGUgbmV3IG5vZGUgYW5jaG9yc1xuXHRcdC8vIHJlbGF0aXZlLWZpcnN0IGdyYXBoIHJlZmVyZW5jZSByZXNvbHV0aW9uIHdoaWxlIGl0cyBvd24gc2lnbmF0dXJlXG5cdFx0Ly8gaXMgYmVpbmcgcmVhZFxuXHRcdGNvbnN0IHByZXZpb3VzQW5jaG9yID0gdGhpcy5jdXJyZW50R3JhcGhBbmNob3I7XG5cdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBub2RlO1xuXHRcdHRyeSB7XG5cdFx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzKGNhbGwpO1xuXG5cdFx0XHQvLyBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZm9yIFR5cGVSZWdpc3RyeSBzaWduYXR1cmVcblx0XHRcdG5vZGUuY29uc3RydWN0b3JQYXJhbXMgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyhjYWxsKTtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBwcmV2aW91c0FuY2hvcjtcblx0XHR9XG5cblx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCk7XG5cdFx0bm9kZS5pbnN0YW5jZVR5cGVPdmVycmlkZSA9IHRoaXMuaGFzQW55VGhpc0Fubm90YXRpb24oY29uc3RydWN0b3JFeHByKSA/ICdhbnknIDogdW5kZWZpbmVkO1xuXHRcdC8vIEFzeW5jIGNvbnN0cnVjdG9yIGRldGVjdGlvbiAoYXN5bmMgbW9kaWZpZXIsIHN5bnRhY3RpYyBvbmx5KVxuXHRcdG5vZGUuaXNBc3luYyA9IHRoaXMuaXNBc3luY0NvbnN0cnVjdEhhbmRsZXIodGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpKTtcblxuXHRcdC8vIEFkZCB0byBncmFwaFxuXHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZENoaWxkKHBhcmVudE5vZGUsIG5vZGUpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZFJvb3Qobm9kZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ3JlYXRlIGRlZmluaXRpb24gaW5mbyB1c2luZyB0aGUgbm9kZSdzIHJlc29sdmVkIGZ1bGxQYXRoXG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IHR5cGVOYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlZmluZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IHBhcmVudE5vZGUgPyBwYXJlbnROb2RlLmZ1bGxQYXRoIDogbnVsbCxcblx0XHRcdHN0cmljdENoYWluIDogY29uZmlnLnN0cmljdENoYWluID8/IHRydWUsXG5cdFx0XHRibG9ja0Vycm9ycyA6IGNvbmZpZy5ibG9ja0Vycm9ycyA/PyBmYWxzZSxcblx0XHR9O1xuXHRcdHRoaXMuZGVmaW5pdGlvbnMuc2V0KG5vZGUuZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXHRcdGlmICghbWV0YWRhdGFPbmx5KSB7XG5cdFx0XHR0aGlzLmVkc1Njb3BlQnlOb2RlLnNldChjYWxsLCBub2RlLmZ1bGxQYXRoKTtcblxuXHRcdFx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudDogY29uc3QgVXNlciA9IGRlZmluZSgnVXNlckVudGl0eScsIC4uLikgLT4gbWFwIFwiVXNlclwiIHRvIFwiVXNlckVudGl0eVwiXG5cdFx0XHQvLyBBIG11bHRpLWhvcCBpbml0aWFsaXplciBiaW5kcyB0aGUgTEFTVCBob3A6IGRlZmluZSgpIHJldHVybnMgdGhlXG5cdFx0XHQvLyBkZWZpbmVkIHR5cGUncyBjb25zdHJ1Y3RvciAoRjE4KVxuXHRcdFx0dGhpcy50cmFja1ZhcmlhYmxlQXNzaWdubWVudChjYWxsLCBwYXJlbnROb2RlLCBub2RlLmZ1bGxQYXRoLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUHJvY2VzcyBhIGxhenkoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NMYXp5Q2FsbCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHQvLyBDaGVjayBpZiB0aGlzIGV4YWN0IGNhbGwgaGFzIGFscmVhZHkgYmVlbiBwcm9jZXNzZWQgKHByZXZlbnRzIGR1cGxpY2F0ZXMgZnJvbSBjaGFpbmVkIGNhbGxzKVxuXHRcdGlmICh0aGlzLm1hcmtQcm9jZXNzZWQoY2FsbCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBHZXQgdGhlIHR5cGUgbmFtZSBhbmQgc291cmNlIGNvbnRleHQgZnJvbSBhcmd1bWVudHNcblx0XHRjb25zdCBsYXp5Q29udGV4dCA9IHRoaXMuZXh0cmFjdExhenlDb250ZXh0KGNhbGwsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBkZWZpbmUoJ0EnKS5sYXp5KCdCJyksIHdlIHdhbnQgdGhlIHBvc2l0aW9uIG9mIHRoZSAubGF6eSgnQicpIHBhcnRcblx0XHQvLyBub3QgdGhlIHN0YXJ0IG9mIHRoZSBlbnRpcmUgZXhwcmVzc2lvblxuXHRcdGxldCBwb3NpdGlvbk5vZGU6IHRzLk5vZGUgPSBjYWxsO1xuXG5cdFx0Ly8gSWYgdGhpcyBpcyBhIGNoYWluZWQgY2FsbCwgZ2V0IHRoZSBwb3NpdGlvbiBvZiB0aGUgcHJvcGVydHkgYWNjZXNzIGV4cHJlc3Npb25cblx0XHQvLyB3aGljaCBpcyB0aGUgLmxhenkgcGFydFxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHQvLyBUaGUgZXhwcmVzc2lvbiBpcyB0aGUgcHJvcGVydHkgYWNjZXNzOiAoZGVmaW5lKCdSb290QXN5bmMnLCAuLi4pKS5sYXp5XG5cdFx0XHQvLyBXZSB3YW50IHRoZSBwb3NpdGlvbiBvZiBqdXN0IHRoZSAubGF6eSBwYXJ0XG5cdFx0XHQvLyBUaGlzIGlzIHRoZSAnbGF6eScgaWRlbnRpZmllclxuXHRcdFx0cG9zaXRpb25Ob2RlID0gY2FsbC5leHByZXNzaW9uLm5hbWU7XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnRQb3MgPSBwb3NpdGlvbk5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSk7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKHNvdXJjZUZpbGUsIHN0YXJ0UG9zKTtcblxuXHRcdC8vIFRoZSB1bm5hbWVkIGZvcm1zIOKAlCBsYXp5KGdldHRlciksIFR5cGUubGF6eShnZXR0ZXIsIGNvbmZpZz8pLFxuXHRcdC8vIGxhenkoc291cmNlLCBnZXR0ZXIsIGNvbmZpZz8pIOKAlCB0aHJvdyBUWVBFTkFNRV9NVVNUX0JFX0FfU1RSSU5HIGF0XG5cdFx0Ly8gcnVudGltZSAodGhlIG5hbWUgaXMgcmVxdWlyZWQpLCBzbyBnZW5lcmF0aW5nIGEgdHlwZSBmcm9tIHRoZVxuXHRcdC8vIGdldHRlcidzIGNvbnN0cnVjdG9yIG5hbWUgd291bGQgYmxlc3MgY29kZSB0aGF0IGNyYXNoZXMuIFRoZXkgYXJlXG5cdFx0Ly8gYW4gYW5hbHl6ZXIgZXJyb3IgbmFtaW5nIHRoZSBjYWxsIHNpdGUgYW5kIHRoZSByZXF1aXJlZCBmb3JtLlxuXHRcdGNvbnN0IGxhenlBcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdGlmIChsYXp5QXJncyAmJiBsYXp5QXJncy5uYW1lID09PSB1bmRlZmluZWQpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ2xhenkoKSByZXF1aXJlcyBhIHR5cGUgbmFtZTogbGF6eShcXCdOYW1lXFwnLCBnZXR0ZXIpJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAoIWxhenlDb250ZXh0LnR5cGVOYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdDb3VsZCBub3QgZXh0cmFjdCB0eXBlIG5hbWUgZnJvbSBsYXp5KCkgY2FsbCcsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyB0eXBlTmFtZSB9ID0gbGF6eUNvbnRleHQ7XG5cblx0XHQvLyBEZXRlcm1pbmUgcGFyZW50IHR5cGUgYW5kIGNvbGxlY3Rpb24gYmFzZWQgb24gdGhlIGNhbGwgc291cmNlLlxuXHRcdGNvbnN0IHBhcmVudE5vZGUgPSBsYXp5Q29udGV4dC5wYXJlbnRUeXBlO1xuXHRcdGNvbnN0IHsgY29sbGVjdGlvbklkIH0gPSBsYXp5Q29udGV4dDtcblxuXHRcdC8vIEV4dHJhY3QgY29uZmlnIG9wdGlvbnNcblx0XHRjb25zdCBjb25maWcgPSB0aGlzLmV4dHJhY3RMYXp5Q29uZmlnKGNhbGwpO1xuXG5cdFx0Ly8gQ3JlYXRlIHR5cGUgbm9kZSBmaXJzdCBzbyBpdHMgaW50ZXJuYWwgZnVsbFBhdGggKGluY2x1ZGluZyBhbnkgY29sbGVjdGlvbiBwcmVmaXgpIGlzIHJlc29sdmVkLlxuXHRcdGNvbnN0IG5vZGUgPSBUeXBlR3JhcGhJbXBsLmNyZWF0ZU5vZGUoXG5cdFx0XHR0eXBlTmFtZSxcblx0XHRcdHBhcmVudE5vZGUsXG5cdFx0XHRzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0bGluZSArIDEsXG5cdFx0XHRjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0Y29sbGVjdGlvbklkXG5cdFx0KTtcblx0XHR0aGlzLmFwcGx5Q29sbGVjdGlvbkVtaXNzaW9uSW5mbyhub2RlLCBjb2xsZWN0aW9uSWQpO1xuXG5cdFx0Ly8gU2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlIGRldGVjdGlvbiAoaGFyZC1mYWlsIGxhdylcblx0XHR0aGlzLnJlY29yZERlZmluZVNpdGUoXG5cdFx0XHRwYXJlbnROb2RlID8gYCR7cGFyZW50Tm9kZS5mdWxsUGF0aH0uJHt0eXBlTmFtZX1gIDogYCR7Y29sbGVjdGlvbklkID8/ICdkZWZhdWx0J306OiR7dHlwZU5hbWV9YCxcblx0XHRcdGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gXG5cdFx0KTtcblxuXHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIHRoZSBjb25zdHJ1Y3RvciByZXR1cm5lZCBieSB0aGUgbGF6eSBnZXR0ZXJcblx0XHQvLyDigJQgdGhlIG5ldyBub2RlIGFuY2hvcnMgcmVsYXRpdmUtZmlyc3QgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb25cblx0XHRjb25zdCBwcmV2aW91c0FuY2hvciA9IHRoaXMuY3VycmVudEdyYXBoQW5jaG9yO1xuXHRcdHRoaXMuY3VycmVudEdyYXBoQW5jaG9yID0gbm9kZTtcblx0XHR0cnkge1xuXHRcdFx0bm9kZS5wcm9wZXJ0aWVzID0gdGhpcy5leHRyYWN0UHJvcGVydGllcyhjYWxsKTtcblxuXHRcdFx0Ly8gRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZvciBUeXBlUmVnaXN0cnkgc2lnbmF0dXJlXG5cdFx0XHRub2RlLmNvbnN0cnVjdG9yUGFyYW1zID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JQYXJhbXMoY2FsbCk7XG5cdFx0fSBmaW5hbGx5IHtcblx0XHRcdHRoaXMuY3VycmVudEdyYXBoQW5jaG9yID0gcHJldmlvdXNBbmNob3I7XG5cdFx0fVxuXG5cdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpO1xuXHRcdG5vZGUuaW5zdGFuY2VUeXBlT3ZlcnJpZGUgPSB0aGlzLmhhc0FueVRoaXNBbm5vdGF0aW9uKGNvbnN0cnVjdG9yRXhwcikgPyAnYW55JyA6IHVuZGVmaW5lZDtcblx0XHQvLyBBc3luYyBjb25zdHJ1Y3RvciBkZXRlY3Rpb24gKGFzeW5jIG1vZGlmaWVyLCBzeW50YWN0aWMgb25seSlcblx0XHRub2RlLmlzQXN5bmMgPSB0aGlzLmlzQXN5bmNDb25zdHJ1Y3RIYW5kbGVyKHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yRXhwcmVzc2lvbihjYWxsKSk7XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGhcblx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChwYXJlbnROb2RlLCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KG5vZGUpO1xuXHRcdH1cblxuXHRcdC8vIENyZWF0ZSBkZWZpbml0aW9uIGluZm8gdXNpbmcgdGhlIG5vZGUncyByZXNvbHZlZCBmdWxsUGF0aFxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiBwYXJlbnROb2RlID8gcGFyZW50Tm9kZS5mdWxsUGF0aCA6IG51bGwsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IGNvbmZpZy5zdHJpY3RDaGFpbiA/PyB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBjb25maWcuYmxvY2tFcnJvcnMgPz8gZmFsc2UsXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChub2RlLmZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0XHR0aGlzLmVkc1Njb3BlQnlOb2RlLnNldChjYWxsLCBub2RlLmZ1bGxQYXRoKTtcblxuXHRcdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnQ6IGNvbnN0IExhenlUeXBlID0gbGF6eSgnTGF6eVR5cGUnLCAuLi4pIC0+IG1hcCBcIkxhenlUeXBlXCIgLT4gXCJMYXp5VHlwZVwiXG5cdFx0Ly8gRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBjb25zdCBYID0gbGF6eSgnQScpLmRlZmluZSgnQicpLCB3ZSB3YW50IHRvIG1hcCBYIC0+IEEgKHRoZSByb290KVxuXHRcdHRoaXMudHJhY2tWYXJpYWJsZUFzc2lnbm1lbnQoY2FsbCwgcGFyZW50Tm9kZSwgbm9kZS5mdWxsUGF0aCwgc291cmNlRmlsZSk7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBsYXp5KCkgY2FsbCBhcmd1bWVudHMgaW50byBhIG5vcm1hbGl6ZWQgc2hhcGUuXG5cdCAqIEhhbmRsZXMgbmFtZWQvdW5uYW1lZCBhbmQgZXhwbGljaXQtc291cmNlIGZvcm1zLCBib3RoIGFzIGZyZWUgY2FsbHNcblx0ICogYW5kIGFzIG1ldGhvZCBjYWxscy4gVGhlIHVubmFtZWQgc2hhcGVzIHJldHVybiBgbmFtZTogdW5kZWZpbmVkYCDigJRcblx0ICogcHJvY2Vzc0xhenlDYWxsIHJlamVjdHMgdGhlbSB3aXRoIGFuIGFuYWx5emVyIGVycm9yICh0aGUgcnVudGltZVxuXHQgKiByZXF1aXJlcyB0aGUgbmFtZSksIHNvIG5vIHR5cGUgaXMgZ2VuZXJhdGVkIGZvciB0aGVtLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0TGF6eUNhbGxBcmdzIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHtcblx0XHRzb3VyY2U/OiB0cy5FeHByZXNzaW9uO1xuXHRcdG5hbWU/OiBzdHJpbmc7XG5cdFx0Z2V0dGVyOiB0cy5FeHByZXNzaW9uO1xuXHRcdGNvbmZpZz86IHRzLkV4cHJlc3Npb247XG5cdH0gfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGFyZ3MgPSBjYWxsLmFyZ3VtZW50cztcblx0XHRjb25zdCBpc01ldGhvZENhbGwgPSB0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pO1xuXG5cdFx0aWYgKGlzTWV0aG9kQ2FsbCkge1xuXHRcdFx0Ly8gU291cmNlIGlzIHRoZSBvYmplY3Qgb2YgdGhlIHByb3BlcnR5IGFjY2VzczogVHlwZS5sYXp5KC4uLilcblx0XHRcdGNvbnN0IHNvdXJjZSA9IGNhbGwuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBbIG1ldGhvZEZpcnN0QXJnIF0gPSBhcmdzO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChtZXRob2RGaXJzdEFyZykpIHtcblx0XHRcdFx0Ly8gVHlwZS5sYXp5KCdOYW1lJywgZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0XHRpZiAoYXJncy5sZW5ndGggPCAyKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHNvdXJjZSxcblx0XHRcdFx0XHRuYW1lICAgOiBtZXRob2RGaXJzdEFyZy50ZXh0LFxuXHRcdFx0XHRcdGdldHRlciA6IGFyZ3NbIDEgXSxcblx0XHRcdFx0XHRjb25maWcgOiBhcmdzWyAyIF0sXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cdFx0XHQvLyBUeXBlLmxhenkoZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0c291cmNlLFxuXHRcdFx0XHRnZXR0ZXIgOiBtZXRob2RGaXJzdEFyZyxcblx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMSBdLFxuXHRcdFx0fTtcblx0XHR9XG5cblx0XHQvLyBGcmVlIGNhbGw6IGxhenkoLi4uKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBhcmdzO1xuXG5cdFx0Ly8gRXhwbGljaXQtc291cmNlIGZvcm06IGxhenkoc291cmNlLCAnTmFtZScsIGdldHRlciwgY29uZmlnPylcblx0XHQvLyBvciBsYXp5KHNvdXJjZSwgZ2V0dGVyLCBjb25maWc/KVxuXHRcdGlmIChhcmdzLmxlbmd0aCA+PSAyICYmIHRzLmlzSWRlbnRpZmllcihmaXJzdEFyZykpIHtcblx0XHRcdGNvbnN0IFsgLCBzZWNvbmRBcmcgXSA9IGFyZ3M7XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKHNlY29uZEFyZykpIHtcblx0XHRcdFx0Ly8gbGF6eShzb3VyY2UsICdOYW1lJywgZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0XHRpZiAoYXJncy5sZW5ndGggPCAzKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHNvdXJjZSA6IGZpcnN0QXJnLFxuXHRcdFx0XHRcdG5hbWUgICA6IHNlY29uZEFyZy50ZXh0LFxuXHRcdFx0XHRcdGdldHRlciA6IGFyZ3NbIDIgXSxcblx0XHRcdFx0XHRjb25maWcgOiBhcmdzWyAzIF0sXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cdFx0XHQvLyBsYXp5KHNvdXJjZSwgZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0c291cmNlIDogZmlyc3RBcmcsXG5cdFx0XHRcdGdldHRlciA6IHNlY29uZEFyZyxcblx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMiBdLFxuXHRcdFx0fTtcblx0XHR9XG5cblx0XHQvLyBOYW1lZCByb290IGZvcm06IGxhenkoJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChmaXJzdEFyZykpIHtcblx0XHRcdGlmIChhcmdzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB7XG5cdFx0XHRcdG5hbWUgICA6IGZpcnN0QXJnLnRleHQsXG5cdFx0XHRcdGdldHRlciA6IGFyZ3NbIDEgXSxcblx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMiBdLFxuXHRcdFx0fTtcblx0XHR9XG5cblx0XHQvLyBVbm5hbWVkIHJvb3QgZm9ybTogbGF6eShnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0cmV0dXJuIHtcblx0XHRcdGdldHRlciA6IGZpcnN0QXJnLFxuXHRcdFx0Y29uZmlnIDogYXJnc1sgMSBdLFxuXHRcdH07XG5cdH1cblxuXHQvKipcblx0ICogVW53cmFwIHRoZSBjb25zdHJ1Y3RvciByZXR1cm5lZCBieSBhIGxhenkgZ2V0dGVyLlxuXHQgKiBTdXBwb3J0czpcblx0ICogICAoKSA9PiBjbGFzcyBOYW1lIHt9XG5cdCAqICAgKCkgPT4gZnVuY3Rpb24gTmFtZSgpIHt9XG5cdCAqICAgKCkgPT4geyByZXR1cm4gY2xhc3MgTmFtZSB7fTsgfVxuXHQgKiAgIGZ1bmN0aW9uICgpIHsgcmV0dXJuIGZ1bmN0aW9uIE5hbWUoKSB7fTsgfVxuXHQgKi9cblx0cHJpdmF0ZSB1bndyYXBMYXp5R2V0dGVyIChnZXR0ZXJFeHByOiB0cy5FeHByZXNzaW9uKTogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihnZXR0ZXJFeHByKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBnZXR0ZXJFeHByO1xuXHRcdFx0aWYgKCF0cy5pc0Jsb2NrKGJvZHkpKSB7XG5cdFx0XHRcdHJldHVybiBib2R5O1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBzdG10IG9mIGJvZHkuc3RhdGVtZW50cykge1xuXHRcdFx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQoc3RtdCkgJiYgc3RtdC5leHByZXNzaW9uKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHN0bXQuZXhwcmVzc2lvbjtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oZ2V0dGVyRXhwcikpIHtcblx0XHRcdGNvbnN0IHsgYm9keSB9ID0gZ2V0dGVyRXhwcjtcblx0XHRcdGZvciAoY29uc3Qgc3RtdCBvZiBib2R5LnN0YXRlbWVudHMpIHtcblx0XHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KHN0bXQpICYmIHN0bXQuZXhwcmVzc2lvbikge1xuXHRcdFx0XHRcdHJldHVybiBzdG10LmV4cHJlc3Npb247XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gTm90IGEgcmVjb2duaXplZCBnZXR0ZXIgcGF0dGVyblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBhIGNvbnN0cnVjdG9yIG5hbWUgZnJvbSBhIGNsYXNzIGV4cHJlc3Npb24sIGNsYXNzIGRlY2xhcmF0aW9uLFxuXHQgKiBvciBuYW1lZCBmdW5jdGlvbiBleHByZXNzaW9uLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JOYW1lIChjb25zdHJ1Y3RvckV4cHI6IENvbnN0cnVjdG9ySGFuZGxlcik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikgJiYgY29uc3RydWN0b3JFeHByLm5hbWUpIHtcblx0XHRcdHJldHVybiBjb25zdHJ1Y3RvckV4cHIubmFtZS50ZXh0O1xuXHRcdH1cblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKGNvbnN0cnVjdG9yRXhwcikgJiYgY29uc3RydWN0b3JFeHByLm5hbWUpIHtcblx0XHRcdHJldHVybiBjb25zdHJ1Y3RvckV4cHIubmFtZS50ZXh0O1xuXHRcdH1cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSAmJiBjb25zdHJ1Y3RvckV4cHIubmFtZSkge1xuXHRcdFx0cmV0dXJuIGNvbnN0cnVjdG9yRXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0aGUgdHlwZSBuYW1lIGZyb20gZWl0aGVyIGEgZGVmaW5lKCkgb3IgbGF6eSgpIGNhbGwuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZSAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChjYWxsKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMuZXh0cmFjdFR5cGVOYW1lKGNhbGwpO1xuXHRcdH1cblx0XHRpZiAodGhpcy5pc0xhenlDYWxsKGNhbGwpKSB7XG5cdFx0XHRjb25zdCBhcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdFx0aWYgKCFhcmdzKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAoYXJncy5uYW1lKSB7XG5cdFx0XHRcdHJldHVybiBhcmdzLm5hbWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLnVud3JhcExhenlHZXR0ZXIoYXJncy5nZXR0ZXIpO1xuXHRcdFx0aWYgKGNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0XHRyZXR1cm4gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JOYW1lKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0aGUgZnVsbCBsYXp5KCkgY2FsbCBjb250ZXh0OiB0eXBlIG5hbWUsIHBhcmVudCB0eXBlLCBhbmQgY29sbGVjdGlvbi5cblx0ICogSGFuZGxlcyBkaXJlY3QgY2FsbHMsIHByb3BlcnR5LWFjY2VzcyBjYWxscywgY2hhaW5lZCBjYWxscywgYW5kIHRoZVxuXHQgKiBleHBsaWNpdC1zb3VyY2UgZm9ybSBgbGF6eShzb3VyY2UsICdUeXBlTmFtZScsIGdldHRlcilgLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0TGF6eUNvbnRleHQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKToge1xuXHRcdHR5cGVOYW1lPzogc3RyaW5nO1xuXHRcdHBhcmVudFR5cGU/OiBUeXBlTm9kZTtcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmc7XG5cdH0ge1xuXHRcdGNvbnN0IGFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0aWYgKCFhcmdzKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0bGV0IHR5cGVOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQgPSBhcmdzLm5hbWU7XG5cdFx0aWYgKCF0eXBlTmFtZSkge1xuXHRcdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy51bndyYXBMYXp5R2V0dGVyKGFyZ3MuZ2V0dGVyKTtcblx0XHRcdGlmIChjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdFx0dHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3Rvck5hbWUoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0aWYgKCF0eXBlTmFtZSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gY2FsbDtcblxuXHRcdC8vIERpcmVjdCBjYWxsOiBsYXp5KCdUeXBlTmFtZScsIC4uLikgb3IgbGF6eShzb3VyY2UsICdUeXBlTmFtZScsIGdldHRlcilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2xhenknKSB7XG5cdFx0XHRpZiAoYXJncy5zb3VyY2UgJiYgdHMuaXNJZGVudGlmaWVyKGFyZ3Muc291cmNlKSkge1xuXHRcdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKGFyZ3Muc291cmNlLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0XHRcdHBhcmVudFR5cGUgICA6IHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSxcblx0XHRcdFx0XHRjb2xsZWN0aW9uSWQgOiBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCxcblx0XHRcdFx0fTtcblx0XHRcdH1cblx0XHRcdC8vIFBsYWluIHJvb3QgbGF6eSBpbiBkZWZhdWx0IGNvbGxlY3Rpb25cblx0XHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiBYLmxhenkoJ1R5cGVOYW1lJywgLi4uKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLm5hbWUudGV4dCA9PT0gJ2xhenknKSB7XG5cdFx0XHRjb25zdCBvYmogPSBleHByZXNzaW9uLmV4cHJlc3Npb247XG5cblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIob2JqKSkge1xuXHRcdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKG9iai50ZXh0KTtcblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHR0eXBlTmFtZSxcblx0XHRcdFx0XHRwYXJlbnRUeXBlICAgOiBzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUsXG5cdFx0XHRcdFx0Y29sbGVjdGlvbklkIDogc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQsXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihvYmopKSB7XG5cdFx0XHRcdC8vIE5lc3RlZCBhY2Nlc3M6IGluc3RhbmNlLlR5cGUubGF6eSAtIHRyeSB0byByZXNvbHZlXG5cdFx0XHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKG9iaik7XG5cdFx0XHRcdGlmIChjaGFpbi5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoY2hhaW4uam9pbignLicpKTtcblx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUgfTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihvYmopKSB7XG5cdFx0XHRcdC8vIERldGVybWluZSB0aGUgY29sbGVjdGlvbiBjb250ZXh0IGZyb20gdGhlIHJvb3Qgb2YgdGhlIGNoYWluIHNvIHRoYXRcblx0XHRcdFx0Ly8gY3VzdG9tLWNvbGxlY3Rpb24gdHlwZXMgZG8gbm90IGdldCBjb25mdXNlZCB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcy5cblx0XHRcdFx0Y29uc3Qgcm9vdElkID0gdGhpcy5nZXRSb290SWRlbnRpZmllcihvYmouZXhwcmVzc2lvbik7XG5cdFx0XHRcdGNvbnN0IGV4cGVjdGVkQ29sbGVjdGlvbklkID0gcm9vdElkXG5cdFx0XHRcdFx0PyB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uocm9vdElkLnRleHQpLmNvbGxlY3Rpb25JZFxuXHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXG5cdFx0XHRcdC8vIENoYWluZWQgY2FsbDogZGVmaW5lKCdBJykubGF6eSgnQicpIG9yIGxhenkoJ0EnKS5sYXp5KCdCJylcblx0XHRcdFx0aWYgKHRoaXMuaXNEZWZpbmVDYWxsKG9iaikpIHtcblx0XHRcdFx0XHR0aGlzLnByb2Nlc3NEZWZpbmVDYWxsKG9iaiwgc291cmNlRmlsZSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzTGF6eUNhbGwob2JqLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBCdWlsZGVyIGxvb2t1cCBjaGFpbjogQXBwLmxvb2t1cCgnVXNlcicpLmxhenkoJ0FkbWluJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMb29rdXBDYWxsKG9iaikpIHtcblx0XHRcdFx0XHRjb25zdCBsb29rZWRVcFBhdGggPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKG9iaik7XG5cdFx0XHRcdFx0aWYgKGxvb2tlZFVwUGF0aCkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUobG9va2VkVXBQYXRoKTtcblx0XHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZS5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgY29uZmlnIG9wdGlvbnMgZnJvbSBsYXp5KCkgY2FsbFxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0TGF6eUNvbmZpZyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0ge1xuXHRcdGNvbnN0IGFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0aWYgKCFhcmdzIHx8ICFhcmdzLmNvbmZpZyB8fCAhdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihhcmdzLmNvbmZpZykpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRjb25zdCBjb25maWdSZXN1bHQgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChhcmdzLmNvbmZpZyk7XG5cdFx0cmV0dXJuIGNvbmZpZ1Jlc3VsdDtcblx0fVxuXG5cdHByaXZhdGUgaGFzR2VuZXJhdGVkVHlwZVJlZmVyZW5jZSAoaGFuZGxlcjogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkKTogYm9vbGVhbiB7XG5cdFx0aWYgKCFoYW5kbGVyKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXHRcdGNvbnN0IGltcG9ydHMgPSB0aGlzLmdlbmVyYXRlZFR5cGVJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdGlmICghaW1wb3J0cyB8fCBpbXBvcnRzLnNpemUgPT09IDApIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0bGV0IGZvdW5kID0gZmFsc2U7XG5cdFx0Y29uc3QgdmlzaXQgPSAobm9kZTogdHMuTm9kZSk6IHZvaWQgPT4ge1xuXHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIobm9kZSkgJiYgaW1wb3J0cy5oYXMobm9kZS50ZXh0KSkge1xuXHRcdFx0XHRmb3VuZCA9IHRydWU7XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCB2aXNpdCk7XG5cdFx0fTtcblx0XHR2aXNpdChoYW5kbGVyKTtcblx0XHRyZXR1cm4gZm91bmQ7XG5cdH1cblxuXHRwcml2YXRlIGhhc1NlbGZUeXBlQW5ub3RhdGlvbiAoaGFuZGxlcjogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkLCBmdWxsUGF0aDogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0aWYgKCFoYW5kbGVyIHx8ICF0cy5pc0Z1bmN0aW9uTGlrZShoYW5kbGVyKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblx0XHRjb25zdCB0eXBlTmFtZSA9IGZ1bGxQYXRoLnNwbGl0KCcuJykucG9wKCk7XG5cdFx0Zm9yIChjb25zdCBwYXJhbWV0ZXIgb2YgaGFuZGxlci5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihwYXJhbWV0ZXIubmFtZSkgfHwgcGFyYW1ldGVyLm5hbWUudGV4dCAhPT0gJ3RoaXMnIHx8ICFwYXJhbWV0ZXIudHlwZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGFubm90YXRpb24gPSBwYXJhbWV0ZXIudHlwZS5nZXRUZXh0KCk7XG5cdFx0XHRjb25zdCByZXN1bHQgPSBhbm5vdGF0aW9uID09PSB0eXBlTmFtZSB8fCBhbm5vdGF0aW9uLmVuZHNXaXRoKGAuJHt0eXBlTmFtZX1gKSB8fFxuXHRcdFx0XHRhbm5vdGF0aW9uID09PSBgSW5zdGFuY2VUeXBlPHR5cGVvZiAke3R5cGVOYW1lfT5gO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0cHJpdmF0ZSByZWNvcmRCdWlsZGVyQ2FuZGlkYXRlIChcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0ZnVsbFBhdGg6IHN0cmluZyxcblx0XHRraW5kOiAncmVnaXN0cnlPZicgfCAndHlwZW9mJyxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdGRlY2xhcmF0aW9uOiB0cy5WYXJpYWJsZURlY2xhcmF0aW9uLFxuXHRcdGV4Y2x1ZGVkOiBib29sZWFuXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IGNhbmRpZGF0ZTogQnVpbGRlckNhbmRpZGF0ZSA9IHtcblx0XHRcdG5hbWUsXG5cdFx0XHRzb3VyY2VGaWxlIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdGtpbmQsXG5cdFx0XHRmdWxsUGF0aCxcblx0XHRcdGV4cG9ydHMgICAgOiBbXSxcblx0XHRcdGV4Y2x1ZGVkXG5cdFx0fTtcblx0XHRjb25zdCBzdGF0ZW1lbnQgPSBkZWNsYXJhdGlvbi5wYXJlbnQucGFyZW50O1xuXHRcdGNvbnN0IG1vZGlmaWVycyA9IHRzLmlzVmFyaWFibGVTdGF0ZW1lbnQoc3RhdGVtZW50KSA/IHRzLmdldE1vZGlmaWVycyhzdGF0ZW1lbnQpID8/IFtdIDogW107XG5cdFx0Y29uc3QgaXNEZWZhdWx0ID0gbW9kaWZpZXJzLnNvbWUobW9kaWZpZXIgPT4gbW9kaWZpZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5EZWZhdWx0S2V5d29yZCk7XG5cdFx0Y29uc3QgaXNFeHBvcnRlZCA9IG1vZGlmaWVycy5zb21lKG1vZGlmaWVyID0+IG1vZGlmaWVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRXhwb3J0S2V5d29yZCk7XG5cdFx0aWYgKGlzRXhwb3J0ZWQpIHtcblx0XHRcdGNhbmRpZGF0ZS5leHBvcnRzLnB1c2goe1xuXHRcdFx0XHRuYW1lICAgICAgICAgIDogbmFtZSxcblx0XHRcdFx0c291cmNlRmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGRlZmF1bHRJbXBvcnQgOiBpc0RlZmF1bHRcblx0XHRcdH0pO1xuXHRcdH1cblx0XHR0aGlzLmJ1aWxkZXJDYW5kaWRhdGVzLnB1c2goY2FuZGlkYXRlKTtcblx0fVxuXG5cdHByaXZhdGUgbWFya0J1aWxkZXJFeHBvcnQgKFxuXHRcdGV4cG9ydGVkTmFtZTogc3RyaW5nLFxuXHRcdG9yaWdpbmFsTmFtZTogc3RyaW5nLFxuXHRcdGZpbGVQYXRoOiBzdHJpbmcsXG5cdFx0bW9kdWxlU3BlY2lmaWVyPzogc3RyaW5nXG5cdCk6IHZvaWQge1xuXHRcdGlmICghbW9kdWxlU3BlY2lmaWVyKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGNhbmRpZGF0ZSBvZiB0aGlzLmJ1aWxkZXJDYW5kaWRhdGVzKSB7XG5cdFx0XHRcdGNvbnN0IG1hdGNoZXNDYW5kaWRhdGUgPSBub2RlUGF0aC5yZXNvbHZlKGNhbmRpZGF0ZS5zb3VyY2VGaWxlKSA9PT0gbm9kZVBhdGgucmVzb2x2ZShmaWxlUGF0aClcblx0XHRcdFx0XHQmJiBjYW5kaWRhdGUubmFtZSA9PT0gb3JpZ2luYWxOYW1lXG5cdFx0XHRcdFx0JiYgIWNhbmRpZGF0ZS5leGNsdWRlZDtcblx0XHRcdFx0aWYgKG1hdGNoZXNDYW5kaWRhdGUpIHtcblx0XHRcdFx0XHRjYW5kaWRhdGUuZXhwb3J0cy5wdXNoKHsgbmFtZSA6IGV4cG9ydGVkTmFtZSwgc291cmNlRmlsZSA6IGZpbGVQYXRoIH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShtb2R1bGVTcGVjaWZpZXIsIGZpbGVQYXRoKTtcblx0XHRpZiAocmVzb2x1dGlvbj8uaXNFeHRlcm5hbCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBmYWxsYmFja1BhdGggPSBtb2R1bGVTcGVjaWZpZXIuZW5kc1dpdGgoJy50cycpXG5cdFx0XHQ/IG5vZGVQYXRoLnJlc29sdmUobm9kZVBhdGguZGlybmFtZShmaWxlUGF0aCksIG1vZHVsZVNwZWNpZmllcilcblx0XHRcdDogYCR7bm9kZVBhdGgucmVzb2x2ZShub2RlUGF0aC5kaXJuYW1lKGZpbGVQYXRoKSwgbW9kdWxlU3BlY2lmaWVyKX0udHNgO1xuXHRcdGNvbnN0IHJlc29sdmVkUGF0aCA9IHJlc29sdXRpb24/LnJlc29sdmVkUGF0aCA/PyBmYWxsYmFja1BhdGg7XG5cdFx0Zm9yIChjb25zdCBjYW5kaWRhdGUgb2YgdGhpcy5idWlsZGVyQ2FuZGlkYXRlcykge1xuXHRcdFx0aWYgKG5vZGVQYXRoLnJlc29sdmUoY2FuZGlkYXRlLnNvdXJjZUZpbGUpICE9PSBub2RlUGF0aC5yZXNvbHZlKHJlc29sdmVkUGF0aCkgfHwgY2FuZGlkYXRlLmV4Y2x1ZGVkKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbWF0Y2hlc05hbWUgPSBvcmlnaW5hbE5hbWUgPT09ICdkZWZhdWx0J1xuXHRcdFx0XHQ/IGNhbmRpZGF0ZS5leHBvcnRzLnNvbWUoZXhwb3J0ZWQgPT4gZXhwb3J0ZWQubmFtZSA9PT0gJ2RlZmF1bHQnKVxuXHRcdFx0XHQ6IGNhbmRpZGF0ZS5uYW1lID09PSBvcmlnaW5hbE5hbWU7XG5cdFx0XHRpZiAobWF0Y2hlc05hbWUpIHtcblx0XHRcdFx0Y2FuZGlkYXRlLmV4cG9ydHMucHVzaCh7XG5cdFx0XHRcdFx0bmFtZSAgICAgICAgICA6IGV4cG9ydGVkTmFtZSxcblx0XHRcdFx0XHRzb3VyY2VGaWxlICAgIDogZmlsZVBhdGgsXG5cdFx0XHRcdFx0ZGVmYXVsdEltcG9ydCA6IG9yaWdpbmFsTmFtZSA9PT0gJ2RlZmF1bHQnXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdHByaXZhdGUgdHJhY2tCdWlsZGVyRXhwb3J0QXNzaWdubWVudCAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNFeHBvcnRBc3NpZ25tZW50KG5vZGUpIHx8ICF0cy5pc0lkZW50aWZpZXIobm9kZS5leHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRmb3IgKGNvbnN0IGNhbmRpZGF0ZSBvZiB0aGlzLmJ1aWxkZXJDYW5kaWRhdGVzKSB7XG5cdFx0XHRjb25zdCBtYXRjaGVzQ2FuZGlkYXRlID0gbm9kZVBhdGgucmVzb2x2ZShjYW5kaWRhdGUuc291cmNlRmlsZSkgPT09IG5vZGVQYXRoLnJlc29sdmUoZmlsZVBhdGgpXG5cdFx0XHRcdCYmIGNhbmRpZGF0ZS5uYW1lID09PSBub2RlLmV4cHJlc3Npb24udGV4dFxuXHRcdFx0XHQmJiAhY2FuZGlkYXRlLmV4Y2x1ZGVkO1xuXHRcdFx0aWYgKG1hdGNoZXNDYW5kaWRhdGUpIHtcblx0XHRcdFx0Y2FuZGlkYXRlLmV4cG9ydHMucHVzaCh7IG5hbWUgOiBub2RlLmV4cHJlc3Npb24udGV4dCwgc291cmNlRmlsZSA6IGZpbGVQYXRoLCBkZWZhdWx0SW1wb3J0IDogdHJ1ZSB9KTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHQqIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnRzIHRoYXQgY2FwdHVyZSBkZWZpbmUoKSByZXN1bHRzXG5cdFx0KiBlLmcuLCBjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKSBtYXBzIFwiVXNlclwiIC0+IFwiVXNlckVudGl0eVwiXG5cdFx0KiBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGNvbnN0IFggPSBkZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKSwgd2UgbWFwIFggLT4gQSAodGhlIHJvb3QgdHlwZSlcblx0XHQqL1xuXHRwcml2YXRlIHRyYWNrVmFyaWFibGVBc3NpZ25tZW50IChcblx0XHRjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHRwYXJlbnROb2RlOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCxcblx0XHRmdWxsUGF0aDogc3RyaW5nLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGVcblx0KTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBjYWxsIGlzIHRoZSByaWdodC1oYW5kIHNpZGUgb2YgYSB2YXJpYWJsZSBkZWNsYXJhdGlvblxuXHRcdC8vIFdhbGsgdXAgdGhlIHRyZWUgdG8gZmluZCBWYXJpYWJsZURlY2xhcmF0aW9uXG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBjYWxsLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihjdXJyZW50KSkge1xuXHRcdFx0XHQvLyBGb3VuZDogY29uc3QgWCA9IGRlZmluZSguLi4pXG5cdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudC5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHZhck5hbWUgPSBjdXJyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0XHQvLyBGMTg6IGRlZmluZSgpIHJldHVybnMgdGhlIERFRklORUQgdHlwZSdzIGNvbnN0cnVjdG9yLFxuXHRcdFx0XHRcdC8vIHNvIGEgY29uc3QgaG9sZGluZyBhIG11bHRpLWhvcCBpbml0aWFsaXplclxuXHRcdFx0XHRcdC8vIChgY29uc3QgWCA9IEEuZGVmaW5lKCdCJykuZGVmaW5lKCdDJylgKSBiaW5kcyB0aGUgTEFTVFxuXHRcdFx0XHRcdC8vIGhvcCDigJQgYSBkZWVwZXIgaG9wIG11c3Qgbm90IGJpbmQsIGFuZCB0aGUgb3V0ZXJtb3N0XG5cdFx0XHRcdFx0Ly8gaG9wIGJpbmRzIHVuY29uZGl0aW9uYWxseSAodmlzaXQtb3JkZXIgaW5kZXBlbmRlbnQpXG5cdFx0XHRcdFx0aWYgKHRoaXMuaXNEZWVwZXJEZWZpbmVIb3AoY2FsbCkpIHtcblx0XHRcdFx0XHRcdHJldHVybjtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Ly8gRm9yIGNoYWluZWQgbGF6eSBjYWxscyBsaWtlIGNvbnN0IFggPSBkZWZpbmUoJ0EnKS5sYXp5KCdCJyksXG5cdFx0XHRcdFx0Ly8gdGhlIGZpcnN0IGNhbGwgaW4gdGhlIGNoYWluIHNldHMgdGhlIG1hcHBpbmcgKGxhenkgaG9wXG5cdFx0XHRcdFx0Ly8ga2VlcHMgaXQg4oCUIHBpbm5lZCBiZWhhdmlvcilcblx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSAmJiB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmhhcyh2YXJOYW1lKSkge1xuXHRcdFx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCB0eXBlTm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoZnVsbFBhdGgpO1xuXHRcdFx0XHRcdGlmICh0eXBlTm9kZT8uY29sbGVjdGlvbklkID09PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHNlbGZSZWZlcmVuY2UgPSB0aGlzLmhhc0dlbmVyYXRlZFR5cGVSZWZlcmVuY2UodGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpKSB8fFxuXHRcdFx0XHRcdFx0dGhpcy5oYXNTZWxmVHlwZUFubm90YXRpb24odGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpLCBmdWxsUGF0aCk7XG5cdFx0XHRcdFx0XHRjb25zdCBleGNsdWRlZCA9IHNlbGZSZWZlcmVuY2UgfHwgKFxuXHRcdFx0XHRcdFx0XHRwYXJlbnROb2RlICE9PSB1bmRlZmluZWQgJiYgdGhpcy5leGNsdWRlZFR5cGVQYXRocy5oYXMocGFyZW50Tm9kZS5mdWxsUGF0aClcblx0XHRcdFx0XHRcdCk7XG5cdFx0XHRcdFx0XHRpZiAoZXhjbHVkZWQpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5leGNsdWRlZFR5cGVQYXRocy5hZGQoZnVsbFBhdGgpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0Y29uc3Qga2luZCA9IHRzLmlzSWRlbnRpZmllcihjYWxsLmV4cHJlc3Npb24pID8gJ3R5cGVvZicgOiAncmVnaXN0cnlPZic7XG5cdFx0XHRcdFx0XHR0aGlzLnJlY29yZEJ1aWxkZXJDYW5kaWRhdGUodmFyTmFtZSwgZnVsbFBhdGgsIGtpbmQsIHNvdXJjZUZpbGUsIGN1cnJlbnQsIGV4Y2x1ZGVkKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0dGhpcy52YXJpYWJsZVRvVHlwZU1hcC5zZXQodmFyTmFtZSwgZnVsbFBhdGgpO1xuXHRcdFx0XHRcdHRoaXMudHJhY2tGaWxlR3JhcGhCaW5kaW5nKHZhck5hbWUsIGZ1bGxQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm47XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEEgYC5kZWZpbmUoLi4uKWAgaG9wIHdyYXBwZWQgYnkgYW5vdGhlciBgLmRlZmluZSguLi4pYCBjYWxsIGlzIG5vdFxuXHQgKiB0aGUgdmFsdWUgaXRzIGNvbnN0IGVuZHMgdXAgaG9sZGluZyDigJQgdGhlIE9VVEVSTU9TVCBob3Agb2YgdGhlXG5cdCAqIGluaXRpYWxpemVyIGNoYWluIGlzIChkZWZpbmUoKSByZXR1cm5zIHRoZSBkZWZpbmVkIHR5cGUnc1xuXHQgKiBjb25zdHJ1Y3RvcikuIE9ubHkgdGhlIG91dGVybW9zdCBob3AgbWF5IGJpbmQgdGhlIHZhcmlhYmxlLlxuXHQgKi9cblx0cHJpdmF0ZSBpc0RlZXBlckRlZmluZUhvcCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBib29sZWFuIHtcblx0XHRjb25zdCB7IHBhcmVudCB9ID0gY2FsbDtcblx0XHRjb25zdCBkZWVwZXIgPSAhIXBhcmVudCAmJlxuXHRcdFx0dHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ocGFyZW50KSAmJlxuXHRcdFx0cGFyZW50Lm5hbWUudGV4dCA9PT0gJ2RlZmluZScgJiZcblx0XHRcdHRzLmlzQ2FsbEV4cHJlc3Npb24ocGFyZW50LnBhcmVudCkgJiZcblx0XHRcdHBhcmVudC5wYXJlbnQuZXhwcmVzc2lvbiA9PT0gcGFyZW50O1xuXHRcdHJldHVybiBkZWVwZXI7XG5cdH1cblxuXHQvKipcblx0ICogTWlycm9yIGEgdmFyaWFibGUgLT4gbW5lbW9uaWNhIGZ1bGxQYXRoIGJpbmRpbmcgaW50byB0aGUgcGVyLWZpbGVcblx0ICogdmFsdWUtc2NvcGUgbWFwIChncmFwaCBpZGVudGl0eSBsYXc6IGB0eXBlb2YgWGAgYW5kIGJhcmUgcmVmZXJlbmNlc1xuXHQgKiByZXNvbHZlIHRocm91Z2ggdGhlIGZpbGUncyBvd24gYmluZGluZ3MgZmlyc3QpLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja0ZpbGVHcmFwaEJpbmRpbmcgKHZhck5hbWU6IHN0cmluZywgZnVsbFBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGxldCBiaW5kaW5ncyA9IHRoaXMuZmlsZUdyYXBoQmluZGluZ3MuZ2V0KGZpbGVQYXRoKTtcblx0XHRpZiAoIWJpbmRpbmdzKSB7XG5cdFx0XHRiaW5kaW5ncyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHR0aGlzLmZpbGVHcmFwaEJpbmRpbmdzLnNldChmaWxlUGF0aCwgYmluZGluZ3MpO1xuXHRcdH1cblx0XHRiaW5kaW5ncy5zZXQodmFyTmFtZSwgZnVsbFBhdGgpO1xuXHR9XG5cdFxuXHQvKipcblx0XHQqIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnRzIGZyb20gbG9va3VwKCkgY2FsbHNcblx0XHQqIGUuZy4sIGNvbnN0IFNlbnRpZW5jZUNvbnN0cnVjdG9yID0gbG9va3VwKCdTZW50aWVuY2UnKSBtYXBzIFwiU2VudGllbmNlQ29uc3RydWN0b3JcIiAtPiBcIlNlbnRpZW5jZVwiXG5cdFx0Ki9cblx0cHJpdmF0ZSB0cmFja0xvb2t1cEFzc2lnbm1lbnQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLCB0eXBlUGF0aDogc3RyaW5nKTogdm9pZCB7XG5cdFx0dGhpcy5iaW5kUmVzdWx0VmFyaWFibGUoY2FsbCwgdHlwZVBhdGgpO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50cyBmcm9tIG5ldyBUeXBlKCkgY2FsbHNcblx0XHQqIGUuZy4sIGNvbnN0IHVzZXIgPSBuZXcgVXNlclR5cGUoKSBtYXBzIFwidXNlclwiIC0+IFwiVXNlclR5cGVcIlxuXHRcdCovXG5cdHByaXZhdGUgdHJhY2tOZXdBc3NpZ25tZW50IChuZXdFeHByOiB0cy5OZXdFeHByZXNzaW9uLCB0eXBlUGF0aDogc3RyaW5nKTogdm9pZCB7XG5cdFx0bGV0IGVmZmVjdGl2ZVBhdGggPSB0eXBlUGF0aDtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5ld0V4cHIucGFyZW50O1xuXHRcdC8vIENoYWluLWZvcm0gY29uc3RydWN0aW9uOiBuZXcgUigpLkEoKS5CKCkg4oCUIHRoZSByZXN1bHQgdmFyaWFibGVcblx0XHQvLyBob2xkcyB0aGUgT1VURVJNT1NUIHRpcCdzIGluc3RhbmNlIChhd2FpdC10cmFuc3BhcmVudCksIG5vdCB0aGVcblx0XHQvLyBpbm5lciBuZXcncyB0eXBlLiBXYWxrIHRoZSBjaGFpbiwga2VlcGluZyB0aGUgbGFzdCByZXNvbHZhYmxlIHRpcC5cblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGN1cnJlbnQpICYmXG5cdFx0XHRcdHRzLmlzQ2FsbEV4cHJlc3Npb24oY3VycmVudC5wYXJlbnQpICYmXG5cdFx0XHRcdGN1cnJlbnQucGFyZW50LmV4cHJlc3Npb24gPT09IGN1cnJlbnQpIHtcblx0XHRcdFx0Y29uc3QgdGlwID0gdGhpcy5yZXNvbHZlQ2hhaW5UaXBUeXBlUGF0aChjdXJyZW50LnBhcmVudCk7XG5cdFx0XHRcdGlmICh0aXApIHtcblx0XHRcdFx0XHRlZmZlY3RpdmVQYXRoID0gdGlwO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudC5wYXJlbnQ7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0YnJlYWs7XG5cdFx0fVxuXHRcdHRoaXMuYmluZFJlc3VsdFZhcmlhYmxlKG5ld0V4cHIsIGVmZmVjdGl2ZVBhdGgpO1xuXHR9XG5cblx0LyoqXG5cdCAqIEJpbmQgdGhlIG5lYXJlc3QgZW5jbG9zaW5nIGBjb25zdC9sZXQvdmFyIFggPSDigKZgIHRvIGEgbW5lbW9uaWNhXG5cdCAqIGZ1bGxQYXRoIOKAlCB0aGUgc2hhcmVkIHJlc3VsdC12YXJpYWJsZSB3YWxrZXIgYmVoaW5kIG5ldy9sb29rdXAvXG5cdCAqIGNoYWluL2ZvcmsvbWVyZ2UvY2FsbCB0cmFja2luZyAodmFsdWUgc2NvcGU6IGRvd25zdHJlYW0gcmVmZXJlbmNlc1xuXHQgKiBhbmQgYHRoaXMueCA9IHhgIGFzc2lnbm1lbnRzIHJlc29sdmUgdGhyb3VnaCB0aGUgc2FtZSBiaW5kaW5nKS5cblx0ICovXG5cdHByaXZhdGUgYmluZFJlc3VsdFZhcmlhYmxlIChmcm9tOiB0cy5Ob2RlLCB0eXBlUGF0aDogc3RyaW5nKTogdm9pZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBmcm9tLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihjdXJyZW50KSkge1xuXHRcdFx0XHQvLyBGb3VuZDogY29uc3QgWCA9IDxjb25zdHJ1Y3Rpb24+XG5cdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudC5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHZhck5hbWUgPSBjdXJyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0XHR0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLnNldCh2YXJOYW1lLCB0eXBlUGF0aCk7XG5cdFx0XHRcdFx0dGhpcy50cmFja0ZpbGVHcmFwaEJpbmRpbmcodmFyTmFtZSwgdHlwZVBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdC8vIFNjb3BlIGJvdW5kYXJ5OiBhIGNvbnN0cnVjdGlvbiBpbnNpZGUgYSBuZXN0ZWQgY2xhc3MvZnVuY3Rpb25cblx0XHRcdC8vIGJvZHkgZG9lcyBub3QgYmluZCB0aGUgb3V0ZXIgdmFyaWFibGUg4oCUXG5cdFx0XHQvLyBgY29uc3QgWCA9IGRlZmluZSgnWCcsIGNsYXNzIHsgbSA9IG5ldyBNYXAoKSB9KWAgaG9sZHMgdGhlXG5cdFx0XHQvLyBkZWZpbmVkIGNvbnN0cnVjdG9yLCBub3QgYSBNYXAuIFdpdGhvdXQgdGhpcyBzdG9wIHRoZSBjbGFzcy1ib2R5XG5cdFx0XHQvLyBpbnN0YW50aWF0aW9uIGNsb2JiZXJzIFgncyBiaW5kaW5nIGFuZCBhIGxhdGVyIFguZGVmaW5lKCdDaGlsZCcpXG5cdFx0XHQvLyBsb3NlcyBpdHMgcGFyZW50ICh0aGUgY2hpbGQgbGFuZHMgYXMgYSBiYXJlIGRlZmF1bHQtY29sbGVjdGlvblxuXHRcdFx0Ly8gcm9vdCDigJQgZmF0YWwgZm9yIGN1c3RvbSBjb2xsZWN0aW9ucywgd2hvc2UgZnVsbFBhdGhzIHRoZVxuXHRcdFx0Ly8gbmFtZS1vbmx5IGZhbGxiYWNrIGNhbm5vdCBzZWUpLlxuXHRcdFx0aWYgKHRzLmlzQ2xhc3NMaWtlKGN1cnJlbnQpIHx8IHRzLmlzRnVuY3Rpb25MaWtlKGN1cnJlbnQpKSB7XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGFuIGBpbnN0YW50aWF0aW9uYCB1c2FnZSBmb3IgYSBjb25zdHJ1Y3Rpb24tc2hhcGUgY2FsbFxuXHQgKiAoY2hhaW4gdGlwIC8gY2FsbCAvIGFwcGx5IC8gZm9yayAvIGNsb25lIC8gbWVyZ2Ug4oCUXG5cdCAqIGJ5dGUtaW5kaXN0aW5ndWlzaGFibGUgZnJvbSBgbmV3YCB1bnRpbCB0aGUgZGVmZXJyZWRcblx0ICogbWVjaGFuaXNtLWtpbmQgcmV2aXNpb24pLiBgY29uc3RydWN0b3JUZXh0YCBkZWZhdWx0cyB0byB0aGUgY2FsbGVlXG5cdCAqIGV4cHJlc3Npb24gdGV4dCBzbyB0aGUgc2l0ZSBzdGF5cyByZWFkYWJsZSB3aXRob3V0IG5ldyBmaWVsZHM7XG5cdCAqIGNhbGwvYXBwbHkgb3ZlcnJpZGUgaXQgd2l0aCB0aGUgQ3RvciBhcmd1bWVudCB0ZXh0LlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZSAoXG5cdFx0Y2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0dHlwZVBhdGg6IHN0cmluZyxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdGNvbnN0cnVjdG9yVGV4dD86IHN0cmluZ1xuXHQpOiB2b2lkIHtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0Y2FsbC5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgY3RvclRleHQgPSBjb25zdHJ1Y3RvclRleHQgPz8gY2FsbC5leHByZXNzaW9uLmdldFRleHQoc291cmNlRmlsZSk7XG5cdFx0dGhpcy5hZGRVc2FnZSh0eXBlUGF0aCwge1xuXHRcdFx0bG9jYXRpb24gICAgICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRraW5kICAgICAgICAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRjb2RlICAgICAgICAgICAgOiBjYWxsLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdGNvbnN0cnVjdG9yVGV4dCA6IGN0b3JUZXh0LnNsaWNlKDAsIDEwMCksXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0aGUgdHlwZSBhIGNvbnN0cnVjdGlvbi1jaGFpbiB0aXAgY2FsbCBjb25zdHJ1Y3RzOlxuXHQgKiBgbmV3IFIoLi4uKS5BKC4uLilgIGNvbnN0cnVjdHMgUi5BOyBgYXdhaXQgbmV3IFIoLi4uKS5BKC4uLikuQiguLi4pYFxuXHQgKiBjb25zdHJ1Y3RzIFIuQS5CLiBUaGUgcmVjZWl2ZXIgaXMgdGhlIG5lc3RlZCBjaGFpbiAoTmV3RXhwcmVzc2lvblxuXHQgKiBiYXNlLCB0aGVuIHRpcCBjYWxscyk7IGV4YWN0IGZ1bGxQYXRoIGZpcnN0LCBhbmQgb25seSB3aGVuIHRoZSByb290XG5cdCAqIGl0c2VsZiBpcyB1bmtub3duIGRvZXMgdGhlIHByb3AtbmFtZSBmYWxsYmFjayBsYXcgYXBwbHkgKHNvIHBsYWluXG5cdCAqIG1ldGhvZCBjYWxscyBvbiBmcmVzaCBpbnN0YW5jZXMgbmV2ZXIgcmVjb3JkIGEgY29uc3RydWN0aW9uKS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUNoYWluVGlwVHlwZVBhdGggKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIXRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlY2VpdmVyID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGxldCByb290UGF0aDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdGlmICh0cy5pc05ld0V4cHJlc3Npb24ocmVjZWl2ZXIuZXhwcmVzc2lvbikpIHtcblx0XHRcdGNvbnN0IGlubmVyID0gcmVjZWl2ZXIuZXhwcmVzc2lvbjtcblx0XHRcdHJvb3RQYXRoID0gdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oaW5uZXIuZXhwcmVzc2lvbilcblx0XHRcdFx0PyB0aGlzLnJlc29sdmVUeXBlUGF0aChpbm5lci5leHByZXNzaW9uKVxuXHRcdFx0XHQ6IHRoaXMuZ2V0VHlwZU5hbWVGcm9tRXhwcmVzc2lvbihpbm5lci5leHByZXNzaW9uKTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24ocmVjZWl2ZXIuZXhwcmVzc2lvbikpIHtcblx0XHRcdHJvb3RQYXRoID0gdGhpcy5yZXNvbHZlQ2hhaW5UaXBUeXBlUGF0aChyZWNlaXZlci5leHByZXNzaW9uKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0aWYgKCFyb290UGF0aCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgY2FuZGlkYXRlID0gYCR7cm9vdFBhdGh9LiR7cmVjZWl2ZXIubmFtZS50ZXh0fWA7XG5cdFx0aWYgKHRoaXMuZGVmaW5pdGlvbnMuaGFzKGNhbmRpZGF0ZSkpIHtcblx0XHRcdHJldHVybiBjYW5kaWRhdGU7XG5cdFx0fVxuXHRcdGlmICghdGhpcy5kZWZpbml0aW9ucy5oYXMocm9vdFBhdGgpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5yZXNvbHZlVHlwZVBhdGgocmVjZWl2ZXIpO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFRydWUgd2hlbiBgZXhwcmAgZGVub3RlcyBhIGNvbnN0cnVjdGlvbiBmdW5jdGlvbiBpbXBvcnRlZCBmcm9tXG5cdCAqICdtbmVtb25pY2EnIOKAlCB0aGUgbmFtZWQtaW1wb3J0IGZvcm0gKGBpbXBvcnQgeyBjYWxsIH0gZnJvbVxuXHQgKiAnbW5lbW9uaWNhJ2AsIGFsaWFzZXMgaW5jbHVkZWQpIG9yIGEgbWVtYmVyIG9mIGEgdHJhY2tlZFxuXHQgKiBtb2R1bGUtb2JqZWN0IGFsaWFzIChgbW5lbW9uaWNhLmNhbGxgKS4gVXNlcmxhbmQgY2FsbC9hcHBseS9iaW5kXG5cdCAqIGZ1bmN0aW9ucyBuZXZlciBtYXRjaC5cblx0ICovXG5cdHByaXZhdGUgaXNNbmVtb25pY2FDb25zdHJ1Y3Rpb25GbiAoZXhwcjogdHMuRXhwcmVzc2lvbiwgZm46ICdjYWxsJyB8ICdhcHBseScgfCAnYmluZCcpOiBib29sZWFuIHtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMubW5lbW9uaWNhTmFtZWRJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQoZXhwci50ZXh0KTtcblx0XHRcdGNvbnN0IG1hdGNoZWQgPSBpbXBvcnRlZCA9PT0gZm47XG5cdFx0XHRyZXR1cm4gbWF0Y2hlZDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpICYmIGV4cHIubmFtZS50ZXh0ID09PSBmbikge1xuXHRcdFx0Y29uc3QgbWF0Y2hlZCA9IHRzLmlzSWRlbnRpZmllcihleHByLmV4cHJlc3Npb24pICYmXG5cdFx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhleHByLmV4cHJlc3Npb24udGV4dCk7XG5cdFx0XHRyZXR1cm4gbWF0Y2hlZDtcblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIG1uZW1vbmljYSBjYWxsL2FwcGx5KGVudGl0eSwgQ3RvciwgLi4uKSAvIGJpbmQoZW50aXR5LCBDdG9yKTpcblx0ICogcmVzb2x2ZSB0aGUgQ3RvciBhcmd1bWVudCAoYXJnIDEpIHRvIGEgZ3JhcGggZnVsbFBhdGggdGhyb3VnaCB0aGVcblx0ICogc2FtZSB0aWVycyBhcyB0aGUgYG5ld2AgYnJhbmNoICh2YWx1ZSBzY29wZSBmb3IgaWRlbnRpZmllcnMsXG5cdCAqIGNoYWluIHJlc29sdXRpb24gZm9yIHByb3BlcnR5IGFjY2Vzc2VzKS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUNvbnN0cnVjdGlvbkZuVHlwZVBhdGggKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBjYWxsZWUgPSBjYWxsLmV4cHJlc3Npb247XG5cdFx0Y29uc3QgaXNDYWxsT3JBcHBseSA9IHRoaXMuaXNNbmVtb25pY2FDb25zdHJ1Y3Rpb25GbihjYWxsZWUsICdjYWxsJykgfHxcblx0XHRcdHRoaXMuaXNNbmVtb25pY2FDb25zdHJ1Y3Rpb25GbihjYWxsZWUsICdhcHBseScpO1xuXHRcdGNvbnN0IGlzQmluZCA9IHRoaXMuaXNNbmVtb25pY2FDb25zdHJ1Y3Rpb25GbihjYWxsZWUsICdiaW5kJyk7XG5cdFx0aWYgKCFpc0NhbGxPckFwcGx5ICYmICFpc0JpbmQpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGlmIChjYWxsLmFyZ3VtZW50cy5sZW5ndGggPCAyKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBbICwgY3RvckFyZyBdID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0Y29uc3Qga25vd24gPSB0aGlzLnJlc29sdmVDdG9yQXJnVHlwZVBhdGgoY3RvckFyZyk7XG5cdFx0cmV0dXJuIGtub3duO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYW4gZXhwcmVzc2lvbiBwYXNzZWQgd2hlcmUgYSBjb25zdHJ1Y3RvciBpcyBleHBlY3RlZCAodGhlXG5cdCAqIEN0b3Igb2YgY2FsbC9hcHBseS9iaW5kLCBhIHBsdWdpbiBmYWN0b3J5J3MgY29uc3RydWN0ZWQgdGFyZ2V0KSB0byBhXG5cdCAqIGRlZmluZWQgdHlwZSdzIGZ1bGxQYXRoOiB2YWx1ZSBzY29wZSBmb3IgaWRlbnRpZmllcnMsIGNoYWluXG5cdCAqIHJlc29sdXRpb24gZm9yIHByb3BlcnR5IGFjY2Vzc2VzLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlQ3RvckFyZ1R5cGVQYXRoIChjdG9yQXJnOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgcmVzb2x2ZWQ6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY3RvckFyZykpIHtcblx0XHRcdHJlc29sdmVkID0gdGhpcy5yZXNvbHZlVHlwZVBhdGgoY3RvckFyZyk7XG5cdFx0fSBlbHNlIGlmICh0cy5pc0lkZW50aWZpZXIoY3RvckFyZykpIHtcblx0XHRcdGNvbnN0IGJvdW5kID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQoY3RvckFyZy50ZXh0KTtcblx0XHRcdGlmIChib3VuZCkge1xuXHRcdFx0XHRyZXNvbHZlZCA9IGJvdW5kO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgZ3JhcGhSZXN1bHQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKGN0b3JBcmcudGV4dCk7XG5cdFx0XHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRcdFx0cmVzb2x2ZWQgPSBncmFwaFJlc3VsdC5ub2RlLmZ1bGxQYXRoO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGNvbnN0IGtub3duID0gcmVzb2x2ZWQgJiYgdGhpcy5kZWZpbml0aW9ucy5oYXMocmVzb2x2ZWQpID8gcmVzb2x2ZWQgOiB1bmRlZmluZWQ7XG5cdFx0cmV0dXJuIGtub3duO1xuXHR9XG5cblx0LyoqXG5cdCAqIGluc3RhbmNlLmZvcmsoLi4uKSAvIGluc3RhbmNlLmNsb25lKC4uLikgb24gYSB0cmFja2VkIHZhcmlhYmxlIOKAlFxuXHQgKiBydW50aW1lIHJldHVybnMgYHRoaXNgLCBzbyB0aGUgcmVzdWx0IGNhcnJpZXMgdGhlIHNvdXJjZSB0eXBlLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRm9ya0xpa2VUeXBlUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgbWV0aG9kID0gY2FsbC5leHByZXNzaW9uLm5hbWUudGV4dDtcblx0XHRpZiAobWV0aG9kICE9PSAnZm9yaycgJiYgbWV0aG9kICE9PSAnY2xvbmUnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZWNlaXZlciA9IGNhbGwuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHJlY2VpdmVyKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQocmVjZWl2ZXIudGV4dCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGcmVlIHV0aWxzIGZvcm1zOiB1dGlscy5tZXJnZShhLCBiLCAuLi4pIChhbHNvIHRoZSBkaXJlY3QgbmFtZWRcblx0ICogaW1wb3J0IGBtZXJnZShhLCBiKWApIGFuZCB0aGUgY3VycmllZCB1dGlscy5mb3JrKGluc3RhbmNlKSguLi4pLlxuXHQgKiBUaGUgcmVzdWx0IGJpbmRzIHRvIGFyZyAwJ3MgdHlwZSDigJQgcnVudGltZSByZXR1cm5zIGEncyBsaW5lYWdlIG92ZXJcblx0ICogYidzIGNvbnRleHQ7IGEncyBmdWxsUGF0aCBpcyB0aGUgaG9uZXN0IGFwcHJveGltYXRpb24gd2l0aGluIHRoZVxuXHQgKiBvdXRwdXQgY29udHJhY3QgKGRvY3VtZW50ZWQgaW4gUkVBRE1FKS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVV0aWxzRm5UeXBlUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGNhbGxlZSA9IGNhbGwuZXhwcmVzc2lvbjtcblx0XHRjb25zdCBpc1V0aWxzT3duZXIgPSAob3duZXI6IHRzLkV4cHJlc3Npb24pOiBib29sZWFuID0+IHtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIob3duZXIpKSB7XG5cdFx0XHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChvd25lci50ZXh0KTtcblx0XHRcdFx0cmV0dXJuIGltcG9ydGVkID09PSAndXRpbHMnO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbWF0Y2hlZCA9IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG93bmVyKSAmJiBvd25lci5uYW1lLnRleHQgPT09ICd1dGlscycgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKG93bmVyLmV4cHJlc3Npb24pICYmIHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhvd25lci5leHByZXNzaW9uLnRleHQpO1xuXHRcdFx0cmV0dXJuIG1hdGNoZWQ7XG5cdFx0fTtcblx0XHRsZXQgc3ViamVjdEFyZzogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZDtcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbGVlKSAmJiBpc1V0aWxzT3duZXIoY2FsbGVlLmV4cHJlc3Npb24pICYmXG5cdFx0XHQoY2FsbGVlLm5hbWUudGV4dCA9PT0gJ21lcmdlJyB8fCBjYWxsZWUubmFtZS50ZXh0ID09PSAnZm9yaycpKSB7XG5cdFx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblx0XHRcdHN1YmplY3RBcmcgPSBmaXJzdEFyZztcblx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihjYWxsZWUpKSB7XG5cdFx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMubW5lbW9uaWNhTmFtZWRJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQoY2FsbGVlLnRleHQpO1xuXHRcdFx0aWYgKGltcG9ydGVkID09PSAnbWVyZ2UnIHx8IGltcG9ydGVkID09PSAnZm9yaycpIHtcblx0XHRcdFx0Y29uc3QgWyBmaXJzdEFyZyBdID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0XHRcdHN1YmplY3RBcmcgPSBmaXJzdEFyZztcblx0XHRcdH1cblx0XHR9IGVsc2UgaWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oY2FsbGVlKSAmJiB0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsZWUuZXhwcmVzc2lvbikgJiZcblx0XHRcdGNhbGxlZS5leHByZXNzaW9uLm5hbWUudGV4dCA9PT0gJ2ZvcmsnICYmIGlzVXRpbHNPd25lcihjYWxsZWUuZXhwcmVzc2lvbi5leHByZXNzaW9uKSkge1xuXHRcdFx0Ly8gdXRpbHMuZm9yayhpbnN0YW5jZSkoLi4uYXJncykg4oCUIHRoZSBjdXJyaWVkIGZvcm1cblx0XHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGNhbGxlZS5hcmd1bWVudHM7XG5cdFx0XHRzdWJqZWN0QXJnID0gZmlyc3RBcmc7XG5cdFx0fVxuXHRcdGlmICghc3ViamVjdEFyZyB8fCAhdHMuaXNJZGVudGlmaWVyKHN1YmplY3RBcmcpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChzdWJqZWN0QXJnLnRleHQpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXG5cdC8qKlxuXHRcdCogUHJvY2VzcyBhIEBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHQgKi9cblx0cHJpdmF0ZSBwcm9jZXNzRGVjb3JhdGVEZWNvcmF0b3IgKFxuXHRcdGRlY29yYXRvcjogdHMuRGVjb3JhdG9yLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0Y2xhc3NEZWNsUGFyYW0/OiB0cy5DbGFzc0RlY2xhcmF0aW9uXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRkZWNvcmF0b3IuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXG5cdFx0Ly8gR2V0IHRoZSBjbGFzcyBkZWNsYXJhdGlvbiAtIHVzZSB0aGUgcGFzc2VkIGNvbnRleHQgaWYgcGFyZW50IGlzIG5vdCBzZXRcblx0XHRjb25zdCBjbGFzc0RlY2wgPSBkZWNvcmF0b3IucGFyZW50IGFzIHRzLkNsYXNzRGVjbGFyYXRpb24gfCB1bmRlZmluZWQgfHwgY2xhc3NEZWNsUGFyYW07XG5cdFx0aWYgKCFjbGFzc0RlY2wgfHwgIWNsYXNzRGVjbC5uYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdEZWNvcmF0ZWQgY2xhc3MgaGFzIG5vIG5hbWUnLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHR5cGVOYW1lID0gY2xhc3NEZWNsLm5hbWUudGV4dDtcblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdEZWNvcmF0ZWQgY2xhc3MgaGFzIG5vIG5hbWUnLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFBhcnNlIGRlY29yYXRvciBhcmd1bWVudHM6IEBkZWNvcmF0ZSgpLCBAZGVjb3JhdGUoUGFyZW50KSxcblx0XHQvLyBAZGVjb3JhdGUoeyAuLi4gfSksIEBkZWNvcmF0ZShQYXJlbnQsIHsgLi4uIH0pLFxuXHRcdC8vIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSwgQE15Q29sbGVjdGlvbi5kZWNvcmF0ZSh7IC4uLiB9KVxuXHRcdGxldCBwYXJlbnROb2RlOiBUeXBlTm9kZSB8IHVuZGVmaW5lZDtcblx0XHRsZXQgcGFyZW50RnVsbFBhdGg6IHN0cmluZyB8IG51bGwgPSBudWxsO1xuXHRcdGxldCBjb2xsZWN0aW9uSWQ6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRsZXQgZGVjb3JhdG9yQ29uZmlnOiB7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0gPSB7fTtcblxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGRlY29yYXRvci5leHByZXNzaW9uKSkge1xuXHRcdFx0Y29uc3QgY2FsbEV4cHIgPSBkZWNvcmF0b3IuZXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IGNhbGxlZSA9IGNhbGxFeHByLmV4cHJlc3Npb247XG5cblx0XHRcdC8vIENoZWNrIGZvciBATXlDb2xsZWN0aW9uLmRlY29yYXRlKCkgd2hlcmUgTXlDb2xsZWN0aW9uIGlzIGEgY3VzdG9tIGNvbGxlY3Rpb24uXG5cdFx0XHQvLyBUaGUgZGVjb3JhdGVkIGNsYXNzIGJlY29tZXMgYSByb290IHR5cGUgaW4gdGhhdCBjb2xsZWN0aW9uLlxuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsZWUpICYmXG5cdFx0XHRcdGNhbGxlZS5uYW1lLnRleHQgPT09ICdkZWNvcmF0ZScgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGNhbGxlZS5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGNhbGxlZS5leHByZXNzaW9uLnRleHQpXG5cdFx0XHQpIHtcblx0XHRcdFx0Y29sbGVjdGlvbklkID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChjYWxsZWUuZXhwcmVzc2lvbi50ZXh0KTtcblx0XHRcdFx0aWYgKGNhbGxFeHByLmFyZ3VtZW50cy5sZW5ndGggPT09IDEgJiYgdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihjYWxsRXhwci5hcmd1bWVudHNbIDAgXSkpIHtcblx0XHRcdFx0XHRkZWNvcmF0b3JDb25maWcgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjYWxsRXhwci5hcmd1bWVudHNbIDAgXSk7XG5cdFx0XHRcdH1cblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGNvbnN0IGFyZ3MgPSBjYWxsRXhwci5hcmd1bWVudHM7XG5cdFx0XHRcdGxldCBwYXJlbnRBcmc6IHRzLklkZW50aWZpZXIgfCB1bmRlZmluZWQ7XG5cdFx0XHRcdGxldCBjb25maWdBcmc6IHRzLk9iamVjdExpdGVyYWxFeHByZXNzaW9uIHwgdW5kZWZpbmVkO1xuXG5cdFx0XHRcdGZvciAoY29uc3QgYXJnIG9mIGFyZ3MpIHtcblx0XHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdFx0XHRcdGlmIChwYXJlbnRBcmcpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdFx0XHRcdFx0bWVzc2FnZSA6ICdAZGVjb3JhdGUoKSBhY2NlcHRzIG9ubHkgb25lIHBhcmVudCByZWZlcmVuY2UnLFxuXHRcdFx0XHRcdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0XHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0XHRwYXJlbnRBcmcgPSBhcmc7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdFx0XHRcdGlmIChjb25maWdBcmcpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdFx0XHRcdFx0bWVzc2FnZSA6ICdAZGVjb3JhdGUoKSBhY2NlcHRzIG9ubHkgb25lIGNvbmZpZyBvYmplY3QnLFxuXHRcdFx0XHRcdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0XHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0XHRjb25maWdBcmcgPSBhcmc7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0aWYgKHBhcmVudEFyZykge1xuXHRcdFx0XHRcdHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlJZGVudGlmaWVyKHBhcmVudEFyZy50ZXh0KTtcblx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0XHRcdFx0cGFyZW50RnVsbFBhdGggPSBwYXJlbnROb2RlLmZ1bGxQYXRoO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGlmIChjb25maWdBcmcpIHtcblx0XHRcdFx0XHRkZWNvcmF0b3JDb25maWcgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjb25maWdBcmcpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gQnVpbGQgZnVsbCBwYXRoIOKAlCBhIHJvb3QgZGVjb3JhdGVkIGludG8gYSBjdXN0b20gY29sbGVjdGlvblxuXHRcdC8vIGNhcnJpZXMgdGhlIGNvbGxlY3Rpb25JZDo6IHByZWZpeCwgZXhhY3RseSBsaWtlIHRoZSBncmFwaCBub2RlJ3Ncblx0XHQvLyBmdWxsUGF0aDogZGVmaW5pdGlvbnMuanNvbiBrZXlzIG11c3Qgam9pbiBoaWVyYXJjaHkuanNvbiAodGhlXG5cdFx0Ly8gcHJlZml4IHdhcyBkcm9wcGVkIGhlcmUgYmVmb3JlLCBzbyBhIGRlY29yYXRlZCBjb2xsZWN0aW9uIHJvb3Rcblx0XHQvLyBuZXZlciBqb2luZWQpXG5cdFx0Y29uc3QgZnVsbFBhdGggPSBwYXJlbnROb2RlXG5cdFx0XHQ/IGAke3BhcmVudE5vZGUuZnVsbFBhdGh9LiR7dHlwZU5hbWV9YFxuXHRcdFx0OiBjb2xsZWN0aW9uSWRcblx0XHRcdFx0PyBgJHtjb2xsZWN0aW9uSWR9Ojoke3R5cGVOYW1lfWBcblx0XHRcdFx0OiB0eXBlTmFtZTtcblxuXHRcdC8vIENyZWF0ZSBkZWZpbml0aW9uIGluZm8gZm9yIGRlY29yYXRlXG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IHR5cGVOYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlY29yYXRlJyxcblx0XHRcdHBhcmVudCAgICAgIDogcGFyZW50RnVsbFBhdGgsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IGRlY29yYXRvckNvbmZpZy5zdHJpY3RDaGFpbiA/PyB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBkZWNvcmF0b3JDb25maWcuYmxvY2tFcnJvcnMgPz8gZmFsc2UsXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChmdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdFx0dGhpcy5lZHNTY29wZUJ5Tm9kZS5zZXQoY2xhc3NEZWNsLCBmdWxsUGF0aCk7XG5cblx0XHQvLyBDcmVhdGUgdHlwZSBub2RlXG5cdFx0Y29uc3Qgbm9kZSA9IFR5cGVHcmFwaEltcGwuY3JlYXRlTm9kZShcblx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0cGFyZW50Tm9kZSxcblx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRsaW5lICsgMSxcblx0XHRcdGNoYXJhY3RlciArIDEsXG5cdFx0XHRjb2xsZWN0aW9uSWRcblx0XHQpO1xuXHRcdHRoaXMuYXBwbHlDb2xsZWN0aW9uRW1pc3Npb25JbmZvKG5vZGUsIG5vZGUuY29sbGVjdGlvbklkKTtcblxuXHRcdC8vIFNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZSBkZXRlY3Rpb24gKGhhcmQtZmFpbCBsYXcpXG5cdFx0dGhpcy5yZWNvcmREZWZpbmVTaXRlKFxuXHRcdFx0cGFyZW50Tm9kZSA/IGAke3BhcmVudE5vZGUuZnVsbFBhdGh9LiR7dHlwZU5hbWV9YCA6IGAke2NvbGxlY3Rpb25JZCA/PyAnZGVmYXVsdCd9Ojoke3R5cGVOYW1lfWAsXG5cdFx0XHRgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YFxuXHRcdCk7XG5cblx0XHQvLyBFeHRyYWN0IHByb3BlcnRpZXMgYW5kIGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBjbGFzcyBtZW1iZXJzIOKAlFxuXHRcdC8vIHRoZSBuZXcgbm9kZSBhbmNob3JzIHJlbGF0aXZlLWZpcnN0IGdyYXBoIHJlZmVyZW5jZSByZXNvbHV0aW9uXG5cdFx0Y29uc3QgcHJldmlvdXNBbmNob3IgPSB0aGlzLmN1cnJlbnRHcmFwaEFuY2hvcjtcblx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IG5vZGU7XG5cdFx0dHJ5IHtcblx0XHRcdG5vZGUucHJvcGVydGllcyA9IHRoaXMuZXh0cmFjdENsYXNzUHJvcGVydGllcyhjbGFzc0RlY2wpO1xuXHRcdFx0bm9kZS5jb25zdHJ1Y3RvclBhcmFtcyA9IHRoaXMuZXh0cmFjdENsYXNzQ29uc3RydWN0b3JQYXJhbXMoY2xhc3NEZWNsKTtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBwcmV2aW91c0FuY2hvcjtcblx0XHR9XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGhcblx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChwYXJlbnROb2RlLCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KG5vZGUpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHR5cGUgbmFtZSBmcm9tIGRlZmluZSgpIGNhbGwgYXJndW1lbnRzLlxuXHQgKiBIYW5kbGVzOlxuXHQgKiAgIGRlZmluZSgnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHQgKiAgIGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpICAgLy8gZXhwbGljaXQtc291cmNlIGZvcm1cblx0ICogICBkZWZpbmUoZnVuY3Rpb24gVHlwZU5hbWUoKSB7fSlcblx0ICogICBkZWZpbmUoKCkgPT4gY2xhc3MgVHlwZU5hbWUge30pXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RUeXBlTmFtZSAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGFyZ3MgPSBjYWxsLmFyZ3VtZW50cztcblxuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBhcmdzO1xuXG5cdFx0Ly8gRXhwbGljaXQtc291cmNlIGZvcm06IGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIgJiYgdHMuaXNJZGVudGlmaWVyKGZpcnN0QXJnKSAmJiB0cy5pc1N0cmluZ0xpdGVyYWwoYXJnc1sgMSBdKSkge1xuXHRcdFx0cmV0dXJuIGFyZ3NbIDEgXS50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIFN0cmluZyBsaXRlcmFsOiBkZWZpbmUoJ1R5cGVOYW1lJywgLi4uKVxuXHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoZmlyc3RBcmcpKSB7XG5cdFx0XHRyZXR1cm4gZmlyc3RBcmcudGV4dDtcblx0XHR9XG5cblx0XHQvLyBGdW5jdGlvbiB3aXRoIG5hbWU6IGRlZmluZShmdW5jdGlvbiBUeXBlTmFtZSgpIHt9KVxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihmaXJzdEFyZykgJiYgZmlyc3RBcmcubmFtZSkge1xuXHRcdFx0cmV0dXJuIGZpcnN0QXJnLm5hbWUudGV4dDtcblx0XHR9XG5cblx0XHQvLyBBcnJvdyBmdW5jdGlvbiByZXR1cm5pbmcgY2xhc3M6IGRlZmluZSgoKSA9PiBjbGFzcyBUeXBlTmFtZSB7fSlcblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGZpcnN0QXJnKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBmaXJzdEFyZztcblx0XHRcdGlmICh0cy5pc0NsYXNzRXhwcmVzc2lvbihib2R5KSAmJiBib2R5Lm5hbWUpIHtcblx0XHRcdFx0cmV0dXJuIGJvZHkubmFtZS50ZXh0O1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGNvbXB1dGVkIGRlZmluZSBuYW1lIG9ubHkgd2hlbiBpdCByYW5nZXMgb3ZlciBhIGNsb3NlZCBjb25zdFxuXHQgKiBvYmplY3Qga2V5IHNldC4gQXJiaXRyYXJ5IHN0cmluZ3MgYW5kIHVucmVzb2x2ZWQgdW5pb25zIHN0YXkgb24gdGhlXG5cdCAqIGV4aXN0aW5nIHdhcm5pbmctYW5kLXNraXAgcGF0aC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENvbXB1dGVkVHlwZU5hbWVzIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZ1tdIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblx0XHRpZiAoIWZpcnN0QXJnIHx8ICF0cy5pc0lkZW50aWZpZXIoZmlyc3RBcmcpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBsb29wTmFtZXMgPSB0aGlzLnJlc29sdmVMb29wS2V5TmFtZXMoZmlyc3RBcmcpO1xuXHRcdGlmIChsb29wTmFtZXMgIT09IHVuZGVmaW5lZCkge1xuXHRcdFx0cmV0dXJuIGxvb3BOYW1lcztcblx0XHR9XG5cdFx0Y29uc3QgcGFyYW1ldGVyTmFtZXMgPSB0aGlzLnJlc29sdmVQYXJhbWV0ZXJLZXlOYW1lcyhmaXJzdEFyZywgY2FsbC5nZXRTb3VyY2VGaWxlKCkpO1xuXHRcdHJldHVybiBwYXJhbWV0ZXJOYW1lcztcblx0fVxuXG5cdHByaXZhdGUgcmVzb2x2ZUxvb3BLZXlOYW1lcyAobmFtZTogdHMuSWRlbnRpZmllcik6IHN0cmluZ1tdIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5hbWUucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNGb3JPZlN0YXRlbWVudChjdXJyZW50KSAmJiB0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb25MaXN0KGN1cnJlbnQuaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRcdGNvbnN0IGRlY2xhcmF0aW9uID0gY3VycmVudC5pbml0aWFsaXplci5kZWNsYXJhdGlvbnMuZmluZChjYW5kaWRhdGUgPT5cblx0XHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoY2FuZGlkYXRlLm5hbWUpICYmIGNhbmRpZGF0ZS5uYW1lLnRleHQgPT09IG5hbWUudGV4dCk7XG5cdFx0XHRcdGlmIChkZWNsYXJhdGlvbikge1xuXHRcdFx0XHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMucmVzb2x2ZU9iamVjdEtleXNDYWxsKGN1cnJlbnQuZXhwcmVzc2lvbiwgY3VycmVudC5nZXRTb3VyY2VGaWxlKCkpO1xuXHRcdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdHByaXZhdGUgcmVzb2x2ZU9iamVjdEtleXNDYWxsIChleHByZXNzaW9uOiB0cy5FeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogc3RyaW5nW10gfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihleHByZXNzaW9uKSB8fCAhdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcmVzc2lvbi5leHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgYWNjZXNzID0gZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdGNvbnN0IFsgYXJndW1lbnQgXSA9IGV4cHJlc3Npb24uYXJndW1lbnRzO1xuXHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGFjY2Vzcy5leHByZXNzaW9uKSB8fCBhY2Nlc3MuZXhwcmVzc2lvbi50ZXh0ICE9PSAnT2JqZWN0JyB8fFxuXHRcdFx0YWNjZXNzLm5hbWUudGV4dCAhPT0gJ2tleXMnIHx8ICFhcmd1bWVudCB8fCAhdHMuaXNJZGVudGlmaWVyKGFyZ3VtZW50KSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5yZXNvbHZlQ29uc3RPYmplY3RLZXlzKGFyZ3VtZW50LnRleHQsIHNvdXJjZUZpbGUpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHRwcml2YXRlIHJlc29sdmVQYXJhbWV0ZXJLZXlOYW1lcyAobmFtZTogdHMuSWRlbnRpZmllciwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHN0cmluZ1tdIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5hbWUucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNGdW5jdGlvbkxpa2UoY3VycmVudCkpIHtcblx0XHRcdFx0Y29uc3QgcGFyYW1ldGVyID0gY3VycmVudC5wYXJhbWV0ZXJzLmZpbmQoY2FuZGlkYXRlID0+XG5cdFx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGNhbmRpZGF0ZS5uYW1lKSAmJiBjYW5kaWRhdGUubmFtZS50ZXh0ID09PSBuYW1lLnRleHQpO1xuXHRcdFx0XHRpZiAocGFyYW1ldGVyKSB7XG5cdFx0XHRcdFx0aWYgKCFwYXJhbWV0ZXIudHlwZSkge1xuXHRcdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5yZXNvbHZlS2V5b2ZUeXBlKHBhcmFtZXRlci50eXBlLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHRwcml2YXRlIHJlc29sdmVLZXlvZlR5cGUgKHR5cGVOb2RlOiB0cy5UeXBlTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHN0cmluZ1tdIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNQYXJlbnRoZXNpemVkVHlwZU5vZGUodHlwZU5vZGUpKSB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnJlc29sdmVLZXlvZlR5cGUodHlwZU5vZGUudHlwZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH1cblx0XHRpZiAodHMuaXNUeXBlT3BlcmF0b3JOb2RlKHR5cGVOb2RlKSAmJiB0eXBlTm9kZS5vcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5LZXlPZktleXdvcmQpIHtcblx0XHRcdGNvbnN0IHF1ZXJpZWQgPSB0eXBlTm9kZS50eXBlO1xuXHRcdFx0aWYgKHRzLmlzVHlwZVF1ZXJ5Tm9kZShxdWVyaWVkKSAmJiB0cy5pc0lkZW50aWZpZXIocXVlcmllZC5leHByTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5yZXNvbHZlQ29uc3RPYmplY3RLZXlzKHF1ZXJpZWQuZXhwck5hbWUudGV4dCwgc291cmNlRmlsZSk7XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZSh0eXBlTm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKHR5cGVOb2RlLnR5cGVOYW1lKSkge1xuXHRcdFx0Y29uc3QgcmVmZXJlbmNlZE5hbWUgPSB0eXBlTm9kZS50eXBlTmFtZS50ZXh0O1xuXHRcdFx0Y29uc3QgYWxpYXMgPSBzb3VyY2VGaWxlLnN0YXRlbWVudHMuZmluZCgoc3RhdGVtZW50KTogc3RhdGVtZW50IGlzIHRzLlR5cGVBbGlhc0RlY2xhcmF0aW9uID0+XG5cdFx0XHRcdHRzLmlzVHlwZUFsaWFzRGVjbGFyYXRpb24oc3RhdGVtZW50KSAmJiBzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSByZWZlcmVuY2VkTmFtZSk7XG5cdFx0XHRpZiAoYWxpYXMpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5yZXNvbHZlS2V5b2ZUeXBlKGFsaWFzLnR5cGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0cHJpdmF0ZSByZXNvbHZlQ29uc3RPYmplY3RLZXlzIChuYW1lOiBzdHJpbmcsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiBzdHJpbmdbXSB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc291cmNlRmlsZS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAoIXRzLmlzVmFyaWFibGVTdGF0ZW1lbnQoc3RhdGVtZW50KSB8fFxuXHRcdFx0XHQoc3RhdGVtZW50LmRlY2xhcmF0aW9uTGlzdC5mbGFncyAmIHRzLk5vZGVGbGFncy5Db25zdCkgPT09IDApIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGRlY2xhcmF0aW9uIG9mIHN0YXRlbWVudC5kZWNsYXJhdGlvbkxpc3QuZGVjbGFyYXRpb25zKSB7XG5cdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGRlY2xhcmF0aW9uLm5hbWUpIHx8IGRlY2xhcmF0aW9uLm5hbWUudGV4dCAhPT0gbmFtZSB8fFxuXHRcdFx0XHRcdCFkZWNsYXJhdGlvbi5pbml0aWFsaXplciB8fCAhdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihkZWNsYXJhdGlvbi5pbml0aWFsaXplcikpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBuYW1lczogc3RyaW5nW10gPSBbXTtcblx0XHRcdFx0Zm9yIChjb25zdCBwcm9wZXJ0eSBvZiBkZWNsYXJhdGlvbi5pbml0aWFsaXplci5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdFx0aWYgKCF0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wZXJ0eSkgfHxcblx0XHRcdFx0XHRcdCghdHMuaXNJZGVudGlmaWVyKHByb3BlcnR5Lm5hbWUpICYmICF0cy5pc1N0cmluZ0xpdGVyYWwocHJvcGVydHkubmFtZSkpKSB7XG5cdFx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRuYW1lcy5wdXNoKHByb3BlcnR5Lm5hbWUudGV4dCk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIG5hbWVzO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdGhlIGZ1bGwgZGVmaW5lKCkgY2FsbCBjb250ZXh0OiB0eXBlIG5hbWUsIHBhcmVudCB0eXBlLCBhbmQgY29sbGVjdGlvbi5cblx0ICogSGFuZGxlcyBkaXJlY3QgY2FsbHMsIHByb3BlcnR5LWFjY2VzcyBjYWxscywgY2hhaW5lZCBjYWxscywgYW5kIHRoZVxuXHQgKiBleHBsaWNpdC1zb3VyY2UgZm9ybSBgZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilgLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0RGVmaW5lQ29udGV4dCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHR5cGVOYW1lT3ZlcnJpZGU/OiBzdHJpbmcpOiB7XG5cdFx0dHlwZU5hbWU/OiBzdHJpbmc7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Y29uc3QgdHlwZU5hbWUgPSB0eXBlTmFtZU92ZXJyaWRlID8/IHRoaXMuZXh0cmFjdFR5cGVOYW1lKGNhbGwpO1xuXHRcdGlmICghdHlwZU5hbWUpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IGNhbGw7XG5cblx0XHQvLyBEaXJlY3QgY2FsbDogZGVmaW5lKCdUeXBlTmFtZScsIC4uLikgb3IgZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2RlZmluZScpIHtcblx0XHRcdC8vIEV4cGxpY2l0LXNvdXJjZSBmb3JtOiBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHRcdFx0aWYgKGNhbGwuYXJndW1lbnRzLmxlbmd0aCA+PSAyICYmIHRzLmlzSWRlbnRpZmllcihjYWxsLmFyZ3VtZW50c1sgMCBdKSkge1xuXHRcdFx0XHRjb25zdCBzb3VyY2VOYW1lID0gY2FsbC5hcmd1bWVudHNbIDAgXS50ZXh0O1xuXHRcdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKHNvdXJjZU5hbWUpO1xuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0XHRcdHBhcmVudFR5cGUgICA6IHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSxcblx0XHRcdFx0XHRjb2xsZWN0aW9uSWQgOiBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCxcblx0XHRcdFx0fTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gUGxhaW4gcm9vdCBkZWZpbmUgaW4gZGVmYXVsdCBjb2xsZWN0aW9uXG5cdFx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2VzczogWC5kZWZpbmUoJ1R5cGVOYW1lJywgLi4uKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLm5hbWUudGV4dCA9PT0gJ2RlZmluZScpIHtcblx0XHRcdGNvbnN0IG9iaiA9IGV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblxuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihvYmopKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uob2JqLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0XHRcdHBhcmVudFR5cGUgICA6IHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSxcblx0XHRcdFx0XHRjb2xsZWN0aW9uSWQgOiBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCxcblx0XHRcdFx0fTtcblx0XHRcdH1cblxuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gTmVzdGVkIGFjY2VzczogaW5zdGFuY2UuVHlwZS5kZWZpbmUgLSB0cnkgdG8gcmVzb2x2ZVxuXHRcdFx0XHRjb25zdCBjaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlDaGFpbihvYmopO1xuXHRcdFx0XHRpZiAoY2hhaW4ubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGNoYWluLmpvaW4oJy4nKSk7XG5cdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlIH07XG5cdFx0XHRcdH1cblx0XHRcdH1cblxuXHRcdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBEZXRlcm1pbmUgdGhlIGNvbGxlY3Rpb24gY29udGV4dCBmcm9tIHRoZSByb290IG9mIHRoZSBjaGFpbiBzbyB0aGF0XG5cdFx0XHRcdC8vIGN1c3RvbS1jb2xsZWN0aW9uIHR5cGVzIGRvIG5vdCBnZXQgY29uZnVzZWQgd2l0aCBkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMuXG5cdFx0XHRcdGNvbnN0IHJvb3RJZCA9IHRoaXMuZ2V0Um9vdElkZW50aWZpZXIob2JqLmV4cHJlc3Npb24pO1xuXHRcdFx0XHRjb25zdCBleHBlY3RlZENvbGxlY3Rpb25JZCA9IHJvb3RJZFxuXHRcdFx0XHRcdD8gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKHJvb3RJZC50ZXh0KS5jb2xsZWN0aW9uSWRcblx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblxuXHRcdFx0XHQvLyBDaGFpbmVkIGNhbGw6IGRlZmluZSgnQScpLmRlZmluZSgnQicpIG9yIG1uZW1vbmljYS5kZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKVxuXHRcdFx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwob2JqKSkge1xuXHRcdFx0XHRcdHRoaXMucHJvY2Vzc0RlZmluZUNhbGwob2JqLCBjYWxsLmdldFNvdXJjZUZpbGUoKSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdC8vIEluaGVyaXQgY29sbGVjdGlvbiBmcm9tIHRoZSBwYXJlbnQgdHlwZSAoaWYgYW55KVxuXHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBDaGFpbmVkIGxhenkgY2FsbDogbGF6eSgnQScpLmRlZmluZSgnQicpIG9yIFR5cGUubGF6eSgnQScpLmRlZmluZSgnQicpXG5cdFx0XHRcdGlmICh0aGlzLmlzTGF6eUNhbGwob2JqKSkge1xuXHRcdFx0XHRcdHRoaXMucHJvY2Vzc0xhenlDYWxsKG9iaiwgY2FsbC5nZXRTb3VyY2VGaWxlKCkpO1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudFR5cGVOYW1lID0gdGhpcy5leHRyYWN0TW5lbW9uaWNhVHlwZU5hbWUob2JqKTtcblx0XHRcdFx0XHRpZiAocGFyZW50VHlwZU5hbWUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKHBhcmVudFR5cGVOYW1lLCBleHBlY3RlZENvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIEJ1aWxkZXIgbG9va3VwIGNoYWluOiBBcHAubG9va3VwKCdVc2VyJykuZGVmaW5lKCdBZG1pbicpXG5cdFx0XHRcdGlmICh0aGlzLmlzTG9va3VwQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0Y29uc3QgbG9va2VkVXBQYXRoID0gdGhpcy5yZXNvbHZlTG9va3VwUGF0aChvYmopO1xuXHRcdFx0XHRcdGlmIChsb29rZWRVcFBhdGgpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGxvb2tlZFVwUGF0aCk7XG5cdFx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGUuY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHsgdHlwZU5hbWUgfTtcblx0fVxuXG5cdC8qKlxuXHQgKiBQcmVmaXggYSBkb3R0ZWQgdHlwZSBwYXRoIHdpdGggYSBjb2xsZWN0aW9uIGlkZW50aWZpZXIgc28gY3VzdG9tLWNvbGxlY3Rpb25cblx0ICogdHlwZXMgZG8gbm90IGNvbGxpZGUgd2l0aCBkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMgaW4gdGhlIGdyYXBoLlxuXHQgKi9cblx0cHJpdmF0ZSBwcmVmaXhDb2xsZWN0aW9uUGF0aCAocGF0aDogc3RyaW5nLCBjb2xsZWN0aW9uSWQ6IHN0cmluZyk6IHN0cmluZyB7XG5cdFx0cmV0dXJuIGAke2NvbGxlY3Rpb25JZH06OiR7cGF0aH1gO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSBkZWZpbmUoKSBzb3VyY2UgaWRlbnRpZmllciB0byBlaXRoZXIgYSBwYXJlbnQgdHlwZSwgYSBjb2xsZWN0aW9uLFxuXHQgKiBvciB0aGUgZGVmYXVsdCAobW9kdWxlIG9iamVjdCkgY29sbGVjdGlvbi5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZURlZmluZVNvdXJjZSAoc291cmNlTmFtZTogc3RyaW5nKToge1xuXHRcdHBhcmVudFR5cGU/OiBUeXBlTm9kZTtcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmc7XG5cdH0ge1xuXHRcdC8vIE1vZHVsZSBvYmplY3QgYWxpYXNlcyAtPiByb290IGluIGRlZmF1bHQgY29sbGVjdGlvblxuXHRcdGlmICh0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoc291cmNlTmFtZSkpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHQvLyBDb2xsZWN0aW9uIHZhcmlhYmxlcyAtPiByb290IGluIHRoYXQgY29sbGVjdGlvblxuXHRcdGNvbnN0IGNvbGxlY3Rpb25JZCA9IHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5nZXQoc291cmNlTmFtZSk7XG5cdFx0aWYgKGNvbGxlY3Rpb25JZCkge1xuXHRcdFx0cmV0dXJuIHsgY29sbGVjdGlvbklkIH07XG5cdFx0fVxuXG5cdFx0Ly8gT3RoZXJ3aXNlIHRyZWF0IGFzIGEgdHlwZSB2YXJpYWJsZSByZWZlcmVuY2Vcblx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5SWRlbnRpZmllcihzb3VyY2VOYW1lKTtcblx0XHRyZXR1cm4geyBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdH1cblxuXHQvKipcblx0ICogQ2hlY2sgaWYgYSBjYWxsIGV4cHJlc3Npb24gaXMgYSBsb29rdXAoKSBjYWxsLlxuXHQgKi9cblx0cHJpdmF0ZSBpc0xvb2t1cENhbGwgKG5vZGU6IHRzLkNhbGxFeHByZXNzaW9uKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgZXhwciA9IG5vZGUuZXhwcmVzc2lvbjtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpICYmIGV4cHIudGV4dCA9PT0gJ2xvb2t1cCcpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikgJiYgZXhwci5uYW1lLnRleHQgPT09ICdsb29rdXAnKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSBsb29rdXAoKSBjYWxsIHRvIGEgZG90dGVkIHR5cGUgcGF0aCAoYmVzdCBlZmZvcnQpLlxuXHQgKiBIYW5kbGVzOlxuXHQgKiAgIGxvb2t1cCgnVXNlcicpXG5cdCAqICAgbG9va3VwKHNvdXJjZSwgJ1VzZXInKVxuXHQgKiAgIEFwcC5sb29rdXAoJ1VzZXInKVxuXHQgKiAgIGNvbGxlY3Rpb24ubG9va3VwKCdVc2VyLkFkbWluJylcblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUxvb2t1cFBhdGggKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBhcmdzID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIFNpbmdsZS1hcmcgbG9va3VwOiBsb29rdXAoJ1VzZXInKSBvciBBcHAubG9va3VwKCdVc2VyJylcblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDEpIHtcblx0XHRcdGNvbnN0IFsgYXJnIF0gPSBhcmdzO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChhcmcpIHx8IHRzLmlzTm9TdWJzdGl0dXRpb25UZW1wbGF0ZUxpdGVyYWwoYXJnKSkge1xuXHRcdFx0XHRjb25zdCBwYXRoID0gYXJnLnRleHQ7XG5cdFx0XHRcdC8vIElmIHRoaXMgaXMgYSBtZXRob2QgY2FsbCBvbiBhIHNvdXJjZSwgcmVzb2x2ZSByZWxhdGl2ZSB0byB0aGF0IHNvdXJjZS5cblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRjb25zdCBzb3VyY2VFeHByID0gY2FsbC5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihzb3VyY2VFeHByKSkge1xuXHRcdFx0XHRcdFx0Y29uc3Qgc291cmNlTmFtZSA9IHNvdXJjZUV4cHIudGV4dDtcblx0XHRcdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRcdFx0XHRpZiAoc291cmNlQ29udGV4dC5wYXJlbnRUeXBlKSB7XG5cdFx0XHRcdFx0XHRcdC8vIFR5cGUgbG9va3VwOiByZWxhdGl2ZSBmaXJzdCwgdGhlbiByb290IGZhbGxiYWNrLlxuXHRcdFx0XHRcdFx0XHQvLyBGb3IgYSB0eXBlIGluc2lkZSBhIGN1c3RvbSBjb2xsZWN0aW9uIHRoZSBmYWxsYmFjayByb290IGlzXG5cdFx0XHRcdFx0XHRcdC8vIHRoZSBjb2xsZWN0aW9uIHJvb3QsIG5ldmVyIHRoZSBkZWZhdWx0IGNvbGxlY3Rpb24uXG5cdFx0XHRcdFx0XHRcdGNvbnN0IHJlbGF0aXZlUGF0aCA9IGAke3NvdXJjZUNvbnRleHQucGFyZW50VHlwZS5mdWxsUGF0aH0uJHtwYXRofWA7XG5cdFx0XHRcdFx0XHRcdGlmICh0aGlzLmdyYXBoLmZpbmRUeXBlKHJlbGF0aXZlUGF0aCkpIHtcblx0XHRcdFx0XHRcdFx0XHRyZXR1cm4gcmVsYXRpdmVQYXRoO1xuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRcdGlmIChzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCkge1xuXHRcdFx0XHRcdFx0XHRcdHJldHVybiB0aGlzLnByZWZpeENvbGxlY3Rpb25QYXRoKHBhdGgsIHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdGlmIChzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCkge1xuXHRcdFx0XHRcdFx0XHQvLyBDb2xsZWN0aW9uIGxvb2t1cDogcHJlZml4IHBhdGggd2l0aCB0aGUgY29sbGVjdGlvbiBpZFxuXHRcdFx0XHRcdFx0XHRyZXR1cm4gdGhpcy5wcmVmaXhDb2xsZWN0aW9uUGF0aChwYXRoLCBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiBwYXRoO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBUd28tYXJnIGxvb2t1cDogbG9va3VwKHNvdXJjZSwgJ1VzZXInKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA+PSAyKSB7XG5cdFx0XHRjb25zdCBbIHNvdXJjZUFyZywgcGF0aEFyZyBdID0gYXJncztcblx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHNvdXJjZUFyZykgfHwgIXRzLmlzU3RyaW5nTGl0ZXJhbChwYXRoQXJnKSkge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgc291cmNlTmFtZSA9IHNvdXJjZUFyZy50ZXh0O1xuXHRcdFx0Y29uc3QgcGF0aCA9IHBhdGhBcmcudGV4dDtcblx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRpZiAoc291cmNlQ29udGV4dC5wYXJlbnRUeXBlKSB7XG5cdFx0XHRcdC8vIFNhbWUgcmVsYXRpdmUtZmlyc3QgbGF3IGFzIHRoZSBzaW5nbGUtYXJnIGZvcm07IGNvbGxlY3Rpb25cblx0XHRcdFx0Ly8gbWVtYmVycyBmYWxsIGJhY2sgdG8gdGhlaXIgY29sbGVjdGlvbiByb290LCBub3QgdGhlIGdsb2JhbCBvbmUuXG5cdFx0XHRcdGNvbnN0IHJlbGF0aXZlUGF0aCA9IGAke3NvdXJjZUNvbnRleHQucGFyZW50VHlwZS5mdWxsUGF0aH0uJHtwYXRofWA7XG5cdFx0XHRcdGlmICh0aGlzLmdyYXBoLmZpbmRUeXBlKHJlbGF0aXZlUGF0aCkpIHtcblx0XHRcdFx0XHRyZXR1cm4gcmVsYXRpdmVQYXRoO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCkge1xuXHRcdFx0XHRcdHJldHVybiB0aGlzLnByZWZpeENvbGxlY3Rpb25QYXRoKHBhdGgsIHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdH1cblx0XHRcdGlmIChzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCkge1xuXHRcdFx0XHRyZXR1cm4gdGhpcy5wcmVmaXhDb2xsZWN0aW9uUGF0aChwYXRoLCBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCk7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gcGF0aDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIExvb2t1cC1sYXcgZGVsZWdhdGUgZm9yIHRoZSBsb2NhbC1zY29wZSB3YWxrZXIgKHNjb3Blcy5qc29uIHR5cGVQYXRoXG5cdCAqIG1ldGFkYXRhKTogcmVzb2x2ZSBhIGxvb2t1cCgpIGluaXRpYWxpemVyIGNhbGwgdGhyb3VnaCBleGFjdGx5IHRoZVxuXHQgKiB0aWVycyB0aGUgdXNhZ2VzIHBhc3MgcmVzb2x2ZWQgaXQgYWdhaW5zdCAoc2FtZSBzb3VyY2UgcmVzb2x1dGlvbixcblx0ICogc2FtZSBjb21wbGV0ZSBncmFwaCkuIFRoZSB3YWxrZXIgcnVucyBpdHMgb3duIHNjb3BlLWNoYWluIHZhbHVlLXNjb3BlXG5cdCAqIHRpZXIgYmVmb3JlIGRlbGVnYXRpbmc7IGV2ZXJ5dGhpbmcgYWJvdmUgdmFsdWUgc2NvcGUgbGFuZHMgaGVyZSwgc29cblx0ICogc2NvcGVzLmpzb24gbmV2ZXIgZGlzYWdyZWVzIHdpdGggdGhlIGhhcmQtZmFpbC1sYXcgdmVyZGljdHMuXG5cdCAqL1xuXHRyZXNvbHZlTG9va3VwQ2FsbFBhdGggKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKGNhbGwpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHQqIEZpbmQgYSBwYXJlbnQgdHlwZSBieSBpdHMgbmFtZSwgc2VhcmNoaW5nIGluIHRoZSBncmFwaC5cblx0XHQqIFdoZW4gY29sbGVjdGlvbklkIGlzIHByb3ZpZGVkLCBvbmx5IHR5cGVzIGZyb20gdGhhdCBjb2xsZWN0aW9uIGFyZSBjb25zaWRlcmVkLlxuXHRcdCovXG5cdHByaXZhdGUgZmluZFBhcmVudFR5cGVCeU5hbWUgKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmdcblx0KTogVHlwZU5vZGUgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IG1hdGNoZXNDb2xsZWN0aW9uID0gKHR5cGU6IFR5cGVOb2RlKTogYm9vbGVhbiA9PiB7XG5cdFx0XHRpZiAoY29sbGVjdGlvbklkID09PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0cmV0dXJuIHR5cGUuY29sbGVjdGlvbklkID09PSB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdHlwZS5jb2xsZWN0aW9uSWQgPT09IGNvbGxlY3Rpb25JZDtcblx0XHR9O1xuXG5cdFx0Ly8gRmlyc3QgdHJ5IGV4YWN0IG1hdGNoIChkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMgdXNlIHRoZSBwbGFpbiBkb3R0ZWQgcGF0aClcblx0XHRjb25zdCBleGFjdCA9IHRoaXMuZ3JhcGguZmluZFR5cGUobmFtZSk7XG5cdFx0aWYgKGV4YWN0ICYmIG1hdGNoZXNDb2xsZWN0aW9uKGV4YWN0KSkge1xuXHRcdFx0cmV0dXJuIGV4YWN0O1xuXHRcdH1cblxuXHRcdC8vIFRoZW4gc2VhcmNoIHRocm91Z2ggYWxsIHR5cGVzIGZvciBvbmUgd2l0aCBtYXRjaGluZyBuYW1lIGFuZCBjb2xsZWN0aW9uXG5cdFx0Zm9yIChjb25zdCB0eXBlIG9mIHRoaXMuZ3JhcGguZ2V0QWxsVHlwZXMoKSkge1xuXHRcdFx0aWYgKHR5cGUubmFtZSA9PT0gbmFtZSAmJiBtYXRjaGVzQ29sbGVjdGlvbih0eXBlKSkge1xuXHRcdFx0XHRyZXR1cm4gdHlwZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBGaW5kIGEgcGFyZW50IHR5cGUgZnJvbSBhbiBpZGVudGlmaWVyIHJlZmVyZW5jZS5cblx0XHQqIEhhbmRsZXMgYm90aCBhbGlhc2VkIHZhcmlhYmxlcyAoY29uc3QgVXNlciA9IGRlZmluZSgnVXNlckVudGl0eScsIC4uLikpXG5cdFx0KiBhbmQgZGlyZWN0IGNsYXNzL3R5cGUgbmFtZXMuXG5cdFx0Ki9cblx0cHJpdmF0ZSBmaW5kUGFyZW50VHlwZUJ5SWRlbnRpZmllciAobmFtZTogc3RyaW5nKTogVHlwZU5vZGUgfCB1bmRlZmluZWQge1xuXHRcdC8vIEZpcnN0IGNoZWNrIHZhcmlhYmxlIG1hcHBpbmc6IGNvbnN0IFVzZXIgPSBkZWZpbmUoJ1VzZXJFbnRpdHknLCAuLi4pXG5cdFx0Y29uc3QgbWFwcGVkRnVsbFBhdGggPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChuYW1lKTtcblx0XHRpZiAobWFwcGVkRnVsbFBhdGgpIHtcblx0XHRcdGNvbnN0IG1hcHBlZE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKG1hcHBlZEZ1bGxQYXRoKTtcblx0XHRcdGlmIChtYXBwZWROb2RlKSByZXR1cm4gbWFwcGVkTm9kZTtcblx0XHR9XG5cblx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShuYW1lKTtcblx0XHRyZXR1cm4gcGFyZW50Tm9kZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgdGhlIGxlZnRtb3N0IGlkZW50aWZpZXIgb2YgYSBwcm9wZXJ0eS1hY2Nlc3MgY2hhaW4uXG5cdCAqIEZvciBgQXBwLmRlZmluZSgnVXNlcicpLmRlZmluZSgnQWRtaW4nKWAgdGhpcyByZXR1cm5zIHRoZSBgQXBwYCBpZGVudGlmaWVyLlxuXHQgKi9cblx0cHJpdmF0ZSBnZXRSb290SWRlbnRpZmllciAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHRzLklkZW50aWZpZXIgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5FeHByZXNzaW9uID0gZXhwcjtcblx0XHR3aGlsZSAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY3VycmVudCkpIHtcblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0fVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudCkpIHtcblx0XHRcdHJldHVybiBjdXJyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBHZXQgcHJvcGVydHkgY2hhaW4gZnJvbSBuZXN0ZWQgYWNjZXNzXG5cdFx0Ki9cblx0cHJpdmF0ZSBnZXRQcm9wZXJ0eUNoYWluIChleHByOiB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24gfCB0cy5JZGVudGlmaWVyKTogc3RyaW5nW10ge1xuXHRcdGNvbnN0IGNoYWluOiBzdHJpbmdbXSA9IFtdO1xuXG5cdFx0bGV0IGN1cnJlbnQ6IHRzLkV4cHJlc3Npb24gPSBleHByO1xuXHRcdHdoaWxlICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0aWYgKGN1cnJlbnQubmFtZSkge1xuXHRcdFx0XHRjaGFpbi51bnNoaWZ0KGN1cnJlbnQubmFtZS50ZXh0KTtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0fVxuXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50KSkge1xuXHRcdFx0Y2hhaW4udW5zaGlmdChjdXJyZW50LnRleHQpO1xuXHRcdH1cblxuXHRcdHJldHVybiBjaGFpbjtcblx0fVxuXG5cdHByaXZhdGUgZmluZENvbnN0cnVjdG9ySW5Nb2R1bGUgKFxuXHRcdG1vZHVsZVBhdGg6IHN0cmluZyxcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0ZGVwdGg6IG51bWJlclxuXHQpOiBDb25zdHJ1Y3RvckhhbmRsZXIgfCB1bmRlZmluZWQge1xuXHRcdGlmIChkZXB0aCA+IE1BWF9SRUVYUE9SVF9DSEFTRV9ERVBUSCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBiaW5kaW5ncyA9IHRoaXMuY29uc3RydWN0b3JCaW5kaW5ncy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0Y29uc3QgZGlyZWN0ID0gYmluZGluZ3M/LmdldChuYW1lKTtcblx0XHRpZiAoZGlyZWN0KSB7XG5cdFx0XHRyZXR1cm4gZGlyZWN0O1xuXHRcdH1cblx0XHRjb25zdCBsb2NhbEFsaWFzID0gdGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydEFsaWFzZXMuZ2V0KG1vZHVsZVBhdGgpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGxvY2FsQWxpYXMpIHtcblx0XHRcdGNvbnN0IGFsaWFzZWQgPSBiaW5kaW5ncz8uZ2V0KGxvY2FsQWxpYXMpO1xuXHRcdFx0aWYgKGFsaWFzZWQpIHtcblx0XHRcdFx0cmV0dXJuIGFsaWFzZWQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVFeHBvcnRTcGVjaWZpZXIgPSB0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLmdldChtb2R1bGVQYXRoKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChyZUV4cG9ydFNwZWNpZmllcikge1xuXHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShyZUV4cG9ydFNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRpZiAobmV4dFJlc29sdXRpb24gJiYgIW5leHRSZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRDb25zdHJ1Y3RvckluTW9kdWxlKG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgbmFtZSwgZGVwdGggKyAxKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGlmIChzdGFycykge1xuXHRcdFx0Zm9yIChjb25zdCBzdGFyU3BlY2lmaWVyIG9mIHN0YXJzKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoc3RhclNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRcdGlmICghbmV4dFJlc29sdXRpb24gfHwgbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kQ29uc3RydWN0b3JJbk1vZHVsZShuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIG5hbWUsIGRlcHRoICsgMSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHRwcml2YXRlIHJlc29sdmVIZWxkQ29uc3RydWN0b3IgKG5hbWU6IHN0cmluZywgZnJvbUZpbGU6IHN0cmluZyk6IENvbnN0cnVjdG9ySGFuZGxlciB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBub2RlUGF0aC5yZXNvbHZlKGZyb21GaWxlKTtcblx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldChmaWxlUGF0aCk/LmdldChuYW1lKTtcblx0XHRpZiAoaW1wb3J0ZWQgJiYgIWltcG9ydGVkLmlzTmFtZXNwYWNlKSB7XG5cdFx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoaW1wb3J0ZWQuc3BlY2lmaWVyLCBmaWxlUGF0aCk7XG5cdFx0XHRpZiAocmVzb2x1dGlvbiAmJiAhcmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kQ29uc3RydWN0b3JJbk1vZHVsZShyZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgaW1wb3J0ZWQub3JpZ2luYWxOYW1lLCAwKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGNvbnN0IGxvY2FsID0gdGhpcy5jb25zdHJ1Y3RvckJpbmRpbmdzLmdldChmaWxlUGF0aCk/LmdldChuYW1lKTtcblx0XHRyZXR1cm4gbG9jYWw7XG5cdH1cblxuXHRwcml2YXRlIHVud3JhcENvbnN0cnVjdG9yQXNzZXJ0aW9ucyAoaGFuZGxlcjogQ29uc3RydWN0b3JIYW5kbGVyKTogQ29uc3RydWN0b3JIYW5kbGVyIHtcblx0XHRsZXQgY3VycmVudCA9IGhhbmRsZXI7XG5cdFx0d2hpbGUgKHRzLmlzUGFyZW50aGVzaXplZEV4cHJlc3Npb24oY3VycmVudCkgfHwgdHMuaXNBc0V4cHJlc3Npb24oY3VycmVudCkgfHxcblx0XHRcdHRzLmlzVHlwZUFzc2VydGlvbkV4cHJlc3Npb24oY3VycmVudCkpIHtcblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0fVxuXHRcdHJldHVybiBjdXJyZW50O1xuXHR9XG5cblx0cHJpdmF0ZSByZXNvbHZlQ29uc3RydWN0b3JFeHByZXNzaW9uIChcblx0XHRleHByZXNzaW9uOiB0cy5FeHByZXNzaW9uLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGVcblx0KTogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBjdXJyZW50ID0gdGhpcy51bndyYXBDb25zdHJ1Y3RvckFzc2VydGlvbnMoZXhwcmVzc2lvbik7XG5cdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoY3VycmVudCkpIHtcblx0XHRcdHJldHVybiBjdXJyZW50O1xuXHRcdH1cblx0XHRjb25zdCByZXNvbHZlZCA9IHRoaXMucmVzb2x2ZUhlbGRDb25zdHJ1Y3RvcihjdXJyZW50LnRleHQsIHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXHRcdGlmICghcmVzb2x2ZWQpIHtcblx0XHRcdHJldHVybiBjdXJyZW50O1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnVud3JhcENvbnN0cnVjdG9yQXNzZXJ0aW9ucyhyZXNvbHZlZCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlcm1pbmUgdGhlIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24gZm9yIGVpdGhlciBhIGRlZmluZSgpIG9yIGxhenkoKSBjYWxsLlxuXHQgKiBGb3IgZGVmaW5lKCkgdGhpcyBpcyB0aGUgY29uc3RydWN0IGhhbmRsZXI7IGZvciBsYXp5KCkgaXQgaXMgdGhlIHZhbHVlXG5cdCAqIHJldHVybmVkIGJ5IHRoZSBsYXp5IGdldHRlci4gSWRlbnRpZmllcnMgcmVzb2x2ZSB0byB0aGVpciBkZWNsYXJhdGlvbnMuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24gKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBleHByID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGNvbnN0IG5hbWUgPSB0cy5pc0lkZW50aWZpZXIoZXhwcilcblx0XHRcdD8gZXhwci50ZXh0XG5cdFx0XHQ6IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpXG5cdFx0XHRcdD8gZXhwci5uYW1lLnRleHRcblx0XHRcdFx0OiAnJztcblx0XHRsZXQgaGFuZGxlcjogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZDtcblxuXHRcdGlmIChuYW1lID09PSAnbGF6eScpIHtcblx0XHRcdGNvbnN0IGxhenlBcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdFx0aWYgKGxhenlBcmdzKSB7XG5cdFx0XHRcdGhhbmRsZXIgPSB0aGlzLnVud3JhcExhenlHZXR0ZXIobGF6eUFyZ3MuZ2V0dGVyKTtcblx0XHRcdH1cblx0XHR9IGVsc2Uge1xuXHRcdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChhcmdzWyAwIF0pKSB7XG5cdFx0XHRcdGNvbnN0IFsgLCBtb2Rlcm5IYW5kbGVyIF0gPSBhcmdzO1xuXHRcdFx0XHRoYW5kbGVyID0gbW9kZXJuSGFuZGxlcjtcblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGNvbnN0IFsgbGVnYWN5SGFuZGxlciBdID0gYXJncztcblx0XHRcdFx0aGFuZGxlciA9IGxlZ2FjeUhhbmRsZXI7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0aWYgKCFoYW5kbGVyKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnJlc29sdmVDb25zdHJ1Y3RvckV4cHJlc3Npb24oaGFuZGxlciwgY2FsbC5nZXRTb3VyY2VGaWxlKCkpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRGV0ZWN0IGFuIGFzeW5jIGNvbnN0cnVjdG9yIGhhbmRsZXI6IHRoZSBhc3luYyBtb2RpZmllciBvbiBhXG5cdCAqIGZ1bmN0aW9uIGV4cHJlc3Npb24gb3IgYXJyb3cuIEFzeW5jIENMQVNTRVMgKGEgY2xhc3MgY29uc3RydWN0b3Jcblx0ICogcmV0dXJuaW5nIGEgUHJvbWlzZSkgYXJlIGRlbGliZXJhdGVseSBOT1QgZGV0ZWN0ZWQg4oCUIHRoZSBzeW50YWN0aWNcblx0ICogY2xhc3Mgc2hhcGUgZ2l2ZXMgbm8gcmVsaWFibGUgc2lnbmFsIHdpdGhvdXQgYSB0eXBlIGNoZWNrZXIsIGFuZCB0aGVcblx0ICogb3duZXIgZGVjaWRlZCB0aGV5IGFyZSB0eXBlZCBieSB0aGUgdXNlciBpbiB1c2VybGFuZC5cblx0ICovXG5cdHByaXZhdGUgaXNBc3luY0NvbnN0cnVjdEhhbmRsZXIgKGNvbnN0cnVjdG9yRXhwcjogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkKTogYm9vbGVhbiB7XG5cdFx0aWYgKCFjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Y29uc3QgaXNGbiA9IHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikgfHxcblx0XHRcdHRzLmlzQXJyb3dGdW5jdGlvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdGlmICghaXNGbikge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblx0XHRjb25zdCBtb2RpZmllcnMgPSB0cy5nZXRNb2RpZmllcnMoY29uc3RydWN0b3JFeHByKTtcblx0XHRjb25zdCByZXN1bHQgPSAhIW1vZGlmaWVycyAmJiBtb2RpZmllcnMuc29tZSgobW9kaWZpZXIpID0+IHtcblx0XHRcdHJldHVybiBtb2RpZmllci5raW5kID09PSB0cy5TeW50YXhLaW5kLkFzeW5jS2V5d29yZDtcblx0XHR9KTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGNvbnN0cnVjdG9yIGZ1bmN0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RQcm9wZXJ0aWVzIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yRXhwcmVzc2lvbihjYWxsKTtcblx0XHRpZiAoIWNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0cmV0dXJuIG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cdFx0fVxuXHRcdGNvbnN0IHJlZmVyZW5jaW5nRmlsZSA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSBub2RlUGF0aC5yZXNvbHZlKGNvbnN0cnVjdG9yRXhwci5nZXRTb3VyY2VGaWxlKCkuZmlsZU5hbWUpO1xuXHRcdHRyeSB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzRnJvbUNvbnN0cnVjdG9yKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH0gZmluYWxseSB7XG5cdFx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSByZWZlcmVuY2luZ0ZpbGU7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGEgY29uc3RydWN0b3IgZXhwcmVzc2lvbiAoZnVuY3Rpb24sIGFycm93LCBvciBjbGFzcykuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RQcm9wZXJ0aWVzRnJvbUNvbnN0cnVjdG9yIChjb25zdHJ1Y3RvckV4cHI6IENvbnN0cnVjdG9ySGFuZGxlcik6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Ly8gQnVpbGQgdHlwZSBtYXAgZnJvbSBkYXRhIHBhcmFtZXRlciAoZm9yIHRoaXMueCA9IGRhdGEueCBwYXR0ZXJucylcblx0XHRjb25zdCBkYXRhVHlwZU1hcCA9IHRoaXMuYnVpbGREYXRhVHlwZU1hcChjb25zdHJ1Y3RvckV4cHIpO1xuXG5cdFx0Ly8gSGFuZGxlIGZ1bmN0aW9uIGV4cHJlc3Npb25cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSB8fCB0cy5pc0Fycm93RnVuY3Rpb24oY29uc3RydWN0b3JFeHByKSB8fFxuXHRcdFx0dHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKGNvbnN0cnVjdG9yRXhwcikpIHtcblx0XHRcdGNvbnN0IHsgYm9keSB9ID0gY29uc3RydWN0b3JFeHByO1xuXG5cdFx0XHQvLyBGaXJzdCwgZXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gYHRoaXNgIHBhcmFtZXRlciB0eXBlIGFubm90YXRpb25cblx0XHRcdC8vIFRoaXMgaGFuZGxlcyBwYXR0ZXJucyBsaWtlOiBmdW5jdGlvbih0aGlzOiBTb21lVHlwZSwgZGF0YTogU29tZVR5cGUpIHsgfVxuXHRcdFx0Y29uc3QgdGhpc1BhcmFtUHJvcGVydGllcyA9IHRoaXMuZXh0cmFjdFRoaXNQYXJhbVByb3BlcnRpZXMoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdGZvciAoY29uc3QgWyBuYW1lLCBwcm9wSW5mbyBdIG9mIHRoaXNQYXJhbVByb3BlcnRpZXMpIHtcblx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwgcHJvcEluZm8pO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBBbiBhbm5vdGF0ZWQgdGhpcyBpcyB0aGUgY29tcGxldGUgZGVjbGFyZWQgaW5zdGFuY2UgdHlwZTogYXNzaWdubWVudHNcblx0XHRcdC8vIGJleW9uZCBpdCBhZGQgbm90aGluZy4gQSBnZW5lcmF0ZWQgLnRhY3RpY2Egb3IgZ3JhcGgtbmFtZSBhbm5vdGF0aW9uXG5cdFx0XHQvLyBpcyB0aGUgb3V0cHV0LCBub3QgdGhlIHNvdXJjZSwgc28gdGhvc2UgaGFuZGxlcnMga2VlcCBhc3NpZ25tZW50IGV4dHJhY3Rpb24uXG5cdFx0XHRjb25zdCBoYXNHZW5lcmF0ZWRSZWZlcmVuY2UgPSB0aGlzLmhhc0dlbmVyYXRlZFRoaXNBbm5vdGF0aW9uKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRjb25zdCBoYXNBdXRob3JpdGF0aXZlVGhpc0Fubm90YXRpb24gPSAhaGFzR2VuZXJhdGVkUmVmZXJlbmNlICYmIGNvbnN0cnVjdG9yRXhwci5wYXJhbWV0ZXJzLnNvbWUocGFyYW0gPT4ge1xuXHRcdFx0XHRjb25zdCByZXN1bHQgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgJiYgcGFyYW0ubmFtZS50ZXh0ID09PSAndGhpcycgJiYgcGFyYW0udHlwZSAhPT0gdW5kZWZpbmVkO1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fSk7XG5cdFx0XHRpZiAoIWhhc0F1dGhvcml0YXRpdmVUaGlzQW5ub3RhdGlvbiAmJiBib2R5ICYmIHRzLmlzQmxvY2soYm9keSkpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBzdG10IG9mIGJvZHkuc3RhdGVtZW50cykge1xuXHRcdFx0XHRcdGlmICh0cy5pc0V4cHJlc3Npb25TdGF0ZW1lbnQoc3RtdCkpIHtcblx0XHRcdFx0XHRcdHRoaXMuZXh0cmFjdFByb3BlcnR5RnJvbVN0YXRlbWVudChzdG10LmV4cHJlc3Npb24sIHByb3BlcnRpZXMsIGRhdGFUeXBlTWFwKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBIYW5kbGUgY2xhc3MgZXhwcmVzc2lvblxuXHRcdGlmICh0cy5pc0NsYXNzRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHQvLyBGaXJzdCBwYXNzOiBjb2xsZWN0IGFsbCBwcm9wZXJ0eSB0eXBlcyBmb3IgbWV0aG9kIGluZmVyZW5jZVxuXHRcdFx0Y29uc3QgY2xhc3NQcm9wZXJ0eVR5cGVzID0gdGhpcy5leHRyYWN0Q2xhc3NQcm9wZXJ0eVR5cGVzKGNvbnN0cnVjdG9yRXhwcik7XG5cblx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGNvbnN0cnVjdG9yRXhwci5tZW1iZXJzKSB7XG5cdFx0XHRcdC8vIEhhbmRsZSBwcm9wZXJ0eSBkZWNsYXJhdGlvbnNcblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlEZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lKSB7XG5cdFx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgcHJvcGVydGllc1xuXHRcdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdFx0XHRtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZDtcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cblx0XHRcdFx0XHRjb25zdCBuYW1lID0gdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSA/IG1lbWJlci5uYW1lLnRleHQgOiAnJztcblx0XHRcdFx0XHRpZiAobmFtZSkge1xuXHRcdFx0XHRcdFx0bGV0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0XHRpZiAodHlwZSA9PT0gJ3Vua25vd24nICYmIG1lbWJlci5pbml0aWFsaXplcikge1xuXHRcdFx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIobWVtYmVyLmluaXRpYWxpemVyKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gSGFuZGxlIG1ldGhvZCBkZWNsYXJhdGlvbnNcblx0XHRcdFx0aWYgKHRzLmlzTWV0aG9kRGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgbWV0aG9kc1xuXHRcdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdFx0XHRtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZDtcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cblx0XHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlck1ldGhvZFR5cGUobWVtYmVyLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIEhhbmRsZSBnZXR0ZXIgZGVjbGFyYXRpb25zXG5cdFx0XHRcdGlmICh0cy5pc0dldEFjY2Vzc29yKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIGdldHRlcnNcblx0XHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4ge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHRcdFx0bS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQ7XG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXG5cdFx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Ly8gRmlyc3QgdHJ5IGV4cGxpY2l0IHR5cGUgYW5ub3RhdGlvbiwgdGhlbiBpbmZlciBmcm9tIGdldHRlciBib2R5XG5cdFx0XHRcdFx0bGV0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0aWYgKHR5cGUgPT09ICd1bmtub3duJyAmJiBtZW1iZXIuYm9keSkge1xuXHRcdFx0XHRcdFx0dHlwZSA9IHRoaXMuaW5mZXJSZXR1cm5UeXBlRnJvbUJvZHkobWVtYmVyLmJvZHksIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdHJlYWRvbmx5IDogdHJ1ZSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBwcm9wZXJ0aWVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEJ1aWxkIGEgdHlwZSBtYXAgZnJvbSBhbGwgcGFyYW1ldGVycyB3aXRoIGlubGluZSBvYmplY3QgdHlwZSBhbm5vdGF0aW9uc1xuXHQgKiBSZXR1cm5zIGEgbWFwIG9mIFwicGFyYW1OYW1lLnByb3BlcnR5TmFtZVwiIC0+IHR5cGVcblx0ICovXG5cdHByaXZhdGUgYnVpbGREYXRhVHlwZU1hcCAoaGFuZGxlckFyZzogQ29uc3RydWN0b3JIYW5kbGVyKTogTWFwPHN0cmluZywgc3RyaW5nPiB7XG5cdFx0Y29uc3QgdHlwZU1hcCA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cblx0XHRpZiAoIXRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGhhbmRsZXJBcmcpICYmICF0cy5pc0Fycm93RnVuY3Rpb24oaGFuZGxlckFyZykgJiZcblx0XHRcdCF0cy5pc0Z1bmN0aW9uRGVjbGFyYXRpb24oaGFuZGxlckFyZykpIHtcblx0XHRcdHJldHVybiB0eXBlTWFwO1xuXHRcdH1cblxuXHRcdC8vIEl0ZXJhdGUgb3ZlciBBTEwgcGFyYW1ldGVyc1xuXHRcdGZvciAoY29uc3QgcGFyYW0gb2YgaGFuZGxlckFyZy5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRpZiAoIXBhcmFtLm5hbWUgfHwgIXBhcmFtLnR5cGUpIGNvbnRpbnVlO1xuXG5cdFx0XHQvLyBHZXQgcGFyYW1ldGVyIG5hbWVcblx0XHRcdGxldCBwYXJhbU5hbWUgPSAnJztcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkpIHtcblx0XHRcdFx0cGFyYW1OYW1lID0gcGFyYW0ubmFtZS50ZXh0O1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Ly8gU2tpcCBkZXN0cnVjdHVyZWQgcGFyYW1ldGVycyBmb3Igbm93XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBDaGVjayBpZiBpdCdzIGFuIGlubGluZSBvYmplY3QgdHlwZSBsaXRlcmFsXG5cdFx0XHRpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUocGFyYW0udHlwZSkpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgcGFyYW0udHlwZS5tZW1iZXJzKSB7XG5cdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQoYCR7cGFyYW1OYW1lfS4ke3Byb3BOYW1lfWAsIHR5cGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Ly8gTmFtZWQgdHlwZSByZWZlcmVuY2UgKGFsaWFzL2ludGVyZmFjZS9jbGFzcywgaW1wb3J0ZWQgb3Jcblx0XHRcdFx0Ly8gbG9jYWwg4oCUIEYxNCk6IGRlY29tcG9zZSB0aGUgcmVzb2x2ZWQgZGVjbGFyYXRpb24gaW50b1xuXHRcdFx0XHQvLyBwZXItcHJvcGVydHkgZW50cmllcyB0aHJvdWdoIHRoZSBzYW1lIGltcG9ydC1hd2FyZVxuXHRcdFx0XHQvLyBtYWNoaW5lcnkgYXMgY29uc3RydWN0b3Igc2lnbmF0dXJlcyAoRjEwKSwgaW5jbHVkaW5nIHRoZVxuXHRcdFx0XHQvLyBoZXJpdGFnZSB3YWxrIChGMTMpLiBXaXRob3V0IHRoaXMsIGB0aGlzLnggPSBwYXJhbS55YFxuXHRcdFx0XHQvLyByZWFkIGB1bmtub3duYCBmb3IgbmFtZWQgcGFyYW1zIOKAlCBvbmx5IGlubGluZSBsaXRlcmFsc1xuXHRcdFx0XHQvLyB3ZXJlIGRlY29tcG9zZWQuIFVucmVzb2x2YWJsZSDihpIgd2hvbGUtcGFyYW0gZmFsbGJhY2tcblx0XHRcdFx0Ly8gYmVsb3c7IGEgYmFyZSBuYW1lIGlzIG5ldmVyIGVtaXR0ZWQgZWl0aGVyIHdheVxuXHRcdFx0XHRsZXQgbmFtZWREZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkO1xuXHRcdFx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZShwYXJhbS50eXBlKSAmJiB0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBwYXJhbVR5cGVOYW1lID0gcGFyYW0udHlwZS50eXBlTmFtZS50ZXh0O1xuXHRcdFx0XHRcdG5hbWVkRGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24ocGFyYW1UeXBlTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAobmFtZWREZWNsKSB7XG5cdFx0XHRcdFx0Ly8gbWVtYmVyIHR5cGVzIHJlc29sdmUgYWdhaW5zdCB0aGUgREVDTEFSSU5HIGZpbGVcblx0XHRcdFx0XHRjb25zdCByZWZlcmVuY2luZ0ZpbGUgPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0XHRcdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gbmFtZWREZWNsLmZpbGU7XG5cdFx0XHRcdFx0dHJ5IHtcblx0XHRcdFx0XHRcdGNvbnN0IGRlY2xQcm9wZXJ0aWVzID0gdGhpcy5yZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzKG5hbWVkRGVjbCk7XG5cdFx0XHRcdFx0XHRmb3IgKGNvbnN0IFsgcHJvcE5hbWUsIGluZm8gXSBvZiBkZWNsUHJvcGVydGllcykge1xuXHRcdFx0XHRcdFx0XHR0eXBlTWFwLnNldChgJHtwYXJhbU5hbWV9LiR7cHJvcE5hbWV9YCwgaW5mby50eXBlKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGZpbmFsbHkge1xuXHRcdFx0XHRcdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gcmVmZXJlbmNpbmdGaWxlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHQvLyBrZWVwIHRoZSB3aG9sZS1wYXJhbSBlbnRyeSB0b286IGB0aGlzLnggPSBkYXRhYCAodGhlXG5cdFx0XHRcdFx0Ly8gYmFyZSBwYXJhbWV0ZXIpIGFzc2lnbnMgdGhlIGZ1bGwgZXhwYW5kZWQgc2hhcGUg4oCUXG5cdFx0XHRcdFx0Ly8gdGhlIHNhbWUgc3RyaW5nIGNvbnN0cnVjdG9yLXNpZ25hdHVyZSBlbWlzc2lvbiB1c2VzXG5cdFx0XHRcdFx0Y29uc3Qgd2hvbGVUeXBlID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKG5hbWVkRGVjbCk7XG5cdFx0XHRcdFx0aWYgKHdob2xlVHlwZSAmJiB3aG9sZVR5cGUgIT09ICd1bmtub3duJykge1xuXHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQocGFyYW1OYW1lLCB3aG9sZVR5cGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHQvLyBTdG9yZSBzaW1wbGUgcGFyYW1ldGVyIHR5cGVzIGxpa2UgYGRlY29yYXRlVmFsdWU6IHN0cmluZ2Bcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cdFx0XHRcdFx0aWYgKHR5cGUgIT09ICd1bmtub3duJykge1xuXHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQocGFyYW1OYW1lLCB0eXBlKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdHlwZU1hcDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnR5IGFjY2VzcyBjaGFpbiAoZS5nLiwgXCJkYXRhUmVuYW1lZC5pZFwiIGZyb20gZGF0YVJlbmFtZWQuaWQpXG5cdCAqIEhhbmRsZXMgZmFsbGJhY2tzIGxpa2U6IGRhdGEucGVybWlzc2lvbnMgfHwgW11cblx0ICovXG5cdHByaXZhdGUgZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbiAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gSGFuZGxlIGlkZW50aWZpZXI6IGRhdGFcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci50ZXh0O1xuXHRcdH1cblx0XHQvLyBIYW5kbGUgcHJvcGVydHkgYWNjZXNzOiBkYXRhLnBlcm1pc3Npb25zXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBiYXNlID0gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGV4cHIuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoYmFzZSkge1xuXHRcdFx0XHRyZXR1cm4gYCR7YmFzZX0uJHtleHByLm5hbWUudGV4dH1gO1xuXHRcdFx0fVxuXHRcdH1cblx0XHQvLyBIYW5kbGUgZmFsbGJhY2sgcGF0dGVybjogZGF0YS5wZXJtaXNzaW9ucyB8fCBbXVxuXHRcdGlmICh0cy5pc0JpbmFyeUV4cHJlc3Npb24oZXhwcikgJiZcblx0XHRcdGV4cHIub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkJhckJhclRva2VuKSB7XG5cdFx0XHQvLyBSZXR1cm4gdGhlIGxlZnQgc2lkZSBvZiB8fCBvcGVyYXRvclxuXHRcdFx0cmV0dXJuIHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihleHByLmxlZnQpO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydHkgYXNzaWdubWVudCBmcm9tIHN0YXRlbWVudFxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UHJvcGVydHlGcm9tU3RhdGVtZW50IChcblx0XHRleHByOiB0cy5FeHByZXNzaW9uLFxuXHRcdHByb3BlcnRpZXM6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4sXG5cdFx0ZGF0YVR5cGVNYXA6IE1hcDxzdHJpbmcsIHN0cmluZz4gPSBuZXcgTWFwKClcblx0KTogdm9pZCB7XG5cdFx0Ly8gSGFuZGxlOiB0aGlzLnByb3BlcnR5ID0gdmFsdWVcblx0XHRpZiAodHMuaXNCaW5hcnlFeHByZXNzaW9uKGV4cHIpICYmXG5cdFx0XHRleHByLm9wZXJhdG9yVG9rZW4ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbikge1xuXHRcdFx0Y29uc3QgeyBsZWZ0IH0gPSBleHByO1xuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obGVmdCkpIHtcblx0XHRcdFx0Ly8gQ2hlY2sgaWYgYWNjZXNzaW5nICd0aGlzJyAoVGhpc0tleXdvcmQpXG5cdFx0XHRcdGlmIChsZWZ0LmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBsZWZ0Lm5hbWU/LnRleHQ7XG5cdFx0XHRcdFx0aWYgKG5hbWUpIHtcblx0XHRcdFx0XHRcdC8vIFRyeSB0byBnZXQgdHlwZSBmcm9tIGRhdGFUeXBlTWFwIHVzaW5nIGZ1bGwgYWNjZXNzIGNoYWluIChlLmcuLCBcImRhdGFSZW5hbWVkLmlkXCIpXG5cdFx0XHRcdFx0XHRjb25zdCBhY2Nlc3NDaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihleHByLnJpZ2h0KTtcblx0XHRcdFx0XHRcdGxldCB0eXBlID0gYWNjZXNzQ2hhaW4gPyBkYXRhVHlwZU1hcC5nZXQoYWNjZXNzQ2hhaW4pIDogdW5kZWZpbmVkO1xuXHRcdFx0XHRcdFx0Ly8gSWYgbm90IGZvdW5kIGFuZCBSSFMgaXMgYSBzaW1wbGUgaWRlbnRpZmllciwgdHJ5IGxvb2tpbmcgaXQgdXAgZGlyZWN0bHlcblx0XHRcdFx0XHRcdGlmICghdHlwZSAmJiB0cy5pc0lkZW50aWZpZXIoZXhwci5yaWdodCkpIHtcblx0XHRcdFx0XHRcdFx0dHlwZSA9IGRhdGFUeXBlTWFwLmdldChleHByLnJpZ2h0LnRleHQpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0Ly8gYSBib3VuZCBjb25zdHJ1Y3Rpb24gcmVzdWx0IChuZXcvbG9va3VwL2NoYWluL2ZvcmsvXG5cdFx0XHRcdFx0XHQvLyBtZXJnZS9jYWxsKTogdGhlIHZhbHVlIHNjb3BlIGJpbmRpbmcgc3VwcGxpZXMgdGhlXG5cdFx0XHRcdFx0XHQvLyBncmFwaCB0eXBlIOKAlCBlbWl0dGVkIGJ5IGl0cyBpbnN0YW5jZS10eXBlIG5hbWVcblx0XHRcdFx0XHRcdGlmICghdHlwZSAmJiB0cy5pc0lkZW50aWZpZXIoZXhwci5yaWdodCkpIHtcblx0XHRcdFx0XHRcdFx0Y29uc3QgYm91bmQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChleHByLnJpZ2h0LnRleHQpO1xuXHRcdFx0XHRcdFx0XHRpZiAoYm91bmQpIHtcblx0XHRcdFx0XHRcdFx0XHQvLyBFbWl0IHRoZSBhbGlhcyB0eXBlcy50cyBkZWNsYXJlcyAoT3B0aW9uIEJcblx0XHRcdFx0XHRcdFx0XHQvLyByZWdpc3RyeSBwcmVmaXgpLCBub3QgdGhlIHJhdyBjb2xsZWN0aW9uSWQ6OlxuXHRcdFx0XHRcdFx0XHRcdC8vIGZ1bGxQYXRoOyBuZXZlci1lbWl0dGVkIHR5cGVzIGZhbGwgdGhyb3VnaFxuXHRcdFx0XHRcdFx0XHRcdC8vIHRvIGluaXRpYWxpemVyIGluZmVyZW5jZVxuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IGJvdW5kTm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoYm91bmQpO1xuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IGJvdW5kQWxpYXMgPSBib3VuZE5vZGVcblx0XHRcdFx0XHRcdFx0XHRcdD8gdGhpcy5nZXRFbWl0dGVkSW5zdGFuY2VUeXBlTmFtZShib3VuZE5vZGUpXG5cdFx0XHRcdFx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblx0XHRcdFx0XHRcdFx0XHRpZiAoYm91bmRBbGlhcykge1xuXHRcdFx0XHRcdFx0XHRcdFx0dHlwZSA9IGJvdW5kQWxpYXM7XG5cdFx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRpZiAoIXR5cGUpIHtcblx0XHRcdFx0XHRcdFx0dHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKGV4cHIucmlnaHQsIGRhdGFUeXBlTWFwKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdC8vIERvbid0IG92ZXJ3cml0ZSBhIGtub3duIHR5cGUgZnJvbSBhIGB0aGlzYCBhbm5vdGF0aW9uXG5cdFx0XHRcdFx0XHQvLyB3aXRoIGFuIHVua25vd24tYmVhcmluZyBpbmZlcmVuY2U6IGFuIGVtcHR5LWFycmF5XG5cdFx0XHRcdFx0XHQvLyBpbml0aWFsaXplciBpbmZlcnMgJ0FycmF5PHVua25vd24+Jywgd2hpY2ggbXVzdCBub3Rcblx0XHRcdFx0XHRcdC8vIGNsb2JiZXIgYW4gYW5ub3RhdGVkICdBcnJheTx7IGlkOiBudW1iZXIgfT4nIGVpdGhlci5cblx0XHRcdFx0XHRcdC8vIFwiS25vd25cIiBvbiB0aGUgRVhJU1RJTkcgc2lkZSBtZWFucyB0aGUgd2hvbGUgdHlwZSBJU1xuXHRcdFx0XHRcdFx0Ly8gYHVua25vd25gIChleGFjdCBtYXRjaCkg4oCUIGEgc3Vic3RyaW5nIG1hdGNoIHRyZWF0c1xuXHRcdFx0XHRcdFx0Ly8gYFJlY29yZDxzdHJpbmcsIHVua25vd24+YCBhcyB1bmtub3duLWJlYXJpbmcgYW5kIGxldFxuXHRcdFx0XHRcdFx0Ly8gaW5mZXJlbmNlIGNsb2JiZXIgYSBnb29kIGFubm90YXRpb24gKEYxNClcblx0XHRcdFx0XHRcdGNvbnN0IGV4aXN0aW5nID0gcHJvcGVydGllcy5nZXQobmFtZSk7XG5cdFx0XHRcdFx0XHRjb25zdCB0eXBlSGFzVW5rbm93biA9ICF0eXBlIHx8IHR5cGUuaW5jbHVkZXMoJ3Vua25vd24nKTtcblx0XHRcdFx0XHRcdGNvbnN0IGV4aXN0aW5nSXNLbm93biA9IGV4aXN0aW5nID8gZXhpc3RpbmcudHlwZS50cmltKCkgIT09ICd1bmtub3duJyA6IGZhbHNlO1xuXHRcdFx0XHRcdFx0aWYgKGV4aXN0aW5nSXNLbm93biAmJiB0eXBlSGFzVW5rbm93bikge1xuXHRcdFx0XHRcdFx0XHQvLyBLZWVwIHRoZSBiZXR0ZXIgdHlwZSBmcm9tIGV4cGxpY2l0IGFubm90YXRpb25cblx0XHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBleGlzdGluZyA/IGV4aXN0aW5nLm9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIEhhbmRsZTogT2JqZWN0LmFzc2lnbih0aGlzLCB7IHByb3A6IHZhbHVlIH0pXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdGNvbnN0IGZuID0gZXhwci5leHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGZuKSAmJlxuXHRcdFx0XHRmbi5uYW1lPy50ZXh0ID09PSAnYXNzaWduJyAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoZm4uZXhwcmVzc2lvbikgJiZcblx0XHRcdFx0Zm4uZXhwcmVzc2lvbi50ZXh0ID09PSAnT2JqZWN0Jykge1xuXHRcdFx0XHRjb25zdCBhcmdzID0gZXhwci5hcmd1bWVudHM7XG5cdFx0XHRcdGlmIChhcmdzLmxlbmd0aCA+PSAyICYmIGFyZ3NbIDAgXS5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gdGhlIHNlY29uZCBhcmd1bWVudFxuXHRcdFx0XHRcdGNvbnN0IFsgLCBwcm9wc0FyZyBdID0gYXJncztcblx0XHRcdFx0XHRpZiAodHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihwcm9wc0FyZykpIHtcblx0XHRcdFx0XHRcdGZvciAoY29uc3QgcHJvcCBvZiBwcm9wc0FyZy5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSAmJiB0cy5pc0lkZW50aWZpZXIocHJvcC5uYW1lKSkge1xuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBwcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0XHRcdFx0dHlwZSAgICAgOiB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihwcm9wLmluaXRpYWxpemVyKSxcblx0XHRcdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihwcm9wc0FyZykpIHtcblx0XHRcdFx0XHRcdC8vIE9iamVjdC5hc3NpZ24odGhpcywgZGF0YSkg4oCUIHRoZSBpZGVudGlmaWVyIGZvcm06IGV2ZXJ5XG5cdFx0XHRcdFx0XHQvLyBwZXItcHJvcGVydHkgZW50cnkgdGhlIGRhdGEgcGFyYW1ldGVyIGNvbnRyaWJ1dGVkIHRvXG5cdFx0XHRcdFx0XHQvLyB0aGUgdHlwZSBtYXAgYmVjb21lcyBhbiBvd24gcHJvcGVydHkuIFRoaXMgaXMgd2hhdFxuXHRcdFx0XHRcdFx0Ly8gY2FycmllcyB0aGUgZmllbGRzIGZvciB0aGUgc2VsZi1yZWZlcmVuY2luZ1xuXHRcdFx0XHRcdFx0Ly8gaW50ZXJzZWN0aW9uLWFsaWFzIHJvb3QgcGF0dGVybiAoRjIxKTogdGhlIHRoaXMtYWxpYXNcblx0XHRcdFx0XHRcdC8vIGlzIGVyZ29ub21pYy1vbmx5IGFuZCBpdHMgaW50ZXJzZWN0aW9uIG1lbWJlcnMgYXJlXG5cdFx0XHRcdFx0XHQvLyBuZXZlciBleHBhbmRlZCwgc28gdGhlIGFzc2lnbiBpcyB3aGVyZSB0aGUgcm9vdCdzXG5cdFx0XHRcdFx0XHQvLyBmaWVsZHMgbXVzdCBjb21lIGZyb21cblx0XHRcdFx0XHRcdGNvbnN0IHBhcmFtTmFtZSA9IHByb3BzQXJnLnRleHQ7XG5cdFx0XHRcdFx0XHRmb3IgKGNvbnN0IFsga2V5LCB0eXBlIF0gb2YgZGF0YVR5cGVNYXApIHtcblx0XHRcdFx0XHRcdFx0aWYgKCFrZXkuc3RhcnRzV2l0aChgJHtwYXJhbU5hbWV9LmApKSB7XG5cdFx0XHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdFx0Y29uc3QgbmFtZSA9IGtleS5zbGljZShwYXJhbU5hbWUubGVuZ3RoICsgMSk7XG5cdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGNsYXNzIGRlY2xhcmF0aW9uIChpbmNsdWRpbmcgbWV0aG9kcyBhbmQgZ2V0dGVycylcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENsYXNzUHJvcGVydGllcyAoY2xhc3NEZWNsOiB0cy5DbGFzc0RlY2xhcmF0aW9uKTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjbGFzc0RlY2wubWVtYmVycykge1xuXHRcdFx0Ly8gSGFuZGxlIHByb3BlcnR5IGRlY2xhcmF0aW9uc1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlEZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lKSB7XG5cdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIHByb3BlcnRpZXNcblx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdCAgICAgbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQpO1xuXHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpID8gbWVtYmVyLm5hbWUudGV4dCA6ICcnO1xuXHRcdFx0XHRpZiAobmFtZSkge1xuXHRcdFx0XHRcdC8vIElmIG5vIGV4cGxpY2l0IHR5cGUgYnV0IGhhcyBpbml0aWFsaXplciwgaW5mZXIgZnJvbSBpbml0aWFsaXplclxuXHRcdFx0XHRcdGxldCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdGlmICh0eXBlID09PSAndW5rbm93bicgJiYgbWVtYmVyLmluaXRpYWxpemVyKSB7XG5cdFx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIobWVtYmVyLmluaXRpYWxpemVyKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblxuXHRcdFx0Ly8gSGFuZGxlIG1ldGhvZCBkZWNsYXJhdGlvbnNcblx0XHRcdGlmICh0cy5pc01ldGhvZERlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBtZXRob2RzXG5cdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHQgICAgIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkKTtcblx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJNZXRob2RUeXBlKG1lbWJlcik7XG5cdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEhhbmRsZSBnZXR0ZXIgZGVjbGFyYXRpb25zXG5cdFx0XHRpZiAodHMuaXNHZXRBY2Nlc3NvcihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgZ2V0dGVyc1xuXHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0ICAgICBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZCk7XG5cdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdC8vIEZpcnN0IHRyeSBleHBsaWNpdCB0eXBlIGFubm90YXRpb24sIHRoZW4gaW5mZXIgZnJvbSBnZXR0ZXIgYm9keVxuXHRcdFx0XHRsZXQgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0aWYgKHR5cGUgPT09ICd1bmtub3duJyAmJiBtZW1iZXIuYm9keSkge1xuXHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyUmV0dXJuVHlwZUZyb21Cb2R5KG1lbWJlci5ib2R5KTtcblx0XHRcdFx0fVxuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0cmVhZG9ubHkgOiB0cnVlLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGNsYXNzIHByb3BlcnR5IHR5cGVzIGZvciBtZXRob2QgcmV0dXJuIHR5cGUgaW5mZXJlbmNlXG5cdCAqIE1hcHMgcHJvcGVydHkgbmFtZXMgdG8gdGhlaXIgVHlwZVNjcmlwdCB0eXBlIHN0cmluZ3Ncblx0ICogTm90ZTogSW5jbHVkZXMgcHJpdmF0ZS9wcm90ZWN0ZWQgcHJvcGVydGllcyBmb3IgbWV0aG9kIGluZmVyZW5jZVxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q2xhc3NQcm9wZXJ0eVR5cGVzIChjbGFzc0RlY2w6IENsYXNzQ29uc3RydWN0b3JIYW5kbGVyKTogTWFwPHN0cmluZywgc3RyaW5nPiB7XG5cdFx0Y29uc3QgcHJvcGVydHlUeXBlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjbGFzc0RlY2wubWVtYmVycykge1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlEZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Ly8gSW5jbHVkZSBBTEwgcHJvcGVydGllcyAoZXZlbiBwcml2YXRlKSBmb3IgbWV0aG9kIHJldHVybiB0eXBlIGluZmVyZW5jZVxuXHRcdFx0XHQvLyBUaGUgdmlzaWJpbGl0eSBjaGVjayBpcyBkb25lIHdoZW4gYWRkaW5nIHRvIG91dHB1dCBwcm9wZXJ0aWVzXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRpZiAobWVtYmVyLnR5cGUpIHtcblx0XHRcdFx0XHRwcm9wZXJ0eVR5cGVzLnNldChuYW1lLCB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSkpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnR5VHlwZXM7XG5cdH1cblxuXHQvKipcblx0ICogSW5mZXIgbWV0aG9kIHR5cGUgZnJvbSBtZXRob2QgZGVjbGFyYXRpb25cblx0ICovXG5cdHByaXZhdGUgaW5mZXJNZXRob2RUeXBlIChtZXRob2Q6IHRzLk1ldGhvZERlY2xhcmF0aW9uLCBjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+KTogc3RyaW5nIHtcblx0XHRjb25zdCBwYXJhbXMgPSBtZXRob2QucGFyYW1ldGVycy5tYXAocGFyYW0gPT4ge1xuXHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpID8gcGFyYW0ubmFtZS50ZXh0IDogJ2FyZyc7XG5cdFx0XHRjb25zdCBwYXJhbVR5cGUgPSB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblx0XHRcdHJldHVybiBgJHtwYXJhbU5hbWV9OiAke3BhcmFtVHlwZX1gO1xuXHRcdH0pLmpvaW4oJywgJyk7XG5cblx0XHRjb25zdCByZXR1cm5UeXBlID0gdGhpcy5pbmZlclJldHVyblR5cGUobWV0aG9kLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXG5cdFx0aWYgKHBhcmFtcykge1xuXHRcdFx0cmV0dXJuIGAoJHtwYXJhbXN9KSA9PiAke3JldHVyblR5cGV9YDtcblx0XHR9XG5cdFx0cmV0dXJuIGAoKSA9PiAke3JldHVyblR5cGV9YDtcblx0fVxuXG5cdHByaXZhdGUgaGFzR2VuZXJhdGVkVGhpc0Fubm90YXRpb24gKGhhbmRsZXI6IENvbnN0cnVjdG9ySGFuZGxlcik6IGJvb2xlYW4ge1xuXHRcdGlmICh0aGlzLmhhc0dlbmVyYXRlZFR5cGVSZWZlcmVuY2UoaGFuZGxlcikpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHRpZiAoIXRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGhhbmRsZXIpICYmICF0cy5pc0Fycm93RnVuY3Rpb24oaGFuZGxlcikgJiZcblx0XHRcdCF0cy5pc0Z1bmN0aW9uRGVjbGFyYXRpb24oaGFuZGxlcikpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBoYW5kbGVyLnBhcmFtZXRlcnMpIHtcblx0XHRcdGNvbnN0IGlzVGhpcyA9IHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSAmJiBwYXJhbS5uYW1lLnRleHQgPT09ICd0aGlzJztcblx0XHRcdGlmICghaXNUaGlzIHx8ICFwYXJhbS50eXBlIHx8ICF0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHBhcmFtLnR5cGUpIHx8XG5cdFx0XHRcdCF0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCB0eXBlTmFtZSA9IHBhcmFtLnR5cGUudHlwZU5hbWUudGV4dDtcblx0XHRcdGlmICh0aGlzLmN1cnJlbnRHcmFwaEFuY2hvcj8ubmFtZSA9PT0gdHlwZU5hbWUgfHwgdGhpcy5jdXJyZW50R3JhcGhBbmNob3I/LmZ1bGxQYXRoID09PSB0eXBlTmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGdyYXBoVHlwZSA9IHRoaXMuZ3JhcGguZmluZFR5cGVCeU5hbWUodHlwZU5hbWUpO1xuXHRcdFx0aWYgKGdyYXBoVHlwZSkge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0cHJpdmF0ZSBoYXNBbnlUaGlzQW5ub3RhdGlvbiAoaGFuZGxlcjogQ29uc3RydWN0b3JIYW5kbGVyIHwgdW5kZWZpbmVkKTogYm9vbGVhbiB7XG5cdFx0aWYgKCFoYW5kbGVyIHx8ICghdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oaGFuZGxlcikgJiYgIXRzLmlzQXJyb3dGdW5jdGlvbihoYW5kbGVyKSAmJlxuXHRcdFx0IXRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihoYW5kbGVyKSkpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gaGFuZGxlci5wYXJhbWV0ZXJzLnNvbWUocGFyYW0gPT4ge1xuXHRcdFx0Y29uc3QgbWF0Y2hlcyA9IHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSAmJiBwYXJhbS5uYW1lLnRleHQgPT09ICd0aGlzJyAmJlxuXHRcdFx0XHRwYXJhbS50eXBlPy5raW5kID09PSB0cy5TeW50YXhLaW5kLkFueUtleXdvcmQ7XG5cdFx0XHRyZXR1cm4gbWF0Y2hlcztcblx0XHR9KTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBgdGhpc2AgcGFyYW1ldGVyIHR5cGUgYW5ub3RhdGlvblxuXHRcdCogSGFuZGxlcyBwYXR0ZXJucyBsaWtlOiBmdW5jdGlvbih0aGlzOiBTb21lVHlwZSwgZGF0YTogU29tZVR5cGUpIHsgfVxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdFRoaXNQYXJhbVByb3BlcnRpZXMgKGhhbmRsZXJBcmc6IEZ1bmN0aW9uQ29uc3RydWN0b3JIYW5kbGVyKTpcblx0XHRNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCBwcm9wZXJ0aWVzID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblxuXHRcdC8vIEZpbmQgdGhlIGB0aGlzYCBwYXJhbWV0ZXIgKGlmIGFueSlcblx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGhhbmRsZXJBcmcucGFyYW1ldGVycykge1xuXHRcdFx0aWYgKHBhcmFtLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpICYmIHBhcmFtLm5hbWUudGV4dCA9PT0gJ3RoaXMnICYmIHBhcmFtLnR5cGUpIHtcblx0XHRcdFx0Ly8gQ2hlY2sgaWYgaXQncyBhIHR5cGUgcmVmZXJlbmNlIChlLmcuLCBgdGhpczogdXNhZ2VgKVxuXHRcdFx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZShwYXJhbS50eXBlKSkge1xuXHRcdFx0XHRcdGNvbnN0IHR5cGVOYW1lID0gdHMuaXNJZGVudGlmaWVyKHBhcmFtLnR5cGUudHlwZU5hbWUpXG5cdFx0XHRcdFx0XHQ/IHBhcmFtLnR5cGUudHlwZU5hbWUudGV4dFxuXHRcdFx0XHRcdFx0OiAnJztcblxuXHRcdFx0XHRcdC8vIFJlc29sdmUgdGhyb3VnaCB0aGUgcmVmZXJlbmNpbmcgZmlsZSdzIG93biBpbXBvcnRzIGZpcnN0IChGMTApXG5cdFx0XHRcdFx0Y29uc3QgZGVjbCA9IHR5cGVOYW1lXG5cdFx0XHRcdFx0XHQ/IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24odHlwZU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSlcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0XHRcdGlmIChkZWNsKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBkZWNsUHJvcGVydGllcyA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllcyhkZWNsKTtcblx0XHRcdFx0XHRcdGZvciAoY29uc3QgWyBwcm9wTmFtZSwgaW5mbyBdIG9mIGRlY2xQcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KHByb3BOYW1lLCBpbmZvKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gQ2hlY2sgaWYgaXQncyBkaXJlY3RseSBhbiBpbmxpbmUgdHlwZSBsaXRlcmFsIChlLmcuLCBgdGhpczogeyBpZDogc3RyaW5nIH1gKVxuXHRcdFx0XHRlbHNlIGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZShwYXJhbS50eXBlKSkge1xuXHRcdFx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIHBhcmFtLnR5cGUubWVtYmVycykge1xuXHRcdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQocHJvcE5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRuYW1lICAgICA6IHByb3BOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gRm91bmQgdGhlIGB0aGlzYCBwYXJhbWV0ZXIsIG5vIG5lZWQgdG8gY29udGludWVcblx0XHRcdFx0YnJlYWs7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHQvKipcblx0XHQqIEluZmVyIFR5cGVTY3JpcHQgdHlwZSBmcm9tIHR5cGUgbm9kZVxuXHRcdCovXG5cdC8qKlxuXHQgKiBJbmZlciBUeXBlU2NyaXB0IHR5cGUgZnJvbSB0eXBlIG5vZGVcblx0ICovXG5cdHByaXZhdGUgaW5mZXJUeXBlICh0eXBlTm9kZT86IHRzLlR5cGVOb2RlKTogc3RyaW5nIHtcblx0XHRpZiAoIXR5cGVOb2RlKSB7XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblxuXHRcdHN3aXRjaCAodHlwZU5vZGUua2luZCkge1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5TdHJpbmdLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdW1iZXJLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Cb29sZWFuS2V5d29yZDpcblx0XHRcdHJldHVybiAnYm9vbGVhbic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVuZGVmaW5lZEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3VuZGVmaW5lZCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bGxLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdudWxsJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQW55S2V5d29yZDpcblx0XHRcdHJldHVybiAnYW55Jztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5rbm93bktleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Wb2lkS2V5d29yZDpcblx0XHRcdHJldHVybiAndm9pZCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkFycmF5VHlwZTpcblx0XHRcdHJldHVybiBgQXJyYXk8JHsgIHRoaXMuaW5mZXJUeXBlKCh0eXBlTm9kZSBhcyB0cy5BcnJheVR5cGVOb2RlKS5lbGVtZW50VHlwZSkgIH0+YDtcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZUxpdGVyYWw6IHtcblx0XHRcdC8vIElubGluZS1leHBhbmQgdHlwZSBsaXRlcmFscyBpbnN0ZWFkIG9mIGNvbGxhcHNpbmcgdG8gJ29iamVjdCdcblx0XHRcdGNvbnN0IHR5cGVMaXQgPSB0eXBlTm9kZSBhcyB0cy5UeXBlTGl0ZXJhbE5vZGU7XG5cdFx0XHRjb25zdCBwcm9wczogc3RyaW5nW10gPSBbXTtcblx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIHR5cGVMaXQubWVtYmVycykge1xuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Y29uc3Qgb3B0aW9uYWwgPSBtZW1iZXIucXVlc3Rpb25Ub2tlbiA/ICc/JyA6ICcnO1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0cHJvcHMucHVzaChgJHtwcm9wTmFtZX0ke29wdGlvbmFsfTogJHt0eXBlfWApO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gYHsgJHtwcm9wcy5qb2luKCc7ICcpfSB9YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkxpdGVyYWxUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgc3RyaW5nIGxpdGVyYWwgdHlwZXMgbGlrZSAndXNlcicsICdhZG1pbicsIGV0Yy5cblx0XHRcdGNvbnN0IHsgbGl0ZXJhbCB9ID0gKHR5cGVOb2RlIGFzIHRzLkxpdGVyYWxUeXBlTm9kZSk7XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGxpdGVyYWwpKSB7XG5cdFx0XHRcdC8vIFJldHVybiB0aGUgYWN0dWFsIGxpdGVyYWwgdmFsdWUgKGUuZy4sICd1c2VyJyBpbnN0ZWFkIG9mIHN0cmluZylcblx0XHRcdFx0cmV0dXJuIGAnJHtsaXRlcmFsLnRleHR9J2A7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNOdW1lcmljTGl0ZXJhbChsaXRlcmFsKSkge1xuXHRcdFx0XHRyZXR1cm4gbGl0ZXJhbC50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0aWYgKGxpdGVyYWwua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCkge1xuXHRcdFx0XHRyZXR1cm4gJ3RydWUnO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGxpdGVyYWwua2luZCA9PT0gdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQpIHtcblx0XHRcdFx0cmV0dXJuICdmYWxzZSc7XG5cdFx0XHR9XG5cdFx0XHRpZiAobGl0ZXJhbC5raW5kID09PSB0cy5TeW50YXhLaW5kLk51bGxLZXl3b3JkKSB7XG5cdFx0XHRcdHJldHVybiAnbnVsbCc7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZVJlZmVyZW5jZToge1xuXHRcdFx0Ly8gSGFuZGxlIHR5cGUgcmVmZXJlbmNlcyBsaWtlIE1hcDxzdHJpbmcsIG51bWJlcj4sIFByb3BlcnR5SW5mbywgZXRjLlxuXHRcdFx0Y29uc3QgdHlwZVJlZiA9IHR5cGVOb2RlIGFzIHRzLlR5cGVSZWZlcmVuY2VOb2RlO1xuXG5cdFx0XHQvLyBRdWFsaWZpZWQgbmFtZXMgKE5hbWVzcGFjZS5UeXBlKTogcmVzb2x2ZSB0aHJvdWdoIG5hbWVzcGFjZSBpbXBvcnRzXG5cdFx0XHRpZiAodHMuaXNRdWFsaWZpZWROYW1lKHR5cGVSZWYudHlwZU5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHJlc29sdmVkUXVhbGlmaWVkID0gdGhpcy5pbmZlclF1YWxpZmllZFR5cGVSZWZlcmVuY2UodHlwZVJlZik7XG5cdFx0XHRcdGlmIChyZXNvbHZlZFF1YWxpZmllZCAhPT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHJlc29sdmVkUXVhbGlmaWVkO1xuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIHVucmVzb2x2ZWQgcXVhbGlmaWVkIHJlZmVyZW5jZXMgbXVzdCBub3QgbGVhayBhIGJhcmUgbmFtZVxuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXG5cdFx0XHRjb25zdCB0eXBlTmFtZSA9IHRzLmlzSWRlbnRpZmllcih0eXBlUmVmLnR5cGVOYW1lKSA/IHR5cGVSZWYudHlwZU5hbWUudGV4dCA6ICd1bmtub3duJztcblxuXHRcdFx0Ly8gSW1wb3J0LWF3YXJlIHJlZmVyZW5jZWQtdHlwZSByZXNvbHV0aW9uIChGMTApOiBhIGRlY2xhcmF0aW9uXG5cdFx0XHQvLyByZWFjaGVkIHRocm91Z2ggdGhlIGN1cnJlbnQgZmlsZSdzIG93biBpbXBvcnRzIChvciBpdHMgbG9jYWxzLFxuXHRcdFx0Ly8gb3IgYSB1bmlxdWUgcHJvZ3JhbS13aWRlIGRlY2xhcmF0aW9uKSBleHBhbmRzIGlubGluZVxuXHRcdFx0Y29uc3Qgc2ltcGxlUmVmID0gdGhpcy5yZXNvbHZlU2ltcGxlVHlwZVJlZmVyZW5jZSh0eXBlTmFtZSwgdHlwZVJlZi50eXBlQXJndW1lbnRzLCB0eXBlUmVmKTtcblx0XHRcdGlmIChzaW1wbGVSZWYgIT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRyZXR1cm4gc2ltcGxlUmVmO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBCdWlsZCBnZW5lcmljIHR5cGUgYXJndW1lbnRzXG5cdFx0XHRjb25zdCB0eXBlQXJncyA9ICh0eXBlUmVmLnR5cGVBcmd1bWVudHMgPz8gW10pLm1hcChhcmcgPT4gdGhpcy5pbmZlclR5cGUoYXJnKSk7XG5cdFx0XHRyZXR1cm4gYCR7dHlwZU5hbWV9PCR7dHlwZUFyZ3Muam9pbignLCAnKX0+YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVuaW9uVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHVuaW9uIHR5cGVzIGxpa2UgJ2EnIHwgJ2InIHwgJ2MnXG5cdFx0XHRjb25zdCB1bmlvblR5cGUgPSB0eXBlTm9kZSBhcyB0cy5VbmlvblR5cGVOb2RlO1xuXHRcdFx0Y29uc3QgdHlwZXMgPSB1bmlvblR5cGUudHlwZXMubWFwKHQgPT4gdGhpcy5pbmZlclR5cGUodCkpO1xuXHRcdFx0cmV0dXJuIHR5cGVzLmpvaW4oJyB8ICcpO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuSW50ZXJzZWN0aW9uVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIGludGVyc2VjdGlvbiB0eXBlcyBsaWtlIFR5cGVBICYgVHlwZUJcblx0XHRcdGNvbnN0IGludGVyc2VjdGlvblR5cGUgPSB0eXBlTm9kZSBhcyB0cy5JbnRlcnNlY3Rpb25UeXBlTm9kZTtcblx0XHRcdGNvbnN0IHR5cGVzID0gaW50ZXJzZWN0aW9uVHlwZS50eXBlcy5tYXAodCA9PiB0aGlzLmluZmVyVHlwZSh0KSk7XG5cdFx0XHRyZXR1cm4gdHlwZXMuam9pbignICYgJyk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UdXBsZVR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSB0dXBsZSB0eXBlcyBsaWtlIFtzdHJpbmcsIG51bWJlcl1cblx0XHRcdGNvbnN0IHR1cGxlVHlwZSA9IHR5cGVOb2RlIGFzIHRzLlR1cGxlVHlwZU5vZGU7XG5cdFx0XHRjb25zdCBlbGVtZW50cyA9IHR1cGxlVHlwZS5lbGVtZW50cy5tYXAoZWxlbSA9PiB0aGlzLmluZmVyVHlwZShlbGVtIGFzIHRzLlR5cGVOb2RlKSk7XG5cdFx0XHRyZXR1cm4gYFske2VsZW1lbnRzLmpvaW4oJywgJyl9XWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5PcHRpb25hbFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBvcHRpb25hbCBlbGVtZW50IGluIHR1cGxlOiBzdHJpbmc/XG5cdFx0XHRjb25zdCBvcHRpb25hbFR5cGUgPSB0eXBlTm9kZSBhcyB0cy5PcHRpb25hbFR5cGVOb2RlO1xuXHRcdFx0cmV0dXJuIGAke3RoaXMuaW5mZXJUeXBlKG9wdGlvbmFsVHlwZS50eXBlKSAgfT9gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuUmVzdFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSByZXN0IGVsZW1lbnQ6IC4uLlRcblx0XHRcdGNvbnN0IHJlc3RUeXBlID0gdHlwZU5vZGUgYXMgdHMuUmVzdFR5cGVOb2RlO1xuXHRcdFx0cmV0dXJuIGAuLi4keyAgdGhpcy5pbmZlclR5cGUocmVzdFR5cGUudHlwZSl9YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlBhcmVudGhlc2l6ZWRUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgcGFyZW50aGVzaXplZCB0eXBlczogKEEgfCBCKVxuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJUeXBlKCh0eXBlTm9kZSBhcyB0cy5QYXJlbnRoZXNpemVkVHlwZU5vZGUpLnR5cGUpO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuSW5kZXhlZEFjY2Vzc1R5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBpbmRleGVkIGFjY2VzczogVFtLXVxuXHRcdFx0Y29uc3QgaW5kZXhlZCA9IHR5cGVOb2RlIGFzIHRzLkluZGV4ZWRBY2Nlc3NUeXBlTm9kZTtcblx0XHRcdC8vIEYyMzogdW53cmFwIHBhcmVudGhlc2VzIGFyb3VuZCB0aGUgb2JqZWN0IOKAlCBgKHR5cGVvZlxuXHRcdFx0Ly8gbGlzdClbbnVtYmVyXWAgbXVzdCB0YWtlIHRoZSB0eXBlb2YgYnJhbmNoIGxpa2UgdGhlIGJhcmVcblx0XHRcdC8vIHNwZWxsaW5nOyBvdGhlcndpc2UgdGhlIGdlbmVyYWwgcGF0aCBpbmZlcnMgdGhlIHVuaW9uIGFuZFxuXHRcdFx0Ly8gZ2x1ZXMgdGhlIHN1ZmZpeCBvbnRvIHRoZSBMQVNUIG1lbWJlclxuXHRcdFx0Ly8gKGAnYScgfCAnYidbbnVtYmVyXWApXG5cdFx0XHRsZXQgb2JqZWN0Tm9kZTogdHMuVHlwZU5vZGUgPSBpbmRleGVkLm9iamVjdFR5cGU7XG5cdFx0XHR3aGlsZSAodHMuaXNQYXJlbnRoZXNpemVkVHlwZU5vZGUob2JqZWN0Tm9kZSkpIHtcblx0XHRcdFx0b2JqZWN0Tm9kZSA9IG9iamVjdE5vZGUudHlwZTtcblx0XHRcdH1cblx0XHRcdC8vIGB0eXBlb2YgY29uc3RBcnJheVtLXWAg4oCUIGVsZW1lbnQgdHlwZSBvZiBhIHRyYWNrZWQgY29uc3QgYXJyYXk6XG5cdFx0XHQvLyBlbWl0IHRoZSBlbGVtZW50IGxpdGVyYWwgdW5pb24gZGlyZWN0bHkgKGFzc2VtYmxpbmdcblx0XHRcdC8vIGB1bmlvbltLXWAgdGV4dCB3b3VsZCBtaXNyZWFkIHByZWNlZGVuY2UsIGFuZCB3aGVuIHRoZSBjb25zdFxuXHRcdFx0Ly8gaXMgbm90IHN0YXRpY2FsbHkgdmlzaWJsZSB0aGUgaG9uZXN0IGFuc3dlciBpcyBgdW5rbm93bmAsXG5cdFx0XHQvLyBuZXZlciBhIGJhcmUgYHR5cGVvZiBuYW1lYCBxdWVyeSlcblx0XHRcdGlmICh0cy5pc1R5cGVRdWVyeU5vZGUob2JqZWN0Tm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKG9iamVjdE5vZGUuZXhwck5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHF1ZXJ5TmFtZSA9IG9iamVjdE5vZGUuZXhwck5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgYXJyYXlMaXRlcmFsID0gdGhpcy5maW5kUmVmZXJlbmNlZENvbnN0QXJyYXkocXVlcnlOYW1lLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHRjb25zdCBsaXRlcmFscyA9IGFycmF5TGl0ZXJhbCA/IHRoaXMubGl0ZXJhbFR5cGVzT2ZBcnJheShhcnJheUxpdGVyYWwpIDogdW5kZWZpbmVkO1xuXHRcdFx0XHRpZiAoIWxpdGVyYWxzKSB7XG5cdFx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAodHMuaXNMaXRlcmFsVHlwZU5vZGUoaW5kZXhlZC5pbmRleFR5cGUpICYmIHRzLmlzTnVtZXJpY0xpdGVyYWwoaW5kZXhlZC5pbmRleFR5cGUubGl0ZXJhbCkpIHtcblx0XHRcdFx0XHRjb25zdCBlbGVtZW50SW5kZXggPSBwYXJzZUludChpbmRleGVkLmluZGV4VHlwZS5saXRlcmFsLnRleHQsIDEwKTtcblx0XHRcdFx0XHRjb25zdCBlbGVtZW50ID0gbGl0ZXJhbHNbIGVsZW1lbnRJbmRleCBdO1xuXHRcdFx0XHRcdGNvbnN0IGVsZW1lbnRSZXN1bHQgPSBlbGVtZW50ID09PSB1bmRlZmluZWQgPyAndW5rbm93bicgOiBlbGVtZW50O1xuXHRcdFx0XHRcdHJldHVybiBlbGVtZW50UmVzdWx0O1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IHVuaW9uUmVzdWx0ID0gbGl0ZXJhbHMuam9pbignIHwgJyk7XG5cdFx0XHRcdHJldHVybiB1bmlvblJlc3VsdDtcblx0XHRcdH1cblx0XHRcdGxldCBvYmplY3RUeXBlID0gdGhpcy5pbmZlclR5cGUob2JqZWN0Tm9kZSk7XG5cdFx0XHRjb25zdCBpbmRleFR5cGUgPSB0aGlzLmluZmVyVHlwZShpbmRleGVkLmluZGV4VHlwZSk7XG5cdFx0XHQvLyBJZiBvYmplY3RUeXBlIGlzICdvYmplY3QnLCB0cnkgdG8gcmVzb2x2ZSB0aGUgdW5kZXJseWluZyByZWZlcmVuY2VkIHR5cGVcblx0XHRcdGlmIChvYmplY3RUeXBlID09PSAnb2JqZWN0JyAmJiB0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKG9iamVjdE5vZGUpKSB7XG5cdFx0XHRcdGNvbnN0IHJlZk5hbWUgPSB0cy5pc0lkZW50aWZpZXIob2JqZWN0Tm9kZS50eXBlTmFtZSkgPyBvYmplY3ROb2RlLnR5cGVOYW1lLnRleHQgOiAnJztcblx0XHRcdFx0aWYgKHJlZk5hbWUpIHtcblx0XHRcdFx0XHRjb25zdCBkZWNsID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihyZWZOYW1lLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHRcdGlmIChkZWNsKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMuZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihkZWNsKTtcblx0XHRcdFx0XHRcdGlmIChleHBhbmRlZCkge1xuXHRcdFx0XHRcdFx0XHRvYmplY3RUeXBlID0gZXhwYW5kZWQ7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBJbnZhcmlhbnQ6IGFuIGluZGV4IHN1ZmZpeCBtdXN0IE5FVkVSIGJlIGdsdWVkIG9udG8gYW5cblx0XHRcdC8vIHVucmVzb2x2ZWQvZmFsbGJhY2sgdGFyZ2V0IOKAlCBgdW5rbm93bltudW1iZXJdYCAvIGBvYmplY3RbS11gXG5cdFx0XHQvLyBhcmUgaW52YWxpZCBUeXBlU2NyaXB0IGluIHRoZSBnZW5lcmF0ZWQgZmlsZSAoaGFyZCBjb21waWxlXG5cdFx0XHQvLyBicmVhaywgRjE3KS4gV2hlbiBlaXRoZXIgc2lkZSBkaWQgbm90IHJlc29sdmUsIHRoZSBXSE9MRVxuXHRcdFx0Ly8gaW5kZXhlZCBhY2Nlc3MgZGVncmFkZXMgdG8gYHVua25vd25gLlxuXHRcdFx0Y29uc3QgdGFyZ2V0VW5yZXNvbHZlZCA9IG9iamVjdFR5cGUgPT09ICd1bmtub3duJyB8fCBvYmplY3RUeXBlID09PSAnb2JqZWN0Jztcblx0XHRcdGNvbnN0IGluZGV4VW5yZXNvbHZlZCA9IGluZGV4VHlwZSA9PT0gJ3Vua25vd24nO1xuXHRcdFx0aWYgKHRhcmdldFVucmVzb2x2ZWQgfHwgaW5kZXhVbnJlc29sdmVkKSB7XG5cdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gYCR7b2JqZWN0VHlwZX1bJHtpbmRleFR5cGV9XWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlT3BlcmF0b3I6IHtcblx0XHRcdC8vIEhhbmRsZSBrZXlvZiwgcmVhZG9ubHksIHVuaXF1ZSBvcGVyYXRvcnNcblx0XHRcdGNvbnN0IHR5cGVPcCA9IHR5cGVOb2RlIGFzIHRzLlR5cGVPcGVyYXRvck5vZGU7XG5cdFx0XHRjb25zdCBvcGVyYXRvciA9IHRzLlN5bnRheEtpbmRbIHR5cGVPcC5vcGVyYXRvciBdO1xuXHRcdFx0cmV0dXJuIGAke29wZXJhdG9yfSAke3RoaXMuaW5mZXJUeXBlKHR5cGVPcC50eXBlKX1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZVF1ZXJ5OiB7XG5cdFx0XHQvLyBgdHlwZW9mIHhgIGFzIGEgRklFTEQgVFlQRTogdGhlIGdlbmVyYXRlZCBmaWxlIGhhcyBubyBpbXBvcnRzLFxuXHRcdFx0Ly8gc28gYSBiYXJlIGB0eXBlb2YgeGAgd291bGQgYmUgYW4gdW5yZXNvbHZhYmxlIG5hbWUgZG93bnN0cmVhbS5cblx0XHRcdC8vIFdoZW4geCBpcyBhIHRyYWNrZWQgY29uc3QgYXJyYXksIGVtaXQgaXRzIGVsZW1lbnQgbGl0ZXJhbFxuXHRcdFx0Ly8gdW5pb247IG90aGVyd2lzZSBkZWdyYWRlIHRvIGB1bmtub3duYC4gKEluc3RhbmNlVHlwZTx0eXBlb2YgWD5cblx0XHRcdC8vIGdyYXBoIHR5cGVzIGFyZSBoYW5kbGVkIGluIHJlc29sdmVTaW1wbGVUeXBlUmVmZXJlbmNlIGJlZm9yZVxuXHRcdFx0Ly8gaW5mZXJUeXBlIHJ1bnMuKVxuXHRcdFx0Y29uc3QgdHlwZVF1ZXJ5ID0gdHlwZU5vZGUgYXMgdHMuVHlwZVF1ZXJ5Tm9kZTtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIodHlwZVF1ZXJ5LmV4cHJOYW1lKSkge1xuXHRcdFx0XHRjb25zdCB1bmlvbiA9IHRoaXMudHlwZU9mQ29uc3RBcnJheVVuaW9uKHR5cGVRdWVyeS5leHByTmFtZS50ZXh0LCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHRpZiAodW5pb24pIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5pb247XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGRlZmF1bHQ6XG5cdFx0XHQvLyBGb3IgY29tcGxleCB0eXBlcywgcmV0dXJuIHRoZSB0ZXh0IHJlcHJlc2VudGF0aW9uXG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdCogSW5mZXIgcmV0dXJuIHR5cGUgZnJvbSBhIG1ldGhvZCBkZWNsYXJhdGlvblxuXHRcdCogVXNlcyBleHBsaWNpdCByZXR1cm4gdHlwZSBhbm5vdGF0aW9uIG9yIGluZmVycyBmcm9tIHJldHVybiBzdGF0ZW1lbnRzXG5cdFx0Ki9cblx0cHJpdmF0ZSBpbmZlclJldHVyblR5cGUgKG1ldGhvZDogdHMuTWV0aG9kRGVjbGFyYXRpb24sIGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz4pOiBzdHJpbmcge1xuXHRcdC8vIElmIG1ldGhvZCBoYXMgZXhwbGljaXQgcmV0dXJuIHR5cGUgYW5ub3RhdGlvbiwgdXNlIGl0XG5cdFx0aWYgKG1ldGhvZC50eXBlKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclR5cGUobWV0aG9kLnR5cGUpO1xuXHRcdH1cblxuXHRcdC8vIE90aGVyd2lzZSwgdHJ5IHRvIGluZmVyIGZyb20gcmV0dXJuIHN0YXRlbWVudHMgaW4gdGhlIG1ldGhvZCBib2R5XG5cdFx0aWYgKG1ldGhvZC5ib2R5KSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclJldHVyblR5cGVGcm9tQm9keShtZXRob2QuYm9keSwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHR9XG5cblx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBJbmZlciByZXR1cm4gdHlwZSBieSBhbmFseXppbmcgcmV0dXJuIHN0YXRlbWVudHMgaW4gdGhlIG1ldGhvZCBib2R5XG5cdFx0Ki9cblx0cHJpdmF0ZSBpbmZlclJldHVyblR5cGVGcm9tQm9keSAoYm9keTogdHMuQmxvY2ssIGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz4pOiBzdHJpbmcge1xuXHRcdGNvbnN0IHJldHVyblR5cGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cblx0XHRjb25zdCB2aXNpdCA9IChub2RlOiB0cy5Ob2RlKTogdm9pZCA9PiB7XG5cdFx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQobm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihub2RlLmV4cHJlc3Npb24sIHVuZGVmaW5lZCwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0aWYgKHR5cGUgIT09ICd1bmtub3duJykge1xuXHRcdFx0XHRcdHJldHVyblR5cGVzLmFkZCh0eXBlKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIHZpc2l0KTtcblx0XHR9O1xuXG5cdFx0dmlzaXQoYm9keSk7XG5cblx0XHRpZiAocmV0dXJuVHlwZXMuc2l6ZSA9PT0gMCkge1xuXHRcdFx0cmV0dXJuICd2b2lkJztcblx0XHR9XG5cdFx0aWYgKHJldHVyblR5cGVzLnNpemUgPT09IDEpIHtcblx0XHRcdHJldHVybiBBcnJheS5mcm9tKHJldHVyblR5cGVzKVsgMCBdO1xuXHRcdH1cblx0XHRyZXR1cm4gQXJyYXkuZnJvbShyZXR1cm5UeXBlcykuam9pbignIHwgJyk7XG5cdH1cblxuXHQvKipcblx0ICogSW5mZXIgdHlwZSBmcm9tIGluaXRpYWxpemVyXG5cdCAqL1xuXHRwcml2YXRlIGluZmVyVHlwZUZyb21Jbml0aWFsaXplciAoXG5cdFx0aW5pdGlhbGl6ZXI6IHRzLkV4cHJlc3Npb24sXG5cdFx0ZGF0YVR5cGVNYXA/OiBNYXA8c3RyaW5nLCBzdHJpbmc+LFxuXHRcdGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz5cblx0KTogc3RyaW5nIHtcblx0XHRzd2l0Y2ggKGluaXRpYWxpemVyLmtpbmQpIHtcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuU3RyaW5nTGl0ZXJhbDpcblx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVtZXJpY0xpdGVyYWw6XG5cdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkOlxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdWxsS2V5d29yZDpcblx0XHRcdHJldHVybiAnbnVsbCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVuZGVmaW5lZEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3VuZGVmaW5lZCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkFycmF5TGl0ZXJhbEV4cHJlc3Npb246XG5cdFx0XHRyZXR1cm4gJ0FycmF5PHVua25vd24+Jztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb246XG5cdFx0XHRyZXR1cm4gJ29iamVjdCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk5ld0V4cHJlc3Npb246IHtcblx0XHRcdC8vIEhhbmRsZSBuZXcgRGF0ZSgpLCBuZXcgTWFwKCksIGV0Yy5cblx0XHRcdGNvbnN0IG5ld0V4cHIgPSBpbml0aWFsaXplciBhcyB0cy5OZXdFeHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihuZXdFeHByLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IGNvbnN0cnVjdGVkTmFtZSA9IG5ld0V4cHIuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHQvLyBFeHBsaWNpdCB0eXBlIGFyZ3VtZW50cyBzdXJ2aXZlOiBuZXcgTWFwPHN0cmluZywgb2JqZWN0PigpXG5cdFx0XHRcdC8vIGVtaXRzIE1hcDxzdHJpbmcsIG9iamVjdD4g4oCUIGRyb3BwaW5nIHRoZW0gcHJvZHVjZWQgYSBiYXJlXG5cdFx0XHRcdC8vIGdlbmVyaWMsIHdoaWNoIGlzIGludmFsaWQgVFMgaW4gdGhlIGdlbmVyYXRlZCBmaWxlIChUUzIzMTQpXG5cdFx0XHRcdGlmIChuZXdFeHByLnR5cGVBcmd1bWVudHMgJiYgbmV3RXhwci50eXBlQXJndW1lbnRzLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0XHRjb25zdCBhcmdUeXBlcyA9IG5ld0V4cHIudHlwZUFyZ3VtZW50cy5tYXAoYXJnID0+IHRoaXMuaW5mZXJUeXBlKGFyZykpO1xuXHRcdFx0XHRcdHJldHVybiBgJHtjb25zdHJ1Y3RlZE5hbWV9PCR7YXJnVHlwZXMuam9pbignLCAnKX0+YDtcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBObyB0eXBlIGFyZ3VtZW50czogYSBrbm93biBnZW5lcmljIGdsb2JhbCBzdGlsbCBuZWVkcyBpdHNcblx0XHRcdFx0Ly8gcGFyYW1ldGVyIGxpc3Qg4oCUIGZpbGwgaXQgd2l0aCB1bmtub3duIChNYXA8dW5rbm93biwgdW5rbm93bj4pXG5cdFx0XHRcdGNvbnN0IGRlZmF1bHRlZEdlbmVyaWMgPSBHRU5FUklDX0dMT0JBTF9ERUZBVUxUX0FSR1MuZ2V0KGNvbnN0cnVjdGVkTmFtZSk7XG5cdFx0XHRcdGlmIChkZWZhdWx0ZWRHZW5lcmljKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGRlZmF1bHRlZEdlbmVyaWM7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIGNvbnN0cnVjdGVkTmFtZTtcblx0XHRcdH1cblx0XHRcdHJldHVybiAnb2JqZWN0Jztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkJpbmFyeUV4cHJlc3Npb246IHtcblx0XHRcdC8vIEhhbmRsZSBhcml0aG1ldGljIG9wZXJhdGlvbnM6IGEgKiBiLCBhICsgYiwgYSAtIGIsIGEgLyBiXG5cdFx0XHRjb25zdCBiaW5hcnlFeHByID0gaW5pdGlhbGl6ZXIgYXMgdHMuQmluYXJ5RXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IGxlZnRUeXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIoYmluYXJ5RXhwci5sZWZ0LCBkYXRhVHlwZU1hcCwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdGNvbnN0IHJpZ2h0VHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKGJpbmFyeUV4cHIucmlnaHQsIGRhdGFUeXBlTWFwLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0XHRcblx0XHRcdC8vIENoZWNrIGlmIGl0J3MgYW4gYXJpdGhtZXRpYyBvcGVyYXRvclxuXHRcdFx0Y29uc3Qgb3BlcmF0b3IgPSBiaW5hcnlFeHByLm9wZXJhdG9yVG9rZW4ua2luZDtcblx0XHRcdGlmIChvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5Bc3Rlcmlza1Rva2VuIHx8XG5cdFx0XHRcdCAgICBvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5TbGFzaFRva2VuIHx8XG5cdFx0XHRcdCAgICBvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5NaW51c1Rva2VuIHx8XG5cdFx0XHRcdCAgICBvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5QZXJjZW50VG9rZW4pIHtcblx0XHRcdFx0Ly8gQXJpdGhtZXRpYyBvcGVyYXRpb25zIG9uIG51bWJlcnMgcHJvZHVjZSBudW1iZXJzXG5cdFx0XHRcdGlmICgobGVmdFR5cGUgPT09ICdudW1iZXInIHx8IGxlZnRUeXBlID09PSAndW5rbm93bicpICYmXG5cdFx0XHRcdFx0ICAgIChyaWdodFR5cGUgPT09ICdudW1iZXInIHx8IHJpZ2h0VHlwZSA9PT0gJ3Vua25vd24nKSkge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLlBsdXNUb2tlbikge1xuXHRcdFx0XHQvLyBQbHVzIGNhbiBiZSBhZGRpdGlvbiBvciBzdHJpbmcgY29uY2F0ZW5hdGlvblxuXHRcdFx0XHRpZiAobGVmdFR5cGUgPT09ICdzdHJpbmcnIHx8IHJpZ2h0VHlwZSA9PT0gJ3N0cmluZycpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGxlZnRUeXBlID09PSAnbnVtYmVyJyAmJiByaWdodFR5cGUgPT09ICdudW1iZXInKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgcHJvcGVydHkgYWNjZXNzIGxpa2UgZGF0YS52YWx1ZSwgZGF0YS5pZFxuXHRcdFx0aWYgKGRhdGFUeXBlTWFwKSB7XG5cdFx0XHRcdGNvbnN0IGFjY2Vzc0NoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGluaXRpYWxpemVyKTtcblx0XHRcdFx0aWYgKGFjY2Vzc0NoYWluKSB7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IGRhdGFUeXBlTWFwLmdldChhY2Nlc3NDaGFpbik7XG5cdFx0XHRcdFx0aWYgKHR5cGUpIHtcblx0XHRcdFx0XHRcdHJldHVybiB0eXBlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gSGFuZGxlIHRoaXMubWFwLnNpemUgcGF0dGVybiAoTWFwLnNpemUgcmV0dXJucyBudW1iZXIpXG5cdFx0XHRjb25zdCBwcm9wQWNjZXNzID0gaW5pdGlhbGl6ZXIgYXMgdHMuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKHByb3BBY2Nlc3MuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y29uc3Qgb3V0ZXJQcm9wID0gcHJvcEFjY2Vzcy5leHByZXNzaW9uO1xuXHRcdFx0XHQvLyBDaGVjayBmb3IgdGhpcy5tYXAgcGF0dGVyblxuXHRcdFx0XHRsZXQgaW5uZXJOYW1lID0gJyc7XG5cdFx0XHRcdGlmIChvdXRlclByb3AuZXhwcmVzc2lvbi5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0aW5uZXJOYW1lID0gJ3RoaXMnO1xuXHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihvdXRlclByb3AuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRpbm5lck5hbWUgPSBvdXRlclByb3AuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IG1hcFByb3AgPSBvdXRlclByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBmaW5hbFByb3AgPSBwcm9wQWNjZXNzLm5hbWUudGV4dDtcblx0XHRcdFx0Ly8gdGhpcy5tYXAuc2l6ZSAtPiBudW1iZXJcblx0XHRcdFx0aWYgKGlubmVyTmFtZSA9PT0gJ3RoaXMnICYmIG1hcFByb3AgPT09ICdtYXAnICYmIGZpbmFsUHJvcCA9PT0gJ3NpemUnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuSWRlbnRpZmllcjoge1xuXHRcdFx0Ly8gSGFuZGxlIGlkZW50aWZpZXIgcmVmZXJlbmNlcyBpZiBpbiBkYXRhVHlwZU1hcFxuXHRcdFx0aWYgKGRhdGFUeXBlTWFwKSB7XG5cdFx0XHRcdGNvbnN0IG5hbWUgPSAoaW5pdGlhbGl6ZXIgYXMgdHMuSWRlbnRpZmllcikudGV4dDtcblx0XHRcdFx0Y29uc3QgdHlwZSA9IGRhdGFUeXBlTWFwLmdldChuYW1lKTtcblx0XHRcdFx0aWYgKHR5cGUpIHtcblx0XHRcdFx0XHRyZXR1cm4gdHlwZTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkVsZW1lbnRBY2Nlc3NFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBGMjI6IHZhbHVlLWxldmVsIGVsZW1lbnQgYWNjZXNzIG92ZXIgYSBjb25zdC1hc3NlcnRlZFxuXHRcdFx0Ly8gbGl0ZXJhbCBhcnJheSDigJQgYCg8Y29uc3Q+W+KApl0pWzBdYCwgYChb4oCmXSBhcyBjb25zdClbMV1gLCBvclxuXHRcdFx0Ly8gYSB0cmFja2VkIG1vZHVsZSBjb25zdCAoYGNvbnN0IHggPSA8Y29uc3Q+W+KApl1gOyBgeFswXWApIOKAlFxuXHRcdFx0Ly8gaW5mZXJzIHRoZSBlbGVtZW50J3MgbGl0ZXJhbCB0eXBlLCB0aGUgdmFsdWUtbGV2ZWwgdHdpbiBvZlxuXHRcdFx0Ly8gdGhlIHR5cGVvZi1wYXRoIHVuaW9uLiBOb24tbnVtZXJpYyBpbmRleGVzLCBub24tbGl0ZXJhbFxuXHRcdFx0Ly8gZWxlbWVudHMsIGFuZCBnZW5lcmFsIGFzc2VydGlvbnMgc3RheSBgdW5rbm93bmAuXG5cdFx0XHRjb25zdCBlbGVtZW50QWNjZXNzID0gaW5pdGlhbGl6ZXIgYXMgdHMuRWxlbWVudEFjY2Vzc0V4cHJlc3Npb247XG5cdFx0XHRjb25zdCBhcmd1bWVudCA9IGVsZW1lbnRBY2Nlc3MuYXJndW1lbnRFeHByZXNzaW9uO1xuXHRcdFx0aWYgKCFhcmd1bWVudCB8fCAhdHMuaXNOdW1lcmljTGl0ZXJhbChhcmd1bWVudCkpIHtcblx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdH1cblx0XHRcdGNvbnN0IGFycmF5TGl0ZXJhbCA9IHRoaXMuY29uc3RBcnJheUxpdGVyYWxPZihlbGVtZW50QWNjZXNzLmV4cHJlc3Npb24pO1xuXHRcdFx0aWYgKCFhcnJheUxpdGVyYWwpIHtcblx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdH1cblx0XHRcdGNvbnN0IGVsZW1lbnQgPSBhcnJheUxpdGVyYWwuZWxlbWVudHNbIHBhcnNlSW50KGFyZ3VtZW50LnRleHQsIDEwKSBdO1xuXHRcdFx0aWYgKCFlbGVtZW50IHx8IHRzLmlzU3ByZWFkRWxlbWVudChlbGVtZW50KSkge1xuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbGl0ZXJhbCA9IHRoaXMubGl0ZXJhbFR5cGVPZkV4cHJlc3Npb24oZWxlbWVudCk7XG5cdFx0XHRjb25zdCBlbGVtZW50UmVzdWx0ID0gbGl0ZXJhbCA/PyAndW5rbm93bic7XG5cdFx0XHRyZXR1cm4gZWxlbWVudFJlc3VsdDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkNhbGxFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgZnVuY3Rpb24gY2FsbHMgbGlrZSBEYXRlLm5vdygpLCBwYXJzZUludCgpLCBldGMuXG5cdFx0XHRjb25zdCBjYWxsRXhwciA9IGluaXRpYWxpemVyIGFzIHRzLkNhbGxFeHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxFeHByLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IG1ldGhvZE5hbWUgPSBjYWxsRXhwci5leHByZXNzaW9uLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3Qgb2JqTmFtZSA9IHRzLmlzSWRlbnRpZmllcihjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb24pXG5cdFx0XHRcdFx0PyBjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb24udGV4dFxuXHRcdFx0XHRcdDogJyc7XG5cdFx0XHRcdFx0XG5cdFx0XHRcdC8vIERhdGUubm93KCkgLT4gbnVtYmVyXG5cdFx0XHRcdGlmIChvYmpOYW1lID09PSAnRGF0ZScgJiYgbWV0aG9kTmFtZSA9PT0gJ25vdycpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gU3RyaW5nIG1ldGhvZHMgdGhhdCByZXR1cm4gc3RyaW5nXG5cdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAndG9TdHJpbmcnIHx8IG1ldGhvZE5hbWUgPT09ICd2YWx1ZU9mJykge1xuXHRcdFx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBIYW5kbGUgTWFwIHByb3BlcnR5IGFjY2VzcyBvbiBjbGFzcyBpbnN0YW5jZXMgKHRoaXMubWFwLiopXG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0Y29uc3Qgb3V0ZXJQcm9wID0gY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdFx0XHRcdC8vIEhhbmRsZSBib3RoICd0aGlzJyBrZXl3b3JkIGFuZCBpZGVudGlmaWVyIHBhdHRlcm5zXG5cdFx0XHRcdFx0bGV0IGlubmVyTmFtZSA9ICcnO1xuXHRcdFx0XHRcdGlmIChvdXRlclByb3AuZXhwcmVzc2lvbi5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0XHRpbm5lck5hbWUgPSAndGhpcyc7XG5cdFx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc0lkZW50aWZpZXIob3V0ZXJQcm9wLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0XHRpbm5lck5hbWUgPSBvdXRlclByb3AuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCBtYXBQcm9wID0gb3V0ZXJQcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0XHQvLyB0aGlzLm1hcC5YKCkgcGF0dGVybnNcblx0XHRcdFx0XHRpZiAoaW5uZXJOYW1lID09PSAndGhpcycgJiYgbWFwUHJvcCA9PT0gJ21hcCcpIHtcblx0XHRcdFx0XHRcdC8vIFRyeSB0byBnZXQgdGhlIE1hcCdzIHZhbHVlIHR5cGUgZnJvbSBjbGFzcyBwcm9wZXJ0aWVzXG5cdFx0XHRcdFx0XHRsZXQgbWFwVmFsdWVUeXBlID0gJ3Vua25vd24nO1xuXHRcdFx0XHRcdFx0aWYgKGNsYXNzUHJvcGVydHlUeXBlcykge1xuXHRcdFx0XHRcdFx0XHRjb25zdCBtYXBUeXBlID0gY2xhc3NQcm9wZXJ0eVR5cGVzLmdldCgnbWFwJyk7XG5cdFx0XHRcdFx0XHRcdGlmIChtYXBUeXBlICYmIG1hcFR5cGUuc3RhcnRzV2l0aCgnTWFwPCcpKSB7XG5cdFx0XHRcdFx0XHRcdFx0Ly8gUGFyc2UgTWFwPEssIFY+IHRvIGdldCBWXG5cdFx0XHRcdFx0XHRcdFx0Y29uc3QgbWF0Y2ggPSBtYXBUeXBlLm1hdGNoKC9NYXA8W14sXSssXFxzKiguKyk+JC8pO1xuXHRcdFx0XHRcdFx0XHRcdGlmIChtYXRjaCkge1xuXHRcdFx0XHRcdFx0XHRcdFx0WyAsIG1hcFZhbHVlVHlwZSBdID0gbWF0Y2g7XG5cdFx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2hhcycpIHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3NldCcpIHJldHVybiAndGhpcyc7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2dldCcpIHJldHVybiBtYXBWYWx1ZVR5cGU7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2RlbGV0ZScpIHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2NsZWFyJykgcmV0dXJuICd2b2lkJztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAndmFsdWVzJykgcmV0dXJuIGBJdGVyYWJsZUl0ZXJhdG9yPCR7bWFwVmFsdWVUeXBlfT5gO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdrZXlzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPHN0cmluZz4nO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdlbnRyaWVzJykgcmV0dXJuIGBJdGVyYWJsZUl0ZXJhdG9yPFtzdHJpbmcsICR7bWFwVmFsdWVUeXBlfV0+YDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gRGlyZWN0IG1hcC5YKCkgY2FsbHNcblx0XHRcdFx0aWYgKG9iak5hbWUgPT09ICdtYXAnIHx8IG9iak5hbWUgPT09ICdvYmonKSB7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdoYXMnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnc2V0JykgcmV0dXJuICd0aGlzJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2dldCcpIHJldHVybiAndW5rbm93bic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdkZWxldGUnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnY2xlYXInKSByZXR1cm4gJ3ZvaWQnO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAndmFsdWVzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPHVua25vd24+Jztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2tleXMnKSByZXR1cm4gJ0l0ZXJhYmxlSXRlcmF0b3I8c3RyaW5nPic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdlbnRyaWVzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPFtzdHJpbmcsIHVua25vd25dPic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIHBhcnNlSW50LCBwYXJzZUZsb2F0IC0+IG51bWJlclxuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjYWxsRXhwci5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBmbk5hbWUgPSBjYWxsRXhwci5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdwYXJzZUludCcgfHwgZm5OYW1lID09PSAncGFyc2VGbG9hdCcpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ1N0cmluZycpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ051bWJlcicpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ0Jvb2xlYW4nKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlRlbXBsYXRlRXhwcmVzc2lvbjpcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTm9TdWJzdGl0dXRpb25UZW1wbGF0ZUxpdGVyYWw6IHtcblx0XHRcdC8vIFRlbXBsYXRlIGxpdGVyYWxzIGxpa2UgYCR7YmFzZVZhbHVlfS0ke2V4dHJhfWAgYWx3YXlzIHByb2R1Y2Ugc3RyaW5nc1xuXHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdH1cblx0XHRkZWZhdWx0OlxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0KiBDb2xsZWN0IHVzYWdlIGluZm9ybWF0aW9uIGZvciB0eXBlIHJlZmVyZW5jZXNcblx0XHRcdCovXG5cdHByaXZhdGUgY29sbGVjdFVzYWdlIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgZm9yIG5ldyBUeXBlKCkgaW5zdGFudGlhdGlvblxuXHRcdGlmICh0cy5pc05ld0V4cHJlc3Npb24obm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRsZXQgdHlwZU5hbWU6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdHR5cGVOYW1lID0gdGhpcy5yZXNvbHZlVHlwZVBhdGgobm9kZS5leHByZXNzaW9uKTtcblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdHR5cGVOYW1lID0gdGhpcy5nZXRUeXBlTmFtZUZyb21FeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHlwZU5hbWUpIHtcblx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHQpO1xuXHRcdFx0XHR0aGlzLmFkZFVzYWdlKHR5cGVOYW1lLCB7XG5cdFx0XHRcdFx0bG9jYXRpb24gICAgICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0a2luZCAgICAgICAgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0XHRcdGNvZGUgICAgICAgICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdC8vIENvbnN0cnVjdG9yIGV4cHJlc3Npb24gdGV4dCAoJ1RoaW5nJywgJ3VzZXIuQWRtaW5FbnRpdHknLFxuXHRcdFx0XHRcdC8vIGEgbG9va3VwIGFsaWFzKSDigJQgQ3JlYXRpb25BbmNob3IuY29uc3RydWN0b3JUZXh0IChQaGFzZSAzKVxuXHRcdFx0XHRcdGNvbnN0cnVjdG9yVGV4dCA6IG5vZGUuZXhwcmVzc2lvbi5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdH0pO1xuXHRcdFx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50IGZyb20gbmV3IFR5cGUoKSBmb3IgZmxvdyBhbmFseXNpc1xuXHRcdFx0XHR0aGlzLnRyYWNrTmV3QXNzaWdubWVudChub2RlLCB0eXBlTmFtZSk7XG5cdFx0XHRcdC8vIEFsc28gcmVjb3JkIGFzIGZsb3cgZXZlbnRcblx0XHRcdFx0dGhpcy5hZGRGbG93KHR5cGVOYW1lLCB7XG5cdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRraW5kICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdGNvbnRleHQgIDogJ25ldyBleHByZXNzaW9uJyxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcblx0XHQvLyBDaGVjayBmb3IgcHJvcGVydHkgYWNjZXNzIG9uIGluc3RhbmNlcyAodXNlci5BZG1pblR5cGUpXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRjb25zdCBwcm9wTmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0Ly8gaW5zdGFuY2UuY2xvbmUg4oCUIHRoZSBQUk9QRVJUWSBmb3JtIChjb3JlIHR5cGVzIGl0XG5cdFx0XHQvLyBgcmVhZG9ubHkgY2xvbmU6IHRoaXNgKTogdGhlIHJlc3VsdCB2YXJpYWJsZSBiaW5kcyB0byB0aGVcblx0XHRcdC8vIHNvdXJjZSBpbnN0YW5jZSdzIHR5cGUsIHNhbWUgYXMgdGhlIGZvcmsoKS9jbG9uZSgpIGNhbGxcblx0XHRcdC8vIGZvcm1zIChhd2FpdC10cmFuc3BhcmVudCkuIFRoZSBjYWxsIGZvcm0ncyByZWNvcmRpbmcgaGFwcGVuc1xuXHRcdFx0Ly8gaW4gdGhlIENhbGxFeHByZXNzaW9uIGJyYW5jaDsgdGhlIHByb3BlcnR5IGJyYW5jaCBza2lwcyBpdFxuXHRcdFx0Ly8gdG8gYXZvaWQgYSBkdXBsaWNhdGUgZW50cnkgYXQgdGhlIHNhbWUgc2l0ZVxuXHRcdFx0aWYgKHByb3BOYW1lID09PSAnY2xvbmUnICYmIHRzLmlzSWRlbnRpZmllcihub2RlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IGNsb25lZFBhdGggPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChub2RlLmV4cHJlc3Npb24udGV4dCk7XG5cdFx0XHRcdGNvbnN0IGlzQ2FsbEZvcm0gPSB0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUucGFyZW50KSAmJiBub2RlLnBhcmVudC5leHByZXNzaW9uID09PSBub2RlO1xuXHRcdFx0XHRpZiAoY2xvbmVkUGF0aCkge1xuXHRcdFx0XHRcdGlmICghaXNDYWxsRm9ybSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdFx0XHQpO1xuXHRcdFx0XHRcdFx0dGhpcy5hZGRVc2FnZShjbG9uZWRQYXRoLCB7XG5cdFx0XHRcdFx0XHRcdGxvY2F0aW9uICAgICAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdFx0XHRraW5kICAgICAgICAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0XHRcdGNvZGUgICAgICAgICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdFx0XHRjb25zdHJ1Y3RvclRleHQgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShub2RlLCBjbG9uZWRQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gQ2hlY2sgaWYgdGhpcyBsb29rcyBsaWtlIGEgdHlwZSBhY2Nlc3MgcGF0dGVyblxuXHRcdFx0aWYgKHByb3BOYW1lICYmIHRoaXMuaXNMaWtlbHlUeXBlTmFtZShwcm9wTmFtZSkpIHtcblx0XHRcdFx0Ly8gbmV3IHguU3ViKOKApik6IHRoZSBOZXdFeHByZXNzaW9uIGJyYW5jaCBhbHJlYWR5IHJlY29yZGVkXG5cdFx0XHRcdC8vIHRoZSBzaXRlIGFzIGFuIGluc3RhbnRpYXRpb24sIHNvIGEgcHJvcGVydHlBY2Nlc3MgcmVjb3JkXG5cdFx0XHRcdC8vIHdvdWxkIGR1cGxpY2F0ZSBpdCDigJQgb25lIHJlY29yZCBwZXIgc2l0ZSwgdGhlIHNhbWUgbGF3IGFzXG5cdFx0XHRcdC8vIHRoZSBjbG9uZSBndWFyZCBhYm92ZS4gKEEgd2hvbGUtY2FsbGVlLXBhcmVudGhlc2l6ZWRcblx0XHRcdFx0Ly8gbmV3ICh4LlN1YikoKSBuZXZlciBtYXRjaGVzIGhlcmU6IHRoZSBhY2Nlc3MncyBwYXJlbnQgaXNcblx0XHRcdFx0Ly8gdGhlIFBhcmVudGhlc2l6ZWRFeHByZXNzaW9uLCBhbmQgdGhlIGluc3RhbnRpYXRpb24gYnJhbmNoXG5cdFx0XHRcdC8vIGNhbm5vdCByZXNvbHZlIHRoYXQgY2FsbGVlIOKAlCB0aGlzIGFjY2VzcyBzdGF5cyB0aGUgc2l0ZSdzXG5cdFx0XHRcdC8vIG9ubHkgcmVjb3JkLilcblx0XHRcdFx0Y29uc3QgaXNOZXdDYWxsZWUgPSB0cy5pc05ld0V4cHJlc3Npb24obm9kZS5wYXJlbnQpICYmIG5vZGUucGFyZW50LmV4cHJlc3Npb24gPT09IG5vZGU7XG5cdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0XHQvLyBUcnkgdG8gcmVzb2x2ZSBmdWxsIHBhdGhcblx0XHRcdFx0Y29uc3QgZnVsbFBhdGggPSB0aGlzLnJlc29sdmVUeXBlUGF0aChub2RlKTtcblx0XHRcdFx0aWYgKGZ1bGxQYXRoICYmICFpc05ld0NhbGxlZSkge1xuXHRcdFx0XHRcdHRoaXMuYWRkVXNhZ2UoZnVsbFBhdGgsIHtcblx0XHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0XHRraW5kICAgICA6ICdwcm9wZXJ0eUFjY2VzcycsXG5cdFx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcblx0XHQvLyBDaGVjayBmb3IgbG9va3VwKCdUeXBlTmFtZScpIG9yIGxvb2t1cChzb3VyY2UsICdUeXBlTmFtZScpIGNhbGxzXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRjb25zdCBmdW5jTmFtZSA9IHRoaXMuZ2V0RnVuY3Rpb25OYW1lKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoZnVuY05hbWUgPT09ICdsb29rdXAnICYmIG5vZGUuYXJndW1lbnRzLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0Y29uc3QgdHlwZVBhdGggPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKG5vZGUpO1xuXHRcdFx0XHRpZiAodHlwZVBhdGgpIHtcblx0XHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHRcdCk7XG5cdFx0XHRcdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRcdFx0XHR0aGlzLmFkZFVzYWdlKHR5cGVQYXRoLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0XHRcdGtpbmQgOiAnbG9va3VwJyxcblx0XHRcdFx0XHRcdGNvZGUgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50IGZyb20gbG9va3VwIGZvciBpbnN0YW50aWF0aW9uIHRyYWNraW5nXG5cdFx0XHRcdFx0dGhpcy50cmFja0xvb2t1cEFzc2lnbm1lbnQobm9kZSwgdHlwZVBhdGgpO1xuXHRcdFx0XHRcdC8vIFJlY29yZCBmb3IgdGhlIGhhcmQtZmFpbCBsYXcgZXZlbiB3aGVuIGFkZFVzYWdlIGRyb3BwZWRcblx0XHRcdFx0XHQvLyB0aGUgcGF0aCAodW5rbm93biBwYXRocyBhcmUgZXhhY3RseSB0aGUgZmFpbHVyZSBjbGFzcylcblx0XHRcdFx0XHR0aGlzLmxvb2t1cFJlZmVyZW5jZXMucHVzaCh7IHBhdGggOiB0eXBlUGF0aCwgbG9jYXRpb24gfSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblxuXHRcdFx0Ly8gQ2hhaW4tZm9ybSBjb25zdHJ1Y3Rpb246IGBuZXcgUiguLi4pLkEoLi4uKWAgLyB0aGUgYXdhaXRlZFxuXHRcdFx0Ly8gc2luZ2xlLWNoYWluIGBhd2FpdCBuZXcgUiguLi4pLkEoLi4uKS5CKC4uLilgIOKAlCB0aGUgY2FsbCBvblxuXHRcdFx0Ly8gdGhlIGZyZXNoIGluc3RhbmNlIGNvbnN0cnVjdHMgdGhlIGNoYWluIFRJUCAoYXdhaXQgaXNcblx0XHRcdC8vIHRyYW5zcGFyZW50OyB0aGUgTmV3RXhwcmVzc2lvbiBicmFuY2ggYWxyZWFkeSByZWNvcmRlZCB0aGVcblx0XHRcdC8vIGlubmVyIHJvb3QpLiBUaGUgcmVzdWx0IHZhcmlhYmxlIGJpbmRzIHRvIHRoZSB0aXAsIG5vdCB0aGVcblx0XHRcdC8vIHJvb3QgKHRyYWNrTmV3QXNzaWdubWVudCByZXNvbHZlcyB0aGUgc2FtZSB0aXApXG5cdFx0XHRjb25zdCBjaGFpblRpcCA9IHRoaXMucmVzb2x2ZUNoYWluVGlwVHlwZVBhdGgobm9kZSk7XG5cdFx0XHRpZiAoY2hhaW5UaXApIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZShub2RlLCBjaGFpblRpcCwgc291cmNlRmlsZSk7XG5cdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0dGhpcy5hZGRGbG93KGNoYWluVGlwLCB7XG5cdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRraW5kICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdGNvbnRleHQgIDogJ2NoYWluZWQgY29uc3RydWN0aW9uJyxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cblx0XHRcdC8vIG1uZW1vbmljYSBjYWxsL2FwcGx5KGVudGl0eSwgQ3RvciwgLi4uKSAvIGJpbmQoZW50aXR5LCBDdG9yKSDigJRcblx0XHRcdC8vIHR5cGVkIGNvbnN0cnVjdGlvbiB3aXRob3V0IGBuZXdgOiB0aGUgQ3RvciBhcmd1bWVudCAoYXJnIDEpIGlzXG5cdFx0XHQvLyB0aGUgY29uc3RydWN0ZWQgdHlwZS4gSW1wb3J0LWF3YXJlOiBvbmx5IGlkZW50aWZpZXJzIGFjdHVhbGx5XG5cdFx0XHQvLyBpbXBvcnRlZCBmcm9tICdtbmVtb25pY2EnIChvciBtZW1iZXJzIG9mIGEgdHJhY2tlZFxuXHRcdFx0Ly8gbW9kdWxlLW9iamVjdCBhbGlhcykgbWF0Y2gg4oCUIHVzZXJsYW5kIGNhbGwvYXBwbHkvYmluZCBuZXZlclxuXHRcdFx0Ly8gZG8uIGNhbGwvYXBwbHkgcmVjb3JkIHRoZSBjb25zdHJ1Y3Rpb247IGJpbmQoKSBjb25zdHJ1Y3RzXG5cdFx0XHQvLyBub3RoaW5nIOKAlCBpdCBvbmx5IGJpbmRzIHRoZSByZXN1bHQgdmFyaWFibGUgdG8gdGhlIEN0b3Inc1xuXHRcdFx0Ly8gdHlwZSAocnVudGltZSBJbnN0YW5jZVJlc3VsdDxNZXJnZTxFLFQ+PiBhcHByb3hpbWF0ZWQgYnkgVFxuXHRcdFx0Ly8gd2l0aGluIHRoZSBvdXRwdXQgY29udHJhY3QpXG5cdFx0XHRjb25zdCBjb25zdHJ1Y3Rpb25QYXRoID0gdGhpcy5yZXNvbHZlQ29uc3RydWN0aW9uRm5UeXBlUGF0aChub2RlKTtcblx0XHRcdGlmIChjb25zdHJ1Y3Rpb25QYXRoKSB7XG5cdFx0XHRcdGNvbnN0IGlzQmluZEZvcm0gPSB0aGlzLmlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4obm9kZS5leHByZXNzaW9uLCAnYmluZCcpO1xuXHRcdFx0XHRpZiAoIWlzQmluZEZvcm0pIHtcblx0XHRcdFx0XHRjb25zdCBjdG9yQXJnVGV4dCA9IG5vZGUuYXJndW1lbnRzWyAxIF0/LmdldFRleHQoc291cmNlRmlsZSk7XG5cdFx0XHRcdFx0dGhpcy5yZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZShub2RlLCBjb25zdHJ1Y3Rpb25QYXRoLCBzb3VyY2VGaWxlLCBjdG9yQXJnVGV4dCk7XG5cdFx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0XHQpO1xuXHRcdFx0XHRcdHRoaXMuYWRkRmxvdyhjb25zdHJ1Y3Rpb25QYXRoLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdFx0a2luZCAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdFx0Y29udGV4dCAgOiAnY2FsbC9hcHBseSBjb25zdHJ1Y3Rpb24nLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHRoaXMuYmluZFJlc3VsdFZhcmlhYmxlKG5vZGUsIGNvbnN0cnVjdGlvblBhdGgpO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBpbnN0YW5jZS5mb3JrKCkvY2xvbmUoKSDigJQgcnVudGltZSByZS1ydW5zIGNvbnN0cnVjdGlvbiAoaG9va3Ncblx0XHRcdC8vIGZpcmUsIGEgZGlzdGluY3QgaW5zdGFuY2Ugb24gYSBkaXN0aW5jdCBsaW5lKSwgc28gYW5cblx0XHRcdC8vIGBpbnN0YW50aWF0aW9uYCB1c2FnZSByZWNvcmRzIHRoZSBzaXRlIElOIEFERElUSU9OIHRvIHRoZVxuXHRcdFx0Ly8gcmVzdWx0LXZhciBiaW5kaW5nIGFuZCB0aGUgZ2VuZXJpYyBtZXRob2RDYWxsIGZsb3cgKHRoZSBlbnRyeVxuXHRcdFx0Ly8gaXMgYnl0ZS1pbmRpc3Rpbmd1aXNoYWJsZSBmcm9tIGBuZXdgIHVudGlsIHRoZSBkZWZlcnJlZFxuXHRcdFx0Ly8gbWVjaGFuaXNtLWtpbmQgcmV2aXNpb24g4oCUIHRoZSBvd25lcidzIGV4cGxpY2l0IGNhbGwpLiBGcmVlXG5cdFx0XHQvLyB1dGlscy5tZXJnZShhLCBiLCAuLi4pIC8gdXRpbHMuZm9yayhpbnN0YW5jZSkoLi4uKSBhcmVcblx0XHRcdC8vIGNvbnN0cnVjdGlvbiBvZiBhJ3MgdHlwZSB0b28gKG1lcmdlID0gZm9yayhhKSBvdmVyIGInc1xuXHRcdFx0Ly8gY29udGV4dCk7IHRoZSByZXN1bHQgYmluZGluZyBrZWVwcyB0aGUgZG9jdW1lbnRlZCBhcmctMFxuXHRcdFx0Ly8gYXBwcm94aW1hdGlvblxuXHRcdFx0Y29uc3QgZm9ya0xpa2VQYXRoID0gdGhpcy5yZXNvbHZlRm9ya0xpa2VUeXBlUGF0aChub2RlKTtcblx0XHRcdGlmIChmb3JrTGlrZVBhdGgpIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZShub2RlLCBmb3JrTGlrZVBhdGgsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShub2RlLCBmb3JrTGlrZVBhdGgpO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgdXRpbHNQYXRoID0gdGhpcy5yZXNvbHZlVXRpbHNGblR5cGVQYXRoKG5vZGUpO1xuXHRcdFx0aWYgKHV0aWxzUGF0aCkge1xuXHRcdFx0XHR0aGlzLnJlY29yZENvbnN0cnVjdGlvblVzYWdlKG5vZGUsIHV0aWxzUGF0aCwgc291cmNlRmlsZSk7XG5cdFx0XHRcdHRoaXMuYmluZFJlc3VsdFZhcmlhYmxlKG5vZGUsIHV0aWxzUGF0aCk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cdFxuXHQvKipcblx0XHRcdCogR2V0IGZ1bmN0aW9uIG5hbWUgZnJvbSBleHByZXNzaW9uIChpZGVudGlmaWVyIG9yIHByb3BlcnR5IGFjY2Vzcylcblx0XHRcdCovXG5cdHByaXZhdGUgZ2V0RnVuY3Rpb25OYW1lIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci50ZXh0O1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIEFkZCBhIHVzYWdlIHRvIHRoZSBjb2xsZWN0aW9uXG5cdFx0XHQqL1xuXHRwcml2YXRlIGFkZFVzYWdlICh0eXBlUGF0aDogc3RyaW5nLCB1c2FnZTogVXNhZ2VJbmZvKTogdm9pZCB7XG5cdFx0Ly8gT25seSB0cmFjayB1c2FnZXMgb2YgbW5lbW9uaWNhLWRlZmluZWQgdHlwZXNcblx0XHRpZiAoIXRoaXMuZGVmaW5pdGlvbnMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAoIXRoaXMudXNhZ2VzLmhhcyh0eXBlUGF0aCkpIHtcblx0XHRcdHRoaXMudXNhZ2VzLnNldCh0eXBlUGF0aCwgW10pO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBkdXBsaWNhdGVzIGJhc2VkIG9uIGxvY2F0aW9uLCBjb2RlLCBhbmQga2luZFxuXHRcdGNvbnN0IGV4aXN0aW5nVXNhZ2VzID0gdGhpcy51c2FnZXMuZ2V0KHR5cGVQYXRoKSE7XG5cdFx0Y29uc3QgaXNEdXBsaWNhdGUgPSBleGlzdGluZ1VzYWdlcy5zb21lKGV4aXN0aW5nID0+XG5cdFx0XHRleGlzdGluZy5sb2NhdGlvbiA9PT0gdXNhZ2UubG9jYXRpb24gJiZcblx0XHRcdFx0ZXhpc3RpbmcuY29kZSA9PT0gdXNhZ2UuY29kZSAmJlxuXHRcdFx0XHRleGlzdGluZy5raW5kID09PSB1c2FnZS5raW5kKTtcblxuXHRcdGlmICghaXNEdXBsaWNhdGUpIHtcblx0XHRcdGV4aXN0aW5nVXNhZ2VzLnB1c2godXNhZ2UpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IEVEUyAoRXhlY3V0aW9uIERhdGEgU3RvcmFnZSkgdXNhZ2UgaW5mb3JtYXRpb25cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEVEUyAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSB8fCAhbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgZnVuY05hbWUgPSB0aGlzLmdldEZ1bmN0aW9uTmFtZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghZnVuY05hbWUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cdFx0Ly8gRW5jbG9zaW5nIG1uZW1vbmljYSB0eXBlIHBhdGgg4oCUIHdyYXAgYXJncyBhcmUgdXN1YWxseSBsb2NhbFxuXHRcdC8vIGZ1bmN0aW9ucywgc28gdGhlIG93bmluZyBkZWZpbmUoKS9sYXp5KCkgaGFuZGxlciBvciBkZWNvcmF0ZWRcblx0XHQvLyBjbGFzcyBpcyB3aGF0IGVkcy5qc29uIGNvbnN1bWVycyAoR3JhcGhCdWlsZGVyKSBjYW4gam9pbiBvbi5cblx0XHRjb25zdCBzY29wZSA9IHRoaXMucmVzb2x2ZUVEU1Njb3BlKG5vZGUpO1xuXG5cdFx0Ly8gd3JhcChmbiksIHdyYXBDb25zdHJ1Y3RvckFyZyhmbiwgcGFyZW50KSwgdXBncmFkZUNvbnN0cnVjdG9yQXJnKGFyZywgaW5zdCksIHdyYXBJbnN0YW5jZU1ldGhvZHMob2JqKVxuXHRcdGlmIChcblx0XHRcdGZ1bmNOYW1lID09PSAnd3JhcCcgfHxcblx0XHRcdGZ1bmNOYW1lID09PSAnd3JhcENvbnN0cnVjdG9yQXJnJyB8fFxuXHRcdFx0ZnVuY05hbWUgPT09ICd1cGdyYWRlQ29uc3RydWN0b3JBcmcnIHx8XG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3dyYXBJbnN0YW5jZU1ldGhvZHMnXG5cdFx0KSB7XG5cdFx0XHRjb25zdCB0YXJnZXRUeXBlID0gdGhpcy5yZXNvbHZlRURTQXJndW1lbnRUeXBlKG5vZGUuYXJndW1lbnRzWyAwIF0pO1xuXHRcdFx0Ly8gZGl2ZSdzIHdyYXAtZmFtaWx5IHNpZ25hdHVyZXMgKGRpdmUvc3JjL2luZGV4LnRzKTpcblx0XHRcdC8vICAgd3JhcChmbiwgbGFiZWw/KSB8IHdyYXAoZm4sIGNvbnRleHQ/LCBsYWJlbD8pXG5cdFx0XHQvLyAgIHdyYXBDb25zdHJ1Y3RvckFyZyhmbiwgY29udGV4dClcblx0XHRcdC8vICAgdXBncmFkZUNvbnN0cnVjdG9yQXJnKGFyZywgaW5zdGFuY2UpXG5cdFx0XHQvLyAgIHdyYXBJbnN0YW5jZU1ldGhvZHMoaW5zdGFuY2UpXG5cdFx0XHQvLyDigKZzbyB0aGUgaW5zdGFuY2UvY29udGV4dCBhcmcgc2l0cyBhdCBhcmdzWzFdIChhcmdzWzBdIGZvclxuXHRcdFx0Ly8gd3JhcEluc3RhbmNlTWV0aG9kcykgYW5kIGEgc3RyaW5nIGxpdGVyYWwgaW4gYXJnc1sxLi4yXSBpcyB0aGUgbGFiZWxcblx0XHRcdGNvbnN0IGluc3RhbmNlQXJnTm9kZSA9IGZ1bmNOYW1lID09PSAnd3JhcEluc3RhbmNlTWV0aG9kcydcblx0XHRcdFx0PyBub2RlLmFyZ3VtZW50c1sgMCBdXG5cdFx0XHRcdDogbm9kZS5hcmd1bWVudHNbIDEgXTtcblx0XHRcdC8vIEZpcmUtYW5kLWZvcmdldCB3cmFwcGVycyAod2lyZS11cCBoZWxwZXJzLCByZWdpc3RyYXRpb25cblx0XHRcdC8vIGZ1bmN0aW9ucykgc2l0IG91dHNpZGUgYW55IGRlZmluZSgpL2xhenkoKSBoYW5kbGVyLCBzbyB0aGVcblx0XHRcdC8vIGxleGljYWwgc2NvcGUgaXMgYWJzZW50IOKAlCBhdHRyaWJ1dGUgdGhyb3VnaCB0aGUgaW5zdGFuY2UvY29udGV4dFxuXHRcdFx0Ly8gYXJndW1lbnQgaW5zdGVhZDogYSB0cmFja2VkIGFzc2lnbm1lbnQsIGVsc2UgdGhlIGVuY2xvc2luZ1xuXHRcdFx0Ly8gZnVuY3Rpb24ncyBwYXJhbWV0ZXIgYW5ub3RhdGlvbiByZXNvbHZlZCB0aHJvdWdoIHRoZSBncmFwaCBsYXdcblx0XHRcdGNvbnN0IGluc3RhbmNlVHlwZVBhdGggPSBpbnN0YW5jZUFyZ05vZGVcblx0XHRcdFx0PyB0aGlzLnJlc29sdmVXcmFwSW5zdGFuY2VUeXBlUGF0aChpbnN0YW5jZUFyZ05vZGUpXG5cdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0Y29uc3QgZWZmZWN0aXZlU2NvcGUgPSBzY29wZSA/PyBpbnN0YW5jZVR5cGVQYXRoO1xuXHRcdFx0Y29uc3QgaW5mbzogRURTSW5mbyA9IHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAnd3JhcCcsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHRhcmdldFR5cGUgOiB0YXJnZXRUeXBlIHx8IHVuZGVmaW5lZCxcblx0XHRcdFx0c2NvcGUgICAgICA6IGVmZmVjdGl2ZVNjb3BlLFxuXHRcdFx0XHRmbiAgICAgICAgIDogZnVuY05hbWUsXG5cdFx0XHR9O1xuXHRcdFx0aWYgKGluc3RhbmNlQXJnTm9kZSAmJiB0cy5pc0lkZW50aWZpZXIoaW5zdGFuY2VBcmdOb2RlKSkge1xuXHRcdFx0XHRpbmZvLmluc3RhbmNlQXJnID0gaW5zdGFuY2VBcmdOb2RlLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGV4dHJhQXJnIG9mIFsgbm9kZS5hcmd1bWVudHNbIDEgXSwgbm9kZS5hcmd1bWVudHNbIDIgXSBdKSB7XG5cdFx0XHRcdGlmIChleHRyYUFyZyAmJiB0cy5pc1N0cmluZ0xpdGVyYWwoZXh0cmFBcmcpKSB7XG5cdFx0XHRcdFx0aW5mby5sYWJlbCA9IGV4dHJhQXJnLnRleHQ7XG5cdFx0XHRcdFx0YnJlYWs7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIEEgd3JhcCgpIGNhbGwgbmVzdGVkIGluc2lkZSBhbm90aGVyIHdyYXBwZWQgYm9keSBjYXJyaWVzIHRoZVxuXHRcdFx0Ly8gbGluayB0byB0aGUgc2l0ZSB3aG9zZSBydW50aW1lIHdyYXBwaW5nIGNhdXNlZCBpdCDigJQgYW5kLCB3aGVuXG5cdFx0XHQvLyB0aGUgbmVzdGVkIHNpdGUgaGFzIG5vIHNjb3BlIG9mIGl0cyBvd24sIHRoZSBjYXVzaW5nIHNpdGUnc1xuXHRcdFx0Ly8gc2NvcGUgYXR0cmlidXRpb24gdHJhdmVscyB3aXRoIHRoZSBsaW5rXG5cdFx0XHRjb25zdCB2aWFMaW5rID0gdGhpcy5uZXN0ZWRXcmFwVmlhLmdldChub2RlKTtcblx0XHRcdGlmICh2aWFMaW5rKSB7XG5cdFx0XHRcdGluZm8udmlhID0gdmlhTGluay52aWE7XG5cdFx0XHRcdGlmIChpbmZvLnNjb3BlID09PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0XHRpbmZvLnNjb3BlID0gdmlhTGluay5zY29wZTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gZGl2ZSB3cmFwcyByZXR1cm5lZCBmdW5jdGlvbnMgdG9vLCBhbmQgYW55IG1uZW1vbmljYSBpbnN0YW5jZVxuXHRcdFx0Ly8gY3JlYXRlZCBpbnNpZGUgdGhlIHdyYXBwZWQgYm9keSBpcyBhIGd1YXJhbnRlZWQgcGF0aCBoaXQg4oCUXG5cdFx0XHQvLyBib3RoIGFyZSBjYWxjdWxhYmxlIEFvVCwgc28gcmVjb3JkIHRoZW1cblx0XHRcdGNvbnN0IHdyYXBwZWQgPSB0aGlzLnJlc29sdmVGdW5jdGlvbkFyZ3VtZW50KG5vZGUuYXJndW1lbnRzWyAwIF0sIHNvdXJjZUZpbGUpO1xuXHRcdFx0aWYgKHdyYXBwZWQpIHtcblx0XHRcdFx0Ly8gVGhlIHdyYXBwZWQgY2FsbGJhY2sgZ2V0cyBpdHMgb3duIHNjb3BlIGluIHNjb3Blcy5qc29uIGtleWVkIGJ5XG5cdFx0XHRcdC8vIGl0cyBzdGFydCBwb3NpdGlvbiDigJQgcmVjb3JkIHRoYXQgc2NvcGVJZCBzbyBncmFwaCBjb25zdW1lcnMgY2FuXG5cdFx0XHRcdC8vIGpvaW4gYSB3cmFwIGVudHJ5IHRvIHRoZSBjYWxsYmFjaydzIGNyZWF0aW9uIG5vZGVcblx0XHRcdFx0Y29uc3QgY2FsbGJhY2tQb3MgPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdHdyYXBwZWQuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0Y29uc3QgY2FsbGJhY2tGaWxlID0gbm9kZVBhdGgucmVzb2x2ZShzb3VyY2VGaWxlLmZpbGVOYW1lKTtcblx0XHRcdFx0aW5mby5jYWxsYmFja1Njb3BlSWQgPSBgJHtjYWxsYmFja0ZpbGV9OiR7Y2FsbGJhY2tQb3MubGluZSArIDF9OiR7Y2FsbGJhY2tQb3MuY2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0XHRjb25zdCBjcmVhdGVzVHlwZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHRcdFx0dGhpcy5hbmFseXplV3JhcHBlZEJvZHkod3JhcHBlZCwgbG9jYXRpb24sIHNvdXJjZUZpbGUsIDAsIG5ldyBTZXQoKSwgY3JlYXRlc1R5cGVzLCBlZmZlY3RpdmVTY29wZSk7XG5cdFx0XHRcdGlmIChjcmVhdGVzVHlwZXMuc2l6ZSA+IDApIHtcblx0XHRcdFx0XHRpbmZvLmNyZWF0ZXNUeXBlcyA9IEFycmF5LmZyb20oY3JlYXRlc1R5cGVzKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgc3RvcmVkID0gdGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCBlZmZlY3RpdmVTY29wZSB8fCAndW5rbm93bicsIGluZm8pO1xuXHRcdFx0dGhpcy53cmFwRW50cnlCeU5vZGUuc2V0KG5vZGUsIHN0b3JlZCk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gY3VycmVudCgpLCBnZXRFcnJvckluc3RhbmNlKGVyciksIGdldEZsb3codGFyZ2V0Pylcblx0XHRpZiAoZnVuY05hbWUgPT09ICdjdXJyZW50JyB8fCBmdW5jTmFtZSA9PT0gJ2dldEVycm9ySW5zdGFuY2UnIHx8IGZ1bmNOYW1lID09PSAnZ2V0RmxvdycpIHtcblx0XHRcdHRoaXMuYWRkRURTKHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCA6ICdjb250ZXh0Q29uc3VtZScsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHNjb3BlLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gYXR0YWNoSG9va3MoY29sbGVjdGlvbikg4oCUIGZyb20gQG1uZW1vbmljYS9vdGVsLCB3aXJlcyBhXG5cdFx0Ly8gVHlwZXNDb2xsZWN0aW9uIHRvIGRpdmUncyBsaWZlY3ljbGUgdHJhY2luZ1xuXHRcdGlmIChmdW5jTmFtZSA9PT0gJ2F0dGFjaEhvb2tzJyAmJiBub2RlLmFyZ3VtZW50cy5sZW5ndGggPiAwKSB7XG5cdFx0XHRjb25zdCBbIGFyZyBdID0gbm9kZS5hcmd1bWVudHM7XG5cdFx0XHRpZiAodHMuaXNBcnJheUxpdGVyYWxFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGFyZy5lbGVtZW50cykge1xuXHRcdFx0XHRcdGNvbnN0IHRhcmdldFR5cGUgPSB0aGlzLnJlc29sdmVFRFNBcmd1bWVudFR5cGUoZWxlbWVudCk7XG5cdFx0XHRcdFx0dGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCBzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRcdFx0a2luZCAgICAgICA6ICdob29rQXR0YWNoJyxcblx0XHRcdFx0XHRcdGNvZGUsXG5cdFx0XHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdFx0XHRzY29wZSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgdGFyZ2V0VHlwZSA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShhcmcpO1xuXHRcdFx0XHR0aGlzLmFkZEVEUyh0YXJnZXRUeXBlIHx8IHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRcdGtpbmQgICAgICAgOiAnaG9va0F0dGFjaCcsXG5cdFx0XHRcdFx0Y29kZSxcblx0XHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdFx0c2NvcGUsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHR5cGUgZnJvbSBFRFMgY2FsbCBhcmd1bWVudCAoYmVzdCBlZmZvcnQpXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVFRFNBcmd1bWVudFR5cGUgKGFyZzogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCFhcmcpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gSWRlbnRpZmllcjogdmFyaWFibGUgbmFtZVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0Y29uc3QgbWFwcGVkID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQoYXJnLnRleHQpO1xuXHRcdFx0aWYgKG1hcHBlZCkge1xuXHRcdFx0XHRyZXR1cm4gbWFwcGVkO1xuXHRcdFx0fVxuXHRcdFx0Ly8gTWF5YmUgaXQncyBhIHR5cGUgbmFtZSBkaXJlY3RseVxuXHRcdFx0aWYgKHRoaXMuZGVmaW5pdGlvbnMuaGFzKGFyZy50ZXh0KSkge1xuXHRcdFx0XHRyZXR1cm4gYXJnLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBsZXQtaW4tdHJ5OiBhIGxldC92YXIgYmluZGluZyBkZWNsYXJlZCB3aXRob3V0IGEgdHJhY2tlZFxuXHRcdFx0Ly8gaW5pdGlhbGl6ZXIgYW5kIGFzc2lnbmVkIGxhdGVyIGluIHRoZSBTQU1FIHNjb3BlICh0aGVcblx0XHRcdC8vIGZpcmUtYW5kLWZvcmdldCBjYXRjaC1ndWFyZCBwYXR0ZXJuOiBgbGV0IGZuOyB0cnkgeyBmbiA9XG5cdFx0XHQvLyDigKYgfSBjYXRjaCB7IHJldHVybiB9IHdyYXAoZm4sIOKApilgKSDigJQgZm9sbG93IHRoZSBmaXJzdFxuXHRcdFx0Ly8gc3RhdGljYWxseS12aXNpYmxlIGluLXNjb3BlIGFzc2lnbm1lbnQuIE5vIGZsb3cgYW5hbHlzaXM6XG5cdFx0XHQvLyBmdW5jdGlvbi9jbGFzcyBib3VuZGFyaWVzIGFyZSBub3QgY3Jvc3NlZCwgYVxuXHRcdFx0Ly8gbmV2ZXItYXNzaWduZWQgYmluZGluZyBzdGF5cyB1bmtub3duIChGMjAgZGlzY2lwbGluZSkuXG5cdFx0XHQvLyBXaGVuIHRoZSBhc3NpZ25tZW50IHJlc29sdmVzLCBpdHMgZXZpZGVuY2UgV0lOUyBvdmVyIGFueVxuXHRcdFx0Ly8gZGVjbGFyYXRpb24gYW5ub3RhdGlvbiAodGhlIGNvbnN0cnVjdGVkIHN1YnR5cGUgaXMgdGhlIG1vcmVcblx0XHRcdC8vIHNwZWNpZmljIHRydXRoKTsgYW4gdW5yZXNvbHZhYmxlIFJIUyAoYSB1c2VybGFuZCBjYWxsLCBzYXkpXG5cdFx0XHQvLyBmYWxscyB0aHJvdWdoIHRvIHRoZSBhbm5vdGF0aW9uIGNsYWltIGJlbG93LlxuXHRcdFx0Y29uc3QgYXNzaWduZWQgPSB0aGlzLmZvbGxvd1Njb3BlQXNzaWdubWVudChhcmcudGV4dCwgYXJnKTtcblx0XHRcdGlmIChhc3NpZ25lZCkge1xuXHRcdFx0XHRjb25zdCByZXNvbHZlZCA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShhc3NpZ25lZCk7XG5cdFx0XHRcdGlmIChyZXNvbHZlZCkge1xuXHRcdFx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gQW5ub3RhdGlvbiBmYWxsYmFjayDigJQgdGhlIEYyMCBkaXNjaXBsaW5lIG9uZSBhcmd1bWVudCBvdmVyOlxuXHRcdFx0Ly8gYW4gZXhwbGljaXQgZGVjbGFyYXRpb24gb3IgcGFyYW1ldGVyIGFubm90YXRpb24gaXMgYSB1c2VyXG5cdFx0XHQvLyBjbGFpbSB3cml0dGVuIGluIHRoZSBBU1QsIG5vdCBmbG93IGFuYWx5c2lzLiBQYXJhbWV0ZXJcblx0XHRcdC8vIGZpcnN0OiBpdCBzaGFkb3dzIGFuIG91dGVyIGxldCwgc2FtZSBhcyB0aGUgY29udGV4dC1hcmcgcGF0aC5cblx0XHRcdGNvbnN0IGFubm90YXRlZCA9IHRoaXMucmVzb2x2ZVBhcmFtZXRlckFubm90YXRpb25UeXBlUGF0aChhcmcudGV4dCwgYXJnKSA/P1xuXHRcdFx0XHR0aGlzLnJlc29sdmVWYXJpYWJsZUFubm90YXRpb25UeXBlUGF0aChhcmcudGV4dCwgYXJnKTtcblx0XHRcdHJldHVybiBhbm5vdGF0ZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gTmV3RXhwcmVzc2lvbjogdGhlIGNvbnN0cnVjdGVkIHR5cGUg4oCUIHJlYWNoYWJsZSBkaXJlY3RseVxuXHRcdC8vICh3cmFwKG5ldyBUKCksIOKApikpIG9yIHRocm91Z2ggYSBmb2xsb3dlZCBhc3NpZ25tZW50XG5cdFx0aWYgKHRzLmlzTmV3RXhwcmVzc2lvbihhcmcpKSB7XG5cdFx0XHRjb25zdCBjdG9yRXhwciA9IGFyZy5leHByZXNzaW9uO1xuXHRcdFx0Y29uc3QgbmFtZSA9IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGN0b3JFeHByKVxuXHRcdFx0XHQ/IHRoaXMucmVzb2x2ZVR5cGVQYXRoKGN0b3JFeHByKVxuXHRcdFx0XHQ6IHRoaXMuZ2V0VHlwZU5hbWVGcm9tRXhwcmVzc2lvbihjdG9yRXhwcik7XG5cdFx0XHRjb25zdCBrbm93biA9IG5hbWUgJiYgdGhpcy5kZWZpbml0aW9ucy5oYXMobmFtZSkgPyBuYW1lIDogdW5kZWZpbmVkO1xuXHRcdFx0cmV0dXJuIGtub3duO1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2Vzczogb2JqLnByb3Bcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMucmVzb2x2ZVR5cGVQYXRoKGFyZyk7XG5cdFx0fVxuXG5cdFx0Ly8gVGhpcyBleHByZXNzaW9uOiB0aGlzLnNvbWV0aGluZ1xuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcmcpICYmIHRzLmlzSWRlbnRpZmllcihhcmcuZXhwcmVzc2lvbikgJiYgYXJnLmV4cHJlc3Npb24udGV4dCA9PT0gJ3RoaXMnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogbGV0LWluLXRyeTogZmluZCB0aGUgUklHSFQtSEFORCBTSURFIG9mIHRoZSBmaXJzdCBzdGF0aWNhbGx5LXZpc2libGVcblx0ICogYXNzaWdubWVudCB0byBgbmFtZWAgaW4gdGhlIHNjb3BlIHRoYXQgZGVjbGFyZXMgaXQuIFRoZSBkZWNsYXJpbmdcblx0ICogY29udGFpbmVyIGlzIGZvdW5kIGlubmVybW9zdC1vdXQgKGJsb2NrcywgY2FzZSBjbGF1c2VzLCB0aGUgc291cmNlXG5cdCAqIGZpbGUg4oCUIHRoZSBGMjAgd2Fsayk7IHRoZSBzY2FuIHJlY3Vyc2VzIGludG8gbmVzdGVkIGJsb2NrcyAodHJ5L1xuXHQgKiBjYXRjaC9maW5hbGx5LCBpZi9lbHNlLCBsb29wcywgc3dpdGNoIGNhc2VzKSBidXQgTkVWRVIgY3Jvc3Nlc1xuXHQgKiBmdW5jdGlvbiBvciBjbGFzcyBib3VuZGFyaWVzIOKAlCBhbiBhc3NpZ25tZW50IGluc2lkZSBhIGNsb3N1cmUgZG9lc1xuXHQgKiBub3QgYXR0cmlidXRlLiBSZXR1cm5zIHVuZGVmaW5lZCB3aGVuIHRoZSBiaW5kaW5nIGlzIGRlY2xhcmVkIGJ1dFxuXHQgKiBuZXZlciBhc3NpZ25lZCBpbiBzY29wZSAoYW5kIHN0b3BzIHRoZXJlOiBhbiBpbm5lciBkZWNsYXJhdGlvblxuXHQgKiBzaGFkb3dzIGFueSBvdXRlciBiaW5kaW5nKS5cblx0ICovXG5cdHByaXZhdGUgZm9sbG93U2NvcGVBc3NpZ25tZW50IChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IGZyb207XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGNvbnN0IHN0YXRlbWVudHM6IHRzLk5vZGVBcnJheTx0cy5TdGF0ZW1lbnQ+IHwgdW5kZWZpbmVkID1cblx0XHRcdFx0dHMuaXNCbG9jayhjdXJyZW50KSB8fCB0cy5pc01vZHVsZUJsb2NrKGN1cnJlbnQpIHx8IHRzLmlzU291cmNlRmlsZShjdXJyZW50KVxuXHRcdFx0XHRcdD8gY3VycmVudC5zdGF0ZW1lbnRzXG5cdFx0XHRcdFx0OiB0cy5pc0Nhc2VDbGF1c2UoY3VycmVudCkgfHwgdHMuaXNEZWZhdWx0Q2xhdXNlKGN1cnJlbnQpXG5cdFx0XHRcdFx0XHQ/IGN1cnJlbnQuc3RhdGVtZW50c1xuXHRcdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cdFx0XHRpZiAoc3RhdGVtZW50cyAmJiB0aGlzLnN0YXRlbWVudHNEZWNsYXJlVmFyaWFibGUoc3RhdGVtZW50cywgbmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcmhzID0gdGhpcy5maW5kQXNzaWdubWVudFJoc0luU3RhdGVtZW50cyhzdGF0ZW1lbnRzLCBuYW1lKTtcblx0XHRcdFx0cmV0dXJuIHJocztcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBUcnVlIHdoZW4gdGhlIHN0YXRlbWVudCBsaXN0IGNvbnRhaW5zIGEgYGxldGAvYHZhcmAvYGNvbnN0YFxuXHQgKiBkZWNsYXJhdGlvbiBmb3IgYG5hbWVgIChhbnkgaW5pdGlhbGl6ZXIgZm9ybSkuXG5cdCAqL1xuXHRwcml2YXRlIHN0YXRlbWVudHNEZWNsYXJlVmFyaWFibGUgKHN0YXRlbWVudHM6IHJlYWRvbmx5IHRzLlN0YXRlbWVudFtdLCBuYW1lOiBzdHJpbmcpOiBib29sZWFuIHtcblx0XHRmb3IgKGNvbnN0IHN0YXRlbWVudCBvZiBzdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAoIXRzLmlzVmFyaWFibGVTdGF0ZW1lbnQoc3RhdGVtZW50KSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3QgZGVjbGFyYXRpb24gb2Ygc3RhdGVtZW50LmRlY2xhcmF0aW9uTGlzdC5kZWNsYXJhdGlvbnMpIHtcblx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihkZWNsYXJhdGlvbi5uYW1lKSAmJiBkZWNsYXJhdGlvbi5uYW1lLnRleHQgPT09IG5hbWUpIHtcblx0XHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogRmlyc3QgYG5hbWUgPSByaHNgIGFzc2lnbm1lbnQgaW4gdGhlIHN0YXRlbWVudCBsaXN0LCByZWN1cnNpbmdcblx0ICogaW50byBuZXN0ZWQgaW4tc2NvcGUgYmxvY2tzLiBGdW5jdGlvbiBhbmQgY2xhc3MgYm9kaWVzIGFyZVxuXHQgKiBib3VuZGFyaWVzIGFuZCBhcmUgbm90IGVudGVyZWQuXG5cdCAqL1xuXHRwcml2YXRlIGZpbmRBc3NpZ25tZW50UmhzSW5TdGF0ZW1lbnRzIChcblx0XHRzdGF0ZW1lbnRzOiByZWFkb25seSB0cy5TdGF0ZW1lbnRbXSxcblx0XHRuYW1lOiBzdHJpbmdcblx0KTogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc3RhdGVtZW50cykge1xuXHRcdFx0Y29uc3QgZGlyZWN0ID0gdGhpcy5kaXJlY3RBc3NpZ25tZW50UmhzKHN0YXRlbWVudCwgbmFtZSk7XG5cdFx0XHRpZiAoZGlyZWN0KSB7XG5cdFx0XHRcdHJldHVybiBkaXJlY3Q7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IG5lc3RlZCBvZiB0aGlzLm5lc3RlZFNjb3BlQmxvY2tzKHN0YXRlbWVudCkpIHtcblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRBc3NpZ25tZW50UmhzSW5TdGF0ZW1lbnRzKG5lc3RlZCwgbmFtZSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIGBuYW1lID0gcmhzYCBhcyBhIGRpcmVjdCBleHByZXNzaW9uIHN0YXRlbWVudC5cblx0ICovXG5cdHByaXZhdGUgZGlyZWN0QXNzaWdubWVudFJocyAoc3RhdGVtZW50OiB0cy5TdGF0ZW1lbnQsIG5hbWU6IHN0cmluZyk6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHMuaXNFeHByZXNzaW9uU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGV4cHIgPSBzdGF0ZW1lbnQuZXhwcmVzc2lvbjtcblx0XHRpZiAoIXRzLmlzQmluYXJ5RXhwcmVzc2lvbihleHByKSB8fCBleHByLm9wZXJhdG9yVG9rZW4ua2luZCAhPT0gdHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbikge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoZXhwci5sZWZ0KSB8fCBleHByLmxlZnQudGV4dCAhPT0gbmFtZSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmhzID0gZXhwci5yaWdodDtcblx0XHRyZXR1cm4gcmhzO1xuXHR9XG5cblx0LyoqXG5cdCAqIFN0YXRlbWVudCBsaXN0cyBvZiB0aGUgbmVzdGVkIGJsb2NrcyB0aGF0IHN0YXkgSU5TSURFIHRoZSBjdXJyZW50XG5cdCAqIHNjb3BlIOKAlCB0cnkvY2F0Y2gvZmluYWxseSwgaWYvZWxzZSwgbG9vcHMsIHN3aXRjaCBjYXNlcywgbmVzdGVkXG5cdCAqIGJsb2NrcywgbGFiZWxlZCBzdGF0ZW1lbnRzLiBGdW5jdGlvbi1saWtlIGFuZCBjbGFzcyBib2RpZXMgYXJlXG5cdCAqIHNjb3BlIGJvdW5kYXJpZXMgYW5kIHlpZWxkIG5vdGhpbmcuXG5cdCAqL1xuXHRwcml2YXRlIG5lc3RlZFNjb3BlQmxvY2tzIChzdGF0ZW1lbnQ6IHRzLlN0YXRlbWVudCk6IHJlYWRvbmx5IChyZWFkb25seSB0cy5TdGF0ZW1lbnRbXSlbXSB7XG5cdFx0Y29uc3QgYmxvY2tzOiB0cy5TdGF0ZW1lbnRbXVtdID0gW107XG5cdFx0Y29uc3QgcHVzaCA9IChub2RlOiB0cy5TdGF0ZW1lbnQgfCB1bmRlZmluZWQpOiB2b2lkID0+IHtcblx0XHRcdGlmIChub2RlICYmIHRzLmlzQmxvY2sobm9kZSkpIHtcblx0XHRcdFx0YmxvY2tzLnB1c2goWyAuLi5ub2RlLnN0YXRlbWVudHMgXSk7XG5cdFx0XHR9XG5cdFx0fTtcblx0XHRpZiAodHMuaXNCbG9jayhzdGF0ZW1lbnQpKSB7XG5cdFx0XHRibG9ja3MucHVzaChbIC4uLnN0YXRlbWVudC5zdGF0ZW1lbnRzIF0pO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNUcnlTdGF0ZW1lbnQoc3RhdGVtZW50KSkge1xuXHRcdFx0cHVzaChzdGF0ZW1lbnQudHJ5QmxvY2spO1xuXHRcdFx0aWYgKHN0YXRlbWVudC5jYXRjaENsYXVzZSkge1xuXHRcdFx0XHRwdXNoKHN0YXRlbWVudC5jYXRjaENsYXVzZS5ibG9jayk7XG5cdFx0XHR9XG5cdFx0XHRwdXNoKHN0YXRlbWVudC5maW5hbGx5QmxvY2spO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNJZlN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRwdXNoKHN0YXRlbWVudC50aGVuU3RhdGVtZW50KTtcblx0XHRcdHB1c2goc3RhdGVtZW50LmVsc2VTdGF0ZW1lbnQpO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNGb3JTdGF0ZW1lbnQoc3RhdGVtZW50KSB8fCB0cy5pc0ZvckluU3RhdGVtZW50KHN0YXRlbWVudCkgfHxcblx0XHRcdHRzLmlzRm9yT2ZTdGF0ZW1lbnQoc3RhdGVtZW50KSB8fCB0cy5pc1doaWxlU3RhdGVtZW50KHN0YXRlbWVudCkgfHxcblx0XHRcdHRzLmlzRG9TdGF0ZW1lbnQoc3RhdGVtZW50KSB8fCB0cy5pc1dpdGhTdGF0ZW1lbnQoc3RhdGVtZW50KSkge1xuXHRcdFx0cHVzaChzdGF0ZW1lbnQuc3RhdGVtZW50KTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzU3dpdGNoU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdGZvciAoY29uc3QgY2xhdXNlIG9mIHN0YXRlbWVudC5jYXNlQmxvY2suY2xhdXNlcykge1xuXHRcdFx0XHRibG9ja3MucHVzaChbIC4uLmNsYXVzZS5zdGF0ZW1lbnRzIF0pO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSBpZiAodHMuaXNMYWJlbGVkU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdGNvbnN0IG5lc3RlZCA9IHRoaXMubmVzdGVkU2NvcGVCbG9ja3Moc3RhdGVtZW50LnN0YXRlbWVudCk7XG5cdFx0XHRmb3IgKGNvbnN0IGJsb2NrIG9mIG5lc3RlZCkge1xuXHRcdFx0XHRibG9ja3MucHVzaChbIC4uLmJsb2NrIF0pO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBibG9ja3M7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHRoZSBlbmNsb3NpbmcgbW5lbW9uaWNhIHNjb3BlIG9mIGFuIEVEUyBjYWxsIHNpdGUgYnkgd2Fsa2luZ1xuXHQgKiB1cCB0aGUgcGFyZW50IGNoYWluOiBuZWFyZXN0IGRlZmluZSgpL2xhenkoKSBjYWxsIHdob3NlIGhhbmRsZXIgaG9sZHNcblx0ICogdGhlIG5vZGUsIG9yIG5lYXJlc3QgQGRlY29yYXRlKCktZWQgY2xhc3MgZGVjbGFyYXRpb24uIEJlc3QgZWZmb3J0IOKAlFxuXHQgKiByZXR1cm5zIHVuZGVmaW5lZCBmb3IgY2FsbHMgb3V0c2lkZSBhbnkgdHlwZSBzY29wZSAobW9kdWxlIHRvcCBsZXZlbCkuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVFRFNTY29wZSAobm9kZTogdHMuTm9kZSk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBub2RlLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0Y29uc3Qgc2NvcGVQYXRoID0gdGhpcy5lZHNTY29wZUJ5Tm9kZS5nZXQoY3VycmVudCk7XG5cdFx0XHRpZiAoc2NvcGVQYXRoKSB7XG5cdFx0XHRcdHJldHVybiBzY29wZVBhdGg7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHdyYXAgc2l0ZSdzIGluc3RhbmNlL2NvbnRleHQgYXJndW1lbnQgdG8gYSBtbmVtb25pY2EgdHlwZVxuXHQgKiBwYXRoIOKAlCB0aGUgZmlyZS1hbmQtZm9yZ2V0LXdyYXBwZXIgYXR0cmlidXRpb24gZmFsbGJhY2sgd2hlbiB0aGUgY2FsbFxuXHQgKiBzaXRzIG91dHNpZGUgYW55IGRlZmluZSgpL2xhenkoKSBoYW5kbGVyOiBhIHRyYWNrZWQgYXNzaWdubWVudFxuXHQgKiAoYGNvbnN0IGhvbGRlciA9IG5ldyBIb2xkZXIoLi4uKWApLCBlbHNlIHRoZSByb290IGlkZW50aWZpZXInc1xuXHQgKiAocHJvcGVydHktYWNjZXNzIHJvb3RzIGluY2x1ZGVkKSBwYXJhbWV0ZXIgYW5ub3RhdGlvbiByZXNvbHZlZFxuXHQgKiB0aHJvdWdoIHRoZSBncmFwaCBsYXcuIEFtYmlndWl0eSBvciBhYnNlbmNlIHN0YXlzIHNpbGVudCDigJQgdGhpcyBpcyBhXG5cdCAqIG1ldGFkYXRhIGhldXJpc3RpYywgbm90IHRoZSBpZGVudGl0eS1sYXcgc3VyZmFjZS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVdyYXBJbnN0YW5jZVR5cGVQYXRoIChhcmc6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGZyb21CaW5kaW5nID0gKG5hbWU6IHN0cmluZywgZnJvbTogdHMuTm9kZSk6IHN0cmluZyB8IHVuZGVmaW5lZCA9PiB7XG5cdFx0XHRjb25zdCBtYXBwZWQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChuYW1lKTtcblx0XHRcdGlmIChtYXBwZWQpIHtcblx0XHRcdFx0cmV0dXJuIG1hcHBlZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGFubm90YXRpb25UeXBlID0gdGhpcy5yZXNvbHZlUGFyYW1ldGVyQW5ub3RhdGlvblR5cGVQYXRoKG5hbWUsIGZyb20pID8/XG5cdFx0XHRcdC8vIEYyMCBjaGVhcCB0aWVyOiB0aGUgaWRlbnRpZmllciBpcyBib3VuZCB0byBhIGxldC92YXIvY29uc3Rcblx0XHRcdFx0Ly8gd2l0aCBhbiBFWFBMSUNJVCB0eXBlIGFubm90YXRpb24g4oCUIHJlc29sdmUgdGhlIGFubm90YXRpb25cblx0XHRcdFx0Ly8gdGhyb3VnaCB0aGUgZ3JhcGggbGF3LiBObyBmbG93LXNlbnNpdGl2ZSBhc3NpZ25tZW50XG5cdFx0XHRcdC8vIHRyYWNraW5nOiBhbiBVTkFOTk9UQVRFRCBsZXQgc3RpbGwgYnVja2V0cyB1bmtub3duXG5cdFx0XHRcdHRoaXMucmVzb2x2ZVZhcmlhYmxlQW5ub3RhdGlvblR5cGVQYXRoKG5hbWUsIGZyb20pO1xuXHRcdFx0cmV0dXJuIGFubm90YXRpb25UeXBlO1xuXHRcdH07XG5cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGZyb21CaW5kaW5nKGFyZy50ZXh0LCBhcmcpO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdGNvbnN0IHJvb3QgPSB0aGlzLmdldFJvb3RJZGVudGlmaWVyKGFyZyk7XG5cdFx0XHRpZiAocm9vdCkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQgPSBmcm9tQmluZGluZyhyb290LnRleHQsIGFyZyk7XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRW1pc3Npb24tbGF3IGhlbHBlciAoMC4yLjAgcmVzdG9yYXRpb24pOiBpcyBgbmFtZWAgZGVjbGFyZWQgaW4gYW55XG5cdCAqIEFOQUxZWkVEIFBST0pFQ1QgZmlsZT8gRXh0ZXJuYWwvYW1iaWVudCBmaWxlcyAoLmQudHMsIG5vZGVfbW9kdWxlcylcblx0ICogZG8gbm90IGNvdW50LiBBIG5hbWUgd2l0aCBubyBwcm9qZWN0IGRlY2xhcmF0aW9uIGlzIGFuIGFtYmllbnQvbGliXG5cdCAqIGNvbnN0cnVjdCDigJQgc2FmZSB0byBlbWl0IHZlcmJhdGltIGludG8gdGhlIHNlbGYtY29udGFpbmVkIHR5cGVzLnRzO1xuXHQgKiBhIHByb2plY3QtbG9jYWwgbmFtZSBpcyBub3QgKG5vIGltcG9ydHMgaW4gdGhlIGdlbmVyYXRlZCBmaWxlKS5cblx0ICovXG5cdHByaXZhdGUgaXNQcm9qZWN0RGVjbGFyZWRUeXBlTmFtZSAobmFtZTogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0Zm9yIChjb25zdCBbIGZpbGUsIGRlY2xzIF0gb2YgdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzKSB7XG5cdFx0XHRpZiAodGhpcy5pc0V4dGVybmFsRGVjbEZpbGUoZmlsZSkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRpZiAoZGVjbHMuaGFzKG5hbWUpKSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBmYWxzZTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEYyNDogcmVzb2x2ZSBhIGJhcmUtaWRlbnRpZmllciBhbm5vdGF0aW9uIHRvIGEgZ3JhcGggZnVsbFBhdGguIFRoZVxuXHQgKiBhbm5vdGF0aW9uIG1heSBuYW1lIHRoZSB0eXBlIGRpcmVjdGx5IChgTGVkZ2VyVXBkYXRlYCkgb3IgY2Fycnlcblx0ICogdGhlIEdFTkVSQVRFRCBpbnN0YW5jZSBhbGlhcyBvZiBhIG5lc3RlZCB0eXBlXG5cdCAqIChgVXBkYXRlUGF5X1NvbWVUZXJtaW5hbGAsIGltcG9ydGVkIGZyb20gdGhlIGdlbmVyYXRlZCB0eXBlcyBmaWxlXG5cdCAqIHZpYSB0c2NvbmZpZyBwYXRocykg4oCUIG5vdCBhIGdyYXBoIG5vZGUgTkFNRS4gVGhlIG5hbWUgaXMgdHJpZWRcblx0ICogYXMtaXMgZmlyc3QsIHRoZW4gaXRzIHVuZGVyc2NvcmXihpJkb3R0ZWQgZm9ybSAodGhlIGdlbmVyYXRlZCBhbGlhc1xuXHQgKiBuYW1pbmcgbGF3OyB0aGUgc2FtZSBtYXBwaW5nIHNjb3Blcy5qc29uIHVzZXMgZm9yIGFubm90YXRpb25zKS5cblx0ICogQW1iaWd1aXR5IGFuZCBhYnNlbmNlIHlpZWxkIHVuZGVmaW5lZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUFubm90YXRpb25UeXBlUGF0aCAobmFtZTogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBkaXJlY3QgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKG5hbWUpO1xuXHRcdGlmIChkaXJlY3Quc3RhdHVzID09PSAndW5pcXVlJykge1xuXHRcdFx0Y29uc3QgcmVzdWx0ID0gZGlyZWN0Lm5vZGUuZnVsbFBhdGg7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH1cblx0XHRpZiAoIW5hbWUuaW5jbHVkZXMoJ18nKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgYWxpYXNlZCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUobmFtZS5yZXBsYWNlKC9fL2csICcuJykpO1xuXHRcdGlmIChhbGlhc2VkLnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGFsaWFzZWQubm9kZS5mdWxsUGF0aDtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGJhcmUtaWRlbnRpZmllciB0eXBlIGFubm90YXRpb24gb2YgdGhlIG5lYXJlc3QgZW5jbG9zaW5nXG5cdCAqIGZ1bmN0aW9uJ3MgcGFyYW1ldGVyIHRocm91Z2ggdGhlIG1uZW1vbmljYS1ncmFwaCB0aWVycyAodmFsdWUgc2NvcGUsXG5cdCAqIGltcG9ydHMsIHJvb3RzLCBwcm9ncmFtLXdpZGUtdW5pcXVlKS4gTm9uLWlkZW50aWZpZXIgYW5kIGdlbmVyaWNcblx0ICogYW5ub3RhdGlvbnMgYXJlIG5vdCBncmFwaCByZWZlcmVuY2VzOyBhbWJpZ3VpdHkgYW5kIGFic2VuY2UgeWllbGRcblx0ICogdW5kZWZpbmVkLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlUGFyYW1ldGVyQW5ub3RhdGlvblR5cGVQYXRoIChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gZnJvbS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc0Z1bmN0aW9uTGlrZShjdXJyZW50KSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGN1cnJlbnQucGFyYW1ldGVycyA/PyBbXSkge1xuXHRcdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpIHx8IHBhcmFtLm5hbWUudGV4dCAhPT0gbmFtZSB8fCAhcGFyYW0udHlwZSB8fFxuXHRcdFx0XHRcdFx0IXRzLmlzVHlwZVJlZmVyZW5jZU5vZGUocGFyYW0udHlwZSkgfHxcblx0XHRcdFx0XHRcdCF0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSkgfHxcblx0XHRcdFx0XHRcdChwYXJhbS50eXBlLnR5cGVBcmd1bWVudHM/Lmxlbmd0aCA/PyAwKSA+IDApIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCByZXNvbHZlZCA9IHRoaXMucmVzb2x2ZUFubm90YXRpb25UeXBlUGF0aChwYXJhbS50eXBlLnR5cGVOYW1lLnRleHQpO1xuXHRcdFx0XHRcdGlmIChyZXNvbHZlZCkge1xuXHRcdFx0XHRcdFx0cmV0dXJuIHJlc29sdmVkO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEYyMCBjaGVhcCB0aWVyOiB0aGUgd3JhcCBhcmd1bWVudCBpcyBhbiBpZGVudGlmaWVyIGRlY2xhcmVkIHdpdGggYW5cblx0ICogRVhQTElDSVQgdHlwZSBhbm5vdGF0aW9uIChgbGV0IHVwZGF0ZUNvbW1pdHRlZDogTGVkZ2VyVXBkYXRlO2Bcblx0ICogYXNzaWduZWQgbGF0ZXIgaW4gYSBmbG93IHRoZSBhbmFseXplciBkb2VzIG5vdCB0cmFjaykuIFRoZVxuXHQgKiBhbm5vdGF0aW9uIHJlc29sdmVzIHRocm91Z2ggdGhlIHNhbWUgZ3JhcGggdGllcnMgYXMgcGFyYW1ldGVyXG5cdCAqIGFubm90YXRpb25zLiBEZWxpYmVyYXRlbHkgTk9UIGZsb3ctc2Vuc2l0aXZlOiBhbiBVTkFOTk9UQVRFRFxuXHQgKiBsZXQvdmFyIHN0aWxsIGJ1Y2tldHMgdW5rbm93biwgYW5kIGEgY29uc3Qgd2l0aCBhbiBhbmFseXphYmxlXG5cdCAqIGluaXRpYWxpemVyIHN0YXlzIHRoZSByZWNvbW1lbmRlZCBkaXNjaXBsaW5lLiBUaGUgbG9va3VwIHdhbGtzIHRoZVxuXHQgKiBlbmNsb3Npbmcgc3RhdGVtZW50IGNvbnRhaW5lcnMgaW5uZXJtb3N0LW91dCwgc28gYSBzaGFkb3dpbmcgaW5uZXJcblx0ICogZGVjbGFyYXRpb24gd2lucy5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVZhcmlhYmxlQW5ub3RhdGlvblR5cGVQYXRoIChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gZnJvbTtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0Y29uc3Qgc3RhdGVtZW50czogdHMuTm9kZUFycmF5PHRzLlN0YXRlbWVudD4gfCB1bmRlZmluZWQgPVxuXHRcdFx0XHR0cy5pc0Jsb2NrKGN1cnJlbnQpIHx8IHRzLmlzTW9kdWxlQmxvY2soY3VycmVudCkgfHwgdHMuaXNTb3VyY2VGaWxlKGN1cnJlbnQpXG5cdFx0XHRcdFx0PyBjdXJyZW50LnN0YXRlbWVudHNcblx0XHRcdFx0XHQ6IHRzLmlzQ2FzZUNsYXVzZShjdXJyZW50KSB8fCB0cy5pc0RlZmF1bHRDbGF1c2UoY3VycmVudClcblx0XHRcdFx0XHRcdD8gY3VycmVudC5zdGF0ZW1lbnRzXG5cdFx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblx0XHRcdGlmIChzdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdGNvbnN0IHJlc29sdmVkID0gdGhpcy5maW5kQW5ub3RhdGVkVmFyaWFibGVUeXBlUGF0aChzdGF0ZW1lbnRzLCBuYW1lKTtcblx0XHRcdFx0aWYgKHJlc29sdmVkKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHJlc29sdmVkO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmlyc3QgdmFyaWFibGUgZGVjbGFyYXRpb24gY2FycnlpbmcgYW4gZXhwbGljaXQgYmFyZS1pZGVudGlmaWVyIHR5cGVcblx0ICogYW5ub3RhdGlvbiBmb3IgYG5hbWVgIGluIHRoZSBnaXZlbiBzdGF0ZW1lbnQgbGlzdCwgcmVzb2x2ZWQgdGhyb3VnaFxuXHQgKiB0aGUgZ3JhcGggbGF3LlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kQW5ub3RhdGVkVmFyaWFibGVUeXBlUGF0aCAoXG5cdFx0c3RhdGVtZW50czogcmVhZG9ubHkgdHMuU3RhdGVtZW50W10sXG5cdFx0bmFtZTogc3RyaW5nXG5cdCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc3RhdGVtZW50cykge1xuXHRcdFx0aWYgKCF0cy5pc1ZhcmlhYmxlU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGRlY2xhcmF0aW9uIG9mIHN0YXRlbWVudC5kZWNsYXJhdGlvbkxpc3QuZGVjbGFyYXRpb25zKSB7XG5cdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGRlY2xhcmF0aW9uLm5hbWUpIHx8IGRlY2xhcmF0aW9uLm5hbWUudGV4dCAhPT0gbmFtZSB8fFxuXHRcdFx0XHRcdCFkZWNsYXJhdGlvbi50eXBlIHx8XG5cdFx0XHRcdFx0IXRzLmlzVHlwZVJlZmVyZW5jZU5vZGUoZGVjbGFyYXRpb24udHlwZSkgfHxcblx0XHRcdFx0XHQhdHMuaXNJZGVudGlmaWVyKGRlY2xhcmF0aW9uLnR5cGUudHlwZU5hbWUpIHx8XG5cdFx0XHRcdFx0KGRlY2xhcmF0aW9uLnR5cGUudHlwZUFyZ3VtZW50cz8ubGVuZ3RoID8/IDApID4gMCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IHJlc29sdmVkID0gdGhpcy5yZXNvbHZlQW5ub3RhdGlvblR5cGVQYXRoKGRlY2xhcmF0aW9uLnR5cGUudHlwZU5hbWUudGV4dCk7XG5cdFx0XHRcdGlmIChyZXNvbHZlZCkge1xuXHRcdFx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSB3cmFwKCkgYXJndW1lbnQgdG8gaXRzIGZ1bmN0aW9uIG5vZGUgd2l0aG91dCB0aGUgdHlwZVxuXHQgKiBjaGVja2VyOiBkaXJlY3QgZnVuY3Rpb24gZXhwcmVzc2lvbnMvYXJyb3dzLCBvciBzYW1lLWZpbGUgYmluZGluZ3Ncblx0ICogKGBjb25zdCBmbiA9ICgpID0+IC4uLmAsIGBmdW5jdGlvbiBmbigpIC4uLmApLiBCZXN0IGVmZm9ydCDigJQgbWV0aG9kXG5cdCAqIHJlZmVyZW5jZXMsIC5iaW5kKCkgcHJvZHVjdHMgYW5kIGNyb3NzLWZpbGUgaWRlbnRpZmllcnMgc3RheVxuXHQgKiB1bnJlc29sdmVkOyB0aGUgY2FsbHNpdGUgZW50cnkgaXRzZWxmIGlzIHN0aWxsIHJlY29yZGVkLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRnVuY3Rpb25Bcmd1bWVudCAoXG5cdFx0YXJnOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGVcblx0KTogdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGlmICghYXJnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGFyZykgfHwgdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0cmV0dXJuIGFyZztcblx0XHR9XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihhcmcpKSB7XG5cdFx0XHRjb25zdCBrZXkgPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfSMke2FyZy50ZXh0fWA7XG5cdFx0XHRjb25zdCBib3VuZCA9IHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5nZXQoa2V5KTtcblx0XHRcdGlmIChib3VuZCkge1xuXHRcdFx0XHRyZXR1cm4gYm91bmQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogQW5hbHlzZSBhIHdyYXBwZWQgZnVuY3Rpb24ncyBib2R5IGZvciBndWFyYW50ZWVkIHJ1bnRpbWUgcGF0aHM6XG5cdCAqIGRpdmUgd3JhcHMgcmV0dXJuZWQgZnVuY3Rpb25zIGFzIHdlbGwgKHJlY3Vyc2l2ZWx5KSwgc28gZWFjaFxuXHQgKiBmdW5jdGlvbi12YWx1ZWQgcmV0dXJuIGlzIGEgbmVzdGVkIHdyYXAgc2l0ZSwgYW5kIGVhY2ggYG5ldyBUeXBlKClgXG5cdCAqIGluc2lkZSB0aGUgYm9keSBtZWFucyB0aGUgcGF0aCBoaXRzIHRoYXQgdHlwZSdzIGNvbnN0cnVjdG9yICh3aGljaFxuXHQgKiBhdHRhY2hIb29rcyB3cmFwcyB0b28pLiBCb3RoIGZhY3RzIGFyZSAxMDAlIGVuc3VyZWQsIHNvIHRoZXkgYXJlXG5cdCAqIHJlY29yZGVkIEFvVC4gTmVzdGVkIGZ1bmN0aW9uIGJvZGllcyBhcmUgTk9UIHdhbGtlZCBoZXJlIOKAlCB0aGV5XG5cdCAqIGJlbG9uZyB0byB0aGVpciBvd24gd3JhcCBhbmFseXNpcywgcmVhY2hlZCB2aWEgdGhlIHJldHVybiBjaGFpbi5cblx0ICogRGVwdGgtY2FwcGVkIGFuZCBjeWNsZS1ndWFyZGVkLlxuXHQgKi9cblx0cHJpdmF0ZSBhbmFseXplV3JhcHBlZEJvZHkgKFxuXHRcdGZuOiB0cy5GdW5jdGlvbkxpa2VEZWNsYXJhdGlvbixcblx0XHR2aWFMb2NhdGlvbjogc3RyaW5nLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0ZGVwdGg6IG51bWJlcixcblx0XHR2aXNpdGVkOiBTZXQ8dHMuTm9kZT4sXG5cdFx0Y3JlYXRlc1R5cGVzOiBTZXQ8c3RyaW5nPixcblx0XHRmYWxsYmFja1Njb3BlPzogc3RyaW5nXG5cdCk6IHZvaWQge1xuXHRcdGlmIChkZXB0aCA+IDUgfHwgdmlzaXRlZC5oYXMoZm4pIHx8ICFmbi5ib2R5KSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHZpc2l0ZWQuYWRkKGZuKTtcblxuXHRcdC8vIEFycm93IHdpdGggZXhwcmVzc2lvbiBib2R5OiBpbXBsaWNpdCByZXR1cm5cblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGZuKSAmJiAhdHMuaXNCbG9jayhmbi5ib2R5KSkge1xuXHRcdFx0dGhpcy5yZWNvcmRXcmFwcGVkUmV0dXJuKGZuLmJvZHksIHZpYUxvY2F0aW9uLCBzb3VyY2VGaWxlLCBkZXB0aCwgdmlzaXRlZCwgZmFsbGJhY2tTY29wZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3Qgd2FsayA9IChub2RlOiB0cy5Ob2RlKTogdm9pZCA9PiB7XG5cdFx0XHRpZiAobm9kZSAhPT0gZm4uYm9keSAmJiAoXG5cdFx0XHRcdHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKG5vZGUpIHx8XG5cdFx0XHRcdHRzLmlzQXJyb3dGdW5jdGlvbihub2RlKSB8fFxuXHRcdFx0XHR0cy5pc0Z1bmN0aW9uRGVjbGFyYXRpb24obm9kZSkgfHxcblx0XHRcdFx0dHMuaXNNZXRob2REZWNsYXJhdGlvbihub2RlKVxuXHRcdFx0KSkge1xuXHRcdFx0XHQvLyBuZXN0ZWQgZnVuY3Rpb24gYm9kaWVzIGFyZSBhbmFseXNlZCB0aHJvdWdoIHRoZSByZXR1cm4gY2hhaW5cblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0XHR0aGlzLnJlY29yZFdyYXBwZWRSZXR1cm4obm9kZS5leHByZXNzaW9uLCB2aWFMb2NhdGlvbiwgc291cmNlRmlsZSwgZGVwdGgsIHZpc2l0ZWQsIGZhbGxiYWNrU2NvcGUpO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzTmV3RXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0XHRjb25zdCBjcmVhdGVkID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKSB8fFxuXHRcdFx0XHRcdCh0cy5pc0lkZW50aWZpZXIobm9kZS5leHByZXNzaW9uKSAmJiB0aGlzLmRlZmluaXRpb25zLmhhcyhub2RlLmV4cHJlc3Npb24udGV4dClcblx0XHRcdFx0XHRcdD8gbm9kZS5leHByZXNzaW9uLnRleHRcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkKTtcblx0XHRcdFx0aWYgKGNyZWF0ZWQpIHtcblx0XHRcdFx0XHRjcmVhdGVzVHlwZXMuYWRkKGNyZWF0ZWQpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0XHRjb25zdCBuZXN0ZWROYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKTtcblx0XHRcdFx0aWYgKFxuXHRcdFx0XHRcdG5lc3RlZE5hbWUgPT09ICd3cmFwJyB8fFxuXHRcdFx0XHRcdG5lc3RlZE5hbWUgPT09ICd3cmFwQ29uc3RydWN0b3JBcmcnIHx8XG5cdFx0XHRcdFx0bmVzdGVkTmFtZSA9PT0gJ3VwZ3JhZGVDb25zdHJ1Y3RvckFyZycgfHxcblx0XHRcdFx0XHRuZXN0ZWROYW1lID09PSAnd3JhcEluc3RhbmNlTWV0aG9kcydcblx0XHRcdFx0KSB7XG5cdFx0XHRcdFx0Ly8gdGhlIG5lc3RlZCBjYWxsIG1heSBhbHJlYWR5IGJlIGNvbGxlY3RlZCAodmlzaXRlZFxuXHRcdFx0XHRcdC8vIGJlZm9yZSB0aGlzIG91dGVyIHdyYXAgc2l0ZSkg4oCUIGJhY2stcGF0Y2ggaXRzIGVudHJ5LFxuXHRcdFx0XHRcdC8vIG90aGVyd2lzZSBsZWF2ZSB0aGUgbGluayAod2l0aCB0aGlzIHNpdGUncyBzY29wZSkgZm9yXG5cdFx0XHRcdFx0Ly8gY29sbGVjdEVEUyB0byBwaWNrIHVwXG5cdFx0XHRcdFx0Y29uc3QgbmVzdGVkRW50cnkgPSB0aGlzLndyYXBFbnRyeUJ5Tm9kZS5nZXQobm9kZSk7XG5cdFx0XHRcdFx0aWYgKG5lc3RlZEVudHJ5KSB7XG5cdFx0XHRcdFx0XHRuZXN0ZWRFbnRyeS52aWEgPSB2aWFMb2NhdGlvbjtcblx0XHRcdFx0XHRcdGlmIChuZXN0ZWRFbnRyeS5zY29wZSA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdFx0XHRcdG5lc3RlZEVudHJ5LnNjb3BlID0gZmFsbGJhY2tTY29wZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0dGhpcy5uZXN0ZWRXcmFwVmlhLnNldChub2RlLCB7IHZpYSA6IHZpYUxvY2F0aW9uLCBzY29wZSA6IGZhbGxiYWNrU2NvcGUgfSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgd2Fsayk7XG5cdFx0fTtcblx0XHR3YWxrKGZuLmJvZHkpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBvbmUgZnVuY3Rpb24tdmFsdWVkIHJldHVybiBvZiBhIHdyYXBwZWQgYm9keSBhcyBhIG5lc3RlZCB3cmFwXG5cdCAqIHNpdGUgKGB2aWFgID0gdGhlIHNpdGUgd2hvc2Ugd3JhcHBpbmcgY2F1c2VkIGl0KSBhbmQgcmVjdXJzZSBpbnRvXG5cdCAqIGl0cyBvd24gcmV0dXJucy4gUmV0dXJucyB0aHJvdWdoIGlkZW50aWZpZXJzIHJlc29sdmUgdGhyb3VnaCB0aGVcblx0ICogc2FtZS1maWxlIGJpbmRpbmdzIHRhYmxlOyB1bnJlc29sdmFibGUgcmV0dXJucyBhcmUgc2ltcGx5IHNraXBwZWQuXG5cdCAqIEEgcmV0dXJuIGRlY2xhcmVkIG91dHNpZGUgYW55IHR5cGUgc2NvcGUgaW5oZXJpdHMgdGhlIGNhdXNpbmcgd3JhcFxuXHQgKiBzaXRlJ3Mgc2NvcGUgYXR0cmlidXRpb24gKHRoZSBnZW5lcmF0aW9uIGNoYWluIGlzIHRoZSBvbmx5IGhvbGRlcikuXG5cdCAqL1xuXHRwcml2YXRlIHJlY29yZFdyYXBwZWRSZXR1cm4gKFxuXHRcdGV4cHI6IHRzLkV4cHJlc3Npb24sXG5cdFx0dmlhTG9jYXRpb246IHN0cmluZyxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdGRlcHRoOiBudW1iZXIsXG5cdFx0dmlzaXRlZDogU2V0PHRzLk5vZGU+LFxuXHRcdGZhbGxiYWNrU2NvcGU/OiBzdHJpbmdcblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgcmV0dXJuZWQgPSB0aGlzLnJlc29sdmVGdW5jdGlvbkFyZ3VtZW50KGV4cHIsIHNvdXJjZUZpbGUpO1xuXHRcdGlmICghcmV0dXJuZWQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdHJldHVybmVkLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSByZXR1cm5lZC5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cdFx0Y29uc3Qgc2NvcGUgPSB0aGlzLnJlc29sdmVFRFNTY29wZShyZXR1cm5lZCkgPz8gZmFsbGJhY2tTY29wZTtcblx0XHRjb25zdCBlbnRyeSA9IHRoaXMuYWRkRURTKHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kIDogJ3dyYXAnLFxuXHRcdFx0Y29kZSxcblx0XHRcdHNjb3BlLFxuXHRcdFx0dmlhICA6IHZpYUxvY2F0aW9uLFxuXHRcdFx0Ly8gZGl2ZSB3cmFwcyByZXR1cm5lZCBmdW5jdGlvbnMgdGhyb3VnaCB0aGUgc2FtZSB3cmFwIG1hY2hpbmVyeVxuXHRcdFx0Zm4gICA6ICd3cmFwJyxcblx0XHR9KTtcblx0XHQvLyB0aGUgcmV0dXJuZWQgZnVuY3Rpb24ncyBvd24gcmV0dXJucyBhcmUgd3JhcHBlZCBpbiB0dXJuOyBgdmlhYFxuXHRcdC8vIGNoYWlucyB0byB0aGlzIG5lc3RlZCBlbnRyeSdzIGxvY2F0aW9uXG5cdFx0Y29uc3QgbmVzdGVkQ3JlYXRlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdHRoaXMuYW5hbHl6ZVdyYXBwZWRCb2R5KHJldHVybmVkLCBsb2NhdGlvbiwgc291cmNlRmlsZSwgZGVwdGggKyAxLCB2aXNpdGVkLCBuZXN0ZWRDcmVhdGVzLCBzY29wZSk7XG5cdFx0aWYgKG5lc3RlZENyZWF0ZXMuc2l6ZSA+IDApIHtcblx0XHRcdGVudHJ5LmNyZWF0ZXNUeXBlcyA9IEFycmF5LmZyb20obmVzdGVkQ3JlYXRlcyk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhbiBFRFMgdXNhZ2UgdG8gdGhlIGNvbGxlY3Rpb25cblx0ICogUmV0dXJucyB0aGUgc3RvcmVkIGVudHJ5ICh0aGUgZXhpc3Rpbmcgb25lIHdoZW4gdGhpcyBpcyBhIGR1cGxpY2F0ZSksXG5cdCAqIHNvIGNhbGxlcnMgY2FuIGVucmljaCBpdCBhZnRlciBuZXN0ZWQgYm9keSBhbmFseXNpcy5cblx0ICovXG5cdHByaXZhdGUgYWRkRURTICh0eXBlUGF0aDogc3RyaW5nLCBpbmZvOiBFRFNJbmZvKTogRURTSW5mbyB7XG5cdFx0aWYgKCF0aGlzLmVkc1VzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLmVkc1VzYWdlcy5zZXQodHlwZVBhdGgsIFtdKTtcblx0XHR9XG5cblx0XHRjb25zdCBleGlzdGluZyA9IHRoaXMuZWRzVXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGR1cGxpY2F0ZSA9IGV4aXN0aW5nLmZpbmQoZSA9PiB7XG5cdFx0XHRyZXR1cm4gZS5sb2NhdGlvbiA9PT0gaW5mby5sb2NhdGlvbiAmJlxuXHRcdFx0XHRlLmtpbmQgPT09IGluZm8ua2luZCAmJlxuXHRcdFx0XHRlLmNvZGUgPT09IGluZm8uY29kZTtcblx0XHR9KTtcblxuXHRcdGlmIChkdXBsaWNhdGUpIHtcblx0XHRcdHJldHVybiBkdXBsaWNhdGU7XG5cdFx0fVxuXHRcdGV4aXN0aW5nLnB1c2goaW5mbyk7XG5cdFx0cmV0dXJuIGluZm87XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBuYXRpdmUgZmxvdyBwYXR0ZXJucyAoaW5zdGFuY2UgdXNhZ2UgYWZ0ZXIgY3JlYXRpb24pXG5cdCAqIFBoYXNlIDE6IHByb3BlcnR5IGFjY2VzcywgbWV0aG9kIGNhbGxzLCBhcmd1bWVudHMsIHJldHVybiwgZGVzdHJ1Y3R1cmluZywgZXRjLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0RmxvdyAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIFByb3BlcnR5IHJlYWQ6IHVzZXIubmFtZSBvciB1c2VyPy5uYW1lXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93UHJvcGVydHlBY2Nlc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRWxlbWVudCBhY2Nlc3M6IHVzZXJbJ25hbWUnXVxuXHRcdGlmICh0cy5pc0VsZW1lbnRBY2Nlc3NFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93RWxlbWVudEFjY2Vzcyhub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSB3cml0ZTogdXNlci5uYW1lID0gdmFsdWVcblx0XHRpZiAodHMuaXNCaW5hcnlFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkVxdWFsc1Rva2VuKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93QXNzaWdubWVudChub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBNZXRob2QgY2FsbDogdXNlci52YWxpZGF0ZSgpICBBTkQgIGFyZ3VtZW50IHBhc3Npbmc6IHByb2Nlc3NVc2VyKHVzZXIpXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93TWV0aG9kQ2FsbChub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dBcmd1bWVudFBhc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRGVzdHJ1Y3R1cmUgcmVhZDogY29uc3QgeyBuYW1lIH0gPSB1c2VyXG5cdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLmluaXRpYWxpemVyKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93RGVzdHJ1Y3R1cmUobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUmV0dXJuIGluc3RhbmNlOiByZXR1cm4gdXNlclxuXHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dSZXR1cm4obm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gU3ByZWFkOiB7IC4uLnVzZXIgfVxuXHRcdGlmICh0cy5pc1NwcmVhZEVsZW1lbnQobm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dTcHJlYWQobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgcHJvcGVydHkgYWNjZXNzIGZsb3cgKHJlYWQgb3IgY29uZGl0aW9uYWwpXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93UHJvcGVydHlBY2Nlc3MgKG5vZGU6IHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHByb3BOYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0Ly8gU2tpcCBpZiB0aGlzIGlzIGEgdHlwZSBjb25zdHJ1Y3RvciBhY2Nlc3MgKGUuZy4sIFVzZXJUeXBlLmRlZmluZSlcblx0XHRpZiAocHJvcE5hbWUgPT09ICdkZWZpbmUnIHx8IHByb3BOYW1lID09PSAnbGF6eScpIHsgcmV0dXJuOyB9XG5cblx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgICAgOiAncHJvcGVydHlSZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHRwcm9wZXJ0eU5hbWUgOiBwcm9wTmFtZSxcblx0XHRcdHRhcmdldFR5cGUgICA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGVsZW1lbnQgYWNjZXNzIGZsb3c6IHVzZXJbJ25hbWUnXVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0VsZW1lbnRBY2Nlc3MgKG5vZGU6IHRzLkVsZW1lbnRBY2Nlc3NFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3Qgb2JqZWN0VHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0aWYgKCFvYmplY3RUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0dGhpcy5hZGRGbG93KG9iamVjdFR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICA6ICdlbGVtZW50QWNjZXNzJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogb2JqZWN0VHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgYXNzaWdubWVudCBmbG93OiB1c2VyLm5hbWUgPSB2YWx1ZSBvciB1c2VyID0gb3RoZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dBc3NpZ25tZW50IChub2RlOiB0cy5CaW5hcnlFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gUHJvcGVydHkgd3JpdGU6IHVzZXIubmFtZSA9IHZhbHVlXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUubGVmdCkpIHtcblx0XHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmxlZnQuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRcdGNvbnN0IHByb3BOYW1lID0gbm9kZS5sZWZ0Lm5hbWUudGV4dDtcblx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0KTtcblx0XHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgICAgOiAncHJvcGVydHlXcml0ZScsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHByb3BlcnR5TmFtZSA6IHByb3BOYW1lLFxuXHRcdFx0XHR0YXJnZXRUeXBlICAgOiBvYmplY3RUeXBlXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBWYXJpYWJsZSByZWFzc2lnbm1lbnQ6IHVzZXIgPSBvdGhlclxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIobm9kZS5sZWZ0KSkge1xuXHRcdFx0Y29uc3QgdmFyTmFtZSA9IG5vZGUubGVmdC50ZXh0O1xuXHRcdFx0Y29uc3QgbWFwcGVkVHlwZSA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KHZhck5hbWUpO1xuXHRcdFx0aWYgKCFtYXBwZWRUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdCk7XG5cdFx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0XHR0aGlzLmFkZEZsb3cobWFwcGVkVHlwZSwge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCAgICAgICA6ICdyZWFzc2lnbm1lbnQnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHR0YXJnZXRUeXBlIDogbWFwcGVkVHlwZVxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgbWV0aG9kIGNhbGwgZmxvdzogdXNlci52YWxpZGF0ZSgpXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93TWV0aG9kQ2FsbCAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbikpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IG1ldGhvZE5hbWUgPSBub2RlLmV4cHJlc3Npb24ubmFtZS50ZXh0O1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIFNraXAgaWYgdGhpcyBpcyBhIHR5cGUgY29uc3RydWN0b3IgY2FsbCAoZS5nLiwgbmV3IFVzZXJUeXBlKCkpXG5cdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdkZWZpbmUnIHx8IG1ldGhvZE5hbWUgPT09ICdsYXp5JykgeyByZXR1cm47IH1cblxuXHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgICA6ICdtZXRob2RDYWxsJyxcblx0XHRcdGNvZGUsXG5cdFx0XHRwcm9wZXJ0eU5hbWUgOiBtZXRob2ROYW1lLFxuXHRcdFx0dGFyZ2V0VHlwZSAgIDogb2JqZWN0VHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgYXJndW1lbnQgcGFzc2luZyBmbG93OiBwcm9jZXNzVXNlcih1c2VyKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0FyZ3VtZW50UGFzcyAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRjb25zdCBhcmcgPSBub2RlLmFyZ3VtZW50c1sgaSBdO1xuXHRcdFx0Y29uc3QgYXJnVHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKGFyZyk7XG5cdFx0XHRpZiAoIWFyZ1R5cGUpIHsgY29udGludWU7IH1cblxuXHRcdFx0Y29uc3QgZnVuY05hbWUgPSB0aGlzLmdldEZ1bmN0aW9uTmFtZShub2RlLmV4cHJlc3Npb24pIHx8ICdhbm9ueW1vdXMnO1xuXHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHQpO1xuXHRcdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdFx0dGhpcy5hZGRGbG93KGFyZ1R5cGUsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAncGFzc0FzQXJnJyxcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSA6IGFyZ1R5cGUsXG5cdFx0XHRcdGNvbnRleHQgICAgOiBgYXJnICR7aX0gdG8gJHtmdW5jTmFtZX1gXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBkZXN0cnVjdHVyaW5nIGZsb3c6IGNvbnN0IHsgbmFtZSB9ID0gdXNlclxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0Rlc3RydWN0dXJlIChub2RlOiB0cy5WYXJpYWJsZURlY2xhcmF0aW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc09iamVjdEJpbmRpbmdQYXR0ZXJuKG5vZGUubmFtZSkpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBzb3VyY2VUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5pbml0aWFsaXplciEpO1xuXHRcdGlmICghc291cmNlVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIEV4dHJhY3QgZGVzdHJ1Y3R1cmVkIHByb3BlcnR5IG5hbWVzXG5cdFx0Y29uc3QgcHJvcHM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIG5vZGUubmFtZS5lbGVtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihlbGVtZW50Lm5hbWUpKSB7XG5cdFx0XHRcdHByb3BzLnB1c2goZWxlbWVudC5uYW1lLnRleHQpO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHRoaXMuYWRkRmxvdyhzb3VyY2VUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnZGVzdHJ1Y3R1cmVSZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogc291cmNlVHlwZSxcblx0XHRcdGNvbnRleHQgICAgOiBwcm9wcy5qb2luKCcsICcpXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCByZXR1cm4gZmxvdzogcmV0dXJuIHVzZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dSZXR1cm4gKG5vZGU6IHRzLlJldHVyblN0YXRlbWVudCwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHJldHVyblR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24hKTtcblx0XHRpZiAoIXJldHVyblR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHR0aGlzLmFkZEZsb3cocmV0dXJuVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ3JldHVybicsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHJldHVyblR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IHNwcmVhZCBmbG93OiB7IC4uLnVzZXIgfVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd1NwcmVhZCAobm9kZTogdHMuU3ByZWFkRWxlbWVudCwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHNwcmVhZFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghc3ByZWFkVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuYWRkRmxvdyhzcHJlYWRUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnc3ByZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogc3ByZWFkVHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgdHlwZSBmcm9tIGFuIGV4cHJlc3Npb24gKGlkZW50aWZpZXIsIHByb3BlcnR5IGFjY2VzcywgZXRjLilcblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUV4cHJlc3Npb25UeXBlIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBJZGVudGlmaWVyOiB1c2VyXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGV4cHIudGV4dCk7XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiB1c2VyLm5hbWUgKHJldHVybiBvYmplY3QgdHlwZSwgbm90IHByb3BlcnR5IHR5cGUpXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUoZXhwci5leHByZXNzaW9uKTtcblx0XHR9XG5cblx0XHQvLyBFbGVtZW50IGFjY2VzczogdXNlclsnbmFtZSddXG5cdFx0aWYgKHRzLmlzRWxlbWVudEFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdHJldHVybiB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShleHByLmV4cHJlc3Npb24pO1xuXHRcdH1cblxuXHRcdC8vIFRoaXMgZXhwcmVzc2lvbjogdGhpcyAoaWYgaW4gYSBtZXRob2QsIHdlIGNhbid0IHJlc29sdmUgd2l0aG91dCBtb3JlIGNvbnRleHQpXG5cdFx0aWYgKGV4cHIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhIGZsb3cgdXNhZ2UgdG8gdGhlIGNvbGxlY3Rpb25cblx0ICovXG5cdHByaXZhdGUgYWRkRmxvdyAodHlwZVBhdGg6IHN0cmluZywgaW5mbzogRmxvd0luZm8pOiB2b2lkIHtcblx0XHRpZiAoIXRoaXMuZmxvd1VzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLmZsb3dVc2FnZXMuc2V0KHR5cGVQYXRoLCBbXSk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZXhpc3RpbmcgPSB0aGlzLmZsb3dVc2FnZXMuZ2V0KHR5cGVQYXRoKSE7XG5cdFx0Y29uc3QgaXNEdXBsaWNhdGUgPSBleGlzdGluZy5zb21lKGUgPT4ge1xuXHRcdFx0cmV0dXJuIGUubG9jYXRpb24gPT09IGluZm8ubG9jYXRpb24gJiZcblx0XHRcdFx0ZS5raW5kID09PSBpbmZvLmtpbmQgJiZcblx0XHRcdFx0ZS5jb2RlID09PSBpbmZvLmNvZGU7XG5cdFx0fSk7XG5cblx0XHRpZiAoIWlzRHVwbGljYXRlKSB7XG5cdFx0XHRleGlzdGluZy5wdXNoKGluZm8pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdFx0KiBHZXQgdHlwZSBuYW1lIGZyb20gZXhwcmVzc2lvbiAoaWRlbnRpZmllciBvciBwcm9wZXJ0eSBhY2Nlc3MpXG5cdFx0XHQqL1xuXHRwcml2YXRlIGdldFR5cGVOYW1lRnJvbUV4cHJlc3Npb24gKGV4cHI6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdGNvbnN0IG5hbWUgPSBleHByLnRleHQ7XG5cdFx0XHQvLyBDaGVjayBpZiB0aGlzIGlkZW50aWZpZXIgaXMgYSB2YXJpYWJsZSBtYXBwZWQgdG8gYSB0eXBlIChlLmcuLCBmcm9tIGxvb2t1cClcblx0XHRcdGNvbnN0IG1hcHBlZFR5cGUgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChuYW1lKTtcblx0XHRcdGlmIChtYXBwZWRUeXBlKSB7XG5cdFx0XHRcdHJldHVybiBtYXBwZWRUeXBlO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIG5hbWU7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4oZXhwcik7XG5cdFx0XHRyZXR1cm4gY2hhaW4uam9pbignLicpO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cdFxuXHQvKipcblx0ICogVGhlIG9uZSBjYW5kaWRhdGUgd2hvc2UgcGFyZW50IHR5cGUgaXMgZGVmaW5lZCBpbiBgZmlsZU5hbWVgLCBvclxuXHQgKiB1bmRlZmluZWQgd2hlbiBub25lIG9yIHNldmVyYWwgcXVhbGlmeS5cblx0ICovXG5cdHByaXZhdGUgc3VidHlwZU93bmVkQnlGaWxlIChjYW5kaWRhdGVzOiBzdHJpbmdbXSwgZmlsZU5hbWU6IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgZmlsZSA9IG5vZGVQYXRoLnJlc29sdmUoZmlsZU5hbWUpO1xuXHRcdGNvbnN0IG93bmVkID0gY2FuZGlkYXRlcy5maWx0ZXIoKGNhbmRpZGF0ZSkgPT4ge1xuXHRcdFx0Y29uc3QgcGFyZW50ID0gdGhpcy5kZWZpbml0aW9ucy5nZXQoY2FuZGlkYXRlKT8ucGFyZW50O1xuXHRcdFx0Y29uc3QgcGFyZW50TG9jYXRpb24gPSBwYXJlbnQgPyB0aGlzLmRlZmluaXRpb25zLmdldChwYXJlbnQpPy5sb2NhdGlvbiA6IHVuZGVmaW5lZDtcblx0XHRcdGNvbnN0IHBhcmVudEZpbGUgPSBwYXJlbnRMb2NhdGlvbiA/IHBhcmVudExvY2F0aW9uLnJlcGxhY2UoLzpcXGQrOlxcZCskLywgJycpIDogdW5kZWZpbmVkO1xuXHRcdFx0Y29uc3QgaW5GaWxlID0gcGFyZW50RmlsZSAhPT0gdW5kZWZpbmVkICYmIG5vZGVQYXRoLnJlc29sdmUocGFyZW50RmlsZSkgPT09IGZpbGU7XG5cdFx0XHRyZXR1cm4gaW5GaWxlO1xuXHRcdH0pO1xuXHRcdGNvbnN0IHJlc3VsdCA9IG93bmVkLmxlbmd0aCA9PT0gMSA/IG93bmVkWyAwIF0gOiB1bmRlZmluZWQ7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHRcdFx0KiBSZXNvbHZlIGZ1bGwgdHlwZSBwYXRoIGZyb20gcHJvcGVydHkgYWNjZXNzXG5cdFx0XHQqL1xuXHRwcml2YXRlIHJlc29sdmVUeXBlUGF0aCAoZXhwcjogdHMuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBjaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlDaGFpbihleHByKTtcblx0XHRpZiAoY2hhaW4ubGVuZ3RoID09PSAwKSByZXR1cm4gdW5kZWZpbmVkO1xuXHRcblx0XHQvLyBDaGVjayBpZiB0aGlzIGNoYWluIG1hdGNoZXMgYSBrbm93biB0eXBlXG5cdFx0Y29uc3QgZnVsbFBhdGggPSBjaGFpbi5qb2luKCcuJyk7XG5cdFx0aWYgKHRoaXMuZGVmaW5pdGlvbnMuaGFzKGZ1bGxQYXRoKSkge1xuXHRcdFx0cmV0dXJuIGZ1bGxQYXRoO1xuXHRcdH1cblx0XG5cdFx0Ly8gSW5zdGFuY2UgcmVjZWl2ZXI6IGBsZXNzb24uTmF0aXZlYCB3aGVyZSBgbGVzc29uYCBpcyBib3VuZCB0byBhXG5cdFx0Ly8gUnVuLkxlc3NvbiBpbnN0YW5jZSBtZWFucyBSdW4uTGVzc29uLk5hdGl2ZSDigJQgcmVzb2x2ZSB0aHJvdWdoIHRoZVxuXHRcdC8vIHZhcmlhYmxlJ3MgdHlwZSBiZWZvcmUgZmFsbGluZyBiYWNrIHRvIHRoZSBiYXJlIG5hbWVcblx0XHRpZiAoY2hhaW4ubGVuZ3RoID4gMSkge1xuXHRcdFx0Y29uc3QgcmVjZWl2ZXJUeXBlID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQoY2hhaW5bIDAgXSk7XG5cdFx0XHRjb25zdCB2aWFSZWNlaXZlciA9IHJlY2VpdmVyVHlwZSA/IGAke3JlY2VpdmVyVHlwZX0uJHtjaGFpbi5zbGljZSgxKS5qb2luKCcuJyl9YCA6IHVuZGVmaW5lZDtcblx0XHRcdGlmICh2aWFSZWNlaXZlciAmJiB0aGlzLmRlZmluaXRpb25zLmhhcyh2aWFSZWNlaXZlcikpIHtcblx0XHRcdFx0cmV0dXJuIHZpYVJlY2VpdmVyO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIFRyeSBqdXN0IHRoZSBwcm9wZXJ0eSBuYW1lXG5cdFx0Y29uc3QgcHJvcE5hbWUgPSBjaGFpblsgY2hhaW4ubGVuZ3RoIC0gMSBdO1xuXHRcdGNvbnN0IGNhbmRpZGF0ZXM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBbIHBhdGggXSBvZiB0aGlzLmRlZmluaXRpb25zKSB7XG5cdFx0XHRpZiAocGF0aC5lbmRzV2l0aChgLiR7cHJvcE5hbWV9YCkgfHwgcGF0aCA9PT0gcHJvcE5hbWUpIHtcblx0XHRcdFx0Y2FuZGlkYXRlcy5wdXNoKHBhdGgpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHQvLyBTZXZlcmFsIHR5cGVzIHNoYXJlIHRoZSBuYW1lIChDb3JyZWN0LlN0YXRVcGRhdGUgYW5kXG5cdFx0Ly8gTWlzdGFrZS5TdGF0VXBkYXRlKTogYG5ldyB0aGlzLlN0YXRVcGRhdGUoKWAgaW5zaWRlIGEgdHlwZSdzIG93blxuXHRcdC8vIGZpbGUgbWVhbnMgVEhBVCB0eXBlJ3Mgc3VidHlwZSDigJQgcHJlZmVyIHRoZSBjYW5kaWRhdGUgd2hvc2UgcGFyZW50XG5cdFx0Ly8gaXMgZGVmaW5lZCBpbiB0aGUgZmlsZSB0aGUgYWNjZXNzIHNpdHMgaW4gKHRvcG9sb2dpY2E6IG9uZSBmaWxlXG5cdFx0Ly8gcGVyIHR5cGUpLiBPdGhlcndpc2UgdGhlIGZpcnN0IG1hdGNoLCBhcyBiZWZvcmUuXG5cdFx0aWYgKGNhbmRpZGF0ZXMubGVuZ3RoID4gMSkge1xuXHRcdFx0Y29uc3Qgb3duZWQgPSB0aGlzLnN1YnR5cGVPd25lZEJ5RmlsZShjYW5kaWRhdGVzLCBleHByLmdldFNvdXJjZUZpbGUoKS5maWxlTmFtZSk7XG5cdFx0XHRpZiAob3duZWQpIHtcblx0XHRcdFx0cmV0dXJuIG93bmVkO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAoY2FuZGlkYXRlcy5sZW5ndGggPiAwKSB7XG5cdFx0XHRyZXR1cm4gY2FuZGlkYXRlc1sgMCBdO1xuXHRcdH1cblxuXHRcdHJldHVybiBmdWxsUGF0aDtcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQgKiBDaGVjayBpZiBhIG5hbWUgbG9va3MgbGlrZSBhIHR5cGUgKHN0YXJ0cyB3aXRoIHVwcGVyY2FzZSlcblx0XHRcdCAqL1xuXHRwcml2YXRlIGlzTGlrZWx5VHlwZU5hbWUgKG5hbWU6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRcdHJldHVybiBuYW1lWyAwIF0gPj0gJ0EnICYmIG5hbWVbIDAgXSA8PSAnWic7XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0ICogUmVzb2x2ZSBhIGNvbnN0cnVjdG9yIHBhcmFtZXRlciB0eXBlLCBleHBhbmRpbmcgaW5saW5lIG9iamVjdCBsaXRlcmFsc1xuXHRcdFx0ICogYW5kIHR5cGUgYWxpYXNlcyB3aGVyZSBwb3NzaWJsZS5cblx0XHRcdCAqL1xuXHRwcml2YXRlIHJlc29sdmVDb25zdHJ1Y3RvclBhcmFtVHlwZSAodHlwZU5vZGU6IHRzLlR5cGVOb2RlIHwgdW5kZWZpbmVkKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIXR5cGVOb2RlKSByZXR1cm4gdW5kZWZpbmVkO1xuXG5cdFx0Ly8gRGlyZWN0IGlubGluZSB0eXBlIGxpdGVyYWw6IHsgcHJvcDogdHlwZSB9XG5cdFx0aWYgKHRzLmlzVHlwZUxpdGVyYWxOb2RlKHR5cGVOb2RlKSkge1xuXHRcdFx0Y29uc3QgcHJvcHM6IHN0cmluZ1tdID0gW107XG5cdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiB0eXBlTm9kZS5tZW1iZXJzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRjb25zdCBvcHRpb25hbCA9IG1lbWJlci5xdWVzdGlvblRva2VuID8gJz8nIDogJyc7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRwcm9wcy5wdXNoKGAke3Byb3BOYW1lfSR7b3B0aW9uYWx9OiAke3R5cGV9YCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiBgeyAke3Byb3BzLmpvaW4oJzsgJyl9IH1gO1xuXHRcdH1cblxuXHRcdC8vIFR5cGUgcmVmZXJlbmNlOiB1c2FnZSwgVXNlckRhdGEsIGV0Yy4gLSByZXNvbHZlIGltcG9ydC1hd2FyZSBhbmRcblx0XHQvLyBleHBhbmQgdGhlIHJlZmVyZW5jZWQgZGVjbGFyYXRpb24gd2hlcmUgcG9zc2libGUgKEYxMClcblx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZSh0eXBlTm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKHR5cGVOb2RlLnR5cGVOYW1lKSkge1xuXHRcdFx0Y29uc3QgdHlwZU5hbWUgPSB0eXBlTm9kZS50eXBlTmFtZS50ZXh0O1xuXHRcdFx0Y29uc3QgZGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24odHlwZU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRpZiAoZGVjbCkge1xuXHRcdFx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMuZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihkZWNsKTtcblx0XHRcdFx0aWYgKGV4cGFuZGVkKSByZXR1cm4gZXhwYW5kZWQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBtbmVtb25pY2EgZ3JhcGggdHlwZXMga2VlcCB0aGVpciBzaW1wbGUgbmFtZSDigJQgdGhlIGdlbmVyYXRvclxuXHRcdFx0Ly8gdXBncmFkZXMgdGhlbSB0byBmdWxsLXBhdGggaW5zdGFuY2UgdHlwZSBuYW1lcy4gUmVzb2x1dGlvbiBpc1xuXHRcdFx0Ly8gcGF0aC1hd2FyZSAoaGFyZC1mYWlsIGxhdyk6IGFtYmlndWl0eSBiZXR3ZWVuIHJlYWwgZ3JhcGggdHlwZXNcblx0XHRcdC8vIHJlY29yZHMgYSBmYXRhbCBlcnJvciBpbnN0ZWFkIG9mIHNpbGVudGx5IHBpY2tpbmcgb25lLlxuXHRcdFx0Y29uc3QgZ3JhcGhSZXN1bHQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKHR5cGVOYW1lKTtcblx0XHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRcdGNvbnN0IHNpbXBsZVJlc3VsdCA9IHR5cGVOYW1lO1xuXHRcdFx0XHRyZXR1cm4gc2ltcGxlUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0aWYgKGdyYXBoUmVzdWx0LnN0YXR1cyA9PT0gJ2FtYmlndW91cycpIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yKHR5cGVOYW1lLCB0eXBlTm9kZSwgZ3JhcGhSZXN1bHQpO1xuXHRcdFx0XHRjb25zdCB1bmtub3duR3JhcGhSZXN1bHQgPSAndW5rbm93bic7XG5cdFx0XHRcdHJldHVybiB1bmtub3duR3JhcGhSZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBJZiBub3QgYW4gb2JqZWN0IHR5cGUgYWxpYXMsIHJldHVybiB0aGUgdHlwZSBuYW1lIHdpdGggYXJnc1xuXHRcdFx0aWYgKHR5cGVOb2RlLnR5cGVBcmd1bWVudHMgJiYgdHlwZU5vZGUudHlwZUFyZ3VtZW50cy5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdGlmIChLTk9XTl9HTE9CQUxfVFlQRVMuaGFzKHR5cGVOYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IGFyZ3MgPSB0eXBlTm9kZS50eXBlQXJndW1lbnRzLm1hcChhcmcgPT4gdGhpcy5pbmZlclR5cGUoYXJnKSk7XG5cdFx0XHRcdFx0cmV0dXJuIGAke3R5cGVOYW1lICB9PCR7ICBhcmdzLmpvaW4oJywgJykgIH0+YDtcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBnZW5lcmljIHJlZmVyZW5jZSB0byBhIG5vbi1nbG9iYWwsIG5vbi1ncmFwaCB0eXBlIGNhbm5vdCBiZVxuXHRcdFx0XHQvLyBlbWl0dGVkIGJhcmUgaW50byB0aGUgZ2VuZXJhdGVkIGZpbGVcblx0XHRcdFx0dGhpcy5yZWNvcmRQbGFpblR5cGVSZWZlcmVuY2VTaXRlKHR5cGVOYW1lLCB0eXBlTm9kZSk7XG5cdFx0XHRcdGNvbnN0IHVua25vd25HZW5lcmljUmVzdWx0ID0gJ3Vua25vd24nO1xuXHRcdFx0XHRyZXR1cm4gdW5rbm93bkdlbmVyaWNSZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBmYWxsYmFja1Jlc3VsdCA9IHRoaXMudW5yZXNvbHZlZFR5cGVSZWZlcmVuY2VGYWxsYmFjayh0eXBlTmFtZSwgdHlwZU5vZGUpO1xuXHRcdFx0cmV0dXJuIGZhbGxiYWNrUmVzdWx0O1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0XHRcdCAqIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGEgY2xhc3MtbGlrZSBub2RlLlxuXHRcdFx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENsYXNzQ29uc3RydWN0b3JQYXJhbXMgKGNsYXNzTGlrZTogdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHRzLkNsYXNzRXhwcmVzc2lvbik6XG5cdFx0Q29uc3RydWN0b3JQYXJhbUluZm9bXSB7XG5cdFx0Y29uc3QgcGFyYW1zOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdID0gW107XG5cblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjbGFzc0xpa2UubWVtYmVycykge1xuXHRcdFx0aWYgKCF0cy5pc0NvbnN0cnVjdG9yRGVjbGFyYXRpb24obWVtYmVyKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblxuXHRcdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBtZW1iZXIucGFyYW1ldGVycykge1xuXHRcdFx0XHRpZiAoIXBhcmFtLm5hbWUgfHwgIXRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSkgY29udGludWU7XG5cdFx0XHRcdGlmICghcGFyYW0udHlwZSkgY29udGludWU7XG5cblx0XHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gcGFyYW0ubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBleHBhbmRlZFR5cGUgPSB0aGlzLnJlc29sdmVDb25zdHJ1Y3RvclBhcmFtVHlwZShwYXJhbS50eXBlKSB8fCB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblxuXHRcdFx0XHRwYXJhbXMucHVzaCh7XG5cdFx0XHRcdFx0bmFtZSAgICAgOiBwYXJhbU5hbWUsXG5cdFx0XHRcdFx0dHlwZSAgICAgOiBleHBhbmRlZFR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiAhIXBhcmFtLnF1ZXN0aW9uVG9rZW4gfHwgISFwYXJhbS5pbml0aWFsaXplcixcblx0XHRcdFx0XHQvLyByZXN0IG1hcmtlciBmb3IgdGhlIGRlZmluaXRpb25zLmpzb24gYXJncyBjb250cmFjdFxuXHRcdFx0XHRcdC4uLihwYXJhbS5kb3REb3REb3RUb2tlbiA/IHsga2luZCA6ICdyZXN0JyBhcyBjb25zdCB9IDoge30pXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdFx0Ly8gT25seSBwcm9jZXNzIGZpcnN0IGNvbnN0cnVjdG9yXG5cdFx0XHRicmVhaztcblx0XHR9XG5cblx0XHRyZXR1cm4gcGFyYW1zO1xuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBkZWZpbmUoKSBjYWxsXG5cdFx0XHQgKiBUaGlzIGlzIHVzZWQgZm9yIFR5cGVSZWdpc3RyeSBjb25zdHJ1Y3RvciBzaWduYXR1cmVzXG5cdFx0XHQgKiBQcmVzZXJ2ZXMgcGFyYW1ldGVyIG5hbWVzIGFuZCBleHBhbmRzIG9iamVjdCB0eXBlcyB0byB0aGVpciBzdHJ1Y3R1cmVcblx0XHRcdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdIHtcblx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCk7XG5cdFx0aWYgKCFjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdGNvbnN0IGZhbGxiYWNrUGFyYW1zOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdID0gWyB7XG5cdFx0XHRcdG5hbWUgICAgIDogJ2FyZ3MnLFxuXHRcdFx0XHR0eXBlICAgICA6ICd1bmtub3duW10nLFxuXHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRraW5kICAgICA6ICdyZXN0Jyxcblx0XHRcdH0gXTtcblx0XHRcdHJldHVybiBmYWxsYmFja1BhcmFtcztcblx0XHR9XG5cdFx0Y29uc3QgcmVmZXJlbmNpbmdGaWxlID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9IG5vZGVQYXRoLnJlc29sdmUoY29uc3RydWN0b3JFeHByLmdldFNvdXJjZUZpbGUoKS5maWxlTmFtZSk7XG5cdFx0dHJ5IHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zRnJvbUNvbnN0cnVjdG9yKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH0gZmluYWxseSB7XG5cdFx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSByZWZlcmVuY2luZ0ZpbGU7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBhIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24uXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JQYXJhbXNGcm9tQ29uc3RydWN0b3IgKGNvbnN0cnVjdG9yRXhwcjogQ29uc3RydWN0b3JIYW5kbGVyKTogQ29uc3RydWN0b3JQYXJhbUluZm9bXSB7XG5cdFx0Y29uc3QgcGFyYW1zOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdID0gW107XG5cdFxuXHRcdC8vIEhhbmRsZSBmdW5jdGlvbiBleHByZXNzaW9uIG9yIGFycm93IGZ1bmN0aW9uXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikgfHwgdHMuaXNBcnJvd0Z1bmN0aW9uKGNvbnN0cnVjdG9yRXhwcikgfHxcblx0XHRcdHRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHQvLyBMb29rIGZvciBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIChzZWNvbmQgcGFyYW0gYWZ0ZXIgYHRoaXNgKVxuXHRcdFx0Ly8gUGF0dGVybnM6IGZ1bmN0aW9uKHRoaXM6IFR5cGUsIGRhdGE6IHsgLi4uIH0pIG9yICh0aGlzOiBUeXBlLCBkYXRhOiB7IC4uLiB9KSA9PlxuXHRcdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBjb25zdHJ1Y3RvckV4cHIucGFyYW1ldGVycy5sZW5ndGg7IGkrKykge1xuXHRcdFx0XHRjb25zdCBwYXJhbSA9IGNvbnN0cnVjdG9yRXhwci5wYXJhbWV0ZXJzWyBpIF07XG5cdFx0XHRcdGlmICghcGFyYW0udHlwZSkgY29udGludWU7XG5cdFxuXHRcdFx0XHQvLyBTa2lwIGB0aGlzYCBwYXJhbWV0ZXIgKGZpcnN0IHBhcmFtKVxuXHRcdFx0XHRpZiAoXG5cdFx0XHRcdFx0aSA9PT0gMCAmJlxuXHRcdFx0XHRcdHBhcmFtLm5hbWUua2luZCA9PT0gdHMuU3ludGF4S2luZC5JZGVudGlmaWVyICYmXG5cdFx0XHRcdFx0KHBhcmFtLm5hbWUgYXMgdHMuSWRlbnRpZmllcikudGV4dCA9PT0gJ3RoaXMnXG5cdFx0XHRcdCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFxuXHRcdFx0XHQvLyBHZXQgcGFyYW1ldGVyIG5hbWUgYW5kIGV4cGFuZCBpdHMgdHlwZVxuXHRcdFx0XHRjb25zdCBwYXJhbU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgPyBwYXJhbS5uYW1lLnRleHQgOiAnYXJnJztcblx0XHRcdFx0Y29uc3QgZXhwYW5kZWRUeXBlID0gdGhpcy5yZXNvbHZlQ29uc3RydWN0b3JQYXJhbVR5cGUocGFyYW0udHlwZSkgfHwgdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cdFx0XHRcdFx0XG5cdFx0XHRcdHBhcmFtcy5wdXNoKHtcblx0XHRcdFx0XHRuYW1lICAgICA6IHBhcmFtTmFtZSxcblx0XHRcdFx0XHR0eXBlICAgICA6IGV4cGFuZGVkVHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6ICEhcGFyYW0ucXVlc3Rpb25Ub2tlbiB8fCAhIXBhcmFtLmluaXRpYWxpemVyLFxuXHRcdFx0XHRcdC8vIHJlc3QgbWFya2VyIGZvciB0aGUgZGVmaW5pdGlvbnMuanNvbiBhcmdzIGNvbnRyYWN0XG5cdFx0XHRcdFx0Li4uKHBhcmFtLmRvdERvdERvdFRva2VuID8geyBraW5kIDogJ3Jlc3QnIGFzIGNvbnN0IH0gOiB7fSlcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcblx0XHQvLyBIYW5kbGUgY2xhc3MgZXhwcmVzc2lvbiAtIGNoZWNrIGNvbnN0cnVjdG9yIG1ldGhvZFxuXHRcdGlmICh0cy5pc0NsYXNzRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHRjb25zdCBjbGFzc1BhcmFtcyA9IHRoaXMuZXh0cmFjdENsYXNzQ29uc3RydWN0b3JQYXJhbXMoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdGZvciAoY29uc3QgcGFyYW0gb2YgY2xhc3NQYXJhbXMpIHtcblx0XHRcdFx0cGFyYW1zLnB1c2gocGFyYW0pO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBwYXJhbXM7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBmcmFtZXdvcmsgaW5zdHJ1bWVudGF0aW9uIHBvaW50cy4gUHVyZWx5IHN5bnRhY3RpYzogaGVyaXRhZ2Vcblx0ICogY2xhdXNlcywgZGVjb3JhdG9yIGFwcGxpY2F0aW9uIHNpdGVzLCBwcm92aWRlci10b2tlbiBvYmplY3QgbGl0ZXJhbHNcblx0ICogYW5kIGNvbnN1bWVyLmFwcGx5KCkuZm9yUm91dGVzKCkgd2lyaW5nLiBUaGUgdm9jYWJ1bGFyeSBjb21lcyBmcm9tXG5cdCAqIHBsdWdpbnM7IGlkZW50aWZpZXIgdGV4dCBpcyBtYXRjaGVkIGFzLWlzIOKAlCBubyBpbXBvcnQgcmVzb2x1dGlvbixcblx0ICogdGhlIHR5cGUgY2hlY2tlciBzdGF5cyB1bnVzZWQuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb24gKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKG5vZGUpICYmIG5vZGUubmFtZSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uQ2xhc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0RlY29yYXRvcihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uRGVjb3JhdG9yKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0XHRpZiAodHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uUHJvdmlkZXIobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RJbnN0cnVtZW50YXRpb25NaWRkbGV3YXJlKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgYSBuYW1lZCBjbGFzcyBkZWNsYXJhdGlvbiBmb3IgaW5zdHJ1bWVudGF0aW9uIHNpdGUgcmVzb2x1dGlvblxuXHQgKiBhbmQgZGV0ZWN0IGhlcml0YWdlLWJhc2VkIGtpbmRzIChgaW1wbGVtZW50cyA8cGx1Z2luIGludGVyZmFjZT5gKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0SW5zdHJ1bWVudGF0aW9uQ2xhc3MgKG5vZGU6IHRzLkNsYXNzRGVjbGFyYXRpb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIW5vZGUubmFtZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBjbGFzc05hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5uYW1lLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdC8vIEZpcnN0IGxpbmUgb2YgdGhlIGRlY2xhcmF0aW9uLCBsaWtlIEVEUyBgY29kZWAgc25pcHBldHNcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNwbGl0KCdcXG4nKVsgMCBdLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRsZXQga2luZDogSW5zdHJ1bWVudGF0aW9uS2luZCB8IHVuZGVmaW5lZDtcblx0XHRpZiAobm9kZS5oZXJpdGFnZUNsYXVzZXMpIHtcblx0XHRcdGZvciAoY29uc3QgY2xhdXNlIG9mIG5vZGUuaGVyaXRhZ2VDbGF1c2VzKSB7XG5cdFx0XHRcdGlmIChjbGF1c2UudG9rZW4gIT09IHRzLlN5bnRheEtpbmQuSW1wbGVtZW50c0tleXdvcmQpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRmb3IgKGNvbnN0IHR5cGUgb2YgY2xhdXNlLnR5cGVzKSB7XG5cdFx0XHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIodHlwZS5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdGNvbnN0IG1hdGNoZWQgPSB0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkuaW50ZXJmYWNlc1sgdHlwZS5leHByZXNzaW9uLnRleHQgXTtcblx0XHRcdFx0XHRpZiAobWF0Y2hlZCkge1xuXHRcdFx0XHRcdFx0a2luZCA9IG1hdGNoZWQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGVjbDogSW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNsID0ge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRjb2RlLFxuXHRcdH07XG5cdFx0aWYgKGtpbmQpIHtcblx0XHRcdGRlY2wua2luZCA9IGtpbmQ7XG5cdFx0fVxuXHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNscy5zZXQoY2xhc3NOYW1lLCBkZWNsKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgZGVjb3JhdG9yIGFwcGxpY2F0aW9uIHNpdGVzOiBwbHVnaW4tbGlzdGVkIGRlY29yYXRvcnMgYXBwbGllZFxuXHQgKiB3aXRoIGNsYXNzIGFyZ3VtZW50cyBvbiBhIGNsYXNzIG9yIG9uZSBvZiBpdHMgbWV0aG9kcy4gT25lIHNpdGUgcGVyXG5cdCAqIHJlZmVyZW5jZWQgY2xhc3MgaWRlbnRpZmllci5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEluc3RydW1lbnRhdGlvbkRlY29yYXRvciAobm9kZTogdHMuRGVjb3JhdG9yLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihleHByZXNzaW9uKSB8fCAhdHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24uZXhwcmVzc2lvbikpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3Qga2luZCA9IHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS51c2VEZWNvcmF0b3JzWyBleHByZXNzaW9uLmV4cHJlc3Npb24udGV4dCBdO1xuXHRcdGlmICgha2luZCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFRoZSBkZWNvcmF0b3IncyBwYXJlbnQgaXMgdGhlIGRlY29yYXRlZCBub2RlOiBhIGNvbnRyb2xsZXIgY2xhc3MsXG5cdFx0Ly8gb25lIG9mIGl0cyBtZXRob2RzLCBvciBvbmUgb2YgaXRzIG1ldGhvZCBwYXJhbWV0ZXJzXG5cdFx0Ly8gKEBCb2R5KG12cC5mb3JUeXBlKER0bykpIG9uIGEgaGFuZGxlciBhcmd1bWVudClcblx0XHRjb25zdCBkZWNvcmF0ZWQgPSBub2RlLnBhcmVudDtcblx0XHRsZXQgc2NvcGU6IEluc3RydW1lbnRhdGlvblNjb3BlO1xuXHRcdGxldCB0YXJnZXRzOiBzdHJpbmdbXTtcblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKGRlY29yYXRlZCkgJiYgZGVjb3JhdGVkLm5hbWUpIHtcblx0XHRcdHNjb3BlID0gYGNvbnRyb2xsZXI6JHtkZWNvcmF0ZWQubmFtZS50ZXh0fWA7XG5cdFx0XHR0YXJnZXRzID0gWyBkZWNvcmF0ZWQubmFtZS50ZXh0IF07XG5cdFx0fSBlbHNlIGlmIChcblx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24oZGVjb3JhdGVkKSAmJlxuXHRcdFx0dHMuaXNJZGVudGlmaWVyKGRlY29yYXRlZC5uYW1lKSAmJlxuXHRcdFx0dHMuaXNDbGFzc0RlY2xhcmF0aW9uKGRlY29yYXRlZC5wYXJlbnQpICYmXG5cdFx0XHRkZWNvcmF0ZWQucGFyZW50Lm5hbWVcblx0XHQpIHtcblx0XHRcdGNvbnN0IGNsYXNzTmFtZSA9IGRlY29yYXRlZC5wYXJlbnQubmFtZS50ZXh0O1xuXHRcdFx0c2NvcGUgPSBgbWV0aG9kOiR7Y2xhc3NOYW1lfS4ke2RlY29yYXRlZC5uYW1lLnRleHR9YDtcblx0XHRcdHRhcmdldHMgPSBbIGNsYXNzTmFtZSBdO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNQYXJhbWV0ZXIoZGVjb3JhdGVkKSkge1xuXHRcdFx0Ly8gUGFyYW1ldGVyIGRlY29yYXRvcnMgdGFrZSB0aGUgZW5jbG9zaW5nIG1ldGhvZCdzIHNjb3BlIOKAlCB0aGVcblx0XHRcdC8vIGF0dGFjaG1lbnQgcG9pbnQgaXMgdGhlIGhhbmRsZXIsIG5vdCB0aGUgYXJndW1lbnQgbmFtZTsgdGhlXG5cdFx0XHQvLyBzYW1lIG1ldGhvZDpDbGFzcy5tZXRob2QgZm9ybSBhcyBtZXRob2QtbGV2ZWwgc2l0ZXMuIFBhcmFtcyBvZlxuXHRcdFx0Ly8gY29uc3RydWN0b3JzLCBmdW5jdGlvbnMsIGFuZCB1bm5hbWVhYmxlIGhvc3RzIHN0YXkgc2lsZW50LCB0aGVcblx0XHRcdC8vIHNhbWUgY29udmVudGlvbiBhcyBvdGhlciB1bnJlc29sdmFibGUgZGVjb3JhdG9yIHBhcmVudHNcblx0XHRcdGNvbnN0IGhvc3QgPSBkZWNvcmF0ZWQucGFyZW50O1xuXHRcdFx0aWYgKFxuXHRcdFx0XHRob3N0ICYmXG5cdFx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24oaG9zdCkgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGhvc3QubmFtZSkgJiZcblx0XHRcdFx0dHMuaXNDbGFzc0RlY2xhcmF0aW9uKGhvc3QucGFyZW50KSAmJlxuXHRcdFx0XHRob3N0LnBhcmVudC5uYW1lXG5cdFx0XHQpIHtcblx0XHRcdFx0Y29uc3QgY2xhc3NOYW1lID0gaG9zdC5wYXJlbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRzY29wZSA9IGBtZXRob2Q6JHtjbGFzc05hbWV9LiR7aG9zdC5uYW1lLnRleHR9YDtcblx0XHRcdFx0dGFyZ2V0cyA9IFsgY2xhc3NOYW1lIF07XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRyZXR1cm47XG5cdFx0XHR9XG5cdFx0fSBlbHNlIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRmb3IgKGNvbnN0IGFyZyBvZiBleHByZXNzaW9uLmFyZ3VtZW50cykge1xuXHRcdFx0Ly8gQ2xhc3MgcmVmZXJlbmNlOiBAUmVnaXN0ZXIoSW1wbCkgb3IgYW4gaW5saW5lIGluc3RhbmNlOlxuXHRcdFx0Ly8gQFJlZ2lzdGVyKG5ldyBJbXBsKHsgLi4ub3B0aW9ucyB9KSlcblx0XHRcdGxldCBjbGFzc05hbWU6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRcdC8vIHBlci1hcmcga2luZDogZmFjdG9yeS1jYWxsIGFyZ3MgY2FycnkgdGhlaXIgb3duIGNvbmZpZ3VyZWRcblx0XHRcdC8vIGtpbmQsIGV2ZXJ5dGhpbmcgZWxzZSB0YWtlcyB0aGUgZGVjb3JhdG9yJ3Ncblx0XHRcdGxldCBhcmdLaW5kID0ga2luZDtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0XHRjbGFzc05hbWUgPSBhcmcudGV4dDtcblx0XHRcdH0gZWxzZSBpZiAodHMuaXNOZXdFeHByZXNzaW9uKGFyZykgJiYgdHMuaXNJZGVudGlmaWVyKGFyZy5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjbGFzc05hbWUgPSBhcmcuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0fSBlbHNlIGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGFyZykgJiYgdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXJnLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdC8vIFBpcGUtZmFjdG9yeSBzaGFwZTogQFVzZVBpcGVzKG12cC5mb3JUeXBlKER0bykpIOKAlCB0aGVcblx0XHRcdFx0Ly8gY2FsbCdzIG1ldGhvZCBuYW1lIGlzIHBsdWdpbi1saXN0ZWQsIHRoZSB0YXJnZXQgY2xhc3Mgc2l0c1xuXHRcdFx0XHQvLyBpbiB0aGUgY29uZmlndXJlZCBhcmd1bWVudCBwb3NpdGlvbiAoZGVmYXVsdCAwKVxuXHRcdFx0XHRjb25zdCBmYWN0b3J5ID0gdGhpcy5pbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5LmRlY29yYXRvckFyZ0ZhY3Rvcmllc1sgYXJnLmV4cHJlc3Npb24ubmFtZS50ZXh0IF07XG5cdFx0XHRcdGlmIChmYWN0b3J5KSB7XG5cdFx0XHRcdFx0Y29uc3QgdGFyZ2V0QXJnID0gYXJnLmFyZ3VtZW50c1sgZmFjdG9yeS50YXJnZXRBcmcgPz8gMCBdO1xuXHRcdFx0XHRcdGlmICh0YXJnZXRBcmcgJiYgdHMuaXNJZGVudGlmaWVyKHRhcmdldEFyZykpIHtcblx0XHRcdFx0XHRcdGNsYXNzTmFtZSA9IHRhcmdldEFyZy50ZXh0O1xuXHRcdFx0XHRcdFx0YXJnS2luZCA9IGZhY3Rvcnkua2luZDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Ly8gVGhlIHBsdWdpbiBkZWNsYXJlcyB0aGF0IHRoaXMgZmFjdG9yeSBjb25zdHJ1Y3RzIGl0c1xuXHRcdFx0XHRcdC8vIHRhcmdldCBvbiB0aGUgY2FsbGVyJ3MgYmVoYWxmOiB0aGUgY2FsbCBzaXRlIGlzIGFcblx0XHRcdFx0XHQvLyBjb25zdHJ1Y3Rpb24gbGlrZSBgbmV3YCwgcmVjb3JkZWQgYXMgYW4gaW5zdGFudGlhdGlvblxuXHRcdFx0XHRcdGlmICh0YXJnZXRBcmcgJiYgZmFjdG9yeS5pbnN0YW50aWF0aW9uKSB7XG5cdFx0XHRcdFx0XHR0aGlzLnJlY29yZEZhY3RvcnlDb25zdHJ1Y3Rpb24oYXJnLCB0YXJnZXRBcmcsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKCFjbGFzc05hbWUpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHR0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzLnB1c2goe1xuXHRcdFx0XHRraW5kIDogYXJnS2luZCxcblx0XHRcdFx0Y2xhc3NOYW1lLFxuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0c2NvcGUsXG5cdFx0XHRcdHRhcmdldHMsXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQSBwbHVnaW4tbGlzdGVkIGRlY29yYXRvci1hcmcgZmFjdG9yeSB3aXRoIGBpbnN0YW50aWF0aW9uOiB0cnVlYFxuXHQgKiAoYEBCb2R5KG12cC5mb3JUeXBlKEVudGl0eSwgRHRvKSlgKSBjb25zdHJ1Y3RzIHRoZSB0eXBlIGF0IGl0c1xuXHQgKiB0YXJnZXQgYXJndW1lbnQgbGF0ZXIsIGF0IHJ1bnRpbWU6IHJlY29yZCB0aGUgZmFjdG9yeSBjYWxsIGFzIHRoYXRcblx0ICogdHlwZSdzIGBpbnN0YW50aWF0aW9uYCB1c2FnZSBhbmQgZmxvdywgdGhlIHNhbWUgYXMgY2FsbC9hcHBseS4gQVxuXHQgKiB0YXJnZXQgdGhhdCByZXNvbHZlcyB0byBubyBkZWZpbmVkIHR5cGUgcmVjb3JkcyBub3RoaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmRGYWN0b3J5Q29uc3RydWN0aW9uIChcblx0XHRjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHR0YXJnZXRBcmc6IHRzLkV4cHJlc3Npb24sXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZVxuXHQpOiB2b2lkIHtcblx0XHRjb25zdCBjb25zdHJ1Y3RlZFBhdGggPSB0aGlzLnJlc29sdmVDdG9yQXJnVHlwZVBhdGgodGFyZ2V0QXJnKTtcblx0XHRpZiAoIWNvbnN0cnVjdGVkUGF0aCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR0aGlzLnJlY29yZENvbnN0cnVjdGlvblVzYWdlKGNhbGwsIGNvbnN0cnVjdGVkUGF0aCwgc291cmNlRmlsZSwgdGFyZ2V0QXJnLmdldFRleHQoc291cmNlRmlsZSkpO1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRjYWxsLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHR0aGlzLmFkZEZsb3coY29uc3RydWN0ZWRQYXRoLCB7XG5cdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRjb2RlICAgICA6IGNhbGwuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0Y29udGV4dCAgOiAncGx1Z2luIGZhY3RvcnkgY29uc3RydWN0aW9uJyxcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgZ2xvYmFsIHJlZ2lzdHJhdGlvbnM6IG9iamVjdCBsaXRlcmFscyBzaGFwZWQgbGlrZVxuXHQgKiBgeyBwcm92aWRlOiA8cGx1Z2luLWxpc3RlZCB0b2tlbj4sIHVzZUNsYXNzOiBYIH1gLlxuXHQgKiB1c2VFeGlzdGluZy91c2VGYWN0b3J5IHdpdGhvdXQgYSB1c2VDbGFzcyBpZGVudGlmaWVyIGFyZSBub3Rcblx0ICogc3RhdGljYWxseSBvYnZpb3VzIOKAlCBza2lwcGVkIHJhdGhlciB0aGFuIGd1ZXNzZWQuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25Qcm92aWRlciAobm9kZTogdHMuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRsZXQga2luZDogSW5zdHJ1bWVudGF0aW9uS2luZCB8IHVuZGVmaW5lZDtcblx0XHRsZXQgdXNlQ2xhc3NOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cblx0XHRmb3IgKGNvbnN0IHByb3Agb2Ygbm9kZS5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdCF0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSB8fFxuXHRcdFx0XHQhdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkgfHxcblx0XHRcdFx0IXRzLmlzSWRlbnRpZmllcihwcm9wLmluaXRpYWxpemVyKVxuXHRcdFx0KSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHByb3AubmFtZS50ZXh0ID09PSAncHJvdmlkZScpIHtcblx0XHRcdFx0a2luZCA9IHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS5hcHBUb2tlbnNbIHByb3AuaW5pdGlhbGl6ZXIudGV4dCBdO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHByb3AubmFtZS50ZXh0ID09PSAndXNlQ2xhc3MnKSB7XG5cdFx0XHRcdHVzZUNsYXNzTmFtZSA9IHByb3AuaW5pdGlhbGl6ZXIudGV4dDtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRpZiAoIWtpbmQgfHwgIXVzZUNsYXNzTmFtZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uU2l0ZXMucHVzaCh7XG5cdFx0XHRraW5kLFxuXHRcdFx0Y2xhc3NOYW1lIDogdXNlQ2xhc3NOYW1lLFxuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRjb2RlLFxuXHRcdFx0c2NvcGUgICAgIDogJ2dsb2JhbCcsXG5cdFx0XHR0YXJnZXRzICAgOiBbXSxcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgbWlkZGxld2FyZSB3aXJpbmc6IGBjb25zdW1lci5hcHBseShNdzEsIE13MikuZm9yUm91dGVzKC4uLilgXG5cdCAqIGluc2lkZSBhIGNsYXNzJ3MgY29uZmlndXJlKCkgbWV0aG9kLiBUYXJnZXRzIGNvbWUgZnJvbSBmb3JSb3V0ZXNcblx0ICogYXJndW1lbnRzIHdoZW4gc3RhdGljYWxseSByZWFkYWJsZSAoc3RyaW5nIHJvdXRlcyBvciBjb250cm9sbGVyXG5cdCAqIGlkZW50aWZpZXJzKSwgZWxzZSBbXS4gU2hhcGUtYmFzZWQsIHNvIGEgcGx1Z2luIG11c3Qgb3B0IGluIHZpYVxuXHQgKiBgbWlkZGxld2FyZVdpcmluZzogdHJ1ZWAuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25NaWRkbGV3YXJlIChub2RlOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdGhpcy5pbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5Lm1pZGRsZXdhcmVXaXJpbmcpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKFxuXHRcdFx0IXRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbikgfHxcblx0XHRcdG5vZGUuZXhwcmVzc2lvbi5uYW1lLnRleHQgIT09ICdmb3JSb3V0ZXMnXG5cdFx0KSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGFwcGx5Q2FsbCA9IG5vZGUuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdGlmIChcblx0XHRcdCF0cy5pc0NhbGxFeHByZXNzaW9uKGFwcGx5Q2FsbCkgfHxcblx0XHRcdCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcHBseUNhbGwuZXhwcmVzc2lvbikgfHxcblx0XHRcdGFwcGx5Q2FsbC5leHByZXNzaW9uLm5hbWUudGV4dCAhPT0gJ2FwcGx5J1xuXHRcdCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAoIXRoaXMuaXNJbnNpZGVDb25maWd1cmVNZXRob2Qobm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB0YXJnZXRzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgYXJnIG9mIG5vZGUuYXJndW1lbnRzKSB7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykgfHwgdHMuaXNTdHJpbmdMaXRlcmFsKGFyZykpIHtcblx0XHRcdFx0dGFyZ2V0cy5wdXNoKGFyZy50ZXh0KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0YXBwbHlDYWxsLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdGZvciAoY29uc3QgYXJnIG9mIGFwcGx5Q2FsbC5hcmd1bWVudHMpIHtcblx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHR0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzLnB1c2goe1xuXHRcdFx0XHRraW5kICAgICAgOiAnbWlkZGxld2FyZScsXG5cdFx0XHRcdGNsYXNzTmFtZSA6IGFyZy50ZXh0LFxuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0c2NvcGUgICAgIDogJ21vZHVsZScsXG5cdFx0XHRcdHRhcmdldHMsXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogV2FsayB1cCB0aGUgcGFyZW50IGNoYWluIGxvb2tpbmcgZm9yIGFuIGVuY2xvc2luZyBjb25maWd1cmUoKSBtZXRob2Rcblx0ICovXG5cdHByaXZhdGUgaXNJbnNpZGVDb25maWd1cmVNZXRob2QgKG5vZGU6IHRzLk5vZGUpOiBib29sZWFuIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5vZGUucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24oY3VycmVudCkgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGN1cnJlbnQubmFtZSkgJiZcblx0XHRcdFx0Y3VycmVudC5uYW1lLnRleHQgPT09ICdjb25maWd1cmUnXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxufVxuIl19