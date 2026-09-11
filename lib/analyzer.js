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
                            // Convert full path with dots to underscores: Usages.UsageEntry -> Usages_UsageEntry
                            return queryResult.node.fullPath.replace(/\./g, '_');
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
                // Convert full path with dots to underscores: Usages.UsageEntry -> Usages_UsageEntry
                return graphResult.node.fullPath.replace(/\./g, '_');
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
            // Generic reference to a non-global, non-graph type cannot be
            // emitted bare into the generated file
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
            const collectionId = this.nextCollectionId();
            this.collectionVariables.set(node.name.text, collectionId);
            const registryInterfaceName = this.extractRegistryInterfaceName(initializer, sourceFile);
            this.collectionInfo.set(collectionId, {
                variableName: node.name.text,
                sourceFile: sourceFile.fileName,
                registryInterfaceName: registryInterfaceName
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
     * Get the registry interface name for a collection id.
     */
    getRegistryInterfaceName(collectionId) {
        if (!collectionId) {
            return undefined;
        }
        return this.collectionInfo.get(collectionId)?.registryInterfaceName;
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
        node.registryInterfaceName = this.getRegistryInterfaceName(collectionId);
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
        node.registryInterfaceName = this.getRegistryInterfaceName(collectionId);
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
        // Build full path
        const fullPath = parentNode ? `${parentNode.fullPath}.${typeName}` : typeName;
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
        node.registryInterfaceName = this.getRegistryInterfaceName(node.collectionId);
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
                        if (sourceContext.collectionId) {
                            // Collection lookup: prefix path with the collection id
                            return this.prefixCollectionPath(path, sourceContext.collectionId);
                        }
                        if (sourceContext.parentType) {
                            // Type lookup: relative first, then root fallback
                            const relativePath = `${sourceContext.parentType.fullPath}.${path}`;
                            if (this.graph.findType(relativePath)) {
                                return relativePath;
                            }
                            return path;
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
            if (sourceContext.collectionId) {
                return this.prefixCollectionPath(path, sourceContext.collectionId);
            }
            if (sourceContext.parentType) {
                const relativePath = `${sourceContext.parentType.fullPath}.${path}`;
                if (this.graph.findType(relativePath)) {
                    return relativePath;
                }
                return path;
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
                                type = bound.replace(/\./g, '_');
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
                    return newExpr.expression.text;
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
                const { line, character } = ts.getLineAndCharacterOfPosition(sourceFile, node.getStart(sourceFile));
                // Try to resolve full path
                const fullPath = this.resolveTypePath(node);
                if (fullPath) {
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
        // Try just the property name
        const propName = chain[chain.length - 1];
        for (const [path] of this.definitions) {
            if (path.endsWith(`.${propName}`) || path === propName) {
                return path;
            }
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
                    optional: !!param.questionToken || !!param.initializer
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
                    optional: !!param.questionToken || !!param.initializer
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYW5hbHl6ZXIuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvYW5hbHl6ZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFFYiwrQ0FBaUM7QUFDakMsK0NBQWlDO0FBT2pDLG1DQUVpQjtBQUNqQix1Q0FFbUI7QUErRG5COzs7R0FHRztBQUNILE1BQU0sa0JBQWtCLEdBQUcsSUFBSSxHQUFHLENBQUM7SUFDbEMsTUFBTSxFQUFFLFFBQVEsRUFBRSxPQUFPLEVBQUUsV0FBVyxFQUFFLFlBQVksRUFBRSxnQkFBZ0I7SUFDdEUsYUFBYSxFQUFFLFdBQVcsRUFBRSxVQUFVLEVBQUUsZ0JBQWdCO0lBQ3hELEtBQUssRUFBRSxLQUFLLEVBQUUsU0FBUyxFQUFFLFNBQVMsRUFBRSxTQUFTLEVBQUUsc0JBQXNCO0lBQ3JFLFNBQVMsRUFBRSxPQUFPLEVBQUUsZUFBZSxFQUFFLFFBQVEsRUFBRSxTQUFTLEVBQUUsVUFBVTtJQUNwRSxVQUFVLEVBQUUsTUFBTSxFQUFFLE1BQU0sRUFBRSxTQUFTLEVBQUUsU0FBUyxFQUFFLGFBQWE7SUFDL0QsWUFBWSxFQUFFLGNBQWMsRUFBRSxZQUFZLEVBQUUsdUJBQXVCO0lBQ25FLFVBQVUsRUFBRSxtQkFBbUIsRUFBRSxtQkFBbUI7SUFDcEQsV0FBVyxFQUFFLFdBQVcsRUFBRSxZQUFZLEVBQUUsY0FBYztJQUN0RCxRQUFRLEVBQUUsUUFBUSxFQUFFLFNBQVMsRUFBRSxRQUFRLEVBQUUsUUFBUSxFQUFFLFFBQVEsRUFBRSxVQUFVO0lBQ3ZFLFVBQVUsRUFBRSxVQUFVLEVBQUUsV0FBVyxFQUFFLGVBQWUsRUFBRSxlQUFlO0lBQ3JFLGdCQUFnQixFQUFFLGtCQUFrQixFQUFFLHVCQUF1QjtJQUM3RCxhQUFhLEVBQUUsYUFBYSxFQUFFLG1CQUFtQixFQUFFLFVBQVU7SUFDN0QsV0FBVyxFQUFFLFlBQVksRUFBRSxtQkFB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TSxHQUFHLElBQUksU0FBUyxDQUFDLFNBQVMsRUFBRSxDQUFDO1lBQ3ZDLElBQUksQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQzNCLFNBQVM7WUFDVixDQUFDO1lBQ0QsSUFBSSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQztnQkFDOUIsSUFBSSxFQUFRLFlBQVk7Z0JBQ3hCLFNBQVMsRUFBRyxHQUFHLENBQUMsSUFBSTtnQkFDcEIsUUFBUTtnQkFDUixJQUFJO2dCQUNKLEtBQUssRUFBTyxRQUFRO2dCQUNwQixPQUFPO2FBQ1AsQ0FBQyxDQUFDO1FBQ0osQ0FBQztJQUNGLENBQUM7SUFFRDs7T0FFRztJQUNLLHVCQUF1QixDQUFFLElBQWE7UUFDN0MsSUFBSSxPQUFPLEdBQXdCLElBQUksQ0FBQyxNQUFNLENBQUM7UUFDL0MsT0FBTyxPQUFPLEVBQUUsQ0FBQztZQUNoQixJQUNDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxPQUFPLENBQUM7Z0JBQy9CLEVBQUUsQ0FBQyxZQUFZLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQztnQkFDN0IsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssV0FBVyxFQUNoQyxDQUFDO2dCQUNGLE9BQU8sSUFBSSxDQUFDO1lBQ2IsQ0FBQztZQUNELE9BQU8sR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDO1FBQzFCLENBQUM7UUFDRCxPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7Q0FDRDtBQTM4TEQsOENBMjhMQyIsInNvdXJjZXNDb250ZW50IjpbIid1c2Ugc3RyaWN0JztcblxuaW1wb3J0ICogYXMgbm9kZVBhdGggZnJvbSAncGF0aCc7XG5pbXBvcnQgKiBhcyB0cyBmcm9tICd0eXBlc2NyaXB0JztcbmltcG9ydCB7XG5cdFR5cGVOb2RlLCBQcm9wZXJ0eUluZm8sIEFuYWx5emVSZXN1bHQsIEFuYWx5emVFcnJvcixcblx0RGVmaW5pdGlvbkluZm8sIFVzYWdlSW5mbywgQ29uc3RydWN0b3JQYXJhbUluZm8sXG5cdEVEU0luZm8sIEZsb3dJbmZvLCBJbnN0cnVtZW50YXRpb25LaW5kLCBJbnN0cnVtZW50YXRpb25Qb2ludCxcblx0SW5zdHJ1bWVudGF0aW9uU2NvcGUsIFJlc29sdXRpb25FcnJvclxufSBmcm9tICcuL3R5cGVzJztcbmltcG9ydCB7XG5cdFR5cGVHcmFwaEltcGwsIHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UsIEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCBcbn0gZnJvbSAnLi9ncmFwaCc7XG5pbXBvcnQge1xuXHRJbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5LCBUYWN0aWNhUGx1Z2luLCBtZXJnZVRhY3RpY2FQbHVnaW5zXG59IGZyb20gJy4vcGx1Z2lucyc7XG5cbmludGVyZmFjZSBDb2xsZWN0aW9uSW5mbyB7XG5cdHZhcmlhYmxlTmFtZTogc3RyaW5nO1xuXHRzb3VyY2VGaWxlOiBzdHJpbmc7XG5cdHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZT86IHN0cmluZztcbn1cblxuLyoqXG4gKiBMb2NhdGlvbi9jb2RlIGNhcHR1cmVkIGF0IGEgY2xhc3MgZGVjbGFyYXRpb24sIHVzZWQgdG8gcmVzb2x2ZVxuICogaW5zdHJ1bWVudGF0aW9uIHJlZ2lzdHJhdGlvbiBzaXRlcyB0byB0aGUgZGVjbGFyZWQgY2xhc3NcbiAqL1xuaW50ZXJmYWNlIEluc3RydW1lbnRhdGlvbkNsYXNzRGVjbCB7XG5cdGtpbmQ/OiBJbnN0cnVtZW50YXRpb25LaW5kO1xuXHRsb2NhdGlvbjogc3RyaW5nO1xuXHRjb2RlOiBzdHJpbmc7XG59XG5cbi8qKlxuICogUmF3IHJlZ2lzdHJhdGlvbiBzaXRlIChkZWNvcmF0b3IsIEFQUF8qIHByb3ZpZGVyLCBjb25zdW1lci5hcHBseSkuXG4gKiBMb2NhdGlvbi9jb2RlIGFyZSB0aGUgc2l0ZSdzIG93bjsgZ2V0SW5zdHJ1bWVudGF0aW9uUG9pbnRzKCkgcmV3cml0ZXNcbiAqIHRoZW0gdG8gdGhlIGNsYXNzIGRlY2xhcmF0aW9uIHdoZW4gdGhlIGNsYXNzIGlzIGRlY2xhcmVkIGluLXByb2plY3QuXG4gKi9cbmludGVyZmFjZSBJbnN0cnVtZW50YXRpb25TaXRlIHtcblx0a2luZDogSW5zdHJ1bWVudGF0aW9uS2luZDtcblx0Y2xhc3NOYW1lOiBzdHJpbmc7XG5cdGxvY2F0aW9uOiBzdHJpbmc7XG5cdGNvZGU6IHN0cmluZztcblx0c2NvcGU6IEluc3RydW1lbnRhdGlvblNjb3BlO1xuXHR0YXJnZXRzOiBzdHJpbmdbXTtcbn1cblxuLyoqXG4gKiBBIG5hbWVkIHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbiAodHlwZSBhbGlhcywgY2xhc3MsIG9yIGludGVyZmFjZSlcbiAqIHJlY29yZGVkIHBlciBmaWxlLCBzbyByZWZlcmVuY2VzIGNhbiBiZSByZXNvbHZlZCB0aHJvdWdoIHRoZSBpbXBvcnRpbmdcbiAqIGZpbGUncyBvd24gaW1wb3J0cyBpbnN0ZWFkIG9mIGEgcHJvZ3JhbS13aWRlIGxhc3Qtd2lucyBuYW1lIG1hcCAoRjEwKS5cbiAqL1xuaW50ZXJmYWNlIFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24ge1xuXHRraW5kOiAnYWxpYXMnIHwgJ2NsYXNzJyB8ICdpbnRlcmZhY2UnO1xuXHRub2RlOiB0cy5UeXBlQWxpYXNEZWNsYXJhdGlvbiB8IHRzLkNsYXNzRGVjbGFyYXRpb24gfCB0cy5JbnRlcmZhY2VEZWNsYXJhdGlvbjtcblx0LyoqIGZpbGUgdGhhdCBkZWNsYXJlcyB0aGUgdHlwZSDigJQgbmVzdGVkIHJlZmVyZW5jZXMgcmVzb2x2ZSBhZ2FpbnN0IGl0ICovXG5cdGZpbGU6IHN0cmluZztcbn1cblxuLyoqXG4gKiBPbmUgaW1wb3J0IGJpbmRpbmcgb2YgYSByZWZlcmVuY2VkIHR5cGU6IHRoZSBsb2NhbCBuYW1lIHVuZGVyIHdoaWNoIHRoZVxuICogZmlsZSBrbm93cyBpdCwgdGhlIG9yaWdpbmFsIGV4cG9ydGVkIG5hbWUgaW4gdGhlIHNvdXJjZSBtb2R1bGUsIGFuZCB0aGVcbiAqIHNwZWNpZmllciBpdCBjYW1lIGZyb20uXG4gKi9cbmludGVyZmFjZSBSZWZlcmVuY2VkVHlwZUltcG9ydCB7XG5cdG9yaWdpbmFsTmFtZTogc3RyaW5nO1xuXHRzcGVjaWZpZXI6IHN0cmluZztcblx0aXNOYW1lc3BhY2U6IGJvb2xlYW47XG59XG5cbi8qKlxuICogUmVzdWx0IG9mIHJlc29sdmluZyBvbmUgbW9kdWxlIHNwZWNpZmllciBmcm9tIG9uZSBjb250YWluaW5nIGZpbGUuXG4gKi9cbmludGVyZmFjZSBSZWZlcmVuY2VkVHlwZVJlc29sdXRpb24ge1xuXHRyZXNvbHZlZFBhdGg6IHN0cmluZztcblx0aXNFeHRlcm5hbDogYm9vbGVhbjtcbn1cblxuLyoqXG4gKiBHbG9iYWwvYnVpbHRpbiB0eXBlIG5hbWVzIHRoYXQgYXJlIHNhZmUgdG8gZW1pdCBiYXJlIGludG8gZ2VuZXJhdGVkIGZpbGVzXG4gKiDigJQgdGhleSByZXNvbHZlIGluIGFueSBUeXBlU2NyaXB0IGNvbXBpbGF0aW9uIHdpdGhvdXQgYW4gaW1wb3J0LlxuICovXG5jb25zdCBLTk9XTl9HTE9CQUxfVFlQRVMgPSBuZXcgU2V0KFtcblx0J0RhdGUnLCAnUmVnRXhwJywgJ0Vycm9yJywgJ0V2YWxFcnJvcicsICdSYW5nZUVycm9yJywgJ1JlZmVyZW5jZUVycm9yJyxcblx0J1N5bnRheEVycm9yJywgJ1R5cGVFcnJvcicsICdVUklFcnJvcicsICdBZ2dyZWdhdGVFcnJvcicsXG5cdCdNYXAnLCAnU2V0JywgJ1dlYWtNYXAnLCAnV2Vha1NldCcsICdXZWFrUmVmJywgJ0ZpbmFsaXphdGlvblJlZ2lzdHJ5Jyxcblx0J1Byb21pc2UnLCAnQXJyYXknLCAnUmVhZG9ubHlBcnJheScsICdSZWNvcmQnLCAnUGFydGlhbCcsICdSZXF1aXJlZCcsXG5cdCdSZWFkb25seScsICdQaWNrJywgJ09taXQnLCAnRXhjbHVkZScsICdFeHRyYWN0JywgJ05vbk51bGxhYmxlJyxcblx0J1JldHVyblR5cGUnLCAnSW5zdGFuY2VUeXBlJywgJ1BhcmFtZXRlcnMnLCAnQ29uc3RydWN0b3JQYXJhbWV0ZXJzJyxcblx0J1RoaXNUeXBlJywgJ1RoaXNQYXJhbWV0ZXJUeXBlJywgJ09taXRUaGlzUGFyYW1ldGVyJyxcblx0J1VwcGVyY2FzZScsICdMb3dlcmNhc2UnLCAnQ2FwaXRhbGl6ZScsICdVbmNhcGl0YWxpemUnLFxuXHQnU3RyaW5nJywgJ051bWJlcicsICdCb29sZWFuJywgJ1N5bWJvbCcsICdCaWdJbnQnLCAnT2JqZWN0JywgJ0Z1bmN0aW9uJyxcblx0J0l0ZXJhYmxlJywgJ0l0ZXJhdG9yJywgJ0dlbmVyYXRvcicsICdBc3luY0l0ZXJhYmxlJywgJ0FzeW5jSXRlcmF0b3InLFxuXHQnQXN5bmNHZW5lcmF0b3InLCAnSXRlcmFibGVJdGVyYXRvcicsICdBc3luY0l0ZXJhYmxlSXRlcmF0b3InLFxuXHQnUHJvcGVydHlLZXknLCAnQXJyYXlCdWZmZXInLCAnU2hhcmVkQXJyYXlCdWZmZXInLCAnRGF0YVZpZXcnLFxuXHQnSW50OEFycmF5JywgJ1VpbnQ4QXJyYXknLCAnVWludDhDbGFtcGVkQXJyYXknLCAnSW50MTZBcnJheScsXG5cdCdVaW50MTZBcnJheScsICdJbnQzMkFycmF5JywgJ1VpbnQzMkFycmF5JywgJ0Zsb2F0MzJBcnJheScsXG5cdCdGbG9hdDY0QXJyYXknLCAnQmlnSW50NjRBcnJheScsICdCaWdVaW50NjRBcnJheScsICdJbnRsJ1xuXSk7XG5cbi8vIEJvdW5kIGZvciBjaGFzaW5nIHJlLWV4cG9ydCBiYXJyZWxzIChleHBvcnQgeyBYIH0gZnJvbSAn4oCmJywgZXhwb3J0ICogZnJvbSAn4oCmJylcbmNvbnN0IE1BWF9SRUVYUE9SVF9DSEFTRV9ERVBUSCA9IDU7XG4vLyBCb3VuZCBmb3Igd2Fsa2luZyBjbGFzcy9pbnRlcmZhY2UgZXh0ZW5kcyBjaGFpbnMgZHVyaW5nIHJlZmVyZW5jZWQtdHlwZVxuLy8gZXhwYW5zaW9uIChpbmhlcml0ZWQgbWVtYmVycyBtZXJnZSBpbnRvIHRoZSBleHBhbmRlZCBmaWVsZHMpXG5jb25zdCBNQVhfSEVSSVRBR0VfREVQVEggPSA4O1xuXG4vKipcbiAqIEFTVCBBbmFseXplciBmb3IgZmluZGluZyBNbmVtb25pY2EgZGVmaW5lKCkgYW5kIGRlY29yYXRlKCkgY2FsbHNcbiAqXG4gKiBGcmFtZXdvcmstYmxpbmQgYnkgY29uc3RydWN0aW9uOiBpbnN0cnVtZW50YXRpb24gZGV0ZWN0aW9uIHZvY2FidWxhcnlcbiAqIChpbnRlcmZhY2UgbmFtZXMsIGRlY29yYXRvciBuYW1lcywgcHJvdmlkZXIgdG9rZW5zLCBtaWRkbGV3YXJlIHdpcmluZylcbiAqIGNvbWVzIGVudGlyZWx5IGZyb20gcGx1Z2lucyDigJQgd2l0aCBub25lIGxvYWRlZCwgemVybyBwb2ludHMgYXJlIGNvbGxlY3RlZC5cbiAqL1xuZXhwb3J0IGNsYXNzIE1uZW1vbmljYUFuYWx5emVyIHtcblx0cHJpdmF0ZSBlcnJvcnM6IEFuYWx5emVFcnJvcltdID0gW107XG5cdHByaXZhdGUgZ3JhcGggPSBuZXcgVHlwZUdyYXBoSW1wbCgpO1xuXHRwcml2YXRlIGRlZmluaXRpb25zID0gbmV3IE1hcDxzdHJpbmcsIERlZmluaXRpb25JbmZvPigpO1xuXHRwcml2YXRlIHVzYWdlcyA9IG5ldyBNYXA8c3RyaW5nLCBVc2FnZUluZm9bXT4oKTtcblx0cHJpdmF0ZSBlZHNVc2FnZXMgPSBuZXcgTWFwPHN0cmluZywgRURTSW5mb1tdPigpO1xuXHRwcml2YXRlIGZsb3dVc2FnZXMgPSBuZXcgTWFwPHN0cmluZywgRmxvd0luZm9bXT4oKTtcblx0Ly8gRW5jbG9zaW5nIG1uZW1vbmljYSBzY29wZSBmb3IgRURTIGtleWluZzogZGVmaW5lKCkvbGF6eSgpIGNhbGwgbm9kZVxuXHQvLyBvciBAZGVjb3JhdGUoKS1lZCBjbGFzcyBkZWNsYXJhdGlvbiAtPiBmdWxsUGF0aCBvZiB0aGUgdHlwZSBpdCBvd25zLlxuXHQvLyBQb3B1bGF0ZWQgb24gdGhlIGRlZmluaXRpb25zIHBhc3M7IEFTVCBub2RlcyBwZXJzaXN0IGFjcm9zcyBwYXNzZXMsXG5cdC8vIHNvIGVudHJpZXMgc3RheSB2YWxpZCBhZnRlciByZXNldFVzYWdlcygpLlxuXHRwcml2YXRlIGVkc1Njb3BlQnlOb2RlID0gbmV3IE1hcDx0cy5Ob2RlLCBzdHJpbmc+KCk7XG5cdC8vIFNhbWUtZmlsZSBmdW5jdGlvbiBiaW5kaW5ncyAoYGZpbGVOYW1lI25hbWVgIC0+IGZ1bmN0aW9uIG5vZGUpIGZvclxuXHQvLyByZXNvbHZpbmcgd3JhcChmbikgYXJndW1lbnRzIHN5bnRhY3RpY2FsbHkg4oCUIHRoZSBjaGVja2VyIHN0YXlzIHVudXNlZFxuXHRwcml2YXRlIGZ1bmN0aW9uQmluZGluZ3MgPSBuZXcgTWFwPHN0cmluZywgdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb24+KCk7XG5cdC8vIHdyYXAgY2FsbCBub2RlIC0+IGxvY2F0aW9uIG9mIHRoZSBlbmNsb3Npbmcgd3JhcCBzaXRlIChwbHVzIHRoYXRcblx0Ly8gc2l0ZSdzIHNjb3BlIGF0dHJpYnV0aW9uKSwgc28gbmVzdGVkIHdyYXAoKSBjYWxscyBpbnNpZGUgYSB3cmFwcGVkXG5cdC8vIGJvZHkgY2FycnkgdGhlIGB2aWFgIGxpbmsg4oCUIGFuZCBpbmhlcml0IHRoZSBzY29wZSB3aGVuIHRoZXkgaGF2ZVxuXHQvLyBub25lIG9mIHRoZWlyIG93blxuXHRwcml2YXRlIG5lc3RlZFdyYXBWaWEgPSBuZXcgTWFwPHRzLk5vZGUsIHsgdmlhOiBzdHJpbmc7IHNjb3BlPzogc3RyaW5nIH0+KCk7XG5cdC8vIHdyYXAgY2FsbCBub2RlIC0+IGl0cyBjb2xsZWN0ZWQgZW50cnksIHNvIGEgbGV4aWNhbGx5IG5lc3RlZCB3cmFwXG5cdC8vICh2aXNpdGVkIEJFRk9SRSB0aGUgb3V0ZXIgd3JhcCBjYWxsLCBwZXIgc291cmNlIG9yZGVyKSBnZXRzIGl0c1xuXHQvLyBgdmlhYCBiYWNrLXBhdGNoZWQgd2hlbiB0aGUgb3V0ZXIgYm9keSBpcyBhbmFseXNlZFxuXHRwcml2YXRlIHdyYXBFbnRyeUJ5Tm9kZSA9IG5ldyBNYXA8dHMuTm9kZSwgRURTSW5mbz4oKTtcblx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHM6IHZhcmlhYmxlTmFtZSAtPiBmdWxsUGF0aCBvZiB0aGUgdHlwZSBpdCBob2xkc1xuXHRwcml2YXRlIHZhcmlhYmxlVG9UeXBlTWFwID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0Ly8gVHJhY2sgbW5lbW9uaWNhIG1vZHVsZS1vYmplY3QgdmFyaWFibGVzIChlLmcuLCBpbXBvcnQgeyBtbmVtb25pY2EgfSBmcm9tICdtbmVtb25pY2EnOyBjb25zdCBtID0gbW5lbW9uaWNhKVxuXHRwcml2YXRlIG1vZHVsZU9iamVjdFZhcmlhYmxlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHQvLyBmaWxlIC0+IChsb2NhbCBuYW1lIC0+IGltcG9ydGVkIG5hbWUpIGZvciBuYW1lZCBpbXBvcnRzIGZyb21cblx0Ly8gJ21uZW1vbmljYScg4oCUIGltcG9ydC1hd2FyZW5lc3MgZm9yIHRoZSBjb25zdHJ1Y3Rpb24tZnVuY3Rpb25cblx0Ly8gcmVjb2duaXRpb24gKGNhbGwvYXBwbHkvYmluZCkgYW5kIHRoZSB1dGlscyBmb3JtcyAobWVyZ2UvZm9yayk6XG5cdC8vIHVzZXJsYW5kIGZ1bmN0aW9ucyB3aXRoIHRob3NlIG5hbWVzIG11c3QgbmV2ZXIgbWF0Y2hcblx0cHJpdmF0ZSBtbmVtb25pY2FOYW1lZEltcG9ydHMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgc3RyaW5nPj4oKTtcblx0Ly8gVHJhY2sgaW1wb3J0ZWQgYWxpYXNlcyBvZiBjcmVhdGVUeXBlc0NvbGxlY3Rpb24gKGUuZy4sIGltcG9ydCB7IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbiBhcyBjdGMgfSlcblx0cHJpdmF0ZSBjcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0Ly8gVHJhY2sgY3VzdG9tIGNvbGxlY3Rpb24gdmFyaWFibGVzOiB2YXJpYWJsZU5hbWUgLT4gY29sbGVjdGlvbklkXG5cdHByaXZhdGUgY29sbGVjdGlvblZhcmlhYmxlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdC8vIFRyYWNrIGN1c3RvbSBjb2xsZWN0aW9uIG1ldGFkYXRhIGZvciBPcHRpb24gQiByZWdpc3RyeSBlbWlzc2lvblxuXHRwcml2YXRlIGNvbGxlY3Rpb25JbmZvID0gbmV3IE1hcDxzdHJpbmcsIENvbGxlY3Rpb25JbmZvPigpO1xuXHRwcml2YXRlIGNvbGxlY3Rpb25Db3VudGVyID0gMDtcblx0Ly8gSW5zdHJ1bWVudGF0aW9uIGNvbGxlY3Rpb24gKHN5bnRhY3RpYyBvbmx5IOKAlCBubyB0eXBlIGNoZWNrZXIpOlxuXHQvLyBldmVyeSBuYW1lZCBjbGFzcyBkZWNsYXJhdGlvbiBieSBzaW1wbGUgbmFtZSwgZm9yIHJlc29sdmluZ1xuXHQvLyByZWdpc3RyYXRpb24gc2l0ZXMgdG8gZGVjbGFyYXRpb24gbG9jYXRpb25zIChiZXN0IGVmZm9ydCwgbGFzdCB3aW5zKVxuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMgPSBuZXcgTWFwPHN0cmluZywgSW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNsPigpO1xuXHQvLyBSZWdpc3RyYXRpb24gc2l0ZXM6IGRlY29yYXRvciBhcHBsaWNhdGlvbnMsIHByb3ZpZGVyLXRva2VuIG9iamVjdFxuXHQvLyBsaXRlcmFscywgY29uc3VtZXIuYXBwbHkoKSBtaWRkbGV3YXJlIHdpcmluZ1xuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvblNpdGVzOiBJbnN0cnVtZW50YXRpb25TaXRlW10gPSBbXTtcblx0Ly8gTWVyZ2VkIHBsdWdpbiB2b2NhYnVsYXJ5IGZvciBpbnN0cnVtZW50YXRpb24gZGV0ZWN0aW9uIChlbXB0eSB3aGVuXG5cdC8vIG5vIHBsdWdpbnMgd2VyZSBwYXNzZWQg4oCUIHRoZSBhbmFseXplciB0aGVuIGNvbGxlY3RzIG5vIHBvaW50cylcblx0cHJpdmF0ZSBpbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5OiBJbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5O1xuXHQvLyBSZWZlcmVuY2VkLXR5cGUgcmVzb2x1dGlvbiAoRjEwKTogcGVyLWZpbGUgZGVjbGFyYXRpb25zIGFuZCBpbXBvcnRzLlxuXHQvLyBBIHR5cGUgbmFtZSB1c2VkIGluIGZpbGUgWCByZXNvbHZlcyB0aHJvdWdoIFgncyBvd24gaW1wb3J0IHN0YXRlbWVudHNcblx0Ly8gZmlyc3QgKHJlbGF0aXZlICsgdHNjb25maWctcGF0aHMsIHZpYSB0cy5yZXNvbHZlTW9kdWxlTmFtZSksIHRoZW5cblx0Ly8gWCdzIGxvY2FsIGRlY2xhcmF0aW9ucywgdGhlbiDigJQgb25seSB3aGVuIG5vdGhpbmcgaW1wb3J0cyBvciBkZWNsYXJlc1xuXHQvLyB0aGUgbmFtZSDigJQgdGhlIHVuaXF1ZSBzYW1lLW5hbWVkIGRlY2xhcmF0aW9uIGFjcm9zcyBzY2FubmVkIGZpbGVzLlxuXHQvLyBHZW51aW5lIGFtYmlndWl0eSBvciBhbiB1bnJlc29sdmFibGUgcmVmZXJlbmNlIHlpZWxkcyBgdW5rbm93bmAsIG5ldmVyXG5cdC8vIGEgYmFyZSBlbWl0dGVkIG5hbWU6IGdlbmVyYXRlZCB0eXBlcy50cyBjYXJyaWVzIG5vIGltcG9ydHMgb2YgaXRzIG93bi5cblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZURlY2xzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24+PigpO1xuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlSW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZUltcG9ydD4+KCk7XG5cdC8vIGZpbGUgLT4gKGV4cG9ydGVkIG5hbWUgLT4gcmUtZXhwb3J0IHNwZWNpZmllcikgZm9yIGBleHBvcnQgeyBYIH0gZnJvbSAn4oCmJ2Bcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZVJlRXhwb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBmaWxlIC0+IHNwZWNpZmllcnMgb2YgYGV4cG9ydCAqIGZyb20gJ+KApidgXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmdbXT4oKTtcblx0Ly8gZmlsZSAtPiAoZXhwb3J0ZWQgbmFtZSAtPiBsb2NhbCBuYW1lKSBmb3IgYGV4cG9ydCB7IFggYXMgWSB9YFxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBmaWxlIC0+IChuYW1lc3BhY2UgbmFtZSAtPiBuYW1lc3BhY2UgZGVjbGFyYXRpb24pIOKAlCBtaWRkbGUgc2VnbWVudHNcblx0Ly8gb2YgcXVhbGlmaWVkIHJlZmVyZW5jZXMgKG1vZGVscy5Jbm5lci5DcmF0ZSkgZGVzY2VuZCB0aHJvdWdoIHRoZXNlXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHRzLk1vZHVsZURlY2xhcmF0aW9uPj4oKTtcblx0Ly8gZmlsZSAtPiAobmFtZXNwYWNlIG5hbWUgLT4gc3BlY2lmaWVyKSBmb3IgYGV4cG9ydCAqIGFzIG5zIGZyb20gJ+KApidgXG5cdC8vIGJhcnJlbHMg4oCUIGEgbmVzdGVkIG1vZHVsZSBuYW1lc3BhY2Ugb25lIHNlZ21lbnQgZGVlcFxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlU3RhcnMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgc3RyaW5nPj4oKTtcblx0Ly8gYCR7Y29udGFpbmluZ0ZpbGV9Ojoke3NwZWNpZmllcn1gIC0+IHJlc29sdXRpb24gKHVuZGVmaW5lZCA9IGZhaWxlZClcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZVJlc29sdXRpb25DYWNoZSA9IG5ldyBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZVJlc29sdXRpb24gfCB1bmRlZmluZWQ+KCk7XG5cdC8vIGZpbGUgLT4gKGNvbnN0IG5hbWUgLT4gYXJyYXkgbGl0ZXJhbCkgZm9yIGNvbnN0cyB3aXRoIGFycmF5LWxpdGVyYWxcblx0Ly8gaW5pdGlhbGl6ZXJzIChgYXMgY29uc3RgIC8gYHNhdGlzZmllc2AgdW53cmFwcGVkKSwgc28gYVxuXHQvLyBgdHlwZW9mIHN0YXR1c0xpc3RbbnVtYmVyXWAgZmllbGQgdHlwZSBleHBhbmRzIHRvIHRoZSBlbGVtZW50IGxpdGVyYWxcblx0Ly8gdW5pb24gaW5zdGVhZCBvZiBsZWFraW5nIGEgYmFyZSB1bnJlc29sdmFibGUgYHR5cGVvZmAgcXVlcnkgaW50byB0aGVcblx0Ly8gZ2VuZXJhdGVkIGZpbGUuIERlY2xhcmF0aW9ucyBwZXJzaXN0IGFjcm9zcyBwYXNzZXMg4oCUIGVudHJpZXMgc3RheVxuXHQvLyB2YWxpZCBhZnRlciByZXNldFVzYWdlcygpLCBzYW1lIGFzIHJlZmVyZW5jZWRUeXBlRGVjbHNcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24+PigpO1xuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlQ29tcGlsZXJPcHRpb25zOiB0cy5Db21waWxlck9wdGlvbnM7XG5cdC8vIEZpbGUgd2hvc2UgQVNUIGlzIGN1cnJlbnRseSBiZWluZyB2aXNpdGVkOyByZWZlcmVuY2VzIHJlc29sdmUgYWdhaW5zdCBpdFxuXHRwcml2YXRlIGN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSAnJztcblx0Ly8gQWxpYXMgbmFtZXMgY3VycmVudGx5IGJlaW5nIGV4cGFuZGVkIChjeWNsZSBndWFyZClcblx0cHJpdmF0ZSBleHBhbmRpbmdSZWZlcmVuY2VkQWxpYXNlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHQvLyBNbmVtb25pY2EtZ3JhcGggaWRlbnRpdHkgbGF3IChoYXJkIGZhaWwpOiBldmVyeSBkZWZpbmUoKS9sYXp5KCkvXG5cdC8vIEBkZWNvcmF0ZSgpIHNpdGUga2V5ZWQgYnkgaXRzIHJ1bnRpbWUgbmFtZXNwYWNlIChjb2xsZWN0aW9uIHJvb3RzOlxuXHQvLyBgPGNvbGxlY3Rpb24+Ojo8bmFtZT5gOyBzdWJ0eXBlczogYDxwYXJlbnRGdWxsUGF0aD4uPG5hbWU+YCkuIFR3b1xuXHQvLyBzaXRlcyBpbiBvbmUgbmFtZXNwYWNlIGFyZSBhIHNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZSDigJQgdGhlIHJ1bnRpbWVcblx0Ly8gdGhyb3dzIEFMUkVBRFlfREVDTEFSRUQg4oCUIGFuZCBtdXN0IGFib3J0IGdlbmVyYXRpb24uXG5cdHByaXZhdGUgZGVmaW5lU2l0ZXMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nW10+KCk7XG5cdC8vIE1uZW1vbmljYS1ncmFwaCByZWZlcmVuY2VzIHRoYXQgc3RheWVkIGFtYmlndW91cyBhZnRlciBwYXRoLWF3YXJlXG5cdC8vIHJlc29sdXRpb24gb3IgcmVzb2x2ZWQgdG8gbm90aGluZyAoaGFyZC1mYWlsIGNsYXNzIDIpXG5cdHByaXZhdGUgZ3JhcGhSZWZlcmVuY2VFcnJvcnM6IFJlc29sdXRpb25FcnJvcltdID0gW107XG5cdC8vIEd1YXJkcyBsb29rdXAoKS1wYXRoIHZhbGlkYXRpb24gc28gaXQgcnVucyBvbmNlIHBlciB1c2FnZXMgcGFzc1xuXHQvLyAoZ2V0UmVzb2x1dGlvbkVycm9ycyBtYXkgYmUgY2FsbGVkIHJlcGVhdGVkbHkpOyByZXNldFVzYWdlcyByZS1hcm1zIGl0XG5cdHByaXZhdGUgbG9va3VwUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHQvLyBMaXRlcmFsIGxvb2t1cCgpIGNhbGwgc2l0ZXMgd2l0aCB0aGVpciByZXNvbHZlZCBwYXRocy4gS2VwdCBhcGFydCBmcm9tXG5cdC8vIHRoZSB1c2FnZXMgbWFwIG9uIHB1cnBvc2U6IGFkZFVzYWdlIGRyb3BzIHBhdGhzIHRoZSBncmFwaCBkb2VzIG5vdFxuXHQvLyBrbm93ICh1c2FnZXMuanNvbiBpbmRleGVzIHJlZmVyZW5jZXMgdG8gS05PV04gdHlwZXMpLCBidXQgYW4gdW5rbm93blxuXHQvLyBsb29rdXAgcGF0aCBpcyBleGFjdGx5IHRoZSBoYXJkLWZhaWwgY2FzZSDigJQgdGhlIHJ1bnRpbWUgcmV0dXJuc1xuXHQvLyB1bmRlZmluZWQgdGhlcmUgYW5kIHRoZSBUeXBlRXJyb3IgYXJyaXZlcyBvbmUgbGluZSBsYXRlclxuXHRwcml2YXRlIGxvb2t1cFJlZmVyZW5jZXM6IHsgcGF0aDogc3RyaW5nOyBsb2NhdGlvbjogc3RyaW5nIH1bXSA9IFtdO1xuXHQvLyBHdWFyZHMgcGxhaW4tVFMgcmVmZXJlbmNlIHZhbGlkYXRpb24gc28gaXQgcnVucyBvbmNlIHBlciB1c2FnZXMgcGFzc1xuXHQvLyAoZ2V0UmVzb2x1dGlvbkVycm9ycyBtYXkgYmUgY2FsbGVkIHJlcGVhdGVkbHkpOyByZXNldFVzYWdlcyByZS1hcm1zIGl0XG5cdHByaXZhdGUgcGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHQvLyBQbGFpbi1UUyB0eXBlIHJlZmVyZW5jZSBzaXRlcyB3aG9zZSByZXNvbHV0aW9uIGZlbGwgdGhyb3VnaCBpbXBvcnRzLFxuXHQvLyBsb2NhbHMsIHRoZSBwcm9ncmFtLXdpZGUgc2NhbiwgYW5kIHRoZSBncmFwaCB0byBhIHNvZnQgYHVua25vd25gLlxuXHQvLyBWYWxpZGF0ZWQgbGF6aWx5IGZyb20gZ2V0UmVzb2x1dGlvbkVycm9ycyBhZ2FpbnN0IHRoZSBjb21wbGV0ZVxuXHQvLyBkZWNsYXJhdGlvbiBtYXA6IGEgbmFtZSBzZXZlcmFsIHByb2plY3Qtc291cmNlIGZpbGVzIGRlY2xhcmUg4oCUIHdpdGhcblx0Ly8gbm8gaW1wb3J0IGluIHRoZSByZWZlcmVuY2luZyBmaWxlIHRvIGFuY2hvciBpdCDigJQgaXMgdGhlIHBsYWluLVRTXG5cdC8vIGFtYmlndWl0eSBoYXJkLWZhaWwgY2xhc3MgKG9uZSB0aWVyIGJlbG93IHRoZSBncmFwaCBpZGVudGl0eSBsYXcpO1xuXHQvLyBhYnNlbmNlIChnaG9zdCBuYW1lcykgc3RheXMgc29mdC4gUmVjb3JkaW5nIGhhcHBlbnMgb24gZXZlcnkgcGFzcyxcblx0Ly8gdGhlIHZlcmRpY3Qgb25seSBoZXJlIOKAlCBwYXNzIDEgc2VlcyBhbiBpbmNvbXBsZXRlIGRlY2xhcmF0aW9uIG1hcCxcblx0Ly8gc28gb25seSB0aGUgdXNhZ2VzIHBhc3MgaXMgYXV0aG9yaXRhdGl2ZSAobWlycm9ycyBsb29rdXAgcmVmZXJlbmNlcylcblx0cHJpdmF0ZSBwbGFpblR5cGVSZWZlcmVuY2VzOiB7IG5hbWU6IHN0cmluZzsgbG9jYXRpb246IHN0cmluZzsgZmlsZTogc3RyaW5nIH1bXSA9IFtdO1xuXHQvLyBQZXItZmlsZSB0b3AtbGV2ZWwgdmFyaWFibGUgLT4gbW5lbW9uaWNhIGZ1bGxQYXRoIGJpbmRpbmdzICh2YWx1ZVxuXHQvLyBzY29wZSk6IGBjb25zdCBBZGRyZXNzID0gVXNlci5kZWZpbmUoJ0FkZHJlc3MnLCDigKYpYCBtYWtlcyBgQWRkcmVzc2Bcblx0Ly8gZGVub3RlIFVzZXIuQWRkcmVzcyB3aGVyZXZlciB0aGF0IGZpbGUncyByZWZlcmVuY2VzIGFyZSByZXNvbHZlZFxuXHRwcml2YXRlIGZpbGVHcmFwaEJpbmRpbmdzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHN0cmluZz4+KCk7XG5cdC8vIFRoZSBncmFwaCB0eXBlIHdob3NlIGNvbnN0cnVjdG9yIGlzIGN1cnJlbnRseSBiZWluZyBleHRyYWN0ZWQ7XG5cdC8vIGFuY2hvcnMgcmVsYXRpdmUtZmlyc3QgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb25cblx0cHJpdmF0ZSBjdXJyZW50R3JhcGhBbmNob3I6IFR5cGVOb2RlIHwgdW5kZWZpbmVkO1xuXHQvLyBkZWZpbmUoKS9sYXp5KCkgY2FsbHMgYWxyZWFkeSBleHRyYWN0ZWQgdGhpcyBwYXNzLiBUaGUgQ0xJIHJlLWFuYWx5emVzXG5cdC8vIGV2ZXJ5IGZpbGUgYWZ0ZXIgcmVzZXRVc2FnZXMoKTsgY2xlYXJpbmcgdGhlIHNldCBsZXRzIHRoZSBzZWNvbmQgcGFzc1xuXHQvLyByZS1leHRyYWN0IGV2ZXJ5IGNvbnN0cnVjdG9yIGFnYWluc3QgdGhlIENPTVBMRVRFIGdyYXBoIOKAlCBwYXNzIDEgc2Vlc1xuXHQvLyBmb3J3YXJkIHJlZmVyZW5jZXMgYXMgYG5vbmVgIChzb2Z0IHVua25vd24pIGJlY2F1c2UgbGF0ZXIgZmlsZXMgaGF2ZVxuXHQvLyBub3QgYmVlbiB2aXNpdGVkIHlldCwgc28gb25seSBwYXNzLTIgcmVzb2x1dGlvbiBpcyBhdXRob3JpdGF0aXZlIGZvclxuXHQvLyB0aGUgaGFyZC1mYWlsIGlkZW50aXR5IGxhdy4gVGhlIHN0YW1wIGxpdmVzIGhlcmUgcmF0aGVyIHRoYW4gb24gdGhlXG5cdC8vIEFTVCBub2RlIHNvIGl0IGNhbiBhY3R1YWxseSBiZSBjbGVhcmVkLiAoQ2hhaW5lZCBjYWxscyB2aXNpdCB0aGUgc2FtZVxuXHQvLyBub2RlIHR3aWNlIHdpdGhpbiBvbmUgcGFzczsgdGhlIGluLXBhc3MgZGVkdXAgYmVsb3cgc3RheXMuKVxuXHRwcml2YXRlIHByb2Nlc3NlZENhbGxzID0gbmV3IFNldDx0cy5DYWxsRXhwcmVzc2lvbj4oKTtcblxuXHRjb25zdHJ1Y3RvciAocHJvZ3JhbT86IHRzLlByb2dyYW0sIHBsdWdpbnM6IFRhY3RpY2FQbHVnaW5bXSA9IFtdKSB7XG5cdFx0Ly8gQ29tcGlsZXIgb3B0aW9ucyBkcml2ZSB0cy5yZXNvbHZlTW9kdWxlTmFtZSBmb3IgaW1wb3J0LWF3YXJlXG5cdFx0Ly8gcmVmZXJlbmNlZC10eXBlIHJlc29sdXRpb24gKHRzY29uZmlnIGBwYXRoc2AsIGV4dGVuc2lvbmxlc3Ncblx0XHQvLyBpbXBvcnRzKTsgdGhlIHR5cGUgY2hlY2tlciBpdHNlbGYgc3RheXMgdW51c2VkLlxuXHRcdHRoaXMucmVmZXJlbmNlZFR5cGVDb21waWxlck9wdGlvbnMgPSBwcm9ncmFtPy5nZXRDb21waWxlck9wdGlvbnMoKSA/PyB7fTtcblx0XHR0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkgPSBtZXJnZVRhY3RpY2FQbHVnaW5zKHBsdWdpbnMpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc2V0IHVzYWdlLXJlbGF0ZWQgc3RhdGUgZm9yIGEgZnJlc2ggcGFzcy5cblx0ICogQ2FsbCBiZWZvcmUgdGhlIHVzYWdlLWNvbGxlY3Rpb24gcGFzcyB0byBhdm9pZCBkdXBsaWNhdGVzIGZyb20gZGVmaW5pdGlvbiBwYXNzLlxuXHQgKi9cblx0cmVzZXRVc2FnZXMgKCk6IHZvaWQge1xuXHRcdHRoaXMudXNhZ2VzLmNsZWFyKCk7XG5cdFx0dGhpcy5lZHNVc2FnZXMuY2xlYXIoKTtcblx0XHR0aGlzLmZsb3dVc2FnZXMuY2xlYXIoKTtcblx0XHR0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmNsZWFyKCk7XG5cdFx0Ly8gRURTIGVudHJ5IHJlZmVyZW5jZXMgZ28gc3RhbGUgd2l0aCBlZHNVc2FnZXM7IHZpYSBsaW5rcyBhcmVcblx0XHQvLyByZS1kZXJpdmVkIG9uIHRoZSBuZXh0IHBhc3Ncblx0XHR0aGlzLndyYXBFbnRyeUJ5Tm9kZS5jbGVhcigpO1xuXHRcdHRoaXMubmVzdGVkV3JhcFZpYS5jbGVhcigpO1xuXHRcdC8vIE5vdGU6IG1vZHVsZU9iamVjdFZhcmlhYmxlcyBhbmQgY29sbGVjdGlvblZhcmlhYmxlcyBpbnRlbnRpb25hbGx5IHBlcnNpc3Rcblx0XHQvLyBhY3Jvc3MgZGVmaW5pdGlvbiBhbmQgdXNhZ2UgcGFzc2VzLlxuXHRcdC8vIFJlLWV4dHJhY3Rpb24gaW4gdGhlIHVzYWdlcyBwYXNzIGlzIHdoYXQgbWFrZXMgZ3JhcGggcmVmZXJlbmNlXG5cdFx0Ly8gcmVzb2x1dGlvbiBhdXRob3JpdGF0aXZlOiBwYXNzIDEgcmVzb2x2ZXMgYWdhaW5zdCBhbiBpbmNvbXBsZXRlXG5cdFx0Ly8gZ3JhcGggKGZvcndhcmQgcmVmZXJlbmNlcyByZWFkIGFzIGBub25lYCksIHBhc3MgMiBhZ2FpbnN0IGFsbCBvZiBpdC5cblx0XHR0aGlzLnByb2Nlc3NlZENhbGxzLmNsZWFyKCk7XG5cdFx0Ly8gbG9va3VwKCktcGF0aCB2YWxpZGF0aW9uIHJ1bnMgYWdhaW5zdCB0aGUgcmVjb3JkZWQgc2l0ZXM7IGEgZnJlc2hcblx0XHQvLyBwYXNzIG11c3QgcmUtcmVjb3JkIGFuZCByZS12YWxpZGF0ZSAocGFzcy0xIHJlc3VsdHMgd291bGQgYmVcblx0XHQvLyBwcmVtYXR1cmUg4oCUIHRoZSBncmFwaCBpcyBzdGlsbCBpbmNvbXBsZXRlKVxuXHRcdHRoaXMubG9va3VwUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHRcdHRoaXMubG9va3VwUmVmZXJlbmNlcyA9IFtdO1xuXHRcdHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHRcdHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlcyA9IFtdO1xuXHR9XG5cblx0LyoqXG5cdCAqIEFuYWx5emUgYSBzb3VyY2UgZmlsZSBmb3IgTW5lbW9uaWNhIHR5cGUgZGVmaW5pdGlvbnNcblx0ICovXG5cdGFuYWx5emVGaWxlIChzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogQW5hbHl6ZVJlc3VsdCB7XG5cdFx0dGhpcy5lcnJvcnMgPSBbXTtcblx0XHQvLyBSZWZlcmVuY2VkLXR5cGUgbmFtZXMgaW4gdGhpcyBmaWxlIHJlc29sdmUgYWdhaW5zdCBpdHMgb3duIGltcG9ydHNcblx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSBub2RlUGF0aC5yZXNvbHZlKHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXHRcdC8vIEVuc3VyZSBwYXJlbnQgbm9kZXMgYXJlIHNldCBmb3IgQVNUIHRyYXZlcnNhbFxuXHRcdHRoaXMuc2V0UGFyZW50Tm9kZXNJblNvdXJjZUZpbGUoc291cmNlRmlsZSk7XG5cdFx0dGhpcy52aXNpdE5vZGUoc291cmNlRmlsZSwgc291cmNlRmlsZSk7XG5cblx0XHRyZXR1cm4ge1xuXHRcdFx0dHlwZXMgIDogdGhpcy5ncmFwaC5nZXRBbGxUeXBlcygpLFxuXHRcdFx0ZXJyb3JzIDogdGhpcy5lcnJvcnMsXG5cdFx0fTtcblx0fVxuXG5cdC8qKlxuXHQgKiBBbmFseXplIHNvdXJjZSBjb2RlIHN0cmluZ1xuXHQgKi9cblx0YW5hbHl6ZVNvdXJjZSAoc291cmNlQ29kZTogc3RyaW5nLCBmaWxlTmFtZSA9ICd0ZW1wLnRzJyk6IEFuYWx5emVSZXN1bHQge1xuXHRcdGNvbnN0IHNvdXJjZUZpbGUgPSB0cy5jcmVhdGVTb3VyY2VGaWxlKFxuXHRcdFx0ZmlsZU5hbWUsXG5cdFx0XHRzb3VyY2VDb2RlLFxuXHRcdFx0dHMuU2NyaXB0VGFyZ2V0LkxhdGVzdCxcblx0XHRcdHRydWVcblx0XHQpO1xuXHRcdHJldHVybiB0aGlzLmFuYWx5emVGaWxlKHNvdXJjZUZpbGUpO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCB0aGUgdHlwZSBncmFwaFxuXHQgKi9cblx0Z2V0R3JhcGggKCk6IFR5cGVHcmFwaEltcGwge1xuXHRcdHJldHVybiB0aGlzLmdyYXBoO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBjb2xsZWN0ZWQgZGVmaW5pdGlvbnNcblx0ICovXG5cdGdldERlZmluaXRpb25zICgpOiBNYXA8c3RyaW5nLCBEZWZpbml0aW9uSW5mbz4ge1xuXHRcdHJldHVybiB0aGlzLmRlZmluaXRpb25zO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBjb2xsZWN0ZWQgdXNhZ2VzXG5cdCAqL1xuXHRnZXRVc2FnZXMgKCk6IE1hcDxzdHJpbmcsIFVzYWdlSW5mb1tdPiB7XG5cdFx0cmV0dXJuIHRoaXMudXNhZ2VzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBjb2xsZWN0ZWQgRURTIHVzYWdlc1xuXHQgKi9cblx0Z2V0RURTVXNhZ2VzICgpOiBNYXA8c3RyaW5nLCBFRFNJbmZvW10+IHtcblx0XHRyZXR1cm4gdGhpcy5lZHNVc2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBmbG93IHVzYWdlc1xuXHQgKi9cblx0Z2V0Rmxvd1VzYWdlcyAoKTogTWFwPHN0cmluZywgRmxvd0luZm9bXT4ge1xuXHRcdHJldHVybiB0aGlzLmZsb3dVc2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBpbnN0cnVtZW50YXRpb24gcG9pbnRzLlxuXHQgKiBSZWdpc3RyYXRpb24gc2l0ZXMgcmVmZXJlbmNpbmcgYSBjbGFzcyBkZWNsYXJlZCBpbiB0aGUgc2FtZSBwcm9qZWN0XG5cdCAqIHJlc29sdmUgdG8gdGhlIGNsYXNzIGRlY2xhcmF0aW9uJ3MgbG9jYXRpb24vY29kZTsgZXh0ZXJuYWwgY2xhc3Nlc1xuXHQgKiAoZS5nLiwgYSBmcmFtZXdvcmstYnVpbHRpbiBpbXBsZW1lbnRhdGlvbiBmcm9tIG5vZGVfbW9kdWxlcykga2VlcFxuXHQgKiB0aGUgcmVnaXN0cmF0aW9uIHNpdGUuXG5cdCAqIERlZHVwZWQgYnkga2luZCtjbGFzc05hbWUrbG9jYXRpb24rc2NvcGUgd2l0aCB0YXJnZXRzIG1lcmdlZCDigJQgYVxuXHQgKiBjbGFzcyBkZXRlY3RlZCBieSBoZXJpdGFnZSBBTkQgYnkgYSBkZWNvcmF0b3Igc2l0ZSB5aWVsZHMgc2VwYXJhdGVcblx0ICogZW50cmllcyB3aXRoIGRpc3RpbmN0IHNjb3BlcyAoc2VlIEluc3RydW1lbnRhdGlvblBvaW50IGluIHR5cGVzLnRzKS5cblx0ICovXG5cdGdldEluc3RydW1lbnRhdGlvblBvaW50cyAoKTogSW5zdHJ1bWVudGF0aW9uUG9pbnRbXSB7XG5cdFx0Y29uc3QgcG9pbnRzID0gbmV3IE1hcDxzdHJpbmcsIEluc3RydW1lbnRhdGlvblBvaW50PigpO1xuXG5cdFx0Y29uc3QgYWRkUG9pbnQgPSAocG9pbnQ6IEluc3RydW1lbnRhdGlvblBvaW50KTogdm9pZCA9PiB7XG5cdFx0XHRjb25zdCBrZXkgPSBgJHtwb2ludC5raW5kfXwke3BvaW50LmNsYXNzTmFtZX18JHtwb2ludC5sb2NhdGlvbn18JHtwb2ludC5zY29wZX1gO1xuXHRcdFx0Y29uc3QgZXhpc3RpbmcgPSBwb2ludHMuZ2V0KGtleSk7XG5cdFx0XHRpZiAoZXhpc3RpbmcpIHtcblx0XHRcdFx0Y29uc3QgbWVyZ2VkID0gbmV3IFNldChbIC4uLmV4aXN0aW5nLnRhcmdldHMsIC4uLnBvaW50LnRhcmdldHMgXSk7XG5cdFx0XHRcdGV4aXN0aW5nLnRhcmdldHMgPSBBcnJheS5mcm9tKG1lcmdlZCk7XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdHBvaW50cy5zZXQoa2V5LCBwb2ludCk7XG5cdFx0fTtcblxuXHRcdGZvciAoY29uc3Qgc2l0ZSBvZiB0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzKSB7XG5cdFx0XHRjb25zdCBkZWNsID0gdGhpcy5pbnN0cnVtZW50YXRpb25DbGFzc0RlY2xzLmdldChzaXRlLmNsYXNzTmFtZSk7XG5cdFx0XHRjb25zdCBwb2ludDogSW5zdHJ1bWVudGF0aW9uUG9pbnQgPSB7XG5cdFx0XHRcdGtpbmQgICAgICA6IHNpdGUua2luZCxcblx0XHRcdFx0Y2xhc3NOYW1lIDogc2l0ZS5jbGFzc05hbWUsXG5cdFx0XHRcdGxvY2F0aW9uICA6IGRlY2wgPyBkZWNsLmxvY2F0aW9uIDogc2l0ZS5sb2NhdGlvbixcblx0XHRcdFx0Y29kZSAgICAgIDogZGVjbCA/IGRlY2wuY29kZSA6IHNpdGUuY29kZSxcblx0XHRcdFx0c2NvcGUgICAgIDogc2l0ZS5zY29wZSxcblx0XHRcdFx0dGFyZ2V0cyAgIDogc2l0ZS50YXJnZXRzLFxuXHRcdFx0fTtcblx0XHRcdGFkZFBvaW50KHBvaW50KTtcblx0XHR9XG5cblx0XHQvLyBIZXJpdGFnZS1kZWNsYXJlZCBjbGFzc2VzIGFsd2F5cyBlbWl0IGEgZGVjbGFyYXRpb24gcG9pbnQgd2l0aFxuXHRcdC8vIHNjb3BlICdtb2R1bGUnIChhdHRhY2htZW50IHN0YXRpY2FsbHkgdW5rbm93bik7IHJlZ2lzdHJhdGlvblxuXHRcdC8vIHNpdGVzIGFib3ZlIGNhcnJ5IHRoZSBuYXJyb3dlciBzY29wZXMgYXMgc2VwYXJhdGUgZW50cmllc1xuXHRcdGZvciAoY29uc3QgWyBjbGFzc05hbWUsIGRlY2wgXSBvZiB0aGlzLmluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMpIHtcblx0XHRcdGlmICghZGVjbC5raW5kKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgcG9pbnQ6IEluc3RydW1lbnRhdGlvblBvaW50ID0ge1xuXHRcdFx0XHRraW5kICAgICAgOiBkZWNsLmtpbmQsXG5cdFx0XHRcdGNsYXNzTmFtZSA6IGNsYXNzTmFtZSxcblx0XHRcdFx0bG9jYXRpb24gIDogZGVjbC5sb2NhdGlvbixcblx0XHRcdFx0Y29kZSAgICAgIDogZGVjbC5jb2RlLFxuXHRcdFx0XHRzY29wZSAgICAgOiAnbW9kdWxlJyxcblx0XHRcdFx0dGFyZ2V0cyAgIDogW10sXG5cdFx0XHR9O1xuXHRcdFx0YWRkUG9pbnQocG9pbnQpO1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlc3VsdCA9IEFycmF5LmZyb20ocG9pbnRzLnZhbHVlcygpKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhIHRvcG9sb2dpY2EgdHlwZSB0byB0aGUgYW5hbHl6ZXIgZm9yIHVzYWdlIHRyYWNraW5nLlxuXHQgKiBUaGlzIGFsbG93cyB0aGUgYW5hbHl6ZXIgdG8gcmVjb2duaXplIHRvcG9sb2dpY2EgdHlwZXMgd2hlbiBjb2xsZWN0aW5nIHVzYWdlcy5cblx0ICovXG5cdGFkZFRvcG9sb2dpY2FUeXBlIChmdWxsUGF0aDogc3RyaW5nLCBub2RlOiBpbXBvcnQoJy4vdHlwZXMnKS5UeXBlTm9kZSk6IHZvaWQge1xuXHRcdC8vIFNraXAgaWYgYWxyZWFkeSBleGlzdHNcblx0XHRpZiAodGhpcy5ncmFwaC5hbGxUeXBlcy5oYXMoZnVsbFBhdGgpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoIHNvIGl0IGNhbiBiZSBmb3VuZCBkdXJpbmcgdXNhZ2UgY29sbGVjdGlvblxuXHRcdGlmIChub2RlLnBhcmVudCkge1xuXHRcdFx0Ly8gQWRkIGFzIGNoaWxkIG9mIHBhcmVudFxuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChub2RlLnBhcmVudCwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdC8vIEFkZCBhcyByb290XG5cdFx0XHR0aGlzLmdyYXBoLmFkZFJvb3Qobm9kZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQWxzbyBhZGQgdG8gZGVmaW5pdGlvbnMgc28gaXQncyByZWNvZ25pemVkIGFzIGEga25vd24gdHlwZVxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiBub2RlLm5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke25vZGUuc291cmNlRmlsZX06JHtub2RlLmxpbmV9OiR7bm9kZS5jb2x1bW59YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlZmluZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IG5vZGUucGFyZW50ID8gbm9kZS5wYXJlbnQuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBmYWxzZVxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQoZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFNldCBwYXJlbnQgbm9kZXMgaW4gYSBzb3VyY2UgZmlsZSB0byBlbmFibGUgQVNUIHRyYXZlcnNhbCB1cFxuXHQgKi9cblx0cHJpdmF0ZSBzZXRQYXJlbnROb2Rlc0luU291cmNlRmlsZSAoc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHNldFBhcmVudCA9IChub2RlOiB0cy5Ob2RlLCBwYXJlbnQ/OiB0cy5Ob2RlKSA9PiB7XG5cdFx0XHQvLyBUeXBlU2NyaXB0IGRvZXNuJ3QgZXhwb3NlIHBhcmVudCBhcyB3cml0YWJsZSwgYnV0IHdlIG5lZWQgaXRcblx0XHRcdC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBAdHlwZXNjcmlwdC1lc2xpbnQvbm8tZXhwbGljaXQtYW55XG5cdFx0XHQobm9kZSBhcyBhbnkpLnBhcmVudCA9IHBhcmVudDtcblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCBjaGlsZCA9PiBzZXRQYXJlbnQoY2hpbGQsIG5vZGUpKTtcblx0XHR9O1xuXHRcdHNldFBhcmVudChzb3VyY2VGaWxlKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBWaXNpdCBhIG5vZGUgaW4gdGhlIEFTVFxuXHQgKi9cblx0cHJpdmF0ZSB2aXNpdE5vZGUgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsIGN1cnJlbnRDbGFzcz86IHRzLkNsYXNzRGVjbGFyYXRpb24pOiB2b2lkIHtcblx0XHQvLyBUcmFjayBtbmVtb25pY2EgbW9kdWxlLW9iamVjdCBhbGlhc2VzIGFuZCBjdXN0b20gY29sbGVjdGlvbiB2YXJpYWJsZXNcblx0XHQvLyBiZWZvcmUgcHJvY2Vzc2luZyBkZWZpbmUoKS9sb29rdXAoKSBjYWxscyBzbyBzb3VyY2UgcmVzb2x1dGlvbiB3b3Jrcy5cblx0XHR0aGlzLnRyYWNrSW1wb3J0cyhub2RlKTtcblx0XHR0aGlzLnRyYWNrTW9kdWxlT2JqZWN0QWxpYXNlcyhub2RlKTtcblx0XHR0aGlzLnRyYWNrQ29sbGVjdGlvbkFsaWFzZXMobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgZGVmaW5lKCkgY2FsbHNcblx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0RlZmluZUNhbGwobm9kZSBhcyB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIGxhenkoKSBjYWxsc1xuXHRcdGlmICh0aGlzLmlzTGF6eUNhbGwobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0xhenlDYWxsKG5vZGUgYXMgdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGUpO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHRcdGlmICh0aGlzLmlzRGVjb3JhdGVEZWNvcmF0b3Iobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0RlY29yYXRlRGVjb3JhdG9yKG5vZGUgYXMgdHMuRGVjb3JhdG9yLCBzb3VyY2VGaWxlLCBjdXJyZW50Q2xhc3MpO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciB0eXBlIHVzYWdlcyAobmV3IFR5cGUoKSwgdHlwZSBhbm5vdGF0aW9ucywgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RVc2FnZShub2RlLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIENoZWNrIGZvciBFRFMgcGF0dGVybnMgKHdyYXAsIGN1cnJlbnQsIGdldEZsb3csIGV0Yy4pXG5cdFx0dGhpcy5jb2xsZWN0RURTKG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIG5hdGl2ZSBmbG93IHBhdHRlcm5zIChwcm9wZXJ0eSBhY2Nlc3MsIG1ldGhvZCBjYWxscywgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RGbG93KG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIGZyYW1ld29yayBpbnN0cnVtZW50YXRpb24gcG9pbnRzICh2b2NhYnVsYXJ5IHN1cHBsaWVkXG5cdFx0Ly8gYnkgcGx1Z2luczsgc3ludGFjdGljIG9ubHkg4oCUIG5vIHR5cGUgY2hlY2tlcilcblx0XHR0aGlzLmNvbGxlY3RJbnN0cnVtZW50YXRpb24obm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDb2xsZWN0IHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbnMgKGFsaWFzZXMsIGNsYXNzZXMsIGludGVyZmFjZXMpXG5cdFx0Ly8gcGVyIGZpbGUsIGFuZCB0aGUgZmlsZSdzIGltcG9ydCB3aXJpbmcsIGZvciBpbXBvcnQtYXdhcmUgcmVzb2x1dGlvblxuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKG5vZGUpO1xuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZUltcG9ydChub2RlKTtcblx0XHR0aGlzLnRyYWNrUmVmZXJlbmNlZFR5cGVSZUV4cG9ydChub2RlKTtcblx0XHR0aGlzLnRyYWNrUmVmZXJlbmNlZFR5cGVDb25zdEFycmF5KG5vZGUpO1xuXG5cdFx0Ly8gVHJhY2sgc2FtZS1maWxlIGZ1bmN0aW9uIGJpbmRpbmdzIHNvIEVEUyBjYW4gcmVzb2x2ZSB3cmFwKGZuKVxuXHRcdC8vIGFyZ3VtZW50cyB3aXRob3V0IHRoZSB0eXBlIGNoZWNrZXIgKGJlc3QgZWZmb3J0LCBsYXN0IHdpbnMpXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9IyR7bm9kZS5uYW1lLnRleHR9YDtcblx0XHRcdHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5zZXQoa2V5LCBub2RlKTtcblx0XHR9XG5cdFx0aWYgKFxuXHRcdFx0dHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSAmJlxuXHRcdFx0bm9kZS5pbml0aWFsaXplciAmJlxuXHRcdFx0KHRzLmlzQXJyb3dGdW5jdGlvbihub2RlLmluaXRpYWxpemVyKSB8fCB0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihub2RlLmluaXRpYWxpemVyKSlcblx0XHQpIHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9IyR7bm9kZS5uYW1lLnRleHR9YDtcblx0XHRcdHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5zZXQoa2V5LCBub2RlLmluaXRpYWxpemVyKTtcblx0XHR9XG5cblx0XHQvLyBUcmFjayBjbGFzcyBkZWNsYXJhdGlvbnMgZm9yIGRlY29yYXRvciBwYXJlbnQgbG9va3VwXG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0Ly8gVmlzaXQgY2hpbGRyZW4gd2l0aCB0aGlzIGNsYXNzIGFzIHRoZSBjdXJyZW50IGNvbnRleHRcblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCBjaGlsZCA9PiB0aGlzLnZpc2l0Tm9kZShjaGlsZCwgc291cmNlRmlsZSwgbm9kZSkpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHQvLyBSZWN1cnNpdmVseSB2aXNpdCBjaGlsZHJlblxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHRoaXMudmlzaXROb2RlKGNoaWxkLCBzb3VyY2VGaWxlLCBjdXJyZW50Q2xhc3MpKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgaW1wb3J0cyBmcm9tICdtbmVtb25pY2EnIHNvIGFsaWFzZXMgb2YgdGhlIG1vZHVsZSBvYmplY3QgYW5kXG5cdCAqIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbiBhcmUgcmVjb2duaXplZCB3aXRob3V0IHJlbHlpbmcgb24gdGhlIHR5cGUgY2hlY2tlci5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tJbXBvcnRzIChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc0ltcG9ydERlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBtb2R1bGVTcGVjaWZpZXIgfSA9IG5vZGU7XG5cdFx0aWYgKCF0cy5pc1N0cmluZ0xpdGVyYWwobW9kdWxlU3BlY2lmaWVyKSB8fCBtb2R1bGVTcGVjaWZpZXIudGV4dCAhPT0gJ21uZW1vbmljYScpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCBjbGF1c2UgPSBub2RlLmltcG9ydENsYXVzZTtcblx0XHRpZiAoIWNsYXVzZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGltcG9ydCB7IG1uZW1vbmljYSwgY3JlYXRlVHlwZXNDb2xsZWN0aW9uIH0gZnJvbSAnbW5lbW9uaWNhJ1xuXHRcdGlmIChjbGF1c2UubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVkSW1wb3J0cyhjbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBjbGF1c2UubmFtZWRCaW5kaW5ncy5lbGVtZW50cykge1xuXHRcdFx0XHRjb25zdCBsb2NhbE5hbWUgPSBlbGVtZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgaW1wb3J0ZWROYW1lID0gZWxlbWVudC5wcm9wZXJ0eU5hbWVcblx0XHRcdFx0XHQ/IGVsZW1lbnQucHJvcGVydHlOYW1lLnRleHRcblx0XHRcdFx0XHQ6IGxvY2FsTmFtZTtcblx0XHRcdFx0aWYgKGltcG9ydGVkTmFtZSA9PT0gJ21uZW1vbmljYScpIHtcblx0XHRcdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQobG9jYWxOYW1lKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoaW1wb3J0ZWROYW1lID09PSAnY3JlYXRlVHlwZXNDb2xsZWN0aW9uJykge1xuXHRcdFx0XHRcdHRoaXMuY3JlYXRlVHlwZXNDb2xsZWN0aW9uVmFyaWFibGVzLmFkZChsb2NhbE5hbWUpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGxldCBmaWxlSW1wb3J0cyA9IHRoaXMubW5lbW9uaWNhTmFtZWRJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHRpZiAoIWZpbGVJbXBvcnRzKSB7XG5cdFx0XHRcdFx0ZmlsZUltcG9ydHMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0XHRcdHRoaXMubW5lbW9uaWNhTmFtZWRJbXBvcnRzLnNldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUsIGZpbGVJbXBvcnRzKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRmaWxlSW1wb3J0cy5zZXQobG9jYWxOYW1lLCBpbXBvcnRlZE5hbWUpO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIGltcG9ydCAqIGFzIG1uZW1vbmljYSBmcm9tICdtbmVtb25pY2EnXG5cdFx0aWYgKGNsYXVzZS5uYW1lZEJpbmRpbmdzICYmIHRzLmlzTmFtZXNwYWNlSW1wb3J0KGNsYXVzZS5uYW1lZEJpbmRpbmdzKSkge1xuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuYWRkKGNsYXVzZS5uYW1lZEJpbmRpbmdzLm5hbWUudGV4dCk7XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0IG1uZW1vbmljYSBmcm9tICdtbmVtb25pY2EnIChkZWZhdWx0IGltcG9ydCkg4oCUIHRyZWF0IGFzIG1vZHVsZSBvYmplY3QgdG9vXG5cdFx0aWYgKGNsYXVzZS5uYW1lKSB7XG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQoY2xhdXNlLm5hbWUudGV4dCk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhIG5hbWVkIHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbiAodHlwZSBhbGlhcywgY2xhc3MsIG9yXG5cdCAqIGludGVyZmFjZSkgZm9yIHRoZSBmaWxlIGN1cnJlbnRseSBiZWluZyB2aXNpdGVkLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHQvLyBOYW1lc3BhY2VzIGFyZSB0aGUgbWlkZGxlIHNlZ21lbnRzIG9mIHF1YWxpZmllZCByZWZlcmVuY2VzXG5cdFx0Ly8gKG1vZGVscy5Jbm5lci5DcmF0ZSkg4oCUIHJlY29yZGVkIHNlcGFyYXRlbHkgZnJvbSB0aGUgcGxhaW4tbmFtZVxuXHRcdC8vIGRlY2xhcmF0aW9uIHRhYmxlIChzdHJpbmctbmFtZWQgYG1vZHVsZSAn4oCmJ2AgZGVjbGFyYXRpb25zIGFyZVxuXHRcdC8vIGFtYmllbnQgZXh0ZXJuYWxzIGFuZCBzdGF5IG91dClcblx0XHRpZiAodHMuaXNNb2R1bGVEZWNsYXJhdGlvbihub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSAmJlxuXHRcdFx0bm9kZS5ib2R5ICYmIHRzLmlzTW9kdWxlQmxvY2sobm9kZS5ib2R5KSkge1xuXHRcdFx0Y29uc3QgbmFtZXNwYWNlRmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0XHRsZXQgbmFtZXNwYWNlcyA9IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzLmdldChuYW1lc3BhY2VGaWxlUGF0aCk7XG5cdFx0XHRpZiAoIW5hbWVzcGFjZXMpIHtcblx0XHRcdFx0bmFtZXNwYWNlcyA9IG5ldyBNYXA8c3RyaW5nLCB0cy5Nb2R1bGVEZWNsYXJhdGlvbj4oKTtcblx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMuc2V0KG5hbWVzcGFjZUZpbGVQYXRoLCBuYW1lc3BhY2VzKTtcblx0XHRcdH1cblx0XHRcdG5hbWVzcGFjZXMuc2V0KG5vZGUubmFtZS50ZXh0LCBub2RlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRsZXQgbmFtZSA9ICcnO1xuXHRcdGxldCBraW5kOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uWydraW5kJ10gfCB1bmRlZmluZWQ7XG5cdFx0bGV0IGRlY2xOb2RlOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uWydub2RlJ10gfCB1bmRlZmluZWQ7XG5cblx0XHRpZiAodHMuaXNUeXBlQWxpYXNEZWNsYXJhdGlvbihub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSkge1xuXHRcdFx0bmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0a2luZCA9ICdhbGlhcyc7XG5cdFx0XHRkZWNsTm9kZSA9IG5vZGU7XG5cdFx0fSBlbHNlIGlmICh0cy5pc0NsYXNzRGVjbGFyYXRpb24obm9kZSkgJiYgbm9kZS5uYW1lKSB7XG5cdFx0XHRuYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0XHRraW5kID0gJ2NsYXNzJztcblx0XHRcdGRlY2xOb2RlID0gbm9kZTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzSW50ZXJmYWNlRGVjbGFyYXRpb24obm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdG5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRcdGtpbmQgPSAnaW50ZXJmYWNlJztcblx0XHRcdGRlY2xOb2RlID0gbm9kZTtcblx0XHR9XG5cblx0XHRpZiAoIWtpbmQgfHwgIWRlY2xOb2RlIHx8ICFuYW1lKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0bGV0IGRlY2xzID0gdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLmdldChmaWxlUGF0aCk7XG5cdFx0aWYgKCFkZWNscykge1xuXHRcdFx0ZGVjbHMgPSBuZXcgTWFwPHN0cmluZywgUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbj4oKTtcblx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscy5zZXQoZmlsZVBhdGgsIGRlY2xzKTtcblx0XHR9XG5cdFx0Y29uc3QgZW50cnk6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gPSB7IGtpbmQsIG5vZGUgOiBkZWNsTm9kZSwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0ZGVjbHMuc2V0KG5hbWUsIGVudHJ5KTtcblxuXHRcdC8vIGBleHBvcnQgZGVmYXVsdCBjbGFzcyBGb28ge31gIGlzIGFsc28gcmVhY2hhYmxlIHVuZGVyIHRoZSAnZGVmYXVsdCdcblx0XHQvLyBiaW5kaW5nIGZvciBkZWZhdWx0IGltcG9ydGVyc1xuXHRcdGlmIChraW5kID09PSAnY2xhc3MnKSB7XG5cdFx0XHRjb25zdCBjbGFzc05vZGUgPSBkZWNsTm9kZSBhcyB0cy5DbGFzc0RlY2xhcmF0aW9uO1xuXHRcdFx0Y29uc3QgaXNFeHBvcnRlZCA9IGNsYXNzTm9kZS5tb2RpZmllcnM/LnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRXhwb3J0S2V5d29yZCkgPz8gZmFsc2U7XG5cdFx0XHRjb25zdCBpc0RlZmF1bHQgPSBjbGFzc05vZGUubW9kaWZpZXJzPy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLkRlZmF1bHRLZXl3b3JkKSA/PyBmYWxzZTtcblx0XHRcdGlmIChpc0V4cG9ydGVkICYmIGlzRGVmYXVsdCkge1xuXHRcdFx0XHRkZWNscy5zZXQoJ2RlZmF1bHQnLCBlbnRyeSk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBjb25zdHMgaW5pdGlhbGl6ZWQgd2l0aCBhbiBhcnJheSBsaXRlcmFsIChvcHRpb25hbGx5IHdyYXBwZWQgaW5cblx0ICogYGFzIGNvbnN0YCAvIGBzYXRpc2ZpZXNgKSwgc28gYSBgdHlwZW9mIHN0YXR1c0xpc3RbbnVtYmVyXWAgZmllbGQgdHlwZVxuXHQgKiBleHBhbmRzIHRvIHRoZSBlbGVtZW50IGxpdGVyYWwgdW5pb24g4oCUIHRoZSBnZW5lcmF0ZWQgZmlsZSBjYXJyaWVzIG5vXG5cdCAqIGltcG9ydHMsIHNvIGVtaXR0aW5nIHRoZSBiYXJlIGB0eXBlb2Ygc3RhdHVzTGlzdGAgcXVlcnkgd291bGQgYmUgYW5cblx0ICogdW5yZXNvbHZhYmxlIG5hbWUgZG93bnN0cmVhbS4gRmlyc3QgYmluZGluZyB3aW5zOiBhIG5lc3RlZCBzaGFkb3dcblx0ICogbXVzdCBub3QgcmVwbGFjZSB0aGUgbW9kdWxlLWxldmVsIGNvbnN0IHRoZSB0eXBlb2YgcmVmZXJzIHRvLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlQ29uc3RBcnJheSAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpIHx8ICF0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSB8fCAhbm9kZS5pbml0aWFsaXplcikge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCB7IGluaXRpYWxpemVyOiByYXdJbml0aWFsaXplciB9ID0gbm9kZTtcblx0XHRsZXQgaW5pdGlhbGl6ZXI6IHRzLkV4cHJlc3Npb24gPSByYXdJbml0aWFsaXplcjtcblx0XHR3aGlsZSAoXG5cdFx0XHR0cy5pc0FzRXhwcmVzc2lvbihpbml0aWFsaXplcikgfHxcblx0XHRcdHRzLmlzU2F0aXNmaWVzRXhwcmVzc2lvbihpbml0aWFsaXplcikgfHxcblx0XHRcdC8vIHRoZSBhbmdsZS1icmFja2V0IGFzc2VydGlvbiBzcGVsbGluZyAoYDxjb25zdD5b4oCmXWApIGlzIHRoZVxuXHRcdFx0Ly8gc2FtZSBjb25zdC1hcnJheSBtYXJrZXIgYXMgdGhlIGBhcyBjb25zdGAgZm9ybSAoRjE3KVxuXHRcdFx0dHMuaXNUeXBlQXNzZXJ0aW9uRXhwcmVzc2lvbihpbml0aWFsaXplcilcblx0XHQpIHtcblx0XHRcdGluaXRpYWxpemVyID0gaW5pdGlhbGl6ZXIuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0aWYgKCF0cy5pc0FycmF5TGl0ZXJhbEV4cHJlc3Npb24oaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGZpbGVQYXRoID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGxldCBjb25zdHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuZ2V0KGZpbGVQYXRoKTtcblx0XHRpZiAoIWNvbnN0cykge1xuXHRcdFx0Y29uc3RzID0gbmV3IE1hcDxzdHJpbmcsIHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24+KCk7XG5cdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuc2V0KGZpbGVQYXRoLCBjb25zdHMpO1xuXHRcdH1cblx0XHRpZiAoIWNvbnN0cy5oYXMobm9kZS5uYW1lLnRleHQpKSB7XG5cdFx0XHRjb25zdHMuc2V0KG5vZGUubmFtZS50ZXh0LCBpbml0aWFsaXplcik7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEZpbmQgdGhlIGFycmF5IGxpdGVyYWwgYmVoaW5kIGEgbW9kdWxlIGNvbnN0IHJlZmVyZW5jZWQgdGhyb3VnaFxuXHQgKiBgdHlwZW9mYDogdGhlIGRlY2xhcmluZyBmaWxlJ3Mgb3duIGNvbnN0cyBmaXJzdCAodGhlIEYxMyBjYXNlIGlzIGFcblx0ICogTk9OLWV4cG9ydGVkIGNvbnN0IGluIHRoZSBzYW1lIG1vZHVsZSBhcyB0aGUgZXhwYW5kZWQgY2xhc3MpLCB0aGVuIOKAlFxuXHQgKiB3aGVuIHRoZSBmaWxlIGltcG9ydHMgdGhlIG5hbWUg4oCUIHRoZSBpbXBvcnRlZCBtb2R1bGUncyBjb25zdHMuXG5cdCAqIEV4dGVybmFsIG1vZHVsZXMgYXJlIG5ldmVyIGFuYWx5emVkLCBzbyB0aG9zZSB5aWVsZCBub3RoaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kUmVmZXJlbmNlZENvbnN0QXJyYXkgKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRmcm9tRmlsZTogc3RyaW5nXG5cdCk6IHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGxvY2FsID0gdGhpcy5yZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzLmdldChmcm9tRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWwpIHtcblx0XHRcdHJldHVybiBsb2NhbDtcblx0XHR9XG5cdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoZnJvbUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKCFpbXBvcnRlZCB8fCBpbXBvcnRlZC5pc05hbWVzcGFjZSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKGltcG9ydGVkLnNwZWNpZmllciwgZnJvbUZpbGUpO1xuXHRcdGlmICghcmVzb2x1dGlvbiB8fCByZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGZvdW5kID0gdGhpcy5yZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzLmdldChyZXNvbHV0aW9uLnJlc29sdmVkUGF0aCk/LmdldChpbXBvcnRlZC5vcmlnaW5hbE5hbWUpO1xuXHRcdHJldHVybiBmb3VuZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFbGVtZW50IGxpdGVyYWwgdHlwZXMgb2YgYSB0cmFja2VkIGNvbnN0IGFycmF5OiBldmVyeSBlbGVtZW50IG11c3QgYmVcblx0ICogYSBwbGFpbiBsaXRlcmFsIChvcHRpb25hbGx5IHdyYXBwZWQgaW4gYGFzIGNvbnN0YCAvIGBzYXRpc2ZpZXNgIC9cblx0ICogYDxjb25zdD5gIGFzc2VydGlvbnMpIOKAlCBzdHJpbmcsIG51bWVyaWMgKHVuYXJ5IGAtYC9gK2AgcHJlc2VydmVkKSxcblx0ICogYm9vbGVhbiwgb3IgbnVsbC4gU3ByZWFkcywgaWRlbnRpZmllcnMsIGFuZCBuZXN0ZWQgYXJyYXlzIG1lYW4gdGhlXG5cdCAqIHVuaW9uIGlzIG5vdCBzdGF0aWNhbGx5IHZpc2libGUgYW5kIHlpZWxkIHVuZGVmaW5lZCwgc28gdGhlIGNhbGxlclxuXHQgKiBkZWdyYWRlcyB0aGUgZmllbGQgdG8gYHVua25vd25gIHJhdGhlciB0aGFuIGd1ZXNzaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBsaXRlcmFsVHlwZXNPZkFycmF5IChhcnJheUxpdGVyYWw6IHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24pOiBzdHJpbmdbXSB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgbGl0ZXJhbHM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGFycmF5TGl0ZXJhbC5lbGVtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzU3ByZWFkRWxlbWVudChlbGVtZW50KSkge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbGl0ZXJhbCA9IHRoaXMubGl0ZXJhbFR5cGVPZkV4cHJlc3Npb24oZWxlbWVudCk7XG5cdFx0XHRpZiAobGl0ZXJhbCA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRsaXRlcmFscy5wdXNoKGxpdGVyYWwpO1xuXHRcdH1cblx0XHRpZiAobGl0ZXJhbHMubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBsaXRlcmFscztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFRoZSBsaXRlcmFsIHR5cGUgb2Ygb25lIGFycmF5IGVsZW1lbnQ6IGEgcGxhaW4gbGl0ZXJhbCAob3B0aW9uYWxseVxuXHQgKiB3cmFwcGVkIGluIGBhcyBjb25zdGAgLyBgc2F0aXNmaWVzYCAvIGFzc2VydGlvbiBleHByZXNzaW9ucykg4oCUXG5cdCAqIHN0cmluZywgbnVtZXJpYyAodW5hcnkgYC1gL2ArYCBwcmVzZXJ2ZWQpLCBib29sZWFuLCBvciBudWxsLlxuXHQgKiBBbnl0aGluZyBlbHNlIHlpZWxkcyB1bmRlZmluZWQuXG5cdCAqL1xuXHRwcml2YXRlIGxpdGVyYWxUeXBlT2ZFeHByZXNzaW9uIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgaW5uZXI6IHRzLkV4cHJlc3Npb24gPSBleHByO1xuXHRcdHdoaWxlICh0cy5pc0FzRXhwcmVzc2lvbihpbm5lcikgfHwgdHMuaXNTYXRpc2ZpZXNFeHByZXNzaW9uKGlubmVyKSB8fCB0cy5pc1R5cGVBc3NlcnRpb25FeHByZXNzaW9uKGlubmVyKSkge1xuXHRcdFx0aW5uZXIgPSBpbm5lci5leHByZXNzaW9uO1xuXHRcdH1cblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGlubmVyKSB8fCB0cy5pc05vU3Vic3RpdHV0aW9uVGVtcGxhdGVMaXRlcmFsKGlubmVyKSkge1xuXHRcdFx0Y29uc3QgbGl0ZXJhbCA9IGAnJHtpbm5lci50ZXh0fSdgO1xuXHRcdFx0cmV0dXJuIGxpdGVyYWw7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1ByZWZpeFVuYXJ5RXhwcmVzc2lvbihpbm5lcikgJiYgdHMuaXNOdW1lcmljTGl0ZXJhbChpbm5lci5vcGVyYW5kKSkge1xuXHRcdFx0aWYgKGlubmVyLm9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLk1pbnVzVG9rZW4pIHtcblx0XHRcdFx0Y29uc3QgbmVnYXRpdmUgPSBgLSR7aW5uZXIub3BlcmFuZC50ZXh0fWA7XG5cdFx0XHRcdHJldHVybiBuZWdhdGl2ZTtcblx0XHRcdH1cblx0XHRcdGlmIChpbm5lci5vcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5QbHVzVG9rZW4pIHtcblx0XHRcdFx0cmV0dXJuIGlubmVyLm9wZXJhbmQudGV4dDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc051bWVyaWNMaXRlcmFsKGlubmVyKSkge1xuXHRcdFx0cmV0dXJuIGlubmVyLnRleHQ7XG5cdFx0fVxuXHRcdGlmIChpbm5lci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRyZXR1cm4gJ3RydWUnO1xuXHRcdH1cblx0XHRpZiAoaW5uZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQpIHtcblx0XHRcdHJldHVybiAnZmFsc2UnO1xuXHRcdH1cblx0XHRpZiAoaW5uZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5OdWxsS2V5d29yZCkge1xuXHRcdFx0cmV0dXJuICdudWxsJztcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGMjI6IHRoZSBjb25zdC1hc3NlcnRpb24gY2hlY2sgc2hhcmVkIGJ5IHRoZSB2YWx1ZS1sZXZlbCBhbmRcblx0ICogZGVjbGFyYXRpb24tbGV2ZWwgcGF0aHMg4oCUIGBleHByIGFzIGNvbnN0YCBhbmQgYDxjb25zdD5leHByYCBwYXJzZVxuXHQgKiBpZGVudGljYWxseSAoYSBUeXBlUmVmZXJlbmNlTm9kZSBuYW1lZCAnY29uc3QnKS4gR2VuZXJhbCBgPFQ+ZXhwcmBcblx0ICogYXNzZXJ0aW9ucyBuZXZlciBtYXRjaC5cblx0ICovXG5cdHByaXZhdGUgaXNDb25zdEFzc2VydGlvblR5cGUgKHR5cGU6IHRzLlR5cGVOb2RlKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgY29uc3RBc3NlcnRpb24gPSB0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHR5cGUpICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIodHlwZS50eXBlTmFtZSkgJiZcblx0XHRcdHR5cGUudHlwZU5hbWUudGV4dCA9PT0gJ2NvbnN0Jztcblx0XHRyZXR1cm4gY29uc3RBc3NlcnRpb247XG5cdH1cblxuXHQvKipcblx0ICogVGhlIGFycmF5IGxpdGVyYWwgYmVoaW5kIGEgdmFsdWUtbGV2ZWwgZWxlbWVudCBhY2Nlc3M6IGlubGluZVxuXHQgKiAoYCg8Y29uc3Q+W+KApl0pWzBdYCwgYChb4oCmXSBhcyBjb25zdClbMV1gKSwgcGFyZW50aGVzaXplZCwgb3IgYVxuXHQgKiB0cmFja2VkIG1vZHVsZSBjb25zdCBhcnJheSAoYGNvbnN0IHggPSA8Y29uc3Q+W+KApl1gIC8gYHhbMF1gLCBGMTdcblx0ICogdHJhY2tpbmcpLiBPbmx5IGNvbnN0IGFzc2VydGlvbnMgYXJlIHVud3JhcHBlZCDigJQgZ2VuZXJhbFxuXHQgKiBhc3NlcnRpb25zIHN0YXkgdW5rbm93biAoRjIyIHNjb3BlIGJvdW5kYXJ5KS5cblx0ICovXG5cdHByaXZhdGUgY29uc3RBcnJheUxpdGVyYWxPZiAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5FeHByZXNzaW9uID0gZXhwcjtcblx0XHR3aGlsZSAodHMuaXNQYXJlbnRoZXNpemVkRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0aWYgKHRzLmlzQXJyYXlMaXRlcmFsRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0cmV0dXJuIGN1cnJlbnQ7XG5cdFx0fVxuXHRcdGlmICgodHMuaXNBc0V4cHJlc3Npb24oY3VycmVudCkgfHwgdHMuaXNUeXBlQXNzZXJ0aW9uRXhwcmVzc2lvbihjdXJyZW50KSkgJiZcblx0XHRcdHRoaXMuaXNDb25zdEFzc2VydGlvblR5cGUoY3VycmVudC50eXBlKSkge1xuXHRcdFx0Y29uc3QgaW5uZXIgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0XHRjb25zdCBsaXRlcmFsID0gdHMuaXNBcnJheUxpdGVyYWxFeHByZXNzaW9uKGlubmVyKSA/IGlubmVyIDogdW5kZWZpbmVkO1xuXHRcdFx0cmV0dXJuIGxpdGVyYWw7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudCkpIHtcblx0XHRcdGNvbnN0IHRyYWNrZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChjdXJyZW50LnRleHQpO1xuXHRcdFx0cmV0dXJuIHRyYWNrZWQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRW1pdC10eXBlIGZvciBgdHlwZW9mIG5hbWVgIHdoZW4gYG5hbWVgIGlzIGEgdHJhY2tlZCBjb25zdCBhcnJheTogdGhlXG5cdCAqIHVuaW9uIG9mIGl0cyBlbGVtZW50IGxpdGVyYWwgdHlwZXMgKGAnYWN0aXZlJyB8ICdjbG9zZWQnYCkuIEV2ZXJ5XG5cdCAqIG90aGVyIHR5cGVvZiBzb3VyY2Ug4oCUIG5vbi1hcnJheSBjb25zdHMsIGZ1bmN0aW9ucywgY2xhc3NlcywgbmFtZXMgbm90XG5cdCAqIHRyYWNrZWQgYXQgYWxsIOKAlCB5aWVsZHMgdW5kZWZpbmVkLCBzbyB0aGUgY2FsbGVyIGRlZ3JhZGVzIHRoZSBmaWVsZFxuXHQgKiB0byBgdW5rbm93bmA6IGEgYmFyZSBgdHlwZW9mIG5hbWVgIGVtaXR0ZWQgaW50byB0eXBlcy50cyBoYXMgbm9cblx0ICogaW1wb3J0IHRvIHJlc29sdmUgYWdhaW5zdCBkb3duc3RyZWFtLlxuXHQgKi9cblx0cHJpdmF0ZSB0eXBlT2ZDb25zdEFycmF5VW5pb24gKG5hbWU6IHN0cmluZywgZnJvbUZpbGU6IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJyYXlMaXRlcmFsID0gdGhpcy5maW5kUmVmZXJlbmNlZENvbnN0QXJyYXkobmFtZSwgZnJvbUZpbGUpO1xuXHRcdGlmICghYXJyYXlMaXRlcmFsKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBsaXRlcmFscyA9IHRoaXMubGl0ZXJhbFR5cGVzT2ZBcnJheShhcnJheUxpdGVyYWwpO1xuXHRcdGlmICghbGl0ZXJhbHMpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHVuaW9uID0gbGl0ZXJhbHMuam9pbignIHwgJyk7XG5cdFx0cmV0dXJuIHVuaW9uO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCB0aGUgaW1wb3J0aW5nIGZpbGUncyBuYW1lZC9uYW1lc3BhY2UvZGVmYXVsdCBpbXBvcnQgYmluZGluZ3Mgc29cblx0ICogcmVmZXJlbmNlZC10eXBlIG5hbWVzIHJlc29sdmUgdGhyb3VnaCB0aGUgZmlsZSdzIG93biBpbXBvcnQgc3RhdGVtZW50c1xuXHQgKiAoRjEwKSByYXRoZXIgdGhhbiBhIHByb2dyYW0td2lkZSBuYW1lIG1hcC5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tSZWZlcmVuY2VkVHlwZUltcG9ydCAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNJbXBvcnREZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCB7IG1vZHVsZVNwZWNpZmllciB9ID0gbm9kZTtcblx0XHRpZiAoIXRzLmlzU3RyaW5nTGl0ZXJhbChtb2R1bGVTcGVjaWZpZXIpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGNsYXVzZSA9IG5vZGUuaW1wb3J0Q2xhdXNlO1xuXHRcdGlmICghY2xhdXNlKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0bGV0IGltcG9ydHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoZmlsZVBhdGgpO1xuXHRcdGlmICghaW1wb3J0cykge1xuXHRcdFx0aW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZUltcG9ydD4oKTtcblx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLnNldChmaWxlUGF0aCwgaW1wb3J0cyk7XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0IHsgU2hhcmVkU2hhcGUgfSBmcm9tICfigKYnIC8gaW1wb3J0IHsgU2hhcmVkU2hhcGUgYXMgUyB9IGZyb20gJ+KApidcblx0XHRpZiAoY2xhdXNlLm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lZEltcG9ydHMoY2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2YgY2xhdXNlLm5hbWVkQmluZGluZ3MuZWxlbWVudHMpIHtcblx0XHRcdFx0Y29uc3QgbG9jYWxOYW1lID0gZWxlbWVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IG9yaWdpbmFsTmFtZSA9IGVsZW1lbnQucHJvcGVydHlOYW1lID8gZWxlbWVudC5wcm9wZXJ0eU5hbWUudGV4dCA6IGxvY2FsTmFtZTtcblx0XHRcdFx0aW1wb3J0cy5zZXQobG9jYWxOYW1lLCB7XG5cdFx0XHRcdFx0b3JpZ2luYWxOYW1lLFxuXHRcdFx0XHRcdHNwZWNpZmllciAgIDogbW9kdWxlU3BlY2lmaWVyLnRleHQsXG5cdFx0XHRcdFx0aXNOYW1lc3BhY2UgOiBmYWxzZVxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgKiBhcyBtb2RlbHMgZnJvbSAn4oCmJyDigJQgcmVzb2x2ZWQgd2hlbiBhIHF1YWxpZmllZCBuYW1lXG5cdFx0Ly8gKG1vZGVscy5TaGFyZWRTaGFwZSkgaXMgZW5jb3VudGVyZWRcblx0XHRpZiAoY2xhdXNlLm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lc3BhY2VJbXBvcnQoY2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHRpbXBvcnRzLnNldChjbGF1c2UubmFtZWRCaW5kaW5ncy5uYW1lLnRleHQsIHtcblx0XHRcdFx0b3JpZ2luYWxOYW1lIDogJycsXG5cdFx0XHRcdHNwZWNpZmllciAgICA6IG1vZHVsZVNwZWNpZmllci50ZXh0LFxuXHRcdFx0XHRpc05hbWVzcGFjZSAgOiB0cnVlXG5cdFx0XHR9KTtcblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgU2hhcmVkU2hhcGUgZnJvbSAn4oCmJyAoZGVmYXVsdCBpbXBvcnQpXG5cdFx0aWYgKGNsYXVzZS5uYW1lKSB7XG5cdFx0XHRpbXBvcnRzLnNldChjbGF1c2UubmFtZS50ZXh0LCB7XG5cdFx0XHRcdG9yaWdpbmFsTmFtZSA6ICdkZWZhdWx0Jyxcblx0XHRcdFx0c3BlY2lmaWVyICAgIDogbW9kdWxlU3BlY2lmaWVyLnRleHQsXG5cdFx0XHRcdGlzTmFtZXNwYWNlICA6IGZhbHNlXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIHJlLWV4cG9ydCB3aXJpbmcgKGBleHBvcnQgeyBYIH0gZnJvbSAn4oCmJ2AsIGBleHBvcnQgKiBmcm9tICfigKYnYCxcblx0ICogYGV4cG9ydCB7IFggYXMgWSB9YCkgc28gcmVzb2x1dGlvbiBjYW4gY2hhc2UgYmFycmVscyB0byB0aGUgb3JpZ2luXG5cdCAqIG1vZHVsZS4gTWlycm9ycyBNb2R1bGVHcmFwaEJ1aWxkZXIucmVzb2x2ZU9yaWdpbiwgbmFtZS1iYXNlZCBvbmx5LlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlUmVFeHBvcnQgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzRXhwb3J0RGVjbGFyYXRpb24obm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0Y29uc3QgeyBtb2R1bGVTcGVjaWZpZXIgfSA9IG5vZGU7XG5cdFx0Y29uc3Qgc3BlY2lmaWVyVGV4dCA9IG1vZHVsZVNwZWNpZmllciAmJiB0cy5pc1N0cmluZ0xpdGVyYWwobW9kdWxlU3BlY2lmaWVyKVxuXHRcdFx0PyBtb2R1bGVTcGVjaWZpZXIudGV4dFxuXHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHRpZiAobm9kZS5leHBvcnRDbGF1c2UgJiYgdHMuaXNOYW1lZEV4cG9ydHMobm9kZS5leHBvcnRDbGF1c2UpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2Ygbm9kZS5leHBvcnRDbGF1c2UuZWxlbWVudHMpIHtcblx0XHRcdFx0Y29uc3QgZXhwb3J0ZWROYW1lID0gZWxlbWVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IGxvY2FsTmFtZSA9IGVsZW1lbnQucHJvcGVydHlOYW1lID8gZWxlbWVudC5wcm9wZXJ0eU5hbWUudGV4dCA6IGV4cG9ydGVkTmFtZTtcblx0XHRcdFx0aWYgKHNwZWNpZmllclRleHQpIHtcblx0XHRcdFx0XHQvLyBleHBvcnQgeyBYIH0gZnJvbSAn4oCmJyAvIGV4cG9ydCB7IFggYXMgWSB9IGZyb20gJ+KApidcblx0XHRcdFx0XHRsZXQgcmVFeHBvcnRzID0gdGhpcy5yZWZlcmVuY2VkVHlwZVJlRXhwb3J0cy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0XHRcdGlmICghcmVFeHBvcnRzKSB7XG5cdFx0XHRcdFx0XHRyZUV4cG9ydHMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZVJlRXhwb3J0cy5zZXQoZmlsZVBhdGgsIHJlRXhwb3J0cyk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdHJlRXhwb3J0cy5zZXQoZXhwb3J0ZWROYW1lLCBzcGVjaWZpZXJUZXh0KTtcblx0XHRcdFx0fSBlbHNlIGlmIChsb2NhbE5hbWUgIT09IGV4cG9ydGVkTmFtZSkge1xuXHRcdFx0XHRcdC8vIGV4cG9ydCB7IFggYXMgWSB9IOKAlCBzYW1lLWZpbGUgYWxpYXMgb2YgYSBsb2NhbCBkZWNsYXJhdGlvblxuXHRcdFx0XHRcdGxldCBhbGlhc2VzID0gdGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydEFsaWFzZXMuZ2V0KGZpbGVQYXRoKTtcblx0XHRcdFx0XHRpZiAoIWFsaWFzZXMpIHtcblx0XHRcdFx0XHRcdGFsaWFzZXMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydEFsaWFzZXMuc2V0KGZpbGVQYXRoLCBhbGlhc2VzKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0YWxpYXNlcy5zZXQoZXhwb3J0ZWROYW1lLCBsb2NhbE5hbWUpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0aWYgKG5vZGUuZXhwb3J0Q2xhdXNlICYmIHRzLmlzTmFtZXNwYWNlRXhwb3J0KG5vZGUuZXhwb3J0Q2xhdXNlKSkge1xuXHRcdFx0Ly8gYGV4cG9ydCAqIGFzIG5zIGZyb20gJ+KApidgIOKAlCBhIG5lc3RlZCBtb2R1bGUgbmFtZXNwYWNlOyBtaWRkbGVcblx0XHRcdC8vIHNlZ21lbnRzIG9mIHF1YWxpZmllZCByZWZlcmVuY2VzIChiYXJyZWwuRGVlcC5HYWRnZXQpIGNoYXNlIGl0XG5cdFx0XHRpZiAoc3BlY2lmaWVyVGV4dCkge1xuXHRcdFx0XHRsZXQgc3RhcnMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlU3RhcnMuZ2V0KGZpbGVQYXRoKTtcblx0XHRcdFx0aWYgKCFzdGFycykge1xuXHRcdFx0XHRcdHN0YXJzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0XHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlU3RhcnMuc2V0KGZpbGVQYXRoLCBzdGFycyk7XG5cdFx0XHRcdH1cblx0XHRcdFx0c3RhcnMuc2V0KG5vZGUuZXhwb3J0Q2xhdXNlLm5hbWUudGV4dCwgc3BlY2lmaWVyVGV4dCk7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0aWYgKCFub2RlLmV4cG9ydENsYXVzZSAmJiBzcGVjaWZpZXJUZXh0KSB7XG5cdFx0XHQvLyBleHBvcnQgKiBmcm9tICfigKYnXG5cdFx0XHRsZXQgc3RhcnMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuZ2V0KGZpbGVQYXRoKTtcblx0XHRcdGlmICghc3RhcnMpIHtcblx0XHRcdFx0c3RhcnMgPSBbXTtcblx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydFN0YXJzLnNldChmaWxlUGF0aCwgc3RhcnMpO1xuXHRcdFx0fVxuXHRcdFx0c3RhcnMucHVzaChzcGVjaWZpZXJUZXh0KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIG1vZHVsZSBzcGVjaWZpZXIgZnJvbSBhIGNvbnRhaW5pbmcgZmlsZSB3aXRoIHRoZSBwcm9ncmFtJ3Ncblx0ICogY29tcGlsZXJPcHRpb25zICh0c2NvbmZpZyBgcGF0aHNgLCBleHRlbnNpb25sZXNzIGltcG9ydHMsIGluZGV4IGZpbGVzKS5cblx0ICogTW9kdWxlIHJlc29sdXRpb24gb25seSDigJQgdGhlIG5vLWdldFR5cGVDaGVja2VyKCkgcHJlY2VkZW50IHN0YXlzLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUgKHNwZWNpZmllcjogc3RyaW5nLCBjb250YWluaW5nRmlsZTogc3RyaW5nKTpcblx0XHRSZWZlcmVuY2VkVHlwZVJlc29sdXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGNhY2hlS2V5ID0gYCR7Y29udGFpbmluZ0ZpbGV9Ojoke3NwZWNpZmllcn1gO1xuXHRcdGlmICh0aGlzLnJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbkNhY2hlLmhhcyhjYWNoZUtleSkpIHtcblx0XHRcdGNvbnN0IGNhY2hlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZXNvbHV0aW9uQ2FjaGUuZ2V0KGNhY2hlS2V5KTtcblx0XHRcdHJldHVybiBjYWNoZWQgPT09IHVuZGVmaW5lZCA/IHVuZGVmaW5lZCA6IGNhY2hlZDtcblx0XHR9XG5cblx0XHRjb25zdCByZXNvbHV0aW9uID0gdHMucmVzb2x2ZU1vZHVsZU5hbWUoXG5cdFx0XHRzcGVjaWZpZXIsXG5cdFx0XHRjb250YWluaW5nRmlsZSxcblx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVDb21waWxlck9wdGlvbnMsXG5cdFx0XHR0cy5zeXNcblx0XHQpLnJlc29sdmVkTW9kdWxlO1xuXG5cdFx0Y29uc3QgcmVzdWx0OiBSZWZlcmVuY2VkVHlwZVJlc29sdXRpb24gfCB1bmRlZmluZWQgPSByZXNvbHV0aW9uXG5cdFx0XHQ/IHtcblx0XHRcdFx0cmVzb2x2ZWRQYXRoIDogbm9kZVBhdGgucmVzb2x2ZShyZXNvbHV0aW9uLnJlc29sdmVkRmlsZU5hbWUpLFxuXHRcdFx0XHRpc0V4dGVybmFsICAgOiAhIXJlc29sdXRpb24uaXNFeHRlcm5hbExpYnJhcnlJbXBvcnRcblx0XHRcdH1cblx0XHRcdDogdW5kZWZpbmVkO1xuXG5cdFx0dGhpcy5yZWZlcmVuY2VkVHlwZVJlc29sdXRpb25DYWNoZS5zZXQoY2FjaGVLZXksIHJlc3VsdCk7XG5cdFx0Y29uc3QgZmluYWxSZXN1bHQgPSByZXN1bHQ7XG5cdFx0cmV0dXJuIGZpbmFsUmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIExvb2sgdXAgYSBuYW1lIGluIG9uZSByZXNvbHZlZCBtb2R1bGUsIGNoYXNpbmcgcmUtZXhwb3J0IGJhcnJlbHMgd2l0aCBhXG5cdCAqIGJvdW5kZWQgZGVwdGguIEV4dGVybmFsIChub2RlX21vZHVsZXMpIG1vZHVsZXMgaG9sZCBubyBpbi1wcm9qZWN0XG5cdCAqIGRlY2xhcmF0aW9ucyBhbmQgc3RvcCB0aGUgY2hhc2UuXG5cdCAqL1xuXHRwcml2YXRlIGZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlIChcblx0XHRtb2R1bGVQYXRoOiBzdHJpbmcsXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdGRlcHRoOiBudW1iZXJcblx0KTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKGRlcHRoID4gTUFYX1JFRVhQT1JUX0NIQVNFX0RFUFRIKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IGRlY2xzID0gdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLmdldChtb2R1bGVQYXRoKTtcblx0XHRjb25zdCBkaXJlY3QgPSBkZWNscz8uZ2V0KG5hbWUpO1xuXHRcdGlmIChkaXJlY3QpIHtcblx0XHRcdHJldHVybiBkaXJlY3Q7XG5cdFx0fVxuXHRcdC8vIGV4cG9ydCB7IFggYXMgWSB9IOKAlCByZXNvbHZlIHRocm91Z2ggdGhlIGxvY2FsIG5hbWVcblx0XHRjb25zdCBsb2NhbEFsaWFzID0gdGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydEFsaWFzZXMuZ2V0KG1vZHVsZVBhdGgpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGxvY2FsQWxpYXMpIHtcblx0XHRcdGNvbnN0IGFsaWFzZWQgPSBkZWNscz8uZ2V0KGxvY2FsQWxpYXMpO1xuXHRcdFx0aWYgKGFsaWFzZWQpIHtcblx0XHRcdFx0cmV0dXJuIGFsaWFzZWQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVFeHBvcnRzID0gdGhpcy5yZWZlcmVuY2VkVHlwZVJlRXhwb3J0cy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0Y29uc3QgcmVFeHBvcnRTcGVjaWZpZXIgPSByZUV4cG9ydHM/LmdldChuYW1lKTtcblx0XHRpZiAocmVFeHBvcnRTcGVjaWZpZXIpIHtcblx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUocmVFeHBvcnRTcGVjaWZpZXIsIG1vZHVsZVBhdGgpO1xuXHRcdFx0aWYgKG5leHRSZXNvbHV0aW9uICYmICFuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZShuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIG5hbWUsIGRlcHRoICsgMSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGNvbnN0IHN0YXJzID0gdGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydFN0YXJzLmdldChtb2R1bGVQYXRoKTtcblx0XHRpZiAoc3RhcnMpIHtcblx0XHRcdGZvciAoY29uc3Qgc3RhclNwZWNpZmllciBvZiBzdGFycykge1xuXHRcdFx0XHRjb25zdCBuZXh0UmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKHN0YXJTcGVjaWZpZXIsIG1vZHVsZVBhdGgpO1xuXHRcdFx0XHRpZiAoIW5leHRSZXNvbHV0aW9uIHx8IG5leHRSZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBmb3VuZCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUobmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBuYW1lLCBkZXB0aCArIDEpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSByZWZlcmVuY2VkIHR5cGUgbmFtZSBhcyB1c2VkIGluIGZyb21GaWxlLCBpbXBvcnQtYXdhcmU6XG5cdCAqICAgMS4gdGhlIGZpbGUncyBvd24gaW1wb3J0IHN0YXRlbWVudHMgKHJlbGF0aXZlICsgdHNjb25maWcgcGF0aHMsXG5cdCAqICAgICAgY2hhc2VkIHRocm91Z2ggcmUtZXhwb3J0IGJhcnJlbHMpLFxuXHQgKiAgIDIuIHRoZSBmaWxlJ3MgbG9jYWwgZGVjbGFyYXRpb25zLFxuXHQgKiAgIDMuIHRoZSB1bmlxdWUgc2FtZS1uYW1lZCBkZWNsYXJhdGlvbiBhY3Jvc3Mgc2Nhbm5lZCBmaWxlcy5cblx0ICogUmV0dXJucyB1bmRlZmluZWQgd2hlbiBub3RoaW5nIG1hdGNoZXMgKG9yIHRoZSBtYXRjaCBpcyBhbWJpZ3VvdXMpLFxuXHQgKiBpbiB3aGljaCBjYXNlIHRoZSBjYWxsZXIgZmFsbHMgYmFjayB0byBgdW5rbm93bmAuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIChcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0ZnJvbUZpbGU6IHN0cmluZ1xuXHQpOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHQvLyAxLiB0aGUgZmlsZSdzIG93biBpbXBvcnRzIHdpbiDigJQgYW4gaW1wb3J0IGlzIG5ldmVyIHNoYWRvd2VkIGJ5IGFcblx0XHQvLyBzYW1lLW5hbWVkIGxvY2FsIGRlY2xhcmF0aW9uIGVsc2V3aGVyZSBpbiB0aGUgcHJvZ3JhbSAoRjEwKVxuXHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KGZyb21GaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChpbXBvcnRlZCAmJiAhaW1wb3J0ZWQuaXNOYW1lc3BhY2UpIHtcblx0XHRcdGNvbnN0IHJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShpbXBvcnRlZC5zcGVjaWZpZXIsIGZyb21GaWxlKTtcblx0XHRcdGlmIChyZXNvbHV0aW9uICYmICFyZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKHJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBpbXBvcnRlZC5vcmlnaW5hbE5hbWUsIDApO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyAyLiBsb2NhbCBkZWNsYXJhdGlvbiBpbiB0aGUgcmVmZXJlbmNpbmcgZmlsZSBpdHNlbGZcblx0XHRjb25zdCBsb2NhbCA9IHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscy5nZXQoZnJvbUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGxvY2FsKSB7XG5cdFx0XHRyZXR1cm4gbG9jYWw7XG5cdFx0fVxuXG5cdFx0Ly8gMy4gcHJvZ3JhbS13aWRlIGZhbGxiYWNrLCB1bmlxdWUgZGVjbGFyYXRpb24gb25seSDigJQgYW1iaWd1aXR5IGFuZFxuXHRcdC8vIGFic2VuY2UgYm90aCB5aWVsZCB1bmRlZmluZWQgKHRoZSBjYWxsZXIgZW1pdHMgYHVua25vd25gKS5cblx0XHQvLyBFeHRlcm5hbC9hbWJpZW50IGRlY2xhcmF0aW9ucyAoLmQudHMsIG5vZGVfbW9kdWxlcykgZG8gbm90XG5cdFx0Ly8gcGFydGljaXBhdGU6IGEgdXNlci1sb2NhbCBkZWNsYXJhdGlvbiBhbHdheXMgd2lucyBvdmVyIGFcblx0XHQvLyBwYWNrYWdlLWRlY2xhcmVkIHNhbWUtbmFtZWQgdHlwZSAodGhlIHBsYWluLVRTIHRpZXIgb2YgdGhlXG5cdFx0Ly8gaWRlbnRpdHkgbGF3OyBhbWJpZ3VpdHkgYW1vbmcgdGhlIHJlbWFpbmluZyBkZWNsYXJhdGlvbnMgaXNcblx0XHQvLyB2YWxpZGF0ZWQgc2VwYXJhdGVseSBhcyBhIGhhcmQgZmFpbClcblx0XHRsZXQgdW5pcXVlOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkO1xuXHRcdGxldCBjb3VudCA9IDA7XG5cdFx0Zm9yIChjb25zdCBbIGZpbGVQYXRoLCBkZWNscyBdIG9mIHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscykge1xuXHRcdFx0aWYgKHRoaXMuaXNFeHRlcm5hbERlY2xGaWxlKGZpbGVQYXRoKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGNhbmRpZGF0ZSA9IGRlY2xzLmdldChuYW1lKTtcblx0XHRcdGlmIChjYW5kaWRhdGUpIHtcblx0XHRcdFx0Y291bnQrKztcblx0XHRcdFx0dW5pcXVlID0gY2FuZGlkYXRlO1xuXHRcdFx0XHRpZiAoY291bnQgPiAxKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGNvbnN0IHJlc3VsdCA9IGNvdW50ID09PSAxID8gdW5pcXVlIDogdW5kZWZpbmVkO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0ZXJuYWwvYW1iaWVudCBkZWNsYXJhdGlvbiBmaWxlcyAoLmQudHMsIGFueXRoaW5nIHVuZGVyXG5cdCAqIG5vZGVfbW9kdWxlcykgbmV2ZXIgcGFydGljaXBhdGUgaW4gcGxhaW4tVFMgcmVmZXJlbmNlZC10eXBlXG5cdCAqIHJlc29sdXRpb24gb3IgdGhlIGFtYmlndWl0eSBsYXc6IHRoZXkgYXJlIG5vdCBwcm9qZWN0IHNvdXJjZSwgdGhlXG5cdCAqIENMSSBuZXZlciBhbmFseXplcyB0aGVtLCBhbmQgYSB1c2VyLWxvY2FsIGRlY2xhcmF0aW9uIGFsd2F5cyB3aW5zXG5cdCAqIG92ZXIgYSBwYWNrYWdlLWRlY2xhcmVkIHNhbWUtbmFtZWQgdHlwZS5cblx0ICovXG5cdHByaXZhdGUgaXNFeHRlcm5hbERlY2xGaWxlIChmaWxlOiBzdHJpbmcpOiBib29sZWFuIHtcblx0XHRjb25zdCBleHRlcm5hbCA9IGZpbGUuZW5kc1dpdGgoJy5kLnRzJykgfHxcblx0XHRcdGZpbGUuaW5jbHVkZXMoYCR7bm9kZVBhdGguc2VwfW5vZGVfbW9kdWxlcyR7bm9kZVBhdGguc2VwfWApO1xuXHRcdHJldHVybiBleHRlcm5hbDtcblx0fVxuXG5cdC8qKlxuXHQgKiBQcm9wZXJ0aWVzIG9mIGEgcmVmZXJlbmNlZCBjbGFzcy9pbnRlcmZhY2UvYWxpYXMtb2YtbGl0ZXJhbCBkZWNsYXJhdGlvbixcblx0ICogc2hhcmVkIGJ5IGB0aGlzOmAtcGFyYW1ldGVyIGV4cGFuc2lvbiBhbmQgaW5saW5lIHR5cGUgZW1pc3Npb24uXG5cdCAqIEluaGVyaXRlZCBtZW1iZXJzIGFyZSBpbmNsdWRlZDogdGhlIGV4dGVuZHMgY2hhaW4gaXMgd2Fsa2VkXG5cdCAqIChkZXB0aC1jYXBwZWQsIGN5Y2xlLWd1YXJkZWQpIGFuZCBwYXJlbnQgZmllbGRzIG1lcmdlIGZpcnN0LCB0aGVcblx0ICogZGVjbGFyYXRpb24ncyBvd24gZmllbGRzIG92ZXJyaWRpbmcgb24gbmFtZSBjbGFzaC5cblx0ICovXG5cdHByaXZhdGUgcmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllcyAoZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbik6XG5cdFx0TWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgdmlzaXRlZCA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSB0aGlzLnJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXNJbm5lcihkZWNsLCB2aXNpdGVkLCAwKTtcblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdHByaXZhdGUgcmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllc0lubmVyIChcblx0XHRkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uLFxuXHRcdHZpc2l0ZWQ6IFNldDxzdHJpbmc+LFxuXHRcdGRlcHRoOiBudW1iZXJcblx0KTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3Qgb3duUHJvcGVydGllcyA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cdFx0Y29uc3QgZGVjbE5vZGUgPSBkZWNsLm5vZGUgYXMgdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHRzLkludGVyZmFjZURlY2xhcmF0aW9uO1xuXHRcdGNvbnN0IGRlY2xOYW1lID0gZGVjbE5vZGUubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIoZGVjbE5vZGUubmFtZSkgPyBkZWNsTm9kZS5uYW1lLnRleHQgOiAnJztcblx0XHRjb25zdCB2aXNpdEtleSA9IGAke2RlY2wua2luZH06JHtkZWNsLmZpbGV9OiR7ZGVjbE5hbWV9YDtcblx0XHRpZiAoZGVwdGggPiBNQVhfSEVSSVRBR0VfREVQVEggfHwgdmlzaXRlZC5oYXModmlzaXRLZXkpKSB7XG5cdFx0XHRyZXR1cm4gb3duUHJvcGVydGllcztcblx0XHR9XG5cdFx0dmlzaXRlZC5hZGQodmlzaXRLZXkpO1xuXG5cdFx0aWYgKGRlY2wua2luZCA9PT0gJ2NsYXNzJykge1xuXHRcdFx0Y29uc3QgY2xhc3NQcm9wcyA9IHRoaXMuZXh0cmFjdENsYXNzUHJvcGVydGllcyhkZWNsLm5vZGUgYXMgdHMuQ2xhc3NEZWNsYXJhdGlvbik7XG5cdFx0XHRmb3IgKGNvbnN0IFsgbmFtZSwgaW5mbyBdIG9mIGNsYXNzUHJvcHMpIHtcblx0XHRcdFx0b3duUHJvcGVydGllcy5zZXQobmFtZSwgaW5mbyk7XG5cdFx0XHR9XG5cdFx0fSBlbHNlIGlmIChkZWNsLmtpbmQgPT09ICdpbnRlcmZhY2UnKSB7XG5cdFx0XHRjb25zdCBpZmFjZSA9IGRlY2wubm9kZSBhcyB0cy5JbnRlcmZhY2VEZWNsYXJhdGlvbjtcblx0XHRcdHRoaXMuY29sbGVjdFR5cGVFbGVtZW50UHJvcGVydGllcyhbIC4uLmlmYWNlLm1lbWJlcnMgXSwgb3duUHJvcGVydGllcyk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdGNvbnN0IGFsaWFzVHlwZSA9IChkZWNsLm5vZGUgYXMgdHMuVHlwZUFsaWFzRGVjbGFyYXRpb24pLnR5cGU7XG5cdFx0XHRpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUoYWxpYXNUeXBlKSkge1xuXHRcdFx0XHR0aGlzLmNvbGxlY3RUeXBlRWxlbWVudFByb3BlcnRpZXMoWyAuLi5hbGlhc1R5cGUubWVtYmVycyBdLCBvd25Qcm9wZXJ0aWVzKTtcblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdHJldHVybiBvd25Qcm9wZXJ0aWVzO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIGhlcml0YWdlIG1lcmdlcyBwYXJlbnQgZmllbGRzIGZpcnN0OyB0aGUgZGVjbGFyYXRpb24ncyBvd24gZmllbGRzXG5cdFx0Ly8gb3ZlcnJpZGUgb24gbmFtZSBjbGFzaCAobGF0ZXIgYmFzZXMgb3ZlcnJpZGUgZWFybGllciBvbmVzKVxuXHRcdGNvbnN0IG1lcmdlZCA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cdFx0Zm9yIChjb25zdCBiYXNlRGVjbCBvZiB0aGlzLnJlc29sdmVIZXJpdGFnZURlY2xhcmF0aW9ucyhkZWNsKSkge1xuXHRcdFx0Y29uc3QgYmFzZVByb3BzID0gdGhpcy5yZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzSW5uZXIoYmFzZURlY2wsIHZpc2l0ZWQsIGRlcHRoICsgMSk7XG5cdFx0XHRmb3IgKGNvbnN0IFsgbmFtZSwgaW5mbyBdIG9mIGJhc2VQcm9wcykge1xuXHRcdFx0XHRtZXJnZWQuc2V0KG5hbWUsIGluZm8pO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRmb3IgKGNvbnN0IFsgbmFtZSwgaW5mbyBdIG9mIG93blByb3BlcnRpZXMpIHtcblx0XHRcdG1lcmdlZC5zZXQobmFtZSwgaW5mbyk7XG5cdFx0fVxuXHRcdHJldHVybiBtZXJnZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUHJvcGVydHkgc2lnbmF0dXJlcyBvZiBpbnRlcmZhY2UvYWxpYXMgdHlwZS1saXRlcmFsIG1lbWJlcnMsIGludG9cblx0ICogdGhlIGdpdmVuIG1hcC5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdFR5cGVFbGVtZW50UHJvcGVydGllcyAoXG5cdFx0bWVtYmVyczogcmVhZG9ubHkgdHMuVHlwZUVsZW1lbnRbXSxcblx0XHRwcm9wZXJ0aWVzOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+XG5cdCk6IHZvaWQge1xuXHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIG1lbWJlcnMpIHtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdHByb3BlcnRpZXMuc2V0KHByb3BOYW1lLCB7XG5cdFx0XHRcdFx0bmFtZSAgICAgOiBwcm9wTmFtZSxcblx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogISFtZW1iZXIucXVlc3Rpb25Ub2tlbixcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgdGhlIGhlcml0YWdlIGNsYXVzZSBvZiBhIGNsYXNzIChgZXh0ZW5kcyBCYXNlYCkgb3IgaW50ZXJmYWNlXG5cdCAqIChgZXh0ZW5kcyBBLCBCYCkgdG8gcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9ucyB0aHJvdWdoIHRoZSBTQU1FXG5cdCAqIGltcG9ydC1hd2FyZSBtYWNoaW5lcnkgYXMgcGxhaW4gcmVmZXJlbmNlcyAodGhlIGRlY2xhcmluZyBmaWxlJ3Mgb3duXG5cdCAqIGltcG9ydHMgZmlyc3QsIHRoZW4gaXRzIGxvY2FscywgdGhlbiB0aGUgdW5pcXVlIHByb2dyYW0td2lkZVxuXHQgKiBkZWNsYXJhdGlvbikuIFVucmVzb2x2YWJsZSBvciBleHRlcm5hbCBiYXNlcyB5aWVsZCBub3RoaW5nIOKAlCB0aGVpclxuXHQgKiBpbmhlcml0ZWQgZmllbGRzIHNpbXBseSBzdGF5IGFic2VudCwgc2FtZSBhcyBiZWZvcmUgdGhpcyB3YWxrXG5cdCAqIGV4aXN0ZWQuIE1peGluIGNhbGxzIChgZXh0ZW5kcyBtaXhpbihYKWApIGFuZCBuYW1lc3BhY2UgYWNjZXNzIGFyZVxuXHQgKiBub3QgZm9sbG93ZWQuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVIZXJpdGFnZURlY2xhcmF0aW9ucyAoZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbik6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25bXSB7XG5cdFx0Y29uc3QgeyBoZXJpdGFnZUNsYXVzZXMgfSA9IChkZWNsLm5vZGUgYXMgdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHRzLkludGVyZmFjZURlY2xhcmF0aW9uKTtcblx0XHRpZiAoIWhlcml0YWdlQ2xhdXNlcykge1xuXHRcdFx0cmV0dXJuIFtdO1xuXHRcdH1cblx0XHRjb25zdCBiYXNlczogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbltdID0gW107XG5cdFx0Zm9yIChjb25zdCBjbGF1c2Ugb2YgaGVyaXRhZ2VDbGF1c2VzKSB7XG5cdFx0XHRpZiAoY2xhdXNlLnRva2VuICE9PSB0cy5TeW50YXhLaW5kLkV4dGVuZHNLZXl3b3JkKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBoZXJpdGFnZVR5cGUgb2YgY2xhdXNlLnR5cGVzKSB7XG5cdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGhlcml0YWdlVHlwZS5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGJhc2VOYW1lID0gaGVyaXRhZ2VUeXBlLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdFx0Y29uc3QgYmFzZURlY2wgPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKGJhc2VOYW1lLCBkZWNsLmZpbGUpO1xuXHRcdFx0XHRpZiAoYmFzZURlY2wpIHtcblx0XHRcdFx0XHRiYXNlcy5wdXNoKGJhc2VEZWNsKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBiYXNlcztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4cGFuZCBhIHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbiB0byBhIHNlbGYtY29udGFpbmVkIHR5cGUgc3RyaW5nXG5cdCAqIGZvciBlbWlzc2lvbiBpbnRvIGdlbmVyYXRlZCBmaWxlczogdHlwZSBhbGlhc2VzIHRocm91Z2ggaW5mZXJUeXBlLFxuXHQgKiBjbGFzc2VzIGFuZCBpbnRlcmZhY2VzIHRocm91Z2ggdGhlaXIgKHB1YmxpYywgbm9uLW1ldGhvZCkgZmllbGRzLlxuXHQgKiBOZXN0ZWQgcmVmZXJlbmNlcyByZXNvbHZlIGFnYWluc3QgdGhlIGRlY2xhcmluZyBmaWxlIHdoaWxlIGV4cGFuZGluZy5cblx0ICovXG5cdHByaXZhdGUgZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiAoZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgcmVmZXJlbmNpbmdGaWxlID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9IGRlY2wuZmlsZTtcblx0XHR0cnkge1xuXHRcdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uSW5uZXIoZGVjbCk7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH0gZmluYWxseSB7XG5cdFx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSByZWZlcmVuY2luZ0ZpbGU7XG5cdFx0fVxuXHR9XG5cblx0cHJpdmF0ZSBleHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uSW5uZXIgKGRlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmIChkZWNsLmtpbmQgPT09ICdhbGlhcycpIHtcblx0XHRcdGNvbnN0IGFsaWFzTm9kZSA9IGRlY2wubm9kZSBhcyB0cy5UeXBlQWxpYXNEZWNsYXJhdGlvbjtcblx0XHRcdGNvbnN0IGFsaWFzTmFtZSA9IHRzLmlzSWRlbnRpZmllcihhbGlhc05vZGUubmFtZSkgPyBhbGlhc05vZGUubmFtZS50ZXh0IDogJyc7XG5cdFx0XHRpZiAoYWxpYXNOYW1lICYmIHRoaXMuZXhwYW5kaW5nUmVmZXJlbmNlZEFsaWFzZXMuaGFzKGFsaWFzTmFtZSkpIHtcblx0XHRcdFx0Ly8gU2VsZi1yZWZlcmVudGlhbCBhbGlhcyBjaGFpbiDigJQgYmFpbCBvdXRcblx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdH1cblx0XHRcdGlmIChhbGlhc05hbWUpIHtcblx0XHRcdFx0dGhpcy5leHBhbmRpbmdSZWZlcmVuY2VkQWxpYXNlcy5hZGQoYWxpYXNOYW1lKTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGV4cGFuZGVkID0gdGhpcy5pbmZlclR5cGUoYWxpYXNOb2RlLnR5cGUpO1xuXHRcdFx0aWYgKGFsaWFzTmFtZSkge1xuXHRcdFx0XHR0aGlzLmV4cGFuZGluZ1JlZmVyZW5jZWRBbGlhc2VzLmRlbGV0ZShhbGlhc05hbWUpO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGV4cGFuZGVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IGRlY2xQcm9wZXJ0aWVzID0gdGhpcy5yZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzKGRlY2wpO1xuXHRcdGNvbnN0IHByb3BzID0gQXJyYXkuZnJvbShkZWNsUHJvcGVydGllcy5lbnRyaWVzKCkpLm1hcCgoWyBwcm9wTmFtZSwgaW5mbyBdKSA9PiB7XG5cdFx0XHRjb25zdCBvcHRpb25hbCA9IGluZm8ub3B0aW9uYWwgPyAnPycgOiAnJztcblx0XHRcdHJldHVybiBgJHtwcm9wTmFtZX0ke29wdGlvbmFsfTogJHtpbmZvLnR5cGV9YDtcblx0XHR9KTtcblxuXHRcdGNvbnN0IHJlc3VsdCA9IGB7ICR7cHJvcHMuam9pbignOyAnKX0gfWA7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgc2ltcGxlIChub24tcXVhbGlmaWVkKSB0eXBlIHJlZmVyZW5jZTogaW1wb3J0LWF3YXJlXG5cdCAqIGRlY2xhcmF0aW9uIGV4cGFuc2lvbiBmaXJzdCwgdGhlbiB0aGUgSW5zdGFuY2VUeXBlPHR5cGVvZiBYPiBwYXR0ZXJuLFxuXHQgKiB0aGVuIG1uZW1vbmljYSBncmFwaCB0eXBlczsga25vd24gZ2xvYmFscyBrZWVwIHRoZWlyIGJhcmUgbmFtZSBhbmRcblx0ICogYW55dGhpbmcgZWxzZSBmYWxscyBiYWNrIHRvIGB1bmtub3duYCBzbyBnZW5lcmF0ZWQgZmlsZXMgbmV2ZXIgY2Fycnlcblx0ICogYW4gdW5yZXNvbHZhYmxlIGJhcmUgbmFtZS4gUmV0dXJucyB1bmRlZmluZWQgd2hlbiB0aGUgY2FsbGVyIHNob3VsZFxuXHQgKiBrZWVwIHRoZSBnZW5lcmljIHNwZWxsaW5nIChoYW5kbGVkIHNlcGFyYXRlbHkpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlU2ltcGxlVHlwZVJlZmVyZW5jZSAoXG5cdFx0dHlwZU5hbWU6IHN0cmluZyxcblx0XHR0eXBlQXJncz86IHRzLk5vZGVBcnJheTx0cy5UeXBlTm9kZT4sXG5cdFx0cmVmTm9kZT86IHRzLk5vZGVcblx0KTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBJbXBvcnQtYXdhcmUgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9uIChGMTApXG5cdFx0Y29uc3QgZGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24odHlwZU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0aWYgKGRlY2wpIHtcblx0XHRcdGNvbnN0IGV4cGFuZGVkID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKGRlY2wpO1xuXHRcdFx0aWYgKGV4cGFuZGVkICE9PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0cmV0dXJuIGV4cGFuZGVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgdW5rbm93blJlc3VsdCA9ICd1bmtub3duJztcblx0XHRcdHJldHVybiB1bmtub3duUmVzdWx0O1xuXHRcdH1cblxuXHRcdC8vIE1uZW1vbmljYS1ncmFwaCBpZGVudGl0eSBsYXc6IHBhdGgtYXdhcmUgcmVzb2x1dGlvbiAodmFsdWUgc2NvcGUsXG5cdFx0Ly8gaW1wb3J0cywgbmVhcmVzdC1jaGFpbiwgcm9vdCwgcHJvZ3JhbS13aWRlKS4gQW1iaWd1aXR5IGJldHdlZW5cblx0XHQvLyByZWFsIGdyYXBoIHR5cGVzIGlzIGEgaGFyZCBmYWlsdXJlOyBhIG5hbWUgbm8gZ3JhcGggdHlwZSBjYXJyaWVzXG5cdFx0Ly8gc3RheXMgaW4gdGhlIHBsYWluLVRTIHNvZnQgc2NvcGUgYW5kIGZhbGxzIHRvIGB1bmtub3duYC5cblx0XHRjb25zdCBncmFwaFJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUodHlwZU5hbWUpO1xuXHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHQvLyBIYW5kbGUgSW5zdGFuY2VUeXBlPHR5cGVvZiBYPiBwYXR0ZXJuIC0+IGNvbnZlcnQgdG8gUGFyZW50X1hcblx0XHRcdGlmICh0eXBlTmFtZSA9PT0gJ0luc3RhbmNlVHlwZScgJiYgdHlwZUFyZ3MgJiYgdHlwZUFyZ3MubGVuZ3RoID09PSAxKSB7XG5cdFx0XHRcdGNvbnN0IFsgYXJnIF0gPSB0eXBlQXJncztcblx0XHRcdFx0aWYgKGFyZy5raW5kID09PSB0cy5TeW50YXhLaW5kLlR5cGVRdWVyeSkge1xuXHRcdFx0XHRcdGNvbnN0IHR5cGVRdWVyeSA9IGFyZyBhcyB0cy5UeXBlUXVlcnlOb2RlO1xuXHRcdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIodHlwZVF1ZXJ5LmV4cHJOYW1lKSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcXVlcnlSZXN1bHQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKHR5cGVRdWVyeS5leHByTmFtZS50ZXh0KTtcblx0XHRcdFx0XHRcdGlmIChxdWVyeVJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRcdFx0XHRcdC8vIENvbnZlcnQgZnVsbCBwYXRoIHdpdGggZG90cyB0byB1bmRlcnNjb3JlczogVXNhZ2VzLlVzYWdlRW50cnkgLT4gVXNhZ2VzX1VzYWdlRW50cnlcblx0XHRcdFx0XHRcdFx0cmV0dXJuIHF1ZXJ5UmVzdWx0Lm5vZGUuZnVsbFBhdGgucmVwbGFjZSgvXFwuL2csICdfJyk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRpZiAocXVlcnlSZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0XHRcdFx0XHR0aGlzLnJlY29yZEdyYXBoUmVmZXJlbmNlRXJyb3IodHlwZVF1ZXJ5LmV4cHJOYW1lLnRleHQsIHR5cGVRdWVyeSwgcXVlcnlSZXN1bHQpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0Ly8gTm90IGEga25vd24gbW5lbW9uaWNhIHR5cGUg4oCUIG5vIGJhcmUgZW1pc3Npb25cblx0XHRcdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAoIXR5cGVBcmdzIHx8IHR5cGVBcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHQvLyBDb252ZXJ0IGZ1bGwgcGF0aCB3aXRoIGRvdHMgdG8gdW5kZXJzY29yZXM6IFVzYWdlcy5Vc2FnZUVudHJ5IC0+IFVzYWdlc19Vc2FnZUVudHJ5XG5cdFx0XHRcdHJldHVybiBncmFwaFJlc3VsdC5ub2RlLmZ1bGxQYXRoLnJlcGxhY2UoL1xcLi9nLCAnXycpO1xuXHRcdFx0fVxuXHRcdFx0Ly8gR2VuZXJpYyB1c2Ugb2YgYSBncmFwaCB0eXBlIGtlZXBzIGl0cyBzaW1wbGUgbmFtZTsgdGhlXG5cdFx0XHQvLyBnZW5lcmF0b3IgdXBncmFkZXMgaXQgdG8gdGhlIGZ1bGwtcGF0aCBpbnN0YW5jZSB0eXBlIG5hbWVcblx0XHRcdHJldHVybiBgJHt0eXBlTmFtZX08JHt0eXBlQXJncy5tYXAoYSA9PiB0aGlzLmluZmVyVHlwZShhKSkuam9pbignLCAnKX0+YDtcblx0XHR9XG5cdFx0aWYgKGdyYXBoUmVzdWx0LnN0YXR1cyA9PT0gJ2FtYmlndW91cycpIHtcblx0XHRcdHRoaXMucmVjb3JkR3JhcGhSZWZlcmVuY2VFcnJvcih0eXBlTmFtZSwgcmVmTm9kZSA/PyB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUsIGdyYXBoUmVzdWx0KTtcblx0XHR9XG5cblx0XHRpZiAodHlwZUFyZ3MgJiYgdHlwZUFyZ3MubGVuZ3RoID4gMCkge1xuXHRcdFx0aWYgKEtOT1dOX0dMT0JBTF9UWVBFUy5oYXModHlwZU5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IGdlbmVyaWNSZXN1bHQgPSBgJHt0eXBlTmFtZX08JHt0eXBlQXJncy5tYXAoYSA9PiB0aGlzLmluZmVyVHlwZShhKSkuam9pbignLCAnKX0+YDtcblx0XHRcdFx0cmV0dXJuIGdlbmVyaWNSZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBHZW5lcmljIHJlZmVyZW5jZSB0byBhIG5vbi1nbG9iYWwsIG5vbi1ncmFwaCB0eXBlIGNhbm5vdCBiZVxuXHRcdFx0Ly8gZW1pdHRlZCBiYXJlIGludG8gdGhlIGdlbmVyYXRlZCBmaWxlXG5cdFx0XHRpZiAocmVmTm9kZSkge1xuXHRcdFx0XHR0aGlzLnJlY29yZFBsYWluVHlwZVJlZmVyZW5jZVNpdGUodHlwZU5hbWUsIHJlZk5vZGUpO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cblx0XHRjb25zdCBmYWxsYmFja1Jlc3VsdCA9IHRoaXMudW5yZXNvbHZlZFR5cGVSZWZlcmVuY2VGYWxsYmFjayh0eXBlTmFtZSwgcmVmTm9kZSk7XG5cdFx0cmV0dXJuIGZhbGxiYWNrUmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSBxdWFsaWZpZWQgdHlwZSByZWZlcmVuY2UgKG1vZGVscy5Jbm5lci5DcmF0ZSkgdGhyb3VnaCB0aGVcblx0ICogY3VycmVudCBmaWxlJ3MgbmFtZXNwYWNlIGltcG9ydHMuIFRoZSBjaGFpbidzIGhlYWQgbXVzdCBiZSBhIG5hbWVzcGFjZVxuXHQgKiBpbXBvcnQ7IG1pZGRsZSBzZWdtZW50cyBkZXNjZW5kIHRocm91Z2ggbmFtZXNwYWNlIGRlY2xhcmF0aW9ucywgbmFtZWRcblx0ICogcmUtZXhwb3J0cyBvZiBuYW1lc3BhY2VzLCBhbmQgYGV4cG9ydCAqIGFzIG5zIGZyb20gJ+KApidgIGJhcnJlbHMgKGVhY2hcblx0ICogc2VnbWVudCBjb25zdW1lZCBleGFjdGx5IG9uY2UsIHNvIHRoZSB3YWxrIGNhbm5vdCBjeWNsZSk7IHRoZSBmaW5hbFxuXHQgKiBzZWdtZW50IHJlc29sdmVzIHRvIGEgZGVjbGFyYXRpb24gd2hpY2ggaXMgZXhwYW5kZWQgaW5saW5lLiBXaGVuIHRoZVxuXHQgKiBwcmVjaXNlIHdhbGsgZmluZHMgbm90aGluZywgdGhlIGxlZ2FjeSByaWdodG1vc3QtbmFtZSBsb29rdXAgaW4gdGhlXG5cdCAqIGhlYWQgbW9kdWxlIGtlZXBzIG9uZS1sZXZlbCBmb3JtcyAobW9kZWxzLlR5cGUpIHdvcmtpbmcg4oCUIG5lc3RlZFxuXHQgKiBkZWNsYXJhdGlvbnMgYXJlIHJlY29yZGVkIGJ5IHBsYWluIG5hbWUgdGhlcmUgdG9vLiBSZXR1cm5zIHVuZGVmaW5lZFxuXHQgKiB3aGVuIHRoZSBoZWFkIGlzIG5vdCBhIG5hbWVzcGFjZSBpbXBvcnQgb3Igbm90aGluZyByZXNvbHZlcy5cblx0ICovXG5cdHByaXZhdGUgaW5mZXJRdWFsaWZpZWRUeXBlUmVmZXJlbmNlICh0eXBlUmVmOiB0cy5UeXBlUmVmZXJlbmNlTm9kZSk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCF0cy5pc1F1YWxpZmllZE5hbWUodHlwZVJlZi50eXBlTmFtZSkpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gZmxhdHRlbiB0aGUgcXVhbGlmaWVkIG5hbWUgY2hhaW46IG1vZGVscy5Jbm5lci5DcmF0ZSDihpIgWydtb2RlbHMnLCAnSW5uZXInLCAnQ3JhdGUnXVxuXHRcdGNvbnN0IHNlZ21lbnRzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGxldCBjaGFpbjogdHMuRW50aXR5TmFtZSA9IHR5cGVSZWYudHlwZU5hbWU7XG5cdFx0d2hpbGUgKHRzLmlzUXVhbGlmaWVkTmFtZShjaGFpbikpIHtcblx0XHRcdHNlZ21lbnRzLnVuc2hpZnQoY2hhaW4ucmlnaHQudGV4dCk7XG5cdFx0XHRjaGFpbiA9IGNoYWluLmxlZnQ7XG5cdFx0fVxuXHRcdHNlZ21lbnRzLnVuc2hpZnQoY2hhaW4udGV4dCk7XG5cblx0XHRjb25zdCBuYW1lc3BhY2VJbXBvcnQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKT8uZ2V0KHNlZ21lbnRzWyAwIF0pO1xuXHRcdGlmICghbmFtZXNwYWNlSW1wb3J0IHx8ICFuYW1lc3BhY2VJbXBvcnQuaXNOYW1lc3BhY2UpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKG5hbWVzcGFjZUltcG9ydC5zcGVjaWZpZXIsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0aWYgKCFyZXNvbHV0aW9uIHx8IHJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBkZXNjZW5kIHRoZSBtaWRkbGUgc2VnbWVudHM6IGEgbW9kdWxlIGNvbnRleHQgcmVzb2x2ZXMgdGhlIHNlZ21lbnRcblx0XHQvLyBhcyBhIG5hbWVzcGFjZSBkZWNsYXJhdGlvbiAvIG5hbWVzcGFjZSByZS1leHBvcnQ7IGEgbmFtZXNwYWNlLWJsb2NrXG5cdFx0Ly8gY29udGV4dCByZXNvbHZlcyBpdCBhcyBhIG5lc3RlZCBuYW1lc3BhY2UgZGVjbGFyYXRpb25cblx0XHRsZXQgcXVhbGlmaWVyOiB7IG1vZHVsZVBhdGg6IHN0cmluZzsgYmxvY2s/OiB0cy5Nb2R1bGVCbG9jayB9IHwgdW5kZWZpbmVkID0ge1xuXHRcdFx0bW9kdWxlUGF0aCA6IHJlc29sdXRpb24ucmVzb2x2ZWRQYXRoXG5cdFx0fTtcblx0XHRmb3IgKGxldCBpID0gMTsgaSA8IHNlZ21lbnRzLmxlbmd0aCAtIDEgJiYgcXVhbGlmaWVyOyBpKyspIHtcblx0XHRcdGNvbnN0IHNlZ21lbnQgPSBzZWdtZW50c1sgaSBdO1xuXHRcdFx0aWYgKHF1YWxpZmllci5ibG9jaykge1xuXHRcdFx0XHRjb25zdCBuZXN0ZWQgPSB0aGlzLmZpbmROYW1lc3BhY2VJbkJsb2NrKHF1YWxpZmllci5ibG9jaywgc2VnbWVudCk7XG5cdFx0XHRcdGlmIChuZXN0ZWQ/LmJvZHkgJiYgdHMuaXNNb2R1bGVCbG9jayhuZXN0ZWQuYm9keSkpIHtcblx0XHRcdFx0XHRxdWFsaWZpZXIgPSB7IG1vZHVsZVBhdGggOiBxdWFsaWZpZXIubW9kdWxlUGF0aCwgYmxvY2sgOiBuZXN0ZWQuYm9keSB9O1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHF1YWxpZmllciA9IHVuZGVmaW5lZDtcblx0XHRcdFx0YnJlYWs7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBuYW1lc3BhY2VEZWNsOiB0cy5Nb2R1bGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCA9XG5cdFx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzLmdldChxdWFsaWZpZXIubW9kdWxlUGF0aCk/LmdldChzZWdtZW50KTtcblx0XHRcdGlmIChuYW1lc3BhY2VEZWNsPy5ib2R5ICYmIHRzLmlzTW9kdWxlQmxvY2sobmFtZXNwYWNlRGVjbC5ib2R5KSkge1xuXHRcdFx0XHRxdWFsaWZpZXIgPSB7IG1vZHVsZVBhdGggOiBxdWFsaWZpZXIubW9kdWxlUGF0aCwgYmxvY2sgOiBuYW1lc3BhY2VEZWNsLmJvZHkgfTtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBzdGFyU3BlY2lmaWVyID0gdGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZVN0YXJzLmdldChxdWFsaWZpZXIubW9kdWxlUGF0aCk/LmdldChzZWdtZW50KTtcblx0XHRcdGlmIChzdGFyU3BlY2lmaWVyKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoc3RhclNwZWNpZmllciwgcXVhbGlmaWVyLm1vZHVsZVBhdGgpO1xuXHRcdFx0XHRpZiAobmV4dFJlc29sdXRpb24gJiYgIW5leHRSZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0XHRxdWFsaWZpZXIgPSB7IG1vZHVsZVBhdGggOiBuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGggfTtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Y29uc3QgcmVFeHBvcnRTcGVjaWZpZXIgPSB0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLmdldChxdWFsaWZpZXIubW9kdWxlUGF0aCk/LmdldChzZWdtZW50KTtcblx0XHRcdGlmIChyZUV4cG9ydFNwZWNpZmllcikge1xuXHRcdFx0XHRjb25zdCBuZXh0UmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKHJlRXhwb3J0U3BlY2lmaWVyLCBxdWFsaWZpZXIubW9kdWxlUGF0aCk7XG5cdFx0XHRcdGNvbnN0IHJlRXhwb3J0ZWQ6IHRzLk1vZHVsZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkID1cblx0XHRcdFx0XHRuZXh0UmVzb2x1dGlvbiAmJiAhbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbFxuXHRcdFx0XHRcdFx0PyB0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlcy5nZXQobmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoKT8uZ2V0KHNlZ21lbnQpXG5cdFx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblx0XHRcdFx0aWYgKHJlRXhwb3J0ZWQ/LmJvZHkgJiYgdHMuaXNNb2R1bGVCbG9jayhyZUV4cG9ydGVkLmJvZHkpKSB7XG5cdFx0XHRcdFx0cXVhbGlmaWVyID0geyBtb2R1bGVQYXRoIDogbmV4dFJlc29sdXRpb24hLnJlc29sdmVkUGF0aCwgYmxvY2sgOiByZUV4cG9ydGVkLmJvZHkgfTtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cXVhbGlmaWVyID0gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZpbmFsTmFtZSA9IHNlZ21lbnRzWyBzZWdtZW50cy5sZW5ndGggLSAxIF07XG5cdFx0bGV0IGRlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQ7XG5cdFx0aWYgKHF1YWxpZmllcj8uYmxvY2spIHtcblx0XHRcdGRlY2wgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluQmxvY2socXVhbGlmaWVyLmJsb2NrLCBxdWFsaWZpZXIubW9kdWxlUGF0aCwgZmluYWxOYW1lKTtcblx0XHR9IGVsc2UgaWYgKHF1YWxpZmllcikge1xuXHRcdFx0ZGVjbCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUocXVhbGlmaWVyLm1vZHVsZVBhdGgsIGZpbmFsTmFtZSwgMCk7XG5cdFx0fVxuXHRcdC8vIGxlZ2FjeSBmYWxsYmFjazogcmlnaHRtb3N0IG5hbWUgYW55d2hlcmUgaW4gdGhlIGhlYWQgbW9kdWxlXG5cdFx0Ly8gKG5hbWVzcGFjZS1uZXN0ZWQgZGVjbGFyYXRpb25zIGFyZSBhbHNvIHJlY29yZGVkIGJ5IHBsYWluIG5hbWUpXG5cdFx0aWYgKCFkZWNsKSB7XG5cdFx0XHRkZWNsID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZShyZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgZmluYWxOYW1lLCAwKTtcblx0XHR9XG5cdFx0aWYgKCFkZWNsKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IGV4cGFuZGVkID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKGRlY2wpO1xuXHRcdHJldHVybiBleHBhbmRlZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGaW5kIGEgbmFtZXNwYWNlIGRlY2xhcmF0aW9uIGJ5IG5hbWUgZGlyZWN0bHkgaW5zaWRlIGEgbW9kdWxlIGJsb2NrLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kTmFtZXNwYWNlSW5CbG9jayAoYmxvY2s6IHRzLk1vZHVsZUJsb2NrLCBuYW1lOiBzdHJpbmcpOiB0cy5Nb2R1bGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2YgYmxvY2suc3RhdGVtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzTW9kdWxlRGVjbGFyYXRpb24oc3RhdGVtZW50KSAmJiB0cy5pc0lkZW50aWZpZXIoc3RhdGVtZW50Lm5hbWUpICYmXG5cdFx0XHRcdHN0YXRlbWVudC5uYW1lLnRleHQgPT09IG5hbWUpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0ID0gc3RhdGVtZW50O1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpbmQgYSBuYW1lZCB0eXBlIGRlY2xhcmF0aW9uIChhbGlhcywgY2xhc3MsIGludGVyZmFjZSkgZGlyZWN0bHkgaW5zaWRlXG5cdCAqIGEgbmFtZXNwYWNlIGJsb2NrIOKAlCB0aGUgZmluYWwgc2VnbWVudCBvZiBhIGRlc2NlbmRlZCBxdWFsaWZpZWQgY2hhaW4uXG5cdCAqL1xuXHRwcml2YXRlIGZpbmRSZWZlcmVuY2VkVHlwZUluQmxvY2sgKFxuXHRcdGJsb2NrOiB0cy5Nb2R1bGVCbG9jayxcblx0XHRmaWxlUGF0aDogc3RyaW5nLFxuXHRcdG5hbWU6IHN0cmluZ1xuXHQpOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRmb3IgKGNvbnN0IHN0YXRlbWVudCBvZiBibG9jay5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAodHMuaXNUeXBlQWxpYXNEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmIHRzLmlzSWRlbnRpZmllcihzdGF0ZW1lbnQubmFtZSkgJiZcblx0XHRcdFx0c3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZSkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQ6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gPSB7IGtpbmQgOiAnYWxpYXMnLCBub2RlIDogc3RhdGVtZW50LCBmaWxlIDogZmlsZVBhdGggfTtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc0NsYXNzRGVjbGFyYXRpb24oc3RhdGVtZW50KSAmJiBzdGF0ZW1lbnQubmFtZSAmJiBzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiA9IHsga2luZCA6ICdjbGFzcycsIG5vZGUgOiBzdGF0ZW1lbnQsIGZpbGUgOiBmaWxlUGF0aCB9O1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzSW50ZXJmYWNlRGVjbGFyYXRpb24oc3RhdGVtZW50KSAmJiB0cy5pc0lkZW50aWZpZXIoc3RhdGVtZW50Lm5hbWUpICYmXG5cdFx0XHRcdHN0YXRlbWVudC5uYW1lLnRleHQgPT09IG5hbWUpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0OiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uID0geyBraW5kIDogJ2ludGVyZmFjZScsIG5vZGUgOiBzdGF0ZW1lbnQsIGZpbGUgOiBmaWxlUGF0aCB9O1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEZhbGxiYWNrIGZvciBhIHR5cGUtcmVmZXJlbmNlIG5hbWUgdGhhdCByZXNvbHZlcyB0byBubyBkZWNsYXJhdGlvbiBhbmRcblx0ICogbm8gZ3JhcGggdHlwZToga25vd24gZ2xvYmFscyBrZWVwIHRoZWlyIGJhcmUgbmFtZSAodGhleSByZXNvbHZlIHdpdGhvdXRcblx0ICogYW4gaW1wb3J0KTsgZXZlcnl0aGluZyBlbHNlIGJlY29tZXMgYHVua25vd25gIHNvIGdlbmVyYXRlZCB0eXBlcy50c1xuXHQgKiBuZXZlciBjYXJyaWVzIGFuIHVucmVzb2x2YWJsZSBiYXJlIG5hbWUgKFJFQURNRSdzIGRvY3VtZW50ZWQgYmVoYXZpb3IpXG5cdCAqIGFuZCB0aGUgc2l0ZSBpcyByZWNvcmRlZCBmb3IgdGhlIHBsYWluLVRTIGFtYmlndWl0eSB2YWxpZGF0aW9uLlxuXHQgKi9cblx0cHJpdmF0ZSB1bnJlc29sdmVkVHlwZVJlZmVyZW5jZUZhbGxiYWNrICh0eXBlTmFtZTogc3RyaW5nLCByZWZOb2RlPzogdHMuTm9kZSk6IHN0cmluZyB7XG5cdFx0aWYgKEtOT1dOX0dMT0JBTF9UWVBFUy5oYXModHlwZU5hbWUpKSB7XG5cdFx0XHRyZXR1cm4gdHlwZU5hbWU7XG5cdFx0fVxuXHRcdGlmIChyZWZOb2RlKSB7XG5cdFx0XHR0aGlzLnJlY29yZFBsYWluVHlwZVJlZmVyZW5jZVNpdGUodHlwZU5hbWUsIHJlZk5vZGUpO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSAndW5rbm93bic7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgb25lIGRlZmluZSgpL2xhenkoKS9AZGVjb3JhdGUoKSBzaXRlIHVuZGVyIGl0cyBydW50aW1lXG5cdCAqIG5hbWVzcGFjZSBrZXkuIFR3byBzaXRlcyBpbiBvbmUgbmFtZXNwYWNlIGFyZSBhIHNhbWUtbmFtZXNwYWNlXG5cdCAqIGR1cGxpY2F0ZSAodGhlIHJ1bnRpbWUgdGhyb3dzIEFMUkVBRFlfREVDTEFSRUQpOyBldmVyeSBzaXRlIGlzIGtlcHRcblx0ICogc28gdGhlIGZhaWx1cmUgY2FuIHJlcG9ydCBhbGwgbG9jYXRpb25zLlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmREZWZpbmVTaXRlIChuYW1lc3BhY2VLZXk6IHN0cmluZywgbG9jYXRpb246IHN0cmluZyk6IHZvaWQge1xuXHRcdGxldCBzaXRlcyA9IHRoaXMuZGVmaW5lU2l0ZXMuZ2V0KG5hbWVzcGFjZUtleSk7XG5cdFx0aWYgKCFzaXRlcykge1xuXHRcdFx0c2l0ZXMgPSBbXTtcblx0XHRcdHRoaXMuZGVmaW5lU2l0ZXMuc2V0KG5hbWVzcGFjZUtleSwgc2l0ZXMpO1xuXHRcdH1cblx0XHRpZiAoIXNpdGVzLmluY2x1ZGVzKGxvY2F0aW9uKSkge1xuXHRcdFx0c2l0ZXMucHVzaChsb2NhdGlvbik7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEZhdGFsIHJlc29sdXRpb24gZmFpbHVyZXMgKGhhcmQtZmFpbCBsYXcpOiBzYW1lLW5hbWVzcGFjZSBkdXBsaWNhdGVcblx0ICogbW5lbW9uaWNhIGRlZmluaXRpb25zIHBsdXMgYW1iaWd1b3VzL3VucmVzb2x2ZWQgbW5lbW9uaWNhLWdyYXBoXG5cdCAqIHJlZmVyZW5jZXMuIFRoZSBDTEkgcHJpbnRzIGV2ZXJ5IGxvY2F0aW9uIGFuZCB3cml0ZXMgbm8gb3V0cHV0LlxuXHQgKi9cblx0Z2V0UmVzb2x1dGlvbkVycm9ycyAoKTogUmVzb2x1dGlvbkVycm9yW10ge1xuXHRcdHRoaXMudmFsaWRhdGVMb29rdXBSZWZlcmVuY2VzKCk7XG5cdFx0dGhpcy52YWxpZGF0ZVBsYWluVHlwZVJlZmVyZW5jZXMoKTtcblx0XHRjb25zdCBlcnJvcnM6IFJlc29sdXRpb25FcnJvcltdID0gW107XG5cdFx0Zm9yIChjb25zdCBbIG5hbWVzcGFjZUtleSwgc2l0ZXMgXSBvZiB0aGlzLmRlZmluZVNpdGVzKSB7XG5cdFx0XHRpZiAoc2l0ZXMubGVuZ3RoIDwgMikge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGRpc3BsYXlOYW1lID0gbmFtZXNwYWNlS2V5LnJlcGxhY2UoL15bXjpdKzo6LywgJycpO1xuXHRcdFx0Y29uc3QgbWVzc2FnZSA9IGBEdXBsaWNhdGUgZGVmaW5pdGlvbiBvZiAnJHtkaXNwbGF5TmFtZX0nIGluIG9uZSBuYW1lc3BhY2Ug4oCUIGAgK1xuXHRcdFx0XHQndGhlIG1uZW1vbmljYSBydW50aW1lIHdvdWxkIHRocm93IEFMUkVBRFlfREVDTEFSRUQnO1xuXHRcdFx0ZXJyb3JzLnB1c2goeyBtZXNzYWdlLCBsb2NhdGlvbnMgOiBbIC4uLnNpdGVzIF0gfSk7XG5cdFx0fVxuXHRcdGZvciAoY29uc3QgZXJyb3Igb2YgdGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycykge1xuXHRcdFx0ZXJyb3JzLnB1c2goZXJyb3IpO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBlcnJvcnM7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgcmVmZXJlbmNlIHRvIGEgbW5lbW9uaWNhIGdyYXBoIHR5cGUgbmFtZSwgaW1wb3J0LWF3YXJlIGFuZFxuXHQgKiBwYXRoLWF3YXJlICh0aGUgaGFyZC1mYWlsIGlkZW50aXR5IGxhdywgbWlycm9yaW5nIHRoZSBydW50aW1lKTpcblx0ICogICAxLiB2YWx1ZSBzY29wZSDigJQgYSB0cmFja2VkIHRvcC1sZXZlbCBiaW5kaW5nIGluIHRoZSByZWZlcmVuY2luZyBmaWxlXG5cdCAqICAgICAgKGBjb25zdCBBZGRyZXNzID0gVXNlci5kZWZpbmUoJ0FkZHJlc3MnLCDigKYpYCksXG5cdCAqICAgMi4gaW1wb3J0IHNjb3BlIOKAlCBhIGJpbmRpbmcgZXhwb3J0ZWQgZnJvbSBhIG1vZHVsZSB0aGlzIGZpbGUgaW1wb3J0c1xuXHQgKiAgICAgIChiYXJyZWxzIGNoYXNlZCksXG5cdCAqICAgMy4gbmVhcmVzdC1jaGFpbiDigJQgdGhlIGFuY2hvciB0eXBlJ3Mgb3duIHN1YnR5cGVzIGZpcnN0LCB0aGVuIGVhY2hcblx0ICogICAgICBhbmNlc3RvciBsZXZlbCAocmVsYXRpdmUtZmlyc3QpLFxuXHQgKiAgIDQuIHJvb3Qg4oCUIHJvb3RzIG9mIHRoZSBhbmNob3IncyBjb2xsZWN0aW9uLFxuXHQgKiAgIDUuIHByb2dyYW0td2lkZSDigJQgb25seSB3aGVuIGV4YWN0bHkgb25lIHR5cGUgY2FycmllcyB0aGUgbmFtZS5cblx0ICogQW1iaWd1aXR5IChzZXZlcmFsIGNhbmRpZGF0ZXMgYW5kIG5vdGhpbmcgZGlzYW1iaWd1YXRlcykgYW5kIGFic2VuY2Vcblx0ICogYXJlIGJvdGggcmV0dXJuZWQgYXMgc3VjaCDigJQgdGhlIGNhbGxlciByZWNvcmRzIGEgaGFyZCBmYWlsdXJlOyBhIGJhcmVcblx0ICogZmlyc3QtbWF0Y2ggbmFtZSBpcyBuZXZlciBlbWl0dGVkLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlR3JhcGhUeXBlTmFtZSAobmFtZTogc3RyaW5nKTogR3JhcGhUeXBlUmVmZXJlbmNlUmVzdWx0IHtcblx0XHQvLyAxLiB2YWx1ZSBzY29wZSBpbiB0aGUgcmVmZXJlbmNpbmcgZmlsZSBpdHNlbGZcblx0XHRjb25zdCBsb2NhbEJpbmRpbmcgPSB0aGlzLmZpbGVHcmFwaEJpbmRpbmdzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGxvY2FsQmluZGluZykge1xuXHRcdFx0Y29uc3Qgbm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUobG9jYWxCaW5kaW5nKTtcblx0XHRcdGlmIChub2RlKSB7XG5cdFx0XHRcdGNvbnN0IHZhbHVlUmVzdWx0OiBHcmFwaFR5cGVSZWZlcmVuY2VSZXN1bHQgPSB7IHN0YXR1cyA6ICd1bmlxdWUnLCBub2RlIH07XG5cdFx0XHRcdHJldHVybiB2YWx1ZVJlc3VsdDtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyAyLiBpbXBvcnQgc2NvcGUg4oCUIHRoZSBpbXBvcnRlZCBtb2R1bGUncyBleHBvcnRlZCBiaW5kaW5nXG5cdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChpbXBvcnRlZCAmJiAhaW1wb3J0ZWQuaXNOYW1lc3BhY2UpIHtcblx0XHRcdGNvbnN0IHJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShpbXBvcnRlZC5zcGVjaWZpZXIsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRpZiAocmVzb2x1dGlvbiAmJiAhcmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdGNvbnN0IGZ1bGxQYXRoID0gdGhpcy5maW5kR3JhcGhCaW5kaW5nSW5Nb2R1bGUocmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIGltcG9ydGVkLm9yaWdpbmFsTmFtZSwgMCk7XG5cdFx0XHRcdGlmIChmdWxsUGF0aCkge1xuXHRcdFx0XHRcdGNvbnN0IG5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGZ1bGxQYXRoKTtcblx0XHRcdFx0XHRpZiAobm9kZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgaW1wb3J0UmVzdWx0OiBHcmFwaFR5cGVSZWZlcmVuY2VSZXN1bHQgPSB7IHN0YXR1cyA6ICd1bmlxdWUnLCBub2RlIH07XG5cdFx0XHRcdFx0XHRyZXR1cm4gaW1wb3J0UmVzdWx0O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIDMtNS4gY2hhaW4gLyByb290IC8gcHJvZ3JhbS13aWRlIHRpZXJzXG5cdFx0Y29uc3QgcmVzdWx0ID0gcmVzb2x2ZUdyYXBoVHlwZVJlZmVyZW5jZSh0aGlzLmdyYXBoLCBuYW1lLCB0aGlzLmN1cnJlbnRHcmFwaEFuY2hvcik7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGaW5kIGEgZ3JhcGggY29uc3RydWN0b3IgYmluZGluZyBleHBvcnRlZCBieSBhIHJlc29sdmVkIG1vZHVsZSxcblx0ICogY2hhc2luZyByZS1leHBvcnQgYmFycmVscyB3aXRoIGEgYm91bmRlZCBkZXB0aC5cblx0ICovXG5cdHByaXZhdGUgZmluZEdyYXBoQmluZGluZ0luTW9kdWxlIChtb2R1bGVQYXRoOiBzdHJpbmcsIG5hbWU6IHN0cmluZywgZGVwdGg6IG51bWJlcik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKGRlcHRoID4gTUFYX1JFRVhQT1JUX0NIQVNFX0RFUFRIKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IGRpcmVjdCA9IHRoaXMuZmlsZUdyYXBoQmluZGluZ3MuZ2V0KG1vZHVsZVBhdGgpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGRpcmVjdCkge1xuXHRcdFx0cmV0dXJuIGRpcmVjdDtcblx0XHR9XG5cblx0XHRjb25zdCByZUV4cG9ydHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLmdldChtb2R1bGVQYXRoKTtcblx0XHRjb25zdCByZUV4cG9ydFNwZWNpZmllciA9IHJlRXhwb3J0cz8uZ2V0KG5hbWUpO1xuXHRcdGlmIChyZUV4cG9ydFNwZWNpZmllcikge1xuXHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShyZUV4cG9ydFNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRpZiAobmV4dFJlc29sdXRpb24gJiYgIW5leHRSZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRHcmFwaEJpbmRpbmdJbk1vZHVsZShuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIG5hbWUsIGRlcHRoICsgMSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGNvbnN0IHN0YXJzID0gdGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydFN0YXJzLmdldChtb2R1bGVQYXRoKTtcblx0XHRpZiAoc3RhcnMpIHtcblx0XHRcdGZvciAoY29uc3Qgc3RhclNwZWNpZmllciBvZiBzdGFycykge1xuXHRcdFx0XHRjb25zdCBuZXh0UmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKHN0YXJTcGVjaWZpZXIsIG1vZHVsZVBhdGgpO1xuXHRcdFx0XHRpZiAoIW5leHRSZXNvbHV0aW9uIHx8IG5leHRSZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBmb3VuZCA9IHRoaXMuZmluZEdyYXBoQmluZGluZ0luTW9kdWxlKG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgbmFtZSwgZGVwdGggKyAxKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBWYWxpZGF0ZSBsaXRlcmFsIGxvb2t1cCgpIHBhdGhzIHJlY29yZGVkIGR1cmluZyB0aGUgdXNhZ2VzIHBhc3Ncblx0ICogYWdhaW5zdCB0aGUgY29tcGxldGUgZ3JhcGguIEEgbG9va3VwIHBhdGggbWF0Y2hpbmcgbm8gdHlwZSBpcyB3aGF0IHRoZVxuXHQgKiBydW50aW1lIGFuc3dlcnMgd2l0aCBgdW5kZWZpbmVkYCDigJQgdGhlIFR5cGVFcnJvciBhcnJpdmVzIG9uZSBsaW5lXG5cdCAqIGxhdGVyIGF0IHRoZSBgbmV3YCDigJQgc28gaXQgam9pbnMgdGhlIGhhcmQtZmFpbCBsYXcuIFRoZSByZWxhdGl2ZS1maXJzdFxuXHQgKiBzdGVwIGFscmVhZHkgcmFuIGluc2lkZSByZXNvbHZlTG9va3VwUGF0aDsgd2hhdGV2ZXIgd2FzIHJlY29yZGVkIGlzXG5cdCAqIHRoZSByb290LXJlc29sdXRpb24gcmVzdWx0LCBzbyBhIHBsYWluIGZpbmRUeXBlIGNoZWNrIGlzIHRoZSBleGFjdFxuXHQgKiBydW50aW1lIGxhdy4gU2FtZS1uYW1lZCB0eXBlcyBlbHNld2hlcmUgaW4gdGhlIGdyYXBoIGFyZSBsaXN0ZWQgYXNcblx0ICogZGlkLXlvdS1tZWFuIGNhbmRpZGF0ZXMuIFJ1bnMgb25jZSBwZXIgdXNhZ2VzIHBhc3MgKHJlLWFybWVkIGJ5XG5cdCAqIHJlc2V0VXNhZ2VzKTsgbm9uLWxpdGVyYWwgbG9va3VwIGFyZ3VtZW50cyBhcmUgbmV2ZXIgcmVjb3JkZWQgYW5kXG5cdCAqIHN0YXkgYmVzdC1lZmZvcnQuXG5cdCAqL1xuXHRwcml2YXRlIHZhbGlkYXRlTG9va3VwUmVmZXJlbmNlcyAoKTogdm9pZCB7XG5cdFx0aWYgKHRoaXMubG9va3VwUmVmZXJlbmNlc1ZhbGlkYXRlZCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR0aGlzLmxvb2t1cFJlZmVyZW5jZXNWYWxpZGF0ZWQgPSB0cnVlO1xuXHRcdC8vIGdyb3VwIHNpdGVzIGJ5IHBhdGg6IGV2ZXJ5IGZhaWxpbmcgc2l0ZSBvZiB0aGUgc2FtZSBwYXRoIGlzIGxpc3RlZFxuXHRcdGNvbnN0IHNpdGVzQnlQYXRoID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZ1tdPigpO1xuXHRcdGZvciAoY29uc3QgcmVmIG9mIHRoaXMubG9va3VwUmVmZXJlbmNlcykge1xuXHRcdFx0Y29uc3Qgc2l0ZXMgPSBzaXRlc0J5UGF0aC5nZXQocmVmLnBhdGgpID8/IFtdO1xuXHRcdFx0c2l0ZXMucHVzaChyZWYubG9jYXRpb24pO1xuXHRcdFx0c2l0ZXNCeVBhdGguc2V0KHJlZi5wYXRoLCBzaXRlcyk7XG5cdFx0fVxuXHRcdGZvciAoY29uc3QgWyB0eXBlUGF0aCwgc2l0ZXMgXSBvZiBzaXRlc0J5UGF0aCkge1xuXHRcdFx0aWYgKHRoaXMuZ3JhcGguZmluZFR5cGUodHlwZVBhdGgpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Ly8gZGlkLXlvdS1tZWFuOiB0eXBlcyBjYXJyeWluZyB0aGUgc2FtZSBuYW1lIGFueXdoZXJlIGluIHRoZVxuXHRcdFx0Ly8gZ3JhcGggKG5ldmVyIGEgZmlyc3QtbWF0Y2ggcGljayDigJQgdGhlIGZ1bGwgbGlzdCBvbmx5KVxuXHRcdFx0Y29uc3QgdW5wcmVmaXhlZCA9IHR5cGVQYXRoLnJlcGxhY2UoL15bXjpdKzo6LywgJycpO1xuXHRcdFx0Y29uc3QgbGFzdFNlZ21lbnQgPSB1bnByZWZpeGVkLnNwbGl0KCcuJykucG9wKCkgPz8gdW5wcmVmaXhlZDtcblx0XHRcdGNvbnN0IGNhbmRpZGF0ZXMgPSB0aGlzLmdyYXBoLmdldEFsbFR5cGVzKCkuZmlsdGVyKHQgPT4gdC5uYW1lID09PSBsYXN0U2VnbWVudCk7XG5cdFx0XHRpZiAoY2FuZGlkYXRlcy5sZW5ndGggPT09IDApIHtcblx0XHRcdFx0Y29uc3Qgbm9uZUVycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7XG5cdFx0XHRcdFx0bWVzc2FnZSA6IGBVbnJlc29sdmVkIGxvb2t1cCBvZiBtbmVtb25pY2EgdHlwZSAnJHt0eXBlUGF0aH0nOiBubyB0eXBlIGF0IHRoYXQgcGF0aCDigJQgYCArXG5cdFx0XHRcdFx0XHQndGhlIHJ1bnRpbWUgd291bGQgcmV0dXJuIHVuZGVmaW5lZCcsXG5cdFx0XHRcdFx0bG9jYXRpb25zIDogc2l0ZXMsXG5cdFx0XHRcdH07XG5cdFx0XHRcdHRoaXMuZ3JhcGhSZWZlcmVuY2VFcnJvcnMucHVzaChub25lRXJyb3IpO1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGNhbmRpZGF0ZUxvY2F0aW9ucyA9IGNhbmRpZGF0ZXMubWFwKG4gPT4gYCR7bi5zb3VyY2VGaWxlfToke24ubGluZX06JHtuLmNvbHVtbn1gKTtcblx0XHRcdGNvbnN0IGNhbmRpZGF0ZVBhdGhzID0gY2FuZGlkYXRlcy5tYXAobiA9PiBuLmZ1bGxQYXRoKS5qb2luKCcsICcpO1xuXHRcdFx0Y29uc3QgYW1iaWd1b3VzRXJyb3I6IFJlc29sdXRpb25FcnJvciA9IHtcblx0XHRcdFx0bWVzc2FnZSA6IGBVbnJlc29sdmVkIGxvb2t1cCBvZiBtbmVtb25pY2EgdHlwZSAnJHt0eXBlUGF0aH0nOiB0aGUgcnVudGltZSB3b3VsZCByZXR1cm4gYCArXG5cdFx0XHRcdFx0YHVuZGVmaW5lZCDigJQgJHtjYW5kaWRhdGVzLmxlbmd0aH0gZ3JhcGggdHlwZShzKSBjYXJyeSB0aGUgbmFtZSBgICtcblx0XHRcdFx0XHRgb2ZmLXJvb3QgKCR7Y2FuZGlkYXRlUGF0aHN9KTsgdXNlIHRoZSBmdWxsIGRvdHRlZCBwYXRoYCxcblx0XHRcdFx0bG9jYXRpb25zIDogWyAuLi5zaXRlcywgLi4uY2FuZGlkYXRlTG9jYXRpb25zIF0sXG5cdFx0XHR9O1xuXHRcdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKGFtYmlndW91c0Vycm9yKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGEgcGxhaW4tVFMgdHlwZSByZWZlcmVuY2Ugc2l0ZSB0aGF0IHJlc29sdmVkIHRvIG5vdGhpbmcgYW5kXG5cdCAqIGZlbGwgYmFjayB0byBgdW5rbm93bmAsIGZvciB0aGUgbGF6aWx5LXJ1biBhbWJpZ3VpdHkgdmFsaWRhdGlvbi5cblx0ICogRGVkdXBlZCBieSAobmFtZSwgbG9jYXRpb24pOiBpbmZlclR5cGUgY2FuIHZpc2l0IHRoZSBzYW1lIG5vZGUgbW9yZVxuXHQgKiB0aGFuIG9uY2UgcGVyIHBhc3MgKGNvbnN0cnVjdG9yIHBhcmFtcyArIHByb3BlcnR5IGluZmVyZW5jZSkuXG5cdCAqL1xuXHRwcml2YXRlIHJlY29yZFBsYWluVHlwZVJlZmVyZW5jZVNpdGUgKG5hbWU6IHN0cmluZywgcmVmTm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gdGhpcy5ub2RlTG9jYXRpb24ocmVmTm9kZSk7XG5cdFx0Y29uc3QgZmlsZSA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRjb25zdCBhbHJlYWR5ID0gdGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzLnNvbWUoKHJlZikgPT4gcmVmLm5hbWUgPT09IG5hbWUgJiYgcmVmLmxvY2F0aW9uID09PSBsb2NhdGlvbik7XG5cdFx0aWYgKGFscmVhZHkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0dGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzLnB1c2goeyBuYW1lLCBsb2NhdGlvbiwgZmlsZSB9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBQcm9qZWN0LXNvdXJjZSBkZWNsYXJhdGlvbiBmaWxlcyBjYXJyeWluZyBgbmFtZWAg4oCUIG9uZSBlbnRyeSBwZXJcblx0ICogZmlsZSwgc28gc2FtZS1maWxlIGludGVyZmFjZSBtZXJnaW5nIGNvdW50cyBvbmNlIChub3QgYW1iaWd1b3VzKS5cblx0ICogRXh0ZXJuYWwvYW1iaWVudCBkZWNsYXJhdGlvbnMgKC5kLnRzLCBhbnl0aGluZyB1bmRlciBub2RlX21vZHVsZXMpXG5cdCAqIG5ldmVyIGNvdW50OiBhIHVzZXItbG9jYWwgZGVjbGFyYXRpb24gYWx3YXlzIHdpbnMgb3ZlciBhIHBhY2thZ2UtXG5cdCAqIGRlY2xhcmVkIHNhbWUtbmFtZWQgdHlwZSwgc28gYW4gZXh0ZXJuYWwgY29sbGlzaW9uIHN0YXlzIHNvZnQuXG5cdCAqL1xuXHRwcml2YXRlIHBsYWluVHlwZURlY2xhcmF0aW9uRmlsZXMgKG5hbWU6IHN0cmluZyk6IHN0cmluZ1tdIHtcblx0XHRjb25zdCBmaWxlczogc3RyaW5nW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IFsgZmlsZSwgZGVjbHMgXSBvZiB0aGlzLnJlZmVyZW5jZWRUeXBlRGVjbHMpIHtcblx0XHRcdGlmICghdGhpcy5pc0V4dGVybmFsRGVjbEZpbGUoZmlsZSkgJiYgZGVjbHMuaGFzKG5hbWUpKSB7XG5cdFx0XHRcdGZpbGVzLnB1c2goZmlsZSk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiBmaWxlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBWYWxpZGF0ZSBwbGFpbi1UUyB0eXBlIHJlZmVyZW5jZSBzaXRlcyByZWNvcmRlZCBkdXJpbmcgdGhlIHVzYWdlc1xuXHQgKiBwYXNzIGFnYWluc3QgdGhlIGNvbXBsZXRlIGRlY2xhcmF0aW9uIG1hcC4gQSBuYW1lIGRlY2xhcmVkIGluXG5cdCAqIHNldmVyYWwgcHJvamVjdC1zb3VyY2UgZmlsZXMg4oCUIHdpdGggbm8gaW1wb3J0IGluIHRoZSByZWZlcmVuY2luZ1xuXHQgKiBmaWxlIHRvIGFuY2hvciBpdCDigJQgaXMgYW1iaWd1b3VzOiBzaWxlbnRseSBlbWl0dGluZyBgdW5rbm93bmAgd291bGRcblx0ICogaGlkZSBhIHJlYWwgdHlwZSB0aGUgYXV0aG9yIG1lYW50LCBzbyBpdCBqb2lucyB0aGUgaGFyZC1mYWlsIGxhd1xuXHQgKiAodGhlIHBsYWluLVRTIHRpZXIgb2YgdGhlIHNhbWUgaWRlbnRpdHkgbGF3IGFzIGdyYXBoIHJlZmVyZW5jZXMpLlxuXHQgKiBBYnNlbmNlIChnaG9zdCBuYW1lcykgYW5kIGV4dGVybmFsIGNvbGxpc2lvbnMgc3RheSBzb2Z0IGB1bmtub3duYC5cblx0ICogUnVucyBvbmNlIHBlciB1c2FnZXMgcGFzcyAocmUtYXJtZWQgYnkgcmVzZXRVc2FnZXMpLCBtaXJyb3Jpbmdcblx0ICogdmFsaWRhdGVMb29rdXBSZWZlcmVuY2VzOiByZWNvcmRpbmcgaGFwcGVucyBvbiBldmVyeSBwYXNzLCBidXQgb25seVxuXHQgKiB0aGUgdXNhZ2VzIHBhc3Mgc2VlcyB0aGUgY29tcGxldGUgZGVjbGFyYXRpb24gbWFwLlxuXHQgKi9cblx0cHJpdmF0ZSB2YWxpZGF0ZVBsYWluVHlwZVJlZmVyZW5jZXMgKCk6IHZvaWQge1xuXHRcdGlmICh0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXNWYWxpZGF0ZWQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0dGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzVmFsaWRhdGVkID0gdHJ1ZTtcblx0XHRjb25zdCBzaXRlc0J5TmFtZSA9IG5ldyBNYXA8c3RyaW5nLCB7IG5hbWU6IHN0cmluZzsgbG9jYXRpb246IHN0cmluZzsgZmlsZTogc3RyaW5nIH1bXT4oKTtcblx0XHRmb3IgKGNvbnN0IHJlZiBvZiB0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXMpIHtcblx0XHRcdGNvbnN0IHNpdGVzID0gc2l0ZXNCeU5hbWUuZ2V0KHJlZi5uYW1lKSA/PyBbXTtcblx0XHRcdHNpdGVzLnB1c2gocmVmKTtcblx0XHRcdHNpdGVzQnlOYW1lLnNldChyZWYubmFtZSwgc2l0ZXMpO1xuXHRcdH1cblx0XHRmb3IgKGNvbnN0IFsgbmFtZSwgc2l0ZXMgXSBvZiBzaXRlc0J5TmFtZSkge1xuXHRcdFx0Ly8gYW4gaW1wb3J0IGJpbmRpbmcgaW4gdGhlIHJlZmVyZW5jaW5nIGZpbGUgYW5jaG9ycyB0aGUgbmFtZSDigJRcblx0XHRcdC8vIHRoZSBhdXRob3IgYWxyZWFkeSBkaXNhbWJpZ3VhdGVkICh0aGUgaW1wb3J0IG1heSBqdXN0IHBvaW50XG5cdFx0XHQvLyBhdCBhbiB1bmFuYWx5emFibGUgZXh0ZXJuYWwgbW9kdWxlLCB3aGljaCBzdGF5cyBzb2Z0KVxuXHRcdFx0Y29uc3QgdW5hbmNob3JlZCA9IHNpdGVzLmZpbHRlcigoc2l0ZSkgPT4gIXRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldChzaXRlLmZpbGUpPy5oYXMobmFtZSkpO1xuXHRcdFx0aWYgKHVuYW5jaG9yZWQubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZGVjbEZpbGVzID0gdGhpcy5wbGFpblR5cGVEZWNsYXJhdGlvbkZpbGVzKG5hbWUpO1xuXHRcdFx0aWYgKGRlY2xGaWxlcy5sZW5ndGggPCAyKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbWVzc2FnZSA9IGBBbWJpZ3VvdXMgcmVmZXJlbmNlIHRvIHR5cGUgJyR7bmFtZX0nOiAke2RlY2xGaWxlcy5sZW5ndGh9IGRlY2xhcmF0aW9ucyBgICtcblx0XHRcdFx0J3NoYXJlIHRoZSBuYW1lIGFuZCBubyBpbXBvcnQgZGlzYW1iaWd1YXRlcyDigJQgaW1wb3J0IHRoZSBvbmUgeW91IG1lYW4nO1xuXHRcdFx0Y29uc3QgZGVjbExvY2F0aW9ucyA9IGRlY2xGaWxlcy5tYXAoKGZpbGUpID0+IHRoaXMucGxhaW5EZWNsTG9jYXRpb24oZmlsZSwgbmFtZSkpO1xuXHRcdFx0Y29uc3QgZXJyb3I6IFJlc29sdXRpb25FcnJvciA9IHtcblx0XHRcdFx0bWVzc2FnZSxcblx0XHRcdFx0bG9jYXRpb25zIDogWyAuLi51bmFuY2hvcmVkLm1hcCgoc2l0ZSkgPT4gc2l0ZS5sb2NhdGlvbiksIC4uLmRlY2xMb2NhdGlvbnMgXVxuXHRcdFx0fTtcblx0XHRcdHRoaXMuZ3JhcGhSZWZlcmVuY2VFcnJvcnMucHVzaChlcnJvcik7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIGBmaWxlOmxpbmU6Y29sdW1uYCBvZiBhIHJlY29yZGVkIGRlY2xhcmF0aW9uLCBmb3IgdGhlIGFtYmlndWl0eVxuXHQgKiByZXBvcnQuIE5vZGVzIHJlY29yZGVkIGR1cmluZyB0cmF2ZXJzYWwga2VlcCB0aGVpciBwb3NpdGlvbnM7IGFcblx0ICogc3ludGhldGljL3VucG9zaXRpb25lZCBub2RlIGZhbGxzIGJhY2sgdG8gdGhlIGZpbGUgaXRzZWxmLlxuXHQgKi9cblx0cHJpdmF0ZSBwbGFpbkRlY2xMb2NhdGlvbiAoZmlsZTogc3RyaW5nLCBuYW1lOiBzdHJpbmcpOiBzdHJpbmcge1xuXHRcdGNvbnN0IGRlY2wgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRGVjbHMuZ2V0KGZpbGUpPy5nZXQobmFtZSk7XG5cdFx0Y29uc3Qgbm9kZSA9IGRlY2w/Lm5vZGU7XG5cdFx0bGV0IGxvY2F0aW9uID0gYCR7ZmlsZX06MToxYDtcblx0XHRpZiAobm9kZSAmJiBub2RlLnBvcyA+PSAwKSB7XG5cdFx0XHRjb25zdCBzb3VyY2VGaWxlID0gbm9kZS5nZXRTb3VyY2VGaWxlKCk7XG5cdFx0XHRjb25zdCBsaW5lID0gc291cmNlRmlsZS5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihub2RlLmdldFN0YXJ0KCkpLmxpbmUgKyAxO1xuXHRcdFx0Y29uc3QgY29sdW1uID0gc291cmNlRmlsZS5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihub2RlLmdldFN0YXJ0KCkpLmNoYXJhY3RlciArIDE7XG5cdFx0XHRsb2NhdGlvbiA9IGAke2ZpbGV9OiR7bGluZX06JHtjb2x1bW59YDtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gbG9jYXRpb247XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgYSBoYXJkLWZhaWwgZ3JhcGggcmVmZXJlbmNlIGVycm9yIHdpdGggdGhlIHJlZmVyZW5jZSBzaXRlIGFuZFxuXHQgKiBldmVyeSBjYW5kaWRhdGUgbG9jYXRpb24uXG5cdCAqL1xuXHRwcml2YXRlIHJlY29yZEdyYXBoUmVmZXJlbmNlRXJyb3IgKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRyZWZOb2RlOiB0cy5Ob2RlIHwgc3RyaW5nLFxuXHRcdHJlc3VsdDogRXh0cmFjdDxHcmFwaFR5cGVSZWZlcmVuY2VSZXN1bHQsIHsgc3RhdHVzOiAnYW1iaWd1b3VzJyB8ICdub25lJyB9PlxuXHQpOiB2b2lkIHtcblx0XHRjb25zdCBsb2NhdGlvbiA9IHR5cGVvZiByZWZOb2RlID09PSAnc3RyaW5nJyA/IHJlZk5vZGUgOiB0aGlzLm5vZGVMb2NhdGlvbihyZWZOb2RlKTtcblx0XHRpZiAocmVzdWx0LnN0YXR1cyA9PT0gJ2FtYmlndW91cycpIHtcblx0XHRcdGNvbnN0IGNhbmRpZGF0ZUxvY2F0aW9ucyA9IHJlc3VsdC5jYW5kaWRhdGVzLm1hcChuID0+IGAke24uc291cmNlRmlsZX06JHtuLmxpbmV9OiR7bi5jb2x1bW59YCk7XG5cdFx0XHRjb25zdCBhbWJpZ3VvdXNNZXNzYWdlID0gYEFtYmlndW91cyByZWZlcmVuY2UgdG8gbW5lbW9uaWNhIHR5cGUgJyR7bmFtZX0nOiBgICtcblx0XHRcdFx0YCR7cmVzdWx0LmNhbmRpZGF0ZXMubGVuZ3RofSB0eXBlcyBzaGFyZSB0aGUgbmFtZSBhbmQgbmVpdGhlciB0aGUgcGFyZW50IGNoYWluIGAgK1xuXHRcdFx0XHQnbm9yIHRoZSBpbXBvcnRzIGRpc2FtYmlndWF0ZSc7XG5cdFx0XHRjb25zdCBhbWJpZ3VvdXNFcnJvcjogUmVzb2x1dGlvbkVycm9yID0ge1xuXHRcdFx0XHRtZXNzYWdlICAgOiBhbWJpZ3VvdXNNZXNzYWdlLFxuXHRcdFx0XHRsb2NhdGlvbnMgOiBbIGxvY2F0aW9uLCAuLi5jYW5kaWRhdGVMb2NhdGlvbnMgXSxcblx0XHRcdH07XG5cdFx0XHR0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzLnB1c2goYW1iaWd1b3VzRXJyb3IpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCB1bnJlc29sdmVkTWVzc2FnZSA9IGBVbnJlc29sdmVkIHJlZmVyZW5jZSB0byBtbmVtb25pY2EgdHlwZSAnJHtuYW1lfSc6IG5vIHR5cGUgbWF0Y2hlcyBgICtcblx0XHRcdCdieSB2YWx1ZSBzY29wZSwgaW1wb3J0cywgcGFyZW50IGNoYWluLCBvciByb290IHBhdGgnO1xuXHRcdGNvbnN0IHVucmVzb2x2ZWRFcnJvcjogUmVzb2x1dGlvbkVycm9yID0geyBtZXNzYWdlIDogdW5yZXNvbHZlZE1lc3NhZ2UsIGxvY2F0aW9ucyA6IFsgbG9jYXRpb24gXSB9O1xuXHRcdHRoaXMuZ3JhcGhSZWZlcmVuY2VFcnJvcnMucHVzaCh1bnJlc29sdmVkRXJyb3IpO1xuXHR9XG5cblx0LyoqXG5cdCAqIExvY2F0aW9uIChgZmlsZTpsaW5lOmNvbHVtbmApIG9mIGFuIEFTVCBub2RlLCBkZXJpdmVkIHdpdGhvdXQgcGFyZW50XG5cdCAqIHBvaW50ZXJzIHdoZW4gbmVjZXNzYXJ5LlxuXHQgKi9cblx0cHJpdmF0ZSBub2RlTG9jYXRpb24gKG5vZGU6IHRzLk5vZGUpOiBzdHJpbmcge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbm9kZTtcblx0XHR3aGlsZSAoY3VycmVudCAmJiAhdHMuaXNTb3VyY2VGaWxlKGN1cnJlbnQpKSB7XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdGlmICghY3VycmVudCkge1xuXHRcdFx0Y29uc3QgZmFsbGJhY2sgPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0XHRyZXR1cm4gZmFsbGJhY2s7XG5cdFx0fVxuXHRcdGNvbnN0IHN0YXJ0ID0gbm9kZS5nZXRTdGFydChjdXJyZW50KTtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oY3VycmVudCwgc3RhcnQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7Y3VycmVudC5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0cmV0dXJuIGxvY2F0aW9uO1xuXHR9XG5cblx0LyoqXG5cdCAqIFRyYWNrIGFsaWFzZXMgb2YgdGhlIG1uZW1vbmljYSBtb2R1bGUgb2JqZWN0LCBlLmcuOlxuXHQgKiAgIGNvbnN0IG0gPSBtbmVtb25pY2E7XG5cdCAqICAgY29uc3QgQXBwID0gbTtcblx0ICovXG5cdHByaXZhdGUgdHJhY2tNb2R1bGVPYmplY3RBbGlhc2VzIChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgfHwgIXRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBpbml0aWFsaXplciB9ID0gbm9kZTtcblx0XHRpZiAoIWluaXRpYWxpemVyKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihpbml0aWFsaXplcikgJiYgdGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuaGFzKGluaXRpYWxpemVyLnRleHQpKSB7XG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQobm9kZS5uYW1lLnRleHQpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBUcmFjayBjdXN0b20gY29sbGVjdGlvbiB2YXJpYWJsZXMsIGUuZy46XG5cdCAqICAgY29uc3QgTXlDb2xsZWN0aW9uID0gY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCk7XG5cdCAqICAgY29uc3QgT3RoZXIgPSBNeUNvbGxlY3Rpb247XG5cdCAqXG5cdCAqIEFsc28gZGV0ZWN0cyBPcHRpb24gQiB1c2VyLXByb3ZpZGVkIHJlZ2lzdHJ5IGludGVyZmFjZXM6XG5cdCAqICAgZXhwb3J0IGludGVyZmFjZSBNeUNvbGxlY3Rpb25SZWdpc3RyeSB7fVxuXHQgKiAgIGNvbnN0IE15Q29sbGVjdGlvbiA9IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbjxNeUNvbGxlY3Rpb25SZWdpc3RyeT4oKTtcblx0ICovXG5cdHByaXZhdGUgdHJhY2tDb2xsZWN0aW9uQWxpYXNlcyAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpIHx8ICF0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgaW5pdGlhbGl6ZXIgfSA9IG5vZGU7XG5cdFx0aWYgKCFpbml0aWFsaXplcikge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIERpcmVjdCBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSBjYWxsXG5cdFx0aWYgKHRoaXMuaXNDcmVhdGVUeXBlc0NvbGxlY3Rpb25DYWxsKGluaXRpYWxpemVyKSkge1xuXHRcdFx0Y29uc3QgY29sbGVjdGlvbklkID0gdGhpcy5uZXh0Q29sbGVjdGlvbklkKCk7XG5cdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuc2V0KG5vZGUubmFtZS50ZXh0LCBjb2xsZWN0aW9uSWQpO1xuXG5cdFx0XHRjb25zdCByZWdpc3RyeUludGVyZmFjZU5hbWUgPSB0aGlzLmV4dHJhY3RSZWdpc3RyeUludGVyZmFjZU5hbWUoXG5cdFx0XHRcdGluaXRpYWxpemVyIGFzIHRzLkNhbGxFeHByZXNzaW9uLFxuXHRcdFx0XHRzb3VyY2VGaWxlXG5cdFx0XHQpO1xuXHRcdFx0dGhpcy5jb2xsZWN0aW9uSW5mby5zZXQoY29sbGVjdGlvbklkLCB7XG5cdFx0XHRcdHZhcmlhYmxlTmFtZSAgICAgICAgICA6IG5vZGUubmFtZS50ZXh0LFxuXHRcdFx0XHRzb3VyY2VGaWxlICAgICAgICAgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRyZWdpc3RyeUludGVyZmFjZU5hbWUgOiByZWdpc3RyeUludGVyZmFjZU5hbWVcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEFsaWFzIG9mIGFub3RoZXIgY29sbGVjdGlvbiB2YXJpYWJsZVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRjb25zdCBleGlzdGluZyA9IHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5nZXQoaW5pdGlhbGl6ZXIudGV4dCk7XG5cdFx0XHRpZiAoZXhpc3RpbmcpIHtcblx0XHRcdFx0dGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLnNldChub2RlLm5hbWUudGV4dCwgZXhpc3RpbmcpO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSByZWdpc3RyeSBpbnRlcmZhY2UgbmFtZSBmcm9tIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbjxSZWdpc3RyeT4oKVxuXHQgKiB3aGVuIHRoZSBpbnRlcmZhY2UgaXMgZGVjbGFyZWQgaW4gdGhlIHNhbWUgc291cmNlIGZpbGUuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RSZWdpc3RyeUludGVyZmFjZU5hbWUgKFxuXHRcdGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGVcblx0KTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCB0eXBlQXJncyA9IGNhbGwudHlwZUFyZ3VtZW50cztcblx0XHRpZiAoIXR5cGVBcmdzIHx8IHR5cGVBcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBbIGZpcnN0VHlwZUFyZyBdID0gdHlwZUFyZ3M7XG5cdFx0aWYgKCF0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKGZpcnN0VHlwZUFyZykgfHwgIXRzLmlzSWRlbnRpZmllcihmaXJzdFR5cGVBcmcudHlwZU5hbWUpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IG5hbWUgPSBmaXJzdFR5cGVBcmcudHlwZU5hbWUudGV4dDtcblxuXHRcdC8vIENvbmZpcm0gdGhlIGludGVyZmFjZSBleGlzdHMgaW4gdGhlIHNhbWUgc291cmNlIGZpbGUuXG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc291cmNlRmlsZS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzSW50ZXJmYWNlRGVjbGFyYXRpb24oc3RhdGVtZW50KSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIG5hbWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgdGhlIHJlZ2lzdHJ5IGludGVyZmFjZSBuYW1lIGZvciBhIGNvbGxlY3Rpb24gaWQuXG5cdCAqL1xuXHRwcml2YXRlIGdldFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSAoY29sbGVjdGlvbklkPzogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIWNvbGxlY3Rpb25JZCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0cmV0dXJuIHRoaXMuY29sbGVjdGlvbkluZm8uZ2V0KGNvbGxlY3Rpb25JZCk/LnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhbiBleHByZXNzaW9uIGlzIGEgY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgY2FsbC5cblx0ICogSGFuZGxlczpcblx0ICogICBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKVxuXHQgKiAgIGN0YygpIC8vIGFsaWFzZWQgaW1wb3J0XG5cdCAqICAgbW5lbW9uaWNhLmNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIC8vIG1vZHVsZSBvYmplY3QgbWV0aG9kXG5cdCAqICAgbS5jcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSAvLyBhbGlhc2VkIG1vZHVsZSBvYmplY3Rcblx0ICovXG5cdHByaXZhdGUgaXNDcmVhdGVUeXBlc0NvbGxlY3Rpb25DYWxsIChub2RlOiB0cy5Ob2RlKTogbm9kZSBpcyB0cy5DYWxsRXhwcmVzc2lvbiB7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXHRcdGNvbnN0IGV4cHIgPSBub2RlLmV4cHJlc3Npb247XG5cblx0XHQvLyBEaXJlY3QgY2FsbCBvciBhbGlhc2VkIGltcG9ydDogY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgLyBjdGMoKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLnRleHQgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nIHx8XG5cdFx0XHRcdHRoaXMuY3JlYXRlVHlwZXNDb2xsZWN0aW9uVmFyaWFibGVzLmhhcyhleHByLnRleHQpO1xuXHRcdH1cblxuXHRcdC8vIE1vZHVsZSBvYmplY3QgbWV0aG9kOiBtbmVtb25pY2EuY3JlYXRlVHlwZXNDb2xsZWN0aW9uKClcblx0XHRpZiAoXG5cdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSAmJlxuXHRcdFx0ZXhwci5uYW1lLnRleHQgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIoZXhwci5leHByZXNzaW9uKSAmJlxuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuaGFzKGV4cHIuZXhwcmVzc2lvbi50ZXh0KVxuXHRcdCkge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdlbmVyYXRlIGEgdW5pcXVlIGNvbGxlY3Rpb24gaWRlbnRpZmllci5cblx0ICovXG5cdHByaXZhdGUgbmV4dENvbGxlY3Rpb25JZCAoKTogc3RyaW5nIHtcblx0XHR0aGlzLmNvbGxlY3Rpb25Db3VudGVyKys7XG5cdFx0Y29uc3QgcmVzdWx0ID0gYGNvbGxlY3Rpb25fJHt0aGlzLmNvbGxlY3Rpb25Db3VudGVyfWA7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhIG5vZGUgaXMgYSBkZWZpbmUoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGlzRGVmaW5lQ2FsbCAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuQ2FsbEV4cHJlc3Npb24ge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBkaXJlY3QgY2FsbDogZGVmaW5lKCdUeXBlTmFtZScsIC4uLilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2RlZmluZScpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBtZXRob2QgY2FsbDogU29tZVR5cGUuZGVmaW5lKCdTdWJUeXBlJywgLi4uKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuIGV4cHJlc3Npb24ubmFtZT8udGV4dCA9PT0gJ2RlZmluZSc7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGEgbm9kZSBpcyBhIGxhenkoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGlzTGF6eUNhbGwgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkNhbGxFeHByZXNzaW9uIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IG5vZGU7XG5cblx0XHQvLyBDaGVjayBmb3IgZGlyZWN0IGNhbGw6IGxhenkoJ1R5cGVOYW1lJywgZ2V0dGVyLCAuLi4pXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLnRleHQgPT09ICdsYXp5Jykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIG1ldGhvZCBjYWxsOiBTb21lVHlwZS5sYXp5KCdTdWJUeXBlJywgZ2V0dGVyLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gZXhwcmVzc2lvbi5uYW1lPy50ZXh0ID09PSAnbGF6eSc7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IGNvbmZpZyBvcHRpb25zIGZyb20gYW4gb2JqZWN0IGxpdGVyYWxcblx0XHQqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbCAoY29uZmlnQXJnOiB0cy5PYmplY3RMaXRlcmFsRXhwcmVzc2lvbik6XG5cdFx0eyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9IHtcblx0XHRjb25zdCBjb25maWc6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSA9IHt9O1xuXG5cdFx0Zm9yIChjb25zdCBwcm9wIG9mIGNvbmZpZ0FyZy5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFzc2lnbm1lbnQocHJvcCkgJiYgdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBwcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0aWYgKHByb3BOYW1lID09PSAnc3RyaWN0Q2hhaW4nICYmIHByb3AuaW5pdGlhbGl6ZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5zdHJpY3RDaGFpbiA9IHRydWU7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdzdHJpY3RDaGFpbicgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5zdHJpY3RDaGFpbiA9IGZhbHNlO1xuXHRcdFx0XHR9IGVsc2UgaWYgKHByb3BOYW1lID09PSAnYmxvY2tFcnJvcnMnICYmIHByb3AuaW5pdGlhbGl6ZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5ibG9ja0Vycm9ycyA9IHRydWU7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdibG9ja0Vycm9ycycgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbmZpZy5ibG9ja0Vycm9ycyA9IGZhbHNlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGNvbmZpZztcblx0fVxuXG5cdC8qKlxuXHRcdCogRXh0cmFjdCBjb25maWcgb3B0aW9ucyBmcm9tIGRlZmluZSgpIGNhbGxcblx0XHQqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25maWcgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogeyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9IHtcblx0XHQvLyBDb25maWcgaXMgdGhlIHRoaXJkIGFyZ3VtZW50OiBkZWZpbmUoJ05hbWUnLCBoYW5kbGVyLCBjb25maWcpXG5cdFx0Y29uc3QgWyAsICwgY29uZmlnQXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblx0XHRpZiAoIWNvbmZpZ0FyZyB8fCAhdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihjb25maWdBcmcpKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgY29uZmlnUmVzdWx0ID0gdGhpcy5leHRyYWN0Q29uZmlnRnJvbU9iamVjdExpdGVyYWwoY29uZmlnQXJnKTtcblx0XHRyZXR1cm4gY29uZmlnUmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0KiBDaGVjayBpZiBhIG5vZGUgaXMgYSBAZGVjb3JhdGUoKSBkZWNvcmF0b3Jcblx0XHQqL1xuXHRwcml2YXRlIGlzRGVjb3JhdGVEZWNvcmF0b3IgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkRlY29yYXRvciB7XG5cdFx0aWYgKCF0cy5pc0RlY29yYXRvcihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBAZGVjb3JhdGVcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2RlY29yYXRlJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIEBkZWNvcmF0ZSgpIG9yIEBkZWNvcmF0ZShQYXJlbnRUeXBlKVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRjb25zdCBmbk5hbWUgPSBleHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGZuTmFtZSkgJiYgZm5OYW1lLnRleHQgPT09ICdkZWNvcmF0ZScpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cblx0XHRcdC8vIENoZWNrIGZvciBATXlDb2xsZWN0aW9uLmRlY29yYXRlKCkgd2hlcmUgTXlDb2xsZWN0aW9uIGlzIGEgY3VzdG9tIGNvbGxlY3Rpb25cblx0XHRcdGlmIChcblx0XHRcdFx0dHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZm5OYW1lKSAmJlxuXHRcdFx0XHRmbk5hbWUubmFtZS50ZXh0ID09PSAnZGVjb3JhdGUnICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihmbk5hbWUuZXhwcmVzc2lvbikgJiZcblx0XHRcdFx0dGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmhhcyhmbk5hbWUuZXhwcmVzc2lvbi50ZXh0KVxuXHRcdFx0KSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBNYXJrIGEgY2FsbCBleHByZXNzaW9uIGFzIHByb2Nlc3NlZCBhbmQgcmV0dXJuIHdoZXRoZXIgaXQgYWxyZWFkeSB3YXMuXG5cdCAqL1xuXHRwcml2YXRlIG1hcmtQcm9jZXNzZWQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogYm9vbGVhbiB7XG5cdFx0aWYgKHRoaXMucHJvY2Vzc2VkQ2FsbHMuaGFzKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cdFx0dGhpcy5wcm9jZXNzZWRDYWxscy5hZGQoY2FsbCk7XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb2Nlc3MgYSBkZWZpbmUoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NEZWZpbmVDYWxsIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGlmIHRoaXMgZXhhY3QgY2FsbCBoYXMgYWxyZWFkeSBiZWVuIHByb2Nlc3NlZCAocHJldmVudHMgZHVwbGljYXRlcyBmcm9tIGNoYWluZWQgY2FsbHMpXG5cdFx0aWYgKHRoaXMubWFya1Byb2Nlc3NlZChjYWxsKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEdldCB0aGUgdHlwZSBuYW1lIGFuZCBzb3VyY2UgY29udGV4dCBmcm9tIGFyZ3VtZW50c1xuXHRcdGNvbnN0IGRlZmluZUNvbnRleHQgPSB0aGlzLmV4dHJhY3REZWZpbmVDb250ZXh0KGNhbGwpO1xuXG5cdFx0Ly8gRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBkZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKSwgd2Ugd2FudCB0aGUgcG9zaXRpb24gb2YgdGhlIC5kZWZpbmUoJ0InKSBwYXJ0XG5cdFx0Ly8gbm90IHRoZSBzdGFydCBvZiB0aGUgZW50aXJlIGV4cHJlc3Npb25cblx0XHRsZXQgcG9zaXRpb25Ob2RlOiB0cy5Ob2RlID0gY2FsbDtcblxuXHRcdC8vIElmIHRoaXMgaXMgYSBjaGFpbmVkIGNhbGwsIGdldCB0aGUgcG9zaXRpb24gb2YgdGhlIHByb3BlcnR5IGFjY2VzcyBleHByZXNzaW9uXG5cdFx0Ly8gd2hpY2ggaXMgdGhlIC5kZWZpbmUgcGFydFxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHQvLyBUaGUgZXhwcmVzc2lvbiBpcyB0aGUgcHJvcGVydHkgYWNjZXNzOiAoZGVmaW5lKCdSb290QXN5bmMnLCAuLi4pKS5kZWZpbmVcblx0XHRcdC8vIFdlIHdhbnQgdGhlIHBvc2l0aW9uIG9mIGp1c3QgdGhlIC5kZWZpbmUgcGFydFxuXHRcdFx0Ly8gVGhpcyBpcyB0aGUgJ2RlZmluZScgaWRlbnRpZmllclxuXHRcdFx0cG9zaXRpb25Ob2RlID0gY2FsbC5leHByZXNzaW9uLm5hbWU7XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnRQb3MgPSBwb3NpdGlvbk5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSk7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKHNvdXJjZUZpbGUsIHN0YXJ0UG9zKTtcblxuXHRcdGlmICghZGVmaW5lQ29udGV4dC50eXBlTmFtZSkge1xuXHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdG1lc3NhZ2UgOiAnQ291bGQgbm90IGV4dHJhY3QgdHlwZSBuYW1lIGZyb20gZGVmaW5lKCkgY2FsbCcsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyB0eXBlTmFtZSB9ID0gZGVmaW5lQ29udGV4dDtcblxuXHRcdC8vIERldGVybWluZSBwYXJlbnQgdHlwZSBhbmQgY29sbGVjdGlvbiBiYXNlZCBvbiB0aGUgY2FsbCBzb3VyY2UuXG5cdFx0Y29uc3QgcGFyZW50Tm9kZSA9IGRlZmluZUNvbnRleHQucGFyZW50VHlwZTtcblx0XHRjb25zdCB7IGNvbGxlY3Rpb25JZCB9ID0gZGVmaW5lQ29udGV4dDtcblxuXHRcdC8vIEV4dHJhY3QgY29uZmlnIG9wdGlvbnNcblx0XHRjb25zdCBjb25maWcgPSB0aGlzLmV4dHJhY3RDb25maWcoY2FsbCk7XG5cblx0XHQvLyBDcmVhdGUgdHlwZSBub2RlIGZpcnN0IHNvIGl0cyBpbnRlcm5hbCBmdWxsUGF0aCAoaW5jbHVkaW5nIGFueSBjb2xsZWN0aW9uIHByZWZpeCkgaXMgcmVzb2x2ZWQuXG5cdFx0Y29uc3Qgbm9kZSA9IFR5cGVHcmFwaEltcGwuY3JlYXRlTm9kZShcblx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0cGFyZW50Tm9kZSxcblx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRsaW5lICsgMSxcblx0XHRcdGNoYXJhY3RlciArIDEsXG5cdFx0XHRjb2xsZWN0aW9uSWRcblx0XHQpO1xuXHRcdG5vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lID0gdGhpcy5nZXRSZWdpc3RyeUludGVyZmFjZU5hbWUoY29sbGVjdGlvbklkKTtcblxuXHRcdC8vIFNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZSBkZXRlY3Rpb24gKGhhcmQtZmFpbCBsYXcpOiBrZXkgYnkgdGhlXG5cdFx0Ly8gcnVudGltZSBuYW1lc3BhY2Ug4oCUIGNvbGxlY3Rpb24gcm9vdHMgYDxjb2xsZWN0aW9uPjo6PG5hbWU+YCwgb3Jcblx0XHQvLyBgPHBhcmVudEZ1bGxQYXRoPi48bmFtZT5gIGZvciBzdWJ0eXBlc1xuXHRcdHRoaXMucmVjb3JkRGVmaW5lU2l0ZShcblx0XHRcdHBhcmVudE5vZGUgPyBgJHtwYXJlbnROb2RlLmZ1bGxQYXRofS4ke3R5cGVOYW1lfWAgOiBgJHtjb2xsZWN0aW9uSWQgPz8gJ2RlZmF1bHQnfTo6JHt0eXBlTmFtZX1gLFxuXHRcdFx0YCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWBcblx0XHQpO1xuXG5cdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gY29uc3RydWN0b3IgZnVuY3Rpb24g4oCUIHRoZSBuZXcgbm9kZSBhbmNob3JzXG5cdFx0Ly8gcmVsYXRpdmUtZmlyc3QgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb24gd2hpbGUgaXRzIG93biBzaWduYXR1cmVcblx0XHQvLyBpcyBiZWluZyByZWFkXG5cdFx0Y29uc3QgcHJldmlvdXNBbmNob3IgPSB0aGlzLmN1cnJlbnRHcmFwaEFuY2hvcjtcblx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IG5vZGU7XG5cdFx0dHJ5IHtcblx0XHRcdG5vZGUucHJvcGVydGllcyA9IHRoaXMuZXh0cmFjdFByb3BlcnRpZXMoY2FsbCk7XG5cblx0XHRcdC8vIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmb3IgVHlwZVJlZ2lzdHJ5IHNpZ25hdHVyZVxuXHRcdFx0bm9kZS5jb25zdHJ1Y3RvclBhcmFtcyA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zKGNhbGwpO1xuXHRcdH0gZmluYWxseSB7XG5cdFx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IHByZXZpb3VzQW5jaG9yO1xuXHRcdH1cblxuXHRcdC8vIEFkZCB0byBncmFwaFxuXHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZENoaWxkKHBhcmVudE5vZGUsIG5vZGUpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZFJvb3Qobm9kZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ3JlYXRlIGRlZmluaXRpb24gaW5mbyB1c2luZyB0aGUgbm9kZSdzIHJlc29sdmVkIGZ1bGxQYXRoXG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IHR5cGVOYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlZmluZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IHBhcmVudE5vZGUgPyBwYXJlbnROb2RlLmZ1bGxQYXRoIDogbnVsbCxcblx0XHRcdHN0cmljdENoYWluIDogY29uZmlnLnN0cmljdENoYWluID8/IHRydWUsXG5cdFx0XHRibG9ja0Vycm9ycyA6IGNvbmZpZy5ibG9ja0Vycm9ycyA/PyBmYWxzZSxcblx0XHR9O1xuXHRcdHRoaXMuZGVmaW5pdGlvbnMuc2V0KG5vZGUuZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXHRcdHRoaXMuZWRzU2NvcGVCeU5vZGUuc2V0KGNhbGwsIG5vZGUuZnVsbFBhdGgpO1xuXG5cdFx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudDogY29uc3QgVXNlciA9IGRlZmluZSgnVXNlckVudGl0eScsIC4uLikgLT4gbWFwIFwiVXNlclwiIHRvIFwiVXNlckVudGl0eVwiXG5cdFx0Ly8gQSBtdWx0aS1ob3AgaW5pdGlhbGl6ZXIgYmluZHMgdGhlIExBU1QgaG9wOiBkZWZpbmUoKSByZXR1cm5zIHRoZVxuXHRcdC8vIGRlZmluZWQgdHlwZSdzIGNvbnN0cnVjdG9yIChGMTgpXG5cdFx0dGhpcy50cmFja1ZhcmlhYmxlQXNzaWdubWVudChjYWxsLCBwYXJlbnROb2RlLCBub2RlLmZ1bGxQYXRoKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBQcm9jZXNzIGEgbGF6eSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgcHJvY2Vzc0xhenlDYWxsIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGlmIHRoaXMgZXhhY3QgY2FsbCBoYXMgYWxyZWFkeSBiZWVuIHByb2Nlc3NlZCAocHJldmVudHMgZHVwbGljYXRlcyBmcm9tIGNoYWluZWQgY2FsbHMpXG5cdFx0aWYgKHRoaXMubWFya1Byb2Nlc3NlZChjYWxsKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEdldCB0aGUgdHlwZSBuYW1lIGFuZCBzb3VyY2UgY29udGV4dCBmcm9tIGFyZ3VtZW50c1xuXHRcdGNvbnN0IGxhenlDb250ZXh0ID0gdGhpcy5leHRyYWN0TGF6eUNvbnRleHQoY2FsbCwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGRlZmluZSgnQScpLmxhenkoJ0InKSwgd2Ugd2FudCB0aGUgcG9zaXRpb24gb2YgdGhlIC5sYXp5KCdCJykgcGFydFxuXHRcdC8vIG5vdCB0aGUgc3RhcnQgb2YgdGhlIGVudGlyZSBleHByZXNzaW9uXG5cdFx0bGV0IHBvc2l0aW9uTm9kZTogdHMuTm9kZSA9IGNhbGw7XG5cblx0XHQvLyBJZiB0aGlzIGlzIGEgY2hhaW5lZCBjYWxsLCBnZXQgdGhlIHBvc2l0aW9uIG9mIHRoZSBwcm9wZXJ0eSBhY2Nlc3MgZXhwcmVzc2lvblxuXHRcdC8vIHdoaWNoIGlzIHRoZSAubGF6eSBwYXJ0XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdC8vIFRoZSBleHByZXNzaW9uIGlzIHRoZSBwcm9wZXJ0eSBhY2Nlc3M6IChkZWZpbmUoJ1Jvb3RBc3luYycsIC4uLikpLmxhenlcblx0XHRcdC8vIFdlIHdhbnQgdGhlIHBvc2l0aW9uIG9mIGp1c3QgdGhlIC5sYXp5IHBhcnRcblx0XHRcdC8vIFRoaXMgaXMgdGhlICdsYXp5JyBpZGVudGlmaWVyXG5cdFx0XHRwb3NpdGlvbk5vZGUgPSBjYWxsLmV4cHJlc3Npb24ubmFtZTtcblx0XHR9XG5cblx0XHRjb25zdCBzdGFydFBvcyA9IHBvc2l0aW9uTm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKTtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oc291cmNlRmlsZSwgc3RhcnRQb3MpO1xuXG5cdFx0aWYgKCFsYXp5Q29udGV4dC50eXBlTmFtZSkge1xuXHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdG1lc3NhZ2UgOiAnQ291bGQgbm90IGV4dHJhY3QgdHlwZSBuYW1lIGZyb20gbGF6eSgpIGNhbGwnLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgdHlwZU5hbWUgfSA9IGxhenlDb250ZXh0O1xuXG5cdFx0Ly8gRGV0ZXJtaW5lIHBhcmVudCB0eXBlIGFuZCBjb2xsZWN0aW9uIGJhc2VkIG9uIHRoZSBjYWxsIHNvdXJjZS5cblx0XHRjb25zdCBwYXJlbnROb2RlID0gbGF6eUNvbnRleHQucGFyZW50VHlwZTtcblx0XHRjb25zdCB7IGNvbGxlY3Rpb25JZCB9ID0gbGF6eUNvbnRleHQ7XG5cblx0XHQvLyBFeHRyYWN0IGNvbmZpZyBvcHRpb25zXG5cdFx0Y29uc3QgY29uZmlnID0gdGhpcy5leHRyYWN0TGF6eUNvbmZpZyhjYWxsKTtcblxuXHRcdC8vIENyZWF0ZSB0eXBlIG5vZGUgZmlyc3Qgc28gaXRzIGludGVybmFsIGZ1bGxQYXRoIChpbmNsdWRpbmcgYW55IGNvbGxlY3Rpb24gcHJlZml4KSBpcyByZXNvbHZlZC5cblx0XHRjb25zdCBub2RlID0gVHlwZUdyYXBoSW1wbC5jcmVhdGVOb2RlKFxuXHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRwYXJlbnROb2RlLFxuXHRcdFx0c291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdGxpbmUgKyAxLFxuXHRcdFx0Y2hhcmFjdGVyICsgMSxcblx0XHRcdGNvbGxlY3Rpb25JZFxuXHRcdCk7XG5cdFx0bm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWUgPSB0aGlzLmdldFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZShjb2xsZWN0aW9uSWQpO1xuXG5cdFx0Ly8gU2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlIGRldGVjdGlvbiAoaGFyZC1mYWlsIGxhdylcblx0XHR0aGlzLnJlY29yZERlZmluZVNpdGUoXG5cdFx0XHRwYXJlbnROb2RlID8gYCR7cGFyZW50Tm9kZS5mdWxsUGF0aH0uJHt0eXBlTmFtZX1gIDogYCR7Y29sbGVjdGlvbklkID8/ICdkZWZhdWx0J306OiR7dHlwZU5hbWV9YCxcblx0XHRcdGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gXG5cdFx0KTtcblxuXHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIHRoZSBjb25zdHJ1Y3RvciByZXR1cm5lZCBieSB0aGUgbGF6eSBnZXR0ZXJcblx0XHQvLyDigJQgdGhlIG5ldyBub2RlIGFuY2hvcnMgcmVsYXRpdmUtZmlyc3QgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb25cblx0XHRjb25zdCBwcmV2aW91c0FuY2hvciA9IHRoaXMuY3VycmVudEdyYXBoQW5jaG9yO1xuXHRcdHRoaXMuY3VycmVudEdyYXBoQW5jaG9yID0gbm9kZTtcblx0XHR0cnkge1xuXHRcdFx0bm9kZS5wcm9wZXJ0aWVzID0gdGhpcy5leHRyYWN0UHJvcGVydGllcyhjYWxsKTtcblxuXHRcdFx0Ly8gRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZvciBUeXBlUmVnaXN0cnkgc2lnbmF0dXJlXG5cdFx0XHRub2RlLmNvbnN0cnVjdG9yUGFyYW1zID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JQYXJhbXMoY2FsbCk7XG5cdFx0fSBmaW5hbGx5IHtcblx0XHRcdHRoaXMuY3VycmVudEdyYXBoQW5jaG9yID0gcHJldmlvdXNBbmNob3I7XG5cdFx0fVxuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoXG5cdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkQ2hpbGQocGFyZW50Tm9kZSwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cblx0XHQvLyBDcmVhdGUgZGVmaW5pdGlvbiBpbmZvIHVzaW5nIHRoZSBub2RlJ3MgcmVzb2x2ZWQgZnVsbFBhdGhcblx0XHRjb25zdCBkZWZpbml0aW9uOiBEZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogcGFyZW50Tm9kZSA/IHBhcmVudE5vZGUuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiBjb25maWcuc3RyaWN0Q2hhaW4gPz8gdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogY29uZmlnLmJsb2NrRXJyb3JzID8/IGZhbHNlLFxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQobm9kZS5mdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdFx0dGhpcy5lZHNTY29wZUJ5Tm9kZS5zZXQoY2FsbCwgbm9kZS5mdWxsUGF0aCk7XG5cblx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50OiBjb25zdCBMYXp5VHlwZSA9IGxhenkoJ0xhenlUeXBlJywgLi4uKSAtPiBtYXAgXCJMYXp5VHlwZVwiIC0+IFwiTGF6eVR5cGVcIlxuXHRcdC8vIEZvciBjaGFpbmVkIGNhbGxzIGxpa2UgY29uc3QgWCA9IGxhenkoJ0EnKS5kZWZpbmUoJ0InKSwgd2Ugd2FudCB0byBtYXAgWCAtPiBBICh0aGUgcm9vdClcblx0XHR0aGlzLnRyYWNrVmFyaWFibGVBc3NpZ25tZW50KGNhbGwsIHBhcmVudE5vZGUsIG5vZGUuZnVsbFBhdGgpO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgbGF6eSgpIGNhbGwgYXJndW1lbnRzIGludG8gYSBub3JtYWxpemVkIHNoYXBlLlxuXHQgKiBIYW5kbGVzIG5hbWVkL3VubmFtZWQgYW5kIGV4cGxpY2l0LXNvdXJjZSBmb3JtcywgYm90aCBhcyBmcmVlIGNhbGxzXG5cdCAqIGFuZCBhcyBtZXRob2QgY2FsbHMuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q2FsbEFyZ3MgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKToge1xuXHRcdHNvdXJjZT86IHRzLkV4cHJlc3Npb247XG5cdFx0bmFtZT86IHN0cmluZztcblx0XHRnZXR0ZXI6IHRzLkV4cHJlc3Npb247XG5cdFx0Y29uZmlnPzogdHMuRXhwcmVzc2lvbjtcblx0fSB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGNvbnN0IGlzTWV0aG9kQ2FsbCA9IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbik7XG5cblx0XHRpZiAoaXNNZXRob2RDYWxsKSB7XG5cdFx0XHQvLyBTb3VyY2UgaXMgdGhlIG9iamVjdCBvZiB0aGUgcHJvcGVydHkgYWNjZXNzOiBUeXBlLmxhenkoLi4uKVxuXHRcdFx0Y29uc3Qgc291cmNlID0gY2FsbC5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IFsgbWV0aG9kRmlyc3RBcmcgXSA9IGFyZ3M7XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKG1ldGhvZEZpcnN0QXJnKSkge1xuXHRcdFx0XHQvLyBUeXBlLmxhenkoJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRcdGlmIChhcmdzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0c291cmNlLFxuXHRcdFx0XHRcdG5hbWUgICA6IG1ldGhvZEZpcnN0QXJnLnRleHQsXG5cdFx0XHRcdFx0Z2V0dGVyIDogYXJnc1sgMSBdLFxuXHRcdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDIgXSxcblx0XHRcdFx0fTtcblx0XHRcdH1cblx0XHRcdC8vIFR5cGUubGF6eShnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRzb3VyY2UsXG5cdFx0XHRcdGdldHRlciA6IG1ldGhvZEZpcnN0QXJnLFxuXHRcdFx0XHRjb25maWcgOiBhcmdzWyAxIF0sXG5cdFx0XHR9O1xuXHRcdH1cblxuXHRcdC8vIEZyZWUgY2FsbDogbGF6eSguLi4pXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGFyZ3M7XG5cblx0XHQvLyBFeHBsaWNpdC1zb3VyY2UgZm9ybTogbGF6eShzb3VyY2UsICdOYW1lJywgZ2V0dGVyLCBjb25maWc/KVxuXHRcdC8vIG9yIGxhenkoc291cmNlLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIgJiYgdHMuaXNJZGVudGlmaWVyKGZpcnN0QXJnKSkge1xuXHRcdFx0Y29uc3QgWyAsIHNlY29uZEFyZyBdID0gYXJncztcblx0XHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoc2Vjb25kQXJnKSkge1xuXHRcdFx0XHQvLyBsYXp5KHNvdXJjZSwgJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRcdGlmIChhcmdzLmxlbmd0aCA8IDMpIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0c291cmNlIDogZmlyc3RBcmcsXG5cdFx0XHRcdFx0bmFtZSAgIDogc2Vjb25kQXJnLnRleHQsXG5cdFx0XHRcdFx0Z2V0dGVyIDogYXJnc1sgMiBdLFxuXHRcdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDMgXSxcblx0XHRcdFx0fTtcblx0XHRcdH1cblx0XHRcdC8vIGxhenkoc291cmNlLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRzb3VyY2UgOiBmaXJzdEFyZyxcblx0XHRcdFx0Z2V0dGVyIDogc2Vjb25kQXJnLFxuXHRcdFx0XHRjb25maWcgOiBhcmdzWyAyIF0sXG5cdFx0XHR9O1xuXHRcdH1cblxuXHRcdC8vIE5hbWVkIHJvb3QgZm9ybTogbGF6eSgnTmFtZScsIGdldHRlciwgY29uZmlnPylcblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGZpcnN0QXJnKSkge1xuXHRcdFx0aWYgKGFyZ3MubGVuZ3RoIDwgMikge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0bmFtZSAgIDogZmlyc3RBcmcudGV4dCxcblx0XHRcdFx0Z2V0dGVyIDogYXJnc1sgMSBdLFxuXHRcdFx0XHRjb25maWcgOiBhcmdzWyAyIF0sXG5cdFx0XHR9O1xuXHRcdH1cblxuXHRcdC8vIFVubmFtZWQgcm9vdCBmb3JtOiBsYXp5KGdldHRlciwgY29uZmlnPylcblx0XHRyZXR1cm4ge1xuXHRcdFx0Z2V0dGVyIDogZmlyc3RBcmcsXG5cdFx0XHRjb25maWcgOiBhcmdzWyAxIF0sXG5cdFx0fTtcblx0fVxuXG5cdC8qKlxuXHQgKiBVbndyYXAgdGhlIGNvbnN0cnVjdG9yIHJldHVybmVkIGJ5IGEgbGF6eSBnZXR0ZXIuXG5cdCAqIFN1cHBvcnRzOlxuXHQgKiAgICgpID0+IGNsYXNzIE5hbWUge31cblx0ICogICAoKSA9PiBmdW5jdGlvbiBOYW1lKCkge31cblx0ICogICAoKSA9PiB7IHJldHVybiBjbGFzcyBOYW1lIHt9OyB9XG5cdCAqICAgZnVuY3Rpb24gKCkgeyByZXR1cm4gZnVuY3Rpb24gTmFtZSgpIHt9OyB9XG5cdCAqL1xuXHRwcml2YXRlIHVud3JhcExhenlHZXR0ZXIgKGdldHRlckV4cHI6IHRzLkV4cHJlc3Npb24pOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGdldHRlckV4cHIpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGdldHRlckV4cHI7XG5cdFx0XHRpZiAoIXRzLmlzQmxvY2soYm9keSkpIHtcblx0XHRcdFx0cmV0dXJuIGJvZHk7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IHN0bXQgb2YgYm9keS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChzdG10KSAmJiBzdG10LmV4cHJlc3Npb24pIHtcblx0XHRcdFx0XHRyZXR1cm4gc3RtdC5leHByZXNzaW9uO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihnZXR0ZXJFeHByKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBnZXR0ZXJFeHByO1xuXHRcdFx0Zm9yIChjb25zdCBzdG10IG9mIGJvZHkuc3RhdGVtZW50cykge1xuXHRcdFx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQoc3RtdCkgJiYgc3RtdC5leHByZXNzaW9uKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHN0bXQuZXhwcmVzc2lvbjtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBOb3QgYSByZWNvZ25pemVkIGdldHRlciBwYXR0ZXJuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGEgY29uc3RydWN0b3IgbmFtZSBmcm9tIGEgY2xhc3MgZXhwcmVzc2lvbiwgY2xhc3MgZGVjbGFyYXRpb24sXG5cdCAqIG9yIG5hbWVkIGZ1bmN0aW9uIGV4cHJlc3Npb24uXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3Rvck5hbWUgKGNvbnN0cnVjdG9yRXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikgJiYgY29uc3RydWN0b3JFeHByLm5hbWUpIHtcblx0XHRcdHJldHVybiBjb25zdHJ1Y3RvckV4cHIubmFtZS50ZXh0O1xuXHRcdH1cblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKGNvbnN0cnVjdG9yRXhwcikgJiYgY29uc3RydWN0b3JFeHByLm5hbWUpIHtcblx0XHRcdHJldHVybiBjb25zdHJ1Y3RvckV4cHIubmFtZS50ZXh0O1xuXHRcdH1cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSAmJiBjb25zdHJ1Y3RvckV4cHIubmFtZSkge1xuXHRcdFx0cmV0dXJuIGNvbnN0cnVjdG9yRXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0aGUgdHlwZSBuYW1lIGZyb20gZWl0aGVyIGEgZGVmaW5lKCkgb3IgbGF6eSgpIGNhbGwuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZSAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChjYWxsKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMuZXh0cmFjdFR5cGVOYW1lKGNhbGwpO1xuXHRcdH1cblx0XHRpZiAodGhpcy5pc0xhenlDYWxsKGNhbGwpKSB7XG5cdFx0XHRjb25zdCBhcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdFx0aWYgKCFhcmdzKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAoYXJncy5uYW1lKSB7XG5cdFx0XHRcdHJldHVybiBhcmdzLm5hbWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLnVud3JhcExhenlHZXR0ZXIoYXJncy5nZXR0ZXIpO1xuXHRcdFx0aWYgKGNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0XHRyZXR1cm4gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JOYW1lKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0aGUgZnVsbCBsYXp5KCkgY2FsbCBjb250ZXh0OiB0eXBlIG5hbWUsIHBhcmVudCB0eXBlLCBhbmQgY29sbGVjdGlvbi5cblx0ICogSGFuZGxlcyBkaXJlY3QgY2FsbHMsIHByb3BlcnR5LWFjY2VzcyBjYWxscywgY2hhaW5lZCBjYWxscywgYW5kIHRoZVxuXHQgKiBleHBsaWNpdC1zb3VyY2UgZm9ybSBgbGF6eShzb3VyY2UsICdUeXBlTmFtZScsIGdldHRlcilgLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0TGF6eUNvbnRleHQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKToge1xuXHRcdHR5cGVOYW1lPzogc3RyaW5nO1xuXHRcdHBhcmVudFR5cGU/OiBUeXBlTm9kZTtcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmc7XG5cdH0ge1xuXHRcdGNvbnN0IGFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0aWYgKCFhcmdzKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0bGV0IHR5cGVOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQgPSBhcmdzLm5hbWU7XG5cdFx0aWYgKCF0eXBlTmFtZSkge1xuXHRcdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy51bndyYXBMYXp5R2V0dGVyKGFyZ3MuZ2V0dGVyKTtcblx0XHRcdGlmIChjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdFx0dHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3Rvck5hbWUoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0aWYgKCF0eXBlTmFtZSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gY2FsbDtcblxuXHRcdC8vIERpcmVjdCBjYWxsOiBsYXp5KCdUeXBlTmFtZScsIC4uLikgb3IgbGF6eShzb3VyY2UsICdUeXBlTmFtZScsIGdldHRlcilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2xhenknKSB7XG5cdFx0XHRpZiAoYXJncy5zb3VyY2UgJiYgdHMuaXNJZGVudGlmaWVyKGFyZ3Muc291cmNlKSkge1xuXHRcdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKGFyZ3Muc291cmNlLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0XHRcdHBhcmVudFR5cGUgICA6IHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSxcblx0XHRcdFx0XHRjb2xsZWN0aW9uSWQgOiBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCxcblx0XHRcdFx0fTtcblx0XHRcdH1cblx0XHRcdC8vIFBsYWluIHJvb3QgbGF6eSBpbiBkZWZhdWx0IGNvbGxlY3Rpb25cblx0XHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiBYLmxhenkoJ1R5cGVOYW1lJywgLi4uKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLm5hbWUudGV4dCA9PT0gJ2xhenknKSB7XG5cdFx0XHRjb25zdCBvYmogPSBleHByZXNzaW9uLmV4cHJlc3Npb247XG5cblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIob2JqKSkge1xuXHRcdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKG9iai50ZXh0KTtcblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHR0eXBlTmFtZSxcblx0XHRcdFx0XHRwYXJlbnRUeXBlICAgOiBzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUsXG5cdFx0XHRcdFx0Y29sbGVjdGlvbklkIDogc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQsXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihvYmopKSB7XG5cdFx0XHRcdC8vIE5lc3RlZCBhY2Nlc3M6IGluc3RhbmNlLlR5cGUubGF6eSAtIHRyeSB0byByZXNvbHZlXG5cdFx0XHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKG9iaik7XG5cdFx0XHRcdGlmIChjaGFpbi5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoY2hhaW4uam9pbignLicpKTtcblx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUgfTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihvYmopKSB7XG5cdFx0XHRcdC8vIERldGVybWluZSB0aGUgY29sbGVjdGlvbiBjb250ZXh0IGZyb20gdGhlIHJvb3Qgb2YgdGhlIGNoYWluIHNvIHRoYXRcblx0XHRcdFx0Ly8gY3VzdG9tLWNvbGxlY3Rpb24gdHlwZXMgZG8gbm90IGdldCBjb25mdXNlZCB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcy5cblx0XHRcdFx0Y29uc3Qgcm9vdElkID0gdGhpcy5nZXRSb290SWRlbnRpZmllcihvYmouZXhwcmVzc2lvbik7XG5cdFx0XHRcdGNvbnN0IGV4cGVjdGVkQ29sbGVjdGlvbklkID0gcm9vdElkXG5cdFx0XHRcdFx0PyB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uocm9vdElkLnRleHQpLmNvbGxlY3Rpb25JZFxuXHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXG5cdFx0XHRcdC8vIENoYWluZWQgY2FsbDogZGVmaW5lKCdBJykubGF6eSgnQicpIG9yIGxhenkoJ0EnKS5sYXp5KCdCJylcblx0XHRcdFx0aWYgKHRoaXMuaXNEZWZpbmVDYWxsKG9iaikpIHtcblx0XHRcdFx0XHR0aGlzLnByb2Nlc3NEZWZpbmVDYWxsKG9iaiwgc291cmNlRmlsZSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzTGF6eUNhbGwob2JqLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBCdWlsZGVyIGxvb2t1cCBjaGFpbjogQXBwLmxvb2t1cCgnVXNlcicpLmxhenkoJ0FkbWluJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMb29rdXBDYWxsKG9iaikpIHtcblx0XHRcdFx0XHRjb25zdCBsb29rZWRVcFBhdGggPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKG9iaik7XG5cdFx0XHRcdFx0aWYgKGxvb2tlZFVwUGF0aCkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUobG9va2VkVXBQYXRoKTtcblx0XHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZS5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgY29uZmlnIG9wdGlvbnMgZnJvbSBsYXp5KCkgY2FsbFxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0TGF6eUNvbmZpZyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0ge1xuXHRcdGNvbnN0IGFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0aWYgKCFhcmdzIHx8ICFhcmdzLmNvbmZpZyB8fCAhdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihhcmdzLmNvbmZpZykpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRjb25zdCBjb25maWdSZXN1bHQgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChhcmdzLmNvbmZpZyk7XG5cdFx0cmV0dXJuIGNvbmZpZ1Jlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHRcdCogVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHMgdGhhdCBjYXB0dXJlIGRlZmluZSgpIHJlc3VsdHNcblx0XHQqIGUuZy4sIGNvbnN0IFVzZXIgPSBkZWZpbmUoJ1VzZXJFbnRpdHknLCAuLi4pIG1hcHMgXCJVc2VyXCIgLT4gXCJVc2VyRW50aXR5XCJcblx0XHQqIEZvciBjaGFpbmVkIGNhbGxzIGxpa2UgY29uc3QgWCA9IGRlZmluZSgnQScpLmRlZmluZSgnQicpLCB3ZSBtYXAgWCAtPiBBICh0aGUgcm9vdCB0eXBlKVxuXHRcdCovXG5cdHByaXZhdGUgdHJhY2tWYXJpYWJsZUFzc2lnbm1lbnQgKFxuXHRcdGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLFxuXHRcdHBhcmVudE5vZGU6IFR5cGVOb2RlIHwgdW5kZWZpbmVkLFxuXHRcdGZ1bGxQYXRoOiBzdHJpbmdcblx0KTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBjYWxsIGlzIHRoZSByaWdodC1oYW5kIHNpZGUgb2YgYSB2YXJpYWJsZSBkZWNsYXJhdGlvblxuXHRcdC8vIFdhbGsgdXAgdGhlIHRyZWUgdG8gZmluZCBWYXJpYWJsZURlY2xhcmF0aW9uXG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBjYWxsLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihjdXJyZW50KSkge1xuXHRcdFx0XHQvLyBGb3VuZDogY29uc3QgWCA9IGRlZmluZSguLi4pXG5cdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudC5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHZhck5hbWUgPSBjdXJyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0XHQvLyBGMTg6IGRlZmluZSgpIHJldHVybnMgdGhlIERFRklORUQgdHlwZSdzIGNvbnN0cnVjdG9yLFxuXHRcdFx0XHRcdC8vIHNvIGEgY29uc3QgaG9sZGluZyBhIG11bHRpLWhvcCBpbml0aWFsaXplclxuXHRcdFx0XHRcdC8vIChgY29uc3QgWCA9IEEuZGVmaW5lKCdCJykuZGVmaW5lKCdDJylgKSBiaW5kcyB0aGUgTEFTVFxuXHRcdFx0XHRcdC8vIGhvcCDigJQgYSBkZWVwZXIgaG9wIG11c3Qgbm90IGJpbmQsIGFuZCB0aGUgb3V0ZXJtb3N0XG5cdFx0XHRcdFx0Ly8gaG9wIGJpbmRzIHVuY29uZGl0aW9uYWxseSAodmlzaXQtb3JkZXIgaW5kZXBlbmRlbnQpXG5cdFx0XHRcdFx0aWYgKHRoaXMuaXNEZWVwZXJEZWZpbmVIb3AoY2FsbCkpIHtcblx0XHRcdFx0XHRcdHJldHVybjtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Ly8gRm9yIGNoYWluZWQgbGF6eSBjYWxscyBsaWtlIGNvbnN0IFggPSBkZWZpbmUoJ0EnKS5sYXp5KCdCJyksXG5cdFx0XHRcdFx0Ly8gdGhlIGZpcnN0IGNhbGwgaW4gdGhlIGNoYWluIHNldHMgdGhlIG1hcHBpbmcgKGxhenkgaG9wXG5cdFx0XHRcdFx0Ly8ga2VlcHMgaXQg4oCUIHBpbm5lZCBiZWhhdmlvcilcblx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSAmJiB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmhhcyh2YXJOYW1lKSkge1xuXHRcdFx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHR0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLnNldCh2YXJOYW1lLCBmdWxsUGF0aCk7XG5cdFx0XHRcdFx0dGhpcy50cmFja0ZpbGVHcmFwaEJpbmRpbmcodmFyTmFtZSwgZnVsbFBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQSBgLmRlZmluZSguLi4pYCBob3Agd3JhcHBlZCBieSBhbm90aGVyIGAuZGVmaW5lKC4uLilgIGNhbGwgaXMgbm90XG5cdCAqIHRoZSB2YWx1ZSBpdHMgY29uc3QgZW5kcyB1cCBob2xkaW5nIOKAlCB0aGUgT1VURVJNT1NUIGhvcCBvZiB0aGVcblx0ICogaW5pdGlhbGl6ZXIgY2hhaW4gaXMgKGRlZmluZSgpIHJldHVybnMgdGhlIGRlZmluZWQgdHlwZSdzXG5cdCAqIGNvbnN0cnVjdG9yKS4gT25seSB0aGUgb3V0ZXJtb3N0IGhvcCBtYXkgYmluZCB0aGUgdmFyaWFibGUuXG5cdCAqL1xuXHRwcml2YXRlIGlzRGVlcGVyRGVmaW5lSG9wIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IGJvb2xlYW4ge1xuXHRcdGNvbnN0IHsgcGFyZW50IH0gPSBjYWxsO1xuXHRcdGNvbnN0IGRlZXBlciA9ICEhcGFyZW50ICYmXG5cdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihwYXJlbnQpICYmXG5cdFx0XHRwYXJlbnQubmFtZS50ZXh0ID09PSAnZGVmaW5lJyAmJlxuXHRcdFx0dHMuaXNDYWxsRXhwcmVzc2lvbihwYXJlbnQucGFyZW50KSAmJlxuXHRcdFx0cGFyZW50LnBhcmVudC5leHByZXNzaW9uID09PSBwYXJlbnQ7XG5cdFx0cmV0dXJuIGRlZXBlcjtcblx0fVxuXG5cdC8qKlxuXHQgKiBNaXJyb3IgYSB2YXJpYWJsZSAtPiBtbmVtb25pY2EgZnVsbFBhdGggYmluZGluZyBpbnRvIHRoZSBwZXItZmlsZVxuXHQgKiB2YWx1ZS1zY29wZSBtYXAgKGdyYXBoIGlkZW50aXR5IGxhdzogYHR5cGVvZiBYYCBhbmQgYmFyZSByZWZlcmVuY2VzXG5cdCAqIHJlc29sdmUgdGhyb3VnaCB0aGUgZmlsZSdzIG93biBiaW5kaW5ncyBmaXJzdCkuXG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrRmlsZUdyYXBoQmluZGluZyAodmFyTmFtZTogc3RyaW5nLCBmdWxsUGF0aDogc3RyaW5nKTogdm9pZCB7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0bGV0IGJpbmRpbmdzID0gdGhpcy5maWxlR3JhcGhCaW5kaW5ncy5nZXQoZmlsZVBhdGgpO1xuXHRcdGlmICghYmluZGluZ3MpIHtcblx0XHRcdGJpbmRpbmdzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0XHRcdHRoaXMuZmlsZUdyYXBoQmluZGluZ3Muc2V0KGZpbGVQYXRoLCBiaW5kaW5ncyk7XG5cdFx0fVxuXHRcdGJpbmRpbmdzLnNldCh2YXJOYW1lLCBmdWxsUGF0aCk7XG5cdH1cblx0XG5cdC8qKlxuXHRcdCogVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHMgZnJvbSBsb29rdXAoKSBjYWxsc1xuXHRcdCogZS5nLiwgY29uc3QgU2VudGllbmNlQ29uc3RydWN0b3IgPSBsb29rdXAoJ1NlbnRpZW5jZScpIG1hcHMgXCJTZW50aWVuY2VDb25zdHJ1Y3RvclwiIC0+IFwiU2VudGllbmNlXCJcblx0XHQqL1xuXHRwcml2YXRlIHRyYWNrTG9va3VwQXNzaWdubWVudCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHR5cGVQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShjYWxsLCB0eXBlUGF0aCk7XG5cdH1cblxuXHQvKipcblx0XHQqIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnRzIGZyb20gbmV3IFR5cGUoKSBjYWxsc1xuXHRcdCogZS5nLiwgY29uc3QgdXNlciA9IG5ldyBVc2VyVHlwZSgpIG1hcHMgXCJ1c2VyXCIgLT4gXCJVc2VyVHlwZVwiXG5cdFx0Ki9cblx0cHJpdmF0ZSB0cmFja05ld0Fzc2lnbm1lbnQgKG5ld0V4cHI6IHRzLk5ld0V4cHJlc3Npb24sIHR5cGVQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHRsZXQgZWZmZWN0aXZlUGF0aCA9IHR5cGVQYXRoO1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbmV3RXhwci5wYXJlbnQ7XG5cdFx0Ly8gQ2hhaW4tZm9ybSBjb25zdHJ1Y3Rpb246IG5ldyBSKCkuQSgpLkIoKSDigJQgdGhlIHJlc3VsdCB2YXJpYWJsZVxuXHRcdC8vIGhvbGRzIHRoZSBPVVRFUk1PU1QgdGlwJ3MgaW5zdGFuY2UgKGF3YWl0LXRyYW5zcGFyZW50KSwgbm90IHRoZVxuXHRcdC8vIGlubmVyIG5ldydzIHR5cGUuIFdhbGsgdGhlIGNoYWluLCBrZWVwaW5nIHRoZSBsYXN0IHJlc29sdmFibGUgdGlwLlxuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY3VycmVudCkgJiZcblx0XHRcdFx0dHMuaXNDYWxsRXhwcmVzc2lvbihjdXJyZW50LnBhcmVudCkgJiZcblx0XHRcdFx0Y3VycmVudC5wYXJlbnQuZXhwcmVzc2lvbiA9PT0gY3VycmVudCkge1xuXHRcdFx0XHRjb25zdCB0aXAgPSB0aGlzLnJlc29sdmVDaGFpblRpcFR5cGVQYXRoKGN1cnJlbnQucGFyZW50KTtcblx0XHRcdFx0aWYgKHRpcCkge1xuXHRcdFx0XHRcdGVmZmVjdGl2ZVBhdGggPSB0aXA7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50LnBhcmVudDtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRicmVhaztcblx0XHR9XG5cdFx0dGhpcy5iaW5kUmVzdWx0VmFyaWFibGUobmV3RXhwciwgZWZmZWN0aXZlUGF0aCk7XG5cdH1cblxuXHQvKipcblx0ICogQmluZCB0aGUgbmVhcmVzdCBlbmNsb3NpbmcgYGNvbnN0L2xldC92YXIgWCA9IOKApmAgdG8gYSBtbmVtb25pY2Fcblx0ICogZnVsbFBhdGgg4oCUIHRoZSBzaGFyZWQgcmVzdWx0LXZhcmlhYmxlIHdhbGtlciBiZWhpbmQgbmV3L2xvb2t1cC9cblx0ICogY2hhaW4vZm9yay9tZXJnZS9jYWxsIHRyYWNraW5nICh2YWx1ZSBzY29wZTogZG93bnN0cmVhbSByZWZlcmVuY2VzXG5cdCAqIGFuZCBgdGhpcy54ID0geGAgYXNzaWdubWVudHMgcmVzb2x2ZSB0aHJvdWdoIHRoZSBzYW1lIGJpbmRpbmcpLlxuXHQgKi9cblx0cHJpdmF0ZSBiaW5kUmVzdWx0VmFyaWFibGUgKGZyb206IHRzLk5vZGUsIHR5cGVQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IGZyb20ucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRcdC8vIEZvdW5kOiBjb25zdCBYID0gPGNvbnN0cnVjdGlvbj5cblx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50Lm5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgdmFyTmFtZSA9IGN1cnJlbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRcdHRoaXMudmFyaWFibGVUb1R5cGVNYXAuc2V0KHZhck5hbWUsIHR5cGVQYXRoKTtcblx0XHRcdFx0XHR0aGlzLnRyYWNrRmlsZUdyYXBoQmluZGluZyh2YXJOYW1lLCB0eXBlUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgYW4gYGluc3RhbnRpYXRpb25gIHVzYWdlIGZvciBhIGNvbnN0cnVjdGlvbi1zaGFwZSBjYWxsXG5cdCAqIChjaGFpbiB0aXAgLyBjYWxsIC8gYXBwbHkgLyBmb3JrIC8gY2xvbmUgLyBtZXJnZSDigJRcblx0ICogYnl0ZS1pbmRpc3Rpbmd1aXNoYWJsZSBmcm9tIGBuZXdgIHVudGlsIHRoZSBkZWZlcnJlZFxuXHQgKiBtZWNoYW5pc20ta2luZCByZXZpc2lvbikuIGBjb25zdHJ1Y3RvclRleHRgIGRlZmF1bHRzIHRvIHRoZSBjYWxsZWVcblx0ICogZXhwcmVzc2lvbiB0ZXh0IHNvIHRoZSBzaXRlIHN0YXlzIHJlYWRhYmxlIHdpdGhvdXQgbmV3IGZpZWxkcztcblx0ICogY2FsbC9hcHBseSBvdmVycmlkZSBpdCB3aXRoIHRoZSBDdG9yIGFyZ3VtZW50IHRleHQuXG5cdCAqL1xuXHRwcml2YXRlIHJlY29yZENvbnN0cnVjdGlvblVzYWdlIChcblx0XHRjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHR0eXBlUGF0aDogc3RyaW5nLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0Y29uc3RydWN0b3JUZXh0Pzogc3RyaW5nXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRjYWxsLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBjdG9yVGV4dCA9IGNvbnN0cnVjdG9yVGV4dCA/PyBjYWxsLmV4cHJlc3Npb24uZ2V0VGV4dChzb3VyY2VGaWxlKTtcblx0XHR0aGlzLmFkZFVzYWdlKHR5cGVQYXRoLCB7XG5cdFx0XHRsb2NhdGlvbiAgICAgICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdGtpbmQgICAgICAgICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdGNvZGUgICAgICAgICAgICA6IGNhbGwuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0Y29uc3RydWN0b3JUZXh0IDogY3RvclRleHQuc2xpY2UoMCwgMTAwKSxcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHRoZSB0eXBlIGEgY29uc3RydWN0aW9uLWNoYWluIHRpcCBjYWxsIGNvbnN0cnVjdHM6XG5cdCAqIGBuZXcgUiguLi4pLkEoLi4uKWAgY29uc3RydWN0cyBSLkE7IGBhd2FpdCBuZXcgUiguLi4pLkEoLi4uKS5CKC4uLilgXG5cdCAqIGNvbnN0cnVjdHMgUi5BLkIuIFRoZSByZWNlaXZlciBpcyB0aGUgbmVzdGVkIGNoYWluIChOZXdFeHByZXNzaW9uXG5cdCAqIGJhc2UsIHRoZW4gdGlwIGNhbGxzKTsgZXhhY3QgZnVsbFBhdGggZmlyc3QsIGFuZCBvbmx5IHdoZW4gdGhlIHJvb3Rcblx0ICogaXRzZWxmIGlzIHVua25vd24gZG9lcyB0aGUgcHJvcC1uYW1lIGZhbGxiYWNrIGxhdyBhcHBseSAoc28gcGxhaW5cblx0ICogbWV0aG9kIGNhbGxzIG9uIGZyZXNoIGluc3RhbmNlcyBuZXZlciByZWNvcmQgYSBjb25zdHJ1Y3Rpb24pLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlQ2hhaW5UaXBUeXBlUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmVjZWl2ZXIgPSBjYWxsLmV4cHJlc3Npb247XG5cdFx0bGV0IHJvb3RQYXRoOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdFx0aWYgKHRzLmlzTmV3RXhwcmVzc2lvbihyZWNlaXZlci5leHByZXNzaW9uKSkge1xuXHRcdFx0Y29uc3QgaW5uZXIgPSByZWNlaXZlci5leHByZXNzaW9uO1xuXHRcdFx0cm9vdFBhdGggPSB0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihpbm5lci5leHByZXNzaW9uKVxuXHRcdFx0XHQ/IHRoaXMucmVzb2x2ZVR5cGVQYXRoKGlubmVyLmV4cHJlc3Npb24pXG5cdFx0XHRcdDogdGhpcy5nZXRUeXBlTmFtZUZyb21FeHByZXNzaW9uKGlubmVyLmV4cHJlc3Npb24pO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihyZWNlaXZlci5leHByZXNzaW9uKSkge1xuXHRcdFx0cm9vdFBhdGggPSB0aGlzLnJlc29sdmVDaGFpblRpcFR5cGVQYXRoKHJlY2VpdmVyLmV4cHJlc3Npb24pO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRpZiAoIXJvb3RQYXRoKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBjYW5kaWRhdGUgPSBgJHtyb290UGF0aH0uJHtyZWNlaXZlci5uYW1lLnRleHR9YDtcblx0XHRpZiAodGhpcy5kZWZpbml0aW9ucy5oYXMoY2FuZGlkYXRlKSkge1xuXHRcdFx0cmV0dXJuIGNhbmRpZGF0ZTtcblx0XHR9XG5cdFx0aWYgKCF0aGlzLmRlZmluaXRpb25zLmhhcyhyb290UGF0aCkpIHtcblx0XHRcdHJldHVybiB0aGlzLnJlc29sdmVUeXBlUGF0aChyZWNlaXZlcik7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogVHJ1ZSB3aGVuIGBleHByYCBkZW5vdGVzIGEgY29uc3RydWN0aW9uIGZ1bmN0aW9uIGltcG9ydGVkIGZyb21cblx0ICogJ21uZW1vbmljYScg4oCUIHRoZSBuYW1lZC1pbXBvcnQgZm9ybSAoYGltcG9ydCB7IGNhbGwgfSBmcm9tXG5cdCAqICdtbmVtb25pY2EnYCwgYWxpYXNlcyBpbmNsdWRlZCkgb3IgYSBtZW1iZXIgb2YgYSB0cmFja2VkXG5cdCAqIG1vZHVsZS1vYmplY3QgYWxpYXMgKGBtbmVtb25pY2EuY2FsbGApLiBVc2VybGFuZCBjYWxsL2FwcGx5L2JpbmRcblx0ICogZnVuY3Rpb25zIG5ldmVyIG1hdGNoLlxuXHQgKi9cblx0cHJpdmF0ZSBpc01uZW1vbmljYUNvbnN0cnVjdGlvbkZuIChleHByOiB0cy5FeHByZXNzaW9uLCBmbjogJ2NhbGwnIHwgJ2FwcGx5JyB8ICdiaW5kJyk6IGJvb2xlYW4ge1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChleHByLnRleHQpO1xuXHRcdFx0Y29uc3QgbWF0Y2hlZCA9IGltcG9ydGVkID09PSBmbjtcblx0XHRcdHJldHVybiBtYXRjaGVkO1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikgJiYgZXhwci5uYW1lLnRleHQgPT09IGZuKSB7XG5cdFx0XHRjb25zdCBtYXRjaGVkID0gdHMuaXNJZGVudGlmaWVyKGV4cHIuZXhwcmVzc2lvbikgJiZcblx0XHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuaGFzKGV4cHIuZXhwcmVzc2lvbi50ZXh0KTtcblx0XHRcdHJldHVybiBtYXRjaGVkO1xuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogbW5lbW9uaWNhIGNhbGwvYXBwbHkoZW50aXR5LCBDdG9yLCAuLi4pIC8gYmluZChlbnRpdHksIEN0b3IpOlxuXHQgKiByZXNvbHZlIHRoZSBDdG9yIGFyZ3VtZW50IChhcmcgMSkgdG8gYSBncmFwaCBmdWxsUGF0aCB0aHJvdWdoIHRoZVxuXHQgKiBzYW1lIHRpZXJzIGFzIHRoZSBgbmV3YCBicmFuY2ggKHZhbHVlIHNjb3BlIGZvciBpZGVudGlmaWVycyxcblx0ICogY2hhaW4gcmVzb2x1dGlvbiBmb3IgcHJvcGVydHkgYWNjZXNzZXMpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlQ29uc3RydWN0aW9uRm5UeXBlUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGNhbGxlZSA9IGNhbGwuZXhwcmVzc2lvbjtcblx0XHRjb25zdCBpc0NhbGxPckFwcGx5ID0gdGhpcy5pc01uZW1vbmljYUNvbnN0cnVjdGlvbkZuKGNhbGxlZSwgJ2NhbGwnKSB8fFxuXHRcdFx0dGhpcy5pc01uZW1vbmljYUNvbnN0cnVjdGlvbkZuKGNhbGxlZSwgJ2FwcGx5Jyk7XG5cdFx0Y29uc3QgaXNCaW5kID0gdGhpcy5pc01uZW1vbmljYUNvbnN0cnVjdGlvbkZuKGNhbGxlZSwgJ2JpbmQnKTtcblx0XHRpZiAoIWlzQ2FsbE9yQXBwbHkgJiYgIWlzQmluZCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0aWYgKGNhbGwuYXJndW1lbnRzLmxlbmd0aCA8IDIpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IFsgLCBjdG9yQXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblx0XHRsZXQgcmVzb2x2ZWQ6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY3RvckFyZykpIHtcblx0XHRcdHJlc29sdmVkID0gdGhpcy5yZXNvbHZlVHlwZVBhdGgoY3RvckFyZyk7XG5cdFx0fSBlbHNlIGlmICh0cy5pc0lkZW50aWZpZXIoY3RvckFyZykpIHtcblx0XHRcdGNvbnN0IGJvdW5kID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQoY3RvckFyZy50ZXh0KTtcblx0XHRcdGlmIChib3VuZCkge1xuXHRcdFx0XHRyZXNvbHZlZCA9IGJvdW5kO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgZ3JhcGhSZXN1bHQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKGN0b3JBcmcudGV4dCk7XG5cdFx0XHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRcdFx0cmVzb2x2ZWQgPSBncmFwaFJlc3VsdC5ub2RlLmZ1bGxQYXRoO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGNvbnN0IGtub3duID0gcmVzb2x2ZWQgJiYgdGhpcy5kZWZpbml0aW9ucy5oYXMocmVzb2x2ZWQpID8gcmVzb2x2ZWQgOiB1bmRlZmluZWQ7XG5cdFx0cmV0dXJuIGtub3duO1xuXHR9XG5cblx0LyoqXG5cdCAqIGluc3RhbmNlLmZvcmsoLi4uKSAvIGluc3RhbmNlLmNsb25lKC4uLikgb24gYSB0cmFja2VkIHZhcmlhYmxlIOKAlFxuXHQgKiBydW50aW1lIHJldHVybnMgYHRoaXNgLCBzbyB0aGUgcmVzdWx0IGNhcnJpZXMgdGhlIHNvdXJjZSB0eXBlLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRm9ya0xpa2VUeXBlUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgbWV0aG9kID0gY2FsbC5leHByZXNzaW9uLm5hbWUudGV4dDtcblx0XHRpZiAobWV0aG9kICE9PSAnZm9yaycgJiYgbWV0aG9kICE9PSAnY2xvbmUnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZWNlaXZlciA9IGNhbGwuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHJlY2VpdmVyKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQocmVjZWl2ZXIudGV4dCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGcmVlIHV0aWxzIGZvcm1zOiB1dGlscy5tZXJnZShhLCBiLCAuLi4pIChhbHNvIHRoZSBkaXJlY3QgbmFtZWRcblx0ICogaW1wb3J0IGBtZXJnZShhLCBiKWApIGFuZCB0aGUgY3VycmllZCB1dGlscy5mb3JrKGluc3RhbmNlKSguLi4pLlxuXHQgKiBUaGUgcmVzdWx0IGJpbmRzIHRvIGFyZyAwJ3MgdHlwZSDigJQgcnVudGltZSByZXR1cm5zIGEncyBsaW5lYWdlIG92ZXJcblx0ICogYidzIGNvbnRleHQ7IGEncyBmdWxsUGF0aCBpcyB0aGUgaG9uZXN0IGFwcHJveGltYXRpb24gd2l0aGluIHRoZVxuXHQgKiBvdXRwdXQgY29udHJhY3QgKGRvY3VtZW50ZWQgaW4gUkVBRE1FKS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVV0aWxzRm5UeXBlUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGNhbGxlZSA9IGNhbGwuZXhwcmVzc2lvbjtcblx0XHRjb25zdCBpc1V0aWxzT3duZXIgPSAob3duZXI6IHRzLkV4cHJlc3Npb24pOiBib29sZWFuID0+IHtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIob3duZXIpKSB7XG5cdFx0XHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChvd25lci50ZXh0KTtcblx0XHRcdFx0cmV0dXJuIGltcG9ydGVkID09PSAndXRpbHMnO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbWF0Y2hlZCA9IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG93bmVyKSAmJiBvd25lci5uYW1lLnRleHQgPT09ICd1dGlscycgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKG93bmVyLmV4cHJlc3Npb24pICYmIHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhvd25lci5leHByZXNzaW9uLnRleHQpO1xuXHRcdFx0cmV0dXJuIG1hdGNoZWQ7XG5cdFx0fTtcblx0XHRsZXQgc3ViamVjdEFyZzogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZDtcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbGVlKSAmJiBpc1V0aWxzT3duZXIoY2FsbGVlLmV4cHJlc3Npb24pICYmXG5cdFx0XHQoY2FsbGVlLm5hbWUudGV4dCA9PT0gJ21lcmdlJyB8fCBjYWxsZWUubmFtZS50ZXh0ID09PSAnZm9yaycpKSB7XG5cdFx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblx0XHRcdHN1YmplY3RBcmcgPSBmaXJzdEFyZztcblx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihjYWxsZWUpKSB7XG5cdFx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMubW5lbW9uaWNhTmFtZWRJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQoY2FsbGVlLnRleHQpO1xuXHRcdFx0aWYgKGltcG9ydGVkID09PSAnbWVyZ2UnIHx8IGltcG9ydGVkID09PSAnZm9yaycpIHtcblx0XHRcdFx0Y29uc3QgWyBmaXJzdEFyZyBdID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0XHRcdHN1YmplY3RBcmcgPSBmaXJzdEFyZztcblx0XHRcdH1cblx0XHR9IGVsc2UgaWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oY2FsbGVlKSAmJiB0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsZWUuZXhwcmVzc2lvbikgJiZcblx0XHRcdGNhbGxlZS5leHByZXNzaW9uLm5hbWUudGV4dCA9PT0gJ2ZvcmsnICYmIGlzVXRpbHNPd25lcihjYWxsZWUuZXhwcmVzc2lvbi5leHByZXNzaW9uKSkge1xuXHRcdFx0Ly8gdXRpbHMuZm9yayhpbnN0YW5jZSkoLi4uYXJncykg4oCUIHRoZSBjdXJyaWVkIGZvcm1cblx0XHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGNhbGxlZS5hcmd1bWVudHM7XG5cdFx0XHRzdWJqZWN0QXJnID0gZmlyc3RBcmc7XG5cdFx0fVxuXHRcdGlmICghc3ViamVjdEFyZyB8fCAhdHMuaXNJZGVudGlmaWVyKHN1YmplY3RBcmcpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChzdWJqZWN0QXJnLnRleHQpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXG5cdC8qKlxuXHRcdCogUHJvY2VzcyBhIEBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHQgKi9cblx0cHJpdmF0ZSBwcm9jZXNzRGVjb3JhdGVEZWNvcmF0b3IgKFxuXHRcdGRlY29yYXRvcjogdHMuRGVjb3JhdG9yLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0Y2xhc3NEZWNsUGFyYW0/OiB0cy5DbGFzc0RlY2xhcmF0aW9uXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRkZWNvcmF0b3IuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXG5cdFx0Ly8gR2V0IHRoZSBjbGFzcyBkZWNsYXJhdGlvbiAtIHVzZSB0aGUgcGFzc2VkIGNvbnRleHQgaWYgcGFyZW50IGlzIG5vdCBzZXRcblx0XHRjb25zdCBjbGFzc0RlY2wgPSBkZWNvcmF0b3IucGFyZW50IGFzIHRzLkNsYXNzRGVjbGFyYXRpb24gfCB1bmRlZmluZWQgfHwgY2xhc3NEZWNsUGFyYW07XG5cdFx0aWYgKCFjbGFzc0RlY2wgfHwgIWNsYXNzRGVjbC5uYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdEZWNvcmF0ZWQgY2xhc3MgaGFzIG5vIG5hbWUnLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHR5cGVOYW1lID0gY2xhc3NEZWNsLm5hbWUudGV4dDtcblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdEZWNvcmF0ZWQgY2xhc3MgaGFzIG5vIG5hbWUnLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFBhcnNlIGRlY29yYXRvciBhcmd1bWVudHM6IEBkZWNvcmF0ZSgpLCBAZGVjb3JhdGUoUGFyZW50KSxcblx0XHQvLyBAZGVjb3JhdGUoeyAuLi4gfSksIEBkZWNvcmF0ZShQYXJlbnQsIHsgLi4uIH0pLFxuXHRcdC8vIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSwgQE15Q29sbGVjdGlvbi5kZWNvcmF0ZSh7IC4uLiB9KVxuXHRcdGxldCBwYXJlbnROb2RlOiBUeXBlTm9kZSB8IHVuZGVmaW5lZDtcblx0XHRsZXQgcGFyZW50RnVsbFBhdGg6IHN0cmluZyB8IG51bGwgPSBudWxsO1xuXHRcdGxldCBjb2xsZWN0aW9uSWQ6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRsZXQgZGVjb3JhdG9yQ29uZmlnOiB7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0gPSB7fTtcblxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGRlY29yYXRvci5leHByZXNzaW9uKSkge1xuXHRcdFx0Y29uc3QgY2FsbEV4cHIgPSBkZWNvcmF0b3IuZXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IGNhbGxlZSA9IGNhbGxFeHByLmV4cHJlc3Npb247XG5cblx0XHRcdC8vIENoZWNrIGZvciBATXlDb2xsZWN0aW9uLmRlY29yYXRlKCkgd2hlcmUgTXlDb2xsZWN0aW9uIGlzIGEgY3VzdG9tIGNvbGxlY3Rpb24uXG5cdFx0XHQvLyBUaGUgZGVjb3JhdGVkIGNsYXNzIGJlY29tZXMgYSByb290IHR5cGUgaW4gdGhhdCBjb2xsZWN0aW9uLlxuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsZWUpICYmXG5cdFx0XHRcdGNhbGxlZS5uYW1lLnRleHQgPT09ICdkZWNvcmF0ZScgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGNhbGxlZS5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGNhbGxlZS5leHByZXNzaW9uLnRleHQpXG5cdFx0XHQpIHtcblx0XHRcdFx0Y29sbGVjdGlvbklkID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChjYWxsZWUuZXhwcmVzc2lvbi50ZXh0KTtcblx0XHRcdFx0aWYgKGNhbGxFeHByLmFyZ3VtZW50cy5sZW5ndGggPT09IDEgJiYgdHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihjYWxsRXhwci5hcmd1bWVudHNbIDAgXSkpIHtcblx0XHRcdFx0XHRkZWNvcmF0b3JDb25maWcgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjYWxsRXhwci5hcmd1bWVudHNbIDAgXSk7XG5cdFx0XHRcdH1cblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGNvbnN0IGFyZ3MgPSBjYWxsRXhwci5hcmd1bWVudHM7XG5cdFx0XHRcdGxldCBwYXJlbnRBcmc6IHRzLklkZW50aWZpZXIgfCB1bmRlZmluZWQ7XG5cdFx0XHRcdGxldCBjb25maWdBcmc6IHRzLk9iamVjdExpdGVyYWxFeHByZXNzaW9uIHwgdW5kZWZpbmVkO1xuXG5cdFx0XHRcdGZvciAoY29uc3QgYXJnIG9mIGFyZ3MpIHtcblx0XHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdFx0XHRcdGlmIChwYXJlbnRBcmcpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdFx0XHRcdFx0bWVzc2FnZSA6ICdAZGVjb3JhdGUoKSBhY2NlcHRzIG9ubHkgb25lIHBhcmVudCByZWZlcmVuY2UnLFxuXHRcdFx0XHRcdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0XHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0XHRwYXJlbnRBcmcgPSBhcmc7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdFx0XHRcdGlmIChjb25maWdBcmcpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdFx0XHRcdFx0bWVzc2FnZSA6ICdAZGVjb3JhdGUoKSBhY2NlcHRzIG9ubHkgb25lIGNvbmZpZyBvYmplY3QnLFxuXHRcdFx0XHRcdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0XHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0XHRjb25maWdBcmcgPSBhcmc7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0aWYgKHBhcmVudEFyZykge1xuXHRcdFx0XHRcdHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlJZGVudGlmaWVyKHBhcmVudEFyZy50ZXh0KTtcblx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0XHRcdFx0cGFyZW50RnVsbFBhdGggPSBwYXJlbnROb2RlLmZ1bGxQYXRoO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGlmIChjb25maWdBcmcpIHtcblx0XHRcdFx0XHRkZWNvcmF0b3JDb25maWcgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjb25maWdBcmcpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gQnVpbGQgZnVsbCBwYXRoXG5cdFx0Y29uc3QgZnVsbFBhdGggPSBwYXJlbnROb2RlID8gYCR7cGFyZW50Tm9kZS5mdWxsUGF0aH0uJHt0eXBlTmFtZX1gIDogdHlwZU5hbWU7XG5cblx0XHQvLyBDcmVhdGUgZGVmaW5pdGlvbiBpbmZvIGZvciBkZWNvcmF0ZVxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWNvcmF0ZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IHBhcmVudEZ1bGxQYXRoLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiBkZWNvcmF0b3JDb25maWcuc3RyaWN0Q2hhaW4gPz8gdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogZGVjb3JhdG9yQ29uZmlnLmJsb2NrRXJyb3JzID8/IGZhbHNlLFxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQoZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXHRcdHRoaXMuZWRzU2NvcGVCeU5vZGUuc2V0KGNsYXNzRGVjbCwgZnVsbFBhdGgpO1xuXG5cdFx0Ly8gQ3JlYXRlIHR5cGUgbm9kZVxuXHRcdGNvbnN0IG5vZGUgPSBUeXBlR3JhcGhJbXBsLmNyZWF0ZU5vZGUoXG5cdFx0XHR0eXBlTmFtZSxcblx0XHRcdHBhcmVudE5vZGUsXG5cdFx0XHRzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0bGluZSArIDEsXG5cdFx0XHRjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0Y29sbGVjdGlvbklkXG5cdFx0KTtcblx0XHRub2RlLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA9IHRoaXMuZ2V0UmVnaXN0cnlJbnRlcmZhY2VOYW1lKG5vZGUuY29sbGVjdGlvbklkKTtcblxuXHRcdC8vIFNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZSBkZXRlY3Rpb24gKGhhcmQtZmFpbCBsYXcpXG5cdFx0dGhpcy5yZWNvcmREZWZpbmVTaXRlKFxuXHRcdFx0cGFyZW50Tm9kZSA/IGAke3BhcmVudE5vZGUuZnVsbFBhdGh9LiR7dHlwZU5hbWV9YCA6IGAke2NvbGxlY3Rpb25JZCA/PyAnZGVmYXVsdCd9Ojoke3R5cGVOYW1lfWAsXG5cdFx0XHRgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YFxuXHRcdCk7XG5cblx0XHQvLyBFeHRyYWN0IHByb3BlcnRpZXMgYW5kIGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBjbGFzcyBtZW1iZXJzIOKAlFxuXHRcdC8vIHRoZSBuZXcgbm9kZSBhbmNob3JzIHJlbGF0aXZlLWZpcnN0IGdyYXBoIHJlZmVyZW5jZSByZXNvbHV0aW9uXG5cdFx0Y29uc3QgcHJldmlvdXNBbmNob3IgPSB0aGlzLmN1cnJlbnRHcmFwaEFuY2hvcjtcblx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IG5vZGU7XG5cdFx0dHJ5IHtcblx0XHRcdG5vZGUucHJvcGVydGllcyA9IHRoaXMuZXh0cmFjdENsYXNzUHJvcGVydGllcyhjbGFzc0RlY2wpO1xuXHRcdFx0bm9kZS5jb25zdHJ1Y3RvclBhcmFtcyA9IHRoaXMuZXh0cmFjdENsYXNzQ29uc3RydWN0b3JQYXJhbXMoY2xhc3NEZWNsKTtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBwcmV2aW91c0FuY2hvcjtcblx0XHR9XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGhcblx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChwYXJlbnROb2RlLCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KG5vZGUpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHR5cGUgbmFtZSBmcm9tIGRlZmluZSgpIGNhbGwgYXJndW1lbnRzLlxuXHQgKiBIYW5kbGVzOlxuXHQgKiAgIGRlZmluZSgnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHQgKiAgIGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpICAgLy8gZXhwbGljaXQtc291cmNlIGZvcm1cblx0ICogICBkZWZpbmUoZnVuY3Rpb24gVHlwZU5hbWUoKSB7fSlcblx0ICogICBkZWZpbmUoKCkgPT4gY2xhc3MgVHlwZU5hbWUge30pXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RUeXBlTmFtZSAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGFyZ3MgPSBjYWxsLmFyZ3VtZW50cztcblxuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBhcmdzO1xuXG5cdFx0Ly8gRXhwbGljaXQtc291cmNlIGZvcm06IGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIgJiYgdHMuaXNJZGVudGlmaWVyKGZpcnN0QXJnKSAmJiB0cy5pc1N0cmluZ0xpdGVyYWwoYXJnc1sgMSBdKSkge1xuXHRcdFx0cmV0dXJuIGFyZ3NbIDEgXS50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIFN0cmluZyBsaXRlcmFsOiBkZWZpbmUoJ1R5cGVOYW1lJywgLi4uKVxuXHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoZmlyc3RBcmcpKSB7XG5cdFx0XHRyZXR1cm4gZmlyc3RBcmcudGV4dDtcblx0XHR9XG5cblx0XHQvLyBGdW5jdGlvbiB3aXRoIG5hbWU6IGRlZmluZShmdW5jdGlvbiBUeXBlTmFtZSgpIHt9KVxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihmaXJzdEFyZykgJiYgZmlyc3RBcmcubmFtZSkge1xuXHRcdFx0cmV0dXJuIGZpcnN0QXJnLm5hbWUudGV4dDtcblx0XHR9XG5cblx0XHQvLyBBcnJvdyBmdW5jdGlvbiByZXR1cm5pbmcgY2xhc3M6IGRlZmluZSgoKSA9PiBjbGFzcyBUeXBlTmFtZSB7fSlcblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGZpcnN0QXJnKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBmaXJzdEFyZztcblx0XHRcdGlmICh0cy5pc0NsYXNzRXhwcmVzc2lvbihib2R5KSAmJiBib2R5Lm5hbWUpIHtcblx0XHRcdFx0cmV0dXJuIGJvZHkubmFtZS50ZXh0O1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0aGUgZnVsbCBkZWZpbmUoKSBjYWxsIGNvbnRleHQ6IHR5cGUgbmFtZSwgcGFyZW50IHR5cGUsIGFuZCBjb2xsZWN0aW9uLlxuXHQgKiBIYW5kbGVzIGRpcmVjdCBjYWxscywgcHJvcGVydHktYWNjZXNzIGNhbGxzLCBjaGFpbmVkIGNhbGxzLCBhbmQgdGhlXG5cdCAqIGV4cGxpY2l0LXNvdXJjZSBmb3JtIGBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKWAuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3REZWZpbmVDb250ZXh0IChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHtcblx0XHR0eXBlTmFtZT86IHN0cmluZztcblx0XHRwYXJlbnRUeXBlPzogVHlwZU5vZGU7XG5cdFx0Y29sbGVjdGlvbklkPzogc3RyaW5nO1xuXHR9IHtcblx0XHRjb25zdCB0eXBlTmFtZSA9IHRoaXMuZXh0cmFjdFR5cGVOYW1lKGNhbGwpO1xuXHRcdGlmICghdHlwZU5hbWUpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IGNhbGw7XG5cblx0XHQvLyBEaXJlY3QgY2FsbDogZGVmaW5lKCdUeXBlTmFtZScsIC4uLikgb3IgZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2RlZmluZScpIHtcblx0XHRcdC8vIEV4cGxpY2l0LXNvdXJjZSBmb3JtOiBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHRcdFx0aWYgKGNhbGwuYXJndW1lbnRzLmxlbmd0aCA+PSAyICYmIHRzLmlzSWRlbnRpZmllcihjYWxsLmFyZ3VtZW50c1sgMCBdKSkge1xuXHRcdFx0XHRjb25zdCBzb3VyY2VOYW1lID0gY2FsbC5hcmd1bWVudHNbIDAgXS50ZXh0O1xuXHRcdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKHNvdXJjZU5hbWUpO1xuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0XHRcdHBhcmVudFR5cGUgICA6IHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSxcblx0XHRcdFx0XHRjb2xsZWN0aW9uSWQgOiBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCxcblx0XHRcdFx0fTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gUGxhaW4gcm9vdCBkZWZpbmUgaW4gZGVmYXVsdCBjb2xsZWN0aW9uXG5cdFx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2VzczogWC5kZWZpbmUoJ1R5cGVOYW1lJywgLi4uKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLm5hbWUudGV4dCA9PT0gJ2RlZmluZScpIHtcblx0XHRcdGNvbnN0IG9iaiA9IGV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblxuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihvYmopKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uob2JqLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0XHRcdHBhcmVudFR5cGUgICA6IHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSxcblx0XHRcdFx0XHRjb2xsZWN0aW9uSWQgOiBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCxcblx0XHRcdFx0fTtcblx0XHRcdH1cblxuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gTmVzdGVkIGFjY2VzczogaW5zdGFuY2UuVHlwZS5kZWZpbmUgLSB0cnkgdG8gcmVzb2x2ZVxuXHRcdFx0XHRjb25zdCBjaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlDaGFpbihvYmopO1xuXHRcdFx0XHRpZiAoY2hhaW4ubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGNoYWluLmpvaW4oJy4nKSk7XG5cdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlIH07XG5cdFx0XHRcdH1cblx0XHRcdH1cblxuXHRcdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBEZXRlcm1pbmUgdGhlIGNvbGxlY3Rpb24gY29udGV4dCBmcm9tIHRoZSByb290IG9mIHRoZSBjaGFpbiBzbyB0aGF0XG5cdFx0XHRcdC8vIGN1c3RvbS1jb2xsZWN0aW9uIHR5cGVzIGRvIG5vdCBnZXQgY29uZnVzZWQgd2l0aCBkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMuXG5cdFx0XHRcdGNvbnN0IHJvb3RJZCA9IHRoaXMuZ2V0Um9vdElkZW50aWZpZXIob2JqLmV4cHJlc3Npb24pO1xuXHRcdFx0XHRjb25zdCBleHBlY3RlZENvbGxlY3Rpb25JZCA9IHJvb3RJZFxuXHRcdFx0XHRcdD8gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKHJvb3RJZC50ZXh0KS5jb2xsZWN0aW9uSWRcblx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblxuXHRcdFx0XHQvLyBDaGFpbmVkIGNhbGw6IGRlZmluZSgnQScpLmRlZmluZSgnQicpIG9yIG1uZW1vbmljYS5kZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKVxuXHRcdFx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwob2JqKSkge1xuXHRcdFx0XHRcdHRoaXMucHJvY2Vzc0RlZmluZUNhbGwob2JqLCBjYWxsLmdldFNvdXJjZUZpbGUoKSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdC8vIEluaGVyaXQgY29sbGVjdGlvbiBmcm9tIHRoZSBwYXJlbnQgdHlwZSAoaWYgYW55KVxuXHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBDaGFpbmVkIGxhenkgY2FsbDogbGF6eSgnQScpLmRlZmluZSgnQicpIG9yIFR5cGUubGF6eSgnQScpLmRlZmluZSgnQicpXG5cdFx0XHRcdGlmICh0aGlzLmlzTGF6eUNhbGwob2JqKSkge1xuXHRcdFx0XHRcdHRoaXMucHJvY2Vzc0xhenlDYWxsKG9iaiwgY2FsbC5nZXRTb3VyY2VGaWxlKCkpO1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudFR5cGVOYW1lID0gdGhpcy5leHRyYWN0TW5lbW9uaWNhVHlwZU5hbWUob2JqKTtcblx0XHRcdFx0XHRpZiAocGFyZW50VHlwZU5hbWUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKHBhcmVudFR5cGVOYW1lLCBleHBlY3RlZENvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIEJ1aWxkZXIgbG9va3VwIGNoYWluOiBBcHAubG9va3VwKCdVc2VyJykuZGVmaW5lKCdBZG1pbicpXG5cdFx0XHRcdGlmICh0aGlzLmlzTG9va3VwQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0Y29uc3QgbG9va2VkVXBQYXRoID0gdGhpcy5yZXNvbHZlTG9va3VwUGF0aChvYmopO1xuXHRcdFx0XHRcdGlmIChsb29rZWRVcFBhdGgpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGxvb2tlZFVwUGF0aCk7XG5cdFx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGUuY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHsgdHlwZU5hbWUgfTtcblx0fVxuXG5cdC8qKlxuXHQgKiBQcmVmaXggYSBkb3R0ZWQgdHlwZSBwYXRoIHdpdGggYSBjb2xsZWN0aW9uIGlkZW50aWZpZXIgc28gY3VzdG9tLWNvbGxlY3Rpb25cblx0ICogdHlwZXMgZG8gbm90IGNvbGxpZGUgd2l0aCBkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMgaW4gdGhlIGdyYXBoLlxuXHQgKi9cblx0cHJpdmF0ZSBwcmVmaXhDb2xsZWN0aW9uUGF0aCAocGF0aDogc3RyaW5nLCBjb2xsZWN0aW9uSWQ6IHN0cmluZyk6IHN0cmluZyB7XG5cdFx0cmV0dXJuIGAke2NvbGxlY3Rpb25JZH06OiR7cGF0aH1gO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSBkZWZpbmUoKSBzb3VyY2UgaWRlbnRpZmllciB0byBlaXRoZXIgYSBwYXJlbnQgdHlwZSwgYSBjb2xsZWN0aW9uLFxuXHQgKiBvciB0aGUgZGVmYXVsdCAobW9kdWxlIG9iamVjdCkgY29sbGVjdGlvbi5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZURlZmluZVNvdXJjZSAoc291cmNlTmFtZTogc3RyaW5nKToge1xuXHRcdHBhcmVudFR5cGU/OiBUeXBlTm9kZTtcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmc7XG5cdH0ge1xuXHRcdC8vIE1vZHVsZSBvYmplY3QgYWxpYXNlcyAtPiByb290IGluIGRlZmF1bHQgY29sbGVjdGlvblxuXHRcdGlmICh0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoc291cmNlTmFtZSkpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHQvLyBDb2xsZWN0aW9uIHZhcmlhYmxlcyAtPiByb290IGluIHRoYXQgY29sbGVjdGlvblxuXHRcdGNvbnN0IGNvbGxlY3Rpb25JZCA9IHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5nZXQoc291cmNlTmFtZSk7XG5cdFx0aWYgKGNvbGxlY3Rpb25JZCkge1xuXHRcdFx0cmV0dXJuIHsgY29sbGVjdGlvbklkIH07XG5cdFx0fVxuXG5cdFx0Ly8gT3RoZXJ3aXNlIHRyZWF0IGFzIGEgdHlwZSB2YXJpYWJsZSByZWZlcmVuY2Vcblx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5SWRlbnRpZmllcihzb3VyY2VOYW1lKTtcblx0XHRyZXR1cm4geyBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdH1cblxuXHQvKipcblx0ICogQ2hlY2sgaWYgYSBjYWxsIGV4cHJlc3Npb24gaXMgYSBsb29rdXAoKSBjYWxsLlxuXHQgKi9cblx0cHJpdmF0ZSBpc0xvb2t1cENhbGwgKG5vZGU6IHRzLkNhbGxFeHByZXNzaW9uKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgZXhwciA9IG5vZGUuZXhwcmVzc2lvbjtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpICYmIGV4cHIudGV4dCA9PT0gJ2xvb2t1cCcpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikgJiYgZXhwci5uYW1lLnRleHQgPT09ICdsb29rdXAnKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSBsb29rdXAoKSBjYWxsIHRvIGEgZG90dGVkIHR5cGUgcGF0aCAoYmVzdCBlZmZvcnQpLlxuXHQgKiBIYW5kbGVzOlxuXHQgKiAgIGxvb2t1cCgnVXNlcicpXG5cdCAqICAgbG9va3VwKHNvdXJjZSwgJ1VzZXInKVxuXHQgKiAgIEFwcC5sb29rdXAoJ1VzZXInKVxuXHQgKiAgIGNvbGxlY3Rpb24ubG9va3VwKCdVc2VyLkFkbWluJylcblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUxvb2t1cFBhdGggKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBhcmdzID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIFNpbmdsZS1hcmcgbG9va3VwOiBsb29rdXAoJ1VzZXInKSBvciBBcHAubG9va3VwKCdVc2VyJylcblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDEpIHtcblx0XHRcdGNvbnN0IFsgYXJnIF0gPSBhcmdzO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChhcmcpIHx8IHRzLmlzTm9TdWJzdGl0dXRpb25UZW1wbGF0ZUxpdGVyYWwoYXJnKSkge1xuXHRcdFx0XHRjb25zdCBwYXRoID0gYXJnLnRleHQ7XG5cdFx0XHRcdC8vIElmIHRoaXMgaXMgYSBtZXRob2QgY2FsbCBvbiBhIHNvdXJjZSwgcmVzb2x2ZSByZWxhdGl2ZSB0byB0aGF0IHNvdXJjZS5cblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRjb25zdCBzb3VyY2VFeHByID0gY2FsbC5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihzb3VyY2VFeHByKSkge1xuXHRcdFx0XHRcdFx0Y29uc3Qgc291cmNlTmFtZSA9IHNvdXJjZUV4cHIudGV4dDtcblx0XHRcdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRcdFx0XHRpZiAoc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQpIHtcblx0XHRcdFx0XHRcdFx0Ly8gQ29sbGVjdGlvbiBsb29rdXA6IHByZWZpeCBwYXRoIHdpdGggdGhlIGNvbGxlY3Rpb24gaWRcblx0XHRcdFx0XHRcdFx0cmV0dXJuIHRoaXMucHJlZml4Q29sbGVjdGlvblBhdGgocGF0aCwgc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSkge1xuXHRcdFx0XHRcdFx0XHQvLyBUeXBlIGxvb2t1cDogcmVsYXRpdmUgZmlyc3QsIHRoZW4gcm9vdCBmYWxsYmFja1xuXHRcdFx0XHRcdFx0XHRjb25zdCByZWxhdGl2ZVBhdGggPSBgJHtzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUuZnVsbFBhdGh9LiR7cGF0aH1gO1xuXHRcdFx0XHRcdFx0XHRpZiAodGhpcy5ncmFwaC5maW5kVHlwZShyZWxhdGl2ZVBhdGgpKSB7XG5cdFx0XHRcdFx0XHRcdFx0cmV0dXJuIHJlbGF0aXZlUGF0aDtcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHBhdGg7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIFR3by1hcmcgbG9va3VwOiBsb29rdXAoc291cmNlLCAnVXNlcicpXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIpIHtcblx0XHRcdGNvbnN0IFsgc291cmNlQXJnLCBwYXRoQXJnIF0gPSBhcmdzO1xuXHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoc291cmNlQXJnKSB8fCAhdHMuaXNTdHJpbmdMaXRlcmFsKHBhdGhBcmcpKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBzb3VyY2VOYW1lID0gc291cmNlQXJnLnRleHQ7XG5cdFx0XHRjb25zdCBwYXRoID0gcGF0aEFyZy50ZXh0O1xuXHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShzb3VyY2VOYW1lKTtcblx0XHRcdGlmIChzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCkge1xuXHRcdFx0XHRyZXR1cm4gdGhpcy5wcmVmaXhDb2xsZWN0aW9uUGF0aChwYXRoLCBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCk7XG5cdFx0XHR9XG5cdFx0XHRpZiAoc291cmNlQ29udGV4dC5wYXJlbnRUeXBlKSB7XG5cdFx0XHRcdGNvbnN0IHJlbGF0aXZlUGF0aCA9IGAke3NvdXJjZUNvbnRleHQucGFyZW50VHlwZS5mdWxsUGF0aH0uJHtwYXRofWA7XG5cdFx0XHRcdGlmICh0aGlzLmdyYXBoLmZpbmRUeXBlKHJlbGF0aXZlUGF0aCkpIHtcblx0XHRcdFx0XHRyZXR1cm4gcmVsYXRpdmVQYXRoO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiBwYXRoO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHBhdGg7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBMb29rdXAtbGF3IGRlbGVnYXRlIGZvciB0aGUgbG9jYWwtc2NvcGUgd2Fsa2VyIChzY29wZXMuanNvbiB0eXBlUGF0aFxuXHQgKiBtZXRhZGF0YSk6IHJlc29sdmUgYSBsb29rdXAoKSBpbml0aWFsaXplciBjYWxsIHRocm91Z2ggZXhhY3RseSB0aGVcblx0ICogdGllcnMgdGhlIHVzYWdlcyBwYXNzIHJlc29sdmVkIGl0IGFnYWluc3QgKHNhbWUgc291cmNlIHJlc29sdXRpb24sXG5cdCAqIHNhbWUgY29tcGxldGUgZ3JhcGgpLiBUaGUgd2Fsa2VyIHJ1bnMgaXRzIG93biBzY29wZS1jaGFpbiB2YWx1ZS1zY29wZVxuXHQgKiB0aWVyIGJlZm9yZSBkZWxlZ2F0aW5nOyBldmVyeXRoaW5nIGFib3ZlIHZhbHVlIHNjb3BlIGxhbmRzIGhlcmUsIHNvXG5cdCAqIHNjb3Blcy5qc29uIG5ldmVyIGRpc2FncmVlcyB3aXRoIHRoZSBoYXJkLWZhaWwtbGF3IHZlcmRpY3RzLlxuXHQgKi9cblx0cmVzb2x2ZUxvb2t1cENhbGxQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5yZXNvbHZlTG9va3VwUGF0aChjYWxsKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0KiBGaW5kIGEgcGFyZW50IHR5cGUgYnkgaXRzIG5hbWUsIHNlYXJjaGluZyBpbiB0aGUgZ3JhcGguXG5cdFx0KiBXaGVuIGNvbGxlY3Rpb25JZCBpcyBwcm92aWRlZCwgb25seSB0eXBlcyBmcm9tIHRoYXQgY29sbGVjdGlvbiBhcmUgY29uc2lkZXJlZC5cblx0XHQqL1xuXHRwcml2YXRlIGZpbmRQYXJlbnRUeXBlQnlOYW1lIChcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0Y29sbGVjdGlvbklkPzogc3RyaW5nXG5cdCk6IFR5cGVOb2RlIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBtYXRjaGVzQ29sbGVjdGlvbiA9ICh0eXBlOiBUeXBlTm9kZSk6IGJvb2xlYW4gPT4ge1xuXHRcdFx0aWYgKGNvbGxlY3Rpb25JZCA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdHJldHVybiB0eXBlLmNvbGxlY3Rpb25JZCA9PT0gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHR5cGUuY29sbGVjdGlvbklkID09PSBjb2xsZWN0aW9uSWQ7XG5cdFx0fTtcblxuXHRcdC8vIEZpcnN0IHRyeSBleGFjdCBtYXRjaCAoZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzIHVzZSB0aGUgcGxhaW4gZG90dGVkIHBhdGgpXG5cdFx0Y29uc3QgZXhhY3QgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKG5hbWUpO1xuXHRcdGlmIChleGFjdCAmJiBtYXRjaGVzQ29sbGVjdGlvbihleGFjdCkpIHtcblx0XHRcdHJldHVybiBleGFjdDtcblx0XHR9XG5cblx0XHQvLyBUaGVuIHNlYXJjaCB0aHJvdWdoIGFsbCB0eXBlcyBmb3Igb25lIHdpdGggbWF0Y2hpbmcgbmFtZSBhbmQgY29sbGVjdGlvblxuXHRcdGZvciAoY29uc3QgdHlwZSBvZiB0aGlzLmdyYXBoLmdldEFsbFR5cGVzKCkpIHtcblx0XHRcdGlmICh0eXBlLm5hbWUgPT09IG5hbWUgJiYgbWF0Y2hlc0NvbGxlY3Rpb24odHlwZSkpIHtcblx0XHRcdFx0cmV0dXJuIHR5cGU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHRcdCogRmluZCBhIHBhcmVudCB0eXBlIGZyb20gYW4gaWRlbnRpZmllciByZWZlcmVuY2UuXG5cdFx0KiBIYW5kbGVzIGJvdGggYWxpYXNlZCB2YXJpYWJsZXMgKGNvbnN0IFVzZXIgPSBkZWZpbmUoJ1VzZXJFbnRpdHknLCAuLi4pKVxuXHRcdCogYW5kIGRpcmVjdCBjbGFzcy90eXBlIG5hbWVzLlxuXHRcdCovXG5cdHByaXZhdGUgZmluZFBhcmVudFR5cGVCeUlkZW50aWZpZXIgKG5hbWU6IHN0cmluZyk6IFR5cGVOb2RlIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBGaXJzdCBjaGVjayB2YXJpYWJsZSBtYXBwaW5nOiBjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKVxuXHRcdGNvbnN0IG1hcHBlZEZ1bGxQYXRoID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0aWYgKG1hcHBlZEZ1bGxQYXRoKSB7XG5cdFx0XHRjb25zdCBtYXBwZWROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShtYXBwZWRGdWxsUGF0aCk7XG5cdFx0XHRpZiAobWFwcGVkTm9kZSkgcmV0dXJuIG1hcHBlZE5vZGU7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUobmFtZSk7XG5cdFx0cmV0dXJuIHBhcmVudE5vZGU7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IHRoZSBsZWZ0bW9zdCBpZGVudGlmaWVyIG9mIGEgcHJvcGVydHktYWNjZXNzIGNoYWluLlxuXHQgKiBGb3IgYEFwcC5kZWZpbmUoJ1VzZXInKS5kZWZpbmUoJ0FkbWluJylgIHRoaXMgcmV0dXJucyB0aGUgYEFwcGAgaWRlbnRpZmllci5cblx0ICovXG5cdHByaXZhdGUgZ2V0Um9vdElkZW50aWZpZXIgKGV4cHI6IHRzLkV4cHJlc3Npb24pOiB0cy5JZGVudGlmaWVyIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuRXhwcmVzc2lvbiA9IGV4cHI7XG5cdFx0d2hpbGUgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5leHByZXNzaW9uO1xuXHRcdH1cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQpKSB7XG5cdFx0XHRyZXR1cm4gY3VycmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHRcdCogR2V0IHByb3BlcnR5IGNoYWluIGZyb20gbmVzdGVkIGFjY2Vzc1xuXHRcdCovXG5cdHByaXZhdGUgZ2V0UHJvcGVydHlDaGFpbiAoZXhwcjogdHMuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uIHwgdHMuSWRlbnRpZmllcik6IHN0cmluZ1tdIHtcblx0XHRjb25zdCBjaGFpbjogc3RyaW5nW10gPSBbXTtcblxuXHRcdGxldCBjdXJyZW50OiB0cy5FeHByZXNzaW9uID0gZXhwcjtcblx0XHR3aGlsZSAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY3VycmVudCkpIHtcblx0XHRcdGlmIChjdXJyZW50Lm5hbWUpIHtcblx0XHRcdFx0Y2hhaW4udW5zaGlmdChjdXJyZW50Lm5hbWUudGV4dCk7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5leHByZXNzaW9uO1xuXHRcdH1cblxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudCkpIHtcblx0XHRcdGNoYWluLnVuc2hpZnQoY3VycmVudC50ZXh0KTtcblx0XHR9XG5cblx0XHRyZXR1cm4gY2hhaW47XG5cdH1cblxuXHQvKipcblx0ICogRGV0ZXJtaW5lIHRoZSBjb25zdHJ1Y3RvciBleHByZXNzaW9uIGZvciBlaXRoZXIgYSBkZWZpbmUoKSBvciBsYXp5KCkgY2FsbC5cblx0ICogRm9yIGRlZmluZSgpIHRoaXMgaXMgdGhlIGNvbnN0cnVjdCBoYW5kbGVyOyBmb3IgbGF6eSgpIGl0IGlzIHRoZSB2YWx1ZVxuXHQgKiByZXR1cm5lZCBieSB0aGUgbGF6eSBnZXR0ZXIuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24gKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgZXhwciA9IGNhbGwuZXhwcmVzc2lvbjtcblx0XHRjb25zdCBuYW1lID0gdHMuaXNJZGVudGlmaWVyKGV4cHIpXG5cdFx0XHQ/IGV4cHIudGV4dFxuXHRcdFx0OiB0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKVxuXHRcdFx0XHQ/IGV4cHIubmFtZS50ZXh0XG5cdFx0XHRcdDogJyc7XG5cblx0XHRpZiAobmFtZSA9PT0gJ2xhenknKSB7XG5cdFx0XHRjb25zdCBsYXp5QXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRcdGlmICghbGF6eUFyZ3MpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB0aGlzLnVud3JhcExhenlHZXR0ZXIobGF6eUFyZ3MuZ2V0dGVyKTtcblx0XHR9XG5cblx0XHQvLyBkZWZpbmUoKSBjYWxsXG5cdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBNb2Rlcm4gZm9ybTogZGVmaW5lKCdOYW1lJywgaGFuZGxlciwgY29uZmlnPylcblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGFyZ3NbIDAgXSkpIHtcblx0XHRcdHJldHVybiBhcmdzWyAxIF07XG5cdFx0fVxuXG5cdFx0Ly8gTGVnYWN5IGZvcm06IGRlZmluZShmdW5jdGlvbiBOYW1lKCkge30pIG9yIGRlZmluZSgoKSA9PiBjbGFzcyBOYW1lIHt9KVxuXHRcdHJldHVybiBhcmdzWyAwIF07XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gY29uc3RydWN0b3IgZnVuY3Rpb25cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFByb3BlcnRpZXMgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpO1xuXHRcdGlmICghY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRyZXR1cm4gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5leHRyYWN0UHJvcGVydGllc0Zyb21Db25zdHJ1Y3Rvcihjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gYSBjb25zdHJ1Y3RvciBleHByZXNzaW9uIChmdW5jdGlvbiwgYXJyb3csIG9yIGNsYXNzKS5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFByb3BlcnRpZXNGcm9tQ29uc3RydWN0b3IgKGNvbnN0cnVjdG9yRXhwcjogdHMuRXhwcmVzc2lvbik6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Ly8gQnVpbGQgdHlwZSBtYXAgZnJvbSBkYXRhIHBhcmFtZXRlciAoZm9yIHRoaXMueCA9IGRhdGEueCBwYXR0ZXJucylcblx0XHRjb25zdCBkYXRhVHlwZU1hcCA9IHRoaXMuYnVpbGREYXRhVHlwZU1hcChjb25zdHJ1Y3RvckV4cHIpO1xuXG5cdFx0Ly8gSGFuZGxlIGZ1bmN0aW9uIGV4cHJlc3Npb25cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSB8fCB0cy5pc0Fycm93RnVuY3Rpb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBjb25zdHJ1Y3RvckV4cHI7XG5cblx0XHRcdC8vIEZpcnN0LCBleHRyYWN0IHByb3BlcnRpZXMgZnJvbSBgdGhpc2AgcGFyYW1ldGVyIHR5cGUgYW5ub3RhdGlvblxuXHRcdFx0Ly8gVGhpcyBoYW5kbGVzIHBhdHRlcm5zIGxpa2U6IGZ1bmN0aW9uKHRoaXM6IFNvbWVUeXBlLCBkYXRhOiBTb21lVHlwZSkgeyB9XG5cdFx0XHRjb25zdCB0aGlzUGFyYW1Qcm9wZXJ0aWVzID0gdGhpcy5leHRyYWN0VGhpc1BhcmFtUHJvcGVydGllcyhjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0Zm9yIChjb25zdCBbIG5hbWUsIHByb3BJbmZvIF0gb2YgdGhpc1BhcmFtUHJvcGVydGllcykge1xuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCBwcm9wSW5mbyk7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEZ1bmN0aW9uIGJvZHkgd2l0aCBzdGF0ZW1lbnRzXG5cdFx0XHRpZiAodHMuaXNCbG9jayhib2R5KSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IHN0bXQgb2YgYm9keS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdFx0aWYgKHRzLmlzRXhwcmVzc2lvblN0YXRlbWVudChzdG10KSkge1xuXHRcdFx0XHRcdFx0dGhpcy5leHRyYWN0UHJvcGVydHlGcm9tU3RhdGVtZW50KHN0bXQuZXhwcmVzc2lvbiwgcHJvcGVydGllcywgZGF0YVR5cGVNYXApO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIEhhbmRsZSBjbGFzcyBleHByZXNzaW9uXG5cdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikpIHtcblx0XHRcdC8vIEZpcnN0IHBhc3M6IGNvbGxlY3QgYWxsIHByb3BlcnR5IHR5cGVzIGZvciBtZXRob2QgaW5mZXJlbmNlXG5cdFx0XHRjb25zdCBjbGFzc1Byb3BlcnR5VHlwZXMgPSB0aGlzLmV4dHJhY3RDbGFzc1Byb3BlcnR5VHlwZXMoY29uc3RydWN0b3JFeHByKTtcblxuXHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgY29uc3RydWN0b3JFeHByLm1lbWJlcnMpIHtcblx0XHRcdFx0Ly8gSGFuZGxlIHByb3BlcnR5IGRlY2xhcmF0aW9uc1xuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eURlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUpIHtcblx0XHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBwcm9wZXJ0aWVzXG5cdFx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0XHRcdG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkO1xuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblxuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpID8gbWVtYmVyLm5hbWUudGV4dCA6ICcnO1xuXHRcdFx0XHRcdGlmIChuYW1lKSB7XG5cdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHRcdHR5cGUgICAgIDogdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpLFxuXHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBIYW5kbGUgbWV0aG9kIGRlY2xhcmF0aW9uc1xuXHRcdFx0XHRpZiAodHMuaXNNZXRob2REZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBtZXRob2RzXG5cdFx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0XHRcdG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkO1xuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblxuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyTWV0aG9kVHlwZShtZW1iZXIsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gSGFuZGxlIGdldHRlciBkZWNsYXJhdGlvbnNcblx0XHRcdFx0aWYgKHRzLmlzR2V0QWNjZXNzb3IobWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgZ2V0dGVyc1xuXHRcdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdFx0XHRtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZDtcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cblx0XHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHQvLyBGaXJzdCB0cnkgZXhwbGljaXQgdHlwZSBhbm5vdGF0aW9uLCB0aGVuIGluZmVyIGZyb20gZ2V0dGVyIGJvZHlcblx0XHRcdFx0XHRsZXQgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRpZiAodHlwZSA9PT0gJ3Vua25vd24nICYmIG1lbWJlci5ib2R5KSB7XG5cdFx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclJldHVyblR5cGVGcm9tQm9keShtZW1iZXIuYm9keSwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0cmVhZG9ubHkgOiB0cnVlLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHQvKipcblx0ICogQnVpbGQgYSB0eXBlIG1hcCBmcm9tIGFsbCBwYXJhbWV0ZXJzIHdpdGggaW5saW5lIG9iamVjdCB0eXBlIGFubm90YXRpb25zXG5cdCAqIFJldHVybnMgYSBtYXAgb2YgXCJwYXJhbU5hbWUucHJvcGVydHlOYW1lXCIgLT4gdHlwZVxuXHQgKi9cblx0cHJpdmF0ZSBidWlsZERhdGFUeXBlTWFwIChoYW5kbGVyQXJnOiB0cy5FeHByZXNzaW9uKTogTWFwPHN0cmluZywgc3RyaW5nPiB7XG5cdFx0Y29uc3QgdHlwZU1hcCA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cblx0XHRpZiAoIXRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGhhbmRsZXJBcmcpICYmICF0cy5pc0Fycm93RnVuY3Rpb24oaGFuZGxlckFyZykpIHtcblx0XHRcdHJldHVybiB0eXBlTWFwO1xuXHRcdH1cblxuXHRcdC8vIEl0ZXJhdGUgb3ZlciBBTEwgcGFyYW1ldGVyc1xuXHRcdGZvciAoY29uc3QgcGFyYW0gb2YgaGFuZGxlckFyZy5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRpZiAoIXBhcmFtLm5hbWUgfHwgIXBhcmFtLnR5cGUpIGNvbnRpbnVlO1xuXG5cdFx0XHQvLyBHZXQgcGFyYW1ldGVyIG5hbWVcblx0XHRcdGxldCBwYXJhbU5hbWUgPSAnJztcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkpIHtcblx0XHRcdFx0cGFyYW1OYW1lID0gcGFyYW0ubmFtZS50ZXh0O1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Ly8gU2tpcCBkZXN0cnVjdHVyZWQgcGFyYW1ldGVycyBmb3Igbm93XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBDaGVjayBpZiBpdCdzIGFuIGlubGluZSBvYmplY3QgdHlwZSBsaXRlcmFsXG5cdFx0XHRpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUocGFyYW0udHlwZSkpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgcGFyYW0udHlwZS5tZW1iZXJzKSB7XG5cdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQoYCR7cGFyYW1OYW1lfS4ke3Byb3BOYW1lfWAsIHR5cGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Ly8gTmFtZWQgdHlwZSByZWZlcmVuY2UgKGFsaWFzL2ludGVyZmFjZS9jbGFzcywgaW1wb3J0ZWQgb3Jcblx0XHRcdFx0Ly8gbG9jYWwg4oCUIEYxNCk6IGRlY29tcG9zZSB0aGUgcmVzb2x2ZWQgZGVjbGFyYXRpb24gaW50b1xuXHRcdFx0XHQvLyBwZXItcHJvcGVydHkgZW50cmllcyB0aHJvdWdoIHRoZSBzYW1lIGltcG9ydC1hd2FyZVxuXHRcdFx0XHQvLyBtYWNoaW5lcnkgYXMgY29uc3RydWN0b3Igc2lnbmF0dXJlcyAoRjEwKSwgaW5jbHVkaW5nIHRoZVxuXHRcdFx0XHQvLyBoZXJpdGFnZSB3YWxrIChGMTMpLiBXaXRob3V0IHRoaXMsIGB0aGlzLnggPSBwYXJhbS55YFxuXHRcdFx0XHQvLyByZWFkIGB1bmtub3duYCBmb3IgbmFtZWQgcGFyYW1zIOKAlCBvbmx5IGlubGluZSBsaXRlcmFsc1xuXHRcdFx0XHQvLyB3ZXJlIGRlY29tcG9zZWQuIFVucmVzb2x2YWJsZSDihpIgd2hvbGUtcGFyYW0gZmFsbGJhY2tcblx0XHRcdFx0Ly8gYmVsb3c7IGEgYmFyZSBuYW1lIGlzIG5ldmVyIGVtaXR0ZWQgZWl0aGVyIHdheVxuXHRcdFx0XHRsZXQgbmFtZWREZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkO1xuXHRcdFx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZShwYXJhbS50eXBlKSAmJiB0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBwYXJhbVR5cGVOYW1lID0gcGFyYW0udHlwZS50eXBlTmFtZS50ZXh0O1xuXHRcdFx0XHRcdG5hbWVkRGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24ocGFyYW1UeXBlTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAobmFtZWREZWNsKSB7XG5cdFx0XHRcdFx0Ly8gbWVtYmVyIHR5cGVzIHJlc29sdmUgYWdhaW5zdCB0aGUgREVDTEFSSU5HIGZpbGVcblx0XHRcdFx0XHRjb25zdCByZWZlcmVuY2luZ0ZpbGUgPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0XHRcdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gbmFtZWREZWNsLmZpbGU7XG5cdFx0XHRcdFx0dHJ5IHtcblx0XHRcdFx0XHRcdGNvbnN0IGRlY2xQcm9wZXJ0aWVzID0gdGhpcy5yZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzKG5hbWVkRGVjbCk7XG5cdFx0XHRcdFx0XHRmb3IgKGNvbnN0IFsgcHJvcE5hbWUsIGluZm8gXSBvZiBkZWNsUHJvcGVydGllcykge1xuXHRcdFx0XHRcdFx0XHR0eXBlTWFwLnNldChgJHtwYXJhbU5hbWV9LiR7cHJvcE5hbWV9YCwgaW5mby50eXBlKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGZpbmFsbHkge1xuXHRcdFx0XHRcdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gcmVmZXJlbmNpbmdGaWxlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHQvLyBrZWVwIHRoZSB3aG9sZS1wYXJhbSBlbnRyeSB0b286IGB0aGlzLnggPSBkYXRhYCAodGhlXG5cdFx0XHRcdFx0Ly8gYmFyZSBwYXJhbWV0ZXIpIGFzc2lnbnMgdGhlIGZ1bGwgZXhwYW5kZWQgc2hhcGUg4oCUXG5cdFx0XHRcdFx0Ly8gdGhlIHNhbWUgc3RyaW5nIGNvbnN0cnVjdG9yLXNpZ25hdHVyZSBlbWlzc2lvbiB1c2VzXG5cdFx0XHRcdFx0Y29uc3Qgd2hvbGVUeXBlID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKG5hbWVkRGVjbCk7XG5cdFx0XHRcdFx0aWYgKHdob2xlVHlwZSAmJiB3aG9sZVR5cGUgIT09ICd1bmtub3duJykge1xuXHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQocGFyYW1OYW1lLCB3aG9sZVR5cGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHQvLyBTdG9yZSBzaW1wbGUgcGFyYW1ldGVyIHR5cGVzIGxpa2UgYGRlY29yYXRlVmFsdWU6IHN0cmluZ2Bcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cdFx0XHRcdFx0aWYgKHR5cGUgIT09ICd1bmtub3duJykge1xuXHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQocGFyYW1OYW1lLCB0eXBlKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdHlwZU1hcDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnR5IGFjY2VzcyBjaGFpbiAoZS5nLiwgXCJkYXRhUmVuYW1lZC5pZFwiIGZyb20gZGF0YVJlbmFtZWQuaWQpXG5cdCAqIEhhbmRsZXMgZmFsbGJhY2tzIGxpa2U6IGRhdGEucGVybWlzc2lvbnMgfHwgW11cblx0ICovXG5cdHByaXZhdGUgZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbiAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gSGFuZGxlIGlkZW50aWZpZXI6IGRhdGFcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci50ZXh0O1xuXHRcdH1cblx0XHQvLyBIYW5kbGUgcHJvcGVydHkgYWNjZXNzOiBkYXRhLnBlcm1pc3Npb25zXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBiYXNlID0gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGV4cHIuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoYmFzZSkge1xuXHRcdFx0XHRyZXR1cm4gYCR7YmFzZX0uJHtleHByLm5hbWUudGV4dH1gO1xuXHRcdFx0fVxuXHRcdH1cblx0XHQvLyBIYW5kbGUgZmFsbGJhY2sgcGF0dGVybjogZGF0YS5wZXJtaXNzaW9ucyB8fCBbXVxuXHRcdGlmICh0cy5pc0JpbmFyeUV4cHJlc3Npb24oZXhwcikgJiZcblx0XHRcdGV4cHIub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkJhckJhclRva2VuKSB7XG5cdFx0XHQvLyBSZXR1cm4gdGhlIGxlZnQgc2lkZSBvZiB8fCBvcGVyYXRvclxuXHRcdFx0cmV0dXJuIHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihleHByLmxlZnQpO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydHkgYXNzaWdubWVudCBmcm9tIHN0YXRlbWVudFxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UHJvcGVydHlGcm9tU3RhdGVtZW50IChcblx0XHRleHByOiB0cy5FeHByZXNzaW9uLFxuXHRcdHByb3BlcnRpZXM6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4sXG5cdFx0ZGF0YVR5cGVNYXA6IE1hcDxzdHJpbmcsIHN0cmluZz4gPSBuZXcgTWFwKClcblx0KTogdm9pZCB7XG5cdFx0Ly8gSGFuZGxlOiB0aGlzLnByb3BlcnR5ID0gdmFsdWVcblx0XHRpZiAodHMuaXNCaW5hcnlFeHByZXNzaW9uKGV4cHIpICYmXG5cdFx0XHRleHByLm9wZXJhdG9yVG9rZW4ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbikge1xuXHRcdFx0Y29uc3QgeyBsZWZ0IH0gPSBleHByO1xuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obGVmdCkpIHtcblx0XHRcdFx0Ly8gQ2hlY2sgaWYgYWNjZXNzaW5nICd0aGlzJyAoVGhpc0tleXdvcmQpXG5cdFx0XHRcdGlmIChsZWZ0LmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBsZWZ0Lm5hbWU/LnRleHQ7XG5cdFx0XHRcdFx0aWYgKG5hbWUpIHtcblx0XHRcdFx0XHRcdC8vIFRyeSB0byBnZXQgdHlwZSBmcm9tIGRhdGFUeXBlTWFwIHVzaW5nIGZ1bGwgYWNjZXNzIGNoYWluIChlLmcuLCBcImRhdGFSZW5hbWVkLmlkXCIpXG5cdFx0XHRcdFx0XHRjb25zdCBhY2Nlc3NDaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihleHByLnJpZ2h0KTtcblx0XHRcdFx0XHRcdGxldCB0eXBlID0gYWNjZXNzQ2hhaW4gPyBkYXRhVHlwZU1hcC5nZXQoYWNjZXNzQ2hhaW4pIDogdW5kZWZpbmVkO1xuXHRcdFx0XHRcdFx0Ly8gSWYgbm90IGZvdW5kIGFuZCBSSFMgaXMgYSBzaW1wbGUgaWRlbnRpZmllciwgdHJ5IGxvb2tpbmcgaXQgdXAgZGlyZWN0bHlcblx0XHRcdFx0XHRcdGlmICghdHlwZSAmJiB0cy5pc0lkZW50aWZpZXIoZXhwci5yaWdodCkpIHtcblx0XHRcdFx0XHRcdFx0dHlwZSA9IGRhdGFUeXBlTWFwLmdldChleHByLnJpZ2h0LnRleHQpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0Ly8gYSBib3VuZCBjb25zdHJ1Y3Rpb24gcmVzdWx0IChuZXcvbG9va3VwL2NoYWluL2ZvcmsvXG5cdFx0XHRcdFx0XHQvLyBtZXJnZS9jYWxsKTogdGhlIHZhbHVlIHNjb3BlIGJpbmRpbmcgc3VwcGxpZXMgdGhlXG5cdFx0XHRcdFx0XHQvLyBncmFwaCB0eXBlIOKAlCBlbWl0dGVkIGJ5IGl0cyBpbnN0YW5jZS10eXBlIG5hbWVcblx0XHRcdFx0XHRcdGlmICghdHlwZSAmJiB0cy5pc0lkZW50aWZpZXIoZXhwci5yaWdodCkpIHtcblx0XHRcdFx0XHRcdFx0Y29uc3QgYm91bmQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChleHByLnJpZ2h0LnRleHQpO1xuXHRcdFx0XHRcdFx0XHRpZiAoYm91bmQpIHtcblx0XHRcdFx0XHRcdFx0XHR0eXBlID0gYm91bmQucmVwbGFjZSgvXFwuL2csICdfJyk7XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdGlmICghdHlwZSkge1xuXHRcdFx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIoZXhwci5yaWdodCwgZGF0YVR5cGVNYXApO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0Ly8gRG9uJ3Qgb3ZlcndyaXRlIGEga25vd24gdHlwZSBmcm9tIGEgYHRoaXNgIGFubm90YXRpb25cblx0XHRcdFx0XHRcdC8vIHdpdGggYW4gdW5rbm93bi1iZWFyaW5nIGluZmVyZW5jZTogYW4gZW1wdHktYXJyYXlcblx0XHRcdFx0XHRcdC8vIGluaXRpYWxpemVyIGluZmVycyAnQXJyYXk8dW5rbm93bj4nLCB3aGljaCBtdXN0IG5vdFxuXHRcdFx0XHRcdFx0Ly8gY2xvYmJlciBhbiBhbm5vdGF0ZWQgJ0FycmF5PHsgaWQ6IG51bWJlciB9PicgZWl0aGVyLlxuXHRcdFx0XHRcdFx0Ly8gXCJLbm93blwiIG9uIHRoZSBFWElTVElORyBzaWRlIG1lYW5zIHRoZSB3aG9sZSB0eXBlIElTXG5cdFx0XHRcdFx0XHQvLyBgdW5rbm93bmAgKGV4YWN0IG1hdGNoKSDigJQgYSBzdWJzdHJpbmcgbWF0Y2ggdHJlYXRzXG5cdFx0XHRcdFx0XHQvLyBgUmVjb3JkPHN0cmluZywgdW5rbm93bj5gIGFzIHVua25vd24tYmVhcmluZyBhbmQgbGV0XG5cdFx0XHRcdFx0XHQvLyBpbmZlcmVuY2UgY2xvYmJlciBhIGdvb2QgYW5ub3RhdGlvbiAoRjE0KVxuXHRcdFx0XHRcdFx0Y29uc3QgZXhpc3RpbmcgPSBwcm9wZXJ0aWVzLmdldChuYW1lKTtcblx0XHRcdFx0XHRcdGNvbnN0IHR5cGVIYXNVbmtub3duID0gIXR5cGUgfHwgdHlwZS5pbmNsdWRlcygndW5rbm93bicpO1xuXHRcdFx0XHRcdFx0Y29uc3QgZXhpc3RpbmdJc0tub3duID0gZXhpc3RpbmcgPyBleGlzdGluZy50eXBlLnRyaW0oKSAhPT0gJ3Vua25vd24nIDogZmFsc2U7XG5cdFx0XHRcdFx0XHRpZiAoZXhpc3RpbmdJc0tub3duICYmIHR5cGVIYXNVbmtub3duKSB7XG5cdFx0XHRcdFx0XHRcdC8vIEtlZXAgdGhlIGJldHRlciB0eXBlIGZyb20gZXhwbGljaXQgYW5ub3RhdGlvblxuXHRcdFx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6IGV4aXN0aW5nID8gZXhpc3Rpbmcub3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gSGFuZGxlOiBPYmplY3QuYXNzaWduKHRoaXMsIHsgcHJvcDogdmFsdWUgfSlcblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0Y29uc3QgZm4gPSBleHByLmV4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZm4pICYmXG5cdFx0XHRcdGZuLm5hbWU/LnRleHQgPT09ICdhc3NpZ24nICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihmbi5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHRmbi5leHByZXNzaW9uLnRleHQgPT09ICdPYmplY3QnKSB7XG5cdFx0XHRcdGNvbnN0IGFyZ3MgPSBleHByLmFyZ3VtZW50cztcblx0XHRcdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIgJiYgYXJnc1sgMCBdLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdFx0XHQvLyBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSB0aGUgc2Vjb25kIGFyZ3VtZW50XG5cdFx0XHRcdFx0Y29uc3QgWyAsIHByb3BzQXJnIF0gPSBhcmdzO1xuXHRcdFx0XHRcdGlmICh0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKHByb3BzQXJnKSkge1xuXHRcdFx0XHRcdFx0Zm9yIChjb25zdCBwcm9wIG9mIHByb3BzQXJnLnByb3BlcnRpZXMpIHtcblx0XHRcdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBc3NpZ25tZW50KHByb3ApICYmIHRzLmlzSWRlbnRpZmllcihwcm9wLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRcdFx0Y29uc3QgbmFtZSA9IHByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0XHR0eXBlICAgICA6IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKHByb3AuaW5pdGlhbGl6ZXIpLFxuXHRcdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH0gZWxzZSBpZiAodHMuaXNJZGVudGlmaWVyKHByb3BzQXJnKSkge1xuXHRcdFx0XHRcdFx0Ly8gT2JqZWN0LmFzc2lnbih0aGlzLCBkYXRhKSDigJQgdGhlIGlkZW50aWZpZXIgZm9ybTogZXZlcnlcblx0XHRcdFx0XHRcdC8vIHBlci1wcm9wZXJ0eSBlbnRyeSB0aGUgZGF0YSBwYXJhbWV0ZXIgY29udHJpYnV0ZWQgdG9cblx0XHRcdFx0XHRcdC8vIHRoZSB0eXBlIG1hcCBiZWNvbWVzIGFuIG93biBwcm9wZXJ0eS4gVGhpcyBpcyB3aGF0XG5cdFx0XHRcdFx0XHQvLyBjYXJyaWVzIHRoZSBmaWVsZHMgZm9yIHRoZSBzZWxmLXJlZmVyZW5jaW5nXG5cdFx0XHRcdFx0XHQvLyBpbnRlcnNlY3Rpb24tYWxpYXMgcm9vdCBwYXR0ZXJuIChGMjEpOiB0aGUgdGhpcy1hbGlhc1xuXHRcdFx0XHRcdFx0Ly8gaXMgZXJnb25vbWljLW9ubHkgYW5kIGl0cyBpbnRlcnNlY3Rpb24gbWVtYmVycyBhcmVcblx0XHRcdFx0XHRcdC8vIG5ldmVyIGV4cGFuZGVkLCBzbyB0aGUgYXNzaWduIGlzIHdoZXJlIHRoZSByb290J3Ncblx0XHRcdFx0XHRcdC8vIGZpZWxkcyBtdXN0IGNvbWUgZnJvbVxuXHRcdFx0XHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gcHJvcHNBcmcudGV4dDtcblx0XHRcdFx0XHRcdGZvciAoY29uc3QgWyBrZXksIHR5cGUgXSBvZiBkYXRhVHlwZU1hcCkge1xuXHRcdFx0XHRcdFx0XHRpZiAoIWtleS5zdGFydHNXaXRoKGAke3BhcmFtTmFtZX0uYCkpIHtcblx0XHRcdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHRjb25zdCBuYW1lID0ga2V5LnNsaWNlKHBhcmFtTmFtZS5sZW5ndGggKyAxKTtcblx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gY2xhc3MgZGVjbGFyYXRpb24gKGluY2x1ZGluZyBtZXRob2RzIGFuZCBnZXR0ZXJzKVxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q2xhc3NQcm9wZXJ0aWVzIChjbGFzc0RlY2w6IHRzLkNsYXNzRGVjbGFyYXRpb24pOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCBwcm9wZXJ0aWVzID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblxuXHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGNsYXNzRGVjbC5tZW1iZXJzKSB7XG5cdFx0XHQvLyBIYW5kbGUgcHJvcGVydHkgZGVjbGFyYXRpb25zXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eURlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUpIHtcblx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgcHJvcGVydGllc1xuXHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0ICAgICBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZCk7XG5cdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Y29uc3QgbmFtZSA9IHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkgPyBtZW1iZXIubmFtZS50ZXh0IDogJyc7XG5cdFx0XHRcdGlmIChuYW1lKSB7XG5cdFx0XHRcdFx0Ly8gSWYgbm8gZXhwbGljaXQgdHlwZSBidXQgaGFzIGluaXRpYWxpemVyLCBpbmZlciBmcm9tIGluaXRpYWxpemVyXG5cdFx0XHRcdFx0bGV0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0aWYgKHR5cGUgPT09ICd1bmtub3duJyAmJiBtZW1iZXIuaW5pdGlhbGl6ZXIpIHtcblx0XHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihtZW1iZXIuaW5pdGlhbGl6ZXIpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdG9wdGlvbmFsIDogISFtZW1iZXIucXVlc3Rpb25Ub2tlbixcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHQvLyBIYW5kbGUgbWV0aG9kIGRlY2xhcmF0aW9uc1xuXHRcdFx0aWYgKHRzLmlzTWV0aG9kRGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIG1ldGhvZHNcblx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdCAgICAgbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQpO1xuXHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlck1ldGhvZFR5cGUobWVtYmVyKTtcblx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gSGFuZGxlIGdldHRlciBkZWNsYXJhdGlvbnNcblx0XHRcdGlmICh0cy5pc0dldEFjY2Vzc29yKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBnZXR0ZXJzXG5cdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHQgICAgIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkKTtcblx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0Ly8gRmlyc3QgdHJ5IGV4cGxpY2l0IHR5cGUgYW5ub3RhdGlvbiwgdGhlbiBpbmZlciBmcm9tIGdldHRlciBib2R5XG5cdFx0XHRcdGxldCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRpZiAodHlwZSA9PT0gJ3Vua25vd24nICYmIG1lbWJlci5ib2R5KSB7XG5cdFx0XHRcdFx0dHlwZSA9IHRoaXMuaW5mZXJSZXR1cm5UeXBlRnJvbUJvZHkobWVtYmVyLmJvZHkpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRyZWFkb25seSA6IHRydWUsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBwcm9wZXJ0aWVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgY2xhc3MgcHJvcGVydHkgdHlwZXMgZm9yIG1ldGhvZCByZXR1cm4gdHlwZSBpbmZlcmVuY2Vcblx0ICogTWFwcyBwcm9wZXJ0eSBuYW1lcyB0byB0aGVpciBUeXBlU2NyaXB0IHR5cGUgc3RyaW5nc1xuXHQgKiBOb3RlOiBJbmNsdWRlcyBwcml2YXRlL3Byb3RlY3RlZCBwcm9wZXJ0aWVzIGZvciBtZXRob2QgaW5mZXJlbmNlXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDbGFzc1Byb3BlcnR5VHlwZXMgKGNsYXNzRGVjbDogdHMuQ2xhc3NFeHByZXNzaW9uKTogTWFwPHN0cmluZywgc3RyaW5nPiB7XG5cdFx0Y29uc3QgcHJvcGVydHlUeXBlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjbGFzc0RlY2wubWVtYmVycykge1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlEZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Ly8gSW5jbHVkZSBBTEwgcHJvcGVydGllcyAoZXZlbiBwcml2YXRlKSBmb3IgbWV0aG9kIHJldHVybiB0eXBlIGluZmVyZW5jZVxuXHRcdFx0XHQvLyBUaGUgdmlzaWJpbGl0eSBjaGVjayBpcyBkb25lIHdoZW4gYWRkaW5nIHRvIG91dHB1dCBwcm9wZXJ0aWVzXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRpZiAobWVtYmVyLnR5cGUpIHtcblx0XHRcdFx0XHRwcm9wZXJ0eVR5cGVzLnNldChuYW1lLCB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSkpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnR5VHlwZXM7XG5cdH1cblxuXHQvKipcblx0ICogSW5mZXIgbWV0aG9kIHR5cGUgZnJvbSBtZXRob2QgZGVjbGFyYXRpb25cblx0ICovXG5cdHByaXZhdGUgaW5mZXJNZXRob2RUeXBlIChtZXRob2Q6IHRzLk1ldGhvZERlY2xhcmF0aW9uLCBjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+KTogc3RyaW5nIHtcblx0XHRjb25zdCBwYXJhbXMgPSBtZXRob2QucGFyYW1ldGVycy5tYXAocGFyYW0gPT4ge1xuXHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpID8gcGFyYW0ubmFtZS50ZXh0IDogJ2FyZyc7XG5cdFx0XHRjb25zdCBwYXJhbVR5cGUgPSB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblx0XHRcdHJldHVybiBgJHtwYXJhbU5hbWV9OiAke3BhcmFtVHlwZX1gO1xuXHRcdH0pLmpvaW4oJywgJyk7XG5cblx0XHRjb25zdCByZXR1cm5UeXBlID0gdGhpcy5pbmZlclJldHVyblR5cGUobWV0aG9kLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXG5cdFx0aWYgKHBhcmFtcykge1xuXHRcdFx0cmV0dXJuIGAoJHtwYXJhbXN9KSA9PiAke3JldHVyblR5cGV9YDtcblx0XHR9XG5cdFx0cmV0dXJuIGAoKSA9PiAke3JldHVyblR5cGV9YDtcblx0fVxuXG5cdC8qKlxuXHRcdCogRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gYHRoaXNgIHBhcmFtZXRlciB0eXBlIGFubm90YXRpb25cblx0XHQqIEhhbmRsZXMgcGF0dGVybnMgbGlrZTogZnVuY3Rpb24odGhpczogU29tZVR5cGUsIGRhdGE6IFNvbWVUeXBlKSB7IH1cblx0XHQqL1xuXHRwcml2YXRlIGV4dHJhY3RUaGlzUGFyYW1Qcm9wZXJ0aWVzIChoYW5kbGVyQXJnOiB0cy5GdW5jdGlvbkV4cHJlc3Npb24gfCB0cy5BcnJvd0Z1bmN0aW9uKTpcblx0XHRNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCBwcm9wZXJ0aWVzID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblxuXHRcdC8vIEZpbmQgdGhlIGB0aGlzYCBwYXJhbWV0ZXIgKGlmIGFueSlcblx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGhhbmRsZXJBcmcucGFyYW1ldGVycykge1xuXHRcdFx0aWYgKHBhcmFtLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpICYmIHBhcmFtLm5hbWUudGV4dCA9PT0gJ3RoaXMnICYmIHBhcmFtLnR5cGUpIHtcblx0XHRcdFx0Ly8gQ2hlY2sgaWYgaXQncyBhIHR5cGUgcmVmZXJlbmNlIChlLmcuLCBgdGhpczogdXNhZ2VgKVxuXHRcdFx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZShwYXJhbS50eXBlKSkge1xuXHRcdFx0XHRcdGNvbnN0IHR5cGVOYW1lID0gdHMuaXNJZGVudGlmaWVyKHBhcmFtLnR5cGUudHlwZU5hbWUpXG5cdFx0XHRcdFx0XHQ/IHBhcmFtLnR5cGUudHlwZU5hbWUudGV4dFxuXHRcdFx0XHRcdFx0OiAnJztcblxuXHRcdFx0XHRcdC8vIFJlc29sdmUgdGhyb3VnaCB0aGUgcmVmZXJlbmNpbmcgZmlsZSdzIG93biBpbXBvcnRzIGZpcnN0IChGMTApXG5cdFx0XHRcdFx0Y29uc3QgZGVjbCA9IHR5cGVOYW1lXG5cdFx0XHRcdFx0XHQ/IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24odHlwZU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSlcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0XHRcdGlmIChkZWNsKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBkZWNsUHJvcGVydGllcyA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllcyhkZWNsKTtcblx0XHRcdFx0XHRcdGZvciAoY29uc3QgWyBwcm9wTmFtZSwgaW5mbyBdIG9mIGRlY2xQcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KHByb3BOYW1lLCBpbmZvKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gQ2hlY2sgaWYgaXQncyBkaXJlY3RseSBhbiBpbmxpbmUgdHlwZSBsaXRlcmFsIChlLmcuLCBgdGhpczogeyBpZDogc3RyaW5nIH1gKVxuXHRcdFx0XHRlbHNlIGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZShwYXJhbS50eXBlKSkge1xuXHRcdFx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIHBhcmFtLnR5cGUubWVtYmVycykge1xuXHRcdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQocHJvcE5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRuYW1lICAgICA6IHByb3BOYW1lLFxuXHRcdFx0XHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gRm91bmQgdGhlIGB0aGlzYCBwYXJhbWV0ZXIsIG5vIG5lZWQgdG8gY29udGludWVcblx0XHRcdFx0YnJlYWs7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHQvKipcblx0XHQqIEluZmVyIFR5cGVTY3JpcHQgdHlwZSBmcm9tIHR5cGUgbm9kZVxuXHRcdCovXG5cdC8qKlxuXHQgKiBJbmZlciBUeXBlU2NyaXB0IHR5cGUgZnJvbSB0eXBlIG5vZGVcblx0ICovXG5cdHByaXZhdGUgaW5mZXJUeXBlICh0eXBlTm9kZT86IHRzLlR5cGVOb2RlKTogc3RyaW5nIHtcblx0XHRpZiAoIXR5cGVOb2RlKSB7XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblxuXHRcdHN3aXRjaCAodHlwZU5vZGUua2luZCkge1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5TdHJpbmdLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdW1iZXJLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Cb29sZWFuS2V5d29yZDpcblx0XHRcdHJldHVybiAnYm9vbGVhbic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVuZGVmaW5lZEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3VuZGVmaW5lZCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bGxLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdudWxsJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQW55S2V5d29yZDpcblx0XHRcdHJldHVybiAnYW55Jztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5rbm93bktleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Wb2lkS2V5d29yZDpcblx0XHRcdHJldHVybiAndm9pZCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkFycmF5VHlwZTpcblx0XHRcdHJldHVybiBgQXJyYXk8JHsgIHRoaXMuaW5mZXJUeXBlKCh0eXBlTm9kZSBhcyB0cy5BcnJheVR5cGVOb2RlKS5lbGVtZW50VHlwZSkgIH0+YDtcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZUxpdGVyYWw6IHtcblx0XHRcdC8vIElubGluZS1leHBhbmQgdHlwZSBsaXRlcmFscyBpbnN0ZWFkIG9mIGNvbGxhcHNpbmcgdG8gJ29iamVjdCdcblx0XHRcdGNvbnN0IHR5cGVMaXQgPSB0eXBlTm9kZSBhcyB0cy5UeXBlTGl0ZXJhbE5vZGU7XG5cdFx0XHRjb25zdCBwcm9wczogc3RyaW5nW10gPSBbXTtcblx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIHR5cGVMaXQubWVtYmVycykge1xuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Y29uc3Qgb3B0aW9uYWwgPSBtZW1iZXIucXVlc3Rpb25Ub2tlbiA/ICc/JyA6ICcnO1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0cHJvcHMucHVzaChgJHtwcm9wTmFtZX0ke29wdGlvbmFsfTogJHt0eXBlfWApO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gYHsgJHtwcm9wcy5qb2luKCc7ICcpfSB9YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkxpdGVyYWxUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgc3RyaW5nIGxpdGVyYWwgdHlwZXMgbGlrZSAndXNlcicsICdhZG1pbicsIGV0Yy5cblx0XHRcdGNvbnN0IHsgbGl0ZXJhbCB9ID0gKHR5cGVOb2RlIGFzIHRzLkxpdGVyYWxUeXBlTm9kZSk7XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGxpdGVyYWwpKSB7XG5cdFx0XHRcdC8vIFJldHVybiB0aGUgYWN0dWFsIGxpdGVyYWwgdmFsdWUgKGUuZy4sICd1c2VyJyBpbnN0ZWFkIG9mIHN0cmluZylcblx0XHRcdFx0cmV0dXJuIGAnJHtsaXRlcmFsLnRleHR9J2A7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNOdW1lcmljTGl0ZXJhbChsaXRlcmFsKSkge1xuXHRcdFx0XHRyZXR1cm4gbGl0ZXJhbC50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0aWYgKGxpdGVyYWwua2luZCA9PT0gdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZCkge1xuXHRcdFx0XHRyZXR1cm4gJ3RydWUnO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGxpdGVyYWwua2luZCA9PT0gdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQpIHtcblx0XHRcdFx0cmV0dXJuICdmYWxzZSc7XG5cdFx0XHR9XG5cdFx0XHRpZiAobGl0ZXJhbC5raW5kID09PSB0cy5TeW50YXhLaW5kLk51bGxLZXl3b3JkKSB7XG5cdFx0XHRcdHJldHVybiAnbnVsbCc7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZVJlZmVyZW5jZToge1xuXHRcdFx0Ly8gSGFuZGxlIHR5cGUgcmVmZXJlbmNlcyBsaWtlIE1hcDxzdHJpbmcsIG51bWJlcj4sIFByb3BlcnR5SW5mbywgZXRjLlxuXHRcdFx0Y29uc3QgdHlwZVJlZiA9IHR5cGVOb2RlIGFzIHRzLlR5cGVSZWZlcmVuY2VOb2RlO1xuXG5cdFx0XHQvLyBRdWFsaWZpZWQgbmFtZXMgKE5hbWVzcGFjZS5UeXBlKTogcmVzb2x2ZSB0aHJvdWdoIG5hbWVzcGFjZSBpbXBvcnRzXG5cdFx0XHRpZiAodHMuaXNRdWFsaWZpZWROYW1lKHR5cGVSZWYudHlwZU5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHJlc29sdmVkUXVhbGlmaWVkID0gdGhpcy5pbmZlclF1YWxpZmllZFR5cGVSZWZlcmVuY2UodHlwZVJlZik7XG5cdFx0XHRcdGlmIChyZXNvbHZlZFF1YWxpZmllZCAhPT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHJlc29sdmVkUXVhbGlmaWVkO1xuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIHVucmVzb2x2ZWQgcXVhbGlmaWVkIHJlZmVyZW5jZXMgbXVzdCBub3QgbGVhayBhIGJhcmUgbmFtZVxuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXG5cdFx0XHRjb25zdCB0eXBlTmFtZSA9IHRzLmlzSWRlbnRpZmllcih0eXBlUmVmLnR5cGVOYW1lKSA/IHR5cGVSZWYudHlwZU5hbWUudGV4dCA6ICd1bmtub3duJztcblxuXHRcdFx0Ly8gSW1wb3J0LWF3YXJlIHJlZmVyZW5jZWQtdHlwZSByZXNvbHV0aW9uIChGMTApOiBhIGRlY2xhcmF0aW9uXG5cdFx0XHQvLyByZWFjaGVkIHRocm91Z2ggdGhlIGN1cnJlbnQgZmlsZSdzIG93biBpbXBvcnRzIChvciBpdHMgbG9jYWxzLFxuXHRcdFx0Ly8gb3IgYSB1bmlxdWUgcHJvZ3JhbS13aWRlIGRlY2xhcmF0aW9uKSBleHBhbmRzIGlubGluZVxuXHRcdFx0Y29uc3Qgc2ltcGxlUmVmID0gdGhpcy5yZXNvbHZlU2ltcGxlVHlwZVJlZmVyZW5jZSh0eXBlTmFtZSwgdHlwZVJlZi50eXBlQXJndW1lbnRzLCB0eXBlUmVmKTtcblx0XHRcdGlmIChzaW1wbGVSZWYgIT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRyZXR1cm4gc2ltcGxlUmVmO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBCdWlsZCBnZW5lcmljIHR5cGUgYXJndW1lbnRzXG5cdFx0XHRjb25zdCB0eXBlQXJncyA9ICh0eXBlUmVmLnR5cGVBcmd1bWVudHMgPz8gW10pLm1hcChhcmcgPT4gdGhpcy5pbmZlclR5cGUoYXJnKSk7XG5cdFx0XHRyZXR1cm4gYCR7dHlwZU5hbWV9PCR7dHlwZUFyZ3Muam9pbignLCAnKX0+YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVuaW9uVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHVuaW9uIHR5cGVzIGxpa2UgJ2EnIHwgJ2InIHwgJ2MnXG5cdFx0XHRjb25zdCB1bmlvblR5cGUgPSB0eXBlTm9kZSBhcyB0cy5VbmlvblR5cGVOb2RlO1xuXHRcdFx0Y29uc3QgdHlwZXMgPSB1bmlvblR5cGUudHlwZXMubWFwKHQgPT4gdGhpcy5pbmZlclR5cGUodCkpO1xuXHRcdFx0cmV0dXJuIHR5cGVzLmpvaW4oJyB8ICcpO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuSW50ZXJzZWN0aW9uVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIGludGVyc2VjdGlvbiB0eXBlcyBsaWtlIFR5cGVBICYgVHlwZUJcblx0XHRcdGNvbnN0IGludGVyc2VjdGlvblR5cGUgPSB0eXBlTm9kZSBhcyB0cy5JbnRlcnNlY3Rpb25UeXBlTm9kZTtcblx0XHRcdGNvbnN0IHR5cGVzID0gaW50ZXJzZWN0aW9uVHlwZS50eXBlcy5tYXAodCA9PiB0aGlzLmluZmVyVHlwZSh0KSk7XG5cdFx0XHRyZXR1cm4gdHlwZXMuam9pbignICYgJyk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UdXBsZVR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSB0dXBsZSB0eXBlcyBsaWtlIFtzdHJpbmcsIG51bWJlcl1cblx0XHRcdGNvbnN0IHR1cGxlVHlwZSA9IHR5cGVOb2RlIGFzIHRzLlR1cGxlVHlwZU5vZGU7XG5cdFx0XHRjb25zdCBlbGVtZW50cyA9IHR1cGxlVHlwZS5lbGVtZW50cy5tYXAoZWxlbSA9PiB0aGlzLmluZmVyVHlwZShlbGVtIGFzIHRzLlR5cGVOb2RlKSk7XG5cdFx0XHRyZXR1cm4gYFske2VsZW1lbnRzLmpvaW4oJywgJyl9XWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5PcHRpb25hbFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBvcHRpb25hbCBlbGVtZW50IGluIHR1cGxlOiBzdHJpbmc/XG5cdFx0XHRjb25zdCBvcHRpb25hbFR5cGUgPSB0eXBlTm9kZSBhcyB0cy5PcHRpb25hbFR5cGVOb2RlO1xuXHRcdFx0cmV0dXJuIGAke3RoaXMuaW5mZXJUeXBlKG9wdGlvbmFsVHlwZS50eXBlKSAgfT9gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuUmVzdFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSByZXN0IGVsZW1lbnQ6IC4uLlRcblx0XHRcdGNvbnN0IHJlc3RUeXBlID0gdHlwZU5vZGUgYXMgdHMuUmVzdFR5cGVOb2RlO1xuXHRcdFx0cmV0dXJuIGAuLi4keyAgdGhpcy5pbmZlclR5cGUocmVzdFR5cGUudHlwZSl9YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlBhcmVudGhlc2l6ZWRUeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgcGFyZW50aGVzaXplZCB0eXBlczogKEEgfCBCKVxuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJUeXBlKCh0eXBlTm9kZSBhcyB0cy5QYXJlbnRoZXNpemVkVHlwZU5vZGUpLnR5cGUpO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuSW5kZXhlZEFjY2Vzc1R5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBpbmRleGVkIGFjY2VzczogVFtLXVxuXHRcdFx0Y29uc3QgaW5kZXhlZCA9IHR5cGVOb2RlIGFzIHRzLkluZGV4ZWRBY2Nlc3NUeXBlTm9kZTtcblx0XHRcdC8vIEYyMzogdW53cmFwIHBhcmVudGhlc2VzIGFyb3VuZCB0aGUgb2JqZWN0IOKAlCBgKHR5cGVvZlxuXHRcdFx0Ly8gbGlzdClbbnVtYmVyXWAgbXVzdCB0YWtlIHRoZSB0eXBlb2YgYnJhbmNoIGxpa2UgdGhlIGJhcmVcblx0XHRcdC8vIHNwZWxsaW5nOyBvdGhlcndpc2UgdGhlIGdlbmVyYWwgcGF0aCBpbmZlcnMgdGhlIHVuaW9uIGFuZFxuXHRcdFx0Ly8gZ2x1ZXMgdGhlIHN1ZmZpeCBvbnRvIHRoZSBMQVNUIG1lbWJlclxuXHRcdFx0Ly8gKGAnYScgfCAnYidbbnVtYmVyXWApXG5cdFx0XHRsZXQgb2JqZWN0Tm9kZTogdHMuVHlwZU5vZGUgPSBpbmRleGVkLm9iamVjdFR5cGU7XG5cdFx0XHR3aGlsZSAodHMuaXNQYXJlbnRoZXNpemVkVHlwZU5vZGUob2JqZWN0Tm9kZSkpIHtcblx0XHRcdFx0b2JqZWN0Tm9kZSA9IG9iamVjdE5vZGUudHlwZTtcblx0XHRcdH1cblx0XHRcdC8vIGB0eXBlb2YgY29uc3RBcnJheVtLXWAg4oCUIGVsZW1lbnQgdHlwZSBvZiBhIHRyYWNrZWQgY29uc3QgYXJyYXk6XG5cdFx0XHQvLyBlbWl0IHRoZSBlbGVtZW50IGxpdGVyYWwgdW5pb24gZGlyZWN0bHkgKGFzc2VtYmxpbmdcblx0XHRcdC8vIGB1bmlvbltLXWAgdGV4dCB3b3VsZCBtaXNyZWFkIHByZWNlZGVuY2UsIGFuZCB3aGVuIHRoZSBjb25zdFxuXHRcdFx0Ly8gaXMgbm90IHN0YXRpY2FsbHkgdmlzaWJsZSB0aGUgaG9uZXN0IGFuc3dlciBpcyBgdW5rbm93bmAsXG5cdFx0XHQvLyBuZXZlciBhIGJhcmUgYHR5cGVvZiBuYW1lYCBxdWVyeSlcblx0XHRcdGlmICh0cy5pc1R5cGVRdWVyeU5vZGUob2JqZWN0Tm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKG9iamVjdE5vZGUuZXhwck5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHF1ZXJ5TmFtZSA9IG9iamVjdE5vZGUuZXhwck5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgYXJyYXlMaXRlcmFsID0gdGhpcy5maW5kUmVmZXJlbmNlZENvbnN0QXJyYXkocXVlcnlOYW1lLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHRjb25zdCBsaXRlcmFscyA9IGFycmF5TGl0ZXJhbCA/IHRoaXMubGl0ZXJhbFR5cGVzT2ZBcnJheShhcnJheUxpdGVyYWwpIDogdW5kZWZpbmVkO1xuXHRcdFx0XHRpZiAoIWxpdGVyYWxzKSB7XG5cdFx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAodHMuaXNMaXRlcmFsVHlwZU5vZGUoaW5kZXhlZC5pbmRleFR5cGUpICYmIHRzLmlzTnVtZXJpY0xpdGVyYWwoaW5kZXhlZC5pbmRleFR5cGUubGl0ZXJhbCkpIHtcblx0XHRcdFx0XHRjb25zdCBlbGVtZW50SW5kZXggPSBwYXJzZUludChpbmRleGVkLmluZGV4VHlwZS5saXRlcmFsLnRleHQsIDEwKTtcblx0XHRcdFx0XHRjb25zdCBlbGVtZW50ID0gbGl0ZXJhbHNbIGVsZW1lbnRJbmRleCBdO1xuXHRcdFx0XHRcdGNvbnN0IGVsZW1lbnRSZXN1bHQgPSBlbGVtZW50ID09PSB1bmRlZmluZWQgPyAndW5rbm93bicgOiBlbGVtZW50O1xuXHRcdFx0XHRcdHJldHVybiBlbGVtZW50UmVzdWx0O1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IHVuaW9uUmVzdWx0ID0gbGl0ZXJhbHMuam9pbignIHwgJyk7XG5cdFx0XHRcdHJldHVybiB1bmlvblJlc3VsdDtcblx0XHRcdH1cblx0XHRcdGxldCBvYmplY3RUeXBlID0gdGhpcy5pbmZlclR5cGUob2JqZWN0Tm9kZSk7XG5cdFx0XHRjb25zdCBpbmRleFR5cGUgPSB0aGlzLmluZmVyVHlwZShpbmRleGVkLmluZGV4VHlwZSk7XG5cdFx0XHQvLyBJZiBvYmplY3RUeXBlIGlzICdvYmplY3QnLCB0cnkgdG8gcmVzb2x2ZSB0aGUgdW5kZXJseWluZyByZWZlcmVuY2VkIHR5cGVcblx0XHRcdGlmIChvYmplY3RUeXBlID09PSAnb2JqZWN0JyAmJiB0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKG9iamVjdE5vZGUpKSB7XG5cdFx0XHRcdGNvbnN0IHJlZk5hbWUgPSB0cy5pc0lkZW50aWZpZXIob2JqZWN0Tm9kZS50eXBlTmFtZSkgPyBvYmplY3ROb2RlLnR5cGVOYW1lLnRleHQgOiAnJztcblx0XHRcdFx0aWYgKHJlZk5hbWUpIHtcblx0XHRcdFx0XHRjb25zdCBkZWNsID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihyZWZOYW1lLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHRcdGlmIChkZWNsKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMuZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihkZWNsKTtcblx0XHRcdFx0XHRcdGlmIChleHBhbmRlZCkge1xuXHRcdFx0XHRcdFx0XHRvYmplY3RUeXBlID0gZXhwYW5kZWQ7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBJbnZhcmlhbnQ6IGFuIGluZGV4IHN1ZmZpeCBtdXN0IE5FVkVSIGJlIGdsdWVkIG9udG8gYW5cblx0XHRcdC8vIHVucmVzb2x2ZWQvZmFsbGJhY2sgdGFyZ2V0IOKAlCBgdW5rbm93bltudW1iZXJdYCAvIGBvYmplY3RbS11gXG5cdFx0XHQvLyBhcmUgaW52YWxpZCBUeXBlU2NyaXB0IGluIHRoZSBnZW5lcmF0ZWQgZmlsZSAoaGFyZCBjb21waWxlXG5cdFx0XHQvLyBicmVhaywgRjE3KS4gV2hlbiBlaXRoZXIgc2lkZSBkaWQgbm90IHJlc29sdmUsIHRoZSBXSE9MRVxuXHRcdFx0Ly8gaW5kZXhlZCBhY2Nlc3MgZGVncmFkZXMgdG8gYHVua25vd25gLlxuXHRcdFx0Y29uc3QgdGFyZ2V0VW5yZXNvbHZlZCA9IG9iamVjdFR5cGUgPT09ICd1bmtub3duJyB8fCBvYmplY3RUeXBlID09PSAnb2JqZWN0Jztcblx0XHRcdGNvbnN0IGluZGV4VW5yZXNvbHZlZCA9IGluZGV4VHlwZSA9PT0gJ3Vua25vd24nO1xuXHRcdFx0aWYgKHRhcmdldFVucmVzb2x2ZWQgfHwgaW5kZXhVbnJlc29sdmVkKSB7XG5cdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gYCR7b2JqZWN0VHlwZX1bJHtpbmRleFR5cGV9XWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlT3BlcmF0b3I6IHtcblx0XHRcdC8vIEhhbmRsZSBrZXlvZiwgcmVhZG9ubHksIHVuaXF1ZSBvcGVyYXRvcnNcblx0XHRcdGNvbnN0IHR5cGVPcCA9IHR5cGVOb2RlIGFzIHRzLlR5cGVPcGVyYXRvck5vZGU7XG5cdFx0XHRjb25zdCBvcGVyYXRvciA9IHRzLlN5bnRheEtpbmRbIHR5cGVPcC5vcGVyYXRvciBdO1xuXHRcdFx0cmV0dXJuIGAke29wZXJhdG9yfSAke3RoaXMuaW5mZXJUeXBlKHR5cGVPcC50eXBlKX1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZVF1ZXJ5OiB7XG5cdFx0XHQvLyBgdHlwZW9mIHhgIGFzIGEgRklFTEQgVFlQRTogdGhlIGdlbmVyYXRlZCBmaWxlIGhhcyBubyBpbXBvcnRzLFxuXHRcdFx0Ly8gc28gYSBiYXJlIGB0eXBlb2YgeGAgd291bGQgYmUgYW4gdW5yZXNvbHZhYmxlIG5hbWUgZG93bnN0cmVhbS5cblx0XHRcdC8vIFdoZW4geCBpcyBhIHRyYWNrZWQgY29uc3QgYXJyYXksIGVtaXQgaXRzIGVsZW1lbnQgbGl0ZXJhbFxuXHRcdFx0Ly8gdW5pb247IG90aGVyd2lzZSBkZWdyYWRlIHRvIGB1bmtub3duYC4gKEluc3RhbmNlVHlwZTx0eXBlb2YgWD5cblx0XHRcdC8vIGdyYXBoIHR5cGVzIGFyZSBoYW5kbGVkIGluIHJlc29sdmVTaW1wbGVUeXBlUmVmZXJlbmNlIGJlZm9yZVxuXHRcdFx0Ly8gaW5mZXJUeXBlIHJ1bnMuKVxuXHRcdFx0Y29uc3QgdHlwZVF1ZXJ5ID0gdHlwZU5vZGUgYXMgdHMuVHlwZVF1ZXJ5Tm9kZTtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIodHlwZVF1ZXJ5LmV4cHJOYW1lKSkge1xuXHRcdFx0XHRjb25zdCB1bmlvbiA9IHRoaXMudHlwZU9mQ29uc3RBcnJheVVuaW9uKHR5cGVRdWVyeS5leHByTmFtZS50ZXh0LCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHRpZiAodW5pb24pIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5pb247XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGRlZmF1bHQ6XG5cdFx0XHQvLyBGb3IgY29tcGxleCB0eXBlcywgcmV0dXJuIHRoZSB0ZXh0IHJlcHJlc2VudGF0aW9uXG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdCogSW5mZXIgcmV0dXJuIHR5cGUgZnJvbSBhIG1ldGhvZCBkZWNsYXJhdGlvblxuXHRcdCogVXNlcyBleHBsaWNpdCByZXR1cm4gdHlwZSBhbm5vdGF0aW9uIG9yIGluZmVycyBmcm9tIHJldHVybiBzdGF0ZW1lbnRzXG5cdFx0Ki9cblx0cHJpdmF0ZSBpbmZlclJldHVyblR5cGUgKG1ldGhvZDogdHMuTWV0aG9kRGVjbGFyYXRpb24sIGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz4pOiBzdHJpbmcge1xuXHRcdC8vIElmIG1ldGhvZCBoYXMgZXhwbGljaXQgcmV0dXJuIHR5cGUgYW5ub3RhdGlvbiwgdXNlIGl0XG5cdFx0aWYgKG1ldGhvZC50eXBlKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclR5cGUobWV0aG9kLnR5cGUpO1xuXHRcdH1cblxuXHRcdC8vIE90aGVyd2lzZSwgdHJ5IHRvIGluZmVyIGZyb20gcmV0dXJuIHN0YXRlbWVudHMgaW4gdGhlIG1ldGhvZCBib2R5XG5cdFx0aWYgKG1ldGhvZC5ib2R5KSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclJldHVyblR5cGVGcm9tQm9keShtZXRob2QuYm9keSwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHR9XG5cblx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBJbmZlciByZXR1cm4gdHlwZSBieSBhbmFseXppbmcgcmV0dXJuIHN0YXRlbWVudHMgaW4gdGhlIG1ldGhvZCBib2R5XG5cdFx0Ki9cblx0cHJpdmF0ZSBpbmZlclJldHVyblR5cGVGcm9tQm9keSAoYm9keTogdHMuQmxvY2ssIGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz4pOiBzdHJpbmcge1xuXHRcdGNvbnN0IHJldHVyblR5cGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cblx0XHRjb25zdCB2aXNpdCA9IChub2RlOiB0cy5Ob2RlKTogdm9pZCA9PiB7XG5cdFx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQobm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihub2RlLmV4cHJlc3Npb24sIHVuZGVmaW5lZCwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0aWYgKHR5cGUgIT09ICd1bmtub3duJykge1xuXHRcdFx0XHRcdHJldHVyblR5cGVzLmFkZCh0eXBlKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIHZpc2l0KTtcblx0XHR9O1xuXG5cdFx0dmlzaXQoYm9keSk7XG5cblx0XHRpZiAocmV0dXJuVHlwZXMuc2l6ZSA9PT0gMCkge1xuXHRcdFx0cmV0dXJuICd2b2lkJztcblx0XHR9XG5cdFx0aWYgKHJldHVyblR5cGVzLnNpemUgPT09IDEpIHtcblx0XHRcdHJldHVybiBBcnJheS5mcm9tKHJldHVyblR5cGVzKVsgMCBdO1xuXHRcdH1cblx0XHRyZXR1cm4gQXJyYXkuZnJvbShyZXR1cm5UeXBlcykuam9pbignIHwgJyk7XG5cdH1cblxuXHQvKipcblx0ICogSW5mZXIgdHlwZSBmcm9tIGluaXRpYWxpemVyXG5cdCAqL1xuXHRwcml2YXRlIGluZmVyVHlwZUZyb21Jbml0aWFsaXplciAoXG5cdFx0aW5pdGlhbGl6ZXI6IHRzLkV4cHJlc3Npb24sXG5cdFx0ZGF0YVR5cGVNYXA/OiBNYXA8c3RyaW5nLCBzdHJpbmc+LFxuXHRcdGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz5cblx0KTogc3RyaW5nIHtcblx0XHRzd2l0Y2ggKGluaXRpYWxpemVyLmtpbmQpIHtcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuU3RyaW5nTGl0ZXJhbDpcblx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVtZXJpY0xpdGVyYWw6XG5cdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkOlxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdWxsS2V5d29yZDpcblx0XHRcdHJldHVybiAnbnVsbCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlVuZGVmaW5lZEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3VuZGVmaW5lZCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkFycmF5TGl0ZXJhbEV4cHJlc3Npb246XG5cdFx0XHRyZXR1cm4gJ0FycmF5PHVua25vd24+Jztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb246XG5cdFx0XHRyZXR1cm4gJ29iamVjdCc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk5ld0V4cHJlc3Npb246IHtcblx0XHRcdC8vIEhhbmRsZSBuZXcgRGF0ZSgpLCBuZXcgTWFwKCksIGV0Yy5cblx0XHRcdGNvbnN0IG5ld0V4cHIgPSBpbml0aWFsaXplciBhcyB0cy5OZXdFeHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihuZXdFeHByLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdHJldHVybiBuZXdFeHByLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdH1cblx0XHRcdHJldHVybiAnb2JqZWN0Jztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkJpbmFyeUV4cHJlc3Npb246IHtcblx0XHRcdC8vIEhhbmRsZSBhcml0aG1ldGljIG9wZXJhdGlvbnM6IGEgKiBiLCBhICsgYiwgYSAtIGIsIGEgLyBiXG5cdFx0XHRjb25zdCBiaW5hcnlFeHByID0gaW5pdGlhbGl6ZXIgYXMgdHMuQmluYXJ5RXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IGxlZnRUeXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIoYmluYXJ5RXhwci5sZWZ0LCBkYXRhVHlwZU1hcCwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdGNvbnN0IHJpZ2h0VHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKGJpbmFyeUV4cHIucmlnaHQsIGRhdGFUeXBlTWFwLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0XHRcblx0XHRcdC8vIENoZWNrIGlmIGl0J3MgYW4gYXJpdGhtZXRpYyBvcGVyYXRvclxuXHRcdFx0Y29uc3Qgb3BlcmF0b3IgPSBiaW5hcnlFeHByLm9wZXJhdG9yVG9rZW4ua2luZDtcblx0XHRcdGlmIChvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5Bc3Rlcmlza1Rva2VuIHx8XG5cdFx0XHRcdCAgICBvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5TbGFzaFRva2VuIHx8XG5cdFx0XHRcdCAgICBvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5NaW51c1Rva2VuIHx8XG5cdFx0XHRcdCAgICBvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5QZXJjZW50VG9rZW4pIHtcblx0XHRcdFx0Ly8gQXJpdGhtZXRpYyBvcGVyYXRpb25zIG9uIG51bWJlcnMgcHJvZHVjZSBudW1iZXJzXG5cdFx0XHRcdGlmICgobGVmdFR5cGUgPT09ICdudW1iZXInIHx8IGxlZnRUeXBlID09PSAndW5rbm93bicpICYmXG5cdFx0XHRcdFx0ICAgIChyaWdodFR5cGUgPT09ICdudW1iZXInIHx8IHJpZ2h0VHlwZSA9PT0gJ3Vua25vd24nKSkge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLlBsdXNUb2tlbikge1xuXHRcdFx0XHQvLyBQbHVzIGNhbiBiZSBhZGRpdGlvbiBvciBzdHJpbmcgY29uY2F0ZW5hdGlvblxuXHRcdFx0XHRpZiAobGVmdFR5cGUgPT09ICdzdHJpbmcnIHx8IHJpZ2h0VHlwZSA9PT0gJ3N0cmluZycpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGxlZnRUeXBlID09PSAnbnVtYmVyJyAmJiByaWdodFR5cGUgPT09ICdudW1iZXInKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgcHJvcGVydHkgYWNjZXNzIGxpa2UgZGF0YS52YWx1ZSwgZGF0YS5pZFxuXHRcdFx0aWYgKGRhdGFUeXBlTWFwKSB7XG5cdFx0XHRcdGNvbnN0IGFjY2Vzc0NoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGluaXRpYWxpemVyKTtcblx0XHRcdFx0aWYgKGFjY2Vzc0NoYWluKSB7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IGRhdGFUeXBlTWFwLmdldChhY2Nlc3NDaGFpbik7XG5cdFx0XHRcdFx0aWYgKHR5cGUpIHtcblx0XHRcdFx0XHRcdHJldHVybiB0eXBlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gSGFuZGxlIHRoaXMubWFwLnNpemUgcGF0dGVybiAoTWFwLnNpemUgcmV0dXJucyBudW1iZXIpXG5cdFx0XHRjb25zdCBwcm9wQWNjZXNzID0gaW5pdGlhbGl6ZXIgYXMgdHMuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKHByb3BBY2Nlc3MuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y29uc3Qgb3V0ZXJQcm9wID0gcHJvcEFjY2Vzcy5leHByZXNzaW9uO1xuXHRcdFx0XHQvLyBDaGVjayBmb3IgdGhpcy5tYXAgcGF0dGVyblxuXHRcdFx0XHRsZXQgaW5uZXJOYW1lID0gJyc7XG5cdFx0XHRcdGlmIChvdXRlclByb3AuZXhwcmVzc2lvbi5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0aW5uZXJOYW1lID0gJ3RoaXMnO1xuXHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihvdXRlclByb3AuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRpbm5lck5hbWUgPSBvdXRlclByb3AuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IG1hcFByb3AgPSBvdXRlclByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBmaW5hbFByb3AgPSBwcm9wQWNjZXNzLm5hbWUudGV4dDtcblx0XHRcdFx0Ly8gdGhpcy5tYXAuc2l6ZSAtPiBudW1iZXJcblx0XHRcdFx0aWYgKGlubmVyTmFtZSA9PT0gJ3RoaXMnICYmIG1hcFByb3AgPT09ICdtYXAnICYmIGZpbmFsUHJvcCA9PT0gJ3NpemUnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuSWRlbnRpZmllcjoge1xuXHRcdFx0Ly8gSGFuZGxlIGlkZW50aWZpZXIgcmVmZXJlbmNlcyBpZiBpbiBkYXRhVHlwZU1hcFxuXHRcdFx0aWYgKGRhdGFUeXBlTWFwKSB7XG5cdFx0XHRcdGNvbnN0IG5hbWUgPSAoaW5pdGlhbGl6ZXIgYXMgdHMuSWRlbnRpZmllcikudGV4dDtcblx0XHRcdFx0Y29uc3QgdHlwZSA9IGRhdGFUeXBlTWFwLmdldChuYW1lKTtcblx0XHRcdFx0aWYgKHR5cGUpIHtcblx0XHRcdFx0XHRyZXR1cm4gdHlwZTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkVsZW1lbnRBY2Nlc3NFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBGMjI6IHZhbHVlLWxldmVsIGVsZW1lbnQgYWNjZXNzIG92ZXIgYSBjb25zdC1hc3NlcnRlZFxuXHRcdFx0Ly8gbGl0ZXJhbCBhcnJheSDigJQgYCg8Y29uc3Q+W+KApl0pWzBdYCwgYChb4oCmXSBhcyBjb25zdClbMV1gLCBvclxuXHRcdFx0Ly8gYSB0cmFja2VkIG1vZHVsZSBjb25zdCAoYGNvbnN0IHggPSA8Y29uc3Q+W+KApl1gOyBgeFswXWApIOKAlFxuXHRcdFx0Ly8gaW5mZXJzIHRoZSBlbGVtZW50J3MgbGl0ZXJhbCB0eXBlLCB0aGUgdmFsdWUtbGV2ZWwgdHdpbiBvZlxuXHRcdFx0Ly8gdGhlIHR5cGVvZi1wYXRoIHVuaW9uLiBOb24tbnVtZXJpYyBpbmRleGVzLCBub24tbGl0ZXJhbFxuXHRcdFx0Ly8gZWxlbWVudHMsIGFuZCBnZW5lcmFsIGFzc2VydGlvbnMgc3RheSBgdW5rbm93bmAuXG5cdFx0XHRjb25zdCBlbGVtZW50QWNjZXNzID0gaW5pdGlhbGl6ZXIgYXMgdHMuRWxlbWVudEFjY2Vzc0V4cHJlc3Npb247XG5cdFx0XHRjb25zdCBhcmd1bWVudCA9IGVsZW1lbnRBY2Nlc3MuYXJndW1lbnRFeHByZXNzaW9uO1xuXHRcdFx0aWYgKCFhcmd1bWVudCB8fCAhdHMuaXNOdW1lcmljTGl0ZXJhbChhcmd1bWVudCkpIHtcblx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdH1cblx0XHRcdGNvbnN0IGFycmF5TGl0ZXJhbCA9IHRoaXMuY29uc3RBcnJheUxpdGVyYWxPZihlbGVtZW50QWNjZXNzLmV4cHJlc3Npb24pO1xuXHRcdFx0aWYgKCFhcnJheUxpdGVyYWwpIHtcblx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdH1cblx0XHRcdGNvbnN0IGVsZW1lbnQgPSBhcnJheUxpdGVyYWwuZWxlbWVudHNbIHBhcnNlSW50KGFyZ3VtZW50LnRleHQsIDEwKSBdO1xuXHRcdFx0aWYgKCFlbGVtZW50IHx8IHRzLmlzU3ByZWFkRWxlbWVudChlbGVtZW50KSkge1xuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbGl0ZXJhbCA9IHRoaXMubGl0ZXJhbFR5cGVPZkV4cHJlc3Npb24oZWxlbWVudCk7XG5cdFx0XHRjb25zdCBlbGVtZW50UmVzdWx0ID0gbGl0ZXJhbCA/PyAndW5rbm93bic7XG5cdFx0XHRyZXR1cm4gZWxlbWVudFJlc3VsdDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkNhbGxFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgZnVuY3Rpb24gY2FsbHMgbGlrZSBEYXRlLm5vdygpLCBwYXJzZUludCgpLCBldGMuXG5cdFx0XHRjb25zdCBjYWxsRXhwciA9IGluaXRpYWxpemVyIGFzIHRzLkNhbGxFeHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxFeHByLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IG1ldGhvZE5hbWUgPSBjYWxsRXhwci5leHByZXNzaW9uLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3Qgb2JqTmFtZSA9IHRzLmlzSWRlbnRpZmllcihjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb24pXG5cdFx0XHRcdFx0PyBjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb24udGV4dFxuXHRcdFx0XHRcdDogJyc7XG5cdFx0XHRcdFx0XG5cdFx0XHRcdC8vIERhdGUubm93KCkgLT4gbnVtYmVyXG5cdFx0XHRcdGlmIChvYmpOYW1lID09PSAnRGF0ZScgJiYgbWV0aG9kTmFtZSA9PT0gJ25vdycpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gU3RyaW5nIG1ldGhvZHMgdGhhdCByZXR1cm4gc3RyaW5nXG5cdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAndG9TdHJpbmcnIHx8IG1ldGhvZE5hbWUgPT09ICd2YWx1ZU9mJykge1xuXHRcdFx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBIYW5kbGUgTWFwIHByb3BlcnR5IGFjY2VzcyBvbiBjbGFzcyBpbnN0YW5jZXMgKHRoaXMubWFwLiopXG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0Y29uc3Qgb3V0ZXJQcm9wID0gY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdFx0XHRcdC8vIEhhbmRsZSBib3RoICd0aGlzJyBrZXl3b3JkIGFuZCBpZGVudGlmaWVyIHBhdHRlcm5zXG5cdFx0XHRcdFx0bGV0IGlubmVyTmFtZSA9ICcnO1xuXHRcdFx0XHRcdGlmIChvdXRlclByb3AuZXhwcmVzc2lvbi5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0XHRpbm5lck5hbWUgPSAndGhpcyc7XG5cdFx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc0lkZW50aWZpZXIob3V0ZXJQcm9wLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0XHRpbm5lck5hbWUgPSBvdXRlclByb3AuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCBtYXBQcm9wID0gb3V0ZXJQcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0XHQvLyB0aGlzLm1hcC5YKCkgcGF0dGVybnNcblx0XHRcdFx0XHRpZiAoaW5uZXJOYW1lID09PSAndGhpcycgJiYgbWFwUHJvcCA9PT0gJ21hcCcpIHtcblx0XHRcdFx0XHRcdC8vIFRyeSB0byBnZXQgdGhlIE1hcCdzIHZhbHVlIHR5cGUgZnJvbSBjbGFzcyBwcm9wZXJ0aWVzXG5cdFx0XHRcdFx0XHRsZXQgbWFwVmFsdWVUeXBlID0gJ3Vua25vd24nO1xuXHRcdFx0XHRcdFx0aWYgKGNsYXNzUHJvcGVydHlUeXBlcykge1xuXHRcdFx0XHRcdFx0XHRjb25zdCBtYXBUeXBlID0gY2xhc3NQcm9wZXJ0eVR5cGVzLmdldCgnbWFwJyk7XG5cdFx0XHRcdFx0XHRcdGlmIChtYXBUeXBlICYmIG1hcFR5cGUuc3RhcnRzV2l0aCgnTWFwPCcpKSB7XG5cdFx0XHRcdFx0XHRcdFx0Ly8gUGFyc2UgTWFwPEssIFY+IHRvIGdldCBWXG5cdFx0XHRcdFx0XHRcdFx0Y29uc3QgbWF0Y2ggPSBtYXBUeXBlLm1hdGNoKC9NYXA8W14sXSssXFxzKiguKyk+JC8pO1xuXHRcdFx0XHRcdFx0XHRcdGlmIChtYXRjaCkge1xuXHRcdFx0XHRcdFx0XHRcdFx0WyAsIG1hcFZhbHVlVHlwZSBdID0gbWF0Y2g7XG5cdFx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2hhcycpIHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3NldCcpIHJldHVybiAndGhpcyc7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2dldCcpIHJldHVybiBtYXBWYWx1ZVR5cGU7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2RlbGV0ZScpIHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2NsZWFyJykgcmV0dXJuICd2b2lkJztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAndmFsdWVzJykgcmV0dXJuIGBJdGVyYWJsZUl0ZXJhdG9yPCR7bWFwVmFsdWVUeXBlfT5gO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdrZXlzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPHN0cmluZz4nO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdlbnRyaWVzJykgcmV0dXJuIGBJdGVyYWJsZUl0ZXJhdG9yPFtzdHJpbmcsICR7bWFwVmFsdWVUeXBlfV0+YDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gRGlyZWN0IG1hcC5YKCkgY2FsbHNcblx0XHRcdFx0aWYgKG9iak5hbWUgPT09ICdtYXAnIHx8IG9iak5hbWUgPT09ICdvYmonKSB7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdoYXMnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnc2V0JykgcmV0dXJuICd0aGlzJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2dldCcpIHJldHVybiAndW5rbm93bic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdkZWxldGUnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnY2xlYXInKSByZXR1cm4gJ3ZvaWQnO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAndmFsdWVzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPHVua25vd24+Jztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2tleXMnKSByZXR1cm4gJ0l0ZXJhYmxlSXRlcmF0b3I8c3RyaW5nPic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdlbnRyaWVzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPFtzdHJpbmcsIHVua25vd25dPic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIHBhcnNlSW50LCBwYXJzZUZsb2F0IC0+IG51bWJlclxuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjYWxsRXhwci5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBmbk5hbWUgPSBjYWxsRXhwci5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdwYXJzZUludCcgfHwgZm5OYW1lID09PSAncGFyc2VGbG9hdCcpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ1N0cmluZycpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ051bWJlcicpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ0Jvb2xlYW4nKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlRlbXBsYXRlRXhwcmVzc2lvbjpcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTm9TdWJzdGl0dXRpb25UZW1wbGF0ZUxpdGVyYWw6IHtcblx0XHRcdC8vIFRlbXBsYXRlIGxpdGVyYWxzIGxpa2UgYCR7YmFzZVZhbHVlfS0ke2V4dHJhfWAgYWx3YXlzIHByb2R1Y2Ugc3RyaW5nc1xuXHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdH1cblx0XHRkZWZhdWx0OlxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0KiBDb2xsZWN0IHVzYWdlIGluZm9ybWF0aW9uIGZvciB0eXBlIHJlZmVyZW5jZXNcblx0XHRcdCovXG5cdHByaXZhdGUgY29sbGVjdFVzYWdlIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgZm9yIG5ldyBUeXBlKCkgaW5zdGFudGlhdGlvblxuXHRcdGlmICh0cy5pc05ld0V4cHJlc3Npb24obm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRsZXQgdHlwZU5hbWU6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdHR5cGVOYW1lID0gdGhpcy5yZXNvbHZlVHlwZVBhdGgobm9kZS5leHByZXNzaW9uKTtcblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdHR5cGVOYW1lID0gdGhpcy5nZXRUeXBlTmFtZUZyb21FeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHlwZU5hbWUpIHtcblx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHQpO1xuXHRcdFx0XHR0aGlzLmFkZFVzYWdlKHR5cGVOYW1lLCB7XG5cdFx0XHRcdFx0bG9jYXRpb24gICAgICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0a2luZCAgICAgICAgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0XHRcdGNvZGUgICAgICAgICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdC8vIENvbnN0cnVjdG9yIGV4cHJlc3Npb24gdGV4dCAoJ1RoaW5nJywgJ3VzZXIuQWRtaW5FbnRpdHknLFxuXHRcdFx0XHRcdC8vIGEgbG9va3VwIGFsaWFzKSDigJQgQ3JlYXRpb25BbmNob3IuY29uc3RydWN0b3JUZXh0IChQaGFzZSAzKVxuXHRcdFx0XHRcdGNvbnN0cnVjdG9yVGV4dCA6IG5vZGUuZXhwcmVzc2lvbi5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdH0pO1xuXHRcdFx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50IGZyb20gbmV3IFR5cGUoKSBmb3IgZmxvdyBhbmFseXNpc1xuXHRcdFx0XHR0aGlzLnRyYWNrTmV3QXNzaWdubWVudChub2RlLCB0eXBlTmFtZSk7XG5cdFx0XHRcdC8vIEFsc28gcmVjb3JkIGFzIGZsb3cgZXZlbnRcblx0XHRcdFx0dGhpcy5hZGRGbG93KHR5cGVOYW1lLCB7XG5cdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRraW5kICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdGNvbnRleHQgIDogJ25ldyBleHByZXNzaW9uJyxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcblx0XHQvLyBDaGVjayBmb3IgcHJvcGVydHkgYWNjZXNzIG9uIGluc3RhbmNlcyAodXNlci5BZG1pblR5cGUpXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRjb25zdCBwcm9wTmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0Ly8gaW5zdGFuY2UuY2xvbmUg4oCUIHRoZSBQUk9QRVJUWSBmb3JtIChjb3JlIHR5cGVzIGl0XG5cdFx0XHQvLyBgcmVhZG9ubHkgY2xvbmU6IHRoaXNgKTogdGhlIHJlc3VsdCB2YXJpYWJsZSBiaW5kcyB0byB0aGVcblx0XHRcdC8vIHNvdXJjZSBpbnN0YW5jZSdzIHR5cGUsIHNhbWUgYXMgdGhlIGZvcmsoKS9jbG9uZSgpIGNhbGxcblx0XHRcdC8vIGZvcm1zIChhd2FpdC10cmFuc3BhcmVudCkuIFRoZSBjYWxsIGZvcm0ncyByZWNvcmRpbmcgaGFwcGVuc1xuXHRcdFx0Ly8gaW4gdGhlIENhbGxFeHByZXNzaW9uIGJyYW5jaDsgdGhlIHByb3BlcnR5IGJyYW5jaCBza2lwcyBpdFxuXHRcdFx0Ly8gdG8gYXZvaWQgYSBkdXBsaWNhdGUgZW50cnkgYXQgdGhlIHNhbWUgc2l0ZVxuXHRcdFx0aWYgKHByb3BOYW1lID09PSAnY2xvbmUnICYmIHRzLmlzSWRlbnRpZmllcihub2RlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IGNsb25lZFBhdGggPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChub2RlLmV4cHJlc3Npb24udGV4dCk7XG5cdFx0XHRcdGNvbnN0IGlzQ2FsbEZvcm0gPSB0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUucGFyZW50KSAmJiBub2RlLnBhcmVudC5leHByZXNzaW9uID09PSBub2RlO1xuXHRcdFx0XHRpZiAoY2xvbmVkUGF0aCkge1xuXHRcdFx0XHRcdGlmICghaXNDYWxsRm9ybSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdFx0XHQpO1xuXHRcdFx0XHRcdFx0dGhpcy5hZGRVc2FnZShjbG9uZWRQYXRoLCB7XG5cdFx0XHRcdFx0XHRcdGxvY2F0aW9uICAgICAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdFx0XHRraW5kICAgICAgICAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0XHRcdGNvZGUgICAgICAgICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdFx0XHRjb25zdHJ1Y3RvclRleHQgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShub2RlLCBjbG9uZWRQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gQ2hlY2sgaWYgdGhpcyBsb29rcyBsaWtlIGEgdHlwZSBhY2Nlc3MgcGF0dGVyblxuXHRcdFx0aWYgKHByb3BOYW1lICYmIHRoaXMuaXNMaWtlbHlUeXBlTmFtZShwcm9wTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHQpO1xuXHRcdFx0XHRcdC8vIFRyeSB0byByZXNvbHZlIGZ1bGwgcGF0aFxuXHRcdFx0XHRjb25zdCBmdWxsUGF0aCA9IHRoaXMucmVzb2x2ZVR5cGVQYXRoKG5vZGUpO1xuXHRcdFx0XHRpZiAoZnVsbFBhdGgpIHtcblx0XHRcdFx0XHR0aGlzLmFkZFVzYWdlKGZ1bGxQYXRoLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdFx0a2luZCAgICAgOiAncHJvcGVydHlBY2Nlc3MnLFxuXHRcdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0Ly8gQ2hlY2sgZm9yIGxvb2t1cCgnVHlwZU5hbWUnKSBvciBsb29rdXAoc291cmNlLCAnVHlwZU5hbWUnKSBjYWxsc1xuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0Y29uc3QgZnVuY05hbWUgPSB0aGlzLmdldEZ1bmN0aW9uTmFtZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdFx0aWYgKGZ1bmNOYW1lID09PSAnbG9va3VwJyAmJiBub2RlLmFyZ3VtZW50cy5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdGNvbnN0IHR5cGVQYXRoID0gdGhpcy5yZXNvbHZlTG9va3VwUGF0aChub2RlKTtcblx0XHRcdFx0aWYgKHR5cGVQYXRoKSB7XG5cdFx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0XHQpO1xuXHRcdFx0XHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRcdFx0dGhpcy5hZGRVc2FnZSh0eXBlUGF0aCwge1xuXHRcdFx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdFx0XHRraW5kIDogJ2xvb2t1cCcsXG5cdFx0XHRcdFx0XHRjb2RlIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudCBmcm9tIGxvb2t1cCBmb3IgaW5zdGFudGlhdGlvbiB0cmFja2luZ1xuXHRcdFx0XHRcdHRoaXMudHJhY2tMb29rdXBBc3NpZ25tZW50KG5vZGUsIHR5cGVQYXRoKTtcblx0XHRcdFx0XHQvLyBSZWNvcmQgZm9yIHRoZSBoYXJkLWZhaWwgbGF3IGV2ZW4gd2hlbiBhZGRVc2FnZSBkcm9wcGVkXG5cdFx0XHRcdFx0Ly8gdGhlIHBhdGggKHVua25vd24gcGF0aHMgYXJlIGV4YWN0bHkgdGhlIGZhaWx1cmUgY2xhc3MpXG5cdFx0XHRcdFx0dGhpcy5sb29rdXBSZWZlcmVuY2VzLnB1c2goeyBwYXRoIDogdHlwZVBhdGgsIGxvY2F0aW9uIH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdC8vIENoYWluLWZvcm0gY29uc3RydWN0aW9uOiBgbmV3IFIoLi4uKS5BKC4uLilgIC8gdGhlIGF3YWl0ZWRcblx0XHRcdC8vIHNpbmdsZS1jaGFpbiBgYXdhaXQgbmV3IFIoLi4uKS5BKC4uLikuQiguLi4pYCDigJQgdGhlIGNhbGwgb25cblx0XHRcdC8vIHRoZSBmcmVzaCBpbnN0YW5jZSBjb25zdHJ1Y3RzIHRoZSBjaGFpbiBUSVAgKGF3YWl0IGlzXG5cdFx0XHQvLyB0cmFuc3BhcmVudDsgdGhlIE5ld0V4cHJlc3Npb24gYnJhbmNoIGFscmVhZHkgcmVjb3JkZWQgdGhlXG5cdFx0XHQvLyBpbm5lciByb290KS4gVGhlIHJlc3VsdCB2YXJpYWJsZSBiaW5kcyB0byB0aGUgdGlwLCBub3QgdGhlXG5cdFx0XHQvLyByb290ICh0cmFja05ld0Fzc2lnbm1lbnQgcmVzb2x2ZXMgdGhlIHNhbWUgdGlwKVxuXHRcdFx0Y29uc3QgY2hhaW5UaXAgPSB0aGlzLnJlc29sdmVDaGFpblRpcFR5cGVQYXRoKG5vZGUpO1xuXHRcdFx0aWYgKGNoYWluVGlwKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkQ29uc3RydWN0aW9uVXNhZ2Uobm9kZSwgY2hhaW5UaXAsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdCk7XG5cdFx0XHRcdHRoaXMuYWRkRmxvdyhjaGFpblRpcCwge1xuXHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0a2luZCAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRjb250ZXh0ICA6ICdjaGFpbmVkIGNvbnN0cnVjdGlvbicsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBtbmVtb25pY2EgY2FsbC9hcHBseShlbnRpdHksIEN0b3IsIC4uLikgLyBiaW5kKGVudGl0eSwgQ3Rvcikg4oCUXG5cdFx0XHQvLyB0eXBlZCBjb25zdHJ1Y3Rpb24gd2l0aG91dCBgbmV3YDogdGhlIEN0b3IgYXJndW1lbnQgKGFyZyAxKSBpc1xuXHRcdFx0Ly8gdGhlIGNvbnN0cnVjdGVkIHR5cGUuIEltcG9ydC1hd2FyZTogb25seSBpZGVudGlmaWVycyBhY3R1YWxseVxuXHRcdFx0Ly8gaW1wb3J0ZWQgZnJvbSAnbW5lbW9uaWNhJyAob3IgbWVtYmVycyBvZiBhIHRyYWNrZWRcblx0XHRcdC8vIG1vZHVsZS1vYmplY3QgYWxpYXMpIG1hdGNoIOKAlCB1c2VybGFuZCBjYWxsL2FwcGx5L2JpbmQgbmV2ZXJcblx0XHRcdC8vIGRvLiBjYWxsL2FwcGx5IHJlY29yZCB0aGUgY29uc3RydWN0aW9uOyBiaW5kKCkgY29uc3RydWN0c1xuXHRcdFx0Ly8gbm90aGluZyDigJQgaXQgb25seSBiaW5kcyB0aGUgcmVzdWx0IHZhcmlhYmxlIHRvIHRoZSBDdG9yJ3Ncblx0XHRcdC8vIHR5cGUgKHJ1bnRpbWUgSW5zdGFuY2VSZXN1bHQ8TWVyZ2U8RSxUPj4gYXBwcm94aW1hdGVkIGJ5IFRcblx0XHRcdC8vIHdpdGhpbiB0aGUgb3V0cHV0IGNvbnRyYWN0KVxuXHRcdFx0Y29uc3QgY29uc3RydWN0aW9uUGF0aCA9IHRoaXMucmVzb2x2ZUNvbnN0cnVjdGlvbkZuVHlwZVBhdGgobm9kZSk7XG5cdFx0XHRpZiAoY29uc3RydWN0aW9uUGF0aCkge1xuXHRcdFx0XHRjb25zdCBpc0JpbmRGb3JtID0gdGhpcy5pc01uZW1vbmljYUNvbnN0cnVjdGlvbkZuKG5vZGUuZXhwcmVzc2lvbiwgJ2JpbmQnKTtcblx0XHRcdFx0aWYgKCFpc0JpbmRGb3JtKSB7XG5cdFx0XHRcdFx0Y29uc3QgY3RvckFyZ1RleHQgPSBub2RlLmFyZ3VtZW50c1sgMSBdPy5nZXRUZXh0KHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRcdHRoaXMucmVjb3JkQ29uc3RydWN0aW9uVXNhZ2Uobm9kZSwgY29uc3RydWN0aW9uUGF0aCwgc291cmNlRmlsZSwgY3RvckFyZ1RleHQpO1xuXHRcdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdFx0KTtcblx0XHRcdFx0XHR0aGlzLmFkZEZsb3coY29uc3RydWN0aW9uUGF0aCwge1xuXHRcdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRcdGtpbmQgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRcdGNvbnRleHQgIDogJ2NhbGwvYXBwbHkgY29uc3RydWN0aW9uJyxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShub2RlLCBjb25zdHJ1Y3Rpb25QYXRoKTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gaW5zdGFuY2UuZm9yaygpL2Nsb25lKCkg4oCUIHJ1bnRpbWUgcmUtcnVucyBjb25zdHJ1Y3Rpb24gKGhvb2tzXG5cdFx0XHQvLyBmaXJlLCBhIGRpc3RpbmN0IGluc3RhbmNlIG9uIGEgZGlzdGluY3QgbGluZSksIHNvIGFuXG5cdFx0XHQvLyBgaW5zdGFudGlhdGlvbmAgdXNhZ2UgcmVjb3JkcyB0aGUgc2l0ZSBJTiBBRERJVElPTiB0byB0aGVcblx0XHRcdC8vIHJlc3VsdC12YXIgYmluZGluZyBhbmQgdGhlIGdlbmVyaWMgbWV0aG9kQ2FsbCBmbG93ICh0aGUgZW50cnlcblx0XHRcdC8vIGlzIGJ5dGUtaW5kaXN0aW5ndWlzaGFibGUgZnJvbSBgbmV3YCB1bnRpbCB0aGUgZGVmZXJyZWRcblx0XHRcdC8vIG1lY2hhbmlzbS1raW5kIHJldmlzaW9uIOKAlCB0aGUgb3duZXIncyBleHBsaWNpdCBjYWxsKS4gRnJlZVxuXHRcdFx0Ly8gdXRpbHMubWVyZ2UoYSwgYiwgLi4uKSAvIHV0aWxzLmZvcmsoaW5zdGFuY2UpKC4uLikgYXJlXG5cdFx0XHQvLyBjb25zdHJ1Y3Rpb24gb2YgYSdzIHR5cGUgdG9vIChtZXJnZSA9IGZvcmsoYSkgb3ZlciBiJ3Ncblx0XHRcdC8vIGNvbnRleHQpOyB0aGUgcmVzdWx0IGJpbmRpbmcga2VlcHMgdGhlIGRvY3VtZW50ZWQgYXJnLTBcblx0XHRcdC8vIGFwcHJveGltYXRpb25cblx0XHRcdGNvbnN0IGZvcmtMaWtlUGF0aCA9IHRoaXMucmVzb2x2ZUZvcmtMaWtlVHlwZVBhdGgobm9kZSk7XG5cdFx0XHRpZiAoZm9ya0xpa2VQYXRoKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkQ29uc3RydWN0aW9uVXNhZ2Uobm9kZSwgZm9ya0xpa2VQYXRoLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0dGhpcy5iaW5kUmVzdWx0VmFyaWFibGUobm9kZSwgZm9ya0xpa2VQYXRoKTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHV0aWxzUGF0aCA9IHRoaXMucmVzb2x2ZVV0aWxzRm5UeXBlUGF0aChub2RlKTtcblx0XHRcdGlmICh1dGlsc1BhdGgpIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZShub2RlLCB1dGlsc1BhdGgsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShub2RlLCB1dGlsc1BhdGgpO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIEdldCBmdW5jdGlvbiBuYW1lIGZyb20gZXhwcmVzc2lvbiAoaWRlbnRpZmllciBvciBwcm9wZXJ0eSBhY2Nlc3MpXG5cdFx0XHQqL1xuXHRwcml2YXRlIGdldEZ1bmN0aW9uTmFtZSAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIGV4cHIudGV4dDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0KiBBZGQgYSB1c2FnZSB0byB0aGUgY29sbGVjdGlvblxuXHRcdFx0Ki9cblx0cHJpdmF0ZSBhZGRVc2FnZSAodHlwZVBhdGg6IHN0cmluZywgdXNhZ2U6IFVzYWdlSW5mbyk6IHZvaWQge1xuXHRcdC8vIE9ubHkgdHJhY2sgdXNhZ2VzIG9mIG1uZW1vbmljYS1kZWZpbmVkIHR5cGVzXG5cdFx0aWYgKCF0aGlzLmRlZmluaXRpb25zLmhhcyh0eXBlUGF0aCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKCF0aGlzLnVzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLnVzYWdlcy5zZXQodHlwZVBhdGgsIFtdKTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgZHVwbGljYXRlcyBiYXNlZCBvbiBsb2NhdGlvbiwgY29kZSwgYW5kIGtpbmRcblx0XHRjb25zdCBleGlzdGluZ1VzYWdlcyA9IHRoaXMudXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGlzRHVwbGljYXRlID0gZXhpc3RpbmdVc2FnZXMuc29tZShleGlzdGluZyA9PlxuXHRcdFx0ZXhpc3RpbmcubG9jYXRpb24gPT09IHVzYWdlLmxvY2F0aW9uICYmXG5cdFx0XHRcdGV4aXN0aW5nLmNvZGUgPT09IHVzYWdlLmNvZGUgJiZcblx0XHRcdFx0ZXhpc3Rpbmcua2luZCA9PT0gdXNhZ2Uua2luZCk7XG5cblx0XHRpZiAoIWlzRHVwbGljYXRlKSB7XG5cdFx0XHRleGlzdGluZ1VzYWdlcy5wdXNoKHVzYWdlKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBFRFMgKEV4ZWN1dGlvbiBEYXRhIFN0b3JhZ2UpIHVzYWdlIGluZm9ybWF0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RFRFMgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkgfHwgIW5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZ1bmNOYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIWZ1bmNOYW1lKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXHRcdC8vIEVuY2xvc2luZyBtbmVtb25pY2EgdHlwZSBwYXRoIOKAlCB3cmFwIGFyZ3MgYXJlIHVzdWFsbHkgbG9jYWxcblx0XHQvLyBmdW5jdGlvbnMsIHNvIHRoZSBvd25pbmcgZGVmaW5lKCkvbGF6eSgpIGhhbmRsZXIgb3IgZGVjb3JhdGVkXG5cdFx0Ly8gY2xhc3MgaXMgd2hhdCBlZHMuanNvbiBjb25zdW1lcnMgKEdyYXBoQnVpbGRlcikgY2FuIGpvaW4gb24uXG5cdFx0Y29uc3Qgc2NvcGUgPSB0aGlzLnJlc29sdmVFRFNTY29wZShub2RlKTtcblxuXHRcdC8vIHdyYXAoZm4pLCB3cmFwQ29uc3RydWN0b3JBcmcoZm4sIHBhcmVudCksIHVwZ3JhZGVDb25zdHJ1Y3RvckFyZyhhcmcsIGluc3QpLCB3cmFwSW5zdGFuY2VNZXRob2RzKG9iailcblx0XHRpZiAoXG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3dyYXAnIHx8XG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3dyYXBDb25zdHJ1Y3RvckFyZycgfHxcblx0XHRcdGZ1bmNOYW1lID09PSAndXBncmFkZUNvbnN0cnVjdG9yQXJnJyB8fFxuXHRcdFx0ZnVuY05hbWUgPT09ICd3cmFwSW5zdGFuY2VNZXRob2RzJ1xuXHRcdCkge1xuXHRcdFx0Y29uc3QgdGFyZ2V0VHlwZSA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShub2RlLmFyZ3VtZW50c1sgMCBdKTtcblx0XHRcdC8vIGRpdmUncyB3cmFwLWZhbWlseSBzaWduYXR1cmVzIChkaXZlL3NyYy9pbmRleC50cyk6XG5cdFx0XHQvLyAgIHdyYXAoZm4sIGxhYmVsPykgfCB3cmFwKGZuLCBjb250ZXh0PywgbGFiZWw/KVxuXHRcdFx0Ly8gICB3cmFwQ29uc3RydWN0b3JBcmcoZm4sIGNvbnRleHQpXG5cdFx0XHQvLyAgIHVwZ3JhZGVDb25zdHJ1Y3RvckFyZyhhcmcsIGluc3RhbmNlKVxuXHRcdFx0Ly8gICB3cmFwSW5zdGFuY2VNZXRob2RzKGluc3RhbmNlKVxuXHRcdFx0Ly8g4oCmc28gdGhlIGluc3RhbmNlL2NvbnRleHQgYXJnIHNpdHMgYXQgYXJnc1sxXSAoYXJnc1swXSBmb3Jcblx0XHRcdC8vIHdyYXBJbnN0YW5jZU1ldGhvZHMpIGFuZCBhIHN0cmluZyBsaXRlcmFsIGluIGFyZ3NbMS4uMl0gaXMgdGhlIGxhYmVsXG5cdFx0XHRjb25zdCBpbnN0YW5jZUFyZ05vZGUgPSBmdW5jTmFtZSA9PT0gJ3dyYXBJbnN0YW5jZU1ldGhvZHMnXG5cdFx0XHRcdD8gbm9kZS5hcmd1bWVudHNbIDAgXVxuXHRcdFx0XHQ6IG5vZGUuYXJndW1lbnRzWyAxIF07XG5cdFx0XHQvLyBGaXJlLWFuZC1mb3JnZXQgd3JhcHBlcnMgKHdpcmUtdXAgaGVscGVycywgcmVnaXN0cmF0aW9uXG5cdFx0XHQvLyBmdW5jdGlvbnMpIHNpdCBvdXRzaWRlIGFueSBkZWZpbmUoKS9sYXp5KCkgaGFuZGxlciwgc28gdGhlXG5cdFx0XHQvLyBsZXhpY2FsIHNjb3BlIGlzIGFic2VudCDigJQgYXR0cmlidXRlIHRocm91Z2ggdGhlIGluc3RhbmNlL2NvbnRleHRcblx0XHRcdC8vIGFyZ3VtZW50IGluc3RlYWQ6IGEgdHJhY2tlZCBhc3NpZ25tZW50LCBlbHNlIHRoZSBlbmNsb3Npbmdcblx0XHRcdC8vIGZ1bmN0aW9uJ3MgcGFyYW1ldGVyIGFubm90YXRpb24gcmVzb2x2ZWQgdGhyb3VnaCB0aGUgZ3JhcGggbGF3XG5cdFx0XHRjb25zdCBpbnN0YW5jZVR5cGVQYXRoID0gaW5zdGFuY2VBcmdOb2RlXG5cdFx0XHRcdD8gdGhpcy5yZXNvbHZlV3JhcEluc3RhbmNlVHlwZVBhdGgoaW5zdGFuY2VBcmdOb2RlKVxuXHRcdFx0XHQ6IHVuZGVmaW5lZDtcblx0XHRcdGNvbnN0IGVmZmVjdGl2ZVNjb3BlID0gc2NvcGUgPz8gaW5zdGFuY2VUeXBlUGF0aDtcblx0XHRcdGNvbnN0IGluZm86IEVEU0luZm8gPSB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgIDogJ3dyYXAnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdHNjb3BlICAgICAgOiBlZmZlY3RpdmVTY29wZSxcblx0XHRcdFx0Zm4gICAgICAgICA6IGZ1bmNOYW1lLFxuXHRcdFx0fTtcblx0XHRcdGlmIChpbnN0YW5jZUFyZ05vZGUgJiYgdHMuaXNJZGVudGlmaWVyKGluc3RhbmNlQXJnTm9kZSkpIHtcblx0XHRcdFx0aW5mby5pbnN0YW5jZUFyZyA9IGluc3RhbmNlQXJnTm9kZS50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBleHRyYUFyZyBvZiBbIG5vZGUuYXJndW1lbnRzWyAxIF0sIG5vZGUuYXJndW1lbnRzWyAyIF0gXSkge1xuXHRcdFx0XHRpZiAoZXh0cmFBcmcgJiYgdHMuaXNTdHJpbmdMaXRlcmFsKGV4dHJhQXJnKSkge1xuXHRcdFx0XHRcdGluZm8ubGFiZWwgPSBleHRyYUFyZy50ZXh0O1xuXHRcdFx0XHRcdGJyZWFrO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBBIHdyYXAoKSBjYWxsIG5lc3RlZCBpbnNpZGUgYW5vdGhlciB3cmFwcGVkIGJvZHkgY2FycmllcyB0aGVcblx0XHRcdC8vIGxpbmsgdG8gdGhlIHNpdGUgd2hvc2UgcnVudGltZSB3cmFwcGluZyBjYXVzZWQgaXQg4oCUIGFuZCwgd2hlblxuXHRcdFx0Ly8gdGhlIG5lc3RlZCBzaXRlIGhhcyBubyBzY29wZSBvZiBpdHMgb3duLCB0aGUgY2F1c2luZyBzaXRlJ3Ncblx0XHRcdC8vIHNjb3BlIGF0dHJpYnV0aW9uIHRyYXZlbHMgd2l0aCB0aGUgbGlua1xuXHRcdFx0Y29uc3QgdmlhTGluayA9IHRoaXMubmVzdGVkV3JhcFZpYS5nZXQobm9kZSk7XG5cdFx0XHRpZiAodmlhTGluaykge1xuXHRcdFx0XHRpbmZvLnZpYSA9IHZpYUxpbmsudmlhO1xuXHRcdFx0XHRpZiAoaW5mby5zY29wZSA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdFx0aW5mby5zY29wZSA9IHZpYUxpbmsuc2NvcGU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIGRpdmUgd3JhcHMgcmV0dXJuZWQgZnVuY3Rpb25zIHRvbywgYW5kIGFueSBtbmVtb25pY2EgaW5zdGFuY2Vcblx0XHRcdC8vIGNyZWF0ZWQgaW5zaWRlIHRoZSB3cmFwcGVkIGJvZHkgaXMgYSBndWFyYW50ZWVkIHBhdGggaGl0IOKAlFxuXHRcdFx0Ly8gYm90aCBhcmUgY2FsY3VsYWJsZSBBb1QsIHNvIHJlY29yZCB0aGVtXG5cdFx0XHRjb25zdCB3cmFwcGVkID0gdGhpcy5yZXNvbHZlRnVuY3Rpb25Bcmd1bWVudChub2RlLmFyZ3VtZW50c1sgMCBdLCBzb3VyY2VGaWxlKTtcblx0XHRcdGlmICh3cmFwcGVkKSB7XG5cdFx0XHRcdC8vIFRoZSB3cmFwcGVkIGNhbGxiYWNrIGdldHMgaXRzIG93biBzY29wZSBpbiBzY29wZXMuanNvbiBrZXllZCBieVxuXHRcdFx0XHQvLyBpdHMgc3RhcnQgcG9zaXRpb24g4oCUIHJlY29yZCB0aGF0IHNjb3BlSWQgc28gZ3JhcGggY29uc3VtZXJzIGNhblxuXHRcdFx0XHQvLyBqb2luIGEgd3JhcCBlbnRyeSB0byB0aGUgY2FsbGJhY2sncyBjcmVhdGlvbiBub2RlXG5cdFx0XHRcdGNvbnN0IGNhbGxiYWNrUG9zID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHR3cmFwcGVkLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdCk7XG5cdFx0XHRcdGNvbnN0IGNhbGxiYWNrRmlsZSA9IG5vZGVQYXRoLnJlc29sdmUoc291cmNlRmlsZS5maWxlTmFtZSk7XG5cdFx0XHRcdGluZm8uY2FsbGJhY2tTY29wZUlkID0gYCR7Y2FsbGJhY2tGaWxlfToke2NhbGxiYWNrUG9zLmxpbmUgKyAxfToke2NhbGxiYWNrUG9zLmNoYXJhY3RlciArIDF9YDtcblx0XHRcdFx0Y29uc3QgY3JlYXRlc1R5cGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0XHRcdHRoaXMuYW5hbHl6ZVdyYXBwZWRCb2R5KHdyYXBwZWQsIGxvY2F0aW9uLCBzb3VyY2VGaWxlLCAwLCBuZXcgU2V0KCksIGNyZWF0ZXNUeXBlcywgZWZmZWN0aXZlU2NvcGUpO1xuXHRcdFx0XHRpZiAoY3JlYXRlc1R5cGVzLnNpemUgPiAwKSB7XG5cdFx0XHRcdFx0aW5mby5jcmVhdGVzVHlwZXMgPSBBcnJheS5mcm9tKGNyZWF0ZXNUeXBlcyk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGNvbnN0IHN0b3JlZCA9IHRoaXMuYWRkRURTKHRhcmdldFR5cGUgfHwgZWZmZWN0aXZlU2NvcGUgfHwgJ3Vua25vd24nLCBpbmZvKTtcblx0XHRcdHRoaXMud3JhcEVudHJ5QnlOb2RlLnNldChub2RlLCBzdG9yZWQpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGN1cnJlbnQoKSwgZ2V0RXJyb3JJbnN0YW5jZShlcnIpLCBnZXRGbG93KHRhcmdldD8pXG5cdFx0aWYgKGZ1bmNOYW1lID09PSAnY3VycmVudCcgfHwgZnVuY05hbWUgPT09ICdnZXRFcnJvckluc3RhbmNlJyB8fCBmdW5jTmFtZSA9PT0gJ2dldEZsb3cnKSB7XG5cdFx0XHR0aGlzLmFkZEVEUyhzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgOiAnY29udGV4dENvbnN1bWUnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRzY29wZSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGF0dGFjaEhvb2tzKGNvbGxlY3Rpb24pIOKAlCBmcm9tIEBtbmVtb25pY2Evb3RlbCwgd2lyZXMgYVxuXHRcdC8vIFR5cGVzQ29sbGVjdGlvbiB0byBkaXZlJ3MgbGlmZWN5Y2xlIHRyYWNpbmdcblx0XHRpZiAoZnVuY05hbWUgPT09ICdhdHRhY2hIb29rcycgJiYgbm9kZS5hcmd1bWVudHMubGVuZ3RoID4gMCkge1xuXHRcdFx0Y29uc3QgWyBhcmcgXSA9IG5vZGUuYXJndW1lbnRzO1xuXHRcdFx0aWYgKHRzLmlzQXJyYXlMaXRlcmFsRXhwcmVzc2lvbihhcmcpKSB7XG5cdFx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBhcmcuZWxlbWVudHMpIHtcblx0XHRcdFx0XHRjb25zdCB0YXJnZXRUeXBlID0gdGhpcy5yZXNvbHZlRURTQXJndW1lbnRUeXBlKGVsZW1lbnQpO1xuXHRcdFx0XHRcdHRoaXMuYWRkRURTKHRhcmdldFR5cGUgfHwgc2NvcGUgfHwgJ3Vua25vd24nLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0XHRcdGtpbmQgICAgICAgOiAnaG9va0F0dGFjaCcsXG5cdFx0XHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRcdFx0dGFyZ2V0VHlwZSA6IHRhcmdldFR5cGUgfHwgdW5kZWZpbmVkLFxuXHRcdFx0XHRcdFx0c2NvcGUsXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGNvbnN0IHRhcmdldFR5cGUgPSB0aGlzLnJlc29sdmVFRFNBcmd1bWVudFR5cGUoYXJnKTtcblx0XHRcdFx0dGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCBzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0XHRraW5kICAgICAgIDogJ2hvb2tBdHRhY2gnLFxuXHRcdFx0XHRcdGNvZGUsXG5cdFx0XHRcdFx0dGFyZ2V0VHlwZSA6IHRhcmdldFR5cGUgfHwgdW5kZWZpbmVkLFxuXHRcdFx0XHRcdHNjb3BlLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0eXBlIGZyb20gRURTIGNhbGwgYXJndW1lbnQgKGJlc3QgZWZmb3J0KVxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRURTQXJndW1lbnRUeXBlIChhcmc6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghYXJnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIElkZW50aWZpZXI6IHZhcmlhYmxlIG5hbWVcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdGNvbnN0IG1hcHBlZCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGFyZy50ZXh0KTtcblx0XHRcdGlmIChtYXBwZWQpIHtcblx0XHRcdFx0cmV0dXJuIG1hcHBlZDtcblx0XHRcdH1cblx0XHRcdC8vIE1heWJlIGl0J3MgYSB0eXBlIG5hbWUgZGlyZWN0bHlcblx0XHRcdGlmICh0aGlzLmRlZmluaXRpb25zLmhhcyhhcmcudGV4dCkpIHtcblx0XHRcdFx0cmV0dXJuIGFyZy50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0Ly8gbGV0LWluLXRyeTogYSBsZXQvdmFyIGJpbmRpbmcgZGVjbGFyZWQgd2l0aG91dCBhIHRyYWNrZWRcblx0XHRcdC8vIGluaXRpYWxpemVyIGFuZCBhc3NpZ25lZCBsYXRlciBpbiB0aGUgU0FNRSBzY29wZSAodGhlXG5cdFx0XHQvLyBmaXJlLWFuZC1mb3JnZXQgY2F0Y2gtZ3VhcmQgcGF0dGVybjogYGxldCBmbjsgdHJ5IHsgZm4gPVxuXHRcdFx0Ly8g4oCmIH0gY2F0Y2ggeyByZXR1cm4gfSB3cmFwKGZuLCDigKYpYCkg4oCUIGZvbGxvdyB0aGUgZmlyc3Rcblx0XHRcdC8vIHN0YXRpY2FsbHktdmlzaWJsZSBpbi1zY29wZSBhc3NpZ25tZW50LiBObyBmbG93IGFuYWx5c2lzOlxuXHRcdFx0Ly8gZnVuY3Rpb24vY2xhc3MgYm91bmRhcmllcyBhcmUgbm90IGNyb3NzZWQsIGFcblx0XHRcdC8vIG5ldmVyLWFzc2lnbmVkIGJpbmRpbmcgc3RheXMgdW5rbm93biAoRjIwIGRpc2NpcGxpbmUpLlxuXHRcdFx0Ly8gV2hlbiB0aGUgYXNzaWdubWVudCByZXNvbHZlcywgaXRzIGV2aWRlbmNlIFdJTlMgb3ZlciBhbnlcblx0XHRcdC8vIGRlY2xhcmF0aW9uIGFubm90YXRpb24gKHRoZSBjb25zdHJ1Y3RlZCBzdWJ0eXBlIGlzIHRoZSBtb3JlXG5cdFx0XHQvLyBzcGVjaWZpYyB0cnV0aCk7IGFuIHVucmVzb2x2YWJsZSBSSFMgKGEgdXNlcmxhbmQgY2FsbCwgc2F5KVxuXHRcdFx0Ly8gZmFsbHMgdGhyb3VnaCB0byB0aGUgYW5ub3RhdGlvbiBjbGFpbSBiZWxvdy5cblx0XHRcdGNvbnN0IGFzc2lnbmVkID0gdGhpcy5mb2xsb3dTY29wZUFzc2lnbm1lbnQoYXJnLnRleHQsIGFyZyk7XG5cdFx0XHRpZiAoYXNzaWduZWQpIHtcblx0XHRcdFx0Y29uc3QgcmVzb2x2ZWQgPSB0aGlzLnJlc29sdmVFRFNBcmd1bWVudFR5cGUoYXNzaWduZWQpO1xuXHRcdFx0XHRpZiAocmVzb2x2ZWQpIHtcblx0XHRcdFx0XHRyZXR1cm4gcmVzb2x2ZWQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIEFubm90YXRpb24gZmFsbGJhY2sg4oCUIHRoZSBGMjAgZGlzY2lwbGluZSBvbmUgYXJndW1lbnQgb3Zlcjpcblx0XHRcdC8vIGFuIGV4cGxpY2l0IGRlY2xhcmF0aW9uIG9yIHBhcmFtZXRlciBhbm5vdGF0aW9uIGlzIGEgdXNlclxuXHRcdFx0Ly8gY2xhaW0gd3JpdHRlbiBpbiB0aGUgQVNULCBub3QgZmxvdyBhbmFseXNpcy4gUGFyYW1ldGVyXG5cdFx0XHQvLyBmaXJzdDogaXQgc2hhZG93cyBhbiBvdXRlciBsZXQsIHNhbWUgYXMgdGhlIGNvbnRleHQtYXJnIHBhdGguXG5cdFx0XHRjb25zdCBhbm5vdGF0ZWQgPSB0aGlzLnJlc29sdmVQYXJhbWV0ZXJBbm5vdGF0aW9uVHlwZVBhdGgoYXJnLnRleHQsIGFyZykgPz9cblx0XHRcdFx0dGhpcy5yZXNvbHZlVmFyaWFibGVBbm5vdGF0aW9uVHlwZVBhdGgoYXJnLnRleHQsIGFyZyk7XG5cdFx0XHRyZXR1cm4gYW5ub3RhdGVkO1xuXHRcdH1cblxuXHRcdC8vIE5ld0V4cHJlc3Npb246IHRoZSBjb25zdHJ1Y3RlZCB0eXBlIOKAlCByZWFjaGFibGUgZGlyZWN0bHlcblx0XHQvLyAod3JhcChuZXcgVCgpLCDigKYpKSBvciB0aHJvdWdoIGEgZm9sbG93ZWQgYXNzaWdubWVudFxuXHRcdGlmICh0cy5pc05ld0V4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0Y29uc3QgY3RvckV4cHIgPSBhcmcuZXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IG5hbWUgPSB0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdG9yRXhwcilcblx0XHRcdFx0PyB0aGlzLnJlc29sdmVUeXBlUGF0aChjdG9yRXhwcilcblx0XHRcdFx0OiB0aGlzLmdldFR5cGVOYW1lRnJvbUV4cHJlc3Npb24oY3RvckV4cHIpO1xuXHRcdFx0Y29uc3Qga25vd24gPSBuYW1lICYmIHRoaXMuZGVmaW5pdGlvbnMuaGFzKG5hbWUpID8gbmFtZSA6IHVuZGVmaW5lZDtcblx0XHRcdHJldHVybiBrbm93bjtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSBhY2Nlc3M6IG9iai5wcm9wXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdHJldHVybiB0aGlzLnJlc29sdmVUeXBlUGF0aChhcmcpO1xuXHRcdH1cblxuXHRcdC8vIFRoaXMgZXhwcmVzc2lvbjogdGhpcy5zb21ldGhpbmdcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXJnKSAmJiB0cy5pc0lkZW50aWZpZXIoYXJnLmV4cHJlc3Npb24pICYmIGFyZy5leHByZXNzaW9uLnRleHQgPT09ICd0aGlzJykge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIGxldC1pbi10cnk6IGZpbmQgdGhlIFJJR0hULUhBTkQgU0lERSBvZiB0aGUgZmlyc3Qgc3RhdGljYWxseS12aXNpYmxlXG5cdCAqIGFzc2lnbm1lbnQgdG8gYG5hbWVgIGluIHRoZSBzY29wZSB0aGF0IGRlY2xhcmVzIGl0LiBUaGUgZGVjbGFyaW5nXG5cdCAqIGNvbnRhaW5lciBpcyBmb3VuZCBpbm5lcm1vc3Qtb3V0IChibG9ja3MsIGNhc2UgY2xhdXNlcywgdGhlIHNvdXJjZVxuXHQgKiBmaWxlIOKAlCB0aGUgRjIwIHdhbGspOyB0aGUgc2NhbiByZWN1cnNlcyBpbnRvIG5lc3RlZCBibG9ja3MgKHRyeS9cblx0ICogY2F0Y2gvZmluYWxseSwgaWYvZWxzZSwgbG9vcHMsIHN3aXRjaCBjYXNlcykgYnV0IE5FVkVSIGNyb3NzZXNcblx0ICogZnVuY3Rpb24gb3IgY2xhc3MgYm91bmRhcmllcyDigJQgYW4gYXNzaWdubWVudCBpbnNpZGUgYSBjbG9zdXJlIGRvZXNcblx0ICogbm90IGF0dHJpYnV0ZS4gUmV0dXJucyB1bmRlZmluZWQgd2hlbiB0aGUgYmluZGluZyBpcyBkZWNsYXJlZCBidXRcblx0ICogbmV2ZXIgYXNzaWduZWQgaW4gc2NvcGUgKGFuZCBzdG9wcyB0aGVyZTogYW4gaW5uZXIgZGVjbGFyYXRpb25cblx0ICogc2hhZG93cyBhbnkgb3V0ZXIgYmluZGluZykuXG5cdCAqL1xuXHRwcml2YXRlIGZvbGxvd1Njb3BlQXNzaWdubWVudCAobmFtZTogc3RyaW5nLCBmcm9tOiB0cy5Ob2RlKTogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBmcm9tO1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRjb25zdCBzdGF0ZW1lbnRzOiB0cy5Ob2RlQXJyYXk8dHMuU3RhdGVtZW50PiB8IHVuZGVmaW5lZCA9XG5cdFx0XHRcdHRzLmlzQmxvY2soY3VycmVudCkgfHwgdHMuaXNNb2R1bGVCbG9jayhjdXJyZW50KSB8fCB0cy5pc1NvdXJjZUZpbGUoY3VycmVudClcblx0XHRcdFx0XHQ/IGN1cnJlbnQuc3RhdGVtZW50c1xuXHRcdFx0XHRcdDogdHMuaXNDYXNlQ2xhdXNlKGN1cnJlbnQpIHx8IHRzLmlzRGVmYXVsdENsYXVzZShjdXJyZW50KVxuXHRcdFx0XHRcdFx0PyBjdXJyZW50LnN0YXRlbWVudHNcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0aWYgKHN0YXRlbWVudHMgJiYgdGhpcy5zdGF0ZW1lbnRzRGVjbGFyZVZhcmlhYmxlKHN0YXRlbWVudHMsIG5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHJocyA9IHRoaXMuZmluZEFzc2lnbm1lbnRSaHNJblN0YXRlbWVudHMoc3RhdGVtZW50cywgbmFtZSk7XG5cdFx0XHRcdHJldHVybiByaHM7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogVHJ1ZSB3aGVuIHRoZSBzdGF0ZW1lbnQgbGlzdCBjb250YWlucyBhIGBsZXRgL2B2YXJgL2Bjb25zdGBcblx0ICogZGVjbGFyYXRpb24gZm9yIGBuYW1lYCAoYW55IGluaXRpYWxpemVyIGZvcm0pLlxuXHQgKi9cblx0cHJpdmF0ZSBzdGF0ZW1lbnRzRGVjbGFyZVZhcmlhYmxlIChzdGF0ZW1lbnRzOiByZWFkb25seSB0cy5TdGF0ZW1lbnRbXSwgbmFtZTogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc3RhdGVtZW50cykge1xuXHRcdFx0aWYgKCF0cy5pc1ZhcmlhYmxlU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGRlY2xhcmF0aW9uIG9mIHN0YXRlbWVudC5kZWNsYXJhdGlvbkxpc3QuZGVjbGFyYXRpb25zKSB7XG5cdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZGVjbGFyYXRpb24ubmFtZSkgJiYgZGVjbGFyYXRpb24ubmFtZS50ZXh0ID09PSBuYW1lKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpcnN0IGBuYW1lID0gcmhzYCBhc3NpZ25tZW50IGluIHRoZSBzdGF0ZW1lbnQgbGlzdCwgcmVjdXJzaW5nXG5cdCAqIGludG8gbmVzdGVkIGluLXNjb3BlIGJsb2Nrcy4gRnVuY3Rpb24gYW5kIGNsYXNzIGJvZGllcyBhcmVcblx0ICogYm91bmRhcmllcyBhbmQgYXJlIG5vdCBlbnRlcmVkLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kQXNzaWdubWVudFJoc0luU3RhdGVtZW50cyAoXG5cdFx0c3RhdGVtZW50czogcmVhZG9ubHkgdHMuU3RhdGVtZW50W10sXG5cdFx0bmFtZTogc3RyaW5nXG5cdCk6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIHN0YXRlbWVudHMpIHtcblx0XHRcdGNvbnN0IGRpcmVjdCA9IHRoaXMuZGlyZWN0QXNzaWdubWVudFJocyhzdGF0ZW1lbnQsIG5hbWUpO1xuXHRcdFx0aWYgKGRpcmVjdCkge1xuXHRcdFx0XHRyZXR1cm4gZGlyZWN0O1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBuZXN0ZWQgb2YgdGhpcy5uZXN0ZWRTY29wZUJsb2NrcyhzdGF0ZW1lbnQpKSB7XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kQXNzaWdubWVudFJoc0luU3RhdGVtZW50cyhuZXN0ZWQsIG5hbWUpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBgbmFtZSA9IHJoc2AgYXMgYSBkaXJlY3QgZXhwcmVzc2lvbiBzdGF0ZW1lbnQuXG5cdCAqL1xuXHRwcml2YXRlIGRpcmVjdEFzc2lnbm1lbnRSaHMgKHN0YXRlbWVudDogdHMuU3RhdGVtZW50LCBuYW1lOiBzdHJpbmcpOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIXRzLmlzRXhwcmVzc2lvblN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBleHByID0gc3RhdGVtZW50LmV4cHJlc3Npb247XG5cdFx0aWYgKCF0cy5pc0JpbmFyeUV4cHJlc3Npb24oZXhwcikgfHwgZXhwci5vcGVyYXRvclRva2VuLmtpbmQgIT09IHRzLlN5bnRheEtpbmQuRXF1YWxzVG9rZW4pIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGV4cHIubGVmdCkgfHwgZXhwci5sZWZ0LnRleHQgIT09IG5hbWUpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJocyA9IGV4cHIucmlnaHQ7XG5cdFx0cmV0dXJuIHJocztcblx0fVxuXG5cdC8qKlxuXHQgKiBTdGF0ZW1lbnQgbGlzdHMgb2YgdGhlIG5lc3RlZCBibG9ja3MgdGhhdCBzdGF5IElOU0lERSB0aGUgY3VycmVudFxuXHQgKiBzY29wZSDigJQgdHJ5L2NhdGNoL2ZpbmFsbHksIGlmL2Vsc2UsIGxvb3BzLCBzd2l0Y2ggY2FzZXMsIG5lc3RlZFxuXHQgKiBibG9ja3MsIGxhYmVsZWQgc3RhdGVtZW50cy4gRnVuY3Rpb24tbGlrZSBhbmQgY2xhc3MgYm9kaWVzIGFyZVxuXHQgKiBzY29wZSBib3VuZGFyaWVzIGFuZCB5aWVsZCBub3RoaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBuZXN0ZWRTY29wZUJsb2NrcyAoc3RhdGVtZW50OiB0cy5TdGF0ZW1lbnQpOiByZWFkb25seSAocmVhZG9ubHkgdHMuU3RhdGVtZW50W10pW10ge1xuXHRcdGNvbnN0IGJsb2NrczogdHMuU3RhdGVtZW50W11bXSA9IFtdO1xuXHRcdGNvbnN0IHB1c2ggPSAobm9kZTogdHMuU3RhdGVtZW50IHwgdW5kZWZpbmVkKTogdm9pZCA9PiB7XG5cdFx0XHRpZiAobm9kZSAmJiB0cy5pc0Jsb2NrKG5vZGUpKSB7XG5cdFx0XHRcdGJsb2Nrcy5wdXNoKFsgLi4ubm9kZS5zdGF0ZW1lbnRzIF0pO1xuXHRcdFx0fVxuXHRcdH07XG5cdFx0aWYgKHRzLmlzQmxvY2soc3RhdGVtZW50KSkge1xuXHRcdFx0YmxvY2tzLnB1c2goWyAuLi5zdGF0ZW1lbnQuc3RhdGVtZW50cyBdKTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzVHJ5U3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdHB1c2goc3RhdGVtZW50LnRyeUJsb2NrKTtcblx0XHRcdGlmIChzdGF0ZW1lbnQuY2F0Y2hDbGF1c2UpIHtcblx0XHRcdFx0cHVzaChzdGF0ZW1lbnQuY2F0Y2hDbGF1c2UuYmxvY2spO1xuXHRcdFx0fVxuXHRcdFx0cHVzaChzdGF0ZW1lbnQuZmluYWxseUJsb2NrKTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzSWZTdGF0ZW1lbnQoc3RhdGVtZW50KSkge1xuXHRcdFx0cHVzaChzdGF0ZW1lbnQudGhlblN0YXRlbWVudCk7XG5cdFx0XHRwdXNoKHN0YXRlbWVudC5lbHNlU3RhdGVtZW50KTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzRm9yU3RhdGVtZW50KHN0YXRlbWVudCkgfHwgdHMuaXNGb3JJblN0YXRlbWVudChzdGF0ZW1lbnQpIHx8XG5cdFx0XHR0cy5pc0Zvck9mU3RhdGVtZW50KHN0YXRlbWVudCkgfHwgdHMuaXNXaGlsZVN0YXRlbWVudChzdGF0ZW1lbnQpIHx8XG5cdFx0XHR0cy5pc0RvU3RhdGVtZW50KHN0YXRlbWVudCkgfHwgdHMuaXNXaXRoU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdHB1c2goc3RhdGVtZW50LnN0YXRlbWVudCk7XG5cdFx0fSBlbHNlIGlmICh0cy5pc1N3aXRjaFN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGNsYXVzZSBvZiBzdGF0ZW1lbnQuY2FzZUJsb2NrLmNsYXVzZXMpIHtcblx0XHRcdFx0YmxvY2tzLnB1c2goWyAuLi5jbGF1c2Uuc3RhdGVtZW50cyBdKTtcblx0XHRcdH1cblx0XHR9IGVsc2UgaWYgKHRzLmlzTGFiZWxlZFN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRjb25zdCBuZXN0ZWQgPSB0aGlzLm5lc3RlZFNjb3BlQmxvY2tzKHN0YXRlbWVudC5zdGF0ZW1lbnQpO1xuXHRcdFx0Zm9yIChjb25zdCBibG9jayBvZiBuZXN0ZWQpIHtcblx0XHRcdFx0YmxvY2tzLnB1c2goWyAuLi5ibG9jayBdKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gYmxvY2tzO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0aGUgZW5jbG9zaW5nIG1uZW1vbmljYSBzY29wZSBvZiBhbiBFRFMgY2FsbCBzaXRlIGJ5IHdhbGtpbmdcblx0ICogdXAgdGhlIHBhcmVudCBjaGFpbjogbmVhcmVzdCBkZWZpbmUoKS9sYXp5KCkgY2FsbCB3aG9zZSBoYW5kbGVyIGhvbGRzXG5cdCAqIHRoZSBub2RlLCBvciBuZWFyZXN0IEBkZWNvcmF0ZSgpLWVkIGNsYXNzIGRlY2xhcmF0aW9uLiBCZXN0IGVmZm9ydCDigJRcblx0ICogcmV0dXJucyB1bmRlZmluZWQgZm9yIGNhbGxzIG91dHNpZGUgYW55IHR5cGUgc2NvcGUgKG1vZHVsZSB0b3AgbGV2ZWwpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRURTU2NvcGUgKG5vZGU6IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbm9kZS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGNvbnN0IHNjb3BlUGF0aCA9IHRoaXMuZWRzU2NvcGVCeU5vZGUuZ2V0KGN1cnJlbnQpO1xuXHRcdFx0aWYgKHNjb3BlUGF0aCkge1xuXHRcdFx0XHRyZXR1cm4gc2NvcGVQYXRoO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSB3cmFwIHNpdGUncyBpbnN0YW5jZS9jb250ZXh0IGFyZ3VtZW50IHRvIGEgbW5lbW9uaWNhIHR5cGVcblx0ICogcGF0aCDigJQgdGhlIGZpcmUtYW5kLWZvcmdldC13cmFwcGVyIGF0dHJpYnV0aW9uIGZhbGxiYWNrIHdoZW4gdGhlIGNhbGxcblx0ICogc2l0cyBvdXRzaWRlIGFueSBkZWZpbmUoKS9sYXp5KCkgaGFuZGxlcjogYSB0cmFja2VkIGFzc2lnbm1lbnRcblx0ICogKGBjb25zdCBob2xkZXIgPSBuZXcgSG9sZGVyKC4uLilgKSwgZWxzZSB0aGUgcm9vdCBpZGVudGlmaWVyJ3Ncblx0ICogKHByb3BlcnR5LWFjY2VzcyByb290cyBpbmNsdWRlZCkgcGFyYW1ldGVyIGFubm90YXRpb24gcmVzb2x2ZWRcblx0ICogdGhyb3VnaCB0aGUgZ3JhcGggbGF3LiBBbWJpZ3VpdHkgb3IgYWJzZW5jZSBzdGF5cyBzaWxlbnQg4oCUIHRoaXMgaXMgYVxuXHQgKiBtZXRhZGF0YSBoZXVyaXN0aWMsIG5vdCB0aGUgaWRlbnRpdHktbGF3IHN1cmZhY2UuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVXcmFwSW5zdGFuY2VUeXBlUGF0aCAoYXJnOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBmcm9tQmluZGluZyA9IChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQgPT4ge1xuXHRcdFx0Y29uc3QgbWFwcGVkID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0XHRpZiAobWFwcGVkKSB7XG5cdFx0XHRcdHJldHVybiBtYXBwZWQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBhbm5vdGF0aW9uVHlwZSA9IHRoaXMucmVzb2x2ZVBhcmFtZXRlckFubm90YXRpb25UeXBlUGF0aChuYW1lLCBmcm9tKSA/P1xuXHRcdFx0XHQvLyBGMjAgY2hlYXAgdGllcjogdGhlIGlkZW50aWZpZXIgaXMgYm91bmQgdG8gYSBsZXQvdmFyL2NvbnN0XG5cdFx0XHRcdC8vIHdpdGggYW4gRVhQTElDSVQgdHlwZSBhbm5vdGF0aW9uIOKAlCByZXNvbHZlIHRoZSBhbm5vdGF0aW9uXG5cdFx0XHRcdC8vIHRocm91Z2ggdGhlIGdyYXBoIGxhdy4gTm8gZmxvdy1zZW5zaXRpdmUgYXNzaWdubWVudFxuXHRcdFx0XHQvLyB0cmFja2luZzogYW4gVU5BTk5PVEFURUQgbGV0IHN0aWxsIGJ1Y2tldHMgdW5rbm93blxuXHRcdFx0XHR0aGlzLnJlc29sdmVWYXJpYWJsZUFubm90YXRpb25UeXBlUGF0aChuYW1lLCBmcm9tKTtcblx0XHRcdHJldHVybiBhbm5vdGF0aW9uVHlwZTtcblx0XHR9O1xuXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihhcmcpKSB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSBmcm9tQmluZGluZyhhcmcudGV4dCwgYXJnKTtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcmcpKSB7XG5cdFx0XHRjb25zdCByb290ID0gdGhpcy5nZXRSb290SWRlbnRpZmllcihhcmcpO1xuXHRcdFx0aWYgKHJvb3QpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0ID0gZnJvbUJpbmRpbmcocm9vdC50ZXh0LCBhcmcpO1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEYyNDogcmVzb2x2ZSBhIGJhcmUtaWRlbnRpZmllciBhbm5vdGF0aW9uIHRvIGEgZ3JhcGggZnVsbFBhdGguIFRoZVxuXHQgKiBhbm5vdGF0aW9uIG1heSBuYW1lIHRoZSB0eXBlIGRpcmVjdGx5IChgTGVkZ2VyVXBkYXRlYCkgb3IgY2Fycnlcblx0ICogdGhlIEdFTkVSQVRFRCBpbnN0YW5jZSBhbGlhcyBvZiBhIG5lc3RlZCB0eXBlXG5cdCAqIChgVXBkYXRlUGF5X1NvbWVUZXJtaW5hbGAsIGltcG9ydGVkIGZyb20gdGhlIGdlbmVyYXRlZCB0eXBlcyBmaWxlXG5cdCAqIHZpYSB0c2NvbmZpZyBwYXRocykg4oCUIG5vdCBhIGdyYXBoIG5vZGUgTkFNRS4gVGhlIG5hbWUgaXMgdHJpZWRcblx0ICogYXMtaXMgZmlyc3QsIHRoZW4gaXRzIHVuZGVyc2NvcmXihpJkb3R0ZWQgZm9ybSAodGhlIGdlbmVyYXRlZCBhbGlhc1xuXHQgKiBuYW1pbmcgbGF3OyB0aGUgc2FtZSBtYXBwaW5nIHNjb3Blcy5qc29uIHVzZXMgZm9yIGFubm90YXRpb25zKS5cblx0ICogQW1iaWd1aXR5IGFuZCBhYnNlbmNlIHlpZWxkIHVuZGVmaW5lZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUFubm90YXRpb25UeXBlUGF0aCAobmFtZTogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBkaXJlY3QgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKG5hbWUpO1xuXHRcdGlmIChkaXJlY3Quc3RhdHVzID09PSAndW5pcXVlJykge1xuXHRcdFx0Y29uc3QgcmVzdWx0ID0gZGlyZWN0Lm5vZGUuZnVsbFBhdGg7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH1cblx0XHRpZiAoIW5hbWUuaW5jbHVkZXMoJ18nKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgYWxpYXNlZCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUobmFtZS5yZXBsYWNlKC9fL2csICcuJykpO1xuXHRcdGlmIChhbGlhc2VkLnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGFsaWFzZWQubm9kZS5mdWxsUGF0aDtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGJhcmUtaWRlbnRpZmllciB0eXBlIGFubm90YXRpb24gb2YgdGhlIG5lYXJlc3QgZW5jbG9zaW5nXG5cdCAqIGZ1bmN0aW9uJ3MgcGFyYW1ldGVyIHRocm91Z2ggdGhlIG1uZW1vbmljYS1ncmFwaCB0aWVycyAodmFsdWUgc2NvcGUsXG5cdCAqIGltcG9ydHMsIHJvb3RzLCBwcm9ncmFtLXdpZGUtdW5pcXVlKS4gTm9uLWlkZW50aWZpZXIgYW5kIGdlbmVyaWNcblx0ICogYW5ub3RhdGlvbnMgYXJlIG5vdCBncmFwaCByZWZlcmVuY2VzOyBhbWJpZ3VpdHkgYW5kIGFic2VuY2UgeWllbGRcblx0ICogdW5kZWZpbmVkLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlUGFyYW1ldGVyQW5ub3RhdGlvblR5cGVQYXRoIChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gZnJvbS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc0Z1bmN0aW9uTGlrZShjdXJyZW50KSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGN1cnJlbnQucGFyYW1ldGVycyA/PyBbXSkge1xuXHRcdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpIHx8IHBhcmFtLm5hbWUudGV4dCAhPT0gbmFtZSB8fCAhcGFyYW0udHlwZSB8fFxuXHRcdFx0XHRcdFx0IXRzLmlzVHlwZVJlZmVyZW5jZU5vZGUocGFyYW0udHlwZSkgfHxcblx0XHRcdFx0XHRcdCF0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSkgfHxcblx0XHRcdFx0XHRcdChwYXJhbS50eXBlLnR5cGVBcmd1bWVudHM/Lmxlbmd0aCA/PyAwKSA+IDApIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCByZXNvbHZlZCA9IHRoaXMucmVzb2x2ZUFubm90YXRpb25UeXBlUGF0aChwYXJhbS50eXBlLnR5cGVOYW1lLnRleHQpO1xuXHRcdFx0XHRcdGlmIChyZXNvbHZlZCkge1xuXHRcdFx0XHRcdFx0cmV0dXJuIHJlc29sdmVkO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEYyMCBjaGVhcCB0aWVyOiB0aGUgd3JhcCBhcmd1bWVudCBpcyBhbiBpZGVudGlmaWVyIGRlY2xhcmVkIHdpdGggYW5cblx0ICogRVhQTElDSVQgdHlwZSBhbm5vdGF0aW9uIChgbGV0IHVwZGF0ZUNvbW1pdHRlZDogTGVkZ2VyVXBkYXRlO2Bcblx0ICogYXNzaWduZWQgbGF0ZXIgaW4gYSBmbG93IHRoZSBhbmFseXplciBkb2VzIG5vdCB0cmFjaykuIFRoZVxuXHQgKiBhbm5vdGF0aW9uIHJlc29sdmVzIHRocm91Z2ggdGhlIHNhbWUgZ3JhcGggdGllcnMgYXMgcGFyYW1ldGVyXG5cdCAqIGFubm90YXRpb25zLiBEZWxpYmVyYXRlbHkgTk9UIGZsb3ctc2Vuc2l0aXZlOiBhbiBVTkFOTk9UQVRFRFxuXHQgKiBsZXQvdmFyIHN0aWxsIGJ1Y2tldHMgdW5rbm93biwgYW5kIGEgY29uc3Qgd2l0aCBhbiBhbmFseXphYmxlXG5cdCAqIGluaXRpYWxpemVyIHN0YXlzIHRoZSByZWNvbW1lbmRlZCBkaXNjaXBsaW5lLiBUaGUgbG9va3VwIHdhbGtzIHRoZVxuXHQgKiBlbmNsb3Npbmcgc3RhdGVtZW50IGNvbnRhaW5lcnMgaW5uZXJtb3N0LW91dCwgc28gYSBzaGFkb3dpbmcgaW5uZXJcblx0ICogZGVjbGFyYXRpb24gd2lucy5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVZhcmlhYmxlQW5ub3RhdGlvblR5cGVQYXRoIChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gZnJvbTtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0Y29uc3Qgc3RhdGVtZW50czogdHMuTm9kZUFycmF5PHRzLlN0YXRlbWVudD4gfCB1bmRlZmluZWQgPVxuXHRcdFx0XHR0cy5pc0Jsb2NrKGN1cnJlbnQpIHx8IHRzLmlzTW9kdWxlQmxvY2soY3VycmVudCkgfHwgdHMuaXNTb3VyY2VGaWxlKGN1cnJlbnQpXG5cdFx0XHRcdFx0PyBjdXJyZW50LnN0YXRlbWVudHNcblx0XHRcdFx0XHQ6IHRzLmlzQ2FzZUNsYXVzZShjdXJyZW50KSB8fCB0cy5pc0RlZmF1bHRDbGF1c2UoY3VycmVudClcblx0XHRcdFx0XHRcdD8gY3VycmVudC5zdGF0ZW1lbnRzXG5cdFx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblx0XHRcdGlmIChzdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdGNvbnN0IHJlc29sdmVkID0gdGhpcy5maW5kQW5ub3RhdGVkVmFyaWFibGVUeXBlUGF0aChzdGF0ZW1lbnRzLCBuYW1lKTtcblx0XHRcdFx0aWYgKHJlc29sdmVkKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHJlc29sdmVkO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmlyc3QgdmFyaWFibGUgZGVjbGFyYXRpb24gY2FycnlpbmcgYW4gZXhwbGljaXQgYmFyZS1pZGVudGlmaWVyIHR5cGVcblx0ICogYW5ub3RhdGlvbiBmb3IgYG5hbWVgIGluIHRoZSBnaXZlbiBzdGF0ZW1lbnQgbGlzdCwgcmVzb2x2ZWQgdGhyb3VnaFxuXHQgKiB0aGUgZ3JhcGggbGF3LlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kQW5ub3RhdGVkVmFyaWFibGVUeXBlUGF0aCAoXG5cdFx0c3RhdGVtZW50czogcmVhZG9ubHkgdHMuU3RhdGVtZW50W10sXG5cdFx0bmFtZTogc3RyaW5nXG5cdCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc3RhdGVtZW50cykge1xuXHRcdFx0aWYgKCF0cy5pc1ZhcmlhYmxlU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGRlY2xhcmF0aW9uIG9mIHN0YXRlbWVudC5kZWNsYXJhdGlvbkxpc3QuZGVjbGFyYXRpb25zKSB7XG5cdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGRlY2xhcmF0aW9uLm5hbWUpIHx8IGRlY2xhcmF0aW9uLm5hbWUudGV4dCAhPT0gbmFtZSB8fFxuXHRcdFx0XHRcdCFkZWNsYXJhdGlvbi50eXBlIHx8XG5cdFx0XHRcdFx0IXRzLmlzVHlwZVJlZmVyZW5jZU5vZGUoZGVjbGFyYXRpb24udHlwZSkgfHxcblx0XHRcdFx0XHQhdHMuaXNJZGVudGlmaWVyKGRlY2xhcmF0aW9uLnR5cGUudHlwZU5hbWUpIHx8XG5cdFx0XHRcdFx0KGRlY2xhcmF0aW9uLnR5cGUudHlwZUFyZ3VtZW50cz8ubGVuZ3RoID8/IDApID4gMCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IHJlc29sdmVkID0gdGhpcy5yZXNvbHZlQW5ub3RhdGlvblR5cGVQYXRoKGRlY2xhcmF0aW9uLnR5cGUudHlwZU5hbWUudGV4dCk7XG5cdFx0XHRcdGlmIChyZXNvbHZlZCkge1xuXHRcdFx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSB3cmFwKCkgYXJndW1lbnQgdG8gaXRzIGZ1bmN0aW9uIG5vZGUgd2l0aG91dCB0aGUgdHlwZVxuXHQgKiBjaGVja2VyOiBkaXJlY3QgZnVuY3Rpb24gZXhwcmVzc2lvbnMvYXJyb3dzLCBvciBzYW1lLWZpbGUgYmluZGluZ3Ncblx0ICogKGBjb25zdCBmbiA9ICgpID0+IC4uLmAsIGBmdW5jdGlvbiBmbigpIC4uLmApLiBCZXN0IGVmZm9ydCDigJQgbWV0aG9kXG5cdCAqIHJlZmVyZW5jZXMsIC5iaW5kKCkgcHJvZHVjdHMgYW5kIGNyb3NzLWZpbGUgaWRlbnRpZmllcnMgc3RheVxuXHQgKiB1bnJlc29sdmVkOyB0aGUgY2FsbHNpdGUgZW50cnkgaXRzZWxmIGlzIHN0aWxsIHJlY29yZGVkLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRnVuY3Rpb25Bcmd1bWVudCAoXG5cdFx0YXJnOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGVcblx0KTogdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGlmICghYXJnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGFyZykgfHwgdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0cmV0dXJuIGFyZztcblx0XHR9XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihhcmcpKSB7XG5cdFx0XHRjb25zdCBrZXkgPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfSMke2FyZy50ZXh0fWA7XG5cdFx0XHRjb25zdCBib3VuZCA9IHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5nZXQoa2V5KTtcblx0XHRcdGlmIChib3VuZCkge1xuXHRcdFx0XHRyZXR1cm4gYm91bmQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogQW5hbHlzZSBhIHdyYXBwZWQgZnVuY3Rpb24ncyBib2R5IGZvciBndWFyYW50ZWVkIHJ1bnRpbWUgcGF0aHM6XG5cdCAqIGRpdmUgd3JhcHMgcmV0dXJuZWQgZnVuY3Rpb25zIGFzIHdlbGwgKHJlY3Vyc2l2ZWx5KSwgc28gZWFjaFxuXHQgKiBmdW5jdGlvbi12YWx1ZWQgcmV0dXJuIGlzIGEgbmVzdGVkIHdyYXAgc2l0ZSwgYW5kIGVhY2ggYG5ldyBUeXBlKClgXG5cdCAqIGluc2lkZSB0aGUgYm9keSBtZWFucyB0aGUgcGF0aCBoaXRzIHRoYXQgdHlwZSdzIGNvbnN0cnVjdG9yICh3aGljaFxuXHQgKiBhdHRhY2hIb29rcyB3cmFwcyB0b28pLiBCb3RoIGZhY3RzIGFyZSAxMDAlIGVuc3VyZWQsIHNvIHRoZXkgYXJlXG5cdCAqIHJlY29yZGVkIEFvVC4gTmVzdGVkIGZ1bmN0aW9uIGJvZGllcyBhcmUgTk9UIHdhbGtlZCBoZXJlIOKAlCB0aGV5XG5cdCAqIGJlbG9uZyB0byB0aGVpciBvd24gd3JhcCBhbmFseXNpcywgcmVhY2hlZCB2aWEgdGhlIHJldHVybiBjaGFpbi5cblx0ICogRGVwdGgtY2FwcGVkIGFuZCBjeWNsZS1ndWFyZGVkLlxuXHQgKi9cblx0cHJpdmF0ZSBhbmFseXplV3JhcHBlZEJvZHkgKFxuXHRcdGZuOiB0cy5GdW5jdGlvbkxpa2VEZWNsYXJhdGlvbixcblx0XHR2aWFMb2NhdGlvbjogc3RyaW5nLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0ZGVwdGg6IG51bWJlcixcblx0XHR2aXNpdGVkOiBTZXQ8dHMuTm9kZT4sXG5cdFx0Y3JlYXRlc1R5cGVzOiBTZXQ8c3RyaW5nPixcblx0XHRmYWxsYmFja1Njb3BlPzogc3RyaW5nXG5cdCk6IHZvaWQge1xuXHRcdGlmIChkZXB0aCA+IDUgfHwgdmlzaXRlZC5oYXMoZm4pIHx8ICFmbi5ib2R5KSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHZpc2l0ZWQuYWRkKGZuKTtcblxuXHRcdC8vIEFycm93IHdpdGggZXhwcmVzc2lvbiBib2R5OiBpbXBsaWNpdCByZXR1cm5cblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGZuKSAmJiAhdHMuaXNCbG9jayhmbi5ib2R5KSkge1xuXHRcdFx0dGhpcy5yZWNvcmRXcmFwcGVkUmV0dXJuKGZuLmJvZHksIHZpYUxvY2F0aW9uLCBzb3VyY2VGaWxlLCBkZXB0aCwgdmlzaXRlZCwgZmFsbGJhY2tTY29wZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3Qgd2FsayA9IChub2RlOiB0cy5Ob2RlKTogdm9pZCA9PiB7XG5cdFx0XHRpZiAobm9kZSAhPT0gZm4uYm9keSAmJiAoXG5cdFx0XHRcdHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKG5vZGUpIHx8XG5cdFx0XHRcdHRzLmlzQXJyb3dGdW5jdGlvbihub2RlKSB8fFxuXHRcdFx0XHR0cy5pc0Z1bmN0aW9uRGVjbGFyYXRpb24obm9kZSkgfHxcblx0XHRcdFx0dHMuaXNNZXRob2REZWNsYXJhdGlvbihub2RlKVxuXHRcdFx0KSkge1xuXHRcdFx0XHQvLyBuZXN0ZWQgZnVuY3Rpb24gYm9kaWVzIGFyZSBhbmFseXNlZCB0aHJvdWdoIHRoZSByZXR1cm4gY2hhaW5cblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0XHR0aGlzLnJlY29yZFdyYXBwZWRSZXR1cm4obm9kZS5leHByZXNzaW9uLCB2aWFMb2NhdGlvbiwgc291cmNlRmlsZSwgZGVwdGgsIHZpc2l0ZWQsIGZhbGxiYWNrU2NvcGUpO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzTmV3RXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0XHRjb25zdCBjcmVhdGVkID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKSB8fFxuXHRcdFx0XHRcdCh0cy5pc0lkZW50aWZpZXIobm9kZS5leHByZXNzaW9uKSAmJiB0aGlzLmRlZmluaXRpb25zLmhhcyhub2RlLmV4cHJlc3Npb24udGV4dClcblx0XHRcdFx0XHRcdD8gbm9kZS5leHByZXNzaW9uLnRleHRcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkKTtcblx0XHRcdFx0aWYgKGNyZWF0ZWQpIHtcblx0XHRcdFx0XHRjcmVhdGVzVHlwZXMuYWRkKGNyZWF0ZWQpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0XHRjb25zdCBuZXN0ZWROYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKTtcblx0XHRcdFx0aWYgKFxuXHRcdFx0XHRcdG5lc3RlZE5hbWUgPT09ICd3cmFwJyB8fFxuXHRcdFx0XHRcdG5lc3RlZE5hbWUgPT09ICd3cmFwQ29uc3RydWN0b3JBcmcnIHx8XG5cdFx0XHRcdFx0bmVzdGVkTmFtZSA9PT0gJ3VwZ3JhZGVDb25zdHJ1Y3RvckFyZycgfHxcblx0XHRcdFx0XHRuZXN0ZWROYW1lID09PSAnd3JhcEluc3RhbmNlTWV0aG9kcydcblx0XHRcdFx0KSB7XG5cdFx0XHRcdFx0Ly8gdGhlIG5lc3RlZCBjYWxsIG1heSBhbHJlYWR5IGJlIGNvbGxlY3RlZCAodmlzaXRlZFxuXHRcdFx0XHRcdC8vIGJlZm9yZSB0aGlzIG91dGVyIHdyYXAgc2l0ZSkg4oCUIGJhY2stcGF0Y2ggaXRzIGVudHJ5LFxuXHRcdFx0XHRcdC8vIG90aGVyd2lzZSBsZWF2ZSB0aGUgbGluayAod2l0aCB0aGlzIHNpdGUncyBzY29wZSkgZm9yXG5cdFx0XHRcdFx0Ly8gY29sbGVjdEVEUyB0byBwaWNrIHVwXG5cdFx0XHRcdFx0Y29uc3QgbmVzdGVkRW50cnkgPSB0aGlzLndyYXBFbnRyeUJ5Tm9kZS5nZXQobm9kZSk7XG5cdFx0XHRcdFx0aWYgKG5lc3RlZEVudHJ5KSB7XG5cdFx0XHRcdFx0XHRuZXN0ZWRFbnRyeS52aWEgPSB2aWFMb2NhdGlvbjtcblx0XHRcdFx0XHRcdGlmIChuZXN0ZWRFbnRyeS5zY29wZSA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdFx0XHRcdG5lc3RlZEVudHJ5LnNjb3BlID0gZmFsbGJhY2tTY29wZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0dGhpcy5uZXN0ZWRXcmFwVmlhLnNldChub2RlLCB7IHZpYSA6IHZpYUxvY2F0aW9uLCBzY29wZSA6IGZhbGxiYWNrU2NvcGUgfSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgd2Fsayk7XG5cdFx0fTtcblx0XHR3YWxrKGZuLmJvZHkpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBvbmUgZnVuY3Rpb24tdmFsdWVkIHJldHVybiBvZiBhIHdyYXBwZWQgYm9keSBhcyBhIG5lc3RlZCB3cmFwXG5cdCAqIHNpdGUgKGB2aWFgID0gdGhlIHNpdGUgd2hvc2Ugd3JhcHBpbmcgY2F1c2VkIGl0KSBhbmQgcmVjdXJzZSBpbnRvXG5cdCAqIGl0cyBvd24gcmV0dXJucy4gUmV0dXJucyB0aHJvdWdoIGlkZW50aWZpZXJzIHJlc29sdmUgdGhyb3VnaCB0aGVcblx0ICogc2FtZS1maWxlIGJpbmRpbmdzIHRhYmxlOyB1bnJlc29sdmFibGUgcmV0dXJucyBhcmUgc2ltcGx5IHNraXBwZWQuXG5cdCAqIEEgcmV0dXJuIGRlY2xhcmVkIG91dHNpZGUgYW55IHR5cGUgc2NvcGUgaW5oZXJpdHMgdGhlIGNhdXNpbmcgd3JhcFxuXHQgKiBzaXRlJ3Mgc2NvcGUgYXR0cmlidXRpb24gKHRoZSBnZW5lcmF0aW9uIGNoYWluIGlzIHRoZSBvbmx5IGhvbGRlcikuXG5cdCAqL1xuXHRwcml2YXRlIHJlY29yZFdyYXBwZWRSZXR1cm4gKFxuXHRcdGV4cHI6IHRzLkV4cHJlc3Npb24sXG5cdFx0dmlhTG9jYXRpb246IHN0cmluZyxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdGRlcHRoOiBudW1iZXIsXG5cdFx0dmlzaXRlZDogU2V0PHRzLk5vZGU+LFxuXHRcdGZhbGxiYWNrU2NvcGU/OiBzdHJpbmdcblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgcmV0dXJuZWQgPSB0aGlzLnJlc29sdmVGdW5jdGlvbkFyZ3VtZW50KGV4cHIsIHNvdXJjZUZpbGUpO1xuXHRcdGlmICghcmV0dXJuZWQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdHJldHVybmVkLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSByZXR1cm5lZC5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cdFx0Y29uc3Qgc2NvcGUgPSB0aGlzLnJlc29sdmVFRFNTY29wZShyZXR1cm5lZCkgPz8gZmFsbGJhY2tTY29wZTtcblx0XHRjb25zdCBlbnRyeSA9IHRoaXMuYWRkRURTKHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kIDogJ3dyYXAnLFxuXHRcdFx0Y29kZSxcblx0XHRcdHNjb3BlLFxuXHRcdFx0dmlhICA6IHZpYUxvY2F0aW9uLFxuXHRcdFx0Ly8gZGl2ZSB3cmFwcyByZXR1cm5lZCBmdW5jdGlvbnMgdGhyb3VnaCB0aGUgc2FtZSB3cmFwIG1hY2hpbmVyeVxuXHRcdFx0Zm4gICA6ICd3cmFwJyxcblx0XHR9KTtcblx0XHQvLyB0aGUgcmV0dXJuZWQgZnVuY3Rpb24ncyBvd24gcmV0dXJucyBhcmUgd3JhcHBlZCBpbiB0dXJuOyBgdmlhYFxuXHRcdC8vIGNoYWlucyB0byB0aGlzIG5lc3RlZCBlbnRyeSdzIGxvY2F0aW9uXG5cdFx0Y29uc3QgbmVzdGVkQ3JlYXRlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdHRoaXMuYW5hbHl6ZVdyYXBwZWRCb2R5KHJldHVybmVkLCBsb2NhdGlvbiwgc291cmNlRmlsZSwgZGVwdGggKyAxLCB2aXNpdGVkLCBuZXN0ZWRDcmVhdGVzLCBzY29wZSk7XG5cdFx0aWYgKG5lc3RlZENyZWF0ZXMuc2l6ZSA+IDApIHtcblx0XHRcdGVudHJ5LmNyZWF0ZXNUeXBlcyA9IEFycmF5LmZyb20obmVzdGVkQ3JlYXRlcyk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhbiBFRFMgdXNhZ2UgdG8gdGhlIGNvbGxlY3Rpb25cblx0ICogUmV0dXJucyB0aGUgc3RvcmVkIGVudHJ5ICh0aGUgZXhpc3Rpbmcgb25lIHdoZW4gdGhpcyBpcyBhIGR1cGxpY2F0ZSksXG5cdCAqIHNvIGNhbGxlcnMgY2FuIGVucmljaCBpdCBhZnRlciBuZXN0ZWQgYm9keSBhbmFseXNpcy5cblx0ICovXG5cdHByaXZhdGUgYWRkRURTICh0eXBlUGF0aDogc3RyaW5nLCBpbmZvOiBFRFNJbmZvKTogRURTSW5mbyB7XG5cdFx0aWYgKCF0aGlzLmVkc1VzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLmVkc1VzYWdlcy5zZXQodHlwZVBhdGgsIFtdKTtcblx0XHR9XG5cblx0XHRjb25zdCBleGlzdGluZyA9IHRoaXMuZWRzVXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGR1cGxpY2F0ZSA9IGV4aXN0aW5nLmZpbmQoZSA9PiB7XG5cdFx0XHRyZXR1cm4gZS5sb2NhdGlvbiA9PT0gaW5mby5sb2NhdGlvbiAmJlxuXHRcdFx0XHRlLmtpbmQgPT09IGluZm8ua2luZCAmJlxuXHRcdFx0XHRlLmNvZGUgPT09IGluZm8uY29kZTtcblx0XHR9KTtcblxuXHRcdGlmIChkdXBsaWNhdGUpIHtcblx0XHRcdHJldHVybiBkdXBsaWNhdGU7XG5cdFx0fVxuXHRcdGV4aXN0aW5nLnB1c2goaW5mbyk7XG5cdFx0cmV0dXJuIGluZm87XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBuYXRpdmUgZmxvdyBwYXR0ZXJucyAoaW5zdGFuY2UgdXNhZ2UgYWZ0ZXIgY3JlYXRpb24pXG5cdCAqIFBoYXNlIDE6IHByb3BlcnR5IGFjY2VzcywgbWV0aG9kIGNhbGxzLCBhcmd1bWVudHMsIHJldHVybiwgZGVzdHJ1Y3R1cmluZywgZXRjLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0RmxvdyAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIFByb3BlcnR5IHJlYWQ6IHVzZXIubmFtZSBvciB1c2VyPy5uYW1lXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93UHJvcGVydHlBY2Nlc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRWxlbWVudCBhY2Nlc3M6IHVzZXJbJ25hbWUnXVxuXHRcdGlmICh0cy5pc0VsZW1lbnRBY2Nlc3NFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93RWxlbWVudEFjY2Vzcyhub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSB3cml0ZTogdXNlci5uYW1lID0gdmFsdWVcblx0XHRpZiAodHMuaXNCaW5hcnlFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkVxdWFsc1Rva2VuKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93QXNzaWdubWVudChub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBNZXRob2QgY2FsbDogdXNlci52YWxpZGF0ZSgpICBBTkQgIGFyZ3VtZW50IHBhc3Npbmc6IHByb2Nlc3NVc2VyKHVzZXIpXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93TWV0aG9kQ2FsbChub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dBcmd1bWVudFBhc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRGVzdHJ1Y3R1cmUgcmVhZDogY29uc3QgeyBuYW1lIH0gPSB1c2VyXG5cdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLmluaXRpYWxpemVyKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93RGVzdHJ1Y3R1cmUobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUmV0dXJuIGluc3RhbmNlOiByZXR1cm4gdXNlclxuXHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dSZXR1cm4obm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gU3ByZWFkOiB7IC4uLnVzZXIgfVxuXHRcdGlmICh0cy5pc1NwcmVhZEVsZW1lbnQobm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dTcHJlYWQobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgcHJvcGVydHkgYWNjZXNzIGZsb3cgKHJlYWQgb3IgY29uZGl0aW9uYWwpXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93UHJvcGVydHlBY2Nlc3MgKG5vZGU6IHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHByb3BOYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0Ly8gU2tpcCBpZiB0aGlzIGlzIGEgdHlwZSBjb25zdHJ1Y3RvciBhY2Nlc3MgKGUuZy4sIFVzZXJUeXBlLmRlZmluZSlcblx0XHRpZiAocHJvcE5hbWUgPT09ICdkZWZpbmUnIHx8IHByb3BOYW1lID09PSAnbGF6eScpIHsgcmV0dXJuOyB9XG5cblx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgICAgOiAncHJvcGVydHlSZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHRwcm9wZXJ0eU5hbWUgOiBwcm9wTmFtZSxcblx0XHRcdHRhcmdldFR5cGUgICA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGVsZW1lbnQgYWNjZXNzIGZsb3c6IHVzZXJbJ25hbWUnXVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0VsZW1lbnRBY2Nlc3MgKG5vZGU6IHRzLkVsZW1lbnRBY2Nlc3NFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3Qgb2JqZWN0VHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0aWYgKCFvYmplY3RUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0dGhpcy5hZGRGbG93KG9iamVjdFR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICA6ICdlbGVtZW50QWNjZXNzJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogb2JqZWN0VHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgYXNzaWdubWVudCBmbG93OiB1c2VyLm5hbWUgPSB2YWx1ZSBvciB1c2VyID0gb3RoZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dBc3NpZ25tZW50IChub2RlOiB0cy5CaW5hcnlFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gUHJvcGVydHkgd3JpdGU6IHVzZXIubmFtZSA9IHZhbHVlXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUubGVmdCkpIHtcblx0XHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmxlZnQuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRcdGNvbnN0IHByb3BOYW1lID0gbm9kZS5sZWZ0Lm5hbWUudGV4dDtcblx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0KTtcblx0XHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgICAgOiAncHJvcGVydHlXcml0ZScsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHByb3BlcnR5TmFtZSA6IHByb3BOYW1lLFxuXHRcdFx0XHR0YXJnZXRUeXBlICAgOiBvYmplY3RUeXBlXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBWYXJpYWJsZSByZWFzc2lnbm1lbnQ6IHVzZXIgPSBvdGhlclxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIobm9kZS5sZWZ0KSkge1xuXHRcdFx0Y29uc3QgdmFyTmFtZSA9IG5vZGUubGVmdC50ZXh0O1xuXHRcdFx0Y29uc3QgbWFwcGVkVHlwZSA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KHZhck5hbWUpO1xuXHRcdFx0aWYgKCFtYXBwZWRUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdCk7XG5cdFx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0XHR0aGlzLmFkZEZsb3cobWFwcGVkVHlwZSwge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCAgICAgICA6ICdyZWFzc2lnbm1lbnQnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHR0YXJnZXRUeXBlIDogbWFwcGVkVHlwZVxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgbWV0aG9kIGNhbGwgZmxvdzogdXNlci52YWxpZGF0ZSgpXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93TWV0aG9kQ2FsbCAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbikpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IG1ldGhvZE5hbWUgPSBub2RlLmV4cHJlc3Npb24ubmFtZS50ZXh0O1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIFNraXAgaWYgdGhpcyBpcyBhIHR5cGUgY29uc3RydWN0b3IgY2FsbCAoZS5nLiwgbmV3IFVzZXJUeXBlKCkpXG5cdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdkZWZpbmUnIHx8IG1ldGhvZE5hbWUgPT09ICdsYXp5JykgeyByZXR1cm47IH1cblxuXHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgICA6ICdtZXRob2RDYWxsJyxcblx0XHRcdGNvZGUsXG5cdFx0XHRwcm9wZXJ0eU5hbWUgOiBtZXRob2ROYW1lLFxuXHRcdFx0dGFyZ2V0VHlwZSAgIDogb2JqZWN0VHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgYXJndW1lbnQgcGFzc2luZyBmbG93OiBwcm9jZXNzVXNlcih1c2VyKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0FyZ3VtZW50UGFzcyAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRjb25zdCBhcmcgPSBub2RlLmFyZ3VtZW50c1sgaSBdO1xuXHRcdFx0Y29uc3QgYXJnVHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKGFyZyk7XG5cdFx0XHRpZiAoIWFyZ1R5cGUpIHsgY29udGludWU7IH1cblxuXHRcdFx0Y29uc3QgZnVuY05hbWUgPSB0aGlzLmdldEZ1bmN0aW9uTmFtZShub2RlLmV4cHJlc3Npb24pIHx8ICdhbm9ueW1vdXMnO1xuXHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHQpO1xuXHRcdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdFx0dGhpcy5hZGRGbG93KGFyZ1R5cGUsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAncGFzc0FzQXJnJyxcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSA6IGFyZ1R5cGUsXG5cdFx0XHRcdGNvbnRleHQgICAgOiBgYXJnICR7aX0gdG8gJHtmdW5jTmFtZX1gXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBkZXN0cnVjdHVyaW5nIGZsb3c6IGNvbnN0IHsgbmFtZSB9ID0gdXNlclxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0Rlc3RydWN0dXJlIChub2RlOiB0cy5WYXJpYWJsZURlY2xhcmF0aW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc09iamVjdEJpbmRpbmdQYXR0ZXJuKG5vZGUubmFtZSkpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBzb3VyY2VUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5pbml0aWFsaXplciEpO1xuXHRcdGlmICghc291cmNlVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIEV4dHJhY3QgZGVzdHJ1Y3R1cmVkIHByb3BlcnR5IG5hbWVzXG5cdFx0Y29uc3QgcHJvcHM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIG5vZGUubmFtZS5lbGVtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihlbGVtZW50Lm5hbWUpKSB7XG5cdFx0XHRcdHByb3BzLnB1c2goZWxlbWVudC5uYW1lLnRleHQpO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHRoaXMuYWRkRmxvdyhzb3VyY2VUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnZGVzdHJ1Y3R1cmVSZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogc291cmNlVHlwZSxcblx0XHRcdGNvbnRleHQgICAgOiBwcm9wcy5qb2luKCcsICcpXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCByZXR1cm4gZmxvdzogcmV0dXJuIHVzZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dSZXR1cm4gKG5vZGU6IHRzLlJldHVyblN0YXRlbWVudCwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHJldHVyblR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24hKTtcblx0XHRpZiAoIXJldHVyblR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHR0aGlzLmFkZEZsb3cocmV0dXJuVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ3JldHVybicsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHJldHVyblR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IHNwcmVhZCBmbG93OiB7IC4uLnVzZXIgfVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd1NwcmVhZCAobm9kZTogdHMuU3ByZWFkRWxlbWVudCwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHNwcmVhZFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghc3ByZWFkVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuYWRkRmxvdyhzcHJlYWRUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnc3ByZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogc3ByZWFkVHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgdHlwZSBmcm9tIGFuIGV4cHJlc3Npb24gKGlkZW50aWZpZXIsIHByb3BlcnR5IGFjY2VzcywgZXRjLilcblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUV4cHJlc3Npb25UeXBlIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBJZGVudGlmaWVyOiB1c2VyXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGV4cHIudGV4dCk7XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiB1c2VyLm5hbWUgKHJldHVybiBvYmplY3QgdHlwZSwgbm90IHByb3BlcnR5IHR5cGUpXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUoZXhwci5leHByZXNzaW9uKTtcblx0XHR9XG5cblx0XHQvLyBFbGVtZW50IGFjY2VzczogdXNlclsnbmFtZSddXG5cdFx0aWYgKHRzLmlzRWxlbWVudEFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdHJldHVybiB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShleHByLmV4cHJlc3Npb24pO1xuXHRcdH1cblxuXHRcdC8vIFRoaXMgZXhwcmVzc2lvbjogdGhpcyAoaWYgaW4gYSBtZXRob2QsIHdlIGNhbid0IHJlc29sdmUgd2l0aG91dCBtb3JlIGNvbnRleHQpXG5cdFx0aWYgKGV4cHIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhIGZsb3cgdXNhZ2UgdG8gdGhlIGNvbGxlY3Rpb25cblx0ICovXG5cdHByaXZhdGUgYWRkRmxvdyAodHlwZVBhdGg6IHN0cmluZywgaW5mbzogRmxvd0luZm8pOiB2b2lkIHtcblx0XHRpZiAoIXRoaXMuZmxvd1VzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLmZsb3dVc2FnZXMuc2V0KHR5cGVQYXRoLCBbXSk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZXhpc3RpbmcgPSB0aGlzLmZsb3dVc2FnZXMuZ2V0KHR5cGVQYXRoKSE7XG5cdFx0Y29uc3QgaXNEdXBsaWNhdGUgPSBleGlzdGluZy5zb21lKGUgPT4ge1xuXHRcdFx0cmV0dXJuIGUubG9jYXRpb24gPT09IGluZm8ubG9jYXRpb24gJiZcblx0XHRcdFx0ZS5raW5kID09PSBpbmZvLmtpbmQgJiZcblx0XHRcdFx0ZS5jb2RlID09PSBpbmZvLmNvZGU7XG5cdFx0fSk7XG5cblx0XHRpZiAoIWlzRHVwbGljYXRlKSB7XG5cdFx0XHRleGlzdGluZy5wdXNoKGluZm8pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdFx0KiBHZXQgdHlwZSBuYW1lIGZyb20gZXhwcmVzc2lvbiAoaWRlbnRpZmllciBvciBwcm9wZXJ0eSBhY2Nlc3MpXG5cdFx0XHQqL1xuXHRwcml2YXRlIGdldFR5cGVOYW1lRnJvbUV4cHJlc3Npb24gKGV4cHI6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdGNvbnN0IG5hbWUgPSBleHByLnRleHQ7XG5cdFx0XHQvLyBDaGVjayBpZiB0aGlzIGlkZW50aWZpZXIgaXMgYSB2YXJpYWJsZSBtYXBwZWQgdG8gYSB0eXBlIChlLmcuLCBmcm9tIGxvb2t1cClcblx0XHRcdGNvbnN0IG1hcHBlZFR5cGUgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChuYW1lKTtcblx0XHRcdGlmIChtYXBwZWRUeXBlKSB7XG5cdFx0XHRcdHJldHVybiBtYXBwZWRUeXBlO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIG5hbWU7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4oZXhwcik7XG5cdFx0XHRyZXR1cm4gY2hhaW4uam9pbignLicpO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cdFxuXHQvKipcblx0XHRcdCogUmVzb2x2ZSBmdWxsIHR5cGUgcGF0aCBmcm9tIHByb3BlcnR5IGFjY2Vzc1xuXHRcdFx0Ki9cblx0cHJpdmF0ZSByZXNvbHZlVHlwZVBhdGggKGV4cHI6IHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4oZXhwcik7XG5cdFx0aWYgKGNoYWluLmxlbmd0aCA9PT0gMCkgcmV0dXJuIHVuZGVmaW5lZDtcblx0XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBjaGFpbiBtYXRjaGVzIGEga25vd24gdHlwZVxuXHRcdGNvbnN0IGZ1bGxQYXRoID0gY2hhaW4uam9pbignLicpO1xuXHRcdGlmICh0aGlzLmRlZmluaXRpb25zLmhhcyhmdWxsUGF0aCkpIHtcblx0XHRcdHJldHVybiBmdWxsUGF0aDtcblx0XHR9XG5cdFxuXHRcdC8vIFRyeSBqdXN0IHRoZSBwcm9wZXJ0eSBuYW1lXG5cdFx0Y29uc3QgcHJvcE5hbWUgPSBjaGFpblsgY2hhaW4ubGVuZ3RoIC0gMSBdO1xuXHRcdGZvciAoY29uc3QgWyBwYXRoIF0gb2YgdGhpcy5kZWZpbml0aW9ucykge1xuXHRcdFx0aWYgKHBhdGguZW5kc1dpdGgoYC4ke3Byb3BOYW1lfWApIHx8IHBhdGggPT09IHByb3BOYW1lKSB7XG5cdFx0XHRcdHJldHVybiBwYXRoO1xuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0cmV0dXJuIGZ1bGxQYXRoO1xuXHR9XG5cdFxuXHQvKipcblx0XHRcdCAqIENoZWNrIGlmIGEgbmFtZSBsb29rcyBsaWtlIGEgdHlwZSAoc3RhcnRzIHdpdGggdXBwZXJjYXNlKVxuXHRcdFx0ICovXG5cdHByaXZhdGUgaXNMaWtlbHlUeXBlTmFtZSAobmFtZTogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0cmV0dXJuIG5hbWVbIDAgXSA+PSAnQScgJiYgbmFtZVsgMCBdIDw9ICdaJztcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQgKiBSZXNvbHZlIGEgY29uc3RydWN0b3IgcGFyYW1ldGVyIHR5cGUsIGV4cGFuZGluZyBpbmxpbmUgb2JqZWN0IGxpdGVyYWxzXG5cdFx0XHQgKiBhbmQgdHlwZSBhbGlhc2VzIHdoZXJlIHBvc3NpYmxlLlxuXHRcdFx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUNvbnN0cnVjdG9yUGFyYW1UeXBlICh0eXBlTm9kZTogdHMuVHlwZU5vZGUgfCB1bmRlZmluZWQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHlwZU5vZGUpIHJldHVybiB1bmRlZmluZWQ7XG5cblx0XHQvLyBEaXJlY3QgaW5saW5lIHR5cGUgbGl0ZXJhbDogeyBwcm9wOiB0eXBlIH1cblx0XHRpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUodHlwZU5vZGUpKSB7XG5cdFx0XHRjb25zdCBwcm9wczogc3RyaW5nW10gPSBbXTtcblx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIHR5cGVOb2RlLm1lbWJlcnMpIHtcblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdGNvbnN0IG9wdGlvbmFsID0gbWVtYmVyLnF1ZXN0aW9uVG9rZW4gPyAnPycgOiAnJztcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdHByb3BzLnB1c2goYCR7cHJvcE5hbWV9JHtvcHRpb25hbH06ICR7dHlwZX1gKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGB7ICR7cHJvcHMuam9pbignOyAnKX0gfWA7XG5cdFx0fVxuXG5cdFx0Ly8gVHlwZSByZWZlcmVuY2U6IHVzYWdlLCBVc2VyRGF0YSwgZXRjLiAtIHJlc29sdmUgaW1wb3J0LWF3YXJlIGFuZFxuXHRcdC8vIGV4cGFuZCB0aGUgcmVmZXJlbmNlZCBkZWNsYXJhdGlvbiB3aGVyZSBwb3NzaWJsZSAoRjEwKVxuXHRcdGlmICh0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHR5cGVOb2RlKSAmJiB0cy5pc0lkZW50aWZpZXIodHlwZU5vZGUudHlwZU5hbWUpKSB7XG5cdFx0XHRjb25zdCB0eXBlTmFtZSA9IHR5cGVOb2RlLnR5cGVOYW1lLnRleHQ7XG5cdFx0XHRjb25zdCBkZWNsID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbih0eXBlTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdGlmIChkZWNsKSB7XG5cdFx0XHRcdGNvbnN0IGV4cGFuZGVkID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKGRlY2wpO1xuXHRcdFx0XHRpZiAoZXhwYW5kZWQpIHJldHVybiBleHBhbmRlZDtcblx0XHRcdH1cblx0XHRcdC8vIG1uZW1vbmljYSBncmFwaCB0eXBlcyBrZWVwIHRoZWlyIHNpbXBsZSBuYW1lIOKAlCB0aGUgZ2VuZXJhdG9yXG5cdFx0XHQvLyB1cGdyYWRlcyB0aGVtIHRvIGZ1bGwtcGF0aCBpbnN0YW5jZSB0eXBlIG5hbWVzLiBSZXNvbHV0aW9uIGlzXG5cdFx0XHQvLyBwYXRoLWF3YXJlIChoYXJkLWZhaWwgbGF3KTogYW1iaWd1aXR5IGJldHdlZW4gcmVhbCBncmFwaCB0eXBlc1xuXHRcdFx0Ly8gcmVjb3JkcyBhIGZhdGFsIGVycm9yIGluc3RlYWQgb2Ygc2lsZW50bHkgcGlja2luZyBvbmUuXG5cdFx0XHRjb25zdCBncmFwaFJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUodHlwZU5hbWUpO1xuXHRcdFx0aWYgKGdyYXBoUmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdFx0Y29uc3Qgc2ltcGxlUmVzdWx0ID0gdHlwZU5hbWU7XG5cdFx0XHRcdHJldHVybiBzaW1wbGVSZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAoZ3JhcGhSZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0XHR0aGlzLnJlY29yZEdyYXBoUmVmZXJlbmNlRXJyb3IodHlwZU5hbWUsIHR5cGVOb2RlLCBncmFwaFJlc3VsdCk7XG5cdFx0XHRcdGNvbnN0IHVua25vd25HcmFwaFJlc3VsdCA9ICd1bmtub3duJztcblx0XHRcdFx0cmV0dXJuIHVua25vd25HcmFwaFJlc3VsdDtcblx0XHRcdH1cblx0XHRcdC8vIElmIG5vdCBhbiBvYmplY3QgdHlwZSBhbGlhcywgcmV0dXJuIHRoZSB0eXBlIG5hbWUgd2l0aCBhcmdzXG5cdFx0XHRpZiAodHlwZU5vZGUudHlwZUFyZ3VtZW50cyAmJiB0eXBlTm9kZS50eXBlQXJndW1lbnRzLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0aWYgKEtOT1dOX0dMT0JBTF9UWVBFUy5oYXModHlwZU5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgYXJncyA9IHR5cGVOb2RlLnR5cGVBcmd1bWVudHMubWFwKGFyZyA9PiB0aGlzLmluZmVyVHlwZShhcmcpKTtcblx0XHRcdFx0XHRyZXR1cm4gYCR7dHlwZU5hbWUgIH08JHsgIGFyZ3Muam9pbignLCAnKSAgfT5gO1xuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIGdlbmVyaWMgcmVmZXJlbmNlIHRvIGEgbm9uLWdsb2JhbCwgbm9uLWdyYXBoIHR5cGUgY2Fubm90IGJlXG5cdFx0XHRcdC8vIGVtaXR0ZWQgYmFyZSBpbnRvIHRoZSBnZW5lcmF0ZWQgZmlsZVxuXHRcdFx0XHR0aGlzLnJlY29yZFBsYWluVHlwZVJlZmVyZW5jZVNpdGUodHlwZU5hbWUsIHR5cGVOb2RlKTtcblx0XHRcdFx0Y29uc3QgdW5rbm93bkdlbmVyaWNSZXN1bHQgPSAndW5rbm93bic7XG5cdFx0XHRcdHJldHVybiB1bmtub3duR2VuZXJpY1Jlc3VsdDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGZhbGxiYWNrUmVzdWx0ID0gdGhpcy51bnJlc29sdmVkVHlwZVJlZmVyZW5jZUZhbGxiYWNrKHR5cGVOYW1lLCB0eXBlTm9kZSk7XG5cdFx0XHRyZXR1cm4gZmFsbGJhY2tSZXN1bHQ7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHRcdFx0ICogRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZyb20gYSBjbGFzcy1saWtlIG5vZGUuXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q2xhc3NDb25zdHJ1Y3RvclBhcmFtcyAoY2xhc3NMaWtlOiB0cy5DbGFzc0RlY2xhcmF0aW9uIHwgdHMuQ2xhc3NFeHByZXNzaW9uKTpcblx0XHRDb25zdHJ1Y3RvclBhcmFtSW5mb1tdIHtcblx0XHRjb25zdCBwYXJhbXM6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10gPSBbXTtcblxuXHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGNsYXNzTGlrZS5tZW1iZXJzKSB7XG5cdFx0XHRpZiAoIXRzLmlzQ29uc3RydWN0b3JEZWNsYXJhdGlvbihtZW1iZXIpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXG5cdFx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIG1lbWJlci5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRcdGlmICghcGFyYW0ubmFtZSB8fCAhdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpKSBjb250aW51ZTtcblx0XHRcdFx0aWYgKCFwYXJhbS50eXBlKSBjb250aW51ZTtcblxuXHRcdFx0XHRjb25zdCBwYXJhbU5hbWUgPSBwYXJhbS5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IGV4cGFuZGVkVHlwZSA9IHRoaXMucmVzb2x2ZUNvbnN0cnVjdG9yUGFyYW1UeXBlKHBhcmFtLnR5cGUpIHx8IHRoaXMuaW5mZXJUeXBlKHBhcmFtLnR5cGUpO1xuXG5cdFx0XHRcdHBhcmFtcy5wdXNoKHtcblx0XHRcdFx0XHRuYW1lICAgICA6IHBhcmFtTmFtZSxcblx0XHRcdFx0XHR0eXBlICAgICA6IGV4cGFuZGVkVHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6ICEhcGFyYW0ucXVlc3Rpb25Ub2tlbiB8fCAhIXBhcmFtLmluaXRpYWxpemVyXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdFx0Ly8gT25seSBwcm9jZXNzIGZpcnN0IGNvbnN0cnVjdG9yXG5cdFx0XHRicmVhaztcblx0XHR9XG5cblx0XHRyZXR1cm4gcGFyYW1zO1xuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBkZWZpbmUoKSBjYWxsXG5cdFx0XHQgKiBUaGlzIGlzIHVzZWQgZm9yIFR5cGVSZWdpc3RyeSBjb25zdHJ1Y3RvciBzaWduYXR1cmVzXG5cdFx0XHQgKiBQcmVzZXJ2ZXMgcGFyYW1ldGVyIG5hbWVzIGFuZCBleHBhbmRzIG9iamVjdCB0eXBlcyB0byB0aGVpciBzdHJ1Y3R1cmVcblx0XHRcdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdIHtcblx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCk7XG5cdFx0aWYgKCFjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdHJldHVybiBbXTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JQYXJhbXNGcm9tQ29uc3RydWN0b3IoY29uc3RydWN0b3JFeHByKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBhIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24uXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JQYXJhbXNGcm9tQ29uc3RydWN0b3IgKGNvbnN0cnVjdG9yRXhwcjogdHMuRXhwcmVzc2lvbik6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10ge1xuXHRcdGNvbnN0IHBhcmFtczogQ29uc3RydWN0b3JQYXJhbUluZm9bXSA9IFtdO1xuXHRcblx0XHQvLyBIYW5kbGUgZnVuY3Rpb24gZXhwcmVzc2lvbiBvciBhcnJvdyBmdW5jdGlvblxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzQXJyb3dGdW5jdGlvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHQvLyBMb29rIGZvciBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIChzZWNvbmQgcGFyYW0gYWZ0ZXIgYHRoaXNgKVxuXHRcdFx0Ly8gUGF0dGVybnM6IGZ1bmN0aW9uKHRoaXM6IFR5cGUsIGRhdGE6IHsgLi4uIH0pIG9yICh0aGlzOiBUeXBlLCBkYXRhOiB7IC4uLiB9KSA9PlxuXHRcdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBjb25zdHJ1Y3RvckV4cHIucGFyYW1ldGVycy5sZW5ndGg7IGkrKykge1xuXHRcdFx0XHRjb25zdCBwYXJhbSA9IGNvbnN0cnVjdG9yRXhwci5wYXJhbWV0ZXJzWyBpIF07XG5cdFx0XHRcdGlmICghcGFyYW0udHlwZSkgY29udGludWU7XG5cdFxuXHRcdFx0XHQvLyBTa2lwIGB0aGlzYCBwYXJhbWV0ZXIgKGZpcnN0IHBhcmFtKVxuXHRcdFx0XHRpZiAoXG5cdFx0XHRcdFx0aSA9PT0gMCAmJlxuXHRcdFx0XHRcdHBhcmFtLm5hbWUua2luZCA9PT0gdHMuU3ludGF4S2luZC5JZGVudGlmaWVyICYmXG5cdFx0XHRcdFx0KHBhcmFtLm5hbWUgYXMgdHMuSWRlbnRpZmllcikudGV4dCA9PT0gJ3RoaXMnXG5cdFx0XHRcdCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFxuXHRcdFx0XHQvLyBHZXQgcGFyYW1ldGVyIG5hbWUgYW5kIGV4cGFuZCBpdHMgdHlwZVxuXHRcdFx0XHRjb25zdCBwYXJhbU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgPyBwYXJhbS5uYW1lLnRleHQgOiAnYXJnJztcblx0XHRcdFx0Y29uc3QgZXhwYW5kZWRUeXBlID0gdGhpcy5yZXNvbHZlQ29uc3RydWN0b3JQYXJhbVR5cGUocGFyYW0udHlwZSkgfHwgdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cdFx0XHRcdFx0XG5cdFx0XHRcdHBhcmFtcy5wdXNoKHtcblx0XHRcdFx0XHRuYW1lICAgICA6IHBhcmFtTmFtZSxcblx0XHRcdFx0XHR0eXBlICAgICA6IGV4cGFuZGVkVHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6ICEhcGFyYW0ucXVlc3Rpb25Ub2tlbiB8fCAhIXBhcmFtLmluaXRpYWxpemVyXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0Ly8gSGFuZGxlIGNsYXNzIGV4cHJlc3Npb24gLSBjaGVjayBjb25zdHJ1Y3RvciBtZXRob2Rcblx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Y29uc3QgY2xhc3NQYXJhbXMgPSB0aGlzLmV4dHJhY3RDbGFzc0NvbnN0cnVjdG9yUGFyYW1zKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGNsYXNzUGFyYW1zKSB7XG5cdFx0XHRcdHBhcmFtcy5wdXNoKHBhcmFtKTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcGFyYW1zO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgZnJhbWV3b3JrIGluc3RydW1lbnRhdGlvbiBwb2ludHMuIFB1cmVseSBzeW50YWN0aWM6IGhlcml0YWdlXG5cdCAqIGNsYXVzZXMsIGRlY29yYXRvciBhcHBsaWNhdGlvbiBzaXRlcywgcHJvdmlkZXItdG9rZW4gb2JqZWN0IGxpdGVyYWxzXG5cdCAqIGFuZCBjb25zdW1lci5hcHBseSgpLmZvclJvdXRlcygpIHdpcmluZy4gVGhlIHZvY2FidWxhcnkgY29tZXMgZnJvbVxuXHQgKiBwbHVnaW5zOyBpZGVudGlmaWVyIHRleHQgaXMgbWF0Y2hlZCBhcy1pcyDigJQgbm8gaW1wb3J0IHJlc29sdXRpb24sXG5cdCAqIHRoZSB0eXBlIGNoZWNrZXIgc3RheXMgdW51c2VkLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0SW5zdHJ1bWVudGF0aW9uIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbkNsYXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0XHRpZiAodHMuaXNEZWNvcmF0b3Iobm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbkRlY29yYXRvcihub2RlLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cdFx0aWYgKHRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvblByb3ZpZGVyKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uTWlkZGxld2FyZShub2RlLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGEgbmFtZWQgY2xhc3MgZGVjbGFyYXRpb24gZm9yIGluc3RydW1lbnRhdGlvbiBzaXRlIHJlc29sdXRpb25cblx0ICogYW5kIGRldGVjdCBoZXJpdGFnZS1iYXNlZCBraW5kcyAoYGltcGxlbWVudHMgPHBsdWdpbiBpbnRlcmZhY2U+YClcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEluc3RydW1lbnRhdGlvbkNsYXNzIChub2RlOiB0cy5DbGFzc0RlY2xhcmF0aW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCFub2RlLm5hbWUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgY2xhc3NOYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUubmFtZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHQvLyBGaXJzdCBsaW5lIG9mIHRoZSBkZWNsYXJhdGlvbiwgbGlrZSBFRFMgYGNvZGVgIHNuaXBwZXRzXG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zcGxpdCgnXFxuJylbIDAgXS5zbGljZSgwLCAxMDApO1xuXG5cdFx0bGV0IGtpbmQ6IEluc3RydW1lbnRhdGlvbktpbmQgfCB1bmRlZmluZWQ7XG5cdFx0aWYgKG5vZGUuaGVyaXRhZ2VDbGF1c2VzKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGNsYXVzZSBvZiBub2RlLmhlcml0YWdlQ2xhdXNlcykge1xuXHRcdFx0XHRpZiAoY2xhdXNlLnRva2VuICE9PSB0cy5TeW50YXhLaW5kLkltcGxlbWVudHNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Zm9yIChjb25zdCB0eXBlIG9mIGNsYXVzZS50eXBlcykge1xuXHRcdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHR5cGUuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCBtYXRjaGVkID0gdGhpcy5pbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5LmludGVyZmFjZXNbIHR5cGUuZXhwcmVzc2lvbi50ZXh0IF07XG5cdFx0XHRcdFx0aWYgKG1hdGNoZWQpIHtcblx0XHRcdFx0XHRcdGtpbmQgPSBtYXRjaGVkO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGNvbnN0IGRlY2w6IEluc3RydW1lbnRhdGlvbkNsYXNzRGVjbCA9IHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0Y29kZSxcblx0XHR9O1xuXHRcdGlmIChraW5kKSB7XG5cdFx0XHRkZWNsLmtpbmQgPSBraW5kO1xuXHRcdH1cblx0XHR0aGlzLmluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMuc2V0KGNsYXNzTmFtZSwgZGVjbCk7XG5cdH1cblxuXHQvKipcblx0ICogRGV0ZWN0IGRlY29yYXRvciBhcHBsaWNhdGlvbiBzaXRlczogcGx1Z2luLWxpc3RlZCBkZWNvcmF0b3JzIGFwcGxpZWRcblx0ICogd2l0aCBjbGFzcyBhcmd1bWVudHMgb24gYSBjbGFzcyBvciBvbmUgb2YgaXRzIG1ldGhvZHMuIE9uZSBzaXRlIHBlclxuXHQgKiByZWZlcmVuY2VkIGNsYXNzIGlkZW50aWZpZXIuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25EZWNvcmF0b3IgKG5vZGU6IHRzLkRlY29yYXRvciwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24oZXhwcmVzc2lvbikgfHwgIXRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGtpbmQgPSB0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkudXNlRGVjb3JhdG9yc1sgZXhwcmVzc2lvbi5leHByZXNzaW9uLnRleHQgXTtcblx0XHRpZiAoIWtpbmQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBUaGUgZGVjb3JhdG9yJ3MgcGFyZW50IGlzIHRoZSBkZWNvcmF0ZWQgbm9kZTogYSBjb250cm9sbGVyIGNsYXNzLFxuXHRcdC8vIG9uZSBvZiBpdHMgbWV0aG9kcywgb3Igb25lIG9mIGl0cyBtZXRob2QgcGFyYW1ldGVyc1xuXHRcdC8vIChAQm9keShtdnAuZm9yVHlwZShEdG8pKSBvbiBhIGhhbmRsZXIgYXJndW1lbnQpXG5cdFx0Y29uc3QgZGVjb3JhdGVkID0gbm9kZS5wYXJlbnQ7XG5cdFx0bGV0IHNjb3BlOiBJbnN0cnVtZW50YXRpb25TY29wZTtcblx0XHRsZXQgdGFyZ2V0czogc3RyaW5nW107XG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihkZWNvcmF0ZWQpICYmIGRlY29yYXRlZC5uYW1lKSB7XG5cdFx0XHRzY29wZSA9IGBjb250cm9sbGVyOiR7ZGVjb3JhdGVkLm5hbWUudGV4dH1gO1xuXHRcdFx0dGFyZ2V0cyA9IFsgZGVjb3JhdGVkLm5hbWUudGV4dCBdO1xuXHRcdH0gZWxzZSBpZiAoXG5cdFx0XHR0cy5pc01ldGhvZERlY2xhcmF0aW9uKGRlY29yYXRlZCkgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcihkZWNvcmF0ZWQubmFtZSkgJiZcblx0XHRcdHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihkZWNvcmF0ZWQucGFyZW50KSAmJlxuXHRcdFx0ZGVjb3JhdGVkLnBhcmVudC5uYW1lXG5cdFx0KSB7XG5cdFx0XHRjb25zdCBjbGFzc05hbWUgPSBkZWNvcmF0ZWQucGFyZW50Lm5hbWUudGV4dDtcblx0XHRcdHNjb3BlID0gYG1ldGhvZDoke2NsYXNzTmFtZX0uJHtkZWNvcmF0ZWQubmFtZS50ZXh0fWA7XG5cdFx0XHR0YXJnZXRzID0gWyBjbGFzc05hbWUgXTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzUGFyYW1ldGVyKGRlY29yYXRlZCkpIHtcblx0XHRcdC8vIFBhcmFtZXRlciBkZWNvcmF0b3JzIHRha2UgdGhlIGVuY2xvc2luZyBtZXRob2QncyBzY29wZSDigJQgdGhlXG5cdFx0XHQvLyBhdHRhY2htZW50IHBvaW50IGlzIHRoZSBoYW5kbGVyLCBub3QgdGhlIGFyZ3VtZW50IG5hbWU7IHRoZVxuXHRcdFx0Ly8gc2FtZSBtZXRob2Q6Q2xhc3MubWV0aG9kIGZvcm0gYXMgbWV0aG9kLWxldmVsIHNpdGVzLiBQYXJhbXMgb2Zcblx0XHRcdC8vIGNvbnN0cnVjdG9ycywgZnVuY3Rpb25zLCBhbmQgdW5uYW1lYWJsZSBob3N0cyBzdGF5IHNpbGVudCwgdGhlXG5cdFx0XHQvLyBzYW1lIGNvbnZlbnRpb24gYXMgb3RoZXIgdW5yZXNvbHZhYmxlIGRlY29yYXRvciBwYXJlbnRzXG5cdFx0XHRjb25zdCBob3N0ID0gZGVjb3JhdGVkLnBhcmVudDtcblx0XHRcdGlmIChcblx0XHRcdFx0aG9zdCAmJlxuXHRcdFx0XHR0cy5pc01ldGhvZERlY2xhcmF0aW9uKGhvc3QpICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihob3N0Lm5hbWUpICYmXG5cdFx0XHRcdHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihob3N0LnBhcmVudCkgJiZcblx0XHRcdFx0aG9zdC5wYXJlbnQubmFtZVxuXHRcdFx0KSB7XG5cdFx0XHRcdGNvbnN0IGNsYXNzTmFtZSA9IGhvc3QucGFyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0c2NvcGUgPSBgbWV0aG9kOiR7Y2xhc3NOYW1lfS4ke2hvc3QubmFtZS50ZXh0fWA7XG5cdFx0XHRcdHRhcmdldHMgPSBbIGNsYXNzTmFtZSBdO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0Zm9yIChjb25zdCBhcmcgb2YgZXhwcmVzc2lvbi5hcmd1bWVudHMpIHtcblx0XHRcdC8vIENsYXNzIHJlZmVyZW5jZTogQFJlZ2lzdGVyKEltcGwpIG9yIGFuIGlubGluZSBpbnN0YW5jZTpcblx0XHRcdC8vIEBSZWdpc3RlcihuZXcgSW1wbCh7IC4uLm9wdGlvbnMgfSkpXG5cdFx0XHRsZXQgY2xhc3NOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdFx0XHQvLyBwZXItYXJnIGtpbmQ6IGZhY3RvcnktY2FsbCBhcmdzIGNhcnJ5IHRoZWlyIG93biBjb25maWd1cmVkXG5cdFx0XHQvLyBraW5kLCBldmVyeXRoaW5nIGVsc2UgdGFrZXMgdGhlIGRlY29yYXRvcidzXG5cdFx0XHRsZXQgYXJnS2luZCA9IGtpbmQ7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdFx0Y2xhc3NOYW1lID0gYXJnLnRleHQ7XG5cdFx0XHR9IGVsc2UgaWYgKHRzLmlzTmV3RXhwcmVzc2lvbihhcmcpICYmIHRzLmlzSWRlbnRpZmllcihhcmcuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y2xhc3NOYW1lID0gYXJnLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdH0gZWxzZSBpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihhcmcpICYmIHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFyZy5leHByZXNzaW9uKSkge1xuXHRcdFx0XHQvLyBQaXBlLWZhY3Rvcnkgc2hhcGU6IEBVc2VQaXBlcyhtdnAuZm9yVHlwZShEdG8pKSDigJQgdGhlXG5cdFx0XHRcdC8vIGNhbGwncyBtZXRob2QgbmFtZSBpcyBwbHVnaW4tbGlzdGVkLCB0aGUgdGFyZ2V0IGNsYXNzIHNpdHNcblx0XHRcdFx0Ly8gaW4gdGhlIGNvbmZpZ3VyZWQgYXJndW1lbnQgcG9zaXRpb24gKGRlZmF1bHQgMClcblx0XHRcdFx0Y29uc3QgZmFjdG9yeSA9IHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS5kZWNvcmF0b3JBcmdGYWN0b3JpZXNbIGFyZy5leHByZXNzaW9uLm5hbWUudGV4dCBdO1xuXHRcdFx0XHRpZiAoZmFjdG9yeSkge1xuXHRcdFx0XHRcdGNvbnN0IHRhcmdldEFyZyA9IGFyZy5hcmd1bWVudHNbIGZhY3RvcnkudGFyZ2V0QXJnID8/IDAgXTtcblx0XHRcdFx0XHRpZiAodGFyZ2V0QXJnICYmIHRzLmlzSWRlbnRpZmllcih0YXJnZXRBcmcpKSB7XG5cdFx0XHRcdFx0XHRjbGFzc05hbWUgPSB0YXJnZXRBcmcudGV4dDtcblx0XHRcdFx0XHRcdGFyZ0tpbmQgPSBmYWN0b3J5LmtpbmQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAoIWNsYXNzTmFtZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uU2l0ZXMucHVzaCh7XG5cdFx0XHRcdGtpbmQgOiBhcmdLaW5kLFxuXHRcdFx0XHRjbGFzc05hbWUsXG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRzY29wZSxcblx0XHRcdFx0dGFyZ2V0cyxcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgZ2xvYmFsIHJlZ2lzdHJhdGlvbnM6IG9iamVjdCBsaXRlcmFscyBzaGFwZWQgbGlrZVxuXHQgKiBgeyBwcm92aWRlOiA8cGx1Z2luLWxpc3RlZCB0b2tlbj4sIHVzZUNsYXNzOiBYIH1gLlxuXHQgKiB1c2VFeGlzdGluZy91c2VGYWN0b3J5IHdpdGhvdXQgYSB1c2VDbGFzcyBpZGVudGlmaWVyIGFyZSBub3Rcblx0ICogc3RhdGljYWxseSBvYnZpb3VzIOKAlCBza2lwcGVkIHJhdGhlciB0aGFuIGd1ZXNzZWQuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25Qcm92aWRlciAobm9kZTogdHMuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRsZXQga2luZDogSW5zdHJ1bWVudGF0aW9uS2luZCB8IHVuZGVmaW5lZDtcblx0XHRsZXQgdXNlQ2xhc3NOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cblx0XHRmb3IgKGNvbnN0IHByb3Agb2Ygbm9kZS5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdCF0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSB8fFxuXHRcdFx0XHQhdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkgfHxcblx0XHRcdFx0IXRzLmlzSWRlbnRpZmllcihwcm9wLmluaXRpYWxpemVyKVxuXHRcdFx0KSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHByb3AubmFtZS50ZXh0ID09PSAncHJvdmlkZScpIHtcblx0XHRcdFx0a2luZCA9IHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS5hcHBUb2tlbnNbIHByb3AuaW5pdGlhbGl6ZXIudGV4dCBdO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHByb3AubmFtZS50ZXh0ID09PSAndXNlQ2xhc3MnKSB7XG5cdFx0XHRcdHVzZUNsYXNzTmFtZSA9IHByb3AuaW5pdGlhbGl6ZXIudGV4dDtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRpZiAoIWtpbmQgfHwgIXVzZUNsYXNzTmFtZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uU2l0ZXMucHVzaCh7XG5cdFx0XHRraW5kLFxuXHRcdFx0Y2xhc3NOYW1lIDogdXNlQ2xhc3NOYW1lLFxuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRjb2RlLFxuXHRcdFx0c2NvcGUgICAgIDogJ2dsb2JhbCcsXG5cdFx0XHR0YXJnZXRzICAgOiBbXSxcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgbWlkZGxld2FyZSB3aXJpbmc6IGBjb25zdW1lci5hcHBseShNdzEsIE13MikuZm9yUm91dGVzKC4uLilgXG5cdCAqIGluc2lkZSBhIGNsYXNzJ3MgY29uZmlndXJlKCkgbWV0aG9kLiBUYXJnZXRzIGNvbWUgZnJvbSBmb3JSb3V0ZXNcblx0ICogYXJndW1lbnRzIHdoZW4gc3RhdGljYWxseSByZWFkYWJsZSAoc3RyaW5nIHJvdXRlcyBvciBjb250cm9sbGVyXG5cdCAqIGlkZW50aWZpZXJzKSwgZWxzZSBbXS4gU2hhcGUtYmFzZWQsIHNvIGEgcGx1Z2luIG11c3Qgb3B0IGluIHZpYVxuXHQgKiBgbWlkZGxld2FyZVdpcmluZzogdHJ1ZWAuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25NaWRkbGV3YXJlIChub2RlOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdGhpcy5pbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5Lm1pZGRsZXdhcmVXaXJpbmcpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKFxuXHRcdFx0IXRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbikgfHxcblx0XHRcdG5vZGUuZXhwcmVzc2lvbi5uYW1lLnRleHQgIT09ICdmb3JSb3V0ZXMnXG5cdFx0KSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGFwcGx5Q2FsbCA9IG5vZGUuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdGlmIChcblx0XHRcdCF0cy5pc0NhbGxFeHByZXNzaW9uKGFwcGx5Q2FsbCkgfHxcblx0XHRcdCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcHBseUNhbGwuZXhwcmVzc2lvbikgfHxcblx0XHRcdGFwcGx5Q2FsbC5leHByZXNzaW9uLm5hbWUudGV4dCAhPT0gJ2FwcGx5J1xuXHRcdCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAoIXRoaXMuaXNJbnNpZGVDb25maWd1cmVNZXRob2Qobm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB0YXJnZXRzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgYXJnIG9mIG5vZGUuYXJndW1lbnRzKSB7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykgfHwgdHMuaXNTdHJpbmdMaXRlcmFsKGFyZykpIHtcblx0XHRcdFx0dGFyZ2V0cy5wdXNoKGFyZy50ZXh0KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0YXBwbHlDYWxsLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdGZvciAoY29uc3QgYXJnIG9mIGFwcGx5Q2FsbC5hcmd1bWVudHMpIHtcblx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHR0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzLnB1c2goe1xuXHRcdFx0XHRraW5kICAgICAgOiAnbWlkZGxld2FyZScsXG5cdFx0XHRcdGNsYXNzTmFtZSA6IGFyZy50ZXh0LFxuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0c2NvcGUgICAgIDogJ21vZHVsZScsXG5cdFx0XHRcdHRhcmdldHMsXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogV2FsayB1cCB0aGUgcGFyZW50IGNoYWluIGxvb2tpbmcgZm9yIGFuIGVuY2xvc2luZyBjb25maWd1cmUoKSBtZXRob2Rcblx0ICovXG5cdHByaXZhdGUgaXNJbnNpZGVDb25maWd1cmVNZXRob2QgKG5vZGU6IHRzLk5vZGUpOiBib29sZWFuIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5vZGUucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24oY3VycmVudCkgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGN1cnJlbnQubmFtZSkgJiZcblx0XHRcdFx0Y3VycmVudC5uYW1lLnRleHQgPT09ICdjb25maWd1cmUnXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxufVxuIl19