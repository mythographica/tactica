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
                    const aliasResult = queryResult.node.fullPath.replace(/\./g, '_');
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYW5hbHl6ZXIuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvYW5hbHl6ZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFFYiwrQ0FBaUM7QUFDakMsK0NBQWlDO0FBT2pDLG1DQUVpQjtBQUNqQix1Q0FFbUI7QUErRG5COzs7R0FHRztBQUNILE1BQU0sa0JBQWtCLEdBQUcsSUFBSSxHQUFHLENBQUM7SUFDbEMsTUFBTSxFQUFFLFFBQVEsRUFBRSxPQUFPLEVBQUUsV0FBVyxFQUFFLFlBQVksRUFBRSxnQkFBZ0I7SUFDdEUsYUFBYSxFQUFFLFdBQVcsRUFBRSxVQUFVLEVBQUUsZ0JBQWdCO0lBQ3hELEtBQUssRUFBRSxLQUFLLEVBQUUsU0FBUyxFQUFFLFNBQVMsRUFBRSxTQUFTLEVBQUUsc0JBQXNCO0lBQ3JFLFNBQVMsRUFBRSxPQUFPLEVBQUUsZUFBZSxFQUFFLFFBQVEsRUFBRSxTQUFTLEVBQUUsVUFBVTtJQUNwRSxVQUFVLEVBQUUsTUFBTSxFQUFFLE1BQU0sRUFBRSxTQUFTLEVBQUUsU0FBUyxFQUFFLGFBQWE7SUFDL0QsWUFBWSxFQUFFLGNBQWMsRUFBRSxZQUFZLEVBQUUsdUJBQXVCO0lBQ25FLFVBQVUsRUFBRSxtQkFBbUIsRUFBRSxtQkFBbUI7SUFDcEQsV0FBVyxFQUFFLFdBQVcsRUFBRSxZQUFZLEVBQUUsY0FBYztJQUN0RCxRQUFRLEVBQUUsUUFBUSxFQUFFLFNBQVMsRUFBRSxRQUFRLEVBQUUsUUFBUSxFQUFFLFFBQVEsRUFBRSxVQUFVO0lBQ3ZFLFVBQVUsRUFBRSxVQUFVLEVBQUUsV0FBVyxFQUFFLGVBQWUsRUFBRSxlQUFlO0lBQ3JFLGdCQUFnQixFQUFFLGtCQUFrQixFQUFFLHVCQUF1QjtJQUM3RCxhQUFhLEVBQUUsYUFBYSxFQUFFLG1CQUFtQixFQUFFLFVBQVU7SUFDN0QsV0FBVyxFQUFFLFlBQVksRUFBRSxtQkFBbUIsRUFBRSxZQUFZO0lBQzVELGFBQWEsRUFBRSxZQUFZLEVBQUUsYUFBYSxFQUFFLGNBQWM7SUFDMUQsY0FBYyxFQUFFLGVBQWUsRUFBRSxnQkFBZ0IsRUFBRSxNQUFNO0NBQ3pELENBQUMsQ0FBQztBQUVILGlGQUFpRjtBQUNqRixNQUFNLHdCQUF3QixHQUFHLENBQUMsQ0FBQztBQUNuQywwRUFBMEU7QUFDMUUsK0RBQStEO0FBQy9ELE1BQU0sa0JBQWtCLEdBQUcsQ0FBQyxDQUFDO0FBRTdCOzs7Ozs7R0FNRztBQUNILE1BQWEsaUJBQWlCO0lBcUk3QixZQUFhLE9BQW9CLEVBQUUsVUFBMkIsRUFBRTtRQXBJeEQsV0FBTSxHQUFtQixFQUFFLENBQUM7UUFDNUIsVUFBSyxHQUFHLElBQUkscUJBQWEsRUFBRSxDQUFDO1FBQzVCLGdCQUFXLEdBQUcsSUFBSSxHQUFHLEVBQTBCLENBQUM7UUFDaEQsV0FBTSxHQUFHLElBQUksR0FBRyxFQUF1QixDQUFDO1FBQ3hDLGNBQVMsR0FBRyxJQUFJLEdBQUcsRUFBcUIsQ0FBQztRQUN6QyxlQUFVLEdBQUcsSUFBSSxHQUFHLEVBQXNCLENBQUM7UUFDbkQsc0VBQXNFO1FBQ3RFLHVFQUF1RTtRQUN2RSxzRUFBc0U7UUFDdEUsNkNBQTZDO1FBQ3JDLG1CQUFjLEdBQUcsSUFBSSxHQUFHLEVBQW1CLENBQUM7UUFDcEQscUVBQXFFO1FBQ3JFLHdFQUF3RTtRQUNoRSxxQkFBZ0IsR0FBRyxJQUFJLEdBQUcsRUFBc0MsQ0FBQztRQUN6RSxtRUFBbUU7UUFDbkUscUVBQXFFO1FBQ3JFLG1FQUFtRTtRQUNuRSxvQkFBb0I7UUFDWixrQkFBYSxHQUFHLElBQUksR0FBRyxFQUE0QyxDQUFDO1FBQzVFLG9FQUFvRTtRQUNwRSxrRUFBa0U7UUFDbEUscURBQXFEO1FBQzdDLG9CQUFlLEdBQUcsSUFBSSxHQUFHLEVBQW9CLENBQUM7UUFDdEQsNEVBQTRFO1FBQ3BFLHNCQUFpQixHQUFHLElBQUksR0FBRyxFQUFrQixDQUFDO1FBQ3RELDZHQUE2RztRQUNyRywwQkFBcUIsR0FBRyxJQUFJLEdBQUcsRUFBVSxDQUFDO1FBQ2xELCtEQUErRDtRQUMvRCwrREFBK0Q7UUFDL0Qsa0VBQWtFO1FBQ2xFLHVEQUF1RDtRQUMvQywwQkFBcUIsR0FBRyxJQUFJLEdBQUcsRUFBK0IsQ0FBQztRQUN2RSxrR0FBa0c7UUFDMUYsbUNBQThCLEdBQUcsSUFBSSxHQUFHLEVBQVUsQ0FBQztRQUMzRCxrRUFBa0U7UUFDMUQsd0JBQW1CLEdBQUcsSUFBSSxHQUFHLEVBQWtCLENBQUM7UUFDeEQsa0VBQWtFO1FBQzFELG1CQUFjLEdBQUcsSUFBSSxHQUFHLEVBQTBCLENBQUM7UUFDbkQsc0JBQWlCLEdBQUcsQ0FBQyxDQUFDO1FBQzlCLGlFQUFpRTtRQUNqRSw4REFBOEQ7UUFDOUQsdUVBQXVFO1FBQy9ELDhCQUF5QixHQUFHLElBQUksR0FBRyxFQUFvQyxDQUFDO1FBQ2hGLG9FQUFvRTtRQUNwRSwrQ0FBK0M7UUFDdkMseUJBQW9CLEdBQTBCLEVBQUUsQ0FBQztRQUl6RCx1RUFBdUU7UUFDdkUsd0VBQXdFO1FBQ3hFLG9FQUFvRTtRQUNwRSx1RUFBdUU7UUFDdkUscUVBQXFFO1FBQ3JFLHlFQUF5RTtRQUN6RSx5RUFBeUU7UUFDakUsd0JBQW1CLEdBQUcsSUFBSSxHQUFHLEVBQWtELENBQUM7UUFDaEYsMEJBQXFCLEdBQUcsSUFBSSxHQUFHLEVBQTZDLENBQUM7UUFDckYsNkVBQTZFO1FBQ3JFLDRCQUF1QixHQUFHLElBQUksR0FBRyxFQUErQixDQUFDO1FBQ3pFLDRDQUE0QztRQUNwQyw4QkFBeUIsR0FBRyxJQUFJLEdBQUcsRUFBb0IsQ0FBQztRQUNoRSxnRUFBZ0U7UUFDeEQsZ0NBQTJCLEdBQUcsSUFBSSxHQUFHLEVBQStCLENBQUM7UUFDN0Usc0VBQXNFO1FBQ3RFLHFFQUFxRTtRQUM3RCw2QkFBd0IsR0FBRyxJQUFJLEdBQUcsRUFBNkMsQ0FBQztRQUN4RixzRUFBc0U7UUFDdEUsdURBQXVEO1FBQy9DLGlDQUE0QixHQUFHLElBQUksR0FBRyxFQUErQixDQUFDO1FBQzlFLHVFQUF1RTtRQUMvRCxrQ0FBNkIsR0FBRyxJQUFJLEdBQUcsRUFBZ0QsQ0FBQztRQUNoRyxzRUFBc0U7UUFDdEUsMERBQTBEO1FBQzFELHdFQUF3RTtRQUN4RSx1RUFBdUU7UUFDdkUsb0VBQW9FO1FBQ3BFLHlEQUF5RDtRQUNqRCw4QkFBeUIsR0FBRyxJQUFJLEdBQUcsRUFBa0QsQ0FBQztRQUU5RiwyRUFBMkU7UUFDbkUsOEJBQXlCLEdBQUcsRUFBRSxDQUFDO1FBQ3ZDLHFEQUFxRDtRQUM3QywrQkFBMEIsR0FBRyxJQUFJLEdBQUcsRUFBVSxDQUFDO1FBQ3ZELG1FQUFtRTtRQUNuRSxxRUFBcUU7UUFDckUsb0VBQW9FO1FBQ3BFLHNFQUFzRTtRQUN0RSx1REFBdUQ7UUFDL0MsZ0JBQVcsR0FBRyxJQUFJLEdBQUcsRUFBb0IsQ0FBQztRQUNsRCxvRUFBb0U7UUFDcEUsd0RBQXdEO1FBQ2hELHlCQUFvQixHQUFzQixFQUFFLENBQUM7UUFDckQsa0VBQWtFO1FBQ2xFLHlFQUF5RTtRQUNqRSw4QkFBeUIsR0FBRyxLQUFLLENBQUM7UUFDMUMseUVBQXlFO1FBQ3pFLHFFQUFxRTtRQUNyRSx1RUFBdUU7UUFDdkUsa0VBQWtFO1FBQ2xFLDJEQUEyRDtRQUNuRCxxQkFBZ0IsR0FBeUMsRUFBRSxDQUFDO1FBQ3BFLHVFQUF1RTtRQUN2RSx5RUFBeUU7UUFDakUsaUNBQTRCLEdBQUcsS0FBSyxDQUFDO1FBQzdDLHVFQUF1RTtRQUN2RSxvRUFBb0U7UUFDcEUsaUVBQWlFO1FBQ2pFLHNFQUFzRTtRQUN0RSxtRUFBbUU7UUFDbkUscUVBQXFFO1FBQ3JFLHFFQUFxRTtRQUNyRSxxRUFBcUU7UUFDckUsdUVBQXVFO1FBQy9ELHdCQUFtQixHQUF1RCxFQUFFLENBQUM7UUFDckYsb0VBQW9FO1FBQ3BFLHNFQUFzRTtRQUN0RSxtRUFBbUU7UUFDM0Qsc0JBQWlCLEdBQUcsSUFBSSxHQUFHLEVBQStCLENBQUM7UUFJbkUseUVBQXlFO1FBQ3pFLHdFQUF3RTtRQUN4RSx3RUFBd0U7UUFDeEUsdUVBQXVFO1FBQ3ZFLHVFQUF1RTtRQUN2RSxzRUFBc0U7UUFDdEUsd0VBQXdFO1FBQ3hFLDhEQUE4RDtRQUN0RCxtQkFBYyxHQUFHLElBQUksR0FBRyxFQUFxQixDQUFDO1FBR3JELCtEQUErRDtRQUMvRCw4REFBOEQ7UUFDOUQsa0RBQWtEO1FBQ2xELElBQUksQ0FBQyw2QkFBNkIsR0FBRyxPQUFPLEVBQUUsa0JBQWtCLEVBQUUsSUFBSSxFQUFFLENBQUM7UUFDekUsSUFBSSxDQUFDLHlCQUF5QixHQUFHLElBQUEsNkJBQW1CLEVBQUMsT0FBTyxDQUFDLENBQUM7SUFDL0QsQ0FBQztJQUVEOzs7T0FHRztJQUNILFdBQVc7UUFDVixJQUFJLENBQUMsTUFBTSxDQUFDLEtBQUssRUFBRSxDQUFDO1FBQ3BCLElBQUksQ0FBQyxTQUFTLENBQUMsS0FBSyxFQUFFLENBQUM7UUFDdkIsSUFBSSxDQUFDLFVBQVUsQ0FBQyxLQUFLLEVBQUUsQ0FBQztRQUN4QixJQUFJLENBQUMsaUJBQWlCLENBQUMsS0FBSyxFQUFFLENBQUM7UUFDL0IsOERBQThEO1FBQzlELDhCQUE4QjtRQUM5QixJQUFJLENBQUMsZUFBZSxDQUFDLEtBQUssRUFBRSxDQUFDO1FBQzdCLElBQUksQ0FBQyxhQUFhLENBQUMsS0FBSyxFQUFFLENBQUM7UUFDM0IsNEVBQTRFO1FBQzVFLHNDQUFzQztRQUN0QyxpRUFBaUU7UUFDakUsa0VBQWtFO1FBQ2xFLHVFQUF1RTtRQUN2RSxJQUFJLENBQUMsY0FBYyxDQUFDLEtBQUssRUFBRSxDQUFDO1FBQzVCLG9FQUFvRTtRQUNwRSwrREFBK0Q7UUFDL0QsNkNBQTZDO1FBQzdDLElBQUksQ0FBQyx5QkFBeUIsR0FBRyxLQUFLLENBQUM7UUFDdkMsSUFBSSxDQUFDLGdCQUFnQixHQUFHLEVBQUUsQ0FBQztRQUMzQixJQUFJLENBQUMsNEJBQTRCLEdBQUcsS0FBSyxDQUFDO1FBQzFDLElBQUksQ0FBQyxtQkFBbUIsR0FBRyxFQUFFLENBQUM7SUFDL0IsQ0FBQztJQUVEOztPQUVHO0lBQ0gsV0FBVyxDQUFFLFVBQXlCO1FBQ3JDLElBQUksQ0FBQyxNQUFNLEdBQUcsRUFBRSxDQUFDO1FBQ2pCLHFFQUFxRTtRQUNyRSxJQUFJLENBQUMseUJBQXlCLEdBQUcsUUFBUSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsUUFBUSxDQUFDLENBQUM7UUFDdkUsZ0RBQWdEO1FBQ2hELElBQUksQ0FBQywwQkFBMEIsQ0FBQyxVQUFVLENBQUMsQ0FBQztRQUM1QyxJQUFJLENBQUMsU0FBUyxDQUFDLFVBQVUsRUFBRSxVQUFVLENBQUMsQ0FBQztRQUV2QyxPQUFPO1lBQ04sS0FBSyxFQUFJLElBQUksQ0FBQyxLQUFLLENBQUMsV0FBVyxFQUFFO1lBQ2pDLE1BQU0sRUFBRyxJQUFJLENBQUMsTUFBTTtTQUNwQixDQUFDO0lBQ0gsQ0FBQztJQUVEOztPQUVHO0lBQ0gsYUFBYSxDQUFFLFVBQWtCLEVBQUUsUUFBUSxHQUFHLFNBQVM7UUFDdEQsTUFBTSxVQUFVLEdBQUcsRUFBRSxDQUFDLGdCQUFnQixDQUNyQyxRQUFRLEVBQ1IsVUFBVSxFQUNWLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxFQUN0QixJQUFJLENBQ0osQ0FBQztRQUNGLE9BQU8sSUFBSSxDQUFDLFdBQVcsQ0FBQyxVQUFVLENBQUMsQ0FBQztJQUNyQyxDQUFDO0lBRUQ7O09BRUc7SUFDSCxRQUFRO1FBQ1AsT0FBTyxJQUFJLENBQUMsS0FBSyxDQUFDO0lBQ25CLENBQUM7SUFFRDs7T0FFRztJQUNILGNBQWM7UUFDYixPQUFPLElBQUksQ0FBQyxXQUFXLENBQUM7SUFDekIsQ0FBQztJQUVEOztPQUVHO0lBQ0gsU0FBUztRQUNSLE9BQU8sSUFBSSxDQUFDLE1BQU0sQ0FBQztJQUNwQixDQUFDO0lBRUQ7O09BRUc7SUFDSCxZQUFZO1FBQ1gsT0FBTyxJQUFJLENBQUMsU0FBUyxDQUFDO0lBQ3ZCLENBQUM7SUFFRDs7T0FFRztJQUNILGFBQWE7UUFDWixPQUFPLElBQUksQ0FBQyxVQUFVLENBQUM7SUFDeEIsQ0FBQztJQUVEOzs7Ozs7Ozs7T0FTRztJQUNILHdCQUF3QjtRQUN2QixNQUFNLE1BQU0sR0FBRyxJQUFJLEdBQUcsRUFBZ0MsQ0FBQztRQUV2RCxNQUFNLFFBQVEsR0FBRyxDQUFDLEtBQTJCLEVBQVEsRUFBRTtZQUN0RCxNQUFNLEdBQUcsR0FBRyxHQUFHLEtBQUssQ0FBQyxJQUFJLElBQUksS0FBSyxDQUFDLFNBQVMsSUFBSSxLQUFLLENBQUMsUUFBUSxJQUFJLEtBQUssQ0FBQyxLQUFLLEVBQUUsQ0FBQztZQUNoRixNQUFNLFFBQVEsR0FBRyxNQUFNLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDO1lBQ2pDLElBQUksUUFBUSxFQUFFLENBQUM7Z0JBQ2QsTUFBTSxNQUFNLEdBQUcsSUFBSSxHQUFHLENBQUMsQ0FBRSxHQUFHLFFBQVEsQ0FBQyxPQUFPLEVBQUUsR0FBRyxLQUFLLENBQUMsT0FBTyxDQUFFLENBQUMsQ0FBQztnQkFDbEUsUUFBUSxDQUFDLE9BQU8sR0FBRyxLQUFLLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxDQUFDO2dCQUN0QyxPQUFPO1lBQ1IsQ0FBQztZQUNELE1BQU0sQ0FBQyxHQUFHLENBQUMsR0FBRyxFQUFFLEtBQUssQ0FBQyxDQUFDO1FBQ3hCLENBQUMsQ0FBQztRQUVGLEtBQUssTUFBTSxJQUFJLElBQUksSUFBSSxDQUFDLG9CQUFvQixFQUFFLENBQUM7WUFDOUMsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUM7WUFDaEUsTUFBTSxLQUFLLEdBQXlCO2dCQUNuQyxJQUFJLEVBQVEsSUFBSSxDQUFDLElBQUk7Z0JBQ3JCLFNBQVMsRUFBRyxJQUFJLENBQUMsU0FBUztnQkFDMUIsUUFBUSxFQUFJLElBQUksQ0FBQyxDQUFDLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDLENBQUMsSUFBSSxDQUFDLFFBQVE7Z0JBQ2hELElBQUksRUFBUSxJQUFJLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJO2dCQUN4QyxLQUFLLEVBQU8sSUFBSSxDQUFDLEtBQUs7Z0JBQ3RCLE9BQU8sRUFBSyxJQUFJLENBQUMsT0FBTzthQUN4QixDQUFDO1lBQ0YsUUFBUSxDQUFDLEtBQUssQ0FBQyxDQUFDO1FBQ2pCLENBQUM7UUFFRCxpRUFBaUU7UUFDakUsK0RBQStEO1FBQy9ELDREQUE0RDtRQUM1RCxLQUFLLE1BQU0sQ0FBRSxTQUFTLEVBQUUsSUFBSSxDQUFFLElBQUksSUFBSSxDQUFDLHlCQUF5QixFQUFFLENBQUM7WUFDbEUsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQztnQkFDaEIsU0FBUztZQUNWLENBQUM7WUFDRCxNQUFNLEtBQUssR0FBeUI7Z0JBQ25DLElBQUksRUFBUSxJQUFJLENBQUMsSUFBSTtnQkFDckIsU0FBUyxFQUFHLFNBQVM7Z0JBQ3JCLFFBQVEsRUFBSSxJQUFJLENBQUMsUUFBUTtnQkFDekIsSUFBSSxFQUFRLElBQUksQ0FBQyxJQUFJO2dCQUNyQixLQUFLLEVBQU8sUUFBUTtnQkFDcEIsT0FBTyxFQUFLLEVBQUU7YUFDZCxDQUFDO1lBQ0YsUUFBUSxDQUFDLEtBQUssQ0FBQyxDQUFDO1FBQ2pCLENBQUM7UUFFRCxNQUFNLE1BQU0sR0FBRyxLQUFLLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxNQUFNLEVBQUUsQ0FBQyxDQUFDO1FBQzNDLE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7T0FHRztJQUNILGlCQUFpQixDQUFFLFFBQWdCLEVBQUUsSUFBZ0M7UUFDcEUseUJBQXlCO1FBQ3pCLElBQUksSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDdkMsT0FBTztRQUNSLENBQUM7UUFFRCwwREFBMEQ7UUFDMUQsSUFBSSxJQUFJLENBQUMsTUFBTSxFQUFFLENBQUM7WUFDakIseUJBQXlCO1lBQ3pCLElBQUksQ0FBQyxLQUFLLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQyxNQUFNLEVBQUUsSUFBSSxDQUFDLENBQUM7UUFDeEMsQ0FBQzthQUFNLENBQUM7WUFDUCxjQUFjO1lBQ2QsSUFBSSxDQUFDLEtBQUssQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDMUIsQ0FBQztRQUVELDZEQUE2RDtRQUM3RCxNQUFNLFVBQVUsR0FBbUI7WUFDbEMsSUFBSSxFQUFVLElBQUksQ0FBQyxJQUFJO1lBQ3ZCLFFBQVEsRUFBTSxHQUFHLElBQUksQ0FBQyxVQUFVLElBQUksSUFBSSxDQUFDLElBQUksSUFBSSxJQUFJLENBQUMsTUFBTSxFQUFFO1lBQzlELElBQUksRUFBVSxRQUFRO1lBQ3RCLE1BQU0sRUFBUSxJQUFJLENBQUMsTUFBTSxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLFFBQVEsQ0FBQyxDQUFDLENBQUMsSUFBSTtZQUN2RCxXQUFXLEVBQUcsSUFBSTtZQUNsQixXQUFXLEVBQUcsS0FBSztTQUNuQixDQUFDO1FBQ0YsSUFBSSxDQUFDLFdBQVcsQ0FBQyxHQUFHLENBQUMsUUFBUSxFQUFFLFVBQVUsQ0FBQyxDQUFDO0lBQzVDLENBQUM7SUFFRDs7T0FFRztJQUNLLDBCQUEwQixDQUFFLFVBQXlCO1FBQzVELE1BQU0sU0FBUyxHQUFHLENBQUMsSUFBYSxFQUFFLE1BQWdCLEVBQUUsRUFBRTtZQUNyRCwrREFBK0Q7WUFDL0QsOERBQThEO1lBQzdELElBQVksQ0FBQyxNQUFNLEdBQUcsTUFBTSxDQUFDO1lBQzlCLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxFQUFFLEtBQUssQ0FBQyxFQUFFLENBQUMsU0FBUyxDQUFDLEtBQUssRUFBRSxJQUFJLENBQUMsQ0FBQyxDQUFDO1FBQ3hELENBQUMsQ0FBQztRQUNGLFNBQVMsQ0FBQyxVQUFVLENBQUMsQ0FBQztJQUN2QixDQUFDO0lBRUQ7O09BRUc7SUFDSyxTQUFTLENBQUUsSUFBYSxFQUFFLFVBQXlCLEVBQUUsWUFBa0M7UUFDOUYsd0VBQXdFO1FBQ3hFLHdFQUF3RTtRQUN4RSxJQUFJLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ3hCLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNwQyxJQUFJLENBQUMsc0JBQXNCLENBQUMsSUFBSSxFQUFFLFVBQVUsQ0FBQyxDQUFDO1FBRTlDLDJCQUEyQjtRQUMzQixJQUFJLElBQUksQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUM3QixJQUFJLENBQUMsaUJBQWlCLENBQUMsSUFBeUIsRUFBRSxVQUFVLENBQUMsQ0FBQztRQUMvRCxDQUFDO1FBRUQseUJBQXlCO1FBQ3pCLElBQUksSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQzNCLElBQUksQ0FBQyxlQUFlLENBQUMsSUFBeUIsRUFBRSxVQUFVLENBQUMsQ0FBQztRQUM3RCxDQUFDO1FBRUQsaUNBQWlDO1FBQ2pDLElBQUksSUFBSSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDcEMsSUFBSSxDQUFDLHdCQUF3QixDQUFDLElBQW9CLEVBQUUsVUFBVSxFQUFFLFlBQVksQ0FBQyxDQUFDO1FBQy9FLENBQUM7UUFFRCw2REFBNkQ7UUFDN0QsSUFBSSxDQUFDLFlBQVksQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFFcEMsd0RBQXdEO1FBQ3hELElBQUksQ0FBQyxVQUFVLENBQUMsSUFBSSxFQUFFLFVBQVUsQ0FBQyxDQUFDO1FBRWxDLHVFQUF1RTtRQUN2RSxJQUFJLENBQUMsV0FBVyxDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsQ0FBQztRQUVuQyxrRUFBa0U7UUFDbEUsZ0RBQWdEO1FBQ2hELElBQUksQ0FBQyxzQkFBc0IsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFFOUMsc0VBQXNFO1FBQ3RFLHNFQUFzRTtRQUN0RSxJQUFJLENBQUMsOEJBQThCLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDMUMsSUFBSSxDQUFDLHlCQUF5QixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ3JDLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUN2QyxJQUFJLENBQUMsNkJBQTZCLENBQUMsSUFBSSxDQUFDLENBQUM7UUFFekMsZ0VBQWdFO1FBQ2hFLDhEQUE4RDtRQUM5RCxJQUFJLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDakQsTUFBTSxHQUFHLEdBQUcsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDdkQsSUFBSSxDQUFDLGdCQUFnQixDQUFDLEdBQUcsQ0FBQyxHQUFHLEVBQUUsSUFBSSxDQUFDLENBQUM7UUFDdEMsQ0FBQztRQUNELElBQ0MsRUFBRSxDQUFDLHFCQUFxQixDQUFDLElBQUksQ0FBQztZQUM5QixFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7WUFDMUIsSUFBSSxDQUFDLFdBQVc7WUFDaEIsQ0FBQyxFQUFFLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxXQUFXLENBQUMsSUFBSSxFQUFFLENBQUMsb0JBQW9CLENBQUMsSUFBSSxDQUFDLFdBQVcsQ0FBQyxDQUFDLEVBQ2xGLENBQUM7WUFDRixNQUFNLEdBQUcsR0FBRyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUN2RCxJQUFJLENBQUMsZ0JBQWdCLENBQUMsR0FBRyxDQUFDLEdBQUcsRUFBRSxJQUFJLENBQUMsV0FBVyxDQUFDLENBQUM7UUFDbEQsQ0FBQztRQUVELHVEQUF1RDtRQUN2RCxJQUFJLEVBQUUsQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ2pDLHdEQUF3RDtZQUN4RCxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksRUFBRSxLQUFLLENBQUMsRUFBRSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsS0FBSyxFQUFFLFVBQVUsRUFBRSxJQUFJLENBQUMsQ0FBQyxDQUFDO1FBQ3pFLENBQUM7YUFBTSxDQUFDO1lBQ1AsNkJBQTZCO1lBQzdCLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxFQUFFLEtBQUssQ0FBQyxFQUFFLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxLQUFLLEVBQUUsVUFBVSxFQUFFLFlBQVksQ0FBQyxDQUFDLENBQUM7UUFDakYsQ0FBQztJQUNGLENBQUM7SUFFRDs7O09BR0c7SUFDSyxZQUFZLENBQUUsSUFBYTtRQUNsQyxJQUFJLENBQUMsRUFBRSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDbkMsT0FBTztRQUNSLENBQUM7UUFFRCxNQUFNLEVBQUUsZUFBZSxFQUFFLEdBQUcsSUFBSSxDQUFDO1FBQ2pDLElBQUksQ0FBQyxFQUFFLENBQUMsZUFBZSxDQUFDLGVBQWUsQ0FBQyxJQUFJLGVBQWUsQ0FBQyxJQUFJLEtBQUssV0FBVyxFQUFFLENBQUM7WUFDbEYsT0FBTztRQUNSLENBQUM7UUFFRCxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsWUFBWSxDQUFDO1FBQ2pDLElBQUksQ0FBQyxNQUFNLEVBQUUsQ0FBQztZQUNiLE9BQU87UUFDUixDQUFDO1FBRUQsK0RBQStEO1FBQy9ELElBQUksTUFBTSxDQUFDLGFBQWEsSUFBSSxFQUFFLENBQUMsY0FBYyxDQUFDLE1BQU0sQ0FBQyxhQUFhLENBQUMsRUFBRSxDQUFDO1lBQ3JFLEtBQUssTUFBTSxPQUFPLElBQUksTUFBTSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsQ0FBQztnQkFDckQsTUFBTSxTQUFTLEdBQUcsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7Z0JBQ3BDLE1BQU0sWUFBWSxHQUFHLE9BQU8sQ0FBQyxZQUFZO29CQUN4QyxDQUFDLENBQUMsT0FBTyxDQUFDLFlBQVksQ0FBQyxJQUFJO29CQUMzQixDQUFDLENBQUMsU0FBUyxDQUFDO2dCQUNiLElBQUksWUFBWSxLQUFLLFdBQVcsRUFBRSxDQUFDO29CQUNsQyxJQUFJLENBQUMscUJBQXFCLENBQUMsR0FBRyxDQUFDLFNBQVMsQ0FBQyxDQUFDO2dCQUMzQyxDQUFDO2dCQUNELElBQUksWUFBWSxLQUFLLHVCQUF1QixFQUFFLENBQUM7b0JBQzlDLElBQUksQ0FBQyw4QkFBOEIsQ0FBQyxHQUFHLENBQUMsU0FBUyxDQUFDLENBQUM7Z0JBQ3BELENBQUM7Z0JBQ0QsSUFBSSxXQUFXLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMseUJBQXlCLENBQUMsQ0FBQztnQkFDakYsSUFBSSxDQUFDLFdBQVcsRUFBRSxDQUFDO29CQUNsQixXQUFXLEdBQUcsSUFBSSxHQUFHLEVBQWtCLENBQUM7b0JBQ3hDLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLHlCQUF5QixFQUFFLFdBQVcsQ0FBQyxDQUFDO2dCQUM3RSxDQUFDO2dCQUNELFdBQVcsQ0FBQyxHQUFHLENBQUMsU0FBUyxFQUFFLFlBQVksQ0FBQyxDQUFDO1lBQzFDLENBQUM7UUFDRixDQUFDO1FBRUQseUNBQXlDO1FBQ3pDLElBQUksTUFBTSxDQUFDLGFBQWEsSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsTUFBTSxDQUFDLGFBQWEsQ0FBQyxFQUFFLENBQUM7WUFDeEUsSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxNQUFNLENBQUMsYUFBYSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNoRSxDQUFDO1FBRUQsa0ZBQWtGO1FBQ2xGLElBQUksTUFBTSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ2pCLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNsRCxDQUFDO0lBQ0YsQ0FBQztJQUVEOzs7T0FHRztJQUNLLDhCQUE4QixDQUFFLElBQWE7UUFDcEQsNkRBQTZEO1FBQzdELGlFQUFpRTtRQUNqRSxnRUFBZ0U7UUFDaEUsa0NBQWtDO1FBQ2xDLElBQUksRUFBRSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztZQUM3RCxJQUFJLENBQUMsSUFBSSxJQUFJLEVBQUUsQ0FBQyxhQUFhLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDM0MsTUFBTSxpQkFBaUIsR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUM7WUFDekQsSUFBSSxVQUFVLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLEdBQUcsQ0FBQyxpQkFBaUIsQ0FBQyxDQUFDO1lBQ3RFLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztnQkFDakIsVUFBVSxHQUFHLElBQUksR0FBRyxFQUFnQyxDQUFDO2dCQUNyRCxJQUFJLENBQUMsd0JBQXdCLENBQUMsR0FBRyxDQUFDLGlCQUFpQixFQUFFLFVBQVUsQ0FBQyxDQUFDO1lBQ2xFLENBQUM7WUFDRCxVQUFVLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxDQUFDO1lBQ3JDLE9BQU87UUFDUixDQUFDO1FBRUQsSUFBSSxJQUFJLEdBQUcsRUFBRSxDQUFDO1FBQ2QsSUFBSSxJQUFtRCxDQUFDO1FBQ3hELElBQUksUUFBdUQsQ0FBQztRQUU1RCxJQUFJLEVBQUUsQ0FBQyxzQkFBc0IsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ25FLElBQUksR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztZQUN0QixJQUFJLEdBQUcsT0FBTyxDQUFDO1lBQ2YsUUFBUSxHQUFHLElBQUksQ0FBQztRQUNqQixDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsa0JBQWtCLENBQUMsSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ3JELElBQUksR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztZQUN0QixJQUFJLEdBQUcsT0FBTyxDQUFDO1lBQ2YsUUFBUSxHQUFHLElBQUksQ0FBQztRQUNqQixDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsc0JBQXNCLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUMxRSxJQUFJLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7WUFDdEIsSUFBSSxHQUFHLFdBQVcsQ0FBQztZQUNuQixRQUFRLEdBQUcsSUFBSSxDQUFDO1FBQ2pCLENBQUM7UUFFRCxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsUUFBUSxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDakMsT0FBTztRQUNSLENBQUM7UUFFRCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUM7UUFDaEQsSUFBSSxLQUFLLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsQ0FBQztRQUNuRCxJQUFJLENBQUMsS0FBSyxFQUFFLENBQUM7WUFDWixLQUFLLEdBQUcsSUFBSSxHQUFHLEVBQXFDLENBQUM7WUFDckQsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsS0FBSyxDQUFDLENBQUM7UUFDL0MsQ0FBQztRQUNELE1BQU0sS0FBSyxHQUE4QixFQUFFLElBQUksRUFBRSxJQUFJLEVBQUcsUUFBUSxFQUFFLElBQUksRUFBRyxRQUFRLEVBQUUsQ0FBQztRQUNwRixLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxLQUFLLENBQUMsQ0FBQztRQUV2QixzRUFBc0U7UUFDdEUsZ0NBQWdDO1FBQ2hDLElBQUksSUFBSSxLQUFLLE9BQU8sRUFBRSxDQUFDO1lBQ3RCLE1BQU0sU0FBUyxHQUFHLFFBQStCLENBQUM7WUFDbEQsTUFBTSxVQUFVLEdBQUcsU0FBUyxDQUFDLFNBQVMsRUFBRSxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsYUFBYSxDQUFDLElBQUksS0FBSyxDQUFDO1lBQ25HLE1BQU0sU0FBUyxHQUFHLFNBQVMsQ0FBQyxTQUFTLEVBQUUsSUFBSSxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGNBQWMsQ0FBQyxJQUFJLEtBQUssQ0FBQztZQUNuRyxJQUFJLFVBQVUsSUFBSSxTQUFTLEVBQUUsQ0FBQztnQkFDN0IsS0FBSyxDQUFDLEdBQUcsQ0FBQyxTQUFTLEVBQUUsS0FBSyxDQUFDLENBQUM7WUFDN0IsQ0FBQztRQUNGLENBQUM7SUFDRixDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNLLDZCQUE2QixDQUFFLElBQWE7UUFDbkQsSUFBSSxDQUFDLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLFdBQVcsRUFBRSxDQUFDO1lBQ3pGLE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxFQUFFLFdBQVcsRUFBRSxjQUFjLEVBQUUsR0FBRyxJQUFJLENBQUM7UUFDN0MsSUFBSSxXQUFXLEdBQWtCLGNBQWMsQ0FBQztRQUNoRCxPQUNDLEVBQUUsQ0FBQyxjQUFjLENBQUMsV0FBVyxDQUFDO1lBQzlCLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxXQUFXLENBQUM7WUFDckMsNkRBQTZEO1lBQzdELHVEQUF1RDtZQUN2RCxFQUFFLENBQUMseUJBQXlCLENBQUMsV0FBVyxDQUFDLEVBQ3hDLENBQUM7WUFDRixXQUFXLEdBQUcsV0FBVyxDQUFDLFVBQVUsQ0FBQztRQUN0QyxDQUFDO1FBQ0QsSUFBSSxDQUFDLEVBQUUsQ0FBQyx3QkFBd0IsQ0FBQyxXQUFXLENBQUMsRUFBRSxDQUFDO1lBQy9DLE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDO1FBQ2hELElBQUksTUFBTSxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLENBQUM7UUFDMUQsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDO1lBQ2IsTUFBTSxHQUFHLElBQUksR0FBRyxFQUFxQyxDQUFDO1lBQ3RELElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxFQUFFLE1BQU0sQ0FBQyxDQUFDO1FBQ3RELENBQUM7UUFDRCxJQUFJLENBQUMsTUFBTSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDakMsTUFBTSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxXQUFXLENBQUMsQ0FBQztRQUN6QyxDQUFDO0lBQ0YsQ0FBQztJQUVEOzs7Ozs7T0FNRztJQUNLLHdCQUF3QixDQUMvQixJQUFZLEVBQ1osUUFBZ0I7UUFFaEIsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsRUFBRSxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDdEUsSUFBSSxLQUFLLEVBQUUsQ0FBQztZQUNYLE9BQU8sS0FBSyxDQUFDO1FBQ2QsQ0FBQztRQUNELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ3JFLElBQUksQ0FBQyxRQUFRLElBQUksUUFBUSxDQUFDLFdBQVcsRUFBRSxDQUFDO1lBQ3ZDLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsMkJBQTJCLENBQUMsUUFBUSxDQUFDLFNBQVMsRUFBRSxRQUFRLENBQUMsQ0FBQztRQUNsRixJQUFJLENBQUMsVUFBVSxJQUFJLFVBQVUsQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUMxQyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBQ0QsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsWUFBWSxDQUFDLEVBQUUsR0FBRyxDQUFDLFFBQVEsQ0FBQyxZQUFZLENBQUMsQ0FBQztRQUN0RyxPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7SUFFRDs7Ozs7OztPQU9HO0lBQ0ssbUJBQW1CLENBQUUsWUFBdUM7UUFDbkUsTUFBTSxRQUFRLEdBQWEsRUFBRSxDQUFDO1FBQzlCLEtBQUssTUFBTSxPQUFPLElBQUksWUFBWSxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQzdDLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO2dCQUNqQyxPQUFPLFNBQVMsQ0FBQztZQUNsQixDQUFDO1lBQ0QsTUFBTSxPQUFPLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLE9BQU8sQ0FBQyxDQUFDO1lBQ3RELElBQUksT0FBTyxLQUFLLFNBQVMsRUFBRSxDQUFDO2dCQUMzQixPQUFPLFNBQVMsQ0FBQztZQUNsQixDQUFDO1lBQ0QsUUFBUSxDQUFDLElBQUksQ0FBQyxPQUFPLENBQUMsQ0FBQztRQUN4QixDQUFDO1FBQ0QsSUFBSSxRQUFRLENBQUMsTUFBTSxLQUFLLENBQUMsRUFBRSxDQUFDO1lBQzNCLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLE1BQU0sR0FBRyxRQUFRLENBQUM7UUFDeEIsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7Ozs7O09BS0c7SUFDSyx1QkFBdUIsQ0FBRSxJQUFtQjtRQUNuRCxJQUFJLEtBQUssR0FBa0IsSUFBSSxDQUFDO1FBQ2hDLE9BQU8sRUFBRSxDQUFDLGNBQWMsQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLENBQUMscUJBQXFCLENBQUMsS0FBSyxDQUFDLElBQUksRUFBRSxDQUFDLHlCQUF5QixDQUFDLEtBQUssQ0FBQyxFQUFFLENBQUM7WUFDM0csS0FBSyxHQUFHLEtBQUssQ0FBQyxVQUFVLENBQUM7UUFDMUIsQ0FBQztRQUNELElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLENBQUMsK0JBQStCLENBQUMsS0FBSyxDQUFDLEVBQUUsQ0FBQztZQUM1RSxNQUFNLE9BQU8sR0FBRyxJQUFJLEtBQUssQ0FBQyxJQUFJLEdBQUcsQ0FBQztZQUNsQyxPQUFPLE9BQU8sQ0FBQztRQUNoQixDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsdUJBQXVCLENBQUMsS0FBSyxDQUFDLElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLEtBQUssQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO1lBQzdFLElBQUksS0FBSyxDQUFDLFFBQVEsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFVBQVUsRUFBRSxDQUFDO2dCQUNqRCxNQUFNLFFBQVEsR0FBRyxJQUFJLEtBQUssQ0FBQyxPQUFPLENBQUMsSUFBSSxFQUFFLENBQUM7Z0JBQzFDLE9BQU8sUUFBUSxDQUFDO1lBQ2pCLENBQUM7WUFDRCxJQUFJLEtBQUssQ0FBQyxRQUFRLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxTQUFTLEVBQUUsQ0FBQztnQkFDaEQsT0FBTyxLQUFLLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQztZQUMzQixDQUFDO1lBQ0QsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLEtBQUssQ0FBQyxFQUFFLENBQUM7WUFDaEMsT0FBTyxLQUFLLENBQUMsSUFBSSxDQUFDO1FBQ25CLENBQUM7UUFDRCxJQUFJLEtBQUssQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxXQUFXLEVBQUUsQ0FBQztZQUM5QyxPQUFPLE1BQU0sQ0FBQztRQUNmLENBQUM7UUFDRCxJQUFJLEtBQUssQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxZQUFZLEVBQUUsQ0FBQztZQUMvQyxPQUFPLE9BQU8sQ0FBQztRQUNoQixDQUFDO1FBQ0QsSUFBSSxLQUFLLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVyxFQUFFLENBQUM7WUFDOUMsT0FBTyxNQUFNLENBQUM7UUFDZixDQUFDO1FBQ0QsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7OztPQUtHO0lBQ0ssb0JBQW9CLENBQUUsSUFBaUI7UUFDOUMsTUFBTSxjQUFjLEdBQUcsRUFBRSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQztZQUNsRCxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUM7WUFDOUIsSUFBSSxDQUFDLFFBQVEsQ0FBQyxJQUFJLEtBQUssT0FBTyxDQUFDO1FBQ2hDLE9BQU8sY0FBYyxDQUFDO0lBQ3ZCLENBQUM7SUFFRDs7Ozs7O09BTUc7SUFDSyxtQkFBbUIsQ0FBRSxJQUFtQjtRQUMvQyxJQUFJLE9BQU8sR0FBa0IsSUFBSSxDQUFDO1FBQ2xDLE9BQU8sRUFBRSxDQUFDLHlCQUF5QixDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7WUFDOUMsT0FBTyxHQUFHLE9BQU8sQ0FBQyxVQUFVLENBQUM7UUFDOUIsQ0FBQztRQUNELElBQUksRUFBRSxDQUFDLHdCQUF3QixDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7WUFDMUMsT0FBTyxPQUFPLENBQUM7UUFDaEIsQ0FBQztRQUNELElBQUksQ0FBQyxFQUFFLENBQUMsY0FBYyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsQ0FBQyx5QkFBeUIsQ0FBQyxPQUFPLENBQUMsQ0FBQztZQUN4RSxJQUFJLENBQUMsb0JBQW9CLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDMUMsTUFBTSxLQUFLLEdBQUcsT0FBTyxDQUFDLFVBQVUsQ0FBQztZQUNqQyxNQUFNLE9BQU8sR0FBRyxFQUFFLENBQUMsd0JBQXdCLENBQUMsS0FBSyxDQUFDLENBQUMsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLENBQUMsU0FBUyxDQUFDO1lBQ3ZFLE9BQU8sT0FBTyxDQUFDO1FBQ2hCLENBQUM7UUFDRCxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsT0FBTyxDQUFDLEVBQUUsQ0FBQztZQUM5QixNQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDdEcsT0FBTyxPQUFPLENBQUM7UUFDaEIsQ0FBQztRQUNELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7Ozs7OztPQU9HO0lBQ0sscUJBQXFCLENBQUUsSUFBWSxFQUFFLFFBQWdCO1FBQzVELE1BQU0sWUFBWSxHQUFHLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxJQUFJLEVBQUUsUUFBUSxDQUFDLENBQUM7UUFDbkUsSUFBSSxDQUFDLFlBQVksRUFBRSxDQUFDO1lBQ25CLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsWUFBWSxDQUFDLENBQUM7UUFDeEQsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQ2YsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELE1BQU0sS0FBSyxHQUFHLFFBQVEsQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7UUFDbkMsT0FBTyxLQUFLLENBQUM7SUFDZCxDQUFDO0lBRUQ7Ozs7T0FJRztJQUNLLHlCQUF5QixDQUFFLElBQWE7UUFDL0MsSUFBSSxDQUFDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ25DLE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxFQUFFLGVBQWUsRUFBRSxHQUFHLElBQUksQ0FBQztRQUNqQyxJQUFJLENBQUMsRUFBRSxDQUFDLGVBQWUsQ0FBQyxlQUFlLENBQUMsRUFBRSxDQUFDO1lBQzFDLE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLFlBQVksQ0FBQztRQUNqQyxJQUFJLENBQUMsTUFBTSxFQUFFLENBQUM7WUFDYixPQUFPO1FBQ1IsQ0FBQztRQUVELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQztRQUNoRCxJQUFJLE9BQU8sR0FBRyxJQUFJLENBQUMscUJBQXFCLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxDQUFDO1FBQ3ZELElBQUksQ0FBQyxPQUFPLEVBQUUsQ0FBQztZQUNkLE9BQU8sR0FBRyxJQUFJLEdBQUcsRUFBZ0MsQ0FBQztZQUNsRCxJQUFJLENBQUMscUJBQXFCLENBQUMsR0FBRyxDQUFDLFFBQVEsRUFBRSxPQUFPLENBQUMsQ0FBQztRQUNuRCxDQUFDO1FBRUQseUVBQXlFO1FBQ3pFLElBQUksTUFBTSxDQUFDLGFBQWEsSUFBSSxFQUFFLENBQUMsY0FBYyxDQUFDLE1BQU0sQ0FBQyxhQUFhLENBQUMsRUFBRSxDQUFDO1lBQ3JFLEtBQUssTUFBTSxPQUFPLElBQUksTUFBTSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsQ0FBQztnQkFDckQsTUFBTSxTQUFTLEdBQUcsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7Z0JBQ3BDLE1BQU0sWUFBWSxHQUFHLE9BQU8sQ0FBQyxZQUFZLENBQUMsQ0FBQyxDQUFDLE9BQU8sQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUM7Z0JBQ2xGLE9BQU8sQ0FBQyxHQUFHLENBQUMsU0FBUyxFQUFFO29CQUN0QixZQUFZO29CQUNaLFNBQVMsRUFBSyxlQUFlLENBQUMsSUFBSTtvQkFDbEMsV0FBVyxFQUFHLEtBQUs7aUJBQ25CLENBQUMsQ0FBQztZQUNKLENBQUM7UUFDRixDQUFDO1FBRUQsK0RBQStEO1FBQy9ELHNDQUFzQztRQUN0QyxJQUFJLE1BQU0sQ0FBQyxhQUFhLElBQUksRUFBRSxDQUFDLGlCQUFpQixDQUFDLE1BQU0sQ0FBQyxhQUFhLENBQUMsRUFBRSxDQUFDO1lBQ3hFLE9BQU8sQ0FBQyxHQUFHLENBQUMsTUFBTSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFO2dCQUMzQyxZQUFZLEVBQUcsRUFBRTtnQkFDakIsU0FBUyxFQUFNLGVBQWUsQ0FBQyxJQUFJO2dCQUNuQyxXQUFXLEVBQUksSUFBSTthQUNuQixDQUFDLENBQUM7UUFDSixDQUFDO1FBRUQsK0NBQStDO1FBQy9DLElBQUksTUFBTSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ2pCLE9BQU8sQ0FBQyxHQUFHLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUU7Z0JBQzdCLFlBQVksRUFBRyxTQUFTO2dCQUN4QixTQUFTLEVBQU0sZUFBZSxDQUFDLElBQUk7Z0JBQ25DLFdBQVcsRUFBSSxLQUFLO2FBQ3BCLENBQUMsQ0FBQztRQUNKLENBQUM7SUFDRixDQUFDO0lBRUQ7Ozs7T0FJRztJQUNLLDJCQUEyQixDQUFFLElBQWE7UUFDakQsSUFBSSxDQUFDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ25DLE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDO1FBQ2hELE1BQU0sRUFBRSxlQUFlLEVBQUUsR0FBRyxJQUFJLENBQUM7UUFDakMsTUFBTSxhQUFhLEdBQUcsZUFBZSxJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsZUFBZSxDQUFDO1lBQzNFLENBQUMsQ0FBQyxlQUFlLENBQUMsSUFBSTtZQUN0QixDQUFDLENBQUMsU0FBUyxDQUFDO1FBRWIsSUFBSSxJQUFJLENBQUMsWUFBWSxJQUFJLEVBQUUsQ0FBQyxjQUFjLENBQUMsSUFBSSxDQUFDLFlBQVksQ0FBQyxFQUFFLENBQUM7WUFDL0QsS0FBSyxNQUFNLE9BQU8sSUFBSSxJQUFJLENBQUMsWUFBWSxDQUFDLFFBQVEsRUFBRSxDQUFDO2dCQUNsRCxNQUFNLFlBQVksR0FBRyxPQUFPLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztnQkFDdkMsTUFBTSxTQUFTLEdBQUcsT0FBTyxDQUFDLFlBQVksQ0FBQyxDQUFDLENBQUMsT0FBTyxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLFlBQVksQ0FBQztnQkFDbEYsSUFBSSxhQUFhLEVBQUUsQ0FBQztvQkFDbkIscURBQXFEO29CQUNyRCxJQUFJLFNBQVMsR0FBRyxJQUFJLENBQUMsdUJBQXVCLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxDQUFDO29CQUMzRCxJQUFJLENBQUMsU0FBUyxFQUFFLENBQUM7d0JBQ2hCLFNBQVMsR0FBRyxJQUFJLEdBQUcsRUFBa0IsQ0FBQzt3QkFDdEMsSUFBSSxDQUFDLHVCQUF1QixDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsU0FBUyxDQUFDLENBQUM7b0JBQ3ZELENBQUM7b0JBQ0QsU0FBUyxDQUFDLEdBQUcsQ0FBQyxZQUFZLEVBQUUsYUFBYSxDQUFDLENBQUM7Z0JBQzVDLENBQUM7cUJBQU0sSUFBSSxTQUFTLEtBQUssWUFBWSxFQUFFLENBQUM7b0JBQ3ZDLDZEQUE2RDtvQkFDN0QsSUFBSSxPQUFPLEdBQUcsSUFBSSxDQUFDLDJCQUEyQixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsQ0FBQztvQkFDN0QsSUFBSSxDQUFDLE9BQU8sRUFBRSxDQUFDO3dCQUNkLE9BQU8sR0FBRyxJQUFJLEdBQUcsRUFBa0IsQ0FBQzt3QkFDcEMsSUFBSSxDQUFDLDJCQUEyQixDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsT0FBTyxDQUFDLENBQUM7b0JBQ3pELENBQUM7b0JBQ0QsT0FBTyxDQUFDLEdBQUcsQ0FBQyxZQUFZLEVBQUUsU0FBUyxDQUFDLENBQUM7Z0JBQ3RDLENBQUM7WUFDRixDQUFDO1lBQ0QsT0FBTztRQUNSLENBQUM7UUFFRCxJQUFJLElBQUksQ0FBQyxZQUFZLElBQUksRUFBRSxDQUFDLGlCQUFpQixDQUFDLElBQUksQ0FBQyxZQUFZLENBQUMsRUFBRSxDQUFDO1lBQ2xFLGdFQUFnRTtZQUNoRSxpRUFBaUU7WUFDakUsSUFBSSxhQUFhLEVBQUUsQ0FBQztnQkFDbkIsSUFBSSxLQUFLLEdBQUcsSUFBSSxDQUFDLDRCQUE0QixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsQ0FBQztnQkFDNUQsSUFBSSxDQUFDLEtBQUssRUFBRSxDQUFDO29CQUNaLEtBQUssR0FBRyxJQUFJLEdBQUcsRUFBa0IsQ0FBQztvQkFDbEMsSUFBSSxDQUFDLDRCQUE0QixDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsS0FBSyxDQUFDLENBQUM7Z0JBQ3hELENBQUM7Z0JBQ0QsS0FBSyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsYUFBYSxDQUFDLENBQUM7WUFDdkQsQ0FBQztZQUNELE9BQU87UUFDUixDQUFDO1FBRUQsSUFBSSxDQUFDLElBQUksQ0FBQyxZQUFZLElBQUksYUFBYSxFQUFFLENBQUM7WUFDekMsb0JBQW9CO1lBQ3BCLElBQUksS0FBSyxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLENBQUM7WUFDekQsSUFBSSxDQUFDLEtBQUssRUFBRSxDQUFDO2dCQUNaLEtBQUssR0FBRyxFQUFFLENBQUM7Z0JBQ1gsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsS0FBSyxDQUFDLENBQUM7WUFDckQsQ0FBQztZQUNELEtBQUssQ0FBQyxJQUFJLENBQUMsYUFBYSxDQUFDLENBQUM7UUFDM0IsQ0FBQztJQUNGLENBQUM7SUFFRDs7OztPQUlHO0lBQ0ssMkJBQTJCLENBQUUsU0FBaUIsRUFBRSxjQUFzQjtRQUU3RSxNQUFNLFFBQVEsR0FBRyxHQUFHLGNBQWMsS0FBSyxTQUFTLEVBQUUsQ0FBQztRQUNuRCxJQUFJLElBQUksQ0FBQyw2QkFBNkIsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUN0RCxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsNkJBQTZCLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxDQUFDO1lBQ2hFLE9BQU8sTUFBTSxLQUFLLFNBQVMsQ0FBQyxDQUFDLENBQUMsU0FBUyxDQUFDLENBQUMsQ0FBQyxNQUFNLENBQUM7UUFDbEQsQ0FBQztRQUVELE1BQU0sVUFBVSxHQUFHLEVBQUUsQ0FBQyxpQkFBaUIsQ0FDdEMsU0FBUyxFQUNULGNBQWMsRUFDZCxJQUFJLENBQUMsNkJBQTZCLEVBQ2xDLEVBQUUsQ0FBQyxHQUFHLENBQ04sQ0FBQyxjQUFjLENBQUM7UUFFakIsTUFBTSxNQUFNLEdBQXlDLFVBQVU7WUFDOUQsQ0FBQyxDQUFDO2dCQUNELFlBQVksRUFBRyxRQUFRLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxnQkFBZ0IsQ0FBQztnQkFDNUQsVUFBVSxFQUFLLENBQUMsQ0FBQyxVQUFVLENBQUMsdUJBQXVCO2FBQ25EO1lBQ0QsQ0FBQyxDQUFDLFNBQVMsQ0FBQztRQUViLElBQUksQ0FBQyw2QkFBNkIsQ0FBQyxHQUFHLENBQUMsUUFBUSxFQUFFLE1BQU0sQ0FBQyxDQUFDO1FBQ3pELE1BQU0sV0FBVyxHQUFHLE1BQU0sQ0FBQztRQUMzQixPQUFPLFdBQVcsQ0FBQztJQUNwQixDQUFDO0lBRUQ7Ozs7T0FJRztJQUNLLDBCQUEwQixDQUNqQyxVQUFrQixFQUNsQixJQUFZLEVBQ1osS0FBYTtRQUViLElBQUksS0FBSyxHQUFHLHdCQUF3QixFQUFFLENBQUM7WUFDdEMsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxHQUFHLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDdkQsTUFBTSxNQUFNLEdBQUcsS0FBSyxFQUFFLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNoQyxJQUFJLE1BQU0sRUFBRSxDQUFDO1lBQ1osT0FBTyxNQUFNLENBQUM7UUFDZixDQUFDO1FBQ0QscURBQXFEO1FBQ3JELE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxHQUFHLENBQUMsVUFBVSxDQUFDLEVBQUUsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQy9FLElBQUksVUFBVSxFQUFFLENBQUM7WUFDaEIsTUFBTSxPQUFPLEdBQUcsS0FBSyxFQUFFLEdBQUcsQ0FBQyxVQUFVLENBQUMsQ0FBQztZQUN2QyxJQUFJLE9BQU8sRUFBRSxDQUFDO2dCQUNiLE9BQU8sT0FBTyxDQUFDO1lBQ2hCLENBQUM7UUFDRixDQUFDO1FBRUQsTUFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsQ0FBQztRQUMvRCxNQUFNLGlCQUFpQixHQUFHLFNBQVMsRUFBRSxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDL0MsSUFBSSxpQkFBaUIsRUFBRSxDQUFDO1lBQ3ZCLE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxpQkFBaUIsRUFBRSxVQUFVLENBQUMsQ0FBQztZQUN2RixJQUFJLGNBQWMsSUFBSSxDQUFDLGNBQWMsQ0FBQyxVQUFVLEVBQUUsQ0FBQztnQkFDbEQsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLDBCQUEwQixDQUFDLGNBQWMsQ0FBQyxZQUFZLEVBQUUsSUFBSSxFQUFFLEtBQUssR0FBRyxDQUFDLENBQUMsQ0FBQztnQkFDNUYsSUFBSSxLQUFLLEVBQUUsQ0FBQztvQkFDWCxPQUFPLEtBQUssQ0FBQztnQkFDZCxDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFFRCxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUMsR0FBRyxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQzdELElBQUksS0FBSyxFQUFFLENBQUM7WUFDWCxLQUFLLE1BQU0sYUFBYSxJQUFJLEtBQUssRUFBRSxDQUFDO2dCQUNuQyxNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsMkJBQTJCLENBQUMsYUFBYSxFQUFFLFVBQVUsQ0FBQyxDQUFDO2dCQUNuRixJQUFJLENBQUMsY0FBYyxJQUFJLGNBQWMsQ0FBQyxVQUFVLEVBQUUsQ0FBQztvQkFDbEQsU0FBUztnQkFDVixDQUFDO2dCQUNELE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQywwQkFBMEIsQ0FBQyxjQUFjLENBQUMsWUFBWSxFQUFFLElBQUksRUFBRSxLQUFLLEdBQUcsQ0FBQyxDQUFDLENBQUM7Z0JBQzVGLElBQUksS0FBSyxFQUFFLENBQUM7b0JBQ1gsT0FBTyxLQUFLLENBQUM7Z0JBQ2QsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7Ozs7OztPQVFHO0lBQ0ssZ0NBQWdDLENBQ3ZDLElBQVksRUFDWixRQUFnQjtRQUVoQixtRUFBbUU7UUFDbkUsOERBQThEO1FBQzlELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ3JFLElBQUksUUFBUSxJQUFJLENBQUMsUUFBUSxDQUFDLFdBQVcsRUFBRSxDQUFDO1lBQ3ZDLE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxRQUFRLENBQUMsU0FBUyxFQUFFLFFBQVEsQ0FBQyxDQUFDO1lBQ2xGLElBQUksVUFBVSxJQUFJLENBQUMsVUFBVSxDQUFDLFVBQVUsRUFBRSxDQUFDO2dCQUMxQyxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMsMEJBQTBCLENBQUMsVUFBVSxDQUFDLFlBQVksRUFBRSxRQUFRLENBQUMsWUFBWSxFQUFFLENBQUMsQ0FBQyxDQUFDO2dCQUNqRyxJQUFJLEtBQUssRUFBRSxDQUFDO29CQUNYLE9BQU8sS0FBSyxDQUFDO2dCQUNkLENBQUM7WUFDRixDQUFDO1FBQ0YsQ0FBQztRQUVELHNEQUFzRDtRQUN0RCxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNoRSxJQUFJLEtBQUssRUFBRSxDQUFDO1lBQ1gsT0FBTyxLQUFLLENBQUM7UUFDZCxDQUFDO1FBRUQsb0VBQW9FO1FBQ3BFLDZEQUE2RDtRQUM3RCw2REFBNkQ7UUFDN0QsMkRBQTJEO1FBQzNELDZEQUE2RDtRQUM3RCw4REFBOEQ7UUFDOUQsdUNBQXVDO1FBQ3ZDLElBQUksTUFBNkMsQ0FBQztRQUNsRCxJQUFJLEtBQUssR0FBRyxDQUFDLENBQUM7UUFDZCxLQUFLLE1BQU0sQ0FBRSxRQUFRLEVBQUUsS0FBSyxDQUFFLElBQUksSUFBSSxDQUFDLG1CQUFtQixFQUFFLENBQUM7WUFDNUQsSUFBSSxJQUFJLENBQUMsa0JBQWtCLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztnQkFDdkMsU0FBUztZQUNWLENBQUM7WUFDRCxNQUFNLFNBQVMsR0FBRyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ2xDLElBQUksU0FBUyxFQUFFLENBQUM7Z0JBQ2YsS0FBSyxFQUFFLENBQUM7Z0JBQ1IsTUFBTSxHQUFHLFNBQVMsQ0FBQztnQkFDbkIsSUFBSSxLQUFLLEdBQUcsQ0FBQyxFQUFFLENBQUM7b0JBQ2YsT0FBTyxTQUFTLENBQUM7Z0JBQ2xCLENBQUM7WUFDRixDQUFDO1FBQ0YsQ0FBQztRQUVELE1BQU0sTUFBTSxHQUFHLEtBQUssS0FBSyxDQUFDLENBQUMsQ0FBQyxDQUFDLE1BQU0sQ0FBQyxDQUFDLENBQUMsU0FBUyxDQUFDO1FBQ2hELE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7Ozs7T0FNRztJQUNLLGtCQUFrQixDQUFFLElBQVk7UUFDdkMsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLFFBQVEsQ0FBQyxPQUFPLENBQUM7WUFDdEMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLFFBQVEsQ0FBQyxHQUFHLGVBQWUsUUFBUSxDQUFDLEdBQUcsRUFBRSxDQUFDLENBQUM7UUFDN0QsT0FBTyxRQUFRLENBQUM7SUFDakIsQ0FBQztJQUVEOzs7Ozs7T0FNRztJQUNLLCtCQUErQixDQUFFLElBQStCO1FBRXZFLE1BQU0sT0FBTyxHQUFHLElBQUksR0FBRyxFQUFVLENBQUM7UUFDbEMsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLG9DQUFvQyxDQUFDLElBQUksRUFBRSxPQUFPLEVBQUUsQ0FBQyxDQUFDLENBQUM7UUFDL0UsT0FBTyxVQUFVLENBQUM7SUFDbkIsQ0FBQztJQUVPLG9DQUFvQyxDQUMzQyxJQUErQixFQUMvQixPQUFvQixFQUNwQixLQUFhO1FBRWIsTUFBTSxhQUFhLEdBQUcsSUFBSSxHQUFHLEVBQXdCLENBQUM7UUFDdEQsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLElBQXFELENBQUM7UUFDNUUsTUFBTSxRQUFRLEdBQUcsUUFBUSxDQUFDLElBQUksSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFFBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQztRQUMzRixNQUFNLFFBQVEsR0FBRyxHQUFHLElBQUksQ0FBQyxJQUFJLElBQUksSUFBSSxDQUFDLElBQUksSUFBSSxRQUFRLEVBQUUsQ0FBQztRQUN6RCxJQUFJLEtBQUssR0FBRyxrQkFBa0IsSUFBSSxPQUFPLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDekQsT0FBTyxhQUFhLENBQUM7UUFDdEIsQ0FBQztRQUNELE9BQU8sQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLENBQUM7UUFFdEIsSUFBSSxJQUFJLENBQUMsSUFBSSxLQUFLLE9BQU8sRUFBRSxDQUFDO1lBQzNCLE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQyxzQkFBc0IsQ0FBQyxJQUFJLENBQUMsSUFBMkIsQ0FBQyxDQUFDO1lBQ2pGLEtBQUssTUFBTSxDQUFFLElBQUksRUFBRSxJQUFJLENBQUUsSUFBSSxVQUFVLEVBQUUsQ0FBQztnQkFDekMsYUFBYSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLENBQUM7WUFDL0IsQ0FBQztRQUNGLENBQUM7YUFBTSxJQUFJLElBQUksQ0FBQyxJQUFJLEtBQUssV0FBVyxFQUFFLENBQUM7WUFDdEMsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLElBQStCLENBQUM7WUFDbkQsSUFBSSxDQUFDLDRCQUE0QixDQUFDLENBQUUsR0FBRyxLQUFLLENBQUMsT0FBTyxDQUFFLEVBQUUsYUFBYSxDQUFDLENBQUM7UUFDeEUsQ0FBQzthQUFNLENBQUM7WUFDUCxNQUFNLFNBQVMsR0FBSSxJQUFJLENBQUMsSUFBZ0MsQ0FBQyxJQUFJLENBQUM7WUFDOUQsSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsU0FBUyxDQUFDLEVBQUUsQ0FBQztnQkFDckMsSUFBSSxDQUFDLDRCQUE0QixDQUFDLENBQUUsR0FBRyxTQUFTLENBQUMsT0FBTyxDQUFFLEVBQUUsYUFBYSxDQUFDLENBQUM7WUFDNUUsQ0FBQztpQkFBTSxDQUFDO2dCQUNQLE9BQU8sYUFBYSxDQUFDO1lBQ3RCLENBQUM7UUFDRixDQUFDO1FBRUQsb0VBQW9FO1FBQ3BFLDZEQUE2RDtRQUM3RCxNQUFNLE1BQU0sR0FBRyxJQUFJLEdBQUcsRUFBd0IsQ0FBQztRQUMvQyxLQUFLLE1BQU0sUUFBUSxJQUFJLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQy9ELE1BQU0sU0FBUyxHQUFHLElBQUksQ0FBQyxvQ0FBb0MsQ0FBQyxRQUFRLEVBQUUsT0FBTyxFQUFFLEtBQUssR0FBRyxDQUFDLENBQUMsQ0FBQztZQUMxRixLQUFLLE1BQU0sQ0FBRSxJQUFJLEVBQUUsSUFBSSxDQUFFLElBQUksU0FBUyxFQUFFLENBQUM7Z0JBQ3hDLE1BQU0sQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxDQUFDO1lBQ3hCLENBQUM7UUFDRixDQUFDO1FBQ0QsS0FBSyxNQUFNLENBQUUsSUFBSSxFQUFFLElBQUksQ0FBRSxJQUFJLGFBQWEsRUFBRSxDQUFDO1lBQzVDLE1BQU0sQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxDQUFDO1FBQ3hCLENBQUM7UUFDRCxPQUFPLE1BQU0sQ0FBQztJQUNmLENBQUM7SUFFRDs7O09BR0c7SUFDSyw0QkFBNEIsQ0FDbkMsT0FBa0MsRUFDbEMsVUFBcUM7UUFFckMsS0FBSyxNQUFNLE1BQU0sSUFBSSxPQUFPLEVBQUUsQ0FBQztZQUM5QixJQUFJLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxNQUFNLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUNwRSxNQUFNLFFBQVEsR0FBRyxNQUFNLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztnQkFDbEMsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7Z0JBQ3pDLFVBQVUsQ0FBQyxHQUFHLENBQUMsUUFBUSxFQUFFO29CQUN4QixJQUFJLEVBQU8sUUFBUTtvQkFDbkIsSUFBSTtvQkFDSixRQUFRLEVBQUcsQ0FBQyxDQUFDLE1BQU0sQ0FBQyxhQUFhO2lCQUNqQyxDQUFDLENBQUM7WUFDSixDQUFDO1FBQ0YsQ0FBQztJQUNGLENBQUM7SUFFRDs7Ozs7Ozs7O09BU0c7SUFDSywyQkFBMkIsQ0FBRSxJQUErQjtRQUNuRSxNQUFNLEVBQUUsZUFBZSxFQUFFLEdBQUksSUFBSSxDQUFDLElBQXNELENBQUM7UUFDekYsSUFBSSxDQUFDLGVBQWUsRUFBRSxDQUFDO1lBQ3RCLE9BQU8sRUFBRSxDQUFDO1FBQ1gsQ0FBQztRQUNELE1BQU0sS0FBSyxHQUFnQyxFQUFFLENBQUM7UUFDOUMsS0FBSyxNQUFNLE1BQU0sSUFBSSxlQUFlLEVBQUUsQ0FBQztZQUN0QyxJQUFJLE1BQU0sQ0FBQyxLQUFLLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxjQUFjLEVBQUUsQ0FBQztnQkFDbkQsU0FBUztZQUNWLENBQUM7WUFDRCxLQUFLLE1BQU0sWUFBWSxJQUFJLE1BQU0sQ0FBQyxLQUFLLEVBQUUsQ0FBQztnQkFDekMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsWUFBWSxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7b0JBQy9DLFNBQVM7Z0JBQ1YsQ0FBQztnQkFDRCxNQUFNLFFBQVEsR0FBRyxZQUFZLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQztnQkFDOUMsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLGdDQUFnQyxDQUFDLFFBQVEsRUFBRSxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7Z0JBQzVFLElBQUksUUFBUSxFQUFFLENBQUM7b0JBQ2QsS0FBSyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQztnQkFDdEIsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsS0FBSyxDQUFDO1FBQ3JCLE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7OztPQUtHO0lBQ0ssK0JBQStCLENBQUUsSUFBK0I7UUFDdkUsTUFBTSxlQUFlLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDO1FBQ3ZELElBQUksQ0FBQyx5QkFBeUIsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDO1FBQzNDLElBQUksQ0FBQztZQUNKLE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxvQ0FBb0MsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUMvRCxPQUFPLE1BQU0sQ0FBQztRQUNmLENBQUM7Z0JBQVMsQ0FBQztZQUNWLElBQUksQ0FBQyx5QkFBeUIsR0FBRyxlQUFlLENBQUM7UUFDbEQsQ0FBQztJQUNGLENBQUM7SUFFTyxvQ0FBb0MsQ0FBRSxJQUErQjtRQUM1RSxJQUFJLElBQUksQ0FBQyxJQUFJLEtBQUssT0FBTyxFQUFFLENBQUM7WUFDM0IsTUFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLElBQStCLENBQUM7WUFDdkQsTUFBTSxTQUFTLEdBQUcsRUFBRSxDQUFDLFlBQVksQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUM7WUFDN0UsSUFBSSxTQUFTLElBQUksSUFBSSxDQUFDLDBCQUEwQixDQUFDLEdBQUcsQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUFDO2dCQUNqRSwwQ0FBMEM7Z0JBQzFDLE9BQU8sU0FBUyxDQUFDO1lBQ2xCLENBQUM7WUFDRCxJQUFJLFNBQVMsRUFBRSxDQUFDO2dCQUNmLElBQUksQ0FBQywwQkFBMEIsQ0FBQyxHQUFHLENBQUMsU0FBUyxDQUFDLENBQUM7WUFDaEQsQ0FBQztZQUNELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ2hELElBQUksU0FBUyxFQUFFLENBQUM7Z0JBQ2YsSUFBSSxDQUFDLDBCQUEwQixDQUFDLE1BQU0sQ0FBQyxTQUFTLENBQUMsQ0FBQztZQUNuRCxDQUFDO1lBQ0QsT0FBTyxRQUFRLENBQUM7UUFDakIsQ0FBQztRQUVELE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQywrQkFBK0IsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNsRSxNQUFNLEtBQUssR0FBRyxLQUFLLENBQUMsSUFBSSxDQUFDLGNBQWMsQ0FBQyxPQUFPLEVBQUUsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUUsUUFBUSxFQUFFLElBQUksQ0FBRSxFQUFFLEVBQUU7WUFDN0UsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUM7WUFDMUMsT0FBTyxHQUFHLFFBQVEsR0FBRyxRQUFRLEtBQUssSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO1FBQy9DLENBQUMsQ0FBQyxDQUFDO1FBRUgsTUFBTSxNQUFNLEdBQUcsS0FBSyxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7UUFDekMsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNLLDBCQUEwQixDQUNqQyxRQUFnQixFQUNoQixRQUFvQyxFQUNwQyxPQUFpQjtRQUVqQixpREFBaUQ7UUFDakQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLGdDQUFnQyxDQUFDLFFBQVEsRUFBRSxJQUFJLENBQUMseUJBQXlCLENBQUMsQ0FBQztRQUM3RixJQUFJLElBQUksRUFBRSxDQUFDO1lBQ1YsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLCtCQUErQixDQUFDLElBQUksQ0FBQyxDQUFDO1lBQzVELElBQUksUUFBUSxLQUFLLFNBQVMsRUFBRSxDQUFDO2dCQUM1QixPQUFPLFFBQVEsQ0FBQztZQUNqQixDQUFDO1lBQ0QsTUFBTSxhQUFhLEdBQUcsU0FBUyxDQUFDO1lBQ2hDLE9BQU8sYUFBYSxDQUFDO1FBQ3RCLENBQUM7UUFFRCw2REFBNkQ7UUFDN0QsbUVBQW1FO1FBQ25FLGtFQUFrRTtRQUNsRSxpRUFBaUU7UUFDakUsK0RBQStEO1FBQy9ELGdFQUFnRTtRQUNoRSxnREFBZ0Q7UUFDaEQsa0VBQWtFO1FBQ2xFLG1FQUFtRTtRQUNuRSx3REFBd0Q7UUFDeEQsSUFBSSxRQUFRLEtBQUssY0FBYyxJQUFJLFFBQVEsSUFBSSxRQUFRLENBQUMsTUFBTSxLQUFLLENBQUMsRUFBRSxDQUFDO1lBQ3RFLE1BQU0sQ0FBRSxXQUFXLENBQUUsR0FBRyxRQUFRLENBQUM7WUFDakMsSUFBSSxXQUFXLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxXQUFXLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFdBQVcsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO2dCQUM3RixNQUFNLFdBQVcsR0FBRyxJQUFJLENBQUMsb0JBQW9CLENBQUMsV0FBVyxDQUFDLFFBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDekUsSUFBSSxXQUFXLENBQUMsTUFBTSxLQUFLLFFBQVEsRUFBRSxDQUFDO29CQUNyQyxNQUFNLFdBQVcsR0FBRyxXQUFXLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxPQUFPLENBQUMsS0FBSyxFQUFFLEdBQUcsQ0FBQyxDQUFDO29CQUNsRSxPQUFPLFdBQVcsQ0FBQztnQkFDcEIsQ0FBQztnQkFDRCxJQUFJLFdBQVcsQ0FBQyxNQUFNLEtBQUssV0FBVyxFQUFFLENBQUM7b0JBQ3hDLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxXQUFXLENBQUMsUUFBUSxDQUFDLElBQUksRUFBRSxXQUFXLEVBQUUsV0FBVyxDQUFDLENBQUM7Z0JBQ3JGLENBQUM7Z0JBQ0QsTUFBTSxjQUFjLEdBQUcsU0FBUyxDQUFDO2dCQUNqQyxPQUFPLGNBQWMsQ0FBQztZQUN2QixDQUFDO1lBQ0QsTUFBTSxXQUFXLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxXQUFXLENBQUMsQ0FBQztZQUNoRCxJQUFJLFdBQVcsS0FBSyxTQUFTLEVBQUUsQ0FBQztnQkFDL0IsTUFBTSxlQUFlLEdBQUcsU0FBUyxDQUFDO2dCQUNsQyxPQUFPLGVBQWUsQ0FBQztZQUN4QixDQUFDO1lBQ0QsTUFBTSxhQUFhLEdBQUcsZ0JBQWdCLFdBQVcsR0FBRyxDQUFDO1lBQ3JELE9BQU8sYUFBYSxDQUFDO1FBQ3RCLENBQUM7UUFFRCxvRUFBb0U7UUFDcEUsaUVBQWlFO1FBQ2pFLG1FQUFtRTtRQUNuRSwyREFBMkQ7UUFDM0QsTUFBTSxXQUFXLEdBQUcsSUFBSSxDQUFDLG9CQUFvQixDQUFDLFFBQVEsQ0FBQyxDQUFDO1FBQ3hELElBQUksV0FBVyxDQUFDLE1BQU0sS0FBSyxRQUFRLEVBQUUsQ0FBQztZQUNyQywrREFBK0Q7WUFDL0QsSUFBSSxRQUFRLEtBQUssY0FBYyxJQUFJLFFBQVEsSUFBSSxRQUFRLENBQUMsTUFBTSxLQUFLLENBQUMsRUFBRSxDQUFDO2dCQUN0RSxNQUFNLENBQUUsR0FBRyxDQUFFLEdBQUcsUUFBUSxDQUFDO2dCQUN6QixJQUFJLEdBQUcsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxTQUFTLEVBQUUsQ0FBQztvQkFDMUMsTUFBTSxTQUFTLEdBQUcsR0FBdUIsQ0FBQztvQkFDMUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFNBQVMsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO3dCQUN6QyxNQUFNLFdBQVcsR0FBRyxJQUFJLENBQUMsb0JBQW9CLENBQUMsU0FBUyxDQUFDLFFBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQzt3QkFDdkUsSUFBSSxXQUFXLENBQUMsTUFBTSxLQUFLLFFBQVEsRUFBRSxDQUFDOzRCQUNyQyxxRkFBcUY7NEJBQ3JGLE9BQU8sV0FBVyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsT0FBTyxDQUFDLEtBQUssRUFBRSxHQUFHLENBQUMsQ0FBQzt3QkFDdEQsQ0FBQzt3QkFDRCxJQUFJLFdBQVcsQ0FBQyxNQUFNLEtBQUssV0FBVyxFQUFFLENBQUM7NEJBQ3hDLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxTQUFTLENBQUMsUUFBUSxDQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsV0FBVyxDQUFDLENBQUM7d0JBQ2pGLENBQUM7d0JBQ0QsZ0RBQWdEO3dCQUNoRCxPQUFPLFNBQVMsQ0FBQztvQkFDbEIsQ0FBQztnQkFDRixDQUFDO1lBQ0YsQ0FBQztZQUNELElBQUksQ0FBQyxRQUFRLElBQUksUUFBUSxDQUFDLE1BQU0sS0FBSyxDQUFDLEVBQUUsQ0FBQztnQkFDeEMscUZBQXFGO2dCQUNyRixPQUFPLFdBQVcsQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLE9BQU8sQ0FBQyxLQUFLLEVBQUUsR0FBRyxDQUFDLENBQUM7WUFDdEQsQ0FBQztZQUNELHlEQUF5RDtZQUN6RCw0REFBNEQ7WUFDNUQsT0FBTyxHQUFHLFFBQVEsSUFBSSxRQUFRLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDO1FBQzFFLENBQUM7UUFDRCxJQUFJLFdBQVcsQ0FBQyxNQUFNLEtBQUssV0FBVyxFQUFFLENBQUM7WUFDeEMsSUFBSSxDQUFDLHlCQUF5QixDQUFDLFFBQVEsRUFBRSxPQUFPLElBQUksSUFBSSxDQUFDLHlCQUF5QixFQUFFLFdBQVcsQ0FBQyxDQUFDO1FBQ2xHLENBQUM7UUFFRCxJQUFJLFFBQVEsSUFBSSxRQUFRLENBQUMsTUFBTSxHQUFHLENBQUMsRUFBRSxDQUFDO1lBQ3JDLElBQUksa0JBQWtCLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7Z0JBQ3RDLE1BQU0sYUFBYSxHQUFHLEdBQUcsUUFBUSxJQUFJLFFBQVEsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUM7Z0JBQ3hGLE9BQU8sYUFBYSxDQUFDO1lBQ3RCLENBQUM7WUFDRCwyREFBMkQ7WUFDM0QsK0RBQStEO1lBQy9ELDJEQUEyRDtZQUMzRCwrREFBK0Q7WUFDL0QsNkRBQTZEO1lBQzdELDhEQUE4RDtZQUM5RCwwREFBMEQ7WUFDMUQsSUFBSSxDQUFDLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO2dCQUMvQyxNQUFNLGNBQWMsR0FBRyxHQUFHLFFBQVEsSUFBSSxRQUFRLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDO2dCQUN6RixPQUFPLGNBQWMsQ0FBQztZQUN2QixDQUFDO1lBQ0QsNkRBQTZEO1lBQzdELHNEQUFzRDtZQUN0RCxJQUFJLE9BQU8sRUFBRSxDQUFDO2dCQUNiLElBQUksQ0FBQyw0QkFBNEIsQ0FBQyxRQUFRLEVBQUUsT0FBTyxDQUFDLENBQUM7WUFDdEQsQ0FBQztZQUNELE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFFRCxNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsK0JBQStCLENBQUMsUUFBUSxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQy9FLE9BQU8sY0FBYyxDQUFDO0lBQ3ZCLENBQUM7SUFFRDs7Ozs7Ozs7Ozs7T0FXRztJQUNLLDJCQUEyQixDQUFFLE9BQTZCO1FBQ2pFLElBQUksQ0FBQyxFQUFFLENBQUMsZUFBZSxDQUFDLE9BQU8sQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO1lBQzNDLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFFRCxzRkFBc0Y7UUFDdEYsTUFBTSxRQUFRLEdBQWEsRUFBRSxDQUFDO1FBQzlCLElBQUksS0FBSyxHQUFrQixPQUFPLENBQUMsUUFBUSxDQUFDO1FBQzVDLE9BQU8sRUFBRSxDQUFDLGVBQWUsQ0FBQyxLQUFLLENBQUMsRUFBRSxDQUFDO1lBQ2xDLFFBQVEsQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUNuQyxLQUFLLEdBQUcsS0FBSyxDQUFDLElBQUksQ0FBQztRQUNwQixDQUFDO1FBQ0QsUUFBUSxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLENBQUM7UUFFN0IsTUFBTSxlQUFlLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMseUJBQXlCLENBQUMsRUFBRSxHQUFHLENBQUMsUUFBUSxDQUFFLENBQUMsQ0FBRSxDQUFDLENBQUM7UUFDM0csSUFBSSxDQUFDLGVBQWUsSUFBSSxDQUFDLGVBQWUsQ0FBQyxXQUFXLEVBQUUsQ0FBQztZQUN0RCxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLDJCQUEyQixDQUFDLGVBQWUsQ0FBQyxTQUFTLEVBQUUsSUFBSSxDQUFDLHlCQUF5QixDQUFDLENBQUM7UUFDL0csSUFBSSxDQUFDLFVBQVUsSUFBSSxVQUFVLENBQUMsVUFBVSxFQUFFLENBQUM7WUFDMUMsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELHFFQUFxRTtRQUNyRSxzRUFBc0U7UUFDdEUsd0RBQXdEO1FBQ3hELElBQUksU0FBUyxHQUErRDtZQUMzRSxVQUFVLEVBQUcsVUFBVSxDQUFDLFlBQVk7U0FDcEMsQ0FBQztRQUNGLEtBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxRQUFRLENBQUMsTUFBTSxHQUFHLENBQUMsSUFBSSxTQUFTLEVBQUUsQ0FBQyxFQUFFLEVBQUUsQ0FBQztZQUMzRCxNQUFNLE9BQU8sR0FBRyxRQUFRLENBQUUsQ0FBQyxDQUFFLENBQUM7WUFDOUIsSUFBSSxTQUFTLENBQUMsS0FBSyxFQUFFLENBQUM7Z0JBQ3JCLE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxTQUFTLENBQUMsS0FBSyxFQUFFLE9BQU8sQ0FBQyxDQUFDO2dCQUNuRSxJQUFJLE1BQU0sRUFBRSxJQUFJLElBQUksRUFBRSxDQUFDLGFBQWEsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztvQkFDbkQsU0FBUyxHQUFHLEVBQUUsVUFBVSxFQUFHLFNBQVMsQ0FBQyxVQUFVLEVBQUUsS0FBSyxFQUFHLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQztvQkFDdkUsU0FBUztnQkFDVixDQUFDO2dCQUNELFNBQVMsR0FBRyxTQUFTLENBQUM7Z0JBQ3RCLE1BQU07WUFDUCxDQUFDO1lBQ0QsTUFBTSxhQUFhLEdBQ2xCLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxHQUFHLENBQUMsU0FBUyxDQUFDLFVBQVUsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxPQUFPLENBQUMsQ0FBQztZQUN2RSxJQUFJLGFBQWEsRUFBRSxJQUFJLElBQUksRUFBRSxDQUFDLGFBQWEsQ0FBQyxhQUFhLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztnQkFDakUsU0FBUyxHQUFHLEVBQUUsVUFBVSxFQUFHLFNBQVMsQ0FBQyxVQUFVLEVBQUUsS0FBSyxFQUFHLGFBQWEsQ0FBQyxJQUFJLEVBQUUsQ0FBQztnQkFDOUUsU0FBUztZQUNWLENBQUM7WUFDRCxNQUFNLGFBQWEsR0FBRyxJQUFJLENBQUMsNEJBQTRCLENBQUMsR0FBRyxDQUFDLFNBQVMsQ0FBQyxVQUFVLENBQUMsRUFBRSxHQUFHLENBQUMsT0FBTyxDQUFDLENBQUM7WUFDaEcsSUFBSSxhQUFhLEVBQUUsQ0FBQztnQkFDbkIsTUFBTSxjQUFjLEdBQUcsSUFBSSxDQUFDLDJCQUEyQixDQUFDLGFBQWEsRUFBRSxTQUFTLENBQUMsVUFBVSxDQUFDLENBQUM7Z0JBQzdGLElBQUksY0FBYyxJQUFJLENBQUMsY0FBYyxDQUFDLFVBQVUsRUFBRSxDQUFDO29CQUNsRCxTQUFTLEdBQUcsRUFBRSxVQUFVLEVBQUcsY0FBYyxDQUFDLFlBQVksRUFBRSxDQUFDO29CQUN6RCxTQUFTO2dCQUNWLENBQUM7WUFDRixDQUFDO1lBQ0QsTUFBTSxpQkFBaUIsR0FBRyxJQUFJLENBQUMsdUJBQXVCLENBQUMsR0FBRyxDQUFDLFNBQVMsQ0FBQyxVQUFVLENBQUMsRUFBRSxHQUFHLENBQUMsT0FBTyxDQUFDLENBQUM7WUFDL0YsSUFBSSxpQkFBaUIsRUFBRSxDQUFDO2dCQUN2QixNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsMkJBQTJCLENBQUMsaUJBQWlCLEVBQUUsU0FBUyxDQUFDLFVBQVUsQ0FBQyxDQUFDO2dCQUNqRyxNQUFNLFVBQVUsR0FDZixjQUFjLElBQUksQ0FBQyxjQUFjLENBQUMsVUFBVTtvQkFDM0MsQ0FBQyxDQUFDLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxHQUFHLENBQUMsY0FBYyxDQUFDLFlBQVksQ0FBQyxFQUFFLEdBQUcsQ0FBQyxPQUFPLENBQUM7b0JBQzlFLENBQUMsQ0FBQyxTQUFTLENBQUM7Z0JBQ2QsSUFBSSxVQUFVLEVBQUUsSUFBSSxJQUFJLEVBQUUsQ0FBQyxhQUFhLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7b0JBQzNELFNBQVMsR0FBRyxFQUFFLFVBQVUsRUFBRyxjQUFlLENBQUMsWUFBWSxFQUFFLEtBQUssRUFBRyxVQUFVLENBQUMsSUFBSSxFQUFFLENBQUM7b0JBQ25GLFNBQVM7Z0JBQ1YsQ0FBQztZQUNGLENBQUM7WUFDRCxTQUFTLEdBQUcsU0FBUyxDQUFDO1FBQ3ZCLENBQUM7UUFFRCxNQUFNLFNBQVMsR0FBRyxRQUFRLENBQUUsUUFBUSxDQUFDLE1BQU0sR0FBRyxDQUFDLENBQUUsQ0FBQztRQUNsRCxJQUFJLElBQTJDLENBQUM7UUFDaEQsSUFBSSxTQUFTLEVBQUUsS0FBSyxFQUFFLENBQUM7WUFDdEIsSUFBSSxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxTQUFTLENBQUMsS0FBSyxFQUFFLFNBQVMsQ0FBQyxVQUFVLEVBQUUsU0FBUyxDQUFDLENBQUM7UUFDekYsQ0FBQzthQUFNLElBQUksU0FBUyxFQUFFLENBQUM7WUFDdEIsSUFBSSxHQUFHLElBQUksQ0FBQywwQkFBMEIsQ0FBQyxTQUFTLENBQUMsVUFBVSxFQUFFLFNBQVMsRUFBRSxDQUFDLENBQUMsQ0FBQztRQUM1RSxDQUFDO1FBQ0QsOERBQThEO1FBQzlELGtFQUFrRTtRQUNsRSxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDWCxJQUFJLEdBQUcsSUFBSSxDQUFDLDBCQUEwQixDQUFDLFVBQVUsQ0FBQyxZQUFZLEVBQUUsU0FBUyxFQUFFLENBQUMsQ0FBQyxDQUFDO1FBQy9FLENBQUM7UUFDRCxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDWCxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLCtCQUErQixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzVELE9BQU8sUUFBUSxDQUFDO0lBQ2pCLENBQUM7SUFFRDs7T0FFRztJQUNLLG9CQUFvQixDQUFFLEtBQXFCLEVBQUUsSUFBWTtRQUNoRSxLQUFLLE1BQU0sU0FBUyxJQUFJLEtBQUssQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUMxQyxJQUFJLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUM7Z0JBQ3ZFLFNBQVMsQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLElBQUksRUFBRSxDQUFDO2dCQUMvQixNQUFNLE1BQU0sR0FBRyxTQUFTLENBQUM7Z0JBQ3pCLE9BQU8sTUFBTSxDQUFDO1lBQ2YsQ0FBQztRQUNGLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7OztPQUdHO0lBQ0sseUJBQXlCLENBQ2hDLEtBQXFCLEVBQ3JCLFFBQWdCLEVBQ2hCLElBQVk7UUFFWixLQUFLLE1BQU0sU0FBUyxJQUFJLEtBQUssQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUMxQyxJQUFJLEVBQUUsQ0FBQyxzQkFBc0IsQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUM7Z0JBQzFFLFNBQVMsQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLElBQUksRUFBRSxDQUFDO2dCQUMvQixNQUFNLE1BQU0sR0FBOEIsRUFBRSxJQUFJLEVBQUcsT0FBTyxFQUFFLElBQUksRUFBRyxTQUFTLEVBQUUsSUFBSSxFQUFHLFFBQVEsRUFBRSxDQUFDO2dCQUNoRyxPQUFPLE1BQU0sQ0FBQztZQUNmLENBQUM7WUFDRCxJQUFJLEVBQUUsQ0FBQyxrQkFBa0IsQ0FBQyxTQUFTLENBQUMsSUFBSSxTQUFTLENBQUMsSUFBSSxJQUFJLFNBQVMsQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLElBQUksRUFBRSxDQUFDO2dCQUN4RixNQUFNLE1BQU0sR0FBOEIsRUFBRSxJQUFJLEVBQUcsT0FBTyxFQUFFLElBQUksRUFBRyxTQUFTLEVBQUUsSUFBSSxFQUFHLFFBQVEsRUFBRSxDQUFDO2dCQUNoRyxPQUFPLE1BQU0sQ0FBQztZQUNmLENBQUM7WUFDRCxJQUFJLEVBQUUsQ0FBQyxzQkFBc0IsQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUM7Z0JBQzFFLFNBQVMsQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLElBQUksRUFBRSxDQUFDO2dCQUMvQixNQUFNLE1BQU0sR0FBOEIsRUFBRSxJQUFJLEVBQUcsV0FBVyxFQUFFLElBQUksRUFBRyxTQUFTLEVBQUUsSUFBSSxFQUFHLFFBQVEsRUFBRSxDQUFDO2dCQUNwRyxPQUFPLE1BQU0sQ0FBQztZQUNmLENBQUM7UUFDRixDQUFDO1FBQ0QsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7Ozs7T0FNRztJQUNLLCtCQUErQixDQUFFLFFBQWdCLEVBQUUsT0FBaUI7UUFDM0UsSUFBSSxrQkFBa0IsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUN0QyxPQUFPLFFBQVEsQ0FBQztRQUNqQixDQUFDO1FBQ0QsSUFBSSxPQUFPLEVBQUUsQ0FBQztZQUNiLElBQUksQ0FBQyw0QkFBNEIsQ0FBQyxRQUFRLEVBQUUsT0FBTyxDQUFDLENBQUM7UUFDdEQsQ0FBQztRQUNELE1BQU0sTUFBTSxHQUFHLFNBQVMsQ0FBQztRQUN6QixPQUFPLE1BQU0sQ0FBQztJQUNmLENBQUM7SUFFRDs7Ozs7T0FLRztJQUNLLGdCQUFnQixDQUFFLFlBQW9CLEVBQUUsUUFBZ0I7UUFDL0QsSUFBSSxLQUFLLEdBQUcsSUFBSSxDQUFDLFdBQVcsQ0FBQyxHQUFHLENBQUMsWUFBWSxDQUFDLENBQUM7UUFDL0MsSUFBSSxDQUFDLEtBQUssRUFBRSxDQUFDO1lBQ1osS0FBSyxHQUFHLEVBQUUsQ0FBQztZQUNYLElBQUksQ0FBQyxXQUFXLENBQUMsR0FBRyxDQUFDLFlBQVksRUFBRSxLQUFLLENBQUMsQ0FBQztRQUMzQyxDQUFDO1FBQ0QsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUMvQixLQUFLLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDO1FBQ3RCLENBQUM7SUFDRixDQUFDO0lBRUQ7Ozs7T0FJRztJQUNILG1CQUFtQjtRQUNsQixJQUFJLENBQUMsd0JBQXdCLEVBQUUsQ0FBQztRQUNoQyxJQUFJLENBQUMsMkJBQTJCLEVBQUUsQ0FBQztRQUNuQyxNQUFNLE1BQU0sR0FBc0IsRUFBRSxDQUFDO1FBQ3JDLEtBQUssTUFBTSxDQUFFLFlBQVksRUFBRSxLQUFLLENBQUUsSUFBSSxJQUFJLENBQUMsV0FBVyxFQUFFLENBQUM7WUFDeEQsSUFBSSxLQUFLLENBQUMsTUFBTSxHQUFHLENBQUMsRUFBRSxDQUFDO2dCQUN0QixTQUFTO1lBQ1YsQ0FBQztZQUNELE1BQU0sV0FBVyxHQUFHLFlBQVksQ0FBQyxPQUFPLENBQUMsVUFBVSxFQUFFLEVBQUUsQ0FBQyxDQUFDO1lBQ3pELE1BQU0sT0FBTyxHQUFHLDRCQUE0QixXQUFXLHVCQUF1QjtnQkFDN0Usb0RBQW9ELENBQUM7WUFDdEQsTUFBTSxDQUFDLElBQUksQ0FBQyxFQUFFLE9BQU8sRUFBRSxTQUFTLEVBQUcsQ0FBRSxHQUFHLEtBQUssQ0FBRSxFQUFFLENBQUMsQ0FBQztRQUNwRCxDQUFDO1FBQ0QsS0FBSyxNQUFNLEtBQUssSUFBSSxJQUFJLENBQUMsb0JBQW9CLEVBQUUsQ0FBQztZQUMvQyxNQUFNLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxDQUFDO1FBQ3BCLENBQUM7UUFDRCxNQUFNLE1BQU0sR0FBRyxNQUFNLENBQUM7UUFDdEIsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7Ozs7Ozs7Ozs7Ozs7O09BY0c7SUFDSyxvQkFBb0IsQ0FBRSxJQUFZO1FBQ3pDLGdEQUFnRDtRQUNoRCxNQUFNLFlBQVksR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUMzRixJQUFJLFlBQVksRUFBRSxDQUFDO1lBQ2xCLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxLQUFLLENBQUMsUUFBUSxDQUFDLFlBQVksQ0FBQyxDQUFDO1lBQy9DLElBQUksSUFBSSxFQUFFLENBQUM7Z0JBQ1YsTUFBTSxXQUFXLEdBQTZCLEVBQUUsTUFBTSxFQUFHLFFBQVEsRUFBRSxJQUFJLEVBQUUsQ0FBQztnQkFDMUUsT0FBTyxXQUFXLENBQUM7WUFDcEIsQ0FBQztRQUNGLENBQUM7UUFFRCwyREFBMkQ7UUFDM0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMseUJBQXlCLENBQUMsRUFBRSxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDM0YsSUFBSSxRQUFRLElBQUksQ0FBQyxRQUFRLENBQUMsV0FBVyxFQUFFLENBQUM7WUFDdkMsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLDJCQUEyQixDQUFDLFFBQVEsQ0FBQyxTQUFTLEVBQUUsSUFBSSxDQUFDLHlCQUF5QixDQUFDLENBQUM7WUFDeEcsSUFBSSxVQUFVLElBQUksQ0FBQyxVQUFVLENBQUMsVUFBVSxFQUFFLENBQUM7Z0JBQzFDLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxVQUFVLENBQUMsWUFBWSxFQUFFLFFBQVEsQ0FBQyxZQUFZLEVBQUUsQ0FBQyxDQUFDLENBQUM7Z0JBQ2xHLElBQUksUUFBUSxFQUFFLENBQUM7b0JBQ2QsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsUUFBUSxDQUFDLENBQUM7b0JBQzNDLElBQUksSUFBSSxFQUFFLENBQUM7d0JBQ1YsTUFBTSxZQUFZLEdBQTZCLEVBQUUsTUFBTSxFQUFHLFFBQVEsRUFBRSxJQUFJLEVBQUUsQ0FBQzt3QkFDM0UsT0FBTyxZQUFZLENBQUM7b0JBQ3JCLENBQUM7Z0JBQ0YsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQseUNBQXlDO1FBQ3pDLE1BQU0sTUFBTSxHQUFHLElBQUEsaUNBQXlCLEVBQUMsSUFBSSxDQUFDLEtBQUssRUFBRSxJQUFJLEVBQUUsSUFBSSxDQUFDLGtCQUFrQixDQUFDLENBQUM7UUFDcEYsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7OztPQUdHO0lBQ0ssd0JBQXdCLENBQUUsVUFBa0IsRUFBRSxJQUFZLEVBQUUsS0FBYTtRQUNoRixJQUFJLEtBQUssR0FBRyx3QkFBd0IsRUFBRSxDQUFDO1lBQ3RDLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFFRCxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLFVBQVUsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNqRSxJQUFJLE1BQU0sRUFBRSxDQUFDO1lBQ1osT0FBTyxNQUFNLENBQUM7UUFDZixDQUFDO1FBRUQsTUFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsQ0FBQztRQUMvRCxNQUFNLGlCQUFpQixHQUFHLFNBQVMsRUFBRSxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDL0MsSUFBSSxpQkFBaUIsRUFBRSxDQUFDO1lBQ3ZCLE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxpQkFBaUIsRUFBRSxVQUFVLENBQUMsQ0FBQztZQUN2RixJQUFJLGNBQWMsSUFBSSxDQUFDLGNBQWMsQ0FBQyxVQUFVLEVBQUUsQ0FBQztnQkFDbEQsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLGNBQWMsQ0FBQyxZQUFZLEVBQUUsSUFBSSxFQUFFLEtBQUssR0FBRyxDQUFDLENBQUMsQ0FBQztnQkFDMUYsSUFBSSxLQUFLLEVBQUUsQ0FBQztvQkFDWCxPQUFPLEtBQUssQ0FBQztnQkFDZCxDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFFRCxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUMsR0FBRyxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQzdELElBQUksS0FBSyxFQUFFLENBQUM7WUFDWCxLQUFLLE1BQU0sYUFBYSxJQUFJLEtBQUssRUFBRSxDQUFDO2dCQUNuQyxNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsMkJBQTJCLENBQUMsYUFBYSxFQUFFLFVBQVUsQ0FBQyxDQUFDO2dCQUNuRixJQUFJLENBQUMsY0FBYyxJQUFJLGNBQWMsQ0FBQyxVQUFVLEVBQUUsQ0FBQztvQkFDbEQsU0FBUztnQkFDVixDQUFDO2dCQUNELE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxjQUFjLENBQUMsWUFBWSxFQUFFLElBQUksRUFBRSxLQUFLLEdBQUcsQ0FBQyxDQUFDLENBQUM7Z0JBQzFGLElBQUksS0FBSyxFQUFFLENBQUM7b0JBQ1gsT0FBTyxLQUFLLENBQUM7Z0JBQ2QsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7Ozs7Ozs7OztPQVdHO0lBQ0ssd0JBQXdCO1FBQy9CLElBQUksSUFBSSxDQUFDLHlCQUF5QixFQUFFLENBQUM7WUFDcEMsT0FBTztRQUNSLENBQUM7UUFDRCxJQUFJLENBQUMseUJBQXlCLEdBQUcsSUFBSSxDQUFDO1FBQ3RDLHFFQUFxRTtRQUNyRSxNQUFNLFdBQVcsR0FBRyxJQUFJLEdBQUcsRUFBb0IsQ0FBQztRQUNoRCxLQUFLLE1BQU0sR0FBRyxJQUFJLElBQUksQ0FBQyxnQkFBZ0IsRUFBRSxDQUFDO1lBQ3pDLE1BQU0sS0FBSyxHQUFHLFdBQVcsQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUM5QyxLQUFLLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsQ0FBQztZQUN6QixXQUFXLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsS0FBSyxDQUFDLENBQUM7UUFDbEMsQ0FBQztRQUNELEtBQUssTUFBTSxDQUFFLFFBQVEsRUFBRSxLQUFLLENBQUUsSUFBSSxXQUFXLEVBQUUsQ0FBQztZQUMvQyxJQUFJLElBQUksQ0FBQyxLQUFLLENBQUMsUUFBUSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7Z0JBQ25DLFNBQVM7WUFDVixDQUFDO1lBQ0QsNkRBQTZEO1lBQzdELHdEQUF3RDtZQUN4RCxNQUFNLFVBQVUsR0FBRyxRQUFRLENBQUMsT0FBTyxDQUFDLFVBQVUsRUFBRSxFQUFFLENBQUMsQ0FBQztZQUNwRCxNQUFNLFdBQVcsR0FBRyxVQUFVLENBQUMsS0FBSyxDQUFDLEdBQUcsQ0FBQyxDQUFDLEdBQUcsRUFBRSxJQUFJLFVBQVUsQ0FBQztZQUM5RCxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDLFdBQVcsRUFBRSxDQUFDLE1BQU0sQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxJQUFJLEtBQUssV0FBVyxDQUFDLENBQUM7WUFDaEYsSUFBSSxVQUFVLENBQUMsTUFBTSxLQUFLLENBQUMsRUFBRSxDQUFDO2dCQUM3QixNQUFNLFNBQVMsR0FBb0I7b0JBQ2xDLE9BQU8sRUFBRyx3Q0FBd0MsUUFBUSw0QkFBNEI7d0JBQ3JGLG9DQUFvQztvQkFDckMsU0FBUyxFQUFHLEtBQUs7aUJBQ2pCLENBQUM7Z0JBQ0YsSUFBSSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsQ0FBQztnQkFDMUMsU0FBUztZQUNWLENBQUM7WUFDRCxNQUFNLGtCQUFrQixHQUFHLFVBQVUsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsQ0FBQyxVQUFVLElBQUksQ0FBQyxDQUFDLElBQUksSUFBSSxDQUFDLENBQUMsTUFBTSxFQUFFLENBQUMsQ0FBQztZQUN4RixNQUFNLGNBQWMsR0FBRyxVQUFVLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDLFFBQVEsQ0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUNsRSxNQUFNLGNBQWMsR0FBb0I7Z0JBQ3ZDLE9BQU8sRUFBRyx3Q0FBd0MsUUFBUSw4QkFBOEI7b0JBQ3ZGLGVBQWUsVUFBVSxDQUFDLE1BQU0sZ0NBQWdDO29CQUNoRSxhQUFhLGNBQWMsNkJBQTZCO2dCQUN6RCxTQUFTLEVBQUcsQ0FBRSxHQUFHLEtBQUssRUFBRSxHQUFHLGtCQUFrQixDQUFFO2FBQy9DLENBQUM7WUFDRixJQUFJLENBQUMsb0JBQW9CLENBQUMsSUFBSSxDQUFDLGNBQWMsQ0FBQyxDQUFDO1FBQ2hELENBQUM7SUFDRixDQUFDO0lBRUQ7Ozs7O09BS0c7SUFDSyw0QkFBNEIsQ0FBRSxJQUFZLEVBQUUsT0FBZ0I7UUFDbkUsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsQ0FBQztRQUM1QyxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUM7UUFDNUMsTUFBTSxPQUFPLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQyxDQUFDLEdBQUcsRUFBRSxFQUFFLENBQUMsR0FBRyxDQUFDLElBQUksS0FBSyxJQUFJLElBQUksR0FBRyxDQUFDLFFBQVEsS0FBSyxRQUFRLENBQUMsQ0FBQztRQUN2RyxJQUFJLE9BQU8sRUFBRSxDQUFDO1lBQ2IsT0FBTztRQUNSLENBQUM7UUFDRCxJQUFJLENBQUMsbUJBQW1CLENBQUMsSUFBSSxDQUFDLEVBQUUsSUFBSSxFQUFFLFFBQVEsRUFBRSxJQUFJLEVBQUUsQ0FBQyxDQUFDO0lBQ3pELENBQUM7SUFFRDs7Ozs7O09BTUc7SUFDSyx5QkFBeUIsQ0FBRSxJQUFZO1FBQzlDLE1BQU0sS0FBSyxHQUFhLEVBQUUsQ0FBQztRQUMzQixLQUFLLE1BQU0sQ0FBRSxJQUFJLEVBQUUsS0FBSyxDQUFFLElBQUksSUFBSSxDQUFDLG1CQUFtQixFQUFFLENBQUM7WUFDeEQsSUFBSSxDQUFDLElBQUksQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQ3ZELEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDbEIsQ0FBQztRQUNGLENBQUM7UUFDRCxPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7SUFFRDs7Ozs7Ozs7Ozs7T0FXRztJQUNLLDJCQUEyQjtRQUNsQyxJQUFJLElBQUksQ0FBQyw0QkFBNEIsRUFBRSxDQUFDO1lBQ3ZDLE9BQU87UUFDUixDQUFDO1FBQ0QsSUFBSSxDQUFDLDRCQUE0QixHQUFHLElBQUksQ0FBQztRQUN6QyxNQUFNLFdBQVcsR0FBRyxJQUFJLEdBQUcsRUFBOEQsQ0FBQztRQUMxRixLQUFLLE1BQU0sR0FBRyxJQUFJLElBQUksQ0FBQyxtQkFBbUIsRUFBRSxDQUFDO1lBQzVDLE1BQU0sS0FBSyxHQUFHLFdBQVcsQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUM5QyxLQUFLLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDO1lBQ2hCLFdBQVcsQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxLQUFLLENBQUMsQ0FBQztRQUNsQyxDQUFDO1FBQ0QsS0FBSyxNQUFNLENBQUUsSUFBSSxFQUFFLEtBQUssQ0FBRSxJQUFJLFdBQVcsRUFBRSxDQUFDO1lBQzNDLCtEQUErRDtZQUMvRCw4REFBOEQ7WUFDOUQsd0RBQXdEO1lBQ3hELE1BQU0sVUFBVSxHQUFHLEtBQUssQ0FBQyxNQUFNLENBQUMsQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUMsSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUUsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUM7WUFDakcsSUFBSSxVQUFVLENBQUMsTUFBTSxLQUFLLENBQUMsRUFBRSxDQUFDO2dCQUM3QixTQUFTO1lBQ1YsQ0FBQztZQUNELE1BQU0sU0FBUyxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUN2RCxJQUFJLFNBQVMsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQzFCLFNBQVM7WUFDVixDQUFDO1lBQ0QsTUFBTSxPQUFPLEdBQUcsZ0NBQWdDLElBQUksTUFBTSxTQUFTLENBQUMsTUFBTSxnQkFBZ0I7Z0JBQ3pGLHNFQUFzRSxDQUFDO1lBQ3hFLE1BQU0sYUFBYSxHQUFHLFNBQVMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLENBQUMsQ0FBQztZQUNsRixNQUFNLEtBQUssR0FBb0I7Z0JBQzlCLE9BQU87Z0JBQ1AsU0FBUyxFQUFHLENBQUUsR0FBRyxVQUFVLENBQUMsR0FBRyxDQUFDLENBQUMsSUFBSSxFQUFFLEVBQUUsQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEVBQUUsR0FBRyxhQUFhLENBQUU7YUFDNUUsQ0FBQztZQUNGLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7UUFDdkMsQ0FBQztJQUNGLENBQUM7SUFFRDs7OztPQUlHO0lBQ0ssaUJBQWlCLENBQUUsSUFBWSxFQUFFLElBQVk7UUFDcEQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsRUFBRSxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDM0QsTUFBTSxJQUFJLEdBQUcsSUFBSSxFQUFFLElBQUksQ0FBQztRQUN4QixJQUFJLFFBQVEsR0FBRyxHQUFHLElBQUksTUFBTSxDQUFDO1FBQzdCLElBQUksSUFBSSxJQUFJLElBQUksQ0FBQyxHQUFHLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDM0IsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLGFBQWEsRUFBRSxDQUFDO1lBQ3hDLE1BQU0sSUFBSSxHQUFHLFVBQVUsQ0FBQyw2QkFBNkIsQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLENBQUMsQ0FBQyxJQUFJLEdBQUcsQ0FBQyxDQUFDO1lBQ2hGLE1BQU0sTUFBTSxHQUFHLFVBQVUsQ0FBQyw2QkFBNkIsQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLENBQUMsQ0FBQyxTQUFTLEdBQUcsQ0FBQyxDQUFDO1lBQ3ZGLFFBQVEsR0FBRyxHQUFHLElBQUksSUFBSSxJQUFJLElBQUksTUFBTSxFQUFFLENBQUM7UUFDeEMsQ0FBQztRQUNELE1BQU0sTUFBTSxHQUFHLFFBQVEsQ0FBQztRQUN4QixPQUFPLE1BQU0sQ0FBQztJQUNmLENBQUM7SUFFRDs7O09BR0c7SUFDSyx5QkFBeUIsQ0FDaEMsSUFBWSxFQUNaLE9BQXlCLEVBQ3pCLE1BQTJFO1FBRTNFLE1BQU0sUUFBUSxHQUFHLE9BQU8sT0FBTyxLQUFLLFFBQVEsQ0FBQyxDQUFDLENBQUMsT0FBTyxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsWUFBWSxDQUFDLE9BQU8sQ0FBQyxDQUFDO1FBQ3BGLElBQUksTUFBTSxDQUFDLE1BQU0sS0FBSyxXQUFXLEVBQUUsQ0FBQztZQUNuQyxNQUFNLGtCQUFrQixHQUFHLE1BQU0sQ0FBQyxVQUFVLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLENBQUMsVUFBVSxJQUFJLENBQUMsQ0FBQyxJQUFJLElBQUksQ0FBQyxDQUFDLE1BQU0sRUFBRSxDQUFDLENBQUM7WUFDL0YsTUFBTSxnQkFBZ0IsR0FBRywwQ0FBMEMsSUFBSSxLQUFLO2dCQUMzRSxHQUFHLE1BQU0sQ0FBQyxVQUFVLENBQUMsTUFBTSxxREFBcUQ7Z0JBQ2hGLDhCQUE4QixDQUFDO1lBQ2hDLE1BQU0sY0FBYyxHQUFvQjtnQkFDdkMsT0FBTyxFQUFLLGdCQUFnQjtnQkFDNUIsU0FBUyxFQUFHLENBQUUsUUFBUSxFQUFFLEdBQUcsa0JBQWtCLENBQUU7YUFDL0MsQ0FBQztZQUNGLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLENBQUMsY0FBYyxDQUFDLENBQUM7WUFDL0MsT0FBTztRQUNSLENBQUM7UUFDRCxNQUFNLGlCQUFpQixHQUFHLDJDQUEyQyxJQUFJLHFCQUFxQjtZQUM3RixxREFBcUQsQ0FBQztRQUN2RCxNQUFNLGVBQWUsR0FBb0IsRUFBRSxPQUFPLEVBQUcsaUJBQWlCLEVBQUUsU0FBUyxFQUFHLENBQUUsUUFBUSxDQUFFLEVBQUUsQ0FBQztRQUNuRyxJQUFJLENBQUMsb0JBQW9CLENBQUMsSUFBSSxDQUFDLGVBQWUsQ0FBQyxDQUFDO0lBQ2pELENBQUM7SUFFRDs7O09BR0c7SUFDSyxZQUFZLENBQUUsSUFBYTtRQUNsQyxJQUFJLE9BQU8sR0FBd0IsSUFBSSxDQUFDO1FBQ3hDLE9BQU8sT0FBTyxJQUFJLENBQUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO1lBQzdDLE9BQU8sR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDO1FBQzFCLENBQUM7UUFDRCxJQUFJLENBQUMsT0FBTyxFQUFFLENBQUM7WUFDZCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUM7WUFDaEQsT0FBTyxRQUFRLENBQUM7UUFDakIsQ0FBQztRQUNELE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyxRQUFRLENBQUMsT0FBTyxDQUFDLENBQUM7UUFDckMsTUFBTSxFQUFFLElBQUksRUFBRSxTQUFTLEVBQUUsR0FBRyxFQUFFLENBQUMsNkJBQTZCLENBQUMsT0FBTyxFQUFFLEtBQUssQ0FBQyxDQUFDO1FBQzdFLE1BQU0sUUFBUSxHQUFHLEdBQUcsT0FBTyxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FBQztRQUNwRSxPQUFPLFFBQVEsQ0FBQztJQUNqQixDQUFDO0lBRUQ7Ozs7T0FJRztJQUNLLHdCQUF3QixDQUFFLElBQWE7UUFDOUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDcEUsT0FBTztRQUNSLENBQUM7UUFFRCxNQUFNLEVBQUUsV0FBVyxFQUFFLEdBQUcsSUFBSSxDQUFDO1FBQzdCLElBQUksQ0FBQyxXQUFXLEVBQUUsQ0FBQztZQUNsQixPQUFPO1FBQ1IsQ0FBQztRQUVELElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxXQUFXLENBQUMsSUFBSSxJQUFJLENBQUMscUJBQXFCLENBQUMsR0FBRyxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ3RGLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNoRCxDQUFDO0lBQ0YsQ0FBQztJQUVEOzs7Ozs7OztPQVFHO0lBQ0ssc0JBQXNCLENBQUUsSUFBYSxFQUFFLFVBQXlCO1FBQ3ZFLElBQUksQ0FBQyxFQUFFLENBQUMscUJBQXFCLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ3BFLE9BQU87UUFDUixDQUFDO1FBRUQsTUFBTSxFQUFFLFdBQVcsRUFBRSxHQUFHLElBQUksQ0FBQztRQUM3QixJQUFJLENBQUMsV0FBVyxFQUFFLENBQUM7WUFDbEIsT0FBTztRQUNSLENBQUM7UUFFRCxzQ0FBc0M7UUFDdEMsSUFBSSxJQUFJLENBQUMsMkJBQTJCLENBQUMsV0FBVyxDQUFDLEVBQUUsQ0FBQztZQUNuRCxNQUFNLFlBQVksR0FBRyxJQUFJLENBQUMsZ0JBQWdCLEVBQUUsQ0FBQztZQUM3QyxJQUFJLENBQUMsbUJBQW1CLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLFlBQVksQ0FBQyxDQUFDO1lBRTNELE1BQU0scUJBQXFCLEdBQUcsSUFBSSxDQUFDLDRCQUE0QixDQUM5RCxXQUFnQyxFQUNoQyxVQUFVLENBQ1YsQ0FBQztZQUNGLElBQUksQ0FBQyxjQUFjLENBQUMsR0FBRyxDQUFDLFlBQVksRUFBRTtnQkFDckMsWUFBWSxFQUFZLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSTtnQkFDdEMsVUFBVSxFQUFjLFVBQVUsQ0FBQyxRQUFRO2dCQUMzQyxxQkFBcUIsRUFBRyxxQkFBcUI7YUFDN0MsQ0FBQyxDQUFDO1lBQ0gsT0FBTztRQUNSLENBQUM7UUFFRCx1Q0FBdUM7UUFDdkMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFdBQVcsQ0FBQyxFQUFFLENBQUM7WUFDbEMsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxXQUFXLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDaEUsSUFBSSxRQUFRLEVBQUUsQ0FBQztnQkFDZCxJQUFJLENBQUMsbUJBQW1CLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLFFBQVEsQ0FBQyxDQUFDO1lBQ3hELENBQUM7UUFDRixDQUFDO0lBQ0YsQ0FBQztJQUVEOzs7T0FHRztJQUNLLDRCQUE0QixDQUNuQyxJQUF1QixFQUN2QixVQUF5QjtRQUV6QixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsYUFBYSxDQUFDO1FBQ3BDLElBQUksQ0FBQyxRQUFRLElBQUksUUFBUSxDQUFDLE1BQU0sS0FBSyxDQUFDLEVBQUUsQ0FBQztZQUN4QyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQsTUFBTSxDQUFFLFlBQVksQ0FBRSxHQUFHLFFBQVEsQ0FBQztRQUNsQyxJQUFJLENBQUMsRUFBRSxDQUFDLG1CQUFtQixDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxZQUFZLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUN0RixPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQsTUFBTSxJQUFJLEdBQUcsWUFBWSxDQUFDLFFBQVEsQ0FBQyxJQUFJLENBQUM7UUFFeEMsd0RBQXdEO1FBQ3hELEtBQUssTUFBTSxTQUFTLElBQUksVUFBVSxDQUFDLFVBQVUsRUFBRSxDQUFDO1lBQy9DLElBQ0MsRUFBRSxDQUFDLHNCQUFzQixDQUFDLFNBQVMsQ0FBQztnQkFDcEMsU0FBUyxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssSUFBSSxFQUMzQixDQUFDO2dCQUNGLE9BQU8sSUFBSSxDQUFDO1lBQ2IsQ0FBQztRQUNGLENBQUM7UUFFRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7O09BRUc7SUFDSyx3QkFBd0IsQ0FBRSxZQUFxQjtRQUN0RCxJQUFJLENBQUMsWUFBWSxFQUFFLENBQUM7WUFDbkIsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELE9BQU8sSUFBSSxDQUFDLGNBQWMsQ0FBQyxHQUFHLENBQUMsWUFBWSxDQUFDLEVBQUUscUJBQXFCLENBQUM7SUFDckUsQ0FBQztJQUVEOzs7Ozs7O09BT0c7SUFDSywyQkFBMkIsQ0FBRSxJQUFhO1FBQ2pELElBQUksQ0FBQyxFQUFFLENBQUMsZ0JBQWdCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUNoQyxPQUFPLEtBQUssQ0FBQztRQUNkLENBQUM7UUFDRCxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsVUFBVSxDQUFDO1FBRTdCLGlFQUFpRTtRQUNqRSxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUMzQixPQUFPLElBQUksQ0FBQyxJQUFJLEtBQUssdUJBQXVCO2dCQUMzQyxJQUFJLENBQUMsOEJBQThCLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNyRCxDQUFDO1FBRUQsMERBQTBEO1FBQzFELElBQ0MsRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQztZQUNuQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyx1QkFBdUI7WUFDMUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDO1lBQ2hDLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsRUFDbkQsQ0FBQztZQUNGLE9BQU8sSUFBSSxDQUFDO1FBQ2IsQ0FBQztRQUVELE9BQU8sS0FBSyxDQUFDO0lBQ2QsQ0FBQztJQUVEOztPQUVHO0lBQ0ssZ0JBQWdCO1FBQ3ZCLElBQUksQ0FBQyxpQkFBaUIsRUFBRSxDQUFDO1FBQ3pCLE1BQU0sTUFBTSxHQUFHLGNBQWMsSUFBSSxDQUFDLGlCQUFpQixFQUFFLENBQUM7UUFDdEQsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7O09BRUc7SUFDSyxZQUFZLENBQUUsSUFBYTtRQUNsQyxJQUFJLENBQUMsRUFBRSxDQUFDLGdCQUFnQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDaEMsT0FBTyxLQUFLLENBQUM7UUFDZCxDQUFDO1FBRUQsTUFBTSxFQUFFLFVBQVUsRUFBRSxHQUFHLElBQUksQ0FBQztRQUU1QixpREFBaUQ7UUFDakQsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFVBQVUsQ0FBQyxJQUFJLFVBQVUsQ0FBQyxJQUFJLEtBQUssUUFBUSxFQUFFLENBQUM7WUFDakUsT0FBTyxJQUFJLENBQUM7UUFDYixDQUFDO1FBRUQseURBQXlEO1FBQ3pELElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7WUFDL0MsT0FBTyxVQUFVLENBQUMsSUFBSSxFQUFFLElBQUksS0FBSyxRQUFRLENBQUM7UUFDM0MsQ0FBQztRQUVELE9BQU8sS0FBSyxDQUFDO0lBQ2QsQ0FBQztJQUVEOztPQUVHO0lBQ0ssVUFBVSxDQUFFLElBQWE7UUFDaEMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQ2hDLE9BQU8sS0FBSyxDQUFDO1FBQ2QsQ0FBQztRQUVELE1BQU0sRUFBRSxVQUFVLEVBQUUsR0FBRyxJQUFJLENBQUM7UUFFNUIsdURBQXVEO1FBQ3ZELElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxVQUFVLENBQUMsSUFBSSxVQUFVLENBQUMsSUFBSSxLQUFLLE1BQU0sRUFBRSxDQUFDO1lBQy9ELE9BQU8sSUFBSSxDQUFDO1FBQ2IsQ0FBQztRQUVELCtEQUErRDtRQUMvRCxJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQy9DLE9BQU8sVUFBVSxDQUFDLElBQUksRUFBRSxJQUFJLEtBQUssTUFBTSxDQUFDO1FBQ3pDLENBQUM7UUFFRCxPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7SUFFRDs7VUFFRztJQUNLLDhCQUE4QixDQUFFLFNBQXFDO1FBRTVFLE1BQU0sTUFBTSxHQUFxRCxFQUFFLENBQUM7UUFFcEUsS0FBSyxNQUFNLElBQUksSUFBSSxTQUFTLENBQUMsVUFBVSxFQUFFLENBQUM7WUFDekMsSUFBSSxFQUFFLENBQUMsb0JBQW9CLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztnQkFDakUsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7Z0JBQ2hDLElBQUksUUFBUSxLQUFLLGFBQWEsSUFBSSxJQUFJLENBQUMsV0FBVyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFdBQVcsRUFBRSxDQUFDO29CQUN2RixNQUFNLENBQUMsV0FBVyxHQUFHLElBQUksQ0FBQztnQkFDM0IsQ0FBQztxQkFBTSxJQUFJLFFBQVEsS0FBSyxhQUFhLElBQUksSUFBSSxDQUFDLFdBQVcsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxZQUFZLEVBQUUsQ0FBQztvQkFDL0YsTUFBTSxDQUFDLFdBQVcsR0FBRyxLQUFLLENBQUM7Z0JBQzVCLENBQUM7cUJBQU0sSUFBSSxRQUFRLEtBQUssYUFBYSxJQUFJLElBQUksQ0FBQyxXQUFXLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVyxFQUFFLENBQUM7b0JBQzlGLE1BQU0sQ0FBQyxXQUFXLEdBQUcsSUFBSSxDQUFDO2dCQUMzQixDQUFDO3FCQUFNLElBQUksUUFBUSxLQUFLLGFBQWEsSUFBSSxJQUFJLENBQUMsV0FBVyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFlBQVksRUFBRSxDQUFDO29CQUMvRixNQUFNLENBQUMsV0FBVyxHQUFHLEtBQUssQ0FBQztnQkFDNUIsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7O1VBRUc7SUFDSyxhQUFhLENBQUUsSUFBdUI7UUFDN0MsZ0VBQWdFO1FBQ2hFLE1BQU0sQ0FBRSxBQUFELEVBQUcsQUFBRCxFQUFHLFNBQVMsQ0FBRSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUM7UUFDekMsSUFBSSxDQUFDLFNBQVMsSUFBSSxDQUFDLEVBQUUsQ0FBQyx5QkFBeUIsQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUFDO1lBQzVELE9BQU8sRUFBRSxDQUFDO1FBQ1gsQ0FBQztRQUVELE1BQU0sWUFBWSxHQUFHLElBQUksQ0FBQyw4QkFBOEIsQ0FBQyxTQUFTLENBQUMsQ0FBQztRQUNwRSxPQUFPLFlBQVksQ0FBQztJQUNyQixDQUFDO0lBRUQ7O1VBRUc7SUFDSyxtQkFBbUIsQ0FBRSxJQUFhO1FBQ3pDLElBQUksQ0FBQyxFQUFFLENBQUMsV0FBVyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDM0IsT0FBTyxLQUFLLENBQUM7UUFDZCxDQUFDO1FBRUQsTUFBTSxFQUFFLFVBQVUsRUFBRSxHQUFHLElBQUksQ0FBQztRQUU1QixzQkFBc0I7UUFDdEIsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFVBQVUsQ0FBQyxJQUFJLFVBQVUsQ0FBQyxJQUFJLEtBQUssVUFBVSxFQUFFLENBQUM7WUFDbkUsT0FBTyxJQUFJLENBQUM7UUFDYixDQUFDO1FBRUQsaURBQWlEO1FBQ2pELElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7WUFDckMsTUFBTSxNQUFNLEdBQUcsVUFBVSxDQUFDLFVBQVUsQ0FBQztZQUNyQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLElBQUksTUFBTSxDQUFDLElBQUksS0FBSyxVQUFVLEVBQUUsQ0FBQztnQkFDM0QsT0FBTyxJQUFJLENBQUM7WUFDYixDQUFDO1lBRUQsK0VBQStFO1lBQy9FLElBQ0MsRUFBRSxDQUFDLDBCQUEwQixDQUFDLE1BQU0sQ0FBQztnQkFDckMsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssVUFBVTtnQkFDL0IsRUFBRSxDQUFDLFlBQVksQ0FBQyxNQUFNLENBQUMsVUFBVSxDQUFDO2dCQUNsQyxJQUFJLENBQUMsbUJBQW1CLENBQUMsR0FBRyxDQUFDLE1BQU0sQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLEVBQ25ELENBQUM7Z0JBQ0YsT0FBTyxJQUFJLENBQUM7WUFDYixDQUFDO1FBQ0YsQ0FBQztRQUVELE9BQU8sS0FBSyxDQUFDO0lBQ2QsQ0FBQztJQUVEOztPQUVHO0lBQ0ssYUFBYSxDQUFFLElBQXVCO1FBQzdDLElBQUksSUFBSSxDQUFDLGNBQWMsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUNuQyxPQUFPLElBQUksQ0FBQztRQUNiLENBQUM7UUFDRCxJQUFJLENBQUMsY0FBYyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUM5QixPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7SUFFRDs7T0FFRztJQUNLLGlCQUFpQixDQUFFLElBQXVCLEVBQUUsVUFBeUI7UUFDNUUsK0ZBQStGO1FBQy9GLElBQUksSUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQzlCLE9BQU87UUFDUixDQUFDO1FBRUQsc0RBQXNEO1FBQ3RELE1BQU0sYUFBYSxHQUFHLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUV0RCxnR0FBZ0c7UUFDaEcseUNBQXlDO1FBQ3pDLElBQUksWUFBWSxHQUFZLElBQUksQ0FBQztRQUVqQyxnRkFBZ0Y7UUFDaEYsNEJBQTRCO1FBQzVCLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQ3BELDJFQUEyRTtZQUMzRSxnREFBZ0Q7WUFDaEQsa0NBQWtDO1lBQ2xDLFlBQVksR0FBRyxJQUFJLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQztRQUNyQyxDQUFDO1FBRUQsTUFBTSxRQUFRLEdBQUcsWUFBWSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FBQztRQUNuRCxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FBQyxVQUFVLEVBQUUsUUFBUSxDQUFDLENBQUM7UUFFbkYsSUFBSSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsQ0FBQztZQUM3QixJQUFJLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQztnQkFDaEIsT0FBTyxFQUFHLGdEQUFnRDtnQkFDMUQsSUFBSSxFQUFNLFVBQVUsQ0FBQyxRQUFRO2dCQUM3QixJQUFJLEVBQU0sSUFBSSxHQUFHLENBQUM7Z0JBQ2xCLE1BQU0sRUFBSSxTQUFTLEdBQUcsQ0FBQzthQUN2QixDQUFDLENBQUM7WUFDSCxPQUFPO1FBQ1IsQ0FBQztRQUVELE1BQU0sRUFBRSxRQUFRLEVBQUUsR0FBRyxhQUFhLENBQUM7UUFFbkMsaUVBQWlFO1FBQ2pFLE1BQU0sVUFBVSxHQUFHLGFBQWEsQ0FBQyxVQUFVLENBQUM7UUFDNUMsTUFBTSxFQUFFLFlBQVksRUFBRSxHQUFHLGFBQWEsQ0FBQztRQUV2Qyx5QkFBeUI7UUFDekIsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUV4QyxpR0FBaUc7UUFDakcsTUFBTSxJQUFJLEdBQUcscUJBQWEsQ0FBQyxVQUFVLENBQ3BDLFFBQVEsRUFDUixVQUFVLEVBQ1YsVUFBVSxDQUFDLFFBQVEsRUFDbkIsSUFBSSxHQUFHLENBQUMsRUFDUixTQUFTLEdBQUcsQ0FBQyxFQUNiLFlBQVksQ0FDWixDQUFDO1FBQ0YsSUFBSSxDQUFDLHFCQUFxQixHQUFHLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxZQUFZLENBQUMsQ0FBQztRQUV6RSxpRUFBaUU7UUFDakUsa0VBQWtFO1FBQ2xFLHlDQUF5QztRQUN6QyxJQUFJLENBQUMsZ0JBQWdCLENBQ3BCLFVBQVUsQ0FBQyxDQUFDLENBQUMsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLFFBQVEsRUFBRSxDQUFDLENBQUMsQ0FBQyxHQUFHLFlBQVksSUFBSSxTQUFTLEtBQUssUUFBUSxFQUFFLEVBQy9GLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FDckQsQ0FBQztRQUVGLHNFQUFzRTtRQUN0RSxvRUFBb0U7UUFDcEUsZ0JBQWdCO1FBQ2hCLE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQyxrQkFBa0IsQ0FBQztRQUMvQyxJQUFJLENBQUMsa0JBQWtCLEdBQUcsSUFBSSxDQUFDO1FBQy9CLElBQUksQ0FBQztZQUNKLElBQUksQ0FBQyxVQUFVLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLElBQUksQ0FBQyxDQUFDO1lBRS9DLDREQUE0RDtZQUM1RCxJQUFJLENBQUMsaUJBQWlCLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzlELENBQUM7Z0JBQVMsQ0FBQztZQUNWLElBQUksQ0FBQyxrQkFBa0IsR0FBRyxjQUFjLENBQUM7UUFDMUMsQ0FBQztRQUVELGVBQWU7UUFDZixJQUFJLFVBQVUsRUFBRSxDQUFDO1lBQ2hCLElBQUksQ0FBQyxLQUFLLENBQUMsUUFBUSxDQUFDLFVBQVUsRUFBRSxJQUFJLENBQUMsQ0FBQztRQUN2QyxDQUFDO2FBQU0sQ0FBQztZQUNQLElBQUksQ0FBQyxLQUFLLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzFCLENBQUM7UUFFRCw0REFBNEQ7UUFDNUQsTUFBTSxVQUFVLEdBQW1CO1lBQ2xDLElBQUksRUFBVSxRQUFRO1lBQ3RCLFFBQVEsRUFBTSxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFO1lBQ25FLElBQUksRUFBVSxRQUFRO1lBQ3RCLE1BQU0sRUFBUSxVQUFVLENBQUMsQ0FBQyxDQUFDLFVBQVUsQ0FBQyxRQUFRLENBQUMsQ0FBQyxDQUFDLElBQUk7WUFDckQsV0FBVyxFQUFHLE1BQU0sQ0FBQyxXQUFXLElBQUksSUFBSTtZQUN4QyxXQUFXLEVBQUcsTUFBTSxDQUFDLFdBQVcsSUFBSSxLQUFLO1NBQ3pDLENBQUM7UUFDRixJQUFJLENBQUMsV0FBVyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLFVBQVUsQ0FBQyxDQUFDO1FBQ2hELElBQUksQ0FBQyxjQUFjLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsUUFBUSxDQUFDLENBQUM7UUFFN0Msa0dBQWtHO1FBQ2xHLG1FQUFtRTtRQUNuRSxtQ0FBbUM7UUFDbkMsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksRUFBRSxVQUFVLEVBQUUsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0lBQy9ELENBQUM7SUFFRDs7T0FFRztJQUNLLGVBQWUsQ0FBRSxJQUF1QixFQUFFLFVBQXlCO1FBQzFFLCtGQUErRjtRQUMvRixJQUFJLElBQUksQ0FBQyxhQUFhLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUM5QixPQUFPO1FBQ1IsQ0FBQztRQUVELHNEQUFzRDtRQUN0RCxNQUFNLFdBQVcsR0FBRyxJQUFJLENBQUMsa0JBQWtCLENBQUMsSUFBSSxFQUFFLFVBQVUsQ0FBQyxDQUFDO1FBRTlELDRGQUE0RjtRQUM1Rix5Q0FBeUM7UUFDekMsSUFBSSxZQUFZLEdBQVksSUFBSSxDQUFDO1FBRWpDLGdGQUFnRjtRQUNoRiwwQkFBMEI7UUFDMUIsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7WUFDcEQseUVBQXlFO1lBQ3pFLDhDQUE4QztZQUM5QyxnQ0FBZ0M7WUFDaEMsWUFBWSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDO1FBQ3JDLENBQUM7UUFFRCxNQUFNLFFBQVEsR0FBRyxZQUFZLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQ25ELE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUFDLFVBQVUsRUFBRSxRQUFRLENBQUMsQ0FBQztRQUVuRixJQUFJLENBQUMsV0FBVyxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQzNCLElBQUksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDO2dCQUNoQixPQUFPLEVBQUcsOENBQThDO2dCQUN4RCxJQUFJLEVBQU0sVUFBVSxDQUFDLFFBQVE7Z0JBQzdCLElBQUksRUFBTSxJQUFJLEdBQUcsQ0FBQztnQkFDbEIsTUFBTSxFQUFJLFNBQVMsR0FBRyxDQUFDO2FBQ3ZCLENBQUMsQ0FBQztZQUNILE9BQU87UUFDUixDQUFDO1FBRUQsTUFBTSxFQUFFLFFBQVEsRUFBRSxHQUFHLFdBQVcsQ0FBQztRQUVqQyxpRUFBaUU7UUFDakUsTUFBTSxVQUFVLEdBQUcsV0FBVyxDQUFDLFVBQVUsQ0FBQztRQUMxQyxNQUFNLEVBQUUsWUFBWSxFQUFFLEdBQUcsV0FBVyxDQUFDO1FBRXJDLHlCQUF5QjtRQUN6QixNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsSUFBSSxDQUFDLENBQUM7UUFFNUMsaUdBQWlHO1FBQ2pHLE1BQU0sSUFBSSxHQUFHLHFCQUFhLENBQUMsVUFBVSxDQUNwQyxRQUFRLEVBQ1IsVUFBVSxFQUNWLFVBQVUsQ0FBQyxRQUFRLEVBQ25CLElBQUksR0FBRyxDQUFDLEVBQ1IsU0FBUyxHQUFHLENBQUMsRUFDYixZQUFZLENBQ1osQ0FBQztRQUNGLElBQUksQ0FBQyxxQkFBcUIsR0FBRyxJQUFJLENBQUMsd0JBQXdCLENBQUMsWUFBWSxDQUFDLENBQUM7UUFFekUscURBQXFEO1FBQ3JELElBQUksQ0FBQyxnQkFBZ0IsQ0FDcEIsVUFBVSxDQUFDLENBQUMsQ0FBQyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksUUFBUSxFQUFFLENBQUMsQ0FBQyxDQUFDLEdBQUcsWUFBWSxJQUFJLFNBQVMsS0FBSyxRQUFRLEVBQUUsRUFDL0YsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsRUFBRSxDQUNyRCxDQUFDO1FBRUYsc0VBQXNFO1FBQ3RFLG1FQUFtRTtRQUNuRSxNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsa0JBQWtCLENBQUM7UUFDL0MsSUFBSSxDQUFDLGtCQUFrQixHQUFHLElBQUksQ0FBQztRQUMvQixJQUFJLENBQUM7WUFDSixJQUFJLENBQUMsVUFBVSxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUUvQyw0REFBNEQ7WUFDNUQsSUFBSSxDQUFDLGlCQUFpQixHQUFHLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUM5RCxDQUFDO2dCQUFTLENBQUM7WUFDVixJQUFJLENBQUMsa0JBQWtCLEdBQUcsY0FBYyxDQUFDO1FBQzFDLENBQUM7UUFFRCxlQUFlO1FBQ2YsSUFBSSxVQUFVLEVBQUUsQ0FBQztZQUNoQixJQUFJLENBQUMsS0FBSyxDQUFDLFFBQVEsQ0FBQyxVQUFVLEVBQUUsSUFBSSxDQUFDLENBQUM7UUFDdkMsQ0FBQzthQUFNLENBQUM7WUFDUCxJQUFJLENBQUMsS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUMxQixDQUFDO1FBRUQsNERBQTREO1FBQzVELE1BQU0sVUFBVSxHQUFtQjtZQUNsQyxJQUFJLEVBQVUsUUFBUTtZQUN0QixRQUFRLEVBQU0sR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsRUFBRTtZQUNuRSxJQUFJLEVBQVUsUUFBUTtZQUN0QixNQUFNLEVBQVEsVUFBVSxDQUFDLENBQUMsQ0FBQyxVQUFVLENBQUMsUUFBUSxDQUFDLENBQUMsQ0FBQyxJQUFJO1lBQ3JELFdBQVcsRUFBRyxNQUFNLENBQUMsV0FBVyxJQUFJLElBQUk7WUFDeEMsV0FBVyxFQUFHLE1BQU0sQ0FBQyxXQUFXLElBQUksS0FBSztTQUN6QyxDQUFDO1FBQ0YsSUFBSSxDQUFDLFdBQVcsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLFFBQVEsRUFBRSxVQUFVLENBQUMsQ0FBQztRQUNoRCxJQUFJLENBQUMsY0FBYyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDO1FBRTdDLG9HQUFvRztRQUNwRywyRkFBMkY7UUFDM0YsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksRUFBRSxVQUFVLEVBQUUsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0lBQy9ELENBQUM7SUFFRDs7OztPQUlHO0lBQ0ssbUJBQW1CLENBQUUsSUFBdUI7UUFNbkQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQztRQUM1QixNQUFNLFlBQVksR0FBRyxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBRXBFLElBQUksWUFBWSxFQUFFLENBQUM7WUFDbEIsOERBQThEO1lBQzlELE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUMsVUFBVSxDQUFDO1lBQzFDLElBQUksSUFBSSxDQUFDLE1BQU0sS0FBSyxDQUFDLEVBQUUsQ0FBQztnQkFDdkIsT0FBTyxTQUFTLENBQUM7WUFDbEIsQ0FBQztZQUNELE1BQU0sQ0FBRSxjQUFjLENBQUUsR0FBRyxJQUFJLENBQUM7WUFDaEMsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLGNBQWMsQ0FBQyxFQUFFLENBQUM7Z0JBQ3hDLHFDQUFxQztnQkFDckMsSUFBSSxJQUFJLENBQUMsTUFBTSxHQUFHLENBQUMsRUFBRSxDQUFDO29CQUNyQixPQUFPLFNBQVMsQ0FBQztnQkFDbEIsQ0FBQztnQkFDRCxPQUFPO29CQUNOLE1BQU07b0JBQ04sSUFBSSxFQUFLLGNBQWMsQ0FBQyxJQUFJO29CQUM1QixNQUFNLEVBQUcsSUFBSSxDQUFFLENBQUMsQ0FBRTtvQkFDbEIsTUFBTSxFQUFHLElBQUksQ0FBRSxDQUFDLENBQUU7aUJBQ2xCLENBQUM7WUFDSCxDQUFDO1lBQ0QsNkJBQTZCO1lBQzdCLE9BQU87Z0JBQ04sTUFBTTtnQkFDTixNQUFNLEVBQUcsY0FBYztnQkFDdkIsTUFBTSxFQUFHLElBQUksQ0FBRSxDQUFDLENBQUU7YUFDbEIsQ0FBQztRQUNILENBQUM7UUFFRCx1QkFBdUI7UUFDdkIsSUFBSSxJQUFJLENBQUMsTUFBTSxLQUFLLENBQUMsRUFBRSxDQUFDO1lBQ3ZCLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFFRCxNQUFNLENBQUUsUUFBUSxDQUFFLEdBQUcsSUFBSSxDQUFDO1FBRTFCLDhEQUE4RDtRQUM5RCxtQ0FBbUM7UUFDbkMsSUFBSSxJQUFJLENBQUMsTUFBTSxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDbkQsTUFBTSxDQUFFLEFBQUQsRUFBRyxTQUFTLENBQUUsR0FBRyxJQUFJLENBQUM7WUFDN0IsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLFNBQVMsQ0FBQyxFQUFFLENBQUM7Z0JBQ25DLHdDQUF3QztnQkFDeEMsSUFBSSxJQUFJLENBQUMsTUFBTSxHQUFHLENBQUMsRUFBRSxDQUFDO29CQUNyQixPQUFPLFNBQVMsQ0FBQztnQkFDbEIsQ0FBQztnQkFDRCxPQUFPO29CQUNOLE1BQU0sRUFBRyxRQUFRO29CQUNqQixJQUFJLEVBQUssU0FBUyxDQUFDLElBQUk7b0JBQ3ZCLE1BQU0sRUFBRyxJQUFJLENBQUUsQ0FBQyxDQUFFO29CQUNsQixNQUFNLEVBQUcsSUFBSSxDQUFFLENBQUMsQ0FBRTtpQkFDbEIsQ0FBQztZQUNILENBQUM7WUFDRCxnQ0FBZ0M7WUFDaEMsT0FBTztnQkFDTixNQUFNLEVBQUcsUUFBUTtnQkFDakIsTUFBTSxFQUFHLFNBQVM7Z0JBQ2xCLE1BQU0sRUFBRyxJQUFJLENBQUUsQ0FBQyxDQUFFO2FBQ2xCLENBQUM7UUFDSCxDQUFDO1FBRUQsaURBQWlEO1FBQ2pELElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO1lBQ2xDLElBQUksSUFBSSxDQUFDLE1BQU0sR0FBRyxDQUFDLEVBQUUsQ0FBQztnQkFDckIsT0FBTyxTQUFTLENBQUM7WUFDbEIsQ0FBQztZQUNELE9BQU87Z0JBQ04sSUFBSSxFQUFLLFFBQVEsQ0FBQyxJQUFJO2dCQUN0QixNQUFNLEVBQUcsSUFBSSxDQUFFLENBQUMsQ0FBRTtnQkFDbEIsTUFBTSxFQUFHLElBQUksQ0FBRSxDQUFDLENBQUU7YUFDbEIsQ0FBQztRQUNILENBQUM7UUFFRCwyQ0FBMkM7UUFDM0MsT0FBTztZQUNOLE1BQU0sRUFBRyxRQUFRO1lBQ2pCLE1BQU0sRUFBRyxJQUFJLENBQUUsQ0FBQyxDQUFFO1NBQ2xCLENBQUM7SUFDSCxDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNLLGdCQUFnQixDQUFFLFVBQXlCO1FBQ2xELElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQ3BDLE1BQU0sRUFBRSxJQUFJLEVBQUUsR0FBRyxVQUFVLENBQUM7WUFDNUIsSUFBSSxDQUFDLEVBQUUsQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztnQkFDdkIsT0FBTyxJQUFJLENBQUM7WUFDYixDQUFDO1lBQ0QsS0FBSyxNQUFNLElBQUksSUFBSSxJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7Z0JBQ3BDLElBQUksRUFBRSxDQUFDLGlCQUFpQixDQUFDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztvQkFDbkQsT0FBTyxJQUFJLENBQUMsVUFBVSxDQUFDO2dCQUN4QixDQUFDO1lBQ0YsQ0FBQztZQUNELE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFFRCxJQUFJLEVBQUUsQ0FBQyxvQkFBb0IsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQ3pDLE1BQU0sRUFBRSxJQUFJLEVBQUUsR0FBRyxVQUFVLENBQUM7WUFDNUIsS0FBSyxNQUFNLElBQUksSUFBSSxJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7Z0JBQ3BDLElBQUksRUFBRSxDQUFDLGlCQUFpQixDQUFDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztvQkFDbkQsT0FBTyxJQUFJLENBQUMsVUFBVSxDQUFDO2dCQUN4QixDQUFDO1lBQ0YsQ0FBQztZQUNELE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFFRCxrQ0FBa0M7UUFDbEMsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7T0FHRztJQUNLLHNCQUFzQixDQUFFLGVBQThCO1FBQzdELElBQUksRUFBRSxDQUFDLGlCQUFpQixDQUFDLGVBQWUsQ0FBQyxJQUFJLGVBQWUsQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUNuRSxPQUFPLGVBQWUsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1FBQ2xDLENBQUM7UUFDRCxJQUFJLEVBQUUsQ0FBQyxrQkFBa0IsQ0FBQyxlQUFlLENBQUMsSUFBSSxlQUFlLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDcEUsT0FBTyxlQUFlLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztRQUNsQyxDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsb0JBQW9CLENBQUMsZUFBZSxDQUFDLElBQUksZUFBZSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ3RFLE9BQU8sZUFBZSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7UUFDbEMsQ0FBQztRQUNELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7T0FFRztJQUNLLHdCQUF3QixDQUFFLElBQXVCO1FBQ3hELElBQUksSUFBSSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQzdCLE9BQU8sSUFBSSxDQUFDLGVBQWUsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNuQyxDQUFDO1FBQ0QsSUFBSSxJQUFJLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDM0IsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQyxDQUFDO1lBQzVDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQztnQkFDWCxPQUFPLFNBQVMsQ0FBQztZQUNsQixDQUFDO1lBQ0QsSUFBSSxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7Z0JBQ2YsT0FBTyxJQUFJLENBQUMsSUFBSSxDQUFDO1lBQ2xCLENBQUM7WUFDRCxNQUFNLGVBQWUsR0FBRyxJQUFJLENBQUMsZ0JBQWdCLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxDQUFDO1lBQzNELElBQUksZUFBZSxFQUFFLENBQUM7Z0JBQ3JCLE9BQU8sSUFBSSxDQUFDLHNCQUFzQixDQUFDLGVBQWUsQ0FBQyxDQUFDO1lBQ3JELENBQUM7UUFDRixDQUFDO1FBQ0QsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7O09BSUc7SUFDSyxrQkFBa0IsQ0FBRSxJQUF1QixFQUFFLFVBQXlCO1FBSzdFLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUM1QyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDWCxPQUFPLEVBQUUsQ0FBQztRQUNYLENBQUM7UUFFRCxJQUFJLFFBQVEsR0FBdUIsSUFBSSxDQUFDLElBQUksQ0FBQztRQUM3QyxJQUFJLENBQUMsUUFBUSxFQUFFLENBQUM7WUFDZixNQUFNLGVBQWUsR0FBRyxJQUFJLENBQUMsZ0JBQWdCLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxDQUFDO1lBQzNELElBQUksZUFBZSxFQUFFLENBQUM7Z0JBQ3JCLFFBQVEsR0FBRyxJQUFJLENBQUMsc0JBQXNCLENBQUMsZUFBZSxDQUFDLENBQUM7WUFDekQsQ0FBQztRQUNGLENBQUM7UUFDRCxJQUFJLENBQUMsUUFBUSxFQUFFLENBQUM7WUFDZixPQUFPLEVBQUUsQ0FBQztRQUNYLENBQUM7UUFFRCxNQUFNLEVBQUUsVUFBVSxFQUFFLEdBQUcsSUFBSSxDQUFDO1FBRTVCLHlFQUF5RTtRQUN6RSxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsVUFBVSxDQUFDLElBQUksVUFBVSxDQUFDLElBQUksS0FBSyxNQUFNLEVBQUUsQ0FBQztZQUMvRCxJQUFJLElBQUksQ0FBQyxNQUFNLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLEVBQUUsQ0FBQztnQkFDakQsTUFBTSxhQUFhLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7Z0JBQ2pFLE9BQU87b0JBQ04sUUFBUTtvQkFDUixVQUFVLEVBQUssYUFBYSxDQUFDLFVBQVU7b0JBQ3ZDLFlBQVksRUFBRyxhQUFhLENBQUMsWUFBWTtpQkFDekMsQ0FBQztZQUNILENBQUM7WUFDRCx3Q0FBd0M7WUFDeEMsT0FBTyxFQUFFLFFBQVEsRUFBRSxDQUFDO1FBQ3JCLENBQUM7UUFFRCwyQ0FBMkM7UUFDM0MsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsVUFBVSxDQUFDLElBQUksVUFBVSxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssTUFBTSxFQUFFLENBQUM7WUFDbEYsTUFBTSxHQUFHLEdBQUcsVUFBVSxDQUFDLFVBQVUsQ0FBQztZQUVsQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztnQkFDMUIsTUFBTSxhQUFhLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDekQsT0FBTztvQkFDTixRQUFRO29CQUNSLFVBQVUsRUFBSyxhQUFhLENBQUMsVUFBVTtvQkFDdkMsWUFBWSxFQUFHLGFBQWEsQ0FBQyxZQUFZO2lCQUN6QyxDQUFDO1lBQ0gsQ0FBQztZQUVELElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQ3hDLHFEQUFxRDtnQkFDckQsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLGdCQUFnQixDQUFDLEdBQUcsQ0FBQyxDQUFDO2dCQUN6QyxJQUFJLEtBQUssQ0FBQyxNQUFNLEdBQUcsQ0FBQyxFQUFFLENBQUM7b0JBQ3RCLE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQyxLQUFLLENBQUMsUUFBUSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQztvQkFDeEQsT0FBTyxFQUFFLFFBQVEsRUFBRSxVQUFVLEVBQUcsVUFBVSxFQUFFLENBQUM7Z0JBQzlDLENBQUM7WUFDRixDQUFDO1lBRUQsSUFBSSxFQUFFLENBQUMsZ0JBQWdCLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztnQkFDOUIsc0VBQXNFO2dCQUN0RSw2RUFBNkU7Z0JBQzdFLE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUMsVUFBVSxDQUFDLENBQUM7Z0JBQ3RELE1BQU0sb0JBQW9CLEdBQUcsTUFBTTtvQkFDbEMsQ0FBQyxDQUFDLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUMsWUFBWTtvQkFDcEQsQ0FBQyxDQUFDLFNBQVMsQ0FBQztnQkFFYiw2REFBNkQ7Z0JBQzdELElBQUksSUFBSSxDQUFDLFlBQVksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO29CQUM1QixJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxFQUFFLFVBQVUsQ0FBQyxDQUFDO29CQUN4QyxNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsd0JBQXdCLENBQUMsR0FBRyxDQUFDLENBQUM7b0JBQzFELElBQUksY0FBYyxFQUFFLENBQUM7d0JBQ3BCLE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxjQUFjLEVBQUUsb0JBQW9CLENBQUMsQ0FBQzt3QkFDbkYsT0FBTyxFQUFFLFFBQVEsRUFBRSxVQUFVLEVBQUcsVUFBVSxFQUFFLFlBQVksRUFBRyxVQUFVLEVBQUUsWUFBWSxFQUFFLENBQUM7b0JBQ3ZGLENBQUM7Z0JBQ0YsQ0FBQztnQkFFRCxJQUFJLElBQUksQ0FBQyxVQUFVLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztvQkFDMUIsSUFBSSxDQUFDLGVBQWUsQ0FBQyxHQUFHLEVBQUUsVUFBVSxDQUFDLENBQUM7b0JBQ3RDLE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxHQUFHLENBQUMsQ0FBQztvQkFDMUQsSUFBSSxjQUFjLEVBQUUsQ0FBQzt3QkFDcEIsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLG9CQUFvQixDQUFDLGNBQWMsRUFBRSxvQkFBb0IsQ0FBQyxDQUFDO3dCQUNuRixPQUFPLEVBQUUsUUFBUSxFQUFFLFVBQVUsRUFBRyxVQUFVLEVBQUUsWUFBWSxFQUFHLFVBQVUsRUFBRSxZQUFZLEVBQUUsQ0FBQztvQkFDdkYsQ0FBQztnQkFDRixDQUFDO2dCQUVELHlEQUF5RDtnQkFDekQsSUFBSSxJQUFJLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7b0JBQzVCLE1BQU0sWUFBWSxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUMsQ0FBQztvQkFDakQsSUFBSSxZQUFZLEVBQUUsQ0FBQzt3QkFDbEIsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsWUFBWSxDQUFDLENBQUM7d0JBQ3JELElBQUksVUFBVSxFQUFFLENBQUM7NEJBQ2hCLE9BQU8sRUFBRSxRQUFRLEVBQUUsVUFBVSxFQUFHLFVBQVUsRUFBRSxZQUFZLEVBQUcsVUFBVSxDQUFDLFlBQVksRUFBRSxDQUFDO3dCQUN0RixDQUFDO29CQUNGLENBQUM7Z0JBQ0YsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxFQUFFLFFBQVEsRUFBRSxDQUFDO0lBQ3JCLENBQUM7SUFFRDs7T0FFRztJQUNLLGlCQUFpQixDQUFFLElBQXVCO1FBQ2pELE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUM1QyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsSUFBSSxDQUFDLE1BQU0sSUFBSSxDQUFDLEVBQUUsQ0FBQyx5QkFBeUIsQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLEVBQUUsQ0FBQztZQUN6RSxPQUFPLEVBQUUsQ0FBQztRQUNYLENBQUM7UUFFRCxNQUFNLFlBQVksR0FBRyxJQUFJLENBQUMsOEJBQThCLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxDQUFDO1FBQ3RFLE9BQU8sWUFBWSxDQUFDO0lBQ3JCLENBQUM7SUFFRDs7OztVQUlHO0lBQ0ssdUJBQXVCLENBQzlCLElBQXVCLEVBQ3ZCLFVBQWdDLEVBQ2hDLFFBQWdCO1FBRWhCLHNFQUFzRTtRQUN0RSwrQ0FBK0M7UUFDL0MsSUFBSSxPQUFPLEdBQXdCLElBQUksQ0FBQyxNQUFNLENBQUM7UUFDL0MsT0FBTyxPQUFPLEVBQUUsQ0FBQztZQUNoQixJQUFJLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO2dCQUN2QywrQkFBK0I7Z0JBQy9CLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztvQkFDbkMsTUFBTSxPQUFPLEdBQUcsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7b0JBQ2xDLHdEQUF3RDtvQkFDeEQsNkNBQTZDO29CQUM3Qyx5REFBeUQ7b0JBQ3pELHNEQUFzRDtvQkFDdEQsc0RBQXNEO29CQUN0RCxJQUFJLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO3dCQUNsQyxPQUFPO29CQUNSLENBQUM7b0JBQ0QsK0RBQStEO29CQUMvRCx5REFBeUQ7b0JBQ3pELDhCQUE4QjtvQkFDOUIsSUFBSSxVQUFVLElBQUksSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO3dCQUN2RCxPQUFPO29CQUNSLENBQUM7b0JBQ0QsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxPQUFPLEVBQUUsUUFBUSxDQUFDLENBQUM7b0JBQzlDLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxPQUFPLEVBQUUsUUFBUSxDQUFDLENBQUM7Z0JBQy9DLENBQUM7Z0JBQ0QsT0FBTztZQUNSLENBQUM7WUFDRCxPQUFPLEdBQUcsT0FBTyxDQUFDLE1BQU0sQ0FBQztRQUMxQixDQUFDO0lBQ0YsQ0FBQztJQUVEOzs7OztPQUtHO0lBQ0ssaUJBQWlCLENBQUUsSUFBdUI7UUFDakQsTUFBTSxFQUFFLE1BQU0sRUFBRSxHQUFHLElBQUksQ0FBQztRQUN4QixNQUFNLE1BQU0sR0FBRyxDQUFDLENBQUMsTUFBTTtZQUN0QixFQUFFLENBQUMsMEJBQTBCLENBQUMsTUFBTSxDQUFDO1lBQ3JDLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLFFBQVE7WUFDN0IsRUFBRSxDQUFDLGdCQUFnQixDQUFDLE1BQU0sQ0FBQyxNQUFNLENBQUM7WUFDbEMsTUFBTSxDQUFDLE1BQU0sQ0FBQyxVQUFVLEtBQUssTUFBTSxDQUFDO1FBQ3JDLE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7O09BSUc7SUFDSyxxQkFBcUIsQ0FBRSxPQUFlLEVBQUUsUUFBZ0I7UUFDL0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDO1FBQ2hELElBQUksUUFBUSxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLENBQUM7UUFDcEQsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQ2YsUUFBUSxHQUFHLElBQUksR0FBRyxFQUFrQixDQUFDO1lBQ3JDLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUMsUUFBUSxFQUFFLFFBQVEsQ0FBQyxDQUFDO1FBQ2hELENBQUM7UUFDRCxRQUFRLENBQUMsR0FBRyxDQUFDLE9BQU8sRUFBRSxRQUFRLENBQUMsQ0FBQztJQUNqQyxDQUFDO0lBRUQ7OztVQUdHO0lBQ0sscUJBQXFCLENBQUUsSUFBdUIsRUFBRSxRQUFnQjtRQUN2RSxJQUFJLENBQUMsa0JBQWtCLENBQUMsSUFBSSxFQUFFLFFBQVEsQ0FBQyxDQUFDO0lBQ3pDLENBQUM7SUFFRDs7O1VBR0c7SUFDSyxrQkFBa0IsQ0FBRSxPQUF5QixFQUFFLFFBQWdCO1FBQ3RFLElBQUksYUFBYSxHQUFHLFFBQVEsQ0FBQztRQUM3QixJQUFJLE9BQU8sR0FBd0IsT0FBTyxDQUFDLE1BQU0sQ0FBQztRQUNsRCxpRUFBaUU7UUFDakUsa0VBQWtFO1FBQ2xFLHFFQUFxRTtRQUNyRSxPQUFPLE9BQU8sRUFBRSxDQUFDO1lBQ2hCLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLE9BQU8sQ0FBQztnQkFDekMsRUFBRSxDQUFDLGdCQUFnQixDQUFDLE9BQU8sQ0FBQyxNQUFNLENBQUM7Z0JBQ25DLE9BQU8sQ0FBQyxNQUFNLENBQUMsVUFBVSxLQUFLLE9BQU8sRUFBRSxDQUFDO2dCQUN4QyxNQUFNLEdBQUcsR0FBRyxJQUFJLENBQUMsdUJBQXVCLENBQUMsT0FBTyxDQUFDLE1BQU0sQ0FBQyxDQUFDO2dCQUN6RCxJQUFJLEdBQUcsRUFBRSxDQUFDO29CQUNULGFBQWEsR0FBRyxHQUFHLENBQUM7Z0JBQ3JCLENBQUM7Z0JBQ0QsT0FBTyxHQUFHLE9BQU8sQ0FBQyxNQUFNLENBQUMsTUFBTSxDQUFDO2dCQUNoQyxTQUFTO1lBQ1YsQ0FBQztZQUNELE1BQU07UUFDUCxDQUFDO1FBQ0QsSUFBSSxDQUFDLGtCQUFrQixDQUFDLE9BQU8sRUFBRSxhQUFhLENBQUMsQ0FBQztJQUNqRCxDQUFDO0lBRUQ7Ozs7O09BS0c7SUFDSyxrQkFBa0IsQ0FBRSxJQUFhLEVBQUUsUUFBZ0I7UUFDMUQsSUFBSSxPQUFPLEdBQXdCLElBQUksQ0FBQyxNQUFNLENBQUM7UUFDL0MsT0FBTyxPQUFPLEVBQUUsQ0FBQztZQUNoQixJQUFJLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO2dCQUN2QyxrQ0FBa0M7Z0JBQ2xDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztvQkFDbkMsTUFBTSxPQUFPLEdBQUcsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7b0JBQ2xDLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUMsT0FBTyxFQUFFLFFBQVEsQ0FBQyxDQUFDO29CQUM5QyxJQUFJLENBQUMscUJBQXFCLENBQUMsT0FBTyxFQUFFLFFBQVEsQ0FBQyxDQUFDO2dCQUMvQyxDQUFDO2dCQUNELE9BQU87WUFDUixDQUFDO1lBQ0QsT0FBTyxHQUFHLE9BQU8sQ0FBQyxNQUFNLENBQUM7UUFDMUIsQ0FBQztJQUNGLENBQUM7SUFFRDs7Ozs7OztPQU9HO0lBQ0ssdUJBQXVCLENBQzlCLElBQXVCLEVBQ3ZCLFFBQWdCLEVBQ2hCLFVBQXlCLEVBQ3pCLGVBQXdCO1FBRXhCLE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztRQUNGLE1BQU0sUUFBUSxHQUFHLGVBQWUsSUFBSSxJQUFJLENBQUMsVUFBVSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQztRQUN4RSxJQUFJLENBQUMsUUFBUSxDQUFDLFFBQVEsRUFBRTtZQUN2QixRQUFRLEVBQVUsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsRUFBRTtZQUN2RSxJQUFJLEVBQWMsZUFBZTtZQUNqQyxJQUFJLEVBQWMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQztZQUN4RCxlQUFlLEVBQUcsUUFBUSxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDO1NBQ3hDLENBQUMsQ0FBQztJQUNKLENBQUM7SUFFRDs7Ozs7OztPQU9HO0lBQ0ssdUJBQXVCLENBQUUsSUFBdUI7UUFDdkQsSUFBSSxDQUFDLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztZQUNyRCxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBQ0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQztRQUNqQyxJQUFJLFFBQTRCLENBQUM7UUFDakMsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQzdDLE1BQU0sS0FBSyxHQUFHLFFBQVEsQ0FBQyxVQUFVLENBQUM7WUFDbEMsUUFBUSxHQUFHLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxLQUFLLENBQUMsVUFBVSxDQUFDO2dCQUN6RCxDQUFDLENBQUMsSUFBSSxDQUFDLGVBQWUsQ0FBQyxLQUFLLENBQUMsVUFBVSxDQUFDO2dCQUN4QyxDQUFDLENBQUMsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsQ0FBQztRQUNyRCxDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsZ0JBQWdCLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7WUFDckQsUUFBUSxHQUFHLElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDOUQsQ0FBQzthQUFNLENBQUM7WUFDUCxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBQ0QsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQ2YsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELE1BQU0sU0FBUyxHQUFHLEdBQUcsUUFBUSxJQUFJLFFBQVEsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7UUFDdEQsSUFBSSxJQUFJLENBQUMsV0FBVyxDQUFDLEdBQUcsQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUFDO1lBQ3JDLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxJQUFJLENBQUMsSUFBSSxDQUFDLFdBQVcsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUNyQyxPQUFPLElBQUksQ0FBQyxlQUFlLENBQUMsUUFBUSxDQUFDLENBQUM7UUFDdkMsQ0FBQztRQUNELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7Ozs7O09BTUc7SUFDSyx5QkFBeUIsQ0FBRSxJQUFtQixFQUFFLEVBQTZCO1FBQ3BGLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQzNCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEVBQUUsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUNoRyxNQUFNLE9BQU8sR0FBRyxRQUFRLEtBQUssRUFBRSxDQUFDO1lBQ2hDLE9BQU8sT0FBTyxDQUFDO1FBQ2hCLENBQUM7UUFDRCxJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxFQUFFLEVBQUUsQ0FBQztZQUNsRSxNQUFNLE9BQU8sR0FBRyxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxVQUFVLENBQUM7Z0JBQy9DLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUN0RCxPQUFPLE9BQU8sQ0FBQztRQUNoQixDQUFDO1FBQ0QsT0FBTyxLQUFLLENBQUM7SUFDZCxDQUFDO0lBRUQ7Ozs7O09BS0c7SUFDSyw2QkFBNkIsQ0FBRSxJQUF1QjtRQUM3RCxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsVUFBVSxDQUFDO1FBQy9CLE1BQU0sYUFBYSxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxNQUFNLEVBQUUsTUFBTSxDQUFDO1lBQ25FLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxNQUFNLEVBQUUsT0FBTyxDQUFDLENBQUM7UUFDakQsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLE1BQU0sRUFBRSxNQUFNLENBQUMsQ0FBQztRQUM5RCxJQUFJLENBQUMsYUFBYSxJQUFJLENBQUMsTUFBTSxFQUFFLENBQUM7WUFDL0IsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELElBQUksSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxFQUFFLENBQUM7WUFDL0IsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELE1BQU0sQ0FBRSxBQUFELEVBQUcsT0FBTyxDQUFFLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQztRQUNyQyxJQUFJLFFBQTRCLENBQUM7UUFDakMsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsT0FBTyxDQUFDLEVBQUUsQ0FBQztZQUM1QyxRQUFRLEdBQUcsSUFBSSxDQUFDLGVBQWUsQ0FBQyxPQUFPLENBQUMsQ0FBQztRQUMxQyxDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7WUFDckMsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDdkQsSUFBSSxLQUFLLEVBQUUsQ0FBQztnQkFDWCxRQUFRLEdBQUcsS0FBSyxDQUFDO1lBQ2xCLENBQUM7aUJBQU0sQ0FBQztnQkFDUCxNQUFNLFdBQVcsR0FBRyxJQUFJLENBQUMsb0JBQW9CLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDO2dCQUM1RCxJQUFJLFdBQVcsQ0FBQyxNQUFNLEtBQUssUUFBUSxFQUFFLENBQUM7b0JBQ3JDLFFBQVEsR0FBRyxXQUFXLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQztnQkFDdEMsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBQ0QsTUFBTSxLQUFLLEdBQUcsUUFBUSxJQUFJLElBQUksQ0FBQyxXQUFXLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxDQUFDLENBQUMsQ0FBQyxRQUFRLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQztRQUNoRixPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7SUFFRDs7O09BR0c7SUFDSyx1QkFBdUIsQ0FBRSxJQUF1QjtRQUN2RCxJQUFJLENBQUMsRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQ3JELE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7UUFDekMsSUFBSSxNQUFNLEtBQUssTUFBTSxJQUFJLE1BQU0sS0FBSyxPQUFPLEVBQUUsQ0FBQztZQUM3QyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBQ0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQyxVQUFVLENBQUM7UUFDNUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUNoQyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDekQsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7Ozs7OztPQU1HO0lBQ0ssc0JBQXNCLENBQUUsSUFBdUI7UUFDdEQsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQztRQUMvQixNQUFNLFlBQVksR0FBRyxDQUFDLEtBQW9CLEVBQVcsRUFBRTtZQUN0RCxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsS0FBSyxDQUFDLEVBQUUsQ0FBQztnQkFDNUIsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMseUJBQXlCLENBQUMsRUFBRSxHQUFHLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxDQUFDO2dCQUNqRyxPQUFPLFFBQVEsS0FBSyxPQUFPLENBQUM7WUFDN0IsQ0FBQztZQUNELE1BQU0sT0FBTyxHQUFHLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxLQUFLLENBQUMsSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxPQUFPO2dCQUNsRixFQUFFLENBQUMsWUFBWSxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsSUFBSSxJQUFJLENBQUMscUJBQXFCLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDNUYsT0FBTyxPQUFPLENBQUM7UUFDaEIsQ0FBQyxDQUFDO1FBQ0YsSUFBSSxVQUFxQyxDQUFDO1FBQzFDLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLE1BQU0sQ0FBQyxJQUFJLFlBQVksQ0FBQyxNQUFNLENBQUMsVUFBVSxDQUFDO1lBQzNFLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssT0FBTyxJQUFJLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLE1BQU0sQ0FBQyxFQUFFLENBQUM7WUFDaEUsTUFBTSxDQUFFLFFBQVEsQ0FBRSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUM7WUFDcEMsVUFBVSxHQUFHLFFBQVEsQ0FBQztRQUN2QixDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLE1BQU0sQ0FBQyxFQUFFLENBQUM7WUFDcEMsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMseUJBQXlCLENBQUMsRUFBRSxHQUFHLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ2xHLElBQUksUUFBUSxLQUFLLE9BQU8sSUFBSSxRQUFRLEtBQUssTUFBTSxFQUFFLENBQUM7Z0JBQ2pELE1BQU0sQ0FBRSxRQUFRLENBQUUsR0FBRyxJQUFJLENBQUMsU0FBUyxDQUFDO2dCQUNwQyxVQUFVLEdBQUcsUUFBUSxDQUFDO1lBQ3ZCLENBQUM7UUFDRixDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsZ0JBQWdCLENBQUMsTUFBTSxDQUFDLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLE1BQU0sQ0FBQyxVQUFVLENBQUM7WUFDekYsTUFBTSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLE1BQU0sSUFBSSxZQUFZLENBQUMsTUFBTSxDQUFDLFVBQVUsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQ3ZGLG1EQUFtRDtZQUNuRCxNQUFNLENBQUUsUUFBUSxDQUFFLEdBQUcsTUFBTSxDQUFDLFNBQVMsQ0FBQztZQUN0QyxVQUFVLEdBQUcsUUFBUSxDQUFDO1FBQ3ZCLENBQUM7UUFDRCxJQUFJLENBQUMsVUFBVSxJQUFJLENBQUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQ2pELE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUMzRCxPQUFPLE1BQU0sQ0FBQztJQUNmLENBQUM7SUFHRDs7T0FFRztJQUNLLHdCQUF3QixDQUMvQixTQUF1QixFQUN2QixVQUF5QixFQUN6QixjQUFvQztRQUVwQyxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLFNBQVMsQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQzlCLENBQUM7UUFFRiwwRUFBMEU7UUFDMUUsTUFBTSxTQUFTLEdBQUcsU0FBUyxDQUFDLE1BQXlDLElBQUksY0FBYyxDQUFDO1FBQ3hGLElBQUksQ0FBQyxTQUFTLElBQUksQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDbkMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUM7Z0JBQ2hCLE9BQU8sRUFBRyw2QkFBNkI7Z0JBQ3ZDLElBQUksRUFBTSxVQUFVLENBQUMsUUFBUTtnQkFDN0IsSUFBSSxFQUFNLElBQUksR0FBRyxDQUFDO2dCQUNsQixNQUFNLEVBQUksU0FBUyxHQUFHLENBQUM7YUFDdkIsQ0FBQyxDQUFDO1lBQ0gsT0FBTztRQUNSLENBQUM7UUFFRCxNQUFNLFFBQVEsR0FBRyxTQUFTLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztRQUNyQyxJQUFJLENBQUMsUUFBUSxFQUFFLENBQUM7WUFDZixJQUFJLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQztnQkFDaEIsT0FBTyxFQUFHLDZCQUE2QjtnQkFDdkMsSUFBSSxFQUFNLFVBQVUsQ0FBQyxRQUFRO2dCQUM3QixJQUFJLEVBQU0sSUFBSSxHQUFHLENBQUM7Z0JBQ2xCLE1BQU0sRUFBSSxTQUFTLEdBQUcsQ0FBQzthQUN2QixDQUFDLENBQUM7WUFDSCxPQUFPO1FBQ1IsQ0FBQztRQUVELDZEQUE2RDtRQUM3RCxrREFBa0Q7UUFDbEQsNERBQTREO1FBQzVELElBQUksVUFBZ0MsQ0FBQztRQUNyQyxJQUFJLGNBQWMsR0FBa0IsSUFBSSxDQUFDO1FBQ3pDLElBQUksWUFBZ0MsQ0FBQztRQUNyQyxJQUFJLGVBQWUsR0FBcUQsRUFBRSxDQUFDO1FBRTNFLElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLFNBQVMsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQy9DLE1BQU0sUUFBUSxHQUFHLFNBQVMsQ0FBQyxVQUFVLENBQUM7WUFDdEMsTUFBTSxNQUFNLEdBQUcsUUFBUSxDQUFDLFVBQVUsQ0FBQztZQUVuQyxnRkFBZ0Y7WUFDaEYsOERBQThEO1lBQzlELElBQ0MsRUFBRSxDQUFDLDBCQUEwQixDQUFDLE1BQU0sQ0FBQztnQkFDckMsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssVUFBVTtnQkFDL0IsRUFBRSxDQUFDLFlBQVksQ0FBQyxNQUFNLENBQUMsVUFBVSxDQUFDO2dCQUNsQyxJQUFJLENBQUMsbUJBQW1CLENBQUMsR0FBRyxDQUFDLE1BQU0sQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLEVBQ25ELENBQUM7Z0JBQ0YsWUFBWSxHQUFHLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxHQUFHLENBQUMsTUFBTSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDcEUsSUFBSSxRQUFRLENBQUMsU0FBUyxDQUFDLE1BQU0sS0FBSyxDQUFDLElBQUksRUFBRSxDQUFDLHlCQUF5QixDQUFDLFFBQVEsQ0FBQyxTQUFTLENBQUUsQ0FBQyxDQUFFLENBQUMsRUFBRSxDQUFDO29CQUM5RixlQUFlLEdBQUcsSUFBSSxDQUFDLDhCQUE4QixDQUFDLFFBQVEsQ0FBQyxTQUFTLENBQUUsQ0FBQyxDQUFFLENBQUMsQ0FBQztnQkFDaEYsQ0FBQztZQUNGLENBQUM7aUJBQU0sQ0FBQztnQkFDUCxNQUFNLElBQUksR0FBRyxRQUFRLENBQUMsU0FBUyxDQUFDO2dCQUNoQyxJQUFJLFNBQW9DLENBQUM7Z0JBQ3pDLElBQUksU0FBaUQsQ0FBQztnQkFFdEQsS0FBSyxNQUFNLEdBQUcsSUFBSSxJQUFJLEVBQUUsQ0FBQztvQkFDeEIsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7d0JBQzFCLElBQUksU0FBUyxFQUFFLENBQUM7NEJBQ2YsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUM7Z0NBQ2hCLE9BQU8sRUFBRywrQ0FBK0M7Z0NBQ3pELElBQUksRUFBTSxVQUFVLENBQUMsUUFBUTtnQ0FDN0IsSUFBSSxFQUFNLElBQUksR0FBRyxDQUFDO2dDQUNsQixNQUFNLEVBQUksU0FBUyxHQUFHLENBQUM7NkJBQ3ZCLENBQUMsQ0FBQzt3QkFDSixDQUFDOzZCQUFNLENBQUM7NEJBQ1AsU0FBUyxHQUFHLEdBQUcsQ0FBQzt3QkFDakIsQ0FBQztvQkFDRixDQUFDO3lCQUFNLElBQUksRUFBRSxDQUFDLHlCQUF5QixDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7d0JBQzlDLElBQUksU0FBUyxFQUFFLENBQUM7NEJBQ2YsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUM7Z0NBQ2hCLE9BQU8sRUFBRyw0Q0FBNEM7Z0NBQ3RELElBQUksRUFBTSxVQUFVLENBQUMsUUFBUTtnQ0FDN0IsSUFBSSxFQUFNLElBQUksR0FBRyxDQUFDO2dDQUNsQixNQUFNLEVBQUksU0FBUyxHQUFHLENBQUM7NkJBQ3ZCLENBQUMsQ0FBQzt3QkFDSixDQUFDOzZCQUFNLENBQUM7NEJBQ1AsU0FBUyxHQUFHLEdBQUcsQ0FBQzt3QkFDakIsQ0FBQztvQkFDRixDQUFDO2dCQUNGLENBQUM7Z0JBRUQsSUFBSSxTQUFTLEVBQUUsQ0FBQztvQkFDZixVQUFVLEdBQUcsSUFBSSxDQUFDLDBCQUEwQixDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsQ0FBQztvQkFDN0QsSUFBSSxVQUFVLEVBQUUsQ0FBQzt3QkFDaEIsY0FBYyxHQUFHLFVBQVUsQ0FBQyxRQUFRLENBQUM7b0JBQ3RDLENBQUM7Z0JBQ0YsQ0FBQztnQkFFRCxJQUFJLFNBQVMsRUFBRSxDQUFDO29CQUNmLGVBQWUsR0FBRyxJQUFJLENBQUMsOEJBQThCLENBQUMsU0FBUyxDQUFDLENBQUM7Z0JBQ2xFLENBQUM7WUFDRixDQUFDO1FBQ0YsQ0FBQztRQUVELGtCQUFrQjtRQUNsQixNQUFNLFFBQVEsR0FBRyxVQUFVLENBQUMsQ0FBQyxDQUFDLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxRQUFRLEVBQUUsQ0FBQyxDQUFDLENBQUMsUUFBUSxDQUFDO1FBRTlFLHNDQUFzQztRQUN0QyxNQUFNLFVBQVUsR0FBbUI7WUFDbEMsSUFBSSxFQUFVLFFBQVE7WUFDdEIsUUFBUSxFQUFNLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUU7WUFDbkUsSUFBSSxFQUFVLFVBQVU7WUFDeEIsTUFBTSxFQUFRLGNBQWM7WUFDNUIsV0FBVyxFQUFHLGVBQWUsQ0FBQyxXQUFXLElBQUksSUFBSTtZQUNqRCxXQUFXLEVBQUcsZUFBZSxDQUFDLFdBQVcsSUFBSSxLQUFLO1NBQ2xELENBQUM7UUFDRixJQUFJLENBQUMsV0FBVyxDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFDM0MsSUFBSSxDQUFDLGNBQWMsQ0FBQyxHQUFHLENBQUMsU0FBUyxFQUFFLFFBQVEsQ0FBQyxDQUFDO1FBRTdDLG1CQUFtQjtRQUNuQixNQUFNLElBQUksR0FBRyxxQkFBYSxDQUFDLFVBQVUsQ0FDcEMsUUFBUSxFQUNSLFVBQVUsRUFDVixVQUFVLENBQUMsUUFBUSxFQUNuQixJQUFJLEdBQUcsQ0FBQyxFQUNSLFNBQVMsR0FBRyxDQUFDLEVBQ2IsWUFBWSxDQUNaLENBQUM7UUFDRixJQUFJLENBQUMscUJBQXFCLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLElBQUksQ0FBQyxZQUFZLENBQUMsQ0FBQztRQUU5RSxxREFBcUQ7UUFDckQsSUFBSSxDQUFDLGdCQUFnQixDQUNwQixVQUFVLENBQUMsQ0FBQyxDQUFDLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxRQUFRLEVBQUUsQ0FBQyxDQUFDLENBQUMsR0FBRyxZQUFZLElBQUksU0FBUyxLQUFLLFFBQVEsRUFBRSxFQUMvRixHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQ3JELENBQUM7UUFFRixxRUFBcUU7UUFDckUsaUVBQWlFO1FBQ2pFLE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQyxrQkFBa0IsQ0FBQztRQUMvQyxJQUFJLENBQUMsa0JBQWtCLEdBQUcsSUFBSSxDQUFDO1FBQy9CLElBQUksQ0FBQztZQUNKLElBQUksQ0FBQyxVQUFVLEdBQUcsSUFBSSxDQUFDLHNCQUFzQixDQUFDLFNBQVMsQ0FBQyxDQUFDO1lBQ3pELElBQUksQ0FBQyxpQkFBaUIsR0FBRyxJQUFJLENBQUMsNkJBQTZCLENBQUMsU0FBUyxDQUFDLENBQUM7UUFDeEUsQ0FBQztnQkFBUyxDQUFDO1lBQ1YsSUFBSSxDQUFDLGtCQUFrQixHQUFHLGNBQWMsQ0FBQztRQUMxQyxDQUFDO1FBRUQsZUFBZTtRQUNmLElBQUksVUFBVSxFQUFFLENBQUM7WUFDaEIsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsVUFBVSxFQUFFLElBQUksQ0FBQyxDQUFDO1FBQ3ZDLENBQUM7YUFBTSxDQUFDO1lBQ1AsSUFBSSxDQUFDLEtBQUssQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDMUIsQ0FBQztJQUNGLENBQUM7SUFFRDs7Ozs7OztPQU9HO0lBQ0ssZUFBZSxDQUFFLElBQXVCO1FBQy9DLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUM7UUFFNUIsSUFBSSxJQUFJLENBQUMsTUFBTSxLQUFLLENBQUMsRUFBRSxDQUFDO1lBQ3ZCLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFFRCxNQUFNLENBQUUsUUFBUSxDQUFFLEdBQUcsSUFBSSxDQUFDO1FBRTFCLDREQUE0RDtRQUM1RCxJQUFJLElBQUksQ0FBQyxNQUFNLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsUUFBUSxDQUFDLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxJQUFJLENBQUUsQ0FBQyxDQUFFLENBQUMsRUFBRSxDQUFDO1lBQ3BGLE9BQU8sSUFBSSxDQUFFLENBQUMsQ0FBRSxDQUFDLElBQUksQ0FBQztRQUN2QixDQUFDO1FBRUQsMENBQTBDO1FBQzFDLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO1lBQ2xDLE9BQU8sUUFBUSxDQUFDLElBQUksQ0FBQztRQUN0QixDQUFDO1FBRUQscURBQXFEO1FBQ3JELElBQUksRUFBRSxDQUFDLG9CQUFvQixDQUFDLFFBQVEsQ0FBQyxJQUFJLFFBQVEsQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUN4RCxPQUFPLFFBQVEsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1FBQzNCLENBQUM7UUFFRCxrRUFBa0U7UUFDbEUsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDbEMsTUFBTSxFQUFFLElBQUksRUFBRSxHQUFHLFFBQVEsQ0FBQztZQUMxQixJQUFJLEVBQUUsQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7Z0JBQzdDLE9BQU8sSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7WUFDdkIsQ0FBQztRQUNGLENBQUM7UUFFRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7Ozs7T0FJRztJQUNLLG9CQUFvQixDQUFFLElBQXVCO1FBS3BELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxlQUFlLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDNUMsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQ2YsT0FBTyxFQUFFLENBQUM7UUFDWCxDQUFDO1FBRUQsTUFBTSxFQUFFLFVBQVUsRUFBRSxHQUFHLElBQUksQ0FBQztRQUU1Qiw4RUFBOEU7UUFDOUUsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFVBQVUsQ0FBQyxJQUFJLFVBQVUsQ0FBQyxJQUFJLEtBQUssUUFBUSxFQUFFLENBQUM7WUFDakUsNERBQTREO1lBQzVELElBQUksSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBRSxDQUFDLENBQUUsQ0FBQyxFQUFFLENBQUM7Z0JBQ3hFLE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUUsQ0FBQyxDQUFFLENBQUMsSUFBSSxDQUFDO2dCQUM1QyxNQUFNLGFBQWEsR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsVUFBVSxDQUFDLENBQUM7Z0JBQzNELE9BQU87b0JBQ04sUUFBUTtvQkFDUixVQUFVLEVBQUssYUFBYSxDQUFDLFVBQVU7b0JBQ3ZDLFlBQVksRUFBRyxhQUFhLENBQUMsWUFBWTtpQkFDekMsQ0FBQztZQUNILENBQUM7WUFFRCwwQ0FBMEM7WUFDMUMsT0FBTyxFQUFFLFFBQVEsRUFBRSxDQUFDO1FBQ3JCLENBQUM7UUFFRCw2Q0FBNkM7UUFDN0MsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsVUFBVSxDQUFDLElBQUksVUFBVSxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssUUFBUSxFQUFFLENBQUM7WUFDcEYsTUFBTSxHQUFHLEdBQUcsVUFBVSxDQUFDLFVBQVUsQ0FBQztZQUVsQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztnQkFDMUIsTUFBTSxhQUFhLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDekQsT0FBTztvQkFDTixRQUFRO29CQUNSLFVBQVUsRUFBSyxhQUFhLENBQUMsVUFBVTtvQkFDdkMsWUFBWSxFQUFHLGFBQWEsQ0FBQyxZQUFZO2lCQUN6QyxDQUFDO1lBQ0gsQ0FBQztZQUVELElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQ3hDLHVEQUF1RDtnQkFDdkQsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLGdCQUFnQixDQUFDLEdBQUcsQ0FBQyxDQUFDO2dCQUN6QyxJQUFJLEtBQUssQ0FBQyxNQUFNLEdBQUcsQ0FBQyxFQUFFLENBQUM7b0JBQ3RCLE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQyxLQUFLLENBQUMsUUFBUSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQztvQkFDeEQsT0FBTyxFQUFFLFFBQVEsRUFBRSxVQUFVLEVBQUcsVUFBVSxFQUFFLENBQUM7Z0JBQzlDLENBQUM7WUFDRixDQUFDO1lBRUQsSUFBSSxFQUFFLENBQUMsZ0JBQWdCLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztnQkFDOUIsc0VBQXNFO2dCQUN0RSw2RUFBNkU7Z0JBQzdFLE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUMsVUFBVSxDQUFDLENBQUM7Z0JBQ3RELE1BQU0sb0JBQW9CLEdBQUcsTUFBTTtvQkFDbEMsQ0FBQyxDQUFDLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUMsWUFBWTtvQkFDcEQsQ0FBQyxDQUFDLFNBQVMsQ0FBQztnQkFFYiw2RUFBNkU7Z0JBQzdFLElBQUksSUFBSSxDQUFDLFlBQVksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO29CQUM1QixJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxFQUFFLElBQUksQ0FBQyxhQUFhLEVBQUUsQ0FBQyxDQUFDO29CQUNsRCxNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsZUFBZSxDQUFDLEdBQUcsQ0FBQyxDQUFDO29CQUNqRCxJQUFJLGNBQWMsRUFBRSxDQUFDO3dCQUNwQixNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsb0JBQW9CLENBQUMsY0FBYyxFQUFFLG9CQUFvQixDQUFDLENBQUM7d0JBQ25GLG1EQUFtRDt3QkFDbkQsT0FBTyxFQUFFLFFBQVEsRUFBRSxVQUFVLEVBQUcsVUFBVSxFQUFFLFlBQVksRUFBRyxVQUFVLEVBQUUsWUFBWSxFQUFFLENBQUM7b0JBQ3ZGLENBQUM7Z0JBQ0YsQ0FBQztnQkFFRCx5RUFBeUU7Z0JBQ3pFLElBQUksSUFBSSxDQUFDLFVBQVUsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO29CQUMxQixJQUFJLENBQUMsZUFBZSxDQUFDLEdBQUcsRUFBRSxJQUFJLENBQUMsYUFBYSxFQUFFLENBQUMsQ0FBQztvQkFDaEQsTUFBTSxjQUFjLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLEdBQUcsQ0FBQyxDQUFDO29CQUMxRCxJQUFJLGNBQWMsRUFBRSxDQUFDO3dCQUNwQixNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsb0JBQW9CLENBQUMsY0FBYyxFQUFFLG9CQUFvQixDQUFDLENBQUM7d0JBQ25GLE9BQU8sRUFBRSxRQUFRLEVBQUUsVUFBVSxFQUFHLFVBQVUsRUFBRSxZQUFZLEVBQUcsVUFBVSxFQUFFLFlBQVksRUFBRSxDQUFDO29CQUN2RixDQUFDO2dCQUNGLENBQUM7Z0JBRUQsMkRBQTJEO2dCQUMzRCxJQUFJLElBQUksQ0FBQyxZQUFZLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztvQkFDNUIsTUFBTSxZQUFZLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxDQUFDO29CQUNqRCxJQUFJLFlBQVksRUFBRSxDQUFDO3dCQUNsQixNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDLFFBQVEsQ0FBQyxZQUFZLENBQUMsQ0FBQzt3QkFDckQsSUFBSSxVQUFVLEVBQUUsQ0FBQzs0QkFDaEIsT0FBTyxFQUFFLFFBQVEsRUFBRSxVQUFVLEVBQUcsVUFBVSxFQUFFLFlBQVksRUFBRyxVQUFVLENBQUMsWUFBWSxFQUFFLENBQUM7d0JBQ3RGLENBQUM7b0JBQ0YsQ0FBQztnQkFDRixDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFFRCxPQUFPLEVBQUUsUUFBUSxFQUFFLENBQUM7SUFDckIsQ0FBQztJQUVEOzs7T0FHRztJQUNLLG9CQUFvQixDQUFFLElBQVksRUFBRSxZQUFvQjtRQUMvRCxPQUFPLEdBQUcsWUFBWSxLQUFLLElBQUksRUFBRSxDQUFDO0lBQ25DLENBQUM7SUFFRDs7O09BR0c7SUFDSyxtQkFBbUIsQ0FBRSxVQUFrQjtRQUk5QyxzREFBc0Q7UUFDdEQsSUFBSSxJQUFJLENBQUMscUJBQXFCLENBQUMsR0FBRyxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7WUFDaEQsT0FBTyxFQUFFLENBQUM7UUFDWCxDQUFDO1FBRUQsa0RBQWtEO1FBQ2xELE1BQU0sWUFBWSxHQUFHLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxHQUFHLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDOUQsSUFBSSxZQUFZLEVBQUUsQ0FBQztZQUNsQixPQUFPLEVBQUUsWUFBWSxFQUFFLENBQUM7UUFDekIsQ0FBQztRQUVELCtDQUErQztRQUMvQyxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsMEJBQTBCLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDL0QsT0FBTyxFQUFFLFVBQVUsRUFBRyxVQUFVLEVBQUUsWUFBWSxFQUFHLFVBQVUsRUFBRSxZQUFZLEVBQUUsQ0FBQztJQUM3RSxDQUFDO0lBRUQ7O09BRUc7SUFDSyxZQUFZLENBQUUsSUFBdUI7UUFDNUMsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQztRQUM3QixJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLElBQUksS0FBSyxRQUFRLEVBQUUsQ0FBQztZQUNyRCxPQUFPLElBQUksQ0FBQztRQUNiLENBQUM7UUFDRCxJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxRQUFRLEVBQUUsQ0FBQztZQUN4RSxPQUFPLElBQUksQ0FBQztRQUNiLENBQUM7UUFDRCxPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7SUFFRDs7Ozs7OztPQU9HO0lBQ0ssaUJBQWlCLENBQUUsSUFBdUI7UUFDakQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQztRQUM1QixJQUFJLElBQUksQ0FBQyxNQUFNLEtBQUssQ0FBQyxFQUFFLENBQUM7WUFDdkIsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELDBEQUEwRDtRQUMxRCxJQUFJLElBQUksQ0FBQyxNQUFNLEtBQUssQ0FBQyxFQUFFLENBQUM7WUFDdkIsTUFBTSxDQUFFLEdBQUcsQ0FBRSxHQUFHLElBQUksQ0FBQztZQUNyQixJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxDQUFDLCtCQUErQixDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQ3hFLE1BQU0sSUFBSSxHQUFHLEdBQUcsQ0FBQyxJQUFJLENBQUM7Z0JBQ3RCLHlFQUF5RTtnQkFDekUsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7b0JBQ3BELE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUMsVUFBVSxDQUFDO29CQUM5QyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQzt3QkFDakMsTUFBTSxVQUFVLEdBQUcsVUFBVSxDQUFDLElBQUksQ0FBQzt3QkFDbkMsTUFBTSxhQUFhLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLFVBQVUsQ0FBQyxDQUFDO3dCQUMzRCxJQUFJLGFBQWEsQ0FBQyxZQUFZLEVBQUUsQ0FBQzs0QkFDaEMsd0RBQXdEOzRCQUN4RCxPQUFPLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLEVBQUUsYUFBYSxDQUFDLFlBQVksQ0FBQyxDQUFDO3dCQUNwRSxDQUFDO3dCQUNELElBQUksYUFBYSxDQUFDLFVBQVUsRUFBRSxDQUFDOzRCQUM5QixrREFBa0Q7NEJBQ2xELE1BQU0sWUFBWSxHQUFHLEdBQUcsYUFBYSxDQUFDLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxFQUFFLENBQUM7NEJBQ3BFLElBQUksSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsWUFBWSxDQUFDLEVBQUUsQ0FBQztnQ0FDdkMsT0FBTyxZQUFZLENBQUM7NEJBQ3JCLENBQUM7NEJBQ0QsT0FBTyxJQUFJLENBQUM7d0JBQ2IsQ0FBQztvQkFDRixDQUFDO2dCQUNGLENBQUM7Z0JBQ0QsT0FBTyxJQUFJLENBQUM7WUFDYixDQUFDO1lBQ0QsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELHlDQUF5QztRQUN6QyxJQUFJLElBQUksQ0FBQyxNQUFNLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDdEIsTUFBTSxDQUFFLFNBQVMsRUFBRSxPQUFPLENBQUUsR0FBRyxJQUFJLENBQUM7WUFDcEMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsZUFBZSxDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7Z0JBQ2pFLE9BQU8sU0FBUyxDQUFDO1lBQ2xCLENBQUM7WUFDRCxNQUFNLFVBQVUsR0FBRyxTQUFTLENBQUMsSUFBSSxDQUFDO1lBQ2xDLE1BQU0sSUFBSSxHQUFHLE9BQU8sQ0FBQyxJQUFJLENBQUM7WUFDMUIsTUFBTSxhQUFhLEdBQUcsSUFBSSxDQUFDLG1CQUFtQixDQUFDLFVBQVUsQ0FBQyxDQUFDO1lBQzNELElBQUksYUFBYSxDQUFDLFlBQVksRUFBRSxDQUFDO2dCQUNoQyxPQUFPLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLEVBQUUsYUFBYSxDQUFDLFlBQVksQ0FBQyxDQUFDO1lBQ3BFLENBQUM7WUFDRCxJQUFJLGFBQWEsQ0FBQyxVQUFVLEVBQUUsQ0FBQztnQkFDOUIsTUFBTSxZQUFZLEdBQUcsR0FBRyxhQUFhLENBQUMsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEVBQUUsQ0FBQztnQkFDcEUsSUFBSSxJQUFJLENBQUMsS0FBSyxDQUFDLFFBQVEsQ0FBQyxZQUFZLENBQUMsRUFBRSxDQUFDO29CQUN2QyxPQUFPLFlBQVksQ0FBQztnQkFDckIsQ0FBQztnQkFDRCxPQUFPLElBQUksQ0FBQztZQUNiLENBQUM7WUFDRCxPQUFPLElBQUksQ0FBQztRQUNiLENBQUM7UUFFRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNILHFCQUFxQixDQUFFLElBQXVCO1FBQzdDLE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUM1QyxPQUFPLE1BQU0sQ0FBQztJQUNmLENBQUM7SUFFRDs7O1VBR0c7SUFDSyxvQkFBb0IsQ0FDM0IsSUFBWSxFQUNaLFlBQXFCO1FBRXJCLE1BQU0saUJBQWlCLEdBQUcsQ0FBQyxJQUFjLEVBQVcsRUFBRTtZQUNyRCxJQUFJLFlBQVksS0FBSyxTQUFTLEVBQUUsQ0FBQztnQkFDaEMsT0FBTyxJQUFJLENBQUMsWUFBWSxLQUFLLFNBQVMsQ0FBQztZQUN4QyxDQUFDO1lBQ0QsT0FBTyxJQUFJLENBQUMsWUFBWSxLQUFLLFlBQVksQ0FBQztRQUMzQyxDQUFDLENBQUM7UUFFRiw2RUFBNkU7UUFDN0UsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDeEMsSUFBSSxLQUFLLElBQUksaUJBQWlCLENBQUMsS0FBSyxDQUFDLEVBQUUsQ0FBQztZQUN2QyxPQUFPLEtBQUssQ0FBQztRQUNkLENBQUM7UUFFRCwwRUFBMEU7UUFDMUUsS0FBSyxNQUFNLElBQUksSUFBSSxJQUFJLENBQUMsS0FBSyxDQUFDLFdBQVcsRUFBRSxFQUFFLENBQUM7WUFDN0MsSUFBSSxJQUFJLENBQUMsSUFBSSxLQUFLLElBQUksSUFBSSxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUNuRCxPQUFPLElBQUksQ0FBQztZQUNiLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7O1VBSUc7SUFDSywwQkFBMEIsQ0FBRSxJQUFZO1FBQy9DLHVFQUF1RTtRQUN2RSxNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQ3hELElBQUksY0FBYyxFQUFFLENBQUM7WUFDcEIsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxRQUFRLENBQUMsY0FBYyxDQUFDLENBQUM7WUFDdkQsSUFBSSxVQUFVO2dCQUFFLE9BQU8sVUFBVSxDQUFDO1FBQ25DLENBQUM7UUFFRCxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsb0JBQW9CLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDbkQsT0FBTyxVQUFVLENBQUM7SUFDbkIsQ0FBQztJQUVEOzs7T0FHRztJQUNLLGlCQUFpQixDQUFFLElBQW1CO1FBQzdDLElBQUksT0FBTyxHQUFrQixJQUFJLENBQUM7UUFDbEMsT0FBTyxFQUFFLENBQUMsMEJBQTBCLENBQUMsT0FBTyxDQUFDLEVBQUUsQ0FBQztZQUMvQyxPQUFPLEdBQUcsT0FBTyxDQUFDLFVBQVUsQ0FBQztRQUM5QixDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7WUFDOUIsT0FBTyxPQUFPLENBQUM7UUFDaEIsQ0FBQztRQUNELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7VUFFRztJQUNLLGdCQUFnQixDQUFFLElBQWlEO1FBQzFFLE1BQU0sS0FBSyxHQUFhLEVBQUUsQ0FBQztRQUUzQixJQUFJLE9BQU8sR0FBa0IsSUFBSSxDQUFDO1FBQ2xDLE9BQU8sRUFBRSxDQUFDLDBCQUEwQixDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7WUFDL0MsSUFBSSxPQUFPLENBQUMsSUFBSSxFQUFFLENBQUM7Z0JBQ2xCLEtBQUssQ0FBQyxPQUFPLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUNsQyxDQUFDO1lBQ0QsT0FBTyxHQUFHLE9BQU8sQ0FBQyxVQUFVLENBQUM7UUFDOUIsQ0FBQztRQUVELElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO1lBQzlCLEtBQUssQ0FBQyxPQUFPLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzdCLENBQUM7UUFFRCxPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7SUFFRDs7OztPQUlHO0lBQ0ssNEJBQTRCLENBQUUsSUFBdUI7UUFDNUQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQztRQUM3QixNQUFNLElBQUksR0FBRyxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQztZQUNqQyxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUk7WUFDWCxDQUFDLENBQUMsRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQztnQkFDcEMsQ0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSTtnQkFDaEIsQ0FBQyxDQUFDLEVBQUUsQ0FBQztRQUVQLElBQUksSUFBSSxLQUFLLE1BQU0sRUFBRSxDQUFDO1lBQ3JCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUNoRCxJQUFJLENBQUMsUUFBUSxFQUFFLENBQUM7Z0JBQ2YsT0FBTyxTQUFTLENBQUM7WUFDbEIsQ0FBQztZQUNELE9BQU8sSUFBSSxDQUFDLGdCQUFnQixDQUFDLFFBQVEsQ0FBQyxNQUFNLENBQUMsQ0FBQztRQUMvQyxDQUFDO1FBRUQsZ0JBQWdCO1FBQ2hCLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUM7UUFDNUIsSUFBSSxJQUFJLENBQUMsTUFBTSxLQUFLLENBQUMsRUFBRSxDQUFDO1lBQ3ZCLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFFRCxnREFBZ0Q7UUFDaEQsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBRSxDQUFDLENBQUUsQ0FBQyxFQUFFLENBQUM7WUFDbkMsT0FBTyxJQUFJLENBQUUsQ0FBQyxDQUFFLENBQUM7UUFDbEIsQ0FBQztRQUVELHlFQUF5RTtRQUN6RSxPQUFPLElBQUksQ0FBRSxDQUFDLENBQUUsQ0FBQztJQUNsQixDQUFDO0lBRUQ7O09BRUc7SUFDSyxpQkFBaUIsQ0FBRSxJQUF1QjtRQUNqRCxNQUFNLGVBQWUsR0FBRyxJQUFJLENBQUMsNEJBQTRCLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDaEUsSUFBSSxDQUFDLGVBQWUsRUFBRSxDQUFDO1lBQ3RCLE9BQU8sSUFBSSxHQUFHLEVBQXdCLENBQUM7UUFDeEMsQ0FBQztRQUNELE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxnQ0FBZ0MsQ0FBQyxlQUFlLENBQUMsQ0FBQztRQUN0RSxPQUFPLE1BQU0sQ0FBQztJQUNmLENBQUM7SUFFRDs7T0FFRztJQUNLLGdDQUFnQyxDQUFFLGVBQThCO1FBQ3ZFLE1BQU0sVUFBVSxHQUFHLElBQUksR0FBRyxFQUF3QixDQUFDO1FBRW5ELG9FQUFvRTtRQUNwRSxNQUFNLFdBQVcsR0FBRyxJQUFJLENBQUMsZ0JBQWdCLENBQUMsZUFBZSxDQUFDLENBQUM7UUFFM0QsNkJBQTZCO1FBQzdCLElBQUksRUFBRSxDQUFDLG9CQUFvQixDQUFDLGVBQWUsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsZUFBZSxDQUFDLEVBQUUsQ0FBQztZQUNyRixNQUFNLEVBQUUsSUFBSSxFQUFFLEdBQUcsZUFBZSxDQUFDO1lBRWpDLGtFQUFrRTtZQUNsRSwyRUFBMkU7WUFDM0UsTUFBTSxtQkFBbUIsR0FBRyxJQUFJLENBQUMsMEJBQTBCLENBQUMsZUFBZSxDQUFDLENBQUM7WUFDN0UsS0FBSyxNQUFNLENBQUUsSUFBSSxFQUFFLFFBQVEsQ0FBRSxJQUFJLG1CQUFtQixFQUFFLENBQUM7Z0JBQ3RELFVBQVUsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLFFBQVEsQ0FBQyxDQUFDO1lBQ2hDLENBQUM7WUFFRCxnQ0FBZ0M7WUFDaEMsSUFBSSxFQUFFLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQ3RCLEtBQUssTUFBTSxJQUFJLElBQUksSUFBSSxDQUFDLFVBQVUsRUFBRSxDQUFDO29CQUNwQyxJQUFJLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO3dCQUNwQyxJQUFJLENBQUMsNEJBQTRCLENBQUMsSUFBSSxDQUFDLFVBQVUsRUFBRSxVQUFVLEVBQUUsV0FBVyxDQUFDLENBQUM7b0JBQzdFLENBQUM7Z0JBQ0YsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsMEJBQTBCO1FBQzFCLElBQUksRUFBRSxDQUFDLGlCQUFpQixDQUFDLGVBQWUsQ0FBQyxFQUFFLENBQUM7WUFDM0MsOERBQThEO1lBQzlELE1BQU0sa0JBQWtCLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLGVBQWUsQ0FBQyxDQUFDO1lBRTNFLEtBQUssTUFBTSxNQUFNLElBQUksZUFBZSxDQUFDLE9BQU8sRUFBRSxDQUFDO2dCQUM5QywrQkFBK0I7Z0JBQy9CLElBQUksRUFBRSxDQUFDLHFCQUFxQixDQUFDLE1BQU0sQ0FBQyxJQUFJLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQztvQkFDckQsd0NBQXdDO29CQUN4QyxJQUFJLE1BQU0sQ0FBQyxTQUFTLEVBQUUsQ0FBQzt3QkFDdEIsTUFBTSxxQkFBcUIsR0FBRyxNQUFNLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsRUFBRTs0QkFDdkQsT0FBTyxDQUFDLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsY0FBYztnQ0FDN0MsQ0FBQyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGdCQUFnQixDQUFDO3dCQUM1QyxDQUFDLENBQUMsQ0FBQzt3QkFDSCxJQUFJLHFCQUFxQixFQUFFLENBQUM7NEJBQzNCLFNBQVM7d0JBQ1YsQ0FBQztvQkFDRixDQUFDO29CQUVELE1BQU0sSUFBSSxHQUFHLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDO29CQUNsRSxJQUFJLElBQUksRUFBRSxDQUFDO3dCQUNWLFVBQVUsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFOzRCQUNwQixJQUFJOzRCQUNKLElBQUksRUFBTyxJQUFJLENBQUMsU0FBUyxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUM7NEJBQ3RDLFFBQVEsRUFBRyxDQUFDLENBQUMsTUFBTSxDQUFDLGFBQWE7eUJBQ2pDLENBQUMsQ0FBQztvQkFDSixDQUFDO2dCQUNGLENBQUM7Z0JBRUQsNkJBQTZCO2dCQUM3QixJQUFJLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxNQUFNLENBQUMsSUFBSSxNQUFNLENBQUMsSUFBSSxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7b0JBQ25GLHFDQUFxQztvQkFDckMsSUFBSSxNQUFNLENBQUMsU0FBUyxFQUFFLENBQUM7d0JBQ3RCLE1BQU0scUJBQXFCLEdBQUcsTUFBTSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUU7NEJBQ3ZELE9BQU8sQ0FBQyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGNBQWM7Z0NBQzdDLENBQUMsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxnQkFBZ0IsQ0FBQzt3QkFDNUMsQ0FBQyxDQUFDLENBQUM7d0JBQ0gsSUFBSSxxQkFBcUIsRUFBRSxDQUFDOzRCQUMzQixTQUFTO3dCQUNWLENBQUM7b0JBQ0YsQ0FBQztvQkFFRCxNQUFNLElBQUksR0FBRyxNQUFNLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztvQkFDOUIsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLGVBQWUsQ0FBQyxNQUFNLEVBQUUsa0JBQWtCLENBQUMsQ0FBQztvQkFDOUQsVUFBVSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUU7d0JBQ3BCLElBQUk7d0JBQ0osSUFBSTt3QkFDSixRQUFRLEVBQUcsS0FBSztxQkFDaEIsQ0FBQyxDQUFDO2dCQUNKLENBQUM7Z0JBRUQsNkJBQTZCO2dCQUM3QixJQUFJLEVBQUUsQ0FBQyxhQUFhLENBQUMsTUFBTSxDQUFDLElBQUksTUFBTSxDQUFDLElBQUksSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO29CQUM3RSxxQ0FBcUM7b0JBQ3JDLElBQUksTUFBTSxDQUFDLFNBQVMsRUFBRSxDQUFDO3dCQUN0QixNQUFNLHFCQUFxQixHQUFHLE1BQU0sQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxFQUFFOzRCQUN2RCxPQUFPLENBQUMsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxjQUFjO2dDQUM3QyxDQUFDLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsZ0JBQWdCLENBQUM7d0JBQzVDLENBQUMsQ0FBQyxDQUFDO3dCQUNILElBQUkscUJBQXFCLEVBQUUsQ0FBQzs0QkFDM0IsU0FBUzt3QkFDVixDQUFDO29CQUNGLENBQUM7b0JBRUQsTUFBTSxJQUFJLEdBQUcsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7b0JBQzlCLGtFQUFrRTtvQkFDbEUsSUFBSSxJQUFJLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7b0JBQ3ZDLElBQUksSUFBSSxLQUFLLFNBQVMsSUFBSSxNQUFNLENBQUMsSUFBSSxFQUFFLENBQUM7d0JBQ3ZDLElBQUksR0FBRyxJQUFJLENBQUMsdUJBQXVCLENBQUMsTUFBTSxDQUFDLElBQUksRUFBRSxrQkFBa0IsQ0FBQyxDQUFDO29CQUN0RSxDQUFDO29CQUNELFVBQVUsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFO3dCQUNwQixJQUFJO3dCQUNKLElBQUk7d0JBQ0osUUFBUSxFQUFHLEtBQUs7d0JBQ2hCLFFBQVEsRUFBRyxJQUFJO3FCQUNmLENBQUMsQ0FBQztnQkFDSixDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFFRCxPQUFPLFVBQVUsQ0FBQztJQUNuQixDQUFDO0lBRUQ7OztPQUdHO0lBQ0ssZ0JBQWdCLENBQUUsVUFBeUI7UUFDbEQsTUFBTSxPQUFPLEdBQUcsSUFBSSxHQUFHLEVBQWtCLENBQUM7UUFFMUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxvQkFBb0IsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxlQUFlLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztZQUM3RSxPQUFPLE9BQU8sQ0FBQztRQUNoQixDQUFDO1FBRUQsOEJBQThCO1FBQzlCLEtBQUssTUFBTSxLQUFLLElBQUksVUFBVSxDQUFDLFVBQVUsRUFBRSxDQUFDO1lBQzNDLElBQUksQ0FBQyxLQUFLLENBQUMsSUFBSSxJQUFJLENBQUMsS0FBSyxDQUFDLElBQUk7Z0JBQUUsU0FBUztZQUV6QyxxQkFBcUI7WUFDckIsSUFBSSxTQUFTLEdBQUcsRUFBRSxDQUFDO1lBQ25CLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztnQkFDakMsU0FBUyxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1lBQzdCLENBQUM7aUJBQU0sQ0FBQztnQkFDUCx1Q0FBdUM7Z0JBQ3ZDLFNBQVM7WUFDVixDQUFDO1lBRUQsOENBQThDO1lBQzlDLElBQUksRUFBRSxDQUFDLGlCQUFpQixDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUN0QyxLQUFLLE1BQU0sTUFBTSxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsT0FBTyxFQUFFLENBQUM7b0JBQ3pDLElBQUksRUFBRSxDQUFDLG1CQUFtQixDQUFDLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7d0JBQ3BFLE1BQU0sUUFBUSxHQUFHLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO3dCQUNsQyxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsU0FBUyxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBQzt3QkFDekMsT0FBTyxDQUFDLEdBQUcsQ0FBQyxHQUFHLFNBQVMsSUFBSSxRQUFRLEVBQUUsRUFBRSxJQUFJLENBQUMsQ0FBQztvQkFDL0MsQ0FBQztnQkFDRixDQUFDO1lBQ0YsQ0FBQztpQkFBTSxDQUFDO2dCQUNQLDJEQUEyRDtnQkFDM0Qsd0RBQXdEO2dCQUN4RCxxREFBcUQ7Z0JBQ3JELDJEQUEyRDtnQkFDM0Qsd0RBQXdEO2dCQUN4RCx5REFBeUQ7Z0JBQ3pELHVEQUF1RDtnQkFDdkQsaURBQWlEO2dCQUNqRCxJQUFJLFNBQWdELENBQUM7Z0JBQ3JELElBQUksRUFBRSxDQUFDLG1CQUFtQixDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztvQkFDaEYsTUFBTSxhQUFhLEdBQUcsS0FBSyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsSUFBSSxDQUFDO29CQUMvQyxTQUFTLEdBQUcsSUFBSSxDQUFDLGdDQUFnQyxDQUFDLGFBQWEsRUFBRSxJQUFJLENBQUMseUJBQXlCLENBQUMsQ0FBQztnQkFDbEcsQ0FBQztnQkFDRCxJQUFJLFNBQVMsRUFBRSxDQUFDO29CQUNmLGtEQUFrRDtvQkFDbEQsTUFBTSxlQUFlLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDO29CQUN2RCxJQUFJLENBQUMseUJBQXlCLEdBQUcsU0FBUyxDQUFDLElBQUksQ0FBQztvQkFDaEQsSUFBSSxDQUFDO3dCQUNKLE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQywrQkFBK0IsQ0FBQyxTQUFTLENBQUMsQ0FBQzt3QkFDdkUsS0FBSyxNQUFNLENBQUUsUUFBUSxFQUFFLElBQUksQ0FBRSxJQUFJLGNBQWMsRUFBRSxDQUFDOzRCQUNqRCxPQUFPLENBQUMsR0FBRyxDQUFDLEdBQUcsU0FBUyxJQUFJLFFBQVEsRUFBRSxFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQzt3QkFDcEQsQ0FBQztvQkFDRixDQUFDOzRCQUFTLENBQUM7d0JBQ1YsSUFBSSxDQUFDLHlCQUF5QixHQUFHLGVBQWUsQ0FBQztvQkFDbEQsQ0FBQztvQkFDRCx1REFBdUQ7b0JBQ3ZELG9EQUFvRDtvQkFDcEQsc0RBQXNEO29CQUN0RCxNQUFNLFNBQVMsR0FBRyxJQUFJLENBQUMsK0JBQStCLENBQUMsU0FBUyxDQUFDLENBQUM7b0JBQ2xFLElBQUksU0FBUyxJQUFJLFNBQVMsS0FBSyxTQUFTLEVBQUUsQ0FBQzt3QkFDMUMsT0FBTyxDQUFDLEdBQUcsQ0FBQyxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7b0JBQ25DLENBQUM7Z0JBQ0YsQ0FBQztxQkFBTSxDQUFDO29CQUNQLDREQUE0RDtvQkFDNUQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLENBQUM7b0JBQ3hDLElBQUksSUFBSSxLQUFLLFNBQVMsRUFBRSxDQUFDO3dCQUN4QixPQUFPLENBQUMsR0FBRyxDQUFDLFNBQVMsRUFBRSxJQUFJLENBQUMsQ0FBQztvQkFDOUIsQ0FBQztnQkFDRixDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFFRCxPQUFPLE9BQU8sQ0FBQztJQUNoQixDQUFDO0lBRUQ7OztPQUdHO0lBQ0ssc0JBQXNCLENBQUUsSUFBbUI7UUFDbEQsMEJBQTBCO1FBQzFCLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQzNCLE9BQU8sSUFBSSxDQUFDLElBQUksQ0FBQztRQUNsQixDQUFDO1FBQ0QsMkNBQTJDO1FBQzNDLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDekMsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLHNCQUFzQixDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsQ0FBQztZQUMxRCxJQUFJLElBQUksRUFBRSxDQUFDO2dCQUNWLE9BQU8sR0FBRyxJQUFJLElBQUksSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUNwQyxDQUFDO1FBQ0YsQ0FBQztRQUNELGtEQUFrRDtRQUNsRCxJQUFJLEVBQUUsQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLENBQUM7WUFDOUIsSUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxXQUFXLEVBQUUsQ0FBQztZQUN4RCxzQ0FBc0M7WUFDdEMsT0FBTyxJQUFJLENBQUMsc0JBQXNCLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQy9DLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7O09BRUc7SUFDSyw0QkFBNEIsQ0FDbkMsSUFBbUIsRUFDbkIsVUFBcUMsRUFDckMsY0FBbUMsSUFBSSxHQUFHLEVBQUU7UUFFNUMsZ0NBQWdDO1FBQ2hDLElBQUksRUFBRSxDQUFDLGtCQUFrQixDQUFDLElBQUksQ0FBQztZQUM5QixJQUFJLENBQUMsYUFBYSxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFdBQVcsRUFBRSxDQUFDO1lBQ3hELE1BQU0sRUFBRSxJQUFJLEVBQUUsR0FBRyxJQUFJLENBQUM7WUFFdEIsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztnQkFDekMsMENBQTBDO2dCQUMxQyxJQUFJLElBQUksQ0FBQyxVQUFVLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVyxFQUFFLENBQUM7b0JBQ3hELE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDO29CQUM3QixJQUFJLElBQUksRUFBRSxDQUFDO3dCQUNWLG9GQUFvRjt3QkFDcEYsTUFBTSxXQUFXLEdBQUcsSUFBSSxDQUFDLHNCQUFzQixDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQzt3QkFDNUQsSUFBSSxJQUFJLEdBQUcsV0FBVyxDQUFDLENBQUMsQ0FBQyxXQUFXLENBQUMsR0FBRyxDQUFDLFdBQVcsQ0FBQyxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUM7d0JBQ2xFLDBFQUEwRTt3QkFDMUUsSUFBSSxDQUFDLElBQUksSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsRUFBRSxDQUFDOzRCQUMxQyxJQUFJLEdBQUcsV0FBVyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxDQUFDO3dCQUN6QyxDQUFDO3dCQUNELHNEQUFzRDt3QkFDdEQsb0RBQW9EO3dCQUNwRCxpREFBaUQ7d0JBQ2pELElBQUksQ0FBQyxJQUFJLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLEVBQUUsQ0FBQzs0QkFDMUMsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxDQUFDOzRCQUMxRCxJQUFJLEtBQUssRUFBRSxDQUFDO2dDQUNYLElBQUksR0FBRyxLQUFLLENBQUMsT0FBTyxDQUFDLEtBQUssRUFBRSxHQUFHLENBQUMsQ0FBQzs0QkFDbEMsQ0FBQzt3QkFDRixDQUFDO3dCQUNELElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQzs0QkFDWCxJQUFJLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLElBQUksQ0FBQyxLQUFLLEVBQUUsV0FBVyxDQUFDLENBQUM7d0JBQy9ELENBQUM7d0JBQ0Qsd0RBQXdEO3dCQUN4RCxvREFBb0Q7d0JBQ3BELHNEQUFzRDt3QkFDdEQsdURBQXVEO3dCQUN2RCx1REFBdUQ7d0JBQ3ZELHFEQUFxRDt3QkFDckQsdURBQXVEO3dCQUN2RCw0Q0FBNEM7d0JBQzVDLE1BQU0sUUFBUSxHQUFHLFVBQVUsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7d0JBQ3RDLE1BQU0sY0FBYyxHQUFHLENBQUMsSUFBSSxJQUFJLElBQUksQ0FBQyxRQUFRLENBQUMsU0FBUyxDQUFDLENBQUM7d0JBQ3pELE1BQU0sZUFBZSxHQUFHLFFBQVEsQ0FBQyxDQUFDLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsS0FBSyxTQUFTLENBQUMsQ0FBQyxDQUFDLEtBQUssQ0FBQzt3QkFDOUUsSUFBSSxlQUFlLElBQUksY0FBYyxFQUFFLENBQUM7NEJBQ3ZDLGdEQUFnRDt3QkFDakQsQ0FBQzs2QkFBTSxDQUFDOzRCQUNQLFVBQVUsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFO2dDQUNwQixJQUFJO2dDQUNKLElBQUk7Z0NBQ0osUUFBUSxFQUFHLFFBQVEsQ0FBQyxDQUFDLENBQUMsUUFBUSxDQUFDLFFBQVEsQ0FBQyxDQUFDLENBQUMsS0FBSzs2QkFDL0MsQ0FBQyxDQUFDO3dCQUNKLENBQUM7b0JBQ0YsQ0FBQztnQkFDRixDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFFRCwrQ0FBK0M7UUFDL0MsSUFBSSxFQUFFLENBQUMsZ0JBQWdCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUMvQixNQUFNLEVBQUUsR0FBRyxJQUFJLENBQUMsVUFBVSxDQUFDO1lBQzNCLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLEVBQUUsQ0FBQztnQkFDcEMsRUFBRSxDQUFDLElBQUksRUFBRSxJQUFJLEtBQUssUUFBUTtnQkFDMUIsRUFBRSxDQUFDLFlBQVksQ0FBQyxFQUFFLENBQUMsVUFBVSxDQUFDO2dCQUM5QixFQUFFLENBQUMsVUFBVSxDQUFDLElBQUksS0FBSyxRQUFRLEVBQUUsQ0FBQztnQkFDbEMsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQztnQkFDNUIsSUFBSSxJQUFJLENBQUMsTUFBTSxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUUsQ0FBQyxDQUFFLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVyxFQUFFLENBQUM7b0JBQ3RFLDhDQUE4QztvQkFDOUMsTUFBTSxDQUFFLEFBQUQsRUFBRyxRQUFRLENBQUUsR0FBRyxJQUFJLENBQUM7b0JBQzVCLElBQUksRUFBRSxDQUFDLHlCQUF5QixDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7d0JBQzVDLEtBQUssTUFBTSxJQUFJLElBQUksUUFBUSxDQUFDLFVBQVUsRUFBRSxDQUFDOzRCQUN4QyxJQUFJLEVBQUUsQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dDQUNqRSxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztnQ0FDNUIsVUFBVSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUU7b0NBQ3BCLElBQUk7b0NBQ0osSUFBSSxFQUFPLElBQUksQ0FBQyx3QkFBd0IsQ0FBQyxJQUFJLENBQUMsV0FBVyxDQUFDO29DQUMxRCxRQUFRLEVBQUcsS0FBSztpQ0FDaEIsQ0FBQyxDQUFDOzRCQUNKLENBQUM7d0JBQ0YsQ0FBQztvQkFDRixDQUFDO3lCQUFNLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO3dCQUN0Qyx5REFBeUQ7d0JBQ3pELHVEQUF1RDt3QkFDdkQscURBQXFEO3dCQUNyRCw4Q0FBOEM7d0JBQzlDLHdEQUF3RDt3QkFDeEQscURBQXFEO3dCQUNyRCxvREFBb0Q7d0JBQ3BELHdCQUF3Qjt3QkFDeEIsTUFBTSxTQUFTLEdBQUcsUUFBUSxDQUFDLElBQUksQ0FBQzt3QkFDaEMsS0FBSyxNQUFNLENBQUUsR0FBRyxFQUFFLElBQUksQ0FBRSxJQUFJLFdBQVcsRUFBRSxDQUFDOzRCQUN6QyxJQUFJLENBQUMsR0FBRyxDQUFDLFVBQVUsQ0FBQyxHQUFHLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FBQztnQ0FDdEMsU0FBUzs0QkFDVixDQUFDOzRCQUNELE1BQU0sSUFBSSxHQUFHLEdBQUcsQ0FBQyxLQUFLLENBQUMsU0FBUyxDQUFDLE1BQU0sR0FBRyxDQUFDLENBQUMsQ0FBQzs0QkFDN0MsVUFBVSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUU7Z0NBQ3BCLElBQUk7Z0NBQ0osSUFBSTtnQ0FDSixRQUFRLEVBQUcsS0FBSzs2QkFDaEIsQ0FBQyxDQUFDO3dCQUNKLENBQUM7b0JBQ0YsQ0FBQztnQkFDRixDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7SUFDRixDQUFDO0lBRUQ7O09BRUc7SUFDSyxzQkFBc0IsQ0FBRSxTQUE4QjtRQUM3RCxNQUFNLFVBQVUsR0FBRyxJQUFJLEdBQUcsRUFBd0IsQ0FBQztRQUVuRCxLQUFLLE1BQU0sTUFBTSxJQUFJLFNBQVMsQ0FBQyxPQUFPLEVBQUUsQ0FBQztZQUN4QywrQkFBK0I7WUFDL0IsSUFBSSxFQUFFLENBQUMscUJBQXFCLENBQUMsTUFBTSxDQUFDLElBQUksTUFBTSxDQUFDLElBQUksRUFBRSxDQUFDO2dCQUNyRCx3Q0FBd0M7Z0JBQ3hDLElBQUksTUFBTSxDQUFDLFNBQVMsRUFBRSxDQUFDO29CQUN0QixNQUFNLHFCQUFxQixHQUFHLE1BQU0sQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGNBQWM7d0JBQzFGLENBQUMsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxnQkFBZ0IsQ0FBQyxDQUFDO29CQUNqRCxJQUFJLHFCQUFxQixFQUFFLENBQUM7d0JBQzNCLFNBQVM7b0JBQ1YsQ0FBQztnQkFDRixDQUFDO2dCQUVELE1BQU0sSUFBSSxHQUFHLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDO2dCQUNsRSxJQUFJLElBQUksRUFBRSxDQUFDO29CQUNWLGtFQUFrRTtvQkFDbEUsSUFBSSxJQUFJLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7b0JBQ3ZDLElBQUksSUFBSSxLQUFLLFNBQVMsSUFBSSxNQUFNLENBQUMsV0FBVyxFQUFFLENBQUM7d0JBQzlDLElBQUksR0FBRyxJQUFJLENBQUMsd0JBQXdCLENBQUMsTUFBTSxDQUFDLFdBQVcsQ0FBQyxDQUFDO29CQUMxRCxDQUFDO29CQUNELFVBQVUsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFO3dCQUNwQixJQUFJO3dCQUNKLElBQUk7d0JBQ0osUUFBUSxFQUFHLENBQUMsQ0FBQyxNQUFNLENBQUMsYUFBYTtxQkFDakMsQ0FBQyxDQUFDO2dCQUNKLENBQUM7WUFDRixDQUFDO1lBRUQsNkJBQTZCO1lBQzdCLElBQUksRUFBRSxDQUFDLG1CQUFtQixDQUFDLE1BQU0sQ0FBQyxJQUFJLE1BQU0sQ0FBQyxJQUFJLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztnQkFDbkYscUNBQXFDO2dCQUNyQyxJQUFJLE1BQU0sQ0FBQyxTQUFTLEVBQUUsQ0FBQztvQkFDdEIsTUFBTSxxQkFBcUIsR0FBRyxNQUFNLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxjQUFjO3dCQUMxRixDQUFDLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsZ0JBQWdCLENBQUMsQ0FBQztvQkFDakQsSUFBSSxxQkFBcUIsRUFBRSxDQUFDO3dCQUMzQixTQUFTO29CQUNWLENBQUM7Z0JBQ0YsQ0FBQztnQkFFRCxNQUFNLElBQUksR0FBRyxNQUFNLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztnQkFDOUIsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLGVBQWUsQ0FBQyxNQUFNLENBQUMsQ0FBQztnQkFDMUMsVUFBVSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUU7b0JBQ3BCLElBQUk7b0JBQ0osSUFBSTtvQkFDSixRQUFRLEVBQUcsS0FBSztpQkFDaEIsQ0FBQyxDQUFDO1lBQ0osQ0FBQztZQUVELDZCQUE2QjtZQUM3QixJQUFJLEVBQUUsQ0FBQyxhQUFhLENBQUMsTUFBTSxDQUFDLElBQUksTUFBTSxDQUFDLElBQUksSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUM3RSxxQ0FBcUM7Z0JBQ3JDLElBQUksTUFBTSxDQUFDLFNBQVMsRUFBRSxDQUFDO29CQUN0QixNQUFNLHFCQUFxQixHQUFHLE1BQU0sQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGNBQWM7d0JBQzFGLENBQUMsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxnQkFBZ0IsQ0FBQyxDQUFDO29CQUNqRCxJQUFJLHFCQUFxQixFQUFFLENBQUM7d0JBQzNCLFNBQVM7b0JBQ1YsQ0FBQztnQkFDRixDQUFDO2dCQUVELE1BQU0sSUFBSSxHQUFHLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO2dCQUM5QixrRUFBa0U7Z0JBQ2xFLElBQUksSUFBSSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxDQUFDO2dCQUN2QyxJQUFJLElBQUksS0FBSyxTQUFTLElBQUksTUFBTSxDQUFDLElBQUksRUFBRSxDQUFDO29CQUN2QyxJQUFJLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDbEQsQ0FBQztnQkFDRCxVQUFVLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRTtvQkFDcEIsSUFBSTtvQkFDSixJQUFJO29CQUNKLFFBQVEsRUFBRyxLQUFLO29CQUNoQixRQUFRLEVBQUcsSUFBSTtpQkFDZixDQUFDLENBQUM7WUFDSixDQUFDO1FBQ0YsQ0FBQztRQUVELE9BQU8sVUFBVSxDQUFDO0lBQ25CLENBQUM7SUFFRDs7OztPQUlHO0lBQ0sseUJBQXlCLENBQUUsU0FBNkI7UUFDL0QsTUFBTSxhQUFhLEdBQUcsSUFBSSxHQUFHLEVBQWtCLENBQUM7UUFFaEQsS0FBSyxNQUFNLE1BQU0sSUFBSSxTQUFTLENBQUMsT0FBTyxFQUFFLENBQUM7WUFDeEMsSUFBSSxFQUFFLENBQUMscUJBQXFCLENBQUMsTUFBTSxDQUFDLElBQUksTUFBTSxDQUFDLElBQUksSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUNyRix5RUFBeUU7Z0JBQ3pFLGdFQUFnRTtnQkFDaEUsTUFBTSxJQUFJLEdBQUcsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7Z0JBQzlCLElBQUksTUFBTSxDQUFDLElBQUksRUFBRSxDQUFDO29CQUNqQixhQUFhLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsU0FBUyxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDO2dCQUN0RCxDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFFRCxPQUFPLGFBQWEsQ0FBQztJQUN0QixDQUFDO0lBRUQ7O09BRUc7SUFDSyxlQUFlLENBQUUsTUFBNEIsRUFBRSxrQkFBd0M7UUFDOUYsTUFBTSxNQUFNLEdBQUcsTUFBTSxDQUFDLFVBQVUsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLEVBQUU7WUFDNUMsTUFBTSxTQUFTLEdBQUcsRUFBRSxDQUFDLFlBQVksQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxLQUFLLENBQUM7WUFDeEUsTUFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDN0MsT0FBTyxHQUFHLFNBQVMsS0FBSyxTQUFTLEVBQUUsQ0FBQztRQUNyQyxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7UUFFZCxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsZUFBZSxDQUFDLE1BQU0sRUFBRSxrQkFBa0IsQ0FBQyxDQUFDO1FBRXBFLElBQUksTUFBTSxFQUFFLENBQUM7WUFDWixPQUFPLElBQUksTUFBTSxRQUFRLFVBQVUsRUFBRSxDQUFDO1FBQ3ZDLENBQUM7UUFDRCxPQUFPLFNBQVMsVUFBVSxFQUFFLENBQUM7SUFDOUIsQ0FBQztJQUVEOzs7VUFHRztJQUNLLDBCQUEwQixDQUFFLFVBQW9EO1FBRXZGLE1BQU0sVUFBVSxHQUFHLElBQUksR0FBRyxFQUF3QixDQUFDO1FBRW5ELHFDQUFxQztRQUNyQyxLQUFLLE1BQU0sS0FBSyxJQUFJLFVBQVUsQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUMzQyxJQUFJLEtBQUssQ0FBQyxJQUFJLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssTUFBTSxJQUFJLEtBQUssQ0FBQyxJQUFJLEVBQUUsQ0FBQztnQkFDM0YsdURBQXVEO2dCQUN2RCxJQUFJLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztvQkFDeEMsTUFBTSxRQUFRLEdBQUcsRUFBRSxDQUFDLFlBQVksQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQzt3QkFDcEQsQ0FBQyxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUk7d0JBQzFCLENBQUMsQ0FBQyxFQUFFLENBQUM7b0JBRU4saUVBQWlFO29CQUNqRSxNQUFNLElBQUksR0FBRyxRQUFRO3dCQUNwQixDQUFDLENBQUMsSUFBSSxDQUFDLGdDQUFnQyxDQUFDLFFBQVEsRUFBRSxJQUFJLENBQUMseUJBQXlCLENBQUM7d0JBQ2pGLENBQUMsQ0FBQyxTQUFTLENBQUM7b0JBQ2IsSUFBSSxJQUFJLEVBQUUsQ0FBQzt3QkFDVixNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsK0JBQStCLENBQUMsSUFBSSxDQUFDLENBQUM7d0JBQ2xFLEtBQUssTUFBTSxDQUFFLFFBQVEsRUFBRSxJQUFJLENBQUUsSUFBSSxjQUFjLEVBQUUsQ0FBQzs0QkFDakQsVUFBVSxDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLENBQUM7d0JBQ2hDLENBQUM7b0JBQ0YsQ0FBQztnQkFDRixDQUFDO2dCQUNELCtFQUErRTtxQkFDMUUsSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7b0JBQzNDLEtBQUssTUFBTSxNQUFNLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxPQUFPLEVBQUUsQ0FBQzt3QkFDekMsSUFBSSxFQUFFLENBQUMsbUJBQW1CLENBQUMsTUFBTSxDQUFDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQzs0QkFDcEUsTUFBTSxRQUFRLEdBQUcsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7NEJBQ2xDLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxDQUFDOzRCQUN6QyxVQUFVLENBQUMsR0FBRyxDQUFDLFFBQVEsRUFBRTtnQ0FDeEIsSUFBSSxFQUFPLFFBQVE7Z0NBQ25CLElBQUk7Z0NBQ0osUUFBUSxFQUFHLENBQUMsQ0FBQyxNQUFNLENBQUMsYUFBYTs2QkFDakMsQ0FBQyxDQUFDO3dCQUNKLENBQUM7b0JBQ0YsQ0FBQztnQkFDRixDQUFDO2dCQUNELGtEQUFrRDtnQkFDbEQsTUFBTTtZQUNQLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxVQUFVLENBQUM7SUFDbkIsQ0FBQztJQUVEOztVQUVHO0lBQ0g7O09BRUc7SUFDSyxTQUFTLENBQUUsUUFBc0I7UUFDeEMsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQ2YsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELFFBQVEsUUFBUSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ3hCLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxhQUFhO2dCQUMvQixPQUFPLFFBQVEsQ0FBQztZQUNqQixLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsYUFBYTtnQkFDL0IsT0FBTyxRQUFRLENBQUM7WUFDakIsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGNBQWM7Z0JBQ2hDLE9BQU8sU0FBUyxDQUFDO1lBQ2xCLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxnQkFBZ0I7Z0JBQ2xDLE9BQU8sV0FBVyxDQUFDO1lBQ3BCLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxXQUFXO2dCQUM3QixPQUFPLE1BQU0sQ0FBQztZQUNmLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxVQUFVO2dCQUM1QixPQUFPLEtBQUssQ0FBQztZQUNkLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxjQUFjO2dCQUNoQyxPQUFPLFNBQVMsQ0FBQztZQUNsQixLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVztnQkFDN0IsT0FBTyxNQUFNLENBQUM7WUFDZixLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsU0FBUztnQkFDM0IsT0FBTyxTQUFXLElBQUksQ0FBQyxTQUFTLENBQUUsUUFBNkIsQ0FBQyxXQUFXLENBQUcsR0FBRyxDQUFDO1lBQ25GLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxXQUFXLENBQUMsQ0FBQyxDQUFDO2dCQUNoQyxnRUFBZ0U7Z0JBQ2hFLE1BQU0sT0FBTyxHQUFHLFFBQThCLENBQUM7Z0JBQy9DLE1BQU0sS0FBSyxHQUFhLEVBQUUsQ0FBQztnQkFDM0IsS0FBSyxNQUFNLE1BQU0sSUFBSSxPQUFPLENBQUMsT0FBTyxFQUFFLENBQUM7b0JBQ3RDLElBQUksRUFBRSxDQUFDLG1CQUFtQixDQUFDLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7d0JBQ3BFLE1BQU0sUUFBUSxHQUFHLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO3dCQUNsQyxNQUFNLFFBQVEsR0FBRyxNQUFNLENBQUMsYUFBYSxDQUFDLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQzt3QkFDakQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7d0JBQ3pDLEtBQUssQ0FBQyxJQUFJLENBQUMsR0FBRyxRQUFRLEdBQUcsUUFBUSxLQUFLLElBQUksRUFBRSxDQUFDLENBQUM7b0JBQy9DLENBQUM7Z0JBQ0YsQ0FBQztnQkFDRCxPQUFPLEtBQUssS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1lBQ2xDLENBQUM7WUFDRCxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVyxDQUFDLENBQUMsQ0FBQztnQkFDaEMseURBQXlEO2dCQUN6RCxNQUFNLEVBQUUsT0FBTyxFQUFFLEdBQUksUUFBK0IsQ0FBQztnQkFDckQsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7b0JBQ2pDLG1FQUFtRTtvQkFDbkUsT0FBTyxJQUFJLE9BQU8sQ0FBQyxJQUFJLEdBQUcsQ0FBQztnQkFDNUIsQ0FBQztnQkFDRCxJQUFJLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDO29CQUNsQyxPQUFPLE9BQU8sQ0FBQyxJQUFJLENBQUM7Z0JBQ3JCLENBQUM7Z0JBQ0QsSUFBSSxPQUFPLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVyxFQUFFLENBQUM7b0JBQ2hELE9BQU8sTUFBTSxDQUFDO2dCQUNmLENBQUM7Z0JBQ0QsSUFBSSxPQUFPLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsWUFBWSxFQUFFLENBQUM7b0JBQ2pELE9BQU8sT0FBTyxDQUFDO2dCQUNoQixDQUFDO2dCQUNELElBQUksT0FBTyxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFdBQVcsRUFBRSxDQUFDO29CQUNoRCxPQUFPLE1BQU0sQ0FBQztnQkFDZixDQUFDO2dCQUNELE9BQU8sU0FBUyxDQUFDO1lBQ2xCLENBQUM7WUFDRCxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsYUFBYSxDQUFDLENBQUMsQ0FBQztnQkFDbEMsc0VBQXNFO2dCQUN0RSxNQUFNLE9BQU8sR0FBRyxRQUFnQyxDQUFDO2dCQUVqRCxzRUFBc0U7Z0JBQ3RFLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxPQUFPLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztvQkFDMUMsTUFBTSxpQkFBaUIsR0FBRyxJQUFJLENBQUMsMkJBQTJCLENBQUMsT0FBTyxDQUFDLENBQUM7b0JBQ3BFLElBQUksaUJBQWlCLEtBQUssU0FBUyxFQUFFLENBQUM7d0JBQ3JDLE9BQU8saUJBQWlCLENBQUM7b0JBQzFCLENBQUM7b0JBQ0QsNERBQTREO29CQUM1RCxPQUFPLFNBQVMsQ0FBQztnQkFDbEIsQ0FBQztnQkFFRCxNQUFNLFFBQVEsR0FBRyxFQUFFLENBQUMsWUFBWSxDQUFDLE9BQU8sQ0FBQyxRQUFRLENBQUMsQ0FBQyxDQUFDLENBQUMsT0FBTyxDQUFDLFFBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQztnQkFFdkYsK0RBQStEO2dCQUMvRCxpRUFBaUU7Z0JBQ2pFLHVEQUF1RDtnQkFDdkQsTUFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLDBCQUEwQixDQUFDLFFBQVEsRUFBRSxPQUFPLENBQUMsYUFBYSxFQUFFLE9BQU8sQ0FBQyxDQUFDO2dCQUM1RixJQUFJLFNBQVMsS0FBSyxTQUFTLEVBQUUsQ0FBQztvQkFDN0IsT0FBTyxTQUFTLENBQUM7Z0JBQ2xCLENBQUM7Z0JBRUQsK0JBQStCO2dCQUMvQixNQUFNLFFBQVEsR0FBRyxDQUFDLE9BQU8sQ0FBQyxhQUFhLElBQUksRUFBRSxDQUFDLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDO2dCQUMvRSxPQUFPLEdBQUcsUUFBUSxJQUFJLFFBQVEsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQztZQUM5QyxDQUFDO1lBQ0QsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFNBQVMsQ0FBQyxDQUFDLENBQUM7Z0JBQzlCLDBDQUEwQztnQkFDMUMsTUFBTSxTQUFTLEdBQUcsUUFBNEIsQ0FBQztnQkFDL0MsTUFBTSxLQUFLLEdBQUcsU0FBUyxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7Z0JBQzFELE9BQU8sS0FBSyxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQztZQUMxQixDQUFDO1lBQ0QsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGdCQUFnQixDQUFDLENBQUMsQ0FBQztnQkFDckMsK0NBQStDO2dCQUMvQyxNQUFNLGdCQUFnQixHQUFHLFFBQW1DLENBQUM7Z0JBQzdELE1BQU0sS0FBSyxHQUFHLGdCQUFnQixDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7Z0JBQ2pFLE9BQU8sS0FBSyxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQztZQUMxQixDQUFDO1lBQ0QsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFNBQVMsQ0FBQyxDQUFDLENBQUM7Z0JBQzlCLDJDQUEyQztnQkFDM0MsTUFBTSxTQUFTLEdBQUcsUUFBNEIsQ0FBQztnQkFDL0MsTUFBTSxRQUFRLEdBQUcsU0FBUyxDQUFDLFFBQVEsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLElBQW1CLENBQUMsQ0FBQyxDQUFDO2dCQUNyRixPQUFPLElBQUksUUFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDO1lBQ25DLENBQUM7WUFDRCxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsWUFBWSxDQUFDLENBQUMsQ0FBQztnQkFDakMsNENBQTRDO2dCQUM1QyxNQUFNLFlBQVksR0FBRyxRQUErQixDQUFDO2dCQUNyRCxPQUFPLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFHLEdBQUcsQ0FBQztZQUNsRCxDQUFDO1lBQ0QsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFFBQVEsQ0FBQyxDQUFDLENBQUM7Z0JBQzdCLDRCQUE0QjtnQkFDNUIsTUFBTSxRQUFRLEdBQUcsUUFBMkIsQ0FBQztnQkFDN0MsT0FBTyxNQUFRLElBQUksQ0FBQyxTQUFTLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDaEQsQ0FBQztZQUNELEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxpQkFBaUIsQ0FBQyxDQUFDLENBQUM7Z0JBQ3RDLHNDQUFzQztnQkFDdEMsT0FBTyxJQUFJLENBQUMsU0FBUyxDQUFFLFFBQXFDLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDcEUsQ0FBQztZQUNELEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxpQkFBaUIsQ0FBQyxDQUFDLENBQUM7Z0JBQ3RDLDhCQUE4QjtnQkFDOUIsTUFBTSxPQUFPLEdBQUcsUUFBb0MsQ0FBQztnQkFDckQsdURBQXVEO2dCQUN2RCwyREFBMkQ7Z0JBQzNELDREQUE0RDtnQkFDNUQsd0NBQXdDO2dCQUN4Qyx3QkFBd0I7Z0JBQ3hCLElBQUksVUFBVSxHQUFnQixPQUFPLENBQUMsVUFBVSxDQUFDO2dCQUNqRCxPQUFPLEVBQUUsQ0FBQyx1QkFBdUIsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO29CQUMvQyxVQUFVLEdBQUcsVUFBVSxDQUFDLElBQUksQ0FBQztnQkFDOUIsQ0FBQztnQkFDRCxrRUFBa0U7Z0JBQ2xFLHNEQUFzRDtnQkFDdEQsK0RBQStEO2dCQUMvRCw0REFBNEQ7Z0JBQzVELG9DQUFvQztnQkFDcEMsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLFVBQVUsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsVUFBVSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7b0JBQzVFLE1BQU0sU0FBUyxHQUFHLFVBQVUsQ0FBQyxRQUFRLENBQUMsSUFBSSxDQUFDO29CQUMzQyxNQUFNLFlBQVksR0FBRyxJQUFJLENBQUMsd0JBQXdCLENBQUMsU0FBUyxFQUFFLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxDQUFDO29CQUM5RixNQUFNLFFBQVEsR0FBRyxZQUFZLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxZQUFZLENBQUMsQ0FBQyxDQUFDLENBQUMsU0FBUyxDQUFDO29CQUNuRixJQUFJLENBQUMsUUFBUSxFQUFFLENBQUM7d0JBQ2YsT0FBTyxTQUFTLENBQUM7b0JBQ2xCLENBQUM7b0JBQ0QsSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsT0FBTyxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxPQUFPLENBQUMsU0FBUyxDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7d0JBQy9GLE1BQU0sWUFBWSxHQUFHLFFBQVEsQ0FBQyxPQUFPLENBQUMsU0FBUyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUM7d0JBQ2xFLE1BQU0sT0FBTyxHQUFHLFFBQVEsQ0FBRSxZQUFZLENBQUUsQ0FBQzt3QkFDekMsTUFBTSxhQUFhLEdBQUcsT0FBTyxLQUFLLFNBQVMsQ0FBQyxDQUFDLENBQUMsU0FBUyxDQUFDLENBQUMsQ0FBQyxPQUFPLENBQUM7d0JBQ2xFLE9BQU8sYUFBYSxDQUFDO29CQUN0QixDQUFDO29CQUNELE1BQU0sV0FBVyxHQUFHLFFBQVEsQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7b0JBQ3pDLE9BQU8sV0FBVyxDQUFDO2dCQUNwQixDQUFDO2dCQUNELElBQUksVUFBVSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsVUFBVSxDQUFDLENBQUM7Z0JBQzVDLE1BQU0sU0FBUyxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsT0FBTyxDQUFDLFNBQVMsQ0FBQyxDQUFDO2dCQUNwRCwyRUFBMkU7Z0JBQzNFLElBQUksVUFBVSxLQUFLLFFBQVEsSUFBSSxFQUFFLENBQUMsbUJBQW1CLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztvQkFDbkUsTUFBTSxPQUFPLEdBQUcsRUFBRSxDQUFDLFlBQVksQ0FBQyxVQUFVLENBQUMsUUFBUSxDQUFDLENBQUMsQ0FBQyxDQUFDLFVBQVUsQ0FBQyxRQUFRLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUM7b0JBQ3JGLElBQUksT0FBTyxFQUFFLENBQUM7d0JBQ2IsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLGdDQUFnQyxDQUFDLE9BQU8sRUFBRSxJQUFJLENBQUMseUJBQXlCLENBQUMsQ0FBQzt3QkFDNUYsSUFBSSxJQUFJLEVBQUUsQ0FBQzs0QkFDVixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsK0JBQStCLENBQUMsSUFBSSxDQUFDLENBQUM7NEJBQzVELElBQUksUUFBUSxFQUFFLENBQUM7Z0NBQ2QsVUFBVSxHQUFHLFFBQVEsQ0FBQzs0QkFDdkIsQ0FBQzt3QkFDRixDQUFDO29CQUNGLENBQUM7Z0JBQ0YsQ0FBQztnQkFDRCx5REFBeUQ7Z0JBQ3pELCtEQUErRDtnQkFDL0QsNkRBQTZEO2dCQUM3RCwyREFBMkQ7Z0JBQzNELHdDQUF3QztnQkFDeEMsTUFBTSxnQkFBZ0IsR0FBRyxVQUFVLEtBQUssU0FBUyxJQUFJLFVBQVUsS0FBSyxRQUFRLENBQUM7Z0JBQzdFLE1BQU0sZUFBZSxHQUFHLFNBQVMsS0FBSyxTQUFTLENBQUM7Z0JBQ2hELElBQUksZ0JBQWdCLElBQUksZUFBZSxFQUFFLENBQUM7b0JBQ3pDLE9BQU8sU0FBUyxDQUFDO2dCQUNsQixDQUFDO2dCQUNELE9BQU8sR0FBRyxVQUFVLElBQUksU0FBUyxHQUFHLENBQUM7WUFDdEMsQ0FBQztZQUNELEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxZQUFZLENBQUMsQ0FBQyxDQUFDO2dCQUNqQywyQ0FBMkM7Z0JBQzNDLE1BQU0sTUFBTSxHQUFHLFFBQStCLENBQUM7Z0JBQy9DLE1BQU0sUUFBUSxHQUFHLEVBQUUsQ0FBQyxVQUFVLENBQUUsTUFBTSxDQUFDLFFBQVEsQ0FBRSxDQUFDO2dCQUNsRCxPQUFPLEdBQUcsUUFBUSxJQUFJLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDckQsQ0FBQztZQUNELEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxTQUFTLENBQUMsQ0FBQyxDQUFDO2dCQUM5QixpRUFBaUU7Z0JBQ2pFLGlFQUFpRTtnQkFDakUsNERBQTREO2dCQUM1RCxpRUFBaUU7Z0JBQ2pFLCtEQUErRDtnQkFDL0QsbUJBQW1CO2dCQUNuQixNQUFNLFNBQVMsR0FBRyxRQUE0QixDQUFDO2dCQUMvQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsU0FBUyxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7b0JBQ3pDLE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxTQUFTLENBQUMsUUFBUSxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMseUJBQXlCLENBQUMsQ0FBQztvQkFDbEcsSUFBSSxLQUFLLEVBQUUsQ0FBQzt3QkFDWCxPQUFPLEtBQUssQ0FBQztvQkFDZCxDQUFDO2dCQUNGLENBQUM7Z0JBQ0QsT0FBTyxTQUFTLENBQUM7WUFDbEIsQ0FBQztZQUNEO2dCQUNDLG9EQUFvRDtnQkFDcEQsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztJQUNGLENBQUM7SUFFRDs7O1VBR0c7SUFDSyxlQUFlLENBQUUsTUFBNEIsRUFBRSxrQkFBd0M7UUFDOUYsd0RBQXdEO1FBQ3hELElBQUksTUFBTSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ2pCLE9BQU8sSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDcEMsQ0FBQztRQUVELG9FQUFvRTtRQUNwRSxJQUFJLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUNqQixPQUFPLElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxNQUFNLENBQUMsSUFBSSxFQUFFLGtCQUFrQixDQUFDLENBQUM7UUFDdEUsQ0FBQztRQUVELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7VUFFRztJQUNLLHVCQUF1QixDQUFFLElBQWMsRUFBRSxrQkFBd0M7UUFDeEYsTUFBTSxXQUFXLEdBQUcsSUFBSSxHQUFHLEVBQVUsQ0FBQztRQUV0QyxNQUFNLEtBQUssR0FBRyxDQUFDLElBQWEsRUFBUSxFQUFFO1lBQ3JDLElBQUksRUFBRSxDQUFDLGlCQUFpQixDQUFDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztnQkFDbkQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLElBQUksQ0FBQyxVQUFVLEVBQUUsU0FBUyxFQUFFLGtCQUFrQixDQUFDLENBQUM7Z0JBQzNGLElBQUksSUFBSSxLQUFLLFNBQVMsRUFBRSxDQUFDO29CQUN4QixXQUFXLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO2dCQUN2QixDQUFDO1lBQ0YsQ0FBQztZQUNELEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxFQUFFLEtBQUssQ0FBQyxDQUFDO1FBQzlCLENBQUMsQ0FBQztRQUVGLEtBQUssQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUVaLElBQUksV0FBVyxDQUFDLElBQUksS0FBSyxDQUFDLEVBQUUsQ0FBQztZQUM1QixPQUFPLE1BQU0sQ0FBQztRQUNmLENBQUM7UUFDRCxJQUFJLFdBQVcsQ0FBQyxJQUFJLEtBQUssQ0FBQyxFQUFFLENBQUM7WUFDNUIsT0FBTyxLQUFLLENBQUMsSUFBSSxDQUFDLFdBQVcsQ0FBQyxDQUFFLENBQUMsQ0FBRSxDQUFDO1FBQ3JDLENBQUM7UUFDRCxPQUFPLEtBQUssQ0FBQyxJQUFJLENBQUMsV0FBVyxDQUFDLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxDQUFDO0lBQzVDLENBQUM7SUFFRDs7T0FFRztJQUNLLHdCQUF3QixDQUMvQixXQUEwQixFQUMxQixXQUFpQyxFQUNqQyxrQkFBd0M7UUFFeEMsUUFBUSxXQUFXLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDM0IsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGFBQWE7Z0JBQy9CLE9BQU8sUUFBUSxDQUFDO1lBQ2pCLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxjQUFjO2dCQUNoQyxPQUFPLFFBQVEsQ0FBQztZQUNqQixLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVyxDQUFDO1lBQy9CLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxZQUFZO2dCQUM5QixPQUFPLFNBQVMsQ0FBQztZQUNsQixLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVztnQkFDN0IsT0FBTyxNQUFNLENBQUM7WUFDZixLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsZ0JBQWdCO2dCQUNsQyxPQUFPLFdBQVcsQ0FBQztZQUNwQixLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsc0JBQXNCO2dCQUN4QyxPQUFPLGdCQUFnQixDQUFDO1lBQ3pCLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyx1QkFBdUI7Z0JBQ3pDLE9BQU8sUUFBUSxDQUFDO1lBQ2pCLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxhQUFhLENBQUMsQ0FBQyxDQUFDO2dCQUNsQyxxQ0FBcUM7Z0JBQ3JDLE1BQU0sT0FBTyxHQUFHLFdBQStCLENBQUM7Z0JBQ2hELElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztvQkFDekMsT0FBTyxPQUFPLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQztnQkFDaEMsQ0FBQztnQkFDRCxPQUFPLFFBQVEsQ0FBQztZQUNqQixDQUFDO1lBQ0QsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGdCQUFnQixDQUFDLENBQUMsQ0FBQztnQkFDckMsMkRBQTJEO2dCQUMzRCxNQUFNLFVBQVUsR0FBRyxXQUFrQyxDQUFDO2dCQUN0RCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsd0JBQXdCLENBQUMsVUFBVSxDQUFDLElBQUksRUFBRSxXQUFXLEVBQUUsa0JBQWtCLENBQUMsQ0FBQztnQkFDakcsTUFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLHdCQUF3QixDQUFDLFVBQVUsQ0FBQyxLQUFLLEVBQUUsV0FBVyxFQUFFLGtCQUFrQixDQUFDLENBQUM7Z0JBRW5HLHVDQUF1QztnQkFDdkMsTUFBTSxRQUFRLEdBQUcsVUFBVSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUM7Z0JBQy9DLElBQUksUUFBUSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsYUFBYTtvQkFDdkMsUUFBUSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsVUFBVTtvQkFDckMsUUFBUSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsVUFBVTtvQkFDckMsUUFBUSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsWUFBWSxFQUFFLENBQUM7b0JBQzlDLG1EQUFtRDtvQkFDbkQsSUFBSSxDQUFDLFFBQVEsS0FBSyxRQUFRLElBQUksUUFBUSxLQUFLLFNBQVMsQ0FBQzt3QkFDaEQsQ0FBQyxTQUFTLEtBQUssUUFBUSxJQUFJLFNBQVMsS0FBSyxTQUFTLENBQUMsRUFBRSxDQUFDO3dCQUMxRCxPQUFPLFFBQVEsQ0FBQztvQkFDakIsQ0FBQztnQkFDRixDQUFDO2dCQUNELElBQUksUUFBUSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsU0FBUyxFQUFFLENBQUM7b0JBQzFDLCtDQUErQztvQkFDL0MsSUFBSSxRQUFRLEtBQUssUUFBUSxJQUFJLFNBQVMsS0FBSyxRQUFRLEVBQUUsQ0FBQzt3QkFDckQsT0FBTyxRQUFRLENBQUM7b0JBQ2pCLENBQUM7b0JBQ0QsSUFBSSxRQUFRLEtBQUssUUFBUSxJQUFJLFNBQVMsS0FBSyxRQUFRLEVBQUUsQ0FBQzt3QkFDckQsT0FBTyxRQUFRLENBQUM7b0JBQ2pCLENBQUM7Z0JBQ0YsQ0FBQztnQkFDRCxPQUFPLFNBQVMsQ0FBQztZQUNsQixDQUFDO1lBQ0QsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLHdCQUF3QixDQUFDLENBQUMsQ0FBQztnQkFDN0Msa0RBQWtEO2dCQUNsRCxJQUFJLFdBQVcsRUFBRSxDQUFDO29CQUNqQixNQUFNLFdBQVcsR0FBRyxJQUFJLENBQUMsc0JBQXNCLENBQUMsV0FBVyxDQUFDLENBQUM7b0JBQzdELElBQUksV0FBVyxFQUFFLENBQUM7d0JBQ2pCLE1BQU0sSUFBSSxHQUFHLFdBQVcsQ0FBQyxHQUFHLENBQUMsV0FBVyxDQUFDLENBQUM7d0JBQzFDLElBQUksSUFBSSxFQUFFLENBQUM7NEJBQ1YsT0FBTyxJQUFJLENBQUM7d0JBQ2IsQ0FBQztvQkFDRixDQUFDO2dCQUNGLENBQUM7Z0JBQ0QseURBQXlEO2dCQUN6RCxNQUFNLFVBQVUsR0FBRyxXQUEwQyxDQUFDO2dCQUM5RCxJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxVQUFVLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztvQkFDMUQsTUFBTSxTQUFTLEdBQUcsVUFBVSxDQUFDLFVBQVUsQ0FBQztvQkFDeEMsNkJBQTZCO29CQUM3QixJQUFJLFNBQVMsR0FBRyxFQUFFLENBQUM7b0JBQ25CLElBQUksU0FBUyxDQUFDLFVBQVUsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxXQUFXLEVBQUUsQ0FBQzt3QkFDN0QsU0FBUyxHQUFHLE1BQU0sQ0FBQztvQkFDcEIsQ0FBQzt5QkFBTSxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsU0FBUyxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7d0JBQ2xELFNBQVMsR0FBRyxTQUFTLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQztvQkFDdkMsQ0FBQztvQkFDRCxNQUFNLE9BQU8sR0FBRyxTQUFTLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztvQkFDcEMsTUFBTSxTQUFTLEdBQUcsVUFBVSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7b0JBQ3ZDLDBCQUEwQjtvQkFDMUIsSUFBSSxTQUFTLEtBQUssTUFBTSxJQUFJLE9BQU8sS0FBSyxLQUFLLElBQUksU0FBUyxLQUFLLE1BQU0sRUFBRSxDQUFDO3dCQUN2RSxPQUFPLFFBQVEsQ0FBQztvQkFDakIsQ0FBQztnQkFDRixDQUFDO2dCQUNELE9BQU8sU0FBUyxDQUFDO1lBQ2xCLENBQUM7WUFDRCxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsVUFBVSxDQUFDLENBQUMsQ0FBQztnQkFDL0IsaURBQWlEO2dCQUNqRCxJQUFJLFdBQVcsRUFBRSxDQUFDO29CQUNqQixNQUFNLElBQUksR0FBSSxXQUE2QixDQUFDLElBQUksQ0FBQztvQkFDakQsTUFBTSxJQUFJLEdBQUcsV0FBVyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztvQkFDbkMsSUFBSSxJQUFJLEVBQUUsQ0FBQzt3QkFDVixPQUFPLElBQUksQ0FBQztvQkFDYixDQUFDO2dCQUNGLENBQUM7Z0JBQ0QsT0FBTyxTQUFTLENBQUM7WUFDbEIsQ0FBQztZQUNELEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyx1QkFBdUIsQ0FBQyxDQUFDLENBQUM7Z0JBQzVDLHdEQUF3RDtnQkFDeEQsNkRBQTZEO2dCQUM3RCw0REFBNEQ7Z0JBQzVELDZEQUE2RDtnQkFDN0QsMERBQTBEO2dCQUMxRCxtREFBbUQ7Z0JBQ25ELE1BQU0sYUFBYSxHQUFHLFdBQXlDLENBQUM7Z0JBQ2hFLE1BQU0sUUFBUSxHQUFHLGFBQWEsQ0FBQyxrQkFBa0IsQ0FBQztnQkFDbEQsSUFBSSxDQUFDLFFBQVEsSUFBSSxDQUFDLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO29CQUNqRCxPQUFPLFNBQVMsQ0FBQztnQkFDbEIsQ0FBQztnQkFDRCxNQUFNLFlBQVksR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsYUFBYSxDQUFDLFVBQVUsQ0FBQyxDQUFDO2dCQUN4RSxJQUFJLENBQUMsWUFBWSxFQUFFLENBQUM7b0JBQ25CLE9BQU8sU0FBUyxDQUFDO2dCQUNsQixDQUFDO2dCQUNELE1BQU0sT0FBTyxHQUFHLFlBQVksQ0FBQyxRQUFRLENBQUUsUUFBUSxDQUFDLFFBQVEsQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUUsQ0FBQztnQkFDckUsSUFBSSxDQUFDLE9BQU8sSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7b0JBQzdDLE9BQU8sU0FBUyxDQUFDO2dCQUNsQixDQUFDO2dCQUNELE1BQU0sT0FBTyxHQUFHLElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxPQUFPLENBQUMsQ0FBQztnQkFDdEQsTUFBTSxhQUFhLEdBQUcsT0FBTyxJQUFJLFNBQVMsQ0FBQztnQkFDM0MsT0FBTyxhQUFhLENBQUM7WUFDdEIsQ0FBQztZQUNELEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxjQUFjLENBQUMsQ0FBQyxDQUFDO2dCQUNuQywwREFBMEQ7Z0JBQzFELE1BQU0sUUFBUSxHQUFHLFdBQWdDLENBQUM7Z0JBQ2xELElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO29CQUN4RCxNQUFNLFVBQVUsR0FBRyxRQUFRLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7b0JBQ2pELE1BQU0sT0FBTyxHQUFHLEVBQUUsQ0FBQyxZQUFZLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxVQUFVLENBQUM7d0JBQzlELENBQUMsQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLFVBQVUsQ0FBQyxJQUFJO3dCQUNyQyxDQUFDLENBQUMsRUFBRSxDQUFDO29CQUVOLHVCQUF1QjtvQkFDdkIsSUFBSSxPQUFPLEtBQUssTUFBTSxJQUFJLFVBQVUsS0FBSyxLQUFLLEVBQUUsQ0FBQzt3QkFDaEQsT0FBTyxRQUFRLENBQUM7b0JBQ2pCLENBQUM7b0JBQ0Qsb0NBQW9DO29CQUNwQyxJQUFJLFVBQVUsS0FBSyxVQUFVLElBQUksVUFBVSxLQUFLLFNBQVMsRUFBRSxDQUFDO3dCQUMzRCxPQUFPLFFBQVEsQ0FBQztvQkFDakIsQ0FBQztvQkFDRCw2REFBNkQ7b0JBQzdELElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQzt3QkFDbkUsTUFBTSxTQUFTLEdBQUcsUUFBUSxDQUFDLFVBQVUsQ0FBQyxVQUFVLENBQUM7d0JBQ2pELHFEQUFxRDt3QkFDckQsSUFBSSxTQUFTLEdBQUcsRUFBRSxDQUFDO3dCQUNuQixJQUFJLFNBQVMsQ0FBQyxVQUFVLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsV0FBVyxFQUFFLENBQUM7NEJBQzdELFNBQVMsR0FBRyxNQUFNLENBQUM7d0JBQ3BCLENBQUM7NkJBQU0sSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFNBQVMsQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDOzRCQUNsRCxTQUFTLEdBQUcsU0FBUyxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUM7d0JBQ3ZDLENBQUM7d0JBQ0QsTUFBTSxPQUFPLEdBQUcsU0FBUyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7d0JBQ3BDLHdCQUF3Qjt3QkFDeEIsSUFBSSxTQUFTLEtBQUssTUFBTSxJQUFJLE9BQU8sS0FBSyxLQUFLLEVBQUUsQ0FBQzs0QkFDL0Msd0RBQXdEOzRCQUN4RCxJQUFJLFlBQVksR0FBRyxTQUFTLENBQUM7NEJBQzdCLElBQUksa0JBQWtCLEVBQUUsQ0FBQztnQ0FDeEIsTUFBTSxPQUFPLEdBQUcsa0JBQWtCLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxDQUFDO2dDQUM5QyxJQUFJLE9BQU8sSUFBSSxPQUFPLENBQUMsVUFBVSxDQUFDLE1BQU0sQ0FBQyxFQUFFLENBQUM7b0NBQzNDLDJCQUEyQjtvQ0FDM0IsTUFBTSxLQUFLLEdBQUcsT0FBTyxDQUFDLEtBQUssQ0FBQyxxQkFBcUIsQ0FBQyxDQUFDO29DQUNuRCxJQUFJLEtBQUssRUFBRSxDQUFDO3dDQUNYLENBQUUsQUFBRCxFQUFHLFlBQVksQ0FBRSxHQUFHLEtBQUssQ0FBQztvQ0FDNUIsQ0FBQztnQ0FDRixDQUFDOzRCQUNGLENBQUM7NEJBQ0QsSUFBSSxVQUFVLEtBQUssS0FBSztnQ0FBRSxPQUFPLFNBQVMsQ0FBQzs0QkFDM0MsSUFBSSxVQUFVLEtBQUssS0FBSztnQ0FBRSxPQUFPLE1BQU0sQ0FBQzs0QkFDeEMsSUFBSSxVQUFVLEtBQUssS0FBSztnQ0FBRSxPQUFPLFlBQVksQ0FBQzs0QkFDOUMsSUFBSSxVQUFVLEtBQUssUUFBUTtnQ0FBRSxPQUFPLFNBQVMsQ0FBQzs0QkFDOUMsSUFBSSxVQUFVLEtBQUssT0FBTztnQ0FBRSxPQUFPLE1BQU0sQ0FBQzs0QkFDMUMsSUFBSSxVQUFVLEtBQUssUUFBUTtnQ0FBRSxPQUFPLG9CQUFvQixZQUFZLEdBQUcsQ0FBQzs0QkFDeEUsSUFBSSxVQUFVLEtBQUssTUFBTTtnQ0FBRSxPQUFPLDBCQUEwQixDQUFDOzRCQUM3RCxJQUFJLFVBQVUsS0FBSyxTQUFTO2dDQUFFLE9BQU8sNkJBQTZCLFlBQVksSUFBSSxDQUFDO3dCQUNwRixDQUFDO29CQUNGLENBQUM7b0JBQ0QsdUJBQXVCO29CQUN2QixJQUFJLE9BQU8sS0FBSyxLQUFLLElBQUksT0FBTyxLQUFLLEtBQUssRUFBRSxDQUFDO3dCQUM1QyxJQUFJLFVBQVUsS0FBSyxLQUFLOzRCQUFFLE9BQU8sU0FBUyxDQUFDO3dCQUMzQyxJQUFJLFVBQVUsS0FBSyxLQUFLOzRCQUFFLE9BQU8sTUFBTSxDQUFDO3dCQUN4QyxJQUFJLFVBQVUsS0FBSyxLQUFLOzRCQUFFLE9BQU8sU0FBUyxDQUFDO3dCQUMzQyxJQUFJLFVBQVUsS0FBSyxRQUFROzRCQUFFLE9BQU8sU0FBUyxDQUFDO3dCQUM5QyxJQUFJLFVBQVUsS0FBSyxPQUFPOzRCQUFFLE9BQU8sTUFBTSxDQUFDO3dCQUMxQyxJQUFJLFVBQVUsS0FBSyxRQUFROzRCQUFFLE9BQU8sMkJBQTJCLENBQUM7d0JBQ2hFLElBQUksVUFBVSxLQUFLLE1BQU07NEJBQUUsT0FBTywwQkFBMEIsQ0FBQzt3QkFDN0QsSUFBSSxVQUFVLEtBQUssU0FBUzs0QkFBRSxPQUFPLHFDQUFxQyxDQUFDO29CQUM1RSxDQUFDO2dCQUNGLENBQUM7Z0JBQ0QsaUNBQWlDO2dCQUNqQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7b0JBQzFDLE1BQU0sTUFBTSxHQUFHLFFBQVEsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDO29CQUN4QyxJQUFJLE1BQU0sS0FBSyxVQUFVLElBQUksTUFBTSxLQUFLLFlBQVksRUFBRSxDQUFDO3dCQUN0RCxPQUFPLFFBQVEsQ0FBQztvQkFDakIsQ0FBQztvQkFDRCxJQUFJLE1BQU0sS0FBSyxRQUFRLEVBQUUsQ0FBQzt3QkFDekIsT0FBTyxRQUFRLENBQUM7b0JBQ2pCLENBQUM7b0JBQ0QsSUFBSSxNQUFNLEtBQUssUUFBUSxFQUFFLENBQUM7d0JBQ3pCLE9BQU8sUUFBUSxDQUFDO29CQUNqQixDQUFDO29CQUNELElBQUksTUFBTSxLQUFLLFNBQVMsRUFBRSxDQUFDO3dCQUMxQixPQUFPLFNBQVMsQ0FBQztvQkFDbEIsQ0FBQztnQkFDRixDQUFDO2dCQUNELE9BQU8sU0FBUyxDQUFDO1lBQ2xCLENBQUM7WUFDRCxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsa0JBQWtCLENBQUM7WUFDdEMsS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLDZCQUE2QixDQUFDLENBQUMsQ0FBQztnQkFDbEQsd0VBQXdFO2dCQUN4RSxPQUFPLFFBQVEsQ0FBQztZQUNqQixDQUFDO1lBQ0Q7Z0JBQ0MsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztJQUNGLENBQUM7SUFFRDs7Y0FFSTtJQUNJLFlBQVksQ0FBRSxJQUFhLEVBQUUsVUFBeUI7UUFDN0QscUNBQXFDO1FBQ3JDLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7WUFDakQsSUFBSSxRQUE0QixDQUFDO1lBQ2pDLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO2dCQUNwRCxRQUFRLEdBQUcsSUFBSSxDQUFDLGVBQWUsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLENBQUM7WUFDbEQsQ0FBQztpQkFBTSxDQUFDO2dCQUNQLFFBQVEsR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDO1lBQzVELENBQUM7WUFDRCxJQUFJLFFBQVEsRUFBRSxDQUFDO2dCQUNkLE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztnQkFDRixJQUFJLENBQUMsUUFBUSxDQUFDLFFBQVEsRUFBRTtvQkFDdkIsUUFBUSxFQUFVLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUU7b0JBQ3ZFLElBQUksRUFBYyxlQUFlO29CQUNqQyxJQUFJLEVBQWMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQztvQkFDeEQsNERBQTREO29CQUM1RCw2REFBNkQ7b0JBQzdELGVBQWUsRUFBRyxJQUFJLENBQUMsVUFBVSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQztpQkFDbkUsQ0FBQyxDQUFDO2dCQUNILDhEQUE4RDtnQkFDOUQsSUFBSSxDQUFDLGtCQUFrQixDQUFDLElBQUksRUFBRSxRQUFRLENBQUMsQ0FBQztnQkFDeEMsNEJBQTRCO2dCQUM1QixJQUFJLENBQUMsT0FBTyxDQUFDLFFBQVEsRUFBRTtvQkFDdEIsUUFBUSxFQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUU7b0JBQ2hFLElBQUksRUFBTyxlQUFlO29CQUMxQixJQUFJLEVBQU8sSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQztvQkFDakQsT0FBTyxFQUFJLGdCQUFnQjtpQkFDM0IsQ0FBQyxDQUFDO1lBQ0osQ0FBQztRQUNGLENBQUM7UUFFRCwwREFBMEQ7UUFDMUQsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUN6QyxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztZQUNoQyxvREFBb0Q7WUFDcEQsNERBQTREO1lBQzVELDBEQUEwRDtZQUMxRCwrREFBK0Q7WUFDL0QsNkRBQTZEO1lBQzdELDhDQUE4QztZQUM5QyxJQUFJLFFBQVEsS0FBSyxPQUFPLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztnQkFDOUQsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxDQUFDO2dCQUNwRSxNQUFNLFVBQVUsR0FBRyxFQUFFLENBQUMsZ0JBQWdCLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLElBQUksQ0FBQyxNQUFNLENBQUMsVUFBVSxLQUFLLElBQUksQ0FBQztnQkFDdkYsSUFBSSxVQUFVLEVBQUUsQ0FBQztvQkFDaEIsSUFBSSxDQUFDLFVBQVUsRUFBRSxDQUFDO3dCQUNqQixNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7d0JBQ0YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLEVBQUU7NEJBQ3pCLFFBQVEsRUFBVSxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFOzRCQUN2RSxJQUFJLEVBQWMsZUFBZTs0QkFDakMsSUFBSSxFQUFjLElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsRUFBRSxHQUFHLENBQUM7NEJBQ3hELGVBQWUsRUFBRyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDO3lCQUN4RCxDQUFDLENBQUM7b0JBQ0osQ0FBQztvQkFDRCxJQUFJLENBQUMsa0JBQWtCLENBQUMsSUFBSSxFQUFFLFVBQVUsQ0FBQyxDQUFDO2dCQUMzQyxDQUFDO1lBQ0YsQ0FBQztZQUNELGlEQUFpRDtZQUNqRCxJQUFJLFFBQVEsSUFBSSxJQUFJLENBQUMsZ0JBQWdCLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztnQkFDakQsTUFBTSxFQUFFLElBQUksRUFBRSxTQUFTLEVBQUUsR0FBRyxFQUFFLENBQUMsNkJBQTZCLENBQzNELFVBQVUsRUFDVixJQUFJLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxDQUN6QixDQUFDO2dCQUNELDJCQUEyQjtnQkFDNUIsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLGVBQWUsQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDNUMsSUFBSSxRQUFRLEVBQUUsQ0FBQztvQkFDZCxJQUFJLENBQUMsUUFBUSxDQUFDLFFBQVEsRUFBRTt3QkFDdkIsUUFBUSxFQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUU7d0JBQ2hFLElBQUksRUFBTyxnQkFBZ0I7d0JBQzNCLElBQUksRUFBTyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDO3FCQUNqRCxDQUFDLENBQUM7Z0JBQ0osQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBRUQsbUVBQW1FO1FBQ25FLElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUNsRCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsQ0FBQztZQUN2RCxJQUFJLFFBQVEsS0FBSyxRQUFRLElBQUksSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQ3hELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDOUMsSUFBSSxRQUFRLEVBQUUsQ0FBQztvQkFDZCxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7b0JBQ0YsTUFBTSxRQUFRLEdBQUcsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsRUFBRSxDQUFDO29CQUN2RSxJQUFJLENBQUMsUUFBUSxDQUFDLFFBQVEsRUFBRTt3QkFDdkIsUUFBUTt3QkFDUixJQUFJLEVBQUcsUUFBUTt3QkFDZixJQUFJLEVBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQztxQkFDN0MsQ0FBQyxDQUFDO29CQUNILG1FQUFtRTtvQkFDbkUsSUFBSSxDQUFDLHFCQUFxQixDQUFDLElBQUksRUFBRSxRQUFRLENBQUMsQ0FBQztvQkFDM0MsMERBQTBEO29CQUMxRCx5REFBeUQ7b0JBQ3pELElBQUksQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLENBQUMsRUFBRSxJQUFJLEVBQUcsUUFBUSxFQUFFLFFBQVEsRUFBRSxDQUFDLENBQUM7Z0JBQzNELENBQUM7WUFDRixDQUFDO1lBRUQsNkRBQTZEO1lBQzdELDhEQUE4RDtZQUM5RCx3REFBd0Q7WUFDeEQsNkRBQTZEO1lBQzdELDZEQUE2RDtZQUM3RCxrREFBa0Q7WUFDbEQsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ3BELElBQUksUUFBUSxFQUFFLENBQUM7Z0JBQ2QsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksRUFBRSxRQUFRLEVBQUUsVUFBVSxDQUFDLENBQUM7Z0JBQ3pELE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztnQkFDRixJQUFJLENBQUMsT0FBTyxDQUFDLFFBQVEsRUFBRTtvQkFDdEIsUUFBUSxFQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUU7b0JBQ2hFLElBQUksRUFBTyxlQUFlO29CQUMxQixJQUFJLEVBQU8sSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQztvQkFDakQsT0FBTyxFQUFJLHNCQUFzQjtpQkFDakMsQ0FBQyxDQUFDO1lBQ0osQ0FBQztZQUVELGlFQUFpRTtZQUNqRSxpRUFBaUU7WUFDakUsZ0VBQWdFO1lBQ2hFLHFEQUFxRDtZQUNyRCw4REFBOEQ7WUFDOUQsNERBQTREO1lBQzVELDREQUE0RDtZQUM1RCw2REFBNkQ7WUFDN0QsOEJBQThCO1lBQzlCLE1BQU0sZ0JBQWdCLEdBQUcsSUFBSSxDQUFDLDZCQUE2QixDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ2xFLElBQUksZ0JBQWdCLEVBQUUsQ0FBQztnQkFDdEIsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLElBQUksQ0FBQyxVQUFVLEVBQUUsTUFBTSxDQUFDLENBQUM7Z0JBQzNFLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztvQkFDakIsTUFBTSxXQUFXLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBRSxDQUFDLENBQUUsRUFBRSxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUM7b0JBQzdELElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxJQUFJLEVBQUUsZ0JBQWdCLEVBQUUsVUFBVSxFQUFFLFdBQVcsQ0FBQyxDQUFDO29CQUM5RSxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7b0JBQ0YsSUFBSSxDQUFDLE9BQU8sQ0FBQyxnQkFBZ0IsRUFBRTt3QkFDOUIsUUFBUSxFQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUU7d0JBQ2hFLElBQUksRUFBTyxlQUFlO3dCQUMxQixJQUFJLEVBQU8sSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQzt3QkFDakQsT0FBTyxFQUFJLHlCQUF5QjtxQkFDcEMsQ0FBQyxDQUFDO2dCQUNKLENBQUM7Z0JBQ0QsSUFBSSxDQUFDLGtCQUFrQixDQUFDLElBQUksRUFBRSxnQkFBZ0IsQ0FBQyxDQUFDO1lBQ2pELENBQUM7WUFFRCxnRUFBZ0U7WUFDaEUsdURBQXVEO1lBQ3ZELDREQUE0RDtZQUM1RCxnRUFBZ0U7WUFDaEUsMERBQTBEO1lBQzFELDZEQUE2RDtZQUM3RCx5REFBeUQ7WUFDekQseURBQXlEO1lBQ3pELDBEQUEwRDtZQUMxRCxnQkFBZ0I7WUFDaEIsTUFBTSxZQUFZLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ3hELElBQUksWUFBWSxFQUFFLENBQUM7Z0JBQ2xCLElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxJQUFJLEVBQUUsWUFBWSxFQUFFLFVBQVUsQ0FBQyxDQUFDO2dCQUM3RCxJQUFJLENBQUMsa0JBQWtCLENBQUMsSUFBSSxFQUFFLFlBQVksQ0FBQyxDQUFDO1lBQzdDLENBQUM7WUFDRCxNQUFNLFNBQVMsR0FBRyxJQUFJLENBQUMsc0JBQXNCLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDcEQsSUFBSSxTQUFTLEVBQUUsQ0FBQztnQkFDZixJQUFJLENBQUMsdUJBQXVCLENBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxVQUFVLENBQUMsQ0FBQztnQkFDMUQsSUFBSSxDQUFDLGtCQUFrQixDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsQ0FBQztZQUMxQyxDQUFDO1FBQ0YsQ0FBQztJQUNGLENBQUM7SUFFRDs7Y0FFSTtJQUNJLGVBQWUsQ0FBRSxJQUFtQjtRQUMzQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUMzQixPQUFPLElBQUksQ0FBQyxJQUFJLENBQUM7UUFDbEIsQ0FBQztRQUNELElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDekMsT0FBTyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztRQUN2QixDQUFDO1FBQ0QsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOztjQUVJO0lBQ0ksUUFBUSxDQUFFLFFBQWdCLEVBQUUsS0FBZ0I7UUFDbkQsK0NBQStDO1FBQy9DLElBQUksQ0FBQyxJQUFJLENBQUMsV0FBVyxDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO1lBQ3JDLE9BQU87UUFDUixDQUFDO1FBQ0QsSUFBSSxDQUFDLElBQUksQ0FBQyxNQUFNLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7WUFDaEMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxHQUFHLENBQUMsUUFBUSxFQUFFLEVBQUUsQ0FBQyxDQUFDO1FBQy9CLENBQUM7UUFFRCx5REFBeUQ7UUFDekQsTUFBTSxjQUFjLEdBQUcsSUFBSSxDQUFDLE1BQU0sQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFFLENBQUM7UUFDbEQsTUFBTSxXQUFXLEdBQUcsY0FBYyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUNsRCxRQUFRLENBQUMsUUFBUSxLQUFLLEtBQUssQ0FBQyxRQUFRO1lBQ25DLFFBQVEsQ0FBQyxJQUFJLEtBQUssS0FBSyxDQUFDLElBQUk7WUFDNUIsUUFBUSxDQUFDLElBQUksS0FBSyxLQUFLLENBQUMsSUFBSSxDQUFDLENBQUM7UUFFaEMsSUFBSSxDQUFDLFdBQVcsRUFBRSxDQUFDO1lBQ2xCLGNBQWMsQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7UUFDNUIsQ0FBQztJQUNGLENBQUM7SUFFRDs7T0FFRztJQUNLLFVBQVUsQ0FBRSxJQUFhLEVBQUUsVUFBeUI7UUFDM0QsSUFBSSxDQUFDLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUNwRCxPQUFPO1FBQ1IsQ0FBQztRQUVELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxlQUFlLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQ3ZELElBQUksQ0FBQyxRQUFRLEVBQUUsQ0FBQztZQUNmLE9BQU87UUFDUixDQUFDO1FBRUQsTUFBTSxFQUFFLElBQUksRUFBRSxTQUFTLEVBQUUsR0FBRyxFQUFFLENBQUMsNkJBQTZCLENBQzNELFVBQVUsRUFDVixJQUFJLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxDQUN6QixDQUFDO1FBQ0YsTUFBTSxRQUFRLEdBQUcsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsRUFBRSxDQUFDO1FBQ3ZFLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsRUFBRSxHQUFHLENBQUMsQ0FBQztRQUNwRCw4REFBOEQ7UUFDOUQsZ0VBQWdFO1FBQ2hFLCtEQUErRDtRQUMvRCxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxDQUFDO1FBRXpDLHVHQUF1RztRQUN2RyxJQUNDLFFBQVEsS0FBSyxNQUFNO1lBQ25CLFFBQVEsS0FBSyxvQkFBb0I7WUFDakMsUUFBUSxLQUFLLHVCQUF1QjtZQUNwQyxRQUFRLEtBQUsscUJBQXFCLEVBQ2pDLENBQUM7WUFDRixNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsc0JBQXNCLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBRSxDQUFDLENBQUUsQ0FBQyxDQUFDO1lBQ3BFLHFEQUFxRDtZQUNyRCxrREFBa0Q7WUFDbEQsb0NBQW9DO1lBQ3BDLHlDQUF5QztZQUN6QyxrQ0FBa0M7WUFDbEMsNERBQTREO1lBQzVELHVFQUF1RTtZQUN2RSxNQUFNLGVBQWUsR0FBRyxRQUFRLEtBQUsscUJBQXFCO2dCQUN6RCxDQUFDLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBRSxDQUFDLENBQUU7Z0JBQ3JCLENBQUMsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFFLENBQUMsQ0FBRSxDQUFDO1lBQ3ZCLDBEQUEwRDtZQUMxRCw2REFBNkQ7WUFDN0QsbUVBQW1FO1lBQ25FLDZEQUE2RDtZQUM3RCxpRUFBaUU7WUFDakUsTUFBTSxnQkFBZ0IsR0FBRyxlQUFlO2dCQUN2QyxDQUFDLENBQUMsSUFBSSxDQUFDLDJCQUEyQixDQUFDLGVBQWUsQ0FBQztnQkFDbkQsQ0FBQyxDQUFDLFNBQVMsQ0FBQztZQUNiLE1BQU0sY0FBYyxHQUFHLEtBQUssSUFBSSxnQkFBZ0IsQ0FBQztZQUNqRCxNQUFNLElBQUksR0FBWTtnQkFDckIsUUFBUTtnQkFDUixJQUFJLEVBQVMsTUFBTTtnQkFDbkIsSUFBSTtnQkFDSixVQUFVLEVBQUcsVUFBVSxJQUFJLFNBQVM7Z0JBQ3BDLEtBQUssRUFBUSxjQUFjO2dCQUMzQixFQUFFLEVBQVcsUUFBUTthQUNyQixDQUFDO1lBQ0YsSUFBSSxlQUFlLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxlQUFlLENBQUMsRUFBRSxDQUFDO2dCQUN6RCxJQUFJLENBQUMsV0FBVyxHQUFHLGVBQWUsQ0FBQyxJQUFJLENBQUM7WUFDekMsQ0FBQztZQUNELEtBQUssTUFBTSxRQUFRLElBQUksQ0FBRSxJQUFJLENBQUMsU0FBUyxDQUFFLENBQUMsQ0FBRSxFQUFFLElBQUksQ0FBQyxTQUFTLENBQUUsQ0FBQyxDQUFFLENBQUUsRUFBRSxDQUFDO2dCQUNyRSxJQUFJLFFBQVEsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLFFBQVEsQ0FBQyxFQUFFLENBQUM7b0JBQzlDLElBQUksQ0FBQyxLQUFLLEdBQUcsUUFBUSxDQUFDLElBQUksQ0FBQztvQkFDM0IsTUFBTTtnQkFDUCxDQUFDO1lBQ0YsQ0FBQztZQUNELCtEQUErRDtZQUMvRCxnRUFBZ0U7WUFDaEUsOERBQThEO1lBQzlELDBDQUEwQztZQUMxQyxNQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMsYUFBYSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUM3QyxJQUFJLE9BQU8sRUFBRSxDQUFDO2dCQUNiLElBQUksQ0FBQyxHQUFHLEdBQUcsT0FBTyxDQUFDLEdBQUcsQ0FBQztnQkFDdkIsSUFBSSxJQUFJLENBQUMsS0FBSyxLQUFLLFNBQVMsRUFBRSxDQUFDO29CQUM5QixJQUFJLENBQUMsS0FBSyxHQUFHLE9BQU8sQ0FBQyxLQUFLLENBQUM7Z0JBQzVCLENBQUM7WUFDRixDQUFDO1lBQ0QsZ0VBQWdFO1lBQ2hFLDZEQUE2RDtZQUM3RCwwQ0FBMEM7WUFDMUMsTUFBTSxPQUFPLEdBQUcsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksQ0FBQyxTQUFTLENBQUUsQ0FBQyxDQUFFLEVBQUUsVUFBVSxDQUFDLENBQUM7WUFDOUUsSUFBSSxPQUFPLEVBQUUsQ0FBQztnQkFDYixrRUFBa0U7Z0JBQ2xFLGtFQUFrRTtnQkFDbEUsb0RBQW9EO2dCQUNwRCxNQUFNLFdBQVcsR0FBRyxFQUFFLENBQUMsNkJBQTZCLENBQ25ELFVBQVUsRUFDVixPQUFPLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxDQUM1QixDQUFDO2dCQUNGLE1BQU0sWUFBWSxHQUFHLFFBQVEsQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLFFBQVEsQ0FBQyxDQUFDO2dCQUMzRCxJQUFJLENBQUMsZUFBZSxHQUFHLEdBQUcsWUFBWSxJQUFJLFdBQVcsQ0FBQyxJQUFJLEdBQUcsQ0FBQyxJQUFJLFdBQVcsQ0FBQyxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQzlGLE1BQU0sWUFBWSxHQUFHLElBQUksR0FBRyxFQUFVLENBQUM7Z0JBQ3ZDLElBQUksQ0FBQyxrQkFBa0IsQ0FBQyxPQUFPLEVBQUUsUUFBUSxFQUFFLFVBQVUsRUFBRSxDQUFDLEVBQUUsSUFBSSxHQUFHLEVBQUUsRUFBRSxZQUFZLEVBQUUsY0FBYyxDQUFDLENBQUM7Z0JBQ25HLElBQUksWUFBWSxDQUFDLElBQUksR0FBRyxDQUFDLEVBQUUsQ0FBQztvQkFDM0IsSUFBSSxDQUFDLFlBQVksR0FBRyxLQUFLLENBQUMsSUFBSSxDQUFDLFlBQVksQ0FBQyxDQUFDO2dCQUM5QyxDQUFDO1lBQ0YsQ0FBQztZQUNELE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxNQUFNLENBQUMsVUFBVSxJQUFJLGNBQWMsSUFBSSxTQUFTLEVBQUUsSUFBSSxDQUFDLENBQUM7WUFDNUUsSUFBSSxDQUFDLGVBQWUsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLE1BQU0sQ0FBQyxDQUFDO1lBQ3ZDLE9BQU87UUFDUixDQUFDO1FBRUQscURBQXFEO1FBQ3JELElBQUksUUFBUSxLQUFLLFNBQVMsSUFBSSxRQUFRLEtBQUssa0JBQWtCLElBQUksUUFBUSxLQUFLLFNBQVMsRUFBRSxDQUFDO1lBQ3pGLElBQUksQ0FBQyxNQUFNLENBQUMsS0FBSyxJQUFJLFNBQVMsRUFBRTtnQkFDL0IsUUFBUTtnQkFDUixJQUFJLEVBQUcsZ0JBQWdCO2dCQUN2QixJQUFJO2dCQUNKLEtBQUs7YUFDTCxDQUFDLENBQUM7WUFDSCxPQUFPO1FBQ1IsQ0FBQztRQUVELDBEQUEwRDtRQUMxRCw4Q0FBOEM7UUFDOUMsSUFBSSxRQUFRLEtBQUssYUFBYSxJQUFJLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxHQUFHLENBQUMsRUFBRSxDQUFDO1lBQzdELE1BQU0sQ0FBRSxHQUFHLENBQUUsR0FBRyxJQUFJLENBQUMsU0FBUyxDQUFDO1lBQy9CLElBQUksRUFBRSxDQUFDLHdCQUF3QixDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQ3RDLEtBQUssTUFBTSxPQUFPLElBQUksR0FBRyxDQUFDLFFBQVEsRUFBRSxDQUFDO29CQUNwQyxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMsc0JBQXNCLENBQUMsT0FBTyxDQUFDLENBQUM7b0JBQ3hELElBQUksQ0FBQyxNQUFNLENBQUMsVUFBVSxJQUFJLEtBQUssSUFBSSxTQUFTLEVBQUU7d0JBQzdDLFFBQVE7d0JBQ1IsSUFBSSxFQUFTLFlBQVk7d0JBQ3pCLElBQUk7d0JBQ0osVUFBVSxFQUFHLFVBQVUsSUFBSSxTQUFTO3dCQUNwQyxLQUFLO3FCQUNMLENBQUMsQ0FBQztnQkFDSixDQUFDO1lBQ0YsQ0FBQztpQkFBTSxDQUFDO2dCQUNQLE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQyxzQkFBc0IsQ0FBQyxHQUFHLENBQUMsQ0FBQztnQkFDcEQsSUFBSSxDQUFDLE1BQU0sQ0FBQyxVQUFVLElBQUksS0FBSyxJQUFJLFNBQVMsRUFBRTtvQkFDN0MsUUFBUTtvQkFDUixJQUFJLEVBQVMsWUFBWTtvQkFDekIsSUFBSTtvQkFDSixVQUFVLEVBQUcsVUFBVSxJQUFJLFNBQVM7b0JBQ3BDLEtBQUs7aUJBQ0wsQ0FBQyxDQUFDO1lBQ0osQ0FBQztZQUNELE9BQU87UUFDUixDQUFDO0lBQ0YsQ0FBQztJQUVEOztPQUVHO0lBQ0ssc0JBQXNCLENBQUUsR0FBOEI7UUFDN0QsSUFBSSxDQUFDLEdBQUcsRUFBRSxDQUFDO1lBQ1YsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELDRCQUE0QjtRQUM1QixJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztZQUMxQixNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUNwRCxJQUFJLE1BQU0sRUFBRSxDQUFDO2dCQUNaLE9BQU8sTUFBTSxDQUFDO1lBQ2YsQ0FBQztZQUNELGtDQUFrQztZQUNsQyxJQUFJLElBQUksQ0FBQyxXQUFXLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUNwQyxPQUFPLEdBQUcsQ0FBQyxJQUFJLENBQUM7WUFDakIsQ0FBQztZQUNELDJEQUEyRDtZQUMzRCx3REFBd0Q7WUFDeEQsMkRBQTJEO1lBQzNELHdEQUF3RDtZQUN4RCw0REFBNEQ7WUFDNUQsK0NBQStDO1lBQy9DLHlEQUF5RDtZQUN6RCwyREFBMkQ7WUFDM0QsOERBQThEO1lBQzlELDhEQUE4RDtZQUM5RCwrQ0FBK0M7WUFDL0MsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsR0FBRyxDQUFDLENBQUM7WUFDM0QsSUFBSSxRQUFRLEVBQUUsQ0FBQztnQkFDZCxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsc0JBQXNCLENBQUMsUUFBUSxDQUFDLENBQUM7Z0JBQ3ZELElBQUksUUFBUSxFQUFFLENBQUM7b0JBQ2QsT0FBTyxRQUFRLENBQUM7Z0JBQ2pCLENBQUM7WUFDRixDQUFDO1lBQ0QsOERBQThEO1lBQzlELDREQUE0RDtZQUM1RCx5REFBeUQ7WUFDekQsZ0VBQWdFO1lBQ2hFLE1BQU0sU0FBUyxHQUFHLElBQUksQ0FBQyxrQ0FBa0MsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLEdBQUcsQ0FBQztnQkFDdkUsSUFBSSxDQUFDLGlDQUFpQyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsR0FBRyxDQUFDLENBQUM7WUFDdkQsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUVELDJEQUEyRDtRQUMzRCxzREFBc0Q7UUFDdEQsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7WUFDN0IsTUFBTSxRQUFRLEdBQUcsR0FBRyxDQUFDLFVBQVUsQ0FBQztZQUNoQyxNQUFNLElBQUksR0FBRyxFQUFFLENBQUMsMEJBQTBCLENBQUMsUUFBUSxDQUFDO2dCQUNuRCxDQUFDLENBQUMsSUFBSSxDQUFDLGVBQWUsQ0FBQyxRQUFRLENBQUM7Z0JBQ2hDLENBQUMsQ0FBQyxJQUFJLENBQUMseUJBQXlCLENBQUMsUUFBUSxDQUFDLENBQUM7WUFDNUMsTUFBTSxLQUFLLEdBQUcsSUFBSSxJQUFJLElBQUksQ0FBQyxXQUFXLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQztZQUNwRSxPQUFPLEtBQUssQ0FBQztRQUNkLENBQUM7UUFFRCw0QkFBNEI7UUFDNUIsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztZQUN4QyxPQUFPLElBQUksQ0FBQyxlQUFlLENBQUMsR0FBRyxDQUFDLENBQUM7UUFDbEMsQ0FBQztRQUVELGtDQUFrQztRQUNsQyxJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxVQUFVLENBQUMsSUFBSSxHQUFHLENBQUMsVUFBVSxDQUFDLElBQUksS0FBSyxNQUFNLEVBQUUsQ0FBQztZQUM3RyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7Ozs7Ozs7O09BVUc7SUFDSyxxQkFBcUIsQ0FBRSxJQUFZLEVBQUUsSUFBYTtRQUN6RCxJQUFJLE9BQU8sR0FBd0IsSUFBSSxDQUFDO1FBQ3hDLE9BQU8sT0FBTyxFQUFFLENBQUM7WUFDaEIsTUFBTSxVQUFVLEdBQ2YsRUFBRSxDQUFDLE9BQU8sQ0FBQyxPQUFPLENBQUMsSUFBSSxFQUFFLENBQUMsYUFBYSxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsT0FBTyxDQUFDO2dCQUMzRSxDQUFDLENBQUMsT0FBTyxDQUFDLFVBQVU7Z0JBQ3BCLENBQUMsQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsT0FBTyxDQUFDO29CQUN4RCxDQUFDLENBQUMsT0FBTyxDQUFDLFVBQVU7b0JBQ3BCLENBQUMsQ0FBQyxTQUFTLENBQUM7WUFDZixJQUFJLFVBQVUsSUFBSSxJQUFJLENBQUMseUJBQXlCLENBQUMsVUFBVSxFQUFFLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQ3BFLE1BQU0sR0FBRyxHQUFHLElBQUksQ0FBQyw2QkFBNkIsQ0FBQyxVQUFVLEVBQUUsSUFBSSxDQUFDLENBQUM7Z0JBQ2pFLE9BQU8sR0FBRyxDQUFDO1lBQ1osQ0FBQztZQUNELE9BQU8sR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDO1FBQzFCLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7OztPQUdHO0lBQ0sseUJBQXlCLENBQUUsVUFBbUMsRUFBRSxJQUFZO1FBQ25GLEtBQUssTUFBTSxTQUFTLElBQUksVUFBVSxFQUFFLENBQUM7WUFDcEMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUFDO2dCQUN4QyxTQUFTO1lBQ1YsQ0FBQztZQUNELEtBQUssTUFBTSxXQUFXLElBQUksU0FBUyxDQUFDLGVBQWUsQ0FBQyxZQUFZLEVBQUUsQ0FBQztnQkFDbEUsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsSUFBSSxXQUFXLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxJQUFJLEVBQUUsQ0FBQztvQkFDekUsT0FBTyxJQUFJLENBQUM7Z0JBQ2IsQ0FBQztZQUNGLENBQUM7UUFDRixDQUFDO1FBQ0QsT0FBTyxLQUFLLENBQUM7SUFDZCxDQUFDO0lBRUQ7Ozs7T0FJRztJQUNLLDZCQUE2QixDQUNwQyxVQUFtQyxFQUNuQyxJQUFZO1FBRVosS0FBSyxNQUFNLFNBQVMsSUFBSSxVQUFVLEVBQUUsQ0FBQztZQUNwQyxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsbUJBQW1CLENBQUMsU0FBUyxFQUFFLElBQUksQ0FBQyxDQUFDO1lBQ3pELElBQUksTUFBTSxFQUFFLENBQUM7Z0JBQ1osT0FBTyxNQUFNLENBQUM7WUFDZixDQUFDO1lBQ0QsS0FBSyxNQUFNLE1BQU0sSUFBSSxJQUFJLENBQUMsaUJBQWlCLENBQUMsU0FBUyxDQUFDLEVBQUUsQ0FBQztnQkFDeEQsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLDZCQUE2QixDQUFDLE1BQU0sRUFBRSxJQUFJLENBQUMsQ0FBQztnQkFDL0QsSUFBSSxLQUFLLEVBQUUsQ0FBQztvQkFDWCxPQUFPLEtBQUssQ0FBQztnQkFDZCxDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7O09BRUc7SUFDSyxtQkFBbUIsQ0FBRSxTQUF1QixFQUFFLElBQVk7UUFDakUsSUFBSSxDQUFDLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUFDO1lBQzFDLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLElBQUksR0FBRyxTQUFTLENBQUMsVUFBVSxDQUFDO1FBQ2xDLElBQUksQ0FBQyxFQUFFLENBQUMsa0JBQWtCLENBQUMsSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxXQUFXLEVBQUUsQ0FBQztZQUMzRixPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBQ0QsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLElBQUksRUFBRSxDQUFDO1lBQzVELE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLEdBQUcsR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDO1FBQ3ZCLE9BQU8sR0FBRyxDQUFDO0lBQ1osQ0FBQztJQUVEOzs7OztPQUtHO0lBQ0ssaUJBQWlCLENBQUUsU0FBdUI7UUFDakQsTUFBTSxNQUFNLEdBQXFCLEVBQUUsQ0FBQztRQUNwQyxNQUFNLElBQUksR0FBRyxDQUFDLElBQThCLEVBQVEsRUFBRTtZQUNyRCxJQUFJLElBQUksSUFBSSxFQUFFLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQzlCLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBRSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUUsQ0FBQyxDQUFDO1lBQ3JDLENBQUM7UUFDRixDQUFDLENBQUM7UUFDRixJQUFJLEVBQUUsQ0FBQyxPQUFPLENBQUMsU0FBUyxDQUFDLEVBQUUsQ0FBQztZQUMzQixNQUFNLENBQUMsSUFBSSxDQUFDLENBQUUsR0FBRyxTQUFTLENBQUMsVUFBVSxDQUFFLENBQUMsQ0FBQztRQUMxQyxDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsY0FBYyxDQUFDLFNBQVMsQ0FBQyxFQUFFLENBQUM7WUFDekMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxRQUFRLENBQUMsQ0FBQztZQUN6QixJQUFJLFNBQVMsQ0FBQyxXQUFXLEVBQUUsQ0FBQztnQkFDM0IsSUFBSSxDQUFDLFNBQVMsQ0FBQyxXQUFXLENBQUMsS0FBSyxDQUFDLENBQUM7WUFDbkMsQ0FBQztZQUNELElBQUksQ0FBQyxTQUFTLENBQUMsWUFBWSxDQUFDLENBQUM7UUFDOUIsQ0FBQzthQUFNLElBQUksRUFBRSxDQUFDLGFBQWEsQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUFDO1lBQ3hDLElBQUksQ0FBQyxTQUFTLENBQUMsYUFBYSxDQUFDLENBQUM7WUFDOUIsSUFBSSxDQUFDLFNBQVMsQ0FBQyxhQUFhLENBQUMsQ0FBQztRQUMvQixDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsY0FBYyxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxTQUFTLENBQUM7WUFDeEUsRUFBRSxDQUFDLGdCQUFnQixDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxTQUFTLENBQUM7WUFDaEUsRUFBRSxDQUFDLGFBQWEsQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLFNBQVMsQ0FBQyxFQUFFLENBQUM7WUFDL0QsSUFBSSxDQUFDLFNBQVMsQ0FBQyxTQUFTLENBQUMsQ0FBQztRQUMzQixDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsU0FBUyxDQUFDLEVBQUUsQ0FBQztZQUM1QyxLQUFLLE1BQU0sTUFBTSxJQUFJLFNBQVMsQ0FBQyxTQUFTLENBQUMsT0FBTyxFQUFFLENBQUM7Z0JBQ2xELE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBRSxHQUFHLE1BQU0sQ0FBQyxVQUFVLENBQUUsQ0FBQyxDQUFDO1lBQ3ZDLENBQUM7UUFDRixDQUFDO2FBQU0sSUFBSSxFQUFFLENBQUMsa0JBQWtCLENBQUMsU0FBUyxDQUFDLEVBQUUsQ0FBQztZQUM3QyxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsU0FBUyxDQUFDLFNBQVMsQ0FBQyxDQUFDO1lBQzNELEtBQUssTUFBTSxLQUFLLElBQUksTUFBTSxFQUFFLENBQUM7Z0JBQzVCLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBRSxHQUFHLEtBQUssQ0FBRSxDQUFDLENBQUM7WUFDM0IsQ0FBQztRQUNGLENBQUM7UUFDRCxNQUFNLE1BQU0sR0FBRyxNQUFNLENBQUM7UUFDdEIsT0FBTyxNQUFNLENBQUM7SUFDZixDQUFDO0lBRUQ7Ozs7O09BS0c7SUFDSyxlQUFlLENBQUUsSUFBYTtRQUNyQyxJQUFJLE9BQU8sR0FBd0IsSUFBSSxDQUFDLE1BQU0sQ0FBQztRQUMvQyxPQUFPLE9BQU8sRUFBRSxDQUFDO1lBQ2hCLE1BQU0sU0FBUyxHQUFHLElBQUksQ0FBQyxjQUFjLENBQUMsR0FBRyxDQUFDLE9BQU8sQ0FBQyxDQUFDO1lBQ25ELElBQUksU0FBUyxFQUFFLENBQUM7Z0JBQ2YsT0FBTyxTQUFTLENBQUM7WUFDbEIsQ0FBQztZQUNELE9BQU8sR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDO1FBQzFCLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7Ozs7Ozs7O09BUUc7SUFDSywyQkFBMkIsQ0FBRSxHQUFrQjtRQUN0RCxNQUFNLFdBQVcsR0FBRyxDQUFDLElBQVksRUFBRSxJQUFhLEVBQXNCLEVBQUU7WUFDdkUsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUNoRCxJQUFJLE1BQU0sRUFBRSxDQUFDO2dCQUNaLE9BQU8sTUFBTSxDQUFDO1lBQ2YsQ0FBQztZQUNELE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQyxrQ0FBa0MsQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDO2dCQUN6RSw2REFBNkQ7Z0JBQzdELDREQUE0RDtnQkFDNUQsc0RBQXNEO2dCQUN0RCxxREFBcUQ7Z0JBQ3JELElBQUksQ0FBQyxpQ0FBaUMsQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLENBQUM7WUFDcEQsT0FBTyxjQUFjLENBQUM7UUFDdkIsQ0FBQyxDQUFDO1FBRUYsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7WUFDMUIsTUFBTSxNQUFNLEdBQUcsV0FBVyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsR0FBRyxDQUFDLENBQUM7WUFDMUMsT0FBTyxNQUFNLENBQUM7UUFDZixDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztZQUN4QyxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLENBQUM7WUFDekMsSUFBSSxJQUFJLEVBQUUsQ0FBQztnQkFDVixNQUFNLE1BQU0sR0FBRyxXQUFXLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxHQUFHLENBQUMsQ0FBQztnQkFDM0MsT0FBTyxNQUFNLENBQUM7WUFDZixDQUFDO1FBQ0YsQ0FBQztRQUNELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7Ozs7O09BTUc7SUFDSyx5QkFBeUIsQ0FBRSxJQUFZO1FBQzlDLEtBQUssTUFBTSxDQUFFLElBQUksRUFBRSxLQUFLLENBQUUsSUFBSSxJQUFJLENBQUMsbUJBQW1CLEVBQUUsQ0FBQztZQUN4RCxJQUFJLElBQUksQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUNuQyxTQUFTO1lBQ1YsQ0FBQztZQUNELElBQUksS0FBSyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUNyQixPQUFPLElBQUksQ0FBQztZQUNiLENBQUM7UUFDRixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsS0FBSyxDQUFDO1FBQ3JCLE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7Ozs7Ozs7T0FTRztJQUNLLHlCQUF5QixDQUFFLElBQVk7UUFDOUMsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQy9DLElBQUksTUFBTSxDQUFDLE1BQU0sS0FBSyxRQUFRLEVBQUUsQ0FBQztZQUNoQyxNQUFNLE1BQU0sR0FBRyxNQUFNLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQztZQUNwQyxPQUFPLE1BQU0sQ0FBQztRQUNmLENBQUM7UUFDRCxJQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO1lBQ3pCLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxNQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMsb0JBQW9CLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsR0FBRyxDQUFDLENBQUMsQ0FBQztRQUNuRSxJQUFJLE9BQU8sQ0FBQyxNQUFNLEtBQUssUUFBUSxFQUFFLENBQUM7WUFDakMsTUFBTSxNQUFNLEdBQUcsT0FBTyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUM7WUFDckMsT0FBTyxNQUFNLENBQUM7UUFDZixDQUFDO1FBQ0QsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOzs7Ozs7T0FNRztJQUNLLGtDQUFrQyxDQUFFLElBQVksRUFBRSxJQUFhO1FBQ3RFLElBQUksT0FBTyxHQUF3QixJQUFJLENBQUMsTUFBTSxDQUFDO1FBQy9DLE9BQU8sT0FBTyxFQUFFLENBQUM7WUFDaEIsSUFBSSxFQUFFLENBQUMsY0FBYyxDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUM7Z0JBQ2hDLEtBQUssTUFBTSxLQUFLLElBQUksT0FBTyxDQUFDLFVBQVUsSUFBSSxFQUFFLEVBQUUsQ0FBQztvQkFDOUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLElBQUksSUFBSSxDQUFDLEtBQUssQ0FBQyxJQUFJO3dCQUMxRSxDQUFDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDO3dCQUNuQyxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUM7d0JBQ3JDLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxhQUFhLEVBQUUsTUFBTSxJQUFJLENBQUMsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO3dCQUM5QyxTQUFTO29CQUNWLENBQUM7b0JBQ0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQyxDQUFDO29CQUMxRSxJQUFJLFFBQVEsRUFBRSxDQUFDO3dCQUNkLE9BQU8sUUFBUSxDQUFDO29CQUNqQixDQUFDO2dCQUNGLENBQUM7Z0JBQ0QsT0FBTyxTQUFTLENBQUM7WUFDbEIsQ0FBQztZQUNELE9BQU8sR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDO1FBQzFCLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7Ozs7Ozs7Ozs7T0FVRztJQUNLLGlDQUFpQyxDQUFFLElBQVksRUFBRSxJQUFhO1FBQ3JFLElBQUksT0FBTyxHQUF3QixJQUFJLENBQUM7UUFDeEMsT0FBTyxPQUFPLEVBQUUsQ0FBQztZQUNoQixNQUFNLFVBQVUsR0FDZixFQUFFLENBQUMsT0FBTyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxhQUFhLENBQUMsT0FBTyxDQUFDLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxPQUFPLENBQUM7Z0JBQzNFLENBQUMsQ0FBQyxPQUFPLENBQUMsVUFBVTtnQkFDcEIsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsT0FBTyxDQUFDLElBQUksRUFBRSxDQUFDLGVBQWUsQ0FBQyxPQUFPLENBQUM7b0JBQ3hELENBQUMsQ0FBQyxPQUFPLENBQUMsVUFBVTtvQkFDcEIsQ0FBQyxDQUFDLFNBQVMsQ0FBQztZQUNmLElBQUksVUFBVSxFQUFFLENBQUM7Z0JBQ2hCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyw2QkFBNkIsQ0FBQyxVQUFVLEVBQUUsSUFBSSxDQUFDLENBQUM7Z0JBQ3RFLElBQUksUUFBUSxFQUFFLENBQUM7b0JBQ2QsT0FBTyxRQUFRLENBQUM7Z0JBQ2pCLENBQUM7WUFDRixDQUFDO1lBQ0QsT0FBTyxHQUFHLE9BQU8sQ0FBQyxNQUFNLENBQUM7UUFDMUIsQ0FBQztRQUNELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7OztPQUlHO0lBQ0ssNkJBQTZCLENBQ3BDLFVBQW1DLEVBQ25DLElBQVk7UUFFWixLQUFLLE1BQU0sU0FBUyxJQUFJLFVBQVUsRUFBRSxDQUFDO1lBQ3BDLElBQUksQ0FBQyxFQUFFLENBQUMsbUJBQW1CLENBQUMsU0FBUyxDQUFDLEVBQUUsQ0FBQztnQkFDeEMsU0FBUztZQUNWLENBQUM7WUFDRCxLQUFLLE1BQU0sV0FBVyxJQUFJLFNBQVMsQ0FBQyxlQUFlLENBQUMsWUFBWSxFQUFFLENBQUM7Z0JBQ2xFLElBQUksQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsSUFBSSxXQUFXLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxJQUFJO29CQUN2RSxDQUFDLFdBQVcsQ0FBQyxJQUFJO29CQUNqQixDQUFDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxXQUFXLENBQUMsSUFBSSxDQUFDO29CQUN6QyxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsV0FBVyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUM7b0JBQzNDLENBQUMsV0FBVyxDQUFDLElBQUksQ0FBQyxhQUFhLEVBQUUsTUFBTSxJQUFJLENBQUMsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO29CQUNwRCxTQUFTO2dCQUNWLENBQUM7Z0JBQ0QsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQyxDQUFDO2dCQUNoRixJQUFJLFFBQVEsRUFBRSxDQUFDO29CQUNkLE9BQU8sUUFBUSxDQUFDO2dCQUNqQixDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7Ozs7OztPQU1HO0lBQ0ssdUJBQXVCLENBQzlCLEdBQThCLEVBQzlCLFVBQXlCO1FBRXpCLElBQUksQ0FBQyxHQUFHLEVBQUUsQ0FBQztZQUNWLE9BQU8sU0FBUyxDQUFDO1FBQ2xCLENBQUM7UUFDRCxJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxDQUFDLG9CQUFvQixDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7WUFDN0QsT0FBTyxHQUFHLENBQUM7UUFDWixDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7WUFDMUIsTUFBTSxHQUFHLEdBQUcsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLEdBQUcsQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUNqRCxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMsZ0JBQWdCLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDO1lBQzdDLElBQUksS0FBSyxFQUFFLENBQUM7Z0JBQ1gsT0FBTyxLQUFLLENBQUM7WUFDZCxDQUFDO1FBQ0YsQ0FBQztRQUNELE9BQU8sU0FBUyxDQUFDO0lBQ2xCLENBQUM7SUFFRDs7Ozs7Ozs7O09BU0c7SUFDSyxrQkFBa0IsQ0FDekIsRUFBOEIsRUFDOUIsV0FBbUIsRUFDbkIsVUFBeUIsRUFDekIsS0FBYSxFQUNiLE9BQXFCLEVBQ3JCLFlBQXlCLEVBQ3pCLGFBQXNCO1FBRXRCLElBQUksS0FBSyxHQUFHLENBQUMsSUFBSSxPQUFPLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQzlDLE9BQU87UUFDUixDQUFDO1FBQ0QsT0FBTyxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsQ0FBQztRQUVoQiw4Q0FBOEM7UUFDOUMsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLE9BQU8sQ0FBQyxFQUFFLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUNwRCxJQUFJLENBQUMsbUJBQW1CLENBQUMsRUFBRSxDQUFDLElBQUksRUFBRSxXQUFXLEVBQUUsVUFBVSxFQUFFLEtBQUssRUFBRSxPQUFPLEVBQUUsYUFBYSxDQUFDLENBQUM7WUFDMUYsT0FBTztRQUNSLENBQUM7UUFFRCxNQUFNLElBQUksR0FBRyxDQUFDLElBQWEsRUFBUSxFQUFFO1lBQ3BDLElBQUksSUFBSSxLQUFLLEVBQUUsQ0FBQyxJQUFJLElBQUksQ0FDdkIsRUFBRSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQztnQkFDN0IsRUFBRSxDQUFDLGVBQWUsQ0FBQyxJQUFJLENBQUM7Z0JBQ3hCLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLENBQUM7Z0JBQzlCLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsQ0FDNUIsRUFBRSxDQUFDO2dCQUNILCtEQUErRDtnQkFDL0QsT0FBTztZQUNSLENBQUM7WUFDRCxJQUFJLEVBQUUsQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7Z0JBQ25ELElBQUksQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsVUFBVSxFQUFFLFdBQVcsRUFBRSxVQUFVLEVBQUUsS0FBSyxFQUFFLE9BQU8sRUFBRSxhQUFhLENBQUMsQ0FBQztZQUNuRyxDQUFDO1lBQ0QsSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQzlCLE1BQU0sT0FBTyxHQUFHLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDO29CQUMxRCxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLElBQUksQ0FBQyxXQUFXLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDO3dCQUM5RSxDQUFDLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJO3dCQUN0QixDQUFDLENBQUMsU0FBUyxDQUFDLENBQUM7Z0JBQ2YsSUFBSSxPQUFPLEVBQUUsQ0FBQztvQkFDYixZQUFZLENBQUMsR0FBRyxDQUFDLE9BQU8sQ0FBQyxDQUFDO2dCQUMzQixDQUFDO1lBQ0YsQ0FBQztZQUNELElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7Z0JBQy9CLE1BQU0sVUFBVSxHQUFHLElBQUksQ0FBQyxlQUFlLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDO2dCQUN6RCxJQUNDLFVBQVUsS0FBSyxNQUFNO29CQUNyQixVQUFVLEtBQUssb0JBQW9CO29CQUNuQyxVQUFVLEtBQUssdUJBQXVCO29CQUN0QyxVQUFVLEtBQUsscUJBQXFCLEVBQ25DLENBQUM7b0JBQ0Ysb0RBQW9EO29CQUNwRCx1REFBdUQ7b0JBQ3ZELHdEQUF3RDtvQkFDeEQsd0JBQXdCO29CQUN4QixNQUFNLFdBQVcsR0FBRyxJQUFJLENBQUMsZUFBZSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztvQkFDbkQsSUFBSSxXQUFXLEVBQUUsQ0FBQzt3QkFDakIsV0FBVyxDQUFDLEdBQUcsR0FBRyxXQUFXLENBQUM7d0JBQzlCLElBQUksV0FBVyxDQUFDLEtBQUssS0FBSyxTQUFTLEVBQUUsQ0FBQzs0QkFDckMsV0FBVyxDQUFDLEtBQUssR0FBRyxhQUFhLENBQUM7d0JBQ25DLENBQUM7b0JBQ0YsQ0FBQzt5QkFBTSxDQUFDO3dCQUNQLElBQUksQ0FBQyxhQUFhLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxFQUFFLEdBQUcsRUFBRyxXQUFXLEVBQUUsS0FBSyxFQUFHLGFBQWEsRUFBRSxDQUFDLENBQUM7b0JBQzVFLENBQUM7Z0JBQ0YsQ0FBQztZQUNGLENBQUM7WUFDRCxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsQ0FBQztRQUM3QixDQUFDLENBQUM7UUFDRixJQUFJLENBQUMsRUFBRSxDQUFDLElBQUksQ0FBQyxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7Ozs7O09BT0c7SUFDSyxtQkFBbUIsQ0FDMUIsSUFBbUIsRUFDbkIsV0FBbUIsRUFDbkIsVUFBeUIsRUFDekIsS0FBYSxFQUNiLE9BQXFCLEVBQ3JCLGFBQXNCO1FBRXRCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyx1QkFBdUIsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFDaEUsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDO1lBQ2YsT0FBTztRQUNSLENBQUM7UUFDRCxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLFFBQVEsQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQzdCLENBQUM7UUFDRixNQUFNLFFBQVEsR0FBRyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7UUFDdkUsTUFBTSxJQUFJLEdBQUcsUUFBUSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxDQUFDO1FBQ3hELE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyxlQUFlLENBQUMsUUFBUSxDQUFDLElBQUksYUFBYSxDQUFDO1FBQzlELE1BQU0sS0FBSyxHQUFHLElBQUksQ0FBQyxNQUFNLENBQUMsS0FBSyxJQUFJLFNBQVMsRUFBRTtZQUM3QyxRQUFRO1lBQ1IsSUFBSSxFQUFHLE1BQU07WUFDYixJQUFJO1lBQ0osS0FBSztZQUNMLEdBQUcsRUFBSSxXQUFXO1lBQ2xCLGdFQUFnRTtZQUNoRSxFQUFFLEVBQUssTUFBTTtTQUNiLENBQUMsQ0FBQztRQUNILGlFQUFpRTtRQUNqRSx5Q0FBeUM7UUFDekMsTUFBTSxhQUFhLEdBQUcsSUFBSSxHQUFHLEVBQVUsQ0FBQztRQUN4QyxJQUFJLENBQUMsa0JBQWtCLENBQUMsUUFBUSxFQUFFLFFBQVEsRUFBRSxVQUFVLEVBQUUsS0FBSyxHQUFHLENBQUMsRUFBRSxPQUFPLEVBQUUsYUFBYSxFQUFFLEtBQUssQ0FBQyxDQUFDO1FBQ2xHLElBQUksYUFBYSxDQUFDLElBQUksR0FBRyxDQUFDLEVBQUUsQ0FBQztZQUM1QixLQUFLLENBQUMsWUFBWSxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsYUFBYSxDQUFDLENBQUM7UUFDaEQsQ0FBQztJQUNGLENBQUM7SUFFRDs7OztPQUlHO0lBQ0ssTUFBTSxDQUFFLFFBQWdCLEVBQUUsSUFBYTtRQUM5QyxJQUFJLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUNuQyxJQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsRUFBRSxDQUFDLENBQUM7UUFDbEMsQ0FBQztRQUVELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBRSxDQUFDO1FBQy9DLE1BQU0sU0FBUyxHQUFHLFFBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUU7WUFDbkMsT0FBTyxDQUFDLENBQUMsUUFBUSxLQUFLLElBQUksQ0FBQyxRQUFRO2dCQUNsQyxDQUFDLENBQUMsSUFBSSxLQUFLLElBQUksQ0FBQyxJQUFJO2dCQUNwQixDQUFDLENBQUMsSUFBSSxLQUFLLElBQUksQ0FBQyxJQUFJLENBQUM7UUFDdkIsQ0FBQyxDQUFDLENBQUM7UUFFSCxJQUFJLFNBQVMsRUFBRSxDQUFDO1lBQ2YsT0FBTyxTQUFTLENBQUM7UUFDbEIsQ0FBQztRQUNELFFBQVEsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDcEIsT0FBTyxJQUFJLENBQUM7SUFDYixDQUFDO0lBRUQ7OztPQUdHO0lBQ0ssV0FBVyxDQUFFLElBQWEsRUFBRSxVQUF5QjtRQUM1RCx5Q0FBeUM7UUFDekMsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUN6QyxJQUFJLENBQUMseUJBQXlCLENBQUMsSUFBSSxFQUFFLFVBQVUsQ0FBQyxDQUFDO1lBQ2pELE9BQU87UUFDUixDQUFDO1FBRUQsK0JBQStCO1FBQy9CLElBQUksRUFBRSxDQUFDLHlCQUF5QixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDeEMsSUFBSSxDQUFDLHdCQUF3QixDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsQ0FBQztZQUNoRCxPQUFPO1FBQ1IsQ0FBQztRQUVELG9DQUFvQztRQUNwQyxJQUFJLEVBQUUsQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsYUFBYSxDQUFDLElBQUksS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLFdBQVcsRUFBRSxDQUFDO1lBQzFGLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7WUFDN0MsT0FBTztRQUNSLENBQUM7UUFFRCx5RUFBeUU7UUFDekUsSUFBSSxFQUFFLENBQUMsZ0JBQWdCLENBQUMsSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLFVBQVUsRUFBRSxDQUFDO1lBQ2xELElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7WUFDN0MsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsQ0FBQztZQUMvQyxPQUFPO1FBQ1IsQ0FBQztRQUVELDBDQUEwQztRQUMxQyxJQUFJLEVBQUUsQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsV0FBVyxFQUFFLENBQUM7WUFDeEQsSUFBSSxDQUFDLHNCQUFzQixDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsQ0FBQztZQUM5QyxPQUFPO1FBQ1IsQ0FBQztRQUVELCtCQUErQjtRQUMvQixJQUFJLEVBQUUsQ0FBQyxpQkFBaUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7WUFDbkQsSUFBSSxDQUFDLGlCQUFpQixDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsQ0FBQztZQUN6QyxPQUFPO1FBQ1IsQ0FBQztRQUVELHNCQUFzQjtRQUN0QixJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUM5QixJQUFJLENBQUMsaUJBQWlCLENBQUMsSUFBSSxFQUFFLFVBQVUsQ0FBQyxDQUFDO1lBQ3pDLE9BQU87UUFDUixDQUFDO0lBQ0YsQ0FBQztJQUVEOztPQUVHO0lBQ0sseUJBQXlCLENBQUUsSUFBaUMsRUFBRSxVQUF5QjtRQUM5RixNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMscUJBQXFCLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQy9ELElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUFDLE9BQU87UUFBQyxDQUFDO1FBRTVCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1FBQ2hDLE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztRQUNGLE1BQU0sUUFBUSxHQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FBQztRQUN2RSxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDLENBQUM7UUFFcEQsb0VBQW9FO1FBQ3BFLElBQUksUUFBUSxLQUFLLFFBQVEsSUFBSSxRQUFRLEtBQUssTUFBTSxFQUFFLENBQUM7WUFBQyxPQUFPO1FBQUMsQ0FBQztRQUU3RCxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsRUFBRTtZQUN4QixRQUFRO1lBQ1IsSUFBSSxFQUFXLGNBQWM7WUFDN0IsSUFBSTtZQUNKLFlBQVksRUFBRyxRQUFRO1lBQ3ZCLFVBQVUsRUFBSyxVQUFVO1NBQ3pCLENBQUMsQ0FBQztJQUNKLENBQUM7SUFFRDs7T0FFRztJQUNLLHdCQUF3QixDQUFFLElBQWdDLEVBQUUsVUFBeUI7UUFDNUYsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsQ0FBQztRQUMvRCxJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7WUFBQyxPQUFPO1FBQUMsQ0FBQztRQUU1QixNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7UUFDRixNQUFNLFFBQVEsR0FBRyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7UUFDdkUsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxDQUFDO1FBRXBELElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxFQUFFO1lBQ3hCLFFBQVE7WUFDUixJQUFJLEVBQVMsZUFBZTtZQUM1QixJQUFJO1lBQ0osVUFBVSxFQUFHLFVBQVU7U0FDdkIsQ0FBQyxDQUFDO0lBQ0osQ0FBQztJQUVEOztPQUVHO0lBQ0sscUJBQXFCLENBQUUsSUFBeUIsRUFBRSxVQUF5QjtRQUNsRixvQ0FBb0M7UUFDcEMsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDOUMsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLENBQUM7WUFDcEUsSUFBSSxDQUFDLFVBQVUsRUFBRSxDQUFDO2dCQUFDLE9BQU87WUFBQyxDQUFDO1lBRTVCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztZQUNyQyxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7WUFDRixNQUFNLFFBQVEsR0FBRyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7WUFDdkUsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxDQUFDO1lBRXBELElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxFQUFFO2dCQUN4QixRQUFRO2dCQUNSLElBQUksRUFBVyxlQUFlO2dCQUM5QixJQUFJO2dCQUNKLFlBQVksRUFBRyxRQUFRO2dCQUN2QixVQUFVLEVBQUssVUFBVTthQUN6QixDQUFDLENBQUM7WUFDSCxPQUFPO1FBQ1IsQ0FBQztRQUVELHNDQUFzQztRQUN0QyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDaEMsTUFBTSxPQUFPLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7WUFDL0IsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxPQUFPLENBQUMsQ0FBQztZQUN2RCxJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7Z0JBQUMsT0FBTztZQUFDLENBQUM7WUFFNUIsTUFBTSxFQUFFLElBQUksRUFBRSxTQUFTLEVBQUUsR0FBRyxFQUFFLENBQUMsNkJBQTZCLENBQzNELFVBQVUsRUFDVixJQUFJLENBQUMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxDQUN6QixDQUFDO1lBQ0YsTUFBTSxRQUFRLEdBQUcsR0FBRyxVQUFVLENBQUMsUUFBUSxJQUFJLElBQUksR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsRUFBRSxDQUFDO1lBQ3ZFLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsRUFBRSxHQUFHLENBQUMsQ0FBQztZQUVwRCxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsRUFBRTtnQkFDeEIsUUFBUTtnQkFDUixJQUFJLEVBQVMsY0FBYztnQkFDM0IsSUFBSTtnQkFDSixVQUFVLEVBQUcsVUFBVTthQUN2QixDQUFDLENBQUM7UUFDSixDQUFDO0lBQ0YsQ0FBQztJQUVEOztPQUVHO0lBQ0sscUJBQXFCLENBQUUsSUFBdUIsRUFBRSxVQUF5QjtRQUNoRixJQUFJLENBQUMsRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDO1lBQUMsT0FBTztRQUFDLENBQUM7UUFFaEUsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDMUUsSUFBSSxDQUFDLFVBQVUsRUFBRSxDQUFDO1lBQUMsT0FBTztRQUFDLENBQUM7UUFFNUIsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1FBQzdDLE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztRQUNGLE1BQU0sUUFBUSxHQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FBQztRQUN2RSxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDLENBQUM7UUFFcEQsaUVBQWlFO1FBQ2pFLElBQUksVUFBVSxLQUFLLFFBQVEsSUFBSSxVQUFVLEtBQUssTUFBTSxFQUFFLENBQUM7WUFBQyxPQUFPO1FBQUMsQ0FBQztRQUVqRSxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsRUFBRTtZQUN4QixRQUFRO1lBQ1IsSUFBSSxFQUFXLFlBQVk7WUFDM0IsSUFBSTtZQUNKLFlBQVksRUFBRyxVQUFVO1lBQ3pCLFVBQVUsRUFBSyxVQUFVO1NBQ3pCLENBQUMsQ0FBQztJQUNKLENBQUM7SUFFRDs7T0FFRztJQUNLLHVCQUF1QixDQUFFLElBQXVCLEVBQUUsVUFBeUI7UUFDbEYsS0FBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFLENBQUM7WUFDaEQsTUFBTSxHQUFHLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBRSxDQUFDLENBQUUsQ0FBQztZQUNoQyxNQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMscUJBQXFCLENBQUMsR0FBRyxDQUFDLENBQUM7WUFDaEQsSUFBSSxDQUFDLE9BQU8sRUFBRSxDQUFDO2dCQUFDLFNBQVM7WUFBQyxDQUFDO1lBRTNCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxlQUFlLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLFdBQVcsQ0FBQztZQUN0RSxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7WUFDRixNQUFNLFFBQVEsR0FBRyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7WUFDdkUsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxDQUFDO1lBRXBELElBQUksQ0FBQyxPQUFPLENBQUMsT0FBTyxFQUFFO2dCQUNyQixRQUFRO2dCQUNSLElBQUksRUFBUyxXQUFXO2dCQUN4QixJQUFJO2dCQUNKLFVBQVUsRUFBRyxPQUFPO2dCQUNwQixPQUFPLEVBQU0sT0FBTyxDQUFDLE9BQU8sUUFBUSxFQUFFO2FBQ3RDLENBQUMsQ0FBQztRQUNKLENBQUM7SUFDRixDQUFDO0lBRUQ7O09BRUc7SUFDSyxzQkFBc0IsQ0FBRSxJQUE0QixFQUFFLFVBQXlCO1FBQ3RGLElBQUksQ0FBQyxFQUFFLENBQUMsc0JBQXNCLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFBQyxPQUFPO1FBQUMsQ0FBQztRQUV0RCxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMscUJBQXFCLENBQUMsSUFBSSxDQUFDLFdBQVksQ0FBQyxDQUFDO1FBQ2pFLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUFDLE9BQU87UUFBQyxDQUFDO1FBRTVCLE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztRQUNGLE1BQU0sUUFBUSxHQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FBQztRQUN2RSxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDLENBQUM7UUFFcEQsc0NBQXNDO1FBQ3RDLE1BQU0sS0FBSyxHQUFhLEVBQUUsQ0FBQztRQUMzQixLQUFLLE1BQU0sT0FBTyxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLENBQUM7WUFDMUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO2dCQUNuQyxLQUFLLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDL0IsQ0FBQztRQUNGLENBQUM7UUFFRCxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsRUFBRTtZQUN4QixRQUFRO1lBQ1IsSUFBSSxFQUFTLGlCQUFpQjtZQUM5QixJQUFJO1lBQ0osVUFBVSxFQUFHLFVBQVU7WUFDdkIsT0FBTyxFQUFNLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1NBQzdCLENBQUMsQ0FBQztJQUNKLENBQUM7SUFFRDs7T0FFRztJQUNLLGlCQUFpQixDQUFFLElBQXdCLEVBQUUsVUFBeUI7UUFDN0UsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLElBQUksQ0FBQyxVQUFXLENBQUMsQ0FBQztRQUNoRSxJQUFJLENBQUMsVUFBVSxFQUFFLENBQUM7WUFBQyxPQUFPO1FBQUMsQ0FBQztRQUU1QixNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7UUFDRixNQUFNLFFBQVEsR0FBRyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7UUFDdkUsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxDQUFDO1FBRXBELElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxFQUFFO1lBQ3hCLFFBQVE7WUFDUixJQUFJLEVBQVMsUUFBUTtZQUNyQixJQUFJO1lBQ0osVUFBVSxFQUFHLFVBQVU7U0FDdkIsQ0FBQyxDQUFDO0lBQ0osQ0FBQztJQUVEOztPQUVHO0lBQ0ssaUJBQWlCLENBQUUsSUFBc0IsRUFBRSxVQUF5QjtRQUMzRSxNQUFNLFVBQVUsR0FBRyxJQUFJLENBQUMscUJBQXFCLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQy9ELElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUFDLE9BQU87UUFBQyxDQUFDO1FBRTVCLE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztRQUNGLE1BQU0sUUFBUSxHQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FBQztRQUN2RSxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDLENBQUM7UUFFcEQsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLEVBQUU7WUFDeEIsUUFBUTtZQUNSLElBQUksRUFBUyxRQUFRO1lBQ3JCLElBQUk7WUFDSixVQUFVLEVBQUcsVUFBVTtTQUN2QixDQUFDLENBQUM7SUFDSixDQUFDO0lBRUQ7O09BRUc7SUFDSyxxQkFBcUIsQ0FBRSxJQUFtQjtRQUNqRCxtQkFBbUI7UUFDbkIsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDM0IsT0FBTyxJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUM5QyxDQUFDO1FBRUQscUVBQXFFO1FBQ3JFLElBQUksRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDekMsT0FBTyxJQUFJLENBQUMscUJBQXFCLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDO1FBQ3BELENBQUM7UUFFRCwrQkFBK0I7UUFDL0IsSUFBSSxFQUFFLENBQUMseUJBQXlCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUN4QyxPQUFPLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDcEQsQ0FBQztRQUVELGdGQUFnRjtRQUNoRixJQUFJLElBQUksQ0FBQyxJQUFJLEtBQUssRUFBRSxDQUFDLFVBQVUsQ0FBQyxXQUFXLEVBQUUsQ0FBQztZQUM3QyxPQUFPLFNBQVMsQ0FBQztRQUNsQixDQUFDO1FBRUQsT0FBTyxTQUFTLENBQUM7SUFDbEIsQ0FBQztJQUVEOztPQUVHO0lBQ0ssT0FBTyxDQUFFLFFBQWdCLEVBQUUsSUFBYztRQUNoRCxJQUFJLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUNwQyxJQUFJLENBQUMsVUFBVSxDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsRUFBRSxDQUFDLENBQUM7UUFDbkMsQ0FBQztRQUVELE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUMsR0FBRyxDQUFDLFFBQVEsQ0FBRSxDQUFDO1FBQ2hELE1BQU0sV0FBVyxHQUFHLFFBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUU7WUFDckMsT0FBTyxDQUFDLENBQUMsUUFBUSxLQUFLLElBQUksQ0FBQyxRQUFRO2dCQUNsQyxDQUFDLENBQUMsSUFBSSxLQUFLLElBQUksQ0FBQyxJQUFJO2dCQUNwQixDQUFDLENBQUMsSUFBSSxLQUFLLElBQUksQ0FBQyxJQUFJLENBQUM7UUFDdkIsQ0FBQyxDQUFDLENBQUM7UUFFSCxJQUFJLENBQUMsV0FBVyxFQUFFLENBQUM7WUFDbEIsUUFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUNyQixDQUFDO0lBQ0YsQ0FBQztJQUVEOztjQUVJO0lBQ0kseUJBQXlCLENBQUUsSUFBbUI7UUFDckQsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDM0IsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQztZQUN2Qiw4RUFBOEU7WUFDOUUsTUFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUNwRCxJQUFJLFVBQVUsRUFBRSxDQUFDO2dCQUNoQixPQUFPLFVBQVUsQ0FBQztZQUNuQixDQUFDO1lBQ0QsT0FBTyxJQUFJLENBQUM7UUFDYixDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsMEJBQTBCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUN6QyxNQUFNLEtBQUssR0FBRyxJQUFJLENBQUMsZ0JBQWdCLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDMUMsT0FBTyxLQUFLLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDO1FBQ3hCLENBQUM7UUFDRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7O2NBRUk7SUFDSSxlQUFlLENBQUUsSUFBaUM7UUFDekQsTUFBTSxLQUFLLEdBQUcsSUFBSSxDQUFDLGdCQUFnQixDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzFDLElBQUksS0FBSyxDQUFDLE1BQU0sS0FBSyxDQUFDO1lBQUUsT0FBTyxTQUFTLENBQUM7UUFFekMsMkNBQTJDO1FBQzNDLE1BQU0sUUFBUSxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUM7UUFDakMsSUFBSSxJQUFJLENBQUMsV0FBVyxDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO1lBQ3BDLE9BQU8sUUFBUSxDQUFDO1FBQ2pCLENBQUM7UUFFRCw2QkFBNkI7UUFDN0IsTUFBTSxRQUFRLEdBQUcsS0FBSyxDQUFFLEtBQUssQ0FBQyxNQUFNLEdBQUcsQ0FBQyxDQUFFLENBQUM7UUFDM0MsS0FBSyxNQUFNLENBQUUsSUFBSSxDQUFFLElBQUksSUFBSSxDQUFDLFdBQVcsRUFBRSxDQUFDO1lBQ3pDLElBQUksSUFBSSxDQUFDLFFBQVEsQ0FBQyxJQUFJLFFBQVEsRUFBRSxDQUFDLElBQUksSUFBSSxLQUFLLFFBQVEsRUFBRSxDQUFDO2dCQUN4RCxPQUFPLElBQUksQ0FBQztZQUNiLENBQUM7UUFDRixDQUFDO1FBRUQsT0FBTyxRQUFRLENBQUM7SUFDakIsQ0FBQztJQUVEOztlQUVLO0lBQ0csZ0JBQWdCLENBQUUsSUFBWTtRQUNyQyxPQUFPLElBQUksQ0FBRSxDQUFDLENBQUUsSUFBSSxHQUFHLElBQUksSUFBSSxDQUFFLENBQUMsQ0FBRSxJQUFJLEdBQUcsQ0FBQztJQUM3QyxDQUFDO0lBRUQ7OztlQUdLO0lBQ0csMkJBQTJCLENBQUUsUUFBaUM7UUFDckUsSUFBSSxDQUFDLFFBQVE7WUFBRSxPQUFPLFNBQVMsQ0FBQztRQUVoQyw2Q0FBNkM7UUFDN0MsSUFBSSxFQUFFLENBQUMsaUJBQWlCLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQztZQUNwQyxNQUFNLEtBQUssR0FBYSxFQUFFLENBQUM7WUFDM0IsS0FBSyxNQUFNLE1BQU0sSUFBSSxRQUFRLENBQUMsT0FBTyxFQUFFLENBQUM7Z0JBQ3ZDLElBQUksRUFBRSxDQUFDLG1CQUFtQixDQUFDLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7b0JBQ3BFLE1BQU0sUUFBUSxHQUFHLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO29CQUNsQyxNQUFNLFFBQVEsR0FBRyxNQUFNLENBQUMsYUFBYSxDQUFDLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQztvQkFDakQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7b0JBQ3pDLEtBQUssQ0FBQyxJQUFJLENBQUMsR0FBRyxRQUFRLEdBQUcsUUFBUSxLQUFLLElBQUksRUFBRSxDQUFDLENBQUM7Z0JBQy9DLENBQUM7WUFDRixDQUFDO1lBQ0QsT0FBTyxLQUFLLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztRQUNsQyxDQUFDO1FBRUQsbUVBQW1FO1FBQ25FLHlEQUF5RDtRQUN6RCxJQUFJLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxRQUFRLENBQUMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLFFBQVEsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO1lBQzVFLE1BQU0sUUFBUSxHQUFHLFFBQVEsQ0FBQyxRQUFRLENBQUMsSUFBSSxDQUFDO1lBQ3hDLE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxnQ0FBZ0MsQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLHlCQUF5QixDQUFDLENBQUM7WUFDN0YsSUFBSSxJQUFJLEVBQUUsQ0FBQztnQkFDVixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsK0JBQStCLENBQUMsSUFBSSxDQUFDLENBQUM7Z0JBQzVELElBQUksUUFBUTtvQkFBRSxPQUFPLFFBQVEsQ0FBQztZQUMvQixDQUFDO1lBQ0QsK0RBQStEO1lBQy9ELGdFQUFnRTtZQUNoRSxpRUFBaUU7WUFDakUseURBQXlEO1lBQ3pELE1BQU0sV0FBVyxHQUFHLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxRQUFRLENBQUMsQ0FBQztZQUN4RCxJQUFJLFdBQVcsQ0FBQyxNQUFNLEtBQUssUUFBUSxFQUFFLENBQUM7Z0JBQ3JDLE1BQU0sWUFBWSxHQUFHLFFBQVEsQ0FBQztnQkFDOUIsT0FBTyxZQUFZLENBQUM7WUFDckIsQ0FBQztZQUNELElBQUksV0FBVyxDQUFDLE1BQU0sS0FBSyxXQUFXLEVBQUUsQ0FBQztnQkFDeEMsSUFBSSxDQUFDLHlCQUF5QixDQUFDLFFBQVEsRUFBRSxRQUFRLEVBQUUsV0FBVyxDQUFDLENBQUM7Z0JBQ2hFLE1BQU0sa0JBQWtCLEdBQUcsU0FBUyxDQUFDO2dCQUNyQyxPQUFPLGtCQUFrQixDQUFDO1lBQzNCLENBQUM7WUFDRCw4REFBOEQ7WUFDOUQsSUFBSSxRQUFRLENBQUMsYUFBYSxJQUFJLFFBQVEsQ0FBQyxhQUFhLENBQUMsTUFBTSxHQUFHLENBQUMsRUFBRSxDQUFDO2dCQUNqRSxJQUFJLGtCQUFrQixDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsRUFBRSxDQUFDO29CQUN0QyxNQUFNLElBQUksR0FBRyxRQUFRLENBQUMsYUFBYSxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQztvQkFDcEUsT0FBTyxHQUFHLFFBQVUsSUFBTSxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBRyxHQUFHLENBQUM7Z0JBQ2hELENBQUM7Z0JBQ0QsOERBQThEO2dCQUM5RCx1Q0FBdUM7Z0JBQ3ZDLElBQUksQ0FBQyw0QkFBNEIsQ0FBQyxRQUFRLEVBQUUsUUFBUSxDQUFDLENBQUM7Z0JBQ3RELE1BQU0sb0JBQW9CLEdBQUcsU0FBUyxDQUFDO2dCQUN2QyxPQUFPLG9CQUFvQixDQUFDO1lBQzdCLENBQUM7WUFDRCxNQUFNLGNBQWMsR0FBRyxJQUFJLENBQUMsK0JBQStCLENBQUMsUUFBUSxFQUFFLFFBQVEsQ0FBQyxDQUFDO1lBQ2hGLE9BQU8sY0FBYyxDQUFDO1FBQ3ZCLENBQUM7UUFFRCxPQUFPLFNBQVMsQ0FBQztJQUNsQixDQUFDO0lBRUQ7O2VBRUs7SUFDRyw2QkFBNkIsQ0FBRSxTQUFtRDtRQUV6RixNQUFNLE1BQU0sR0FBMkIsRUFBRSxDQUFDO1FBRTFDLEtBQUssTUFBTSxNQUFNLElBQUksU0FBUyxDQUFDLE9BQU8sRUFBRSxDQUFDO1lBQ3hDLElBQUksQ0FBQyxFQUFFLENBQUMsd0JBQXdCLENBQUMsTUFBTSxDQUFDLEVBQUUsQ0FBQztnQkFDMUMsU0FBUztZQUNWLENBQUM7WUFFRCxLQUFLLE1BQU0sS0FBSyxJQUFJLE1BQU0sQ0FBQyxVQUFVLEVBQUUsQ0FBQztnQkFDdkMsSUFBSSxDQUFDLEtBQUssQ0FBQyxJQUFJLElBQUksQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUM7b0JBQUUsU0FBUztnQkFDMUQsSUFBSSxDQUFDLEtBQUssQ0FBQyxJQUFJO29CQUFFLFNBQVM7Z0JBRTFCLE1BQU0sU0FBUyxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO2dCQUNsQyxNQUFNLFlBQVksR0FBRyxJQUFJLENBQUMsMkJBQTJCLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLElBQUksQ0FBQyxTQUFTLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxDQUFDO2dCQUVoRyxNQUFNLENBQUMsSUFBSSxDQUFDO29CQUNYLElBQUksRUFBTyxTQUFTO29CQUNwQixJQUFJLEVBQU8sWUFBWTtvQkFDdkIsUUFBUSxFQUFHLENBQUMsQ0FBQyxLQUFLLENBQUMsYUFBYSxJQUFJLENBQUMsQ0FBQyxLQUFLLENBQUMsV0FBVztpQkFDdkQsQ0FBQyxDQUFDO1lBQ0osQ0FBQztZQUNELGlDQUFpQztZQUNqQyxNQUFNO1FBQ1AsQ0FBQztRQUVELE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7O2VBSUs7SUFDRyx3QkFBd0IsQ0FBRSxJQUF1QjtRQUN4RCxNQUFNLGVBQWUsR0FBRyxJQUFJLENBQUMsNEJBQTRCLENBQUMsSUFBSSxDQUFDLENBQUM7UUFDaEUsSUFBSSxDQUFDLGVBQWUsRUFBRSxDQUFDO1lBQ3RCLE9BQU8sRUFBRSxDQUFDO1FBQ1gsQ0FBQztRQUNELE1BQU0sTUFBTSxHQUFHLElBQUksQ0FBQyx1Q0FBdUMsQ0FBQyxlQUFlLENBQUMsQ0FBQztRQUM3RSxPQUFPLE1BQU0sQ0FBQztJQUNmLENBQUM7SUFFRDs7ZUFFSztJQUNHLHVDQUF1QyxDQUFFLGVBQThCO1FBQzlFLE1BQU0sTUFBTSxHQUEyQixFQUFFLENBQUM7UUFFMUMsK0NBQStDO1FBQy9DLElBQUksRUFBRSxDQUFDLG9CQUFvQixDQUFDLGVBQWUsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsZUFBZSxDQUFDLEVBQUUsQ0FBQztZQUNyRiw4REFBOEQ7WUFDOUQsa0ZBQWtGO1lBQ2xGLEtBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxlQUFlLENBQUMsVUFBVSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRSxDQUFDO2dCQUM1RCxNQUFNLEtBQUssR0FBRyxlQUFlLENBQUMsVUFBVSxDQUFFLENBQUMsQ0FBRSxDQUFDO2dCQUM5QyxJQUFJLENBQUMsS0FBSyxDQUFDLElBQUk7b0JBQUUsU0FBUztnQkFFMUIsc0NBQXNDO2dCQUN0QyxJQUNDLENBQUMsS0FBSyxDQUFDO29CQUNQLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLEVBQUUsQ0FBQyxVQUFVLENBQUMsVUFBVTtvQkFDM0MsS0FBSyxDQUFDLElBQXNCLENBQUMsSUFBSSxLQUFLLE1BQU0sRUFDNUMsQ0FBQztvQkFDRixTQUFTO2dCQUNWLENBQUM7Z0JBRUQseUNBQXlDO2dCQUN6QyxNQUFNLFNBQVMsR0FBRyxFQUFFLENBQUMsWUFBWSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEtBQUssQ0FBQztnQkFDeEUsTUFBTSxZQUFZLEdBQUcsSUFBSSxDQUFDLDJCQUEyQixDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsU0FBUyxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFFaEcsTUFBTSxDQUFDLElBQUksQ0FBQztvQkFDWCxJQUFJLEVBQU8sU0FBUztvQkFDcEIsSUFBSSxFQUFPLFlBQVk7b0JBQ3ZCLFFBQVEsRUFBRyxDQUFDLENBQUMsS0FBSyxDQUFDLGFBQWEsSUFBSSxDQUFDLENBQUMsS0FBSyxDQUFDLFdBQVc7aUJBQ3ZELENBQUMsQ0FBQztZQUNKLENBQUM7UUFDRixDQUFDO1FBRUQscURBQXFEO1FBQ3JELElBQUksRUFBRSxDQUFDLGlCQUFpQixDQUFDLGVBQWUsQ0FBQyxFQUFFLENBQUM7WUFDM0MsTUFBTSxXQUFXLEdBQUcsSUFBSSxDQUFDLDZCQUE2QixDQUFDLGVBQWUsQ0FBQyxDQUFDO1lBQ3hFLEtBQUssTUFBTSxLQUFLLElBQUksV0FBVyxFQUFFLENBQUM7Z0JBQ2pDLE1BQU0sQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7WUFDcEIsQ0FBQztRQUNGLENBQUM7UUFFRCxPQUFPLE1BQU0sQ0FBQztJQUNmLENBQUM7SUFFRDs7Ozs7O09BTUc7SUFDSyxzQkFBc0IsQ0FBRSxJQUFhLEVBQUUsVUFBeUI7UUFDdkUsSUFBSSxFQUFFLENBQUMsa0JBQWtCLENBQUMsSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQzlDLElBQUksQ0FBQywyQkFBMkIsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFDcEQsQ0FBQztRQUNELElBQUksRUFBRSxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDO1lBQzFCLElBQUksQ0FBQywrQkFBK0IsQ0FBQyxJQUFJLEVBQUUsVUFBVSxDQUFDLENBQUM7UUFDeEQsQ0FBQztRQUNELElBQUksRUFBRSxDQUFDLHlCQUF5QixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDeEMsSUFBSSxDQUFDLDhCQUE4QixDQUFDLElBQUksRUFBRSxVQUFVLENBQUMsQ0FBQztRQUN2RCxDQUFDO1FBQ0QsSUFBSSxFQUFFLENBQUMsZ0JBQWdCLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQztZQUMvQixJQUFJLENBQUMsZ0NBQWdDLENBQUMsSUFBSSxFQUFFLFVBQVUsQ0FBQyxDQUFDO1FBQ3pELENBQUM7SUFDRixDQUFDO0lBRUQ7OztPQUdHO0lBQ0ssMkJBQTJCLENBQUUsSUFBeUIsRUFBRSxVQUF5QjtRQUN4RixJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ2hCLE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7UUFDakMsTUFBTSxFQUFFLElBQUksRUFBRSxTQUFTLEVBQUUsR0FBRyxFQUFFLENBQUMsNkJBQTZCLENBQzNELFVBQVUsRUFDVixJQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDOUIsQ0FBQztRQUNGLE1BQU0sUUFBUSxHQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FBQztRQUN2RSwwREFBMEQ7UUFDMUQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLENBQUUsQ0FBQyxDQUFFLENBQUMsS0FBSyxDQUFDLENBQUMsRUFBRSxHQUFHLENBQUMsQ0FBQztRQUVyRSxJQUFJLElBQXFDLENBQUM7UUFDMUMsSUFBSSxJQUFJLENBQUMsZUFBZSxFQUFFLENBQUM7WUFDMUIsS0FBSyxNQUFNLE1BQU0sSUFBSSxJQUFJLENBQUMsZUFBZSxFQUFFLENBQUM7Z0JBQzNDLElBQUksTUFBTSxDQUFDLEtBQUssS0FBSyxFQUFFLENBQUMsVUFBVSxDQUFDLGlCQUFpQixFQUFFLENBQUM7b0JBQ3RELFNBQVM7Z0JBQ1YsQ0FBQztnQkFDRCxLQUFLLE1BQU0sSUFBSSxJQUFJLE1BQU0sQ0FBQyxLQUFLLEVBQUUsQ0FBQztvQkFDakMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7d0JBQ3ZDLFNBQVM7b0JBQ1YsQ0FBQztvQkFDRCxNQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMseUJBQXlCLENBQUMsVUFBVSxDQUFFLElBQUksQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFFLENBQUM7b0JBQ2xGLElBQUksT0FBTyxFQUFFLENBQUM7d0JBQ2IsSUFBSSxHQUFHLE9BQU8sQ0FBQztvQkFDaEIsQ0FBQztnQkFDRixDQUFDO1lBQ0YsQ0FBQztRQUNGLENBQUM7UUFFRCxNQUFNLElBQUksR0FBNkI7WUFDdEMsUUFBUTtZQUNSLElBQUk7U0FDSixDQUFDO1FBQ0YsSUFBSSxJQUFJLEVBQUUsQ0FBQztZQUNWLElBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO1FBQ2xCLENBQUM7UUFDRCxJQUFJLENBQUMseUJBQXlCLENBQUMsR0FBRyxDQUFDLFNBQVMsRUFBRSxJQUFJLENBQUMsQ0FBQztJQUNyRCxDQUFDO0lBRUQ7Ozs7T0FJRztJQUNLLCtCQUErQixDQUFFLElBQWtCLEVBQUUsVUFBeUI7UUFDckYsTUFBTSxFQUFFLFVBQVUsRUFBRSxHQUFHLElBQUksQ0FBQztRQUM1QixJQUFJLENBQUMsRUFBRSxDQUFDLGdCQUFnQixDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxVQUFVLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztZQUNqRixPQUFPO1FBQ1IsQ0FBQztRQUNELE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyx5QkFBeUIsQ0FBQyxhQUFhLENBQUUsVUFBVSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUUsQ0FBQztRQUN4RixJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDWCxPQUFPO1FBQ1IsQ0FBQztRQUVELG9FQUFvRTtRQUNwRSxzREFBc0Q7UUFDdEQsa0RBQWtEO1FBQ2xELE1BQU0sU0FBUyxHQUFHLElBQUksQ0FBQyxNQUFNLENBQUM7UUFDOUIsSUFBSSxLQUEyQixDQUFDO1FBQ2hDLElBQUksT0FBaUIsQ0FBQztRQUN0QixJQUFJLEVBQUUsQ0FBQyxrQkFBa0IsQ0FBQyxTQUFTLENBQUMsSUFBSSxTQUFTLENBQUMsSUFBSSxFQUFFLENBQUM7WUFDeEQsS0FBSyxHQUFHLGNBQWMsU0FBUyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQztZQUM1QyxPQUFPLEdBQUcsQ0FBRSxTQUFTLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBRSxDQUFDO1FBQ25DLENBQUM7YUFBTSxJQUNOLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxTQUFTLENBQUM7WUFDakMsRUFBRSxDQUFDLFlBQVksQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDO1lBQy9CLEVBQUUsQ0FBQyxrQkFBa0IsQ0FBQyxTQUFTLENBQUMsTUFBTSxDQUFDO1lBQ3ZDLFNBQVMsQ0FBQyxNQUFNLENBQUMsSUFBSSxFQUNwQixDQUFDO1lBQ0YsTUFBTSxTQUFTLEdBQUcsU0FBUyxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO1lBQzdDLEtBQUssR0FBRyxVQUFVLFNBQVMsSUFBSSxTQUFTLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO1lBQ3JELE9BQU8sR0FBRyxDQUFFLFNBQVMsQ0FBRSxDQUFDO1FBQ3pCLENBQUM7YUFBTSxJQUFJLEVBQUUsQ0FBQyxXQUFXLENBQUMsU0FBUyxDQUFDLEVBQUUsQ0FBQztZQUN0QywrREFBK0Q7WUFDL0QsOERBQThEO1lBQzlELGlFQUFpRTtZQUNqRSxpRUFBaUU7WUFDakUsMERBQTBEO1lBQzFELE1BQU0sSUFBSSxHQUFHLFNBQVMsQ0FBQyxNQUFNLENBQUM7WUFDOUIsSUFDQyxJQUFJO2dCQUNKLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUM7Z0JBQzVCLEVBQUUsQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQztnQkFDMUIsRUFBRSxDQUFDLGtCQUFrQixDQUFDLElBQUksQ0FBQyxNQUFNLENBQUM7Z0JBQ2xDLElBQUksQ0FBQyxNQUFNLENBQUMsSUFBSSxFQUNmLENBQUM7Z0JBQ0YsTUFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO2dCQUN4QyxLQUFLLEdBQUcsVUFBVSxTQUFTLElBQUksSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQztnQkFDaEQsT0FBTyxHQUFHLENBQUUsU0FBUyxDQUFFLENBQUM7WUFDekIsQ0FBQztpQkFBTSxDQUFDO2dCQUNQLE9BQU87WUFDUixDQUFDO1FBQ0YsQ0FBQzthQUFNLENBQUM7WUFDUCxPQUFPO1FBQ1IsQ0FBQztRQUVELE1BQU0sRUFBRSxJQUFJLEVBQUUsU0FBUyxFQUFFLEdBQUcsRUFBRSxDQUFDLDZCQUE2QixDQUMzRCxVQUFVLEVBQ1YsSUFBSSxDQUFDLFFBQVEsQ0FBQyxVQUFVLENBQUMsQ0FDekIsQ0FBQztRQUNGLE1BQU0sUUFBUSxHQUFHLEdBQUcsVUFBVSxDQUFDLFFBQVEsSUFBSSxJQUFJLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUUsQ0FBQztRQUN2RSxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsR0FBRyxDQUFDLENBQUM7UUFFcEQsS0FBSyxNQUFNLEdBQUcsSUFBSSxVQUFVLENBQUMsU0FBUyxFQUFFLENBQUM7WUFDeEMsMERBQTBEO1lBQzFELHNDQUFzQztZQUN0QyxJQUFJLFNBQTZCLENBQUM7WUFDbEMsNkRBQTZEO1lBQzdELDhDQUE4QztZQUM5QyxJQUFJLE9BQU8sR0FBRyxJQUFJLENBQUM7WUFDbkIsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQzFCLFNBQVMsR0FBRyxHQUFHLENBQUMsSUFBSSxDQUFDO1lBQ3RCLENBQUM7aUJBQU0sSUFBSSxFQUFFLENBQUMsZUFBZSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxZQUFZLENBQUMsR0FBRyxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUM7Z0JBQ3ZFLFNBQVMsR0FBRyxHQUFHLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQztZQUNqQyxDQUFDO2lCQUFNLElBQUksRUFBRSxDQUFDLGdCQUFnQixDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsQ0FBQywwQkFBMEIsQ0FBQyxHQUFHLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQztnQkFDdEYsd0RBQXdEO2dCQUN4RCw2REFBNkQ7Z0JBQzdELGtEQUFrRDtnQkFDbEQsTUFBTSxPQUFPLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLHFCQUFxQixDQUFFLEdBQUcsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBRSxDQUFDO2dCQUNqRyxJQUFJLE9BQU8sRUFBRSxDQUFDO29CQUNiLE1BQU0sU0FBUyxHQUFHLEdBQUcsQ0FBQyxTQUFTLENBQUUsT0FBTyxDQUFDLFNBQVMsSUFBSSxDQUFDLENBQUUsQ0FBQztvQkFDMUQsSUFBSSxTQUFTLElBQUksRUFBRSxDQUFDLFlBQVksQ0FBQyxTQUFTLENBQUMsRUFBRSxDQUFDO3dCQUM3QyxTQUFTLEdBQUcsU0FBUyxDQUFDLElBQUksQ0FBQzt3QkFDM0IsT0FBTyxHQUFHLE9BQU8sQ0FBQyxJQUFJLENBQUM7b0JBQ3hCLENBQUM7Z0JBQ0YsQ0FBQztZQUNGLENBQUM7WUFDRCxJQUFJLENBQUMsU0FBUyxFQUFFLENBQUM7Z0JBQ2hCLFNBQVM7WUFDVixDQUFDO1lBQ0QsSUFBSSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQztnQkFDOUIsSUFBSSxFQUFHLE9BQU87Z0JBQ2QsU0FBUztnQkFDVCxRQUFRO2dCQUNSLElBQUk7Z0JBQ0osS0FBSztnQkFDTCxPQUFPO2FBQ1AsQ0FBQyxDQUFDO1FBQ0osQ0FBQztJQUNGLENBQUM7SUFFRDs7Ozs7T0FLRztJQUNLLDhCQUE4QixDQUFFLElBQWdDLEVBQUUsVUFBeUI7UUFDbEcsSUFBSSxJQUFxQyxDQUFDO1FBQzFDLElBQUksWUFBZ0MsQ0FBQztRQUVyQyxLQUFLLE1BQU0sSUFBSSxJQUFJLElBQUksQ0FBQyxVQUFVLEVBQUUsQ0FBQztZQUNwQyxJQUNDLENBQUMsRUFBRSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQztnQkFDOUIsQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7Z0JBQzNCLENBQUMsRUFBRSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsV0FBVyxDQUFDLEVBQ2pDLENBQUM7Z0JBQ0YsU0FBUztZQUNWLENBQUM7WUFDRCxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLFNBQVMsRUFBRSxDQUFDO2dCQUNsQyxJQUFJLEdBQUcsSUFBSSxDQUFDLHlCQUF5QixDQUFDLFNBQVMsQ0FBRSxJQUFJLENBQUMsV0FBVyxDQUFDLElBQUksQ0FBRSxDQUFDO1lBQzFFLENBQUM7WUFDRCxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLFVBQVUsRUFBRSxDQUFDO2dCQUNuQyxZQUFZLEdBQUcsSUFBSSxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUM7WUFDdEMsQ0FBQztRQUNGLENBQUM7UUFFRCxJQUFJLENBQUMsSUFBSSxJQUFJLENBQUMsWUFBWSxFQUFFLENBQUM7WUFDNUIsT0FBTztRQUNSLENBQUM7UUFFRCxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLElBQUksQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQ3pCLENBQUM7UUFDRixNQUFNLFFBQVEsR0FBRyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7UUFDdkUsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxDQUFDO1FBRXBELElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxJQUFJLENBQUM7WUFDOUIsSUFBSTtZQUNKLFNBQVMsRUFBRyxZQUFZO1lBQ3hCLFFBQVE7WUFDUixJQUFJO1lBQ0osS0FBSyxFQUFPLFFBQVE7WUFDcEIsT0FBTyxFQUFLLEVBQUU7U0FDZCxDQUFDLENBQUM7SUFDSixDQUFDO0lBRUQ7Ozs7OztPQU1HO0lBQ0ssZ0NBQWdDLENBQUUsSUFBdUIsRUFBRSxVQUF5QjtRQUMzRixJQUFJLENBQUMsSUFBSSxDQUFDLHlCQUF5QixDQUFDLGdCQUFnQixFQUFFLENBQUM7WUFDdEQsT0FBTztRQUNSLENBQUM7UUFDRCxJQUNDLENBQUMsRUFBRSxDQUFDLDBCQUEwQixDQUFDLElBQUksQ0FBQyxVQUFVLENBQUM7WUFDL0MsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLFdBQVcsRUFDeEMsQ0FBQztZQUNGLE9BQU87UUFDUixDQUFDO1FBQ0QsTUFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQyxVQUFVLENBQUM7UUFDN0MsSUFDQyxDQUFDLEVBQUUsQ0FBQyxnQkFBZ0IsQ0FBQyxTQUFTLENBQUM7WUFDL0IsQ0FBQyxFQUFFLENBQUMsMEJBQTBCLENBQUMsU0FBUyxDQUFDLFVBQVUsQ0FBQztZQUNwRCxTQUFTLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssT0FBTyxFQUN6QyxDQUFDO1lBQ0YsT0FBTztRQUNSLENBQUM7UUFDRCxJQUFJLENBQUMsSUFBSSxDQUFDLHVCQUF1QixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7WUFDekMsT0FBTztRQUNSLENBQUM7UUFFRCxNQUFNLE9BQU8sR0FBYSxFQUFFLENBQUM7UUFDN0IsS0FBSyxNQUFNLEdBQUcsSUFBSSxJQUFJLENBQUMsU0FBUyxFQUFFLENBQUM7WUFDbEMsSUFBSSxFQUFFLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxlQUFlLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztnQkFDckQsT0FBTyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7WUFDeEIsQ0FBQztRQUNGLENBQUM7UUFFRCxNQUFNLEVBQUUsSUFBSSxFQUFFLFNBQVMsRUFBRSxHQUFHLEVBQUUsQ0FBQyw2QkFBNkIsQ0FDM0QsVUFBVSxFQUNWLFNBQVMsQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLENBQzlCLENBQUM7UUFDRixNQUFNLFFBQVEsR0FBRyxHQUFHLFVBQVUsQ0FBQyxRQUFRLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxFQUFFLENBQUM7UUFDdkUsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxDQUFDO1FBRXBELEtBQUssTUFBTSxHQUFHLElBQUksU0FBUyxDQUFDLFNBQVMsRUFBRSxDQUFDO1lBQ3ZDLElBQUksQ0FBQyxFQUFFLENBQUMsWUFBWSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUM7Z0JBQzNCLFNBQVM7WUFDVixDQUFDO1lBQ0QsSUFBSSxDQUFDLG9CQUFvQixDQUFDLElBQUksQ0FBQztnQkFDOUIsSUFBSSxFQUFRLFlBQVk7Z0JBQ3hCLFNBQVMsRUFBRyxHQUFHLENBQUMsSUFBSTtnQkFDcEIsUUFBUTtnQkFDUixJQUFJO2dCQUNKLEtBQUssRUFBTyxRQUFRO2dCQUNwQixPQUFPO2FBQ1AsQ0FBQyxDQUFDO1FBQ0osQ0FBQztJQUNGLENBQUM7SUFFRDs7T0FFRztJQUNLLHVCQUF1QixDQUFFLElBQWE7UUFDN0MsSUFBSSxPQUFPLEdBQXdCLElBQUksQ0FBQyxNQUFNLENBQUM7UUFDL0MsT0FBTyxPQUFPLEVBQUUsQ0FBQztZQUNoQixJQUNDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxPQUFPLENBQUM7Z0JBQy9CLEVBQUUsQ0FBQyxZQUFZLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQztnQkFDN0IsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssV0FBVyxFQUNoQyxDQUFDO2dCQUNGLE9BQU8sSUFBSSxDQUFDO1lBQ2IsQ0FBQztZQUNELE9BQU8sR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDO1FBQzFCLENBQUM7UUFDRCxPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7Q0FDRDtBQTNnTUQsOENBMmdNQyIsInNvdXJjZXNDb250ZW50IjpbIid1c2Ugc3RyaWN0JztcblxuaW1wb3J0ICogYXMgbm9kZVBhdGggZnJvbSAncGF0aCc7XG5pbXBvcnQgKiBhcyB0cyBmcm9tICd0eXBlc2NyaXB0JztcbmltcG9ydCB7XG5cdFR5cGVOb2RlLCBQcm9wZXJ0eUluZm8sIEFuYWx5emVSZXN1bHQsIEFuYWx5emVFcnJvcixcblx0RGVmaW5pdGlvbkluZm8sIFVzYWdlSW5mbywgQ29uc3RydWN0b3JQYXJhbUluZm8sXG5cdEVEU0luZm8sIEZsb3dJbmZvLCBJbnN0cnVtZW50YXRpb25LaW5kLCBJbnN0cnVtZW50YXRpb25Qb2ludCxcblx0SW5zdHJ1bWVudGF0aW9uU2NvcGUsIFJlc29sdXRpb25FcnJvclxufSBmcm9tICcuL3R5cGVzJztcbmltcG9ydCB7XG5cdFR5cGVHcmFwaEltcGwsIHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UsIEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCBcbn0gZnJvbSAnLi9ncmFwaCc7XG5pbXBvcnQge1xuXHRJbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5LCBUYWN0aWNhUGx1Z2luLCBtZXJnZVRhY3RpY2FQbHVnaW5zXG59IGZyb20gJy4vcGx1Z2lucyc7XG5cbmludGVyZmFjZSBDb2xsZWN0aW9uSW5mbyB7XG5cdHZhcmlhYmxlTmFtZTogc3RyaW5nO1xuXHRzb3VyY2VGaWxlOiBzdHJpbmc7XG5cdHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZT86IHN0cmluZztcbn1cblxuLyoqXG4gKiBMb2NhdGlvbi9jb2RlIGNhcHR1cmVkIGF0IGEgY2xhc3MgZGVjbGFyYXRpb24sIHVzZWQgdG8gcmVzb2x2ZVxuICogaW5zdHJ1bWVudGF0aW9uIHJlZ2lzdHJhdGlvbiBzaXRlcyB0byB0aGUgZGVjbGFyZWQgY2xhc3NcbiAqL1xuaW50ZXJmYWNlIEluc3RydW1lbnRhdGlvbkNsYXNzRGVjbCB7XG5cdGtpbmQ/OiBJbnN0cnVtZW50YXRpb25LaW5kO1xuXHRsb2NhdGlvbjogc3RyaW5nO1xuXHRjb2RlOiBzdHJpbmc7XG59XG5cbi8qKlxuICogUmF3IHJlZ2lzdHJhdGlvbiBzaXRlIChkZWNvcmF0b3IsIEFQUF8qIHByb3ZpZGVyLCBjb25zdW1lci5hcHBseSkuXG4gKiBMb2NhdGlvbi9jb2RlIGFyZSB0aGUgc2l0ZSdzIG93bjsgZ2V0SW5zdHJ1bWVudGF0aW9uUG9pbnRzKCkgcmV3cml0ZXNcbiAqIHRoZW0gdG8gdGhlIGNsYXNzIGRlY2xhcmF0aW9uIHdoZW4gdGhlIGNsYXNzIGlzIGRlY2xhcmVkIGluLXByb2plY3QuXG4gKi9cbmludGVyZmFjZSBJbnN0cnVtZW50YXRpb25TaXRlIHtcblx0a2luZDogSW5zdHJ1bWVudGF0aW9uS2luZDtcblx0Y2xhc3NOYW1lOiBzdHJpbmc7XG5cdGxvY2F0aW9uOiBzdHJpbmc7XG5cdGNvZGU6IHN0cmluZztcblx0c2NvcGU6IEluc3RydW1lbnRhdGlvblNjb3BlO1xuXHR0YXJnZXRzOiBzdHJpbmdbXTtcbn1cblxuLyoqXG4gKiBBIG5hbWVkIHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbiAodHlwZSBhbGlhcywgY2xhc3MsIG9yIGludGVyZmFjZSlcbiAqIHJlY29yZGVkIHBlciBmaWxlLCBzbyByZWZlcmVuY2VzIGNhbiBiZSByZXNvbHZlZCB0aHJvdWdoIHRoZSBpbXBvcnRpbmdcbiAqIGZpbGUncyBvd24gaW1wb3J0cyBpbnN0ZWFkIG9mIGEgcHJvZ3JhbS13aWRlIGxhc3Qtd2lucyBuYW1lIG1hcCAoRjEwKS5cbiAqL1xuaW50ZXJmYWNlIFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24ge1xuXHRraW5kOiAnYWxpYXMnIHwgJ2NsYXNzJyB8ICdpbnRlcmZhY2UnO1xuXHRub2RlOiB0cy5UeXBlQWxpYXNEZWNsYXJhdGlvbiB8IHRzLkNsYXNzRGVjbGFyYXRpb24gfCB0cy5JbnRlcmZhY2VEZWNsYXJhdGlvbjtcblx0LyoqIGZpbGUgdGhhdCBkZWNsYXJlcyB0aGUgdHlwZSDigJQgbmVzdGVkIHJlZmVyZW5jZXMgcmVzb2x2ZSBhZ2FpbnN0IGl0ICovXG5cdGZpbGU6IHN0cmluZztcbn1cblxuLyoqXG4gKiBPbmUgaW1wb3J0IGJpbmRpbmcgb2YgYSByZWZlcmVuY2VkIHR5cGU6IHRoZSBsb2NhbCBuYW1lIHVuZGVyIHdoaWNoIHRoZVxuICogZmlsZSBrbm93cyBpdCwgdGhlIG9yaWdpbmFsIGV4cG9ydGVkIG5hbWUgaW4gdGhlIHNvdXJjZSBtb2R1bGUsIGFuZCB0aGVcbiAqIHNwZWNpZmllciBpdCBjYW1lIGZyb20uXG4gKi9cbmludGVyZmFjZSBSZWZlcmVuY2VkVHlwZUltcG9ydCB7XG5cdG9yaWdpbmFsTmFtZTogc3RyaW5nO1xuXHRzcGVjaWZpZXI6IHN0cmluZztcblx0aXNOYW1lc3BhY2U6IGJvb2xlYW47XG59XG5cbi8qKlxuICogUmVzdWx0IG9mIHJlc29sdmluZyBvbmUgbW9kdWxlIHNwZWNpZmllciBmcm9tIG9uZSBjb250YWluaW5nIGZpbGUuXG4gKi9cbmludGVyZmFjZSBSZWZlcmVuY2VkVHlwZVJlc29sdXRpb24ge1xuXHRyZXNvbHZlZFBhdGg6IHN0cmluZztcblx0aXNFeHRlcm5hbDogYm9vbGVhbjtcbn1cblxuLyoqXG4gKiBHbG9iYWwvYnVpbHRpbiB0eXBlIG5hbWVzIHRoYXQgYXJlIHNhZmUgdG8gZW1pdCBiYXJlIGludG8gZ2VuZXJhdGVkIGZpbGVzXG4gKiDigJQgdGhleSByZXNvbHZlIGluIGFueSBUeXBlU2NyaXB0IGNvbXBpbGF0aW9uIHdpdGhvdXQgYW4gaW1wb3J0LlxuICovXG5jb25zdCBLTk9XTl9HTE9CQUxfVFlQRVMgPSBuZXcgU2V0KFtcblx0J0RhdGUnLCAnUmVnRXhwJywgJ0Vycm9yJywgJ0V2YWxFcnJvcicsICdSYW5nZUVycm9yJywgJ1JlZmVyZW5jZUVycm9yJyxcblx0J1N5bnRheEVycm9yJywgJ1R5cGVFcnJvcicsICdVUklFcnJvcicsICdBZ2dyZWdhdGVFcnJvcicsXG5cdCdNYXAnLCAnU2V0JywgJ1dlYWtNYXAnLCAnV2Vha1NldCcsICdXZWFrUmVmJywgJ0ZpbmFsaXphdGlvblJlZ2lzdHJ5Jyxcblx0J1Byb21pc2UnLCAnQXJyYXknLCAnUmVhZG9ubHlBcnJheScsICdSZWNvcmQnLCAnUGFydGlhbCcsICdSZXF1aXJlZCcsXG5cdCdSZWFkb25seScsICdQaWNrJywgJ09taXQnLCAnRXhjbHVkZScsICdFeHRyYWN0JywgJ05vbk51bGxhYmxlJyxcblx0J1JldHVyblR5cGUnLCAnSW5zdGFuY2VUeXBlJywgJ1BhcmFtZXRlcnMnLCAnQ29uc3RydWN0b3JQYXJhbWV0ZXJzJyxcblx0J1RoaXNUeXBlJywgJ1RoaXNQYXJhbWV0ZXJUeXBlJywgJ09taXRUaGlzUGFyYW1ldGVyJyxcblx0J1VwcGVyY2FzZScsICdMb3dlcmNhc2UnLCAnQ2FwaXRhbGl6ZScsICdVbmNhcGl0YWxpemUnLFxuXHQnU3RyaW5nJywgJ051bWJlcicsICdCb29sZWFuJywgJ1N5bWJvbCcsICdCaWdJbnQnLCAnT2JqZWN0JywgJ0Z1bmN0aW9uJyxcblx0J0l0ZXJhYmxlJywgJ0l0ZXJhdG9yJywgJ0dlbmVyYXRvcicsICdBc3luY0l0ZXJhYmxlJywgJ0FzeW5jSXRlcmF0b3InLFxuXHQnQXN5bmNHZW5lcmF0b3InLCAnSXRlcmFibGVJdGVyYXRvcicsICdBc3luY0l0ZXJhYmxlSXRlcmF0b3InLFxuXHQnUHJvcGVydHlLZXknLCAnQXJyYXlCdWZmZXInLCAnU2hhcmVkQXJyYXlCdWZmZXInLCAnRGF0YVZpZXcnLFxuXHQnSW50OEFycmF5JywgJ1VpbnQ4QXJyYXknLCAnVWludDhDbGFtcGVkQXJyYXknLCAnSW50MTZBcnJheScsXG5cdCdVaW50MTZBcnJheScsICdJbnQzMkFycmF5JywgJ1VpbnQzMkFycmF5JywgJ0Zsb2F0MzJBcnJheScsXG5cdCdGbG9hdDY0QXJyYXknLCAnQmlnSW50NjRBcnJheScsICdCaWdVaW50NjRBcnJheScsICdJbnRsJ1xuXSk7XG5cbi8vIEJvdW5kIGZvciBjaGFzaW5nIHJlLWV4cG9ydCBiYXJyZWxzIChleHBvcnQgeyBYIH0gZnJvbSAn4oCmJywgZXhwb3J0ICogZnJvbSAn4oCmJylcbmNvbnN0IE1BWF9SRUVYUE9SVF9DSEFTRV9ERVBUSCA9IDU7XG4vLyBCb3VuZCBmb3Igd2Fsa2luZyBjbGFzcy9pbnRlcmZhY2UgZXh0ZW5kcyBjaGFpbnMgZHVyaW5nIHJlZmVyZW5jZWQtdHlwZVxuLy8gZXhwYW5zaW9uIChpbmhlcml0ZWQgbWVtYmVycyBtZXJnZSBpbnRvIHRoZSBleHBhbmRlZCBmaWVsZHMpXG5jb25zdCBNQVhfSEVSSVRBR0VfREVQVEggPSA4O1xuXG4vKipcbiAqIEFTVCBBbmFseXplciBmb3IgZmluZGluZyBNbmVtb25pY2EgZGVmaW5lKCkgYW5kIGRlY29yYXRlKCkgY2FsbHNcbiAqXG4gKiBGcmFtZXdvcmstYmxpbmQgYnkgY29uc3RydWN0aW9uOiBpbnN0cnVtZW50YXRpb24gZGV0ZWN0aW9uIHZvY2FidWxhcnlcbiAqIChpbnRlcmZhY2UgbmFtZXMsIGRlY29yYXRvciBuYW1lcywgcHJvdmlkZXIgdG9rZW5zLCBtaWRkbGV3YXJlIHdpcmluZylcbiAqIGNvbWVzIGVudGlyZWx5IGZyb20gcGx1Z2lucyDigJQgd2l0aCBub25lIGxvYWRlZCwgemVybyBwb2ludHMgYXJlIGNvbGxlY3RlZC5cbiAqL1xuZXhwb3J0IGNsYXNzIE1uZW1vbmljYUFuYWx5emVyIHtcblx0cHJpdmF0ZSBlcnJvcnM6IEFuYWx5emVFcnJvcltdID0gW107XG5cdHByaXZhdGUgZ3JhcGggPSBuZXcgVHlwZUdyYXBoSW1wbCgpO1xuXHRwcml2YXRlIGRlZmluaXRpb25zID0gbmV3IE1hcDxzdHJpbmcsIERlZmluaXRpb25JbmZvPigpO1xuXHRwcml2YXRlIHVzYWdlcyA9IG5ldyBNYXA8c3RyaW5nLCBVc2FnZUluZm9bXT4oKTtcblx0cHJpdmF0ZSBlZHNVc2FnZXMgPSBuZXcgTWFwPHN0cmluZywgRURTSW5mb1tdPigpO1xuXHRwcml2YXRlIGZsb3dVc2FnZXMgPSBuZXcgTWFwPHN0cmluZywgRmxvd0luZm9bXT4oKTtcblx0Ly8gRW5jbG9zaW5nIG1uZW1vbmljYSBzY29wZSBmb3IgRURTIGtleWluZzogZGVmaW5lKCkvbGF6eSgpIGNhbGwgbm9kZVxuXHQvLyBvciBAZGVjb3JhdGUoKS1lZCBjbGFzcyBkZWNsYXJhdGlvbiAtPiBmdWxsUGF0aCBvZiB0aGUgdHlwZSBpdCBvd25zLlxuXHQvLyBQb3B1bGF0ZWQgb24gdGhlIGRlZmluaXRpb25zIHBhc3M7IEFTVCBub2RlcyBwZXJzaXN0IGFjcm9zcyBwYXNzZXMsXG5cdC8vIHNvIGVudHJpZXMgc3RheSB2YWxpZCBhZnRlciByZXNldFVzYWdlcygpLlxuXHRwcml2YXRlIGVkc1Njb3BlQnlOb2RlID0gbmV3IE1hcDx0cy5Ob2RlLCBzdHJpbmc+KCk7XG5cdC8vIFNhbWUtZmlsZSBmdW5jdGlvbiBiaW5kaW5ncyAoYGZpbGVOYW1lI25hbWVgIC0+IGZ1bmN0aW9uIG5vZGUpIGZvclxuXHQvLyByZXNvbHZpbmcgd3JhcChmbikgYXJndW1lbnRzIHN5bnRhY3RpY2FsbHkg4oCUIHRoZSBjaGVja2VyIHN0YXlzIHVudXNlZFxuXHRwcml2YXRlIGZ1bmN0aW9uQmluZGluZ3MgPSBuZXcgTWFwPHN0cmluZywgdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb24+KCk7XG5cdC8vIHdyYXAgY2FsbCBub2RlIC0+IGxvY2F0aW9uIG9mIHRoZSBlbmNsb3Npbmcgd3JhcCBzaXRlIChwbHVzIHRoYXRcblx0Ly8gc2l0ZSdzIHNjb3BlIGF0dHJpYnV0aW9uKSwgc28gbmVzdGVkIHdyYXAoKSBjYWxscyBpbnNpZGUgYSB3cmFwcGVkXG5cdC8vIGJvZHkgY2FycnkgdGhlIGB2aWFgIGxpbmsg4oCUIGFuZCBpbmhlcml0IHRoZSBzY29wZSB3aGVuIHRoZXkgaGF2ZVxuXHQvLyBub25lIG9mIHRoZWlyIG93blxuXHRwcml2YXRlIG5lc3RlZFdyYXBWaWEgPSBuZXcgTWFwPHRzLk5vZGUsIHsgdmlhOiBzdHJpbmc7IHNjb3BlPzogc3RyaW5nIH0+KCk7XG5cdC8vIHdyYXAgY2FsbCBub2RlIC0+IGl0cyBjb2xsZWN0ZWQgZW50cnksIHNvIGEgbGV4aWNhbGx5IG5lc3RlZCB3cmFwXG5cdC8vICh2aXNpdGVkIEJFRk9SRSB0aGUgb3V0ZXIgd3JhcCBjYWxsLCBwZXIgc291cmNlIG9yZGVyKSBnZXRzIGl0c1xuXHQvLyBgdmlhYCBiYWNrLXBhdGNoZWQgd2hlbiB0aGUgb3V0ZXIgYm9keSBpcyBhbmFseXNlZFxuXHRwcml2YXRlIHdyYXBFbnRyeUJ5Tm9kZSA9IG5ldyBNYXA8dHMuTm9kZSwgRURTSW5mbz4oKTtcblx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHM6IHZhcmlhYmxlTmFtZSAtPiBmdWxsUGF0aCBvZiB0aGUgdHlwZSBpdCBob2xkc1xuXHRwcml2YXRlIHZhcmlhYmxlVG9UeXBlTWFwID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0Ly8gVHJhY2sgbW5lbW9uaWNhIG1vZHVsZS1vYmplY3QgdmFyaWFibGVzIChlLmcuLCBpbXBvcnQgeyBtbmVtb25pY2EgfSBmcm9tICdtbmVtb25pY2EnOyBjb25zdCBtID0gbW5lbW9uaWNhKVxuXHRwcml2YXRlIG1vZHVsZU9iamVjdFZhcmlhYmxlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHQvLyBmaWxlIC0+IChsb2NhbCBuYW1lIC0+IGltcG9ydGVkIG5hbWUpIGZvciBuYW1lZCBpbXBvcnRzIGZyb21cblx0Ly8gJ21uZW1vbmljYScg4oCUIGltcG9ydC1hd2FyZW5lc3MgZm9yIHRoZSBjb25zdHJ1Y3Rpb24tZnVuY3Rpb25cblx0Ly8gcmVjb2duaXRpb24gKGNhbGwvYXBwbHkvYmluZCkgYW5kIHRoZSB1dGlscyBmb3JtcyAobWVyZ2UvZm9yayk6XG5cdC8vIHVzZXJsYW5kIGZ1bmN0aW9ucyB3aXRoIHRob3NlIG5hbWVzIG11c3QgbmV2ZXIgbWF0Y2hcblx0cHJpdmF0ZSBtbmVtb25pY2FOYW1lZEltcG9ydHMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgc3RyaW5nPj4oKTtcblx0Ly8gVHJhY2sgaW1wb3J0ZWQgYWxpYXNlcyBvZiBjcmVhdGVUeXBlc0NvbGxlY3Rpb24gKGUuZy4sIGltcG9ydCB7IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbiBhcyBjdGMgfSlcblx0cHJpdmF0ZSBjcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0Ly8gVHJhY2sgY3VzdG9tIGNvbGxlY3Rpb24gdmFyaWFibGVzOiB2YXJpYWJsZU5hbWUgLT4gY29sbGVjdGlvbklkXG5cdHByaXZhdGUgY29sbGVjdGlvblZhcmlhYmxlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdC8vIFRyYWNrIGN1c3RvbSBjb2xsZWN0aW9uIG1ldGFkYXRhIGZvciBPcHRpb24gQiByZWdpc3RyeSBlbWlzc2lvblxuXHRwcml2YXRlIGNvbGxlY3Rpb25JbmZvID0gbmV3IE1hcDxzdHJpbmcsIENvbGxlY3Rpb25JbmZvPigpO1xuXHRwcml2YXRlIGNvbGxlY3Rpb25Db3VudGVyID0gMDtcblx0Ly8gSW5zdHJ1bWVudGF0aW9uIGNvbGxlY3Rpb24gKHN5bnRhY3RpYyBvbmx5IOKAlCBubyB0eXBlIGNoZWNrZXIpOlxuXHQvLyBldmVyeSBuYW1lZCBjbGFzcyBkZWNsYXJhdGlvbiBieSBzaW1wbGUgbmFtZSwgZm9yIHJlc29sdmluZ1xuXHQvLyByZWdpc3RyYXRpb24gc2l0ZXMgdG8gZGVjbGFyYXRpb24gbG9jYXRpb25zIChiZXN0IGVmZm9ydCwgbGFzdCB3aW5zKVxuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMgPSBuZXcgTWFwPHN0cmluZywgSW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNsPigpO1xuXHQvLyBSZWdpc3RyYXRpb24gc2l0ZXM6IGRlY29yYXRvciBhcHBsaWNhdGlvbnMsIHByb3ZpZGVyLXRva2VuIG9iamVjdFxuXHQvLyBsaXRlcmFscywgY29uc3VtZXIuYXBwbHkoKSBtaWRkbGV3YXJlIHdpcmluZ1xuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvblNpdGVzOiBJbnN0cnVtZW50YXRpb25TaXRlW10gPSBbXTtcblx0Ly8gTWVyZ2VkIHBsdWdpbiB2b2NhYnVsYXJ5IGZvciBpbnN0cnVtZW50YXRpb24gZGV0ZWN0aW9uIChlbXB0eSB3aGVuXG5cdC8vIG5vIHBsdWdpbnMgd2VyZSBwYXNzZWQg4oCUIHRoZSBhbmFseXplciB0aGVuIGNvbGxlY3RzIG5vIHBvaW50cylcblx0cHJpdmF0ZSBpbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5OiBJbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5O1xuXHQvLyBSZWZlcmVuY2VkLXR5cGUgcmVzb2x1dGlvbiAoRjEwKTogcGVyLWZpbGUgZGVjbGFyYXRpb25zIGFuZCBpbXBvcnRzLlxuXHQvLyBBIHR5cGUgbmFtZSB1c2VkIGluIGZpbGUgWCByZXNvbHZlcyB0aHJvdWdoIFgncyBvd24gaW1wb3J0IHN0YXRlbWVudHNcblx0Ly8gZmlyc3QgKHJlbGF0aXZlICsgdHNjb25maWctcGF0aHMsIHZpYSB0cy5yZXNvbHZlTW9kdWxlTmFtZSksIHRoZW5cblx0Ly8gWCdzIGxvY2FsIGRlY2xhcmF0aW9ucywgdGhlbiDigJQgb25seSB3aGVuIG5vdGhpbmcgaW1wb3J0cyBvciBkZWNsYXJlc1xuXHQvLyB0aGUgbmFtZSDigJQgdGhlIHVuaXF1ZSBzYW1lLW5hbWVkIGRlY2xhcmF0aW9uIGFjcm9zcyBzY2FubmVkIGZpbGVzLlxuXHQvLyBHZW51aW5lIGFtYmlndWl0eSBvciBhbiB1bnJlc29sdmFibGUgcmVmZXJlbmNlIHlpZWxkcyBgdW5rbm93bmAsIG5ldmVyXG5cdC8vIGEgYmFyZSBlbWl0dGVkIG5hbWU6IGdlbmVyYXRlZCB0eXBlcy50cyBjYXJyaWVzIG5vIGltcG9ydHMgb2YgaXRzIG93bi5cblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZURlY2xzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24+PigpO1xuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlSW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZUltcG9ydD4+KCk7XG5cdC8vIGZpbGUgLT4gKGV4cG9ydGVkIG5hbWUgLT4gcmUtZXhwb3J0IHNwZWNpZmllcikgZm9yIGBleHBvcnQgeyBYIH0gZnJvbSAn4oCmJ2Bcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZVJlRXhwb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBmaWxlIC0+IHNwZWNpZmllcnMgb2YgYGV4cG9ydCAqIGZyb20gJ+KApidgXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmdbXT4oKTtcblx0Ly8gZmlsZSAtPiAoZXhwb3J0ZWQgbmFtZSAtPiBsb2NhbCBuYW1lKSBmb3IgYGV4cG9ydCB7IFggYXMgWSB9YFxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBmaWxlIC0+IChuYW1lc3BhY2UgbmFtZSAtPiBuYW1lc3BhY2UgZGVjbGFyYXRpb24pIOKAlCBtaWRkbGUgc2VnbWVudHNcblx0Ly8gb2YgcXVhbGlmaWVkIHJlZmVyZW5jZXMgKG1vZGVscy5Jbm5lci5DcmF0ZSkgZGVzY2VuZCB0aHJvdWdoIHRoZXNlXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHRzLk1vZHVsZURlY2xhcmF0aW9uPj4oKTtcblx0Ly8gZmlsZSAtPiAobmFtZXNwYWNlIG5hbWUgLT4gc3BlY2lmaWVyKSBmb3IgYGV4cG9ydCAqIGFzIG5zIGZyb20gJ+KApidgXG5cdC8vIGJhcnJlbHMg4oCUIGEgbmVzdGVkIG1vZHVsZSBuYW1lc3BhY2Ugb25lIHNlZ21lbnQgZGVlcFxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlU3RhcnMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgc3RyaW5nPj4oKTtcblx0Ly8gYCR7Y29udGFpbmluZ0ZpbGV9Ojoke3NwZWNpZmllcn1gIC0+IHJlc29sdXRpb24gKHVuZGVmaW5lZCA9IGZhaWxlZClcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZVJlc29sdXRpb25DYWNoZSA9IG5ldyBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZVJlc29sdXRpb24gfCB1bmRlZmluZWQ+KCk7XG5cdC8vIGZpbGUgLT4gKGNvbnN0IG5hbWUgLT4gYXJyYXkgbGl0ZXJhbCkgZm9yIGNvbnN0cyB3aXRoIGFycmF5LWxpdGVyYWxcblx0Ly8gaW5pdGlhbGl6ZXJzIChgYXMgY29uc3RgIC8gYHNhdGlzZmllc2AgdW53cmFwcGVkKSwgc28gYVxuXHQvLyBgdHlwZW9mIHN0YXR1c0xpc3RbbnVtYmVyXWAgZmllbGQgdHlwZSBleHBhbmRzIHRvIHRoZSBlbGVtZW50IGxpdGVyYWxcblx0Ly8gdW5pb24gaW5zdGVhZCBvZiBsZWFraW5nIGEgYmFyZSB1bnJlc29sdmFibGUgYHR5cGVvZmAgcXVlcnkgaW50byB0aGVcblx0Ly8gZ2VuZXJhdGVkIGZpbGUuIERlY2xhcmF0aW9ucyBwZXJzaXN0IGFjcm9zcyBwYXNzZXMg4oCUIGVudHJpZXMgc3RheVxuXHQvLyB2YWxpZCBhZnRlciByZXNldFVzYWdlcygpLCBzYW1lIGFzIHJlZmVyZW5jZWRUeXBlRGVjbHNcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24+PigpO1xuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlQ29tcGlsZXJPcHRpb25zOiB0cy5Db21waWxlck9wdGlvbnM7XG5cdC8vIEZpbGUgd2hvc2UgQVNUIGlzIGN1cnJlbnRseSBiZWluZyB2aXNpdGVkOyByZWZlcmVuY2VzIHJlc29sdmUgYWdhaW5zdCBpdFxuXHRwcml2YXRlIGN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSAnJztcblx0Ly8gQWxpYXMgbmFtZXMgY3VycmVudGx5IGJlaW5nIGV4cGFuZGVkIChjeWNsZSBndWFyZClcblx0cHJpdmF0ZSBleHBhbmRpbmdSZWZlcmVuY2VkQWxpYXNlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHQvLyBNbmVtb25pY2EtZ3JhcGggaWRlbnRpdHkgbGF3IChoYXJkIGZhaWwpOiBldmVyeSBkZWZpbmUoKS9sYXp5KCkvXG5cdC8vIEBkZWNvcmF0ZSgpIHNpdGUga2V5ZWQgYnkgaXRzIHJ1bnRpbWUgbmFtZXNwYWNlIChjb2xsZWN0aW9uIHJvb3RzOlxuXHQvLyBgPGNvbGxlY3Rpb24+Ojo8bmFtZT5gOyBzdWJ0eXBlczogYDxwYXJlbnRGdWxsUGF0aD4uPG5hbWU+YCkuIFR3b1xuXHQvLyBzaXRlcyBpbiBvbmUgbmFtZXNwYWNlIGFyZSBhIHNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZSDigJQgdGhlIHJ1bnRpbWVcblx0Ly8gdGhyb3dzIEFMUkVBRFlfREVDTEFSRUQg4oCUIGFuZCBtdXN0IGFib3J0IGdlbmVyYXRpb24uXG5cdHByaXZhdGUgZGVmaW5lU2l0ZXMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nW10+KCk7XG5cdC8vIE1uZW1vbmljYS1ncmFwaCByZWZlcmVuY2VzIHRoYXQgc3RheWVkIGFtYmlndW91cyBhZnRlciBwYXRoLWF3YXJlXG5cdC8vIHJlc29sdXRpb24gb3IgcmVzb2x2ZWQgdG8gbm90aGluZyAoaGFyZC1mYWlsIGNsYXNzIDIpXG5cdHByaXZhdGUgZ3JhcGhSZWZlcmVuY2VFcnJvcnM6IFJlc29sdXRpb25FcnJvcltdID0gW107XG5cdC8vIEd1YXJkcyBsb29rdXAoKS1wYXRoIHZhbGlkYXRpb24gc28gaXQgcnVucyBvbmNlIHBlciB1c2FnZXMgcGFzc1xuXHQvLyAoZ2V0UmVzb2x1dGlvbkVycm9ycyBtYXkgYmUgY2FsbGVkIHJlcGVhdGVkbHkpOyByZXNldFVzYWdlcyByZS1hcm1zIGl0XG5cdHByaXZhdGUgbG9va3VwUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHQvLyBMaXRlcmFsIGxvb2t1cCgpIGNhbGwgc2l0ZXMgd2l0aCB0aGVpciByZXNvbHZlZCBwYXRocy4gS2VwdCBhcGFydCBmcm9tXG5cdC8vIHRoZSB1c2FnZXMgbWFwIG9uIHB1cnBvc2U6IGFkZFVzYWdlIGRyb3BzIHBhdGhzIHRoZSBncmFwaCBkb2VzIG5vdFxuXHQvLyBrbm93ICh1c2FnZXMuanNvbiBpbmRleGVzIHJlZmVyZW5jZXMgdG8gS05PV04gdHlwZXMpLCBidXQgYW4gdW5rbm93blxuXHQvLyBsb29rdXAgcGF0aCBpcyBleGFjdGx5IHRoZSBoYXJkLWZhaWwgY2FzZSDigJQgdGhlIHJ1bnRpbWUgcmV0dXJuc1xuXHQvLyB1bmRlZmluZWQgdGhlcmUgYW5kIHRoZSBUeXBlRXJyb3IgYXJyaXZlcyBvbmUgbGluZSBsYXRlclxuXHRwcml2YXRlIGxvb2t1cFJlZmVyZW5jZXM6IHsgcGF0aDogc3RyaW5nOyBsb2NhdGlvbjogc3RyaW5nIH1bXSA9IFtdO1xuXHQvLyBHdWFyZHMgcGxhaW4tVFMgcmVmZXJlbmNlIHZhbGlkYXRpb24gc28gaXQgcnVucyBvbmNlIHBlciB1c2FnZXMgcGFzc1xuXHQvLyAoZ2V0UmVzb2x1dGlvbkVycm9ycyBtYXkgYmUgY2FsbGVkIHJlcGVhdGVkbHkpOyByZXNldFVzYWdlcyByZS1hcm1zIGl0XG5cdHByaXZhdGUgcGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHQvLyBQbGFpbi1UUyB0eXBlIHJlZmVyZW5jZSBzaXRlcyB3aG9zZSByZXNvbHV0aW9uIGZlbGwgdGhyb3VnaCBpbXBvcnRzLFxuXHQvLyBsb2NhbHMsIHRoZSBwcm9ncmFtLXdpZGUgc2NhbiwgYW5kIHRoZSBncmFwaCB0byBhIHNvZnQgYHVua25vd25gLlxuXHQvLyBWYWxpZGF0ZWQgbGF6aWx5IGZyb20gZ2V0UmVzb2x1dGlvbkVycm9ycyBhZ2FpbnN0IHRoZSBjb21wbGV0ZVxuXHQvLyBkZWNsYXJhdGlvbiBtYXA6IGEgbmFtZSBzZXZlcmFsIHByb2plY3Qtc291cmNlIGZpbGVzIGRlY2xhcmUg4oCUIHdpdGhcblx0Ly8gbm8gaW1wb3J0IGluIHRoZSByZWZlcmVuY2luZyBmaWxlIHRvIGFuY2hvciBpdCDigJQgaXMgdGhlIHBsYWluLVRTXG5cdC8vIGFtYmlndWl0eSBoYXJkLWZhaWwgY2xhc3MgKG9uZSB0aWVyIGJlbG93IHRoZSBncmFwaCBpZGVudGl0eSBsYXcpO1xuXHQvLyBhYnNlbmNlIChnaG9zdCBuYW1lcykgc3RheXMgc29mdC4gUmVjb3JkaW5nIGhhcHBlbnMgb24gZXZlcnkgcGFzcyxcblx0Ly8gdGhlIHZlcmRpY3Qgb25seSBoZXJlIOKAlCBwYXNzIDEgc2VlcyBhbiBpbmNvbXBsZXRlIGRlY2xhcmF0aW9uIG1hcCxcblx0Ly8gc28gb25seSB0aGUgdXNhZ2VzIHBhc3MgaXMgYXV0aG9yaXRhdGl2ZSAobWlycm9ycyBsb29rdXAgcmVmZXJlbmNlcylcblx0cHJpdmF0ZSBwbGFpblR5cGVSZWZlcmVuY2VzOiB7IG5hbWU6IHN0cmluZzsgbG9jYXRpb246IHN0cmluZzsgZmlsZTogc3RyaW5nIH1bXSA9IFtdO1xuXHQvLyBQZXItZmlsZSB0b3AtbGV2ZWwgdmFyaWFibGUgLT4gbW5lbW9uaWNhIGZ1bGxQYXRoIGJpbmRpbmdzICh2YWx1ZVxuXHQvLyBzY29wZSk6IGBjb25zdCBBZGRyZXNzID0gVXNlci5kZWZpbmUoJ0FkZHJlc3MnLCDigKYpYCBtYWtlcyBgQWRkcmVzc2Bcblx0Ly8gZGVub3RlIFVzZXIuQWRkcmVzcyB3aGVyZXZlciB0aGF0IGZpbGUncyByZWZlcmVuY2VzIGFyZSByZXNvbHZlZFxuXHRwcml2YXRlIGZpbGVHcmFwaEJpbmRpbmdzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHN0cmluZz4+KCk7XG5cdC8vIFRoZSBncmFwaCB0eXBlIHdob3NlIGNvbnN0cnVjdG9yIGlzIGN1cnJlbnRseSBiZWluZyBleHRyYWN0ZWQ7XG5cdC8vIGFuY2hvcnMgcmVsYXRpdmUtZmlyc3QgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb25cblx0cHJpdmF0ZSBjdXJyZW50R3JhcGhBbmNob3I6IFR5cGVOb2RlIHwgdW5kZWZpbmVkO1xuXHQvLyBkZWZpbmUoKS9sYXp5KCkgY2FsbHMgYWxyZWFkeSBleHRyYWN0ZWQgdGhpcyBwYXNzLiBUaGUgQ0xJIHJlLWFuYWx5emVzXG5cdC8vIGV2ZXJ5IGZpbGUgYWZ0ZXIgcmVzZXRVc2FnZXMoKTsgY2xlYXJpbmcgdGhlIHNldCBsZXRzIHRoZSBzZWNvbmQgcGFzc1xuXHQvLyByZS1leHRyYWN0IGV2ZXJ5IGNvbnN0cnVjdG9yIGFnYWluc3QgdGhlIENPTVBMRVRFIGdyYXBoIOKAlCBwYXNzIDEgc2Vlc1xuXHQvLyBmb3J3YXJkIHJlZmVyZW5jZXMgYXMgYG5vbmVgIChzb2Z0IHVua25vd24pIGJlY2F1c2UgbGF0ZXIgZmlsZXMgaGF2ZVxuXHQvLyBub3QgYmVlbiB2aXNpdGVkIHlldCwgc28gb25seSBwYXNzLTIgcmVzb2x1dGlvbiBpcyBhdXRob3JpdGF0aXZlIGZvclxuXHQvLyB0aGUgaGFyZC1mYWlsIGlkZW50aXR5IGxhdy4gVGhlIHN0YW1wIGxpdmVzIGhlcmUgcmF0aGVyIHRoYW4gb24gdGhlXG5cdC8vIEFTVCBub2RlIHNvIGl0IGNhbiBhY3R1YWxseSBiZSBjbGVhcmVkLiAoQ2hhaW5lZCBjYWxscyB2aXNpdCB0aGUgc2FtZVxuXHQvLyBub2RlIHR3aWNlIHdpdGhpbiBvbmUgcGFzczsgdGhlIGluLXBhc3MgZGVkdXAgYmVsb3cgc3RheXMuKVxuXHRwcml2YXRlIHByb2Nlc3NlZENhbGxzID0gbmV3IFNldDx0cy5DYWxsRXhwcmVzc2lvbj4oKTtcblxuXHRjb25zdHJ1Y3RvciAocHJvZ3JhbT86IHRzLlByb2dyYW0sIHBsdWdpbnM6IFRhY3RpY2FQbHVnaW5bXSA9IFtdKSB7XG5cdFx0Ly8gQ29tcGlsZXIgb3B0aW9ucyBkcml2ZSB0cy5yZXNvbHZlTW9kdWxlTmFtZSBmb3IgaW1wb3J0LWF3YXJlXG5cdFx0Ly8gcmVmZXJlbmNlZC10eXBlIHJlc29sdXRpb24gKHRzY29uZmlnIGBwYXRoc2AsIGV4dGVuc2lvbmxlc3Ncblx0XHQvLyBpbXBvcnRzKTsgdGhlIHR5cGUgY2hlY2tlciBpdHNlbGYgc3RheXMgdW51c2VkLlxuXHRcdHRoaXMucmVmZXJlbmNlZFR5cGVDb21waWxlck9wdGlvbnMgPSBwcm9ncmFtPy5nZXRDb21waWxlck9wdGlvbnMoKSA/PyB7fTtcblx0XHR0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkgPSBtZXJnZVRhY3RpY2FQbHVnaW5zKHBsdWdpbnMpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc2V0IHVzYWdlLXJlbGF0ZWQgc3RhdGUgZm9yIGEgZnJlc2ggcGFzcy5cblx0ICogQ2FsbCBiZWZvcmUgdGhlIHVzYWdlLWNvbGxlY3Rpb24gcGFzcyB0byBhdm9pZCBkdXBsaWNhdGVzIGZyb20gZGVmaW5pdGlvbiBwYXNzLlxuXHQgKi9cblx0cmVzZXRVc2FnZXMgKCk6IHZvaWQge1xuXHRcdHRoaXMudXNhZ2VzLmNsZWFyKCk7XG5cdFx0dGhpcy5lZHNVc2FnZXMuY2xlYXIoKTtcblx0XHR0aGlzLmZsb3dVc2FnZXMuY2xlYXIoKTtcblx0XHR0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmNsZWFyKCk7XG5cdFx0Ly8gRURTIGVudHJ5IHJlZmVyZW5jZXMgZ28gc3RhbGUgd2l0aCBlZHNVc2FnZXM7IHZpYSBsaW5rcyBhcmVcblx0XHQvLyByZS1kZXJpdmVkIG9uIHRoZSBuZXh0IHBhc3Ncblx0XHR0aGlzLndyYXBFbnRyeUJ5Tm9kZS5jbGVhcigpO1xuXHRcdHRoaXMubmVzdGVkV3JhcFZpYS5jbGVhcigpO1xuXHRcdC8vIE5vdGU6IG1vZHVsZU9iamVjdFZhcmlhYmxlcyBhbmQgY29sbGVjdGlvblZhcmlhYmxlcyBpbnRlbnRpb25hbGx5IHBlcnNpc3Rcblx0XHQvLyBhY3Jvc3MgZGVmaW5pdGlvbiBhbmQgdXNhZ2UgcGFzc2VzLlxuXHRcdC8vIFJlLWV4dHJhY3Rpb24gaW4gdGhlIHVzYWdlcyBwYXNzIGlzIHdoYXQgbWFrZXMgZ3JhcGggcmVmZXJlbmNlXG5cdFx0Ly8gcmVzb2x1dGlvbiBhdXRob3JpdGF0aXZlOiBwYXNzIDEgcmVzb2x2ZXMgYWdhaW5zdCBhbiBpbmNvbXBsZXRlXG5cdFx0Ly8gZ3JhcGggKGZvcndhcmQgcmVmZXJlbmNlcyByZWFkIGFzIGBub25lYCksIHBhc3MgMiBhZ2FpbnN0IGFsbCBvZiBpdC5cblx0XHR0aGlzLnByb2Nlc3NlZENhbGxzLmNsZWFyKCk7XG5cdFx0Ly8gbG9va3VwKCktcGF0aCB2YWxpZGF0aW9uIHJ1bnMgYWdhaW5zdCB0aGUgcmVjb3JkZWQgc2l0ZXM7IGEgZnJlc2hcblx0XHQvLyBwYXNzIG11c3QgcmUtcmVjb3JkIGFuZCByZS12YWxpZGF0ZSAocGFzcy0xIHJlc3VsdHMgd291bGQgYmVcblx0XHQvLyBwcmVtYXR1cmUg4oCUIHRoZSBncmFwaCBpcyBzdGlsbCBpbmNvbXBsZXRlKVxuXHRcdHRoaXMubG9va3VwUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHRcdHRoaXMubG9va3VwUmVmZXJlbmNlcyA9IFtdO1xuXHRcdHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IGZhbHNlO1xuXHRcdHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlcyA9IFtdO1xuXHR9XG5cblx0LyoqXG5cdCAqIEFuYWx5emUgYSBzb3VyY2UgZmlsZSBmb3IgTW5lbW9uaWNhIHR5cGUgZGVmaW5pdGlvbnNcblx0ICovXG5cdGFuYWx5emVGaWxlIChzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogQW5hbHl6ZVJlc3VsdCB7XG5cdFx0dGhpcy5lcnJvcnMgPSBbXTtcblx0XHQvLyBSZWZlcmVuY2VkLXR5cGUgbmFtZXMgaW4gdGhpcyBmaWxlIHJlc29sdmUgYWdhaW5zdCBpdHMgb3duIGltcG9ydHNcblx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSBub2RlUGF0aC5yZXNvbHZlKHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXHRcdC8vIEVuc3VyZSBwYXJlbnQgbm9kZXMgYXJlIHNldCBmb3IgQVNUIHRyYXZlcnNhbFxuXHRcdHRoaXMuc2V0UGFyZW50Tm9kZXNJblNvdXJjZUZpbGUoc291cmNlRmlsZSk7XG5cdFx0dGhpcy52aXNpdE5vZGUoc291cmNlRmlsZSwgc291cmNlRmlsZSk7XG5cblx0XHRyZXR1cm4ge1xuXHRcdFx0dHlwZXMgIDogdGhpcy5ncmFwaC5nZXRBbGxUeXBlcygpLFxuXHRcdFx0ZXJyb3JzIDogdGhpcy5lcnJvcnMsXG5cdFx0fTtcblx0fVxuXG5cdC8qKlxuXHQgKiBBbmFseXplIHNvdXJjZSBjb2RlIHN0cmluZ1xuXHQgKi9cblx0YW5hbHl6ZVNvdXJjZSAoc291cmNlQ29kZTogc3RyaW5nLCBmaWxlTmFtZSA9ICd0ZW1wLnRzJyk6IEFuYWx5emVSZXN1bHQge1xuXHRcdGNvbnN0IHNvdXJjZUZpbGUgPSB0cy5jcmVhdGVTb3VyY2VGaWxlKFxuXHRcdFx0ZmlsZU5hbWUsXG5cdFx0XHRzb3VyY2VDb2RlLFxuXHRcdFx0dHMuU2NyaXB0VGFyZ2V0LkxhdGVzdCxcblx0XHRcdHRydWVcblx0XHQpO1xuXHRcdHJldHVybiB0aGlzLmFuYWx5emVGaWxlKHNvdXJjZUZpbGUpO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCB0aGUgdHlwZSBncmFwaFxuXHQgKi9cblx0Z2V0R3JhcGggKCk6IFR5cGVHcmFwaEltcGwge1xuXHRcdHJldHVybiB0aGlzLmdyYXBoO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBjb2xsZWN0ZWQgZGVmaW5pdGlvbnNcblx0ICovXG5cdGdldERlZmluaXRpb25zICgpOiBNYXA8c3RyaW5nLCBEZWZpbml0aW9uSW5mbz4ge1xuXHRcdHJldHVybiB0aGlzLmRlZmluaXRpb25zO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBjb2xsZWN0ZWQgdXNhZ2VzXG5cdCAqL1xuXHRnZXRVc2FnZXMgKCk6IE1hcDxzdHJpbmcsIFVzYWdlSW5mb1tdPiB7XG5cdFx0cmV0dXJuIHRoaXMudXNhZ2VzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBjb2xsZWN0ZWQgRURTIHVzYWdlc1xuXHQgKi9cblx0Z2V0RURTVXNhZ2VzICgpOiBNYXA8c3RyaW5nLCBFRFNJbmZvW10+IHtcblx0XHRyZXR1cm4gdGhpcy5lZHNVc2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBmbG93IHVzYWdlc1xuXHQgKi9cblx0Z2V0Rmxvd1VzYWdlcyAoKTogTWFwPHN0cmluZywgRmxvd0luZm9bXT4ge1xuXHRcdHJldHVybiB0aGlzLmZsb3dVc2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBpbnN0cnVtZW50YXRpb24gcG9pbnRzLlxuXHQgKiBSZWdpc3RyYXRpb24gc2l0ZXMgcmVmZXJlbmNpbmcgYSBjbGFzcyBkZWNsYXJlZCBpbiB0aGUgc2FtZSBwcm9qZWN0XG5cdCAqIHJlc29sdmUgdG8gdGhlIGNsYXNzIGRlY2xhcmF0aW9uJ3MgbG9jYXRpb24vY29kZTsgZXh0ZXJuYWwgY2xhc3Nlc1xuXHQgKiAoZS5nLiwgYSBmcmFtZXdvcmstYnVpbHRpbiBpbXBsZW1lbnRhdGlvbiBmcm9tIG5vZGVfbW9kdWxlcykga2VlcFxuXHQgKiB0aGUgcmVnaXN0cmF0aW9uIHNpdGUuXG5cdCAqIERlZHVwZWQgYnkga2luZCtjbGFzc05hbWUrbG9jYXRpb24rc2NvcGUgd2l0aCB0YXJnZXRzIG1lcmdlZCDigJQgYVxuXHQgKiBjbGFzcyBkZXRlY3RlZCBieSBoZXJpdGFnZSBBTkQgYnkgYSBkZWNvcmF0b3Igc2l0ZSB5aWVsZHMgc2VwYXJhdGVcblx0ICogZW50cmllcyB3aXRoIGRpc3RpbmN0IHNjb3BlcyAoc2VlIEluc3RydW1lbnRhdGlvblBvaW50IGluIHR5cGVzLnRzKS5cblx0ICovXG5cdGdldEluc3RydW1lbnRhdGlvblBvaW50cyAoKTogSW5zdHJ1bWVudGF0aW9uUG9pbnRbXSB7XG5cdFx0Y29uc3QgcG9pbnRzID0gbmV3IE1hcDxzdHJpbmcsIEluc3RydW1lbnRhdGlvblBvaW50PigpO1xuXG5cdFx0Y29uc3QgYWRkUG9pbnQgPSAocG9pbnQ6IEluc3RydW1lbnRhdGlvblBvaW50KTogdm9pZCA9PiB7XG5cdFx0XHRjb25zdCBrZXkgPSBgJHtwb2ludC5raW5kfXwke3BvaW50LmNsYXNzTmFtZX18JHtwb2ludC5sb2NhdGlvbn18JHtwb2ludC5zY29wZX1gO1xuXHRcdFx0Y29uc3QgZXhpc3RpbmcgPSBwb2ludHMuZ2V0KGtleSk7XG5cdFx0XHRpZiAoZXhpc3RpbmcpIHtcblx0XHRcdFx0Y29uc3QgbWVyZ2VkID0gbmV3IFNldChbIC4uLmV4aXN0aW5nLnRhcmdldHMsIC4uLnBvaW50LnRhcmdldHMgXSk7XG5cdFx0XHRcdGV4aXN0aW5nLnRhcmdldHMgPSBBcnJheS5mcm9tKG1lcmdlZCk7XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdHBvaW50cy5zZXQoa2V5LCBwb2ludCk7XG5cdFx0fTtcblxuXHRcdGZvciAoY29uc3Qgc2l0ZSBvZiB0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzKSB7XG5cdFx0XHRjb25zdCBkZWNsID0gdGhpcy5pbnN0cnVtZW50YXRpb25DbGFzc0RlY2xzLmdldChzaXRlLmNsYXNzTmFtZSk7XG5cdFx0XHRjb25zdCBwb2ludDogSW5zdHJ1bWVudGF0aW9uUG9pbnQgPSB7XG5cdFx0XHRcdGtpbmQgICAgICA6IHNpdGUua2luZCxcblx0XHRcdFx0Y2xhc3NOYW1lIDogc2l0ZS5jbGFzc05hbWUsXG5cdFx0XHRcdGxvY2F0aW9uICA6IGRlY2wgPyBkZWNsLmxvY2F0aW9uIDogc2l0ZS5sb2NhdGlvbixcblx0XHRcdFx0Y29kZSAgICAgIDogZGVjbCA/IGRlY2wuY29kZSA6IHNpdGUuY29kZSxcblx0XHRcdFx0c2NvcGUgICAgIDogc2l0ZS5zY29wZSxcblx0XHRcdFx0dGFyZ2V0cyAgIDogc2l0ZS50YXJnZXRzLFxuXHRcdFx0fTtcblx0XHRcdGFkZFBvaW50KHBvaW50KTtcblx0XHR9XG5cblx0XHQvLyBIZXJpdGFnZS1kZWNsYXJlZCBjbGFzc2VzIGFsd2F5cyBlbWl0IGEgZGVjbGFyYXRpb24gcG9pbnQgd2l0aFxuXHRcdC8vIHNjb3BlICdtb2R1bGUnIChhdHRhY2htZW50IHN0YXRpY2FsbHkgdW5rbm93bik7IHJlZ2lzdHJhdGlvblxuXHRcdC8vIHNpdGVzIGFib3ZlIGNhcnJ5IHRoZSBuYXJyb3dlciBzY29wZXMgYXMgc2VwYXJhdGUgZW50cmllc1xuXHRcdGZvciAoY29uc3QgWyBjbGFzc05hbWUsIGRlY2wgXSBvZiB0aGlzLmluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMpIHtcblx0XHRcdGlmICghZGVjbC5raW5kKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgcG9pbnQ6IEluc3RydW1lbnRhdGlvblBvaW50ID0ge1xuXHRcdFx0XHRraW5kICAgICAgOiBkZWNsLmtpbmQsXG5cdFx0XHRcdGNsYXNzTmFtZSA6IGNsYXNzTmFtZSxcblx0XHRcdFx0bG9jYXRpb24gIDogZGVjbC5sb2NhdGlvbixcblx0XHRcdFx0Y29kZSAgICAgIDogZGVjbC5jb2RlLFxuXHRcdFx0XHRzY29wZSAgICAgOiAnbW9kdWxlJyxcblx0XHRcdFx0dGFyZ2V0cyAgIDogW10sXG5cdFx0XHR9O1xuXHRcdFx0YWRkUG9pbnQocG9pbnQpO1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlc3VsdCA9IEFycmF5LmZyb20ocG9pbnRzLnZhbHVlcygpKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhIHRvcG9sb2dpY2EgdHlwZSB0byB0aGUgYW5hbHl6ZXIgZm9yIHVzYWdlIHRyYWNraW5nLlxuXHQgKiBUaGlzIGFsbG93cyB0aGUgYW5hbHl6ZXIgdG8gcmVjb2duaXplIHRvcG9sb2dpY2EgdHlwZXMgd2hlbiBjb2xsZWN0aW5nIHVzYWdlcy5cblx0ICovXG5cdGFkZFRvcG9sb2dpY2FUeXBlIChmdWxsUGF0aDogc3RyaW5nLCBub2RlOiBpbXBvcnQoJy4vdHlwZXMnKS5UeXBlTm9kZSk6IHZvaWQge1xuXHRcdC8vIFNraXAgaWYgYWxyZWFkeSBleGlzdHNcblx0XHRpZiAodGhpcy5ncmFwaC5hbGxUeXBlcy5oYXMoZnVsbFBhdGgpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoIHNvIGl0IGNhbiBiZSBmb3VuZCBkdXJpbmcgdXNhZ2UgY29sbGVjdGlvblxuXHRcdGlmIChub2RlLnBhcmVudCkge1xuXHRcdFx0Ly8gQWRkIGFzIGNoaWxkIG9mIHBhcmVudFxuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChub2RlLnBhcmVudCwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdC8vIEFkZCBhcyByb290XG5cdFx0XHR0aGlzLmdyYXBoLmFkZFJvb3Qobm9kZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQWxzbyBhZGQgdG8gZGVmaW5pdGlvbnMgc28gaXQncyByZWNvZ25pemVkIGFzIGEga25vd24gdHlwZVxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiBub2RlLm5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke25vZGUuc291cmNlRmlsZX06JHtub2RlLmxpbmV9OiR7bm9kZS5jb2x1bW59YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlZmluZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IG5vZGUucGFyZW50ID8gbm9kZS5wYXJlbnQuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBmYWxzZVxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQoZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFNldCBwYXJlbnQgbm9kZXMgaW4gYSBzb3VyY2UgZmlsZSB0byBlbmFibGUgQVNUIHRyYXZlcnNhbCB1cFxuXHQgKi9cblx0cHJpdmF0ZSBzZXRQYXJlbnROb2Rlc0luU291cmNlRmlsZSAoc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHNldFBhcmVudCA9IChub2RlOiB0cy5Ob2RlLCBwYXJlbnQ/OiB0cy5Ob2RlKSA9PiB7XG5cdFx0XHQvLyBUeXBlU2NyaXB0IGRvZXNuJ3QgZXhwb3NlIHBhcmVudCBhcyB3cml0YWJsZSwgYnV0IHdlIG5lZWQgaXRcblx0XHRcdC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBAdHlwZXNjcmlwdC1lc2xpbnQvbm8tZXhwbGljaXQtYW55XG5cdFx0XHQobm9kZSBhcyBhbnkpLnBhcmVudCA9IHBhcmVudDtcblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCBjaGlsZCA9PiBzZXRQYXJlbnQoY2hpbGQsIG5vZGUpKTtcblx0XHR9O1xuXHRcdHNldFBhcmVudChzb3VyY2VGaWxlKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBWaXNpdCBhIG5vZGUgaW4gdGhlIEFTVFxuXHQgKi9cblx0cHJpdmF0ZSB2aXNpdE5vZGUgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsIGN1cnJlbnRDbGFzcz86IHRzLkNsYXNzRGVjbGFyYXRpb24pOiB2b2lkIHtcblx0XHQvLyBUcmFjayBtbmVtb25pY2EgbW9kdWxlLW9iamVjdCBhbGlhc2VzIGFuZCBjdXN0b20gY29sbGVjdGlvbiB2YXJpYWJsZXNcblx0XHQvLyBiZWZvcmUgcHJvY2Vzc2luZyBkZWZpbmUoKS9sb29rdXAoKSBjYWxscyBzbyBzb3VyY2UgcmVzb2x1dGlvbiB3b3Jrcy5cblx0XHR0aGlzLnRyYWNrSW1wb3J0cyhub2RlKTtcblx0XHR0aGlzLnRyYWNrTW9kdWxlT2JqZWN0QWxpYXNlcyhub2RlKTtcblx0XHR0aGlzLnRyYWNrQ29sbGVjdGlvbkFsaWFzZXMobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgZGVmaW5lKCkgY2FsbHNcblx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0RlZmluZUNhbGwobm9kZSBhcyB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIGxhenkoKSBjYWxsc1xuXHRcdGlmICh0aGlzLmlzTGF6eUNhbGwobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0xhenlDYWxsKG5vZGUgYXMgdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGUpO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHRcdGlmICh0aGlzLmlzRGVjb3JhdGVEZWNvcmF0b3Iobm9kZSkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0RlY29yYXRlRGVjb3JhdG9yKG5vZGUgYXMgdHMuRGVjb3JhdG9yLCBzb3VyY2VGaWxlLCBjdXJyZW50Q2xhc3MpO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciB0eXBlIHVzYWdlcyAobmV3IFR5cGUoKSwgdHlwZSBhbm5vdGF0aW9ucywgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RVc2FnZShub2RlLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIENoZWNrIGZvciBFRFMgcGF0dGVybnMgKHdyYXAsIGN1cnJlbnQsIGdldEZsb3csIGV0Yy4pXG5cdFx0dGhpcy5jb2xsZWN0RURTKG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIG5hdGl2ZSBmbG93IHBhdHRlcm5zIChwcm9wZXJ0eSBhY2Nlc3MsIG1ldGhvZCBjYWxscywgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RGbG93KG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIGZyYW1ld29yayBpbnN0cnVtZW50YXRpb24gcG9pbnRzICh2b2NhYnVsYXJ5IHN1cHBsaWVkXG5cdFx0Ly8gYnkgcGx1Z2luczsgc3ludGFjdGljIG9ubHkg4oCUIG5vIHR5cGUgY2hlY2tlcilcblx0XHR0aGlzLmNvbGxlY3RJbnN0cnVtZW50YXRpb24obm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDb2xsZWN0IHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbnMgKGFsaWFzZXMsIGNsYXNzZXMsIGludGVyZmFjZXMpXG5cdFx0Ly8gcGVyIGZpbGUsIGFuZCB0aGUgZmlsZSdzIGltcG9ydCB3aXJpbmcsIGZvciBpbXBvcnQtYXdhcmUgcmVzb2x1dGlvblxuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKG5vZGUpO1xuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZUltcG9ydChub2RlKTtcblx0XHR0aGlzLnRyYWNrUmVmZXJlbmNlZFR5cGVSZUV4cG9ydChub2RlKTtcblx0XHR0aGlzLnRyYWNrUmVmZXJlbmNlZFR5cGVDb25zdEFycmF5KG5vZGUpO1xuXG5cdFx0Ly8gVHJhY2sgc2FtZS1maWxlIGZ1bmN0aW9uIGJpbmRpbmdzIHNvIEVEUyBjYW4gcmVzb2x2ZSB3cmFwKGZuKVxuXHRcdC8vIGFyZ3VtZW50cyB3aXRob3V0IHRoZSB0eXBlIGNoZWNrZXIgKGJlc3QgZWZmb3J0LCBsYXN0IHdpbnMpXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9IyR7bm9kZS5uYW1lLnRleHR9YDtcblx0XHRcdHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5zZXQoa2V5LCBub2RlKTtcblx0XHR9XG5cdFx0aWYgKFxuXHRcdFx0dHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSAmJlxuXHRcdFx0bm9kZS5pbml0aWFsaXplciAmJlxuXHRcdFx0KHRzLmlzQXJyb3dGdW5jdGlvbihub2RlLmluaXRpYWxpemVyKSB8fCB0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihub2RlLmluaXRpYWxpemVyKSlcblx0XHQpIHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9IyR7bm9kZS5uYW1lLnRleHR9YDtcblx0XHRcdHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5zZXQoa2V5LCBub2RlLmluaXRpYWxpemVyKTtcblx0XHR9XG5cblx0XHQvLyBUcmFjayBjbGFzcyBkZWNsYXJhdGlvbnMgZm9yIGRlY29yYXRvciBwYXJlbnQgbG9va3VwXG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0Ly8gVmlzaXQgY2hpbGRyZW4gd2l0aCB0aGlzIGNsYXNzIGFzIHRoZSBjdXJyZW50IGNvbnRleHRcblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCBjaGlsZCA9PiB0aGlzLnZpc2l0Tm9kZShjaGlsZCwgc291cmNlRmlsZSwgbm9kZSkpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHQvLyBSZWN1cnNpdmVseSB2aXNpdCBjaGlsZHJlblxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHRoaXMudmlzaXROb2RlKGNoaWxkLCBzb3VyY2VGaWxlLCBjdXJyZW50Q2xhc3MpKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgaW1wb3J0cyBmcm9tICdtbmVtb25pY2EnIHNvIGFsaWFzZXMgb2YgdGhlIG1vZHVsZSBvYmplY3QgYW5kXG5cdCAqIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbiBhcmUgcmVjb2duaXplZCB3aXRob3V0IHJlbHlpbmcgb24gdGhlIHR5cGUgY2hlY2tlci5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tJbXBvcnRzIChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc0ltcG9ydERlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBtb2R1bGVTcGVjaWZpZXIgfSA9IG5vZGU7XG5cdFx0aWYgKCF0cy5pc1N0cmluZ0xpdGVyYWwobW9kdWxlU3BlY2lmaWVyKSB8fCBtb2R1bGVTcGVjaWZpZXIudGV4dCAhPT0gJ21uZW1vbmljYScpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCBjbGF1c2UgPSBub2RlLmltcG9ydENsYXVzZTtcblx0XHRpZiAoIWNsYXVzZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGltcG9ydCB7IG1uZW1vbmljYSwgY3JlYXRlVHlwZXNDb2xsZWN0aW9uIH0gZnJvbSAnbW5lbW9uaWNhJ1xuXHRcdGlmIChjbGF1c2UubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVkSW1wb3J0cyhjbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBjbGF1c2UubmFtZWRCaW5kaW5ncy5lbGVtZW50cykge1xuXHRcdFx0XHRjb25zdCBsb2NhbE5hbWUgPSBlbGVtZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgaW1wb3J0ZWROYW1lID0gZWxlbWVudC5wcm9wZXJ0eU5hbWVcblx0XHRcdFx0XHQ/IGVsZW1lbnQucHJvcGVydHlOYW1lLnRleHRcblx0XHRcdFx0XHQ6IGxvY2FsTmFtZTtcblx0XHRcdFx0aWYgKGltcG9ydGVkTmFtZSA9PT0gJ21uZW1vbmljYScpIHtcblx0XHRcdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQobG9jYWxOYW1lKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoaW1wb3J0ZWROYW1lID09PSAnY3JlYXRlVHlwZXNDb2xsZWN0aW9uJykge1xuXHRcdFx0XHRcdHRoaXMuY3JlYXRlVHlwZXNDb2xsZWN0aW9uVmFyaWFibGVzLmFkZChsb2NhbE5hbWUpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGxldCBmaWxlSW1wb3J0cyA9IHRoaXMubW5lbW9uaWNhTmFtZWRJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHRpZiAoIWZpbGVJbXBvcnRzKSB7XG5cdFx0XHRcdFx0ZmlsZUltcG9ydHMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0XHRcdHRoaXMubW5lbW9uaWNhTmFtZWRJbXBvcnRzLnNldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUsIGZpbGVJbXBvcnRzKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRmaWxlSW1wb3J0cy5zZXQobG9jYWxOYW1lLCBpbXBvcnRlZE5hbWUpO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIGltcG9ydCAqIGFzIG1uZW1vbmljYSBmcm9tICdtbmVtb25pY2EnXG5cdFx0aWYgKGNsYXVzZS5uYW1lZEJpbmRpbmdzICYmIHRzLmlzTmFtZXNwYWNlSW1wb3J0KGNsYXVzZS5uYW1lZEJpbmRpbmdzKSkge1xuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuYWRkKGNsYXVzZS5uYW1lZEJpbmRpbmdzLm5hbWUudGV4dCk7XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0IG1uZW1vbmljYSBmcm9tICdtbmVtb25pY2EnIChkZWZhdWx0IGltcG9ydCkg4oCUIHRyZWF0IGFzIG1vZHVsZSBvYmplY3QgdG9vXG5cdFx0aWYgKGNsYXVzZS5uYW1lKSB7XG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQoY2xhdXNlLm5hbWUudGV4dCk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhIG5hbWVkIHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbiAodHlwZSBhbGlhcywgY2xhc3MsIG9yXG5cdCAqIGludGVyZmFjZSkgZm9yIHRoZSBmaWxlIGN1cnJlbnRseSBiZWluZyB2aXNpdGVkLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHQvLyBOYW1lc3BhY2VzIGFyZSB0aGUgbWlkZGxlIHNlZ21lbnRzIG9mIHF1YWxpZmllZCByZWZlcmVuY2VzXG5cdFx0Ly8gKG1vZGVscy5Jbm5lci5DcmF0ZSkg4oCUIHJlY29yZGVkIHNlcGFyYXRlbHkgZnJvbSB0aGUgcGxhaW4tbmFtZVxuXHRcdC8vIGRlY2xhcmF0aW9uIHRhYmxlIChzdHJpbmctbmFtZWQgYG1vZHVsZSAn4oCmJ2AgZGVjbGFyYXRpb25zIGFyZVxuXHRcdC8vIGFtYmllbnQgZXh0ZXJuYWxzIGFuZCBzdGF5IG91dClcblx0XHRpZiAodHMuaXNNb2R1bGVEZWNsYXJhdGlvbihub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSAmJlxuXHRcdFx0bm9kZS5ib2R5ICYmIHRzLmlzTW9kdWxlQmxvY2sobm9kZS5ib2R5KSkge1xuXHRcdFx0Y29uc3QgbmFtZXNwYWNlRmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0XHRsZXQgbmFtZXNwYWNlcyA9IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzLmdldChuYW1lc3BhY2VGaWxlUGF0aCk7XG5cdFx0XHRpZiAoIW5hbWVzcGFjZXMpIHtcblx0XHRcdFx0bmFtZXNwYWNlcyA9IG5ldyBNYXA8c3RyaW5nLCB0cy5Nb2R1bGVEZWNsYXJhdGlvbj4oKTtcblx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMuc2V0KG5hbWVzcGFjZUZpbGVQYXRoLCBuYW1lc3BhY2VzKTtcblx0XHRcdH1cblx0XHRcdG5hbWVzcGFjZXMuc2V0KG5vZGUubmFtZS50ZXh0LCBub2RlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRsZXQgbmFtZSA9ICcnO1xuXHRcdGxldCBraW5kOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uWydraW5kJ10gfCB1bmRlZmluZWQ7XG5cdFx0bGV0IGRlY2xOb2RlOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uWydub2RlJ10gfCB1bmRlZmluZWQ7XG5cblx0XHRpZiAodHMuaXNUeXBlQWxpYXNEZWNsYXJhdGlvbihub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSkge1xuXHRcdFx0bmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0a2luZCA9ICdhbGlhcyc7XG5cdFx0XHRkZWNsTm9kZSA9IG5vZGU7XG5cdFx0fSBlbHNlIGlmICh0cy5pc0NsYXNzRGVjbGFyYXRpb24obm9kZSkgJiYgbm9kZS5uYW1lKSB7XG5cdFx0XHRuYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0XHRraW5kID0gJ2NsYXNzJztcblx0XHRcdGRlY2xOb2RlID0gbm9kZTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzSW50ZXJmYWNlRGVjbGFyYXRpb24obm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdG5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRcdGtpbmQgPSAnaW50ZXJmYWNlJztcblx0XHRcdGRlY2xOb2RlID0gbm9kZTtcblx0XHR9XG5cblx0XHRpZiAoIWtpbmQgfHwgIWRlY2xOb2RlIHx8ICFuYW1lKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0bGV0IGRlY2xzID0gdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLmdldChmaWxlUGF0aCk7XG5cdFx0aWYgKCFkZWNscykge1xuXHRcdFx0ZGVjbHMgPSBuZXcgTWFwPHN0cmluZywgUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbj4oKTtcblx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscy5zZXQoZmlsZVBhdGgsIGRlY2xzKTtcblx0XHR9XG5cdFx0Y29uc3QgZW50cnk6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gPSB7IGtpbmQsIG5vZGUgOiBkZWNsTm9kZSwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0ZGVjbHMuc2V0KG5hbWUsIGVudHJ5KTtcblxuXHRcdC8vIGBleHBvcnQgZGVmYXVsdCBjbGFzcyBGb28ge31gIGlzIGFsc28gcmVhY2hhYmxlIHVuZGVyIHRoZSAnZGVmYXVsdCdcblx0XHQvLyBiaW5kaW5nIGZvciBkZWZhdWx0IGltcG9ydGVyc1xuXHRcdGlmIChraW5kID09PSAnY2xhc3MnKSB7XG5cdFx0XHRjb25zdCBjbGFzc05vZGUgPSBkZWNsTm9kZSBhcyB0cy5DbGFzc0RlY2xhcmF0aW9uO1xuXHRcdFx0Y29uc3QgaXNFeHBvcnRlZCA9IGNsYXNzTm9kZS5tb2RpZmllcnM/LnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRXhwb3J0S2V5d29yZCkgPz8gZmFsc2U7XG5cdFx0XHRjb25zdCBpc0RlZmF1bHQgPSBjbGFzc05vZGUubW9kaWZpZXJzPy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLkRlZmF1bHRLZXl3b3JkKSA/PyBmYWxzZTtcblx0XHRcdGlmIChpc0V4cG9ydGVkICYmIGlzRGVmYXVsdCkge1xuXHRcdFx0XHRkZWNscy5zZXQoJ2RlZmF1bHQnLCBlbnRyeSk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBjb25zdHMgaW5pdGlhbGl6ZWQgd2l0aCBhbiBhcnJheSBsaXRlcmFsIChvcHRpb25hbGx5IHdyYXBwZWQgaW5cblx0ICogYGFzIGNvbnN0YCAvIGBzYXRpc2ZpZXNgKSwgc28gYSBgdHlwZW9mIHN0YXR1c0xpc3RbbnVtYmVyXWAgZmllbGQgdHlwZVxuXHQgKiBleHBhbmRzIHRvIHRoZSBlbGVtZW50IGxpdGVyYWwgdW5pb24g4oCUIHRoZSBnZW5lcmF0ZWQgZmlsZSBjYXJyaWVzIG5vXG5cdCAqIGltcG9ydHMsIHNvIGVtaXR0aW5nIHRoZSBiYXJlIGB0eXBlb2Ygc3RhdHVzTGlzdGAgcXVlcnkgd291bGQgYmUgYW5cblx0ICogdW5yZXNvbHZhYmxlIG5hbWUgZG93bnN0cmVhbS4gRmlyc3QgYmluZGluZyB3aW5zOiBhIG5lc3RlZCBzaGFkb3dcblx0ICogbXVzdCBub3QgcmVwbGFjZSB0aGUgbW9kdWxlLWxldmVsIGNvbnN0IHRoZSB0eXBlb2YgcmVmZXJzIHRvLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlQ29uc3RBcnJheSAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpIHx8ICF0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSB8fCAhbm9kZS5pbml0aWFsaXplcikge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCB7IGluaXRpYWxpemVyOiByYXdJbml0aWFsaXplciB9ID0gbm9kZTtcblx0XHRsZXQgaW5pdGlhbGl6ZXI6IHRzLkV4cHJlc3Npb24gPSByYXdJbml0aWFsaXplcjtcblx0XHR3aGlsZSAoXG5cdFx0XHR0cy5pc0FzRXhwcmVzc2lvbihpbml0aWFsaXplcikgfHxcblx0XHRcdHRzLmlzU2F0aXNmaWVzRXhwcmVzc2lvbihpbml0aWFsaXplcikgfHxcblx0XHRcdC8vIHRoZSBhbmdsZS1icmFja2V0IGFzc2VydGlvbiBzcGVsbGluZyAoYDxjb25zdD5b4oCmXWApIGlzIHRoZVxuXHRcdFx0Ly8gc2FtZSBjb25zdC1hcnJheSBtYXJrZXIgYXMgdGhlIGBhcyBjb25zdGAgZm9ybSAoRjE3KVxuXHRcdFx0dHMuaXNUeXBlQXNzZXJ0aW9uRXhwcmVzc2lvbihpbml0aWFsaXplcilcblx0XHQpIHtcblx0XHRcdGluaXRpYWxpemVyID0gaW5pdGlhbGl6ZXIuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0aWYgKCF0cy5pc0FycmF5TGl0ZXJhbEV4cHJlc3Npb24oaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGZpbGVQYXRoID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGxldCBjb25zdHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuZ2V0KGZpbGVQYXRoKTtcblx0XHRpZiAoIWNvbnN0cykge1xuXHRcdFx0Y29uc3RzID0gbmV3IE1hcDxzdHJpbmcsIHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24+KCk7XG5cdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuc2V0KGZpbGVQYXRoLCBjb25zdHMpO1xuXHRcdH1cblx0XHRpZiAoIWNvbnN0cy5oYXMobm9kZS5uYW1lLnRleHQpKSB7XG5cdFx0XHRjb25zdHMuc2V0KG5vZGUubmFtZS50ZXh0LCBpbml0aWFsaXplcik7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEZpbmQgdGhlIGFycmF5IGxpdGVyYWwgYmVoaW5kIGEgbW9kdWxlIGNvbnN0IHJlZmVyZW5jZWQgdGhyb3VnaFxuXHQgKiBgdHlwZW9mYDogdGhlIGRlY2xhcmluZyBmaWxlJ3Mgb3duIGNvbnN0cyBmaXJzdCAodGhlIEYxMyBjYXNlIGlzIGFcblx0ICogTk9OLWV4cG9ydGVkIGNvbnN0IGluIHRoZSBzYW1lIG1vZHVsZSBhcyB0aGUgZXhwYW5kZWQgY2xhc3MpLCB0aGVuIOKAlFxuXHQgKiB3aGVuIHRoZSBmaWxlIGltcG9ydHMgdGhlIG5hbWUg4oCUIHRoZSBpbXBvcnRlZCBtb2R1bGUncyBjb25zdHMuXG5cdCAqIEV4dGVybmFsIG1vZHVsZXMgYXJlIG5ldmVyIGFuYWx5emVkLCBzbyB0aG9zZSB5aWVsZCBub3RoaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kUmVmZXJlbmNlZENvbnN0QXJyYXkgKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRmcm9tRmlsZTogc3RyaW5nXG5cdCk6IHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGxvY2FsID0gdGhpcy5yZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzLmdldChmcm9tRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWwpIHtcblx0XHRcdHJldHVybiBsb2NhbDtcblx0XHR9XG5cdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoZnJvbUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKCFpbXBvcnRlZCB8fCBpbXBvcnRlZC5pc05hbWVzcGFjZSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKGltcG9ydGVkLnNwZWNpZmllciwgZnJvbUZpbGUpO1xuXHRcdGlmICghcmVzb2x1dGlvbiB8fCByZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGZvdW5kID0gdGhpcy5yZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzLmdldChyZXNvbHV0aW9uLnJlc29sdmVkUGF0aCk/LmdldChpbXBvcnRlZC5vcmlnaW5hbE5hbWUpO1xuXHRcdHJldHVybiBmb3VuZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFbGVtZW50IGxpdGVyYWwgdHlwZXMgb2YgYSB0cmFja2VkIGNvbnN0IGFycmF5OiBldmVyeSBlbGVtZW50IG11c3QgYmVcblx0ICogYSBwbGFpbiBsaXRlcmFsIChvcHRpb25hbGx5IHdyYXBwZWQgaW4gYGFzIGNvbnN0YCAvIGBzYXRpc2ZpZXNgIC9cblx0ICogYDxjb25zdD5gIGFzc2VydGlvbnMpIOKAlCBzdHJpbmcsIG51bWVyaWMgKHVuYXJ5IGAtYC9gK2AgcHJlc2VydmVkKSxcblx0ICogYm9vbGVhbiwgb3IgbnVsbC4gU3ByZWFkcywgaWRlbnRpZmllcnMsIGFuZCBuZXN0ZWQgYXJyYXlzIG1lYW4gdGhlXG5cdCAqIHVuaW9uIGlzIG5vdCBzdGF0aWNhbGx5IHZpc2libGUgYW5kIHlpZWxkIHVuZGVmaW5lZCwgc28gdGhlIGNhbGxlclxuXHQgKiBkZWdyYWRlcyB0aGUgZmllbGQgdG8gYHVua25vd25gIHJhdGhlciB0aGFuIGd1ZXNzaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBsaXRlcmFsVHlwZXNPZkFycmF5IChhcnJheUxpdGVyYWw6IHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24pOiBzdHJpbmdbXSB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgbGl0ZXJhbHM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGFycmF5TGl0ZXJhbC5lbGVtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzU3ByZWFkRWxlbWVudChlbGVtZW50KSkge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbGl0ZXJhbCA9IHRoaXMubGl0ZXJhbFR5cGVPZkV4cHJlc3Npb24oZWxlbWVudCk7XG5cdFx0XHRpZiAobGl0ZXJhbCA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRsaXRlcmFscy5wdXNoKGxpdGVyYWwpO1xuXHRcdH1cblx0XHRpZiAobGl0ZXJhbHMubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBsaXRlcmFscztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFRoZSBsaXRlcmFsIHR5cGUgb2Ygb25lIGFycmF5IGVsZW1lbnQ6IGEgcGxhaW4gbGl0ZXJhbCAob3B0aW9uYWxseVxuXHQgKiB3cmFwcGVkIGluIGBhcyBjb25zdGAgLyBgc2F0aXNmaWVzYCAvIGFzc2VydGlvbiBleHByZXNzaW9ucykg4oCUXG5cdCAqIHN0cmluZywgbnVtZXJpYyAodW5hcnkgYC1gL2ArYCBwcmVzZXJ2ZWQpLCBib29sZWFuLCBvciBudWxsLlxuXHQgKiBBbnl0aGluZyBlbHNlIHlpZWxkcyB1bmRlZmluZWQuXG5cdCAqL1xuXHRwcml2YXRlIGxpdGVyYWxUeXBlT2ZFeHByZXNzaW9uIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgaW5uZXI6IHRzLkV4cHJlc3Npb24gPSBleHByO1xuXHRcdHdoaWxlICh0cy5pc0FzRXhwcmVzc2lvbihpbm5lcikgfHwgdHMuaXNTYXRpc2ZpZXNFeHByZXNzaW9uKGlubmVyKSB8fCB0cy5pc1R5cGVBc3NlcnRpb25FeHByZXNzaW9uKGlubmVyKSkge1xuXHRcdFx0aW5uZXIgPSBpbm5lci5leHByZXNzaW9uO1xuXHRcdH1cblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGlubmVyKSB8fCB0cy5pc05vU3Vic3RpdHV0aW9uVGVtcGxhdGVMaXRlcmFsKGlubmVyKSkge1xuXHRcdFx0Y29uc3QgbGl0ZXJhbCA9IGAnJHtpbm5lci50ZXh0fSdgO1xuXHRcdFx0cmV0dXJuIGxpdGVyYWw7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1ByZWZpeFVuYXJ5RXhwcmVzc2lvbihpbm5lcikgJiYgdHMuaXNOdW1lcmljTGl0ZXJhbChpbm5lci5vcGVyYW5kKSkge1xuXHRcdFx0aWYgKGlubmVyLm9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLk1pbnVzVG9rZW4pIHtcblx0XHRcdFx0Y29uc3QgbmVnYXRpdmUgPSBgLSR7aW5uZXIub3BlcmFuZC50ZXh0fWA7XG5cdFx0XHRcdHJldHVybiBuZWdhdGl2ZTtcblx0XHRcdH1cblx0XHRcdGlmIChpbm5lci5vcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5QbHVzVG9rZW4pIHtcblx0XHRcdFx0cmV0dXJuIGlubmVyLm9wZXJhbmQudGV4dDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc051bWVyaWNMaXRlcmFsKGlubmVyKSkge1xuXHRcdFx0cmV0dXJuIGlubmVyLnRleHQ7XG5cdFx0fVxuXHRcdGlmIChpbm5lci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRyZXR1cm4gJ3RydWUnO1xuXHRcdH1cblx0XHRpZiAoaW5uZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQpIHtcblx0XHRcdHJldHVybiAnZmFsc2UnO1xuXHRcdH1cblx0XHRpZiAoaW5uZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5OdWxsS2V5d29yZCkge1xuXHRcdFx0cmV0dXJuICdudWxsJztcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGMjI6IHRoZSBjb25zdC1hc3NlcnRpb24gY2hlY2sgc2hhcmVkIGJ5IHRoZSB2YWx1ZS1sZXZlbCBhbmRcblx0ICogZGVjbGFyYXRpb24tbGV2ZWwgcGF0aHMg4oCUIGBleHByIGFzIGNvbnN0YCBhbmQgYDxjb25zdD5leHByYCBwYXJzZVxuXHQgKiBpZGVudGljYWxseSAoYSBUeXBlUmVmZXJlbmNlTm9kZSBuYW1lZCAnY29uc3QnKS4gR2VuZXJhbCBgPFQ+ZXhwcmBcblx0ICogYXNzZXJ0aW9ucyBuZXZlciBtYXRjaC5cblx0ICovXG5cdHByaXZhdGUgaXNDb25zdEFzc2VydGlvblR5cGUgKHR5cGU6IHRzLlR5cGVOb2RlKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgY29uc3RBc3NlcnRpb24gPSB0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHR5cGUpICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIodHlwZS50eXBlTmFtZSkgJiZcblx0XHRcdHR5cGUudHlwZU5hbWUudGV4dCA9PT0gJ2NvbnN0Jztcblx0XHRyZXR1cm4gY29uc3RBc3NlcnRpb247XG5cdH1cblxuXHQvKipcblx0ICogVGhlIGFycmF5IGxpdGVyYWwgYmVoaW5kIGEgdmFsdWUtbGV2ZWwgZWxlbWVudCBhY2Nlc3M6IGlubGluZVxuXHQgKiAoYCg8Y29uc3Q+W+KApl0pWzBdYCwgYChb4oCmXSBhcyBjb25zdClbMV1gKSwgcGFyZW50aGVzaXplZCwgb3IgYVxuXHQgKiB0cmFja2VkIG1vZHVsZSBjb25zdCBhcnJheSAoYGNvbnN0IHggPSA8Y29uc3Q+W+KApl1gIC8gYHhbMF1gLCBGMTdcblx0ICogdHJhY2tpbmcpLiBPbmx5IGNvbnN0IGFzc2VydGlvbnMgYXJlIHVud3JhcHBlZCDigJQgZ2VuZXJhbFxuXHQgKiBhc3NlcnRpb25zIHN0YXkgdW5rbm93biAoRjIyIHNjb3BlIGJvdW5kYXJ5KS5cblx0ICovXG5cdHByaXZhdGUgY29uc3RBcnJheUxpdGVyYWxPZiAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5FeHByZXNzaW9uID0gZXhwcjtcblx0XHR3aGlsZSAodHMuaXNQYXJlbnRoZXNpemVkRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0aWYgKHRzLmlzQXJyYXlMaXRlcmFsRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0cmV0dXJuIGN1cnJlbnQ7XG5cdFx0fVxuXHRcdGlmICgodHMuaXNBc0V4cHJlc3Npb24oY3VycmVudCkgfHwgdHMuaXNUeXBlQXNzZXJ0aW9uRXhwcmVzc2lvbihjdXJyZW50KSkgJiZcblx0XHRcdHRoaXMuaXNDb25zdEFzc2VydGlvblR5cGUoY3VycmVudC50eXBlKSkge1xuXHRcdFx0Y29uc3QgaW5uZXIgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0XHRjb25zdCBsaXRlcmFsID0gdHMuaXNBcnJheUxpdGVyYWxFeHByZXNzaW9uKGlubmVyKSA/IGlubmVyIDogdW5kZWZpbmVkO1xuXHRcdFx0cmV0dXJuIGxpdGVyYWw7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudCkpIHtcblx0XHRcdGNvbnN0IHRyYWNrZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChjdXJyZW50LnRleHQpO1xuXHRcdFx0cmV0dXJuIHRyYWNrZWQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRW1pdC10eXBlIGZvciBgdHlwZW9mIG5hbWVgIHdoZW4gYG5hbWVgIGlzIGEgdHJhY2tlZCBjb25zdCBhcnJheTogdGhlXG5cdCAqIHVuaW9uIG9mIGl0cyBlbGVtZW50IGxpdGVyYWwgdHlwZXMgKGAnYWN0aXZlJyB8ICdjbG9zZWQnYCkuIEV2ZXJ5XG5cdCAqIG90aGVyIHR5cGVvZiBzb3VyY2Ug4oCUIG5vbi1hcnJheSBjb25zdHMsIGZ1bmN0aW9ucywgY2xhc3NlcywgbmFtZXMgbm90XG5cdCAqIHRyYWNrZWQgYXQgYWxsIOKAlCB5aWVsZHMgdW5kZWZpbmVkLCBzbyB0aGUgY2FsbGVyIGRlZ3JhZGVzIHRoZSBmaWVsZFxuXHQgKiB0byBgdW5rbm93bmA6IGEgYmFyZSBgdHlwZW9mIG5hbWVgIGVtaXR0ZWQgaW50byB0eXBlcy50cyBoYXMgbm9cblx0ICogaW1wb3J0IHRvIHJlc29sdmUgYWdhaW5zdCBkb3duc3RyZWFtLlxuXHQgKi9cblx0cHJpdmF0ZSB0eXBlT2ZDb25zdEFycmF5VW5pb24gKG5hbWU6IHN0cmluZywgZnJvbUZpbGU6IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJyYXlMaXRlcmFsID0gdGhpcy5maW5kUmVmZXJlbmNlZENvbnN0QXJyYXkobmFtZSwgZnJvbUZpbGUpO1xuXHRcdGlmICghYXJyYXlMaXRlcmFsKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBsaXRlcmFscyA9IHRoaXMubGl0ZXJhbFR5cGVzT2ZBcnJheShhcnJheUxpdGVyYWwpO1xuXHRcdGlmICghbGl0ZXJhbHMpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHVuaW9uID0gbGl0ZXJhbHMuam9pbignIHwgJyk7XG5cdFx0cmV0dXJuIHVuaW9uO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCB0aGUgaW1wb3J0aW5nIGZpbGUncyBuYW1lZC9uYW1lc3BhY2UvZGVmYXVsdCBpbXBvcnQgYmluZGluZ3Mgc29cblx0ICogcmVmZXJlbmNlZC10eXBlIG5hbWVzIHJlc29sdmUgdGhyb3VnaCB0aGUgZmlsZSdzIG93biBpbXBvcnQgc3RhdGVtZW50c1xuXHQgKiAoRjEwKSByYXRoZXIgdGhhbiBhIHByb2dyYW0td2lkZSBuYW1lIG1hcC5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tSZWZlcmVuY2VkVHlwZUltcG9ydCAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNJbXBvcnREZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCB7IG1vZHVsZVNwZWNpZmllciB9ID0gbm9kZTtcblx0XHRpZiAoIXRzLmlzU3RyaW5nTGl0ZXJhbChtb2R1bGVTcGVjaWZpZXIpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGNsYXVzZSA9IG5vZGUuaW1wb3J0Q2xhdXNlO1xuXHRcdGlmICghY2xhdXNlKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0bGV0IGltcG9ydHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoZmlsZVBhdGgpO1xuXHRcdGlmICghaW1wb3J0cykge1xuXHRcdFx0aW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZUltcG9ydD4oKTtcblx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLnNldChmaWxlUGF0aCwgaW1wb3J0cyk7XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0IHsgU2hhcmVkU2hhcGUgfSBmcm9tICfigKYnIC8gaW1wb3J0IHsgU2hhcmVkU2hhcGUgYXMgUyB9IGZyb20gJ+KApidcblx0XHRpZiAoY2xhdXNlLm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lZEltcG9ydHMoY2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2YgY2xhdXNlLm5hbWVkQmluZGluZ3MuZWxlbWVudHMpIHtcblx0XHRcdFx0Y29uc3QgbG9jYWxOYW1lID0gZWxlbWVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IG9yaWdpbmFsTmFtZSA9IGVsZW1lbnQucHJvcGVydHlOYW1lID8gZWxlbWVudC5wcm9wZXJ0eU5hbWUudGV4dCA6IGxvY2FsTmFtZTtcblx0XHRcdFx0aW1wb3J0cy5zZXQobG9jYWxOYW1lLCB7XG5cdFx0XHRcdFx0b3JpZ2luYWxOYW1lLFxuXHRcdFx0XHRcdHNwZWNpZmllciAgIDogbW9kdWxlU3BlY2lmaWVyLnRleHQsXG5cdFx0XHRcdFx0aXNOYW1lc3BhY2UgOiBmYWxzZVxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgKiBhcyBtb2RlbHMgZnJvbSAn4oCmJyDigJQgcmVzb2x2ZWQgd2hlbiBhIHF1YWxpZmllZCBuYW1lXG5cdFx0Ly8gKG1vZGVscy5TaGFyZWRTaGFwZSkgaXMgZW5jb3VudGVyZWRcblx0XHRpZiAoY2xhdXNlLm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lc3BhY2VJbXBvcnQoY2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHRpbXBvcnRzLnNldChjbGF1c2UubmFtZWRCaW5kaW5ncy5uYW1lLnRleHQsIHtcblx0XHRcdFx0b3JpZ2luYWxOYW1lIDogJycsXG5cdFx0XHRcdHNwZWNpZmllciAgICA6IG1vZHVsZVNwZWNpZmllci50ZXh0LFxuXHRcdFx0XHRpc05hbWVzcGFjZSAgOiB0cnVlXG5cdFx0XHR9KTtcblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgU2hhcmVkU2hhcGUgZnJvbSAn4oCmJyAoZGVmYXVsdCBpbXBvcnQpXG5cdFx0aWYgKGNsYXVzZS5uYW1lKSB7XG5cdFx0XHRpbXBvcnRzLnNldChjbGF1c2UubmFtZS50ZXh0LCB7XG5cdFx0XHRcdG9yaWdpbmFsTmFtZSA6ICdkZWZhdWx0Jyxcblx0XHRcdFx0c3BlY2lmaWVyICAgIDogbW9kdWxlU3BlY2lmaWVyLnRleHQsXG5cdFx0XHRcdGlzTmFtZXNwYWNlICA6IGZhbHNlXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIHJlLWV4cG9ydCB3aXJpbmcgKGBleHBvcnQgeyBYIH0gZnJvbSAn4oCmJ2AsIGBleHBvcnQgKiBmcm9tICfigKYnYCxcblx0ICogYGV4cG9ydCB7IFggYXMgWSB9YCkgc28gcmVzb2x1dGlvbiBjYW4gY2hhc2UgYmFycmVscyB0byB0aGUgb3JpZ2luXG5cdCAqIG1vZHVsZS4gTWlycm9ycyBNb2R1bGVHcmFwaEJ1aWxkZXIucmVzb2x2ZU9yaWdpbiwgbmFtZS1iYXNlZCBvbmx5LlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlUmVFeHBvcnQgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzRXhwb3J0RGVjbGFyYXRpb24obm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0Y29uc3QgeyBtb2R1bGVTcGVjaWZpZXIgfSA9IG5vZGU7XG5cdFx0Y29uc3Qgc3BlY2lmaWVyVGV4dCA9IG1vZHVsZVNwZWNpZmllciAmJiB0cy5pc1N0cmluZ0xpdGVyYWwobW9kdWxlU3BlY2lmaWVyKVxuXHRcdFx0PyBtb2R1bGVTcGVjaWZpZXIudGV4dFxuXHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHRpZiAobm9kZS5leHBvcnRDbGF1c2UgJiYgdHMuaXNOYW1lZEV4cG9ydHMobm9kZS5leHBvcnRDbGF1c2UpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2Ygbm9kZS5leHBvcnRDbGF1c2UuZWxlbWVudHMpIHtcblx0XHRcdFx0Y29uc3QgZXhwb3J0ZWROYW1lID0gZWxlbWVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IGxvY2FsTmFtZSA9IGVsZW1lbnQucHJvcGVydHlOYW1lID8gZWxlbWVudC5wcm9wZXJ0eU5hbWUudGV4dCA6IGV4cG9ydGVkTmFtZTtcblx0XHRcdFx0aWYgKHNwZWNpZmllclRleHQpIHtcblx0XHRcdFx0XHQvLyBleHBvcnQgeyBYIH0gZnJvbSAn4oCmJyAvIGV4cG9ydCB7IFggYXMgWSB9IGZyb20gJ+KApidcblx0XHRcdFx0XHRsZXQgcmVFeHBvcnRzID0gdGhpcy5yZWZlcmVuY2VkVHlwZVJlRXhwb3J0cy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0XHRcdGlmICghcmVFeHBvcnRzKSB7XG5cdFx0XHRcdFx0XHRyZUV4cG9ydHMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZVJlRXhwb3J0cy5zZXQoZmlsZVBhdGgsIHJlRXhwb3J0cyk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdHJlRXhwb3J0cy5zZXQoZXhwb3J0ZWROYW1lLCBzcGVjaWZpZXJUZXh0KTtcblx0XHRcdFx0fSBlbHNlIGlmIChsb2NhbE5hbWUgIT09IGV4cG9ydGVkTmFtZSkge1xuXHRcdFx0XHRcdC8vIGV4cG9ydCB7IFggYXMgWSB9IOKAlCBzYW1lLWZpbGUgYWxpYXMgb2YgYSBsb2NhbCBkZWNsYXJhdGlvblxuXHRcdFx0XHRcdGxldCBhbGlhc2VzID0gdGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydEFsaWFzZXMuZ2V0KGZpbGVQYXRoKTtcblx0XHRcdFx0XHRpZiAoIWFsaWFzZXMpIHtcblx0XHRcdFx0XHRcdGFsaWFzZXMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydEFsaWFzZXMuc2V0KGZpbGVQYXRoLCBhbGlhc2VzKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0YWxpYXNlcy5zZXQoZXhwb3J0ZWROYW1lLCBsb2NhbE5hbWUpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0aWYgKG5vZGUuZXhwb3J0Q2xhdXNlICYmIHRzLmlzTmFtZXNwYWNlRXhwb3J0KG5vZGUuZXhwb3J0Q2xhdXNlKSkge1xuXHRcdFx0Ly8gYGV4cG9ydCAqIGFzIG5zIGZyb20gJ+KApidgIOKAlCBhIG5lc3RlZCBtb2R1bGUgbmFtZXNwYWNlOyBtaWRkbGVcblx0XHRcdC8vIHNlZ21lbnRzIG9mIHF1YWxpZmllZCByZWZlcmVuY2VzIChiYXJyZWwuRGVlcC5HYWRnZXQpIGNoYXNlIGl0XG5cdFx0XHRpZiAoc3BlY2lmaWVyVGV4dCkge1xuXHRcdFx0XHRsZXQgc3RhcnMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlU3RhcnMuZ2V0KGZpbGVQYXRoKTtcblx0XHRcdFx0aWYgKCFzdGFycykge1xuXHRcdFx0XHRcdHN0YXJzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0XHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlU3RhcnMuc2V0KGZpbGVQYXRoLCBzdGFycyk7XG5cdFx0XHRcdH1cblx0XHRcdFx0c3RhcnMuc2V0KG5vZGUuZXhwb3J0Q2xhdXNlLm5hbWUudGV4dCwgc3BlY2lmaWVyVGV4dCk7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0aWYgKCFub2RlLmV4cG9ydENsYXVzZSAmJiBzcGVjaWZpZXJUZXh0KSB7XG5cdFx0XHQvLyBleHBvcnQgKiBmcm9tICfigKYnXG5cdFx0XHRsZXQgc3RhcnMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuZ2V0KGZpbGVQYXRoKTtcblx0XHRcdGlmICghc3RhcnMpIHtcblx0XHRcdFx0c3RhcnMgPSBbXTtcblx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydFN0YXJzLnNldChmaWxlUGF0aCwgc3RhcnMpO1xuXHRcdFx0fVxuXHRcdFx0c3RhcnMucHVzaChzcGVjaWZpZXJUZXh0KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIG1vZHVsZSBzcGVjaWZpZXIgZnJvbSBhIGNvbnRhaW5pbmcgZmlsZSB3aXRoIHRoZSBwcm9ncmFtJ3Ncblx0ICogY29tcGlsZXJPcHRpb25zICh0c2NvbmZpZyBgcGF0aHNgLCBleHRlbnNpb25sZXNzIGltcG9ydHMsIGluZGV4IGZpbGVzKS5cblx0ICogTW9kdWxlIHJlc29sdXRpb24gb25seSDigJQgdGhlIG5vLWdldFR5cGVDaGVja2VyKCkgcHJlY2VkZW50IHN0YXlzLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUgKHNwZWNpZmllcjogc3RyaW5nLCBjb250YWluaW5nRmlsZTogc3RyaW5nKTpcblx0XHRSZWZlcmVuY2VkVHlwZVJlc29sdXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGNhY2hlS2V5ID0gYCR7Y29udGFpbmluZ0ZpbGV9Ojoke3NwZWNpZmllcn1gO1xuXHRcdGlmICh0aGlzLnJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbkNhY2hlLmhhcyhjYWNoZUtleSkpIHtcblx0XHRcdGNvbnN0IGNhY2hlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZXNvbHV0aW9uQ2FjaGUuZ2V0KGNhY2hlS2V5KTtcblx0XHRcdHJldHVybiBjYWNoZWQgPT09IHVuZGVmaW5lZCA/IHVuZGVmaW5lZCA6IGNhY2hlZDtcblx0XHR9XG5cblx0XHRjb25zdCByZXNvbHV0aW9uID0gdHMucmVzb2x2ZU1vZHVsZU5hbWUoXG5cdFx0XHRzcGVjaWZpZXIsXG5cdFx0XHRjb250YWluaW5nRmlsZSxcblx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVDb21waWxlck9wdGlvbnMsXG5cdFx0XHR0cy5zeXNcblx0XHQpLnJlc29sdmVkTW9kdWxlO1xuXG5cdFx0Y29uc3QgcmVzdWx0OiBSZWZlcmVuY2VkVHlwZVJlc29sdXRpb24gfCB1bmRlZmluZWQgPSByZXNvbHV0aW9uXG5cdFx0XHQ/IHtcblx0XHRcdFx0cmVzb2x2ZWRQYXRoIDogbm9kZVBhdGgucmVzb2x2ZShyZXNvbHV0aW9uLnJlc29sdmVkRmlsZU5hbWUpLFxuXHRcdFx0XHRpc0V4dGVybmFsICAgOiAhIXJlc29sdXRpb24uaXNFeHRlcm5hbExpYnJhcnlJbXBvcnRcblx0XHRcdH1cblx0XHRcdDogdW5kZWZpbmVkO1xuXG5cdFx0dGhpcy5yZWZlcmVuY2VkVHlwZVJlc29sdXRpb25DYWNoZS5zZXQoY2FjaGVLZXksIHJlc3VsdCk7XG5cdFx0Y29uc3QgZmluYWxSZXN1bHQgPSByZXN1bHQ7XG5cdFx0cmV0dXJuIGZpbmFsUmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIExvb2sgdXAgYSBuYW1lIGluIG9uZSByZXNvbHZlZCBtb2R1bGUsIGNoYXNpbmcgcmUtZXhwb3J0IGJhcnJlbHMgd2l0aCBhXG5cdCAqIGJvdW5kZWQgZGVwdGguIEV4dGVybmFsIChub2RlX21vZHVsZXMpIG1vZHVsZXMgaG9sZCBubyBpbi1wcm9qZWN0XG5cdCAqIGRlY2xhcmF0aW9ucyBhbmQgc3RvcCB0aGUgY2hhc2UuXG5cdCAqL1xuXHRwcml2YXRlIGZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlIChcblx0XHRtb2R1bGVQYXRoOiBzdHJpbmcsXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdGRlcHRoOiBudW1iZXJcblx0KTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKGRlcHRoID4gTUFYX1JFRVhQT1JUX0NIQVNFX0RFUFRIKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IGRlY2xzID0gdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLmdldChtb2R1bGVQYXRoKTtcblx0XHRjb25zdCBkaXJlY3QgPSBkZWNscz8uZ2V0KG5hbWUpO1xuXHRcdGlmIChkaXJlY3QpIHtcblx0XHRcdHJldHVybiBkaXJlY3Q7XG5cdFx0fVxuXHRcdC8vIGV4cG9ydCB7IFggYXMgWSB9IOKAlCByZXNvbHZlIHRocm91Z2ggdGhlIGxvY2FsIG5hbWVcblx0XHRjb25zdCBsb2NhbEFsaWFzID0gdGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydEFsaWFzZXMuZ2V0KG1vZHVsZVBhdGgpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGxvY2FsQWxpYXMpIHtcblx0XHRcdGNvbnN0IGFsaWFzZWQgPSBkZWNscz8uZ2V0KGxvY2FsQWxpYXMpO1xuXHRcdFx0aWYgKGFsaWFzZWQpIHtcblx0XHRcdFx0cmV0dXJuIGFsaWFzZWQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVFeHBvcnRzID0gdGhpcy5yZWZlcmVuY2VkVHlwZVJlRXhwb3J0cy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0Y29uc3QgcmVFeHBvcnRTcGVjaWZpZXIgPSByZUV4cG9ydHM/LmdldChuYW1lKTtcblx0XHRpZiAocmVFeHBvcnRTcGVjaWZpZXIpIHtcblx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUocmVFeHBvcnRTcGVjaWZpZXIsIG1vZHVsZVBhdGgpO1xuXHRcdFx0aWYgKG5leHRSZXNvbHV0aW9uICYmICFuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZShuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIG5hbWUsIGRlcHRoICsgMSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGNvbnN0IHN0YXJzID0gdGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydFN0YXJzLmdldChtb2R1bGVQYXRoKTtcblx0XHRpZiAoc3RhcnMpIHtcblx0XHRcdGZvciAoY29uc3Qgc3RhclNwZWNpZmllciBvZiBzdGFycykge1xuXHRcdFx0XHRjb25zdCBuZXh0UmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKHN0YXJTcGVjaWZpZXIsIG1vZHVsZVBhdGgpO1xuXHRcdFx0XHRpZiAoIW5leHRSZXNvbHV0aW9uIHx8IG5leHRSZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBmb3VuZCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUobmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBuYW1lLCBkZXB0aCArIDEpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSByZWZlcmVuY2VkIHR5cGUgbmFtZSBhcyB1c2VkIGluIGZyb21GaWxlLCBpbXBvcnQtYXdhcmU6XG5cdCAqICAgMS4gdGhlIGZpbGUncyBvd24gaW1wb3J0IHN0YXRlbWVudHMgKHJlbGF0aXZlICsgdHNjb25maWcgcGF0aHMsXG5cdCAqICAgICAgY2hhc2VkIHRocm91Z2ggcmUtZXhwb3J0IGJhcnJlbHMpLFxuXHQgKiAgIDIuIHRoZSBmaWxlJ3MgbG9jYWwgZGVjbGFyYXRpb25zLFxuXHQgKiAgIDMuIHRoZSB1bmlxdWUgc2FtZS1uYW1lZCBkZWNsYXJhdGlvbiBhY3Jvc3Mgc2Nhbm5lZCBmaWxlcy5cblx0ICogUmV0dXJucyB1bmRlZmluZWQgd2hlbiBub3RoaW5nIG1hdGNoZXMgKG9yIHRoZSBtYXRjaCBpcyBhbWJpZ3VvdXMpLFxuXHQgKiBpbiB3aGljaCBjYXNlIHRoZSBjYWxsZXIgZmFsbHMgYmFjayB0byBgdW5rbm93bmAuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIChcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0ZnJvbUZpbGU6IHN0cmluZ1xuXHQpOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHQvLyAxLiB0aGUgZmlsZSdzIG93biBpbXBvcnRzIHdpbiDigJQgYW4gaW1wb3J0IGlzIG5ldmVyIHNoYWRvd2VkIGJ5IGFcblx0XHQvLyBzYW1lLW5hbWVkIGxvY2FsIGRlY2xhcmF0aW9uIGVsc2V3aGVyZSBpbiB0aGUgcHJvZ3JhbSAoRjEwKVxuXHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KGZyb21GaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChpbXBvcnRlZCAmJiAhaW1wb3J0ZWQuaXNOYW1lc3BhY2UpIHtcblx0XHRcdGNvbnN0IHJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShpbXBvcnRlZC5zcGVjaWZpZXIsIGZyb21GaWxlKTtcblx0XHRcdGlmIChyZXNvbHV0aW9uICYmICFyZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKHJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBpbXBvcnRlZC5vcmlnaW5hbE5hbWUsIDApO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyAyLiBsb2NhbCBkZWNsYXJhdGlvbiBpbiB0aGUgcmVmZXJlbmNpbmcgZmlsZSBpdHNlbGZcblx0XHRjb25zdCBsb2NhbCA9IHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscy5nZXQoZnJvbUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGxvY2FsKSB7XG5cdFx0XHRyZXR1cm4gbG9jYWw7XG5cdFx0fVxuXG5cdFx0Ly8gMy4gcHJvZ3JhbS13aWRlIGZhbGxiYWNrLCB1bmlxdWUgZGVjbGFyYXRpb24gb25seSDigJQgYW1iaWd1aXR5IGFuZFxuXHRcdC8vIGFic2VuY2UgYm90aCB5aWVsZCB1bmRlZmluZWQgKHRoZSBjYWxsZXIgZW1pdHMgYHVua25vd25gKS5cblx0XHQvLyBFeHRlcm5hbC9hbWJpZW50IGRlY2xhcmF0aW9ucyAoLmQudHMsIG5vZGVfbW9kdWxlcykgZG8gbm90XG5cdFx0Ly8gcGFydGljaXBhdGU6IGEgdXNlci1sb2NhbCBkZWNsYXJhdGlvbiBhbHdheXMgd2lucyBvdmVyIGFcblx0XHQvLyBwYWNrYWdlLWRlY2xhcmVkIHNhbWUtbmFtZWQgdHlwZSAodGhlIHBsYWluLVRTIHRpZXIgb2YgdGhlXG5cdFx0Ly8gaWRlbnRpdHkgbGF3OyBhbWJpZ3VpdHkgYW1vbmcgdGhlIHJlbWFpbmluZyBkZWNsYXJhdGlvbnMgaXNcblx0XHQvLyB2YWxpZGF0ZWQgc2VwYXJhdGVseSBhcyBhIGhhcmQgZmFpbClcblx0XHRsZXQgdW5pcXVlOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkO1xuXHRcdGxldCBjb3VudCA9IDA7XG5cdFx0Zm9yIChjb25zdCBbIGZpbGVQYXRoLCBkZWNscyBdIG9mIHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscykge1xuXHRcdFx0aWYgKHRoaXMuaXNFeHRlcm5hbERlY2xGaWxlKGZpbGVQYXRoKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGNhbmRpZGF0ZSA9IGRlY2xzLmdldChuYW1lKTtcblx0XHRcdGlmIChjYW5kaWRhdGUpIHtcblx0XHRcdFx0Y291bnQrKztcblx0XHRcdFx0dW5pcXVlID0gY2FuZGlkYXRlO1xuXHRcdFx0XHRpZiAoY291bnQgPiAxKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGNvbnN0IHJlc3VsdCA9IGNvdW50ID09PSAxID8gdW5pcXVlIDogdW5kZWZpbmVkO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0ZXJuYWwvYW1iaWVudCBkZWNsYXJhdGlvbiBmaWxlcyAoLmQudHMsIGFueXRoaW5nIHVuZGVyXG5cdCAqIG5vZGVfbW9kdWxlcykgbmV2ZXIgcGFydGljaXBhdGUgaW4gcGxhaW4tVFMgcmVmZXJlbmNlZC10eXBlXG5cdCAqIHJlc29sdXRpb24gb3IgdGhlIGFtYmlndWl0eSBsYXc6IHRoZXkgYXJlIG5vdCBwcm9qZWN0IHNvdXJjZSwgdGhlXG5cdCAqIENMSSBuZXZlciBhbmFseXplcyB0aGVtLCBhbmQgYSB1c2VyLWxvY2FsIGRlY2xhcmF0aW9uIGFsd2F5cyB3aW5zXG5cdCAqIG92ZXIgYSBwYWNrYWdlLWRlY2xhcmVkIHNhbWUtbmFtZWQgdHlwZS5cblx0ICovXG5cdHByaXZhdGUgaXNFeHRlcm5hbERlY2xGaWxlIChmaWxlOiBzdHJpbmcpOiBib29sZWFuIHtcblx0XHRjb25zdCBleHRlcm5hbCA9IGZpbGUuZW5kc1dpdGgoJy5kLnRzJykgfHxcblx0XHRcdGZpbGUuaW5jbHVkZXMoYCR7bm9kZVBhdGguc2VwfW5vZGVfbW9kdWxlcyR7bm9kZVBhdGguc2VwfWApO1xuXHRcdHJldHVybiBleHRlcm5hbDtcblx0fVxuXG5cdC8qKlxuXHQgKiBQcm9wZXJ0aWVzIG9mIGEgcmVmZXJlbmNlZCBjbGFzcy9pbnRlcmZhY2UvYWxpYXMtb2YtbGl0ZXJhbCBkZWNsYXJhdGlvbixcblx0ICogc2hhcmVkIGJ5IGB0aGlzOmAtcGFyYW1ldGVyIGV4cGFuc2lvbiBhbmQgaW5saW5lIHR5cGUgZW1pc3Npb24uXG5cdCAqIEluaGVyaXRlZCBtZW1iZXJzIGFyZSBpbmNsdWRlZDogdGhlIGV4dGVuZHMgY2hhaW4gaXMgd2Fsa2VkXG5cdCAqIChkZXB0aC1jYXBwZWQsIGN5Y2xlLWd1YXJkZWQpIGFuZCBwYXJlbnQgZmllbGRzIG1lcmdlIGZpcnN0LCB0aGVcblx0ICogZGVjbGFyYXRpb24ncyBvd24gZmllbGRzIG92ZXJyaWRpbmcgb24gbmFtZSBjbGFzaC5cblx0ICovXG5cdHByaXZhdGUgcmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllcyAoZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbik6XG5cdFx0TWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgdmlzaXRlZCA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSB0aGlzLnJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXNJbm5lcihkZWNsLCB2aXNpdGVkLCAwKTtcblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdHByaXZhdGUgcmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllc0lubmVyIChcblx0XHRkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uLFxuXHRcdHZpc2l0ZWQ6IFNldDxzdHJpbmc+LFxuXHRcdGRlcHRoOiBudW1iZXJcblx0KTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3Qgb3duUHJvcGVydGllcyA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cdFx0Y29uc3QgZGVjbE5vZGUgPSBkZWNsLm5vZGUgYXMgdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHRzLkludGVyZmFjZURlY2xhcmF0aW9uO1xuXHRcdGNvbnN0IGRlY2xOYW1lID0gZGVjbE5vZGUubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIoZGVjbE5vZGUubmFtZSkgPyBkZWNsTm9kZS5uYW1lLnRleHQgOiAnJztcblx0XHRjb25zdCB2aXNpdEtleSA9IGAke2RlY2wua2luZH06JHtkZWNsLmZpbGV9OiR7ZGVjbE5hbWV9YDtcblx0XHRpZiAoZGVwdGggPiBNQVhfSEVSSVRBR0VfREVQVEggfHwgdmlzaXRlZC5oYXModmlzaXRLZXkpKSB7XG5cdFx0XHRyZXR1cm4gb3duUHJvcGVydGllcztcblx0XHR9XG5cdFx0dmlzaXRlZC5hZGQodmlzaXRLZXkpO1xuXG5cdFx0aWYgKGRlY2wua2luZCA9PT0gJ2NsYXNzJykge1xuXHRcdFx0Y29uc3QgY2xhc3NQcm9wcyA9IHRoaXMuZXh0cmFjdENsYXNzUHJvcGVydGllcyhkZWNsLm5vZGUgYXMgdHMuQ2xhc3NEZWNsYXJhdGlvbik7XG5cdFx0XHRmb3IgKGNvbnN0IFsgbmFtZSwgaW5mbyBdIG9mIGNsYXNzUHJvcHMpIHtcblx0XHRcdFx0b3duUHJvcGVydGllcy5zZXQobmFtZSwgaW5mbyk7XG5cdFx0XHR9XG5cdFx0fSBlbHNlIGlmIChkZWNsLmtpbmQgPT09ICdpbnRlcmZhY2UnKSB7XG5cdFx0XHRjb25zdCBpZmFjZSA9IGRlY2wubm9kZSBhcyB0cy5JbnRlcmZhY2VEZWNsYXJhdGlvbjtcblx0XHRcdHRoaXMuY29sbGVjdFR5cGVFbGVtZW50UHJvcGVydGllcyhbIC4uLmlmYWNlLm1lbWJlcnMgXSwgb3duUHJvcGVydGllcyk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdGNvbnN0IGFsaWFzVHlwZSA9IChkZWNsLm5vZGUgYXMgdHMuVHlwZUFsaWFzRGVjbGFyYXRpb24pLnR5cGU7XG5cdFx0XHRpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUoYWxpYXNUeXBlKSkge1xuXHRcdFx0XHR0aGlzLmNvbGxlY3RUeXBlRWxlbWVudFByb3BlcnRpZXMoWyAuLi5hbGlhc1R5cGUubWVtYmVycyBdLCBvd25Qcm9wZXJ0aWVzKTtcblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdHJldHVybiBvd25Qcm9wZXJ0aWVzO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIGhlcml0YWdlIG1lcmdlcyBwYXJlbnQgZmllbGRzIGZpcnN0OyB0aGUgZGVjbGFyYXRpb24ncyBvd24gZmllbGRzXG5cdFx0Ly8gb3ZlcnJpZGUgb24gbmFtZSBjbGFzaCAobGF0ZXIgYmFzZXMgb3ZlcnJpZGUgZWFybGllciBvbmVzKVxuXHRcdGNvbnN0IG1lcmdlZCA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cdFx0Zm9yIChjb25zdCBiYXNlRGVjbCBvZiB0aGlzLnJlc29sdmVIZXJpdGFnZURlY2xhcmF0aW9ucyhkZWNsKSkge1xuXHRcdFx0Y29uc3QgYmFzZVByb3BzID0gdGhpcy5yZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzSW5uZXIoYmFzZURlY2wsIHZpc2l0ZWQsIGRlcHRoICsgMSk7XG5cdFx0XHRmb3IgKGNvbnN0IFsgbmFtZSwgaW5mbyBdIG9mIGJhc2VQcm9wcykge1xuXHRcdFx0XHRtZXJnZWQuc2V0KG5hbWUsIGluZm8pO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRmb3IgKGNvbnN0IFsgbmFtZSwgaW5mbyBdIG9mIG93blByb3BlcnRpZXMpIHtcblx0XHRcdG1lcmdlZC5zZXQobmFtZSwgaW5mbyk7XG5cdFx0fVxuXHRcdHJldHVybiBtZXJnZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUHJvcGVydHkgc2lnbmF0dXJlcyBvZiBpbnRlcmZhY2UvYWxpYXMgdHlwZS1saXRlcmFsIG1lbWJlcnMsIGludG9cblx0ICogdGhlIGdpdmVuIG1hcC5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdFR5cGVFbGVtZW50UHJvcGVydGllcyAoXG5cdFx0bWVtYmVyczogcmVhZG9ubHkgdHMuVHlwZUVsZW1lbnRbXSxcblx0XHRwcm9wZXJ0aWVzOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+XG5cdCk6IHZvaWQge1xuXHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIG1lbWJlcnMpIHtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdHByb3BlcnRpZXMuc2V0KHByb3BOYW1lLCB7XG5cdFx0XHRcdFx0bmFtZSAgICAgOiBwcm9wTmFtZSxcblx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogISFtZW1iZXIucXVlc3Rpb25Ub2tlbixcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgdGhlIGhlcml0YWdlIGNsYXVzZSBvZiBhIGNsYXNzIChgZXh0ZW5kcyBCYXNlYCkgb3IgaW50ZXJmYWNlXG5cdCAqIChgZXh0ZW5kcyBBLCBCYCkgdG8gcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9ucyB0aHJvdWdoIHRoZSBTQU1FXG5cdCAqIGltcG9ydC1hd2FyZSBtYWNoaW5lcnkgYXMgcGxhaW4gcmVmZXJlbmNlcyAodGhlIGRlY2xhcmluZyBmaWxlJ3Mgb3duXG5cdCAqIGltcG9ydHMgZmlyc3QsIHRoZW4gaXRzIGxvY2FscywgdGhlbiB0aGUgdW5pcXVlIHByb2dyYW0td2lkZVxuXHQgKiBkZWNsYXJhdGlvbikuIFVucmVzb2x2YWJsZSBvciBleHRlcm5hbCBiYXNlcyB5aWVsZCBub3RoaW5nIOKAlCB0aGVpclxuXHQgKiBpbmhlcml0ZWQgZmllbGRzIHNpbXBseSBzdGF5IGFic2VudCwgc2FtZSBhcyBiZWZvcmUgdGhpcyB3YWxrXG5cdCAqIGV4aXN0ZWQuIE1peGluIGNhbGxzIChgZXh0ZW5kcyBtaXhpbihYKWApIGFuZCBuYW1lc3BhY2UgYWNjZXNzIGFyZVxuXHQgKiBub3QgZm9sbG93ZWQuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVIZXJpdGFnZURlY2xhcmF0aW9ucyAoZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbik6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25bXSB7XG5cdFx0Y29uc3QgeyBoZXJpdGFnZUNsYXVzZXMgfSA9IChkZWNsLm5vZGUgYXMgdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHRzLkludGVyZmFjZURlY2xhcmF0aW9uKTtcblx0XHRpZiAoIWhlcml0YWdlQ2xhdXNlcykge1xuXHRcdFx0cmV0dXJuIFtdO1xuXHRcdH1cblx0XHRjb25zdCBiYXNlczogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbltdID0gW107XG5cdFx0Zm9yIChjb25zdCBjbGF1c2Ugb2YgaGVyaXRhZ2VDbGF1c2VzKSB7XG5cdFx0XHRpZiAoY2xhdXNlLnRva2VuICE9PSB0cy5TeW50YXhLaW5kLkV4dGVuZHNLZXl3b3JkKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBoZXJpdGFnZVR5cGUgb2YgY2xhdXNlLnR5cGVzKSB7XG5cdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGhlcml0YWdlVHlwZS5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGJhc2VOYW1lID0gaGVyaXRhZ2VUeXBlLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdFx0Y29uc3QgYmFzZURlY2wgPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKGJhc2VOYW1lLCBkZWNsLmZpbGUpO1xuXHRcdFx0XHRpZiAoYmFzZURlY2wpIHtcblx0XHRcdFx0XHRiYXNlcy5wdXNoKGJhc2VEZWNsKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBiYXNlcztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4cGFuZCBhIHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbiB0byBhIHNlbGYtY29udGFpbmVkIHR5cGUgc3RyaW5nXG5cdCAqIGZvciBlbWlzc2lvbiBpbnRvIGdlbmVyYXRlZCBmaWxlczogdHlwZSBhbGlhc2VzIHRocm91Z2ggaW5mZXJUeXBlLFxuXHQgKiBjbGFzc2VzIGFuZCBpbnRlcmZhY2VzIHRocm91Z2ggdGhlaXIgKHB1YmxpYywgbm9uLW1ldGhvZCkgZmllbGRzLlxuXHQgKiBOZXN0ZWQgcmVmZXJlbmNlcyByZXNvbHZlIGFnYWluc3QgdGhlIGRlY2xhcmluZyBmaWxlIHdoaWxlIGV4cGFuZGluZy5cblx0ICovXG5cdHByaXZhdGUgZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiAoZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgcmVmZXJlbmNpbmdGaWxlID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9IGRlY2wuZmlsZTtcblx0XHR0cnkge1xuXHRcdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uSW5uZXIoZGVjbCk7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH0gZmluYWxseSB7XG5cdFx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSByZWZlcmVuY2luZ0ZpbGU7XG5cdFx0fVxuXHR9XG5cblx0cHJpdmF0ZSBleHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uSW5uZXIgKGRlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmIChkZWNsLmtpbmQgPT09ICdhbGlhcycpIHtcblx0XHRcdGNvbnN0IGFsaWFzTm9kZSA9IGRlY2wubm9kZSBhcyB0cy5UeXBlQWxpYXNEZWNsYXJhdGlvbjtcblx0XHRcdGNvbnN0IGFsaWFzTmFtZSA9IHRzLmlzSWRlbnRpZmllcihhbGlhc05vZGUubmFtZSkgPyBhbGlhc05vZGUubmFtZS50ZXh0IDogJyc7XG5cdFx0XHRpZiAoYWxpYXNOYW1lICYmIHRoaXMuZXhwYW5kaW5nUmVmZXJlbmNlZEFsaWFzZXMuaGFzKGFsaWFzTmFtZSkpIHtcblx0XHRcdFx0Ly8gU2VsZi1yZWZlcmVudGlhbCBhbGlhcyBjaGFpbiDigJQgYmFpbCBvdXRcblx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdH1cblx0XHRcdGlmIChhbGlhc05hbWUpIHtcblx0XHRcdFx0dGhpcy5leHBhbmRpbmdSZWZlcmVuY2VkQWxpYXNlcy5hZGQoYWxpYXNOYW1lKTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGV4cGFuZGVkID0gdGhpcy5pbmZlclR5cGUoYWxpYXNOb2RlLnR5cGUpO1xuXHRcdFx0aWYgKGFsaWFzTmFtZSkge1xuXHRcdFx0XHR0aGlzLmV4cGFuZGluZ1JlZmVyZW5jZWRBbGlhc2VzLmRlbGV0ZShhbGlhc05hbWUpO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGV4cGFuZGVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IGRlY2xQcm9wZXJ0aWVzID0gdGhpcy5yZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzKGRlY2wpO1xuXHRcdGNvbnN0IHByb3BzID0gQXJyYXkuZnJvbShkZWNsUHJvcGVydGllcy5lbnRyaWVzKCkpLm1hcCgoWyBwcm9wTmFtZSwgaW5mbyBdKSA9PiB7XG5cdFx0XHRjb25zdCBvcHRpb25hbCA9IGluZm8ub3B0aW9uYWwgPyAnPycgOiAnJztcblx0XHRcdHJldHVybiBgJHtwcm9wTmFtZX0ke29wdGlvbmFsfTogJHtpbmZvLnR5cGV9YDtcblx0XHR9KTtcblxuXHRcdGNvbnN0IHJlc3VsdCA9IGB7ICR7cHJvcHMuam9pbignOyAnKX0gfWA7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgc2ltcGxlIChub24tcXVhbGlmaWVkKSB0eXBlIHJlZmVyZW5jZTogaW1wb3J0LWF3YXJlXG5cdCAqIGRlY2xhcmF0aW9uIGV4cGFuc2lvbiBmaXJzdCwgdGhlbiB0aGUgSW5zdGFuY2VUeXBlPHR5cGVvZiBYPiBwYXR0ZXJuLFxuXHQgKiB0aGVuIG1uZW1vbmljYSBncmFwaCB0eXBlczsga25vd24gZ2xvYmFscyBrZWVwIHRoZWlyIGJhcmUgbmFtZSBhbmRcblx0ICogYW55dGhpbmcgZWxzZSBmYWxscyBiYWNrIHRvIGB1bmtub3duYCBzbyBnZW5lcmF0ZWQgZmlsZXMgbmV2ZXIgY2Fycnlcblx0ICogYW4gdW5yZXNvbHZhYmxlIGJhcmUgbmFtZS4gUmV0dXJucyB1bmRlZmluZWQgd2hlbiB0aGUgY2FsbGVyIHNob3VsZFxuXHQgKiBrZWVwIHRoZSBnZW5lcmljIHNwZWxsaW5nIChoYW5kbGVkIHNlcGFyYXRlbHkpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlU2ltcGxlVHlwZVJlZmVyZW5jZSAoXG5cdFx0dHlwZU5hbWU6IHN0cmluZyxcblx0XHR0eXBlQXJncz86IHRzLk5vZGVBcnJheTx0cy5UeXBlTm9kZT4sXG5cdFx0cmVmTm9kZT86IHRzLk5vZGVcblx0KTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBJbXBvcnQtYXdhcmUgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9uIChGMTApXG5cdFx0Y29uc3QgZGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24odHlwZU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0aWYgKGRlY2wpIHtcblx0XHRcdGNvbnN0IGV4cGFuZGVkID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKGRlY2wpO1xuXHRcdFx0aWYgKGV4cGFuZGVkICE9PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0cmV0dXJuIGV4cGFuZGVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgdW5rbm93blJlc3VsdCA9ICd1bmtub3duJztcblx0XHRcdHJldHVybiB1bmtub3duUmVzdWx0O1xuXHRcdH1cblxuXHRcdC8vIEluc3RhbmNlVHlwZTx0eXBlb2YgWD4gbGF3ICgwLjIuMCBiZWhhdmlvciwgcmVzdG9yZWQpOiB0aGVcblx0XHQvLyBnZW5lcmF0ZWQgYWxpYXMgYWxyZWFkeSBJUyB0aGUgaW5zdGFuY2UgdHlwZSDigJQgcmVzb2x2ZSBYIHRocm91Z2hcblx0XHQvLyB0aGUgZ3JhcGggdGllcnMgYW5kIGRyb3AgdGhlIHdyYXBwZXIuIE11c3QgcnVuIEJFRk9SRSB0aGUgZ3JhcGhcblx0XHQvLyByZXNvbHV0aW9uOiAnSW5zdGFuY2VUeXBlJyBpcyBhbiBhbWJpZW50IGdsb2JhbCwgbmV2ZXIgYSBncmFwaFxuXHRcdC8vIHR5cGUgKHRoZSBvbGQgc3BlY2lhbCBjYXNlIGJlbG93IHNhdCBpbnNpZGUgdGhlIGdyYXBoLXVuaXF1ZVxuXHRcdC8vIGJyYW5jaCBhbmQgd2FzIGRlYWQgY29kZSkuIFdoZW4gWCBkb2VzIG5vdCByZXNvbHZlLCB0aGUgV0hPTEVcblx0XHQvLyBleHByZXNzaW9uIGRlZ3JhZGVzIHRvIGB1bmtub3duYCDigJQgbmV2ZXIgZW1pdFxuXHRcdC8vIGBJbnN0YW5jZVR5cGU8dW5rbm93bj5gOiBpbnZhbGlkIFRTIChUUzIzNDQsICd1bmtub3duJyBkb2VzIG5vdFxuXHRcdC8vIHNhdGlzZnkgdGhlIGNvbnN0cnVjdG9yIGNvbnN0cmFpbnQpLiBSZWFjaGVkIGRpcmVjdGx5IG9yIHRocm91Z2hcblx0XHQvLyBhIGxvY2FsIGFsaWFzIChgWEluc3RhbmNlID0gSW5zdGFuY2VUeXBlPHR5cGVvZiBYPmApLlxuXHRcdGlmICh0eXBlTmFtZSA9PT0gJ0luc3RhbmNlVHlwZScgJiYgdHlwZUFyZ3MgJiYgdHlwZUFyZ3MubGVuZ3RoID09PSAxKSB7XG5cdFx0XHRjb25zdCBbIGluc3RhbmNlQXJnIF0gPSB0eXBlQXJncztcblx0XHRcdGlmIChpbnN0YW5jZUFyZyAmJiB0cy5pc1R5cGVRdWVyeU5vZGUoaW5zdGFuY2VBcmcpICYmIHRzLmlzSWRlbnRpZmllcihpbnN0YW5jZUFyZy5leHByTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcXVlcnlSZXN1bHQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKGluc3RhbmNlQXJnLmV4cHJOYW1lLnRleHQpO1xuXHRcdFx0XHRpZiAocXVlcnlSZXN1bHQuc3RhdHVzID09PSAndW5pcXVlJykge1xuXHRcdFx0XHRcdGNvbnN0IGFsaWFzUmVzdWx0ID0gcXVlcnlSZXN1bHQubm9kZS5mdWxsUGF0aC5yZXBsYWNlKC9cXC4vZywgJ18nKTtcblx0XHRcdFx0XHRyZXR1cm4gYWxpYXNSZXN1bHQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKHF1ZXJ5UmVzdWx0LnN0YXR1cyA9PT0gJ2FtYmlndW91cycpIHtcblx0XHRcdFx0XHR0aGlzLnJlY29yZEdyYXBoUmVmZXJlbmNlRXJyb3IoaW5zdGFuY2VBcmcuZXhwck5hbWUudGV4dCwgaW5zdGFuY2VBcmcsIHF1ZXJ5UmVzdWx0KTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBkZWdyYWRlZFJlc3VsdCA9ICd1bmtub3duJztcblx0XHRcdFx0cmV0dXJuIGRlZ3JhZGVkUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgaW5mZXJyZWRBcmcgPSB0aGlzLmluZmVyVHlwZShpbnN0YW5jZUFyZyk7XG5cdFx0XHRpZiAoaW5mZXJyZWRBcmcgPT09ICd1bmtub3duJykge1xuXHRcdFx0XHRjb25zdCBkZWdyYWRlZFdyYXBwZXIgPSAndW5rbm93bic7XG5cdFx0XHRcdHJldHVybiBkZWdyYWRlZFdyYXBwZXI7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCB3cmFwcGVkUmVzdWx0ID0gYEluc3RhbmNlVHlwZTwke2luZmVycmVkQXJnfT5gO1xuXHRcdFx0cmV0dXJuIHdyYXBwZWRSZXN1bHQ7XG5cdFx0fVxuXG5cdFx0Ly8gTW5lbW9uaWNhLWdyYXBoIGlkZW50aXR5IGxhdzogcGF0aC1hd2FyZSByZXNvbHV0aW9uICh2YWx1ZSBzY29wZSxcblx0XHQvLyBpbXBvcnRzLCBuZWFyZXN0LWNoYWluLCByb290LCBwcm9ncmFtLXdpZGUpLiBBbWJpZ3VpdHkgYmV0d2VlblxuXHRcdC8vIHJlYWwgZ3JhcGggdHlwZXMgaXMgYSBoYXJkIGZhaWx1cmU7IGEgbmFtZSBubyBncmFwaCB0eXBlIGNhcnJpZXNcblx0XHQvLyBzdGF5cyBpbiB0aGUgcGxhaW4tVFMgc29mdCBzY29wZSBhbmQgZmFsbHMgdG8gYHVua25vd25gLlxuXHRcdGNvbnN0IGdyYXBoUmVzdWx0ID0gdGhpcy5yZXNvbHZlR3JhcGhUeXBlTmFtZSh0eXBlTmFtZSk7XG5cdFx0aWYgKGdyYXBoUmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdC8vIEhhbmRsZSBJbnN0YW5jZVR5cGU8dHlwZW9mIFg+IHBhdHRlcm4gLT4gY29udmVydCB0byBQYXJlbnRfWFxuXHRcdFx0aWYgKHR5cGVOYW1lID09PSAnSW5zdGFuY2VUeXBlJyAmJiB0eXBlQXJncyAmJiB0eXBlQXJncy5sZW5ndGggPT09IDEpIHtcblx0XHRcdFx0Y29uc3QgWyBhcmcgXSA9IHR5cGVBcmdzO1xuXHRcdFx0XHRpZiAoYXJnLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVHlwZVF1ZXJ5KSB7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZVF1ZXJ5ID0gYXJnIGFzIHRzLlR5cGVRdWVyeU5vZGU7XG5cdFx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcih0eXBlUXVlcnkuZXhwck5hbWUpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBxdWVyeVJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUodHlwZVF1ZXJ5LmV4cHJOYW1lLnRleHQpO1xuXHRcdFx0XHRcdFx0aWYgKHF1ZXJ5UmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdFx0XHRcdFx0Ly8gQ29udmVydCBmdWxsIHBhdGggd2l0aCBkb3RzIHRvIHVuZGVyc2NvcmVzOiBVc2FnZXMuVXNhZ2VFbnRyeSAtPiBVc2FnZXNfVXNhZ2VFbnRyeVxuXHRcdFx0XHRcdFx0XHRyZXR1cm4gcXVlcnlSZXN1bHQubm9kZS5mdWxsUGF0aC5yZXBsYWNlKC9cXC4vZywgJ18nKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdGlmIChxdWVyeVJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHRcdFx0XHRcdHRoaXMucmVjb3JkR3JhcGhSZWZlcmVuY2VFcnJvcih0eXBlUXVlcnkuZXhwck5hbWUudGV4dCwgdHlwZVF1ZXJ5LCBxdWVyeVJlc3VsdCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHQvLyBOb3QgYSBrbm93biBtbmVtb25pY2EgdHlwZSDigJQgbm8gYmFyZSBlbWlzc2lvblxuXHRcdFx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGlmICghdHlwZUFyZ3MgfHwgdHlwZUFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRcdC8vIENvbnZlcnQgZnVsbCBwYXRoIHdpdGggZG90cyB0byB1bmRlcnNjb3JlczogVXNhZ2VzLlVzYWdlRW50cnkgLT4gVXNhZ2VzX1VzYWdlRW50cnlcblx0XHRcdFx0cmV0dXJuIGdyYXBoUmVzdWx0Lm5vZGUuZnVsbFBhdGgucmVwbGFjZSgvXFwuL2csICdfJyk7XG5cdFx0XHR9XG5cdFx0XHQvLyBHZW5lcmljIHVzZSBvZiBhIGdyYXBoIHR5cGUga2VlcHMgaXRzIHNpbXBsZSBuYW1lOyB0aGVcblx0XHRcdC8vIGdlbmVyYXRvciB1cGdyYWRlcyBpdCB0byB0aGUgZnVsbC1wYXRoIGluc3RhbmNlIHR5cGUgbmFtZVxuXHRcdFx0cmV0dXJuIGAke3R5cGVOYW1lfTwke3R5cGVBcmdzLm1hcChhID0+IHRoaXMuaW5mZXJUeXBlKGEpKS5qb2luKCcsICcpfT5gO1xuXHRcdH1cblx0XHRpZiAoZ3JhcGhSZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0dGhpcy5yZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yKHR5cGVOYW1lLCByZWZOb2RlID8/IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSwgZ3JhcGhSZXN1bHQpO1xuXHRcdH1cblxuXHRcdGlmICh0eXBlQXJncyAmJiB0eXBlQXJncy5sZW5ndGggPiAwKSB7XG5cdFx0XHRpZiAoS05PV05fR0xPQkFMX1RZUEVTLmhhcyh0eXBlTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgZ2VuZXJpY1Jlc3VsdCA9IGAke3R5cGVOYW1lfTwke3R5cGVBcmdzLm1hcChhID0+IHRoaXMuaW5mZXJUeXBlKGEpKS5qb2luKCcsICcpfT5gO1xuXHRcdFx0XHRyZXR1cm4gZ2VuZXJpY1Jlc3VsdDtcblx0XHRcdH1cblx0XHRcdC8vIEVtaXNzaW9uIHJlc3RvcmF0aW9uICgwLjIuMCBiZWhhdmlvcik6IGEgbm9uLWdyYXBoIG91dGVyXG5cdFx0XHQvLyBnZW5lcmljIHRoYXQgaXMgTk9UIGRlY2xhcmVkIGluIGFueSBhbmFseXplZCBwcm9qZWN0IGZpbGUgaXNcblx0XHRcdC8vIGFuIGFtYmllbnQvbGliIGNvbnN0cnVjdCAoTWFwSXRlcmF0b3IsIGxpYiBoZWxwZXJzKSDigJQgaXRcblx0XHRcdC8vIHJlc29sdmVzIGluIGV2ZXJ5IGNvbnN1bWVyIGNvbXBpbGF0aW9uIHdpdGhvdXQgYW4gaW1wb3J0LCBzb1xuXHRcdFx0Ly8gZW1pdCBpdCBWRVJCQVRJTSB3aXRoIGlubmVyIGdyYXBoIGFsaWFzZXMgcmVzb2x2ZWQuIEEgbmFtZVxuXHRcdFx0Ly8gZGVjbGFyZWQgaW4gcHJvamVjdCBmaWxlcyBzdGF5cyB1bmtub3duOiB0aGUgc2VsZi1jb250YWluZWRcblx0XHRcdC8vIHR5cGVzLnRzIGNhbiBjYXJyeSBuZWl0aGVyIHRoZSBiYXJlIG5hbWUgbm9yIGFuIGltcG9ydC5cblx0XHRcdGlmICghdGhpcy5pc1Byb2plY3REZWNsYXJlZFR5cGVOYW1lKHR5cGVOYW1lKSkge1xuXHRcdFx0XHRjb25zdCB2ZXJiYXRpbVJlc3VsdCA9IGAke3R5cGVOYW1lfTwke3R5cGVBcmdzLm1hcChhID0+IHRoaXMuaW5mZXJUeXBlKGEpKS5qb2luKCcsICcpfT5gO1xuXHRcdFx0XHRyZXR1cm4gdmVyYmF0aW1SZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBHZW5lcmljIHJlZmVyZW5jZSB0byBhIG5vbi1nbG9iYWwsIG5vbi1ncmFwaCBQUk9KRUNULUxPQ0FMXG5cdFx0XHQvLyB0eXBlIGNhbm5vdCBiZSBlbWl0dGVkIGJhcmUgaW50byB0aGUgZ2VuZXJhdGVkIGZpbGVcblx0XHRcdGlmIChyZWZOb2RlKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSh0eXBlTmFtZSwgcmVmTm9kZSk7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZhbGxiYWNrUmVzdWx0ID0gdGhpcy51bnJlc29sdmVkVHlwZVJlZmVyZW5jZUZhbGxiYWNrKHR5cGVOYW1lLCByZWZOb2RlKTtcblx0XHRyZXR1cm4gZmFsbGJhY2tSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHF1YWxpZmllZCB0eXBlIHJlZmVyZW5jZSAobW9kZWxzLklubmVyLkNyYXRlKSB0aHJvdWdoIHRoZVxuXHQgKiBjdXJyZW50IGZpbGUncyBuYW1lc3BhY2UgaW1wb3J0cy4gVGhlIGNoYWluJ3MgaGVhZCBtdXN0IGJlIGEgbmFtZXNwYWNlXG5cdCAqIGltcG9ydDsgbWlkZGxlIHNlZ21lbnRzIGRlc2NlbmQgdGhyb3VnaCBuYW1lc3BhY2UgZGVjbGFyYXRpb25zLCBuYW1lZFxuXHQgKiByZS1leHBvcnRzIG9mIG5hbWVzcGFjZXMsIGFuZCBgZXhwb3J0ICogYXMgbnMgZnJvbSAn4oCmJ2AgYmFycmVscyAoZWFjaFxuXHQgKiBzZWdtZW50IGNvbnN1bWVkIGV4YWN0bHkgb25jZSwgc28gdGhlIHdhbGsgY2Fubm90IGN5Y2xlKTsgdGhlIGZpbmFsXG5cdCAqIHNlZ21lbnQgcmVzb2x2ZXMgdG8gYSBkZWNsYXJhdGlvbiB3aGljaCBpcyBleHBhbmRlZCBpbmxpbmUuIFdoZW4gdGhlXG5cdCAqIHByZWNpc2Ugd2FsayBmaW5kcyBub3RoaW5nLCB0aGUgbGVnYWN5IHJpZ2h0bW9zdC1uYW1lIGxvb2t1cCBpbiB0aGVcblx0ICogaGVhZCBtb2R1bGUga2VlcHMgb25lLWxldmVsIGZvcm1zIChtb2RlbHMuVHlwZSkgd29ya2luZyDigJQgbmVzdGVkXG5cdCAqIGRlY2xhcmF0aW9ucyBhcmUgcmVjb3JkZWQgYnkgcGxhaW4gbmFtZSB0aGVyZSB0b28uIFJldHVybnMgdW5kZWZpbmVkXG5cdCAqIHdoZW4gdGhlIGhlYWQgaXMgbm90IGEgbmFtZXNwYWNlIGltcG9ydCBvciBub3RoaW5nIHJlc29sdmVzLlxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlclF1YWxpZmllZFR5cGVSZWZlcmVuY2UgKHR5cGVSZWY6IHRzLlR5cGVSZWZlcmVuY2VOb2RlKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIXRzLmlzUXVhbGlmaWVkTmFtZSh0eXBlUmVmLnR5cGVOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBmbGF0dGVuIHRoZSBxdWFsaWZpZWQgbmFtZSBjaGFpbjogbW9kZWxzLklubmVyLkNyYXRlIOKGkiBbJ21vZGVscycsICdJbm5lcicsICdDcmF0ZSddXG5cdFx0Y29uc3Qgc2VnbWVudHM6IHN0cmluZ1tdID0gW107XG5cdFx0bGV0IGNoYWluOiB0cy5FbnRpdHlOYW1lID0gdHlwZVJlZi50eXBlTmFtZTtcblx0XHR3aGlsZSAodHMuaXNRdWFsaWZpZWROYW1lKGNoYWluKSkge1xuXHRcdFx0c2VnbWVudHMudW5zaGlmdChjaGFpbi5yaWdodC50ZXh0KTtcblx0XHRcdGNoYWluID0gY2hhaW4ubGVmdDtcblx0XHR9XG5cdFx0c2VnbWVudHMudW5zaGlmdChjaGFpbi50ZXh0KTtcblxuXHRcdGNvbnN0IG5hbWVzcGFjZUltcG9ydCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQoc2VnbWVudHNbIDAgXSk7XG5cdFx0aWYgKCFuYW1lc3BhY2VJbXBvcnQgfHwgIW5hbWVzcGFjZUltcG9ydC5pc05hbWVzcGFjZSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUobmFtZXNwYWNlSW1wb3J0LnNwZWNpZmllciwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRpZiAoIXJlc29sdXRpb24gfHwgcmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIGRlc2NlbmQgdGhlIG1pZGRsZSBzZWdtZW50czogYSBtb2R1bGUgY29udGV4dCByZXNvbHZlcyB0aGUgc2VnbWVudFxuXHRcdC8vIGFzIGEgbmFtZXNwYWNlIGRlY2xhcmF0aW9uIC8gbmFtZXNwYWNlIHJlLWV4cG9ydDsgYSBuYW1lc3BhY2UtYmxvY2tcblx0XHQvLyBjb250ZXh0IHJlc29sdmVzIGl0IGFzIGEgbmVzdGVkIG5hbWVzcGFjZSBkZWNsYXJhdGlvblxuXHRcdGxldCBxdWFsaWZpZXI6IHsgbW9kdWxlUGF0aDogc3RyaW5nOyBibG9jaz86IHRzLk1vZHVsZUJsb2NrIH0gfCB1bmRlZmluZWQgPSB7XG5cdFx0XHRtb2R1bGVQYXRoIDogcmVzb2x1dGlvbi5yZXNvbHZlZFBhdGhcblx0XHR9O1xuXHRcdGZvciAobGV0IGkgPSAxOyBpIDwgc2VnbWVudHMubGVuZ3RoIC0gMSAmJiBxdWFsaWZpZXI7IGkrKykge1xuXHRcdFx0Y29uc3Qgc2VnbWVudCA9IHNlZ21lbnRzWyBpIF07XG5cdFx0XHRpZiAocXVhbGlmaWVyLmJsb2NrKSB7XG5cdFx0XHRcdGNvbnN0IG5lc3RlZCA9IHRoaXMuZmluZE5hbWVzcGFjZUluQmxvY2socXVhbGlmaWVyLmJsb2NrLCBzZWdtZW50KTtcblx0XHRcdFx0aWYgKG5lc3RlZD8uYm9keSAmJiB0cy5pc01vZHVsZUJsb2NrKG5lc3RlZC5ib2R5KSkge1xuXHRcdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IHF1YWxpZmllci5tb2R1bGVQYXRoLCBibG9jayA6IG5lc3RlZC5ib2R5IH07XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0cXVhbGlmaWVyID0gdW5kZWZpbmVkO1xuXHRcdFx0XHRicmVhaztcblx0XHRcdH1cblx0XHRcdGNvbnN0IG5hbWVzcGFjZURlY2w6IHRzLk1vZHVsZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkID1cblx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMuZ2V0KHF1YWxpZmllci5tb2R1bGVQYXRoKT8uZ2V0KHNlZ21lbnQpO1xuXHRcdFx0aWYgKG5hbWVzcGFjZURlY2w/LmJvZHkgJiYgdHMuaXNNb2R1bGVCbG9jayhuYW1lc3BhY2VEZWNsLmJvZHkpKSB7XG5cdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IHF1YWxpZmllci5tb2R1bGVQYXRoLCBibG9jayA6IG5hbWVzcGFjZURlY2wuYm9keSB9O1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHN0YXJTcGVjaWZpZXIgPSB0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlU3RhcnMuZ2V0KHF1YWxpZmllci5tb2R1bGVQYXRoKT8uZ2V0KHNlZ21lbnQpO1xuXHRcdFx0aWYgKHN0YXJTcGVjaWZpZXIpIHtcblx0XHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShzdGFyU3BlY2lmaWVyLCBxdWFsaWZpZXIubW9kdWxlUGF0aCk7XG5cdFx0XHRcdGlmIChuZXh0UmVzb2x1dGlvbiAmJiAhbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCB9O1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRjb25zdCByZUV4cG9ydFNwZWNpZmllciA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuZ2V0KHF1YWxpZmllci5tb2R1bGVQYXRoKT8uZ2V0KHNlZ21lbnQpO1xuXHRcdFx0aWYgKHJlRXhwb3J0U3BlY2lmaWVyKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUocmVFeHBvcnRTcGVjaWZpZXIsIHF1YWxpZmllci5tb2R1bGVQYXRoKTtcblx0XHRcdFx0Y29uc3QgcmVFeHBvcnRlZDogdHMuTW9kdWxlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQgPVxuXHRcdFx0XHRcdG5leHRSZXNvbHV0aW9uICYmICFuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsXG5cdFx0XHRcdFx0XHQ/IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzLmdldChuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgpPy5nZXQoc2VnbWVudClcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0XHRpZiAocmVFeHBvcnRlZD8uYm9keSAmJiB0cy5pc01vZHVsZUJsb2NrKHJlRXhwb3J0ZWQuYm9keSkpIHtcblx0XHRcdFx0XHRxdWFsaWZpZXIgPSB7IG1vZHVsZVBhdGggOiBuZXh0UmVzb2x1dGlvbiEucmVzb2x2ZWRQYXRoLCBibG9jayA6IHJlRXhwb3J0ZWQuYm9keSB9O1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRxdWFsaWZpZXIgPSB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmluYWxOYW1lID0gc2VnbWVudHNbIHNlZ21lbnRzLmxlbmd0aCAtIDEgXTtcblx0XHRsZXQgZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZDtcblx0XHRpZiAocXVhbGlmaWVyPy5ibG9jaykge1xuXHRcdFx0ZGVjbCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5CbG9jayhxdWFsaWZpZXIuYmxvY2ssIHF1YWxpZmllci5tb2R1bGVQYXRoLCBmaW5hbE5hbWUpO1xuXHRcdH0gZWxzZSBpZiAocXVhbGlmaWVyKSB7XG5cdFx0XHRkZWNsID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZShxdWFsaWZpZXIubW9kdWxlUGF0aCwgZmluYWxOYW1lLCAwKTtcblx0XHR9XG5cdFx0Ly8gbGVnYWN5IGZhbGxiYWNrOiByaWdodG1vc3QgbmFtZSBhbnl3aGVyZSBpbiB0aGUgaGVhZCBtb2R1bGVcblx0XHQvLyAobmFtZXNwYWNlLW5lc3RlZCBkZWNsYXJhdGlvbnMgYXJlIGFsc28gcmVjb3JkZWQgYnkgcGxhaW4gbmFtZSlcblx0XHRpZiAoIWRlY2wpIHtcblx0XHRcdGRlY2wgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKHJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBmaW5hbE5hbWUsIDApO1xuXHRcdH1cblx0XHRpZiAoIWRlY2wpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oZGVjbCk7XG5cdFx0cmV0dXJuIGV4cGFuZGVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpbmQgYSBuYW1lc3BhY2UgZGVjbGFyYXRpb24gYnkgbmFtZSBkaXJlY3RseSBpbnNpZGUgYSBtb2R1bGUgYmxvY2suXG5cdCAqL1xuXHRwcml2YXRlIGZpbmROYW1lc3BhY2VJbkJsb2NrIChibG9jazogdHMuTW9kdWxlQmxvY2ssIG5hbWU6IHN0cmluZyk6IHRzLk1vZHVsZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRmb3IgKGNvbnN0IHN0YXRlbWVudCBvZiBibG9jay5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAodHMuaXNNb2R1bGVEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmIHRzLmlzSWRlbnRpZmllcihzdGF0ZW1lbnQubmFtZSkgJiZcblx0XHRcdFx0c3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZSkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQgPSBzdGF0ZW1lbnQ7XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmluZCBhIG5hbWVkIHR5cGUgZGVjbGFyYXRpb24gKGFsaWFzLCBjbGFzcywgaW50ZXJmYWNlKSBkaXJlY3RseSBpbnNpZGVcblx0ICogYSBuYW1lc3BhY2UgYmxvY2sg4oCUIHRoZSBmaW5hbCBzZWdtZW50IG9mIGEgZGVzY2VuZGVkIHF1YWxpZmllZCBjaGFpbi5cblx0ICovXG5cdHByaXZhdGUgZmluZFJlZmVyZW5jZWRUeXBlSW5CbG9jayAoXG5cdFx0YmxvY2s6IHRzLk1vZHVsZUJsb2NrLFxuXHRcdGZpbGVQYXRoOiBzdHJpbmcsXG5cdFx0bmFtZTogc3RyaW5nXG5cdCk6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIGJsb2NrLnN0YXRlbWVudHMpIHtcblx0XHRcdGlmICh0cy5pc1R5cGVBbGlhc0RlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiYgdHMuaXNJZGVudGlmaWVyKHN0YXRlbWVudC5uYW1lKSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiA9IHsga2luZCA6ICdhbGlhcycsIG5vZGUgOiBzdGF0ZW1lbnQsIGZpbGUgOiBmaWxlUGF0aCB9O1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmIHN0YXRlbWVudC5uYW1lICYmIHN0YXRlbWVudC5uYW1lLnRleHQgPT09IG5hbWUpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0OiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uID0geyBraW5kIDogJ2NsYXNzJywgbm9kZSA6IHN0YXRlbWVudCwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNJbnRlcmZhY2VEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmIHRzLmlzSWRlbnRpZmllcihzdGF0ZW1lbnQubmFtZSkgJiZcblx0XHRcdFx0c3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZSkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQ6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gPSB7IGtpbmQgOiAnaW50ZXJmYWNlJywgbm9kZSA6IHN0YXRlbWVudCwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmFsbGJhY2sgZm9yIGEgdHlwZS1yZWZlcmVuY2UgbmFtZSB0aGF0IHJlc29sdmVzIHRvIG5vIGRlY2xhcmF0aW9uIGFuZFxuXHQgKiBubyBncmFwaCB0eXBlOiBrbm93biBnbG9iYWxzIGtlZXAgdGhlaXIgYmFyZSBuYW1lICh0aGV5IHJlc29sdmUgd2l0aG91dFxuXHQgKiBhbiBpbXBvcnQpOyBldmVyeXRoaW5nIGVsc2UgYmVjb21lcyBgdW5rbm93bmAgc28gZ2VuZXJhdGVkIHR5cGVzLnRzXG5cdCAqIG5ldmVyIGNhcnJpZXMgYW4gdW5yZXNvbHZhYmxlIGJhcmUgbmFtZSAoUkVBRE1FJ3MgZG9jdW1lbnRlZCBiZWhhdmlvcilcblx0ICogYW5kIHRoZSBzaXRlIGlzIHJlY29yZGVkIGZvciB0aGUgcGxhaW4tVFMgYW1iaWd1aXR5IHZhbGlkYXRpb24uXG5cdCAqL1xuXHRwcml2YXRlIHVucmVzb2x2ZWRUeXBlUmVmZXJlbmNlRmFsbGJhY2sgKHR5cGVOYW1lOiBzdHJpbmcsIHJlZk5vZGU/OiB0cy5Ob2RlKTogc3RyaW5nIHtcblx0XHRpZiAoS05PV05fR0xPQkFMX1RZUEVTLmhhcyh0eXBlTmFtZSkpIHtcblx0XHRcdHJldHVybiB0eXBlTmFtZTtcblx0XHR9XG5cdFx0aWYgKHJlZk5vZGUpIHtcblx0XHRcdHRoaXMucmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSh0eXBlTmFtZSwgcmVmTm9kZSk7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9ICd1bmtub3duJztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBvbmUgZGVmaW5lKCkvbGF6eSgpL0BkZWNvcmF0ZSgpIHNpdGUgdW5kZXIgaXRzIHJ1bnRpbWVcblx0ICogbmFtZXNwYWNlIGtleS4gVHdvIHNpdGVzIGluIG9uZSBuYW1lc3BhY2UgYXJlIGEgc2FtZS1uYW1lc3BhY2Vcblx0ICogZHVwbGljYXRlICh0aGUgcnVudGltZSB0aHJvd3MgQUxSRUFEWV9ERUNMQVJFRCk7IGV2ZXJ5IHNpdGUgaXMga2VwdFxuXHQgKiBzbyB0aGUgZmFpbHVyZSBjYW4gcmVwb3J0IGFsbCBsb2NhdGlvbnMuXG5cdCAqL1xuXHRwcml2YXRlIHJlY29yZERlZmluZVNpdGUgKG5hbWVzcGFjZUtleTogc3RyaW5nLCBsb2NhdGlvbjogc3RyaW5nKTogdm9pZCB7XG5cdFx0bGV0IHNpdGVzID0gdGhpcy5kZWZpbmVTaXRlcy5nZXQobmFtZXNwYWNlS2V5KTtcblx0XHRpZiAoIXNpdGVzKSB7XG5cdFx0XHRzaXRlcyA9IFtdO1xuXHRcdFx0dGhpcy5kZWZpbmVTaXRlcy5zZXQobmFtZXNwYWNlS2V5LCBzaXRlcyk7XG5cdFx0fVxuXHRcdGlmICghc2l0ZXMuaW5jbHVkZXMobG9jYXRpb24pKSB7XG5cdFx0XHRzaXRlcy5wdXNoKGxvY2F0aW9uKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRmF0YWwgcmVzb2x1dGlvbiBmYWlsdXJlcyAoaGFyZC1mYWlsIGxhdyk6IHNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZVxuXHQgKiBtbmVtb25pY2EgZGVmaW5pdGlvbnMgcGx1cyBhbWJpZ3VvdXMvdW5yZXNvbHZlZCBtbmVtb25pY2EtZ3JhcGhcblx0ICogcmVmZXJlbmNlcy4gVGhlIENMSSBwcmludHMgZXZlcnkgbG9jYXRpb24gYW5kIHdyaXRlcyBubyBvdXRwdXQuXG5cdCAqL1xuXHRnZXRSZXNvbHV0aW9uRXJyb3JzICgpOiBSZXNvbHV0aW9uRXJyb3JbXSB7XG5cdFx0dGhpcy52YWxpZGF0ZUxvb2t1cFJlZmVyZW5jZXMoKTtcblx0XHR0aGlzLnZhbGlkYXRlUGxhaW5UeXBlUmVmZXJlbmNlcygpO1xuXHRcdGNvbnN0IGVycm9yczogUmVzb2x1dGlvbkVycm9yW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IFsgbmFtZXNwYWNlS2V5LCBzaXRlcyBdIG9mIHRoaXMuZGVmaW5lU2l0ZXMpIHtcblx0XHRcdGlmIChzaXRlcy5sZW5ndGggPCAyKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZGlzcGxheU5hbWUgPSBuYW1lc3BhY2VLZXkucmVwbGFjZSgvXlteOl0rOjovLCAnJyk7XG5cdFx0XHRjb25zdCBtZXNzYWdlID0gYER1cGxpY2F0ZSBkZWZpbml0aW9uIG9mICcke2Rpc3BsYXlOYW1lfScgaW4gb25lIG5hbWVzcGFjZSDigJQgYCArXG5cdFx0XHRcdCd0aGUgbW5lbW9uaWNhIHJ1bnRpbWUgd291bGQgdGhyb3cgQUxSRUFEWV9ERUNMQVJFRCc7XG5cdFx0XHRlcnJvcnMucHVzaCh7IG1lc3NhZ2UsIGxvY2F0aW9ucyA6IFsgLi4uc2l0ZXMgXSB9KTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBlcnJvciBvZiB0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzKSB7XG5cdFx0XHRlcnJvcnMucHVzaChlcnJvcik7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGVycm9ycztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSByZWZlcmVuY2UgdG8gYSBtbmVtb25pY2EgZ3JhcGggdHlwZSBuYW1lLCBpbXBvcnQtYXdhcmUgYW5kXG5cdCAqIHBhdGgtYXdhcmUgKHRoZSBoYXJkLWZhaWwgaWRlbnRpdHkgbGF3LCBtaXJyb3JpbmcgdGhlIHJ1bnRpbWUpOlxuXHQgKiAgIDEuIHZhbHVlIHNjb3BlIOKAlCBhIHRyYWNrZWQgdG9wLWxldmVsIGJpbmRpbmcgaW4gdGhlIHJlZmVyZW5jaW5nIGZpbGVcblx0ICogICAgICAoYGNvbnN0IEFkZHJlc3MgPSBVc2VyLmRlZmluZSgnQWRkcmVzcycsIOKApilgKSxcblx0ICogICAyLiBpbXBvcnQgc2NvcGUg4oCUIGEgYmluZGluZyBleHBvcnRlZCBmcm9tIGEgbW9kdWxlIHRoaXMgZmlsZSBpbXBvcnRzXG5cdCAqICAgICAgKGJhcnJlbHMgY2hhc2VkKSxcblx0ICogICAzLiBuZWFyZXN0LWNoYWluIOKAlCB0aGUgYW5jaG9yIHR5cGUncyBvd24gc3VidHlwZXMgZmlyc3QsIHRoZW4gZWFjaFxuXHQgKiAgICAgIGFuY2VzdG9yIGxldmVsIChyZWxhdGl2ZS1maXJzdCksXG5cdCAqICAgNC4gcm9vdCDigJQgcm9vdHMgb2YgdGhlIGFuY2hvcidzIGNvbGxlY3Rpb24sXG5cdCAqICAgNS4gcHJvZ3JhbS13aWRlIOKAlCBvbmx5IHdoZW4gZXhhY3RseSBvbmUgdHlwZSBjYXJyaWVzIHRoZSBuYW1lLlxuXHQgKiBBbWJpZ3VpdHkgKHNldmVyYWwgY2FuZGlkYXRlcyBhbmQgbm90aGluZyBkaXNhbWJpZ3VhdGVzKSBhbmQgYWJzZW5jZVxuXHQgKiBhcmUgYm90aCByZXR1cm5lZCBhcyBzdWNoIOKAlCB0aGUgY2FsbGVyIHJlY29yZHMgYSBoYXJkIGZhaWx1cmU7IGEgYmFyZVxuXHQgKiBmaXJzdC1tYXRjaCBuYW1lIGlzIG5ldmVyIGVtaXR0ZWQuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVHcmFwaFR5cGVOYW1lIChuYW1lOiBzdHJpbmcpOiBHcmFwaFR5cGVSZWZlcmVuY2VSZXN1bHQge1xuXHRcdC8vIDEuIHZhbHVlIHNjb3BlIGluIHRoZSByZWZlcmVuY2luZyBmaWxlIGl0c2VsZlxuXHRcdGNvbnN0IGxvY2FsQmluZGluZyA9IHRoaXMuZmlsZUdyYXBoQmluZGluZ3MuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWxCaW5kaW5nKSB7XG5cdFx0XHRjb25zdCBub2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShsb2NhbEJpbmRpbmcpO1xuXHRcdFx0aWYgKG5vZGUpIHtcblx0XHRcdFx0Y29uc3QgdmFsdWVSZXN1bHQ6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCA9IHsgc3RhdHVzIDogJ3VuaXF1ZScsIG5vZGUgfTtcblx0XHRcdFx0cmV0dXJuIHZhbHVlUmVzdWx0O1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIDIuIGltcG9ydCBzY29wZSDigJQgdGhlIGltcG9ydGVkIG1vZHVsZSdzIGV4cG9ydGVkIGJpbmRpbmdcblx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGltcG9ydGVkICYmICFpbXBvcnRlZC5pc05hbWVzcGFjZSkge1xuXHRcdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKGltcG9ydGVkLnNwZWNpZmllciwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdGlmIChyZXNvbHV0aW9uICYmICFyZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0Y29uc3QgZnVsbFBhdGggPSB0aGlzLmZpbmRHcmFwaEJpbmRpbmdJbk1vZHVsZShyZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgaW1wb3J0ZWQub3JpZ2luYWxOYW1lLCAwKTtcblx0XHRcdFx0aWYgKGZ1bGxQYXRoKSB7XG5cdFx0XHRcdFx0Y29uc3Qgbm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoZnVsbFBhdGgpO1xuXHRcdFx0XHRcdGlmIChub2RlKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBpbXBvcnRSZXN1bHQ6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCA9IHsgc3RhdHVzIDogJ3VuaXF1ZScsIG5vZGUgfTtcblx0XHRcdFx0XHRcdHJldHVybiBpbXBvcnRSZXN1bHQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gMy01LiBjaGFpbiAvIHJvb3QgLyBwcm9ncmFtLXdpZGUgdGllcnNcblx0XHRjb25zdCByZXN1bHQgPSByZXNvbHZlR3JhcGhUeXBlUmVmZXJlbmNlKHRoaXMuZ3JhcGgsIG5hbWUsIHRoaXMuY3VycmVudEdyYXBoQW5jaG9yKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpbmQgYSBncmFwaCBjb25zdHJ1Y3RvciBiaW5kaW5nIGV4cG9ydGVkIGJ5IGEgcmVzb2x2ZWQgbW9kdWxlLFxuXHQgKiBjaGFzaW5nIHJlLWV4cG9ydCBiYXJyZWxzIHdpdGggYSBib3VuZGVkIGRlcHRoLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kR3JhcGhCaW5kaW5nSW5Nb2R1bGUgKG1vZHVsZVBhdGg6IHN0cmluZywgbmFtZTogc3RyaW5nLCBkZXB0aDogbnVtYmVyKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoZGVwdGggPiBNQVhfUkVFWFBPUlRfQ0hBU0VfREVQVEgpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGlyZWN0ID0gdGhpcy5maWxlR3JhcGhCaW5kaW5ncy5nZXQobW9kdWxlUGF0aCk/LmdldChuYW1lKTtcblx0XHRpZiAoZGlyZWN0KSB7XG5cdFx0XHRyZXR1cm4gZGlyZWN0O1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlRXhwb3J0cyA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGNvbnN0IHJlRXhwb3J0U3BlY2lmaWVyID0gcmVFeHBvcnRzPy5nZXQobmFtZSk7XG5cdFx0aWYgKHJlRXhwb3J0U3BlY2lmaWVyKSB7XG5cdFx0XHRjb25zdCBuZXh0UmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKHJlRXhwb3J0U3BlY2lmaWVyLCBtb2R1bGVQYXRoKTtcblx0XHRcdGlmIChuZXh0UmVzb2x1dGlvbiAmJiAhbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRjb25zdCBmb3VuZCA9IHRoaXMuZmluZEdyYXBoQmluZGluZ0luTW9kdWxlKG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgbmFtZSwgZGVwdGggKyAxKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGlmIChzdGFycykge1xuXHRcdFx0Zm9yIChjb25zdCBzdGFyU3BlY2lmaWVyIG9mIHN0YXJzKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoc3RhclNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRcdGlmICghbmV4dFJlc29sdXRpb24gfHwgbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kR3JhcGhCaW5kaW5nSW5Nb2R1bGUobmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBuYW1lLCBkZXB0aCArIDEpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFZhbGlkYXRlIGxpdGVyYWwgbG9va3VwKCkgcGF0aHMgcmVjb3JkZWQgZHVyaW5nIHRoZSB1c2FnZXMgcGFzc1xuXHQgKiBhZ2FpbnN0IHRoZSBjb21wbGV0ZSBncmFwaC4gQSBsb29rdXAgcGF0aCBtYXRjaGluZyBubyB0eXBlIGlzIHdoYXQgdGhlXG5cdCAqIHJ1bnRpbWUgYW5zd2VycyB3aXRoIGB1bmRlZmluZWRgIOKAlCB0aGUgVHlwZUVycm9yIGFycml2ZXMgb25lIGxpbmVcblx0ICogbGF0ZXIgYXQgdGhlIGBuZXdgIOKAlCBzbyBpdCBqb2lucyB0aGUgaGFyZC1mYWlsIGxhdy4gVGhlIHJlbGF0aXZlLWZpcnN0XG5cdCAqIHN0ZXAgYWxyZWFkeSByYW4gaW5zaWRlIHJlc29sdmVMb29rdXBQYXRoOyB3aGF0ZXZlciB3YXMgcmVjb3JkZWQgaXNcblx0ICogdGhlIHJvb3QtcmVzb2x1dGlvbiByZXN1bHQsIHNvIGEgcGxhaW4gZmluZFR5cGUgY2hlY2sgaXMgdGhlIGV4YWN0XG5cdCAqIHJ1bnRpbWUgbGF3LiBTYW1lLW5hbWVkIHR5cGVzIGVsc2V3aGVyZSBpbiB0aGUgZ3JhcGggYXJlIGxpc3RlZCBhc1xuXHQgKiBkaWQteW91LW1lYW4gY2FuZGlkYXRlcy4gUnVucyBvbmNlIHBlciB1c2FnZXMgcGFzcyAocmUtYXJtZWQgYnlcblx0ICogcmVzZXRVc2FnZXMpOyBub24tbGl0ZXJhbCBsb29rdXAgYXJndW1lbnRzIGFyZSBuZXZlciByZWNvcmRlZCBhbmRcblx0ICogc3RheSBiZXN0LWVmZm9ydC5cblx0ICovXG5cdHByaXZhdGUgdmFsaWRhdGVMb29rdXBSZWZlcmVuY2VzICgpOiB2b2lkIHtcblx0XHRpZiAodGhpcy5sb29rdXBSZWZlcmVuY2VzVmFsaWRhdGVkKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHRoaXMubG9va3VwUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IHRydWU7XG5cdFx0Ly8gZ3JvdXAgc2l0ZXMgYnkgcGF0aDogZXZlcnkgZmFpbGluZyBzaXRlIG9mIHRoZSBzYW1lIHBhdGggaXMgbGlzdGVkXG5cdFx0Y29uc3Qgc2l0ZXNCeVBhdGggPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nW10+KCk7XG5cdFx0Zm9yIChjb25zdCByZWYgb2YgdGhpcy5sb29rdXBSZWZlcmVuY2VzKSB7XG5cdFx0XHRjb25zdCBzaXRlcyA9IHNpdGVzQnlQYXRoLmdldChyZWYucGF0aCkgPz8gW107XG5cdFx0XHRzaXRlcy5wdXNoKHJlZi5sb2NhdGlvbik7XG5cdFx0XHRzaXRlc0J5UGF0aC5zZXQocmVmLnBhdGgsIHNpdGVzKTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBbIHR5cGVQYXRoLCBzaXRlcyBdIG9mIHNpdGVzQnlQYXRoKSB7XG5cdFx0XHRpZiAodGhpcy5ncmFwaC5maW5kVHlwZSh0eXBlUGF0aCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHQvLyBkaWQteW91LW1lYW46IHR5cGVzIGNhcnJ5aW5nIHRoZSBzYW1lIG5hbWUgYW55d2hlcmUgaW4gdGhlXG5cdFx0XHQvLyBncmFwaCAobmV2ZXIgYSBmaXJzdC1tYXRjaCBwaWNrIOKAlCB0aGUgZnVsbCBsaXN0IG9ubHkpXG5cdFx0XHRjb25zdCB1bnByZWZpeGVkID0gdHlwZVBhdGgucmVwbGFjZSgvXlteOl0rOjovLCAnJyk7XG5cdFx0XHRjb25zdCBsYXN0U2VnbWVudCA9IHVucHJlZml4ZWQuc3BsaXQoJy4nKS5wb3AoKSA/PyB1bnByZWZpeGVkO1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlcyA9IHRoaXMuZ3JhcGguZ2V0QWxsVHlwZXMoKS5maWx0ZXIodCA9PiB0Lm5hbWUgPT09IGxhc3RTZWdtZW50KTtcblx0XHRcdGlmIChjYW5kaWRhdGVzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHRjb25zdCBub25lRXJyb3I6IFJlc29sdXRpb25FcnJvciA9IHtcblx0XHRcdFx0XHRtZXNzYWdlIDogYFVucmVzb2x2ZWQgbG9va3VwIG9mIG1uZW1vbmljYSB0eXBlICcke3R5cGVQYXRofSc6IG5vIHR5cGUgYXQgdGhhdCBwYXRoIOKAlCBgICtcblx0XHRcdFx0XHRcdCd0aGUgcnVudGltZSB3b3VsZCByZXR1cm4gdW5kZWZpbmVkJyxcblx0XHRcdFx0XHRsb2NhdGlvbnMgOiBzaXRlcyxcblx0XHRcdFx0fTtcblx0XHRcdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKG5vbmVFcnJvcik7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgY2FuZGlkYXRlTG9jYXRpb25zID0gY2FuZGlkYXRlcy5tYXAobiA9PiBgJHtuLnNvdXJjZUZpbGV9OiR7bi5saW5lfToke24uY29sdW1ufWApO1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlUGF0aHMgPSBjYW5kaWRhdGVzLm1hcChuID0+IG4uZnVsbFBhdGgpLmpvaW4oJywgJyk7XG5cdFx0XHRjb25zdCBhbWJpZ3VvdXNFcnJvcjogUmVzb2x1dGlvbkVycm9yID0ge1xuXHRcdFx0XHRtZXNzYWdlIDogYFVucmVzb2x2ZWQgbG9va3VwIG9mIG1uZW1vbmljYSB0eXBlICcke3R5cGVQYXRofSc6IHRoZSBydW50aW1lIHdvdWxkIHJldHVybiBgICtcblx0XHRcdFx0XHRgdW5kZWZpbmVkIOKAlCAke2NhbmRpZGF0ZXMubGVuZ3RofSBncmFwaCB0eXBlKHMpIGNhcnJ5IHRoZSBuYW1lIGAgK1xuXHRcdFx0XHRcdGBvZmYtcm9vdCAoJHtjYW5kaWRhdGVQYXRoc30pOyB1c2UgdGhlIGZ1bGwgZG90dGVkIHBhdGhgLFxuXHRcdFx0XHRsb2NhdGlvbnMgOiBbIC4uLnNpdGVzLCAuLi5jYW5kaWRhdGVMb2NhdGlvbnMgXSxcblx0XHRcdH07XG5cdFx0XHR0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzLnB1c2goYW1iaWd1b3VzRXJyb3IpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgYSBwbGFpbi1UUyB0eXBlIHJlZmVyZW5jZSBzaXRlIHRoYXQgcmVzb2x2ZWQgdG8gbm90aGluZyBhbmRcblx0ICogZmVsbCBiYWNrIHRvIGB1bmtub3duYCwgZm9yIHRoZSBsYXppbHktcnVuIGFtYmlndWl0eSB2YWxpZGF0aW9uLlxuXHQgKiBEZWR1cGVkIGJ5IChuYW1lLCBsb2NhdGlvbik6IGluZmVyVHlwZSBjYW4gdmlzaXQgdGhlIHNhbWUgbm9kZSBtb3JlXG5cdCAqIHRoYW4gb25jZSBwZXIgcGFzcyAoY29uc3RydWN0b3IgcGFyYW1zICsgcHJvcGVydHkgaW5mZXJlbmNlKS5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSAobmFtZTogc3RyaW5nLCByZWZOb2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSB0aGlzLm5vZGVMb2NhdGlvbihyZWZOb2RlKTtcblx0XHRjb25zdCBmaWxlID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGNvbnN0IGFscmVhZHkgPSB0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXMuc29tZSgocmVmKSA9PiByZWYubmFtZSA9PT0gbmFtZSAmJiByZWYubG9jYXRpb24gPT09IGxvY2F0aW9uKTtcblx0XHRpZiAoYWxyZWFkeSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXMucHVzaCh7IG5hbWUsIGxvY2F0aW9uLCBmaWxlIH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb2plY3Qtc291cmNlIGRlY2xhcmF0aW9uIGZpbGVzIGNhcnJ5aW5nIGBuYW1lYCDigJQgb25lIGVudHJ5IHBlclxuXHQgKiBmaWxlLCBzbyBzYW1lLWZpbGUgaW50ZXJmYWNlIG1lcmdpbmcgY291bnRzIG9uY2UgKG5vdCBhbWJpZ3VvdXMpLlxuXHQgKiBFeHRlcm5hbC9hbWJpZW50IGRlY2xhcmF0aW9ucyAoLmQudHMsIGFueXRoaW5nIHVuZGVyIG5vZGVfbW9kdWxlcylcblx0ICogbmV2ZXIgY291bnQ6IGEgdXNlci1sb2NhbCBkZWNsYXJhdGlvbiBhbHdheXMgd2lucyBvdmVyIGEgcGFja2FnZS1cblx0ICogZGVjbGFyZWQgc2FtZS1uYW1lZCB0eXBlLCBzbyBhbiBleHRlcm5hbCBjb2xsaXNpb24gc3RheXMgc29mdC5cblx0ICovXG5cdHByaXZhdGUgcGxhaW5UeXBlRGVjbGFyYXRpb25GaWxlcyAobmFtZTogc3RyaW5nKTogc3RyaW5nW10ge1xuXHRcdGNvbnN0IGZpbGVzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgWyBmaWxlLCBkZWNscyBdIG9mIHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscykge1xuXHRcdFx0aWYgKCF0aGlzLmlzRXh0ZXJuYWxEZWNsRmlsZShmaWxlKSAmJiBkZWNscy5oYXMobmFtZSkpIHtcblx0XHRcdFx0ZmlsZXMucHVzaChmaWxlKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIGZpbGVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIFZhbGlkYXRlIHBsYWluLVRTIHR5cGUgcmVmZXJlbmNlIHNpdGVzIHJlY29yZGVkIGR1cmluZyB0aGUgdXNhZ2VzXG5cdCAqIHBhc3MgYWdhaW5zdCB0aGUgY29tcGxldGUgZGVjbGFyYXRpb24gbWFwLiBBIG5hbWUgZGVjbGFyZWQgaW5cblx0ICogc2V2ZXJhbCBwcm9qZWN0LXNvdXJjZSBmaWxlcyDigJQgd2l0aCBubyBpbXBvcnQgaW4gdGhlIHJlZmVyZW5jaW5nXG5cdCAqIGZpbGUgdG8gYW5jaG9yIGl0IOKAlCBpcyBhbWJpZ3VvdXM6IHNpbGVudGx5IGVtaXR0aW5nIGB1bmtub3duYCB3b3VsZFxuXHQgKiBoaWRlIGEgcmVhbCB0eXBlIHRoZSBhdXRob3IgbWVhbnQsIHNvIGl0IGpvaW5zIHRoZSBoYXJkLWZhaWwgbGF3XG5cdCAqICh0aGUgcGxhaW4tVFMgdGllciBvZiB0aGUgc2FtZSBpZGVudGl0eSBsYXcgYXMgZ3JhcGggcmVmZXJlbmNlcykuXG5cdCAqIEFic2VuY2UgKGdob3N0IG5hbWVzKSBhbmQgZXh0ZXJuYWwgY29sbGlzaW9ucyBzdGF5IHNvZnQgYHVua25vd25gLlxuXHQgKiBSdW5zIG9uY2UgcGVyIHVzYWdlcyBwYXNzIChyZS1hcm1lZCBieSByZXNldFVzYWdlcyksIG1pcnJvcmluZ1xuXHQgKiB2YWxpZGF0ZUxvb2t1cFJlZmVyZW5jZXM6IHJlY29yZGluZyBoYXBwZW5zIG9uIGV2ZXJ5IHBhc3MsIGJ1dCBvbmx5XG5cdCAqIHRoZSB1c2FnZXMgcGFzcyBzZWVzIHRoZSBjb21wbGV0ZSBkZWNsYXJhdGlvbiBtYXAuXG5cdCAqL1xuXHRwcml2YXRlIHZhbGlkYXRlUGxhaW5UeXBlUmVmZXJlbmNlcyAoKTogdm9pZCB7XG5cdFx0aWYgKHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXNWYWxpZGF0ZWQgPSB0cnVlO1xuXHRcdGNvbnN0IHNpdGVzQnlOYW1lID0gbmV3IE1hcDxzdHJpbmcsIHsgbmFtZTogc3RyaW5nOyBsb2NhdGlvbjogc3RyaW5nOyBmaWxlOiBzdHJpbmcgfVtdPigpO1xuXHRcdGZvciAoY29uc3QgcmVmIG9mIHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlcykge1xuXHRcdFx0Y29uc3Qgc2l0ZXMgPSBzaXRlc0J5TmFtZS5nZXQocmVmLm5hbWUpID8/IFtdO1xuXHRcdFx0c2l0ZXMucHVzaChyZWYpO1xuXHRcdFx0c2l0ZXNCeU5hbWUuc2V0KHJlZi5uYW1lLCBzaXRlcyk7XG5cdFx0fVxuXHRcdGZvciAoY29uc3QgWyBuYW1lLCBzaXRlcyBdIG9mIHNpdGVzQnlOYW1lKSB7XG5cdFx0XHQvLyBhbiBpbXBvcnQgYmluZGluZyBpbiB0aGUgcmVmZXJlbmNpbmcgZmlsZSBhbmNob3JzIHRoZSBuYW1lIOKAlFxuXHRcdFx0Ly8gdGhlIGF1dGhvciBhbHJlYWR5IGRpc2FtYmlndWF0ZWQgKHRoZSBpbXBvcnQgbWF5IGp1c3QgcG9pbnRcblx0XHRcdC8vIGF0IGFuIHVuYW5hbHl6YWJsZSBleHRlcm5hbCBtb2R1bGUsIHdoaWNoIHN0YXlzIHNvZnQpXG5cdFx0XHRjb25zdCB1bmFuY2hvcmVkID0gc2l0ZXMuZmlsdGVyKChzaXRlKSA9PiAhdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KHNpdGUuZmlsZSk/LmhhcyhuYW1lKSk7XG5cdFx0XHRpZiAodW5hbmNob3JlZC5sZW5ndGggPT09IDApIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBkZWNsRmlsZXMgPSB0aGlzLnBsYWluVHlwZURlY2xhcmF0aW9uRmlsZXMobmFtZSk7XG5cdFx0XHRpZiAoZGVjbEZpbGVzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBtZXNzYWdlID0gYEFtYmlndW91cyByZWZlcmVuY2UgdG8gdHlwZSAnJHtuYW1lfSc6ICR7ZGVjbEZpbGVzLmxlbmd0aH0gZGVjbGFyYXRpb25zIGAgK1xuXHRcdFx0XHQnc2hhcmUgdGhlIG5hbWUgYW5kIG5vIGltcG9ydCBkaXNhbWJpZ3VhdGVzIOKAlCBpbXBvcnQgdGhlIG9uZSB5b3UgbWVhbic7XG5cdFx0XHRjb25zdCBkZWNsTG9jYXRpb25zID0gZGVjbEZpbGVzLm1hcCgoZmlsZSkgPT4gdGhpcy5wbGFpbkRlY2xMb2NhdGlvbihmaWxlLCBuYW1lKSk7XG5cdFx0XHRjb25zdCBlcnJvcjogUmVzb2x1dGlvbkVycm9yID0ge1xuXHRcdFx0XHRtZXNzYWdlLFxuXHRcdFx0XHRsb2NhdGlvbnMgOiBbIC4uLnVuYW5jaG9yZWQubWFwKChzaXRlKSA9PiBzaXRlLmxvY2F0aW9uKSwgLi4uZGVjbExvY2F0aW9ucyBdXG5cdFx0XHR9O1xuXHRcdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKGVycm9yKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogYGZpbGU6bGluZTpjb2x1bW5gIG9mIGEgcmVjb3JkZWQgZGVjbGFyYXRpb24sIGZvciB0aGUgYW1iaWd1aXR5XG5cdCAqIHJlcG9ydC4gTm9kZXMgcmVjb3JkZWQgZHVyaW5nIHRyYXZlcnNhbCBrZWVwIHRoZWlyIHBvc2l0aW9uczsgYVxuXHQgKiBzeW50aGV0aWMvdW5wb3NpdGlvbmVkIG5vZGUgZmFsbHMgYmFjayB0byB0aGUgZmlsZSBpdHNlbGYuXG5cdCAqL1xuXHRwcml2YXRlIHBsYWluRGVjbExvY2F0aW9uIChmaWxlOiBzdHJpbmcsIG5hbWU6IHN0cmluZyk6IHN0cmluZyB7XG5cdFx0Y29uc3QgZGVjbCA9IHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscy5nZXQoZmlsZSk/LmdldChuYW1lKTtcblx0XHRjb25zdCBub2RlID0gZGVjbD8ubm9kZTtcblx0XHRsZXQgbG9jYXRpb24gPSBgJHtmaWxlfToxOjFgO1xuXHRcdGlmIChub2RlICYmIG5vZGUucG9zID49IDApIHtcblx0XHRcdGNvbnN0IHNvdXJjZUZpbGUgPSBub2RlLmdldFNvdXJjZUZpbGUoKTtcblx0XHRcdGNvbnN0IGxpbmUgPSBzb3VyY2VGaWxlLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKG5vZGUuZ2V0U3RhcnQoKSkubGluZSArIDE7XG5cdFx0XHRjb25zdCBjb2x1bW4gPSBzb3VyY2VGaWxlLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKG5vZGUuZ2V0U3RhcnQoKSkuY2hhcmFjdGVyICsgMTtcblx0XHRcdGxvY2F0aW9uID0gYCR7ZmlsZX06JHtsaW5lfToke2NvbHVtbn1gO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBsb2NhdGlvbjtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhIGhhcmQtZmFpbCBncmFwaCByZWZlcmVuY2UgZXJyb3Igd2l0aCB0aGUgcmVmZXJlbmNlIHNpdGUgYW5kXG5cdCAqIGV2ZXJ5IGNhbmRpZGF0ZSBsb2NhdGlvbi5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkR3JhcGhSZWZlcmVuY2VFcnJvciAoXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdHJlZk5vZGU6IHRzLk5vZGUgfCBzdHJpbmcsXG5cdFx0cmVzdWx0OiBFeHRyYWN0PEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCwgeyBzdGF0dXM6ICdhbWJpZ3VvdXMnIHwgJ25vbmUnIH0+XG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gdHlwZW9mIHJlZk5vZGUgPT09ICdzdHJpbmcnID8gcmVmTm9kZSA6IHRoaXMubm9kZUxvY2F0aW9uKHJlZk5vZGUpO1xuXHRcdGlmIChyZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlTG9jYXRpb25zID0gcmVzdWx0LmNhbmRpZGF0ZXMubWFwKG4gPT4gYCR7bi5zb3VyY2VGaWxlfToke24ubGluZX06JHtuLmNvbHVtbn1gKTtcblx0XHRcdGNvbnN0IGFtYmlndW91c01lc3NhZ2UgPSBgQW1iaWd1b3VzIHJlZmVyZW5jZSB0byBtbmVtb25pY2EgdHlwZSAnJHtuYW1lfSc6IGAgK1xuXHRcdFx0XHRgJHtyZXN1bHQuY2FuZGlkYXRlcy5sZW5ndGh9IHR5cGVzIHNoYXJlIHRoZSBuYW1lIGFuZCBuZWl0aGVyIHRoZSBwYXJlbnQgY2hhaW4gYCArXG5cdFx0XHRcdCdub3IgdGhlIGltcG9ydHMgZGlzYW1iaWd1YXRlJztcblx0XHRcdGNvbnN0IGFtYmlndW91c0Vycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7XG5cdFx0XHRcdG1lc3NhZ2UgICA6IGFtYmlndW91c01lc3NhZ2UsXG5cdFx0XHRcdGxvY2F0aW9ucyA6IFsgbG9jYXRpb24sIC4uLmNhbmRpZGF0ZUxvY2F0aW9ucyBdLFxuXHRcdFx0fTtcblx0XHRcdHRoaXMuZ3JhcGhSZWZlcmVuY2VFcnJvcnMucHVzaChhbWJpZ3VvdXNFcnJvcik7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHVucmVzb2x2ZWRNZXNzYWdlID0gYFVucmVzb2x2ZWQgcmVmZXJlbmNlIHRvIG1uZW1vbmljYSB0eXBlICcke25hbWV9Jzogbm8gdHlwZSBtYXRjaGVzIGAgK1xuXHRcdFx0J2J5IHZhbHVlIHNjb3BlLCBpbXBvcnRzLCBwYXJlbnQgY2hhaW4sIG9yIHJvb3QgcGF0aCc7XG5cdFx0Y29uc3QgdW5yZXNvbHZlZEVycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7IG1lc3NhZ2UgOiB1bnJlc29sdmVkTWVzc2FnZSwgbG9jYXRpb25zIDogWyBsb2NhdGlvbiBdIH07XG5cdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKHVucmVzb2x2ZWRFcnJvcik7XG5cdH1cblxuXHQvKipcblx0ICogTG9jYXRpb24gKGBmaWxlOmxpbmU6Y29sdW1uYCkgb2YgYW4gQVNUIG5vZGUsIGRlcml2ZWQgd2l0aG91dCBwYXJlbnRcblx0ICogcG9pbnRlcnMgd2hlbiBuZWNlc3NhcnkuXG5cdCAqL1xuXHRwcml2YXRlIG5vZGVMb2NhdGlvbiAobm9kZTogdHMuTm9kZSk6IHN0cmluZyB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBub2RlO1xuXHRcdHdoaWxlIChjdXJyZW50ICYmICF0cy5pc1NvdXJjZUZpbGUoY3VycmVudCkpIHtcblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0aWYgKCFjdXJyZW50KSB7XG5cdFx0XHRjb25zdCBmYWxsYmFjayA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRcdHJldHVybiBmYWxsYmFjaztcblx0XHR9XG5cdFx0Y29uc3Qgc3RhcnQgPSBub2RlLmdldFN0YXJ0KGN1cnJlbnQpO1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihjdXJyZW50LCBzdGFydCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtjdXJyZW50LmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRyZXR1cm4gbG9jYXRpb247XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgYWxpYXNlcyBvZiB0aGUgbW5lbW9uaWNhIG1vZHVsZSBvYmplY3QsIGUuZy46XG5cdCAqICAgY29uc3QgbSA9IG1uZW1vbmljYTtcblx0ICogICBjb25zdCBBcHAgPSBtO1xuXHQgKi9cblx0cHJpdmF0ZSB0cmFja01vZHVsZU9iamVjdEFsaWFzZXMgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSB8fCAhdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGluaXRpYWxpemVyIH0gPSBub2RlO1xuXHRcdGlmICghaW5pdGlhbGl6ZXIpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGluaXRpYWxpemVyKSAmJiB0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoaW5pdGlhbGl6ZXIudGV4dCkpIHtcblx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChub2RlLm5hbWUudGV4dCk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFRyYWNrIGN1c3RvbSBjb2xsZWN0aW9uIHZhcmlhYmxlcywgZS5nLjpcblx0ICogICBjb25zdCBNeUNvbGxlY3Rpb24gPSBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKTtcblx0ICogICBjb25zdCBPdGhlciA9IE15Q29sbGVjdGlvbjtcblx0ICpcblx0ICogQWxzbyBkZXRlY3RzIE9wdGlvbiBCIHVzZXItcHJvdmlkZWQgcmVnaXN0cnkgaW50ZXJmYWNlczpcblx0ICogICBleHBvcnQgaW50ZXJmYWNlIE15Q29sbGVjdGlvblJlZ2lzdHJ5IHt9XG5cdCAqICAgY29uc3QgTXlDb2xsZWN0aW9uID0gY3JlYXRlVHlwZXNDb2xsZWN0aW9uPE15Q29sbGVjdGlvblJlZ2lzdHJ5PigpO1xuXHQgKi9cblx0cHJpdmF0ZSB0cmFja0NvbGxlY3Rpb25BbGlhc2VzIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgfHwgIXRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBpbml0aWFsaXplciB9ID0gbm9kZTtcblx0XHRpZiAoIWluaXRpYWxpemVyKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRGlyZWN0IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIGNhbGxcblx0XHRpZiAodGhpcy5pc0NyZWF0ZVR5cGVzQ29sbGVjdGlvbkNhbGwoaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRjb25zdCBjb2xsZWN0aW9uSWQgPSB0aGlzLm5leHRDb2xsZWN0aW9uSWQoKTtcblx0XHRcdHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5zZXQobm9kZS5uYW1lLnRleHQsIGNvbGxlY3Rpb25JZCk7XG5cblx0XHRcdGNvbnN0IHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA9IHRoaXMuZXh0cmFjdFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZShcblx0XHRcdFx0aW5pdGlhbGl6ZXIgYXMgdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0XHRcdHNvdXJjZUZpbGVcblx0XHRcdCk7XG5cdFx0XHR0aGlzLmNvbGxlY3Rpb25JbmZvLnNldChjb2xsZWN0aW9uSWQsIHtcblx0XHRcdFx0dmFyaWFibGVOYW1lICAgICAgICAgIDogbm9kZS5uYW1lLnRleHQsXG5cdFx0XHRcdHNvdXJjZUZpbGUgICAgICAgICAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA6IHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZVxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gQWxpYXMgb2YgYW5vdGhlciBjb2xsZWN0aW9uIHZhcmlhYmxlXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihpbml0aWFsaXplcikpIHtcblx0XHRcdGNvbnN0IGV4aXN0aW5nID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChpbml0aWFsaXplci50ZXh0KTtcblx0XHRcdGlmIChleGlzdGluZykge1xuXHRcdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuc2V0KG5vZGUubmFtZS50ZXh0LCBleGlzdGluZyk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdGhlIHJlZ2lzdHJ5IGludGVyZmFjZSBuYW1lIGZyb20gY3JlYXRlVHlwZXNDb2xsZWN0aW9uPFJlZ2lzdHJ5PigpXG5cdCAqIHdoZW4gdGhlIGludGVyZmFjZSBpcyBkZWNsYXJlZCBpbiB0aGUgc2FtZSBzb3VyY2UgZmlsZS5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSAoXG5cdFx0Y2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZVxuXHQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IHR5cGVBcmdzID0gY2FsbC50eXBlQXJndW1lbnRzO1xuXHRcdGlmICghdHlwZUFyZ3MgfHwgdHlwZUFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IFsgZmlyc3RUeXBlQXJnIF0gPSB0eXBlQXJncztcblx0XHRpZiAoIXRzLmlzVHlwZVJlZmVyZW5jZU5vZGUoZmlyc3RUeXBlQXJnKSB8fCAhdHMuaXNJZGVudGlmaWVyKGZpcnN0VHlwZUFyZy50eXBlTmFtZSkpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgbmFtZSA9IGZpcnN0VHlwZUFyZy50eXBlTmFtZS50ZXh0O1xuXG5cdFx0Ly8gQ29uZmlybSB0aGUgaW50ZXJmYWNlIGV4aXN0cyBpbiB0aGUgc2FtZSBzb3VyY2UgZmlsZS5cblx0XHRmb3IgKGNvbnN0IHN0YXRlbWVudCBvZiBzb3VyY2VGaWxlLnN0YXRlbWVudHMpIHtcblx0XHRcdGlmIChcblx0XHRcdFx0dHMuaXNJbnRlcmZhY2VEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmXG5cdFx0XHRcdHN0YXRlbWVudC5uYW1lLnRleHQgPT09IG5hbWVcblx0XHRcdCkge1xuXHRcdFx0XHRyZXR1cm4gbmFtZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCB0aGUgcmVnaXN0cnkgaW50ZXJmYWNlIG5hbWUgZm9yIGEgY29sbGVjdGlvbiBpZC5cblx0ICovXG5cdHByaXZhdGUgZ2V0UmVnaXN0cnlJbnRlcmZhY2VOYW1lIChjb2xsZWN0aW9uSWQ/OiBzdHJpbmcpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghY29sbGVjdGlvbklkKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRyZXR1cm4gdGhpcy5jb2xsZWN0aW9uSW5mby5nZXQoY29sbGVjdGlvbklkKT8ucmVnaXN0cnlJbnRlcmZhY2VOYW1lO1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGFuIGV4cHJlc3Npb24gaXMgYSBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSBjYWxsLlxuXHQgKiBIYW5kbGVzOlxuXHQgKiAgIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpXG5cdCAqICAgY3RjKCkgLy8gYWxpYXNlZCBpbXBvcnRcblx0ICogICBtbmVtb25pY2EuY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgLy8gbW9kdWxlIG9iamVjdCBtZXRob2Rcblx0ICogICBtLmNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIC8vIGFsaWFzZWQgbW9kdWxlIG9iamVjdFxuXHQgKi9cblx0cHJpdmF0ZSBpc0NyZWF0ZVR5cGVzQ29sbGVjdGlvbkNhbGwgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkNhbGxFeHByZXNzaW9uIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Y29uc3QgZXhwciA9IG5vZGUuZXhwcmVzc2lvbjtcblxuXHRcdC8vIERpcmVjdCBjYWxsIG9yIGFsaWFzZWQgaW1wb3J0OiBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSAvIGN0YygpXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIGV4cHIudGV4dCA9PT0gJ2NyZWF0ZVR5cGVzQ29sbGVjdGlvbicgfHxcblx0XHRcdFx0dGhpcy5jcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGV4cHIudGV4dCk7XG5cdFx0fVxuXG5cdFx0Ly8gTW9kdWxlIG9iamVjdCBtZXRob2Q6IG1uZW1vbmljYS5jcmVhdGVUeXBlc0NvbGxlY3Rpb24oKVxuXHRcdGlmIChcblx0XHRcdHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpICYmXG5cdFx0XHRleHByLm5hbWUudGV4dCA9PT0gJ2NyZWF0ZVR5cGVzQ29sbGVjdGlvbicgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcihleHByLmV4cHJlc3Npb24pICYmXG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoZXhwci5leHByZXNzaW9uLnRleHQpXG5cdFx0KSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogR2VuZXJhdGUgYSB1bmlxdWUgY29sbGVjdGlvbiBpZGVudGlmaWVyLlxuXHQgKi9cblx0cHJpdmF0ZSBuZXh0Q29sbGVjdGlvbklkICgpOiBzdHJpbmcge1xuXHRcdHRoaXMuY29sbGVjdGlvbkNvdW50ZXIrKztcblx0XHRjb25zdCByZXN1bHQgPSBgY29sbGVjdGlvbl8ke3RoaXMuY29sbGVjdGlvbkNvdW50ZXJ9YDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGEgbm9kZSBpcyBhIGRlZmluZSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgaXNEZWZpbmVDYWxsIChub2RlOiB0cy5Ob2RlKTogbm9kZSBpcyB0cy5DYWxsRXhwcmVzc2lvbiB7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIGRpcmVjdCBjYWxsOiBkZWZpbmUoJ1R5cGVOYW1lJywgLi4uKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIG1ldGhvZCBjYWxsOiBTb21lVHlwZS5kZWZpbmUoJ1N1YlR5cGUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gZXhwcmVzc2lvbi5uYW1lPy50ZXh0ID09PSAnZGVmaW5lJztcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogQ2hlY2sgaWYgYSBub2RlIGlzIGEgbGF6eSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgaXNMYXp5Q2FsbCAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuQ2FsbEV4cHJlc3Npb24ge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBkaXJlY3QgY2FsbDogbGF6eSgnVHlwZU5hbWUnLCBnZXR0ZXIsIC4uLilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2xhenknKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgbWV0aG9kIGNhbGw6IFNvbWVUeXBlLmxhenkoJ1N1YlR5cGUnLCBnZXR0ZXIsIC4uLilcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcmVzc2lvbikpIHtcblx0XHRcdHJldHVybiBleHByZXNzaW9uLm5hbWU/LnRleHQgPT09ICdsYXp5Jztcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0XHQqIEV4dHJhY3QgY29uZmlnIG9wdGlvbnMgZnJvbSBhbiBvYmplY3QgbGl0ZXJhbFxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsIChjb25maWdBcmc6IHRzLk9iamVjdExpdGVyYWxFeHByZXNzaW9uKTpcblx0XHR7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0ge1xuXHRcdGNvbnN0IGNvbmZpZzogeyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9ID0ge307XG5cblx0XHRmb3IgKGNvbnN0IHByb3Agb2YgY29uZmlnQXJnLnByb3BlcnRpZXMpIHtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSAmJiB0cy5pc0lkZW50aWZpZXIocHJvcC5uYW1lKSkge1xuXHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IHByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRpZiAocHJvcE5hbWUgPT09ICdzdHJpY3RDaGFpbicgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLnN0cmljdENoYWluID0gdHJ1ZTtcblx0XHRcdFx0fSBlbHNlIGlmIChwcm9wTmFtZSA9PT0gJ3N0cmljdENoYWluJyAmJiBwcm9wLmluaXRpYWxpemVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLnN0cmljdENoYWluID0gZmFsc2U7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdibG9ja0Vycm9ycycgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLmJsb2NrRXJyb3JzID0gdHJ1ZTtcblx0XHRcdFx0fSBlbHNlIGlmIChwcm9wTmFtZSA9PT0gJ2Jsb2NrRXJyb3JzJyAmJiBwcm9wLmluaXRpYWxpemVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLmJsb2NrRXJyb3JzID0gZmFsc2U7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gY29uZmlnO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IGNvbmZpZyBvcHRpb25zIGZyb20gZGVmaW5lKCkgY2FsbFxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdENvbmZpZyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0ge1xuXHRcdC8vIENvbmZpZyBpcyB0aGUgdGhpcmQgYXJndW1lbnQ6IGRlZmluZSgnTmFtZScsIGhhbmRsZXIsIGNvbmZpZylcblx0XHRjb25zdCBbICwgLCBjb25maWdBcmcgXSA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGlmICghY29uZmlnQXJnIHx8ICF0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGNvbmZpZ0FyZykpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRjb25zdCBjb25maWdSZXN1bHQgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjb25maWdBcmcpO1xuXHRcdHJldHVybiBjb25maWdSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHQqIENoZWNrIGlmIGEgbm9kZSBpcyBhIEBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHRcdCovXG5cdHByaXZhdGUgaXNEZWNvcmF0ZURlY29yYXRvciAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuRGVjb3JhdG9yIHtcblx0XHRpZiAoIXRzLmlzRGVjb3JhdG9yKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIEBkZWNvcmF0ZVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVjb3JhdGUnKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgQGRlY29yYXRlKCkgb3IgQGRlY29yYXRlKFBhcmVudFR5cGUpXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZXhwcmVzc2lvbikpIHtcblx0XHRcdGNvbnN0IGZuTmFtZSA9IGV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZm5OYW1lKSAmJiBmbk5hbWUudGV4dCA9PT0gJ2RlY29yYXRlJykge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gQ2hlY2sgZm9yIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSB3aGVyZSBNeUNvbGxlY3Rpb24gaXMgYSBjdXN0b20gY29sbGVjdGlvblxuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihmbk5hbWUpICYmXG5cdFx0XHRcdGZuTmFtZS5uYW1lLnRleHQgPT09ICdkZWNvcmF0ZScgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGZuTmFtZS5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGZuTmFtZS5leHByZXNzaW9uLnRleHQpXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIE1hcmsgYSBjYWxsIGV4cHJlc3Npb24gYXMgcHJvY2Vzc2VkIGFuZCByZXR1cm4gd2hldGhlciBpdCBhbHJlYWR5IHdhcy5cblx0ICovXG5cdHByaXZhdGUgbWFya1Byb2Nlc3NlZCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBib29sZWFuIHtcblx0XHRpZiAodGhpcy5wcm9jZXNzZWRDYWxscy5oYXMoY2FsbCkpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHR0aGlzLnByb2Nlc3NlZENhbGxzLmFkZChjYWxsKTtcblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogUHJvY2VzcyBhIGRlZmluZSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgcHJvY2Vzc0RlZmluZUNhbGwgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBleGFjdCBjYWxsIGhhcyBhbHJlYWR5IGJlZW4gcHJvY2Vzc2VkIChwcmV2ZW50cyBkdXBsaWNhdGVzIGZyb20gY2hhaW5lZCBjYWxscylcblx0XHRpZiAodGhpcy5tYXJrUHJvY2Vzc2VkKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gR2V0IHRoZSB0eXBlIG5hbWUgYW5kIHNvdXJjZSBjb250ZXh0IGZyb20gYXJndW1lbnRzXG5cdFx0Y29uc3QgZGVmaW5lQ29udGV4dCA9IHRoaXMuZXh0cmFjdERlZmluZUNvbnRleHQoY2FsbCk7XG5cblx0XHQvLyBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGRlZmluZSgnQScpLmRlZmluZSgnQicpLCB3ZSB3YW50IHRoZSBwb3NpdGlvbiBvZiB0aGUgLmRlZmluZSgnQicpIHBhcnRcblx0XHQvLyBub3QgdGhlIHN0YXJ0IG9mIHRoZSBlbnRpcmUgZXhwcmVzc2lvblxuXHRcdGxldCBwb3NpdGlvbk5vZGU6IHRzLk5vZGUgPSBjYWxsO1xuXG5cdFx0Ly8gSWYgdGhpcyBpcyBhIGNoYWluZWQgY2FsbCwgZ2V0IHRoZSBwb3NpdGlvbiBvZiB0aGUgcHJvcGVydHkgYWNjZXNzIGV4cHJlc3Npb25cblx0XHQvLyB3aGljaCBpcyB0aGUgLmRlZmluZSBwYXJ0XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdC8vIFRoZSBleHByZXNzaW9uIGlzIHRoZSBwcm9wZXJ0eSBhY2Nlc3M6IChkZWZpbmUoJ1Jvb3RBc3luYycsIC4uLikpLmRlZmluZVxuXHRcdFx0Ly8gV2Ugd2FudCB0aGUgcG9zaXRpb24gb2YganVzdCB0aGUgLmRlZmluZSBwYXJ0XG5cdFx0XHQvLyBUaGlzIGlzIHRoZSAnZGVmaW5lJyBpZGVudGlmaWVyXG5cdFx0XHRwb3NpdGlvbk5vZGUgPSBjYWxsLmV4cHJlc3Npb24ubmFtZTtcblx0XHR9XG5cblx0XHRjb25zdCBzdGFydFBvcyA9IHBvc2l0aW9uTm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKTtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oc291cmNlRmlsZSwgc3RhcnRQb3MpO1xuXG5cdFx0aWYgKCFkZWZpbmVDb250ZXh0LnR5cGVOYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdDb3VsZCBub3QgZXh0cmFjdCB0eXBlIG5hbWUgZnJvbSBkZWZpbmUoKSBjYWxsJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IHR5cGVOYW1lIH0gPSBkZWZpbmVDb250ZXh0O1xuXG5cdFx0Ly8gRGV0ZXJtaW5lIHBhcmVudCB0eXBlIGFuZCBjb2xsZWN0aW9uIGJhc2VkIG9uIHRoZSBjYWxsIHNvdXJjZS5cblx0XHRjb25zdCBwYXJlbnROb2RlID0gZGVmaW5lQ29udGV4dC5wYXJlbnRUeXBlO1xuXHRcdGNvbnN0IHsgY29sbGVjdGlvbklkIH0gPSBkZWZpbmVDb250ZXh0O1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25maWcgb3B0aW9uc1xuXHRcdGNvbnN0IGNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZyhjYWxsKTtcblxuXHRcdC8vIENyZWF0ZSB0eXBlIG5vZGUgZmlyc3Qgc28gaXRzIGludGVybmFsIGZ1bGxQYXRoIChpbmNsdWRpbmcgYW55IGNvbGxlY3Rpb24gcHJlZml4KSBpcyByZXNvbHZlZC5cblx0XHRjb25zdCBub2RlID0gVHlwZUdyYXBoSW1wbC5jcmVhdGVOb2RlKFxuXHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRwYXJlbnROb2RlLFxuXHRcdFx0c291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdGxpbmUgKyAxLFxuXHRcdFx0Y2hhcmFjdGVyICsgMSxcblx0XHRcdGNvbGxlY3Rpb25JZFxuXHRcdCk7XG5cdFx0bm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWUgPSB0aGlzLmdldFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZShjb2xsZWN0aW9uSWQpO1xuXG5cdFx0Ly8gU2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlIGRldGVjdGlvbiAoaGFyZC1mYWlsIGxhdyk6IGtleSBieSB0aGVcblx0XHQvLyBydW50aW1lIG5hbWVzcGFjZSDigJQgY29sbGVjdGlvbiByb290cyBgPGNvbGxlY3Rpb24+Ojo8bmFtZT5gLCBvclxuXHRcdC8vIGA8cGFyZW50RnVsbFBhdGg+LjxuYW1lPmAgZm9yIHN1YnR5cGVzXG5cdFx0dGhpcy5yZWNvcmREZWZpbmVTaXRlKFxuXHRcdFx0cGFyZW50Tm9kZSA/IGAke3BhcmVudE5vZGUuZnVsbFBhdGh9LiR7dHlwZU5hbWV9YCA6IGAke2NvbGxlY3Rpb25JZCA/PyAnZGVmYXVsdCd9Ojoke3R5cGVOYW1lfWAsXG5cdFx0XHRgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YFxuXHRcdCk7XG5cblx0XHQvLyBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBjb25zdHJ1Y3RvciBmdW5jdGlvbiDigJQgdGhlIG5ldyBub2RlIGFuY2hvcnNcblx0XHQvLyByZWxhdGl2ZS1maXJzdCBncmFwaCByZWZlcmVuY2UgcmVzb2x1dGlvbiB3aGlsZSBpdHMgb3duIHNpZ25hdHVyZVxuXHRcdC8vIGlzIGJlaW5nIHJlYWRcblx0XHRjb25zdCBwcmV2aW91c0FuY2hvciA9IHRoaXMuY3VycmVudEdyYXBoQW5jaG9yO1xuXHRcdHRoaXMuY3VycmVudEdyYXBoQW5jaG9yID0gbm9kZTtcblx0XHR0cnkge1xuXHRcdFx0bm9kZS5wcm9wZXJ0aWVzID0gdGhpcy5leHRyYWN0UHJvcGVydGllcyhjYWxsKTtcblxuXHRcdFx0Ly8gRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZvciBUeXBlUmVnaXN0cnkgc2lnbmF0dXJlXG5cdFx0XHRub2RlLmNvbnN0cnVjdG9yUGFyYW1zID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JQYXJhbXMoY2FsbCk7XG5cdFx0fSBmaW5hbGx5IHtcblx0XHRcdHRoaXMuY3VycmVudEdyYXBoQW5jaG9yID0gcHJldmlvdXNBbmNob3I7XG5cdFx0fVxuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoXG5cdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkQ2hpbGQocGFyZW50Tm9kZSwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cblx0XHQvLyBDcmVhdGUgZGVmaW5pdGlvbiBpbmZvIHVzaW5nIHRoZSBub2RlJ3MgcmVzb2x2ZWQgZnVsbFBhdGhcblx0XHRjb25zdCBkZWZpbml0aW9uOiBEZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogcGFyZW50Tm9kZSA/IHBhcmVudE5vZGUuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiBjb25maWcuc3RyaWN0Q2hhaW4gPz8gdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogY29uZmlnLmJsb2NrRXJyb3JzID8/IGZhbHNlLFxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQobm9kZS5mdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdFx0dGhpcy5lZHNTY29wZUJ5Tm9kZS5zZXQoY2FsbCwgbm9kZS5mdWxsUGF0aCk7XG5cblx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50OiBjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKSAtPiBtYXAgXCJVc2VyXCIgdG8gXCJVc2VyRW50aXR5XCJcblx0XHQvLyBBIG11bHRpLWhvcCBpbml0aWFsaXplciBiaW5kcyB0aGUgTEFTVCBob3A6IGRlZmluZSgpIHJldHVybnMgdGhlXG5cdFx0Ly8gZGVmaW5lZCB0eXBlJ3MgY29uc3RydWN0b3IgKEYxOClcblx0XHR0aGlzLnRyYWNrVmFyaWFibGVBc3NpZ25tZW50KGNhbGwsIHBhcmVudE5vZGUsIG5vZGUuZnVsbFBhdGgpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb2Nlc3MgYSBsYXp5KCkgY2FsbFxuXHQgKi9cblx0cHJpdmF0ZSBwcm9jZXNzTGF6eUNhbGwgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBleGFjdCBjYWxsIGhhcyBhbHJlYWR5IGJlZW4gcHJvY2Vzc2VkIChwcmV2ZW50cyBkdXBsaWNhdGVzIGZyb20gY2hhaW5lZCBjYWxscylcblx0XHRpZiAodGhpcy5tYXJrUHJvY2Vzc2VkKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gR2V0IHRoZSB0eXBlIG5hbWUgYW5kIHNvdXJjZSBjb250ZXh0IGZyb20gYXJndW1lbnRzXG5cdFx0Y29uc3QgbGF6eUNvbnRleHQgPSB0aGlzLmV4dHJhY3RMYXp5Q29udGV4dChjYWxsLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIEZvciBjaGFpbmVkIGNhbGxzIGxpa2UgZGVmaW5lKCdBJykubGF6eSgnQicpLCB3ZSB3YW50IHRoZSBwb3NpdGlvbiBvZiB0aGUgLmxhenkoJ0InKSBwYXJ0XG5cdFx0Ly8gbm90IHRoZSBzdGFydCBvZiB0aGUgZW50aXJlIGV4cHJlc3Npb25cblx0XHRsZXQgcG9zaXRpb25Ob2RlOiB0cy5Ob2RlID0gY2FsbDtcblxuXHRcdC8vIElmIHRoaXMgaXMgYSBjaGFpbmVkIGNhbGwsIGdldCB0aGUgcG9zaXRpb24gb2YgdGhlIHByb3BlcnR5IGFjY2VzcyBleHByZXNzaW9uXG5cdFx0Ly8gd2hpY2ggaXMgdGhlIC5sYXp5IHBhcnRcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0Ly8gVGhlIGV4cHJlc3Npb24gaXMgdGhlIHByb3BlcnR5IGFjY2VzczogKGRlZmluZSgnUm9vdEFzeW5jJywgLi4uKSkubGF6eVxuXHRcdFx0Ly8gV2Ugd2FudCB0aGUgcG9zaXRpb24gb2YganVzdCB0aGUgLmxhenkgcGFydFxuXHRcdFx0Ly8gVGhpcyBpcyB0aGUgJ2xhenknIGlkZW50aWZpZXJcblx0XHRcdHBvc2l0aW9uTm9kZSA9IGNhbGwuZXhwcmVzc2lvbi5uYW1lO1xuXHRcdH1cblxuXHRcdGNvbnN0IHN0YXJ0UG9zID0gcG9zaXRpb25Ob2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpO1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihzb3VyY2VGaWxlLCBzdGFydFBvcyk7XG5cblx0XHRpZiAoIWxhenlDb250ZXh0LnR5cGVOYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdDb3VsZCBub3QgZXh0cmFjdCB0eXBlIG5hbWUgZnJvbSBsYXp5KCkgY2FsbCcsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyB0eXBlTmFtZSB9ID0gbGF6eUNvbnRleHQ7XG5cblx0XHQvLyBEZXRlcm1pbmUgcGFyZW50IHR5cGUgYW5kIGNvbGxlY3Rpb24gYmFzZWQgb24gdGhlIGNhbGwgc291cmNlLlxuXHRcdGNvbnN0IHBhcmVudE5vZGUgPSBsYXp5Q29udGV4dC5wYXJlbnRUeXBlO1xuXHRcdGNvbnN0IHsgY29sbGVjdGlvbklkIH0gPSBsYXp5Q29udGV4dDtcblxuXHRcdC8vIEV4dHJhY3QgY29uZmlnIG9wdGlvbnNcblx0XHRjb25zdCBjb25maWcgPSB0aGlzLmV4dHJhY3RMYXp5Q29uZmlnKGNhbGwpO1xuXG5cdFx0Ly8gQ3JlYXRlIHR5cGUgbm9kZSBmaXJzdCBzbyBpdHMgaW50ZXJuYWwgZnVsbFBhdGggKGluY2x1ZGluZyBhbnkgY29sbGVjdGlvbiBwcmVmaXgpIGlzIHJlc29sdmVkLlxuXHRcdGNvbnN0IG5vZGUgPSBUeXBlR3JhcGhJbXBsLmNyZWF0ZU5vZGUoXG5cdFx0XHR0eXBlTmFtZSxcblx0XHRcdHBhcmVudE5vZGUsXG5cdFx0XHRzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0bGluZSArIDEsXG5cdFx0XHRjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0Y29sbGVjdGlvbklkXG5cdFx0KTtcblx0XHRub2RlLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA9IHRoaXMuZ2V0UmVnaXN0cnlJbnRlcmZhY2VOYW1lKGNvbGxlY3Rpb25JZCk7XG5cblx0XHQvLyBTYW1lLW5hbWVzcGFjZSBkdXBsaWNhdGUgZGV0ZWN0aW9uIChoYXJkLWZhaWwgbGF3KVxuXHRcdHRoaXMucmVjb3JkRGVmaW5lU2l0ZShcblx0XHRcdHBhcmVudE5vZGUgPyBgJHtwYXJlbnROb2RlLmZ1bGxQYXRofS4ke3R5cGVOYW1lfWAgOiBgJHtjb2xsZWN0aW9uSWQgPz8gJ2RlZmF1bHQnfTo6JHt0eXBlTmFtZX1gLFxuXHRcdFx0YCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWBcblx0XHQpO1xuXG5cdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gdGhlIGNvbnN0cnVjdG9yIHJldHVybmVkIGJ5IHRoZSBsYXp5IGdldHRlclxuXHRcdC8vIOKAlCB0aGUgbmV3IG5vZGUgYW5jaG9ycyByZWxhdGl2ZS1maXJzdCBncmFwaCByZWZlcmVuY2UgcmVzb2x1dGlvblxuXHRcdGNvbnN0IHByZXZpb3VzQW5jaG9yID0gdGhpcy5jdXJyZW50R3JhcGhBbmNob3I7XG5cdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBub2RlO1xuXHRcdHRyeSB7XG5cdFx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzKGNhbGwpO1xuXG5cdFx0XHQvLyBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZm9yIFR5cGVSZWdpc3RyeSBzaWduYXR1cmVcblx0XHRcdG5vZGUuY29uc3RydWN0b3JQYXJhbXMgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyhjYWxsKTtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBwcmV2aW91c0FuY2hvcjtcblx0XHR9XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGhcblx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChwYXJlbnROb2RlLCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KG5vZGUpO1xuXHRcdH1cblxuXHRcdC8vIENyZWF0ZSBkZWZpbml0aW9uIGluZm8gdXNpbmcgdGhlIG5vZGUncyByZXNvbHZlZCBmdWxsUGF0aFxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiBwYXJlbnROb2RlID8gcGFyZW50Tm9kZS5mdWxsUGF0aCA6IG51bGwsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IGNvbmZpZy5zdHJpY3RDaGFpbiA/PyB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBjb25maWcuYmxvY2tFcnJvcnMgPz8gZmFsc2UsXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChub2RlLmZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0XHR0aGlzLmVkc1Njb3BlQnlOb2RlLnNldChjYWxsLCBub2RlLmZ1bGxQYXRoKTtcblxuXHRcdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnQ6IGNvbnN0IExhenlUeXBlID0gbGF6eSgnTGF6eVR5cGUnLCAuLi4pIC0+IG1hcCBcIkxhenlUeXBlXCIgLT4gXCJMYXp5VHlwZVwiXG5cdFx0Ly8gRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBjb25zdCBYID0gbGF6eSgnQScpLmRlZmluZSgnQicpLCB3ZSB3YW50IHRvIG1hcCBYIC0+IEEgKHRoZSByb290KVxuXHRcdHRoaXMudHJhY2tWYXJpYWJsZUFzc2lnbm1lbnQoY2FsbCwgcGFyZW50Tm9kZSwgbm9kZS5mdWxsUGF0aCk7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBsYXp5KCkgY2FsbCBhcmd1bWVudHMgaW50byBhIG5vcm1hbGl6ZWQgc2hhcGUuXG5cdCAqIEhhbmRsZXMgbmFtZWQvdW5uYW1lZCBhbmQgZXhwbGljaXQtc291cmNlIGZvcm1zLCBib3RoIGFzIGZyZWUgY2FsbHNcblx0ICogYW5kIGFzIG1ldGhvZCBjYWxscy5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdExhenlDYWxsQXJncyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7XG5cdFx0c291cmNlPzogdHMuRXhwcmVzc2lvbjtcblx0XHRuYW1lPzogc3RyaW5nO1xuXHRcdGdldHRlcjogdHMuRXhwcmVzc2lvbjtcblx0XHRjb25maWc/OiB0cy5FeHByZXNzaW9uO1xuXHR9IHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBhcmdzID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0Y29uc3QgaXNNZXRob2RDYWxsID0gdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKTtcblxuXHRcdGlmIChpc01ldGhvZENhbGwpIHtcblx0XHRcdC8vIFNvdXJjZSBpcyB0aGUgb2JqZWN0IG9mIHRoZSBwcm9wZXJ0eSBhY2Nlc3M6IFR5cGUubGF6eSguLi4pXG5cdFx0XHRjb25zdCBzb3VyY2UgPSBjYWxsLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgWyBtZXRob2RGaXJzdEFyZyBdID0gYXJncztcblx0XHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwobWV0aG9kRmlyc3RBcmcpKSB7XG5cdFx0XHRcdC8vIFR5cGUubGF6eSgnTmFtZScsIGdldHRlciwgY29uZmlnPylcblx0XHRcdFx0aWYgKGFyZ3MubGVuZ3RoIDwgMikge1xuXHRcdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHRzb3VyY2UsXG5cdFx0XHRcdFx0bmFtZSAgIDogbWV0aG9kRmlyc3RBcmcudGV4dCxcblx0XHRcdFx0XHRnZXR0ZXIgOiBhcmdzWyAxIF0sXG5cdFx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMiBdLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXHRcdFx0Ly8gVHlwZS5sYXp5KGdldHRlciwgY29uZmlnPylcblx0XHRcdHJldHVybiB7XG5cdFx0XHRcdHNvdXJjZSxcblx0XHRcdFx0Z2V0dGVyIDogbWV0aG9kRmlyc3RBcmcsXG5cdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDEgXSxcblx0XHRcdH07XG5cdFx0fVxuXG5cdFx0Ly8gRnJlZSBjYWxsOiBsYXp5KC4uLilcblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgWyBmaXJzdEFyZyBdID0gYXJncztcblxuXHRcdC8vIEV4cGxpY2l0LXNvdXJjZSBmb3JtOiBsYXp5KHNvdXJjZSwgJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0Ly8gb3IgbGF6eShzb3VyY2UsIGdldHRlciwgY29uZmlnPylcblx0XHRpZiAoYXJncy5sZW5ndGggPj0gMiAmJiB0cy5pc0lkZW50aWZpZXIoZmlyc3RBcmcpKSB7XG5cdFx0XHRjb25zdCBbICwgc2Vjb25kQXJnIF0gPSBhcmdzO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChzZWNvbmRBcmcpKSB7XG5cdFx0XHRcdC8vIGxhenkoc291cmNlLCAnTmFtZScsIGdldHRlciwgY29uZmlnPylcblx0XHRcdFx0aWYgKGFyZ3MubGVuZ3RoIDwgMykge1xuXHRcdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHRzb3VyY2UgOiBmaXJzdEFyZyxcblx0XHRcdFx0XHRuYW1lICAgOiBzZWNvbmRBcmcudGV4dCxcblx0XHRcdFx0XHRnZXR0ZXIgOiBhcmdzWyAyIF0sXG5cdFx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMyBdLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXHRcdFx0Ly8gbGF6eShzb3VyY2UsIGdldHRlciwgY29uZmlnPylcblx0XHRcdHJldHVybiB7XG5cdFx0XHRcdHNvdXJjZSA6IGZpcnN0QXJnLFxuXHRcdFx0XHRnZXR0ZXIgOiBzZWNvbmRBcmcsXG5cdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDIgXSxcblx0XHRcdH07XG5cdFx0fVxuXG5cdFx0Ly8gTmFtZWQgcm9vdCBmb3JtOiBsYXp5KCdOYW1lJywgZ2V0dGVyLCBjb25maWc/KVxuXHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoZmlyc3RBcmcpKSB7XG5cdFx0XHRpZiAoYXJncy5sZW5ndGggPCAyKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRuYW1lICAgOiBmaXJzdEFyZy50ZXh0LFxuXHRcdFx0XHRnZXR0ZXIgOiBhcmdzWyAxIF0sXG5cdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDIgXSxcblx0XHRcdH07XG5cdFx0fVxuXG5cdFx0Ly8gVW5uYW1lZCByb290IGZvcm06IGxhenkoZ2V0dGVyLCBjb25maWc/KVxuXHRcdHJldHVybiB7XG5cdFx0XHRnZXR0ZXIgOiBmaXJzdEFyZyxcblx0XHRcdGNvbmZpZyA6IGFyZ3NbIDEgXSxcblx0XHR9O1xuXHR9XG5cblx0LyoqXG5cdCAqIFVud3JhcCB0aGUgY29uc3RydWN0b3IgcmV0dXJuZWQgYnkgYSBsYXp5IGdldHRlci5cblx0ICogU3VwcG9ydHM6XG5cdCAqICAgKCkgPT4gY2xhc3MgTmFtZSB7fVxuXHQgKiAgICgpID0+IGZ1bmN0aW9uIE5hbWUoKSB7fVxuXHQgKiAgICgpID0+IHsgcmV0dXJuIGNsYXNzIE5hbWUge307IH1cblx0ICogICBmdW5jdGlvbiAoKSB7IHJldHVybiBmdW5jdGlvbiBOYW1lKCkge307IH1cblx0ICovXG5cdHByaXZhdGUgdW53cmFwTGF6eUdldHRlciAoZ2V0dGVyRXhwcjogdHMuRXhwcmVzc2lvbik6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc0Fycm93RnVuY3Rpb24oZ2V0dGVyRXhwcikpIHtcblx0XHRcdGNvbnN0IHsgYm9keSB9ID0gZ2V0dGVyRXhwcjtcblx0XHRcdGlmICghdHMuaXNCbG9jayhib2R5KSkge1xuXHRcdFx0XHRyZXR1cm4gYm9keTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3Qgc3RtdCBvZiBib2R5LnN0YXRlbWVudHMpIHtcblx0XHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KHN0bXQpICYmIHN0bXQuZXhwcmVzc2lvbikge1xuXHRcdFx0XHRcdHJldHVybiBzdG10LmV4cHJlc3Npb247XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGdldHRlckV4cHIpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGdldHRlckV4cHI7XG5cdFx0XHRmb3IgKGNvbnN0IHN0bXQgb2YgYm9keS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChzdG10KSAmJiBzdG10LmV4cHJlc3Npb24pIHtcblx0XHRcdFx0XHRyZXR1cm4gc3RtdC5leHByZXNzaW9uO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIE5vdCBhIHJlY29nbml6ZWQgZ2V0dGVyIHBhdHRlcm5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgYSBjb25zdHJ1Y3RvciBuYW1lIGZyb20gYSBjbGFzcyBleHByZXNzaW9uLCBjbGFzcyBkZWNsYXJhdGlvbixcblx0ICogb3IgbmFtZWQgZnVuY3Rpb24gZXhwcmVzc2lvbi5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENvbnN0cnVjdG9yTmFtZSAoY29uc3RydWN0b3JFeHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSAmJiBjb25zdHJ1Y3RvckV4cHIubmFtZSkge1xuXHRcdFx0cmV0dXJuIGNvbnN0cnVjdG9yRXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0NsYXNzRGVjbGFyYXRpb24oY29uc3RydWN0b3JFeHByKSAmJiBjb25zdHJ1Y3RvckV4cHIubmFtZSkge1xuXHRcdFx0cmV0dXJuIGNvbnN0cnVjdG9yRXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpICYmIGNvbnN0cnVjdG9yRXhwci5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gY29uc3RydWN0b3JFeHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSB0eXBlIG5hbWUgZnJvbSBlaXRoZXIgYSBkZWZpbmUoKSBvciBsYXp5KCkgY2FsbC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRoaXMuaXNEZWZpbmVDYWxsKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5leHRyYWN0VHlwZU5hbWUoY2FsbCk7XG5cdFx0fVxuXHRcdGlmICh0aGlzLmlzTGF6eUNhbGwoY2FsbCkpIHtcblx0XHRcdGNvbnN0IGFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0XHRpZiAoIWFyZ3MpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGlmIChhcmdzLm5hbWUpIHtcblx0XHRcdFx0cmV0dXJuIGFyZ3MubmFtZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMudW53cmFwTGF6eUdldHRlcihhcmdzLmdldHRlcik7XG5cdFx0XHRpZiAoY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRcdHJldHVybiB0aGlzLmV4dHJhY3RDb25zdHJ1Y3Rvck5hbWUoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSBmdWxsIGxhenkoKSBjYWxsIGNvbnRleHQ6IHR5cGUgbmFtZSwgcGFyZW50IHR5cGUsIGFuZCBjb2xsZWN0aW9uLlxuXHQgKiBIYW5kbGVzIGRpcmVjdCBjYWxscywgcHJvcGVydHktYWNjZXNzIGNhbGxzLCBjaGFpbmVkIGNhbGxzLCBhbmQgdGhlXG5cdCAqIGV4cGxpY2l0LXNvdXJjZSBmb3JtIGBsYXp5KHNvdXJjZSwgJ1R5cGVOYW1lJywgZ2V0dGVyKWAuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q29udGV4dCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB7XG5cdFx0dHlwZU5hbWU/OiBzdHJpbmc7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Y29uc3QgYXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRpZiAoIWFyZ3MpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRsZXQgdHlwZU5hbWU6IHN0cmluZyB8IHVuZGVmaW5lZCA9IGFyZ3MubmFtZTtcblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLnVud3JhcExhenlHZXR0ZXIoYXJncy5nZXR0ZXIpO1xuXHRcdFx0aWYgKGNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0XHR0eXBlTmFtZSA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yTmFtZShjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBjYWxsO1xuXG5cdFx0Ly8gRGlyZWN0IGNhbGw6IGxhenkoJ1R5cGVOYW1lJywgLi4uKSBvciBsYXp5KHNvdXJjZSwgJ1R5cGVOYW1lJywgZ2V0dGVyKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnbGF6eScpIHtcblx0XHRcdGlmIChhcmdzLnNvdXJjZSAmJiB0cy5pc0lkZW50aWZpZXIoYXJncy5zb3VyY2UpKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2UoYXJncy5zb3VyY2UudGV4dCk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXHRcdFx0Ly8gUGxhaW4gcm9vdCBsYXp5IGluIGRlZmF1bHQgY29sbGVjdGlvblxuXHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUgfTtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSBhY2Nlc3M6IFgubGF6eSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnbGF6eScpIHtcblx0XHRcdGNvbnN0IG9iaiA9IGV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblxuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihvYmopKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uob2JqLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0XHRcdHBhcmVudFR5cGUgICA6IHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSxcblx0XHRcdFx0XHRjb2xsZWN0aW9uSWQgOiBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCxcblx0XHRcdFx0fTtcblx0XHRcdH1cblxuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gTmVzdGVkIGFjY2VzczogaW5zdGFuY2UuVHlwZS5sYXp5IC0gdHJ5IHRvIHJlc29sdmVcblx0XHRcdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4ob2JqKTtcblx0XHRcdFx0aWYgKGNoYWluLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShjaGFpbi5qb2luKCcuJykpO1xuXHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSB9O1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gRGV0ZXJtaW5lIHRoZSBjb2xsZWN0aW9uIGNvbnRleHQgZnJvbSB0aGUgcm9vdCBvZiB0aGUgY2hhaW4gc28gdGhhdFxuXHRcdFx0XHQvLyBjdXN0b20tY29sbGVjdGlvbiB0eXBlcyBkbyBub3QgZ2V0IGNvbmZ1c2VkIHdpdGggZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzLlxuXHRcdFx0XHRjb25zdCByb290SWQgPSB0aGlzLmdldFJvb3RJZGVudGlmaWVyKG9iai5leHByZXNzaW9uKTtcblx0XHRcdFx0Y29uc3QgZXhwZWN0ZWRDb2xsZWN0aW9uSWQgPSByb290SWRcblx0XHRcdFx0XHQ/IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShyb290SWQudGV4dCkuY29sbGVjdGlvbklkXG5cdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHRcdFx0Ly8gQ2hhaW5lZCBjYWxsOiBkZWZpbmUoJ0EnKS5sYXp5KCdCJykgb3IgbGF6eSgnQScpLmxhenkoJ0InKVxuXHRcdFx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwob2JqKSkge1xuXHRcdFx0XHRcdHRoaXMucHJvY2Vzc0RlZmluZUNhbGwob2JqLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRpZiAodGhpcy5pc0xhenlDYWxsKG9iaikpIHtcblx0XHRcdFx0XHR0aGlzLnByb2Nlc3NMYXp5Q2FsbChvYmosIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudFR5cGVOYW1lID0gdGhpcy5leHRyYWN0TW5lbW9uaWNhVHlwZU5hbWUob2JqKTtcblx0XHRcdFx0XHRpZiAocGFyZW50VHlwZU5hbWUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKHBhcmVudFR5cGVOYW1lLCBleHBlY3RlZENvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIEJ1aWxkZXIgbG9va3VwIGNoYWluOiBBcHAubG9va3VwKCdVc2VyJykubGF6eSgnQWRtaW4nKVxuXHRcdFx0XHRpZiAodGhpcy5pc0xvb2t1cENhbGwob2JqKSkge1xuXHRcdFx0XHRcdGNvbnN0IGxvb2tlZFVwUGF0aCA9IHRoaXMucmVzb2x2ZUxvb2t1cFBhdGgob2JqKTtcblx0XHRcdFx0XHRpZiAobG9va2VkVXBQYXRoKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShsb29rZWRVcFBhdGgpO1xuXHRcdFx0XHRcdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlLmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBjb25maWcgb3B0aW9ucyBmcm9tIGxhenkoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q29uZmlnIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSB7XG5cdFx0Y29uc3QgYXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRpZiAoIWFyZ3MgfHwgIWFyZ3MuY29uZmlnIHx8ICF0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGFyZ3MuY29uZmlnKSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IGNvbmZpZ1Jlc3VsdCA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGFyZ3MuY29uZmlnKTtcblx0XHRyZXR1cm4gY29uZmlnUmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0KiBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50cyB0aGF0IGNhcHR1cmUgZGVmaW5lKCkgcmVzdWx0c1xuXHRcdCogZS5nLiwgY29uc3QgVXNlciA9IGRlZmluZSgnVXNlckVudGl0eScsIC4uLikgbWFwcyBcIlVzZXJcIiAtPiBcIlVzZXJFbnRpdHlcIlxuXHRcdCogRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBjb25zdCBYID0gZGVmaW5lKCdBJykuZGVmaW5lKCdCJyksIHdlIG1hcCBYIC0+IEEgKHRoZSByb290IHR5cGUpXG5cdFx0Ki9cblx0cHJpdmF0ZSB0cmFja1ZhcmlhYmxlQXNzaWdubWVudCAoXG5cdFx0Y2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0cGFyZW50Tm9kZTogVHlwZU5vZGUgfCB1bmRlZmluZWQsXG5cdFx0ZnVsbFBhdGg6IHN0cmluZ1xuXHQpOiB2b2lkIHtcblx0XHQvLyBDaGVjayBpZiB0aGlzIGNhbGwgaXMgdGhlIHJpZ2h0LWhhbmQgc2lkZSBvZiBhIHZhcmlhYmxlIGRlY2xhcmF0aW9uXG5cdFx0Ly8gV2FsayB1cCB0aGUgdHJlZSB0byBmaW5kIFZhcmlhYmxlRGVjbGFyYXRpb25cblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IGNhbGwucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRcdC8vIEZvdW5kOiBjb25zdCBYID0gZGVmaW5lKC4uLilcblx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50Lm5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgdmFyTmFtZSA9IGN1cnJlbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRcdC8vIEYxODogZGVmaW5lKCkgcmV0dXJucyB0aGUgREVGSU5FRCB0eXBlJ3MgY29uc3RydWN0b3IsXG5cdFx0XHRcdFx0Ly8gc28gYSBjb25zdCBob2xkaW5nIGEgbXVsdGktaG9wIGluaXRpYWxpemVyXG5cdFx0XHRcdFx0Ly8gKGBjb25zdCBYID0gQS5kZWZpbmUoJ0InKS5kZWZpbmUoJ0MnKWApIGJpbmRzIHRoZSBMQVNUXG5cdFx0XHRcdFx0Ly8gaG9wIOKAlCBhIGRlZXBlciBob3AgbXVzdCBub3QgYmluZCwgYW5kIHRoZSBvdXRlcm1vc3Rcblx0XHRcdFx0XHQvLyBob3AgYmluZHMgdW5jb25kaXRpb25hbGx5ICh2aXNpdC1vcmRlciBpbmRlcGVuZGVudClcblx0XHRcdFx0XHRpZiAodGhpcy5pc0RlZXBlckRlZmluZUhvcChjYWxsKSkge1xuXHRcdFx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHQvLyBGb3IgY2hhaW5lZCBsYXp5IGNhbGxzIGxpa2UgY29uc3QgWCA9IGRlZmluZSgnQScpLmxhenkoJ0InKSxcblx0XHRcdFx0XHQvLyB0aGUgZmlyc3QgY2FsbCBpbiB0aGUgY2hhaW4gc2V0cyB0aGUgbWFwcGluZyAobGF6eSBob3Bcblx0XHRcdFx0XHQvLyBrZWVwcyBpdCDigJQgcGlubmVkIGJlaGF2aW9yKVxuXHRcdFx0XHRcdGlmIChwYXJlbnROb2RlICYmIHRoaXMudmFyaWFibGVUb1R5cGVNYXAuaGFzKHZhck5hbWUpKSB7XG5cdFx0XHRcdFx0XHRyZXR1cm47XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdHRoaXMudmFyaWFibGVUb1R5cGVNYXAuc2V0KHZhck5hbWUsIGZ1bGxQYXRoKTtcblx0XHRcdFx0XHR0aGlzLnRyYWNrRmlsZUdyYXBoQmluZGluZyh2YXJOYW1lLCBmdWxsUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBBIGAuZGVmaW5lKC4uLilgIGhvcCB3cmFwcGVkIGJ5IGFub3RoZXIgYC5kZWZpbmUoLi4uKWAgY2FsbCBpcyBub3Rcblx0ICogdGhlIHZhbHVlIGl0cyBjb25zdCBlbmRzIHVwIGhvbGRpbmcg4oCUIHRoZSBPVVRFUk1PU1QgaG9wIG9mIHRoZVxuXHQgKiBpbml0aWFsaXplciBjaGFpbiBpcyAoZGVmaW5lKCkgcmV0dXJucyB0aGUgZGVmaW5lZCB0eXBlJ3Ncblx0ICogY29uc3RydWN0b3IpLiBPbmx5IHRoZSBvdXRlcm1vc3QgaG9wIG1heSBiaW5kIHRoZSB2YXJpYWJsZS5cblx0ICovXG5cdHByaXZhdGUgaXNEZWVwZXJEZWZpbmVIb3AgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgeyBwYXJlbnQgfSA9IGNhbGw7XG5cdFx0Y29uc3QgZGVlcGVyID0gISFwYXJlbnQgJiZcblx0XHRcdHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKHBhcmVudCkgJiZcblx0XHRcdHBhcmVudC5uYW1lLnRleHQgPT09ICdkZWZpbmUnICYmXG5cdFx0XHR0cy5pc0NhbGxFeHByZXNzaW9uKHBhcmVudC5wYXJlbnQpICYmXG5cdFx0XHRwYXJlbnQucGFyZW50LmV4cHJlc3Npb24gPT09IHBhcmVudDtcblx0XHRyZXR1cm4gZGVlcGVyO1xuXHR9XG5cblx0LyoqXG5cdCAqIE1pcnJvciBhIHZhcmlhYmxlIC0+IG1uZW1vbmljYSBmdWxsUGF0aCBiaW5kaW5nIGludG8gdGhlIHBlci1maWxlXG5cdCAqIHZhbHVlLXNjb3BlIG1hcCAoZ3JhcGggaWRlbnRpdHkgbGF3OiBgdHlwZW9mIFhgIGFuZCBiYXJlIHJlZmVyZW5jZXNcblx0ICogcmVzb2x2ZSB0aHJvdWdoIHRoZSBmaWxlJ3Mgb3duIGJpbmRpbmdzIGZpcnN0KS5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tGaWxlR3JhcGhCaW5kaW5nICh2YXJOYW1lOiBzdHJpbmcsIGZ1bGxQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRsZXQgYmluZGluZ3MgPSB0aGlzLmZpbGVHcmFwaEJpbmRpbmdzLmdldChmaWxlUGF0aCk7XG5cdFx0aWYgKCFiaW5kaW5ncykge1xuXHRcdFx0YmluZGluZ3MgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0dGhpcy5maWxlR3JhcGhCaW5kaW5ncy5zZXQoZmlsZVBhdGgsIGJpbmRpbmdzKTtcblx0XHR9XG5cdFx0YmluZGluZ3Muc2V0KHZhck5hbWUsIGZ1bGxQYXRoKTtcblx0fVxuXHRcblx0LyoqXG5cdFx0KiBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50cyBmcm9tIGxvb2t1cCgpIGNhbGxzXG5cdFx0KiBlLmcuLCBjb25zdCBTZW50aWVuY2VDb25zdHJ1Y3RvciA9IGxvb2t1cCgnU2VudGllbmNlJykgbWFwcyBcIlNlbnRpZW5jZUNvbnN0cnVjdG9yXCIgLT4gXCJTZW50aWVuY2VcIlxuXHRcdCovXG5cdHByaXZhdGUgdHJhY2tMb29rdXBBc3NpZ25tZW50IChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgdHlwZVBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdHRoaXMuYmluZFJlc3VsdFZhcmlhYmxlKGNhbGwsIHR5cGVQYXRoKTtcblx0fVxuXG5cdC8qKlxuXHRcdCogVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHMgZnJvbSBuZXcgVHlwZSgpIGNhbGxzXG5cdFx0KiBlLmcuLCBjb25zdCB1c2VyID0gbmV3IFVzZXJUeXBlKCkgbWFwcyBcInVzZXJcIiAtPiBcIlVzZXJUeXBlXCJcblx0XHQqL1xuXHRwcml2YXRlIHRyYWNrTmV3QXNzaWdubWVudCAobmV3RXhwcjogdHMuTmV3RXhwcmVzc2lvbiwgdHlwZVBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdGxldCBlZmZlY3RpdmVQYXRoID0gdHlwZVBhdGg7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBuZXdFeHByLnBhcmVudDtcblx0XHQvLyBDaGFpbi1mb3JtIGNvbnN0cnVjdGlvbjogbmV3IFIoKS5BKCkuQigpIOKAlCB0aGUgcmVzdWx0IHZhcmlhYmxlXG5cdFx0Ly8gaG9sZHMgdGhlIE9VVEVSTU9TVCB0aXAncyBpbnN0YW5jZSAoYXdhaXQtdHJhbnNwYXJlbnQpLCBub3QgdGhlXG5cdFx0Ly8gaW5uZXIgbmV3J3MgdHlwZS4gV2FsayB0aGUgY2hhaW4sIGtlZXBpbmcgdGhlIGxhc3QgcmVzb2x2YWJsZSB0aXAuXG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdXJyZW50KSAmJlxuXHRcdFx0XHR0cy5pc0NhbGxFeHByZXNzaW9uKGN1cnJlbnQucGFyZW50KSAmJlxuXHRcdFx0XHRjdXJyZW50LnBhcmVudC5leHByZXNzaW9uID09PSBjdXJyZW50KSB7XG5cdFx0XHRcdGNvbnN0IHRpcCA9IHRoaXMucmVzb2x2ZUNoYWluVGlwVHlwZVBhdGgoY3VycmVudC5wYXJlbnQpO1xuXHRcdFx0XHRpZiAodGlwKSB7XG5cdFx0XHRcdFx0ZWZmZWN0aXZlUGF0aCA9IHRpcDtcblx0XHRcdFx0fVxuXHRcdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQucGFyZW50O1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGJyZWFrO1xuXHRcdH1cblx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShuZXdFeHByLCBlZmZlY3RpdmVQYXRoKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBCaW5kIHRoZSBuZWFyZXN0IGVuY2xvc2luZyBgY29uc3QvbGV0L3ZhciBYID0g4oCmYCB0byBhIG1uZW1vbmljYVxuXHQgKiBmdWxsUGF0aCDigJQgdGhlIHNoYXJlZCByZXN1bHQtdmFyaWFibGUgd2Fsa2VyIGJlaGluZCBuZXcvbG9va3VwL1xuXHQgKiBjaGFpbi9mb3JrL21lcmdlL2NhbGwgdHJhY2tpbmcgKHZhbHVlIHNjb3BlOiBkb3duc3RyZWFtIHJlZmVyZW5jZXNcblx0ICogYW5kIGB0aGlzLnggPSB4YCBhc3NpZ25tZW50cyByZXNvbHZlIHRocm91Z2ggdGhlIHNhbWUgYmluZGluZykuXG5cdCAqL1xuXHRwcml2YXRlIGJpbmRSZXN1bHRWYXJpYWJsZSAoZnJvbTogdHMuTm9kZSwgdHlwZVBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gZnJvbS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24oY3VycmVudCkpIHtcblx0XHRcdFx0Ly8gRm91bmQ6IGNvbnN0IFggPSA8Y29uc3RydWN0aW9uPlxuXHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCB2YXJOYW1lID0gY3VycmVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0dGhpcy52YXJpYWJsZVRvVHlwZU1hcC5zZXQodmFyTmFtZSwgdHlwZVBhdGgpO1xuXHRcdFx0XHRcdHRoaXMudHJhY2tGaWxlR3JhcGhCaW5kaW5nKHZhck5hbWUsIHR5cGVQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm47XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhbiBgaW5zdGFudGlhdGlvbmAgdXNhZ2UgZm9yIGEgY29uc3RydWN0aW9uLXNoYXBlIGNhbGxcblx0ICogKGNoYWluIHRpcCAvIGNhbGwgLyBhcHBseSAvIGZvcmsgLyBjbG9uZSAvIG1lcmdlIOKAlFxuXHQgKiBieXRlLWluZGlzdGluZ3Vpc2hhYmxlIGZyb20gYG5ld2AgdW50aWwgdGhlIGRlZmVycmVkXG5cdCAqIG1lY2hhbmlzbS1raW5kIHJldmlzaW9uKS4gYGNvbnN0cnVjdG9yVGV4dGAgZGVmYXVsdHMgdG8gdGhlIGNhbGxlZVxuXHQgKiBleHByZXNzaW9uIHRleHQgc28gdGhlIHNpdGUgc3RheXMgcmVhZGFibGUgd2l0aG91dCBuZXcgZmllbGRzO1xuXHQgKiBjYWxsL2FwcGx5IG92ZXJyaWRlIGl0IHdpdGggdGhlIEN0b3IgYXJndW1lbnQgdGV4dC5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkQ29uc3RydWN0aW9uVXNhZ2UgKFxuXHRcdGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLFxuXHRcdHR5cGVQYXRoOiBzdHJpbmcsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRjb25zdHJ1Y3RvclRleHQ/OiBzdHJpbmdcblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdGNhbGwuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGN0b3JUZXh0ID0gY29uc3RydWN0b3JUZXh0ID8/IGNhbGwuZXhwcmVzc2lvbi5nZXRUZXh0KHNvdXJjZUZpbGUpO1xuXHRcdHRoaXMuYWRkVXNhZ2UodHlwZVBhdGgsIHtcblx0XHRcdGxvY2F0aW9uICAgICAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0Y29kZSAgICAgICAgICAgIDogY2FsbC5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRjb25zdHJ1Y3RvclRleHQgOiBjdG9yVGV4dC5zbGljZSgwLCAxMDApLFxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgdGhlIHR5cGUgYSBjb25zdHJ1Y3Rpb24tY2hhaW4gdGlwIGNhbGwgY29uc3RydWN0czpcblx0ICogYG5ldyBSKC4uLikuQSguLi4pYCBjb25zdHJ1Y3RzIFIuQTsgYGF3YWl0IG5ldyBSKC4uLikuQSguLi4pLkIoLi4uKWBcblx0ICogY29uc3RydWN0cyBSLkEuQi4gVGhlIHJlY2VpdmVyIGlzIHRoZSBuZXN0ZWQgY2hhaW4gKE5ld0V4cHJlc3Npb25cblx0ICogYmFzZSwgdGhlbiB0aXAgY2FsbHMpOyBleGFjdCBmdWxsUGF0aCBmaXJzdCwgYW5kIG9ubHkgd2hlbiB0aGUgcm9vdFxuXHQgKiBpdHNlbGYgaXMgdW5rbm93biBkb2VzIHRoZSBwcm9wLW5hbWUgZmFsbGJhY2sgbGF3IGFwcGx5IChzbyBwbGFpblxuXHQgKiBtZXRob2QgY2FsbHMgb24gZnJlc2ggaW5zdGFuY2VzIG5ldmVyIHJlY29yZCBhIGNvbnN0cnVjdGlvbikuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVDaGFpblRpcFR5cGVQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZWNlaXZlciA9IGNhbGwuZXhwcmVzc2lvbjtcblx0XHRsZXQgcm9vdFBhdGg6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRpZiAodHMuaXNOZXdFeHByZXNzaW9uKHJlY2VpdmVyLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRjb25zdCBpbm5lciA9IHJlY2VpdmVyLmV4cHJlc3Npb247XG5cdFx0XHRyb290UGF0aCA9IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGlubmVyLmV4cHJlc3Npb24pXG5cdFx0XHRcdD8gdGhpcy5yZXNvbHZlVHlwZVBhdGgoaW5uZXIuZXhwcmVzc2lvbilcblx0XHRcdFx0OiB0aGlzLmdldFR5cGVOYW1lRnJvbUV4cHJlc3Npb24oaW5uZXIuZXhwcmVzc2lvbik7XG5cdFx0fSBlbHNlIGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKHJlY2VpdmVyLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyb290UGF0aCA9IHRoaXMucmVzb2x2ZUNoYWluVGlwVHlwZVBhdGgocmVjZWl2ZXIuZXhwcmVzc2lvbik7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGlmICghcm9vdFBhdGgpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGNhbmRpZGF0ZSA9IGAke3Jvb3RQYXRofS4ke3JlY2VpdmVyLm5hbWUudGV4dH1gO1xuXHRcdGlmICh0aGlzLmRlZmluaXRpb25zLmhhcyhjYW5kaWRhdGUpKSB7XG5cdFx0XHRyZXR1cm4gY2FuZGlkYXRlO1xuXHRcdH1cblx0XHRpZiAoIXRoaXMuZGVmaW5pdGlvbnMuaGFzKHJvb3RQYXRoKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMucmVzb2x2ZVR5cGVQYXRoKHJlY2VpdmVyKTtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBUcnVlIHdoZW4gYGV4cHJgIGRlbm90ZXMgYSBjb25zdHJ1Y3Rpb24gZnVuY3Rpb24gaW1wb3J0ZWQgZnJvbVxuXHQgKiAnbW5lbW9uaWNhJyDigJQgdGhlIG5hbWVkLWltcG9ydCBmb3JtIChgaW1wb3J0IHsgY2FsbCB9IGZyb21cblx0ICogJ21uZW1vbmljYSdgLCBhbGlhc2VzIGluY2x1ZGVkKSBvciBhIG1lbWJlciBvZiBhIHRyYWNrZWRcblx0ICogbW9kdWxlLW9iamVjdCBhbGlhcyAoYG1uZW1vbmljYS5jYWxsYCkuIFVzZXJsYW5kIGNhbGwvYXBwbHkvYmluZFxuXHQgKiBmdW5jdGlvbnMgbmV2ZXIgbWF0Y2guXG5cdCAqL1xuXHRwcml2YXRlIGlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4gKGV4cHI6IHRzLkV4cHJlc3Npb24sIGZuOiAnY2FsbCcgfCAnYXBwbHknIHwgJ2JpbmQnKTogYm9vbGVhbiB7XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLm1uZW1vbmljYU5hbWVkSW1wb3J0cy5nZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKT8uZ2V0KGV4cHIudGV4dCk7XG5cdFx0XHRjb25zdCBtYXRjaGVkID0gaW1wb3J0ZWQgPT09IGZuO1xuXHRcdFx0cmV0dXJuIG1hdGNoZWQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSAmJiBleHByLm5hbWUudGV4dCA9PT0gZm4pIHtcblx0XHRcdGNvbnN0IG1hdGNoZWQgPSB0cy5pc0lkZW50aWZpZXIoZXhwci5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoZXhwci5leHByZXNzaW9uLnRleHQpO1xuXHRcdFx0cmV0dXJuIG1hdGNoZWQ7XG5cdFx0fVxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBtbmVtb25pY2EgY2FsbC9hcHBseShlbnRpdHksIEN0b3IsIC4uLikgLyBiaW5kKGVudGl0eSwgQ3Rvcik6XG5cdCAqIHJlc29sdmUgdGhlIEN0b3IgYXJndW1lbnQgKGFyZyAxKSB0byBhIGdyYXBoIGZ1bGxQYXRoIHRocm91Z2ggdGhlXG5cdCAqIHNhbWUgdGllcnMgYXMgdGhlIGBuZXdgIGJyYW5jaCAodmFsdWUgc2NvcGUgZm9yIGlkZW50aWZpZXJzLFxuXHQgKiBjaGFpbiByZXNvbHV0aW9uIGZvciBwcm9wZXJ0eSBhY2Nlc3NlcykuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVDb25zdHJ1Y3Rpb25GblR5cGVQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2FsbGVlID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGNvbnN0IGlzQ2FsbE9yQXBwbHkgPSB0aGlzLmlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4oY2FsbGVlLCAnY2FsbCcpIHx8XG5cdFx0XHR0aGlzLmlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4oY2FsbGVlLCAnYXBwbHknKTtcblx0XHRjb25zdCBpc0JpbmQgPSB0aGlzLmlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4oY2FsbGVlLCAnYmluZCcpO1xuXHRcdGlmICghaXNDYWxsT3JBcHBseSAmJiAhaXNCaW5kKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRpZiAoY2FsbC5hcmd1bWVudHMubGVuZ3RoIDwgMikge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgWyAsIGN0b3JBcmcgXSA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGxldCByZXNvbHZlZDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdG9yQXJnKSkge1xuXHRcdFx0cmVzb2x2ZWQgPSB0aGlzLnJlc29sdmVUeXBlUGF0aChjdG9yQXJnKTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihjdG9yQXJnKSkge1xuXHRcdFx0Y29uc3QgYm91bmQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChjdG9yQXJnLnRleHQpO1xuXHRcdFx0aWYgKGJvdW5kKSB7XG5cdFx0XHRcdHJlc29sdmVkID0gYm91bmQ7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRjb25zdCBncmFwaFJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUoY3RvckFyZy50ZXh0KTtcblx0XHRcdFx0aWYgKGdyYXBoUmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdFx0XHRyZXNvbHZlZCA9IGdyYXBoUmVzdWx0Lm5vZGUuZnVsbFBhdGg7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc3Qga25vd24gPSByZXNvbHZlZCAmJiB0aGlzLmRlZmluaXRpb25zLmhhcyhyZXNvbHZlZCkgPyByZXNvbHZlZCA6IHVuZGVmaW5lZDtcblx0XHRyZXR1cm4ga25vd247XG5cdH1cblxuXHQvKipcblx0ICogaW5zdGFuY2UuZm9yayguLi4pIC8gaW5zdGFuY2UuY2xvbmUoLi4uKSBvbiBhIHRyYWNrZWQgdmFyaWFibGUg4oCUXG5cdCAqIHJ1bnRpbWUgcmV0dXJucyBgdGhpc2AsIHNvIHRoZSByZXN1bHQgY2FycmllcyB0aGUgc291cmNlIHR5cGUuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVGb3JrTGlrZVR5cGVQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBtZXRob2QgPSBjYWxsLmV4cHJlc3Npb24ubmFtZS50ZXh0O1xuXHRcdGlmIChtZXRob2QgIT09ICdmb3JrJyAmJiBtZXRob2QgIT09ICdjbG9uZScpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlY2VpdmVyID0gY2FsbC5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIocmVjZWl2ZXIpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChyZWNlaXZlci50ZXh0KTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEZyZWUgdXRpbHMgZm9ybXM6IHV0aWxzLm1lcmdlKGEsIGIsIC4uLikgKGFsc28gdGhlIGRpcmVjdCBuYW1lZFxuXHQgKiBpbXBvcnQgYG1lcmdlKGEsIGIpYCkgYW5kIHRoZSBjdXJyaWVkIHV0aWxzLmZvcmsoaW5zdGFuY2UpKC4uLikuXG5cdCAqIFRoZSByZXN1bHQgYmluZHMgdG8gYXJnIDAncyB0eXBlIOKAlCBydW50aW1lIHJldHVybnMgYSdzIGxpbmVhZ2Ugb3ZlclxuXHQgKiBiJ3MgY29udGV4dDsgYSdzIGZ1bGxQYXRoIGlzIHRoZSBob25lc3QgYXBwcm94aW1hdGlvbiB3aXRoaW4gdGhlXG5cdCAqIG91dHB1dCBjb250cmFjdCAoZG9jdW1lbnRlZCBpbiBSRUFETUUpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlVXRpbHNGblR5cGVQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2FsbGVlID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGNvbnN0IGlzVXRpbHNPd25lciA9IChvd25lcjogdHMuRXhwcmVzc2lvbik6IGJvb2xlYW4gPT4ge1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihvd25lcikpIHtcblx0XHRcdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLm1uZW1vbmljYU5hbWVkSW1wb3J0cy5nZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKT8uZ2V0KG93bmVyLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4gaW1wb3J0ZWQgPT09ICd1dGlscyc7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBtYXRjaGVkID0gdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ob3duZXIpICYmIG93bmVyLm5hbWUudGV4dCA9PT0gJ3V0aWxzJyAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIob3duZXIuZXhwcmVzc2lvbikgJiYgdGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuaGFzKG93bmVyLmV4cHJlc3Npb24udGV4dCk7XG5cdFx0XHRyZXR1cm4gbWF0Y2hlZDtcblx0XHR9O1xuXHRcdGxldCBzdWJqZWN0QXJnOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkO1xuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsZWUpICYmIGlzVXRpbHNPd25lcihjYWxsZWUuZXhwcmVzc2lvbikgJiZcblx0XHRcdChjYWxsZWUubmFtZS50ZXh0ID09PSAnbWVyZ2UnIHx8IGNhbGxlZS5uYW1lLnRleHQgPT09ICdmb3JrJykpIHtcblx0XHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdFx0c3ViamVjdEFyZyA9IGZpcnN0QXJnO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNJZGVudGlmaWVyKGNhbGxlZSkpIHtcblx0XHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChjYWxsZWUudGV4dCk7XG5cdFx0XHRpZiAoaW1wb3J0ZWQgPT09ICdtZXJnZScgfHwgaW1wb3J0ZWQgPT09ICdmb3JrJykge1xuXHRcdFx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblx0XHRcdFx0c3ViamVjdEFyZyA9IGZpcnN0QXJnO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSBpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihjYWxsZWUpICYmIHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxlZS5leHByZXNzaW9uKSAmJlxuXHRcdFx0Y2FsbGVlLmV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnZm9yaycgJiYgaXNVdGlsc093bmVyKGNhbGxlZS5leHByZXNzaW9uLmV4cHJlc3Npb24pKSB7XG5cdFx0XHQvLyB1dGlscy5mb3JrKGluc3RhbmNlKSguLi5hcmdzKSDigJQgdGhlIGN1cnJpZWQgZm9ybVxuXHRcdFx0Y29uc3QgWyBmaXJzdEFyZyBdID0gY2FsbGVlLmFyZ3VtZW50cztcblx0XHRcdHN1YmplY3RBcmcgPSBmaXJzdEFyZztcblx0XHR9XG5cdFx0aWYgKCFzdWJqZWN0QXJnIHx8ICF0cy5pc0lkZW50aWZpZXIoc3ViamVjdEFyZykpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KHN1YmplY3RBcmcudGV4dCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cblx0LyoqXG5cdFx0KiBQcm9jZXNzIGEgQGRlY29yYXRlKCkgZGVjb3JhdG9yXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NEZWNvcmF0ZURlY29yYXRvciAoXG5cdFx0ZGVjb3JhdG9yOiB0cy5EZWNvcmF0b3IsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRjbGFzc0RlY2xQYXJhbT86IHRzLkNsYXNzRGVjbGFyYXRpb25cblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdGRlY29yYXRvci5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cblx0XHQvLyBHZXQgdGhlIGNsYXNzIGRlY2xhcmF0aW9uIC0gdXNlIHRoZSBwYXNzZWQgY29udGV4dCBpZiBwYXJlbnQgaXMgbm90IHNldFxuXHRcdGNvbnN0IGNsYXNzRGVjbCA9IGRlY29yYXRvci5wYXJlbnQgYXMgdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCB8fCBjbGFzc0RlY2xQYXJhbTtcblx0XHRpZiAoIWNsYXNzRGVjbCB8fCAhY2xhc3NEZWNsLm5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0RlY29yYXRlZCBjbGFzcyBoYXMgbm8gbmFtZScsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgdHlwZU5hbWUgPSBjbGFzc0RlY2wubmFtZS50ZXh0O1xuXHRcdGlmICghdHlwZU5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0RlY29yYXRlZCBjbGFzcyBoYXMgbm8gbmFtZScsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUGFyc2UgZGVjb3JhdG9yIGFyZ3VtZW50czogQGRlY29yYXRlKCksIEBkZWNvcmF0ZShQYXJlbnQpLFxuXHRcdC8vIEBkZWNvcmF0ZSh7IC4uLiB9KSwgQGRlY29yYXRlKFBhcmVudCwgeyAuLi4gfSksXG5cdFx0Ly8gQE15Q29sbGVjdGlvbi5kZWNvcmF0ZSgpLCBATXlDb2xsZWN0aW9uLmRlY29yYXRlKHsgLi4uIH0pXG5cdFx0bGV0IHBhcmVudE5vZGU6IFR5cGVOb2RlIHwgdW5kZWZpbmVkO1xuXHRcdGxldCBwYXJlbnRGdWxsUGF0aDogc3RyaW5nIHwgbnVsbCA9IG51bGw7XG5cdFx0bGV0IGNvbGxlY3Rpb25JZDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdGxldCBkZWNvcmF0b3JDb25maWc6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSA9IHt9O1xuXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZGVjb3JhdG9yLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRjb25zdCBjYWxsRXhwciA9IGRlY29yYXRvci5leHByZXNzaW9uO1xuXHRcdFx0Y29uc3QgY2FsbGVlID0gY2FsbEV4cHIuZXhwcmVzc2lvbjtcblxuXHRcdFx0Ly8gQ2hlY2sgZm9yIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSB3aGVyZSBNeUNvbGxlY3Rpb24gaXMgYSBjdXN0b20gY29sbGVjdGlvbi5cblx0XHRcdC8vIFRoZSBkZWNvcmF0ZWQgY2xhc3MgYmVjb21lcyBhIHJvb3QgdHlwZSBpbiB0aGF0IGNvbGxlY3Rpb24uXG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxlZSkgJiZcblx0XHRcdFx0Y2FsbGVlLm5hbWUudGV4dCA9PT0gJ2RlY29yYXRlJyAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoY2FsbGVlLmV4cHJlc3Npb24pICYmXG5cdFx0XHRcdHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5oYXMoY2FsbGVlLmV4cHJlc3Npb24udGV4dClcblx0XHRcdCkge1xuXHRcdFx0XHRjb2xsZWN0aW9uSWQgPSB0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuZ2V0KGNhbGxlZS5leHByZXNzaW9uLnRleHQpO1xuXHRcdFx0XHRpZiAoY2FsbEV4cHIuYXJndW1lbnRzLmxlbmd0aCA9PT0gMSAmJiB0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGNhbGxFeHByLmFyZ3VtZW50c1sgMCBdKSkge1xuXHRcdFx0XHRcdGRlY29yYXRvckNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGNhbGxFeHByLmFyZ3VtZW50c1sgMCBdKTtcblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgYXJncyA9IGNhbGxFeHByLmFyZ3VtZW50cztcblx0XHRcdFx0bGV0IHBhcmVudEFyZzogdHMuSWRlbnRpZmllciB8IHVuZGVmaW5lZDtcblx0XHRcdFx0bGV0IGNvbmZpZ0FyZzogdHMuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24gfCB1bmRlZmluZWQ7XG5cblx0XHRcdFx0Zm9yIChjb25zdCBhcmcgb2YgYXJncykge1xuXHRcdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0XHRcdFx0aWYgKHBhcmVudEFyZykge1xuXHRcdFx0XHRcdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0XHRcdFx0XHRtZXNzYWdlIDogJ0BkZWNvcmF0ZSgpIGFjY2VwdHMgb25seSBvbmUgcGFyZW50IHJlZmVyZW5jZScsXG5cdFx0XHRcdFx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRcdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHRcdHBhcmVudEFyZyA9IGFyZztcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0XHRcdFx0aWYgKGNvbmZpZ0FyZykge1xuXHRcdFx0XHRcdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0XHRcdFx0XHRtZXNzYWdlIDogJ0BkZWNvcmF0ZSgpIGFjY2VwdHMgb25seSBvbmUgY29uZmlnIG9iamVjdCcsXG5cdFx0XHRcdFx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRcdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHRcdGNvbmZpZ0FyZyA9IGFyZztcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRpZiAocGFyZW50QXJnKSB7XG5cdFx0XHRcdFx0cGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeUlkZW50aWZpZXIocGFyZW50QXJnLnRleHQpO1xuXHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHRwYXJlbnRGdWxsUGF0aCA9IHBhcmVudE5vZGUuZnVsbFBhdGg7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0aWYgKGNvbmZpZ0FyZykge1xuXHRcdFx0XHRcdGRlY29yYXRvckNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGNvbmZpZ0FyZyk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBCdWlsZCBmdWxsIHBhdGhcblx0XHRjb25zdCBmdWxsUGF0aCA9IHBhcmVudE5vZGUgPyBgJHtwYXJlbnROb2RlLmZ1bGxQYXRofS4ke3R5cGVOYW1lfWAgOiB0eXBlTmFtZTtcblxuXHRcdC8vIENyZWF0ZSBkZWZpbml0aW9uIGluZm8gZm9yIGRlY29yYXRlXG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IHR5cGVOYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlY29yYXRlJyxcblx0XHRcdHBhcmVudCAgICAgIDogcGFyZW50RnVsbFBhdGgsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IGRlY29yYXRvckNvbmZpZy5zdHJpY3RDaGFpbiA/PyB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBkZWNvcmF0b3JDb25maWcuYmxvY2tFcnJvcnMgPz8gZmFsc2UsXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChmdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdFx0dGhpcy5lZHNTY29wZUJ5Tm9kZS5zZXQoY2xhc3NEZWNsLCBmdWxsUGF0aCk7XG5cblx0XHQvLyBDcmVhdGUgdHlwZSBub2RlXG5cdFx0Y29uc3Qgbm9kZSA9IFR5cGVHcmFwaEltcGwuY3JlYXRlTm9kZShcblx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0cGFyZW50Tm9kZSxcblx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRsaW5lICsgMSxcblx0XHRcdGNoYXJhY3RlciArIDEsXG5cdFx0XHRjb2xsZWN0aW9uSWRcblx0XHQpO1xuXHRcdG5vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lID0gdGhpcy5nZXRSZWdpc3RyeUludGVyZmFjZU5hbWUobm9kZS5jb2xsZWN0aW9uSWQpO1xuXG5cdFx0Ly8gU2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlIGRldGVjdGlvbiAoaGFyZC1mYWlsIGxhdylcblx0XHR0aGlzLnJlY29yZERlZmluZVNpdGUoXG5cdFx0XHRwYXJlbnROb2RlID8gYCR7cGFyZW50Tm9kZS5mdWxsUGF0aH0uJHt0eXBlTmFtZX1gIDogYCR7Y29sbGVjdGlvbklkID8/ICdkZWZhdWx0J306OiR7dHlwZU5hbWV9YCxcblx0XHRcdGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gXG5cdFx0KTtcblxuXHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBhbmQgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGNsYXNzIG1lbWJlcnMg4oCUXG5cdFx0Ly8gdGhlIG5ldyBub2RlIGFuY2hvcnMgcmVsYXRpdmUtZmlyc3QgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb25cblx0XHRjb25zdCBwcmV2aW91c0FuY2hvciA9IHRoaXMuY3VycmVudEdyYXBoQW5jaG9yO1xuXHRcdHRoaXMuY3VycmVudEdyYXBoQW5jaG9yID0gbm9kZTtcblx0XHR0cnkge1xuXHRcdFx0bm9kZS5wcm9wZXJ0aWVzID0gdGhpcy5leHRyYWN0Q2xhc3NQcm9wZXJ0aWVzKGNsYXNzRGVjbCk7XG5cdFx0XHRub2RlLmNvbnN0cnVjdG9yUGFyYW1zID0gdGhpcy5leHRyYWN0Q2xhc3NDb25zdHJ1Y3RvclBhcmFtcyhjbGFzc0RlY2wpO1xuXHRcdH0gZmluYWxseSB7XG5cdFx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IHByZXZpb3VzQW5jaG9yO1xuXHRcdH1cblxuXHRcdC8vIEFkZCB0byBncmFwaFxuXHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZENoaWxkKHBhcmVudE5vZGUsIG5vZGUpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZFJvb3Qobm9kZSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdHlwZSBuYW1lIGZyb20gZGVmaW5lKCkgY2FsbCBhcmd1bWVudHMuXG5cdCAqIEhhbmRsZXM6XG5cdCAqICAgZGVmaW5lKCdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdCAqICAgZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcikgICAvLyBleHBsaWNpdC1zb3VyY2UgZm9ybVxuXHQgKiAgIGRlZmluZShmdW5jdGlvbiBUeXBlTmFtZSgpIHt9KVxuXHQgKiAgIGRlZmluZSgoKSA9PiBjbGFzcyBUeXBlTmFtZSB7fSlcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFR5cGVOYW1lIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGFyZ3M7XG5cblx0XHQvLyBFeHBsaWNpdC1zb3VyY2UgZm9ybTogZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilcblx0XHRpZiAoYXJncy5sZW5ndGggPj0gMiAmJiB0cy5pc0lkZW50aWZpZXIoZmlyc3RBcmcpICYmIHRzLmlzU3RyaW5nTGl0ZXJhbChhcmdzWyAxIF0pKSB7XG5cdFx0XHRyZXR1cm4gYXJnc1sgMSBdLnRleHQ7XG5cdFx0fVxuXG5cdFx0Ly8gU3RyaW5nIGxpdGVyYWw6IGRlZmluZSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChmaXJzdEFyZykpIHtcblx0XHRcdHJldHVybiBmaXJzdEFyZy50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIEZ1bmN0aW9uIHdpdGggbmFtZTogZGVmaW5lKGZ1bmN0aW9uIFR5cGVOYW1lKCkge30pXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGZpcnN0QXJnKSAmJiBmaXJzdEFyZy5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gZmlyc3RBcmcubmFtZS50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIEFycm93IGZ1bmN0aW9uIHJldHVybmluZyBjbGFzczogZGVmaW5lKCgpID0+IGNsYXNzIFR5cGVOYW1lIHt9KVxuXHRcdGlmICh0cy5pc0Fycm93RnVuY3Rpb24oZmlyc3RBcmcpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGZpcnN0QXJnO1xuXHRcdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGJvZHkpICYmIGJvZHkubmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gYm9keS5uYW1lLnRleHQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSBmdWxsIGRlZmluZSgpIGNhbGwgY29udGV4dDogdHlwZSBuYW1lLCBwYXJlbnQgdHlwZSwgYW5kIGNvbGxlY3Rpb24uXG5cdCAqIEhhbmRsZXMgZGlyZWN0IGNhbGxzLCBwcm9wZXJ0eS1hY2Nlc3MgY2FsbHMsIGNoYWluZWQgY2FsbHMsIGFuZCB0aGVcblx0ICogZXhwbGljaXQtc291cmNlIGZvcm0gYGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpYC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdERlZmluZUNvbnRleHQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKToge1xuXHRcdHR5cGVOYW1lPzogc3RyaW5nO1xuXHRcdHBhcmVudFR5cGU/OiBUeXBlTm9kZTtcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmc7XG5cdH0ge1xuXHRcdGNvbnN0IHR5cGVOYW1lID0gdGhpcy5leHRyYWN0VHlwZU5hbWUoY2FsbCk7XG5cdFx0aWYgKCF0eXBlTmFtZSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gY2FsbDtcblxuXHRcdC8vIERpcmVjdCBjYWxsOiBkZWZpbmUoJ1R5cGVOYW1lJywgLi4uKSBvciBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0Ly8gRXhwbGljaXQtc291cmNlIGZvcm06IGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdFx0XHRpZiAoY2FsbC5hcmd1bWVudHMubGVuZ3RoID49IDIgJiYgdHMuaXNJZGVudGlmaWVyKGNhbGwuYXJndW1lbnRzWyAwIF0pKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZU5hbWUgPSBjYWxsLmFyZ3VtZW50c1sgMCBdLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBQbGFpbiByb290IGRlZmluZSBpbiBkZWZhdWx0IGNvbGxlY3Rpb25cblx0XHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiBYLmRlZmluZSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0Y29uc3Qgb2JqID0gZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG9iaikpIHtcblx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShvYmoudGV4dCk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBOZXN0ZWQgYWNjZXNzOiBpbnN0YW5jZS5UeXBlLmRlZmluZSAtIHRyeSB0byByZXNvbHZlXG5cdFx0XHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKG9iaik7XG5cdFx0XHRcdGlmIChjaGFpbi5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoY2hhaW4uam9pbignLicpKTtcblx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUgfTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihvYmopKSB7XG5cdFx0XHRcdC8vIERldGVybWluZSB0aGUgY29sbGVjdGlvbiBjb250ZXh0IGZyb20gdGhlIHJvb3Qgb2YgdGhlIGNoYWluIHNvIHRoYXRcblx0XHRcdFx0Ly8gY3VzdG9tLWNvbGxlY3Rpb24gdHlwZXMgZG8gbm90IGdldCBjb25mdXNlZCB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcy5cblx0XHRcdFx0Y29uc3Qgcm9vdElkID0gdGhpcy5nZXRSb290SWRlbnRpZmllcihvYmouZXhwcmVzc2lvbik7XG5cdFx0XHRcdGNvbnN0IGV4cGVjdGVkQ29sbGVjdGlvbklkID0gcm9vdElkXG5cdFx0XHRcdFx0PyB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uocm9vdElkLnRleHQpLmNvbGxlY3Rpb25JZFxuXHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXG5cdFx0XHRcdC8vIENoYWluZWQgY2FsbDogZGVmaW5lKCdBJykuZGVmaW5lKCdCJykgb3IgbW5lbW9uaWNhLmRlZmluZSgnQScpLmRlZmluZSgnQicpXG5cdFx0XHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ2FsbChvYmosIGNhbGwuZ2V0U291cmNlRmlsZSgpKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdFR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0Ly8gSW5oZXJpdCBjb2xsZWN0aW9uIGZyb20gdGhlIHBhcmVudCB0eXBlIChpZiBhbnkpXG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIENoYWluZWQgbGF6eSBjYWxsOiBsYXp5KCdBJykuZGVmaW5lKCdCJykgb3IgVHlwZS5sYXp5KCdBJykuZGVmaW5lKCdCJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzTGF6eUNhbGwob2JqLCBjYWxsLmdldFNvdXJjZUZpbGUoKSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gQnVpbGRlciBsb29rdXAgY2hhaW46IEFwcC5sb29rdXAoJ1VzZXInKS5kZWZpbmUoJ0FkbWluJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMb29rdXBDYWxsKG9iaikpIHtcblx0XHRcdFx0XHRjb25zdCBsb29rZWRVcFBhdGggPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKG9iaik7XG5cdFx0XHRcdFx0aWYgKGxvb2tlZFVwUGF0aCkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUobG9va2VkVXBQYXRoKTtcblx0XHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZS5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHR9XG5cblx0LyoqXG5cdCAqIFByZWZpeCBhIGRvdHRlZCB0eXBlIHBhdGggd2l0aCBhIGNvbGxlY3Rpb24gaWRlbnRpZmllciBzbyBjdXN0b20tY29sbGVjdGlvblxuXHQgKiB0eXBlcyBkbyBub3QgY29sbGlkZSB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcyBpbiB0aGUgZ3JhcGguXG5cdCAqL1xuXHRwcml2YXRlIHByZWZpeENvbGxlY3Rpb25QYXRoIChwYXRoOiBzdHJpbmcsIGNvbGxlY3Rpb25JZDogc3RyaW5nKTogc3RyaW5nIHtcblx0XHRyZXR1cm4gYCR7Y29sbGVjdGlvbklkfTo6JHtwYXRofWA7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGRlZmluZSgpIHNvdXJjZSBpZGVudGlmaWVyIHRvIGVpdGhlciBhIHBhcmVudCB0eXBlLCBhIGNvbGxlY3Rpb24sXG5cdCAqIG9yIHRoZSBkZWZhdWx0IChtb2R1bGUgb2JqZWN0KSBjb2xsZWN0aW9uLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRGVmaW5lU291cmNlIChzb3VyY2VOYW1lOiBzdHJpbmcpOiB7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Ly8gTW9kdWxlIG9iamVjdCBhbGlhc2VzIC0+IHJvb3QgaW4gZGVmYXVsdCBjb2xsZWN0aW9uXG5cdFx0aWYgKHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhzb3VyY2VOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdC8vIENvbGxlY3Rpb24gdmFyaWFibGVzIC0+IHJvb3QgaW4gdGhhdCBjb2xsZWN0aW9uXG5cdFx0Y29uc3QgY29sbGVjdGlvbklkID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChzb3VyY2VOYW1lKTtcblx0XHRpZiAoY29sbGVjdGlvbklkKSB7XG5cdFx0XHRyZXR1cm4geyBjb2xsZWN0aW9uSWQgfTtcblx0XHR9XG5cblx0XHQvLyBPdGhlcndpc2UgdHJlYXQgYXMgYSB0eXBlIHZhcmlhYmxlIHJlZmVyZW5jZVxuXHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlJZGVudGlmaWVyKHNvdXJjZU5hbWUpO1xuXHRcdHJldHVybiB7IHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhIGNhbGwgZXhwcmVzc2lvbiBpcyBhIGxvb2t1cCgpIGNhbGwuXG5cdCAqL1xuXHRwcml2YXRlIGlzTG9va3VwQ2FsbCAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24pOiBib29sZWFuIHtcblx0XHRjb25zdCBleHByID0gbm9kZS5leHByZXNzaW9uO1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikgJiYgZXhwci50ZXh0ID09PSAnbG9va3VwJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSAmJiBleHByLm5hbWUudGV4dCA9PT0gJ2xvb2t1cCcpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGxvb2t1cCgpIGNhbGwgdG8gYSBkb3R0ZWQgdHlwZSBwYXRoIChiZXN0IGVmZm9ydCkuXG5cdCAqIEhhbmRsZXM6XG5cdCAqICAgbG9va3VwKCdVc2VyJylcblx0ICogICBsb29rdXAoc291cmNlLCAnVXNlcicpXG5cdCAqICAgQXBwLmxvb2t1cCgnVXNlcicpXG5cdCAqICAgY29sbGVjdGlvbi5sb29rdXAoJ1VzZXIuQWRtaW4nKVxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlTG9va3VwUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGFyZ3MgPSBjYWxsLmFyZ3VtZW50cztcblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gU2luZ2xlLWFyZyBsb29rdXA6IGxvb2t1cCgnVXNlcicpIG9yIEFwcC5sb29rdXAoJ1VzZXInKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMSkge1xuXHRcdFx0Y29uc3QgWyBhcmcgXSA9IGFyZ3M7XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGFyZykgfHwgdHMuaXNOb1N1YnN0aXR1dGlvblRlbXBsYXRlTGl0ZXJhbChhcmcpKSB7XG5cdFx0XHRcdGNvbnN0IHBhdGggPSBhcmcudGV4dDtcblx0XHRcdFx0Ly8gSWYgdGhpcyBpcyBhIG1ldGhvZCBjYWxsIG9uIGEgc291cmNlLCByZXNvbHZlIHJlbGF0aXZlIHRvIHRoYXQgc291cmNlLlxuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdGNvbnN0IHNvdXJjZUV4cHIgPSBjYWxsLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKHNvdXJjZUV4cHIpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBzb3VyY2VOYW1lID0gc291cmNlRXhwci50ZXh0O1xuXHRcdFx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShzb3VyY2VOYW1lKTtcblx0XHRcdFx0XHRcdGlmIChzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCkge1xuXHRcdFx0XHRcdFx0XHQvLyBDb2xsZWN0aW9uIGxvb2t1cDogcHJlZml4IHBhdGggd2l0aCB0aGUgY29sbGVjdGlvbiBpZFxuXHRcdFx0XHRcdFx0XHRyZXR1cm4gdGhpcy5wcmVmaXhDb2xsZWN0aW9uUGF0aChwYXRoLCBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRpZiAoc291cmNlQ29udGV4dC5wYXJlbnRUeXBlKSB7XG5cdFx0XHRcdFx0XHRcdC8vIFR5cGUgbG9va3VwOiByZWxhdGl2ZSBmaXJzdCwgdGhlbiByb290IGZhbGxiYWNrXG5cdFx0XHRcdFx0XHRcdGNvbnN0IHJlbGF0aXZlUGF0aCA9IGAke3NvdXJjZUNvbnRleHQucGFyZW50VHlwZS5mdWxsUGF0aH0uJHtwYXRofWA7XG5cdFx0XHRcdFx0XHRcdGlmICh0aGlzLmdyYXBoLmZpbmRUeXBlKHJlbGF0aXZlUGF0aCkpIHtcblx0XHRcdFx0XHRcdFx0XHRyZXR1cm4gcmVsYXRpdmVQYXRoO1xuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRcdHJldHVybiBwYXRoO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gVHdvLWFyZyBsb29rdXA6IGxvb2t1cChzb3VyY2UsICdVc2VyJylcblx0XHRpZiAoYXJncy5sZW5ndGggPj0gMikge1xuXHRcdFx0Y29uc3QgWyBzb3VyY2VBcmcsIHBhdGhBcmcgXSA9IGFyZ3M7XG5cdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihzb3VyY2VBcmcpIHx8ICF0cy5pc1N0cmluZ0xpdGVyYWwocGF0aEFyZykpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHNvdXJjZU5hbWUgPSBzb3VyY2VBcmcudGV4dDtcblx0XHRcdGNvbnN0IHBhdGggPSBwYXRoQXJnLnRleHQ7XG5cdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKHNvdXJjZU5hbWUpO1xuXHRcdFx0aWYgKHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKSB7XG5cdFx0XHRcdHJldHVybiB0aGlzLnByZWZpeENvbGxlY3Rpb25QYXRoKHBhdGgsIHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKTtcblx0XHRcdH1cblx0XHRcdGlmIChzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUpIHtcblx0XHRcdFx0Y29uc3QgcmVsYXRpdmVQYXRoID0gYCR7c291cmNlQ29udGV4dC5wYXJlbnRUeXBlLmZ1bGxQYXRofS4ke3BhdGh9YDtcblx0XHRcdFx0aWYgKHRoaXMuZ3JhcGguZmluZFR5cGUocmVsYXRpdmVQYXRoKSkge1xuXHRcdFx0XHRcdHJldHVybiByZWxhdGl2ZVBhdGg7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHBhdGg7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gcGF0aDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIExvb2t1cC1sYXcgZGVsZWdhdGUgZm9yIHRoZSBsb2NhbC1zY29wZSB3YWxrZXIgKHNjb3Blcy5qc29uIHR5cGVQYXRoXG5cdCAqIG1ldGFkYXRhKTogcmVzb2x2ZSBhIGxvb2t1cCgpIGluaXRpYWxpemVyIGNhbGwgdGhyb3VnaCBleGFjdGx5IHRoZVxuXHQgKiB0aWVycyB0aGUgdXNhZ2VzIHBhc3MgcmVzb2x2ZWQgaXQgYWdhaW5zdCAoc2FtZSBzb3VyY2UgcmVzb2x1dGlvbixcblx0ICogc2FtZSBjb21wbGV0ZSBncmFwaCkuIFRoZSB3YWxrZXIgcnVucyBpdHMgb3duIHNjb3BlLWNoYWluIHZhbHVlLXNjb3BlXG5cdCAqIHRpZXIgYmVmb3JlIGRlbGVnYXRpbmc7IGV2ZXJ5dGhpbmcgYWJvdmUgdmFsdWUgc2NvcGUgbGFuZHMgaGVyZSwgc29cblx0ICogc2NvcGVzLmpzb24gbmV2ZXIgZGlzYWdyZWVzIHdpdGggdGhlIGhhcmQtZmFpbC1sYXcgdmVyZGljdHMuXG5cdCAqL1xuXHRyZXNvbHZlTG9va3VwQ2FsbFBhdGggKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKGNhbGwpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHQqIEZpbmQgYSBwYXJlbnQgdHlwZSBieSBpdHMgbmFtZSwgc2VhcmNoaW5nIGluIHRoZSBncmFwaC5cblx0XHQqIFdoZW4gY29sbGVjdGlvbklkIGlzIHByb3ZpZGVkLCBvbmx5IHR5cGVzIGZyb20gdGhhdCBjb2xsZWN0aW9uIGFyZSBjb25zaWRlcmVkLlxuXHRcdCovXG5cdHByaXZhdGUgZmluZFBhcmVudFR5cGVCeU5hbWUgKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmdcblx0KTogVHlwZU5vZGUgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IG1hdGNoZXNDb2xsZWN0aW9uID0gKHR5cGU6IFR5cGVOb2RlKTogYm9vbGVhbiA9PiB7XG5cdFx0XHRpZiAoY29sbGVjdGlvbklkID09PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0cmV0dXJuIHR5cGUuY29sbGVjdGlvbklkID09PSB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdHlwZS5jb2xsZWN0aW9uSWQgPT09IGNvbGxlY3Rpb25JZDtcblx0XHR9O1xuXG5cdFx0Ly8gRmlyc3QgdHJ5IGV4YWN0IG1hdGNoIChkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMgdXNlIHRoZSBwbGFpbiBkb3R0ZWQgcGF0aClcblx0XHRjb25zdCBleGFjdCA9IHRoaXMuZ3JhcGguZmluZFR5cGUobmFtZSk7XG5cdFx0aWYgKGV4YWN0ICYmIG1hdGNoZXNDb2xsZWN0aW9uKGV4YWN0KSkge1xuXHRcdFx0cmV0dXJuIGV4YWN0O1xuXHRcdH1cblxuXHRcdC8vIFRoZW4gc2VhcmNoIHRocm91Z2ggYWxsIHR5cGVzIGZvciBvbmUgd2l0aCBtYXRjaGluZyBuYW1lIGFuZCBjb2xsZWN0aW9uXG5cdFx0Zm9yIChjb25zdCB0eXBlIG9mIHRoaXMuZ3JhcGguZ2V0QWxsVHlwZXMoKSkge1xuXHRcdFx0aWYgKHR5cGUubmFtZSA9PT0gbmFtZSAmJiBtYXRjaGVzQ29sbGVjdGlvbih0eXBlKSkge1xuXHRcdFx0XHRyZXR1cm4gdHlwZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBGaW5kIGEgcGFyZW50IHR5cGUgZnJvbSBhbiBpZGVudGlmaWVyIHJlZmVyZW5jZS5cblx0XHQqIEhhbmRsZXMgYm90aCBhbGlhc2VkIHZhcmlhYmxlcyAoY29uc3QgVXNlciA9IGRlZmluZSgnVXNlckVudGl0eScsIC4uLikpXG5cdFx0KiBhbmQgZGlyZWN0IGNsYXNzL3R5cGUgbmFtZXMuXG5cdFx0Ki9cblx0cHJpdmF0ZSBmaW5kUGFyZW50VHlwZUJ5SWRlbnRpZmllciAobmFtZTogc3RyaW5nKTogVHlwZU5vZGUgfCB1bmRlZmluZWQge1xuXHRcdC8vIEZpcnN0IGNoZWNrIHZhcmlhYmxlIG1hcHBpbmc6IGNvbnN0IFVzZXIgPSBkZWZpbmUoJ1VzZXJFbnRpdHknLCAuLi4pXG5cdFx0Y29uc3QgbWFwcGVkRnVsbFBhdGggPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChuYW1lKTtcblx0XHRpZiAobWFwcGVkRnVsbFBhdGgpIHtcblx0XHRcdGNvbnN0IG1hcHBlZE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKG1hcHBlZEZ1bGxQYXRoKTtcblx0XHRcdGlmIChtYXBwZWROb2RlKSByZXR1cm4gbWFwcGVkTm9kZTtcblx0XHR9XG5cblx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShuYW1lKTtcblx0XHRyZXR1cm4gcGFyZW50Tm9kZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgdGhlIGxlZnRtb3N0IGlkZW50aWZpZXIgb2YgYSBwcm9wZXJ0eS1hY2Nlc3MgY2hhaW4uXG5cdCAqIEZvciBgQXBwLmRlZmluZSgnVXNlcicpLmRlZmluZSgnQWRtaW4nKWAgdGhpcyByZXR1cm5zIHRoZSBgQXBwYCBpZGVudGlmaWVyLlxuXHQgKi9cblx0cHJpdmF0ZSBnZXRSb290SWRlbnRpZmllciAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHRzLklkZW50aWZpZXIgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5FeHByZXNzaW9uID0gZXhwcjtcblx0XHR3aGlsZSAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY3VycmVudCkpIHtcblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0fVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudCkpIHtcblx0XHRcdHJldHVybiBjdXJyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBHZXQgcHJvcGVydHkgY2hhaW4gZnJvbSBuZXN0ZWQgYWNjZXNzXG5cdFx0Ki9cblx0cHJpdmF0ZSBnZXRQcm9wZXJ0eUNoYWluIChleHByOiB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24gfCB0cy5JZGVudGlmaWVyKTogc3RyaW5nW10ge1xuXHRcdGNvbnN0IGNoYWluOiBzdHJpbmdbXSA9IFtdO1xuXG5cdFx0bGV0IGN1cnJlbnQ6IHRzLkV4cHJlc3Npb24gPSBleHByO1xuXHRcdHdoaWxlICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0aWYgKGN1cnJlbnQubmFtZSkge1xuXHRcdFx0XHRjaGFpbi51bnNoaWZ0KGN1cnJlbnQubmFtZS50ZXh0KTtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0fVxuXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50KSkge1xuXHRcdFx0Y2hhaW4udW5zaGlmdChjdXJyZW50LnRleHQpO1xuXHRcdH1cblxuXHRcdHJldHVybiBjaGFpbjtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlcm1pbmUgdGhlIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24gZm9yIGVpdGhlciBhIGRlZmluZSgpIG9yIGxhenkoKSBjYWxsLlxuXHQgKiBGb3IgZGVmaW5lKCkgdGhpcyBpcyB0aGUgY29uc3RydWN0IGhhbmRsZXI7IGZvciBsYXp5KCkgaXQgaXMgdGhlIHZhbHVlXG5cdCAqIHJldHVybmVkIGJ5IHRoZSBsYXp5IGdldHRlci5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENvbnN0cnVjdG9yRXhwcmVzc2lvbiAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBleHByID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGNvbnN0IG5hbWUgPSB0cy5pc0lkZW50aWZpZXIoZXhwcilcblx0XHRcdD8gZXhwci50ZXh0XG5cdFx0XHQ6IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpXG5cdFx0XHRcdD8gZXhwci5uYW1lLnRleHRcblx0XHRcdFx0OiAnJztcblxuXHRcdGlmIChuYW1lID09PSAnbGF6eScpIHtcblx0XHRcdGNvbnN0IGxhenlBcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdFx0aWYgKCFsYXp5QXJncykge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHRoaXMudW53cmFwTGF6eUdldHRlcihsYXp5QXJncy5nZXR0ZXIpO1xuXHRcdH1cblxuXHRcdC8vIGRlZmluZSgpIGNhbGxcblx0XHRjb25zdCBhcmdzID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIE1vZGVybiBmb3JtOiBkZWZpbmUoJ05hbWUnLCBoYW5kbGVyLCBjb25maWc/KVxuXHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoYXJnc1sgMCBdKSkge1xuXHRcdFx0cmV0dXJuIGFyZ3NbIDEgXTtcblx0XHR9XG5cblx0XHQvLyBMZWdhY3kgZm9ybTogZGVmaW5lKGZ1bmN0aW9uIE5hbWUoKSB7fSkgb3IgZGVmaW5lKCgpID0+IGNsYXNzIE5hbWUge30pXG5cdFx0cmV0dXJuIGFyZ3NbIDAgXTtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBjb25zdHJ1Y3RvciBmdW5jdGlvblxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UHJvcGVydGllcyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCk7XG5cdFx0aWYgKCFjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdHJldHVybiBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzRnJvbUNvbnN0cnVjdG9yKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBhIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24gKGZ1bmN0aW9uLCBhcnJvdywgb3IgY2xhc3MpLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UHJvcGVydGllc0Zyb21Db25zdHJ1Y3RvciAoY29uc3RydWN0b3JFeHByOiB0cy5FeHByZXNzaW9uKTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cblx0XHQvLyBCdWlsZCB0eXBlIG1hcCBmcm9tIGRhdGEgcGFyYW1ldGVyIChmb3IgdGhpcy54ID0gZGF0YS54IHBhdHRlcm5zKVxuXHRcdGNvbnN0IGRhdGFUeXBlTWFwID0gdGhpcy5idWlsZERhdGFUeXBlTWFwKGNvbnN0cnVjdG9yRXhwcik7XG5cblx0XHQvLyBIYW5kbGUgZnVuY3Rpb24gZXhwcmVzc2lvblxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzQXJyb3dGdW5jdGlvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGNvbnN0cnVjdG9yRXhwcjtcblxuXHRcdFx0Ly8gRmlyc3QsIGV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGB0aGlzYCBwYXJhbWV0ZXIgdHlwZSBhbm5vdGF0aW9uXG5cdFx0XHQvLyBUaGlzIGhhbmRsZXMgcGF0dGVybnMgbGlrZTogZnVuY3Rpb24odGhpczogU29tZVR5cGUsIGRhdGE6IFNvbWVUeXBlKSB7IH1cblx0XHRcdGNvbnN0IHRoaXNQYXJhbVByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RUaGlzUGFyYW1Qcm9wZXJ0aWVzKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRmb3IgKGNvbnN0IFsgbmFtZSwgcHJvcEluZm8gXSBvZiB0aGlzUGFyYW1Qcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHByb3BJbmZvKTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gRnVuY3Rpb24gYm9keSB3aXRoIHN0YXRlbWVudHNcblx0XHRcdGlmICh0cy5pc0Jsb2NrKGJvZHkpKSB7XG5cdFx0XHRcdGZvciAoY29uc3Qgc3RtdCBvZiBib2R5LnN0YXRlbWVudHMpIHtcblx0XHRcdFx0XHRpZiAodHMuaXNFeHByZXNzaW9uU3RhdGVtZW50KHN0bXQpKSB7XG5cdFx0XHRcdFx0XHR0aGlzLmV4dHJhY3RQcm9wZXJ0eUZyb21TdGF0ZW1lbnQoc3RtdC5leHByZXNzaW9uLCBwcm9wZXJ0aWVzLCBkYXRhVHlwZU1hcCk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gSGFuZGxlIGNsYXNzIGV4cHJlc3Npb25cblx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Ly8gRmlyc3QgcGFzczogY29sbGVjdCBhbGwgcHJvcGVydHkgdHlwZXMgZm9yIG1ldGhvZCBpbmZlcmVuY2Vcblx0XHRcdGNvbnN0IGNsYXNzUHJvcGVydHlUeXBlcyA9IHRoaXMuZXh0cmFjdENsYXNzUHJvcGVydHlUeXBlcyhjb25zdHJ1Y3RvckV4cHIpO1xuXG5cdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjb25zdHJ1Y3RvckV4cHIubWVtYmVycykge1xuXHRcdFx0XHQvLyBIYW5kbGUgcHJvcGVydHkgZGVjbGFyYXRpb25zXG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5RGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSkge1xuXHRcdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIHByb3BlcnRpZXNcblx0XHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4ge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHRcdFx0bS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQ7XG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXG5cdFx0XHRcdFx0Y29uc3QgbmFtZSA9IHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkgPyBtZW1iZXIubmFtZS50ZXh0IDogJyc7XG5cdFx0XHRcdFx0aWYgKG5hbWUpIHtcblx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdFx0dHlwZSAgICAgOiB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSksXG5cdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogISFtZW1iZXIucXVlc3Rpb25Ub2tlbixcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIEhhbmRsZSBtZXRob2QgZGVjbGFyYXRpb25zXG5cdFx0XHRcdGlmICh0cy5pc01ldGhvZERlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIG1ldGhvZHNcblx0XHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4ge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHRcdFx0bS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQ7XG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXG5cdFx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJNZXRob2RUeXBlKG1lbWJlciwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBIYW5kbGUgZ2V0dGVyIGRlY2xhcmF0aW9uc1xuXHRcdFx0XHRpZiAodHMuaXNHZXRBY2Nlc3NvcihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBnZXR0ZXJzXG5cdFx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0XHRcdG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkO1xuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblxuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdC8vIEZpcnN0IHRyeSBleHBsaWNpdCB0eXBlIGFubm90YXRpb24sIHRoZW4gaW5mZXIgZnJvbSBnZXR0ZXIgYm9keVxuXHRcdFx0XHRcdGxldCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdGlmICh0eXBlID09PSAndW5rbm93bicgJiYgbWVtYmVyLmJvZHkpIHtcblx0XHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyUmV0dXJuVHlwZUZyb21Cb2R5KG1lbWJlci5ib2R5LCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0XHRyZWFkb25seSA6IHRydWUsXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdC8qKlxuXHQgKiBCdWlsZCBhIHR5cGUgbWFwIGZyb20gYWxsIHBhcmFtZXRlcnMgd2l0aCBpbmxpbmUgb2JqZWN0IHR5cGUgYW5ub3RhdGlvbnNcblx0ICogUmV0dXJucyBhIG1hcCBvZiBcInBhcmFtTmFtZS5wcm9wZXJ0eU5hbWVcIiAtPiB0eXBlXG5cdCAqL1xuXHRwcml2YXRlIGJ1aWxkRGF0YVR5cGVNYXAgKGhhbmRsZXJBcmc6IHRzLkV4cHJlc3Npb24pOiBNYXA8c3RyaW5nLCBzdHJpbmc+IHtcblx0XHRjb25zdCB0eXBlTWFwID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblxuXHRcdGlmICghdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oaGFuZGxlckFyZykgJiYgIXRzLmlzQXJyb3dGdW5jdGlvbihoYW5kbGVyQXJnKSkge1xuXHRcdFx0cmV0dXJuIHR5cGVNYXA7XG5cdFx0fVxuXG5cdFx0Ly8gSXRlcmF0ZSBvdmVyIEFMTCBwYXJhbWV0ZXJzXG5cdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBoYW5kbGVyQXJnLnBhcmFtZXRlcnMpIHtcblx0XHRcdGlmICghcGFyYW0ubmFtZSB8fCAhcGFyYW0udHlwZSkgY29udGludWU7XG5cblx0XHRcdC8vIEdldCBwYXJhbWV0ZXIgbmFtZVxuXHRcdFx0bGV0IHBhcmFtTmFtZSA9ICcnO1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSkge1xuXHRcdFx0XHRwYXJhbU5hbWUgPSBwYXJhbS5uYW1lLnRleHQ7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHQvLyBTa2lwIGRlc3RydWN0dXJlZCBwYXJhbWV0ZXJzIGZvciBub3dcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cblx0XHRcdC8vIENoZWNrIGlmIGl0J3MgYW4gaW5saW5lIG9iamVjdCB0eXBlIGxpdGVyYWxcblx0XHRcdGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZShwYXJhbS50eXBlKSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBwYXJhbS50eXBlLm1lbWJlcnMpIHtcblx0XHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0XHR0eXBlTWFwLnNldChgJHtwYXJhbU5hbWV9LiR7cHJvcE5hbWV9YCwgdHlwZSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHQvLyBOYW1lZCB0eXBlIHJlZmVyZW5jZSAoYWxpYXMvaW50ZXJmYWNlL2NsYXNzLCBpbXBvcnRlZCBvclxuXHRcdFx0XHQvLyBsb2NhbCDigJQgRjE0KTogZGVjb21wb3NlIHRoZSByZXNvbHZlZCBkZWNsYXJhdGlvbiBpbnRvXG5cdFx0XHRcdC8vIHBlci1wcm9wZXJ0eSBlbnRyaWVzIHRocm91Z2ggdGhlIHNhbWUgaW1wb3J0LWF3YXJlXG5cdFx0XHRcdC8vIG1hY2hpbmVyeSBhcyBjb25zdHJ1Y3RvciBzaWduYXR1cmVzIChGMTApLCBpbmNsdWRpbmcgdGhlXG5cdFx0XHRcdC8vIGhlcml0YWdlIHdhbGsgKEYxMykuIFdpdGhvdXQgdGhpcywgYHRoaXMueCA9IHBhcmFtLnlgXG5cdFx0XHRcdC8vIHJlYWQgYHVua25vd25gIGZvciBuYW1lZCBwYXJhbXMg4oCUIG9ubHkgaW5saW5lIGxpdGVyYWxzXG5cdFx0XHRcdC8vIHdlcmUgZGVjb21wb3NlZC4gVW5yZXNvbHZhYmxlIOKGkiB3aG9sZS1wYXJhbSBmYWxsYmFja1xuXHRcdFx0XHQvLyBiZWxvdzsgYSBiYXJlIG5hbWUgaXMgbmV2ZXIgZW1pdHRlZCBlaXRoZXIgd2F5XG5cdFx0XHRcdGxldCBuYW1lZERlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQ7XG5cdFx0XHRcdGlmICh0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHBhcmFtLnR5cGUpICYmIHRzLmlzSWRlbnRpZmllcihwYXJhbS50eXBlLnR5cGVOYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHBhcmFtVHlwZU5hbWUgPSBwYXJhbS50eXBlLnR5cGVOYW1lLnRleHQ7XG5cdFx0XHRcdFx0bmFtZWREZWNsID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihwYXJhbVR5cGVOYW1lLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChuYW1lZERlY2wpIHtcblx0XHRcdFx0XHQvLyBtZW1iZXIgdHlwZXMgcmVzb2x2ZSBhZ2FpbnN0IHRoZSBERUNMQVJJTkcgZmlsZVxuXHRcdFx0XHRcdGNvbnN0IHJlZmVyZW5jaW5nRmlsZSA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRcdFx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSBuYW1lZERlY2wuZmlsZTtcblx0XHRcdFx0XHR0cnkge1xuXHRcdFx0XHRcdFx0Y29uc3QgZGVjbFByb3BlcnRpZXMgPSB0aGlzLnJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXMobmFtZWREZWNsKTtcblx0XHRcdFx0XHRcdGZvciAoY29uc3QgWyBwcm9wTmFtZSwgaW5mbyBdIG9mIGRlY2xQcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdFx0XHRcdHR5cGVNYXAuc2V0KGAke3BhcmFtTmFtZX0uJHtwcm9wTmFtZX1gLCBpbmZvLnR5cGUpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH0gZmluYWxseSB7XG5cdFx0XHRcdFx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSByZWZlcmVuY2luZ0ZpbGU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdC8vIGtlZXAgdGhlIHdob2xlLXBhcmFtIGVudHJ5IHRvbzogYHRoaXMueCA9IGRhdGFgICh0aGVcblx0XHRcdFx0XHQvLyBiYXJlIHBhcmFtZXRlcikgYXNzaWducyB0aGUgZnVsbCBleHBhbmRlZCBzaGFwZSDigJRcblx0XHRcdFx0XHQvLyB0aGUgc2FtZSBzdHJpbmcgY29uc3RydWN0b3Itc2lnbmF0dXJlIGVtaXNzaW9uIHVzZXNcblx0XHRcdFx0XHRjb25zdCB3aG9sZVR5cGUgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24obmFtZWREZWNsKTtcblx0XHRcdFx0XHRpZiAod2hvbGVUeXBlICYmIHdob2xlVHlwZSAhPT0gJ3Vua25vd24nKSB7XG5cdFx0XHRcdFx0XHR0eXBlTWFwLnNldChwYXJhbU5hbWUsIHdob2xlVHlwZSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdC8vIFN0b3JlIHNpbXBsZSBwYXJhbWV0ZXIgdHlwZXMgbGlrZSBgZGVjb3JhdGVWYWx1ZTogc3RyaW5nYFxuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblx0XHRcdFx0XHRpZiAodHlwZSAhPT0gJ3Vua25vd24nKSB7XG5cdFx0XHRcdFx0XHR0eXBlTWFwLnNldChwYXJhbU5hbWUsIHR5cGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB0eXBlTWFwO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydHkgYWNjZXNzIGNoYWluIChlLmcuLCBcImRhdGFSZW5hbWVkLmlkXCIgZnJvbSBkYXRhUmVuYW1lZC5pZClcblx0ICogSGFuZGxlcyBmYWxsYmFja3MgbGlrZTogZGF0YS5wZXJtaXNzaW9ucyB8fCBbXVxuXHQgKi9cblx0cHJpdmF0ZSBnZXRQcm9wZXJ0eUFjY2Vzc0NoYWluIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBIYW5kbGUgaWRlbnRpZmllcjogZGF0YVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLnRleHQ7XG5cdFx0fVxuXHRcdC8vIEhhbmRsZSBwcm9wZXJ0eSBhY2Nlc3M6IGRhdGEucGVybWlzc2lvbnNcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdGNvbnN0IGJhc2UgPSB0aGlzLmdldFByb3BlcnR5QWNjZXNzQ2hhaW4oZXhwci5leHByZXNzaW9uKTtcblx0XHRcdGlmIChiYXNlKSB7XG5cdFx0XHRcdHJldHVybiBgJHtiYXNlfS4ke2V4cHIubmFtZS50ZXh0fWA7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdC8vIEhhbmRsZSBmYWxsYmFjayBwYXR0ZXJuOiBkYXRhLnBlcm1pc3Npb25zIHx8IFtdXG5cdFx0aWYgKHRzLmlzQmluYXJ5RXhwcmVzc2lvbihleHByKSAmJlxuXHRcdFx0ZXhwci5vcGVyYXRvclRva2VuLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuQmFyQmFyVG9rZW4pIHtcblx0XHRcdC8vIFJldHVybiB0aGUgbGVmdCBzaWRlIG9mIHx8IG9wZXJhdG9yXG5cdFx0XHRyZXR1cm4gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGV4cHIubGVmdCk7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0eSBhc3NpZ25tZW50IGZyb20gc3RhdGVtZW50XG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RQcm9wZXJ0eUZyb21TdGF0ZW1lbnQgKFxuXHRcdGV4cHI6IHRzLkV4cHJlc3Npb24sXG5cdFx0cHJvcGVydGllczogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPixcblx0XHRkYXRhVHlwZU1hcDogTWFwPHN0cmluZywgc3RyaW5nPiA9IG5ldyBNYXAoKVxuXHQpOiB2b2lkIHtcblx0XHQvLyBIYW5kbGU6IHRoaXMucHJvcGVydHkgPSB2YWx1ZVxuXHRcdGlmICh0cy5pc0JpbmFyeUV4cHJlc3Npb24oZXhwcikgJiZcblx0XHRcdGV4cHIub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkVxdWFsc1Rva2VuKSB7XG5cdFx0XHRjb25zdCB7IGxlZnQgfSA9IGV4cHI7XG5cblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihsZWZ0KSkge1xuXHRcdFx0XHQvLyBDaGVjayBpZiBhY2Nlc3NpbmcgJ3RoaXMnIChUaGlzS2V5d29yZClcblx0XHRcdFx0aWYgKGxlZnQuZXhwcmVzc2lvbi5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uc3QgbmFtZSA9IGxlZnQubmFtZT8udGV4dDtcblx0XHRcdFx0XHRpZiAobmFtZSkge1xuXHRcdFx0XHRcdFx0Ly8gVHJ5IHRvIGdldCB0eXBlIGZyb20gZGF0YVR5cGVNYXAgdXNpbmcgZnVsbCBhY2Nlc3MgY2hhaW4gKGUuZy4sIFwiZGF0YVJlbmFtZWQuaWRcIilcblx0XHRcdFx0XHRcdGNvbnN0IGFjY2Vzc0NoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGV4cHIucmlnaHQpO1xuXHRcdFx0XHRcdFx0bGV0IHR5cGUgPSBhY2Nlc3NDaGFpbiA/IGRhdGFUeXBlTWFwLmdldChhY2Nlc3NDaGFpbikgOiB1bmRlZmluZWQ7XG5cdFx0XHRcdFx0XHQvLyBJZiBub3QgZm91bmQgYW5kIFJIUyBpcyBhIHNpbXBsZSBpZGVudGlmaWVyLCB0cnkgbG9va2luZyBpdCB1cCBkaXJlY3RseVxuXHRcdFx0XHRcdFx0aWYgKCF0eXBlICYmIHRzLmlzSWRlbnRpZmllcihleHByLnJpZ2h0KSkge1xuXHRcdFx0XHRcdFx0XHR0eXBlID0gZGF0YVR5cGVNYXAuZ2V0KGV4cHIucmlnaHQudGV4dCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHQvLyBhIGJvdW5kIGNvbnN0cnVjdGlvbiByZXN1bHQgKG5ldy9sb29rdXAvY2hhaW4vZm9yay9cblx0XHRcdFx0XHRcdC8vIG1lcmdlL2NhbGwpOiB0aGUgdmFsdWUgc2NvcGUgYmluZGluZyBzdXBwbGllcyB0aGVcblx0XHRcdFx0XHRcdC8vIGdyYXBoIHR5cGUg4oCUIGVtaXR0ZWQgYnkgaXRzIGluc3RhbmNlLXR5cGUgbmFtZVxuXHRcdFx0XHRcdFx0aWYgKCF0eXBlICYmIHRzLmlzSWRlbnRpZmllcihleHByLnJpZ2h0KSkge1xuXHRcdFx0XHRcdFx0XHRjb25zdCBib3VuZCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGV4cHIucmlnaHQudGV4dCk7XG5cdFx0XHRcdFx0XHRcdGlmIChib3VuZCkge1xuXHRcdFx0XHRcdFx0XHRcdHR5cGUgPSBib3VuZC5yZXBsYWNlKC9cXC4vZywgJ18nKTtcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKCF0eXBlKSB7XG5cdFx0XHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihleHByLnJpZ2h0LCBkYXRhVHlwZU1hcCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHQvLyBEb24ndCBvdmVyd3JpdGUgYSBrbm93biB0eXBlIGZyb20gYSBgdGhpc2AgYW5ub3RhdGlvblxuXHRcdFx0XHRcdFx0Ly8gd2l0aCBhbiB1bmtub3duLWJlYXJpbmcgaW5mZXJlbmNlOiBhbiBlbXB0eS1hcnJheVxuXHRcdFx0XHRcdFx0Ly8gaW5pdGlhbGl6ZXIgaW5mZXJzICdBcnJheTx1bmtub3duPicsIHdoaWNoIG11c3Qgbm90XG5cdFx0XHRcdFx0XHQvLyBjbG9iYmVyIGFuIGFubm90YXRlZCAnQXJyYXk8eyBpZDogbnVtYmVyIH0+JyBlaXRoZXIuXG5cdFx0XHRcdFx0XHQvLyBcIktub3duXCIgb24gdGhlIEVYSVNUSU5HIHNpZGUgbWVhbnMgdGhlIHdob2xlIHR5cGUgSVNcblx0XHRcdFx0XHRcdC8vIGB1bmtub3duYCAoZXhhY3QgbWF0Y2gpIOKAlCBhIHN1YnN0cmluZyBtYXRjaCB0cmVhdHNcblx0XHRcdFx0XHRcdC8vIGBSZWNvcmQ8c3RyaW5nLCB1bmtub3duPmAgYXMgdW5rbm93bi1iZWFyaW5nIGFuZCBsZXRcblx0XHRcdFx0XHRcdC8vIGluZmVyZW5jZSBjbG9iYmVyIGEgZ29vZCBhbm5vdGF0aW9uIChGMTQpXG5cdFx0XHRcdFx0XHRjb25zdCBleGlzdGluZyA9IHByb3BlcnRpZXMuZ2V0KG5hbWUpO1xuXHRcdFx0XHRcdFx0Y29uc3QgdHlwZUhhc1Vua25vd24gPSAhdHlwZSB8fCB0eXBlLmluY2x1ZGVzKCd1bmtub3duJyk7XG5cdFx0XHRcdFx0XHRjb25zdCBleGlzdGluZ0lzS25vd24gPSBleGlzdGluZyA/IGV4aXN0aW5nLnR5cGUudHJpbSgpICE9PSAndW5rbm93bicgOiBmYWxzZTtcblx0XHRcdFx0XHRcdGlmIChleGlzdGluZ0lzS25vd24gJiYgdHlwZUhhc1Vua25vd24pIHtcblx0XHRcdFx0XHRcdFx0Ly8gS2VlcCB0aGUgYmV0dGVyIHR5cGUgZnJvbSBleHBsaWNpdCBhbm5vdGF0aW9uXG5cdFx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZXhpc3RpbmcgPyBleGlzdGluZy5vcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBIYW5kbGU6IE9iamVjdC5hc3NpZ24odGhpcywgeyBwcm9wOiB2YWx1ZSB9KVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBmbiA9IGV4cHIuZXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihmbikgJiZcblx0XHRcdFx0Zm4ubmFtZT8udGV4dCA9PT0gJ2Fzc2lnbicgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGZuLmV4cHJlc3Npb24pICYmXG5cdFx0XHRcdGZuLmV4cHJlc3Npb24udGV4dCA9PT0gJ09iamVjdCcpIHtcblx0XHRcdFx0Y29uc3QgYXJncyA9IGV4cHIuYXJndW1lbnRzO1xuXHRcdFx0XHRpZiAoYXJncy5sZW5ndGggPj0gMiAmJiBhcmdzWyAwIF0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIHRoZSBzZWNvbmQgYXJndW1lbnRcblx0XHRcdFx0XHRjb25zdCBbICwgcHJvcHNBcmcgXSA9IGFyZ3M7XG5cdFx0XHRcdFx0aWYgKHRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24ocHJvcHNBcmcpKSB7XG5cdFx0XHRcdFx0XHRmb3IgKGNvbnN0IHByb3Agb2YgcHJvcHNBcmcucHJvcGVydGllcykge1xuXHRcdFx0XHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFzc2lnbm1lbnQocHJvcCkgJiYgdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkpIHtcblx0XHRcdFx0XHRcdFx0XHRjb25zdCBuYW1lID0gcHJvcC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdFx0XHRcdHR5cGUgICAgIDogdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIocHJvcC5pbml0aWFsaXplciksXG5cdFx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc0lkZW50aWZpZXIocHJvcHNBcmcpKSB7XG5cdFx0XHRcdFx0XHQvLyBPYmplY3QuYXNzaWduKHRoaXMsIGRhdGEpIOKAlCB0aGUgaWRlbnRpZmllciBmb3JtOiBldmVyeVxuXHRcdFx0XHRcdFx0Ly8gcGVyLXByb3BlcnR5IGVudHJ5IHRoZSBkYXRhIHBhcmFtZXRlciBjb250cmlidXRlZCB0b1xuXHRcdFx0XHRcdFx0Ly8gdGhlIHR5cGUgbWFwIGJlY29tZXMgYW4gb3duIHByb3BlcnR5LiBUaGlzIGlzIHdoYXRcblx0XHRcdFx0XHRcdC8vIGNhcnJpZXMgdGhlIGZpZWxkcyBmb3IgdGhlIHNlbGYtcmVmZXJlbmNpbmdcblx0XHRcdFx0XHRcdC8vIGludGVyc2VjdGlvbi1hbGlhcyByb290IHBhdHRlcm4gKEYyMSk6IHRoZSB0aGlzLWFsaWFzXG5cdFx0XHRcdFx0XHQvLyBpcyBlcmdvbm9taWMtb25seSBhbmQgaXRzIGludGVyc2VjdGlvbiBtZW1iZXJzIGFyZVxuXHRcdFx0XHRcdFx0Ly8gbmV2ZXIgZXhwYW5kZWQsIHNvIHRoZSBhc3NpZ24gaXMgd2hlcmUgdGhlIHJvb3Qnc1xuXHRcdFx0XHRcdFx0Ly8gZmllbGRzIG11c3QgY29tZSBmcm9tXG5cdFx0XHRcdFx0XHRjb25zdCBwYXJhbU5hbWUgPSBwcm9wc0FyZy50ZXh0O1xuXHRcdFx0XHRcdFx0Zm9yIChjb25zdCBbIGtleSwgdHlwZSBdIG9mIGRhdGFUeXBlTWFwKSB7XG5cdFx0XHRcdFx0XHRcdGlmICgha2V5LnN0YXJ0c1dpdGgoYCR7cGFyYW1OYW1lfS5gKSkge1xuXHRcdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBrZXkuc2xpY2UocGFyYW1OYW1lLmxlbmd0aCArIDEpO1xuXHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBjbGFzcyBkZWNsYXJhdGlvbiAoaW5jbHVkaW5nIG1ldGhvZHMgYW5kIGdldHRlcnMpXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDbGFzc1Byb3BlcnRpZXMgKGNsYXNzRGVjbDogdHMuQ2xhc3NEZWNsYXJhdGlvbik6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgY2xhc3NEZWNsLm1lbWJlcnMpIHtcblx0XHRcdC8vIEhhbmRsZSBwcm9wZXJ0eSBkZWNsYXJhdGlvbnNcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5RGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSkge1xuXHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBwcm9wZXJ0aWVzXG5cdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHQgICAgIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkKTtcblx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRjb25zdCBuYW1lID0gdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSA/IG1lbWJlci5uYW1lLnRleHQgOiAnJztcblx0XHRcdFx0aWYgKG5hbWUpIHtcblx0XHRcdFx0XHQvLyBJZiBubyBleHBsaWNpdCB0eXBlIGJ1dCBoYXMgaW5pdGlhbGl6ZXIsIGluZmVyIGZyb20gaW5pdGlhbGl6ZXJcblx0XHRcdFx0XHRsZXQgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRpZiAodHlwZSA9PT0gJ3Vua25vd24nICYmIG1lbWJlci5pbml0aWFsaXplcikge1xuXHRcdFx0XHRcdFx0dHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKG1lbWJlci5pbml0aWFsaXplcik7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdC8vIEhhbmRsZSBtZXRob2QgZGVjbGFyYXRpb25zXG5cdFx0XHRpZiAodHMuaXNNZXRob2REZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgbWV0aG9kc1xuXHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0ICAgICBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZCk7XG5cdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyTWV0aG9kVHlwZShtZW1iZXIpO1xuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBIYW5kbGUgZ2V0dGVyIGRlY2xhcmF0aW9uc1xuXHRcdFx0aWYgKHRzLmlzR2V0QWNjZXNzb3IobWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIGdldHRlcnNcblx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdCAgICAgbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQpO1xuXHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHQvLyBGaXJzdCB0cnkgZXhwbGljaXQgdHlwZSBhbm5vdGF0aW9uLCB0aGVuIGluZmVyIGZyb20gZ2V0dGVyIGJvZHlcblx0XHRcdFx0bGV0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdGlmICh0eXBlID09PSAndW5rbm93bicgJiYgbWVtYmVyLmJvZHkpIHtcblx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclJldHVyblR5cGVGcm9tQm9keShtZW1iZXIuYm9keSk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdHJlYWRvbmx5IDogdHJ1ZSxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBjbGFzcyBwcm9wZXJ0eSB0eXBlcyBmb3IgbWV0aG9kIHJldHVybiB0eXBlIGluZmVyZW5jZVxuXHQgKiBNYXBzIHByb3BlcnR5IG5hbWVzIHRvIHRoZWlyIFR5cGVTY3JpcHQgdHlwZSBzdHJpbmdzXG5cdCAqIE5vdGU6IEluY2x1ZGVzIHByaXZhdGUvcHJvdGVjdGVkIHByb3BlcnRpZXMgZm9yIG1ldGhvZCBpbmZlcmVuY2Vcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENsYXNzUHJvcGVydHlUeXBlcyAoY2xhc3NEZWNsOiB0cy5DbGFzc0V4cHJlc3Npb24pOiBNYXA8c3RyaW5nLCBzdHJpbmc+IHtcblx0XHRjb25zdCBwcm9wZXJ0eVR5cGVzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblxuXHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGNsYXNzRGVjbC5tZW1iZXJzKSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eURlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHQvLyBJbmNsdWRlIEFMTCBwcm9wZXJ0aWVzIChldmVuIHByaXZhdGUpIGZvciBtZXRob2QgcmV0dXJuIHR5cGUgaW5mZXJlbmNlXG5cdFx0XHRcdC8vIFRoZSB2aXNpYmlsaXR5IGNoZWNrIGlzIGRvbmUgd2hlbiBhZGRpbmcgdG8gb3V0cHV0IHByb3BlcnRpZXNcblx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdGlmIChtZW1iZXIudHlwZSkge1xuXHRcdFx0XHRcdHByb3BlcnR5VHlwZXMuc2V0KG5hbWUsIHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydHlUeXBlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBJbmZlciBtZXRob2QgdHlwZSBmcm9tIG1ldGhvZCBkZWNsYXJhdGlvblxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlck1ldGhvZFR5cGUgKG1ldGhvZDogdHMuTWV0aG9kRGVjbGFyYXRpb24sIGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz4pOiBzdHJpbmcge1xuXHRcdGNvbnN0IHBhcmFtcyA9IG1ldGhvZC5wYXJhbWV0ZXJzLm1hcChwYXJhbSA9PiB7XG5cdFx0XHRjb25zdCBwYXJhbU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgPyBwYXJhbS5uYW1lLnRleHQgOiAnYXJnJztcblx0XHRcdGNvbnN0IHBhcmFtVHlwZSA9IHRoaXMuaW5mZXJUeXBlKHBhcmFtLnR5cGUpO1xuXHRcdFx0cmV0dXJuIGAke3BhcmFtTmFtZX06ICR7cGFyYW1UeXBlfWA7XG5cdFx0fSkuam9pbignLCAnKTtcblxuXHRcdGNvbnN0IHJldHVyblR5cGUgPSB0aGlzLmluZmVyUmV0dXJuVHlwZShtZXRob2QsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cblx0XHRpZiAocGFyYW1zKSB7XG5cdFx0XHRyZXR1cm4gYCgke3BhcmFtc30pID0+ICR7cmV0dXJuVHlwZX1gO1xuXHRcdH1cblx0XHRyZXR1cm4gYCgpID0+ICR7cmV0dXJuVHlwZX1gO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBgdGhpc2AgcGFyYW1ldGVyIHR5cGUgYW5ub3RhdGlvblxuXHRcdCogSGFuZGxlcyBwYXR0ZXJucyBsaWtlOiBmdW5jdGlvbih0aGlzOiBTb21lVHlwZSwgZGF0YTogU29tZVR5cGUpIHsgfVxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdFRoaXNQYXJhbVByb3BlcnRpZXMgKGhhbmRsZXJBcmc6IHRzLkZ1bmN0aW9uRXhwcmVzc2lvbiB8IHRzLkFycm93RnVuY3Rpb24pOlxuXHRcdE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Ly8gRmluZCB0aGUgYHRoaXNgIHBhcmFtZXRlciAoaWYgYW55KVxuXHRcdGZvciAoY29uc3QgcGFyYW0gb2YgaGFuZGxlckFyZy5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRpZiAocGFyYW0ubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgJiYgcGFyYW0ubmFtZS50ZXh0ID09PSAndGhpcycgJiYgcGFyYW0udHlwZSkge1xuXHRcdFx0XHQvLyBDaGVjayBpZiBpdCdzIGEgdHlwZSByZWZlcmVuY2UgKGUuZy4sIGB0aGlzOiB1c2FnZWApXG5cdFx0XHRcdGlmICh0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHBhcmFtLnR5cGUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSlcblx0XHRcdFx0XHRcdD8gcGFyYW0udHlwZS50eXBlTmFtZS50ZXh0XG5cdFx0XHRcdFx0XHQ6ICcnO1xuXG5cdFx0XHRcdFx0Ly8gUmVzb2x2ZSB0aHJvdWdoIHRoZSByZWZlcmVuY2luZyBmaWxlJ3Mgb3duIGltcG9ydHMgZmlyc3QgKEYxMClcblx0XHRcdFx0XHRjb25zdCBkZWNsID0gdHlwZU5hbWVcblx0XHRcdFx0XHRcdD8gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbih0eXBlTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKVxuXHRcdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cdFx0XHRcdFx0aWYgKGRlY2wpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGRlY2xQcm9wZXJ0aWVzID0gdGhpcy5yZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzKGRlY2wpO1xuXHRcdFx0XHRcdFx0Zm9yIChjb25zdCBbIHByb3BOYW1lLCBpbmZvIF0gb2YgZGVjbFByb3BlcnRpZXMpIHtcblx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQocHJvcE5hbWUsIGluZm8pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBDaGVjayBpZiBpdCdzIGRpcmVjdGx5IGFuIGlubGluZSB0eXBlIGxpdGVyYWwgKGUuZy4sIGB0aGlzOiB7IGlkOiBzdHJpbmcgfWApXG5cdFx0XHRcdGVsc2UgaWYgKHRzLmlzVHlwZUxpdGVyYWxOb2RlKHBhcmFtLnR5cGUpKSB7XG5cdFx0XHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgcGFyYW0udHlwZS5tZW1iZXJzKSB7XG5cdFx0XHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChwcm9wTmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdG5hbWUgICAgIDogcHJvcE5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBGb3VuZCB0aGUgYHRoaXNgIHBhcmFtZXRlciwgbm8gbmVlZCB0byBjb250aW51ZVxuXHRcdFx0XHRicmVhaztcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdC8qKlxuXHRcdCogSW5mZXIgVHlwZVNjcmlwdCB0eXBlIGZyb20gdHlwZSBub2RlXG5cdFx0Ki9cblx0LyoqXG5cdCAqIEluZmVyIFR5cGVTY3JpcHQgdHlwZSBmcm9tIHR5cGUgbm9kZVxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlclR5cGUgKHR5cGVOb2RlPzogdHMuVHlwZU5vZGUpOiBzdHJpbmcge1xuXHRcdGlmICghdHlwZU5vZGUpIHtcblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXG5cdFx0c3dpdGNoICh0eXBlTm9kZS5raW5kKSB7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlN0cmluZ0tleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bWJlcktleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkJvb2xlYW5LZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5kZWZpbmVkS2V5d29yZDpcblx0XHRcdHJldHVybiAndW5kZWZpbmVkJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bGwnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5BbnlLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdhbnknO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Vbmtub3duS2V5d29yZDpcblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlZvaWRLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICd2b2lkJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQXJyYXlUeXBlOlxuXHRcdFx0cmV0dXJuIGBBcnJheTwkeyAgdGhpcy5pbmZlclR5cGUoKHR5cGVOb2RlIGFzIHRzLkFycmF5VHlwZU5vZGUpLmVsZW1lbnRUeXBlKSAgfT5gO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlTGl0ZXJhbDoge1xuXHRcdFx0Ly8gSW5saW5lLWV4cGFuZCB0eXBlIGxpdGVyYWxzIGluc3RlYWQgb2YgY29sbGFwc2luZyB0byAnb2JqZWN0J1xuXHRcdFx0Y29uc3QgdHlwZUxpdCA9IHR5cGVOb2RlIGFzIHRzLlR5cGVMaXRlcmFsTm9kZTtcblx0XHRcdGNvbnN0IHByb3BzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgdHlwZUxpdC5tZW1iZXJzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRjb25zdCBvcHRpb25hbCA9IG1lbWJlci5xdWVzdGlvblRva2VuID8gJz8nIDogJyc7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRwcm9wcy5wdXNoKGAke3Byb3BOYW1lfSR7b3B0aW9uYWx9OiAke3R5cGV9YCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiBgeyAke3Byb3BzLmpvaW4oJzsgJyl9IH1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTGl0ZXJhbFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBzdHJpbmcgbGl0ZXJhbCB0eXBlcyBsaWtlICd1c2VyJywgJ2FkbWluJywgZXRjLlxuXHRcdFx0Y29uc3QgeyBsaXRlcmFsIH0gPSAodHlwZU5vZGUgYXMgdHMuTGl0ZXJhbFR5cGVOb2RlKTtcblx0XHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwobGl0ZXJhbCkpIHtcblx0XHRcdFx0Ly8gUmV0dXJuIHRoZSBhY3R1YWwgbGl0ZXJhbCB2YWx1ZSAoZS5nLiwgJ3VzZXInIGluc3RlYWQgb2Ygc3RyaW5nKVxuXHRcdFx0XHRyZXR1cm4gYCcke2xpdGVyYWwudGV4dH0nYDtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc051bWVyaWNMaXRlcmFsKGxpdGVyYWwpKSB7XG5cdFx0XHRcdHJldHVybiBsaXRlcmFsLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAobGl0ZXJhbC5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdHJldHVybiAndHJ1ZSc7XG5cdFx0XHR9XG5cdFx0XHRpZiAobGl0ZXJhbC5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRyZXR1cm4gJ2ZhbHNlJztcblx0XHRcdH1cblx0XHRcdGlmIChsaXRlcmFsLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQpIHtcblx0XHRcdFx0cmV0dXJuICdudWxsJztcblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlUmVmZXJlbmNlOiB7XG5cdFx0XHQvLyBIYW5kbGUgdHlwZSByZWZlcmVuY2VzIGxpa2UgTWFwPHN0cmluZywgbnVtYmVyPiwgUHJvcGVydHlJbmZvLCBldGMuXG5cdFx0XHRjb25zdCB0eXBlUmVmID0gdHlwZU5vZGUgYXMgdHMuVHlwZVJlZmVyZW5jZU5vZGU7XG5cblx0XHRcdC8vIFF1YWxpZmllZCBuYW1lcyAoTmFtZXNwYWNlLlR5cGUpOiByZXNvbHZlIHRocm91Z2ggbmFtZXNwYWNlIGltcG9ydHNcblx0XHRcdGlmICh0cy5pc1F1YWxpZmllZE5hbWUodHlwZVJlZi50eXBlTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcmVzb2x2ZWRRdWFsaWZpZWQgPSB0aGlzLmluZmVyUXVhbGlmaWVkVHlwZVJlZmVyZW5jZSh0eXBlUmVmKTtcblx0XHRcdFx0aWYgKHJlc29sdmVkUXVhbGlmaWVkICE9PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0XHRyZXR1cm4gcmVzb2x2ZWRRdWFsaWZpZWQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gdW5yZXNvbHZlZCBxdWFsaWZpZWQgcmVmZXJlbmNlcyBtdXN0IG5vdCBsZWFrIGEgYmFyZSBuYW1lXG5cdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHR9XG5cblx0XHRcdGNvbnN0IHR5cGVOYW1lID0gdHMuaXNJZGVudGlmaWVyKHR5cGVSZWYudHlwZU5hbWUpID8gdHlwZVJlZi50eXBlTmFtZS50ZXh0IDogJ3Vua25vd24nO1xuXG5cdFx0XHQvLyBJbXBvcnQtYXdhcmUgcmVmZXJlbmNlZC10eXBlIHJlc29sdXRpb24gKEYxMCk6IGEgZGVjbGFyYXRpb25cblx0XHRcdC8vIHJlYWNoZWQgdGhyb3VnaCB0aGUgY3VycmVudCBmaWxlJ3Mgb3duIGltcG9ydHMgKG9yIGl0cyBsb2NhbHMsXG5cdFx0XHQvLyBvciBhIHVuaXF1ZSBwcm9ncmFtLXdpZGUgZGVjbGFyYXRpb24pIGV4cGFuZHMgaW5saW5lXG5cdFx0XHRjb25zdCBzaW1wbGVSZWYgPSB0aGlzLnJlc29sdmVTaW1wbGVUeXBlUmVmZXJlbmNlKHR5cGVOYW1lLCB0eXBlUmVmLnR5cGVBcmd1bWVudHMsIHR5cGVSZWYpO1xuXHRcdFx0aWYgKHNpbXBsZVJlZiAhPT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdHJldHVybiBzaW1wbGVSZWY7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEJ1aWxkIGdlbmVyaWMgdHlwZSBhcmd1bWVudHNcblx0XHRcdGNvbnN0IHR5cGVBcmdzID0gKHR5cGVSZWYudHlwZUFyZ3VtZW50cyA/PyBbXSkubWFwKGFyZyA9PiB0aGlzLmluZmVyVHlwZShhcmcpKTtcblx0XHRcdHJldHVybiBgJHt0eXBlTmFtZX08JHt0eXBlQXJncy5qb2luKCcsICcpfT5gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5pb25UeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgdW5pb24gdHlwZXMgbGlrZSAnYScgfCAnYicgfCAnYydcblx0XHRcdGNvbnN0IHVuaW9uVHlwZSA9IHR5cGVOb2RlIGFzIHRzLlVuaW9uVHlwZU5vZGU7XG5cdFx0XHRjb25zdCB0eXBlcyA9IHVuaW9uVHlwZS50eXBlcy5tYXAodCA9PiB0aGlzLmluZmVyVHlwZSh0KSk7XG5cdFx0XHRyZXR1cm4gdHlwZXMuam9pbignIHwgJyk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5JbnRlcnNlY3Rpb25UeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgaW50ZXJzZWN0aW9uIHR5cGVzIGxpa2UgVHlwZUEgJiBUeXBlQlxuXHRcdFx0Y29uc3QgaW50ZXJzZWN0aW9uVHlwZSA9IHR5cGVOb2RlIGFzIHRzLkludGVyc2VjdGlvblR5cGVOb2RlO1xuXHRcdFx0Y29uc3QgdHlwZXMgPSBpbnRlcnNlY3Rpb25UeXBlLnR5cGVzLm1hcCh0ID0+IHRoaXMuaW5mZXJUeXBlKHQpKTtcblx0XHRcdHJldHVybiB0eXBlcy5qb2luKCcgJiAnKTtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR1cGxlVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHR1cGxlIHR5cGVzIGxpa2UgW3N0cmluZywgbnVtYmVyXVxuXHRcdFx0Y29uc3QgdHVwbGVUeXBlID0gdHlwZU5vZGUgYXMgdHMuVHVwbGVUeXBlTm9kZTtcblx0XHRcdGNvbnN0IGVsZW1lbnRzID0gdHVwbGVUeXBlLmVsZW1lbnRzLm1hcChlbGVtID0+IHRoaXMuaW5mZXJUeXBlKGVsZW0gYXMgdHMuVHlwZU5vZGUpKTtcblx0XHRcdHJldHVybiBgWyR7ZWxlbWVudHMuam9pbignLCAnKX1dYDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk9wdGlvbmFsVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIG9wdGlvbmFsIGVsZW1lbnQgaW4gdHVwbGU6IHN0cmluZz9cblx0XHRcdGNvbnN0IG9wdGlvbmFsVHlwZSA9IHR5cGVOb2RlIGFzIHRzLk9wdGlvbmFsVHlwZU5vZGU7XG5cdFx0XHRyZXR1cm4gYCR7dGhpcy5pbmZlclR5cGUob3B0aW9uYWxUeXBlLnR5cGUpICB9P2A7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5SZXN0VHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHJlc3QgZWxlbWVudDogLi4uVFxuXHRcdFx0Y29uc3QgcmVzdFR5cGUgPSB0eXBlTm9kZSBhcyB0cy5SZXN0VHlwZU5vZGU7XG5cdFx0XHRyZXR1cm4gYC4uLiR7ICB0aGlzLmluZmVyVHlwZShyZXN0VHlwZS50eXBlKX1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuUGFyZW50aGVzaXplZFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBwYXJlbnRoZXNpemVkIHR5cGVzOiAoQSB8IEIpXG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclR5cGUoKHR5cGVOb2RlIGFzIHRzLlBhcmVudGhlc2l6ZWRUeXBlTm9kZSkudHlwZSk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5JbmRleGVkQWNjZXNzVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIGluZGV4ZWQgYWNjZXNzOiBUW0tdXG5cdFx0XHRjb25zdCBpbmRleGVkID0gdHlwZU5vZGUgYXMgdHMuSW5kZXhlZEFjY2Vzc1R5cGVOb2RlO1xuXHRcdFx0Ly8gRjIzOiB1bndyYXAgcGFyZW50aGVzZXMgYXJvdW5kIHRoZSBvYmplY3Qg4oCUIGAodHlwZW9mXG5cdFx0XHQvLyBsaXN0KVtudW1iZXJdYCBtdXN0IHRha2UgdGhlIHR5cGVvZiBicmFuY2ggbGlrZSB0aGUgYmFyZVxuXHRcdFx0Ly8gc3BlbGxpbmc7IG90aGVyd2lzZSB0aGUgZ2VuZXJhbCBwYXRoIGluZmVycyB0aGUgdW5pb24gYW5kXG5cdFx0XHQvLyBnbHVlcyB0aGUgc3VmZml4IG9udG8gdGhlIExBU1QgbWVtYmVyXG5cdFx0XHQvLyAoYCdhJyB8ICdiJ1tudW1iZXJdYClcblx0XHRcdGxldCBvYmplY3ROb2RlOiB0cy5UeXBlTm9kZSA9IGluZGV4ZWQub2JqZWN0VHlwZTtcblx0XHRcdHdoaWxlICh0cy5pc1BhcmVudGhlc2l6ZWRUeXBlTm9kZShvYmplY3ROb2RlKSkge1xuXHRcdFx0XHRvYmplY3ROb2RlID0gb2JqZWN0Tm9kZS50eXBlO1xuXHRcdFx0fVxuXHRcdFx0Ly8gYHR5cGVvZiBjb25zdEFycmF5W0tdYCDigJQgZWxlbWVudCB0eXBlIG9mIGEgdHJhY2tlZCBjb25zdCBhcnJheTpcblx0XHRcdC8vIGVtaXQgdGhlIGVsZW1lbnQgbGl0ZXJhbCB1bmlvbiBkaXJlY3RseSAoYXNzZW1ibGluZ1xuXHRcdFx0Ly8gYHVuaW9uW0tdYCB0ZXh0IHdvdWxkIG1pc3JlYWQgcHJlY2VkZW5jZSwgYW5kIHdoZW4gdGhlIGNvbnN0XG5cdFx0XHQvLyBpcyBub3Qgc3RhdGljYWxseSB2aXNpYmxlIHRoZSBob25lc3QgYW5zd2VyIGlzIGB1bmtub3duYCxcblx0XHRcdC8vIG5ldmVyIGEgYmFyZSBgdHlwZW9mIG5hbWVgIHF1ZXJ5KVxuXHRcdFx0aWYgKHRzLmlzVHlwZVF1ZXJ5Tm9kZShvYmplY3ROb2RlKSAmJiB0cy5pc0lkZW50aWZpZXIob2JqZWN0Tm9kZS5leHByTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcXVlcnlOYW1lID0gb2JqZWN0Tm9kZS5leHByTmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBhcnJheUxpdGVyYWwgPSB0aGlzLmZpbmRSZWZlcmVuY2VkQ29uc3RBcnJheShxdWVyeU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRcdGNvbnN0IGxpdGVyYWxzID0gYXJyYXlMaXRlcmFsID8gdGhpcy5saXRlcmFsVHlwZXNPZkFycmF5KGFycmF5TGl0ZXJhbCkgOiB1bmRlZmluZWQ7XG5cdFx0XHRcdGlmICghbGl0ZXJhbHMpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmICh0cy5pc0xpdGVyYWxUeXBlTm9kZShpbmRleGVkLmluZGV4VHlwZSkgJiYgdHMuaXNOdW1lcmljTGl0ZXJhbChpbmRleGVkLmluZGV4VHlwZS5saXRlcmFsKSkge1xuXHRcdFx0XHRcdGNvbnN0IGVsZW1lbnRJbmRleCA9IHBhcnNlSW50KGluZGV4ZWQuaW5kZXhUeXBlLmxpdGVyYWwudGV4dCwgMTApO1xuXHRcdFx0XHRcdGNvbnN0IGVsZW1lbnQgPSBsaXRlcmFsc1sgZWxlbWVudEluZGV4IF07XG5cdFx0XHRcdFx0Y29uc3QgZWxlbWVudFJlc3VsdCA9IGVsZW1lbnQgPT09IHVuZGVmaW5lZCA/ICd1bmtub3duJyA6IGVsZW1lbnQ7XG5cdFx0XHRcdFx0cmV0dXJuIGVsZW1lbnRSZXN1bHQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgdW5pb25SZXN1bHQgPSBsaXRlcmFscy5qb2luKCcgfCAnKTtcblx0XHRcdFx0cmV0dXJuIHVuaW9uUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0bGV0IG9iamVjdFR5cGUgPSB0aGlzLmluZmVyVHlwZShvYmplY3ROb2RlKTtcblx0XHRcdGNvbnN0IGluZGV4VHlwZSA9IHRoaXMuaW5mZXJUeXBlKGluZGV4ZWQuaW5kZXhUeXBlKTtcblx0XHRcdC8vIElmIG9iamVjdFR5cGUgaXMgJ29iamVjdCcsIHRyeSB0byByZXNvbHZlIHRoZSB1bmRlcmx5aW5nIHJlZmVyZW5jZWQgdHlwZVxuXHRcdFx0aWYgKG9iamVjdFR5cGUgPT09ICdvYmplY3QnICYmIHRzLmlzVHlwZVJlZmVyZW5jZU5vZGUob2JqZWN0Tm9kZSkpIHtcblx0XHRcdFx0Y29uc3QgcmVmTmFtZSA9IHRzLmlzSWRlbnRpZmllcihvYmplY3ROb2RlLnR5cGVOYW1lKSA/IG9iamVjdE5vZGUudHlwZU5hbWUudGV4dCA6ICcnO1xuXHRcdFx0XHRpZiAocmVmTmFtZSkge1xuXHRcdFx0XHRcdGNvbnN0IGRlY2wgPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKHJlZk5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRcdFx0aWYgKGRlY2wpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGV4cGFuZGVkID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKGRlY2wpO1xuXHRcdFx0XHRcdFx0aWYgKGV4cGFuZGVkKSB7XG5cdFx0XHRcdFx0XHRcdG9iamVjdFR5cGUgPSBleHBhbmRlZDtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIEludmFyaWFudDogYW4gaW5kZXggc3VmZml4IG11c3QgTkVWRVIgYmUgZ2x1ZWQgb250byBhblxuXHRcdFx0Ly8gdW5yZXNvbHZlZC9mYWxsYmFjayB0YXJnZXQg4oCUIGB1bmtub3duW251bWJlcl1gIC8gYG9iamVjdFtLXWBcblx0XHRcdC8vIGFyZSBpbnZhbGlkIFR5cGVTY3JpcHQgaW4gdGhlIGdlbmVyYXRlZCBmaWxlIChoYXJkIGNvbXBpbGVcblx0XHRcdC8vIGJyZWFrLCBGMTcpLiBXaGVuIGVpdGhlciBzaWRlIGRpZCBub3QgcmVzb2x2ZSwgdGhlIFdIT0xFXG5cdFx0XHQvLyBpbmRleGVkIGFjY2VzcyBkZWdyYWRlcyB0byBgdW5rbm93bmAuXG5cdFx0XHRjb25zdCB0YXJnZXRVbnJlc29sdmVkID0gb2JqZWN0VHlwZSA9PT0gJ3Vua25vd24nIHx8IG9iamVjdFR5cGUgPT09ICdvYmplY3QnO1xuXHRcdFx0Y29uc3QgaW5kZXhVbnJlc29sdmVkID0gaW5kZXhUeXBlID09PSAndW5rbm93bic7XG5cdFx0XHRpZiAodGFyZ2V0VW5yZXNvbHZlZCB8fCBpbmRleFVucmVzb2x2ZWQpIHtcblx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdH1cblx0XHRcdHJldHVybiBgJHtvYmplY3RUeXBlfVske2luZGV4VHlwZX1dYDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR5cGVPcGVyYXRvcjoge1xuXHRcdFx0Ly8gSGFuZGxlIGtleW9mLCByZWFkb25seSwgdW5pcXVlIG9wZXJhdG9yc1xuXHRcdFx0Y29uc3QgdHlwZU9wID0gdHlwZU5vZGUgYXMgdHMuVHlwZU9wZXJhdG9yTm9kZTtcblx0XHRcdGNvbnN0IG9wZXJhdG9yID0gdHMuU3ludGF4S2luZFsgdHlwZU9wLm9wZXJhdG9yIF07XG5cdFx0XHRyZXR1cm4gYCR7b3BlcmF0b3J9ICR7dGhpcy5pbmZlclR5cGUodHlwZU9wLnR5cGUpfWA7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlUXVlcnk6IHtcblx0XHRcdC8vIGB0eXBlb2YgeGAgYXMgYSBGSUVMRCBUWVBFOiB0aGUgZ2VuZXJhdGVkIGZpbGUgaGFzIG5vIGltcG9ydHMsXG5cdFx0XHQvLyBzbyBhIGJhcmUgYHR5cGVvZiB4YCB3b3VsZCBiZSBhbiB1bnJlc29sdmFibGUgbmFtZSBkb3duc3RyZWFtLlxuXHRcdFx0Ly8gV2hlbiB4IGlzIGEgdHJhY2tlZCBjb25zdCBhcnJheSwgZW1pdCBpdHMgZWxlbWVudCBsaXRlcmFsXG5cdFx0XHQvLyB1bmlvbjsgb3RoZXJ3aXNlIGRlZ3JhZGUgdG8gYHVua25vd25gLiAoSW5zdGFuY2VUeXBlPHR5cGVvZiBYPlxuXHRcdFx0Ly8gZ3JhcGggdHlwZXMgYXJlIGhhbmRsZWQgaW4gcmVzb2x2ZVNpbXBsZVR5cGVSZWZlcmVuY2UgYmVmb3JlXG5cdFx0XHQvLyBpbmZlclR5cGUgcnVucy4pXG5cdFx0XHRjb25zdCB0eXBlUXVlcnkgPSB0eXBlTm9kZSBhcyB0cy5UeXBlUXVlcnlOb2RlO1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcih0eXBlUXVlcnkuZXhwck5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHVuaW9uID0gdGhpcy50eXBlT2ZDb25zdEFycmF5VW5pb24odHlwZVF1ZXJ5LmV4cHJOYW1lLnRleHQsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRcdGlmICh1bmlvbikge1xuXHRcdFx0XHRcdHJldHVybiB1bmlvbjtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0ZGVmYXVsdDpcblx0XHRcdC8vIEZvciBjb21wbGV4IHR5cGVzLCByZXR1cm4gdGhlIHRleHQgcmVwcmVzZW50YXRpb25cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdFx0KiBJbmZlciByZXR1cm4gdHlwZSBmcm9tIGEgbWV0aG9kIGRlY2xhcmF0aW9uXG5cdFx0KiBVc2VzIGV4cGxpY2l0IHJldHVybiB0eXBlIGFubm90YXRpb24gb3IgaW5mZXJzIGZyb20gcmV0dXJuIHN0YXRlbWVudHNcblx0XHQqL1xuXHRwcml2YXRlIGluZmVyUmV0dXJuVHlwZSAobWV0aG9kOiB0cy5NZXRob2REZWNsYXJhdGlvbiwgY2xhc3NQcm9wZXJ0eVR5cGVzPzogTWFwPHN0cmluZywgc3RyaW5nPik6IHN0cmluZyB7XG5cdFx0Ly8gSWYgbWV0aG9kIGhhcyBleHBsaWNpdCByZXR1cm4gdHlwZSBhbm5vdGF0aW9uLCB1c2UgaXRcblx0XHRpZiAobWV0aG9kLnR5cGUpIHtcblx0XHRcdHJldHVybiB0aGlzLmluZmVyVHlwZShtZXRob2QudHlwZSk7XG5cdFx0fVxuXG5cdFx0Ly8gT3RoZXJ3aXNlLCB0cnkgdG8gaW5mZXIgZnJvbSByZXR1cm4gc3RhdGVtZW50cyBpbiB0aGUgbWV0aG9kIGJvZHlcblx0XHRpZiAobWV0aG9kLmJvZHkpIHtcblx0XHRcdHJldHVybiB0aGlzLmluZmVyUmV0dXJuVHlwZUZyb21Cb2R5KG1ldGhvZC5ib2R5LCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdH1cblxuXHRcdHJldHVybiAndW5rbm93bic7XG5cdH1cblxuXHQvKipcblx0XHQqIEluZmVyIHJldHVybiB0eXBlIGJ5IGFuYWx5emluZyByZXR1cm4gc3RhdGVtZW50cyBpbiB0aGUgbWV0aG9kIGJvZHlcblx0XHQqL1xuXHRwcml2YXRlIGluZmVyUmV0dXJuVHlwZUZyb21Cb2R5IChib2R5OiB0cy5CbG9jaywgY2xhc3NQcm9wZXJ0eVR5cGVzPzogTWFwPHN0cmluZywgc3RyaW5nPik6IHN0cmluZyB7XG5cdFx0Y29uc3QgcmV0dXJuVHlwZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblxuXHRcdGNvbnN0IHZpc2l0ID0gKG5vZGU6IHRzLk5vZGUpOiB2b2lkID0+IHtcblx0XHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKG5vZGUuZXhwcmVzc2lvbiwgdW5kZWZpbmVkLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0XHRpZiAodHlwZSAhPT0gJ3Vua25vd24nKSB7XG5cdFx0XHRcdFx0cmV0dXJuVHlwZXMuYWRkKHR5cGUpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgdmlzaXQpO1xuXHRcdH07XG5cblx0XHR2aXNpdChib2R5KTtcblxuXHRcdGlmIChyZXR1cm5UeXBlcy5zaXplID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gJ3ZvaWQnO1xuXHRcdH1cblx0XHRpZiAocmV0dXJuVHlwZXMuc2l6ZSA9PT0gMSkge1xuXHRcdFx0cmV0dXJuIEFycmF5LmZyb20ocmV0dXJuVHlwZXMpWyAwIF07XG5cdFx0fVxuXHRcdHJldHVybiBBcnJheS5mcm9tKHJldHVyblR5cGVzKS5qb2luKCcgfCAnKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBJbmZlciB0eXBlIGZyb20gaW5pdGlhbGl6ZXJcblx0ICovXG5cdHByaXZhdGUgaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyIChcblx0XHRpbml0aWFsaXplcjogdHMuRXhwcmVzc2lvbixcblx0XHRkYXRhVHlwZU1hcD86IE1hcDxzdHJpbmcsIHN0cmluZz4sXG5cdFx0Y2xhc3NQcm9wZXJ0eVR5cGVzPzogTWFwPHN0cmluZywgc3RyaW5nPlxuXHQpOiBzdHJpbmcge1xuXHRcdHN3aXRjaCAoaW5pdGlhbGl6ZXIua2luZCkge1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5TdHJpbmdMaXRlcmFsOlxuXHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OdW1lcmljTGl0ZXJhbDpcblx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHJ1ZUtleXdvcmQ6XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZDpcblx0XHRcdHJldHVybiAnYm9vbGVhbic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bGxLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdudWxsJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5kZWZpbmVkS2V5d29yZDpcblx0XHRcdHJldHVybiAndW5kZWZpbmVkJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbjpcblx0XHRcdHJldHVybiAnQXJyYXk8dW5rbm93bj4nO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5PYmplY3RMaXRlcmFsRXhwcmVzc2lvbjpcblx0XHRcdHJldHVybiAnb2JqZWN0Jztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTmV3RXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gSGFuZGxlIG5ldyBEYXRlKCksIG5ldyBNYXAoKSwgZXRjLlxuXHRcdFx0Y29uc3QgbmV3RXhwciA9IGluaXRpYWxpemVyIGFzIHRzLk5ld0V4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG5ld0V4cHIuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0cmV0dXJuIG5ld0V4cHIuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICdvYmplY3QnO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQmluYXJ5RXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gSGFuZGxlIGFyaXRobWV0aWMgb3BlcmF0aW9uczogYSAqIGIsIGEgKyBiLCBhIC0gYiwgYSAvIGJcblx0XHRcdGNvbnN0IGJpbmFyeUV4cHIgPSBpbml0aWFsaXplciBhcyB0cy5CaW5hcnlFeHByZXNzaW9uO1xuXHRcdFx0Y29uc3QgbGVmdFR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihiaW5hcnlFeHByLmxlZnQsIGRhdGFUeXBlTWFwLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0Y29uc3QgcmlnaHRUeXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIoYmluYXJ5RXhwci5yaWdodCwgZGF0YVR5cGVNYXAsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdFxuXHRcdFx0Ly8gQ2hlY2sgaWYgaXQncyBhbiBhcml0aG1ldGljIG9wZXJhdG9yXG5cdFx0XHRjb25zdCBvcGVyYXRvciA9IGJpbmFyeUV4cHIub3BlcmF0b3JUb2tlbi5raW5kO1xuXHRcdFx0aWYgKG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLkFzdGVyaXNrVG9rZW4gfHxcblx0XHRcdFx0ICAgIG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLlNsYXNoVG9rZW4gfHxcblx0XHRcdFx0ICAgIG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLk1pbnVzVG9rZW4gfHxcblx0XHRcdFx0ICAgIG9wZXJhdG9yID09PSB0cy5TeW50YXhLaW5kLlBlcmNlbnRUb2tlbikge1xuXHRcdFx0XHQvLyBBcml0aG1ldGljIG9wZXJhdGlvbnMgb24gbnVtYmVycyBwcm9kdWNlIG51bWJlcnNcblx0XHRcdFx0aWYgKChsZWZ0VHlwZSA9PT0gJ251bWJlcicgfHwgbGVmdFR5cGUgPT09ICd1bmtub3duJykgJiZcblx0XHRcdFx0XHQgICAgKHJpZ2h0VHlwZSA9PT0gJ251bWJlcicgfHwgcmlnaHRUeXBlID09PSAndW5rbm93bicpKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAob3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuUGx1c1Rva2VuKSB7XG5cdFx0XHRcdC8vIFBsdXMgY2FuIGJlIGFkZGl0aW9uIG9yIHN0cmluZyBjb25jYXRlbmF0aW9uXG5cdFx0XHRcdGlmIChsZWZ0VHlwZSA9PT0gJ3N0cmluZycgfHwgcmlnaHRUeXBlID09PSAnc3RyaW5nJykge1xuXHRcdFx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAobGVmdFR5cGUgPT09ICdudW1iZXInICYmIHJpZ2h0VHlwZSA9PT0gJ251bWJlcicpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb246IHtcblx0XHRcdC8vIEhhbmRsZSBwcm9wZXJ0eSBhY2Nlc3MgbGlrZSBkYXRhLnZhbHVlLCBkYXRhLmlkXG5cdFx0XHRpZiAoZGF0YVR5cGVNYXApIHtcblx0XHRcdFx0Y29uc3QgYWNjZXNzQ2hhaW4gPSB0aGlzLmdldFByb3BlcnR5QWNjZXNzQ2hhaW4oaW5pdGlhbGl6ZXIpO1xuXHRcdFx0XHRpZiAoYWNjZXNzQ2hhaW4pIHtcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gZGF0YVR5cGVNYXAuZ2V0KGFjY2Vzc0NoYWluKTtcblx0XHRcdFx0XHRpZiAodHlwZSkge1xuXHRcdFx0XHRcdFx0cmV0dXJuIHR5cGU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBIYW5kbGUgdGhpcy5tYXAuc2l6ZSBwYXR0ZXJuIChNYXAuc2l6ZSByZXR1cm5zIG51bWJlcilcblx0XHRcdGNvbnN0IHByb3BBY2Nlc3MgPSBpbml0aWFsaXplciBhcyB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ocHJvcEFjY2Vzcy5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBvdXRlclByb3AgPSBwcm9wQWNjZXNzLmV4cHJlc3Npb247XG5cdFx0XHRcdC8vIENoZWNrIGZvciB0aGlzLm1hcCBwYXR0ZXJuXG5cdFx0XHRcdGxldCBpbm5lck5hbWUgPSAnJztcblx0XHRcdFx0aWYgKG91dGVyUHJvcC5leHByZXNzaW9uLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdFx0XHRpbm5lck5hbWUgPSAndGhpcyc7XG5cdFx0XHRcdH0gZWxzZSBpZiAodHMuaXNJZGVudGlmaWVyKG91dGVyUHJvcC5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdGlubmVyTmFtZSA9IG91dGVyUHJvcC5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgbWFwUHJvcCA9IG91dGVyUHJvcC5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IGZpbmFsUHJvcCA9IHByb3BBY2Nlc3MubmFtZS50ZXh0O1xuXHRcdFx0XHQvLyB0aGlzLm1hcC5zaXplIC0+IG51bWJlclxuXHRcdFx0XHRpZiAoaW5uZXJOYW1lID09PSAndGhpcycgJiYgbWFwUHJvcCA9PT0gJ21hcCcgJiYgZmluYWxQcm9wID09PSAnc2l6ZScpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5JZGVudGlmaWVyOiB7XG5cdFx0XHQvLyBIYW5kbGUgaWRlbnRpZmllciByZWZlcmVuY2VzIGlmIGluIGRhdGFUeXBlTWFwXG5cdFx0XHRpZiAoZGF0YVR5cGVNYXApIHtcblx0XHRcdFx0Y29uc3QgbmFtZSA9IChpbml0aWFsaXplciBhcyB0cy5JZGVudGlmaWVyKS50ZXh0O1xuXHRcdFx0XHRjb25zdCB0eXBlID0gZGF0YVR5cGVNYXAuZ2V0KG5hbWUpO1xuXHRcdFx0XHRpZiAodHlwZSkge1xuXHRcdFx0XHRcdHJldHVybiB0eXBlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuRWxlbWVudEFjY2Vzc0V4cHJlc3Npb246IHtcblx0XHRcdC8vIEYyMjogdmFsdWUtbGV2ZWwgZWxlbWVudCBhY2Nlc3Mgb3ZlciBhIGNvbnN0LWFzc2VydGVkXG5cdFx0XHQvLyBsaXRlcmFsIGFycmF5IOKAlCBgKDxjb25zdD5b4oCmXSlbMF1gLCBgKFvigKZdIGFzIGNvbnN0KVsxXWAsIG9yXG5cdFx0XHQvLyBhIHRyYWNrZWQgbW9kdWxlIGNvbnN0IChgY29uc3QgeCA9IDxjb25zdD5b4oCmXWA7IGB4WzBdYCkg4oCUXG5cdFx0XHQvLyBpbmZlcnMgdGhlIGVsZW1lbnQncyBsaXRlcmFsIHR5cGUsIHRoZSB2YWx1ZS1sZXZlbCB0d2luIG9mXG5cdFx0XHQvLyB0aGUgdHlwZW9mLXBhdGggdW5pb24uIE5vbi1udW1lcmljIGluZGV4ZXMsIG5vbi1saXRlcmFsXG5cdFx0XHQvLyBlbGVtZW50cywgYW5kIGdlbmVyYWwgYXNzZXJ0aW9ucyBzdGF5IGB1bmtub3duYC5cblx0XHRcdGNvbnN0IGVsZW1lbnRBY2Nlc3MgPSBpbml0aWFsaXplciBhcyB0cy5FbGVtZW50QWNjZXNzRXhwcmVzc2lvbjtcblx0XHRcdGNvbnN0IGFyZ3VtZW50ID0gZWxlbWVudEFjY2Vzcy5hcmd1bWVudEV4cHJlc3Npb247XG5cdFx0XHRpZiAoIWFyZ3VtZW50IHx8ICF0cy5pc051bWVyaWNMaXRlcmFsKGFyZ3VtZW50KSkge1xuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgYXJyYXlMaXRlcmFsID0gdGhpcy5jb25zdEFycmF5TGl0ZXJhbE9mKGVsZW1lbnRBY2Nlc3MuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoIWFycmF5TGl0ZXJhbCkge1xuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZWxlbWVudCA9IGFycmF5TGl0ZXJhbC5lbGVtZW50c1sgcGFyc2VJbnQoYXJndW1lbnQudGV4dCwgMTApIF07XG5cdFx0XHRpZiAoIWVsZW1lbnQgfHwgdHMuaXNTcHJlYWRFbGVtZW50KGVsZW1lbnQpKSB7XG5cdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBsaXRlcmFsID0gdGhpcy5saXRlcmFsVHlwZU9mRXhwcmVzc2lvbihlbGVtZW50KTtcblx0XHRcdGNvbnN0IGVsZW1lbnRSZXN1bHQgPSBsaXRlcmFsID8/ICd1bmtub3duJztcblx0XHRcdHJldHVybiBlbGVtZW50UmVzdWx0O1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQ2FsbEV4cHJlc3Npb246IHtcblx0XHRcdC8vIEhhbmRsZSBmdW5jdGlvbiBjYWxscyBsaWtlIERhdGUubm93KCksIHBhcnNlSW50KCksIGV0Yy5cblx0XHRcdGNvbnN0IGNhbGxFeHByID0gaW5pdGlhbGl6ZXIgYXMgdHMuQ2FsbEV4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbEV4cHIuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y29uc3QgbWV0aG9kTmFtZSA9IGNhbGxFeHByLmV4cHJlc3Npb24ubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBvYmpOYW1lID0gdHMuaXNJZGVudGlmaWVyKGNhbGxFeHByLmV4cHJlc3Npb24uZXhwcmVzc2lvbilcblx0XHRcdFx0XHQ/IGNhbGxFeHByLmV4cHJlc3Npb24uZXhwcmVzc2lvbi50ZXh0XG5cdFx0XHRcdFx0OiAnJztcblx0XHRcdFx0XHRcblx0XHRcdFx0Ly8gRGF0ZS5ub3coKSAtPiBudW1iZXJcblx0XHRcdFx0aWYgKG9iak5hbWUgPT09ICdEYXRlJyAmJiBtZXRob2ROYW1lID09PSAnbm93Jykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBTdHJpbmcgbWV0aG9kcyB0aGF0IHJldHVybiBzdHJpbmdcblx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICd0b1N0cmluZycgfHwgbWV0aG9kTmFtZSA9PT0gJ3ZhbHVlT2YnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIEhhbmRsZSBNYXAgcHJvcGVydHkgYWNjZXNzIG9uIGNsYXNzIGluc3RhbmNlcyAodGhpcy5tYXAuKilcblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxFeHByLmV4cHJlc3Npb24uZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRjb25zdCBvdXRlclByb3AgPSBjYWxsRXhwci5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0XHRcdFx0Ly8gSGFuZGxlIGJvdGggJ3RoaXMnIGtleXdvcmQgYW5kIGlkZW50aWZpZXIgcGF0dGVybnNcblx0XHRcdFx0XHRsZXQgaW5uZXJOYW1lID0gJyc7XG5cdFx0XHRcdFx0aWYgKG91dGVyUHJvcC5leHByZXNzaW9uLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdFx0XHRcdGlubmVyTmFtZSA9ICd0aGlzJztcblx0XHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihvdXRlclByb3AuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRcdGlubmVyTmFtZSA9IG91dGVyUHJvcC5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdGNvbnN0IG1hcFByb3AgPSBvdXRlclByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRcdC8vIHRoaXMubWFwLlgoKSBwYXR0ZXJuc1xuXHRcdFx0XHRcdGlmIChpbm5lck5hbWUgPT09ICd0aGlzJyAmJiBtYXBQcm9wID09PSAnbWFwJykge1xuXHRcdFx0XHRcdFx0Ly8gVHJ5IHRvIGdldCB0aGUgTWFwJ3MgdmFsdWUgdHlwZSBmcm9tIGNsYXNzIHByb3BlcnRpZXNcblx0XHRcdFx0XHRcdGxldCBtYXBWYWx1ZVR5cGUgPSAndW5rbm93bic7XG5cdFx0XHRcdFx0XHRpZiAoY2xhc3NQcm9wZXJ0eVR5cGVzKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnN0IG1hcFR5cGUgPSBjbGFzc1Byb3BlcnR5VHlwZXMuZ2V0KCdtYXAnKTtcblx0XHRcdFx0XHRcdFx0aWYgKG1hcFR5cGUgJiYgbWFwVHlwZS5zdGFydHNXaXRoKCdNYXA8JykpIHtcblx0XHRcdFx0XHRcdFx0XHQvLyBQYXJzZSBNYXA8SywgVj4gdG8gZ2V0IFZcblx0XHRcdFx0XHRcdFx0XHRjb25zdCBtYXRjaCA9IG1hcFR5cGUubWF0Y2goL01hcDxbXixdKyxcXHMqKC4rKT4kLyk7XG5cdFx0XHRcdFx0XHRcdFx0aWYgKG1hdGNoKSB7XG5cdFx0XHRcdFx0XHRcdFx0XHRbICwgbWFwVmFsdWVUeXBlIF0gPSBtYXRjaDtcblx0XHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnaGFzJykgcmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnc2V0JykgcmV0dXJuICd0aGlzJztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZ2V0JykgcmV0dXJuIG1hcFZhbHVlVHlwZTtcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZGVsZXRlJykgcmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnY2xlYXInKSByZXR1cm4gJ3ZvaWQnO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICd2YWx1ZXMnKSByZXR1cm4gYEl0ZXJhYmxlSXRlcmF0b3I8JHttYXBWYWx1ZVR5cGV9PmA7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2tleXMnKSByZXR1cm4gJ0l0ZXJhYmxlSXRlcmF0b3I8c3RyaW5nPic7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2VudHJpZXMnKSByZXR1cm4gYEl0ZXJhYmxlSXRlcmF0b3I8W3N0cmluZywgJHttYXBWYWx1ZVR5cGV9XT5gO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBEaXJlY3QgbWFwLlgoKSBjYWxsc1xuXHRcdFx0XHRpZiAob2JqTmFtZSA9PT0gJ21hcCcgfHwgb2JqTmFtZSA9PT0gJ29iaicpIHtcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2hhcycpIHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdzZXQnKSByZXR1cm4gJ3RoaXMnO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZ2V0JykgcmV0dXJuICd1bmtub3duJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2RlbGV0ZScpIHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdjbGVhcicpIHJldHVybiAndm9pZCc7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICd2YWx1ZXMnKSByZXR1cm4gJ0l0ZXJhYmxlSXRlcmF0b3I8dW5rbm93bj4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAna2V5cycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjxzdHJpbmc+Jztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2VudHJpZXMnKSByZXR1cm4gJ0l0ZXJhYmxlSXRlcmF0b3I8W3N0cmluZywgdW5rbm93bl0+Jztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gcGFyc2VJbnQsIHBhcnNlRmxvYXQgLT4gbnVtYmVyXG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGNhbGxFeHByLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IGZuTmFtZSA9IGNhbGxFeHByLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdFx0aWYgKGZuTmFtZSA9PT0gJ3BhcnNlSW50JyB8fCBmbk5hbWUgPT09ICdwYXJzZUZsb2F0Jykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoZm5OYW1lID09PSAnU3RyaW5nJykge1xuXHRcdFx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoZm5OYW1lID09PSAnTnVtYmVyJykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoZm5OYW1lID09PSAnQm9vbGVhbicpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVGVtcGxhdGVFeHByZXNzaW9uOlxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Ob1N1YnN0aXR1dGlvblRlbXBsYXRlTGl0ZXJhbDoge1xuXHRcdFx0Ly8gVGVtcGxhdGUgbGl0ZXJhbHMgbGlrZSBgJHtiYXNlVmFsdWV9LSR7ZXh0cmF9YCBhbHdheXMgcHJvZHVjZSBzdHJpbmdzXG5cdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0fVxuXHRcdGRlZmF1bHQ6XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIENvbGxlY3QgdXNhZ2UgaW5mb3JtYXRpb24gZm9yIHR5cGUgcmVmZXJlbmNlc1xuXHRcdFx0Ki9cblx0cHJpdmF0ZSBjb2xsZWN0VXNhZ2UgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHQvLyBDaGVjayBmb3IgbmV3IFR5cGUoKSBpbnN0YW50aWF0aW9uXG5cdFx0aWYgKHRzLmlzTmV3RXhwcmVzc2lvbihub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdGxldCB0eXBlTmFtZTogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0dHlwZU5hbWUgPSB0aGlzLnJlc29sdmVUeXBlUGF0aChub2RlLmV4cHJlc3Npb24pO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0dHlwZU5hbWUgPSB0aGlzLmdldFR5cGVOYW1lRnJvbUV4cHJlc3Npb24obm9kZS5leHByZXNzaW9uKTtcblx0XHRcdH1cblx0XHRcdGlmICh0eXBlTmFtZSkge1xuXHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdCk7XG5cdFx0XHRcdHRoaXMuYWRkVXNhZ2UodHlwZU5hbWUsIHtcblx0XHRcdFx0XHRsb2NhdGlvbiAgICAgICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRraW5kICAgICAgICAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0Y29kZSAgICAgICAgICAgIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0Ly8gQ29uc3RydWN0b3IgZXhwcmVzc2lvbiB0ZXh0ICgnVGhpbmcnLCAndXNlci5BZG1pbkVudGl0eScsXG5cdFx0XHRcdFx0Ly8gYSBsb29rdXAgYWxpYXMpIOKAlCBDcmVhdGlvbkFuY2hvci5jb25zdHJ1Y3RvclRleHQgKFBoYXNlIDMpXG5cdFx0XHRcdFx0Y29uc3RydWN0b3JUZXh0IDogbm9kZS5leHByZXNzaW9uLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0fSk7XG5cdFx0XHRcdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnQgZnJvbSBuZXcgVHlwZSgpIGZvciBmbG93IGFuYWx5c2lzXG5cdFx0XHRcdHRoaXMudHJhY2tOZXdBc3NpZ25tZW50KG5vZGUsIHR5cGVOYW1lKTtcblx0XHRcdFx0Ly8gQWxzbyByZWNvcmQgYXMgZmxvdyBldmVudFxuXHRcdFx0XHR0aGlzLmFkZEZsb3codHlwZU5hbWUsIHtcblx0XHRcdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdGtpbmQgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0XHRcdGNvZGUgICAgIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0Y29udGV4dCAgOiAnbmV3IGV4cHJlc3Npb24nLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cdFxuXHRcdC8vIENoZWNrIGZvciBwcm9wZXJ0eSBhY2Nlc3Mgb24gaW5zdGFuY2VzICh1c2VyLkFkbWluVHlwZSlcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdGNvbnN0IHByb3BOYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0XHQvLyBpbnN0YW5jZS5jbG9uZSDigJQgdGhlIFBST1BFUlRZIGZvcm0gKGNvcmUgdHlwZXMgaXRcblx0XHRcdC8vIGByZWFkb25seSBjbG9uZTogdGhpc2ApOiB0aGUgcmVzdWx0IHZhcmlhYmxlIGJpbmRzIHRvIHRoZVxuXHRcdFx0Ly8gc291cmNlIGluc3RhbmNlJ3MgdHlwZSwgc2FtZSBhcyB0aGUgZm9yaygpL2Nsb25lKCkgY2FsbFxuXHRcdFx0Ly8gZm9ybXMgKGF3YWl0LXRyYW5zcGFyZW50KS4gVGhlIGNhbGwgZm9ybSdzIHJlY29yZGluZyBoYXBwZW5zXG5cdFx0XHQvLyBpbiB0aGUgQ2FsbEV4cHJlc3Npb24gYnJhbmNoOyB0aGUgcHJvcGVydHkgYnJhbmNoIHNraXBzIGl0XG5cdFx0XHQvLyB0byBhdm9pZCBhIGR1cGxpY2F0ZSBlbnRyeSBhdCB0aGUgc2FtZSBzaXRlXG5cdFx0XHRpZiAocHJvcE5hbWUgPT09ICdjbG9uZScgJiYgdHMuaXNJZGVudGlmaWVyKG5vZGUuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y29uc3QgY2xvbmVkUGF0aCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KG5vZGUuZXhwcmVzc2lvbi50ZXh0KTtcblx0XHRcdFx0Y29uc3QgaXNDYWxsRm9ybSA9IHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZS5wYXJlbnQpICYmIG5vZGUucGFyZW50LmV4cHJlc3Npb24gPT09IG5vZGU7XG5cdFx0XHRcdGlmIChjbG9uZWRQYXRoKSB7XG5cdFx0XHRcdFx0aWYgKCFpc0NhbGxGb3JtKSB7XG5cdFx0XHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0XHRcdCk7XG5cdFx0XHRcdFx0XHR0aGlzLmFkZFVzYWdlKGNsb25lZFBhdGgsIHtcblx0XHRcdFx0XHRcdFx0bG9jYXRpb24gICAgICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0XHRcdGtpbmQgICAgICAgICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRcdFx0Y29kZSAgICAgICAgICAgIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0XHRcdGNvbnN0cnVjdG9yVGV4dCA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdHRoaXMuYmluZFJlc3VsdFZhcmlhYmxlKG5vZGUsIGNsb25lZFBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBDaGVjayBpZiB0aGlzIGxvb2tzIGxpa2UgYSB0eXBlIGFjY2VzcyBwYXR0ZXJuXG5cdFx0XHRpZiAocHJvcE5hbWUgJiYgdGhpcy5pc0xpa2VseVR5cGVOYW1lKHByb3BOYW1lKSkge1xuXHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdCk7XG5cdFx0XHRcdFx0Ly8gVHJ5IHRvIHJlc29sdmUgZnVsbCBwYXRoXG5cdFx0XHRcdGNvbnN0IGZ1bGxQYXRoID0gdGhpcy5yZXNvbHZlVHlwZVBhdGgobm9kZSk7XG5cdFx0XHRcdGlmIChmdWxsUGF0aCkge1xuXHRcdFx0XHRcdHRoaXMuYWRkVXNhZ2UoZnVsbFBhdGgsIHtcblx0XHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0XHRraW5kICAgICA6ICdwcm9wZXJ0eUFjY2VzcycsXG5cdFx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcblx0XHQvLyBDaGVjayBmb3IgbG9va3VwKCdUeXBlTmFtZScpIG9yIGxvb2t1cChzb3VyY2UsICdUeXBlTmFtZScpIGNhbGxzXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRjb25zdCBmdW5jTmFtZSA9IHRoaXMuZ2V0RnVuY3Rpb25OYW1lKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoZnVuY05hbWUgPT09ICdsb29rdXAnICYmIG5vZGUuYXJndW1lbnRzLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0Y29uc3QgdHlwZVBhdGggPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKG5vZGUpO1xuXHRcdFx0XHRpZiAodHlwZVBhdGgpIHtcblx0XHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHRcdCk7XG5cdFx0XHRcdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRcdFx0XHR0aGlzLmFkZFVzYWdlKHR5cGVQYXRoLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0XHRcdGtpbmQgOiAnbG9va3VwJyxcblx0XHRcdFx0XHRcdGNvZGUgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50IGZyb20gbG9va3VwIGZvciBpbnN0YW50aWF0aW9uIHRyYWNraW5nXG5cdFx0XHRcdFx0dGhpcy50cmFja0xvb2t1cEFzc2lnbm1lbnQobm9kZSwgdHlwZVBhdGgpO1xuXHRcdFx0XHRcdC8vIFJlY29yZCBmb3IgdGhlIGhhcmQtZmFpbCBsYXcgZXZlbiB3aGVuIGFkZFVzYWdlIGRyb3BwZWRcblx0XHRcdFx0XHQvLyB0aGUgcGF0aCAodW5rbm93biBwYXRocyBhcmUgZXhhY3RseSB0aGUgZmFpbHVyZSBjbGFzcylcblx0XHRcdFx0XHR0aGlzLmxvb2t1cFJlZmVyZW5jZXMucHVzaCh7IHBhdGggOiB0eXBlUGF0aCwgbG9jYXRpb24gfSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblxuXHRcdFx0Ly8gQ2hhaW4tZm9ybSBjb25zdHJ1Y3Rpb246IGBuZXcgUiguLi4pLkEoLi4uKWAgLyB0aGUgYXdhaXRlZFxuXHRcdFx0Ly8gc2luZ2xlLWNoYWluIGBhd2FpdCBuZXcgUiguLi4pLkEoLi4uKS5CKC4uLilgIOKAlCB0aGUgY2FsbCBvblxuXHRcdFx0Ly8gdGhlIGZyZXNoIGluc3RhbmNlIGNvbnN0cnVjdHMgdGhlIGNoYWluIFRJUCAoYXdhaXQgaXNcblx0XHRcdC8vIHRyYW5zcGFyZW50OyB0aGUgTmV3RXhwcmVzc2lvbiBicmFuY2ggYWxyZWFkeSByZWNvcmRlZCB0aGVcblx0XHRcdC8vIGlubmVyIHJvb3QpLiBUaGUgcmVzdWx0IHZhcmlhYmxlIGJpbmRzIHRvIHRoZSB0aXAsIG5vdCB0aGVcblx0XHRcdC8vIHJvb3QgKHRyYWNrTmV3QXNzaWdubWVudCByZXNvbHZlcyB0aGUgc2FtZSB0aXApXG5cdFx0XHRjb25zdCBjaGFpblRpcCA9IHRoaXMucmVzb2x2ZUNoYWluVGlwVHlwZVBhdGgobm9kZSk7XG5cdFx0XHRpZiAoY2hhaW5UaXApIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZShub2RlLCBjaGFpblRpcCwgc291cmNlRmlsZSk7XG5cdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0dGhpcy5hZGRGbG93KGNoYWluVGlwLCB7XG5cdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRraW5kICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdGNvbnRleHQgIDogJ2NoYWluZWQgY29uc3RydWN0aW9uJyxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cblx0XHRcdC8vIG1uZW1vbmljYSBjYWxsL2FwcGx5KGVudGl0eSwgQ3RvciwgLi4uKSAvIGJpbmQoZW50aXR5LCBDdG9yKSDigJRcblx0XHRcdC8vIHR5cGVkIGNvbnN0cnVjdGlvbiB3aXRob3V0IGBuZXdgOiB0aGUgQ3RvciBhcmd1bWVudCAoYXJnIDEpIGlzXG5cdFx0XHQvLyB0aGUgY29uc3RydWN0ZWQgdHlwZS4gSW1wb3J0LWF3YXJlOiBvbmx5IGlkZW50aWZpZXJzIGFjdHVhbGx5XG5cdFx0XHQvLyBpbXBvcnRlZCBmcm9tICdtbmVtb25pY2EnIChvciBtZW1iZXJzIG9mIGEgdHJhY2tlZFxuXHRcdFx0Ly8gbW9kdWxlLW9iamVjdCBhbGlhcykgbWF0Y2gg4oCUIHVzZXJsYW5kIGNhbGwvYXBwbHkvYmluZCBuZXZlclxuXHRcdFx0Ly8gZG8uIGNhbGwvYXBwbHkgcmVjb3JkIHRoZSBjb25zdHJ1Y3Rpb247IGJpbmQoKSBjb25zdHJ1Y3RzXG5cdFx0XHQvLyBub3RoaW5nIOKAlCBpdCBvbmx5IGJpbmRzIHRoZSByZXN1bHQgdmFyaWFibGUgdG8gdGhlIEN0b3Inc1xuXHRcdFx0Ly8gdHlwZSAocnVudGltZSBJbnN0YW5jZVJlc3VsdDxNZXJnZTxFLFQ+PiBhcHByb3hpbWF0ZWQgYnkgVFxuXHRcdFx0Ly8gd2l0aGluIHRoZSBvdXRwdXQgY29udHJhY3QpXG5cdFx0XHRjb25zdCBjb25zdHJ1Y3Rpb25QYXRoID0gdGhpcy5yZXNvbHZlQ29uc3RydWN0aW9uRm5UeXBlUGF0aChub2RlKTtcblx0XHRcdGlmIChjb25zdHJ1Y3Rpb25QYXRoKSB7XG5cdFx0XHRcdGNvbnN0IGlzQmluZEZvcm0gPSB0aGlzLmlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4obm9kZS5leHByZXNzaW9uLCAnYmluZCcpO1xuXHRcdFx0XHRpZiAoIWlzQmluZEZvcm0pIHtcblx0XHRcdFx0XHRjb25zdCBjdG9yQXJnVGV4dCA9IG5vZGUuYXJndW1lbnRzWyAxIF0/LmdldFRleHQoc291cmNlRmlsZSk7XG5cdFx0XHRcdFx0dGhpcy5yZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZShub2RlLCBjb25zdHJ1Y3Rpb25QYXRoLCBzb3VyY2VGaWxlLCBjdG9yQXJnVGV4dCk7XG5cdFx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0XHQpO1xuXHRcdFx0XHRcdHRoaXMuYWRkRmxvdyhjb25zdHJ1Y3Rpb25QYXRoLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdFx0a2luZCAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0XHRjb2RlICAgICA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdFx0Y29udGV4dCAgOiAnY2FsbC9hcHBseSBjb25zdHJ1Y3Rpb24nLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHRoaXMuYmluZFJlc3VsdFZhcmlhYmxlKG5vZGUsIGNvbnN0cnVjdGlvblBhdGgpO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBpbnN0YW5jZS5mb3JrKCkvY2xvbmUoKSDigJQgcnVudGltZSByZS1ydW5zIGNvbnN0cnVjdGlvbiAoaG9va3Ncblx0XHRcdC8vIGZpcmUsIGEgZGlzdGluY3QgaW5zdGFuY2Ugb24gYSBkaXN0aW5jdCBsaW5lKSwgc28gYW5cblx0XHRcdC8vIGBpbnN0YW50aWF0aW9uYCB1c2FnZSByZWNvcmRzIHRoZSBzaXRlIElOIEFERElUSU9OIHRvIHRoZVxuXHRcdFx0Ly8gcmVzdWx0LXZhciBiaW5kaW5nIGFuZCB0aGUgZ2VuZXJpYyBtZXRob2RDYWxsIGZsb3cgKHRoZSBlbnRyeVxuXHRcdFx0Ly8gaXMgYnl0ZS1pbmRpc3Rpbmd1aXNoYWJsZSBmcm9tIGBuZXdgIHVudGlsIHRoZSBkZWZlcnJlZFxuXHRcdFx0Ly8gbWVjaGFuaXNtLWtpbmQgcmV2aXNpb24g4oCUIHRoZSBvd25lcidzIGV4cGxpY2l0IGNhbGwpLiBGcmVlXG5cdFx0XHQvLyB1dGlscy5tZXJnZShhLCBiLCAuLi4pIC8gdXRpbHMuZm9yayhpbnN0YW5jZSkoLi4uKSBhcmVcblx0XHRcdC8vIGNvbnN0cnVjdGlvbiBvZiBhJ3MgdHlwZSB0b28gKG1lcmdlID0gZm9yayhhKSBvdmVyIGInc1xuXHRcdFx0Ly8gY29udGV4dCk7IHRoZSByZXN1bHQgYmluZGluZyBrZWVwcyB0aGUgZG9jdW1lbnRlZCBhcmctMFxuXHRcdFx0Ly8gYXBwcm94aW1hdGlvblxuXHRcdFx0Y29uc3QgZm9ya0xpa2VQYXRoID0gdGhpcy5yZXNvbHZlRm9ya0xpa2VUeXBlUGF0aChub2RlKTtcblx0XHRcdGlmIChmb3JrTGlrZVBhdGgpIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRDb25zdHJ1Y3Rpb25Vc2FnZShub2RlLCBmb3JrTGlrZVBhdGgsIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShub2RlLCBmb3JrTGlrZVBhdGgpO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgdXRpbHNQYXRoID0gdGhpcy5yZXNvbHZlVXRpbHNGblR5cGVQYXRoKG5vZGUpO1xuXHRcdFx0aWYgKHV0aWxzUGF0aCkge1xuXHRcdFx0XHR0aGlzLnJlY29yZENvbnN0cnVjdGlvblVzYWdlKG5vZGUsIHV0aWxzUGF0aCwgc291cmNlRmlsZSk7XG5cdFx0XHRcdHRoaXMuYmluZFJlc3VsdFZhcmlhYmxlKG5vZGUsIHV0aWxzUGF0aCk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cdFxuXHQvKipcblx0XHRcdCogR2V0IGZ1bmN0aW9uIG5hbWUgZnJvbSBleHByZXNzaW9uIChpZGVudGlmaWVyIG9yIHByb3BlcnR5IGFjY2Vzcylcblx0XHRcdCovXG5cdHByaXZhdGUgZ2V0RnVuY3Rpb25OYW1lIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci50ZXh0O1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIEFkZCBhIHVzYWdlIHRvIHRoZSBjb2xsZWN0aW9uXG5cdFx0XHQqL1xuXHRwcml2YXRlIGFkZFVzYWdlICh0eXBlUGF0aDogc3RyaW5nLCB1c2FnZTogVXNhZ2VJbmZvKTogdm9pZCB7XG5cdFx0Ly8gT25seSB0cmFjayB1c2FnZXMgb2YgbW5lbW9uaWNhLWRlZmluZWQgdHlwZXNcblx0XHRpZiAoIXRoaXMuZGVmaW5pdGlvbnMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAoIXRoaXMudXNhZ2VzLmhhcyh0eXBlUGF0aCkpIHtcblx0XHRcdHRoaXMudXNhZ2VzLnNldCh0eXBlUGF0aCwgW10pO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBkdXBsaWNhdGVzIGJhc2VkIG9uIGxvY2F0aW9uLCBjb2RlLCBhbmQga2luZFxuXHRcdGNvbnN0IGV4aXN0aW5nVXNhZ2VzID0gdGhpcy51c2FnZXMuZ2V0KHR5cGVQYXRoKSE7XG5cdFx0Y29uc3QgaXNEdXBsaWNhdGUgPSBleGlzdGluZ1VzYWdlcy5zb21lKGV4aXN0aW5nID0+XG5cdFx0XHRleGlzdGluZy5sb2NhdGlvbiA9PT0gdXNhZ2UubG9jYXRpb24gJiZcblx0XHRcdFx0ZXhpc3RpbmcuY29kZSA9PT0gdXNhZ2UuY29kZSAmJlxuXHRcdFx0XHRleGlzdGluZy5raW5kID09PSB1c2FnZS5raW5kKTtcblxuXHRcdGlmICghaXNEdXBsaWNhdGUpIHtcblx0XHRcdGV4aXN0aW5nVXNhZ2VzLnB1c2godXNhZ2UpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IEVEUyAoRXhlY3V0aW9uIERhdGEgU3RvcmFnZSkgdXNhZ2UgaW5mb3JtYXRpb25cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEVEUyAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSB8fCAhbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgZnVuY05hbWUgPSB0aGlzLmdldEZ1bmN0aW9uTmFtZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghZnVuY05hbWUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cdFx0Ly8gRW5jbG9zaW5nIG1uZW1vbmljYSB0eXBlIHBhdGgg4oCUIHdyYXAgYXJncyBhcmUgdXN1YWxseSBsb2NhbFxuXHRcdC8vIGZ1bmN0aW9ucywgc28gdGhlIG93bmluZyBkZWZpbmUoKS9sYXp5KCkgaGFuZGxlciBvciBkZWNvcmF0ZWRcblx0XHQvLyBjbGFzcyBpcyB3aGF0IGVkcy5qc29uIGNvbnN1bWVycyAoR3JhcGhCdWlsZGVyKSBjYW4gam9pbiBvbi5cblx0XHRjb25zdCBzY29wZSA9IHRoaXMucmVzb2x2ZUVEU1Njb3BlKG5vZGUpO1xuXG5cdFx0Ly8gd3JhcChmbiksIHdyYXBDb25zdHJ1Y3RvckFyZyhmbiwgcGFyZW50KSwgdXBncmFkZUNvbnN0cnVjdG9yQXJnKGFyZywgaW5zdCksIHdyYXBJbnN0YW5jZU1ldGhvZHMob2JqKVxuXHRcdGlmIChcblx0XHRcdGZ1bmNOYW1lID09PSAnd3JhcCcgfHxcblx0XHRcdGZ1bmNOYW1lID09PSAnd3JhcENvbnN0cnVjdG9yQXJnJyB8fFxuXHRcdFx0ZnVuY05hbWUgPT09ICd1cGdyYWRlQ29uc3RydWN0b3JBcmcnIHx8XG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3dyYXBJbnN0YW5jZU1ldGhvZHMnXG5cdFx0KSB7XG5cdFx0XHRjb25zdCB0YXJnZXRUeXBlID0gdGhpcy5yZXNvbHZlRURTQXJndW1lbnRUeXBlKG5vZGUuYXJndW1lbnRzWyAwIF0pO1xuXHRcdFx0Ly8gZGl2ZSdzIHdyYXAtZmFtaWx5IHNpZ25hdHVyZXMgKGRpdmUvc3JjL2luZGV4LnRzKTpcblx0XHRcdC8vICAgd3JhcChmbiwgbGFiZWw/KSB8IHdyYXAoZm4sIGNvbnRleHQ/LCBsYWJlbD8pXG5cdFx0XHQvLyAgIHdyYXBDb25zdHJ1Y3RvckFyZyhmbiwgY29udGV4dClcblx0XHRcdC8vICAgdXBncmFkZUNvbnN0cnVjdG9yQXJnKGFyZywgaW5zdGFuY2UpXG5cdFx0XHQvLyAgIHdyYXBJbnN0YW5jZU1ldGhvZHMoaW5zdGFuY2UpXG5cdFx0XHQvLyDigKZzbyB0aGUgaW5zdGFuY2UvY29udGV4dCBhcmcgc2l0cyBhdCBhcmdzWzFdIChhcmdzWzBdIGZvclxuXHRcdFx0Ly8gd3JhcEluc3RhbmNlTWV0aG9kcykgYW5kIGEgc3RyaW5nIGxpdGVyYWwgaW4gYXJnc1sxLi4yXSBpcyB0aGUgbGFiZWxcblx0XHRcdGNvbnN0IGluc3RhbmNlQXJnTm9kZSA9IGZ1bmNOYW1lID09PSAnd3JhcEluc3RhbmNlTWV0aG9kcydcblx0XHRcdFx0PyBub2RlLmFyZ3VtZW50c1sgMCBdXG5cdFx0XHRcdDogbm9kZS5hcmd1bWVudHNbIDEgXTtcblx0XHRcdC8vIEZpcmUtYW5kLWZvcmdldCB3cmFwcGVycyAod2lyZS11cCBoZWxwZXJzLCByZWdpc3RyYXRpb25cblx0XHRcdC8vIGZ1bmN0aW9ucykgc2l0IG91dHNpZGUgYW55IGRlZmluZSgpL2xhenkoKSBoYW5kbGVyLCBzbyB0aGVcblx0XHRcdC8vIGxleGljYWwgc2NvcGUgaXMgYWJzZW50IOKAlCBhdHRyaWJ1dGUgdGhyb3VnaCB0aGUgaW5zdGFuY2UvY29udGV4dFxuXHRcdFx0Ly8gYXJndW1lbnQgaW5zdGVhZDogYSB0cmFja2VkIGFzc2lnbm1lbnQsIGVsc2UgdGhlIGVuY2xvc2luZ1xuXHRcdFx0Ly8gZnVuY3Rpb24ncyBwYXJhbWV0ZXIgYW5ub3RhdGlvbiByZXNvbHZlZCB0aHJvdWdoIHRoZSBncmFwaCBsYXdcblx0XHRcdGNvbnN0IGluc3RhbmNlVHlwZVBhdGggPSBpbnN0YW5jZUFyZ05vZGVcblx0XHRcdFx0PyB0aGlzLnJlc29sdmVXcmFwSW5zdGFuY2VUeXBlUGF0aChpbnN0YW5jZUFyZ05vZGUpXG5cdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0Y29uc3QgZWZmZWN0aXZlU2NvcGUgPSBzY29wZSA/PyBpbnN0YW5jZVR5cGVQYXRoO1xuXHRcdFx0Y29uc3QgaW5mbzogRURTSW5mbyA9IHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAnd3JhcCcsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHRhcmdldFR5cGUgOiB0YXJnZXRUeXBlIHx8IHVuZGVmaW5lZCxcblx0XHRcdFx0c2NvcGUgICAgICA6IGVmZmVjdGl2ZVNjb3BlLFxuXHRcdFx0XHRmbiAgICAgICAgIDogZnVuY05hbWUsXG5cdFx0XHR9O1xuXHRcdFx0aWYgKGluc3RhbmNlQXJnTm9kZSAmJiB0cy5pc0lkZW50aWZpZXIoaW5zdGFuY2VBcmdOb2RlKSkge1xuXHRcdFx0XHRpbmZvLmluc3RhbmNlQXJnID0gaW5zdGFuY2VBcmdOb2RlLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGV4dHJhQXJnIG9mIFsgbm9kZS5hcmd1bWVudHNbIDEgXSwgbm9kZS5hcmd1bWVudHNbIDIgXSBdKSB7XG5cdFx0XHRcdGlmIChleHRyYUFyZyAmJiB0cy5pc1N0cmluZ0xpdGVyYWwoZXh0cmFBcmcpKSB7XG5cdFx0XHRcdFx0aW5mby5sYWJlbCA9IGV4dHJhQXJnLnRleHQ7XG5cdFx0XHRcdFx0YnJlYWs7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIEEgd3JhcCgpIGNhbGwgbmVzdGVkIGluc2lkZSBhbm90aGVyIHdyYXBwZWQgYm9keSBjYXJyaWVzIHRoZVxuXHRcdFx0Ly8gbGluayB0byB0aGUgc2l0ZSB3aG9zZSBydW50aW1lIHdyYXBwaW5nIGNhdXNlZCBpdCDigJQgYW5kLCB3aGVuXG5cdFx0XHQvLyB0aGUgbmVzdGVkIHNpdGUgaGFzIG5vIHNjb3BlIG9mIGl0cyBvd24sIHRoZSBjYXVzaW5nIHNpdGUnc1xuXHRcdFx0Ly8gc2NvcGUgYXR0cmlidXRpb24gdHJhdmVscyB3aXRoIHRoZSBsaW5rXG5cdFx0XHRjb25zdCB2aWFMaW5rID0gdGhpcy5uZXN0ZWRXcmFwVmlhLmdldChub2RlKTtcblx0XHRcdGlmICh2aWFMaW5rKSB7XG5cdFx0XHRcdGluZm8udmlhID0gdmlhTGluay52aWE7XG5cdFx0XHRcdGlmIChpbmZvLnNjb3BlID09PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0XHRpbmZvLnNjb3BlID0gdmlhTGluay5zY29wZTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gZGl2ZSB3cmFwcyByZXR1cm5lZCBmdW5jdGlvbnMgdG9vLCBhbmQgYW55IG1uZW1vbmljYSBpbnN0YW5jZVxuXHRcdFx0Ly8gY3JlYXRlZCBpbnNpZGUgdGhlIHdyYXBwZWQgYm9keSBpcyBhIGd1YXJhbnRlZWQgcGF0aCBoaXQg4oCUXG5cdFx0XHQvLyBib3RoIGFyZSBjYWxjdWxhYmxlIEFvVCwgc28gcmVjb3JkIHRoZW1cblx0XHRcdGNvbnN0IHdyYXBwZWQgPSB0aGlzLnJlc29sdmVGdW5jdGlvbkFyZ3VtZW50KG5vZGUuYXJndW1lbnRzWyAwIF0sIHNvdXJjZUZpbGUpO1xuXHRcdFx0aWYgKHdyYXBwZWQpIHtcblx0XHRcdFx0Ly8gVGhlIHdyYXBwZWQgY2FsbGJhY2sgZ2V0cyBpdHMgb3duIHNjb3BlIGluIHNjb3Blcy5qc29uIGtleWVkIGJ5XG5cdFx0XHRcdC8vIGl0cyBzdGFydCBwb3NpdGlvbiDigJQgcmVjb3JkIHRoYXQgc2NvcGVJZCBzbyBncmFwaCBjb25zdW1lcnMgY2FuXG5cdFx0XHRcdC8vIGpvaW4gYSB3cmFwIGVudHJ5IHRvIHRoZSBjYWxsYmFjaydzIGNyZWF0aW9uIG5vZGVcblx0XHRcdFx0Y29uc3QgY2FsbGJhY2tQb3MgPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdHdyYXBwZWQuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0Y29uc3QgY2FsbGJhY2tGaWxlID0gbm9kZVBhdGgucmVzb2x2ZShzb3VyY2VGaWxlLmZpbGVOYW1lKTtcblx0XHRcdFx0aW5mby5jYWxsYmFja1Njb3BlSWQgPSBgJHtjYWxsYmFja0ZpbGV9OiR7Y2FsbGJhY2tQb3MubGluZSArIDF9OiR7Y2FsbGJhY2tQb3MuY2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0XHRjb25zdCBjcmVhdGVzVHlwZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHRcdFx0dGhpcy5hbmFseXplV3JhcHBlZEJvZHkod3JhcHBlZCwgbG9jYXRpb24sIHNvdXJjZUZpbGUsIDAsIG5ldyBTZXQoKSwgY3JlYXRlc1R5cGVzLCBlZmZlY3RpdmVTY29wZSk7XG5cdFx0XHRcdGlmIChjcmVhdGVzVHlwZXMuc2l6ZSA+IDApIHtcblx0XHRcdFx0XHRpbmZvLmNyZWF0ZXNUeXBlcyA9IEFycmF5LmZyb20oY3JlYXRlc1R5cGVzKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgc3RvcmVkID0gdGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCBlZmZlY3RpdmVTY29wZSB8fCAndW5rbm93bicsIGluZm8pO1xuXHRcdFx0dGhpcy53cmFwRW50cnlCeU5vZGUuc2V0KG5vZGUsIHN0b3JlZCk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gY3VycmVudCgpLCBnZXRFcnJvckluc3RhbmNlKGVyciksIGdldEZsb3codGFyZ2V0Pylcblx0XHRpZiAoZnVuY05hbWUgPT09ICdjdXJyZW50JyB8fCBmdW5jTmFtZSA9PT0gJ2dldEVycm9ySW5zdGFuY2UnIHx8IGZ1bmNOYW1lID09PSAnZ2V0RmxvdycpIHtcblx0XHRcdHRoaXMuYWRkRURTKHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCA6ICdjb250ZXh0Q29uc3VtZScsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHNjb3BlLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gYXR0YWNoSG9va3MoY29sbGVjdGlvbikg4oCUIGZyb20gQG1uZW1vbmljYS9vdGVsLCB3aXJlcyBhXG5cdFx0Ly8gVHlwZXNDb2xsZWN0aW9uIHRvIGRpdmUncyBsaWZlY3ljbGUgdHJhY2luZ1xuXHRcdGlmIChmdW5jTmFtZSA9PT0gJ2F0dGFjaEhvb2tzJyAmJiBub2RlLmFyZ3VtZW50cy5sZW5ndGggPiAwKSB7XG5cdFx0XHRjb25zdCBbIGFyZyBdID0gbm9kZS5hcmd1bWVudHM7XG5cdFx0XHRpZiAodHMuaXNBcnJheUxpdGVyYWxFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGFyZy5lbGVtZW50cykge1xuXHRcdFx0XHRcdGNvbnN0IHRhcmdldFR5cGUgPSB0aGlzLnJlc29sdmVFRFNBcmd1bWVudFR5cGUoZWxlbWVudCk7XG5cdFx0XHRcdFx0dGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCBzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRcdFx0a2luZCAgICAgICA6ICdob29rQXR0YWNoJyxcblx0XHRcdFx0XHRcdGNvZGUsXG5cdFx0XHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdFx0XHRzY29wZSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgdGFyZ2V0VHlwZSA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShhcmcpO1xuXHRcdFx0XHR0aGlzLmFkZEVEUyh0YXJnZXRUeXBlIHx8IHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRcdGtpbmQgICAgICAgOiAnaG9va0F0dGFjaCcsXG5cdFx0XHRcdFx0Y29kZSxcblx0XHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdFx0c2NvcGUsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHR5cGUgZnJvbSBFRFMgY2FsbCBhcmd1bWVudCAoYmVzdCBlZmZvcnQpXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVFRFNBcmd1bWVudFR5cGUgKGFyZzogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCFhcmcpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gSWRlbnRpZmllcjogdmFyaWFibGUgbmFtZVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0Y29uc3QgbWFwcGVkID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQoYXJnLnRleHQpO1xuXHRcdFx0aWYgKG1hcHBlZCkge1xuXHRcdFx0XHRyZXR1cm4gbWFwcGVkO1xuXHRcdFx0fVxuXHRcdFx0Ly8gTWF5YmUgaXQncyBhIHR5cGUgbmFtZSBkaXJlY3RseVxuXHRcdFx0aWYgKHRoaXMuZGVmaW5pdGlvbnMuaGFzKGFyZy50ZXh0KSkge1xuXHRcdFx0XHRyZXR1cm4gYXJnLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBsZXQtaW4tdHJ5OiBhIGxldC92YXIgYmluZGluZyBkZWNsYXJlZCB3aXRob3V0IGEgdHJhY2tlZFxuXHRcdFx0Ly8gaW5pdGlhbGl6ZXIgYW5kIGFzc2lnbmVkIGxhdGVyIGluIHRoZSBTQU1FIHNjb3BlICh0aGVcblx0XHRcdC8vIGZpcmUtYW5kLWZvcmdldCBjYXRjaC1ndWFyZCBwYXR0ZXJuOiBgbGV0IGZuOyB0cnkgeyBmbiA9XG5cdFx0XHQvLyDigKYgfSBjYXRjaCB7IHJldHVybiB9IHdyYXAoZm4sIOKApilgKSDigJQgZm9sbG93IHRoZSBmaXJzdFxuXHRcdFx0Ly8gc3RhdGljYWxseS12aXNpYmxlIGluLXNjb3BlIGFzc2lnbm1lbnQuIE5vIGZsb3cgYW5hbHlzaXM6XG5cdFx0XHQvLyBmdW5jdGlvbi9jbGFzcyBib3VuZGFyaWVzIGFyZSBub3QgY3Jvc3NlZCwgYVxuXHRcdFx0Ly8gbmV2ZXItYXNzaWduZWQgYmluZGluZyBzdGF5cyB1bmtub3duIChGMjAgZGlzY2lwbGluZSkuXG5cdFx0XHQvLyBXaGVuIHRoZSBhc3NpZ25tZW50IHJlc29sdmVzLCBpdHMgZXZpZGVuY2UgV0lOUyBvdmVyIGFueVxuXHRcdFx0Ly8gZGVjbGFyYXRpb24gYW5ub3RhdGlvbiAodGhlIGNvbnN0cnVjdGVkIHN1YnR5cGUgaXMgdGhlIG1vcmVcblx0XHRcdC8vIHNwZWNpZmljIHRydXRoKTsgYW4gdW5yZXNvbHZhYmxlIFJIUyAoYSB1c2VybGFuZCBjYWxsLCBzYXkpXG5cdFx0XHQvLyBmYWxscyB0aHJvdWdoIHRvIHRoZSBhbm5vdGF0aW9uIGNsYWltIGJlbG93LlxuXHRcdFx0Y29uc3QgYXNzaWduZWQgPSB0aGlzLmZvbGxvd1Njb3BlQXNzaWdubWVudChhcmcudGV4dCwgYXJnKTtcblx0XHRcdGlmIChhc3NpZ25lZCkge1xuXHRcdFx0XHRjb25zdCByZXNvbHZlZCA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShhc3NpZ25lZCk7XG5cdFx0XHRcdGlmIChyZXNvbHZlZCkge1xuXHRcdFx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gQW5ub3RhdGlvbiBmYWxsYmFjayDigJQgdGhlIEYyMCBkaXNjaXBsaW5lIG9uZSBhcmd1bWVudCBvdmVyOlxuXHRcdFx0Ly8gYW4gZXhwbGljaXQgZGVjbGFyYXRpb24gb3IgcGFyYW1ldGVyIGFubm90YXRpb24gaXMgYSB1c2VyXG5cdFx0XHQvLyBjbGFpbSB3cml0dGVuIGluIHRoZSBBU1QsIG5vdCBmbG93IGFuYWx5c2lzLiBQYXJhbWV0ZXJcblx0XHRcdC8vIGZpcnN0OiBpdCBzaGFkb3dzIGFuIG91dGVyIGxldCwgc2FtZSBhcyB0aGUgY29udGV4dC1hcmcgcGF0aC5cblx0XHRcdGNvbnN0IGFubm90YXRlZCA9IHRoaXMucmVzb2x2ZVBhcmFtZXRlckFubm90YXRpb25UeXBlUGF0aChhcmcudGV4dCwgYXJnKSA/P1xuXHRcdFx0XHR0aGlzLnJlc29sdmVWYXJpYWJsZUFubm90YXRpb25UeXBlUGF0aChhcmcudGV4dCwgYXJnKTtcblx0XHRcdHJldHVybiBhbm5vdGF0ZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gTmV3RXhwcmVzc2lvbjogdGhlIGNvbnN0cnVjdGVkIHR5cGUg4oCUIHJlYWNoYWJsZSBkaXJlY3RseVxuXHRcdC8vICh3cmFwKG5ldyBUKCksIOKApikpIG9yIHRocm91Z2ggYSBmb2xsb3dlZCBhc3NpZ25tZW50XG5cdFx0aWYgKHRzLmlzTmV3RXhwcmVzc2lvbihhcmcpKSB7XG5cdFx0XHRjb25zdCBjdG9yRXhwciA9IGFyZy5leHByZXNzaW9uO1xuXHRcdFx0Y29uc3QgbmFtZSA9IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGN0b3JFeHByKVxuXHRcdFx0XHQ/IHRoaXMucmVzb2x2ZVR5cGVQYXRoKGN0b3JFeHByKVxuXHRcdFx0XHQ6IHRoaXMuZ2V0VHlwZU5hbWVGcm9tRXhwcmVzc2lvbihjdG9yRXhwcik7XG5cdFx0XHRjb25zdCBrbm93biA9IG5hbWUgJiYgdGhpcy5kZWZpbml0aW9ucy5oYXMobmFtZSkgPyBuYW1lIDogdW5kZWZpbmVkO1xuXHRcdFx0cmV0dXJuIGtub3duO1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2Vzczogb2JqLnByb3Bcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMucmVzb2x2ZVR5cGVQYXRoKGFyZyk7XG5cdFx0fVxuXG5cdFx0Ly8gVGhpcyBleHByZXNzaW9uOiB0aGlzLnNvbWV0aGluZ1xuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcmcpICYmIHRzLmlzSWRlbnRpZmllcihhcmcuZXhwcmVzc2lvbikgJiYgYXJnLmV4cHJlc3Npb24udGV4dCA9PT0gJ3RoaXMnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogbGV0LWluLXRyeTogZmluZCB0aGUgUklHSFQtSEFORCBTSURFIG9mIHRoZSBmaXJzdCBzdGF0aWNhbGx5LXZpc2libGVcblx0ICogYXNzaWdubWVudCB0byBgbmFtZWAgaW4gdGhlIHNjb3BlIHRoYXQgZGVjbGFyZXMgaXQuIFRoZSBkZWNsYXJpbmdcblx0ICogY29udGFpbmVyIGlzIGZvdW5kIGlubmVybW9zdC1vdXQgKGJsb2NrcywgY2FzZSBjbGF1c2VzLCB0aGUgc291cmNlXG5cdCAqIGZpbGUg4oCUIHRoZSBGMjAgd2Fsayk7IHRoZSBzY2FuIHJlY3Vyc2VzIGludG8gbmVzdGVkIGJsb2NrcyAodHJ5L1xuXHQgKiBjYXRjaC9maW5hbGx5LCBpZi9lbHNlLCBsb29wcywgc3dpdGNoIGNhc2VzKSBidXQgTkVWRVIgY3Jvc3Nlc1xuXHQgKiBmdW5jdGlvbiBvciBjbGFzcyBib3VuZGFyaWVzIOKAlCBhbiBhc3NpZ25tZW50IGluc2lkZSBhIGNsb3N1cmUgZG9lc1xuXHQgKiBub3QgYXR0cmlidXRlLiBSZXR1cm5zIHVuZGVmaW5lZCB3aGVuIHRoZSBiaW5kaW5nIGlzIGRlY2xhcmVkIGJ1dFxuXHQgKiBuZXZlciBhc3NpZ25lZCBpbiBzY29wZSAoYW5kIHN0b3BzIHRoZXJlOiBhbiBpbm5lciBkZWNsYXJhdGlvblxuXHQgKiBzaGFkb3dzIGFueSBvdXRlciBiaW5kaW5nKS5cblx0ICovXG5cdHByaXZhdGUgZm9sbG93U2NvcGVBc3NpZ25tZW50IChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IGZyb207XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGNvbnN0IHN0YXRlbWVudHM6IHRzLk5vZGVBcnJheTx0cy5TdGF0ZW1lbnQ+IHwgdW5kZWZpbmVkID1cblx0XHRcdFx0dHMuaXNCbG9jayhjdXJyZW50KSB8fCB0cy5pc01vZHVsZUJsb2NrKGN1cnJlbnQpIHx8IHRzLmlzU291cmNlRmlsZShjdXJyZW50KVxuXHRcdFx0XHRcdD8gY3VycmVudC5zdGF0ZW1lbnRzXG5cdFx0XHRcdFx0OiB0cy5pc0Nhc2VDbGF1c2UoY3VycmVudCkgfHwgdHMuaXNEZWZhdWx0Q2xhdXNlKGN1cnJlbnQpXG5cdFx0XHRcdFx0XHQ/IGN1cnJlbnQuc3RhdGVtZW50c1xuXHRcdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cdFx0XHRpZiAoc3RhdGVtZW50cyAmJiB0aGlzLnN0YXRlbWVudHNEZWNsYXJlVmFyaWFibGUoc3RhdGVtZW50cywgbmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcmhzID0gdGhpcy5maW5kQXNzaWdubWVudFJoc0luU3RhdGVtZW50cyhzdGF0ZW1lbnRzLCBuYW1lKTtcblx0XHRcdFx0cmV0dXJuIHJocztcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBUcnVlIHdoZW4gdGhlIHN0YXRlbWVudCBsaXN0IGNvbnRhaW5zIGEgYGxldGAvYHZhcmAvYGNvbnN0YFxuXHQgKiBkZWNsYXJhdGlvbiBmb3IgYG5hbWVgIChhbnkgaW5pdGlhbGl6ZXIgZm9ybSkuXG5cdCAqL1xuXHRwcml2YXRlIHN0YXRlbWVudHNEZWNsYXJlVmFyaWFibGUgKHN0YXRlbWVudHM6IHJlYWRvbmx5IHRzLlN0YXRlbWVudFtdLCBuYW1lOiBzdHJpbmcpOiBib29sZWFuIHtcblx0XHRmb3IgKGNvbnN0IHN0YXRlbWVudCBvZiBzdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAoIXRzLmlzVmFyaWFibGVTdGF0ZW1lbnQoc3RhdGVtZW50KSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3QgZGVjbGFyYXRpb24gb2Ygc3RhdGVtZW50LmRlY2xhcmF0aW9uTGlzdC5kZWNsYXJhdGlvbnMpIHtcblx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihkZWNsYXJhdGlvbi5uYW1lKSAmJiBkZWNsYXJhdGlvbi5uYW1lLnRleHQgPT09IG5hbWUpIHtcblx0XHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogRmlyc3QgYG5hbWUgPSByaHNgIGFzc2lnbm1lbnQgaW4gdGhlIHN0YXRlbWVudCBsaXN0LCByZWN1cnNpbmdcblx0ICogaW50byBuZXN0ZWQgaW4tc2NvcGUgYmxvY2tzLiBGdW5jdGlvbiBhbmQgY2xhc3MgYm9kaWVzIGFyZVxuXHQgKiBib3VuZGFyaWVzIGFuZCBhcmUgbm90IGVudGVyZWQuXG5cdCAqL1xuXHRwcml2YXRlIGZpbmRBc3NpZ25tZW50UmhzSW5TdGF0ZW1lbnRzIChcblx0XHRzdGF0ZW1lbnRzOiByZWFkb25seSB0cy5TdGF0ZW1lbnRbXSxcblx0XHRuYW1lOiBzdHJpbmdcblx0KTogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc3RhdGVtZW50cykge1xuXHRcdFx0Y29uc3QgZGlyZWN0ID0gdGhpcy5kaXJlY3RBc3NpZ25tZW50UmhzKHN0YXRlbWVudCwgbmFtZSk7XG5cdFx0XHRpZiAoZGlyZWN0KSB7XG5cdFx0XHRcdHJldHVybiBkaXJlY3Q7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IG5lc3RlZCBvZiB0aGlzLm5lc3RlZFNjb3BlQmxvY2tzKHN0YXRlbWVudCkpIHtcblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRBc3NpZ25tZW50UmhzSW5TdGF0ZW1lbnRzKG5lc3RlZCwgbmFtZSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIGBuYW1lID0gcmhzYCBhcyBhIGRpcmVjdCBleHByZXNzaW9uIHN0YXRlbWVudC5cblx0ICovXG5cdHByaXZhdGUgZGlyZWN0QXNzaWdubWVudFJocyAoc3RhdGVtZW50OiB0cy5TdGF0ZW1lbnQsIG5hbWU6IHN0cmluZyk6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHMuaXNFeHByZXNzaW9uU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGV4cHIgPSBzdGF0ZW1lbnQuZXhwcmVzc2lvbjtcblx0XHRpZiAoIXRzLmlzQmluYXJ5RXhwcmVzc2lvbihleHByKSB8fCBleHByLm9wZXJhdG9yVG9rZW4ua2luZCAhPT0gdHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbikge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoZXhwci5sZWZ0KSB8fCBleHByLmxlZnQudGV4dCAhPT0gbmFtZSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmhzID0gZXhwci5yaWdodDtcblx0XHRyZXR1cm4gcmhzO1xuXHR9XG5cblx0LyoqXG5cdCAqIFN0YXRlbWVudCBsaXN0cyBvZiB0aGUgbmVzdGVkIGJsb2NrcyB0aGF0IHN0YXkgSU5TSURFIHRoZSBjdXJyZW50XG5cdCAqIHNjb3BlIOKAlCB0cnkvY2F0Y2gvZmluYWxseSwgaWYvZWxzZSwgbG9vcHMsIHN3aXRjaCBjYXNlcywgbmVzdGVkXG5cdCAqIGJsb2NrcywgbGFiZWxlZCBzdGF0ZW1lbnRzLiBGdW5jdGlvbi1saWtlIGFuZCBjbGFzcyBib2RpZXMgYXJlXG5cdCAqIHNjb3BlIGJvdW5kYXJpZXMgYW5kIHlpZWxkIG5vdGhpbmcuXG5cdCAqL1xuXHRwcml2YXRlIG5lc3RlZFNjb3BlQmxvY2tzIChzdGF0ZW1lbnQ6IHRzLlN0YXRlbWVudCk6IHJlYWRvbmx5IChyZWFkb25seSB0cy5TdGF0ZW1lbnRbXSlbXSB7XG5cdFx0Y29uc3QgYmxvY2tzOiB0cy5TdGF0ZW1lbnRbXVtdID0gW107XG5cdFx0Y29uc3QgcHVzaCA9IChub2RlOiB0cy5TdGF0ZW1lbnQgfCB1bmRlZmluZWQpOiB2b2lkID0+IHtcblx0XHRcdGlmIChub2RlICYmIHRzLmlzQmxvY2sobm9kZSkpIHtcblx0XHRcdFx0YmxvY2tzLnB1c2goWyAuLi5ub2RlLnN0YXRlbWVudHMgXSk7XG5cdFx0XHR9XG5cdFx0fTtcblx0XHRpZiAodHMuaXNCbG9jayhzdGF0ZW1lbnQpKSB7XG5cdFx0XHRibG9ja3MucHVzaChbIC4uLnN0YXRlbWVudC5zdGF0ZW1lbnRzIF0pO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNUcnlTdGF0ZW1lbnQoc3RhdGVtZW50KSkge1xuXHRcdFx0cHVzaChzdGF0ZW1lbnQudHJ5QmxvY2spO1xuXHRcdFx0aWYgKHN0YXRlbWVudC5jYXRjaENsYXVzZSkge1xuXHRcdFx0XHRwdXNoKHN0YXRlbWVudC5jYXRjaENsYXVzZS5ibG9jayk7XG5cdFx0XHR9XG5cdFx0XHRwdXNoKHN0YXRlbWVudC5maW5hbGx5QmxvY2spO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNJZlN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRwdXNoKHN0YXRlbWVudC50aGVuU3RhdGVtZW50KTtcblx0XHRcdHB1c2goc3RhdGVtZW50LmVsc2VTdGF0ZW1lbnQpO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNGb3JTdGF0ZW1lbnQoc3RhdGVtZW50KSB8fCB0cy5pc0ZvckluU3RhdGVtZW50KHN0YXRlbWVudCkgfHxcblx0XHRcdHRzLmlzRm9yT2ZTdGF0ZW1lbnQoc3RhdGVtZW50KSB8fCB0cy5pc1doaWxlU3RhdGVtZW50KHN0YXRlbWVudCkgfHxcblx0XHRcdHRzLmlzRG9TdGF0ZW1lbnQoc3RhdGVtZW50KSB8fCB0cy5pc1dpdGhTdGF0ZW1lbnQoc3RhdGVtZW50KSkge1xuXHRcdFx0cHVzaChzdGF0ZW1lbnQuc3RhdGVtZW50KTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzU3dpdGNoU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdGZvciAoY29uc3QgY2xhdXNlIG9mIHN0YXRlbWVudC5jYXNlQmxvY2suY2xhdXNlcykge1xuXHRcdFx0XHRibG9ja3MucHVzaChbIC4uLmNsYXVzZS5zdGF0ZW1lbnRzIF0pO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSBpZiAodHMuaXNMYWJlbGVkU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdGNvbnN0IG5lc3RlZCA9IHRoaXMubmVzdGVkU2NvcGVCbG9ja3Moc3RhdGVtZW50LnN0YXRlbWVudCk7XG5cdFx0XHRmb3IgKGNvbnN0IGJsb2NrIG9mIG5lc3RlZCkge1xuXHRcdFx0XHRibG9ja3MucHVzaChbIC4uLmJsb2NrIF0pO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBibG9ja3M7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHRoZSBlbmNsb3NpbmcgbW5lbW9uaWNhIHNjb3BlIG9mIGFuIEVEUyBjYWxsIHNpdGUgYnkgd2Fsa2luZ1xuXHQgKiB1cCB0aGUgcGFyZW50IGNoYWluOiBuZWFyZXN0IGRlZmluZSgpL2xhenkoKSBjYWxsIHdob3NlIGhhbmRsZXIgaG9sZHNcblx0ICogdGhlIG5vZGUsIG9yIG5lYXJlc3QgQGRlY29yYXRlKCktZWQgY2xhc3MgZGVjbGFyYXRpb24uIEJlc3QgZWZmb3J0IOKAlFxuXHQgKiByZXR1cm5zIHVuZGVmaW5lZCBmb3IgY2FsbHMgb3V0c2lkZSBhbnkgdHlwZSBzY29wZSAobW9kdWxlIHRvcCBsZXZlbCkuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVFRFNTY29wZSAobm9kZTogdHMuTm9kZSk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBub2RlLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0Y29uc3Qgc2NvcGVQYXRoID0gdGhpcy5lZHNTY29wZUJ5Tm9kZS5nZXQoY3VycmVudCk7XG5cdFx0XHRpZiAoc2NvcGVQYXRoKSB7XG5cdFx0XHRcdHJldHVybiBzY29wZVBhdGg7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHdyYXAgc2l0ZSdzIGluc3RhbmNlL2NvbnRleHQgYXJndW1lbnQgdG8gYSBtbmVtb25pY2EgdHlwZVxuXHQgKiBwYXRoIOKAlCB0aGUgZmlyZS1hbmQtZm9yZ2V0LXdyYXBwZXIgYXR0cmlidXRpb24gZmFsbGJhY2sgd2hlbiB0aGUgY2FsbFxuXHQgKiBzaXRzIG91dHNpZGUgYW55IGRlZmluZSgpL2xhenkoKSBoYW5kbGVyOiBhIHRyYWNrZWQgYXNzaWdubWVudFxuXHQgKiAoYGNvbnN0IGhvbGRlciA9IG5ldyBIb2xkZXIoLi4uKWApLCBlbHNlIHRoZSByb290IGlkZW50aWZpZXInc1xuXHQgKiAocHJvcGVydHktYWNjZXNzIHJvb3RzIGluY2x1ZGVkKSBwYXJhbWV0ZXIgYW5ub3RhdGlvbiByZXNvbHZlZFxuXHQgKiB0aHJvdWdoIHRoZSBncmFwaCBsYXcuIEFtYmlndWl0eSBvciBhYnNlbmNlIHN0YXlzIHNpbGVudCDigJQgdGhpcyBpcyBhXG5cdCAqIG1ldGFkYXRhIGhldXJpc3RpYywgbm90IHRoZSBpZGVudGl0eS1sYXcgc3VyZmFjZS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVdyYXBJbnN0YW5jZVR5cGVQYXRoIChhcmc6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGZyb21CaW5kaW5nID0gKG5hbWU6IHN0cmluZywgZnJvbTogdHMuTm9kZSk6IHN0cmluZyB8IHVuZGVmaW5lZCA9PiB7XG5cdFx0XHRjb25zdCBtYXBwZWQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChuYW1lKTtcblx0XHRcdGlmIChtYXBwZWQpIHtcblx0XHRcdFx0cmV0dXJuIG1hcHBlZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGFubm90YXRpb25UeXBlID0gdGhpcy5yZXNvbHZlUGFyYW1ldGVyQW5ub3RhdGlvblR5cGVQYXRoKG5hbWUsIGZyb20pID8/XG5cdFx0XHRcdC8vIEYyMCBjaGVhcCB0aWVyOiB0aGUgaWRlbnRpZmllciBpcyBib3VuZCB0byBhIGxldC92YXIvY29uc3Rcblx0XHRcdFx0Ly8gd2l0aCBhbiBFWFBMSUNJVCB0eXBlIGFubm90YXRpb24g4oCUIHJlc29sdmUgdGhlIGFubm90YXRpb25cblx0XHRcdFx0Ly8gdGhyb3VnaCB0aGUgZ3JhcGggbGF3LiBObyBmbG93LXNlbnNpdGl2ZSBhc3NpZ25tZW50XG5cdFx0XHRcdC8vIHRyYWNraW5nOiBhbiBVTkFOTk9UQVRFRCBsZXQgc3RpbGwgYnVja2V0cyB1bmtub3duXG5cdFx0XHRcdHRoaXMucmVzb2x2ZVZhcmlhYmxlQW5ub3RhdGlvblR5cGVQYXRoKG5hbWUsIGZyb20pO1xuXHRcdFx0cmV0dXJuIGFubm90YXRpb25UeXBlO1xuXHRcdH07XG5cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGZyb21CaW5kaW5nKGFyZy50ZXh0LCBhcmcpO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdGNvbnN0IHJvb3QgPSB0aGlzLmdldFJvb3RJZGVudGlmaWVyKGFyZyk7XG5cdFx0XHRpZiAocm9vdCkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQgPSBmcm9tQmluZGluZyhyb290LnRleHQsIGFyZyk7XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRW1pc3Npb24tbGF3IGhlbHBlciAoMC4yLjAgcmVzdG9yYXRpb24pOiBpcyBgbmFtZWAgZGVjbGFyZWQgaW4gYW55XG5cdCAqIEFOQUxZWkVEIFBST0pFQ1QgZmlsZT8gRXh0ZXJuYWwvYW1iaWVudCBmaWxlcyAoLmQudHMsIG5vZGVfbW9kdWxlcylcblx0ICogZG8gbm90IGNvdW50LiBBIG5hbWUgd2l0aCBubyBwcm9qZWN0IGRlY2xhcmF0aW9uIGlzIGFuIGFtYmllbnQvbGliXG5cdCAqIGNvbnN0cnVjdCDigJQgc2FmZSB0byBlbWl0IHZlcmJhdGltIGludG8gdGhlIHNlbGYtY29udGFpbmVkIHR5cGVzLnRzO1xuXHQgKiBhIHByb2plY3QtbG9jYWwgbmFtZSBpcyBub3QgKG5vIGltcG9ydHMgaW4gdGhlIGdlbmVyYXRlZCBmaWxlKS5cblx0ICovXG5cdHByaXZhdGUgaXNQcm9qZWN0RGVjbGFyZWRUeXBlTmFtZSAobmFtZTogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0Zm9yIChjb25zdCBbIGZpbGUsIGRlY2xzIF0gb2YgdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzKSB7XG5cdFx0XHRpZiAodGhpcy5pc0V4dGVybmFsRGVjbEZpbGUoZmlsZSkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRpZiAoZGVjbHMuaGFzKG5hbWUpKSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBmYWxzZTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEYyNDogcmVzb2x2ZSBhIGJhcmUtaWRlbnRpZmllciBhbm5vdGF0aW9uIHRvIGEgZ3JhcGggZnVsbFBhdGguIFRoZVxuXHQgKiBhbm5vdGF0aW9uIG1heSBuYW1lIHRoZSB0eXBlIGRpcmVjdGx5IChgTGVkZ2VyVXBkYXRlYCkgb3IgY2Fycnlcblx0ICogdGhlIEdFTkVSQVRFRCBpbnN0YW5jZSBhbGlhcyBvZiBhIG5lc3RlZCB0eXBlXG5cdCAqIChgVXBkYXRlUGF5X1NvbWVUZXJtaW5hbGAsIGltcG9ydGVkIGZyb20gdGhlIGdlbmVyYXRlZCB0eXBlcyBmaWxlXG5cdCAqIHZpYSB0c2NvbmZpZyBwYXRocykg4oCUIG5vdCBhIGdyYXBoIG5vZGUgTkFNRS4gVGhlIG5hbWUgaXMgdHJpZWRcblx0ICogYXMtaXMgZmlyc3QsIHRoZW4gaXRzIHVuZGVyc2NvcmXihpJkb3R0ZWQgZm9ybSAodGhlIGdlbmVyYXRlZCBhbGlhc1xuXHQgKiBuYW1pbmcgbGF3OyB0aGUgc2FtZSBtYXBwaW5nIHNjb3Blcy5qc29uIHVzZXMgZm9yIGFubm90YXRpb25zKS5cblx0ICogQW1iaWd1aXR5IGFuZCBhYnNlbmNlIHlpZWxkIHVuZGVmaW5lZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUFubm90YXRpb25UeXBlUGF0aCAobmFtZTogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBkaXJlY3QgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKG5hbWUpO1xuXHRcdGlmIChkaXJlY3Quc3RhdHVzID09PSAndW5pcXVlJykge1xuXHRcdFx0Y29uc3QgcmVzdWx0ID0gZGlyZWN0Lm5vZGUuZnVsbFBhdGg7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH1cblx0XHRpZiAoIW5hbWUuaW5jbHVkZXMoJ18nKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgYWxpYXNlZCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUobmFtZS5yZXBsYWNlKC9fL2csICcuJykpO1xuXHRcdGlmIChhbGlhc2VkLnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGFsaWFzZWQubm9kZS5mdWxsUGF0aDtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGJhcmUtaWRlbnRpZmllciB0eXBlIGFubm90YXRpb24gb2YgdGhlIG5lYXJlc3QgZW5jbG9zaW5nXG5cdCAqIGZ1bmN0aW9uJ3MgcGFyYW1ldGVyIHRocm91Z2ggdGhlIG1uZW1vbmljYS1ncmFwaCB0aWVycyAodmFsdWUgc2NvcGUsXG5cdCAqIGltcG9ydHMsIHJvb3RzLCBwcm9ncmFtLXdpZGUtdW5pcXVlKS4gTm9uLWlkZW50aWZpZXIgYW5kIGdlbmVyaWNcblx0ICogYW5ub3RhdGlvbnMgYXJlIG5vdCBncmFwaCByZWZlcmVuY2VzOyBhbWJpZ3VpdHkgYW5kIGFic2VuY2UgeWllbGRcblx0ICogdW5kZWZpbmVkLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlUGFyYW1ldGVyQW5ub3RhdGlvblR5cGVQYXRoIChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gZnJvbS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc0Z1bmN0aW9uTGlrZShjdXJyZW50KSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGN1cnJlbnQucGFyYW1ldGVycyA/PyBbXSkge1xuXHRcdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpIHx8IHBhcmFtLm5hbWUudGV4dCAhPT0gbmFtZSB8fCAhcGFyYW0udHlwZSB8fFxuXHRcdFx0XHRcdFx0IXRzLmlzVHlwZVJlZmVyZW5jZU5vZGUocGFyYW0udHlwZSkgfHxcblx0XHRcdFx0XHRcdCF0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSkgfHxcblx0XHRcdFx0XHRcdChwYXJhbS50eXBlLnR5cGVBcmd1bWVudHM/Lmxlbmd0aCA/PyAwKSA+IDApIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCByZXNvbHZlZCA9IHRoaXMucmVzb2x2ZUFubm90YXRpb25UeXBlUGF0aChwYXJhbS50eXBlLnR5cGVOYW1lLnRleHQpO1xuXHRcdFx0XHRcdGlmIChyZXNvbHZlZCkge1xuXHRcdFx0XHRcdFx0cmV0dXJuIHJlc29sdmVkO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEYyMCBjaGVhcCB0aWVyOiB0aGUgd3JhcCBhcmd1bWVudCBpcyBhbiBpZGVudGlmaWVyIGRlY2xhcmVkIHdpdGggYW5cblx0ICogRVhQTElDSVQgdHlwZSBhbm5vdGF0aW9uIChgbGV0IHVwZGF0ZUNvbW1pdHRlZDogTGVkZ2VyVXBkYXRlO2Bcblx0ICogYXNzaWduZWQgbGF0ZXIgaW4gYSBmbG93IHRoZSBhbmFseXplciBkb2VzIG5vdCB0cmFjaykuIFRoZVxuXHQgKiBhbm5vdGF0aW9uIHJlc29sdmVzIHRocm91Z2ggdGhlIHNhbWUgZ3JhcGggdGllcnMgYXMgcGFyYW1ldGVyXG5cdCAqIGFubm90YXRpb25zLiBEZWxpYmVyYXRlbHkgTk9UIGZsb3ctc2Vuc2l0aXZlOiBhbiBVTkFOTk9UQVRFRFxuXHQgKiBsZXQvdmFyIHN0aWxsIGJ1Y2tldHMgdW5rbm93biwgYW5kIGEgY29uc3Qgd2l0aCBhbiBhbmFseXphYmxlXG5cdCAqIGluaXRpYWxpemVyIHN0YXlzIHRoZSByZWNvbW1lbmRlZCBkaXNjaXBsaW5lLiBUaGUgbG9va3VwIHdhbGtzIHRoZVxuXHQgKiBlbmNsb3Npbmcgc3RhdGVtZW50IGNvbnRhaW5lcnMgaW5uZXJtb3N0LW91dCwgc28gYSBzaGFkb3dpbmcgaW5uZXJcblx0ICogZGVjbGFyYXRpb24gd2lucy5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVZhcmlhYmxlQW5ub3RhdGlvblR5cGVQYXRoIChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gZnJvbTtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0Y29uc3Qgc3RhdGVtZW50czogdHMuTm9kZUFycmF5PHRzLlN0YXRlbWVudD4gfCB1bmRlZmluZWQgPVxuXHRcdFx0XHR0cy5pc0Jsb2NrKGN1cnJlbnQpIHx8IHRzLmlzTW9kdWxlQmxvY2soY3VycmVudCkgfHwgdHMuaXNTb3VyY2VGaWxlKGN1cnJlbnQpXG5cdFx0XHRcdFx0PyBjdXJyZW50LnN0YXRlbWVudHNcblx0XHRcdFx0XHQ6IHRzLmlzQ2FzZUNsYXVzZShjdXJyZW50KSB8fCB0cy5pc0RlZmF1bHRDbGF1c2UoY3VycmVudClcblx0XHRcdFx0XHRcdD8gY3VycmVudC5zdGF0ZW1lbnRzXG5cdFx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblx0XHRcdGlmIChzdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdGNvbnN0IHJlc29sdmVkID0gdGhpcy5maW5kQW5ub3RhdGVkVmFyaWFibGVUeXBlUGF0aChzdGF0ZW1lbnRzLCBuYW1lKTtcblx0XHRcdFx0aWYgKHJlc29sdmVkKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHJlc29sdmVkO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmlyc3QgdmFyaWFibGUgZGVjbGFyYXRpb24gY2FycnlpbmcgYW4gZXhwbGljaXQgYmFyZS1pZGVudGlmaWVyIHR5cGVcblx0ICogYW5ub3RhdGlvbiBmb3IgYG5hbWVgIGluIHRoZSBnaXZlbiBzdGF0ZW1lbnQgbGlzdCwgcmVzb2x2ZWQgdGhyb3VnaFxuXHQgKiB0aGUgZ3JhcGggbGF3LlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kQW5ub3RhdGVkVmFyaWFibGVUeXBlUGF0aCAoXG5cdFx0c3RhdGVtZW50czogcmVhZG9ubHkgdHMuU3RhdGVtZW50W10sXG5cdFx0bmFtZTogc3RyaW5nXG5cdCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc3RhdGVtZW50cykge1xuXHRcdFx0aWYgKCF0cy5pc1ZhcmlhYmxlU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGRlY2xhcmF0aW9uIG9mIHN0YXRlbWVudC5kZWNsYXJhdGlvbkxpc3QuZGVjbGFyYXRpb25zKSB7XG5cdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGRlY2xhcmF0aW9uLm5hbWUpIHx8IGRlY2xhcmF0aW9uLm5hbWUudGV4dCAhPT0gbmFtZSB8fFxuXHRcdFx0XHRcdCFkZWNsYXJhdGlvbi50eXBlIHx8XG5cdFx0XHRcdFx0IXRzLmlzVHlwZVJlZmVyZW5jZU5vZGUoZGVjbGFyYXRpb24udHlwZSkgfHxcblx0XHRcdFx0XHQhdHMuaXNJZGVudGlmaWVyKGRlY2xhcmF0aW9uLnR5cGUudHlwZU5hbWUpIHx8XG5cdFx0XHRcdFx0KGRlY2xhcmF0aW9uLnR5cGUudHlwZUFyZ3VtZW50cz8ubGVuZ3RoID8/IDApID4gMCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IHJlc29sdmVkID0gdGhpcy5yZXNvbHZlQW5ub3RhdGlvblR5cGVQYXRoKGRlY2xhcmF0aW9uLnR5cGUudHlwZU5hbWUudGV4dCk7XG5cdFx0XHRcdGlmIChyZXNvbHZlZCkge1xuXHRcdFx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSB3cmFwKCkgYXJndW1lbnQgdG8gaXRzIGZ1bmN0aW9uIG5vZGUgd2l0aG91dCB0aGUgdHlwZVxuXHQgKiBjaGVja2VyOiBkaXJlY3QgZnVuY3Rpb24gZXhwcmVzc2lvbnMvYXJyb3dzLCBvciBzYW1lLWZpbGUgYmluZGluZ3Ncblx0ICogKGBjb25zdCBmbiA9ICgpID0+IC4uLmAsIGBmdW5jdGlvbiBmbigpIC4uLmApLiBCZXN0IGVmZm9ydCDigJQgbWV0aG9kXG5cdCAqIHJlZmVyZW5jZXMsIC5iaW5kKCkgcHJvZHVjdHMgYW5kIGNyb3NzLWZpbGUgaWRlbnRpZmllcnMgc3RheVxuXHQgKiB1bnJlc29sdmVkOyB0aGUgY2FsbHNpdGUgZW50cnkgaXRzZWxmIGlzIHN0aWxsIHJlY29yZGVkLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRnVuY3Rpb25Bcmd1bWVudCAoXG5cdFx0YXJnOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGVcblx0KTogdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGlmICghYXJnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGFyZykgfHwgdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0cmV0dXJuIGFyZztcblx0XHR9XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihhcmcpKSB7XG5cdFx0XHRjb25zdCBrZXkgPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfSMke2FyZy50ZXh0fWA7XG5cdFx0XHRjb25zdCBib3VuZCA9IHRoaXMuZnVuY3Rpb25CaW5kaW5ncy5nZXQoa2V5KTtcblx0XHRcdGlmIChib3VuZCkge1xuXHRcdFx0XHRyZXR1cm4gYm91bmQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogQW5hbHlzZSBhIHdyYXBwZWQgZnVuY3Rpb24ncyBib2R5IGZvciBndWFyYW50ZWVkIHJ1bnRpbWUgcGF0aHM6XG5cdCAqIGRpdmUgd3JhcHMgcmV0dXJuZWQgZnVuY3Rpb25zIGFzIHdlbGwgKHJlY3Vyc2l2ZWx5KSwgc28gZWFjaFxuXHQgKiBmdW5jdGlvbi12YWx1ZWQgcmV0dXJuIGlzIGEgbmVzdGVkIHdyYXAgc2l0ZSwgYW5kIGVhY2ggYG5ldyBUeXBlKClgXG5cdCAqIGluc2lkZSB0aGUgYm9keSBtZWFucyB0aGUgcGF0aCBoaXRzIHRoYXQgdHlwZSdzIGNvbnN0cnVjdG9yICh3aGljaFxuXHQgKiBhdHRhY2hIb29rcyB3cmFwcyB0b28pLiBCb3RoIGZhY3RzIGFyZSAxMDAlIGVuc3VyZWQsIHNvIHRoZXkgYXJlXG5cdCAqIHJlY29yZGVkIEFvVC4gTmVzdGVkIGZ1bmN0aW9uIGJvZGllcyBhcmUgTk9UIHdhbGtlZCBoZXJlIOKAlCB0aGV5XG5cdCAqIGJlbG9uZyB0byB0aGVpciBvd24gd3JhcCBhbmFseXNpcywgcmVhY2hlZCB2aWEgdGhlIHJldHVybiBjaGFpbi5cblx0ICogRGVwdGgtY2FwcGVkIGFuZCBjeWNsZS1ndWFyZGVkLlxuXHQgKi9cblx0cHJpdmF0ZSBhbmFseXplV3JhcHBlZEJvZHkgKFxuXHRcdGZuOiB0cy5GdW5jdGlvbkxpa2VEZWNsYXJhdGlvbixcblx0XHR2aWFMb2NhdGlvbjogc3RyaW5nLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0ZGVwdGg6IG51bWJlcixcblx0XHR2aXNpdGVkOiBTZXQ8dHMuTm9kZT4sXG5cdFx0Y3JlYXRlc1R5cGVzOiBTZXQ8c3RyaW5nPixcblx0XHRmYWxsYmFja1Njb3BlPzogc3RyaW5nXG5cdCk6IHZvaWQge1xuXHRcdGlmIChkZXB0aCA+IDUgfHwgdmlzaXRlZC5oYXMoZm4pIHx8ICFmbi5ib2R5KSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHZpc2l0ZWQuYWRkKGZuKTtcblxuXHRcdC8vIEFycm93IHdpdGggZXhwcmVzc2lvbiBib2R5OiBpbXBsaWNpdCByZXR1cm5cblx0XHRpZiAodHMuaXNBcnJvd0Z1bmN0aW9uKGZuKSAmJiAhdHMuaXNCbG9jayhmbi5ib2R5KSkge1xuXHRcdFx0dGhpcy5yZWNvcmRXcmFwcGVkUmV0dXJuKGZuLmJvZHksIHZpYUxvY2F0aW9uLCBzb3VyY2VGaWxlLCBkZXB0aCwgdmlzaXRlZCwgZmFsbGJhY2tTY29wZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3Qgd2FsayA9IChub2RlOiB0cy5Ob2RlKTogdm9pZCA9PiB7XG5cdFx0XHRpZiAobm9kZSAhPT0gZm4uYm9keSAmJiAoXG5cdFx0XHRcdHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKG5vZGUpIHx8XG5cdFx0XHRcdHRzLmlzQXJyb3dGdW5jdGlvbihub2RlKSB8fFxuXHRcdFx0XHR0cy5pc0Z1bmN0aW9uRGVjbGFyYXRpb24obm9kZSkgfHxcblx0XHRcdFx0dHMuaXNNZXRob2REZWNsYXJhdGlvbihub2RlKVxuXHRcdFx0KSkge1xuXHRcdFx0XHQvLyBuZXN0ZWQgZnVuY3Rpb24gYm9kaWVzIGFyZSBhbmFseXNlZCB0aHJvdWdoIHRoZSByZXR1cm4gY2hhaW5cblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0XHR0aGlzLnJlY29yZFdyYXBwZWRSZXR1cm4obm9kZS5leHByZXNzaW9uLCB2aWFMb2NhdGlvbiwgc291cmNlRmlsZSwgZGVwdGgsIHZpc2l0ZWQsIGZhbGxiYWNrU2NvcGUpO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzTmV3RXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0XHRjb25zdCBjcmVhdGVkID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKSB8fFxuXHRcdFx0XHRcdCh0cy5pc0lkZW50aWZpZXIobm9kZS5leHByZXNzaW9uKSAmJiB0aGlzLmRlZmluaXRpb25zLmhhcyhub2RlLmV4cHJlc3Npb24udGV4dClcblx0XHRcdFx0XHRcdD8gbm9kZS5leHByZXNzaW9uLnRleHRcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkKTtcblx0XHRcdFx0aWYgKGNyZWF0ZWQpIHtcblx0XHRcdFx0XHRjcmVhdGVzVHlwZXMuYWRkKGNyZWF0ZWQpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0XHRjb25zdCBuZXN0ZWROYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKTtcblx0XHRcdFx0aWYgKFxuXHRcdFx0XHRcdG5lc3RlZE5hbWUgPT09ICd3cmFwJyB8fFxuXHRcdFx0XHRcdG5lc3RlZE5hbWUgPT09ICd3cmFwQ29uc3RydWN0b3JBcmcnIHx8XG5cdFx0XHRcdFx0bmVzdGVkTmFtZSA9PT0gJ3VwZ3JhZGVDb25zdHJ1Y3RvckFyZycgfHxcblx0XHRcdFx0XHRuZXN0ZWROYW1lID09PSAnd3JhcEluc3RhbmNlTWV0aG9kcydcblx0XHRcdFx0KSB7XG5cdFx0XHRcdFx0Ly8gdGhlIG5lc3RlZCBjYWxsIG1heSBhbHJlYWR5IGJlIGNvbGxlY3RlZCAodmlzaXRlZFxuXHRcdFx0XHRcdC8vIGJlZm9yZSB0aGlzIG91dGVyIHdyYXAgc2l0ZSkg4oCUIGJhY2stcGF0Y2ggaXRzIGVudHJ5LFxuXHRcdFx0XHRcdC8vIG90aGVyd2lzZSBsZWF2ZSB0aGUgbGluayAod2l0aCB0aGlzIHNpdGUncyBzY29wZSkgZm9yXG5cdFx0XHRcdFx0Ly8gY29sbGVjdEVEUyB0byBwaWNrIHVwXG5cdFx0XHRcdFx0Y29uc3QgbmVzdGVkRW50cnkgPSB0aGlzLndyYXBFbnRyeUJ5Tm9kZS5nZXQobm9kZSk7XG5cdFx0XHRcdFx0aWYgKG5lc3RlZEVudHJ5KSB7XG5cdFx0XHRcdFx0XHRuZXN0ZWRFbnRyeS52aWEgPSB2aWFMb2NhdGlvbjtcblx0XHRcdFx0XHRcdGlmIChuZXN0ZWRFbnRyeS5zY29wZSA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdFx0XHRcdG5lc3RlZEVudHJ5LnNjb3BlID0gZmFsbGJhY2tTY29wZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0dGhpcy5uZXN0ZWRXcmFwVmlhLnNldChub2RlLCB7IHZpYSA6IHZpYUxvY2F0aW9uLCBzY29wZSA6IGZhbGxiYWNrU2NvcGUgfSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgd2Fsayk7XG5cdFx0fTtcblx0XHR3YWxrKGZuLmJvZHkpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBvbmUgZnVuY3Rpb24tdmFsdWVkIHJldHVybiBvZiBhIHdyYXBwZWQgYm9keSBhcyBhIG5lc3RlZCB3cmFwXG5cdCAqIHNpdGUgKGB2aWFgID0gdGhlIHNpdGUgd2hvc2Ugd3JhcHBpbmcgY2F1c2VkIGl0KSBhbmQgcmVjdXJzZSBpbnRvXG5cdCAqIGl0cyBvd24gcmV0dXJucy4gUmV0dXJucyB0aHJvdWdoIGlkZW50aWZpZXJzIHJlc29sdmUgdGhyb3VnaCB0aGVcblx0ICogc2FtZS1maWxlIGJpbmRpbmdzIHRhYmxlOyB1bnJlc29sdmFibGUgcmV0dXJucyBhcmUgc2ltcGx5IHNraXBwZWQuXG5cdCAqIEEgcmV0dXJuIGRlY2xhcmVkIG91dHNpZGUgYW55IHR5cGUgc2NvcGUgaW5oZXJpdHMgdGhlIGNhdXNpbmcgd3JhcFxuXHQgKiBzaXRlJ3Mgc2NvcGUgYXR0cmlidXRpb24gKHRoZSBnZW5lcmF0aW9uIGNoYWluIGlzIHRoZSBvbmx5IGhvbGRlcikuXG5cdCAqL1xuXHRwcml2YXRlIHJlY29yZFdyYXBwZWRSZXR1cm4gKFxuXHRcdGV4cHI6IHRzLkV4cHJlc3Npb24sXG5cdFx0dmlhTG9jYXRpb246IHN0cmluZyxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdGRlcHRoOiBudW1iZXIsXG5cdFx0dmlzaXRlZDogU2V0PHRzLk5vZGU+LFxuXHRcdGZhbGxiYWNrU2NvcGU/OiBzdHJpbmdcblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgcmV0dXJuZWQgPSB0aGlzLnJlc29sdmVGdW5jdGlvbkFyZ3VtZW50KGV4cHIsIHNvdXJjZUZpbGUpO1xuXHRcdGlmICghcmV0dXJuZWQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdHJldHVybmVkLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSByZXR1cm5lZC5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cdFx0Y29uc3Qgc2NvcGUgPSB0aGlzLnJlc29sdmVFRFNTY29wZShyZXR1cm5lZCkgPz8gZmFsbGJhY2tTY29wZTtcblx0XHRjb25zdCBlbnRyeSA9IHRoaXMuYWRkRURTKHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kIDogJ3dyYXAnLFxuXHRcdFx0Y29kZSxcblx0XHRcdHNjb3BlLFxuXHRcdFx0dmlhICA6IHZpYUxvY2F0aW9uLFxuXHRcdFx0Ly8gZGl2ZSB3cmFwcyByZXR1cm5lZCBmdW5jdGlvbnMgdGhyb3VnaCB0aGUgc2FtZSB3cmFwIG1hY2hpbmVyeVxuXHRcdFx0Zm4gICA6ICd3cmFwJyxcblx0XHR9KTtcblx0XHQvLyB0aGUgcmV0dXJuZWQgZnVuY3Rpb24ncyBvd24gcmV0dXJucyBhcmUgd3JhcHBlZCBpbiB0dXJuOyBgdmlhYFxuXHRcdC8vIGNoYWlucyB0byB0aGlzIG5lc3RlZCBlbnRyeSdzIGxvY2F0aW9uXG5cdFx0Y29uc3QgbmVzdGVkQ3JlYXRlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdHRoaXMuYW5hbHl6ZVdyYXBwZWRCb2R5KHJldHVybmVkLCBsb2NhdGlvbiwgc291cmNlRmlsZSwgZGVwdGggKyAxLCB2aXNpdGVkLCBuZXN0ZWRDcmVhdGVzLCBzY29wZSk7XG5cdFx0aWYgKG5lc3RlZENyZWF0ZXMuc2l6ZSA+IDApIHtcblx0XHRcdGVudHJ5LmNyZWF0ZXNUeXBlcyA9IEFycmF5LmZyb20obmVzdGVkQ3JlYXRlcyk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhbiBFRFMgdXNhZ2UgdG8gdGhlIGNvbGxlY3Rpb25cblx0ICogUmV0dXJucyB0aGUgc3RvcmVkIGVudHJ5ICh0aGUgZXhpc3Rpbmcgb25lIHdoZW4gdGhpcyBpcyBhIGR1cGxpY2F0ZSksXG5cdCAqIHNvIGNhbGxlcnMgY2FuIGVucmljaCBpdCBhZnRlciBuZXN0ZWQgYm9keSBhbmFseXNpcy5cblx0ICovXG5cdHByaXZhdGUgYWRkRURTICh0eXBlUGF0aDogc3RyaW5nLCBpbmZvOiBFRFNJbmZvKTogRURTSW5mbyB7XG5cdFx0aWYgKCF0aGlzLmVkc1VzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLmVkc1VzYWdlcy5zZXQodHlwZVBhdGgsIFtdKTtcblx0XHR9XG5cblx0XHRjb25zdCBleGlzdGluZyA9IHRoaXMuZWRzVXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGR1cGxpY2F0ZSA9IGV4aXN0aW5nLmZpbmQoZSA9PiB7XG5cdFx0XHRyZXR1cm4gZS5sb2NhdGlvbiA9PT0gaW5mby5sb2NhdGlvbiAmJlxuXHRcdFx0XHRlLmtpbmQgPT09IGluZm8ua2luZCAmJlxuXHRcdFx0XHRlLmNvZGUgPT09IGluZm8uY29kZTtcblx0XHR9KTtcblxuXHRcdGlmIChkdXBsaWNhdGUpIHtcblx0XHRcdHJldHVybiBkdXBsaWNhdGU7XG5cdFx0fVxuXHRcdGV4aXN0aW5nLnB1c2goaW5mbyk7XG5cdFx0cmV0dXJuIGluZm87XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBuYXRpdmUgZmxvdyBwYXR0ZXJucyAoaW5zdGFuY2UgdXNhZ2UgYWZ0ZXIgY3JlYXRpb24pXG5cdCAqIFBoYXNlIDE6IHByb3BlcnR5IGFjY2VzcywgbWV0aG9kIGNhbGxzLCBhcmd1bWVudHMsIHJldHVybiwgZGVzdHJ1Y3R1cmluZywgZXRjLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0RmxvdyAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIFByb3BlcnR5IHJlYWQ6IHVzZXIubmFtZSBvciB1c2VyPy5uYW1lXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93UHJvcGVydHlBY2Nlc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRWxlbWVudCBhY2Nlc3M6IHVzZXJbJ25hbWUnXVxuXHRcdGlmICh0cy5pc0VsZW1lbnRBY2Nlc3NFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93RWxlbWVudEFjY2Vzcyhub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSB3cml0ZTogdXNlci5uYW1lID0gdmFsdWVcblx0XHRpZiAodHMuaXNCaW5hcnlFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkVxdWFsc1Rva2VuKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93QXNzaWdubWVudChub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBNZXRob2QgY2FsbDogdXNlci52YWxpZGF0ZSgpICBBTkQgIGFyZ3VtZW50IHBhc3Npbmc6IHByb2Nlc3NVc2VyKHVzZXIpXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93TWV0aG9kQ2FsbChub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dBcmd1bWVudFBhc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRGVzdHJ1Y3R1cmUgcmVhZDogY29uc3QgeyBuYW1lIH0gPSB1c2VyXG5cdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLmluaXRpYWxpemVyKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93RGVzdHJ1Y3R1cmUobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUmV0dXJuIGluc3RhbmNlOiByZXR1cm4gdXNlclxuXHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dSZXR1cm4obm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gU3ByZWFkOiB7IC4uLnVzZXIgfVxuXHRcdGlmICh0cy5pc1NwcmVhZEVsZW1lbnQobm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dTcHJlYWQobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgcHJvcGVydHkgYWNjZXNzIGZsb3cgKHJlYWQgb3IgY29uZGl0aW9uYWwpXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93UHJvcGVydHlBY2Nlc3MgKG5vZGU6IHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHByb3BOYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0Ly8gU2tpcCBpZiB0aGlzIGlzIGEgdHlwZSBjb25zdHJ1Y3RvciBhY2Nlc3MgKGUuZy4sIFVzZXJUeXBlLmRlZmluZSlcblx0XHRpZiAocHJvcE5hbWUgPT09ICdkZWZpbmUnIHx8IHByb3BOYW1lID09PSAnbGF6eScpIHsgcmV0dXJuOyB9XG5cblx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgICAgOiAncHJvcGVydHlSZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHRwcm9wZXJ0eU5hbWUgOiBwcm9wTmFtZSxcblx0XHRcdHRhcmdldFR5cGUgICA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGVsZW1lbnQgYWNjZXNzIGZsb3c6IHVzZXJbJ25hbWUnXVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0VsZW1lbnRBY2Nlc3MgKG5vZGU6IHRzLkVsZW1lbnRBY2Nlc3NFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3Qgb2JqZWN0VHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0aWYgKCFvYmplY3RUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0dGhpcy5hZGRGbG93KG9iamVjdFR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICA6ICdlbGVtZW50QWNjZXNzJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogb2JqZWN0VHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgYXNzaWdubWVudCBmbG93OiB1c2VyLm5hbWUgPSB2YWx1ZSBvciB1c2VyID0gb3RoZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dBc3NpZ25tZW50IChub2RlOiB0cy5CaW5hcnlFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gUHJvcGVydHkgd3JpdGU6IHVzZXIubmFtZSA9IHZhbHVlXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUubGVmdCkpIHtcblx0XHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmxlZnQuZXhwcmVzc2lvbik7XG5cdFx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRcdGNvbnN0IHByb3BOYW1lID0gbm9kZS5sZWZ0Lm5hbWUudGV4dDtcblx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0KTtcblx0XHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgICAgOiAncHJvcGVydHlXcml0ZScsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHByb3BlcnR5TmFtZSA6IHByb3BOYW1lLFxuXHRcdFx0XHR0YXJnZXRUeXBlICAgOiBvYmplY3RUeXBlXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBWYXJpYWJsZSByZWFzc2lnbm1lbnQ6IHVzZXIgPSBvdGhlclxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIobm9kZS5sZWZ0KSkge1xuXHRcdFx0Y29uc3QgdmFyTmFtZSA9IG5vZGUubGVmdC50ZXh0O1xuXHRcdFx0Y29uc3QgbWFwcGVkVHlwZSA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KHZhck5hbWUpO1xuXHRcdFx0aWYgKCFtYXBwZWRUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdCk7XG5cdFx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0XHR0aGlzLmFkZEZsb3cobWFwcGVkVHlwZSwge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCAgICAgICA6ICdyZWFzc2lnbm1lbnQnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHR0YXJnZXRUeXBlIDogbWFwcGVkVHlwZVxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgbWV0aG9kIGNhbGwgZmxvdzogdXNlci52YWxpZGF0ZSgpXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93TWV0aG9kQ2FsbCAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbikpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IG1ldGhvZE5hbWUgPSBub2RlLmV4cHJlc3Npb24ubmFtZS50ZXh0O1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIFNraXAgaWYgdGhpcyBpcyBhIHR5cGUgY29uc3RydWN0b3IgY2FsbCAoZS5nLiwgbmV3IFVzZXJUeXBlKCkpXG5cdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdkZWZpbmUnIHx8IG1ldGhvZE5hbWUgPT09ICdsYXp5JykgeyByZXR1cm47IH1cblxuXHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgICA6ICdtZXRob2RDYWxsJyxcblx0XHRcdGNvZGUsXG5cdFx0XHRwcm9wZXJ0eU5hbWUgOiBtZXRob2ROYW1lLFxuXHRcdFx0dGFyZ2V0VHlwZSAgIDogb2JqZWN0VHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgYXJndW1lbnQgcGFzc2luZyBmbG93OiBwcm9jZXNzVXNlcih1c2VyKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0FyZ3VtZW50UGFzcyAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRjb25zdCBhcmcgPSBub2RlLmFyZ3VtZW50c1sgaSBdO1xuXHRcdFx0Y29uc3QgYXJnVHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKGFyZyk7XG5cdFx0XHRpZiAoIWFyZ1R5cGUpIHsgY29udGludWU7IH1cblxuXHRcdFx0Y29uc3QgZnVuY05hbWUgPSB0aGlzLmdldEZ1bmN0aW9uTmFtZShub2RlLmV4cHJlc3Npb24pIHx8ICdhbm9ueW1vdXMnO1xuXHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHQpO1xuXHRcdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdFx0dGhpcy5hZGRGbG93KGFyZ1R5cGUsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAncGFzc0FzQXJnJyxcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSA6IGFyZ1R5cGUsXG5cdFx0XHRcdGNvbnRleHQgICAgOiBgYXJnICR7aX0gdG8gJHtmdW5jTmFtZX1gXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBkZXN0cnVjdHVyaW5nIGZsb3c6IGNvbnN0IHsgbmFtZSB9ID0gdXNlclxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0Rlc3RydWN0dXJlIChub2RlOiB0cy5WYXJpYWJsZURlY2xhcmF0aW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc09iamVjdEJpbmRpbmdQYXR0ZXJuKG5vZGUubmFtZSkpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBzb3VyY2VUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5pbml0aWFsaXplciEpO1xuXHRcdGlmICghc291cmNlVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIEV4dHJhY3QgZGVzdHJ1Y3R1cmVkIHByb3BlcnR5IG5hbWVzXG5cdFx0Y29uc3QgcHJvcHM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIG5vZGUubmFtZS5lbGVtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihlbGVtZW50Lm5hbWUpKSB7XG5cdFx0XHRcdHByb3BzLnB1c2goZWxlbWVudC5uYW1lLnRleHQpO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHRoaXMuYWRkRmxvdyhzb3VyY2VUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnZGVzdHJ1Y3R1cmVSZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogc291cmNlVHlwZSxcblx0XHRcdGNvbnRleHQgICAgOiBwcm9wcy5qb2luKCcsICcpXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCByZXR1cm4gZmxvdzogcmV0dXJuIHVzZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dSZXR1cm4gKG5vZGU6IHRzLlJldHVyblN0YXRlbWVudCwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHJldHVyblR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24hKTtcblx0XHRpZiAoIXJldHVyblR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHR0aGlzLmFkZEZsb3cocmV0dXJuVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ3JldHVybicsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHJldHVyblR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IHNwcmVhZCBmbG93OiB7IC4uLnVzZXIgfVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd1NwcmVhZCAobm9kZTogdHMuU3ByZWFkRWxlbWVudCwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHNwcmVhZFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghc3ByZWFkVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuYWRkRmxvdyhzcHJlYWRUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnc3ByZWFkJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogc3ByZWFkVHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgdHlwZSBmcm9tIGFuIGV4cHJlc3Npb24gKGlkZW50aWZpZXIsIHByb3BlcnR5IGFjY2VzcywgZXRjLilcblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUV4cHJlc3Npb25UeXBlIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBJZGVudGlmaWVyOiB1c2VyXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGV4cHIudGV4dCk7XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiB1c2VyLm5hbWUgKHJldHVybiBvYmplY3QgdHlwZSwgbm90IHByb3BlcnR5IHR5cGUpXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUoZXhwci5leHByZXNzaW9uKTtcblx0XHR9XG5cblx0XHQvLyBFbGVtZW50IGFjY2VzczogdXNlclsnbmFtZSddXG5cdFx0aWYgKHRzLmlzRWxlbWVudEFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdHJldHVybiB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShleHByLmV4cHJlc3Npb24pO1xuXHRcdH1cblxuXHRcdC8vIFRoaXMgZXhwcmVzc2lvbjogdGhpcyAoaWYgaW4gYSBtZXRob2QsIHdlIGNhbid0IHJlc29sdmUgd2l0aG91dCBtb3JlIGNvbnRleHQpXG5cdFx0aWYgKGV4cHIua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEFkZCBhIGZsb3cgdXNhZ2UgdG8gdGhlIGNvbGxlY3Rpb25cblx0ICovXG5cdHByaXZhdGUgYWRkRmxvdyAodHlwZVBhdGg6IHN0cmluZywgaW5mbzogRmxvd0luZm8pOiB2b2lkIHtcblx0XHRpZiAoIXRoaXMuZmxvd1VzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLmZsb3dVc2FnZXMuc2V0KHR5cGVQYXRoLCBbXSk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZXhpc3RpbmcgPSB0aGlzLmZsb3dVc2FnZXMuZ2V0KHR5cGVQYXRoKSE7XG5cdFx0Y29uc3QgaXNEdXBsaWNhdGUgPSBleGlzdGluZy5zb21lKGUgPT4ge1xuXHRcdFx0cmV0dXJuIGUubG9jYXRpb24gPT09IGluZm8ubG9jYXRpb24gJiZcblx0XHRcdFx0ZS5raW5kID09PSBpbmZvLmtpbmQgJiZcblx0XHRcdFx0ZS5jb2RlID09PSBpbmZvLmNvZGU7XG5cdFx0fSk7XG5cblx0XHRpZiAoIWlzRHVwbGljYXRlKSB7XG5cdFx0XHRleGlzdGluZy5wdXNoKGluZm8pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdFx0KiBHZXQgdHlwZSBuYW1lIGZyb20gZXhwcmVzc2lvbiAoaWRlbnRpZmllciBvciBwcm9wZXJ0eSBhY2Nlc3MpXG5cdFx0XHQqL1xuXHRwcml2YXRlIGdldFR5cGVOYW1lRnJvbUV4cHJlc3Npb24gKGV4cHI6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdGNvbnN0IG5hbWUgPSBleHByLnRleHQ7XG5cdFx0XHQvLyBDaGVjayBpZiB0aGlzIGlkZW50aWZpZXIgaXMgYSB2YXJpYWJsZSBtYXBwZWQgdG8gYSB0eXBlIChlLmcuLCBmcm9tIGxvb2t1cClcblx0XHRcdGNvbnN0IG1hcHBlZFR5cGUgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChuYW1lKTtcblx0XHRcdGlmIChtYXBwZWRUeXBlKSB7XG5cdFx0XHRcdHJldHVybiBtYXBwZWRUeXBlO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIG5hbWU7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4oZXhwcik7XG5cdFx0XHRyZXR1cm4gY2hhaW4uam9pbignLicpO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cdFxuXHQvKipcblx0XHRcdCogUmVzb2x2ZSBmdWxsIHR5cGUgcGF0aCBmcm9tIHByb3BlcnR5IGFjY2Vzc1xuXHRcdFx0Ki9cblx0cHJpdmF0ZSByZXNvbHZlVHlwZVBhdGggKGV4cHI6IHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4oZXhwcik7XG5cdFx0aWYgKGNoYWluLmxlbmd0aCA9PT0gMCkgcmV0dXJuIHVuZGVmaW5lZDtcblx0XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBjaGFpbiBtYXRjaGVzIGEga25vd24gdHlwZVxuXHRcdGNvbnN0IGZ1bGxQYXRoID0gY2hhaW4uam9pbignLicpO1xuXHRcdGlmICh0aGlzLmRlZmluaXRpb25zLmhhcyhmdWxsUGF0aCkpIHtcblx0XHRcdHJldHVybiBmdWxsUGF0aDtcblx0XHR9XG5cdFxuXHRcdC8vIFRyeSBqdXN0IHRoZSBwcm9wZXJ0eSBuYW1lXG5cdFx0Y29uc3QgcHJvcE5hbWUgPSBjaGFpblsgY2hhaW4ubGVuZ3RoIC0gMSBdO1xuXHRcdGZvciAoY29uc3QgWyBwYXRoIF0gb2YgdGhpcy5kZWZpbml0aW9ucykge1xuXHRcdFx0aWYgKHBhdGguZW5kc1dpdGgoYC4ke3Byb3BOYW1lfWApIHx8IHBhdGggPT09IHByb3BOYW1lKSB7XG5cdFx0XHRcdHJldHVybiBwYXRoO1xuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0cmV0dXJuIGZ1bGxQYXRoO1xuXHR9XG5cdFxuXHQvKipcblx0XHRcdCAqIENoZWNrIGlmIGEgbmFtZSBsb29rcyBsaWtlIGEgdHlwZSAoc3RhcnRzIHdpdGggdXBwZXJjYXNlKVxuXHRcdFx0ICovXG5cdHByaXZhdGUgaXNMaWtlbHlUeXBlTmFtZSAobmFtZTogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0cmV0dXJuIG5hbWVbIDAgXSA+PSAnQScgJiYgbmFtZVsgMCBdIDw9ICdaJztcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQgKiBSZXNvbHZlIGEgY29uc3RydWN0b3IgcGFyYW1ldGVyIHR5cGUsIGV4cGFuZGluZyBpbmxpbmUgb2JqZWN0IGxpdGVyYWxzXG5cdFx0XHQgKiBhbmQgdHlwZSBhbGlhc2VzIHdoZXJlIHBvc3NpYmxlLlxuXHRcdFx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUNvbnN0cnVjdG9yUGFyYW1UeXBlICh0eXBlTm9kZTogdHMuVHlwZU5vZGUgfCB1bmRlZmluZWQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHlwZU5vZGUpIHJldHVybiB1bmRlZmluZWQ7XG5cblx0XHQvLyBEaXJlY3QgaW5saW5lIHR5cGUgbGl0ZXJhbDogeyBwcm9wOiB0eXBlIH1cblx0XHRpZiAodHMuaXNUeXBlTGl0ZXJhbE5vZGUodHlwZU5vZGUpKSB7XG5cdFx0XHRjb25zdCBwcm9wczogc3RyaW5nW10gPSBbXTtcblx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIHR5cGVOb2RlLm1lbWJlcnMpIHtcblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdGNvbnN0IG9wdGlvbmFsID0gbWVtYmVyLnF1ZXN0aW9uVG9rZW4gPyAnPycgOiAnJztcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdHByb3BzLnB1c2goYCR7cHJvcE5hbWV9JHtvcHRpb25hbH06ICR7dHlwZX1gKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGB7ICR7cHJvcHMuam9pbignOyAnKX0gfWA7XG5cdFx0fVxuXG5cdFx0Ly8gVHlwZSByZWZlcmVuY2U6IHVzYWdlLCBVc2VyRGF0YSwgZXRjLiAtIHJlc29sdmUgaW1wb3J0LWF3YXJlIGFuZFxuXHRcdC8vIGV4cGFuZCB0aGUgcmVmZXJlbmNlZCBkZWNsYXJhdGlvbiB3aGVyZSBwb3NzaWJsZSAoRjEwKVxuXHRcdGlmICh0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHR5cGVOb2RlKSAmJiB0cy5pc0lkZW50aWZpZXIodHlwZU5vZGUudHlwZU5hbWUpKSB7XG5cdFx0XHRjb25zdCB0eXBlTmFtZSA9IHR5cGVOb2RlLnR5cGVOYW1lLnRleHQ7XG5cdFx0XHRjb25zdCBkZWNsID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbih0eXBlTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdGlmIChkZWNsKSB7XG5cdFx0XHRcdGNvbnN0IGV4cGFuZGVkID0gdGhpcy5leHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKGRlY2wpO1xuXHRcdFx0XHRpZiAoZXhwYW5kZWQpIHJldHVybiBleHBhbmRlZDtcblx0XHRcdH1cblx0XHRcdC8vIG1uZW1vbmljYSBncmFwaCB0eXBlcyBrZWVwIHRoZWlyIHNpbXBsZSBuYW1lIOKAlCB0aGUgZ2VuZXJhdG9yXG5cdFx0XHQvLyB1cGdyYWRlcyB0aGVtIHRvIGZ1bGwtcGF0aCBpbnN0YW5jZSB0eXBlIG5hbWVzLiBSZXNvbHV0aW9uIGlzXG5cdFx0XHQvLyBwYXRoLWF3YXJlIChoYXJkLWZhaWwgbGF3KTogYW1iaWd1aXR5IGJldHdlZW4gcmVhbCBncmFwaCB0eXBlc1xuXHRcdFx0Ly8gcmVjb3JkcyBhIGZhdGFsIGVycm9yIGluc3RlYWQgb2Ygc2lsZW50bHkgcGlja2luZyBvbmUuXG5cdFx0XHRjb25zdCBncmFwaFJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUodHlwZU5hbWUpO1xuXHRcdFx0aWYgKGdyYXBoUmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdFx0Y29uc3Qgc2ltcGxlUmVzdWx0ID0gdHlwZU5hbWU7XG5cdFx0XHRcdHJldHVybiBzaW1wbGVSZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAoZ3JhcGhSZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0XHR0aGlzLnJlY29yZEdyYXBoUmVmZXJlbmNlRXJyb3IodHlwZU5hbWUsIHR5cGVOb2RlLCBncmFwaFJlc3VsdCk7XG5cdFx0XHRcdGNvbnN0IHVua25vd25HcmFwaFJlc3VsdCA9ICd1bmtub3duJztcblx0XHRcdFx0cmV0dXJuIHVua25vd25HcmFwaFJlc3VsdDtcblx0XHRcdH1cblx0XHRcdC8vIElmIG5vdCBhbiBvYmplY3QgdHlwZSBhbGlhcywgcmV0dXJuIHRoZSB0eXBlIG5hbWUgd2l0aCBhcmdzXG5cdFx0XHRpZiAodHlwZU5vZGUudHlwZUFyZ3VtZW50cyAmJiB0eXBlTm9kZS50eXBlQXJndW1lbnRzLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0aWYgKEtOT1dOX0dMT0JBTF9UWVBFUy5oYXModHlwZU5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgYXJncyA9IHR5cGVOb2RlLnR5cGVBcmd1bWVudHMubWFwKGFyZyA9PiB0aGlzLmluZmVyVHlwZShhcmcpKTtcblx0XHRcdFx0XHRyZXR1cm4gYCR7dHlwZU5hbWUgIH08JHsgIGFyZ3Muam9pbignLCAnKSAgfT5gO1xuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIGdlbmVyaWMgcmVmZXJlbmNlIHRvIGEgbm9uLWdsb2JhbCwgbm9uLWdyYXBoIHR5cGUgY2Fubm90IGJlXG5cdFx0XHRcdC8vIGVtaXR0ZWQgYmFyZSBpbnRvIHRoZSBnZW5lcmF0ZWQgZmlsZVxuXHRcdFx0XHR0aGlzLnJlY29yZFBsYWluVHlwZVJlZmVyZW5jZVNpdGUodHlwZU5hbWUsIHR5cGVOb2RlKTtcblx0XHRcdFx0Y29uc3QgdW5rbm93bkdlbmVyaWNSZXN1bHQgPSAndW5rbm93bic7XG5cdFx0XHRcdHJldHVybiB1bmtub3duR2VuZXJpY1Jlc3VsdDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGZhbGxiYWNrUmVzdWx0ID0gdGhpcy51bnJlc29sdmVkVHlwZVJlZmVyZW5jZUZhbGxiYWNrKHR5cGVOYW1lLCB0eXBlTm9kZSk7XG5cdFx0XHRyZXR1cm4gZmFsbGJhY2tSZXN1bHQ7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHRcdFx0ICogRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZyb20gYSBjbGFzcy1saWtlIG5vZGUuXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q2xhc3NDb25zdHJ1Y3RvclBhcmFtcyAoY2xhc3NMaWtlOiB0cy5DbGFzc0RlY2xhcmF0aW9uIHwgdHMuQ2xhc3NFeHByZXNzaW9uKTpcblx0XHRDb25zdHJ1Y3RvclBhcmFtSW5mb1tdIHtcblx0XHRjb25zdCBwYXJhbXM6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10gPSBbXTtcblxuXHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGNsYXNzTGlrZS5tZW1iZXJzKSB7XG5cdFx0XHRpZiAoIXRzLmlzQ29uc3RydWN0b3JEZWNsYXJhdGlvbihtZW1iZXIpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXG5cdFx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIG1lbWJlci5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRcdGlmICghcGFyYW0ubmFtZSB8fCAhdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpKSBjb250aW51ZTtcblx0XHRcdFx0aWYgKCFwYXJhbS50eXBlKSBjb250aW51ZTtcblxuXHRcdFx0XHRjb25zdCBwYXJhbU5hbWUgPSBwYXJhbS5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IGV4cGFuZGVkVHlwZSA9IHRoaXMucmVzb2x2ZUNvbnN0cnVjdG9yUGFyYW1UeXBlKHBhcmFtLnR5cGUpIHx8IHRoaXMuaW5mZXJUeXBlKHBhcmFtLnR5cGUpO1xuXG5cdFx0XHRcdHBhcmFtcy5wdXNoKHtcblx0XHRcdFx0XHRuYW1lICAgICA6IHBhcmFtTmFtZSxcblx0XHRcdFx0XHR0eXBlICAgICA6IGV4cGFuZGVkVHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6ICEhcGFyYW0ucXVlc3Rpb25Ub2tlbiB8fCAhIXBhcmFtLmluaXRpYWxpemVyXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdFx0Ly8gT25seSBwcm9jZXNzIGZpcnN0IGNvbnN0cnVjdG9yXG5cdFx0XHRicmVhaztcblx0XHR9XG5cblx0XHRyZXR1cm4gcGFyYW1zO1xuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBkZWZpbmUoKSBjYWxsXG5cdFx0XHQgKiBUaGlzIGlzIHVzZWQgZm9yIFR5cGVSZWdpc3RyeSBjb25zdHJ1Y3RvciBzaWduYXR1cmVzXG5cdFx0XHQgKiBQcmVzZXJ2ZXMgcGFyYW1ldGVyIG5hbWVzIGFuZCBleHBhbmRzIG9iamVjdCB0eXBlcyB0byB0aGVpciBzdHJ1Y3R1cmVcblx0XHRcdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdIHtcblx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCk7XG5cdFx0aWYgKCFjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdHJldHVybiBbXTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JQYXJhbXNGcm9tQ29uc3RydWN0b3IoY29uc3RydWN0b3JFeHByKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBhIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24uXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JQYXJhbXNGcm9tQ29uc3RydWN0b3IgKGNvbnN0cnVjdG9yRXhwcjogdHMuRXhwcmVzc2lvbik6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10ge1xuXHRcdGNvbnN0IHBhcmFtczogQ29uc3RydWN0b3JQYXJhbUluZm9bXSA9IFtdO1xuXHRcblx0XHQvLyBIYW5kbGUgZnVuY3Rpb24gZXhwcmVzc2lvbiBvciBhcnJvdyBmdW5jdGlvblxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzQXJyb3dGdW5jdGlvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHQvLyBMb29rIGZvciBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIChzZWNvbmQgcGFyYW0gYWZ0ZXIgYHRoaXNgKVxuXHRcdFx0Ly8gUGF0dGVybnM6IGZ1bmN0aW9uKHRoaXM6IFR5cGUsIGRhdGE6IHsgLi4uIH0pIG9yICh0aGlzOiBUeXBlLCBkYXRhOiB7IC4uLiB9KSA9PlxuXHRcdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBjb25zdHJ1Y3RvckV4cHIucGFyYW1ldGVycy5sZW5ndGg7IGkrKykge1xuXHRcdFx0XHRjb25zdCBwYXJhbSA9IGNvbnN0cnVjdG9yRXhwci5wYXJhbWV0ZXJzWyBpIF07XG5cdFx0XHRcdGlmICghcGFyYW0udHlwZSkgY29udGludWU7XG5cdFxuXHRcdFx0XHQvLyBTa2lwIGB0aGlzYCBwYXJhbWV0ZXIgKGZpcnN0IHBhcmFtKVxuXHRcdFx0XHRpZiAoXG5cdFx0XHRcdFx0aSA9PT0gMCAmJlxuXHRcdFx0XHRcdHBhcmFtLm5hbWUua2luZCA9PT0gdHMuU3ludGF4S2luZC5JZGVudGlmaWVyICYmXG5cdFx0XHRcdFx0KHBhcmFtLm5hbWUgYXMgdHMuSWRlbnRpZmllcikudGV4dCA9PT0gJ3RoaXMnXG5cdFx0XHRcdCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFxuXHRcdFx0XHQvLyBHZXQgcGFyYW1ldGVyIG5hbWUgYW5kIGV4cGFuZCBpdHMgdHlwZVxuXHRcdFx0XHRjb25zdCBwYXJhbU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgPyBwYXJhbS5uYW1lLnRleHQgOiAnYXJnJztcblx0XHRcdFx0Y29uc3QgZXhwYW5kZWRUeXBlID0gdGhpcy5yZXNvbHZlQ29uc3RydWN0b3JQYXJhbVR5cGUocGFyYW0udHlwZSkgfHwgdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cdFx0XHRcdFx0XG5cdFx0XHRcdHBhcmFtcy5wdXNoKHtcblx0XHRcdFx0XHRuYW1lICAgICA6IHBhcmFtTmFtZSxcblx0XHRcdFx0XHR0eXBlICAgICA6IGV4cGFuZGVkVHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6ICEhcGFyYW0ucXVlc3Rpb25Ub2tlbiB8fCAhIXBhcmFtLmluaXRpYWxpemVyXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0Ly8gSGFuZGxlIGNsYXNzIGV4cHJlc3Npb24gLSBjaGVjayBjb25zdHJ1Y3RvciBtZXRob2Rcblx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Y29uc3QgY2xhc3NQYXJhbXMgPSB0aGlzLmV4dHJhY3RDbGFzc0NvbnN0cnVjdG9yUGFyYW1zKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGNsYXNzUGFyYW1zKSB7XG5cdFx0XHRcdHBhcmFtcy5wdXNoKHBhcmFtKTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcGFyYW1zO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgZnJhbWV3b3JrIGluc3RydW1lbnRhdGlvbiBwb2ludHMuIFB1cmVseSBzeW50YWN0aWM6IGhlcml0YWdlXG5cdCAqIGNsYXVzZXMsIGRlY29yYXRvciBhcHBsaWNhdGlvbiBzaXRlcywgcHJvdmlkZXItdG9rZW4gb2JqZWN0IGxpdGVyYWxzXG5cdCAqIGFuZCBjb25zdW1lci5hcHBseSgpLmZvclJvdXRlcygpIHdpcmluZy4gVGhlIHZvY2FidWxhcnkgY29tZXMgZnJvbVxuXHQgKiBwbHVnaW5zOyBpZGVudGlmaWVyIHRleHQgaXMgbWF0Y2hlZCBhcy1pcyDigJQgbm8gaW1wb3J0IHJlc29sdXRpb24sXG5cdCAqIHRoZSB0eXBlIGNoZWNrZXIgc3RheXMgdW51c2VkLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0SW5zdHJ1bWVudGF0aW9uIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbkNsYXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0XHRpZiAodHMuaXNEZWNvcmF0b3Iobm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbkRlY29yYXRvcihub2RlLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cdFx0aWYgKHRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvblByb3ZpZGVyKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uTWlkZGxld2FyZShub2RlLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGEgbmFtZWQgY2xhc3MgZGVjbGFyYXRpb24gZm9yIGluc3RydW1lbnRhdGlvbiBzaXRlIHJlc29sdXRpb25cblx0ICogYW5kIGRldGVjdCBoZXJpdGFnZS1iYXNlZCBraW5kcyAoYGltcGxlbWVudHMgPHBsdWdpbiBpbnRlcmZhY2U+YClcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEluc3RydW1lbnRhdGlvbkNsYXNzIChub2RlOiB0cy5DbGFzc0RlY2xhcmF0aW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCFub2RlLm5hbWUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgY2xhc3NOYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUubmFtZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHQvLyBGaXJzdCBsaW5lIG9mIHRoZSBkZWNsYXJhdGlvbiwgbGlrZSBFRFMgYGNvZGVgIHNuaXBwZXRzXG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zcGxpdCgnXFxuJylbIDAgXS5zbGljZSgwLCAxMDApO1xuXG5cdFx0bGV0IGtpbmQ6IEluc3RydW1lbnRhdGlvbktpbmQgfCB1bmRlZmluZWQ7XG5cdFx0aWYgKG5vZGUuaGVyaXRhZ2VDbGF1c2VzKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGNsYXVzZSBvZiBub2RlLmhlcml0YWdlQ2xhdXNlcykge1xuXHRcdFx0XHRpZiAoY2xhdXNlLnRva2VuICE9PSB0cy5TeW50YXhLaW5kLkltcGxlbWVudHNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Zm9yIChjb25zdCB0eXBlIG9mIGNsYXVzZS50eXBlcykge1xuXHRcdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHR5cGUuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCBtYXRjaGVkID0gdGhpcy5pbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5LmludGVyZmFjZXNbIHR5cGUuZXhwcmVzc2lvbi50ZXh0IF07XG5cdFx0XHRcdFx0aWYgKG1hdGNoZWQpIHtcblx0XHRcdFx0XHRcdGtpbmQgPSBtYXRjaGVkO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGNvbnN0IGRlY2w6IEluc3RydW1lbnRhdGlvbkNsYXNzRGVjbCA9IHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0Y29kZSxcblx0XHR9O1xuXHRcdGlmIChraW5kKSB7XG5cdFx0XHRkZWNsLmtpbmQgPSBraW5kO1xuXHRcdH1cblx0XHR0aGlzLmluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMuc2V0KGNsYXNzTmFtZSwgZGVjbCk7XG5cdH1cblxuXHQvKipcblx0ICogRGV0ZWN0IGRlY29yYXRvciBhcHBsaWNhdGlvbiBzaXRlczogcGx1Z2luLWxpc3RlZCBkZWNvcmF0b3JzIGFwcGxpZWRcblx0ICogd2l0aCBjbGFzcyBhcmd1bWVudHMgb24gYSBjbGFzcyBvciBvbmUgb2YgaXRzIG1ldGhvZHMuIE9uZSBzaXRlIHBlclxuXHQgKiByZWZlcmVuY2VkIGNsYXNzIGlkZW50aWZpZXIuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25EZWNvcmF0b3IgKG5vZGU6IHRzLkRlY29yYXRvciwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24oZXhwcmVzc2lvbikgfHwgIXRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGtpbmQgPSB0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkudXNlRGVjb3JhdG9yc1sgZXhwcmVzc2lvbi5leHByZXNzaW9uLnRleHQgXTtcblx0XHRpZiAoIWtpbmQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBUaGUgZGVjb3JhdG9yJ3MgcGFyZW50IGlzIHRoZSBkZWNvcmF0ZWQgbm9kZTogYSBjb250cm9sbGVyIGNsYXNzLFxuXHRcdC8vIG9uZSBvZiBpdHMgbWV0aG9kcywgb3Igb25lIG9mIGl0cyBtZXRob2QgcGFyYW1ldGVyc1xuXHRcdC8vIChAQm9keShtdnAuZm9yVHlwZShEdG8pKSBvbiBhIGhhbmRsZXIgYXJndW1lbnQpXG5cdFx0Y29uc3QgZGVjb3JhdGVkID0gbm9kZS5wYXJlbnQ7XG5cdFx0bGV0IHNjb3BlOiBJbnN0cnVtZW50YXRpb25TY29wZTtcblx0XHRsZXQgdGFyZ2V0czogc3RyaW5nW107XG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihkZWNvcmF0ZWQpICYmIGRlY29yYXRlZC5uYW1lKSB7XG5cdFx0XHRzY29wZSA9IGBjb250cm9sbGVyOiR7ZGVjb3JhdGVkLm5hbWUudGV4dH1gO1xuXHRcdFx0dGFyZ2V0cyA9IFsgZGVjb3JhdGVkLm5hbWUudGV4dCBdO1xuXHRcdH0gZWxzZSBpZiAoXG5cdFx0XHR0cy5pc01ldGhvZERlY2xhcmF0aW9uKGRlY29yYXRlZCkgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcihkZWNvcmF0ZWQubmFtZSkgJiZcblx0XHRcdHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihkZWNvcmF0ZWQucGFyZW50KSAmJlxuXHRcdFx0ZGVjb3JhdGVkLnBhcmVudC5uYW1lXG5cdFx0KSB7XG5cdFx0XHRjb25zdCBjbGFzc05hbWUgPSBkZWNvcmF0ZWQucGFyZW50Lm5hbWUudGV4dDtcblx0XHRcdHNjb3BlID0gYG1ldGhvZDoke2NsYXNzTmFtZX0uJHtkZWNvcmF0ZWQubmFtZS50ZXh0fWA7XG5cdFx0XHR0YXJnZXRzID0gWyBjbGFzc05hbWUgXTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzUGFyYW1ldGVyKGRlY29yYXRlZCkpIHtcblx0XHRcdC8vIFBhcmFtZXRlciBkZWNvcmF0b3JzIHRha2UgdGhlIGVuY2xvc2luZyBtZXRob2QncyBzY29wZSDigJQgdGhlXG5cdFx0XHQvLyBhdHRhY2htZW50IHBvaW50IGlzIHRoZSBoYW5kbGVyLCBub3QgdGhlIGFyZ3VtZW50IG5hbWU7IHRoZVxuXHRcdFx0Ly8gc2FtZSBtZXRob2Q6Q2xhc3MubWV0aG9kIGZvcm0gYXMgbWV0aG9kLWxldmVsIHNpdGVzLiBQYXJhbXMgb2Zcblx0XHRcdC8vIGNvbnN0cnVjdG9ycywgZnVuY3Rpb25zLCBhbmQgdW5uYW1lYWJsZSBob3N0cyBzdGF5IHNpbGVudCwgdGhlXG5cdFx0XHQvLyBzYW1lIGNvbnZlbnRpb24gYXMgb3RoZXIgdW5yZXNvbHZhYmxlIGRlY29yYXRvciBwYXJlbnRzXG5cdFx0XHRjb25zdCBob3N0ID0gZGVjb3JhdGVkLnBhcmVudDtcblx0XHRcdGlmIChcblx0XHRcdFx0aG9zdCAmJlxuXHRcdFx0XHR0cy5pc01ldGhvZERlY2xhcmF0aW9uKGhvc3QpICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihob3N0Lm5hbWUpICYmXG5cdFx0XHRcdHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihob3N0LnBhcmVudCkgJiZcblx0XHRcdFx0aG9zdC5wYXJlbnQubmFtZVxuXHRcdFx0KSB7XG5cdFx0XHRcdGNvbnN0IGNsYXNzTmFtZSA9IGhvc3QucGFyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0c2NvcGUgPSBgbWV0aG9kOiR7Y2xhc3NOYW1lfS4ke2hvc3QubmFtZS50ZXh0fWA7XG5cdFx0XHRcdHRhcmdldHMgPSBbIGNsYXNzTmFtZSBdO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0Zm9yIChjb25zdCBhcmcgb2YgZXhwcmVzc2lvbi5hcmd1bWVudHMpIHtcblx0XHRcdC8vIENsYXNzIHJlZmVyZW5jZTogQFJlZ2lzdGVyKEltcGwpIG9yIGFuIGlubGluZSBpbnN0YW5jZTpcblx0XHRcdC8vIEBSZWdpc3RlcihuZXcgSW1wbCh7IC4uLm9wdGlvbnMgfSkpXG5cdFx0XHRsZXQgY2xhc3NOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdFx0XHQvLyBwZXItYXJnIGtpbmQ6IGZhY3RvcnktY2FsbCBhcmdzIGNhcnJ5IHRoZWlyIG93biBjb25maWd1cmVkXG5cdFx0XHQvLyBraW5kLCBldmVyeXRoaW5nIGVsc2UgdGFrZXMgdGhlIGRlY29yYXRvcidzXG5cdFx0XHRsZXQgYXJnS2luZCA9IGtpbmQ7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdFx0Y2xhc3NOYW1lID0gYXJnLnRleHQ7XG5cdFx0XHR9IGVsc2UgaWYgKHRzLmlzTmV3RXhwcmVzc2lvbihhcmcpICYmIHRzLmlzSWRlbnRpZmllcihhcmcuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y2xhc3NOYW1lID0gYXJnLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdH0gZWxzZSBpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihhcmcpICYmIHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFyZy5leHByZXNzaW9uKSkge1xuXHRcdFx0XHQvLyBQaXBlLWZhY3Rvcnkgc2hhcGU6IEBVc2VQaXBlcyhtdnAuZm9yVHlwZShEdG8pKSDigJQgdGhlXG5cdFx0XHRcdC8vIGNhbGwncyBtZXRob2QgbmFtZSBpcyBwbHVnaW4tbGlzdGVkLCB0aGUgdGFyZ2V0IGNsYXNzIHNpdHNcblx0XHRcdFx0Ly8gaW4gdGhlIGNvbmZpZ3VyZWQgYXJndW1lbnQgcG9zaXRpb24gKGRlZmF1bHQgMClcblx0XHRcdFx0Y29uc3QgZmFjdG9yeSA9IHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS5kZWNvcmF0b3JBcmdGYWN0b3JpZXNbIGFyZy5leHByZXNzaW9uLm5hbWUudGV4dCBdO1xuXHRcdFx0XHRpZiAoZmFjdG9yeSkge1xuXHRcdFx0XHRcdGNvbnN0IHRhcmdldEFyZyA9IGFyZy5hcmd1bWVudHNbIGZhY3RvcnkudGFyZ2V0QXJnID8/IDAgXTtcblx0XHRcdFx0XHRpZiAodGFyZ2V0QXJnICYmIHRzLmlzSWRlbnRpZmllcih0YXJnZXRBcmcpKSB7XG5cdFx0XHRcdFx0XHRjbGFzc05hbWUgPSB0YXJnZXRBcmcudGV4dDtcblx0XHRcdFx0XHRcdGFyZ0tpbmQgPSBmYWN0b3J5LmtpbmQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAoIWNsYXNzTmFtZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uU2l0ZXMucHVzaCh7XG5cdFx0XHRcdGtpbmQgOiBhcmdLaW5kLFxuXHRcdFx0XHRjbGFzc05hbWUsXG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRzY29wZSxcblx0XHRcdFx0dGFyZ2V0cyxcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgZ2xvYmFsIHJlZ2lzdHJhdGlvbnM6IG9iamVjdCBsaXRlcmFscyBzaGFwZWQgbGlrZVxuXHQgKiBgeyBwcm92aWRlOiA8cGx1Z2luLWxpc3RlZCB0b2tlbj4sIHVzZUNsYXNzOiBYIH1gLlxuXHQgKiB1c2VFeGlzdGluZy91c2VGYWN0b3J5IHdpdGhvdXQgYSB1c2VDbGFzcyBpZGVudGlmaWVyIGFyZSBub3Rcblx0ICogc3RhdGljYWxseSBvYnZpb3VzIOKAlCBza2lwcGVkIHJhdGhlciB0aGFuIGd1ZXNzZWQuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25Qcm92aWRlciAobm9kZTogdHMuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRsZXQga2luZDogSW5zdHJ1bWVudGF0aW9uS2luZCB8IHVuZGVmaW5lZDtcblx0XHRsZXQgdXNlQ2xhc3NOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cblx0XHRmb3IgKGNvbnN0IHByb3Agb2Ygbm9kZS5wcm9wZXJ0aWVzKSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdCF0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSB8fFxuXHRcdFx0XHQhdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkgfHxcblx0XHRcdFx0IXRzLmlzSWRlbnRpZmllcihwcm9wLmluaXRpYWxpemVyKVxuXHRcdFx0KSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHByb3AubmFtZS50ZXh0ID09PSAncHJvdmlkZScpIHtcblx0XHRcdFx0a2luZCA9IHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS5hcHBUb2tlbnNbIHByb3AuaW5pdGlhbGl6ZXIudGV4dCBdO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHByb3AubmFtZS50ZXh0ID09PSAndXNlQ2xhc3MnKSB7XG5cdFx0XHRcdHVzZUNsYXNzTmFtZSA9IHByb3AuaW5pdGlhbGl6ZXIudGV4dDtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRpZiAoIWtpbmQgfHwgIXVzZUNsYXNzTmFtZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uU2l0ZXMucHVzaCh7XG5cdFx0XHRraW5kLFxuXHRcdFx0Y2xhc3NOYW1lIDogdXNlQ2xhc3NOYW1lLFxuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRjb2RlLFxuXHRcdFx0c2NvcGUgICAgIDogJ2dsb2JhbCcsXG5cdFx0XHR0YXJnZXRzICAgOiBbXSxcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgbWlkZGxld2FyZSB3aXJpbmc6IGBjb25zdW1lci5hcHBseShNdzEsIE13MikuZm9yUm91dGVzKC4uLilgXG5cdCAqIGluc2lkZSBhIGNsYXNzJ3MgY29uZmlndXJlKCkgbWV0aG9kLiBUYXJnZXRzIGNvbWUgZnJvbSBmb3JSb3V0ZXNcblx0ICogYXJndW1lbnRzIHdoZW4gc3RhdGljYWxseSByZWFkYWJsZSAoc3RyaW5nIHJvdXRlcyBvciBjb250cm9sbGVyXG5cdCAqIGlkZW50aWZpZXJzKSwgZWxzZSBbXS4gU2hhcGUtYmFzZWQsIHNvIGEgcGx1Z2luIG11c3Qgb3B0IGluIHZpYVxuXHQgKiBgbWlkZGxld2FyZVdpcmluZzogdHJ1ZWAuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25NaWRkbGV3YXJlIChub2RlOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdGhpcy5pbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5Lm1pZGRsZXdhcmVXaXJpbmcpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKFxuXHRcdFx0IXRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG5vZGUuZXhwcmVzc2lvbikgfHxcblx0XHRcdG5vZGUuZXhwcmVzc2lvbi5uYW1lLnRleHQgIT09ICdmb3JSb3V0ZXMnXG5cdFx0KSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGFwcGx5Q2FsbCA9IG5vZGUuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdGlmIChcblx0XHRcdCF0cy5pc0NhbGxFeHByZXNzaW9uKGFwcGx5Q2FsbCkgfHxcblx0XHRcdCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcHBseUNhbGwuZXhwcmVzc2lvbikgfHxcblx0XHRcdGFwcGx5Q2FsbC5leHByZXNzaW9uLm5hbWUudGV4dCAhPT0gJ2FwcGx5J1xuXHRcdCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAoIXRoaXMuaXNJbnNpZGVDb25maWd1cmVNZXRob2Qobm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB0YXJnZXRzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgYXJnIG9mIG5vZGUuYXJndW1lbnRzKSB7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykgfHwgdHMuaXNTdHJpbmdMaXRlcmFsKGFyZykpIHtcblx0XHRcdFx0dGFyZ2V0cy5wdXNoKGFyZy50ZXh0KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0YXBwbHlDYWxsLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdGZvciAoY29uc3QgYXJnIG9mIGFwcGx5Q2FsbC5hcmd1bWVudHMpIHtcblx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHR0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzLnB1c2goe1xuXHRcdFx0XHRraW5kICAgICAgOiAnbWlkZGxld2FyZScsXG5cdFx0XHRcdGNsYXNzTmFtZSA6IGFyZy50ZXh0LFxuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0c2NvcGUgICAgIDogJ21vZHVsZScsXG5cdFx0XHRcdHRhcmdldHMsXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogV2FsayB1cCB0aGUgcGFyZW50IGNoYWluIGxvb2tpbmcgZm9yIGFuIGVuY2xvc2luZyBjb25maWd1cmUoKSBtZXRob2Rcblx0ICovXG5cdHByaXZhdGUgaXNJbnNpZGVDb25maWd1cmVNZXRob2QgKG5vZGU6IHRzLk5vZGUpOiBib29sZWFuIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5vZGUucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24oY3VycmVudCkgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGN1cnJlbnQubmFtZSkgJiZcblx0XHRcdFx0Y3VycmVudC5uYW1lLnRleHQgPT09ICdjb25maWd1cmUnXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxufVxuIl19