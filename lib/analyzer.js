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
        while (ts.isAsExpression(initializer) || ts.isSatisfiesExpression(initializer)) {
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
     * a plain literal (optionally wrapped in `as const` / `satisfies`) —
     * string, numeric, boolean, or null. Spreads, identifiers, and nested
     * arrays mean the union is not statically visible and yield undefined,
     * so the caller degrades the field to `unknown` rather than guessing.
     */
    literalTypesOfArray(arrayLiteral) {
        const literals = [];
        for (const element of arrayLiteral.elements) {
            if (ts.isSpreadElement(element)) {
                return undefined;
            }
            let expr = element;
            while (ts.isAsExpression(expr) || ts.isSatisfiesExpression(expr)) {
                expr = expr.expression;
            }
            if (ts.isStringLiteral(expr) || ts.isNoSubstitutionTemplateLiteral(expr)) {
                literals.push(`'${expr.text}'`);
            }
            else if (ts.isNumericLiteral(expr)) {
                literals.push(expr.text);
            }
            else if (expr.kind === ts.SyntaxKind.TrueKeyword) {
                literals.push('true');
            }
            else if (expr.kind === ts.SyntaxKind.FalseKeyword) {
                literals.push('false');
            }
            else if (expr.kind === ts.SyntaxKind.NullKeyword) {
                literals.push('null');
            }
            else {
                return undefined;
            }
        }
        if (literals.length === 0) {
            return undefined;
        }
        const result = literals;
        return result;
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
        // For chained calls like const X = define('A').define('B'), we want to map X -> A (the root)
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
                    // If this is a chained call (has parent), don't overwrite existing mapping
                    // The first define in the chain sets the mapping to the root type
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
        // Walk up the tree to find VariableDeclaration
        let current = call.parent;
        while (current) {
            if (ts.isVariableDeclaration(current)) {
                // Found: const X = lookup(...)
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
        * Track variable assignments from new Type() calls
        * e.g., const user = new UserType() maps "user" -> "UserType"
        */
    trackNewAssignment(newExpr, typePath) {
        // Walk up the tree to find VariableDeclaration
        let current = newExpr.parent;
        while (current) {
            if (ts.isVariableDeclaration(current)) {
                // Found: const X = new Type(...)
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
                // `typeof constArray[K]` — element type of a tracked const array:
                // emit the element literal union directly (assembling
                // `union[K]` text would misread precedence, and when the const
                // is not statically visible the honest answer is `unknown`,
                // never a bare `typeof name` query)
                if (ts.isTypeQueryNode(indexed.objectType) && ts.isIdentifier(indexed.objectType.exprName)) {
                    const queryName = indexed.objectType.exprName.text;
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
                let objectType = this.inferType(indexed.objectType);
                const indexType = this.inferType(indexed.indexType);
                // If objectType is 'object', try to resolve the underlying referenced type
                if (objectType === 'object' && ts.isTypeReferenceNode(indexed.objectType)) {
                    const refName = ts.isIdentifier(indexed.objectType.typeName) ? indexed.objectType.typeName.text : '';
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
            return undefined;
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
            const annotationType = this.resolveParameterAnnotationTypePath(name, from);
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
                    const graphResult = this.resolveGraphTypeName(param.type.typeName.text);
                    if (graphResult.status === 'unique') {
                        const result = graphResult.node.fullPath;
                        return result;
                    }
                }
                return undefined;
            }
            current = current.parent;
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYW5hbHl6ZXIuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvYW5hbHl6ZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFFYiwrQ0FBaUM7QUFDakMsK0NBQWlDO0FBT2pDLG1DQUVpQjtBQUNqQix1Q0FFbUI7QUErRG5COzs7R0FHRztBQUNILE1BQU0sa0JBQWtCLEdBQUcsSUFBSSxHQUFHLENBQUM7SUFDbEMsTUFBTSxFQUFFLFFBQVEsRUFBRSxPQUFPLEVBQUUsV0FBVyxFQUFFLFlBQVksRUFBRSxnQkFBZ0I7SUFDdEUsYUFBYSxFQUFFLFdBQVcsRUFBRSxVQUFVLEVBQUUsZ0JBQWdCO0lBQ3hELEtBQUssRUFBRSxLQUFLLEVBQUUsU0FBUyxFQUFFLFNBQVMsRUFBRSxTQUFTLEVBQUUsc0JBQXNCO0lBQ3JFLFNBQVMsRUFBRSxPQUFPLEVBQUUsZUFBZSxFQUFFLFFBQVEsRUFBRSxTQUFTLEVBQUUsVUFBVTtJQUNwRSxVQUFVLEVBQUUsTUFBTSxFQUFFLE1BQU0sRUFBRSxTQUFTLEVBQUUsU0FBUyxFQUFFLGFBQWE7SUFDL0QsWUFBWSxFQUFFLGNBQWMsRUFBRSxZQUFZLEVBQUUsdUJBQXVCO0lBQ25FLFVBQVUsRUFBRSxtQkFBbUIsRUFBRSxtQkFBbUI7SUFDcEQsV0FBVyxFQUFFLFdBQVcsRUFBRSxZQUFZLEVBQUUsY0FBYztJQUN0RCxRQUFRLEVBQUUsUUFBUSxFQUFFLFNBQVMsRUFBRSxRQUFRLEVBQUUsUUFBUSxFQUFFLFFBQVEsRUFBRSxVQUFVO0lBQ3ZFLFVBQVUsRUFBRSxVQUFVLEVBQUUsV0FBVyxFQUFFLGVBQWUsRUFBRSxlQUFlO0lBQ3JFLGdCQUFnQixFQUFFLGtCQUFrQixFQUFFLHVCQUF1QjtJQUM3RCxhQUFhLEVBQUUsYUFBYSxFQUFFLG1CQUFtQixFQUFFLFVBQVU7SUFDN0QsV0FBVyxFQUFFLFlBQVksRUFBRSxtQkFB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Z0JBQ3hCLFNBQVMsRUFBRyxHQUFHLENBQUMsSUFBSTtnQkFDcEIsUUFBUTtnQkFDUixJQUFJO2dCQUNKLEtBQUssRUFBTyxRQUFRO2dCQUNwQixPQUFPO2FBQ1AsQ0FBQyxDQUFDO1FBQ0osQ0FBQztJQUNGLENBQUM7SUFFRDs7T0FFRztJQUNLLHVCQUF1QixDQUFFLElBQWE7UUFDN0MsSUFBSSxPQUFPLEdBQXdCLElBQUksQ0FBQyxNQUFNLENBQUM7UUFDL0MsT0FBTyxPQUFPLEVBQUUsQ0FBQztZQUNoQixJQUNDLEVBQUUsQ0FBQyxtQkFBbUIsQ0FBQyxPQUFPLENBQUM7Z0JBQy9CLEVBQUUsQ0FBQyxZQUFZLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQztnQkFDN0IsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssV0FBVyxFQUNoQyxDQUFDO2dCQUNGLE9BQU8sSUFBSSxDQUFDO1lBQ2IsQ0FBQztZQUNELE9BQU8sR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDO1FBQzFCLENBQUM7UUFDRCxPQUFPLEtBQUssQ0FBQztJQUNkLENBQUM7Q0FDRDtBQXp1S0QsOENBeXVLQyIsInNvdXJjZXNDb250ZW50IjpbIid1c2Ugc3RyaWN0JztcblxuaW1wb3J0ICogYXMgbm9kZVBhdGggZnJvbSAncGF0aCc7XG5pbXBvcnQgKiBhcyB0cyBmcm9tICd0eXBlc2NyaXB0JztcbmltcG9ydCB7XG5cdFR5cGVOb2RlLCBQcm9wZXJ0eUluZm8sIEFuYWx5emVSZXN1bHQsIEFuYWx5emVFcnJvcixcblx0RGVmaW5pdGlvbkluZm8sIFVzYWdlSW5mbywgQ29uc3RydWN0b3JQYXJhbUluZm8sXG5cdEVEU0luZm8sIEZsb3dJbmZvLCBJbnN0cnVtZW50YXRpb25LaW5kLCBJbnN0cnVtZW50YXRpb25Qb2ludCxcblx0SW5zdHJ1bWVudGF0aW9uU2NvcGUsIFJlc29sdXRpb25FcnJvclxufSBmcm9tICcuL3R5cGVzJztcbmltcG9ydCB7XG5cdFR5cGVHcmFwaEltcGwsIHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UsIEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCBcbn0gZnJvbSAnLi9ncmFwaCc7XG5pbXBvcnQge1xuXHRJbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5LCBUYWN0aWNhUGx1Z2luLCBtZXJnZVRhY3RpY2FQbHVnaW5zXG59IGZyb20gJy4vcGx1Z2lucyc7XG5cbmludGVyZmFjZSBDb2xsZWN0aW9uSW5mbyB7XG5cdHZhcmlhYmxlTmFtZTogc3RyaW5nO1xuXHRzb3VyY2VGaWxlOiBzdHJpbmc7XG5cdHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZT86IHN0cmluZztcbn1cblxuLyoqXG4gKiBMb2NhdGlvbi9jb2RlIGNhcHR1cmVkIGF0IGEgY2xhc3MgZGVjbGFyYXRpb24sIHVzZWQgdG8gcmVzb2x2ZVxuICogaW5zdHJ1bWVudGF0aW9uIHJlZ2lzdHJhdGlvbiBzaXRlcyB0byB0aGUgZGVjbGFyZWQgY2xhc3NcbiAqL1xuaW50ZXJmYWNlIEluc3RydW1lbnRhdGlvbkNsYXNzRGVjbCB7XG5cdGtpbmQ/OiBJbnN0cnVtZW50YXRpb25LaW5kO1xuXHRsb2NhdGlvbjogc3RyaW5nO1xuXHRjb2RlOiBzdHJpbmc7XG59XG5cbi8qKlxuICogUmF3IHJlZ2lzdHJhdGlvbiBzaXRlIChkZWNvcmF0b3IsIEFQUF8qIHByb3ZpZGVyLCBjb25zdW1lci5hcHBseSkuXG4gKiBMb2NhdGlvbi9jb2RlIGFyZSB0aGUgc2l0ZSdzIG93bjsgZ2V0SW5zdHJ1bWVudGF0aW9uUG9pbnRzKCkgcmV3cml0ZXNcbiAqIHRoZW0gdG8gdGhlIGNsYXNzIGRlY2xhcmF0aW9uIHdoZW4gdGhlIGNsYXNzIGlzIGRlY2xhcmVkIGluLXByb2plY3QuXG4gKi9cbmludGVyZmFjZSBJbnN0cnVtZW50YXRpb25TaXRlIHtcblx0a2luZDogSW5zdHJ1bWVudGF0aW9uS2luZDtcblx0Y2xhc3NOYW1lOiBzdHJpbmc7XG5cdGxvY2F0aW9uOiBzdHJpbmc7XG5cdGNvZGU6IHN0cmluZztcblx0c2NvcGU6IEluc3RydW1lbnRhdGlvblNjb3BlO1xuXHR0YXJnZXRzOiBzdHJpbmdbXTtcbn1cblxuLyoqXG4gKiBBIG5hbWVkIHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbiAodHlwZSBhbGlhcywgY2xhc3MsIG9yIGludGVyZmFjZSlcbiAqIHJlY29yZGVkIHBlciBmaWxlLCBzbyByZWZlcmVuY2VzIGNhbiBiZSByZXNvbHZlZCB0aHJvdWdoIHRoZSBpbXBvcnRpbmdcbiAqIGZpbGUncyBvd24gaW1wb3J0cyBpbnN0ZWFkIG9mIGEgcHJvZ3JhbS13aWRlIGxhc3Qtd2lucyBuYW1lIG1hcCAoRjEwKS5cbiAqL1xuaW50ZXJmYWNlIFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24ge1xuXHRraW5kOiAnYWxpYXMnIHwgJ2NsYXNzJyB8ICdpbnRlcmZhY2UnO1xuXHRub2RlOiB0cy5UeXBlQWxpYXNEZWNsYXJhdGlvbiB8IHRzLkNsYXNzRGVjbGFyYXRpb24gfCB0cy5JbnRlcmZhY2VEZWNsYXJhdGlvbjtcblx0LyoqIGZpbGUgdGhhdCBkZWNsYXJlcyB0aGUgdHlwZSDigJQgbmVzdGVkIHJlZmVyZW5jZXMgcmVzb2x2ZSBhZ2FpbnN0IGl0ICovXG5cdGZpbGU6IHN0cmluZztcbn1cblxuLyoqXG4gKiBPbmUgaW1wb3J0IGJpbmRpbmcgb2YgYSByZWZlcmVuY2VkIHR5cGU6IHRoZSBsb2NhbCBuYW1lIHVuZGVyIHdoaWNoIHRoZVxuICogZmlsZSBrbm93cyBpdCwgdGhlIG9yaWdpbmFsIGV4cG9ydGVkIG5hbWUgaW4gdGhlIHNvdXJjZSBtb2R1bGUsIGFuZCB0aGVcbiAqIHNwZWNpZmllciBpdCBjYW1lIGZyb20uXG4gKi9cbmludGVyZmFjZSBSZWZlcmVuY2VkVHlwZUltcG9ydCB7XG5cdG9yaWdpbmFsTmFtZTogc3RyaW5nO1xuXHRzcGVjaWZpZXI6IHN0cmluZztcblx0aXNOYW1lc3BhY2U6IGJvb2xlYW47XG59XG5cbi8qKlxuICogUmVzdWx0IG9mIHJlc29sdmluZyBvbmUgbW9kdWxlIHNwZWNpZmllciBmcm9tIG9uZSBjb250YWluaW5nIGZpbGUuXG4gKi9cbmludGVyZmFjZSBSZWZlcmVuY2VkVHlwZVJlc29sdXRpb24ge1xuXHRyZXNvbHZlZFBhdGg6IHN0cmluZztcblx0aXNFeHRlcm5hbDogYm9vbGVhbjtcbn1cblxuLyoqXG4gKiBHbG9iYWwvYnVpbHRpbiB0eXBlIG5hbWVzIHRoYXQgYXJlIHNhZmUgdG8gZW1pdCBiYXJlIGludG8gZ2VuZXJhdGVkIGZpbGVzXG4gKiDigJQgdGhleSByZXNvbHZlIGluIGFueSBUeXBlU2NyaXB0IGNvbXBpbGF0aW9uIHdpdGhvdXQgYW4gaW1wb3J0LlxuICovXG5jb25zdCBLTk9XTl9HTE9CQUxfVFlQRVMgPSBuZXcgU2V0KFtcblx0J0RhdGUnLCAnUmVnRXhwJywgJ0Vycm9yJywgJ0V2YWxFcnJvcicsICdSYW5nZUVycm9yJywgJ1JlZmVyZW5jZUVycm9yJyxcblx0J1N5bnRheEVycm9yJywgJ1R5cGVFcnJvcicsICdVUklFcnJvcicsICdBZ2dyZWdhdGVFcnJvcicsXG5cdCdNYXAnLCAnU2V0JywgJ1dlYWtNYXAnLCAnV2Vha1NldCcsICdXZWFrUmVmJywgJ0ZpbmFsaXphdGlvblJlZ2lzdHJ5Jyxcblx0J1Byb21pc2UnLCAnQXJyYXknLCAnUmVhZG9ubHlBcnJheScsICdSZWNvcmQnLCAnUGFydGlhbCcsICdSZXF1aXJlZCcsXG5cdCdSZWFkb25seScsICdQaWNrJywgJ09taXQnLCAnRXhjbHVkZScsICdFeHRyYWN0JywgJ05vbk51bGxhYmxlJyxcblx0J1JldHVyblR5cGUnLCAnSW5zdGFuY2VUeXBlJywgJ1BhcmFtZXRlcnMnLCAnQ29uc3RydWN0b3JQYXJhbWV0ZXJzJyxcblx0J1RoaXNUeXBlJywgJ1RoaXNQYXJhbWV0ZXJUeXBlJywgJ09taXRUaGlzUGFyYW1ldGVyJyxcblx0J1VwcGVyY2FzZScsICdMb3dlcmNhc2UnLCAnQ2FwaXRhbGl6ZScsICdVbmNhcGl0YWxpemUnLFxuXHQnU3RyaW5nJywgJ051bWJlcicsICdCb29sZWFuJywgJ1N5bWJvbCcsICdCaWdJbnQnLCAnT2JqZWN0JywgJ0Z1bmN0aW9uJyxcblx0J0l0ZXJhYmxlJywgJ0l0ZXJhdG9yJywgJ0dlbmVyYXRvcicsICdBc3luY0l0ZXJhYmxlJywgJ0FzeW5jSXRlcmF0b3InLFxuXHQnQXN5bmNHZW5lcmF0b3InLCAnSXRlcmFibGVJdGVyYXRvcicsICdBc3luY0l0ZXJhYmxlSXRlcmF0b3InLFxuXHQnUHJvcGVydHlLZXknLCAnQXJyYXlCdWZmZXInLCAnU2hhcmVkQXJyYXlCdWZmZXInLCAnRGF0YVZpZXcnLFxuXHQnSW50OEFycmF5JywgJ1VpbnQ4QXJyYXknLCAnVWludDhDbGFtcGVkQXJyYXknLCAnSW50MTZBcnJheScsXG5cdCdVaW50MTZBcnJheScsICdJbnQzMkFycmF5JywgJ1VpbnQzMkFycmF5JywgJ0Zsb2F0MzJBcnJheScsXG5cdCdGbG9hdDY0QXJyYXknLCAnQmlnSW50NjRBcnJheScsICdCaWdVaW50NjRBcnJheScsICdJbnRsJ1xuXSk7XG5cbi8vIEJvdW5kIGZvciBjaGFzaW5nIHJlLWV4cG9ydCBiYXJyZWxzIChleHBvcnQgeyBYIH0gZnJvbSAn4oCmJywgZXhwb3J0ICogZnJvbSAn4oCmJylcbmNvbnN0IE1BWF9SRUVYUE9SVF9DSEFTRV9ERVBUSCA9IDU7XG4vLyBCb3VuZCBmb3Igd2Fsa2luZyBjbGFzcy9pbnRlcmZhY2UgZXh0ZW5kcyBjaGFpbnMgZHVyaW5nIHJlZmVyZW5jZWQtdHlwZVxuLy8gZXhwYW5zaW9uIChpbmhlcml0ZWQgbWVtYmVycyBtZXJnZSBpbnRvIHRoZSBleHBhbmRlZCBmaWVsZHMpXG5jb25zdCBNQVhfSEVSSVRBR0VfREVQVEggPSA4O1xuXG4vKipcbiAqIEFTVCBBbmFseXplciBmb3IgZmluZGluZyBNbmVtb25pY2EgZGVmaW5lKCkgYW5kIGRlY29yYXRlKCkgY2FsbHNcbiAqXG4gKiBGcmFtZXdvcmstYmxpbmQgYnkgY29uc3RydWN0aW9uOiBpbnN0cnVtZW50YXRpb24gZGV0ZWN0aW9uIHZvY2FidWxhcnlcbiAqIChpbnRlcmZhY2UgbmFtZXMsIGRlY29yYXRvciBuYW1lcywgcHJvdmlkZXIgdG9rZW5zLCBtaWRkbGV3YXJlIHdpcmluZylcbiAqIGNvbWVzIGVudGlyZWx5IGZyb20gcGx1Z2lucyDigJQgd2l0aCBub25lIGxvYWRlZCwgemVybyBwb2ludHMgYXJlIGNvbGxlY3RlZC5cbiAqL1xuZXhwb3J0IGNsYXNzIE1uZW1vbmljYUFuYWx5emVyIHtcblx0cHJpdmF0ZSBlcnJvcnM6IEFuYWx5emVFcnJvcltdID0gW107XG5cdHByaXZhdGUgZ3JhcGggPSBuZXcgVHlwZUdyYXBoSW1wbCgpO1xuXHRwcml2YXRlIGRlZmluaXRpb25zID0gbmV3IE1hcDxzdHJpbmcsIERlZmluaXRpb25JbmZvPigpO1xuXHRwcml2YXRlIHVzYWdlcyA9IG5ldyBNYXA8c3RyaW5nLCBVc2FnZUluZm9bXT4oKTtcblx0cHJpdmF0ZSBlZHNVc2FnZXMgPSBuZXcgTWFwPHN0cmluZywgRURTSW5mb1tdPigpO1xuXHRwcml2YXRlIGZsb3dVc2FnZXMgPSBuZXcgTWFwPHN0cmluZywgRmxvd0luZm9bXT4oKTtcblx0Ly8gRW5jbG9zaW5nIG1uZW1vbmljYSBzY29wZSBmb3IgRURTIGtleWluZzogZGVmaW5lKCkvbGF6eSgpIGNhbGwgbm9kZVxuXHQvLyBvciBAZGVjb3JhdGUoKS1lZCBjbGFzcyBkZWNsYXJhdGlvbiAtPiBmdWxsUGF0aCBvZiB0aGUgdHlwZSBpdCBvd25zLlxuXHQvLyBQb3B1bGF0ZWQgb24gdGhlIGRlZmluaXRpb25zIHBhc3M7IEFTVCBub2RlcyBwZXJzaXN0IGFjcm9zcyBwYXNzZXMsXG5cdC8vIHNvIGVudHJpZXMgc3RheSB2YWxpZCBhZnRlciByZXNldFVzYWdlcygpLlxuXHRwcml2YXRlIGVkc1Njb3BlQnlOb2RlID0gbmV3IE1hcDx0cy5Ob2RlLCBzdHJpbmc+KCk7XG5cdC8vIFNhbWUtZmlsZSBmdW5jdGlvbiBiaW5kaW5ncyAoYGZpbGVOYW1lI25hbWVgIC0+IGZ1bmN0aW9uIG5vZGUpIGZvclxuXHQvLyByZXNvbHZpbmcgd3JhcChmbikgYXJndW1lbnRzIHN5bnRhY3RpY2FsbHkg4oCUIHRoZSBjaGVja2VyIHN0YXlzIHVudXNlZFxuXHRwcml2YXRlIGZ1bmN0aW9uQmluZGluZ3MgPSBuZXcgTWFwPHN0cmluZywgdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb24+KCk7XG5cdC8vIHdyYXAgY2FsbCBub2RlIC0+IGxvY2F0aW9uIG9mIHRoZSBlbmNsb3Npbmcgd3JhcCBzaXRlIChwbHVzIHRoYXRcblx0Ly8gc2l0ZSdzIHNjb3BlIGF0dHJpYnV0aW9uKSwgc28gbmVzdGVkIHdyYXAoKSBjYWxscyBpbnNpZGUgYSB3cmFwcGVkXG5cdC8vIGJvZHkgY2FycnkgdGhlIGB2aWFgIGxpbmsg4oCUIGFuZCBpbmhlcml0IHRoZSBzY29wZSB3aGVuIHRoZXkgaGF2ZVxuXHQvLyBub25lIG9mIHRoZWlyIG93blxuXHRwcml2YXRlIG5lc3RlZFdyYXBWaWEgPSBuZXcgTWFwPHRzLk5vZGUsIHsgdmlhOiBzdHJpbmc7IHNjb3BlPzogc3RyaW5nIH0+KCk7XG5cdC8vIHdyYXAgY2FsbCBub2RlIC0+IGl0cyBjb2xsZWN0ZWQgZW50cnksIHNvIGEgbGV4aWNhbGx5IG5lc3RlZCB3cmFwXG5cdC8vICh2aXNpdGVkIEJFRk9SRSB0aGUgb3V0ZXIgd3JhcCBjYWxsLCBwZXIgc291cmNlIG9yZGVyKSBnZXRzIGl0c1xuXHQvLyBgdmlhYCBiYWNrLXBhdGNoZWQgd2hlbiB0aGUgb3V0ZXIgYm9keSBpcyBhbmFseXNlZFxuXHRwcml2YXRlIHdyYXBFbnRyeUJ5Tm9kZSA9IG5ldyBNYXA8dHMuTm9kZSwgRURTSW5mbz4oKTtcblx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHM6IHZhcmlhYmxlTmFtZSAtPiBmdWxsUGF0aCBvZiB0aGUgdHlwZSBpdCBob2xkc1xuXHRwcml2YXRlIHZhcmlhYmxlVG9UeXBlTWFwID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0Ly8gVHJhY2sgbW5lbW9uaWNhIG1vZHVsZS1vYmplY3QgdmFyaWFibGVzIChlLmcuLCBpbXBvcnQgeyBtbmVtb25pY2EgfSBmcm9tICdtbmVtb25pY2EnOyBjb25zdCBtID0gbW5lbW9uaWNhKVxuXHRwcml2YXRlIG1vZHVsZU9iamVjdFZhcmlhYmxlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHQvLyBUcmFjayBpbXBvcnRlZCBhbGlhc2VzIG9mIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbiAoZS5nLiwgaW1wb3J0IHsgY3JlYXRlVHlwZXNDb2xsZWN0aW9uIGFzIGN0YyB9KVxuXHRwcml2YXRlIGNyZWF0ZVR5cGVzQ29sbGVjdGlvblZhcmlhYmxlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHQvLyBUcmFjayBjdXN0b20gY29sbGVjdGlvbiB2YXJpYWJsZXM6IHZhcmlhYmxlTmFtZSAtPiBjb2xsZWN0aW9uSWRcblx0cHJpdmF0ZSBjb2xsZWN0aW9uVmFyaWFibGVzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0Ly8gVHJhY2sgY3VzdG9tIGNvbGxlY3Rpb24gbWV0YWRhdGEgZm9yIE9wdGlvbiBCIHJlZ2lzdHJ5IGVtaXNzaW9uXG5cdHByaXZhdGUgY29sbGVjdGlvbkluZm8gPSBuZXcgTWFwPHN0cmluZywgQ29sbGVjdGlvbkluZm8+KCk7XG5cdHByaXZhdGUgY29sbGVjdGlvbkNvdW50ZXIgPSAwO1xuXHQvLyBJbnN0cnVtZW50YXRpb24gY29sbGVjdGlvbiAoc3ludGFjdGljIG9ubHkg4oCUIG5vIHR5cGUgY2hlY2tlcik6XG5cdC8vIGV2ZXJ5IG5hbWVkIGNsYXNzIGRlY2xhcmF0aW9uIGJ5IHNpbXBsZSBuYW1lLCBmb3IgcmVzb2x2aW5nXG5cdC8vIHJlZ2lzdHJhdGlvbiBzaXRlcyB0byBkZWNsYXJhdGlvbiBsb2NhdGlvbnMgKGJlc3QgZWZmb3J0LCBsYXN0IHdpbnMpXG5cdHByaXZhdGUgaW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNscyA9IG5ldyBNYXA8c3RyaW5nLCBJbnN0cnVtZW50YXRpb25DbGFzc0RlY2w+KCk7XG5cdC8vIFJlZ2lzdHJhdGlvbiBzaXRlczogZGVjb3JhdG9yIGFwcGxpY2F0aW9ucywgcHJvdmlkZXItdG9rZW4gb2JqZWN0XG5cdC8vIGxpdGVyYWxzLCBjb25zdW1lci5hcHBseSgpIG1pZGRsZXdhcmUgd2lyaW5nXG5cdHByaXZhdGUgaW5zdHJ1bWVudGF0aW9uU2l0ZXM6IEluc3RydW1lbnRhdGlvblNpdGVbXSA9IFtdO1xuXHQvLyBNZXJnZWQgcGx1Z2luIHZvY2FidWxhcnkgZm9yIGluc3RydW1lbnRhdGlvbiBkZXRlY3Rpb24gKGVtcHR5IHdoZW5cblx0Ly8gbm8gcGx1Z2lucyB3ZXJlIHBhc3NlZCDigJQgdGhlIGFuYWx5emVyIHRoZW4gY29sbGVjdHMgbm8gcG9pbnRzKVxuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvblZvY2FidWxhcnk6IEluc3RydW1lbnRhdGlvblZvY2FidWxhcnk7XG5cdC8vIFJlZmVyZW5jZWQtdHlwZSByZXNvbHV0aW9uIChGMTApOiBwZXItZmlsZSBkZWNsYXJhdGlvbnMgYW5kIGltcG9ydHMuXG5cdC8vIEEgdHlwZSBuYW1lIHVzZWQgaW4gZmlsZSBYIHJlc29sdmVzIHRocm91Z2ggWCdzIG93biBpbXBvcnQgc3RhdGVtZW50c1xuXHQvLyBmaXJzdCAocmVsYXRpdmUgKyB0c2NvbmZpZy1wYXRocywgdmlhIHRzLnJlc29sdmVNb2R1bGVOYW1lKSwgdGhlblxuXHQvLyBYJ3MgbG9jYWwgZGVjbGFyYXRpb25zLCB0aGVuIOKAlCBvbmx5IHdoZW4gbm90aGluZyBpbXBvcnRzIG9yIGRlY2xhcmVzXG5cdC8vIHRoZSBuYW1lIOKAlCB0aGUgdW5pcXVlIHNhbWUtbmFtZWQgZGVjbGFyYXRpb24gYWNyb3NzIHNjYW5uZWQgZmlsZXMuXG5cdC8vIEdlbnVpbmUgYW1iaWd1aXR5IG9yIGFuIHVucmVzb2x2YWJsZSByZWZlcmVuY2UgeWllbGRzIGB1bmtub3duYCwgbmV2ZXJcblx0Ly8gYSBiYXJlIGVtaXR0ZWQgbmFtZTogZ2VuZXJhdGVkIHR5cGVzLnRzIGNhcnJpZXMgbm8gaW1wb3J0cyBvZiBpdHMgb3duLlxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlRGVjbHMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbj4+KCk7XG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVJbXBvcnRzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlSW1wb3J0Pj4oKTtcblx0Ly8gZmlsZSAtPiAoZXhwb3J0ZWQgbmFtZSAtPiByZS1leHBvcnQgc3BlY2lmaWVyKSBmb3IgYGV4cG9ydCB7IFggfSBmcm9tICfigKYnYFxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHN0cmluZz4+KCk7XG5cdC8vIGZpbGUgLT4gc3BlY2lmaWVycyBvZiBgZXhwb3J0ICogZnJvbSAn4oCmJ2Bcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZUV4cG9ydFN0YXJzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZ1tdPigpO1xuXHQvLyBmaWxlIC0+IChleHBvcnRlZCBuYW1lIC0+IGxvY2FsIG5hbWUpIGZvciBgZXhwb3J0IHsgWCBhcyBZIH1gXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVFeHBvcnRBbGlhc2VzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHN0cmluZz4+KCk7XG5cdC8vIGZpbGUgLT4gKG5hbWVzcGFjZSBuYW1lIC0+IG5hbWVzcGFjZSBkZWNsYXJhdGlvbikg4oCUIG1pZGRsZSBzZWdtZW50c1xuXHQvLyBvZiBxdWFsaWZpZWQgcmVmZXJlbmNlcyAobW9kZWxzLklubmVyLkNyYXRlKSBkZXNjZW5kIHRocm91Z2ggdGhlc2Vcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgdHMuTW9kdWxlRGVjbGFyYXRpb24+PigpO1xuXHQvLyBmaWxlIC0+IChuYW1lc3BhY2UgbmFtZSAtPiBzcGVjaWZpZXIpIGZvciBgZXhwb3J0ICogYXMgbnMgZnJvbSAn4oCmJ2Bcblx0Ly8gYmFycmVscyDigJQgYSBuZXN0ZWQgbW9kdWxlIG5hbWVzcGFjZSBvbmUgc2VnbWVudCBkZWVwXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VTdGFycyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBgJHtjb250YWluaW5nRmlsZX06OiR7c3BlY2lmaWVyfWAgLT4gcmVzb2x1dGlvbiAodW5kZWZpbmVkID0gZmFpbGVkKVxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbkNhY2hlID0gbmV3IE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbiB8IHVuZGVmaW5lZD4oKTtcblx0Ly8gZmlsZSAtPiAoY29uc3QgbmFtZSAtPiBhcnJheSBsaXRlcmFsKSBmb3IgY29uc3RzIHdpdGggYXJyYXktbGl0ZXJhbFxuXHQvLyBpbml0aWFsaXplcnMgKGBhcyBjb25zdGAgLyBgc2F0aXNmaWVzYCB1bndyYXBwZWQpLCBzbyBhXG5cdC8vIGB0eXBlb2Ygc3RhdHVzTGlzdFtudW1iZXJdYCBmaWVsZCB0eXBlIGV4cGFuZHMgdG8gdGhlIGVsZW1lbnQgbGl0ZXJhbFxuXHQvLyB1bmlvbiBpbnN0ZWFkIG9mIGxlYWtpbmcgYSBiYXJlIHVucmVzb2x2YWJsZSBgdHlwZW9mYCBxdWVyeSBpbnRvIHRoZVxuXHQvLyBnZW5lcmF0ZWQgZmlsZS4gRGVjbGFyYXRpb25zIHBlcnNpc3QgYWNyb3NzIHBhc3NlcyDigJQgZW50cmllcyBzdGF5XG5cdC8vIHZhbGlkIGFmdGVyIHJlc2V0VXNhZ2VzKCksIHNhbWUgYXMgcmVmZXJlbmNlZFR5cGVEZWNsc1xuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgdHMuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbj4+KCk7XG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVDb21waWxlck9wdGlvbnM6IHRzLkNvbXBpbGVyT3B0aW9ucztcblx0Ly8gRmlsZSB3aG9zZSBBU1QgaXMgY3VycmVudGx5IGJlaW5nIHZpc2l0ZWQ7IHJlZmVyZW5jZXMgcmVzb2x2ZSBhZ2FpbnN0IGl0XG5cdHByaXZhdGUgY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9ICcnO1xuXHQvLyBBbGlhcyBuYW1lcyBjdXJyZW50bHkgYmVpbmcgZXhwYW5kZWQgKGN5Y2xlIGd1YXJkKVxuXHRwcml2YXRlIGV4cGFuZGluZ1JlZmVyZW5jZWRBbGlhc2VzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdC8vIE1uZW1vbmljYS1ncmFwaCBpZGVudGl0eSBsYXcgKGhhcmQgZmFpbCk6IGV2ZXJ5IGRlZmluZSgpL2xhenkoKS9cblx0Ly8gQGRlY29yYXRlKCkgc2l0ZSBrZXllZCBieSBpdHMgcnVudGltZSBuYW1lc3BhY2UgKGNvbGxlY3Rpb24gcm9vdHM6XG5cdC8vIGA8Y29sbGVjdGlvbj46OjxuYW1lPmA7IHN1YnR5cGVzOiBgPHBhcmVudEZ1bGxQYXRoPi48bmFtZT5gKS4gVHdvXG5cdC8vIHNpdGVzIGluIG9uZSBuYW1lc3BhY2UgYXJlIGEgc2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlIOKAlCB0aGUgcnVudGltZVxuXHQvLyB0aHJvd3MgQUxSRUFEWV9ERUNMQVJFRCDigJQgYW5kIG11c3QgYWJvcnQgZ2VuZXJhdGlvbi5cblx0cHJpdmF0ZSBkZWZpbmVTaXRlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmdbXT4oKTtcblx0Ly8gTW5lbW9uaWNhLWdyYXBoIHJlZmVyZW5jZXMgdGhhdCBzdGF5ZWQgYW1iaWd1b3VzIGFmdGVyIHBhdGgtYXdhcmVcblx0Ly8gcmVzb2x1dGlvbiBvciByZXNvbHZlZCB0byBub3RoaW5nIChoYXJkLWZhaWwgY2xhc3MgMilcblx0cHJpdmF0ZSBncmFwaFJlZmVyZW5jZUVycm9yczogUmVzb2x1dGlvbkVycm9yW10gPSBbXTtcblx0Ly8gR3VhcmRzIGxvb2t1cCgpLXBhdGggdmFsaWRhdGlvbiBzbyBpdCBydW5zIG9uY2UgcGVyIHVzYWdlcyBwYXNzXG5cdC8vIChnZXRSZXNvbHV0aW9uRXJyb3JzIG1heSBiZSBjYWxsZWQgcmVwZWF0ZWRseSk7IHJlc2V0VXNhZ2VzIHJlLWFybXMgaXRcblx0cHJpdmF0ZSBsb29rdXBSZWZlcmVuY2VzVmFsaWRhdGVkID0gZmFsc2U7XG5cdC8vIExpdGVyYWwgbG9va3VwKCkgY2FsbCBzaXRlcyB3aXRoIHRoZWlyIHJlc29sdmVkIHBhdGhzLiBLZXB0IGFwYXJ0IGZyb21cblx0Ly8gdGhlIHVzYWdlcyBtYXAgb24gcHVycG9zZTogYWRkVXNhZ2UgZHJvcHMgcGF0aHMgdGhlIGdyYXBoIGRvZXMgbm90XG5cdC8vIGtub3cgKHVzYWdlcy5qc29uIGluZGV4ZXMgcmVmZXJlbmNlcyB0byBLTk9XTiB0eXBlcyksIGJ1dCBhbiB1bmtub3duXG5cdC8vIGxvb2t1cCBwYXRoIGlzIGV4YWN0bHkgdGhlIGhhcmQtZmFpbCBjYXNlIOKAlCB0aGUgcnVudGltZSByZXR1cm5zXG5cdC8vIHVuZGVmaW5lZCB0aGVyZSBhbmQgdGhlIFR5cGVFcnJvciBhcnJpdmVzIG9uZSBsaW5lIGxhdGVyXG5cdHByaXZhdGUgbG9va3VwUmVmZXJlbmNlczogeyBwYXRoOiBzdHJpbmc7IGxvY2F0aW9uOiBzdHJpbmcgfVtdID0gW107XG5cdC8vIEd1YXJkcyBwbGFpbi1UUyByZWZlcmVuY2UgdmFsaWRhdGlvbiBzbyBpdCBydW5zIG9uY2UgcGVyIHVzYWdlcyBwYXNzXG5cdC8vIChnZXRSZXNvbHV0aW9uRXJyb3JzIG1heSBiZSBjYWxsZWQgcmVwZWF0ZWRseSk7IHJlc2V0VXNhZ2VzIHJlLWFybXMgaXRcblx0cHJpdmF0ZSBwbGFpblR5cGVSZWZlcmVuY2VzVmFsaWRhdGVkID0gZmFsc2U7XG5cdC8vIFBsYWluLVRTIHR5cGUgcmVmZXJlbmNlIHNpdGVzIHdob3NlIHJlc29sdXRpb24gZmVsbCB0aHJvdWdoIGltcG9ydHMsXG5cdC8vIGxvY2FscywgdGhlIHByb2dyYW0td2lkZSBzY2FuLCBhbmQgdGhlIGdyYXBoIHRvIGEgc29mdCBgdW5rbm93bmAuXG5cdC8vIFZhbGlkYXRlZCBsYXppbHkgZnJvbSBnZXRSZXNvbHV0aW9uRXJyb3JzIGFnYWluc3QgdGhlIGNvbXBsZXRlXG5cdC8vIGRlY2xhcmF0aW9uIG1hcDogYSBuYW1lIHNldmVyYWwgcHJvamVjdC1zb3VyY2UgZmlsZXMgZGVjbGFyZSDigJQgd2l0aFxuXHQvLyBubyBpbXBvcnQgaW4gdGhlIHJlZmVyZW5jaW5nIGZpbGUgdG8gYW5jaG9yIGl0IOKAlCBpcyB0aGUgcGxhaW4tVFNcblx0Ly8gYW1iaWd1aXR5IGhhcmQtZmFpbCBjbGFzcyAob25lIHRpZXIgYmVsb3cgdGhlIGdyYXBoIGlkZW50aXR5IGxhdyk7XG5cdC8vIGFic2VuY2UgKGdob3N0IG5hbWVzKSBzdGF5cyBzb2Z0LiBSZWNvcmRpbmcgaGFwcGVucyBvbiBldmVyeSBwYXNzLFxuXHQvLyB0aGUgdmVyZGljdCBvbmx5IGhlcmUg4oCUIHBhc3MgMSBzZWVzIGFuIGluY29tcGxldGUgZGVjbGFyYXRpb24gbWFwLFxuXHQvLyBzbyBvbmx5IHRoZSB1c2FnZXMgcGFzcyBpcyBhdXRob3JpdGF0aXZlIChtaXJyb3JzIGxvb2t1cCByZWZlcmVuY2VzKVxuXHRwcml2YXRlIHBsYWluVHlwZVJlZmVyZW5jZXM6IHsgbmFtZTogc3RyaW5nOyBsb2NhdGlvbjogc3RyaW5nOyBmaWxlOiBzdHJpbmcgfVtdID0gW107XG5cdC8vIFBlci1maWxlIHRvcC1sZXZlbCB2YXJpYWJsZSAtPiBtbmVtb25pY2EgZnVsbFBhdGggYmluZGluZ3MgKHZhbHVlXG5cdC8vIHNjb3BlKTogYGNvbnN0IEFkZHJlc3MgPSBVc2VyLmRlZmluZSgnQWRkcmVzcycsIOKApilgIG1ha2VzIGBBZGRyZXNzYFxuXHQvLyBkZW5vdGUgVXNlci5BZGRyZXNzIHdoZXJldmVyIHRoYXQgZmlsZSdzIHJlZmVyZW5jZXMgYXJlIHJlc29sdmVkXG5cdHByaXZhdGUgZmlsZUdyYXBoQmluZGluZ3MgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgc3RyaW5nPj4oKTtcblx0Ly8gVGhlIGdyYXBoIHR5cGUgd2hvc2UgY29uc3RydWN0b3IgaXMgY3VycmVudGx5IGJlaW5nIGV4dHJhY3RlZDtcblx0Ly8gYW5jaG9ycyByZWxhdGl2ZS1maXJzdCBncmFwaCByZWZlcmVuY2UgcmVzb2x1dGlvblxuXHRwcml2YXRlIGN1cnJlbnRHcmFwaEFuY2hvcjogVHlwZU5vZGUgfCB1bmRlZmluZWQ7XG5cdC8vIGRlZmluZSgpL2xhenkoKSBjYWxscyBhbHJlYWR5IGV4dHJhY3RlZCB0aGlzIHBhc3MuIFRoZSBDTEkgcmUtYW5hbHl6ZXNcblx0Ly8gZXZlcnkgZmlsZSBhZnRlciByZXNldFVzYWdlcygpOyBjbGVhcmluZyB0aGUgc2V0IGxldHMgdGhlIHNlY29uZCBwYXNzXG5cdC8vIHJlLWV4dHJhY3QgZXZlcnkgY29uc3RydWN0b3IgYWdhaW5zdCB0aGUgQ09NUExFVEUgZ3JhcGgg4oCUIHBhc3MgMSBzZWVzXG5cdC8vIGZvcndhcmQgcmVmZXJlbmNlcyBhcyBgbm9uZWAgKHNvZnQgdW5rbm93bikgYmVjYXVzZSBsYXRlciBmaWxlcyBoYXZlXG5cdC8vIG5vdCBiZWVuIHZpc2l0ZWQgeWV0LCBzbyBvbmx5IHBhc3MtMiByZXNvbHV0aW9uIGlzIGF1dGhvcml0YXRpdmUgZm9yXG5cdC8vIHRoZSBoYXJkLWZhaWwgaWRlbnRpdHkgbGF3LiBUaGUgc3RhbXAgbGl2ZXMgaGVyZSByYXRoZXIgdGhhbiBvbiB0aGVcblx0Ly8gQVNUIG5vZGUgc28gaXQgY2FuIGFjdHVhbGx5IGJlIGNsZWFyZWQuIChDaGFpbmVkIGNhbGxzIHZpc2l0IHRoZSBzYW1lXG5cdC8vIG5vZGUgdHdpY2Ugd2l0aGluIG9uZSBwYXNzOyB0aGUgaW4tcGFzcyBkZWR1cCBiZWxvdyBzdGF5cy4pXG5cdHByaXZhdGUgcHJvY2Vzc2VkQ2FsbHMgPSBuZXcgU2V0PHRzLkNhbGxFeHByZXNzaW9uPigpO1xuXG5cdGNvbnN0cnVjdG9yIChwcm9ncmFtPzogdHMuUHJvZ3JhbSwgcGx1Z2luczogVGFjdGljYVBsdWdpbltdID0gW10pIHtcblx0XHQvLyBDb21waWxlciBvcHRpb25zIGRyaXZlIHRzLnJlc29sdmVNb2R1bGVOYW1lIGZvciBpbXBvcnQtYXdhcmVcblx0XHQvLyByZWZlcmVuY2VkLXR5cGUgcmVzb2x1dGlvbiAodHNjb25maWcgYHBhdGhzYCwgZXh0ZW5zaW9ubGVzc1xuXHRcdC8vIGltcG9ydHMpOyB0aGUgdHlwZSBjaGVja2VyIGl0c2VsZiBzdGF5cyB1bnVzZWQuXG5cdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUNvbXBpbGVyT3B0aW9ucyA9IHByb2dyYW0/LmdldENvbXBpbGVyT3B0aW9ucygpID8/IHt9O1xuXHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeSA9IG1lcmdlVGFjdGljYVBsdWdpbnMocGx1Z2lucyk7XG5cdH1cblxuXHQvKipcblx0ICogUmVzZXQgdXNhZ2UtcmVsYXRlZCBzdGF0ZSBmb3IgYSBmcmVzaCBwYXNzLlxuXHQgKiBDYWxsIGJlZm9yZSB0aGUgdXNhZ2UtY29sbGVjdGlvbiBwYXNzIHRvIGF2b2lkIGR1cGxpY2F0ZXMgZnJvbSBkZWZpbml0aW9uIHBhc3MuXG5cdCAqL1xuXHRyZXNldFVzYWdlcyAoKTogdm9pZCB7XG5cdFx0dGhpcy51c2FnZXMuY2xlYXIoKTtcblx0XHR0aGlzLmVkc1VzYWdlcy5jbGVhcigpO1xuXHRcdHRoaXMuZmxvd1VzYWdlcy5jbGVhcigpO1xuXHRcdHRoaXMudmFyaWFibGVUb1R5cGVNYXAuY2xlYXIoKTtcblx0XHQvLyBFRFMgZW50cnkgcmVmZXJlbmNlcyBnbyBzdGFsZSB3aXRoIGVkc1VzYWdlczsgdmlhIGxpbmtzIGFyZVxuXHRcdC8vIHJlLWRlcml2ZWQgb24gdGhlIG5leHQgcGFzc1xuXHRcdHRoaXMud3JhcEVudHJ5QnlOb2RlLmNsZWFyKCk7XG5cdFx0dGhpcy5uZXN0ZWRXcmFwVmlhLmNsZWFyKCk7XG5cdFx0Ly8gTm90ZTogbW9kdWxlT2JqZWN0VmFyaWFibGVzIGFuZCBjb2xsZWN0aW9uVmFyaWFibGVzIGludGVudGlvbmFsbHkgcGVyc2lzdFxuXHRcdC8vIGFjcm9zcyBkZWZpbml0aW9uIGFuZCB1c2FnZSBwYXNzZXMuXG5cdFx0Ly8gUmUtZXh0cmFjdGlvbiBpbiB0aGUgdXNhZ2VzIHBhc3MgaXMgd2hhdCBtYWtlcyBncmFwaCByZWZlcmVuY2Vcblx0XHQvLyByZXNvbHV0aW9uIGF1dGhvcml0YXRpdmU6IHBhc3MgMSByZXNvbHZlcyBhZ2FpbnN0IGFuIGluY29tcGxldGVcblx0XHQvLyBncmFwaCAoZm9yd2FyZCByZWZlcmVuY2VzIHJlYWQgYXMgYG5vbmVgKSwgcGFzcyAyIGFnYWluc3QgYWxsIG9mIGl0LlxuXHRcdHRoaXMucHJvY2Vzc2VkQ2FsbHMuY2xlYXIoKTtcblx0XHQvLyBsb29rdXAoKS1wYXRoIHZhbGlkYXRpb24gcnVucyBhZ2FpbnN0IHRoZSByZWNvcmRlZCBzaXRlczsgYSBmcmVzaFxuXHRcdC8vIHBhc3MgbXVzdCByZS1yZWNvcmQgYW5kIHJlLXZhbGlkYXRlIChwYXNzLTEgcmVzdWx0cyB3b3VsZCBiZVxuXHRcdC8vIHByZW1hdHVyZSDigJQgdGhlIGdyYXBoIGlzIHN0aWxsIGluY29tcGxldGUpXG5cdFx0dGhpcy5sb29rdXBSZWZlcmVuY2VzVmFsaWRhdGVkID0gZmFsc2U7XG5cdFx0dGhpcy5sb29rdXBSZWZlcmVuY2VzID0gW107XG5cdFx0dGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzVmFsaWRhdGVkID0gZmFsc2U7XG5cdFx0dGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzID0gW107XG5cdH1cblxuXHQvKipcblx0ICogQW5hbHl6ZSBhIHNvdXJjZSBmaWxlIGZvciBNbmVtb25pY2EgdHlwZSBkZWZpbml0aW9uc1xuXHQgKi9cblx0YW5hbHl6ZUZpbGUgKHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiBBbmFseXplUmVzdWx0IHtcblx0XHR0aGlzLmVycm9ycyA9IFtdO1xuXHRcdC8vIFJlZmVyZW5jZWQtdHlwZSBuYW1lcyBpbiB0aGlzIGZpbGUgcmVzb2x2ZSBhZ2FpbnN0IGl0cyBvd24gaW1wb3J0c1xuXHRcdHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9IG5vZGVQYXRoLnJlc29sdmUoc291cmNlRmlsZS5maWxlTmFtZSk7XG5cdFx0Ly8gRW5zdXJlIHBhcmVudCBub2RlcyBhcmUgc2V0IGZvciBBU1QgdHJhdmVyc2FsXG5cdFx0dGhpcy5zZXRQYXJlbnROb2Rlc0luU291cmNlRmlsZShzb3VyY2VGaWxlKTtcblx0XHR0aGlzLnZpc2l0Tm9kZShzb3VyY2VGaWxlLCBzb3VyY2VGaWxlKTtcblxuXHRcdHJldHVybiB7XG5cdFx0XHR0eXBlcyAgOiB0aGlzLmdyYXBoLmdldEFsbFR5cGVzKCksXG5cdFx0XHRlcnJvcnMgOiB0aGlzLmVycm9ycyxcblx0XHR9O1xuXHR9XG5cblx0LyoqXG5cdCAqIEFuYWx5emUgc291cmNlIGNvZGUgc3RyaW5nXG5cdCAqL1xuXHRhbmFseXplU291cmNlIChzb3VyY2VDb2RlOiBzdHJpbmcsIGZpbGVOYW1lID0gJ3RlbXAudHMnKTogQW5hbHl6ZVJlc3VsdCB7XG5cdFx0Y29uc3Qgc291cmNlRmlsZSA9IHRzLmNyZWF0ZVNvdXJjZUZpbGUoXG5cdFx0XHRmaWxlTmFtZSxcblx0XHRcdHNvdXJjZUNvZGUsXG5cdFx0XHR0cy5TY3JpcHRUYXJnZXQuTGF0ZXN0LFxuXHRcdFx0dHJ1ZVxuXHRcdCk7XG5cdFx0cmV0dXJuIHRoaXMuYW5hbHl6ZUZpbGUoc291cmNlRmlsZSk7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IHRoZSB0eXBlIGdyYXBoXG5cdCAqL1xuXHRnZXRHcmFwaCAoKTogVHlwZUdyYXBoSW1wbCB7XG5cdFx0cmV0dXJuIHRoaXMuZ3JhcGg7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBkZWZpbml0aW9uc1xuXHQgKi9cblx0Z2V0RGVmaW5pdGlvbnMgKCk6IE1hcDxzdHJpbmcsIERlZmluaXRpb25JbmZvPiB7XG5cdFx0cmV0dXJuIHRoaXMuZGVmaW5pdGlvbnM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCB1c2FnZXNcblx0ICovXG5cdGdldFVzYWdlcyAoKTogTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+IHtcblx0XHRyZXR1cm4gdGhpcy51c2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBFRFMgdXNhZ2VzXG5cdCAqL1xuXHRnZXRFRFNVc2FnZXMgKCk6IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4ge1xuXHRcdHJldHVybiB0aGlzLmVkc1VzYWdlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGZsb3cgdXNhZ2VzXG5cdCAqL1xuXHRnZXRGbG93VXNhZ2VzICgpOiBNYXA8c3RyaW5nLCBGbG93SW5mb1tdPiB7XG5cdFx0cmV0dXJuIHRoaXMuZmxvd1VzYWdlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGluc3RydW1lbnRhdGlvbiBwb2ludHMuXG5cdCAqIFJlZ2lzdHJhdGlvbiBzaXRlcyByZWZlcmVuY2luZyBhIGNsYXNzIGRlY2xhcmVkIGluIHRoZSBzYW1lIHByb2plY3Rcblx0ICogcmVzb2x2ZSB0byB0aGUgY2xhc3MgZGVjbGFyYXRpb24ncyBsb2NhdGlvbi9jb2RlOyBleHRlcm5hbCBjbGFzc2VzXG5cdCAqIChlLmcuLCBhIGZyYW1ld29yay1idWlsdGluIGltcGxlbWVudGF0aW9uIGZyb20gbm9kZV9tb2R1bGVzKSBrZWVwXG5cdCAqIHRoZSByZWdpc3RyYXRpb24gc2l0ZS5cblx0ICogRGVkdXBlZCBieSBraW5kK2NsYXNzTmFtZStsb2NhdGlvbitzY29wZSB3aXRoIHRhcmdldHMgbWVyZ2VkIOKAlCBhXG5cdCAqIGNsYXNzIGRldGVjdGVkIGJ5IGhlcml0YWdlIEFORCBieSBhIGRlY29yYXRvciBzaXRlIHlpZWxkcyBzZXBhcmF0ZVxuXHQgKiBlbnRyaWVzIHdpdGggZGlzdGluY3Qgc2NvcGVzIChzZWUgSW5zdHJ1bWVudGF0aW9uUG9pbnQgaW4gdHlwZXMudHMpLlxuXHQgKi9cblx0Z2V0SW5zdHJ1bWVudGF0aW9uUG9pbnRzICgpOiBJbnN0cnVtZW50YXRpb25Qb2ludFtdIHtcblx0XHRjb25zdCBwb2ludHMgPSBuZXcgTWFwPHN0cmluZywgSW5zdHJ1bWVudGF0aW9uUG9pbnQ+KCk7XG5cblx0XHRjb25zdCBhZGRQb2ludCA9IChwb2ludDogSW5zdHJ1bWVudGF0aW9uUG9pbnQpOiB2b2lkID0+IHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3BvaW50LmtpbmR9fCR7cG9pbnQuY2xhc3NOYW1lfXwke3BvaW50LmxvY2F0aW9ufXwke3BvaW50LnNjb3BlfWA7XG5cdFx0XHRjb25zdCBleGlzdGluZyA9IHBvaW50cy5nZXQoa2V5KTtcblx0XHRcdGlmIChleGlzdGluZykge1xuXHRcdFx0XHRjb25zdCBtZXJnZWQgPSBuZXcgU2V0KFsgLi4uZXhpc3RpbmcudGFyZ2V0cywgLi4ucG9pbnQudGFyZ2V0cyBdKTtcblx0XHRcdFx0ZXhpc3RpbmcudGFyZ2V0cyA9IEFycmF5LmZyb20obWVyZ2VkKTtcblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0cG9pbnRzLnNldChrZXksIHBvaW50KTtcblx0XHR9O1xuXG5cdFx0Zm9yIChjb25zdCBzaXRlIG9mIHRoaXMuaW5zdHJ1bWVudGF0aW9uU2l0ZXMpIHtcblx0XHRcdGNvbnN0IGRlY2wgPSB0aGlzLmluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMuZ2V0KHNpdGUuY2xhc3NOYW1lKTtcblx0XHRcdGNvbnN0IHBvaW50OiBJbnN0cnVtZW50YXRpb25Qb2ludCA9IHtcblx0XHRcdFx0a2luZCAgICAgIDogc2l0ZS5raW5kLFxuXHRcdFx0XHRjbGFzc05hbWUgOiBzaXRlLmNsYXNzTmFtZSxcblx0XHRcdFx0bG9jYXRpb24gIDogZGVjbCA/IGRlY2wubG9jYXRpb24gOiBzaXRlLmxvY2F0aW9uLFxuXHRcdFx0XHRjb2RlICAgICAgOiBkZWNsID8gZGVjbC5jb2RlIDogc2l0ZS5jb2RlLFxuXHRcdFx0XHRzY29wZSAgICAgOiBzaXRlLnNjb3BlLFxuXHRcdFx0XHR0YXJnZXRzICAgOiBzaXRlLnRhcmdldHMsXG5cdFx0XHR9O1xuXHRcdFx0YWRkUG9pbnQocG9pbnQpO1xuXHRcdH1cblxuXHRcdC8vIEhlcml0YWdlLWRlY2xhcmVkIGNsYXNzZXMgYWx3YXlzIGVtaXQgYSBkZWNsYXJhdGlvbiBwb2ludCB3aXRoXG5cdFx0Ly8gc2NvcGUgJ21vZHVsZScgKGF0dGFjaG1lbnQgc3RhdGljYWxseSB1bmtub3duKTsgcmVnaXN0cmF0aW9uXG5cdFx0Ly8gc2l0ZXMgYWJvdmUgY2FycnkgdGhlIG5hcnJvd2VyIHNjb3BlcyBhcyBzZXBhcmF0ZSBlbnRyaWVzXG5cdFx0Zm9yIChjb25zdCBbIGNsYXNzTmFtZSwgZGVjbCBdIG9mIHRoaXMuaW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNscykge1xuXHRcdFx0aWYgKCFkZWNsLmtpbmQpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBwb2ludDogSW5zdHJ1bWVudGF0aW9uUG9pbnQgPSB7XG5cdFx0XHRcdGtpbmQgICAgICA6IGRlY2wua2luZCxcblx0XHRcdFx0Y2xhc3NOYW1lIDogY2xhc3NOYW1lLFxuXHRcdFx0XHRsb2NhdGlvbiAgOiBkZWNsLmxvY2F0aW9uLFxuXHRcdFx0XHRjb2RlICAgICAgOiBkZWNsLmNvZGUsXG5cdFx0XHRcdHNjb3BlICAgICA6ICdtb2R1bGUnLFxuXHRcdFx0XHR0YXJnZXRzICAgOiBbXSxcblx0XHRcdH07XG5cdFx0XHRhZGRQb2ludChwb2ludCk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVzdWx0ID0gQXJyYXkuZnJvbShwb2ludHMudmFsdWVzKCkpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogQWRkIGEgdG9wb2xvZ2ljYSB0eXBlIHRvIHRoZSBhbmFseXplciBmb3IgdXNhZ2UgdHJhY2tpbmcuXG5cdCAqIFRoaXMgYWxsb3dzIHRoZSBhbmFseXplciB0byByZWNvZ25pemUgdG9wb2xvZ2ljYSB0eXBlcyB3aGVuIGNvbGxlY3RpbmcgdXNhZ2VzLlxuXHQgKi9cblx0YWRkVG9wb2xvZ2ljYVR5cGUgKGZ1bGxQYXRoOiBzdHJpbmcsIG5vZGU6IGltcG9ydCgnLi90eXBlcycpLlR5cGVOb2RlKTogdm9pZCB7XG5cdFx0Ly8gU2tpcCBpZiBhbHJlYWR5IGV4aXN0c1xuXHRcdGlmICh0aGlzLmdyYXBoLmFsbFR5cGVzLmhhcyhmdWxsUGF0aCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGggc28gaXQgY2FuIGJlIGZvdW5kIGR1cmluZyB1c2FnZSBjb2xsZWN0aW9uXG5cdFx0aWYgKG5vZGUucGFyZW50KSB7XG5cdFx0XHQvLyBBZGQgYXMgY2hpbGQgb2YgcGFyZW50XG5cdFx0XHR0aGlzLmdyYXBoLmFkZENoaWxkKG5vZGUucGFyZW50LCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0Ly8gQWRkIGFzIHJvb3Rcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cblx0XHQvLyBBbHNvIGFkZCB0byBkZWZpbml0aW9ucyBzbyBpdCdzIHJlY29nbml6ZWQgYXMgYSBrbm93biB0eXBlXG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IG5vZGUubmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7bm9kZS5zb3VyY2VGaWxlfToke25vZGUubGluZX06JHtub2RlLmNvbHVtbn1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogbm9kZS5wYXJlbnQgPyBub2RlLnBhcmVudC5mdWxsUGF0aCA6IG51bGwsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IHRydWUsXG5cdFx0XHRibG9ja0Vycm9ycyA6IGZhbHNlXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChmdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdH1cblxuXHQvKipcblx0ICogU2V0IHBhcmVudCBub2RlcyBpbiBhIHNvdXJjZSBmaWxlIHRvIGVuYWJsZSBBU1QgdHJhdmVyc2FsIHVwXG5cdCAqL1xuXHRwcml2YXRlIHNldFBhcmVudE5vZGVzSW5Tb3VyY2VGaWxlIChzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3Qgc2V0UGFyZW50ID0gKG5vZGU6IHRzLk5vZGUsIHBhcmVudD86IHRzLk5vZGUpID0+IHtcblx0XHRcdC8vIFR5cGVTY3JpcHQgZG9lc24ndCBleHBvc2UgcGFyZW50IGFzIHdyaXRhYmxlLCBidXQgd2UgbmVlZCBpdFxuXHRcdFx0Ly8gZXNsaW50LWRpc2FibGUtbmV4dC1saW5lIEB0eXBlc2NyaXB0LWVzbGludC9uby1leHBsaWNpdC1hbnlcblx0XHRcdChub2RlIGFzIGFueSkucGFyZW50ID0gcGFyZW50O1xuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHNldFBhcmVudChjaGlsZCwgbm9kZSkpO1xuXHRcdH07XG5cdFx0c2V0UGFyZW50KHNvdXJjZUZpbGUpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFZpc2l0IGEgbm9kZSBpbiB0aGUgQVNUXG5cdCAqL1xuXHRwcml2YXRlIHZpc2l0Tm9kZSAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSwgY3VycmVudENsYXNzPzogdHMuQ2xhc3NEZWNsYXJhdGlvbik6IHZvaWQge1xuXHRcdC8vIFRyYWNrIG1uZW1vbmljYSBtb2R1bGUtb2JqZWN0IGFsaWFzZXMgYW5kIGN1c3RvbSBjb2xsZWN0aW9uIHZhcmlhYmxlc1xuXHRcdC8vIGJlZm9yZSBwcm9jZXNzaW5nIGRlZmluZSgpL2xvb2t1cCgpIGNhbGxzIHNvIHNvdXJjZSByZXNvbHV0aW9uIHdvcmtzLlxuXHRcdHRoaXMudHJhY2tJbXBvcnRzKG5vZGUpO1xuXHRcdHRoaXMudHJhY2tNb2R1bGVPYmplY3RBbGlhc2VzKG5vZGUpO1xuXHRcdHRoaXMudHJhY2tDb2xsZWN0aW9uQWxpYXNlcyhub2RlLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIENoZWNrIGZvciBkZWZpbmUoKSBjYWxsc1xuXHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChub2RlKSkge1xuXHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ2FsbChub2RlIGFzIHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgbGF6eSgpIGNhbGxzXG5cdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChub2RlKSkge1xuXHRcdFx0dGhpcy5wcm9jZXNzTGF6eUNhbGwobm9kZSBhcyB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIGRlY29yYXRlKCkgZGVjb3JhdG9yXG5cdFx0aWYgKHRoaXMuaXNEZWNvcmF0ZURlY29yYXRvcihub2RlKSkge1xuXHRcdFx0dGhpcy5wcm9jZXNzRGVjb3JhdGVEZWNvcmF0b3Iobm9kZSBhcyB0cy5EZWNvcmF0b3IsIHNvdXJjZUZpbGUsIGN1cnJlbnRDbGFzcyk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIHR5cGUgdXNhZ2VzIChuZXcgVHlwZSgpLCB0eXBlIGFubm90YXRpb25zLCBldGMuKVxuXHRcdHRoaXMuY29sbGVjdFVzYWdlKG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIEVEUyBwYXR0ZXJucyAod3JhcCwgY3VycmVudCwgZ2V0RmxvdywgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RFRFMobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgbmF0aXZlIGZsb3cgcGF0dGVybnMgKHByb3BlcnR5IGFjY2VzcywgbWV0aG9kIGNhbGxzLCBldGMuKVxuXHRcdHRoaXMuY29sbGVjdEZsb3cobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgZnJhbWV3b3JrIGluc3RydW1lbnRhdGlvbiBwb2ludHMgKHZvY2FidWxhcnkgc3VwcGxpZWRcblx0XHQvLyBieSBwbHVnaW5zOyBzeW50YWN0aWMgb25seSDigJQgbm8gdHlwZSBjaGVja2VyKVxuXHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbihub2RlLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIENvbGxlY3QgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9ucyAoYWxpYXNlcywgY2xhc3NlcywgaW50ZXJmYWNlcylcblx0XHQvLyBwZXIgZmlsZSwgYW5kIHRoZSBmaWxlJ3MgaW1wb3J0IHdpcmluZywgZm9yIGltcG9ydC1hd2FyZSByZXNvbHV0aW9uXG5cdFx0dGhpcy50cmFja1JlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24obm9kZSk7XG5cdFx0dGhpcy50cmFja1JlZmVyZW5jZWRUeXBlSW1wb3J0KG5vZGUpO1xuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZVJlRXhwb3J0KG5vZGUpO1xuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXkobm9kZSk7XG5cblx0XHQvLyBUcmFjayBzYW1lLWZpbGUgZnVuY3Rpb24gYmluZGluZ3Mgc28gRURTIGNhbiByZXNvbHZlIHdyYXAoZm4pXG5cdFx0Ly8gYXJndW1lbnRzIHdpdGhvdXQgdGhlIHR5cGUgY2hlY2tlciAoYmVzdCBlZmZvcnQsIGxhc3Qgd2lucylcblx0XHRpZiAodHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKG5vZGUpICYmIG5vZGUubmFtZSkge1xuXHRcdFx0Y29uc3Qga2V5ID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX0jJHtub2RlLm5hbWUudGV4dH1gO1xuXHRcdFx0dGhpcy5mdW5jdGlvbkJpbmRpbmdzLnNldChrZXksIG5vZGUpO1xuXHRcdH1cblx0XHRpZiAoXG5cdFx0XHR0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpICYmXG5cdFx0XHRub2RlLmluaXRpYWxpemVyICYmXG5cdFx0XHQodHMuaXNBcnJvd0Z1bmN0aW9uKG5vZGUuaW5pdGlhbGl6ZXIpIHx8IHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKG5vZGUuaW5pdGlhbGl6ZXIpKVxuXHRcdCkge1xuXHRcdFx0Y29uc3Qga2V5ID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX0jJHtub2RlLm5hbWUudGV4dH1gO1xuXHRcdFx0dGhpcy5mdW5jdGlvbkJpbmRpbmdzLnNldChrZXksIG5vZGUuaW5pdGlhbGl6ZXIpO1xuXHRcdH1cblxuXHRcdC8vIFRyYWNrIGNsYXNzIGRlY2xhcmF0aW9ucyBmb3IgZGVjb3JhdG9yIHBhcmVudCBsb29rdXBcblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHQvLyBWaXNpdCBjaGlsZHJlbiB3aXRoIHRoaXMgY2xhc3MgYXMgdGhlIGN1cnJlbnQgY29udGV4dFxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHRoaXMudmlzaXROb2RlKGNoaWxkLCBzb3VyY2VGaWxlLCBub2RlKSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdC8vIFJlY3Vyc2l2ZWx5IHZpc2l0IGNoaWxkcmVuXG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgY2hpbGQgPT4gdGhpcy52aXNpdE5vZGUoY2hpbGQsIHNvdXJjZUZpbGUsIGN1cnJlbnRDbGFzcykpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBUcmFjayBpbXBvcnRzIGZyb20gJ21uZW1vbmljYScgc28gYWxpYXNlcyBvZiB0aGUgbW9kdWxlIG9iamVjdCBhbmRcblx0ICogY3JlYXRlVHlwZXNDb2xsZWN0aW9uIGFyZSByZWNvZ25pemVkIHdpdGhvdXQgcmVseWluZyBvbiB0aGUgdHlwZSBjaGVja2VyLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja0ltcG9ydHMgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzSW1wb3J0RGVjbGFyYXRpb24obm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IG1vZHVsZVNwZWNpZmllciB9ID0gbm9kZTtcblx0XHRpZiAoIXRzLmlzU3RyaW5nTGl0ZXJhbChtb2R1bGVTcGVjaWZpZXIpIHx8IG1vZHVsZVNwZWNpZmllci50ZXh0ICE9PSAnbW5lbW9uaWNhJykge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IGNsYXVzZSA9IG5vZGUuaW1wb3J0Q2xhdXNlO1xuXHRcdGlmICghY2xhdXNlKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0IHsgbW5lbW9uaWNhLCBjcmVhdGVUeXBlc0NvbGxlY3Rpb24gfSBmcm9tICdtbmVtb25pY2EnXG5cdFx0aWYgKGNsYXVzZS5uYW1lZEJpbmRpbmdzICYmIHRzLmlzTmFtZWRJbXBvcnRzKGNsYXVzZS5uYW1lZEJpbmRpbmdzKSkge1xuXHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGNsYXVzZS5uYW1lZEJpbmRpbmdzLmVsZW1lbnRzKSB7XG5cdFx0XHRcdGNvbnN0IGxvY2FsTmFtZSA9IGVsZW1lbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBpbXBvcnRlZE5hbWUgPSBlbGVtZW50LnByb3BlcnR5TmFtZVxuXHRcdFx0XHRcdD8gZWxlbWVudC5wcm9wZXJ0eU5hbWUudGV4dFxuXHRcdFx0XHRcdDogbG9jYWxOYW1lO1xuXHRcdFx0XHRpZiAoaW1wb3J0ZWROYW1lID09PSAnbW5lbW9uaWNhJykge1xuXHRcdFx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChsb2NhbE5hbWUpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChpbXBvcnRlZE5hbWUgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nKSB7XG5cdFx0XHRcdFx0dGhpcy5jcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMuYWRkKGxvY2FsTmFtZSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgKiBhcyBtbmVtb25pY2EgZnJvbSAnbW5lbW9uaWNhJ1xuXHRcdGlmIChjbGF1c2UubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVzcGFjZUltcG9ydChjbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChjbGF1c2UubmFtZWRCaW5kaW5ncy5uYW1lLnRleHQpO1xuXHRcdH1cblxuXHRcdC8vIGltcG9ydCBtbmVtb25pY2EgZnJvbSAnbW5lbW9uaWNhJyAoZGVmYXVsdCBpbXBvcnQpIOKAlCB0cmVhdCBhcyBtb2R1bGUgb2JqZWN0IHRvb1xuXHRcdGlmIChjbGF1c2UubmFtZSkge1xuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuYWRkKGNsYXVzZS5uYW1lLnRleHQpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgYSBuYW1lZCByZWZlcmVuY2VkLXR5cGUgZGVjbGFyYXRpb24gKHR5cGUgYWxpYXMsIGNsYXNzLCBvclxuXHQgKiBpbnRlcmZhY2UpIGZvciB0aGUgZmlsZSBjdXJyZW50bHkgYmVpbmcgdmlzaXRlZC5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0Ly8gTmFtZXNwYWNlcyBhcmUgdGhlIG1pZGRsZSBzZWdtZW50cyBvZiBxdWFsaWZpZWQgcmVmZXJlbmNlc1xuXHRcdC8vIChtb2RlbHMuSW5uZXIuQ3JhdGUpIOKAlCByZWNvcmRlZCBzZXBhcmF0ZWx5IGZyb20gdGhlIHBsYWluLW5hbWVcblx0XHQvLyBkZWNsYXJhdGlvbiB0YWJsZSAoc3RyaW5nLW5hbWVkIGBtb2R1bGUgJ+KApidgIGRlY2xhcmF0aW9ucyBhcmVcblx0XHQvLyBhbWJpZW50IGV4dGVybmFscyBhbmQgc3RheSBvdXQpXG5cdFx0aWYgKHRzLmlzTW9kdWxlRGVjbGFyYXRpb24obm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkgJiZcblx0XHRcdG5vZGUuYm9keSAmJiB0cy5pc01vZHVsZUJsb2NrKG5vZGUuYm9keSkpIHtcblx0XHRcdGNvbnN0IG5hbWVzcGFjZUZpbGVQYXRoID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdFx0bGV0IG5hbWVzcGFjZXMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlcy5nZXQobmFtZXNwYWNlRmlsZVBhdGgpO1xuXHRcdFx0aWYgKCFuYW1lc3BhY2VzKSB7XG5cdFx0XHRcdG5hbWVzcGFjZXMgPSBuZXcgTWFwPHN0cmluZywgdHMuTW9kdWxlRGVjbGFyYXRpb24+KCk7XG5cdFx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzLnNldChuYW1lc3BhY2VGaWxlUGF0aCwgbmFtZXNwYWNlcyk7XG5cdFx0XHR9XG5cdFx0XHRuYW1lc3BhY2VzLnNldChub2RlLm5hbWUudGV4dCwgbm9kZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0bGV0IG5hbWUgPSAnJztcblx0XHRsZXQga2luZDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvblsna2luZCddIHwgdW5kZWZpbmVkO1xuXHRcdGxldCBkZWNsTm9kZTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvblsnbm9kZSddIHwgdW5kZWZpbmVkO1xuXG5cdFx0aWYgKHRzLmlzVHlwZUFsaWFzRGVjbGFyYXRpb24obm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdG5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRcdGtpbmQgPSAnYWxpYXMnO1xuXHRcdFx0ZGVjbE5vZGUgPSBub2RlO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKG5vZGUpICYmIG5vZGUubmFtZSkge1xuXHRcdFx0bmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0a2luZCA9ICdjbGFzcyc7XG5cdFx0XHRkZWNsTm9kZSA9IG5vZGU7XG5cdFx0fSBlbHNlIGlmICh0cy5pc0ludGVyZmFjZURlY2xhcmF0aW9uKG5vZGUpICYmIHRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpKSB7XG5cdFx0XHRuYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0XHRraW5kID0gJ2ludGVyZmFjZSc7XG5cdFx0XHRkZWNsTm9kZSA9IG5vZGU7XG5cdFx0fVxuXG5cdFx0aWYgKCFraW5kIHx8ICFkZWNsTm9kZSB8fCAhbmFtZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZpbGVQYXRoID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGxldCBkZWNscyA9IHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscy5nZXQoZmlsZVBhdGgpO1xuXHRcdGlmICghZGVjbHMpIHtcblx0XHRcdGRlY2xzID0gbmV3IE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24+KCk7XG5cdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlRGVjbHMuc2V0KGZpbGVQYXRoLCBkZWNscyk7XG5cdFx0fVxuXHRcdGNvbnN0IGVudHJ5OiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uID0geyBraW5kLCBub2RlIDogZGVjbE5vZGUsIGZpbGUgOiBmaWxlUGF0aCB9O1xuXHRcdGRlY2xzLnNldChuYW1lLCBlbnRyeSk7XG5cblx0XHQvLyBgZXhwb3J0IGRlZmF1bHQgY2xhc3MgRm9vIHt9YCBpcyBhbHNvIHJlYWNoYWJsZSB1bmRlciB0aGUgJ2RlZmF1bHQnXG5cdFx0Ly8gYmluZGluZyBmb3IgZGVmYXVsdCBpbXBvcnRlcnNcblx0XHRpZiAoa2luZCA9PT0gJ2NsYXNzJykge1xuXHRcdFx0Y29uc3QgY2xhc3NOb2RlID0gZGVjbE5vZGUgYXMgdHMuQ2xhc3NEZWNsYXJhdGlvbjtcblx0XHRcdGNvbnN0IGlzRXhwb3J0ZWQgPSBjbGFzc05vZGUubW9kaWZpZXJzPy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLkV4cG9ydEtleXdvcmQpID8/IGZhbHNlO1xuXHRcdFx0Y29uc3QgaXNEZWZhdWx0ID0gY2xhc3NOb2RlLm1vZGlmaWVycz8uc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5EZWZhdWx0S2V5d29yZCkgPz8gZmFsc2U7XG5cdFx0XHRpZiAoaXNFeHBvcnRlZCAmJiBpc0RlZmF1bHQpIHtcblx0XHRcdFx0ZGVjbHMuc2V0KCdkZWZhdWx0JywgZW50cnkpO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgY29uc3RzIGluaXRpYWxpemVkIHdpdGggYW4gYXJyYXkgbGl0ZXJhbCAob3B0aW9uYWxseSB3cmFwcGVkIGluXG5cdCAqIGBhcyBjb25zdGAgLyBgc2F0aXNmaWVzYCksIHNvIGEgYHR5cGVvZiBzdGF0dXNMaXN0W251bWJlcl1gIGZpZWxkIHR5cGVcblx0ICogZXhwYW5kcyB0byB0aGUgZWxlbWVudCBsaXRlcmFsIHVuaW9uIOKAlCB0aGUgZ2VuZXJhdGVkIGZpbGUgY2FycmllcyBub1xuXHQgKiBpbXBvcnRzLCBzbyBlbWl0dGluZyB0aGUgYmFyZSBgdHlwZW9mIHN0YXR1c0xpc3RgIHF1ZXJ5IHdvdWxkIGJlIGFuXG5cdCAqIHVucmVzb2x2YWJsZSBuYW1lIGRvd25zdHJlYW0uIEZpcnN0IGJpbmRpbmcgd2luczogYSBuZXN0ZWQgc2hhZG93XG5cdCAqIG11c3Qgbm90IHJlcGxhY2UgdGhlIG1vZHVsZS1sZXZlbCBjb25zdCB0aGUgdHlwZW9mIHJlZmVycyB0by5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tSZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXkgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSB8fCAhdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkgfHwgIW5vZGUuaW5pdGlhbGl6ZXIpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgeyBpbml0aWFsaXplcjogcmF3SW5pdGlhbGl6ZXIgfSA9IG5vZGU7XG5cdFx0bGV0IGluaXRpYWxpemVyOiB0cy5FeHByZXNzaW9uID0gcmF3SW5pdGlhbGl6ZXI7XG5cdFx0d2hpbGUgKHRzLmlzQXNFeHByZXNzaW9uKGluaXRpYWxpemVyKSB8fCB0cy5pc1NhdGlzZmllc0V4cHJlc3Npb24oaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRpbml0aWFsaXplciA9IGluaXRpYWxpemVyLmV4cHJlc3Npb247XG5cdFx0fVxuXHRcdGlmICghdHMuaXNBcnJheUxpdGVyYWxFeHByZXNzaW9uKGluaXRpYWxpemVyKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRsZXQgY29uc3RzID0gdGhpcy5yZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzLmdldChmaWxlUGF0aCk7XG5cdFx0aWYgKCFjb25zdHMpIHtcblx0XHRcdGNvbnN0cyA9IG5ldyBNYXA8c3RyaW5nLCB0cy5BcnJheUxpdGVyYWxFeHByZXNzaW9uPigpO1xuXHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXlzLnNldChmaWxlUGF0aCwgY29uc3RzKTtcblx0XHR9XG5cdFx0aWYgKCFjb25zdHMuaGFzKG5vZGUubmFtZS50ZXh0KSkge1xuXHRcdFx0Y29uc3RzLnNldChub2RlLm5hbWUudGV4dCwgaW5pdGlhbGl6ZXIpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBGaW5kIHRoZSBhcnJheSBsaXRlcmFsIGJlaGluZCBhIG1vZHVsZSBjb25zdCByZWZlcmVuY2VkIHRocm91Z2hcblx0ICogYHR5cGVvZmA6IHRoZSBkZWNsYXJpbmcgZmlsZSdzIG93biBjb25zdHMgZmlyc3QgKHRoZSBGMTMgY2FzZSBpcyBhXG5cdCAqIE5PTi1leHBvcnRlZCBjb25zdCBpbiB0aGUgc2FtZSBtb2R1bGUgYXMgdGhlIGV4cGFuZGVkIGNsYXNzKSwgdGhlbiDigJRcblx0ICogd2hlbiB0aGUgZmlsZSBpbXBvcnRzIHRoZSBuYW1lIOKAlCB0aGUgaW1wb3J0ZWQgbW9kdWxlJ3MgY29uc3RzLlxuXHQgKiBFeHRlcm5hbCBtb2R1bGVzIGFyZSBuZXZlciBhbmFseXplZCwgc28gdGhvc2UgeWllbGQgbm90aGluZy5cblx0ICovXG5cdHByaXZhdGUgZmluZFJlZmVyZW5jZWRDb25zdEFycmF5IChcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0ZnJvbUZpbGU6IHN0cmluZ1xuXHQpOiB0cy5BcnJheUxpdGVyYWxFeHByZXNzaW9uIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBsb2NhbCA9IHRoaXMucmVmZXJlbmNlZFR5cGVDb25zdEFycmF5cy5nZXQoZnJvbUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGxvY2FsKSB7XG5cdFx0XHRyZXR1cm4gbG9jYWw7XG5cdFx0fVxuXHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KGZyb21GaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGlmICghaW1wb3J0ZWQgfHwgaW1wb3J0ZWQuaXNOYW1lc3BhY2UpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShpbXBvcnRlZC5zcGVjaWZpZXIsIGZyb21GaWxlKTtcblx0XHRpZiAoIXJlc29sdXRpb24gfHwgcmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBmb3VuZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVDb25zdEFycmF5cy5nZXQocmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgpPy5nZXQoaW1wb3J0ZWQub3JpZ2luYWxOYW1lKTtcblx0XHRyZXR1cm4gZm91bmQ7XG5cdH1cblxuXHQvKipcblx0ICogRWxlbWVudCBsaXRlcmFsIHR5cGVzIG9mIGEgdHJhY2tlZCBjb25zdCBhcnJheTogZXZlcnkgZWxlbWVudCBtdXN0IGJlXG5cdCAqIGEgcGxhaW4gbGl0ZXJhbCAob3B0aW9uYWxseSB3cmFwcGVkIGluIGBhcyBjb25zdGAgLyBgc2F0aXNmaWVzYCkg4oCUXG5cdCAqIHN0cmluZywgbnVtZXJpYywgYm9vbGVhbiwgb3IgbnVsbC4gU3ByZWFkcywgaWRlbnRpZmllcnMsIGFuZCBuZXN0ZWRcblx0ICogYXJyYXlzIG1lYW4gdGhlIHVuaW9uIGlzIG5vdCBzdGF0aWNhbGx5IHZpc2libGUgYW5kIHlpZWxkIHVuZGVmaW5lZCxcblx0ICogc28gdGhlIGNhbGxlciBkZWdyYWRlcyB0aGUgZmllbGQgdG8gYHVua25vd25gIHJhdGhlciB0aGFuIGd1ZXNzaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBsaXRlcmFsVHlwZXNPZkFycmF5IChhcnJheUxpdGVyYWw6IHRzLkFycmF5TGl0ZXJhbEV4cHJlc3Npb24pOiBzdHJpbmdbXSB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgbGl0ZXJhbHM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGFycmF5TGl0ZXJhbC5lbGVtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzU3ByZWFkRWxlbWVudChlbGVtZW50KSkge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0bGV0IGV4cHI6IHRzLkV4cHJlc3Npb24gPSBlbGVtZW50O1xuXHRcdFx0d2hpbGUgKHRzLmlzQXNFeHByZXNzaW9uKGV4cHIpIHx8IHRzLmlzU2F0aXNmaWVzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0XHRleHByID0gZXhwci5leHByZXNzaW9uO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChleHByKSB8fCB0cy5pc05vU3Vic3RpdHV0aW9uVGVtcGxhdGVMaXRlcmFsKGV4cHIpKSB7XG5cdFx0XHRcdGxpdGVyYWxzLnB1c2goYCcke2V4cHIudGV4dH0nYCk7XG5cdFx0XHR9IGVsc2UgaWYgKHRzLmlzTnVtZXJpY0xpdGVyYWwoZXhwcikpIHtcblx0XHRcdFx0bGl0ZXJhbHMucHVzaChleHByLnRleHQpO1xuXHRcdFx0fSBlbHNlIGlmIChleHByLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVHJ1ZUtleXdvcmQpIHtcblx0XHRcdFx0bGl0ZXJhbHMucHVzaCgndHJ1ZScpO1xuXHRcdFx0fSBlbHNlIGlmIChleHByLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkKSB7XG5cdFx0XHRcdGxpdGVyYWxzLnB1c2goJ2ZhbHNlJyk7XG5cdFx0XHR9IGVsc2UgaWYgKGV4cHIua2luZCA9PT0gdHMuU3ludGF4S2luZC5OdWxsS2V5d29yZCkge1xuXHRcdFx0XHRsaXRlcmFscy5wdXNoKCdudWxsJyk7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAobGl0ZXJhbHMubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBsaXRlcmFscztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEVtaXQtdHlwZSBmb3IgYHR5cGVvZiBuYW1lYCB3aGVuIGBuYW1lYCBpcyBhIHRyYWNrZWQgY29uc3QgYXJyYXk6IHRoZVxuXHQgKiB1bmlvbiBvZiBpdHMgZWxlbWVudCBsaXRlcmFsIHR5cGVzIChgJ2FjdGl2ZScgfCAnY2xvc2VkJ2ApLiBFdmVyeVxuXHQgKiBvdGhlciB0eXBlb2Ygc291cmNlIOKAlCBub24tYXJyYXkgY29uc3RzLCBmdW5jdGlvbnMsIGNsYXNzZXMsIG5hbWVzIG5vdFxuXHQgKiB0cmFja2VkIGF0IGFsbCDigJQgeWllbGRzIHVuZGVmaW5lZCwgc28gdGhlIGNhbGxlciBkZWdyYWRlcyB0aGUgZmllbGRcblx0ICogdG8gYHVua25vd25gOiBhIGJhcmUgYHR5cGVvZiBuYW1lYCBlbWl0dGVkIGludG8gdHlwZXMudHMgaGFzIG5vXG5cdCAqIGltcG9ydCB0byByZXNvbHZlIGFnYWluc3QgZG93bnN0cmVhbS5cblx0ICovXG5cdHByaXZhdGUgdHlwZU9mQ29uc3RBcnJheVVuaW9uIChuYW1lOiBzdHJpbmcsIGZyb21GaWxlOiBzdHJpbmcpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGFycmF5TGl0ZXJhbCA9IHRoaXMuZmluZFJlZmVyZW5jZWRDb25zdEFycmF5KG5hbWUsIGZyb21GaWxlKTtcblx0XHRpZiAoIWFycmF5TGl0ZXJhbCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgbGl0ZXJhbHMgPSB0aGlzLmxpdGVyYWxUeXBlc09mQXJyYXkoYXJyYXlMaXRlcmFsKTtcblx0XHRpZiAoIWxpdGVyYWxzKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCB1bmlvbiA9IGxpdGVyYWxzLmpvaW4oJyB8ICcpO1xuXHRcdHJldHVybiB1bmlvbjtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgdGhlIGltcG9ydGluZyBmaWxlJ3MgbmFtZWQvbmFtZXNwYWNlL2RlZmF1bHQgaW1wb3J0IGJpbmRpbmdzIHNvXG5cdCAqIHJlZmVyZW5jZWQtdHlwZSBuYW1lcyByZXNvbHZlIHRocm91Z2ggdGhlIGZpbGUncyBvd24gaW1wb3J0IHN0YXRlbWVudHNcblx0ICogKEYxMCkgcmF0aGVyIHRoYW4gYSBwcm9ncmFtLXdpZGUgbmFtZSBtYXAuXG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrUmVmZXJlbmNlZFR5cGVJbXBvcnQgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzSW1wb3J0RGVjbGFyYXRpb24obm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgeyBtb2R1bGVTcGVjaWZpZXIgfSA9IG5vZGU7XG5cdFx0aWYgKCF0cy5pc1N0cmluZ0xpdGVyYWwobW9kdWxlU3BlY2lmaWVyKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBjbGF1c2UgPSBub2RlLmltcG9ydENsYXVzZTtcblx0XHRpZiAoIWNsYXVzZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZpbGVQYXRoID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGxldCBpbXBvcnRzID0gdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KGZpbGVQYXRoKTtcblx0XHRpZiAoIWltcG9ydHMpIHtcblx0XHRcdGltcG9ydHMgPSBuZXcgTWFwPHN0cmluZywgUmVmZXJlbmNlZFR5cGVJbXBvcnQ+KCk7XG5cdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5zZXQoZmlsZVBhdGgsIGltcG9ydHMpO1xuXHRcdH1cblxuXHRcdC8vIGltcG9ydCB7IFNoYXJlZFNoYXBlIH0gZnJvbSAn4oCmJyAvIGltcG9ydCB7IFNoYXJlZFNoYXBlIGFzIFMgfSBmcm9tICfigKYnXG5cdFx0aWYgKGNsYXVzZS5uYW1lZEJpbmRpbmdzICYmIHRzLmlzTmFtZWRJbXBvcnRzKGNsYXVzZS5uYW1lZEJpbmRpbmdzKSkge1xuXHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGNsYXVzZS5uYW1lZEJpbmRpbmdzLmVsZW1lbnRzKSB7XG5cdFx0XHRcdGNvbnN0IGxvY2FsTmFtZSA9IGVsZW1lbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBvcmlnaW5hbE5hbWUgPSBlbGVtZW50LnByb3BlcnR5TmFtZSA/IGVsZW1lbnQucHJvcGVydHlOYW1lLnRleHQgOiBsb2NhbE5hbWU7XG5cdFx0XHRcdGltcG9ydHMuc2V0KGxvY2FsTmFtZSwge1xuXHRcdFx0XHRcdG9yaWdpbmFsTmFtZSxcblx0XHRcdFx0XHRzcGVjaWZpZXIgICA6IG1vZHVsZVNwZWNpZmllci50ZXh0LFxuXHRcdFx0XHRcdGlzTmFtZXNwYWNlIDogZmFsc2Vcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0ICogYXMgbW9kZWxzIGZyb20gJ+KApicg4oCUIHJlc29sdmVkIHdoZW4gYSBxdWFsaWZpZWQgbmFtZVxuXHRcdC8vIChtb2RlbHMuU2hhcmVkU2hhcGUpIGlzIGVuY291bnRlcmVkXG5cdFx0aWYgKGNsYXVzZS5uYW1lZEJpbmRpbmdzICYmIHRzLmlzTmFtZXNwYWNlSW1wb3J0KGNsYXVzZS5uYW1lZEJpbmRpbmdzKSkge1xuXHRcdFx0aW1wb3J0cy5zZXQoY2xhdXNlLm5hbWVkQmluZGluZ3MubmFtZS50ZXh0LCB7XG5cdFx0XHRcdG9yaWdpbmFsTmFtZSA6ICcnLFxuXHRcdFx0XHRzcGVjaWZpZXIgICAgOiBtb2R1bGVTcGVjaWZpZXIudGV4dCxcblx0XHRcdFx0aXNOYW1lc3BhY2UgIDogdHJ1ZVxuXHRcdFx0fSk7XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0IFNoYXJlZFNoYXBlIGZyb20gJ+KApicgKGRlZmF1bHQgaW1wb3J0KVxuXHRcdGlmIChjbGF1c2UubmFtZSkge1xuXHRcdFx0aW1wb3J0cy5zZXQoY2xhdXNlLm5hbWUudGV4dCwge1xuXHRcdFx0XHRvcmlnaW5hbE5hbWUgOiAnZGVmYXVsdCcsXG5cdFx0XHRcdHNwZWNpZmllciAgICA6IG1vZHVsZVNwZWNpZmllci50ZXh0LFxuXHRcdFx0XHRpc05hbWVzcGFjZSAgOiBmYWxzZVxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCByZS1leHBvcnQgd2lyaW5nIChgZXhwb3J0IHsgWCB9IGZyb20gJ+KApidgLCBgZXhwb3J0ICogZnJvbSAn4oCmJ2AsXG5cdCAqIGBleHBvcnQgeyBYIGFzIFkgfWApIHNvIHJlc29sdXRpb24gY2FuIGNoYXNlIGJhcnJlbHMgdG8gdGhlIG9yaWdpblxuXHQgKiBtb2R1bGUuIE1pcnJvcnMgTW9kdWxlR3JhcGhCdWlsZGVyLnJlc29sdmVPcmlnaW4sIG5hbWUtYmFzZWQgb25seS5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tSZWZlcmVuY2VkVHlwZVJlRXhwb3J0IChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc0V4cG9ydERlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGZpbGVQYXRoID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGNvbnN0IHsgbW9kdWxlU3BlY2lmaWVyIH0gPSBub2RlO1xuXHRcdGNvbnN0IHNwZWNpZmllclRleHQgPSBtb2R1bGVTcGVjaWZpZXIgJiYgdHMuaXNTdHJpbmdMaXRlcmFsKG1vZHVsZVNwZWNpZmllcilcblx0XHRcdD8gbW9kdWxlU3BlY2lmaWVyLnRleHRcblx0XHRcdDogdW5kZWZpbmVkO1xuXG5cdFx0aWYgKG5vZGUuZXhwb3J0Q2xhdXNlICYmIHRzLmlzTmFtZWRFeHBvcnRzKG5vZGUuZXhwb3J0Q2xhdXNlKSkge1xuXHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIG5vZGUuZXhwb3J0Q2xhdXNlLmVsZW1lbnRzKSB7XG5cdFx0XHRcdGNvbnN0IGV4cG9ydGVkTmFtZSA9IGVsZW1lbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBsb2NhbE5hbWUgPSBlbGVtZW50LnByb3BlcnR5TmFtZSA/IGVsZW1lbnQucHJvcGVydHlOYW1lLnRleHQgOiBleHBvcnRlZE5hbWU7XG5cdFx0XHRcdGlmIChzcGVjaWZpZXJUZXh0KSB7XG5cdFx0XHRcdFx0Ly8gZXhwb3J0IHsgWCB9IGZyb20gJ+KApicgLyBleHBvcnQgeyBYIGFzIFkgfSBmcm9tICfigKYnXG5cdFx0XHRcdFx0bGV0IHJlRXhwb3J0cyA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuZ2V0KGZpbGVQYXRoKTtcblx0XHRcdFx0XHRpZiAoIXJlRXhwb3J0cykge1xuXHRcdFx0XHRcdFx0cmVFeHBvcnRzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0XHRcdFx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuc2V0KGZpbGVQYXRoLCByZUV4cG9ydHMpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRyZUV4cG9ydHMuc2V0KGV4cG9ydGVkTmFtZSwgc3BlY2lmaWVyVGV4dCk7XG5cdFx0XHRcdH0gZWxzZSBpZiAobG9jYWxOYW1lICE9PSBleHBvcnRlZE5hbWUpIHtcblx0XHRcdFx0XHQvLyBleHBvcnQgeyBYIGFzIFkgfSDigJQgc2FtZS1maWxlIGFsaWFzIG9mIGEgbG9jYWwgZGVjbGFyYXRpb25cblx0XHRcdFx0XHRsZXQgYWxpYXNlcyA9IHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRBbGlhc2VzLmdldChmaWxlUGF0aCk7XG5cdFx0XHRcdFx0aWYgKCFhbGlhc2VzKSB7XG5cdFx0XHRcdFx0XHRhbGlhc2VzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0XHRcdFx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRBbGlhc2VzLnNldChmaWxlUGF0aCwgYWxpYXNlcyk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdGFsaWFzZXMuc2V0KGV4cG9ydGVkTmFtZSwgbG9jYWxOYW1lKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGlmIChub2RlLmV4cG9ydENsYXVzZSAmJiB0cy5pc05hbWVzcGFjZUV4cG9ydChub2RlLmV4cG9ydENsYXVzZSkpIHtcblx0XHRcdC8vIGBleHBvcnQgKiBhcyBucyBmcm9tICfigKYnYCDigJQgYSBuZXN0ZWQgbW9kdWxlIG5hbWVzcGFjZTsgbWlkZGxlXG5cdFx0XHQvLyBzZWdtZW50cyBvZiBxdWFsaWZpZWQgcmVmZXJlbmNlcyAoYmFycmVsLkRlZXAuR2FkZ2V0KSBjaGFzZSBpdFxuXHRcdFx0aWYgKHNwZWNpZmllclRleHQpIHtcblx0XHRcdFx0bGV0IHN0YXJzID0gdGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZVN0YXJzLmdldChmaWxlUGF0aCk7XG5cdFx0XHRcdGlmICghc3RhcnMpIHtcblx0XHRcdFx0XHRzdGFycyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZVN0YXJzLnNldChmaWxlUGF0aCwgc3RhcnMpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHN0YXJzLnNldChub2RlLmV4cG9ydENsYXVzZS5uYW1lLnRleHQsIHNwZWNpZmllclRleHQpO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGlmICghbm9kZS5leHBvcnRDbGF1c2UgJiYgc3BlY2lmaWVyVGV4dCkge1xuXHRcdFx0Ly8gZXhwb3J0ICogZnJvbSAn4oCmJ1xuXHRcdFx0bGV0IHN0YXJzID0gdGhpcy5yZWZlcmVuY2VkVHlwZUV4cG9ydFN0YXJzLmdldChmaWxlUGF0aCk7XG5cdFx0XHRpZiAoIXN0YXJzKSB7XG5cdFx0XHRcdHN0YXJzID0gW107XG5cdFx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycy5zZXQoZmlsZVBhdGgsIHN0YXJzKTtcblx0XHRcdH1cblx0XHRcdHN0YXJzLnB1c2goc3BlY2lmaWVyVGV4dCk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSBtb2R1bGUgc3BlY2lmaWVyIGZyb20gYSBjb250YWluaW5nIGZpbGUgd2l0aCB0aGUgcHJvZ3JhbSdzXG5cdCAqIGNvbXBpbGVyT3B0aW9ucyAodHNjb25maWcgYHBhdGhzYCwgZXh0ZW5zaW9ubGVzcyBpbXBvcnRzLCBpbmRleCBmaWxlcykuXG5cdCAqIE1vZHVsZSByZXNvbHV0aW9uIG9ubHkg4oCUIHRoZSBuby1nZXRUeXBlQ2hlY2tlcigpIHByZWNlZGVudCBzdGF5cy5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlIChzcGVjaWZpZXI6IHN0cmluZywgY29udGFpbmluZ0ZpbGU6IHN0cmluZyk6XG5cdFx0UmVmZXJlbmNlZFR5cGVSZXNvbHV0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBjYWNoZUtleSA9IGAke2NvbnRhaW5pbmdGaWxlfTo6JHtzcGVjaWZpZXJ9YDtcblx0XHRpZiAodGhpcy5yZWZlcmVuY2VkVHlwZVJlc29sdXRpb25DYWNoZS5oYXMoY2FjaGVLZXkpKSB7XG5cdFx0XHRjb25zdCBjYWNoZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbkNhY2hlLmdldChjYWNoZUtleSk7XG5cdFx0XHRyZXR1cm4gY2FjaGVkID09PSB1bmRlZmluZWQgPyB1bmRlZmluZWQgOiBjYWNoZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRzLnJlc29sdmVNb2R1bGVOYW1lKFxuXHRcdFx0c3BlY2lmaWVyLFxuXHRcdFx0Y29udGFpbmluZ0ZpbGUsXG5cdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlQ29tcGlsZXJPcHRpb25zLFxuXHRcdFx0dHMuc3lzXG5cdFx0KS5yZXNvbHZlZE1vZHVsZTtcblxuXHRcdGNvbnN0IHJlc3VsdDogUmVmZXJlbmNlZFR5cGVSZXNvbHV0aW9uIHwgdW5kZWZpbmVkID0gcmVzb2x1dGlvblxuXHRcdFx0PyB7XG5cdFx0XHRcdHJlc29sdmVkUGF0aCA6IG5vZGVQYXRoLnJlc29sdmUocmVzb2x1dGlvbi5yZXNvbHZlZEZpbGVOYW1lKSxcblx0XHRcdFx0aXNFeHRlcm5hbCAgIDogISFyZXNvbHV0aW9uLmlzRXh0ZXJuYWxMaWJyYXJ5SW1wb3J0XG5cdFx0XHR9XG5cdFx0XHQ6IHVuZGVmaW5lZDtcblxuXHRcdHRoaXMucmVmZXJlbmNlZFR5cGVSZXNvbHV0aW9uQ2FjaGUuc2V0KGNhY2hlS2V5LCByZXN1bHQpO1xuXHRcdGNvbnN0IGZpbmFsUmVzdWx0ID0gcmVzdWx0O1xuXHRcdHJldHVybiBmaW5hbFJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBMb29rIHVwIGEgbmFtZSBpbiBvbmUgcmVzb2x2ZWQgbW9kdWxlLCBjaGFzaW5nIHJlLWV4cG9ydCBiYXJyZWxzIHdpdGggYVxuXHQgKiBib3VuZGVkIGRlcHRoLiBFeHRlcm5hbCAobm9kZV9tb2R1bGVzKSBtb2R1bGVzIGhvbGQgbm8gaW4tcHJvamVjdFxuXHQgKiBkZWNsYXJhdGlvbnMgYW5kIHN0b3AgdGhlIGNoYXNlLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZSAoXG5cdFx0bW9kdWxlUGF0aDogc3RyaW5nLFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRkZXB0aDogbnVtYmVyXG5cdCk6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGlmIChkZXB0aCA+IE1BWF9SRUVYUE9SVF9DSEFTRV9ERVBUSCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBkZWNscyA9IHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0Y29uc3QgZGlyZWN0ID0gZGVjbHM/LmdldChuYW1lKTtcblx0XHRpZiAoZGlyZWN0KSB7XG5cdFx0XHRyZXR1cm4gZGlyZWN0O1xuXHRcdH1cblx0XHQvLyBleHBvcnQgeyBYIGFzIFkgfSDigJQgcmVzb2x2ZSB0aHJvdWdoIHRoZSBsb2NhbCBuYW1lXG5cdFx0Y29uc3QgbG9jYWxBbGlhcyA9IHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRBbGlhc2VzLmdldChtb2R1bGVQYXRoKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChsb2NhbEFsaWFzKSB7XG5cdFx0XHRjb25zdCBhbGlhc2VkID0gZGVjbHM/LmdldChsb2NhbEFsaWFzKTtcblx0XHRcdGlmIChhbGlhc2VkKSB7XG5cdFx0XHRcdHJldHVybiBhbGlhc2VkO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGNvbnN0IHJlRXhwb3J0cyA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGNvbnN0IHJlRXhwb3J0U3BlY2lmaWVyID0gcmVFeHBvcnRzPy5nZXQobmFtZSk7XG5cdFx0aWYgKHJlRXhwb3J0U3BlY2lmaWVyKSB7XG5cdFx0XHRjb25zdCBuZXh0UmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKHJlRXhwb3J0U3BlY2lmaWVyLCBtb2R1bGVQYXRoKTtcblx0XHRcdGlmIChuZXh0UmVzb2x1dGlvbiAmJiAhbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRjb25zdCBmb3VuZCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUobmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBuYW1lLCBkZXB0aCArIDEpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCBzdGFycyA9IHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0aWYgKHN0YXJzKSB7XG5cdFx0XHRmb3IgKGNvbnN0IHN0YXJTcGVjaWZpZXIgb2Ygc3RhcnMpIHtcblx0XHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShzdGFyU3BlY2lmaWVyLCBtb2R1bGVQYXRoKTtcblx0XHRcdFx0aWYgKCFuZXh0UmVzb2x1dGlvbiB8fCBuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgbmFtZSwgZGVwdGggKyAxKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgcmVmZXJlbmNlZCB0eXBlIG5hbWUgYXMgdXNlZCBpbiBmcm9tRmlsZSwgaW1wb3J0LWF3YXJlOlxuXHQgKiAgIDEuIHRoZSBmaWxlJ3Mgb3duIGltcG9ydCBzdGF0ZW1lbnRzIChyZWxhdGl2ZSArIHRzY29uZmlnIHBhdGhzLFxuXHQgKiAgICAgIGNoYXNlZCB0aHJvdWdoIHJlLWV4cG9ydCBiYXJyZWxzKSxcblx0ICogICAyLiB0aGUgZmlsZSdzIGxvY2FsIGRlY2xhcmF0aW9ucyxcblx0ICogICAzLiB0aGUgdW5pcXVlIHNhbWUtbmFtZWQgZGVjbGFyYXRpb24gYWNyb3NzIHNjYW5uZWQgZmlsZXMuXG5cdCAqIFJldHVybnMgdW5kZWZpbmVkIHdoZW4gbm90aGluZyBtYXRjaGVzIChvciB0aGUgbWF0Y2ggaXMgYW1iaWd1b3VzKSxcblx0ICogaW4gd2hpY2ggY2FzZSB0aGUgY2FsbGVyIGZhbGxzIGJhY2sgdG8gYHVua25vd25gLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiAoXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdGZyb21GaWxlOiBzdHJpbmdcblx0KTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gMS4gdGhlIGZpbGUncyBvd24gaW1wb3J0cyB3aW4g4oCUIGFuIGltcG9ydCBpcyBuZXZlciBzaGFkb3dlZCBieSBhXG5cdFx0Ly8gc2FtZS1uYW1lZCBsb2NhbCBkZWNsYXJhdGlvbiBlbHNld2hlcmUgaW4gdGhlIHByb2dyYW0gKEYxMClcblx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldChmcm9tRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAoaW1wb3J0ZWQgJiYgIWltcG9ydGVkLmlzTmFtZXNwYWNlKSB7XG5cdFx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoaW1wb3J0ZWQuc3BlY2lmaWVyLCBmcm9tRmlsZSk7XG5cdFx0XHRpZiAocmVzb2x1dGlvbiAmJiAhcmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZShyZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgaW1wb3J0ZWQub3JpZ2luYWxOYW1lLCAwKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gMi4gbG9jYWwgZGVjbGFyYXRpb24gaW4gdGhlIHJlZmVyZW5jaW5nIGZpbGUgaXRzZWxmXG5cdFx0Y29uc3QgbG9jYWwgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRGVjbHMuZ2V0KGZyb21GaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChsb2NhbCkge1xuXHRcdFx0cmV0dXJuIGxvY2FsO1xuXHRcdH1cblxuXHRcdC8vIDMuIHByb2dyYW0td2lkZSBmYWxsYmFjaywgdW5pcXVlIGRlY2xhcmF0aW9uIG9ubHkg4oCUIGFtYmlndWl0eSBhbmRcblx0XHQvLyBhYnNlbmNlIGJvdGggeWllbGQgdW5kZWZpbmVkICh0aGUgY2FsbGVyIGVtaXRzIGB1bmtub3duYCkuXG5cdFx0Ly8gRXh0ZXJuYWwvYW1iaWVudCBkZWNsYXJhdGlvbnMgKC5kLnRzLCBub2RlX21vZHVsZXMpIGRvIG5vdFxuXHRcdC8vIHBhcnRpY2lwYXRlOiBhIHVzZXItbG9jYWwgZGVjbGFyYXRpb24gYWx3YXlzIHdpbnMgb3ZlciBhXG5cdFx0Ly8gcGFja2FnZS1kZWNsYXJlZCBzYW1lLW5hbWVkIHR5cGUgKHRoZSBwbGFpbi1UUyB0aWVyIG9mIHRoZVxuXHRcdC8vIGlkZW50aXR5IGxhdzsgYW1iaWd1aXR5IGFtb25nIHRoZSByZW1haW5pbmcgZGVjbGFyYXRpb25zIGlzXG5cdFx0Ly8gdmFsaWRhdGVkIHNlcGFyYXRlbHkgYXMgYSBoYXJkIGZhaWwpXG5cdFx0bGV0IHVuaXF1ZTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZDtcblx0XHRsZXQgY291bnQgPSAwO1xuXHRcdGZvciAoY29uc3QgWyBmaWxlUGF0aCwgZGVjbHMgXSBvZiB0aGlzLnJlZmVyZW5jZWRUeXBlRGVjbHMpIHtcblx0XHRcdGlmICh0aGlzLmlzRXh0ZXJuYWxEZWNsRmlsZShmaWxlUGF0aCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBjYW5kaWRhdGUgPSBkZWNscy5nZXQobmFtZSk7XG5cdFx0XHRpZiAoY2FuZGlkYXRlKSB7XG5cdFx0XHRcdGNvdW50Kys7XG5cdFx0XHRcdHVuaXF1ZSA9IGNhbmRpZGF0ZTtcblx0XHRcdFx0aWYgKGNvdW50ID4gMSkge1xuXHRcdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCByZXN1bHQgPSBjb3VudCA9PT0gMSA/IHVuaXF1ZSA6IHVuZGVmaW5lZDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dGVybmFsL2FtYmllbnQgZGVjbGFyYXRpb24gZmlsZXMgKC5kLnRzLCBhbnl0aGluZyB1bmRlclxuXHQgKiBub2RlX21vZHVsZXMpIG5ldmVyIHBhcnRpY2lwYXRlIGluIHBsYWluLVRTIHJlZmVyZW5jZWQtdHlwZVxuXHQgKiByZXNvbHV0aW9uIG9yIHRoZSBhbWJpZ3VpdHkgbGF3OiB0aGV5IGFyZSBub3QgcHJvamVjdCBzb3VyY2UsIHRoZVxuXHQgKiBDTEkgbmV2ZXIgYW5hbHl6ZXMgdGhlbSwgYW5kIGEgdXNlci1sb2NhbCBkZWNsYXJhdGlvbiBhbHdheXMgd2luc1xuXHQgKiBvdmVyIGEgcGFja2FnZS1kZWNsYXJlZCBzYW1lLW5hbWVkIHR5cGUuXG5cdCAqL1xuXHRwcml2YXRlIGlzRXh0ZXJuYWxEZWNsRmlsZSAoZmlsZTogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgZXh0ZXJuYWwgPSBmaWxlLmVuZHNXaXRoKCcuZC50cycpIHx8XG5cdFx0XHRmaWxlLmluY2x1ZGVzKGAke25vZGVQYXRoLnNlcH1ub2RlX21vZHVsZXMke25vZGVQYXRoLnNlcH1gKTtcblx0XHRyZXR1cm4gZXh0ZXJuYWw7XG5cdH1cblxuXHQvKipcblx0ICogUHJvcGVydGllcyBvZiBhIHJlZmVyZW5jZWQgY2xhc3MvaW50ZXJmYWNlL2FsaWFzLW9mLWxpdGVyYWwgZGVjbGFyYXRpb24sXG5cdCAqIHNoYXJlZCBieSBgdGhpczpgLXBhcmFtZXRlciBleHBhbnNpb24gYW5kIGlubGluZSB0eXBlIGVtaXNzaW9uLlxuXHQgKiBJbmhlcml0ZWQgbWVtYmVycyBhcmUgaW5jbHVkZWQ6IHRoZSBleHRlbmRzIGNoYWluIGlzIHdhbGtlZFxuXHQgKiAoZGVwdGgtY2FwcGVkLCBjeWNsZS1ndWFyZGVkKSBhbmQgcGFyZW50IGZpZWxkcyBtZXJnZSBmaXJzdCwgdGhlXG5cdCAqIGRlY2xhcmF0aW9uJ3Mgb3duIGZpZWxkcyBvdmVycmlkaW5nIG9uIG5hbWUgY2xhc2guXG5cdCAqL1xuXHRwcml2YXRlIHJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXMgKGRlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24pOlxuXHRcdE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHZpc2l0ZWQgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHRjb25zdCBwcm9wZXJ0aWVzID0gdGhpcy5yZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzSW5uZXIoZGVjbCwgdmlzaXRlZCwgMCk7XG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHRwcml2YXRlIHJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXNJbm5lciAoXG5cdFx0ZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbixcblx0XHR2aXNpdGVkOiBTZXQ8c3RyaW5nPixcblx0XHRkZXB0aDogbnVtYmVyXG5cdCk6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IG93blByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXHRcdGNvbnN0IGRlY2xOb2RlID0gZGVjbC5ub2RlIGFzIHRzLkNsYXNzRGVjbGFyYXRpb24gfCB0cy5JbnRlcmZhY2VEZWNsYXJhdGlvbjtcblx0XHRjb25zdCBkZWNsTmFtZSA9IGRlY2xOb2RlLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKGRlY2xOb2RlLm5hbWUpID8gZGVjbE5vZGUubmFtZS50ZXh0IDogJyc7XG5cdFx0Y29uc3QgdmlzaXRLZXkgPSBgJHtkZWNsLmtpbmR9OiR7ZGVjbC5maWxlfToke2RlY2xOYW1lfWA7XG5cdFx0aWYgKGRlcHRoID4gTUFYX0hFUklUQUdFX0RFUFRIIHx8IHZpc2l0ZWQuaGFzKHZpc2l0S2V5KSkge1xuXHRcdFx0cmV0dXJuIG93blByb3BlcnRpZXM7XG5cdFx0fVxuXHRcdHZpc2l0ZWQuYWRkKHZpc2l0S2V5KTtcblxuXHRcdGlmIChkZWNsLmtpbmQgPT09ICdjbGFzcycpIHtcblx0XHRcdGNvbnN0IGNsYXNzUHJvcHMgPSB0aGlzLmV4dHJhY3RDbGFzc1Byb3BlcnRpZXMoZGVjbC5ub2RlIGFzIHRzLkNsYXNzRGVjbGFyYXRpb24pO1xuXHRcdFx0Zm9yIChjb25zdCBbIG5hbWUsIGluZm8gXSBvZiBjbGFzc1Byb3BzKSB7XG5cdFx0XHRcdG93blByb3BlcnRpZXMuc2V0KG5hbWUsIGluZm8pO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSBpZiAoZGVjbC5raW5kID09PSAnaW50ZXJmYWNlJykge1xuXHRcdFx0Y29uc3QgaWZhY2UgPSBkZWNsLm5vZGUgYXMgdHMuSW50ZXJmYWNlRGVjbGFyYXRpb247XG5cdFx0XHR0aGlzLmNvbGxlY3RUeXBlRWxlbWVudFByb3BlcnRpZXMoWyAuLi5pZmFjZS5tZW1iZXJzIF0sIG93blByb3BlcnRpZXMpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHRjb25zdCBhbGlhc1R5cGUgPSAoZGVjbC5ub2RlIGFzIHRzLlR5cGVBbGlhc0RlY2xhcmF0aW9uKS50eXBlO1xuXHRcdFx0aWYgKHRzLmlzVHlwZUxpdGVyYWxOb2RlKGFsaWFzVHlwZSkpIHtcblx0XHRcdFx0dGhpcy5jb2xsZWN0VHlwZUVsZW1lbnRQcm9wZXJ0aWVzKFsgLi4uYWxpYXNUeXBlLm1lbWJlcnMgXSwgb3duUHJvcGVydGllcyk7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRyZXR1cm4gb3duUHJvcGVydGllcztcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBoZXJpdGFnZSBtZXJnZXMgcGFyZW50IGZpZWxkcyBmaXJzdDsgdGhlIGRlY2xhcmF0aW9uJ3Mgb3duIGZpZWxkc1xuXHRcdC8vIG92ZXJyaWRlIG9uIG5hbWUgY2xhc2ggKGxhdGVyIGJhc2VzIG92ZXJyaWRlIGVhcmxpZXIgb25lcylcblx0XHRjb25zdCBtZXJnZWQgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXHRcdGZvciAoY29uc3QgYmFzZURlY2wgb2YgdGhpcy5yZXNvbHZlSGVyaXRhZ2VEZWNsYXJhdGlvbnMoZGVjbCkpIHtcblx0XHRcdGNvbnN0IGJhc2VQcm9wcyA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllc0lubmVyKGJhc2VEZWNsLCB2aXNpdGVkLCBkZXB0aCArIDEpO1xuXHRcdFx0Zm9yIChjb25zdCBbIG5hbWUsIGluZm8gXSBvZiBiYXNlUHJvcHMpIHtcblx0XHRcdFx0bWVyZ2VkLnNldChuYW1lLCBpbmZvKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0Zm9yIChjb25zdCBbIG5hbWUsIGluZm8gXSBvZiBvd25Qcm9wZXJ0aWVzKSB7XG5cdFx0XHRtZXJnZWQuc2V0KG5hbWUsIGluZm8pO1xuXHRcdH1cblx0XHRyZXR1cm4gbWVyZ2VkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb3BlcnR5IHNpZ25hdHVyZXMgb2YgaW50ZXJmYWNlL2FsaWFzIHR5cGUtbGl0ZXJhbCBtZW1iZXJzLCBpbnRvXG5cdCAqIHRoZSBnaXZlbiBtYXAuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RUeXBlRWxlbWVudFByb3BlcnRpZXMgKFxuXHRcdG1lbWJlcnM6IHJlYWRvbmx5IHRzLlR5cGVFbGVtZW50W10sXG5cdFx0cHJvcGVydGllczogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPlxuXHQpOiB2b2lkIHtcblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBtZW1iZXJzKSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChwcm9wTmFtZSwge1xuXHRcdFx0XHRcdG5hbWUgICAgIDogcHJvcE5hbWUsXG5cdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHRoZSBoZXJpdGFnZSBjbGF1c2Ugb2YgYSBjbGFzcyAoYGV4dGVuZHMgQmFzZWApIG9yIGludGVyZmFjZVxuXHQgKiAoYGV4dGVuZHMgQSwgQmApIHRvIHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbnMgdGhyb3VnaCB0aGUgU0FNRVxuXHQgKiBpbXBvcnQtYXdhcmUgbWFjaGluZXJ5IGFzIHBsYWluIHJlZmVyZW5jZXMgKHRoZSBkZWNsYXJpbmcgZmlsZSdzIG93blxuXHQgKiBpbXBvcnRzIGZpcnN0LCB0aGVuIGl0cyBsb2NhbHMsIHRoZW4gdGhlIHVuaXF1ZSBwcm9ncmFtLXdpZGVcblx0ICogZGVjbGFyYXRpb24pLiBVbnJlc29sdmFibGUgb3IgZXh0ZXJuYWwgYmFzZXMgeWllbGQgbm90aGluZyDigJQgdGhlaXJcblx0ICogaW5oZXJpdGVkIGZpZWxkcyBzaW1wbHkgc3RheSBhYnNlbnQsIHNhbWUgYXMgYmVmb3JlIHRoaXMgd2Fsa1xuXHQgKiBleGlzdGVkLiBNaXhpbiBjYWxscyAoYGV4dGVuZHMgbWl4aW4oWClgKSBhbmQgbmFtZXNwYWNlIGFjY2VzcyBhcmVcblx0ICogbm90IGZvbGxvd2VkLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlSGVyaXRhZ2VEZWNsYXJhdGlvbnMgKGRlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24pOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uW10ge1xuXHRcdGNvbnN0IHsgaGVyaXRhZ2VDbGF1c2VzIH0gPSAoZGVjbC5ub2RlIGFzIHRzLkNsYXNzRGVjbGFyYXRpb24gfCB0cy5JbnRlcmZhY2VEZWNsYXJhdGlvbik7XG5cdFx0aWYgKCFoZXJpdGFnZUNsYXVzZXMpIHtcblx0XHRcdHJldHVybiBbXTtcblx0XHR9XG5cdFx0Y29uc3QgYmFzZXM6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25bXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgY2xhdXNlIG9mIGhlcml0YWdlQ2xhdXNlcykge1xuXHRcdFx0aWYgKGNsYXVzZS50b2tlbiAhPT0gdHMuU3ludGF4S2luZC5FeHRlbmRzS2V5d29yZCkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3QgaGVyaXRhZ2VUeXBlIG9mIGNsYXVzZS50eXBlcykge1xuXHRcdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihoZXJpdGFnZVR5cGUuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBiYXNlTmFtZSA9IGhlcml0YWdlVHlwZS5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHRcdGNvbnN0IGJhc2VEZWNsID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihiYXNlTmFtZSwgZGVjbC5maWxlKTtcblx0XHRcdFx0aWYgKGJhc2VEZWNsKSB7XG5cdFx0XHRcdFx0YmFzZXMucHVzaChiYXNlRGVjbCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gYmFzZXM7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHBhbmQgYSByZWZlcmVuY2VkLXR5cGUgZGVjbGFyYXRpb24gdG8gYSBzZWxmLWNvbnRhaW5lZCB0eXBlIHN0cmluZ1xuXHQgKiBmb3IgZW1pc3Npb24gaW50byBnZW5lcmF0ZWQgZmlsZXM6IHR5cGUgYWxpYXNlcyB0aHJvdWdoIGluZmVyVHlwZSxcblx0ICogY2xhc3NlcyBhbmQgaW50ZXJmYWNlcyB0aHJvdWdoIHRoZWlyIChwdWJsaWMsIG5vbi1tZXRob2QpIGZpZWxkcy5cblx0ICogTmVzdGVkIHJlZmVyZW5jZXMgcmVzb2x2ZSBhZ2FpbnN0IHRoZSBkZWNsYXJpbmcgZmlsZSB3aGlsZSBleHBhbmRpbmcuXG5cdCAqL1xuXHRwcml2YXRlIGV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gKGRlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IHJlZmVyZW5jaW5nRmlsZSA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSBkZWNsLmZpbGU7XG5cdFx0dHJ5IHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMuZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbklubmVyKGRlY2wpO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gcmVmZXJlbmNpbmdGaWxlO1xuXHRcdH1cblx0fVxuXG5cdHByaXZhdGUgZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbklubmVyIChkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoZGVjbC5raW5kID09PSAnYWxpYXMnKSB7XG5cdFx0XHRjb25zdCBhbGlhc05vZGUgPSBkZWNsLm5vZGUgYXMgdHMuVHlwZUFsaWFzRGVjbGFyYXRpb247XG5cdFx0XHRjb25zdCBhbGlhc05hbWUgPSB0cy5pc0lkZW50aWZpZXIoYWxpYXNOb2RlLm5hbWUpID8gYWxpYXNOb2RlLm5hbWUudGV4dCA6ICcnO1xuXHRcdFx0aWYgKGFsaWFzTmFtZSAmJiB0aGlzLmV4cGFuZGluZ1JlZmVyZW5jZWRBbGlhc2VzLmhhcyhhbGlhc05hbWUpKSB7XG5cdFx0XHRcdC8vIFNlbGYtcmVmZXJlbnRpYWwgYWxpYXMgY2hhaW4g4oCUIGJhaWwgb3V0XG5cdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHR9XG5cdFx0XHRpZiAoYWxpYXNOYW1lKSB7XG5cdFx0XHRcdHRoaXMuZXhwYW5kaW5nUmVmZXJlbmNlZEFsaWFzZXMuYWRkKGFsaWFzTmFtZSk7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMuaW5mZXJUeXBlKGFsaWFzTm9kZS50eXBlKTtcblx0XHRcdGlmIChhbGlhc05hbWUpIHtcblx0XHRcdFx0dGhpcy5leHBhbmRpbmdSZWZlcmVuY2VkQWxpYXNlcy5kZWxldGUoYWxpYXNOYW1lKTtcblx0XHRcdH1cblx0XHRcdHJldHVybiBleHBhbmRlZDtcblx0XHR9XG5cblx0XHRjb25zdCBkZWNsUHJvcGVydGllcyA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllcyhkZWNsKTtcblx0XHRjb25zdCBwcm9wcyA9IEFycmF5LmZyb20oZGVjbFByb3BlcnRpZXMuZW50cmllcygpKS5tYXAoKFsgcHJvcE5hbWUsIGluZm8gXSkgPT4ge1xuXHRcdFx0Y29uc3Qgb3B0aW9uYWwgPSBpbmZvLm9wdGlvbmFsID8gJz8nIDogJyc7XG5cdFx0XHRyZXR1cm4gYCR7cHJvcE5hbWV9JHtvcHRpb25hbH06ICR7aW5mby50eXBlfWA7XG5cdFx0fSk7XG5cblx0XHRjb25zdCByZXN1bHQgPSBgeyAke3Byb3BzLmpvaW4oJzsgJyl9IH1gO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHNpbXBsZSAobm9uLXF1YWxpZmllZCkgdHlwZSByZWZlcmVuY2U6IGltcG9ydC1hd2FyZVxuXHQgKiBkZWNsYXJhdGlvbiBleHBhbnNpb24gZmlyc3QsIHRoZW4gdGhlIEluc3RhbmNlVHlwZTx0eXBlb2YgWD4gcGF0dGVybixcblx0ICogdGhlbiBtbmVtb25pY2EgZ3JhcGggdHlwZXM7IGtub3duIGdsb2JhbHMga2VlcCB0aGVpciBiYXJlIG5hbWUgYW5kXG5cdCAqIGFueXRoaW5nIGVsc2UgZmFsbHMgYmFjayB0byBgdW5rbm93bmAgc28gZ2VuZXJhdGVkIGZpbGVzIG5ldmVyIGNhcnJ5XG5cdCAqIGFuIHVucmVzb2x2YWJsZSBiYXJlIG5hbWUuIFJldHVybnMgdW5kZWZpbmVkIHdoZW4gdGhlIGNhbGxlciBzaG91bGRcblx0ICoga2VlcCB0aGUgZ2VuZXJpYyBzcGVsbGluZyAoaGFuZGxlZCBzZXBhcmF0ZWx5KS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVNpbXBsZVR5cGVSZWZlcmVuY2UgKFxuXHRcdHR5cGVOYW1lOiBzdHJpbmcsXG5cdFx0dHlwZUFyZ3M/OiB0cy5Ob2RlQXJyYXk8dHMuVHlwZU5vZGU+LFxuXHRcdHJlZk5vZGU/OiB0cy5Ob2RlXG5cdCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gSW1wb3J0LWF3YXJlIHJlZmVyZW5jZWQtdHlwZSBkZWNsYXJhdGlvbiAoRjEwKVxuXHRcdGNvbnN0IGRlY2wgPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKHR5cGVOYW1lLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdGlmIChkZWNsKSB7XG5cdFx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMuZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihkZWNsKTtcblx0XHRcdGlmIChleHBhbmRlZCAhPT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdHJldHVybiBleHBhbmRlZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHVua25vd25SZXN1bHQgPSAndW5rbm93bic7XG5cdFx0XHRyZXR1cm4gdW5rbm93blJlc3VsdDtcblx0XHR9XG5cblx0XHQvLyBNbmVtb25pY2EtZ3JhcGggaWRlbnRpdHkgbGF3OiBwYXRoLWF3YXJlIHJlc29sdXRpb24gKHZhbHVlIHNjb3BlLFxuXHRcdC8vIGltcG9ydHMsIG5lYXJlc3QtY2hhaW4sIHJvb3QsIHByb2dyYW0td2lkZSkuIEFtYmlndWl0eSBiZXR3ZWVuXG5cdFx0Ly8gcmVhbCBncmFwaCB0eXBlcyBpcyBhIGhhcmQgZmFpbHVyZTsgYSBuYW1lIG5vIGdyYXBoIHR5cGUgY2Fycmllc1xuXHRcdC8vIHN0YXlzIGluIHRoZSBwbGFpbi1UUyBzb2Z0IHNjb3BlIGFuZCBmYWxscyB0byBgdW5rbm93bmAuXG5cdFx0Y29uc3QgZ3JhcGhSZXN1bHQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKHR5cGVOYW1lKTtcblx0XHRpZiAoZ3JhcGhSZXN1bHQuc3RhdHVzID09PSAndW5pcXVlJykge1xuXHRcdFx0Ly8gSGFuZGxlIEluc3RhbmNlVHlwZTx0eXBlb2YgWD4gcGF0dGVybiAtPiBjb252ZXJ0IHRvIFBhcmVudF9YXG5cdFx0XHRpZiAodHlwZU5hbWUgPT09ICdJbnN0YW5jZVR5cGUnICYmIHR5cGVBcmdzICYmIHR5cGVBcmdzLmxlbmd0aCA9PT0gMSkge1xuXHRcdFx0XHRjb25zdCBbIGFyZyBdID0gdHlwZUFyZ3M7XG5cdFx0XHRcdGlmIChhcmcua2luZCA9PT0gdHMuU3ludGF4S2luZC5UeXBlUXVlcnkpIHtcblx0XHRcdFx0XHRjb25zdCB0eXBlUXVlcnkgPSBhcmcgYXMgdHMuVHlwZVF1ZXJ5Tm9kZTtcblx0XHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKHR5cGVRdWVyeS5leHByTmFtZSkpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHF1ZXJ5UmVzdWx0ID0gdGhpcy5yZXNvbHZlR3JhcGhUeXBlTmFtZSh0eXBlUXVlcnkuZXhwck5hbWUudGV4dCk7XG5cdFx0XHRcdFx0XHRpZiAocXVlcnlSZXN1bHQuc3RhdHVzID09PSAndW5pcXVlJykge1xuXHRcdFx0XHRcdFx0XHQvLyBDb252ZXJ0IGZ1bGwgcGF0aCB3aXRoIGRvdHMgdG8gdW5kZXJzY29yZXM6IFVzYWdlcy5Vc2FnZUVudHJ5IC0+IFVzYWdlc19Vc2FnZUVudHJ5XG5cdFx0XHRcdFx0XHRcdHJldHVybiBxdWVyeVJlc3VsdC5ub2RlLmZ1bGxQYXRoLnJlcGxhY2UoL1xcLi9nLCAnXycpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKHF1ZXJ5UmVzdWx0LnN0YXR1cyA9PT0gJ2FtYmlndW91cycpIHtcblx0XHRcdFx0XHRcdFx0dGhpcy5yZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yKHR5cGVRdWVyeS5leHByTmFtZS50ZXh0LCB0eXBlUXVlcnksIHF1ZXJ5UmVzdWx0KTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdC8vIE5vdCBhIGtub3duIG1uZW1vbmljYSB0eXBlIOKAlCBubyBiYXJlIGVtaXNzaW9uXG5cdFx0XHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKCF0eXBlQXJncyB8fCB0eXBlQXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdFx0Ly8gQ29udmVydCBmdWxsIHBhdGggd2l0aCBkb3RzIHRvIHVuZGVyc2NvcmVzOiBVc2FnZXMuVXNhZ2VFbnRyeSAtPiBVc2FnZXNfVXNhZ2VFbnRyeVxuXHRcdFx0XHRyZXR1cm4gZ3JhcGhSZXN1bHQubm9kZS5mdWxsUGF0aC5yZXBsYWNlKC9cXC4vZywgJ18nKTtcblx0XHRcdH1cblx0XHRcdC8vIEdlbmVyaWMgdXNlIG9mIGEgZ3JhcGggdHlwZSBrZWVwcyBpdHMgc2ltcGxlIG5hbWU7IHRoZVxuXHRcdFx0Ly8gZ2VuZXJhdG9yIHVwZ3JhZGVzIGl0IHRvIHRoZSBmdWxsLXBhdGggaW5zdGFuY2UgdHlwZSBuYW1lXG5cdFx0XHRyZXR1cm4gYCR7dHlwZU5hbWV9PCR7dHlwZUFyZ3MubWFwKGEgPT4gdGhpcy5pbmZlclR5cGUoYSkpLmpvaW4oJywgJyl9PmA7XG5cdFx0fVxuXHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHR0aGlzLnJlY29yZEdyYXBoUmVmZXJlbmNlRXJyb3IodHlwZU5hbWUsIHJlZk5vZGUgPz8gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlLCBncmFwaFJlc3VsdCk7XG5cdFx0fVxuXG5cdFx0aWYgKHR5cGVBcmdzICYmIHR5cGVBcmdzLmxlbmd0aCA+IDApIHtcblx0XHRcdGlmIChLTk9XTl9HTE9CQUxfVFlQRVMuaGFzKHR5cGVOYW1lKSkge1xuXHRcdFx0XHRjb25zdCBnZW5lcmljUmVzdWx0ID0gYCR7dHlwZU5hbWV9PCR7dHlwZUFyZ3MubWFwKGEgPT4gdGhpcy5pbmZlclR5cGUoYSkpLmpvaW4oJywgJyl9PmA7XG5cdFx0XHRcdHJldHVybiBnZW5lcmljUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0Ly8gR2VuZXJpYyByZWZlcmVuY2UgdG8gYSBub24tZ2xvYmFsLCBub24tZ3JhcGggdHlwZSBjYW5ub3QgYmVcblx0XHRcdC8vIGVtaXR0ZWQgYmFyZSBpbnRvIHRoZSBnZW5lcmF0ZWQgZmlsZVxuXHRcdFx0aWYgKHJlZk5vZGUpIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRQbGFpblR5cGVSZWZlcmVuY2VTaXRlKHR5cGVOYW1lLCByZWZOb2RlKTtcblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmFsbGJhY2tSZXN1bHQgPSB0aGlzLnVucmVzb2x2ZWRUeXBlUmVmZXJlbmNlRmFsbGJhY2sodHlwZU5hbWUsIHJlZk5vZGUpO1xuXHRcdHJldHVybiBmYWxsYmFja1Jlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgcXVhbGlmaWVkIHR5cGUgcmVmZXJlbmNlIChtb2RlbHMuSW5uZXIuQ3JhdGUpIHRocm91Z2ggdGhlXG5cdCAqIGN1cnJlbnQgZmlsZSdzIG5hbWVzcGFjZSBpbXBvcnRzLiBUaGUgY2hhaW4ncyBoZWFkIG11c3QgYmUgYSBuYW1lc3BhY2Vcblx0ICogaW1wb3J0OyBtaWRkbGUgc2VnbWVudHMgZGVzY2VuZCB0aHJvdWdoIG5hbWVzcGFjZSBkZWNsYXJhdGlvbnMsIG5hbWVkXG5cdCAqIHJlLWV4cG9ydHMgb2YgbmFtZXNwYWNlcywgYW5kIGBleHBvcnQgKiBhcyBucyBmcm9tICfigKYnYCBiYXJyZWxzIChlYWNoXG5cdCAqIHNlZ21lbnQgY29uc3VtZWQgZXhhY3RseSBvbmNlLCBzbyB0aGUgd2FsayBjYW5ub3QgY3ljbGUpOyB0aGUgZmluYWxcblx0ICogc2VnbWVudCByZXNvbHZlcyB0byBhIGRlY2xhcmF0aW9uIHdoaWNoIGlzIGV4cGFuZGVkIGlubGluZS4gV2hlbiB0aGVcblx0ICogcHJlY2lzZSB3YWxrIGZpbmRzIG5vdGhpbmcsIHRoZSBsZWdhY3kgcmlnaHRtb3N0LW5hbWUgbG9va3VwIGluIHRoZVxuXHQgKiBoZWFkIG1vZHVsZSBrZWVwcyBvbmUtbGV2ZWwgZm9ybXMgKG1vZGVscy5UeXBlKSB3b3JraW5nIOKAlCBuZXN0ZWRcblx0ICogZGVjbGFyYXRpb25zIGFyZSByZWNvcmRlZCBieSBwbGFpbiBuYW1lIHRoZXJlIHRvby4gUmV0dXJucyB1bmRlZmluZWRcblx0ICogd2hlbiB0aGUgaGVhZCBpcyBub3QgYSBuYW1lc3BhY2UgaW1wb3J0IG9yIG5vdGhpbmcgcmVzb2x2ZXMuXG5cdCAqL1xuXHRwcml2YXRlIGluZmVyUXVhbGlmaWVkVHlwZVJlZmVyZW5jZSAodHlwZVJlZjogdHMuVHlwZVJlZmVyZW5jZU5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghdHMuaXNRdWFsaWZpZWROYW1lKHR5cGVSZWYudHlwZU5hbWUpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIGZsYXR0ZW4gdGhlIHF1YWxpZmllZCBuYW1lIGNoYWluOiBtb2RlbHMuSW5uZXIuQ3JhdGUg4oaSIFsnbW9kZWxzJywgJ0lubmVyJywgJ0NyYXRlJ11cblx0XHRjb25zdCBzZWdtZW50czogc3RyaW5nW10gPSBbXTtcblx0XHRsZXQgY2hhaW46IHRzLkVudGl0eU5hbWUgPSB0eXBlUmVmLnR5cGVOYW1lO1xuXHRcdHdoaWxlICh0cy5pc1F1YWxpZmllZE5hbWUoY2hhaW4pKSB7XG5cdFx0XHRzZWdtZW50cy51bnNoaWZ0KGNoYWluLnJpZ2h0LnRleHQpO1xuXHRcdFx0Y2hhaW4gPSBjaGFpbi5sZWZ0O1xuXHRcdH1cblx0XHRzZWdtZW50cy51bnNoaWZ0KGNoYWluLnRleHQpO1xuXG5cdFx0Y29uc3QgbmFtZXNwYWNlSW1wb3J0ID0gdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChzZWdtZW50c1sgMCBdKTtcblx0XHRpZiAoIW5hbWVzcGFjZUltcG9ydCB8fCAhbmFtZXNwYWNlSW1wb3J0LmlzTmFtZXNwYWNlKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShuYW1lc3BhY2VJbXBvcnQuc3BlY2lmaWVyLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdGlmICghcmVzb2x1dGlvbiB8fCByZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gZGVzY2VuZCB0aGUgbWlkZGxlIHNlZ21lbnRzOiBhIG1vZHVsZSBjb250ZXh0IHJlc29sdmVzIHRoZSBzZWdtZW50XG5cdFx0Ly8gYXMgYSBuYW1lc3BhY2UgZGVjbGFyYXRpb24gLyBuYW1lc3BhY2UgcmUtZXhwb3J0OyBhIG5hbWVzcGFjZS1ibG9ja1xuXHRcdC8vIGNvbnRleHQgcmVzb2x2ZXMgaXQgYXMgYSBuZXN0ZWQgbmFtZXNwYWNlIGRlY2xhcmF0aW9uXG5cdFx0bGV0IHF1YWxpZmllcjogeyBtb2R1bGVQYXRoOiBzdHJpbmc7IGJsb2NrPzogdHMuTW9kdWxlQmxvY2sgfSB8IHVuZGVmaW5lZCA9IHtcblx0XHRcdG1vZHVsZVBhdGggOiByZXNvbHV0aW9uLnJlc29sdmVkUGF0aFxuXHRcdH07XG5cdFx0Zm9yIChsZXQgaSA9IDE7IGkgPCBzZWdtZW50cy5sZW5ndGggLSAxICYmIHF1YWxpZmllcjsgaSsrKSB7XG5cdFx0XHRjb25zdCBzZWdtZW50ID0gc2VnbWVudHNbIGkgXTtcblx0XHRcdGlmIChxdWFsaWZpZXIuYmxvY2spIHtcblx0XHRcdFx0Y29uc3QgbmVzdGVkID0gdGhpcy5maW5kTmFtZXNwYWNlSW5CbG9jayhxdWFsaWZpZXIuYmxvY2ssIHNlZ21lbnQpO1xuXHRcdFx0XHRpZiAobmVzdGVkPy5ib2R5ICYmIHRzLmlzTW9kdWxlQmxvY2sobmVzdGVkLmJvZHkpKSB7XG5cdFx0XHRcdFx0cXVhbGlmaWVyID0geyBtb2R1bGVQYXRoIDogcXVhbGlmaWVyLm1vZHVsZVBhdGgsIGJsb2NrIDogbmVzdGVkLmJvZHkgfTtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRxdWFsaWZpZXIgPSB1bmRlZmluZWQ7XG5cdFx0XHRcdGJyZWFrO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbmFtZXNwYWNlRGVjbDogdHMuTW9kdWxlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQgPVxuXHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlcy5nZXQocXVhbGlmaWVyLm1vZHVsZVBhdGgpPy5nZXQoc2VnbWVudCk7XG5cdFx0XHRpZiAobmFtZXNwYWNlRGVjbD8uYm9keSAmJiB0cy5pc01vZHVsZUJsb2NrKG5hbWVzcGFjZURlY2wuYm9keSkpIHtcblx0XHRcdFx0cXVhbGlmaWVyID0geyBtb2R1bGVQYXRoIDogcXVhbGlmaWVyLm1vZHVsZVBhdGgsIGJsb2NrIDogbmFtZXNwYWNlRGVjbC5ib2R5IH07XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgc3RhclNwZWNpZmllciA9IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VTdGFycy5nZXQocXVhbGlmaWVyLm1vZHVsZVBhdGgpPy5nZXQoc2VnbWVudCk7XG5cdFx0XHRpZiAoc3RhclNwZWNpZmllcikge1xuXHRcdFx0XHRjb25zdCBuZXh0UmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKHN0YXJTcGVjaWZpZXIsIHF1YWxpZmllci5tb2R1bGVQYXRoKTtcblx0XHRcdFx0aWYgKG5leHRSZXNvbHV0aW9uICYmICFuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdFx0cXVhbGlmaWVyID0geyBtb2R1bGVQYXRoIDogbmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoIH07XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGNvbnN0IHJlRXhwb3J0U3BlY2lmaWVyID0gdGhpcy5yZWZlcmVuY2VkVHlwZVJlRXhwb3J0cy5nZXQocXVhbGlmaWVyLm1vZHVsZVBhdGgpPy5nZXQoc2VnbWVudCk7XG5cdFx0XHRpZiAocmVFeHBvcnRTcGVjaWZpZXIpIHtcblx0XHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShyZUV4cG9ydFNwZWNpZmllciwgcXVhbGlmaWVyLm1vZHVsZVBhdGgpO1xuXHRcdFx0XHRjb25zdCByZUV4cG9ydGVkOiB0cy5Nb2R1bGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCA9XG5cdFx0XHRcdFx0bmV4dFJlc29sdXRpb24gJiYgIW5leHRSZXNvbHV0aW9uLmlzRXh0ZXJuYWxcblx0XHRcdFx0XHRcdD8gdGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMuZ2V0KG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCk/LmdldChzZWdtZW50KVxuXHRcdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cdFx0XHRcdGlmIChyZUV4cG9ydGVkPy5ib2R5ICYmIHRzLmlzTW9kdWxlQmxvY2socmVFeHBvcnRlZC5ib2R5KSkge1xuXHRcdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IG5leHRSZXNvbHV0aW9uIS5yZXNvbHZlZFBhdGgsIGJsb2NrIDogcmVFeHBvcnRlZC5ib2R5IH07XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHF1YWxpZmllciA9IHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBmaW5hbE5hbWUgPSBzZWdtZW50c1sgc2VnbWVudHMubGVuZ3RoIC0gMSBdO1xuXHRcdGxldCBkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkO1xuXHRcdGlmIChxdWFsaWZpZXI/LmJsb2NrKSB7XG5cdFx0XHRkZWNsID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbkJsb2NrKHF1YWxpZmllci5ibG9jaywgcXVhbGlmaWVyLm1vZHVsZVBhdGgsIGZpbmFsTmFtZSk7XG5cdFx0fSBlbHNlIGlmIChxdWFsaWZpZXIpIHtcblx0XHRcdGRlY2wgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKHF1YWxpZmllci5tb2R1bGVQYXRoLCBmaW5hbE5hbWUsIDApO1xuXHRcdH1cblx0XHQvLyBsZWdhY3kgZmFsbGJhY2s6IHJpZ2h0bW9zdCBuYW1lIGFueXdoZXJlIGluIHRoZSBoZWFkIG1vZHVsZVxuXHRcdC8vIChuYW1lc3BhY2UtbmVzdGVkIGRlY2xhcmF0aW9ucyBhcmUgYWxzbyByZWNvcmRlZCBieSBwbGFpbiBuYW1lKVxuXHRcdGlmICghZGVjbCkge1xuXHRcdFx0ZGVjbCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUocmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIGZpbmFsTmFtZSwgMCk7XG5cdFx0fVxuXHRcdGlmICghZGVjbCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMuZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihkZWNsKTtcblx0XHRyZXR1cm4gZXhwYW5kZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmluZCBhIG5hbWVzcGFjZSBkZWNsYXJhdGlvbiBieSBuYW1lIGRpcmVjdGx5IGluc2lkZSBhIG1vZHVsZSBibG9jay5cblx0ICovXG5cdHByaXZhdGUgZmluZE5hbWVzcGFjZUluQmxvY2sgKGJsb2NrOiB0cy5Nb2R1bGVCbG9jaywgbmFtZTogc3RyaW5nKTogdHMuTW9kdWxlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIGJsb2NrLnN0YXRlbWVudHMpIHtcblx0XHRcdGlmICh0cy5pc01vZHVsZURlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiYgdHMuaXNJZGVudGlmaWVyKHN0YXRlbWVudC5uYW1lKSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdCA9IHN0YXRlbWVudDtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGaW5kIGEgbmFtZWQgdHlwZSBkZWNsYXJhdGlvbiAoYWxpYXMsIGNsYXNzLCBpbnRlcmZhY2UpIGRpcmVjdGx5IGluc2lkZVxuXHQgKiBhIG5hbWVzcGFjZSBibG9jayDigJQgdGhlIGZpbmFsIHNlZ21lbnQgb2YgYSBkZXNjZW5kZWQgcXVhbGlmaWVkIGNoYWluLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kUmVmZXJlbmNlZFR5cGVJbkJsb2NrIChcblx0XHRibG9jazogdHMuTW9kdWxlQmxvY2ssXG5cdFx0ZmlsZVBhdGg6IHN0cmluZyxcblx0XHRuYW1lOiBzdHJpbmdcblx0KTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2YgYmxvY2suc3RhdGVtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzVHlwZUFsaWFzRGVjbGFyYXRpb24oc3RhdGVtZW50KSAmJiB0cy5pc0lkZW50aWZpZXIoc3RhdGVtZW50Lm5hbWUpICYmXG5cdFx0XHRcdHN0YXRlbWVudC5uYW1lLnRleHQgPT09IG5hbWUpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0OiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uID0geyBraW5kIDogJ2FsaWFzJywgbm9kZSA6IHN0YXRlbWVudCwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiYgc3RhdGVtZW50Lm5hbWUgJiYgc3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZSkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQ6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gPSB7IGtpbmQgOiAnY2xhc3MnLCBub2RlIDogc3RhdGVtZW50LCBmaWxlIDogZmlsZVBhdGggfTtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc0ludGVyZmFjZURlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiYgdHMuaXNJZGVudGlmaWVyKHN0YXRlbWVudC5uYW1lKSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiA9IHsga2luZCA6ICdpbnRlcmZhY2UnLCBub2RlIDogc3RhdGVtZW50LCBmaWxlIDogZmlsZVBhdGggfTtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGYWxsYmFjayBmb3IgYSB0eXBlLXJlZmVyZW5jZSBuYW1lIHRoYXQgcmVzb2x2ZXMgdG8gbm8gZGVjbGFyYXRpb24gYW5kXG5cdCAqIG5vIGdyYXBoIHR5cGU6IGtub3duIGdsb2JhbHMga2VlcCB0aGVpciBiYXJlIG5hbWUgKHRoZXkgcmVzb2x2ZSB3aXRob3V0XG5cdCAqIGFuIGltcG9ydCk7IGV2ZXJ5dGhpbmcgZWxzZSBiZWNvbWVzIGB1bmtub3duYCBzbyBnZW5lcmF0ZWQgdHlwZXMudHNcblx0ICogbmV2ZXIgY2FycmllcyBhbiB1bnJlc29sdmFibGUgYmFyZSBuYW1lIChSRUFETUUncyBkb2N1bWVudGVkIGJlaGF2aW9yKVxuXHQgKiBhbmQgdGhlIHNpdGUgaXMgcmVjb3JkZWQgZm9yIHRoZSBwbGFpbi1UUyBhbWJpZ3VpdHkgdmFsaWRhdGlvbi5cblx0ICovXG5cdHByaXZhdGUgdW5yZXNvbHZlZFR5cGVSZWZlcmVuY2VGYWxsYmFjayAodHlwZU5hbWU6IHN0cmluZywgcmVmTm9kZT86IHRzLk5vZGUpOiBzdHJpbmcge1xuXHRcdGlmIChLTk9XTl9HTE9CQUxfVFlQRVMuaGFzKHR5cGVOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHR5cGVOYW1lO1xuXHRcdH1cblx0XHRpZiAocmVmTm9kZSkge1xuXHRcdFx0dGhpcy5yZWNvcmRQbGFpblR5cGVSZWZlcmVuY2VTaXRlKHR5cGVOYW1lLCByZWZOb2RlKTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gJ3Vua25vd24nO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIG9uZSBkZWZpbmUoKS9sYXp5KCkvQGRlY29yYXRlKCkgc2l0ZSB1bmRlciBpdHMgcnVudGltZVxuXHQgKiBuYW1lc3BhY2Uga2V5LiBUd28gc2l0ZXMgaW4gb25lIG5hbWVzcGFjZSBhcmUgYSBzYW1lLW5hbWVzcGFjZVxuXHQgKiBkdXBsaWNhdGUgKHRoZSBydW50aW1lIHRocm93cyBBTFJFQURZX0RFQ0xBUkVEKTsgZXZlcnkgc2l0ZSBpcyBrZXB0XG5cdCAqIHNvIHRoZSBmYWlsdXJlIGNhbiByZXBvcnQgYWxsIGxvY2F0aW9ucy5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkRGVmaW5lU2l0ZSAobmFtZXNwYWNlS2V5OiBzdHJpbmcsIGxvY2F0aW9uOiBzdHJpbmcpOiB2b2lkIHtcblx0XHRsZXQgc2l0ZXMgPSB0aGlzLmRlZmluZVNpdGVzLmdldChuYW1lc3BhY2VLZXkpO1xuXHRcdGlmICghc2l0ZXMpIHtcblx0XHRcdHNpdGVzID0gW107XG5cdFx0XHR0aGlzLmRlZmluZVNpdGVzLnNldChuYW1lc3BhY2VLZXksIHNpdGVzKTtcblx0XHR9XG5cdFx0aWYgKCFzaXRlcy5pbmNsdWRlcyhsb2NhdGlvbikpIHtcblx0XHRcdHNpdGVzLnB1c2gobG9jYXRpb24pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBGYXRhbCByZXNvbHV0aW9uIGZhaWx1cmVzIChoYXJkLWZhaWwgbGF3KTogc2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlXG5cdCAqIG1uZW1vbmljYSBkZWZpbml0aW9ucyBwbHVzIGFtYmlndW91cy91bnJlc29sdmVkIG1uZW1vbmljYS1ncmFwaFxuXHQgKiByZWZlcmVuY2VzLiBUaGUgQ0xJIHByaW50cyBldmVyeSBsb2NhdGlvbiBhbmQgd3JpdGVzIG5vIG91dHB1dC5cblx0ICovXG5cdGdldFJlc29sdXRpb25FcnJvcnMgKCk6IFJlc29sdXRpb25FcnJvcltdIHtcblx0XHR0aGlzLnZhbGlkYXRlTG9va3VwUmVmZXJlbmNlcygpO1xuXHRcdHRoaXMudmFsaWRhdGVQbGFpblR5cGVSZWZlcmVuY2VzKCk7XG5cdFx0Y29uc3QgZXJyb3JzOiBSZXNvbHV0aW9uRXJyb3JbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgWyBuYW1lc3BhY2VLZXksIHNpdGVzIF0gb2YgdGhpcy5kZWZpbmVTaXRlcykge1xuXHRcdFx0aWYgKHNpdGVzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBkaXNwbGF5TmFtZSA9IG5hbWVzcGFjZUtleS5yZXBsYWNlKC9eW146XSs6Oi8sICcnKTtcblx0XHRcdGNvbnN0IG1lc3NhZ2UgPSBgRHVwbGljYXRlIGRlZmluaXRpb24gb2YgJyR7ZGlzcGxheU5hbWV9JyBpbiBvbmUgbmFtZXNwYWNlIOKAlCBgICtcblx0XHRcdFx0J3RoZSBtbmVtb25pY2EgcnVudGltZSB3b3VsZCB0aHJvdyBBTFJFQURZX0RFQ0xBUkVEJztcblx0XHRcdGVycm9ycy5wdXNoKHsgbWVzc2FnZSwgbG9jYXRpb25zIDogWyAuLi5zaXRlcyBdIH0pO1xuXHRcdH1cblx0XHRmb3IgKGNvbnN0IGVycm9yIG9mIHRoaXMuZ3JhcGhSZWZlcmVuY2VFcnJvcnMpIHtcblx0XHRcdGVycm9ycy5wdXNoKGVycm9yKTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gZXJyb3JzO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHJlZmVyZW5jZSB0byBhIG1uZW1vbmljYSBncmFwaCB0eXBlIG5hbWUsIGltcG9ydC1hd2FyZSBhbmRcblx0ICogcGF0aC1hd2FyZSAodGhlIGhhcmQtZmFpbCBpZGVudGl0eSBsYXcsIG1pcnJvcmluZyB0aGUgcnVudGltZSk6XG5cdCAqICAgMS4gdmFsdWUgc2NvcGUg4oCUIGEgdHJhY2tlZCB0b3AtbGV2ZWwgYmluZGluZyBpbiB0aGUgcmVmZXJlbmNpbmcgZmlsZVxuXHQgKiAgICAgIChgY29uc3QgQWRkcmVzcyA9IFVzZXIuZGVmaW5lKCdBZGRyZXNzJywg4oCmKWApLFxuXHQgKiAgIDIuIGltcG9ydCBzY29wZSDigJQgYSBiaW5kaW5nIGV4cG9ydGVkIGZyb20gYSBtb2R1bGUgdGhpcyBmaWxlIGltcG9ydHNcblx0ICogICAgICAoYmFycmVscyBjaGFzZWQpLFxuXHQgKiAgIDMuIG5lYXJlc3QtY2hhaW4g4oCUIHRoZSBhbmNob3IgdHlwZSdzIG93biBzdWJ0eXBlcyBmaXJzdCwgdGhlbiBlYWNoXG5cdCAqICAgICAgYW5jZXN0b3IgbGV2ZWwgKHJlbGF0aXZlLWZpcnN0KSxcblx0ICogICA0LiByb290IOKAlCByb290cyBvZiB0aGUgYW5jaG9yJ3MgY29sbGVjdGlvbixcblx0ICogICA1LiBwcm9ncmFtLXdpZGUg4oCUIG9ubHkgd2hlbiBleGFjdGx5IG9uZSB0eXBlIGNhcnJpZXMgdGhlIG5hbWUuXG5cdCAqIEFtYmlndWl0eSAoc2V2ZXJhbCBjYW5kaWRhdGVzIGFuZCBub3RoaW5nIGRpc2FtYmlndWF0ZXMpIGFuZCBhYnNlbmNlXG5cdCAqIGFyZSBib3RoIHJldHVybmVkIGFzIHN1Y2gg4oCUIHRoZSBjYWxsZXIgcmVjb3JkcyBhIGhhcmQgZmFpbHVyZTsgYSBiYXJlXG5cdCAqIGZpcnN0LW1hdGNoIG5hbWUgaXMgbmV2ZXIgZW1pdHRlZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUdyYXBoVHlwZU5hbWUgKG5hbWU6IHN0cmluZyk6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCB7XG5cdFx0Ly8gMS4gdmFsdWUgc2NvcGUgaW4gdGhlIHJlZmVyZW5jaW5nIGZpbGUgaXRzZWxmXG5cdFx0Y29uc3QgbG9jYWxCaW5kaW5nID0gdGhpcy5maWxlR3JhcGhCaW5kaW5ncy5nZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChsb2NhbEJpbmRpbmcpIHtcblx0XHRcdGNvbnN0IG5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGxvY2FsQmluZGluZyk7XG5cdFx0XHRpZiAobm9kZSkge1xuXHRcdFx0XHRjb25zdCB2YWx1ZVJlc3VsdDogR3JhcGhUeXBlUmVmZXJlbmNlUmVzdWx0ID0geyBzdGF0dXMgOiAndW5pcXVlJywgbm9kZSB9O1xuXHRcdFx0XHRyZXR1cm4gdmFsdWVSZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gMi4gaW1wb3J0IHNjb3BlIOKAlCB0aGUgaW1wb3J0ZWQgbW9kdWxlJ3MgZXhwb3J0ZWQgYmluZGluZ1xuXHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAoaW1wb3J0ZWQgJiYgIWltcG9ydGVkLmlzTmFtZXNwYWNlKSB7XG5cdFx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoaW1wb3J0ZWQuc3BlY2lmaWVyLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0aWYgKHJlc29sdXRpb24gJiYgIXJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRjb25zdCBmdWxsUGF0aCA9IHRoaXMuZmluZEdyYXBoQmluZGluZ0luTW9kdWxlKHJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBpbXBvcnRlZC5vcmlnaW5hbE5hbWUsIDApO1xuXHRcdFx0XHRpZiAoZnVsbFBhdGgpIHtcblx0XHRcdFx0XHRjb25zdCBub2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShmdWxsUGF0aCk7XG5cdFx0XHRcdFx0aWYgKG5vZGUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGltcG9ydFJlc3VsdDogR3JhcGhUeXBlUmVmZXJlbmNlUmVzdWx0ID0geyBzdGF0dXMgOiAndW5pcXVlJywgbm9kZSB9O1xuXHRcdFx0XHRcdFx0cmV0dXJuIGltcG9ydFJlc3VsdDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyAzLTUuIGNoYWluIC8gcm9vdCAvIHByb2dyYW0td2lkZSB0aWVyc1xuXHRcdGNvbnN0IHJlc3VsdCA9IHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UodGhpcy5ncmFwaCwgbmFtZSwgdGhpcy5jdXJyZW50R3JhcGhBbmNob3IpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRmluZCBhIGdyYXBoIGNvbnN0cnVjdG9yIGJpbmRpbmcgZXhwb3J0ZWQgYnkgYSByZXNvbHZlZCBtb2R1bGUsXG5cdCAqIGNoYXNpbmcgcmUtZXhwb3J0IGJhcnJlbHMgd2l0aCBhIGJvdW5kZWQgZGVwdGguXG5cdCAqL1xuXHRwcml2YXRlIGZpbmRHcmFwaEJpbmRpbmdJbk1vZHVsZSAobW9kdWxlUGF0aDogc3RyaW5nLCBuYW1lOiBzdHJpbmcsIGRlcHRoOiBudW1iZXIpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmIChkZXB0aCA+IE1BWF9SRUVYUE9SVF9DSEFTRV9ERVBUSCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBkaXJlY3QgPSB0aGlzLmZpbGVHcmFwaEJpbmRpbmdzLmdldChtb2R1bGVQYXRoKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChkaXJlY3QpIHtcblx0XHRcdHJldHVybiBkaXJlY3Q7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVFeHBvcnRzID0gdGhpcy5yZWZlcmVuY2VkVHlwZVJlRXhwb3J0cy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0Y29uc3QgcmVFeHBvcnRTcGVjaWZpZXIgPSByZUV4cG9ydHM/LmdldChuYW1lKTtcblx0XHRpZiAocmVFeHBvcnRTcGVjaWZpZXIpIHtcblx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUocmVFeHBvcnRTcGVjaWZpZXIsIG1vZHVsZVBhdGgpO1xuXHRcdFx0aWYgKG5leHRSZXNvbHV0aW9uICYmICFuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kR3JhcGhCaW5kaW5nSW5Nb2R1bGUobmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBuYW1lLCBkZXB0aCArIDEpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCBzdGFycyA9IHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycy5nZXQobW9kdWxlUGF0aCk7XG5cdFx0aWYgKHN0YXJzKSB7XG5cdFx0XHRmb3IgKGNvbnN0IHN0YXJTcGVjaWZpZXIgb2Ygc3RhcnMpIHtcblx0XHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShzdGFyU3BlY2lmaWVyLCBtb2R1bGVQYXRoKTtcblx0XHRcdFx0aWYgKCFuZXh0UmVzb2x1dGlvbiB8fCBuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRHcmFwaEJpbmRpbmdJbk1vZHVsZShuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIG5hbWUsIGRlcHRoICsgMSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogVmFsaWRhdGUgbGl0ZXJhbCBsb29rdXAoKSBwYXRocyByZWNvcmRlZCBkdXJpbmcgdGhlIHVzYWdlcyBwYXNzXG5cdCAqIGFnYWluc3QgdGhlIGNvbXBsZXRlIGdyYXBoLiBBIGxvb2t1cCBwYXRoIG1hdGNoaW5nIG5vIHR5cGUgaXMgd2hhdCB0aGVcblx0ICogcnVudGltZSBhbnN3ZXJzIHdpdGggYHVuZGVmaW5lZGAg4oCUIHRoZSBUeXBlRXJyb3IgYXJyaXZlcyBvbmUgbGluZVxuXHQgKiBsYXRlciBhdCB0aGUgYG5ld2Ag4oCUIHNvIGl0IGpvaW5zIHRoZSBoYXJkLWZhaWwgbGF3LiBUaGUgcmVsYXRpdmUtZmlyc3Rcblx0ICogc3RlcCBhbHJlYWR5IHJhbiBpbnNpZGUgcmVzb2x2ZUxvb2t1cFBhdGg7IHdoYXRldmVyIHdhcyByZWNvcmRlZCBpc1xuXHQgKiB0aGUgcm9vdC1yZXNvbHV0aW9uIHJlc3VsdCwgc28gYSBwbGFpbiBmaW5kVHlwZSBjaGVjayBpcyB0aGUgZXhhY3Rcblx0ICogcnVudGltZSBsYXcuIFNhbWUtbmFtZWQgdHlwZXMgZWxzZXdoZXJlIGluIHRoZSBncmFwaCBhcmUgbGlzdGVkIGFzXG5cdCAqIGRpZC15b3UtbWVhbiBjYW5kaWRhdGVzLiBSdW5zIG9uY2UgcGVyIHVzYWdlcyBwYXNzIChyZS1hcm1lZCBieVxuXHQgKiByZXNldFVzYWdlcyk7IG5vbi1saXRlcmFsIGxvb2t1cCBhcmd1bWVudHMgYXJlIG5ldmVyIHJlY29yZGVkIGFuZFxuXHQgKiBzdGF5IGJlc3QtZWZmb3J0LlxuXHQgKi9cblx0cHJpdmF0ZSB2YWxpZGF0ZUxvb2t1cFJlZmVyZW5jZXMgKCk6IHZvaWQge1xuXHRcdGlmICh0aGlzLmxvb2t1cFJlZmVyZW5jZXNWYWxpZGF0ZWQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0dGhpcy5sb29rdXBSZWZlcmVuY2VzVmFsaWRhdGVkID0gdHJ1ZTtcblx0XHQvLyBncm91cCBzaXRlcyBieSBwYXRoOiBldmVyeSBmYWlsaW5nIHNpdGUgb2YgdGhlIHNhbWUgcGF0aCBpcyBsaXN0ZWRcblx0XHRjb25zdCBzaXRlc0J5UGF0aCA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmdbXT4oKTtcblx0XHRmb3IgKGNvbnN0IHJlZiBvZiB0aGlzLmxvb2t1cFJlZmVyZW5jZXMpIHtcblx0XHRcdGNvbnN0IHNpdGVzID0gc2l0ZXNCeVBhdGguZ2V0KHJlZi5wYXRoKSA/PyBbXTtcblx0XHRcdHNpdGVzLnB1c2gocmVmLmxvY2F0aW9uKTtcblx0XHRcdHNpdGVzQnlQYXRoLnNldChyZWYucGF0aCwgc2l0ZXMpO1xuXHRcdH1cblx0XHRmb3IgKGNvbnN0IFsgdHlwZVBhdGgsIHNpdGVzIF0gb2Ygc2l0ZXNCeVBhdGgpIHtcblx0XHRcdGlmICh0aGlzLmdyYXBoLmZpbmRUeXBlKHR5cGVQYXRoKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdC8vIGRpZC15b3UtbWVhbjogdHlwZXMgY2FycnlpbmcgdGhlIHNhbWUgbmFtZSBhbnl3aGVyZSBpbiB0aGVcblx0XHRcdC8vIGdyYXBoIChuZXZlciBhIGZpcnN0LW1hdGNoIHBpY2sg4oCUIHRoZSBmdWxsIGxpc3Qgb25seSlcblx0XHRcdGNvbnN0IHVucHJlZml4ZWQgPSB0eXBlUGF0aC5yZXBsYWNlKC9eW146XSs6Oi8sICcnKTtcblx0XHRcdGNvbnN0IGxhc3RTZWdtZW50ID0gdW5wcmVmaXhlZC5zcGxpdCgnLicpLnBvcCgpID8/IHVucHJlZml4ZWQ7XG5cdFx0XHRjb25zdCBjYW5kaWRhdGVzID0gdGhpcy5ncmFwaC5nZXRBbGxUeXBlcygpLmZpbHRlcih0ID0+IHQubmFtZSA9PT0gbGFzdFNlZ21lbnQpO1xuXHRcdFx0aWYgKGNhbmRpZGF0ZXMubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRcdGNvbnN0IG5vbmVFcnJvcjogUmVzb2x1dGlvbkVycm9yID0ge1xuXHRcdFx0XHRcdG1lc3NhZ2UgOiBgVW5yZXNvbHZlZCBsb29rdXAgb2YgbW5lbW9uaWNhIHR5cGUgJyR7dHlwZVBhdGh9Jzogbm8gdHlwZSBhdCB0aGF0IHBhdGgg4oCUIGAgK1xuXHRcdFx0XHRcdFx0J3RoZSBydW50aW1lIHdvdWxkIHJldHVybiB1bmRlZmluZWQnLFxuXHRcdFx0XHRcdGxvY2F0aW9ucyA6IHNpdGVzLFxuXHRcdFx0XHR9O1xuXHRcdFx0XHR0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzLnB1c2gobm9uZUVycm9yKTtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBjYW5kaWRhdGVMb2NhdGlvbnMgPSBjYW5kaWRhdGVzLm1hcChuID0+IGAke24uc291cmNlRmlsZX06JHtuLmxpbmV9OiR7bi5jb2x1bW59YCk7XG5cdFx0XHRjb25zdCBjYW5kaWRhdGVQYXRocyA9IGNhbmRpZGF0ZXMubWFwKG4gPT4gbi5mdWxsUGF0aCkuam9pbignLCAnKTtcblx0XHRcdGNvbnN0IGFtYmlndW91c0Vycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7XG5cdFx0XHRcdG1lc3NhZ2UgOiBgVW5yZXNvbHZlZCBsb29rdXAgb2YgbW5lbW9uaWNhIHR5cGUgJyR7dHlwZVBhdGh9JzogdGhlIHJ1bnRpbWUgd291bGQgcmV0dXJuIGAgK1xuXHRcdFx0XHRcdGB1bmRlZmluZWQg4oCUICR7Y2FuZGlkYXRlcy5sZW5ndGh9IGdyYXBoIHR5cGUocykgY2FycnkgdGhlIG5hbWUgYCArXG5cdFx0XHRcdFx0YG9mZi1yb290ICgke2NhbmRpZGF0ZVBhdGhzfSk7IHVzZSB0aGUgZnVsbCBkb3R0ZWQgcGF0aGAsXG5cdFx0XHRcdGxvY2F0aW9ucyA6IFsgLi4uc2l0ZXMsIC4uLmNhbmRpZGF0ZUxvY2F0aW9ucyBdLFxuXHRcdFx0fTtcblx0XHRcdHRoaXMuZ3JhcGhSZWZlcmVuY2VFcnJvcnMucHVzaChhbWJpZ3VvdXNFcnJvcik7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhIHBsYWluLVRTIHR5cGUgcmVmZXJlbmNlIHNpdGUgdGhhdCByZXNvbHZlZCB0byBub3RoaW5nIGFuZFxuXHQgKiBmZWxsIGJhY2sgdG8gYHVua25vd25gLCBmb3IgdGhlIGxhemlseS1ydW4gYW1iaWd1aXR5IHZhbGlkYXRpb24uXG5cdCAqIERlZHVwZWQgYnkgKG5hbWUsIGxvY2F0aW9uKTogaW5mZXJUeXBlIGNhbiB2aXNpdCB0aGUgc2FtZSBub2RlIG1vcmVcblx0ICogdGhhbiBvbmNlIHBlciBwYXNzIChjb25zdHJ1Y3RvciBwYXJhbXMgKyBwcm9wZXJ0eSBpbmZlcmVuY2UpLlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmRQbGFpblR5cGVSZWZlcmVuY2VTaXRlIChuYW1lOiBzdHJpbmcsIHJlZk5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRjb25zdCBsb2NhdGlvbiA9IHRoaXMubm9kZUxvY2F0aW9uKHJlZk5vZGUpO1xuXHRcdGNvbnN0IGZpbGUgPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0Y29uc3QgYWxyZWFkeSA9IHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlcy5zb21lKChyZWYpID0+IHJlZi5uYW1lID09PSBuYW1lICYmIHJlZi5sb2NhdGlvbiA9PT0gbG9jYXRpb24pO1xuXHRcdGlmIChhbHJlYWR5KSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlcy5wdXNoKHsgbmFtZSwgbG9jYXRpb24sIGZpbGUgfSk7XG5cdH1cblxuXHQvKipcblx0ICogUHJvamVjdC1zb3VyY2UgZGVjbGFyYXRpb24gZmlsZXMgY2FycnlpbmcgYG5hbWVgIOKAlCBvbmUgZW50cnkgcGVyXG5cdCAqIGZpbGUsIHNvIHNhbWUtZmlsZSBpbnRlcmZhY2UgbWVyZ2luZyBjb3VudHMgb25jZSAobm90IGFtYmlndW91cykuXG5cdCAqIEV4dGVybmFsL2FtYmllbnQgZGVjbGFyYXRpb25zICguZC50cywgYW55dGhpbmcgdW5kZXIgbm9kZV9tb2R1bGVzKVxuXHQgKiBuZXZlciBjb3VudDogYSB1c2VyLWxvY2FsIGRlY2xhcmF0aW9uIGFsd2F5cyB3aW5zIG92ZXIgYSBwYWNrYWdlLVxuXHQgKiBkZWNsYXJlZCBzYW1lLW5hbWVkIHR5cGUsIHNvIGFuIGV4dGVybmFsIGNvbGxpc2lvbiBzdGF5cyBzb2Z0LlxuXHQgKi9cblx0cHJpdmF0ZSBwbGFpblR5cGVEZWNsYXJhdGlvbkZpbGVzIChuYW1lOiBzdHJpbmcpOiBzdHJpbmdbXSB7XG5cdFx0Y29uc3QgZmlsZXM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBbIGZpbGUsIGRlY2xzIF0gb2YgdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzKSB7XG5cdFx0XHRpZiAoIXRoaXMuaXNFeHRlcm5hbERlY2xGaWxlKGZpbGUpICYmIGRlY2xzLmhhcyhuYW1lKSkge1xuXHRcdFx0XHRmaWxlcy5wdXNoKGZpbGUpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gZmlsZXM7XG5cdH1cblxuXHQvKipcblx0ICogVmFsaWRhdGUgcGxhaW4tVFMgdHlwZSByZWZlcmVuY2Ugc2l0ZXMgcmVjb3JkZWQgZHVyaW5nIHRoZSB1c2FnZXNcblx0ICogcGFzcyBhZ2FpbnN0IHRoZSBjb21wbGV0ZSBkZWNsYXJhdGlvbiBtYXAuIEEgbmFtZSBkZWNsYXJlZCBpblxuXHQgKiBzZXZlcmFsIHByb2plY3Qtc291cmNlIGZpbGVzIOKAlCB3aXRoIG5vIGltcG9ydCBpbiB0aGUgcmVmZXJlbmNpbmdcblx0ICogZmlsZSB0byBhbmNob3IgaXQg4oCUIGlzIGFtYmlndW91czogc2lsZW50bHkgZW1pdHRpbmcgYHVua25vd25gIHdvdWxkXG5cdCAqIGhpZGUgYSByZWFsIHR5cGUgdGhlIGF1dGhvciBtZWFudCwgc28gaXQgam9pbnMgdGhlIGhhcmQtZmFpbCBsYXdcblx0ICogKHRoZSBwbGFpbi1UUyB0aWVyIG9mIHRoZSBzYW1lIGlkZW50aXR5IGxhdyBhcyBncmFwaCByZWZlcmVuY2VzKS5cblx0ICogQWJzZW5jZSAoZ2hvc3QgbmFtZXMpIGFuZCBleHRlcm5hbCBjb2xsaXNpb25zIHN0YXkgc29mdCBgdW5rbm93bmAuXG5cdCAqIFJ1bnMgb25jZSBwZXIgdXNhZ2VzIHBhc3MgKHJlLWFybWVkIGJ5IHJlc2V0VXNhZ2VzKSwgbWlycm9yaW5nXG5cdCAqIHZhbGlkYXRlTG9va3VwUmVmZXJlbmNlczogcmVjb3JkaW5nIGhhcHBlbnMgb24gZXZlcnkgcGFzcywgYnV0IG9ubHlcblx0ICogdGhlIHVzYWdlcyBwYXNzIHNlZXMgdGhlIGNvbXBsZXRlIGRlY2xhcmF0aW9uIG1hcC5cblx0ICovXG5cdHByaXZhdGUgdmFsaWRhdGVQbGFpblR5cGVSZWZlcmVuY2VzICgpOiB2b2lkIHtcblx0XHRpZiAodGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzVmFsaWRhdGVkKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IHRydWU7XG5cdFx0Y29uc3Qgc2l0ZXNCeU5hbWUgPSBuZXcgTWFwPHN0cmluZywgeyBuYW1lOiBzdHJpbmc7IGxvY2F0aW9uOiBzdHJpbmc7IGZpbGU6IHN0cmluZyB9W10+KCk7XG5cdFx0Zm9yIChjb25zdCByZWYgb2YgdGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzKSB7XG5cdFx0XHRjb25zdCBzaXRlcyA9IHNpdGVzQnlOYW1lLmdldChyZWYubmFtZSkgPz8gW107XG5cdFx0XHRzaXRlcy5wdXNoKHJlZik7XG5cdFx0XHRzaXRlc0J5TmFtZS5zZXQocmVmLm5hbWUsIHNpdGVzKTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBbIG5hbWUsIHNpdGVzIF0gb2Ygc2l0ZXNCeU5hbWUpIHtcblx0XHRcdC8vIGFuIGltcG9ydCBiaW5kaW5nIGluIHRoZSByZWZlcmVuY2luZyBmaWxlIGFuY2hvcnMgdGhlIG5hbWUg4oCUXG5cdFx0XHQvLyB0aGUgYXV0aG9yIGFscmVhZHkgZGlzYW1iaWd1YXRlZCAodGhlIGltcG9ydCBtYXkganVzdCBwb2ludFxuXHRcdFx0Ly8gYXQgYW4gdW5hbmFseXphYmxlIGV4dGVybmFsIG1vZHVsZSwgd2hpY2ggc3RheXMgc29mdClcblx0XHRcdGNvbnN0IHVuYW5jaG9yZWQgPSBzaXRlcy5maWx0ZXIoKHNpdGUpID0+ICF0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoc2l0ZS5maWxlKT8uaGFzKG5hbWUpKTtcblx0XHRcdGlmICh1bmFuY2hvcmVkLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGRlY2xGaWxlcyA9IHRoaXMucGxhaW5UeXBlRGVjbGFyYXRpb25GaWxlcyhuYW1lKTtcblx0XHRcdGlmIChkZWNsRmlsZXMubGVuZ3RoIDwgMikge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IG1lc3NhZ2UgPSBgQW1iaWd1b3VzIHJlZmVyZW5jZSB0byB0eXBlICcke25hbWV9JzogJHtkZWNsRmlsZXMubGVuZ3RofSBkZWNsYXJhdGlvbnMgYCArXG5cdFx0XHRcdCdzaGFyZSB0aGUgbmFtZSBhbmQgbm8gaW1wb3J0IGRpc2FtYmlndWF0ZXMg4oCUIGltcG9ydCB0aGUgb25lIHlvdSBtZWFuJztcblx0XHRcdGNvbnN0IGRlY2xMb2NhdGlvbnMgPSBkZWNsRmlsZXMubWFwKChmaWxlKSA9PiB0aGlzLnBsYWluRGVjbExvY2F0aW9uKGZpbGUsIG5hbWUpKTtcblx0XHRcdGNvbnN0IGVycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7XG5cdFx0XHRcdG1lc3NhZ2UsXG5cdFx0XHRcdGxvY2F0aW9ucyA6IFsgLi4udW5hbmNob3JlZC5tYXAoKHNpdGUpID0+IHNpdGUubG9jYXRpb24pLCAuLi5kZWNsTG9jYXRpb25zIF1cblx0XHRcdH07XG5cdFx0XHR0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzLnB1c2goZXJyb3IpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBgZmlsZTpsaW5lOmNvbHVtbmAgb2YgYSByZWNvcmRlZCBkZWNsYXJhdGlvbiwgZm9yIHRoZSBhbWJpZ3VpdHlcblx0ICogcmVwb3J0LiBOb2RlcyByZWNvcmRlZCBkdXJpbmcgdHJhdmVyc2FsIGtlZXAgdGhlaXIgcG9zaXRpb25zOyBhXG5cdCAqIHN5bnRoZXRpYy91bnBvc2l0aW9uZWQgbm9kZSBmYWxscyBiYWNrIHRvIHRoZSBmaWxlIGl0c2VsZi5cblx0ICovXG5cdHByaXZhdGUgcGxhaW5EZWNsTG9jYXRpb24gKGZpbGU6IHN0cmluZywgbmFtZTogc3RyaW5nKTogc3RyaW5nIHtcblx0XHRjb25zdCBkZWNsID0gdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLmdldChmaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGNvbnN0IG5vZGUgPSBkZWNsPy5ub2RlO1xuXHRcdGxldCBsb2NhdGlvbiA9IGAke2ZpbGV9OjE6MWA7XG5cdFx0aWYgKG5vZGUgJiYgbm9kZS5wb3MgPj0gMCkge1xuXHRcdFx0Y29uc3Qgc291cmNlRmlsZSA9IG5vZGUuZ2V0U291cmNlRmlsZSgpO1xuXHRcdFx0Y29uc3QgbGluZSA9IHNvdXJjZUZpbGUuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24obm9kZS5nZXRTdGFydCgpKS5saW5lICsgMTtcblx0XHRcdGNvbnN0IGNvbHVtbiA9IHNvdXJjZUZpbGUuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24obm9kZS5nZXRTdGFydCgpKS5jaGFyYWN0ZXIgKyAxO1xuXHRcdFx0bG9jYXRpb24gPSBgJHtmaWxlfToke2xpbmV9OiR7Y29sdW1ufWA7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGxvY2F0aW9uO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGEgaGFyZC1mYWlsIGdyYXBoIHJlZmVyZW5jZSBlcnJvciB3aXRoIHRoZSByZWZlcmVuY2Ugc2l0ZSBhbmRcblx0ICogZXZlcnkgY2FuZGlkYXRlIGxvY2F0aW9uLlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yIChcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0cmVmTm9kZTogdHMuTm9kZSB8IHN0cmluZyxcblx0XHRyZXN1bHQ6IEV4dHJhY3Q8R3JhcGhUeXBlUmVmZXJlbmNlUmVzdWx0LCB7IHN0YXR1czogJ2FtYmlndW91cycgfCAnbm9uZScgfT5cblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSB0eXBlb2YgcmVmTm9kZSA9PT0gJ3N0cmluZycgPyByZWZOb2RlIDogdGhpcy5ub2RlTG9jYXRpb24ocmVmTm9kZSk7XG5cdFx0aWYgKHJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHRjb25zdCBjYW5kaWRhdGVMb2NhdGlvbnMgPSByZXN1bHQuY2FuZGlkYXRlcy5tYXAobiA9PiBgJHtuLnNvdXJjZUZpbGV9OiR7bi5saW5lfToke24uY29sdW1ufWApO1xuXHRcdFx0Y29uc3QgYW1iaWd1b3VzTWVzc2FnZSA9IGBBbWJpZ3VvdXMgcmVmZXJlbmNlIHRvIG1uZW1vbmljYSB0eXBlICcke25hbWV9JzogYCArXG5cdFx0XHRcdGAke3Jlc3VsdC5jYW5kaWRhdGVzLmxlbmd0aH0gdHlwZXMgc2hhcmUgdGhlIG5hbWUgYW5kIG5laXRoZXIgdGhlIHBhcmVudCBjaGFpbiBgICtcblx0XHRcdFx0J25vciB0aGUgaW1wb3J0cyBkaXNhbWJpZ3VhdGUnO1xuXHRcdFx0Y29uc3QgYW1iaWd1b3VzRXJyb3I6IFJlc29sdXRpb25FcnJvciA9IHtcblx0XHRcdFx0bWVzc2FnZSAgIDogYW1iaWd1b3VzTWVzc2FnZSxcblx0XHRcdFx0bG9jYXRpb25zIDogWyBsb2NhdGlvbiwgLi4uY2FuZGlkYXRlTG9jYXRpb25zIF0sXG5cdFx0XHR9O1xuXHRcdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKGFtYmlndW91c0Vycm9yKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgdW5yZXNvbHZlZE1lc3NhZ2UgPSBgVW5yZXNvbHZlZCByZWZlcmVuY2UgdG8gbW5lbW9uaWNhIHR5cGUgJyR7bmFtZX0nOiBubyB0eXBlIG1hdGNoZXMgYCArXG5cdFx0XHQnYnkgdmFsdWUgc2NvcGUsIGltcG9ydHMsIHBhcmVudCBjaGFpbiwgb3Igcm9vdCBwYXRoJztcblx0XHRjb25zdCB1bnJlc29sdmVkRXJyb3I6IFJlc29sdXRpb25FcnJvciA9IHsgbWVzc2FnZSA6IHVucmVzb2x2ZWRNZXNzYWdlLCBsb2NhdGlvbnMgOiBbIGxvY2F0aW9uIF0gfTtcblx0XHR0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzLnB1c2godW5yZXNvbHZlZEVycm9yKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBMb2NhdGlvbiAoYGZpbGU6bGluZTpjb2x1bW5gKSBvZiBhbiBBU1Qgbm9kZSwgZGVyaXZlZCB3aXRob3V0IHBhcmVudFxuXHQgKiBwb2ludGVycyB3aGVuIG5lY2Vzc2FyeS5cblx0ICovXG5cdHByaXZhdGUgbm9kZUxvY2F0aW9uIChub2RlOiB0cy5Ob2RlKTogc3RyaW5nIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5vZGU7XG5cdFx0d2hpbGUgKGN1cnJlbnQgJiYgIXRzLmlzU291cmNlRmlsZShjdXJyZW50KSkge1xuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRpZiAoIWN1cnJlbnQpIHtcblx0XHRcdGNvbnN0IGZhbGxiYWNrID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdFx0cmV0dXJuIGZhbGxiYWNrO1xuXHRcdH1cblx0XHRjb25zdCBzdGFydCA9IG5vZGUuZ2V0U3RhcnQoY3VycmVudCk7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKGN1cnJlbnQsIHN0YXJ0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke2N1cnJlbnQuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdHJldHVybiBsb2NhdGlvbjtcblx0fVxuXG5cdC8qKlxuXHQgKiBUcmFjayBhbGlhc2VzIG9mIHRoZSBtbmVtb25pY2EgbW9kdWxlIG9iamVjdCwgZS5nLjpcblx0ICogICBjb25zdCBtID0gbW5lbW9uaWNhO1xuXHQgKiAgIGNvbnN0IEFwcCA9IG07XG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrTW9kdWxlT2JqZWN0QWxpYXNlcyAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpIHx8ICF0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgaW5pdGlhbGl6ZXIgfSA9IG5vZGU7XG5cdFx0aWYgKCFpbml0aWFsaXplcikge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoaW5pdGlhbGl6ZXIpICYmIHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhpbml0aWFsaXplci50ZXh0KSkge1xuXHRcdFx0dGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuYWRkKG5vZGUubmFtZS50ZXh0KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgY3VzdG9tIGNvbGxlY3Rpb24gdmFyaWFibGVzLCBlLmcuOlxuXHQgKiAgIGNvbnN0IE15Q29sbGVjdGlvbiA9IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpO1xuXHQgKiAgIGNvbnN0IE90aGVyID0gTXlDb2xsZWN0aW9uO1xuXHQgKlxuXHQgKiBBbHNvIGRldGVjdHMgT3B0aW9uIEIgdXNlci1wcm92aWRlZCByZWdpc3RyeSBpbnRlcmZhY2VzOlxuXHQgKiAgIGV4cG9ydCBpbnRlcmZhY2UgTXlDb2xsZWN0aW9uUmVnaXN0cnkge31cblx0ICogICBjb25zdCBNeUNvbGxlY3Rpb24gPSBjcmVhdGVUeXBlc0NvbGxlY3Rpb248TXlDb2xsZWN0aW9uUmVnaXN0cnk+KCk7XG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrQ29sbGVjdGlvbkFsaWFzZXMgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSB8fCAhdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGluaXRpYWxpemVyIH0gPSBub2RlO1xuXHRcdGlmICghaW5pdGlhbGl6ZXIpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBEaXJlY3QgY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgY2FsbFxuXHRcdGlmICh0aGlzLmlzQ3JlYXRlVHlwZXNDb2xsZWN0aW9uQ2FsbChpbml0aWFsaXplcikpIHtcblx0XHRcdGNvbnN0IGNvbGxlY3Rpb25JZCA9IHRoaXMubmV4dENvbGxlY3Rpb25JZCgpO1xuXHRcdFx0dGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLnNldChub2RlLm5hbWUudGV4dCwgY29sbGVjdGlvbklkKTtcblxuXHRcdFx0Y29uc3QgcmVnaXN0cnlJbnRlcmZhY2VOYW1lID0gdGhpcy5leHRyYWN0UmVnaXN0cnlJbnRlcmZhY2VOYW1lKFxuXHRcdFx0XHRpbml0aWFsaXplciBhcyB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHRcdFx0c291cmNlRmlsZVxuXHRcdFx0KTtcblx0XHRcdHRoaXMuY29sbGVjdGlvbkluZm8uc2V0KGNvbGxlY3Rpb25JZCwge1xuXHRcdFx0XHR2YXJpYWJsZU5hbWUgICAgICAgICAgOiBub2RlLm5hbWUudGV4dCxcblx0XHRcdFx0c291cmNlRmlsZSAgICAgICAgICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0cmVnaXN0cnlJbnRlcmZhY2VOYW1lIDogcmVnaXN0cnlJbnRlcmZhY2VOYW1lXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBBbGlhcyBvZiBhbm90aGVyIGNvbGxlY3Rpb24gdmFyaWFibGVcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGluaXRpYWxpemVyKSkge1xuXHRcdFx0Y29uc3QgZXhpc3RpbmcgPSB0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuZ2V0KGluaXRpYWxpemVyLnRleHQpO1xuXHRcdFx0aWYgKGV4aXN0aW5nKSB7XG5cdFx0XHRcdHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5zZXQobm9kZS5uYW1lLnRleHQsIGV4aXN0aW5nKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0aGUgcmVnaXN0cnkgaW50ZXJmYWNlIG5hbWUgZnJvbSBjcmVhdGVUeXBlc0NvbGxlY3Rpb248UmVnaXN0cnk+KClcblx0ICogd2hlbiB0aGUgaW50ZXJmYWNlIGlzIGRlY2xhcmVkIGluIHRoZSBzYW1lIHNvdXJjZSBmaWxlLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UmVnaXN0cnlJbnRlcmZhY2VOYW1lIChcblx0XHRjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlXG5cdCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgdHlwZUFyZ3MgPSBjYWxsLnR5cGVBcmd1bWVudHM7XG5cdFx0aWYgKCF0eXBlQXJncyB8fCB0eXBlQXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgWyBmaXJzdFR5cGVBcmcgXSA9IHR5cGVBcmdzO1xuXHRcdGlmICghdHMuaXNUeXBlUmVmZXJlbmNlTm9kZShmaXJzdFR5cGVBcmcpIHx8ICF0cy5pc0lkZW50aWZpZXIoZmlyc3RUeXBlQXJnLnR5cGVOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBuYW1lID0gZmlyc3RUeXBlQXJnLnR5cGVOYW1lLnRleHQ7XG5cblx0XHQvLyBDb25maXJtIHRoZSBpbnRlcmZhY2UgZXhpc3RzIGluIHRoZSBzYW1lIHNvdXJjZSBmaWxlLlxuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIHNvdXJjZUZpbGUuc3RhdGVtZW50cykge1xuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc0ludGVyZmFjZURlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiZcblx0XHRcdFx0c3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZVxuXHRcdFx0KSB7XG5cdFx0XHRcdHJldHVybiBuYW1lO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IHRoZSByZWdpc3RyeSBpbnRlcmZhY2UgbmFtZSBmb3IgYSBjb2xsZWN0aW9uIGlkLlxuXHQgKi9cblx0cHJpdmF0ZSBnZXRSZWdpc3RyeUludGVyZmFjZU5hbWUgKGNvbGxlY3Rpb25JZD86IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCFjb2xsZWN0aW9uSWQpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdHJldHVybiB0aGlzLmNvbGxlY3Rpb25JbmZvLmdldChjb2xsZWN0aW9uSWQpPy5yZWdpc3RyeUludGVyZmFjZU5hbWU7XG5cdH1cblxuXHQvKipcblx0ICogQ2hlY2sgaWYgYW4gZXhwcmVzc2lvbiBpcyBhIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIGNhbGwuXG5cdCAqIEhhbmRsZXM6XG5cdCAqICAgY3JlYXRlVHlwZXNDb2xsZWN0aW9uKClcblx0ICogICBjdGMoKSAvLyBhbGlhc2VkIGltcG9ydFxuXHQgKiAgIG1uZW1vbmljYS5jcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSAvLyBtb2R1bGUgb2JqZWN0IG1ldGhvZFxuXHQgKiAgIG0uY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgLy8gYWxpYXNlZCBtb2R1bGUgb2JqZWN0XG5cdCAqL1xuXHRwcml2YXRlIGlzQ3JlYXRlVHlwZXNDb2xsZWN0aW9uQ2FsbCAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuQ2FsbEV4cHJlc3Npb24ge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblx0XHRjb25zdCBleHByID0gbm9kZS5leHByZXNzaW9uO1xuXG5cdFx0Ly8gRGlyZWN0IGNhbGwgb3IgYWxpYXNlZCBpbXBvcnQ6IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIC8gY3RjKClcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci50ZXh0ID09PSAnY3JlYXRlVHlwZXNDb2xsZWN0aW9uJyB8fFxuXHRcdFx0XHR0aGlzLmNyZWF0ZVR5cGVzQ29sbGVjdGlvblZhcmlhYmxlcy5oYXMoZXhwci50ZXh0KTtcblx0XHR9XG5cblx0XHQvLyBNb2R1bGUgb2JqZWN0IG1ldGhvZDogbW5lbW9uaWNhLmNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpXG5cdFx0aWYgKFxuXHRcdFx0dHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikgJiZcblx0XHRcdGV4cHIubmFtZS50ZXh0ID09PSAnY3JlYXRlVHlwZXNDb2xsZWN0aW9uJyAmJlxuXHRcdFx0dHMuaXNJZGVudGlmaWVyKGV4cHIuZXhwcmVzc2lvbikgJiZcblx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhleHByLmV4cHJlc3Npb24udGV4dClcblx0XHQpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZW5lcmF0ZSBhIHVuaXF1ZSBjb2xsZWN0aW9uIGlkZW50aWZpZXIuXG5cdCAqL1xuXHRwcml2YXRlIG5leHRDb2xsZWN0aW9uSWQgKCk6IHN0cmluZyB7XG5cdFx0dGhpcy5jb2xsZWN0aW9uQ291bnRlcisrO1xuXHRcdGNvbnN0IHJlc3VsdCA9IGBjb2xsZWN0aW9uXyR7dGhpcy5jb2xsZWN0aW9uQ291bnRlcn1gO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogQ2hlY2sgaWYgYSBub2RlIGlzIGEgZGVmaW5lKCkgY2FsbFxuXHQgKi9cblx0cHJpdmF0ZSBpc0RlZmluZUNhbGwgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkNhbGxFeHByZXNzaW9uIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IG5vZGU7XG5cblx0XHQvLyBDaGVjayBmb3IgZGlyZWN0IGNhbGw6IGRlZmluZSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLnRleHQgPT09ICdkZWZpbmUnKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgbWV0aG9kIGNhbGw6IFNvbWVUeXBlLmRlZmluZSgnU3ViVHlwZScsIC4uLilcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcmVzc2lvbikpIHtcblx0XHRcdHJldHVybiBleHByZXNzaW9uLm5hbWU/LnRleHQgPT09ICdkZWZpbmUnO1xuXHRcdH1cblxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhIG5vZGUgaXMgYSBsYXp5KCkgY2FsbFxuXHQgKi9cblx0cHJpdmF0ZSBpc0xhenlDYWxsIChub2RlOiB0cy5Ob2RlKTogbm9kZSBpcyB0cy5DYWxsRXhwcmVzc2lvbiB7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIGRpcmVjdCBjYWxsOiBsYXp5KCdUeXBlTmFtZScsIGdldHRlciwgLi4uKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnbGF6eScpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBtZXRob2QgY2FsbDogU29tZVR5cGUubGF6eSgnU3ViVHlwZScsIGdldHRlciwgLi4uKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuIGV4cHJlc3Npb24ubmFtZT8udGV4dCA9PT0gJ2xhenknO1xuXHRcdH1cblxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXG5cdC8qKlxuXHRcdCogRXh0cmFjdCBjb25maWcgb3B0aW9ucyBmcm9tIGFuIG9iamVjdCBsaXRlcmFsXG5cdFx0Ki9cblx0cHJpdmF0ZSBleHRyYWN0Q29uZmlnRnJvbU9iamVjdExpdGVyYWwgKGNvbmZpZ0FyZzogdHMuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24pOlxuXHRcdHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSB7XG5cdFx0Y29uc3QgY29uZmlnOiB7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0gPSB7fTtcblxuXHRcdGZvciAoY29uc3QgcHJvcCBvZiBjb25maWdBcmcucHJvcGVydGllcykge1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBc3NpZ25tZW50KHByb3ApICYmIHRzLmlzSWRlbnRpZmllcihwcm9wLm5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gcHJvcC5uYW1lLnRleHQ7XG5cdFx0XHRcdGlmIChwcm9wTmFtZSA9PT0gJ3N0cmljdENoYWluJyAmJiBwcm9wLmluaXRpYWxpemVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVHJ1ZUtleXdvcmQpIHtcblx0XHRcdFx0XHRjb25maWcuc3RyaWN0Q2hhaW4gPSB0cnVlO1xuXHRcdFx0XHR9IGVsc2UgaWYgKHByb3BOYW1lID09PSAnc3RyaWN0Q2hhaW4nICYmIHByb3AuaW5pdGlhbGl6ZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQpIHtcblx0XHRcdFx0XHRjb25maWcuc3RyaWN0Q2hhaW4gPSBmYWxzZTtcblx0XHRcdFx0fSBlbHNlIGlmIChwcm9wTmFtZSA9PT0gJ2Jsb2NrRXJyb3JzJyAmJiBwcm9wLmluaXRpYWxpemVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVHJ1ZUtleXdvcmQpIHtcblx0XHRcdFx0XHRjb25maWcuYmxvY2tFcnJvcnMgPSB0cnVlO1xuXHRcdFx0XHR9IGVsc2UgaWYgKHByb3BOYW1lID09PSAnYmxvY2tFcnJvcnMnICYmIHByb3AuaW5pdGlhbGl6ZXIua2luZCA9PT0gdHMuU3ludGF4S2luZC5GYWxzZUtleXdvcmQpIHtcblx0XHRcdFx0XHRjb25maWcuYmxvY2tFcnJvcnMgPSBmYWxzZTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBjb25maWc7XG5cdH1cblxuXHQvKipcblx0XHQqIEV4dHJhY3QgY29uZmlnIG9wdGlvbnMgZnJvbSBkZWZpbmUoKSBjYWxsXG5cdFx0Ki9cblx0cHJpdmF0ZSBleHRyYWN0Q29uZmlnIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSB7XG5cdFx0Ly8gQ29uZmlnIGlzIHRoZSB0aGlyZCBhcmd1bWVudDogZGVmaW5lKCdOYW1lJywgaGFuZGxlciwgY29uZmlnKVxuXHRcdGNvbnN0IFsgLCAsIGNvbmZpZ0FyZyBdID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0aWYgKCFjb25maWdBcmcgfHwgIXRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24oY29uZmlnQXJnKSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IGNvbmZpZ1Jlc3VsdCA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGNvbmZpZ0FyZyk7XG5cdFx0cmV0dXJuIGNvbmZpZ1Jlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHRcdCogQ2hlY2sgaWYgYSBub2RlIGlzIGEgQGRlY29yYXRlKCkgZGVjb3JhdG9yXG5cdFx0Ki9cblx0cHJpdmF0ZSBpc0RlY29yYXRlRGVjb3JhdG9yIChub2RlOiB0cy5Ob2RlKTogbm9kZSBpcyB0cy5EZWNvcmF0b3Ige1xuXHRcdGlmICghdHMuaXNEZWNvcmF0b3Iobm9kZSkpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IG5vZGU7XG5cblx0XHQvLyBDaGVjayBmb3IgQGRlY29yYXRlXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLnRleHQgPT09ICdkZWNvcmF0ZScpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGZvciBAZGVjb3JhdGUoKSBvciBAZGVjb3JhdGUoUGFyZW50VHlwZSlcblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihleHByZXNzaW9uKSkge1xuXHRcdFx0Y29uc3QgZm5OYW1lID0gZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihmbk5hbWUpICYmIGZuTmFtZS50ZXh0ID09PSAnZGVjb3JhdGUnKSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBDaGVjayBmb3IgQE15Q29sbGVjdGlvbi5kZWNvcmF0ZSgpIHdoZXJlIE15Q29sbGVjdGlvbiBpcyBhIGN1c3RvbSBjb2xsZWN0aW9uXG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGZuTmFtZSkgJiZcblx0XHRcdFx0Zm5OYW1lLm5hbWUudGV4dCA9PT0gJ2RlY29yYXRlJyAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoZm5OYW1lLmV4cHJlc3Npb24pICYmXG5cdFx0XHRcdHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5oYXMoZm5OYW1lLmV4cHJlc3Npb24udGV4dClcblx0XHRcdCkge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogTWFyayBhIGNhbGwgZXhwcmVzc2lvbiBhcyBwcm9jZXNzZWQgYW5kIHJldHVybiB3aGV0aGVyIGl0IGFscmVhZHkgd2FzLlxuXHQgKi9cblx0cHJpdmF0ZSBtYXJrUHJvY2Vzc2VkIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IGJvb2xlYW4ge1xuXHRcdGlmICh0aGlzLnByb2Nlc3NlZENhbGxzLmhhcyhjYWxsKSkge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXHRcdHRoaXMucHJvY2Vzc2VkQ2FsbHMuYWRkKGNhbGwpO1xuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBQcm9jZXNzIGEgZGVmaW5lKCkgY2FsbFxuXHQgKi9cblx0cHJpdmF0ZSBwcm9jZXNzRGVmaW5lQ2FsbCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHQvLyBDaGVjayBpZiB0aGlzIGV4YWN0IGNhbGwgaGFzIGFscmVhZHkgYmVlbiBwcm9jZXNzZWQgKHByZXZlbnRzIGR1cGxpY2F0ZXMgZnJvbSBjaGFpbmVkIGNhbGxzKVxuXHRcdGlmICh0aGlzLm1hcmtQcm9jZXNzZWQoY2FsbCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBHZXQgdGhlIHR5cGUgbmFtZSBhbmQgc291cmNlIGNvbnRleHQgZnJvbSBhcmd1bWVudHNcblx0XHRjb25zdCBkZWZpbmVDb250ZXh0ID0gdGhpcy5leHRyYWN0RGVmaW5lQ29udGV4dChjYWxsKTtcblxuXHRcdC8vIEZvciBjaGFpbmVkIGNhbGxzIGxpa2UgZGVmaW5lKCdBJykuZGVmaW5lKCdCJyksIHdlIHdhbnQgdGhlIHBvc2l0aW9uIG9mIHRoZSAuZGVmaW5lKCdCJykgcGFydFxuXHRcdC8vIG5vdCB0aGUgc3RhcnQgb2YgdGhlIGVudGlyZSBleHByZXNzaW9uXG5cdFx0bGV0IHBvc2l0aW9uTm9kZTogdHMuTm9kZSA9IGNhbGw7XG5cblx0XHQvLyBJZiB0aGlzIGlzIGEgY2hhaW5lZCBjYWxsLCBnZXQgdGhlIHBvc2l0aW9uIG9mIHRoZSBwcm9wZXJ0eSBhY2Nlc3MgZXhwcmVzc2lvblxuXHRcdC8vIHdoaWNoIGlzIHRoZSAuZGVmaW5lIHBhcnRcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0Ly8gVGhlIGV4cHJlc3Npb24gaXMgdGhlIHByb3BlcnR5IGFjY2VzczogKGRlZmluZSgnUm9vdEFzeW5jJywgLi4uKSkuZGVmaW5lXG5cdFx0XHQvLyBXZSB3YW50IHRoZSBwb3NpdGlvbiBvZiBqdXN0IHRoZSAuZGVmaW5lIHBhcnRcblx0XHRcdC8vIFRoaXMgaXMgdGhlICdkZWZpbmUnIGlkZW50aWZpZXJcblx0XHRcdHBvc2l0aW9uTm9kZSA9IGNhbGwuZXhwcmVzc2lvbi5uYW1lO1xuXHRcdH1cblxuXHRcdGNvbnN0IHN0YXJ0UG9zID0gcG9zaXRpb25Ob2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpO1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihzb3VyY2VGaWxlLCBzdGFydFBvcyk7XG5cblx0XHRpZiAoIWRlZmluZUNvbnRleHQudHlwZU5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0NvdWxkIG5vdCBleHRyYWN0IHR5cGUgbmFtZSBmcm9tIGRlZmluZSgpIGNhbGwnLFxuXHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRjb2x1bW4gIDogY2hhcmFjdGVyICsgMSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgdHlwZU5hbWUgfSA9IGRlZmluZUNvbnRleHQ7XG5cblx0XHQvLyBEZXRlcm1pbmUgcGFyZW50IHR5cGUgYW5kIGNvbGxlY3Rpb24gYmFzZWQgb24gdGhlIGNhbGwgc291cmNlLlxuXHRcdGNvbnN0IHBhcmVudE5vZGUgPSBkZWZpbmVDb250ZXh0LnBhcmVudFR5cGU7XG5cdFx0Y29uc3QgeyBjb2xsZWN0aW9uSWQgfSA9IGRlZmluZUNvbnRleHQ7XG5cblx0XHQvLyBFeHRyYWN0IGNvbmZpZyBvcHRpb25zXG5cdFx0Y29uc3QgY29uZmlnID0gdGhpcy5leHRyYWN0Q29uZmlnKGNhbGwpO1xuXG5cdFx0Ly8gQ3JlYXRlIHR5cGUgbm9kZSBmaXJzdCBzbyBpdHMgaW50ZXJuYWwgZnVsbFBhdGggKGluY2x1ZGluZyBhbnkgY29sbGVjdGlvbiBwcmVmaXgpIGlzIHJlc29sdmVkLlxuXHRcdGNvbnN0IG5vZGUgPSBUeXBlR3JhcGhJbXBsLmNyZWF0ZU5vZGUoXG5cdFx0XHR0eXBlTmFtZSxcblx0XHRcdHBhcmVudE5vZGUsXG5cdFx0XHRzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0bGluZSArIDEsXG5cdFx0XHRjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0Y29sbGVjdGlvbklkXG5cdFx0KTtcblx0XHRub2RlLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA9IHRoaXMuZ2V0UmVnaXN0cnlJbnRlcmZhY2VOYW1lKGNvbGxlY3Rpb25JZCk7XG5cblx0XHQvLyBTYW1lLW5hbWVzcGFjZSBkdXBsaWNhdGUgZGV0ZWN0aW9uIChoYXJkLWZhaWwgbGF3KToga2V5IGJ5IHRoZVxuXHRcdC8vIHJ1bnRpbWUgbmFtZXNwYWNlIOKAlCBjb2xsZWN0aW9uIHJvb3RzIGA8Y29sbGVjdGlvbj46OjxuYW1lPmAsIG9yXG5cdFx0Ly8gYDxwYXJlbnRGdWxsUGF0aD4uPG5hbWU+YCBmb3Igc3VidHlwZXNcblx0XHR0aGlzLnJlY29yZERlZmluZVNpdGUoXG5cdFx0XHRwYXJlbnROb2RlID8gYCR7cGFyZW50Tm9kZS5mdWxsUGF0aH0uJHt0eXBlTmFtZX1gIDogYCR7Y29sbGVjdGlvbklkID8/ICdkZWZhdWx0J306OiR7dHlwZU5hbWV9YCxcblx0XHRcdGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gXG5cdFx0KTtcblxuXHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGNvbnN0cnVjdG9yIGZ1bmN0aW9uIOKAlCB0aGUgbmV3IG5vZGUgYW5jaG9yc1xuXHRcdC8vIHJlbGF0aXZlLWZpcnN0IGdyYXBoIHJlZmVyZW5jZSByZXNvbHV0aW9uIHdoaWxlIGl0cyBvd24gc2lnbmF0dXJlXG5cdFx0Ly8gaXMgYmVpbmcgcmVhZFxuXHRcdGNvbnN0IHByZXZpb3VzQW5jaG9yID0gdGhpcy5jdXJyZW50R3JhcGhBbmNob3I7XG5cdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBub2RlO1xuXHRcdHRyeSB7XG5cdFx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzKGNhbGwpO1xuXG5cdFx0XHQvLyBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZm9yIFR5cGVSZWdpc3RyeSBzaWduYXR1cmVcblx0XHRcdG5vZGUuY29uc3RydWN0b3JQYXJhbXMgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyhjYWxsKTtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBwcmV2aW91c0FuY2hvcjtcblx0XHR9XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGhcblx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChwYXJlbnROb2RlLCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KG5vZGUpO1xuXHRcdH1cblxuXHRcdC8vIENyZWF0ZSBkZWZpbml0aW9uIGluZm8gdXNpbmcgdGhlIG5vZGUncyByZXNvbHZlZCBmdWxsUGF0aFxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiBwYXJlbnROb2RlID8gcGFyZW50Tm9kZS5mdWxsUGF0aCA6IG51bGwsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IGNvbmZpZy5zdHJpY3RDaGFpbiA/PyB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBjb25maWcuYmxvY2tFcnJvcnMgPz8gZmFsc2UsXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChub2RlLmZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0XHR0aGlzLmVkc1Njb3BlQnlOb2RlLnNldChjYWxsLCBub2RlLmZ1bGxQYXRoKTtcblxuXHRcdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnQ6IGNvbnN0IFVzZXIgPSBkZWZpbmUoJ1VzZXJFbnRpdHknLCAuLi4pIC0+IG1hcCBcIlVzZXJcIiB0byBcIlVzZXJFbnRpdHlcIlxuXHRcdC8vIEZvciBjaGFpbmVkIGNhbGxzIGxpa2UgY29uc3QgWCA9IGRlZmluZSgnQScpLmRlZmluZSgnQicpLCB3ZSB3YW50IHRvIG1hcCBYIC0+IEEgKHRoZSByb290KVxuXHRcdHRoaXMudHJhY2tWYXJpYWJsZUFzc2lnbm1lbnQoY2FsbCwgcGFyZW50Tm9kZSwgbm9kZS5mdWxsUGF0aCk7XG5cdH1cblxuXHQvKipcblx0ICogUHJvY2VzcyBhIGxhenkoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NMYXp5Q2FsbCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHQvLyBDaGVjayBpZiB0aGlzIGV4YWN0IGNhbGwgaGFzIGFscmVhZHkgYmVlbiBwcm9jZXNzZWQgKHByZXZlbnRzIGR1cGxpY2F0ZXMgZnJvbSBjaGFpbmVkIGNhbGxzKVxuXHRcdGlmICh0aGlzLm1hcmtQcm9jZXNzZWQoY2FsbCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBHZXQgdGhlIHR5cGUgbmFtZSBhbmQgc291cmNlIGNvbnRleHQgZnJvbSBhcmd1bWVudHNcblx0XHRjb25zdCBsYXp5Q29udGV4dCA9IHRoaXMuZXh0cmFjdExhenlDb250ZXh0KGNhbGwsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBkZWZpbmUoJ0EnKS5sYXp5KCdCJyksIHdlIHdhbnQgdGhlIHBvc2l0aW9uIG9mIHRoZSAubGF6eSgnQicpIHBhcnRcblx0XHQvLyBub3QgdGhlIHN0YXJ0IG9mIHRoZSBlbnRpcmUgZXhwcmVzc2lvblxuXHRcdGxldCBwb3NpdGlvbk5vZGU6IHRzLk5vZGUgPSBjYWxsO1xuXG5cdFx0Ly8gSWYgdGhpcyBpcyBhIGNoYWluZWQgY2FsbCwgZ2V0IHRoZSBwb3NpdGlvbiBvZiB0aGUgcHJvcGVydHkgYWNjZXNzIGV4cHJlc3Npb25cblx0XHQvLyB3aGljaCBpcyB0aGUgLmxhenkgcGFydFxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHQvLyBUaGUgZXhwcmVzc2lvbiBpcyB0aGUgcHJvcGVydHkgYWNjZXNzOiAoZGVmaW5lKCdSb290QXN5bmMnLCAuLi4pKS5sYXp5XG5cdFx0XHQvLyBXZSB3YW50IHRoZSBwb3NpdGlvbiBvZiBqdXN0IHRoZSAubGF6eSBwYXJ0XG5cdFx0XHQvLyBUaGlzIGlzIHRoZSAnbGF6eScgaWRlbnRpZmllclxuXHRcdFx0cG9zaXRpb25Ob2RlID0gY2FsbC5leHByZXNzaW9uLm5hbWU7XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnRQb3MgPSBwb3NpdGlvbk5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSk7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKHNvdXJjZUZpbGUsIHN0YXJ0UG9zKTtcblxuXHRcdGlmICghbGF6eUNvbnRleHQudHlwZU5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0NvdWxkIG5vdCBleHRyYWN0IHR5cGUgbmFtZSBmcm9tIGxhenkoKSBjYWxsJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IHR5cGVOYW1lIH0gPSBsYXp5Q29udGV4dDtcblxuXHRcdC8vIERldGVybWluZSBwYXJlbnQgdHlwZSBhbmQgY29sbGVjdGlvbiBiYXNlZCBvbiB0aGUgY2FsbCBzb3VyY2UuXG5cdFx0Y29uc3QgcGFyZW50Tm9kZSA9IGxhenlDb250ZXh0LnBhcmVudFR5cGU7XG5cdFx0Y29uc3QgeyBjb2xsZWN0aW9uSWQgfSA9IGxhenlDb250ZXh0O1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25maWcgb3B0aW9uc1xuXHRcdGNvbnN0IGNvbmZpZyA9IHRoaXMuZXh0cmFjdExhenlDb25maWcoY2FsbCk7XG5cblx0XHQvLyBDcmVhdGUgdHlwZSBub2RlIGZpcnN0IHNvIGl0cyBpbnRlcm5hbCBmdWxsUGF0aCAoaW5jbHVkaW5nIGFueSBjb2xsZWN0aW9uIHByZWZpeCkgaXMgcmVzb2x2ZWQuXG5cdFx0Y29uc3Qgbm9kZSA9IFR5cGVHcmFwaEltcGwuY3JlYXRlTm9kZShcblx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0cGFyZW50Tm9kZSxcblx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRsaW5lICsgMSxcblx0XHRcdGNoYXJhY3RlciArIDEsXG5cdFx0XHRjb2xsZWN0aW9uSWRcblx0XHQpO1xuXHRcdG5vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lID0gdGhpcy5nZXRSZWdpc3RyeUludGVyZmFjZU5hbWUoY29sbGVjdGlvbklkKTtcblxuXHRcdC8vIFNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZSBkZXRlY3Rpb24gKGhhcmQtZmFpbCBsYXcpXG5cdFx0dGhpcy5yZWNvcmREZWZpbmVTaXRlKFxuXHRcdFx0cGFyZW50Tm9kZSA/IGAke3BhcmVudE5vZGUuZnVsbFBhdGh9LiR7dHlwZU5hbWV9YCA6IGAke2NvbGxlY3Rpb25JZCA/PyAnZGVmYXVsdCd9Ojoke3R5cGVOYW1lfWAsXG5cdFx0XHRgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YFxuXHRcdCk7XG5cblx0XHQvLyBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSB0aGUgY29uc3RydWN0b3IgcmV0dXJuZWQgYnkgdGhlIGxhenkgZ2V0dGVyXG5cdFx0Ly8g4oCUIHRoZSBuZXcgbm9kZSBhbmNob3JzIHJlbGF0aXZlLWZpcnN0IGdyYXBoIHJlZmVyZW5jZSByZXNvbHV0aW9uXG5cdFx0Y29uc3QgcHJldmlvdXNBbmNob3IgPSB0aGlzLmN1cnJlbnRHcmFwaEFuY2hvcjtcblx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IG5vZGU7XG5cdFx0dHJ5IHtcblx0XHRcdG5vZGUucHJvcGVydGllcyA9IHRoaXMuZXh0cmFjdFByb3BlcnRpZXMoY2FsbCk7XG5cblx0XHRcdC8vIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmb3IgVHlwZVJlZ2lzdHJ5IHNpZ25hdHVyZVxuXHRcdFx0bm9kZS5jb25zdHJ1Y3RvclBhcmFtcyA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zKGNhbGwpO1xuXHRcdH0gZmluYWxseSB7XG5cdFx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IHByZXZpb3VzQW5jaG9yO1xuXHRcdH1cblxuXHRcdC8vIEFkZCB0byBncmFwaFxuXHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZENoaWxkKHBhcmVudE5vZGUsIG5vZGUpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZFJvb3Qobm9kZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ3JlYXRlIGRlZmluaXRpb24gaW5mbyB1c2luZyB0aGUgbm9kZSdzIHJlc29sdmVkIGZ1bGxQYXRoXG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IHR5cGVOYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlZmluZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IHBhcmVudE5vZGUgPyBwYXJlbnROb2RlLmZ1bGxQYXRoIDogbnVsbCxcblx0XHRcdHN0cmljdENoYWluIDogY29uZmlnLnN0cmljdENoYWluID8/IHRydWUsXG5cdFx0XHRibG9ja0Vycm9ycyA6IGNvbmZpZy5ibG9ja0Vycm9ycyA/PyBmYWxzZSxcblx0XHR9O1xuXHRcdHRoaXMuZGVmaW5pdGlvbnMuc2V0KG5vZGUuZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXHRcdHRoaXMuZWRzU2NvcGVCeU5vZGUuc2V0KGNhbGwsIG5vZGUuZnVsbFBhdGgpO1xuXG5cdFx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudDogY29uc3QgTGF6eVR5cGUgPSBsYXp5KCdMYXp5VHlwZScsIC4uLikgLT4gbWFwIFwiTGF6eVR5cGVcIiAtPiBcIkxhenlUeXBlXCJcblx0XHQvLyBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGNvbnN0IFggPSBsYXp5KCdBJykuZGVmaW5lKCdCJyksIHdlIHdhbnQgdG8gbWFwIFggLT4gQSAodGhlIHJvb3QpXG5cdFx0dGhpcy50cmFja1ZhcmlhYmxlQXNzaWdubWVudChjYWxsLCBwYXJlbnROb2RlLCBub2RlLmZ1bGxQYXRoKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGxhenkoKSBjYWxsIGFyZ3VtZW50cyBpbnRvIGEgbm9ybWFsaXplZCBzaGFwZS5cblx0ICogSGFuZGxlcyBuYW1lZC91bm5hbWVkIGFuZCBleHBsaWNpdC1zb3VyY2UgZm9ybXMsIGJvdGggYXMgZnJlZSBjYWxsc1xuXHQgKiBhbmQgYXMgbWV0aG9kIGNhbGxzLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0TGF6eUNhbGxBcmdzIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHtcblx0XHRzb3VyY2U/OiB0cy5FeHByZXNzaW9uO1xuXHRcdG5hbWU/OiBzdHJpbmc7XG5cdFx0Z2V0dGVyOiB0cy5FeHByZXNzaW9uO1xuXHRcdGNvbmZpZz86IHRzLkV4cHJlc3Npb247XG5cdH0gfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGFyZ3MgPSBjYWxsLmFyZ3VtZW50cztcblx0XHRjb25zdCBpc01ldGhvZENhbGwgPSB0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pO1xuXG5cdFx0aWYgKGlzTWV0aG9kQ2FsbCkge1xuXHRcdFx0Ly8gU291cmNlIGlzIHRoZSBvYmplY3Qgb2YgdGhlIHByb3BlcnR5IGFjY2VzczogVHlwZS5sYXp5KC4uLilcblx0XHRcdGNvbnN0IHNvdXJjZSA9IGNhbGwuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBbIG1ldGhvZEZpcnN0QXJnIF0gPSBhcmdzO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChtZXRob2RGaXJzdEFyZykpIHtcblx0XHRcdFx0Ly8gVHlwZS5sYXp5KCdOYW1lJywgZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0XHRpZiAoYXJncy5sZW5ndGggPCAyKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHNvdXJjZSxcblx0XHRcdFx0XHRuYW1lICAgOiBtZXRob2RGaXJzdEFyZy50ZXh0LFxuXHRcdFx0XHRcdGdldHRlciA6IGFyZ3NbIDEgXSxcblx0XHRcdFx0XHRjb25maWcgOiBhcmdzWyAyIF0sXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cdFx0XHQvLyBUeXBlLmxhenkoZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0c291cmNlLFxuXHRcdFx0XHRnZXR0ZXIgOiBtZXRob2RGaXJzdEFyZyxcblx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMSBdLFxuXHRcdFx0fTtcblx0XHR9XG5cblx0XHQvLyBGcmVlIGNhbGw6IGxhenkoLi4uKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBhcmdzO1xuXG5cdFx0Ly8gRXhwbGljaXQtc291cmNlIGZvcm06IGxhenkoc291cmNlLCAnTmFtZScsIGdldHRlciwgY29uZmlnPylcblx0XHQvLyBvciBsYXp5KHNvdXJjZSwgZ2V0dGVyLCBjb25maWc/KVxuXHRcdGlmIChhcmdzLmxlbmd0aCA+PSAyICYmIHRzLmlzSWRlbnRpZmllcihmaXJzdEFyZykpIHtcblx0XHRcdGNvbnN0IFsgLCBzZWNvbmRBcmcgXSA9IGFyZ3M7XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKHNlY29uZEFyZykpIHtcblx0XHRcdFx0Ly8gbGF6eShzb3VyY2UsICdOYW1lJywgZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0XHRpZiAoYXJncy5sZW5ndGggPCAzKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHNvdXJjZSA6IGZpcnN0QXJnLFxuXHRcdFx0XHRcdG5hbWUgICA6IHNlY29uZEFyZy50ZXh0LFxuXHRcdFx0XHRcdGdldHRlciA6IGFyZ3NbIDIgXSxcblx0XHRcdFx0XHRjb25maWcgOiBhcmdzWyAzIF0sXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cdFx0XHQvLyBsYXp5KHNvdXJjZSwgZ2V0dGVyLCBjb25maWc/KVxuXHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0c291cmNlIDogZmlyc3RBcmcsXG5cdFx0XHRcdGdldHRlciA6IHNlY29uZEFyZyxcblx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMiBdLFxuXHRcdFx0fTtcblx0XHR9XG5cblx0XHQvLyBOYW1lZCByb290IGZvcm06IGxhenkoJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChmaXJzdEFyZykpIHtcblx0XHRcdGlmIChhcmdzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB7XG5cdFx0XHRcdG5hbWUgICA6IGZpcnN0QXJnLnRleHQsXG5cdFx0XHRcdGdldHRlciA6IGFyZ3NbIDEgXSxcblx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMiBdLFxuXHRcdFx0fTtcblx0XHR9XG5cblx0XHQvLyBVbm5hbWVkIHJvb3QgZm9ybTogbGF6eShnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0cmV0dXJuIHtcblx0XHRcdGdldHRlciA6IGZpcnN0QXJnLFxuXHRcdFx0Y29uZmlnIDogYXJnc1sgMSBdLFxuXHRcdH07XG5cdH1cblxuXHQvKipcblx0ICogVW53cmFwIHRoZSBjb25zdHJ1Y3RvciByZXR1cm5lZCBieSBhIGxhenkgZ2V0dGVyLlxuXHQgKiBTdXBwb3J0czpcblx0ICogICAoKSA9PiBjbGFzcyBOYW1lIHt9XG5cdCAqICAgKCkgPT4gZnVuY3Rpb24gTmFtZSgpIHt9XG5cdCAqICAgKCkgPT4geyByZXR1cm4gY2xhc3MgTmFtZSB7fTsgfVxuXHQgKiAgIGZ1bmN0aW9uICgpIHsgcmV0dXJuIGZ1bmN0aW9uIE5hbWUoKSB7fTsgfVxuXHQgKi9cblx0cHJpdmF0ZSB1bndyYXBMYXp5R2V0dGVyIChnZXR0ZXJFeHByOiB0cy5FeHByZXNzaW9uKTogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihnZXR0ZXJFeHByKSkge1xuXHRcdFx0Y29uc3QgeyBib2R5IH0gPSBnZXR0ZXJFeHByO1xuXHRcdFx0aWYgKCF0cy5pc0Jsb2NrKGJvZHkpKSB7XG5cdFx0XHRcdHJldHVybiBib2R5O1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBzdG10IG9mIGJvZHkuc3RhdGVtZW50cykge1xuXHRcdFx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQoc3RtdCkgJiYgc3RtdC5leHByZXNzaW9uKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHN0bXQuZXhwcmVzc2lvbjtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oZ2V0dGVyRXhwcikpIHtcblx0XHRcdGNvbnN0IHsgYm9keSB9ID0gZ2V0dGVyRXhwcjtcblx0XHRcdGZvciAoY29uc3Qgc3RtdCBvZiBib2R5LnN0YXRlbWVudHMpIHtcblx0XHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KHN0bXQpICYmIHN0bXQuZXhwcmVzc2lvbikge1xuXHRcdFx0XHRcdHJldHVybiBzdG10LmV4cHJlc3Npb247XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gTm90IGEgcmVjb2duaXplZCBnZXR0ZXIgcGF0dGVyblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBhIGNvbnN0cnVjdG9yIG5hbWUgZnJvbSBhIGNsYXNzIGV4cHJlc3Npb24sIGNsYXNzIGRlY2xhcmF0aW9uLFxuXHQgKiBvciBuYW1lZCBmdW5jdGlvbiBleHByZXNzaW9uLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JOYW1lIChjb25zdHJ1Y3RvckV4cHI6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc0NsYXNzRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpICYmIGNvbnN0cnVjdG9yRXhwci5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gY29uc3RydWN0b3JFeHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihjb25zdHJ1Y3RvckV4cHIpICYmIGNvbnN0cnVjdG9yRXhwci5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gY29uc3RydWN0b3JFeHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikgJiYgY29uc3RydWN0b3JFeHByLm5hbWUpIHtcblx0XHRcdHJldHVybiBjb25zdHJ1Y3RvckV4cHIubmFtZS50ZXh0O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdGhlIHR5cGUgbmFtZSBmcm9tIGVpdGhlciBhIGRlZmluZSgpIG9yIGxhenkoKSBjYWxsLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0TW5lbW9uaWNhVHlwZU5hbWUgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwoY2FsbCkpIHtcblx0XHRcdHJldHVybiB0aGlzLmV4dHJhY3RUeXBlTmFtZShjYWxsKTtcblx0XHR9XG5cdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChjYWxsKSkge1xuXHRcdFx0Y29uc3QgYXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRcdGlmICghYXJncykge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGFyZ3MubmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gYXJncy5uYW1lO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy51bndyYXBMYXp5R2V0dGVyKGFyZ3MuZ2V0dGVyKTtcblx0XHRcdGlmIChjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdFx0cmV0dXJuIHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yTmFtZShjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdGhlIGZ1bGwgbGF6eSgpIGNhbGwgY29udGV4dDogdHlwZSBuYW1lLCBwYXJlbnQgdHlwZSwgYW5kIGNvbGxlY3Rpb24uXG5cdCAqIEhhbmRsZXMgZGlyZWN0IGNhbGxzLCBwcm9wZXJ0eS1hY2Nlc3MgY2FsbHMsIGNoYWluZWQgY2FsbHMsIGFuZCB0aGVcblx0ICogZXhwbGljaXQtc291cmNlIGZvcm0gYGxhenkoc291cmNlLCAnVHlwZU5hbWUnLCBnZXR0ZXIpYC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdExhenlDb250ZXh0IChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHtcblx0XHR0eXBlTmFtZT86IHN0cmluZztcblx0XHRwYXJlbnRUeXBlPzogVHlwZU5vZGU7XG5cdFx0Y29sbGVjdGlvbklkPzogc3RyaW5nO1xuXHR9IHtcblx0XHRjb25zdCBhcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdGlmICghYXJncykge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGxldCB0eXBlTmFtZTogc3RyaW5nIHwgdW5kZWZpbmVkID0gYXJncy5uYW1lO1xuXHRcdGlmICghdHlwZU5hbWUpIHtcblx0XHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMudW53cmFwTGF6eUdldHRlcihhcmdzLmdldHRlcik7XG5cdFx0XHRpZiAoY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRcdHR5cGVOYW1lID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JOYW1lKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGlmICghdHlwZU5hbWUpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IGNhbGw7XG5cblx0XHQvLyBEaXJlY3QgY2FsbDogbGF6eSgnVHlwZU5hbWUnLCAuLi4pIG9yIGxhenkoc291cmNlLCAnVHlwZU5hbWUnLCBnZXR0ZXIpXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLnRleHQgPT09ICdsYXp5Jykge1xuXHRcdFx0aWYgKGFyZ3Muc291cmNlICYmIHRzLmlzSWRlbnRpZmllcihhcmdzLnNvdXJjZSkpIHtcblx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShhcmdzLnNvdXJjZS50ZXh0KTtcblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHR0eXBlTmFtZSxcblx0XHRcdFx0XHRwYXJlbnRUeXBlICAgOiBzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUsXG5cdFx0XHRcdFx0Y29sbGVjdGlvbklkIDogc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQsXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cdFx0XHQvLyBQbGFpbiByb290IGxhenkgaW4gZGVmYXVsdCBjb2xsZWN0aW9uXG5cdFx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2VzczogWC5sYXp5KCdUeXBlTmFtZScsIC4uLilcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi5uYW1lLnRleHQgPT09ICdsYXp5Jykge1xuXHRcdFx0Y29uc3Qgb2JqID0gZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG9iaikpIHtcblx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShvYmoudGV4dCk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBOZXN0ZWQgYWNjZXNzOiBpbnN0YW5jZS5UeXBlLmxhenkgLSB0cnkgdG8gcmVzb2x2ZVxuXHRcdFx0XHRjb25zdCBjaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlDaGFpbihvYmopO1xuXHRcdFx0XHRpZiAoY2hhaW4ubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGNoYWluLmpvaW4oJy4nKSk7XG5cdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlIH07XG5cdFx0XHRcdH1cblx0XHRcdH1cblxuXHRcdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBEZXRlcm1pbmUgdGhlIGNvbGxlY3Rpb24gY29udGV4dCBmcm9tIHRoZSByb290IG9mIHRoZSBjaGFpbiBzbyB0aGF0XG5cdFx0XHRcdC8vIGN1c3RvbS1jb2xsZWN0aW9uIHR5cGVzIGRvIG5vdCBnZXQgY29uZnVzZWQgd2l0aCBkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMuXG5cdFx0XHRcdGNvbnN0IHJvb3RJZCA9IHRoaXMuZ2V0Um9vdElkZW50aWZpZXIob2JqLmV4cHJlc3Npb24pO1xuXHRcdFx0XHRjb25zdCBleHBlY3RlZENvbGxlY3Rpb25JZCA9IHJvb3RJZFxuXHRcdFx0XHRcdD8gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKHJvb3RJZC50ZXh0KS5jb2xsZWN0aW9uSWRcblx0XHRcdFx0XHQ6IHVuZGVmaW5lZDtcblxuXHRcdFx0XHQvLyBDaGFpbmVkIGNhbGw6IGRlZmluZSgnQScpLmxhenkoJ0InKSBvciBsYXp5KCdBJykubGF6eSgnQicpXG5cdFx0XHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ2FsbChvYmosIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudFR5cGVOYW1lID0gdGhpcy5leHRyYWN0TW5lbW9uaWNhVHlwZU5hbWUob2JqKTtcblx0XHRcdFx0XHRpZiAocGFyZW50VHlwZU5hbWUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKHBhcmVudFR5cGVOYW1lLCBleHBlY3RlZENvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGlmICh0aGlzLmlzTGF6eUNhbGwob2JqKSkge1xuXHRcdFx0XHRcdHRoaXMucHJvY2Vzc0xhenlDYWxsKG9iaiwgc291cmNlRmlsZSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gQnVpbGRlciBsb29rdXAgY2hhaW46IEFwcC5sb29rdXAoJ1VzZXInKS5sYXp5KCdBZG1pbicpXG5cdFx0XHRcdGlmICh0aGlzLmlzTG9va3VwQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0Y29uc3QgbG9va2VkVXBQYXRoID0gdGhpcy5yZXNvbHZlTG9va3VwUGF0aChvYmopO1xuXHRcdFx0XHRcdGlmIChsb29rZWRVcFBhdGgpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKGxvb2tlZFVwUGF0aCk7XG5cdFx0XHRcdFx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGUuY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHsgdHlwZU5hbWUgfTtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IGNvbmZpZyBvcHRpb25zIGZyb20gbGF6eSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdExhenlDb25maWcgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogeyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9IHtcblx0XHRjb25zdCBhcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdGlmICghYXJncyB8fCAhYXJncy5jb25maWcgfHwgIXRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24oYXJncy5jb25maWcpKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgY29uZmlnUmVzdWx0ID0gdGhpcy5leHRyYWN0Q29uZmlnRnJvbU9iamVjdExpdGVyYWwoYXJncy5jb25maWcpO1xuXHRcdHJldHVybiBjb25maWdSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHQqIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnRzIHRoYXQgY2FwdHVyZSBkZWZpbmUoKSByZXN1bHRzXG5cdFx0KiBlLmcuLCBjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKSBtYXBzIFwiVXNlclwiIC0+IFwiVXNlckVudGl0eVwiXG5cdFx0KiBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGNvbnN0IFggPSBkZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKSwgd2UgbWFwIFggLT4gQSAodGhlIHJvb3QgdHlwZSlcblx0XHQqL1xuXHRwcml2YXRlIHRyYWNrVmFyaWFibGVBc3NpZ25tZW50IChcblx0XHRjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbixcblx0XHRwYXJlbnROb2RlOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCxcblx0XHRmdWxsUGF0aDogc3RyaW5nXG5cdCk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGlmIHRoaXMgY2FsbCBpcyB0aGUgcmlnaHQtaGFuZCBzaWRlIG9mIGEgdmFyaWFibGUgZGVjbGFyYXRpb25cblx0XHQvLyBXYWxrIHVwIHRoZSB0cmVlIHRvIGZpbmQgVmFyaWFibGVEZWNsYXJhdGlvblxuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gY2FsbC5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24oY3VycmVudCkpIHtcblx0XHRcdFx0Ly8gRm91bmQ6IGNvbnN0IFggPSBkZWZpbmUoLi4uKVxuXHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCB2YXJOYW1lID0gY3VycmVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Ly8gSWYgdGhpcyBpcyBhIGNoYWluZWQgY2FsbCAoaGFzIHBhcmVudCksIGRvbid0IG92ZXJ3cml0ZSBleGlzdGluZyBtYXBwaW5nXG5cdFx0XHRcdFx0Ly8gVGhlIGZpcnN0IGRlZmluZSBpbiB0aGUgY2hhaW4gc2V0cyB0aGUgbWFwcGluZyB0byB0aGUgcm9vdCB0eXBlXG5cdFx0XHRcdFx0aWYgKHBhcmVudE5vZGUgJiYgdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5oYXModmFyTmFtZSkpIHtcblx0XHRcdFx0XHRcdHJldHVybjtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0dGhpcy52YXJpYWJsZVRvVHlwZU1hcC5zZXQodmFyTmFtZSwgZnVsbFBhdGgpO1xuXHRcdFx0XHRcdHRoaXMudHJhY2tGaWxlR3JhcGhCaW5kaW5nKHZhck5hbWUsIGZ1bGxQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm47XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIE1pcnJvciBhIHZhcmlhYmxlIC0+IG1uZW1vbmljYSBmdWxsUGF0aCBiaW5kaW5nIGludG8gdGhlIHBlci1maWxlXG5cdCAqIHZhbHVlLXNjb3BlIG1hcCAoZ3JhcGggaWRlbnRpdHkgbGF3OiBgdHlwZW9mIFhgIGFuZCBiYXJlIHJlZmVyZW5jZXNcblx0ICogcmVzb2x2ZSB0aHJvdWdoIHRoZSBmaWxlJ3Mgb3duIGJpbmRpbmdzIGZpcnN0KS5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tGaWxlR3JhcGhCaW5kaW5nICh2YXJOYW1lOiBzdHJpbmcsIGZ1bGxQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRsZXQgYmluZGluZ3MgPSB0aGlzLmZpbGVHcmFwaEJpbmRpbmdzLmdldChmaWxlUGF0aCk7XG5cdFx0aWYgKCFiaW5kaW5ncykge1xuXHRcdFx0YmluZGluZ3MgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0dGhpcy5maWxlR3JhcGhCaW5kaW5ncy5zZXQoZmlsZVBhdGgsIGJpbmRpbmdzKTtcblx0XHR9XG5cdFx0YmluZGluZ3Muc2V0KHZhck5hbWUsIGZ1bGxQYXRoKTtcblx0fVxuXHRcblx0LyoqXG5cdFx0KiBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50cyBmcm9tIGxvb2t1cCgpIGNhbGxzXG5cdFx0KiBlLmcuLCBjb25zdCBTZW50aWVuY2VDb25zdHJ1Y3RvciA9IGxvb2t1cCgnU2VudGllbmNlJykgbWFwcyBcIlNlbnRpZW5jZUNvbnN0cnVjdG9yXCIgLT4gXCJTZW50aWVuY2VcIlxuXHRcdCovXG5cdHByaXZhdGUgdHJhY2tMb29rdXBBc3NpZ25tZW50IChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgdHlwZVBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdC8vIFdhbGsgdXAgdGhlIHRyZWUgdG8gZmluZCBWYXJpYWJsZURlY2xhcmF0aW9uXG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBjYWxsLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0aWYgKHRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihjdXJyZW50KSkge1xuXHRcdFx0XHQvLyBGb3VuZDogY29uc3QgWCA9IGxvb2t1cCguLi4pXG5cdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudC5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHZhck5hbWUgPSBjdXJyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0XHR0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLnNldCh2YXJOYW1lLCB0eXBlUGF0aCk7XG5cdFx0XHRcdFx0dGhpcy50cmFja0ZpbGVHcmFwaEJpbmRpbmcodmFyTmFtZSwgdHlwZVBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHQqIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnRzIGZyb20gbmV3IFR5cGUoKSBjYWxsc1xuXHRcdCogZS5nLiwgY29uc3QgdXNlciA9IG5ldyBVc2VyVHlwZSgpIG1hcHMgXCJ1c2VyXCIgLT4gXCJVc2VyVHlwZVwiXG5cdFx0Ki9cblx0cHJpdmF0ZSB0cmFja05ld0Fzc2lnbm1lbnQgKG5ld0V4cHI6IHRzLk5ld0V4cHJlc3Npb24sIHR5cGVQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHQvLyBXYWxrIHVwIHRoZSB0cmVlIHRvIGZpbmQgVmFyaWFibGVEZWNsYXJhdGlvblxuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbmV3RXhwci5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24oY3VycmVudCkpIHtcblx0XHRcdFx0Ly8gRm91bmQ6IGNvbnN0IFggPSBuZXcgVHlwZSguLi4pXG5cdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudC5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHZhck5hbWUgPSBjdXJyZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0XHR0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLnNldCh2YXJOYW1lLCB0eXBlUGF0aCk7XG5cdFx0XHRcdFx0dGhpcy50cmFja0ZpbGVHcmFwaEJpbmRpbmcodmFyTmFtZSwgdHlwZVBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHQqIFByb2Nlc3MgYSBAZGVjb3JhdGUoKSBkZWNvcmF0b3Jcblx0ICovXG5cdHByaXZhdGUgcHJvY2Vzc0RlY29yYXRlRGVjb3JhdG9yIChcblx0XHRkZWNvcmF0b3I6IHRzLkRlY29yYXRvcixcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdGNsYXNzRGVjbFBhcmFtPzogdHMuQ2xhc3NEZWNsYXJhdGlvblxuXHQpOiB2b2lkIHtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0ZGVjb3JhdG9yLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblxuXHRcdC8vIEdldCB0aGUgY2xhc3MgZGVjbGFyYXRpb24gLSB1c2UgdGhlIHBhc3NlZCBjb250ZXh0IGlmIHBhcmVudCBpcyBub3Qgc2V0XG5cdFx0Y29uc3QgY2xhc3NEZWNsID0gZGVjb3JhdG9yLnBhcmVudCBhcyB0cy5DbGFzc0RlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHx8IGNsYXNzRGVjbFBhcmFtO1xuXHRcdGlmICghY2xhc3NEZWNsIHx8ICFjbGFzc0RlY2wubmFtZSkge1xuXHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdG1lc3NhZ2UgOiAnRGVjb3JhdGVkIGNsYXNzIGhhcyBubyBuYW1lJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB0eXBlTmFtZSA9IGNsYXNzRGVjbC5uYW1lLnRleHQ7XG5cdFx0aWYgKCF0eXBlTmFtZSkge1xuXHRcdFx0dGhpcy5lcnJvcnMucHVzaCh7XG5cdFx0XHRcdG1lc3NhZ2UgOiAnRGVjb3JhdGVkIGNsYXNzIGhhcyBubyBuYW1lJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBQYXJzZSBkZWNvcmF0b3IgYXJndW1lbnRzOiBAZGVjb3JhdGUoKSwgQGRlY29yYXRlKFBhcmVudCksXG5cdFx0Ly8gQGRlY29yYXRlKHsgLi4uIH0pLCBAZGVjb3JhdGUoUGFyZW50LCB7IC4uLiB9KSxcblx0XHQvLyBATXlDb2xsZWN0aW9uLmRlY29yYXRlKCksIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoeyAuLi4gfSlcblx0XHRsZXQgcGFyZW50Tm9kZTogVHlwZU5vZGUgfCB1bmRlZmluZWQ7XG5cdFx0bGV0IHBhcmVudEZ1bGxQYXRoOiBzdHJpbmcgfCBudWxsID0gbnVsbDtcblx0XHRsZXQgY29sbGVjdGlvbklkOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdFx0bGV0IGRlY29yYXRvckNvbmZpZzogeyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9ID0ge307XG5cblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihkZWNvcmF0b3IuZXhwcmVzc2lvbikpIHtcblx0XHRcdGNvbnN0IGNhbGxFeHByID0gZGVjb3JhdG9yLmV4cHJlc3Npb247XG5cdFx0XHRjb25zdCBjYWxsZWUgPSBjYWxsRXhwci5leHByZXNzaW9uO1xuXG5cdFx0XHQvLyBDaGVjayBmb3IgQE15Q29sbGVjdGlvbi5kZWNvcmF0ZSgpIHdoZXJlIE15Q29sbGVjdGlvbiBpcyBhIGN1c3RvbSBjb2xsZWN0aW9uLlxuXHRcdFx0Ly8gVGhlIGRlY29yYXRlZCBjbGFzcyBiZWNvbWVzIGEgcm9vdCB0eXBlIGluIHRoYXQgY29sbGVjdGlvbi5cblx0XHRcdGlmIChcblx0XHRcdFx0dHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbGVlKSAmJlxuXHRcdFx0XHRjYWxsZWUubmFtZS50ZXh0ID09PSAnZGVjb3JhdGUnICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihjYWxsZWUuZXhwcmVzc2lvbikgJiZcblx0XHRcdFx0dGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmhhcyhjYWxsZWUuZXhwcmVzc2lvbi50ZXh0KVxuXHRcdFx0KSB7XG5cdFx0XHRcdGNvbGxlY3Rpb25JZCA9IHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5nZXQoY2FsbGVlLmV4cHJlc3Npb24udGV4dCk7XG5cdFx0XHRcdGlmIChjYWxsRXhwci5hcmd1bWVudHMubGVuZ3RoID09PSAxICYmIHRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24oY2FsbEV4cHIuYXJndW1lbnRzWyAwIF0pKSB7XG5cdFx0XHRcdFx0ZGVjb3JhdG9yQ29uZmlnID0gdGhpcy5leHRyYWN0Q29uZmlnRnJvbU9iamVjdExpdGVyYWwoY2FsbEV4cHIuYXJndW1lbnRzWyAwIF0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRjb25zdCBhcmdzID0gY2FsbEV4cHIuYXJndW1lbnRzO1xuXHRcdFx0XHRsZXQgcGFyZW50QXJnOiB0cy5JZGVudGlmaWVyIHwgdW5kZWZpbmVkO1xuXHRcdFx0XHRsZXQgY29uZmlnQXJnOiB0cy5PYmplY3RMaXRlcmFsRXhwcmVzc2lvbiB8IHVuZGVmaW5lZDtcblxuXHRcdFx0XHRmb3IgKGNvbnN0IGFyZyBvZiBhcmdzKSB7XG5cdFx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihhcmcpKSB7XG5cdFx0XHRcdFx0XHRpZiAocGFyZW50QXJnKSB7XG5cdFx0XHRcdFx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRcdFx0XHRcdG1lc3NhZ2UgOiAnQGRlY29yYXRlKCkgYWNjZXB0cyBvbmx5IG9uZSBwYXJlbnQgcmVmZXJlbmNlJyxcblx0XHRcdFx0XHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0XHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdFx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHRcdFx0cGFyZW50QXJnID0gYXJnO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH0gZWxzZSBpZiAodHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihhcmcpKSB7XG5cdFx0XHRcdFx0XHRpZiAoY29uZmlnQXJnKSB7XG5cdFx0XHRcdFx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRcdFx0XHRcdG1lc3NhZ2UgOiAnQGRlY29yYXRlKCkgYWNjZXB0cyBvbmx5IG9uZSBjb25maWcgb2JqZWN0Jyxcblx0XHRcdFx0XHRcdFx0XHRmaWxlICAgIDogc291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdFx0XHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdFx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHRcdFx0Y29uZmlnQXJnID0gYXJnO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGlmIChwYXJlbnRBcmcpIHtcblx0XHRcdFx0XHRwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5SWRlbnRpZmllcihwYXJlbnRBcmcudGV4dCk7XG5cdFx0XHRcdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdFx0XHRcdHBhcmVudEZ1bGxQYXRoID0gcGFyZW50Tm9kZS5mdWxsUGF0aDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRpZiAoY29uZmlnQXJnKSB7XG5cdFx0XHRcdFx0ZGVjb3JhdG9yQ29uZmlnID0gdGhpcy5leHRyYWN0Q29uZmlnRnJvbU9iamVjdExpdGVyYWwoY29uZmlnQXJnKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIEJ1aWxkIGZ1bGwgcGF0aFxuXHRcdGNvbnN0IGZ1bGxQYXRoID0gcGFyZW50Tm9kZSA/IGAke3BhcmVudE5vZGUuZnVsbFBhdGh9LiR7dHlwZU5hbWV9YCA6IHR5cGVOYW1lO1xuXG5cdFx0Ly8gQ3JlYXRlIGRlZmluaXRpb24gaW5mbyBmb3IgZGVjb3JhdGVcblx0XHRjb25zdCBkZWZpbml0aW9uOiBEZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVjb3JhdGUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiBwYXJlbnRGdWxsUGF0aCxcblx0XHRcdHN0cmljdENoYWluIDogZGVjb3JhdG9yQ29uZmlnLnN0cmljdENoYWluID8/IHRydWUsXG5cdFx0XHRibG9ja0Vycm9ycyA6IGRlY29yYXRvckNvbmZpZy5ibG9ja0Vycm9ycyA/PyBmYWxzZSxcblx0XHR9O1xuXHRcdHRoaXMuZGVmaW5pdGlvbnMuc2V0KGZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0XHR0aGlzLmVkc1Njb3BlQnlOb2RlLnNldChjbGFzc0RlY2wsIGZ1bGxQYXRoKTtcblxuXHRcdC8vIENyZWF0ZSB0eXBlIG5vZGVcblx0XHRjb25zdCBub2RlID0gVHlwZUdyYXBoSW1wbC5jcmVhdGVOb2RlKFxuXHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRwYXJlbnROb2RlLFxuXHRcdFx0c291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdGxpbmUgKyAxLFxuXHRcdFx0Y2hhcmFjdGVyICsgMSxcblx0XHRcdGNvbGxlY3Rpb25JZFxuXHRcdCk7XG5cdFx0bm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWUgPSB0aGlzLmdldFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZShub2RlLmNvbGxlY3Rpb25JZCk7XG5cblx0XHQvLyBTYW1lLW5hbWVzcGFjZSBkdXBsaWNhdGUgZGV0ZWN0aW9uIChoYXJkLWZhaWwgbGF3KVxuXHRcdHRoaXMucmVjb3JkRGVmaW5lU2l0ZShcblx0XHRcdHBhcmVudE5vZGUgPyBgJHtwYXJlbnROb2RlLmZ1bGxQYXRofS4ke3R5cGVOYW1lfWAgOiBgJHtjb2xsZWN0aW9uSWQgPz8gJ2RlZmF1bHQnfTo6JHt0eXBlTmFtZX1gLFxuXHRcdFx0YCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWBcblx0XHQpO1xuXG5cdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGFuZCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZyb20gY2xhc3MgbWVtYmVycyDigJRcblx0XHQvLyB0aGUgbmV3IG5vZGUgYW5jaG9ycyByZWxhdGl2ZS1maXJzdCBncmFwaCByZWZlcmVuY2UgcmVzb2x1dGlvblxuXHRcdGNvbnN0IHByZXZpb3VzQW5jaG9yID0gdGhpcy5jdXJyZW50R3JhcGhBbmNob3I7XG5cdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBub2RlO1xuXHRcdHRyeSB7XG5cdFx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RDbGFzc1Byb3BlcnRpZXMoY2xhc3NEZWNsKTtcblx0XHRcdG5vZGUuY29uc3RydWN0b3JQYXJhbXMgPSB0aGlzLmV4dHJhY3RDbGFzc0NvbnN0cnVjdG9yUGFyYW1zKGNsYXNzRGVjbCk7XG5cdFx0fSBmaW5hbGx5IHtcblx0XHRcdHRoaXMuY3VycmVudEdyYXBoQW5jaG9yID0gcHJldmlvdXNBbmNob3I7XG5cdFx0fVxuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoXG5cdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkQ2hpbGQocGFyZW50Tm9kZSwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCB0eXBlIG5hbWUgZnJvbSBkZWZpbmUoKSBjYWxsIGFyZ3VtZW50cy5cblx0ICogSGFuZGxlczpcblx0ICogICBkZWZpbmUoJ1R5cGVOYW1lJywgaGFuZGxlcilcblx0ICogICBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKSAgIC8vIGV4cGxpY2l0LXNvdXJjZSBmb3JtXG5cdCAqICAgZGVmaW5lKGZ1bmN0aW9uIFR5cGVOYW1lKCkge30pXG5cdCAqICAgZGVmaW5lKCgpID0+IGNsYXNzIFR5cGVOYW1lIHt9KVxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0VHlwZU5hbWUgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBhcmdzID0gY2FsbC5hcmd1bWVudHM7XG5cblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgWyBmaXJzdEFyZyBdID0gYXJncztcblxuXHRcdC8vIEV4cGxpY2l0LXNvdXJjZSBmb3JtOiBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA+PSAyICYmIHRzLmlzSWRlbnRpZmllcihmaXJzdEFyZykgJiYgdHMuaXNTdHJpbmdMaXRlcmFsKGFyZ3NbIDEgXSkpIHtcblx0XHRcdHJldHVybiBhcmdzWyAxIF0udGV4dDtcblx0XHR9XG5cblx0XHQvLyBTdHJpbmcgbGl0ZXJhbDogZGVmaW5lKCdUeXBlTmFtZScsIC4uLilcblx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGZpcnN0QXJnKSkge1xuXHRcdFx0cmV0dXJuIGZpcnN0QXJnLnRleHQ7XG5cdFx0fVxuXG5cdFx0Ly8gRnVuY3Rpb24gd2l0aCBuYW1lOiBkZWZpbmUoZnVuY3Rpb24gVHlwZU5hbWUoKSB7fSlcblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oZmlyc3RBcmcpICYmIGZpcnN0QXJnLm5hbWUpIHtcblx0XHRcdHJldHVybiBmaXJzdEFyZy5uYW1lLnRleHQ7XG5cdFx0fVxuXG5cdFx0Ly8gQXJyb3cgZnVuY3Rpb24gcmV0dXJuaW5nIGNsYXNzOiBkZWZpbmUoKCkgPT4gY2xhc3MgVHlwZU5hbWUge30pXG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihmaXJzdEFyZykpIHtcblx0XHRcdGNvbnN0IHsgYm9keSB9ID0gZmlyc3RBcmc7XG5cdFx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oYm9keSkgJiYgYm9keS5uYW1lKSB7XG5cdFx0XHRcdHJldHVybiBib2R5Lm5hbWUudGV4dDtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdGhlIGZ1bGwgZGVmaW5lKCkgY2FsbCBjb250ZXh0OiB0eXBlIG5hbWUsIHBhcmVudCB0eXBlLCBhbmQgY29sbGVjdGlvbi5cblx0ICogSGFuZGxlcyBkaXJlY3QgY2FsbHMsIHByb3BlcnR5LWFjY2VzcyBjYWxscywgY2hhaW5lZCBjYWxscywgYW5kIHRoZVxuXHQgKiBleHBsaWNpdC1zb3VyY2UgZm9ybSBgZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilgLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0RGVmaW5lQ29udGV4dCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7XG5cdFx0dHlwZU5hbWU/OiBzdHJpbmc7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Y29uc3QgdHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RUeXBlTmFtZShjYWxsKTtcblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBjYWxsO1xuXG5cdFx0Ly8gRGlyZWN0IGNhbGw6IGRlZmluZSgnVHlwZU5hbWUnLCAuLi4pIG9yIGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByZXNzaW9uKSAmJiBleHByZXNzaW9uLnRleHQgPT09ICdkZWZpbmUnKSB7XG5cdFx0XHQvLyBFeHBsaWNpdC1zb3VyY2UgZm9ybTogZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilcblx0XHRcdGlmIChjYWxsLmFyZ3VtZW50cy5sZW5ndGggPj0gMiAmJiB0cy5pc0lkZW50aWZpZXIoY2FsbC5hcmd1bWVudHNbIDAgXSkpIHtcblx0XHRcdFx0Y29uc3Qgc291cmNlTmFtZSA9IGNhbGwuYXJndW1lbnRzWyAwIF0udGV4dDtcblx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShzb3VyY2VOYW1lKTtcblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHR0eXBlTmFtZSxcblx0XHRcdFx0XHRwYXJlbnRUeXBlICAgOiBzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUsXG5cdFx0XHRcdFx0Y29sbGVjdGlvbklkIDogc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQsXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cblx0XHRcdC8vIFBsYWluIHJvb3QgZGVmaW5lIGluIGRlZmF1bHQgY29sbGVjdGlvblxuXHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUgfTtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSBhY2Nlc3M6IFguZGVmaW5lKCdUeXBlTmFtZScsIC4uLilcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi5uYW1lLnRleHQgPT09ICdkZWZpbmUnKSB7XG5cdFx0XHRjb25zdCBvYmogPSBleHByZXNzaW9uLmV4cHJlc3Npb247XG5cblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIob2JqKSkge1xuXHRcdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKG9iai50ZXh0KTtcblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHR0eXBlTmFtZSxcblx0XHRcdFx0XHRwYXJlbnRUeXBlICAgOiBzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUsXG5cdFx0XHRcdFx0Y29sbGVjdGlvbklkIDogc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQsXG5cdFx0XHRcdH07XG5cdFx0XHR9XG5cblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihvYmopKSB7XG5cdFx0XHRcdC8vIE5lc3RlZCBhY2Nlc3M6IGluc3RhbmNlLlR5cGUuZGVmaW5lIC0gdHJ5IHRvIHJlc29sdmVcblx0XHRcdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4ob2JqKTtcblx0XHRcdFx0aWYgKGNoYWluLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShjaGFpbi5qb2luKCcuJykpO1xuXHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSB9O1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gRGV0ZXJtaW5lIHRoZSBjb2xsZWN0aW9uIGNvbnRleHQgZnJvbSB0aGUgcm9vdCBvZiB0aGUgY2hhaW4gc28gdGhhdFxuXHRcdFx0XHQvLyBjdXN0b20tY29sbGVjdGlvbiB0eXBlcyBkbyBub3QgZ2V0IGNvbmZ1c2VkIHdpdGggZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzLlxuXHRcdFx0XHRjb25zdCByb290SWQgPSB0aGlzLmdldFJvb3RJZGVudGlmaWVyKG9iai5leHByZXNzaW9uKTtcblx0XHRcdFx0Y29uc3QgZXhwZWN0ZWRDb2xsZWN0aW9uSWQgPSByb290SWRcblx0XHRcdFx0XHQ/IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShyb290SWQudGV4dCkuY29sbGVjdGlvbklkXG5cdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHRcdFx0Ly8gQ2hhaW5lZCBjYWxsOiBkZWZpbmUoJ0EnKS5kZWZpbmUoJ0InKSBvciBtbmVtb25pY2EuZGVmaW5lKCdBJykuZGVmaW5lKCdCJylcblx0XHRcdFx0aWYgKHRoaXMuaXNEZWZpbmVDYWxsKG9iaikpIHtcblx0XHRcdFx0XHR0aGlzLnByb2Nlc3NEZWZpbmVDYWxsKG9iaiwgY2FsbC5nZXRTb3VyY2VGaWxlKCkpO1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudFR5cGVOYW1lID0gdGhpcy5leHRyYWN0VHlwZU5hbWUob2JqKTtcblx0XHRcdFx0XHRpZiAocGFyZW50VHlwZU5hbWUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKHBhcmVudFR5cGVOYW1lLCBleHBlY3RlZENvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHQvLyBJbmhlcml0IGNvbGxlY3Rpb24gZnJvbSB0aGUgcGFyZW50IHR5cGUgKGlmIGFueSlcblx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gQ2hhaW5lZCBsYXp5IGNhbGw6IGxhenkoJ0EnKS5kZWZpbmUoJ0InKSBvciBUeXBlLmxhenkoJ0EnKS5kZWZpbmUoJ0InKVxuXHRcdFx0XHRpZiAodGhpcy5pc0xhenlDYWxsKG9iaikpIHtcblx0XHRcdFx0XHR0aGlzLnByb2Nlc3NMYXp5Q2FsbChvYmosIGNhbGwuZ2V0U291cmNlRmlsZSgpKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBCdWlsZGVyIGxvb2t1cCBjaGFpbjogQXBwLmxvb2t1cCgnVXNlcicpLmRlZmluZSgnQWRtaW4nKVxuXHRcdFx0XHRpZiAodGhpcy5pc0xvb2t1cENhbGwob2JqKSkge1xuXHRcdFx0XHRcdGNvbnN0IGxvb2tlZFVwUGF0aCA9IHRoaXMucmVzb2x2ZUxvb2t1cFBhdGgob2JqKTtcblx0XHRcdFx0XHRpZiAobG9va2VkVXBQYXRoKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShsb29rZWRVcFBhdGgpO1xuXHRcdFx0XHRcdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlLmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdH1cblxuXHQvKipcblx0ICogUHJlZml4IGEgZG90dGVkIHR5cGUgcGF0aCB3aXRoIGEgY29sbGVjdGlvbiBpZGVudGlmaWVyIHNvIGN1c3RvbS1jb2xsZWN0aW9uXG5cdCAqIHR5cGVzIGRvIG5vdCBjb2xsaWRlIHdpdGggZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzIGluIHRoZSBncmFwaC5cblx0ICovXG5cdHByaXZhdGUgcHJlZml4Q29sbGVjdGlvblBhdGggKHBhdGg6IHN0cmluZywgY29sbGVjdGlvbklkOiBzdHJpbmcpOiBzdHJpbmcge1xuXHRcdHJldHVybiBgJHtjb2xsZWN0aW9uSWR9Ojoke3BhdGh9YDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgZGVmaW5lKCkgc291cmNlIGlkZW50aWZpZXIgdG8gZWl0aGVyIGEgcGFyZW50IHR5cGUsIGEgY29sbGVjdGlvbixcblx0ICogb3IgdGhlIGRlZmF1bHQgKG1vZHVsZSBvYmplY3QpIGNvbGxlY3Rpb24uXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVEZWZpbmVTb3VyY2UgKHNvdXJjZU5hbWU6IHN0cmluZyk6IHtcblx0XHRwYXJlbnRUeXBlPzogVHlwZU5vZGU7XG5cdFx0Y29sbGVjdGlvbklkPzogc3RyaW5nO1xuXHR9IHtcblx0XHQvLyBNb2R1bGUgb2JqZWN0IGFsaWFzZXMgLT4gcm9vdCBpbiBkZWZhdWx0IGNvbGxlY3Rpb25cblx0XHRpZiAodGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuaGFzKHNvdXJjZU5hbWUpKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Ly8gQ29sbGVjdGlvbiB2YXJpYWJsZXMgLT4gcm9vdCBpbiB0aGF0IGNvbGxlY3Rpb25cblx0XHRjb25zdCBjb2xsZWN0aW9uSWQgPSB0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuZ2V0KHNvdXJjZU5hbWUpO1xuXHRcdGlmIChjb2xsZWN0aW9uSWQpIHtcblx0XHRcdHJldHVybiB7IGNvbGxlY3Rpb25JZCB9O1xuXHRcdH1cblxuXHRcdC8vIE90aGVyd2lzZSB0cmVhdCBhcyBhIHR5cGUgdmFyaWFibGUgcmVmZXJlbmNlXG5cdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeUlkZW50aWZpZXIoc291cmNlTmFtZSk7XG5cdFx0cmV0dXJuIHsgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGEgY2FsbCBleHByZXNzaW9uIGlzIGEgbG9va3VwKCkgY2FsbC5cblx0ICovXG5cdHByaXZhdGUgaXNMb29rdXBDYWxsIChub2RlOiB0cy5DYWxsRXhwcmVzc2lvbik6IGJvb2xlYW4ge1xuXHRcdGNvbnN0IGV4cHIgPSBub2RlLmV4cHJlc3Npb247XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSAmJiBleHByLnRleHQgPT09ICdsb29rdXAnKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpICYmIGV4cHIubmFtZS50ZXh0ID09PSAnbG9va3VwJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgbG9va3VwKCkgY2FsbCB0byBhIGRvdHRlZCB0eXBlIHBhdGggKGJlc3QgZWZmb3J0KS5cblx0ICogSGFuZGxlczpcblx0ICogICBsb29rdXAoJ1VzZXInKVxuXHQgKiAgIGxvb2t1cChzb3VyY2UsICdVc2VyJylcblx0ICogICBBcHAubG9va3VwKCdVc2VyJylcblx0ICogICBjb2xsZWN0aW9uLmxvb2t1cCgnVXNlci5BZG1pbicpXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVMb29rdXBQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBTaW5nbGUtYXJnIGxvb2t1cDogbG9va3VwKCdVc2VyJykgb3IgQXBwLmxvb2t1cCgnVXNlcicpXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAxKSB7XG5cdFx0XHRjb25zdCBbIGFyZyBdID0gYXJncztcblx0XHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoYXJnKSB8fCB0cy5pc05vU3Vic3RpdHV0aW9uVGVtcGxhdGVMaXRlcmFsKGFyZykpIHtcblx0XHRcdFx0Y29uc3QgcGF0aCA9IGFyZy50ZXh0O1xuXHRcdFx0XHQvLyBJZiB0aGlzIGlzIGEgbWV0aG9kIGNhbGwgb24gYSBzb3VyY2UsIHJlc29sdmUgcmVsYXRpdmUgdG8gdGhhdCBzb3VyY2UuXG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0Y29uc3Qgc291cmNlRXhwciA9IGNhbGwuZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXHRcdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoc291cmNlRXhwcikpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHNvdXJjZU5hbWUgPSBzb3VyY2VFeHByLnRleHQ7XG5cdFx0XHRcdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKHNvdXJjZU5hbWUpO1xuXHRcdFx0XHRcdFx0aWYgKHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKSB7XG5cdFx0XHRcdFx0XHRcdC8vIENvbGxlY3Rpb24gbG9va3VwOiBwcmVmaXggcGF0aCB3aXRoIHRoZSBjb2xsZWN0aW9uIGlkXG5cdFx0XHRcdFx0XHRcdHJldHVybiB0aGlzLnByZWZpeENvbGxlY3Rpb25QYXRoKHBhdGgsIHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdGlmIChzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUpIHtcblx0XHRcdFx0XHRcdFx0Ly8gVHlwZSBsb29rdXA6IHJlbGF0aXZlIGZpcnN0LCB0aGVuIHJvb3QgZmFsbGJhY2tcblx0XHRcdFx0XHRcdFx0Y29uc3QgcmVsYXRpdmVQYXRoID0gYCR7c291cmNlQ29udGV4dC5wYXJlbnRUeXBlLmZ1bGxQYXRofS4ke3BhdGh9YDtcblx0XHRcdFx0XHRcdFx0aWYgKHRoaXMuZ3JhcGguZmluZFR5cGUocmVsYXRpdmVQYXRoKSkge1xuXHRcdFx0XHRcdFx0XHRcdHJldHVybiByZWxhdGl2ZVBhdGg7XG5cdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdFx0cmV0dXJuIHBhdGg7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiBwYXRoO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBUd28tYXJnIGxvb2t1cDogbG9va3VwKHNvdXJjZSwgJ1VzZXInKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA+PSAyKSB7XG5cdFx0XHRjb25zdCBbIHNvdXJjZUFyZywgcGF0aEFyZyBdID0gYXJncztcblx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHNvdXJjZUFyZykgfHwgIXRzLmlzU3RyaW5nTGl0ZXJhbChwYXRoQXJnKSkge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgc291cmNlTmFtZSA9IHNvdXJjZUFyZy50ZXh0O1xuXHRcdFx0Y29uc3QgcGF0aCA9IHBhdGhBcmcudGV4dDtcblx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRpZiAoc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQpIHtcblx0XHRcdFx0cmV0dXJuIHRoaXMucHJlZml4Q29sbGVjdGlvblBhdGgocGF0aCwgc291cmNlQ29udGV4dC5jb2xsZWN0aW9uSWQpO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSkge1xuXHRcdFx0XHRjb25zdCByZWxhdGl2ZVBhdGggPSBgJHtzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUuZnVsbFBhdGh9LiR7cGF0aH1gO1xuXHRcdFx0XHRpZiAodGhpcy5ncmFwaC5maW5kVHlwZShyZWxhdGl2ZVBhdGgpKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHJlbGF0aXZlUGF0aDtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdH1cblx0XHRcdHJldHVybiBwYXRoO1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogTG9va3VwLWxhdyBkZWxlZ2F0ZSBmb3IgdGhlIGxvY2FsLXNjb3BlIHdhbGtlciAoc2NvcGVzLmpzb24gdHlwZVBhdGhcblx0ICogbWV0YWRhdGEpOiByZXNvbHZlIGEgbG9va3VwKCkgaW5pdGlhbGl6ZXIgY2FsbCB0aHJvdWdoIGV4YWN0bHkgdGhlXG5cdCAqIHRpZXJzIHRoZSB1c2FnZXMgcGFzcyByZXNvbHZlZCBpdCBhZ2FpbnN0IChzYW1lIHNvdXJjZSByZXNvbHV0aW9uLFxuXHQgKiBzYW1lIGNvbXBsZXRlIGdyYXBoKS4gVGhlIHdhbGtlciBydW5zIGl0cyBvd24gc2NvcGUtY2hhaW4gdmFsdWUtc2NvcGVcblx0ICogdGllciBiZWZvcmUgZGVsZWdhdGluZzsgZXZlcnl0aGluZyBhYm92ZSB2YWx1ZSBzY29wZSBsYW5kcyBoZXJlLCBzb1xuXHQgKiBzY29wZXMuanNvbiBuZXZlciBkaXNhZ3JlZXMgd2l0aCB0aGUgaGFyZC1mYWlsLWxhdyB2ZXJkaWN0cy5cblx0ICovXG5cdHJlc29sdmVMb29rdXBDYWxsUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMucmVzb2x2ZUxvb2t1cFBhdGgoY2FsbCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHRcdCogRmluZCBhIHBhcmVudCB0eXBlIGJ5IGl0cyBuYW1lLCBzZWFyY2hpbmcgaW4gdGhlIGdyYXBoLlxuXHRcdCogV2hlbiBjb2xsZWN0aW9uSWQgaXMgcHJvdmlkZWQsIG9ubHkgdHlwZXMgZnJvbSB0aGF0IGNvbGxlY3Rpb24gYXJlIGNvbnNpZGVyZWQuXG5cdFx0Ki9cblx0cHJpdmF0ZSBmaW5kUGFyZW50VHlwZUJ5TmFtZSAoXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZ1xuXHQpOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgbWF0Y2hlc0NvbGxlY3Rpb24gPSAodHlwZTogVHlwZU5vZGUpOiBib29sZWFuID0+IHtcblx0XHRcdGlmIChjb2xsZWN0aW9uSWQgPT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRyZXR1cm4gdHlwZS5jb2xsZWN0aW9uSWQgPT09IHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB0eXBlLmNvbGxlY3Rpb25JZCA9PT0gY29sbGVjdGlvbklkO1xuXHRcdH07XG5cblx0XHQvLyBGaXJzdCB0cnkgZXhhY3QgbWF0Y2ggKGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcyB1c2UgdGhlIHBsYWluIGRvdHRlZCBwYXRoKVxuXHRcdGNvbnN0IGV4YWN0ID0gdGhpcy5ncmFwaC5maW5kVHlwZShuYW1lKTtcblx0XHRpZiAoZXhhY3QgJiYgbWF0Y2hlc0NvbGxlY3Rpb24oZXhhY3QpKSB7XG5cdFx0XHRyZXR1cm4gZXhhY3Q7XG5cdFx0fVxuXG5cdFx0Ly8gVGhlbiBzZWFyY2ggdGhyb3VnaCBhbGwgdHlwZXMgZm9yIG9uZSB3aXRoIG1hdGNoaW5nIG5hbWUgYW5kIGNvbGxlY3Rpb25cblx0XHRmb3IgKGNvbnN0IHR5cGUgb2YgdGhpcy5ncmFwaC5nZXRBbGxUeXBlcygpKSB7XG5cdFx0XHRpZiAodHlwZS5uYW1lID09PSBuYW1lICYmIG1hdGNoZXNDb2xsZWN0aW9uKHR5cGUpKSB7XG5cdFx0XHRcdHJldHVybiB0eXBlO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0XHQqIEZpbmQgYSBwYXJlbnQgdHlwZSBmcm9tIGFuIGlkZW50aWZpZXIgcmVmZXJlbmNlLlxuXHRcdCogSGFuZGxlcyBib3RoIGFsaWFzZWQgdmFyaWFibGVzIChjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKSlcblx0XHQqIGFuZCBkaXJlY3QgY2xhc3MvdHlwZSBuYW1lcy5cblx0XHQqL1xuXHRwcml2YXRlIGZpbmRQYXJlbnRUeXBlQnlJZGVudGlmaWVyIChuYW1lOiBzdHJpbmcpOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gRmlyc3QgY2hlY2sgdmFyaWFibGUgbWFwcGluZzogY29uc3QgVXNlciA9IGRlZmluZSgnVXNlckVudGl0eScsIC4uLilcblx0XHRjb25zdCBtYXBwZWRGdWxsUGF0aCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KG5hbWUpO1xuXHRcdGlmIChtYXBwZWRGdWxsUGF0aCkge1xuXHRcdFx0Y29uc3QgbWFwcGVkTm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUobWFwcGVkRnVsbFBhdGgpO1xuXHRcdFx0aWYgKG1hcHBlZE5vZGUpIHJldHVybiBtYXBwZWROb2RlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKG5hbWUpO1xuXHRcdHJldHVybiBwYXJlbnROb2RlO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCB0aGUgbGVmdG1vc3QgaWRlbnRpZmllciBvZiBhIHByb3BlcnR5LWFjY2VzcyBjaGFpbi5cblx0ICogRm9yIGBBcHAuZGVmaW5lKCdVc2VyJykuZGVmaW5lKCdBZG1pbicpYCB0aGlzIHJldHVybnMgdGhlIGBBcHBgIGlkZW50aWZpZXIuXG5cdCAqL1xuXHRwcml2YXRlIGdldFJvb3RJZGVudGlmaWVyIChleHByOiB0cy5FeHByZXNzaW9uKTogdHMuSWRlbnRpZmllciB8IHVuZGVmaW5lZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLkV4cHJlc3Npb24gPSBleHByO1xuXHRcdHdoaWxlICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQuZXhwcmVzc2lvbjtcblx0XHR9XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50KSkge1xuXHRcdFx0cmV0dXJuIGN1cnJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0XHQqIEdldCBwcm9wZXJ0eSBjaGFpbiBmcm9tIG5lc3RlZCBhY2Nlc3Ncblx0XHQqL1xuXHRwcml2YXRlIGdldFByb3BlcnR5Q2hhaW4gKGV4cHI6IHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbiB8IHRzLklkZW50aWZpZXIpOiBzdHJpbmdbXSB7XG5cdFx0Y29uc3QgY2hhaW46IHN0cmluZ1tdID0gW107XG5cblx0XHRsZXQgY3VycmVudDogdHMuRXhwcmVzc2lvbiA9IGV4cHI7XG5cdFx0d2hpbGUgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRpZiAoY3VycmVudC5uYW1lKSB7XG5cdFx0XHRcdGNoYWluLnVuc2hpZnQoY3VycmVudC5uYW1lLnRleHQpO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQuZXhwcmVzc2lvbjtcblx0XHR9XG5cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQpKSB7XG5cdFx0XHRjaGFpbi51bnNoaWZ0KGN1cnJlbnQudGV4dCk7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGNoYWluO1xuXHR9XG5cblx0LyoqXG5cdCAqIERldGVybWluZSB0aGUgY29uc3RydWN0b3IgZXhwcmVzc2lvbiBmb3IgZWl0aGVyIGEgZGVmaW5lKCkgb3IgbGF6eSgpIGNhbGwuXG5cdCAqIEZvciBkZWZpbmUoKSB0aGlzIGlzIHRoZSBjb25zdHJ1Y3QgaGFuZGxlcjsgZm9yIGxhenkoKSBpdCBpcyB0aGUgdmFsdWVcblx0ICogcmV0dXJuZWQgYnkgdGhlIGxhenkgZ2V0dGVyLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGV4cHIgPSBjYWxsLmV4cHJlc3Npb247XG5cdFx0Y29uc3QgbmFtZSA9IHRzLmlzSWRlbnRpZmllcihleHByKVxuXHRcdFx0PyBleHByLnRleHRcblx0XHRcdDogdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcilcblx0XHRcdFx0PyBleHByLm5hbWUudGV4dFxuXHRcdFx0XHQ6ICcnO1xuXG5cdFx0aWYgKG5hbWUgPT09ICdsYXp5Jykge1xuXHRcdFx0Y29uc3QgbGF6eUFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0XHRpZiAoIWxhenlBcmdzKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdGhpcy51bndyYXBMYXp5R2V0dGVyKGxhenlBcmdzLmdldHRlcik7XG5cdFx0fVxuXG5cdFx0Ly8gZGVmaW5lKCkgY2FsbFxuXHRcdGNvbnN0IGFyZ3MgPSBjYWxsLmFyZ3VtZW50cztcblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gTW9kZXJuIGZvcm06IGRlZmluZSgnTmFtZScsIGhhbmRsZXIsIGNvbmZpZz8pXG5cdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChhcmdzWyAwIF0pKSB7XG5cdFx0XHRyZXR1cm4gYXJnc1sgMSBdO1xuXHRcdH1cblxuXHRcdC8vIExlZ2FjeSBmb3JtOiBkZWZpbmUoZnVuY3Rpb24gTmFtZSgpIHt9KSBvciBkZWZpbmUoKCkgPT4gY2xhc3MgTmFtZSB7fSlcblx0XHRyZXR1cm4gYXJnc1sgMCBdO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGNvbnN0cnVjdG9yIGZ1bmN0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RQcm9wZXJ0aWVzIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yRXhwcmVzc2lvbihjYWxsKTtcblx0XHRpZiAoIWNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0cmV0dXJuIG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMuZXh0cmFjdFByb3BlcnRpZXNGcm9tQ29uc3RydWN0b3IoY29uc3RydWN0b3JFeHByKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGEgY29uc3RydWN0b3IgZXhwcmVzc2lvbiAoZnVuY3Rpb24sIGFycm93LCBvciBjbGFzcykuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RQcm9wZXJ0aWVzRnJvbUNvbnN0cnVjdG9yIChjb25zdHJ1Y3RvckV4cHI6IHRzLkV4cHJlc3Npb24pOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCBwcm9wZXJ0aWVzID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblxuXHRcdC8vIEJ1aWxkIHR5cGUgbWFwIGZyb20gZGF0YSBwYXJhbWV0ZXIgKGZvciB0aGlzLnggPSBkYXRhLnggcGF0dGVybnMpXG5cdFx0Y29uc3QgZGF0YVR5cGVNYXAgPSB0aGlzLmJ1aWxkRGF0YVR5cGVNYXAoY29uc3RydWN0b3JFeHByKTtcblxuXHRcdC8vIEhhbmRsZSBmdW5jdGlvbiBleHByZXNzaW9uXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikgfHwgdHMuaXNBcnJvd0Z1bmN0aW9uKGNvbnN0cnVjdG9yRXhwcikpIHtcblx0XHRcdGNvbnN0IHsgYm9keSB9ID0gY29uc3RydWN0b3JFeHByO1xuXG5cdFx0XHQvLyBGaXJzdCwgZXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gYHRoaXNgIHBhcmFtZXRlciB0eXBlIGFubm90YXRpb25cblx0XHRcdC8vIFRoaXMgaGFuZGxlcyBwYXR0ZXJucyBsaWtlOiBmdW5jdGlvbih0aGlzOiBTb21lVHlwZSwgZGF0YTogU29tZVR5cGUpIHsgfVxuXHRcdFx0Y29uc3QgdGhpc1BhcmFtUHJvcGVydGllcyA9IHRoaXMuZXh0cmFjdFRoaXNQYXJhbVByb3BlcnRpZXMoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdGZvciAoY29uc3QgWyBuYW1lLCBwcm9wSW5mbyBdIG9mIHRoaXNQYXJhbVByb3BlcnRpZXMpIHtcblx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwgcHJvcEluZm8pO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBGdW5jdGlvbiBib2R5IHdpdGggc3RhdGVtZW50c1xuXHRcdFx0aWYgKHRzLmlzQmxvY2soYm9keSkpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBzdG10IG9mIGJvZHkuc3RhdGVtZW50cykge1xuXHRcdFx0XHRcdGlmICh0cy5pc0V4cHJlc3Npb25TdGF0ZW1lbnQoc3RtdCkpIHtcblx0XHRcdFx0XHRcdHRoaXMuZXh0cmFjdFByb3BlcnR5RnJvbVN0YXRlbWVudChzdG10LmV4cHJlc3Npb24sIHByb3BlcnRpZXMsIGRhdGFUeXBlTWFwKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBIYW5kbGUgY2xhc3MgZXhwcmVzc2lvblxuXHRcdGlmICh0cy5pc0NsYXNzRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHQvLyBGaXJzdCBwYXNzOiBjb2xsZWN0IGFsbCBwcm9wZXJ0eSB0eXBlcyBmb3IgbWV0aG9kIGluZmVyZW5jZVxuXHRcdFx0Y29uc3QgY2xhc3NQcm9wZXJ0eVR5cGVzID0gdGhpcy5leHRyYWN0Q2xhc3NQcm9wZXJ0eVR5cGVzKGNvbnN0cnVjdG9yRXhwcik7XG5cblx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGNvbnN0cnVjdG9yRXhwci5tZW1iZXJzKSB7XG5cdFx0XHRcdC8vIEhhbmRsZSBwcm9wZXJ0eSBkZWNsYXJhdGlvbnNcblx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlEZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lKSB7XG5cdFx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgcHJvcGVydGllc1xuXHRcdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdFx0XHRtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZDtcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cblx0XHRcdFx0XHRjb25zdCBuYW1lID0gdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSA/IG1lbWJlci5uYW1lLnRleHQgOiAnJztcblx0XHRcdFx0XHRpZiAobmFtZSkge1xuXHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0XHR0eXBlICAgICA6IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKSxcblx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gSGFuZGxlIG1ldGhvZCBkZWNsYXJhdGlvbnNcblx0XHRcdFx0aWYgKHRzLmlzTWV0aG9kRGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgbWV0aG9kc1xuXHRcdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdFx0XHRtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZDtcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cblx0XHRcdFx0XHRjb25zdCBuYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlck1ldGhvZFR5cGUobWVtYmVyLCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIEhhbmRsZSBnZXR0ZXIgZGVjbGFyYXRpb25zXG5cdFx0XHRcdGlmICh0cy5pc0dldEFjY2Vzc29yKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIGdldHRlcnNcblx0XHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4ge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHRcdFx0bS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQ7XG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXG5cdFx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Ly8gRmlyc3QgdHJ5IGV4cGxpY2l0IHR5cGUgYW5ub3RhdGlvbiwgdGhlbiBpbmZlciBmcm9tIGdldHRlciBib2R5XG5cdFx0XHRcdFx0bGV0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0aWYgKHR5cGUgPT09ICd1bmtub3duJyAmJiBtZW1iZXIuYm9keSkge1xuXHRcdFx0XHRcdFx0dHlwZSA9IHRoaXMuaW5mZXJSZXR1cm5UeXBlRnJvbUJvZHkobWVtYmVyLmJvZHksIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdHJlYWRvbmx5IDogdHJ1ZSxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBwcm9wZXJ0aWVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIEJ1aWxkIGEgdHlwZSBtYXAgZnJvbSBhbGwgcGFyYW1ldGVycyB3aXRoIGlubGluZSBvYmplY3QgdHlwZSBhbm5vdGF0aW9uc1xuXHQgKiBSZXR1cm5zIGEgbWFwIG9mIFwicGFyYW1OYW1lLnByb3BlcnR5TmFtZVwiIC0+IHR5cGVcblx0ICovXG5cdHByaXZhdGUgYnVpbGREYXRhVHlwZU1hcCAoaGFuZGxlckFyZzogdHMuRXhwcmVzc2lvbik6IE1hcDxzdHJpbmcsIHN0cmluZz4ge1xuXHRcdGNvbnN0IHR5cGVNYXAgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXG5cdFx0aWYgKCF0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihoYW5kbGVyQXJnKSAmJiAhdHMuaXNBcnJvd0Z1bmN0aW9uKGhhbmRsZXJBcmcpKSB7XG5cdFx0XHRyZXR1cm4gdHlwZU1hcDtcblx0XHR9XG5cblx0XHQvLyBJdGVyYXRlIG92ZXIgQUxMIHBhcmFtZXRlcnNcblx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGhhbmRsZXJBcmcucGFyYW1ldGVycykge1xuXHRcdFx0aWYgKCFwYXJhbS5uYW1lIHx8ICFwYXJhbS50eXBlKSBjb250aW51ZTtcblxuXHRcdFx0Ly8gR2V0IHBhcmFtZXRlciBuYW1lXG5cdFx0XHRsZXQgcGFyYW1OYW1lID0gJyc7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpKSB7XG5cdFx0XHRcdHBhcmFtTmFtZSA9IHBhcmFtLm5hbWUudGV4dDtcblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdC8vIFNraXAgZGVzdHJ1Y3R1cmVkIHBhcmFtZXRlcnMgZm9yIG5vd1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gQ2hlY2sgaWYgaXQncyBhbiBpbmxpbmUgb2JqZWN0IHR5cGUgbGl0ZXJhbFxuXHRcdFx0aWYgKHRzLmlzVHlwZUxpdGVyYWxOb2RlKHBhcmFtLnR5cGUpKSB7XG5cdFx0XHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIHBhcmFtLnR5cGUubWVtYmVycykge1xuXHRcdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRcdHR5cGVNYXAuc2V0KGAke3BhcmFtTmFtZX0uJHtwcm9wTmFtZX1gLCB0eXBlKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdC8vIE5hbWVkIHR5cGUgcmVmZXJlbmNlIChhbGlhcy9pbnRlcmZhY2UvY2xhc3MsIGltcG9ydGVkIG9yXG5cdFx0XHRcdC8vIGxvY2FsIOKAlCBGMTQpOiBkZWNvbXBvc2UgdGhlIHJlc29sdmVkIGRlY2xhcmF0aW9uIGludG9cblx0XHRcdFx0Ly8gcGVyLXByb3BlcnR5IGVudHJpZXMgdGhyb3VnaCB0aGUgc2FtZSBpbXBvcnQtYXdhcmVcblx0XHRcdFx0Ly8gbWFjaGluZXJ5IGFzIGNvbnN0cnVjdG9yIHNpZ25hdHVyZXMgKEYxMCksIGluY2x1ZGluZyB0aGVcblx0XHRcdFx0Ly8gaGVyaXRhZ2Ugd2FsayAoRjEzKS4gV2l0aG91dCB0aGlzLCBgdGhpcy54ID0gcGFyYW0ueWBcblx0XHRcdFx0Ly8gcmVhZCBgdW5rbm93bmAgZm9yIG5hbWVkIHBhcmFtcyDigJQgb25seSBpbmxpbmUgbGl0ZXJhbHNcblx0XHRcdFx0Ly8gd2VyZSBkZWNvbXBvc2VkLiBVbnJlc29sdmFibGUg4oaSIHdob2xlLXBhcmFtIGZhbGxiYWNrXG5cdFx0XHRcdC8vIGJlbG93OyBhIGJhcmUgbmFtZSBpcyBuZXZlciBlbWl0dGVkIGVpdGhlciB3YXlcblx0XHRcdFx0bGV0IG5hbWVkRGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZDtcblx0XHRcdFx0aWYgKHRzLmlzVHlwZVJlZmVyZW5jZU5vZGUocGFyYW0udHlwZSkgJiYgdHMuaXNJZGVudGlmaWVyKHBhcmFtLnR5cGUudHlwZU5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgcGFyYW1UeXBlTmFtZSA9IHBhcmFtLnR5cGUudHlwZU5hbWUudGV4dDtcblx0XHRcdFx0XHRuYW1lZERlY2wgPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKHBhcmFtVHlwZU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKG5hbWVkRGVjbCkge1xuXHRcdFx0XHRcdC8vIG1lbWJlciB0eXBlcyByZXNvbHZlIGFnYWluc3QgdGhlIERFQ0xBUklORyBmaWxlXG5cdFx0XHRcdFx0Y29uc3QgcmVmZXJlbmNpbmdGaWxlID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdFx0XHRcdHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9IG5hbWVkRGVjbC5maWxlO1xuXHRcdFx0XHRcdHRyeSB7XG5cdFx0XHRcdFx0XHRjb25zdCBkZWNsUHJvcGVydGllcyA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllcyhuYW1lZERlY2wpO1xuXHRcdFx0XHRcdFx0Zm9yIChjb25zdCBbIHByb3BOYW1lLCBpbmZvIF0gb2YgZGVjbFByb3BlcnRpZXMpIHtcblx0XHRcdFx0XHRcdFx0dHlwZU1hcC5zZXQoYCR7cGFyYW1OYW1lfS4ke3Byb3BOYW1lfWAsIGluZm8udHlwZSk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fSBmaW5hbGx5IHtcblx0XHRcdFx0XHRcdHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9IHJlZmVyZW5jaW5nRmlsZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Ly8ga2VlcCB0aGUgd2hvbGUtcGFyYW0gZW50cnkgdG9vOiBgdGhpcy54ID0gZGF0YWAgKHRoZVxuXHRcdFx0XHRcdC8vIGJhcmUgcGFyYW1ldGVyKSBhc3NpZ25zIHRoZSBmdWxsIGV4cGFuZGVkIHNoYXBlIOKAlFxuXHRcdFx0XHRcdC8vIHRoZSBzYW1lIHN0cmluZyBjb25zdHJ1Y3Rvci1zaWduYXR1cmUgZW1pc3Npb24gdXNlc1xuXHRcdFx0XHRcdGNvbnN0IHdob2xlVHlwZSA9IHRoaXMuZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihuYW1lZERlY2wpO1xuXHRcdFx0XHRcdGlmICh3aG9sZVR5cGUgJiYgd2hvbGVUeXBlICE9PSAndW5rbm93bicpIHtcblx0XHRcdFx0XHRcdHR5cGVNYXAuc2V0KHBhcmFtTmFtZSwgd2hvbGVUeXBlKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0Ly8gU3RvcmUgc2ltcGxlIHBhcmFtZXRlciB0eXBlcyBsaWtlIGBkZWNvcmF0ZVZhbHVlOiBzdHJpbmdgXG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKHBhcmFtLnR5cGUpO1xuXHRcdFx0XHRcdGlmICh0eXBlICE9PSAndW5rbm93bicpIHtcblx0XHRcdFx0XHRcdHR5cGVNYXAuc2V0KHBhcmFtTmFtZSwgdHlwZSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHR5cGVNYXA7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0eSBhY2Nlc3MgY2hhaW4gKGUuZy4sIFwiZGF0YVJlbmFtZWQuaWRcIiBmcm9tIGRhdGFSZW5hbWVkLmlkKVxuXHQgKiBIYW5kbGVzIGZhbGxiYWNrcyBsaWtlOiBkYXRhLnBlcm1pc3Npb25zIHx8IFtdXG5cdCAqL1xuXHRwcml2YXRlIGdldFByb3BlcnR5QWNjZXNzQ2hhaW4gKGV4cHI6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdC8vIEhhbmRsZSBpZGVudGlmaWVyOiBkYXRhXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIGV4cHIudGV4dDtcblx0XHR9XG5cdFx0Ly8gSGFuZGxlIHByb3BlcnR5IGFjY2VzczogZGF0YS5wZXJtaXNzaW9uc1xuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0Y29uc3QgYmFzZSA9IHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihleHByLmV4cHJlc3Npb24pO1xuXHRcdFx0aWYgKGJhc2UpIHtcblx0XHRcdFx0cmV0dXJuIGAke2Jhc2V9LiR7ZXhwci5uYW1lLnRleHR9YDtcblx0XHRcdH1cblx0XHR9XG5cdFx0Ly8gSGFuZGxlIGZhbGxiYWNrIHBhdHRlcm46IGRhdGEucGVybWlzc2lvbnMgfHwgW11cblx0XHRpZiAodHMuaXNCaW5hcnlFeHByZXNzaW9uKGV4cHIpICYmXG5cdFx0XHRleHByLm9wZXJhdG9yVG9rZW4ua2luZCA9PT0gdHMuU3ludGF4S2luZC5CYXJCYXJUb2tlbikge1xuXHRcdFx0Ly8gUmV0dXJuIHRoZSBsZWZ0IHNpZGUgb2YgfHwgb3BlcmF0b3Jcblx0XHRcdHJldHVybiB0aGlzLmdldFByb3BlcnR5QWNjZXNzQ2hhaW4oZXhwci5sZWZ0KTtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnR5IGFzc2lnbm1lbnQgZnJvbSBzdGF0ZW1lbnRcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFByb3BlcnR5RnJvbVN0YXRlbWVudCAoXG5cdFx0ZXhwcjogdHMuRXhwcmVzc2lvbixcblx0XHRwcm9wZXJ0aWVzOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+LFxuXHRcdGRhdGFUeXBlTWFwOiBNYXA8c3RyaW5nLCBzdHJpbmc+ID0gbmV3IE1hcCgpXG5cdCk6IHZvaWQge1xuXHRcdC8vIEhhbmRsZTogdGhpcy5wcm9wZXJ0eSA9IHZhbHVlXG5cdFx0aWYgKHRzLmlzQmluYXJ5RXhwcmVzc2lvbihleHByKSAmJlxuXHRcdFx0ZXhwci5vcGVyYXRvclRva2VuLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRXF1YWxzVG9rZW4pIHtcblx0XHRcdGNvbnN0IHsgbGVmdCB9ID0gZXhwcjtcblxuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGxlZnQpKSB7XG5cdFx0XHRcdC8vIENoZWNrIGlmIGFjY2Vzc2luZyAndGhpcycgKFRoaXNLZXl3b3JkKVxuXHRcdFx0XHRpZiAobGVmdC5leHByZXNzaW9uLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdFx0XHRjb25zdCBuYW1lID0gbGVmdC5uYW1lPy50ZXh0O1xuXHRcdFx0XHRcdGlmIChuYW1lKSB7XG5cdFx0XHRcdFx0XHQvLyBUcnkgdG8gZ2V0IHR5cGUgZnJvbSBkYXRhVHlwZU1hcCB1c2luZyBmdWxsIGFjY2VzcyBjaGFpbiAoZS5nLiwgXCJkYXRhUmVuYW1lZC5pZFwiKVxuXHRcdFx0XHRcdFx0Y29uc3QgYWNjZXNzQ2hhaW4gPSB0aGlzLmdldFByb3BlcnR5QWNjZXNzQ2hhaW4oZXhwci5yaWdodCk7XG5cdFx0XHRcdFx0XHRsZXQgdHlwZSA9IGFjY2Vzc0NoYWluID8gZGF0YVR5cGVNYXAuZ2V0KGFjY2Vzc0NoYWluKSA6IHVuZGVmaW5lZDtcblx0XHRcdFx0XHRcdC8vIElmIG5vdCBmb3VuZCBhbmQgUkhTIGlzIGEgc2ltcGxlIGlkZW50aWZpZXIsIHRyeSBsb29raW5nIGl0IHVwIGRpcmVjdGx5XG5cdFx0XHRcdFx0XHRpZiAoIXR5cGUgJiYgdHMuaXNJZGVudGlmaWVyKGV4cHIucmlnaHQpKSB7XG5cdFx0XHRcdFx0XHRcdHR5cGUgPSBkYXRhVHlwZU1hcC5nZXQoZXhwci5yaWdodC50ZXh0KTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdGlmICghdHlwZSkge1xuXHRcdFx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIoZXhwci5yaWdodCwgZGF0YVR5cGVNYXApO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0Ly8gRG9uJ3Qgb3ZlcndyaXRlIGEga25vd24gdHlwZSBmcm9tIGEgYHRoaXNgIGFubm90YXRpb25cblx0XHRcdFx0XHRcdC8vIHdpdGggYW4gdW5rbm93bi1iZWFyaW5nIGluZmVyZW5jZTogYW4gZW1wdHktYXJyYXlcblx0XHRcdFx0XHRcdC8vIGluaXRpYWxpemVyIGluZmVycyAnQXJyYXk8dW5rbm93bj4nLCB3aGljaCBtdXN0IG5vdFxuXHRcdFx0XHRcdFx0Ly8gY2xvYmJlciBhbiBhbm5vdGF0ZWQgJ0FycmF5PHsgaWQ6IG51bWJlciB9PicgZWl0aGVyLlxuXHRcdFx0XHRcdFx0Ly8gXCJLbm93blwiIG9uIHRoZSBFWElTVElORyBzaWRlIG1lYW5zIHRoZSB3aG9sZSB0eXBlIElTXG5cdFx0XHRcdFx0XHQvLyBgdW5rbm93bmAgKGV4YWN0IG1hdGNoKSDigJQgYSBzdWJzdHJpbmcgbWF0Y2ggdHJlYXRzXG5cdFx0XHRcdFx0XHQvLyBgUmVjb3JkPHN0cmluZywgdW5rbm93bj5gIGFzIHVua25vd24tYmVhcmluZyBhbmQgbGV0XG5cdFx0XHRcdFx0XHQvLyBpbmZlcmVuY2UgY2xvYmJlciBhIGdvb2QgYW5ub3RhdGlvbiAoRjE0KVxuXHRcdFx0XHRcdFx0Y29uc3QgZXhpc3RpbmcgPSBwcm9wZXJ0aWVzLmdldChuYW1lKTtcblx0XHRcdFx0XHRcdGNvbnN0IHR5cGVIYXNVbmtub3duID0gIXR5cGUgfHwgdHlwZS5pbmNsdWRlcygndW5rbm93bicpO1xuXHRcdFx0XHRcdFx0Y29uc3QgZXhpc3RpbmdJc0tub3duID0gZXhpc3RpbmcgPyBleGlzdGluZy50eXBlLnRyaW0oKSAhPT0gJ3Vua25vd24nIDogZmFsc2U7XG5cdFx0XHRcdFx0XHRpZiAoZXhpc3RpbmdJc0tub3duICYmIHR5cGVIYXNVbmtub3duKSB7XG5cdFx0XHRcdFx0XHRcdC8vIEtlZXAgdGhlIGJldHRlciB0eXBlIGZyb20gZXhwbGljaXQgYW5ub3RhdGlvblxuXHRcdFx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6IGV4aXN0aW5nID8gZXhpc3Rpbmcub3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gSGFuZGxlOiBPYmplY3QuYXNzaWduKHRoaXMsIHsgcHJvcDogdmFsdWUgfSlcblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0Y29uc3QgZm4gPSBleHByLmV4cHJlc3Npb247XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZm4pICYmXG5cdFx0XHRcdGZuLm5hbWU/LnRleHQgPT09ICdhc3NpZ24nICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihmbi5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHRmbi5leHByZXNzaW9uLnRleHQgPT09ICdPYmplY3QnKSB7XG5cdFx0XHRcdGNvbnN0IGFyZ3MgPSBleHByLmFyZ3VtZW50cztcblx0XHRcdFx0aWYgKGFyZ3MubGVuZ3RoID49IDIgJiYgYXJnc1sgMCBdLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdFx0XHQvLyBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSB0aGUgc2Vjb25kIGFyZ3VtZW50XG5cdFx0XHRcdFx0Y29uc3QgWyAsIHByb3BzQXJnIF0gPSBhcmdzO1xuXHRcdFx0XHRcdGlmICh0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKHByb3BzQXJnKSkge1xuXHRcdFx0XHRcdFx0Zm9yIChjb25zdCBwcm9wIG9mIHByb3BzQXJnLnByb3BlcnRpZXMpIHtcblx0XHRcdFx0XHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBc3NpZ25tZW50KHByb3ApICYmIHRzLmlzSWRlbnRpZmllcihwcm9wLm5hbWUpKSB7XG5cdFx0XHRcdFx0XHRcdFx0Y29uc3QgbmFtZSA9IHByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0XHR0eXBlICAgICA6IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKHByb3AuaW5pdGlhbGl6ZXIpLFxuXHRcdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBmYWxzZSxcblx0XHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBjbGFzcyBkZWNsYXJhdGlvbiAoaW5jbHVkaW5nIG1ldGhvZHMgYW5kIGdldHRlcnMpXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDbGFzc1Byb3BlcnRpZXMgKGNsYXNzRGVjbDogdHMuQ2xhc3NEZWNsYXJhdGlvbik6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgY2xhc3NEZWNsLm1lbWJlcnMpIHtcblx0XHRcdC8vIEhhbmRsZSBwcm9wZXJ0eSBkZWNsYXJhdGlvbnNcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5RGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSkge1xuXHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBwcm9wZXJ0aWVzXG5cdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHQgICAgIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkKTtcblx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRjb25zdCBuYW1lID0gdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSA/IG1lbWJlci5uYW1lLnRleHQgOiAnJztcblx0XHRcdFx0aWYgKG5hbWUpIHtcblx0XHRcdFx0XHQvLyBJZiBubyBleHBsaWNpdCB0eXBlIGJ1dCBoYXMgaW5pdGlhbGl6ZXIsIGluZmVyIGZyb20gaW5pdGlhbGl6ZXJcblx0XHRcdFx0XHRsZXQgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRpZiAodHlwZSA9PT0gJ3Vua25vd24nICYmIG1lbWJlci5pbml0aWFsaXplcikge1xuXHRcdFx0XHRcdFx0dHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKG1lbWJlci5pbml0aWFsaXplcik7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdC8vIEhhbmRsZSBtZXRob2QgZGVjbGFyYXRpb25zXG5cdFx0XHRpZiAodHMuaXNNZXRob2REZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgbWV0aG9kc1xuXHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0ICAgICBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZCk7XG5cdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyTWV0aG9kVHlwZShtZW1iZXIpO1xuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBIYW5kbGUgZ2V0dGVyIGRlY2xhcmF0aW9uc1xuXHRcdFx0aWYgKHRzLmlzR2V0QWNjZXNzb3IobWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIGdldHRlcnNcblx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdCAgICAgbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQpO1xuXHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHQvLyBGaXJzdCB0cnkgZXhwbGljaXQgdHlwZSBhbm5vdGF0aW9uLCB0aGVuIGluZmVyIGZyb20gZ2V0dGVyIGJvZHlcblx0XHRcdFx0bGV0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdGlmICh0eXBlID09PSAndW5rbm93bicgJiYgbWVtYmVyLmJvZHkpIHtcblx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclJldHVyblR5cGVGcm9tQm9keShtZW1iZXIuYm9keSk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdHJlYWRvbmx5IDogdHJ1ZSxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBjbGFzcyBwcm9wZXJ0eSB0eXBlcyBmb3IgbWV0aG9kIHJldHVybiB0eXBlIGluZmVyZW5jZVxuXHQgKiBNYXBzIHByb3BlcnR5IG5hbWVzIHRvIHRoZWlyIFR5cGVTY3JpcHQgdHlwZSBzdHJpbmdzXG5cdCAqIE5vdGU6IEluY2x1ZGVzIHByaXZhdGUvcHJvdGVjdGVkIHByb3BlcnRpZXMgZm9yIG1ldGhvZCBpbmZlcmVuY2Vcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENsYXNzUHJvcGVydHlUeXBlcyAoY2xhc3NEZWNsOiB0cy5DbGFzc0V4cHJlc3Npb24pOiBNYXA8c3RyaW5nLCBzdHJpbmc+IHtcblx0XHRjb25zdCBwcm9wZXJ0eVR5cGVzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblxuXHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGNsYXNzRGVjbC5tZW1iZXJzKSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eURlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHQvLyBJbmNsdWRlIEFMTCBwcm9wZXJ0aWVzIChldmVuIHByaXZhdGUpIGZvciBtZXRob2QgcmV0dXJuIHR5cGUgaW5mZXJlbmNlXG5cdFx0XHRcdC8vIFRoZSB2aXNpYmlsaXR5IGNoZWNrIGlzIGRvbmUgd2hlbiBhZGRpbmcgdG8gb3V0cHV0IHByb3BlcnRpZXNcblx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdGlmIChtZW1iZXIudHlwZSkge1xuXHRcdFx0XHRcdHByb3BlcnR5VHlwZXMuc2V0KG5hbWUsIHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydHlUeXBlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBJbmZlciBtZXRob2QgdHlwZSBmcm9tIG1ldGhvZCBkZWNsYXJhdGlvblxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlck1ldGhvZFR5cGUgKG1ldGhvZDogdHMuTWV0aG9kRGVjbGFyYXRpb24sIGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz4pOiBzdHJpbmcge1xuXHRcdGNvbnN0IHBhcmFtcyA9IG1ldGhvZC5wYXJhbWV0ZXJzLm1hcChwYXJhbSA9PiB7XG5cdFx0XHRjb25zdCBwYXJhbU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgPyBwYXJhbS5uYW1lLnRleHQgOiAnYXJnJztcblx0XHRcdGNvbnN0IHBhcmFtVHlwZSA9IHRoaXMuaW5mZXJUeXBlKHBhcmFtLnR5cGUpO1xuXHRcdFx0cmV0dXJuIGAke3BhcmFtTmFtZX06ICR7cGFyYW1UeXBlfWA7XG5cdFx0fSkuam9pbignLCAnKTtcblxuXHRcdGNvbnN0IHJldHVyblR5cGUgPSB0aGlzLmluZmVyUmV0dXJuVHlwZShtZXRob2QsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cblx0XHRpZiAocGFyYW1zKSB7XG5cdFx0XHRyZXR1cm4gYCgke3BhcmFtc30pID0+ICR7cmV0dXJuVHlwZX1gO1xuXHRcdH1cblx0XHRyZXR1cm4gYCgpID0+ICR7cmV0dXJuVHlwZX1gO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBgdGhpc2AgcGFyYW1ldGVyIHR5cGUgYW5ub3RhdGlvblxuXHRcdCogSGFuZGxlcyBwYXR0ZXJucyBsaWtlOiBmdW5jdGlvbih0aGlzOiBTb21lVHlwZSwgZGF0YTogU29tZVR5cGUpIHsgfVxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdFRoaXNQYXJhbVByb3BlcnRpZXMgKGhhbmRsZXJBcmc6IHRzLkZ1bmN0aW9uRXhwcmVzc2lvbiB8IHRzLkFycm93RnVuY3Rpb24pOlxuXHRcdE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Ly8gRmluZCB0aGUgYHRoaXNgIHBhcmFtZXRlciAoaWYgYW55KVxuXHRcdGZvciAoY29uc3QgcGFyYW0gb2YgaGFuZGxlckFyZy5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRpZiAocGFyYW0ubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgJiYgcGFyYW0ubmFtZS50ZXh0ID09PSAndGhpcycgJiYgcGFyYW0udHlwZSkge1xuXHRcdFx0XHQvLyBDaGVjayBpZiBpdCdzIGEgdHlwZSByZWZlcmVuY2UgKGUuZy4sIGB0aGlzOiB1c2FnZWApXG5cdFx0XHRcdGlmICh0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHBhcmFtLnR5cGUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSlcblx0XHRcdFx0XHRcdD8gcGFyYW0udHlwZS50eXBlTmFtZS50ZXh0XG5cdFx0XHRcdFx0XHQ6ICcnO1xuXG5cdFx0XHRcdFx0Ly8gUmVzb2x2ZSB0aHJvdWdoIHRoZSByZWZlcmVuY2luZyBmaWxlJ3Mgb3duIGltcG9ydHMgZmlyc3QgKEYxMClcblx0XHRcdFx0XHRjb25zdCBkZWNsID0gdHlwZU5hbWVcblx0XHRcdFx0XHRcdD8gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbih0eXBlTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKVxuXHRcdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cdFx0XHRcdFx0aWYgKGRlY2wpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGRlY2xQcm9wZXJ0aWVzID0gdGhpcy5yZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzKGRlY2wpO1xuXHRcdFx0XHRcdFx0Zm9yIChjb25zdCBbIHByb3BOYW1lLCBpbmZvIF0gb2YgZGVjbFByb3BlcnRpZXMpIHtcblx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQocHJvcE5hbWUsIGluZm8pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBDaGVjayBpZiBpdCdzIGRpcmVjdGx5IGFuIGlubGluZSB0eXBlIGxpdGVyYWwgKGUuZy4sIGB0aGlzOiB7IGlkOiBzdHJpbmcgfWApXG5cdFx0XHRcdGVsc2UgaWYgKHRzLmlzVHlwZUxpdGVyYWxOb2RlKHBhcmFtLnR5cGUpKSB7XG5cdFx0XHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgcGFyYW0udHlwZS5tZW1iZXJzKSB7XG5cdFx0XHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChwcm9wTmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdG5hbWUgICAgIDogcHJvcE5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBGb3VuZCB0aGUgYHRoaXNgIHBhcmFtZXRlciwgbm8gbmVlZCB0byBjb250aW51ZVxuXHRcdFx0XHRicmVhaztcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdC8qKlxuXHRcdCogSW5mZXIgVHlwZVNjcmlwdCB0eXBlIGZyb20gdHlwZSBub2RlXG5cdFx0Ki9cblx0LyoqXG5cdCAqIEluZmVyIFR5cGVTY3JpcHQgdHlwZSBmcm9tIHR5cGUgbm9kZVxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlclR5cGUgKHR5cGVOb2RlPzogdHMuVHlwZU5vZGUpOiBzdHJpbmcge1xuXHRcdGlmICghdHlwZU5vZGUpIHtcblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXG5cdFx0c3dpdGNoICh0eXBlTm9kZS5raW5kKSB7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlN0cmluZ0tleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bWJlcktleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkJvb2xlYW5LZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5kZWZpbmVkS2V5d29yZDpcblx0XHRcdHJldHVybiAndW5kZWZpbmVkJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bGwnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5BbnlLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdhbnknO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Vbmtub3duS2V5d29yZDpcblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlZvaWRLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICd2b2lkJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQXJyYXlUeXBlOlxuXHRcdFx0cmV0dXJuIGBBcnJheTwkeyAgdGhpcy5pbmZlclR5cGUoKHR5cGVOb2RlIGFzIHRzLkFycmF5VHlwZU5vZGUpLmVsZW1lbnRUeXBlKSAgfT5gO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlTGl0ZXJhbDoge1xuXHRcdFx0Ly8gSW5saW5lLWV4cGFuZCB0eXBlIGxpdGVyYWxzIGluc3RlYWQgb2YgY29sbGFwc2luZyB0byAnb2JqZWN0J1xuXHRcdFx0Y29uc3QgdHlwZUxpdCA9IHR5cGVOb2RlIGFzIHRzLlR5cGVMaXRlcmFsTm9kZTtcblx0XHRcdGNvbnN0IHByb3BzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgdHlwZUxpdC5tZW1iZXJzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRjb25zdCBvcHRpb25hbCA9IG1lbWJlci5xdWVzdGlvblRva2VuID8gJz8nIDogJyc7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRwcm9wcy5wdXNoKGAke3Byb3BOYW1lfSR7b3B0aW9uYWx9OiAke3R5cGV9YCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiBgeyAke3Byb3BzLmpvaW4oJzsgJyl9IH1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTGl0ZXJhbFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBzdHJpbmcgbGl0ZXJhbCB0eXBlcyBsaWtlICd1c2VyJywgJ2FkbWluJywgZXRjLlxuXHRcdFx0Y29uc3QgeyBsaXRlcmFsIH0gPSAodHlwZU5vZGUgYXMgdHMuTGl0ZXJhbFR5cGVOb2RlKTtcblx0XHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwobGl0ZXJhbCkpIHtcblx0XHRcdFx0Ly8gUmV0dXJuIHRoZSBhY3R1YWwgbGl0ZXJhbCB2YWx1ZSAoZS5nLiwgJ3VzZXInIGluc3RlYWQgb2Ygc3RyaW5nKVxuXHRcdFx0XHRyZXR1cm4gYCcke2xpdGVyYWwudGV4dH0nYDtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc051bWVyaWNMaXRlcmFsKGxpdGVyYWwpKSB7XG5cdFx0XHRcdHJldHVybiBsaXRlcmFsLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAobGl0ZXJhbC5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdHJldHVybiAndHJ1ZSc7XG5cdFx0XHR9XG5cdFx0XHRpZiAobGl0ZXJhbC5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRyZXR1cm4gJ2ZhbHNlJztcblx0XHRcdH1cblx0XHRcdGlmIChsaXRlcmFsLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQpIHtcblx0XHRcdFx0cmV0dXJuICdudWxsJztcblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlUmVmZXJlbmNlOiB7XG5cdFx0XHQvLyBIYW5kbGUgdHlwZSByZWZlcmVuY2VzIGxpa2UgTWFwPHN0cmluZywgbnVtYmVyPiwgUHJvcGVydHlJbmZvLCBldGMuXG5cdFx0XHRjb25zdCB0eXBlUmVmID0gdHlwZU5vZGUgYXMgdHMuVHlwZVJlZmVyZW5jZU5vZGU7XG5cblx0XHRcdC8vIFF1YWxpZmllZCBuYW1lcyAoTmFtZXNwYWNlLlR5cGUpOiByZXNvbHZlIHRocm91Z2ggbmFtZXNwYWNlIGltcG9ydHNcblx0XHRcdGlmICh0cy5pc1F1YWxpZmllZE5hbWUodHlwZVJlZi50eXBlTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcmVzb2x2ZWRRdWFsaWZpZWQgPSB0aGlzLmluZmVyUXVhbGlmaWVkVHlwZVJlZmVyZW5jZSh0eXBlUmVmKTtcblx0XHRcdFx0aWYgKHJlc29sdmVkUXVhbGlmaWVkICE9PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0XHRyZXR1cm4gcmVzb2x2ZWRRdWFsaWZpZWQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gdW5yZXNvbHZlZCBxdWFsaWZpZWQgcmVmZXJlbmNlcyBtdXN0IG5vdCBsZWFrIGEgYmFyZSBuYW1lXG5cdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHR9XG5cblx0XHRcdGNvbnN0IHR5cGVOYW1lID0gdHMuaXNJZGVudGlmaWVyKHR5cGVSZWYudHlwZU5hbWUpID8gdHlwZVJlZi50eXBlTmFtZS50ZXh0IDogJ3Vua25vd24nO1xuXG5cdFx0XHQvLyBJbXBvcnQtYXdhcmUgcmVmZXJlbmNlZC10eXBlIHJlc29sdXRpb24gKEYxMCk6IGEgZGVjbGFyYXRpb25cblx0XHRcdC8vIHJlYWNoZWQgdGhyb3VnaCB0aGUgY3VycmVudCBmaWxlJ3Mgb3duIGltcG9ydHMgKG9yIGl0cyBsb2NhbHMsXG5cdFx0XHQvLyBvciBhIHVuaXF1ZSBwcm9ncmFtLXdpZGUgZGVjbGFyYXRpb24pIGV4cGFuZHMgaW5saW5lXG5cdFx0XHRjb25zdCBzaW1wbGVSZWYgPSB0aGlzLnJlc29sdmVTaW1wbGVUeXBlUmVmZXJlbmNlKHR5cGVOYW1lLCB0eXBlUmVmLnR5cGVBcmd1bWVudHMsIHR5cGVSZWYpO1xuXHRcdFx0aWYgKHNpbXBsZVJlZiAhPT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdHJldHVybiBzaW1wbGVSZWY7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEJ1aWxkIGdlbmVyaWMgdHlwZSBhcmd1bWVudHNcblx0XHRcdGNvbnN0IHR5cGVBcmdzID0gKHR5cGVSZWYudHlwZUFyZ3VtZW50cyA/PyBbXSkubWFwKGFyZyA9PiB0aGlzLmluZmVyVHlwZShhcmcpKTtcblx0XHRcdHJldHVybiBgJHt0eXBlTmFtZX08JHt0eXBlQXJncy5qb2luKCcsICcpfT5gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5pb25UeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgdW5pb24gdHlwZXMgbGlrZSAnYScgfCAnYicgfCAnYydcblx0XHRcdGNvbnN0IHVuaW9uVHlwZSA9IHR5cGVOb2RlIGFzIHRzLlVuaW9uVHlwZU5vZGU7XG5cdFx0XHRjb25zdCB0eXBlcyA9IHVuaW9uVHlwZS50eXBlcy5tYXAodCA9PiB0aGlzLmluZmVyVHlwZSh0KSk7XG5cdFx0XHRyZXR1cm4gdHlwZXMuam9pbignIHwgJyk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5JbnRlcnNlY3Rpb25UeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgaW50ZXJzZWN0aW9uIHR5cGVzIGxpa2UgVHlwZUEgJiBUeXBlQlxuXHRcdFx0Y29uc3QgaW50ZXJzZWN0aW9uVHlwZSA9IHR5cGVOb2RlIGFzIHRzLkludGVyc2VjdGlvblR5cGVOb2RlO1xuXHRcdFx0Y29uc3QgdHlwZXMgPSBpbnRlcnNlY3Rpb25UeXBlLnR5cGVzLm1hcCh0ID0+IHRoaXMuaW5mZXJUeXBlKHQpKTtcblx0XHRcdHJldHVybiB0eXBlcy5qb2luKCcgJiAnKTtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR1cGxlVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHR1cGxlIHR5cGVzIGxpa2UgW3N0cmluZywgbnVtYmVyXVxuXHRcdFx0Y29uc3QgdHVwbGVUeXBlID0gdHlwZU5vZGUgYXMgdHMuVHVwbGVUeXBlTm9kZTtcblx0XHRcdGNvbnN0IGVsZW1lbnRzID0gdHVwbGVUeXBlLmVsZW1lbnRzLm1hcChlbGVtID0+IHRoaXMuaW5mZXJUeXBlKGVsZW0gYXMgdHMuVHlwZU5vZGUpKTtcblx0XHRcdHJldHVybiBgWyR7ZWxlbWVudHMuam9pbignLCAnKX1dYDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk9wdGlvbmFsVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIG9wdGlvbmFsIGVsZW1lbnQgaW4gdHVwbGU6IHN0cmluZz9cblx0XHRcdGNvbnN0IG9wdGlvbmFsVHlwZSA9IHR5cGVOb2RlIGFzIHRzLk9wdGlvbmFsVHlwZU5vZGU7XG5cdFx0XHRyZXR1cm4gYCR7dGhpcy5pbmZlclR5cGUob3B0aW9uYWxUeXBlLnR5cGUpICB9P2A7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5SZXN0VHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHJlc3QgZWxlbWVudDogLi4uVFxuXHRcdFx0Y29uc3QgcmVzdFR5cGUgPSB0eXBlTm9kZSBhcyB0cy5SZXN0VHlwZU5vZGU7XG5cdFx0XHRyZXR1cm4gYC4uLiR7ICB0aGlzLmluZmVyVHlwZShyZXN0VHlwZS50eXBlKX1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuUGFyZW50aGVzaXplZFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBwYXJlbnRoZXNpemVkIHR5cGVzOiAoQSB8IEIpXG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclR5cGUoKHR5cGVOb2RlIGFzIHRzLlBhcmVudGhlc2l6ZWRUeXBlTm9kZSkudHlwZSk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5JbmRleGVkQWNjZXNzVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIGluZGV4ZWQgYWNjZXNzOiBUW0tdXG5cdFx0XHRjb25zdCBpbmRleGVkID0gdHlwZU5vZGUgYXMgdHMuSW5kZXhlZEFjY2Vzc1R5cGVOb2RlO1xuXHRcdFx0Ly8gYHR5cGVvZiBjb25zdEFycmF5W0tdYCDigJQgZWxlbWVudCB0eXBlIG9mIGEgdHJhY2tlZCBjb25zdCBhcnJheTpcblx0XHRcdC8vIGVtaXQgdGhlIGVsZW1lbnQgbGl0ZXJhbCB1bmlvbiBkaXJlY3RseSAoYXNzZW1ibGluZ1xuXHRcdFx0Ly8gYHVuaW9uW0tdYCB0ZXh0IHdvdWxkIG1pc3JlYWQgcHJlY2VkZW5jZSwgYW5kIHdoZW4gdGhlIGNvbnN0XG5cdFx0XHQvLyBpcyBub3Qgc3RhdGljYWxseSB2aXNpYmxlIHRoZSBob25lc3QgYW5zd2VyIGlzIGB1bmtub3duYCxcblx0XHRcdC8vIG5ldmVyIGEgYmFyZSBgdHlwZW9mIG5hbWVgIHF1ZXJ5KVxuXHRcdFx0aWYgKHRzLmlzVHlwZVF1ZXJ5Tm9kZShpbmRleGVkLm9iamVjdFR5cGUpICYmIHRzLmlzSWRlbnRpZmllcihpbmRleGVkLm9iamVjdFR5cGUuZXhwck5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHF1ZXJ5TmFtZSA9IGluZGV4ZWQub2JqZWN0VHlwZS5leHByTmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBhcnJheUxpdGVyYWwgPSB0aGlzLmZpbmRSZWZlcmVuY2VkQ29uc3RBcnJheShxdWVyeU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRcdGNvbnN0IGxpdGVyYWxzID0gYXJyYXlMaXRlcmFsID8gdGhpcy5saXRlcmFsVHlwZXNPZkFycmF5KGFycmF5TGl0ZXJhbCkgOiB1bmRlZmluZWQ7XG5cdFx0XHRcdGlmICghbGl0ZXJhbHMpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmICh0cy5pc0xpdGVyYWxUeXBlTm9kZShpbmRleGVkLmluZGV4VHlwZSkgJiYgdHMuaXNOdW1lcmljTGl0ZXJhbChpbmRleGVkLmluZGV4VHlwZS5saXRlcmFsKSkge1xuXHRcdFx0XHRcdGNvbnN0IGVsZW1lbnRJbmRleCA9IHBhcnNlSW50KGluZGV4ZWQuaW5kZXhUeXBlLmxpdGVyYWwudGV4dCwgMTApO1xuXHRcdFx0XHRcdGNvbnN0IGVsZW1lbnQgPSBsaXRlcmFsc1sgZWxlbWVudEluZGV4IF07XG5cdFx0XHRcdFx0Y29uc3QgZWxlbWVudFJlc3VsdCA9IGVsZW1lbnQgPT09IHVuZGVmaW5lZCA/ICd1bmtub3duJyA6IGVsZW1lbnQ7XG5cdFx0XHRcdFx0cmV0dXJuIGVsZW1lbnRSZXN1bHQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgdW5pb25SZXN1bHQgPSBsaXRlcmFscy5qb2luKCcgfCAnKTtcblx0XHRcdFx0cmV0dXJuIHVuaW9uUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0bGV0IG9iamVjdFR5cGUgPSB0aGlzLmluZmVyVHlwZShpbmRleGVkLm9iamVjdFR5cGUpO1xuXHRcdFx0Y29uc3QgaW5kZXhUeXBlID0gdGhpcy5pbmZlclR5cGUoaW5kZXhlZC5pbmRleFR5cGUpO1xuXHRcdFx0Ly8gSWYgb2JqZWN0VHlwZSBpcyAnb2JqZWN0JywgdHJ5IHRvIHJlc29sdmUgdGhlIHVuZGVybHlpbmcgcmVmZXJlbmNlZCB0eXBlXG5cdFx0XHRpZiAob2JqZWN0VHlwZSA9PT0gJ29iamVjdCcgJiYgdHMuaXNUeXBlUmVmZXJlbmNlTm9kZShpbmRleGVkLm9iamVjdFR5cGUpKSB7XG5cdFx0XHRcdGNvbnN0IHJlZk5hbWUgPSB0cy5pc0lkZW50aWZpZXIoaW5kZXhlZC5vYmplY3RUeXBlLnR5cGVOYW1lKSA/IGluZGV4ZWQub2JqZWN0VHlwZS50eXBlTmFtZS50ZXh0IDogJyc7XG5cdFx0XHRcdGlmIChyZWZOYW1lKSB7XG5cdFx0XHRcdFx0Y29uc3QgZGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24ocmVmTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdFx0XHRpZiAoZGVjbCkge1xuXHRcdFx0XHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oZGVjbCk7XG5cdFx0XHRcdFx0XHRpZiAoZXhwYW5kZWQpIHtcblx0XHRcdFx0XHRcdFx0b2JqZWN0VHlwZSA9IGV4cGFuZGVkO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGAke29iamVjdFR5cGV9WyR7aW5kZXhUeXBlfV1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZU9wZXJhdG9yOiB7XG5cdFx0XHQvLyBIYW5kbGUga2V5b2YsIHJlYWRvbmx5LCB1bmlxdWUgb3BlcmF0b3JzXG5cdFx0XHRjb25zdCB0eXBlT3AgPSB0eXBlTm9kZSBhcyB0cy5UeXBlT3BlcmF0b3JOb2RlO1xuXHRcdFx0Y29uc3Qgb3BlcmF0b3IgPSB0cy5TeW50YXhLaW5kWyB0eXBlT3Aub3BlcmF0b3IgXTtcblx0XHRcdHJldHVybiBgJHtvcGVyYXRvcn0gJHt0aGlzLmluZmVyVHlwZSh0eXBlT3AudHlwZSl9YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR5cGVRdWVyeToge1xuXHRcdFx0Ly8gYHR5cGVvZiB4YCBhcyBhIEZJRUxEIFRZUEU6IHRoZSBnZW5lcmF0ZWQgZmlsZSBoYXMgbm8gaW1wb3J0cyxcblx0XHRcdC8vIHNvIGEgYmFyZSBgdHlwZW9mIHhgIHdvdWxkIGJlIGFuIHVucmVzb2x2YWJsZSBuYW1lIGRvd25zdHJlYW0uXG5cdFx0XHQvLyBXaGVuIHggaXMgYSB0cmFja2VkIGNvbnN0IGFycmF5LCBlbWl0IGl0cyBlbGVtZW50IGxpdGVyYWxcblx0XHRcdC8vIHVuaW9uOyBvdGhlcndpc2UgZGVncmFkZSB0byBgdW5rbm93bmAuIChJbnN0YW5jZVR5cGU8dHlwZW9mIFg+XG5cdFx0XHQvLyBncmFwaCB0eXBlcyBhcmUgaGFuZGxlZCBpbiByZXNvbHZlU2ltcGxlVHlwZVJlZmVyZW5jZSBiZWZvcmVcblx0XHRcdC8vIGluZmVyVHlwZSBydW5zLilcblx0XHRcdGNvbnN0IHR5cGVRdWVyeSA9IHR5cGVOb2RlIGFzIHRzLlR5cGVRdWVyeU5vZGU7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKHR5cGVRdWVyeS5leHByTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgdW5pb24gPSB0aGlzLnR5cGVPZkNvbnN0QXJyYXlVbmlvbih0eXBlUXVlcnkuZXhwck5hbWUudGV4dCwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdFx0aWYgKHVuaW9uKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHVuaW9uO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRkZWZhdWx0OlxuXHRcdFx0Ly8gRm9yIGNvbXBsZXggdHlwZXMsIHJldHVybiB0aGUgdGV4dCByZXByZXNlbnRhdGlvblxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHQqIEluZmVyIHJldHVybiB0eXBlIGZyb20gYSBtZXRob2QgZGVjbGFyYXRpb25cblx0XHQqIFVzZXMgZXhwbGljaXQgcmV0dXJuIHR5cGUgYW5ub3RhdGlvbiBvciBpbmZlcnMgZnJvbSByZXR1cm4gc3RhdGVtZW50c1xuXHRcdCovXG5cdHByaXZhdGUgaW5mZXJSZXR1cm5UeXBlIChtZXRob2Q6IHRzLk1ldGhvZERlY2xhcmF0aW9uLCBjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+KTogc3RyaW5nIHtcblx0XHQvLyBJZiBtZXRob2QgaGFzIGV4cGxpY2l0IHJldHVybiB0eXBlIGFubm90YXRpb24sIHVzZSBpdFxuXHRcdGlmIChtZXRob2QudHlwZSkge1xuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJUeXBlKG1ldGhvZC50eXBlKTtcblx0XHR9XG5cblx0XHQvLyBPdGhlcndpc2UsIHRyeSB0byBpbmZlciBmcm9tIHJldHVybiBzdGF0ZW1lbnRzIGluIHRoZSBtZXRob2QgYm9keVxuXHRcdGlmIChtZXRob2QuYm9keSkge1xuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJSZXR1cm5UeXBlRnJvbUJvZHkobWV0aG9kLmJvZHksIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0fVxuXG5cdFx0cmV0dXJuICd1bmtub3duJztcblx0fVxuXG5cdC8qKlxuXHRcdCogSW5mZXIgcmV0dXJuIHR5cGUgYnkgYW5hbHl6aW5nIHJldHVybiBzdGF0ZW1lbnRzIGluIHRoZSBtZXRob2QgYm9keVxuXHRcdCovXG5cdHByaXZhdGUgaW5mZXJSZXR1cm5UeXBlRnJvbUJvZHkgKGJvZHk6IHRzLkJsb2NrLCBjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+KTogc3RyaW5nIHtcblx0XHRjb25zdCByZXR1cm5UeXBlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXG5cdFx0Y29uc3QgdmlzaXQgPSAobm9kZTogdHMuTm9kZSk6IHZvaWQgPT4ge1xuXHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIobm9kZS5leHByZXNzaW9uLCB1bmRlZmluZWQsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdGlmICh0eXBlICE9PSAndW5rbm93bicpIHtcblx0XHRcdFx0XHRyZXR1cm5UeXBlcy5hZGQodHlwZSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCB2aXNpdCk7XG5cdFx0fTtcblxuXHRcdHZpc2l0KGJvZHkpO1xuXG5cdFx0aWYgKHJldHVyblR5cGVzLnNpemUgPT09IDApIHtcblx0XHRcdHJldHVybiAndm9pZCc7XG5cdFx0fVxuXHRcdGlmIChyZXR1cm5UeXBlcy5zaXplID09PSAxKSB7XG5cdFx0XHRyZXR1cm4gQXJyYXkuZnJvbShyZXR1cm5UeXBlcylbIDAgXTtcblx0XHR9XG5cdFx0cmV0dXJuIEFycmF5LmZyb20ocmV0dXJuVHlwZXMpLmpvaW4oJyB8ICcpO1xuXHR9XG5cblx0LyoqXG5cdCAqIEluZmVyIHR5cGUgZnJvbSBpbml0aWFsaXplclxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIgKFxuXHRcdGluaXRpYWxpemVyOiB0cy5FeHByZXNzaW9uLFxuXHRcdGRhdGFUeXBlTWFwPzogTWFwPHN0cmluZywgc3RyaW5nPixcblx0XHRjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+XG5cdCk6IHN0cmluZyB7XG5cdFx0c3dpdGNoIChpbml0aWFsaXplci5raW5kKSB7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlN0cmluZ0xpdGVyYWw6XG5cdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bWVyaWNMaXRlcmFsOlxuXHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZDpcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bGwnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5VbmRlZmluZWRLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICd1bmRlZmluZWQnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5BcnJheUxpdGVyYWxFeHByZXNzaW9uOlxuXHRcdFx0cmV0dXJuICdBcnJheTx1bmtub3duPic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk9iamVjdExpdGVyYWxFeHByZXNzaW9uOlxuXHRcdFx0cmV0dXJuICdvYmplY3QnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OZXdFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgbmV3IERhdGUoKSwgbmV3IE1hcCgpLCBldGMuXG5cdFx0XHRjb25zdCBuZXdFeHByID0gaW5pdGlhbGl6ZXIgYXMgdHMuTmV3RXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIobmV3RXhwci5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRyZXR1cm4gbmV3RXhwci5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ29iamVjdCc7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5CaW5hcnlFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgYXJpdGhtZXRpYyBvcGVyYXRpb25zOiBhICogYiwgYSArIGIsIGEgLSBiLCBhIC8gYlxuXHRcdFx0Y29uc3QgYmluYXJ5RXhwciA9IGluaXRpYWxpemVyIGFzIHRzLkJpbmFyeUV4cHJlc3Npb247XG5cdFx0XHRjb25zdCBsZWZ0VHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKGJpbmFyeUV4cHIubGVmdCwgZGF0YVR5cGVNYXAsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRjb25zdCByaWdodFR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihiaW5hcnlFeHByLnJpZ2h0LCBkYXRhVHlwZU1hcCwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0XG5cdFx0XHQvLyBDaGVjayBpZiBpdCdzIGFuIGFyaXRobWV0aWMgb3BlcmF0b3Jcblx0XHRcdGNvbnN0IG9wZXJhdG9yID0gYmluYXJ5RXhwci5vcGVyYXRvclRva2VuLmtpbmQ7XG5cdFx0XHRpZiAob3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuQXN0ZXJpc2tUb2tlbiB8fFxuXHRcdFx0XHQgICAgb3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuU2xhc2hUb2tlbiB8fFxuXHRcdFx0XHQgICAgb3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuTWludXNUb2tlbiB8fFxuXHRcdFx0XHQgICAgb3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuUGVyY2VudFRva2VuKSB7XG5cdFx0XHRcdC8vIEFyaXRobWV0aWMgb3BlcmF0aW9ucyBvbiBudW1iZXJzIHByb2R1Y2UgbnVtYmVyc1xuXHRcdFx0XHRpZiAoKGxlZnRUeXBlID09PSAnbnVtYmVyJyB8fCBsZWZ0VHlwZSA9PT0gJ3Vua25vd24nKSAmJlxuXHRcdFx0XHRcdCAgICAocmlnaHRUeXBlID09PSAnbnVtYmVyJyB8fCByaWdodFR5cGUgPT09ICd1bmtub3duJykpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGlmIChvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5QbHVzVG9rZW4pIHtcblx0XHRcdFx0Ly8gUGx1cyBjYW4gYmUgYWRkaXRpb24gb3Igc3RyaW5nIGNvbmNhdGVuYXRpb25cblx0XHRcdFx0aWYgKGxlZnRUeXBlID09PSAnc3RyaW5nJyB8fCByaWdodFR5cGUgPT09ICdzdHJpbmcnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChsZWZ0VHlwZSA9PT0gJ251bWJlcicgJiYgcmlnaHRUeXBlID09PSAnbnVtYmVyJykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gSGFuZGxlIHByb3BlcnR5IGFjY2VzcyBsaWtlIGRhdGEudmFsdWUsIGRhdGEuaWRcblx0XHRcdGlmIChkYXRhVHlwZU1hcCkge1xuXHRcdFx0XHRjb25zdCBhY2Nlc3NDaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihpbml0aWFsaXplcik7XG5cdFx0XHRcdGlmIChhY2Nlc3NDaGFpbikge1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSBkYXRhVHlwZU1hcC5nZXQoYWNjZXNzQ2hhaW4pO1xuXHRcdFx0XHRcdGlmICh0eXBlKSB7XG5cdFx0XHRcdFx0XHRyZXR1cm4gdHlwZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIEhhbmRsZSB0aGlzLm1hcC5zaXplIHBhdHRlcm4gKE1hcC5zaXplIHJldHVybnMgbnVtYmVyKVxuXHRcdFx0Y29uc3QgcHJvcEFjY2VzcyA9IGluaXRpYWxpemVyIGFzIHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihwcm9wQWNjZXNzLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IG91dGVyUHJvcCA9IHByb3BBY2Nlc3MuZXhwcmVzc2lvbjtcblx0XHRcdFx0Ly8gQ2hlY2sgZm9yIHRoaXMubWFwIHBhdHRlcm5cblx0XHRcdFx0bGV0IGlubmVyTmFtZSA9ICcnO1xuXHRcdFx0XHRpZiAob3V0ZXJQcm9wLmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdGlubmVyTmFtZSA9ICd0aGlzJztcblx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc0lkZW50aWZpZXIob3V0ZXJQcm9wLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0aW5uZXJOYW1lID0gb3V0ZXJQcm9wLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBtYXBQcm9wID0gb3V0ZXJQcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgZmluYWxQcm9wID0gcHJvcEFjY2Vzcy5uYW1lLnRleHQ7XG5cdFx0XHRcdC8vIHRoaXMubWFwLnNpemUgLT4gbnVtYmVyXG5cdFx0XHRcdGlmIChpbm5lck5hbWUgPT09ICd0aGlzJyAmJiBtYXBQcm9wID09PSAnbWFwJyAmJiBmaW5hbFByb3AgPT09ICdzaXplJykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLklkZW50aWZpZXI6IHtcblx0XHRcdC8vIEhhbmRsZSBpZGVudGlmaWVyIHJlZmVyZW5jZXMgaWYgaW4gZGF0YVR5cGVNYXBcblx0XHRcdGlmIChkYXRhVHlwZU1hcCkge1xuXHRcdFx0XHRjb25zdCBuYW1lID0gKGluaXRpYWxpemVyIGFzIHRzLklkZW50aWZpZXIpLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHR5cGUgPSBkYXRhVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0XHRcdGlmICh0eXBlKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHR5cGU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5DYWxsRXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gSGFuZGxlIGZ1bmN0aW9uIGNhbGxzIGxpa2UgRGF0ZS5ub3coKSwgcGFyc2VJbnQoKSwgZXRjLlxuXHRcdFx0Y29uc3QgY2FsbEV4cHIgPSBpbml0aWFsaXplciBhcyB0cy5DYWxsRXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsRXhwci5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBtZXRob2ROYW1lID0gY2FsbEV4cHIuZXhwcmVzc2lvbi5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IG9iak5hbWUgPSB0cy5pc0lkZW50aWZpZXIoY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uKVxuXHRcdFx0XHRcdD8gY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uLnRleHRcblx0XHRcdFx0XHQ6ICcnO1xuXHRcdFx0XHRcdFxuXHRcdFx0XHQvLyBEYXRlLm5vdygpIC0+IG51bWJlclxuXHRcdFx0XHRpZiAob2JqTmFtZSA9PT0gJ0RhdGUnICYmIG1ldGhvZE5hbWUgPT09ICdub3cnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIFN0cmluZyBtZXRob2RzIHRoYXQgcmV0dXJuIHN0cmluZ1xuXHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3RvU3RyaW5nJyB8fCBtZXRob2ROYW1lID09PSAndmFsdWVPZicpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gSGFuZGxlIE1hcCBwcm9wZXJ0eSBhY2Nlc3Mgb24gY2xhc3MgaW5zdGFuY2VzICh0aGlzLm1hcC4qKVxuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdGNvbnN0IG91dGVyUHJvcCA9IGNhbGxFeHByLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdFx0XHQvLyBIYW5kbGUgYm90aCAndGhpcycga2V5d29yZCBhbmQgaWRlbnRpZmllciBwYXR0ZXJuc1xuXHRcdFx0XHRcdGxldCBpbm5lck5hbWUgPSAnJztcblx0XHRcdFx0XHRpZiAob3V0ZXJQcm9wLmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdFx0aW5uZXJOYW1lID0gJ3RoaXMnO1xuXHRcdFx0XHRcdH0gZWxzZSBpZiAodHMuaXNJZGVudGlmaWVyKG91dGVyUHJvcC5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdFx0aW5uZXJOYW1lID0gb3V0ZXJQcm9wLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Y29uc3QgbWFwUHJvcCA9IG91dGVyUHJvcC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Ly8gdGhpcy5tYXAuWCgpIHBhdHRlcm5zXG5cdFx0XHRcdFx0aWYgKGlubmVyTmFtZSA9PT0gJ3RoaXMnICYmIG1hcFByb3AgPT09ICdtYXAnKSB7XG5cdFx0XHRcdFx0XHQvLyBUcnkgdG8gZ2V0IHRoZSBNYXAncyB2YWx1ZSB0eXBlIGZyb20gY2xhc3MgcHJvcGVydGllc1xuXHRcdFx0XHRcdFx0bGV0IG1hcFZhbHVlVHlwZSA9ICd1bmtub3duJztcblx0XHRcdFx0XHRcdGlmIChjbGFzc1Byb3BlcnR5VHlwZXMpIHtcblx0XHRcdFx0XHRcdFx0Y29uc3QgbWFwVHlwZSA9IGNsYXNzUHJvcGVydHlUeXBlcy5nZXQoJ21hcCcpO1xuXHRcdFx0XHRcdFx0XHRpZiAobWFwVHlwZSAmJiBtYXBUeXBlLnN0YXJ0c1dpdGgoJ01hcDwnKSkge1xuXHRcdFx0XHRcdFx0XHRcdC8vIFBhcnNlIE1hcDxLLCBWPiB0byBnZXQgVlxuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IG1hdGNoID0gbWFwVHlwZS5tYXRjaCgvTWFwPFteLF0rLFxccyooLispPiQvKTtcblx0XHRcdFx0XHRcdFx0XHRpZiAobWF0Y2gpIHtcblx0XHRcdFx0XHRcdFx0XHRcdFsgLCBtYXBWYWx1ZVR5cGUgXSA9IG1hdGNoO1xuXHRcdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdoYXMnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdzZXQnKSByZXR1cm4gJ3RoaXMnO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdnZXQnKSByZXR1cm4gbWFwVmFsdWVUeXBlO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdkZWxldGUnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdjbGVhcicpIHJldHVybiAndm9pZCc7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3ZhbHVlcycpIHJldHVybiBgSXRlcmFibGVJdGVyYXRvcjwke21hcFZhbHVlVHlwZX0+YDtcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAna2V5cycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjxzdHJpbmc+Jztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZW50cmllcycpIHJldHVybiBgSXRlcmFibGVJdGVyYXRvcjxbc3RyaW5nLCAke21hcFZhbHVlVHlwZX1dPmA7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIERpcmVjdCBtYXAuWCgpIGNhbGxzXG5cdFx0XHRcdGlmIChvYmpOYW1lID09PSAnbWFwJyB8fCBvYmpOYW1lID09PSAnb2JqJykge1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnaGFzJykgcmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3NldCcpIHJldHVybiAndGhpcyc7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdnZXQnKSByZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZGVsZXRlJykgcmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2NsZWFyJykgcmV0dXJuICd2b2lkJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3ZhbHVlcycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjx1bmtub3duPic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdrZXlzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPHN0cmluZz4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZW50cmllcycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjxbc3RyaW5nLCB1bmtub3duXT4nO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBwYXJzZUludCwgcGFyc2VGbG9hdCAtPiBudW1iZXJcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY2FsbEV4cHIuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y29uc3QgZm5OYW1lID0gY2FsbEV4cHIuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHRpZiAoZm5OYW1lID09PSAncGFyc2VJbnQnIHx8IGZuTmFtZSA9PT0gJ3BhcnNlRmxvYXQnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdTdHJpbmcnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdOdW1iZXInKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdCb29sZWFuJykge1xuXHRcdFx0XHRcdHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UZW1wbGF0ZUV4cHJlc3Npb246XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk5vU3Vic3RpdHV0aW9uVGVtcGxhdGVMaXRlcmFsOiB7XG5cdFx0XHQvLyBUZW1wbGF0ZSBsaXRlcmFscyBsaWtlIGAke2Jhc2VWYWx1ZX0tJHtleHRyYX1gIGFsd2F5cyBwcm9kdWNlIHN0cmluZ3Ncblx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHR9XG5cdFx0ZGVmYXVsdDpcblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHR9XG5cdFxuXHQvKipcblx0XHRcdCogQ29sbGVjdCB1c2FnZSBpbmZvcm1hdGlvbiBmb3IgdHlwZSByZWZlcmVuY2VzXG5cdFx0XHQqL1xuXHRwcml2YXRlIGNvbGxlY3RVc2FnZSAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGZvciBuZXcgVHlwZSgpIGluc3RhbnRpYXRpb25cblx0XHRpZiAodHMuaXNOZXdFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0bGV0IHR5cGVOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obm9kZS5leHByZXNzaW9uKSkge1xuXHRcdFx0XHR0eXBlTmFtZSA9IHRoaXMucmVzb2x2ZVR5cGVQYXRoKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHR0eXBlTmFtZSA9IHRoaXMuZ2V0VHlwZU5hbWVGcm9tRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHR5cGVOYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0dGhpcy5hZGRVc2FnZSh0eXBlTmFtZSwge1xuXHRcdFx0XHRcdGxvY2F0aW9uICAgICAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdGtpbmQgICAgICAgICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRjb2RlICAgICAgICAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHQvLyBDb25zdHJ1Y3RvciBleHByZXNzaW9uIHRleHQgKCdUaGluZycsICd1c2VyLkFkbWluRW50aXR5Jyxcblx0XHRcdFx0XHQvLyBhIGxvb2t1cCBhbGlhcykg4oCUIENyZWF0aW9uQW5jaG9yLmNvbnN0cnVjdG9yVGV4dCAoUGhhc2UgMylcblx0XHRcdFx0XHRjb25zdHJ1Y3RvclRleHQgOiBub2RlLmV4cHJlc3Npb24uZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHR9KTtcblx0XHRcdFx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudCBmcm9tIG5ldyBUeXBlKCkgZm9yIGZsb3cgYW5hbHlzaXNcblx0XHRcdFx0dGhpcy50cmFja05ld0Fzc2lnbm1lbnQobm9kZSwgdHlwZU5hbWUpO1xuXHRcdFx0XHQvLyBBbHNvIHJlY29yZCBhcyBmbG93IGV2ZW50XG5cdFx0XHRcdHRoaXMuYWRkRmxvdyh0eXBlTmFtZSwge1xuXHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0a2luZCAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRjb250ZXh0ICA6ICduZXcgZXhwcmVzc2lvbicsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0Ly8gQ2hlY2sgZm9yIHByb3BlcnR5IGFjY2VzcyBvbiBpbnN0YW5jZXMgKHVzZXIuQWRtaW5UeXBlKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRcdC8vIENoZWNrIGlmIHRoaXMgbG9va3MgbGlrZSBhIHR5cGUgYWNjZXNzIHBhdHRlcm5cblx0XHRcdGlmIChwcm9wTmFtZSAmJiB0aGlzLmlzTGlrZWx5VHlwZU5hbWUocHJvcE5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0XHQvLyBUcnkgdG8gcmVzb2x2ZSBmdWxsIHBhdGhcblx0XHRcdFx0Y29uc3QgZnVsbFBhdGggPSB0aGlzLnJlc29sdmVUeXBlUGF0aChub2RlKTtcblx0XHRcdFx0aWYgKGZ1bGxQYXRoKSB7XG5cdFx0XHRcdFx0dGhpcy5hZGRVc2FnZShmdWxsUGF0aCwge1xuXHRcdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRcdGtpbmQgICAgIDogJ3Byb3BlcnR5QWNjZXNzJyxcblx0XHRcdFx0XHRcdGNvZGUgICAgIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFxuXHRcdC8vIENoZWNrIGZvciBsb29rdXAoJ1R5cGVOYW1lJykgb3IgbG9va3VwKHNvdXJjZSwgJ1R5cGVOYW1lJykgY2FsbHNcblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdGNvbnN0IGZ1bmNOYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKTtcblx0XHRcdGlmIChmdW5jTmFtZSA9PT0gJ2xvb2t1cCcgJiYgbm9kZS5hcmd1bWVudHMubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRjb25zdCB0eXBlUGF0aCA9IHRoaXMucmVzb2x2ZUxvb2t1cFBhdGgobm9kZSk7XG5cdFx0XHRcdGlmICh0eXBlUGF0aCkge1xuXHRcdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdFx0KTtcblx0XHRcdFx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0XHRcdHRoaXMuYWRkVXNhZ2UodHlwZVBhdGgsIHtcblx0XHRcdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRcdFx0a2luZCA6ICdsb29rdXAnLFxuXHRcdFx0XHRcdFx0Y29kZSA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnQgZnJvbSBsb29rdXAgZm9yIGluc3RhbnRpYXRpb24gdHJhY2tpbmdcblx0XHRcdFx0XHR0aGlzLnRyYWNrTG9va3VwQXNzaWdubWVudChub2RlLCB0eXBlUGF0aCk7XG5cdFx0XHRcdFx0Ly8gUmVjb3JkIGZvciB0aGUgaGFyZC1mYWlsIGxhdyBldmVuIHdoZW4gYWRkVXNhZ2UgZHJvcHBlZFxuXHRcdFx0XHRcdC8vIHRoZSBwYXRoICh1bmtub3duIHBhdGhzIGFyZSBleGFjdGx5IHRoZSBmYWlsdXJlIGNsYXNzKVxuXHRcdFx0XHRcdHRoaXMubG9va3VwUmVmZXJlbmNlcy5wdXNoKHsgcGF0aCA6IHR5cGVQYXRoLCBsb2NhdGlvbiB9KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIEdldCBmdW5jdGlvbiBuYW1lIGZyb20gZXhwcmVzc2lvbiAoaWRlbnRpZmllciBvciBwcm9wZXJ0eSBhY2Nlc3MpXG5cdFx0XHQqL1xuXHRwcml2YXRlIGdldEZ1bmN0aW9uTmFtZSAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIGV4cHIudGV4dDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gZXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0KiBBZGQgYSB1c2FnZSB0byB0aGUgY29sbGVjdGlvblxuXHRcdFx0Ki9cblx0cHJpdmF0ZSBhZGRVc2FnZSAodHlwZVBhdGg6IHN0cmluZywgdXNhZ2U6IFVzYWdlSW5mbyk6IHZvaWQge1xuXHRcdC8vIE9ubHkgdHJhY2sgdXNhZ2VzIG9mIG1uZW1vbmljYS1kZWZpbmVkIHR5cGVzXG5cdFx0aWYgKCF0aGlzLmRlZmluaXRpb25zLmhhcyh0eXBlUGF0aCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKCF0aGlzLnVzYWdlcy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHR0aGlzLnVzYWdlcy5zZXQodHlwZVBhdGgsIFtdKTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgZHVwbGljYXRlcyBiYXNlZCBvbiBsb2NhdGlvbiwgY29kZSwgYW5kIGtpbmRcblx0XHRjb25zdCBleGlzdGluZ1VzYWdlcyA9IHRoaXMudXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGlzRHVwbGljYXRlID0gZXhpc3RpbmdVc2FnZXMuc29tZShleGlzdGluZyA9PlxuXHRcdFx0ZXhpc3RpbmcubG9jYXRpb24gPT09IHVzYWdlLmxvY2F0aW9uICYmXG5cdFx0XHRcdGV4aXN0aW5nLmNvZGUgPT09IHVzYWdlLmNvZGUgJiZcblx0XHRcdFx0ZXhpc3Rpbmcua2luZCA9PT0gdXNhZ2Uua2luZCk7XG5cblx0XHRpZiAoIWlzRHVwbGljYXRlKSB7XG5cdFx0XHRleGlzdGluZ1VzYWdlcy5wdXNoKHVzYWdlKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBFRFMgKEV4ZWN1dGlvbiBEYXRhIFN0b3JhZ2UpIHVzYWdlIGluZm9ybWF0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RFRFMgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkgfHwgIW5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZ1bmNOYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIWZ1bmNOYW1lKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXHRcdC8vIEVuY2xvc2luZyBtbmVtb25pY2EgdHlwZSBwYXRoIOKAlCB3cmFwIGFyZ3MgYXJlIHVzdWFsbHkgbG9jYWxcblx0XHQvLyBmdW5jdGlvbnMsIHNvIHRoZSBvd25pbmcgZGVmaW5lKCkvbGF6eSgpIGhhbmRsZXIgb3IgZGVjb3JhdGVkXG5cdFx0Ly8gY2xhc3MgaXMgd2hhdCBlZHMuanNvbiBjb25zdW1lcnMgKEdyYXBoQnVpbGRlcikgY2FuIGpvaW4gb24uXG5cdFx0Y29uc3Qgc2NvcGUgPSB0aGlzLnJlc29sdmVFRFNTY29wZShub2RlKTtcblxuXHRcdC8vIHdyYXAoZm4pLCB3cmFwQ29uc3RydWN0b3JBcmcoZm4sIHBhcmVudCksIHVwZ3JhZGVDb25zdHJ1Y3RvckFyZyhhcmcsIGluc3QpLCB3cmFwSW5zdGFuY2VNZXRob2RzKG9iailcblx0XHRpZiAoXG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3dyYXAnIHx8XG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3dyYXBDb25zdHJ1Y3RvckFyZycgfHxcblx0XHRcdGZ1bmNOYW1lID09PSAndXBncmFkZUNvbnN0cnVjdG9yQXJnJyB8fFxuXHRcdFx0ZnVuY05hbWUgPT09ICd3cmFwSW5zdGFuY2VNZXRob2RzJ1xuXHRcdCkge1xuXHRcdFx0Y29uc3QgdGFyZ2V0VHlwZSA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShub2RlLmFyZ3VtZW50c1sgMCBdKTtcblx0XHRcdC8vIGRpdmUncyB3cmFwLWZhbWlseSBzaWduYXR1cmVzIChkaXZlL3NyYy9pbmRleC50cyk6XG5cdFx0XHQvLyAgIHdyYXAoZm4sIGxhYmVsPykgfCB3cmFwKGZuLCBjb250ZXh0PywgbGFiZWw/KVxuXHRcdFx0Ly8gICB3cmFwQ29uc3RydWN0b3JBcmcoZm4sIGNvbnRleHQpXG5cdFx0XHQvLyAgIHVwZ3JhZGVDb25zdHJ1Y3RvckFyZyhhcmcsIGluc3RhbmNlKVxuXHRcdFx0Ly8gICB3cmFwSW5zdGFuY2VNZXRob2RzKGluc3RhbmNlKVxuXHRcdFx0Ly8g4oCmc28gdGhlIGluc3RhbmNlL2NvbnRleHQgYXJnIHNpdHMgYXQgYXJnc1sxXSAoYXJnc1swXSBmb3Jcblx0XHRcdC8vIHdyYXBJbnN0YW5jZU1ldGhvZHMpIGFuZCBhIHN0cmluZyBsaXRlcmFsIGluIGFyZ3NbMS4uMl0gaXMgdGhlIGxhYmVsXG5cdFx0XHRjb25zdCBpbnN0YW5jZUFyZ05vZGUgPSBmdW5jTmFtZSA9PT0gJ3dyYXBJbnN0YW5jZU1ldGhvZHMnXG5cdFx0XHRcdD8gbm9kZS5hcmd1bWVudHNbIDAgXVxuXHRcdFx0XHQ6IG5vZGUuYXJndW1lbnRzWyAxIF07XG5cdFx0XHQvLyBGaXJlLWFuZC1mb3JnZXQgd3JhcHBlcnMgKHdpcmUtdXAgaGVscGVycywgcmVnaXN0cmF0aW9uXG5cdFx0XHQvLyBmdW5jdGlvbnMpIHNpdCBvdXRzaWRlIGFueSBkZWZpbmUoKS9sYXp5KCkgaGFuZGxlciwgc28gdGhlXG5cdFx0XHQvLyBsZXhpY2FsIHNjb3BlIGlzIGFic2VudCDigJQgYXR0cmlidXRlIHRocm91Z2ggdGhlIGluc3RhbmNlL2NvbnRleHRcblx0XHRcdC8vIGFyZ3VtZW50IGluc3RlYWQ6IGEgdHJhY2tlZCBhc3NpZ25tZW50LCBlbHNlIHRoZSBlbmNsb3Npbmdcblx0XHRcdC8vIGZ1bmN0aW9uJ3MgcGFyYW1ldGVyIGFubm90YXRpb24gcmVzb2x2ZWQgdGhyb3VnaCB0aGUgZ3JhcGggbGF3XG5cdFx0XHRjb25zdCBpbnN0YW5jZVR5cGVQYXRoID0gaW5zdGFuY2VBcmdOb2RlXG5cdFx0XHRcdD8gdGhpcy5yZXNvbHZlV3JhcEluc3RhbmNlVHlwZVBhdGgoaW5zdGFuY2VBcmdOb2RlKVxuXHRcdFx0XHQ6IHVuZGVmaW5lZDtcblx0XHRcdGNvbnN0IGVmZmVjdGl2ZVNjb3BlID0gc2NvcGUgPz8gaW5zdGFuY2VUeXBlUGF0aDtcblx0XHRcdGNvbnN0IGluZm86IEVEU0luZm8gPSB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgIDogJ3dyYXAnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHR0YXJnZXRUeXBlIDogdGFyZ2V0VHlwZSB8fCB1bmRlZmluZWQsXG5cdFx0XHRcdHNjb3BlICAgICAgOiBlZmZlY3RpdmVTY29wZSxcblx0XHRcdFx0Zm4gICAgICAgICA6IGZ1bmNOYW1lLFxuXHRcdFx0fTtcblx0XHRcdGlmIChpbnN0YW5jZUFyZ05vZGUgJiYgdHMuaXNJZGVudGlmaWVyKGluc3RhbmNlQXJnTm9kZSkpIHtcblx0XHRcdFx0aW5mby5pbnN0YW5jZUFyZyA9IGluc3RhbmNlQXJnTm9kZS50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBleHRyYUFyZyBvZiBbIG5vZGUuYXJndW1lbnRzWyAxIF0sIG5vZGUuYXJndW1lbnRzWyAyIF0gXSkge1xuXHRcdFx0XHRpZiAoZXh0cmFBcmcgJiYgdHMuaXNTdHJpbmdMaXRlcmFsKGV4dHJhQXJnKSkge1xuXHRcdFx0XHRcdGluZm8ubGFiZWwgPSBleHRyYUFyZy50ZXh0O1xuXHRcdFx0XHRcdGJyZWFrO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBBIHdyYXAoKSBjYWxsIG5lc3RlZCBpbnNpZGUgYW5vdGhlciB3cmFwcGVkIGJvZHkgY2FycmllcyB0aGVcblx0XHRcdC8vIGxpbmsgdG8gdGhlIHNpdGUgd2hvc2UgcnVudGltZSB3cmFwcGluZyBjYXVzZWQgaXQg4oCUIGFuZCwgd2hlblxuXHRcdFx0Ly8gdGhlIG5lc3RlZCBzaXRlIGhhcyBubyBzY29wZSBvZiBpdHMgb3duLCB0aGUgY2F1c2luZyBzaXRlJ3Ncblx0XHRcdC8vIHNjb3BlIGF0dHJpYnV0aW9uIHRyYXZlbHMgd2l0aCB0aGUgbGlua1xuXHRcdFx0Y29uc3QgdmlhTGluayA9IHRoaXMubmVzdGVkV3JhcFZpYS5nZXQobm9kZSk7XG5cdFx0XHRpZiAodmlhTGluaykge1xuXHRcdFx0XHRpbmZvLnZpYSA9IHZpYUxpbmsudmlhO1xuXHRcdFx0XHRpZiAoaW5mby5zY29wZSA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdFx0aW5mby5zY29wZSA9IHZpYUxpbmsuc2NvcGU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIGRpdmUgd3JhcHMgcmV0dXJuZWQgZnVuY3Rpb25zIHRvbywgYW5kIGFueSBtbmVtb25pY2EgaW5zdGFuY2Vcblx0XHRcdC8vIGNyZWF0ZWQgaW5zaWRlIHRoZSB3cmFwcGVkIGJvZHkgaXMgYSBndWFyYW50ZWVkIHBhdGggaGl0IOKAlFxuXHRcdFx0Ly8gYm90aCBhcmUgY2FsY3VsYWJsZSBBb1QsIHNvIHJlY29yZCB0aGVtXG5cdFx0XHRjb25zdCB3cmFwcGVkID0gdGhpcy5yZXNvbHZlRnVuY3Rpb25Bcmd1bWVudChub2RlLmFyZ3VtZW50c1sgMCBdLCBzb3VyY2VGaWxlKTtcblx0XHRcdGlmICh3cmFwcGVkKSB7XG5cdFx0XHRcdC8vIFRoZSB3cmFwcGVkIGNhbGxiYWNrIGdldHMgaXRzIG93biBzY29wZSBpbiBzY29wZXMuanNvbiBrZXllZCBieVxuXHRcdFx0XHQvLyBpdHMgc3RhcnQgcG9zaXRpb24g4oCUIHJlY29yZCB0aGF0IHNjb3BlSWQgc28gZ3JhcGggY29uc3VtZXJzIGNhblxuXHRcdFx0XHQvLyBqb2luIGEgd3JhcCBlbnRyeSB0byB0aGUgY2FsbGJhY2sncyBjcmVhdGlvbiBub2RlXG5cdFx0XHRcdGNvbnN0IGNhbGxiYWNrUG9zID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHR3cmFwcGVkLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdCk7XG5cdFx0XHRcdGNvbnN0IGNhbGxiYWNrRmlsZSA9IG5vZGVQYXRoLnJlc29sdmUoc291cmNlRmlsZS5maWxlTmFtZSk7XG5cdFx0XHRcdGluZm8uY2FsbGJhY2tTY29wZUlkID0gYCR7Y2FsbGJhY2tGaWxlfToke2NhbGxiYWNrUG9zLmxpbmUgKyAxfToke2NhbGxiYWNrUG9zLmNoYXJhY3RlciArIDF9YDtcblx0XHRcdFx0Y29uc3QgY3JlYXRlc1R5cGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0XHRcdHRoaXMuYW5hbHl6ZVdyYXBwZWRCb2R5KHdyYXBwZWQsIGxvY2F0aW9uLCBzb3VyY2VGaWxlLCAwLCBuZXcgU2V0KCksIGNyZWF0ZXNUeXBlcywgZWZmZWN0aXZlU2NvcGUpO1xuXHRcdFx0XHRpZiAoY3JlYXRlc1R5cGVzLnNpemUgPiAwKSB7XG5cdFx0XHRcdFx0aW5mby5jcmVhdGVzVHlwZXMgPSBBcnJheS5mcm9tKGNyZWF0ZXNUeXBlcyk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGNvbnN0IHN0b3JlZCA9IHRoaXMuYWRkRURTKHRhcmdldFR5cGUgfHwgZWZmZWN0aXZlU2NvcGUgfHwgJ3Vua25vd24nLCBpbmZvKTtcblx0XHRcdHRoaXMud3JhcEVudHJ5QnlOb2RlLnNldChub2RlLCBzdG9yZWQpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGN1cnJlbnQoKSwgZ2V0RXJyb3JJbnN0YW5jZShlcnIpLCBnZXRGbG93KHRhcmdldD8pXG5cdFx0aWYgKGZ1bmNOYW1lID09PSAnY3VycmVudCcgfHwgZnVuY05hbWUgPT09ICdnZXRFcnJvckluc3RhbmNlJyB8fCBmdW5jTmFtZSA9PT0gJ2dldEZsb3cnKSB7XG5cdFx0XHR0aGlzLmFkZEVEUyhzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgOiAnY29udGV4dENvbnN1bWUnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRzY29wZSxcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIGF0dGFjaEhvb2tzKGNvbGxlY3Rpb24pIOKAlCBmcm9tIEBtbmVtb25pY2Evb3RlbCwgd2lyZXMgYVxuXHRcdC8vIFR5cGVzQ29sbGVjdGlvbiB0byBkaXZlJ3MgbGlmZWN5Y2xlIHRyYWNpbmdcblx0XHRpZiAoZnVuY05hbWUgPT09ICdhdHRhY2hIb29rcycgJiYgbm9kZS5hcmd1bWVudHMubGVuZ3RoID4gMCkge1xuXHRcdFx0Y29uc3QgWyBhcmcgXSA9IG5vZGUuYXJndW1lbnRzO1xuXHRcdFx0aWYgKHRzLmlzQXJyYXlMaXRlcmFsRXhwcmVzc2lvbihhcmcpKSB7XG5cdFx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBhcmcuZWxlbWVudHMpIHtcblx0XHRcdFx0XHRjb25zdCB0YXJnZXRUeXBlID0gdGhpcy5yZXNvbHZlRURTQXJndW1lbnRUeXBlKGVsZW1lbnQpO1xuXHRcdFx0XHRcdHRoaXMuYWRkRURTKHRhcmdldFR5cGUgfHwgc2NvcGUgfHwgJ3Vua25vd24nLCB7XG5cdFx0XHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0XHRcdGtpbmQgICAgICAgOiAnaG9va0F0dGFjaCcsXG5cdFx0XHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRcdFx0dGFyZ2V0VHlwZSA6IHRhcmdldFR5cGUgfHwgdW5kZWZpbmVkLFxuXHRcdFx0XHRcdFx0c2NvcGUsXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGNvbnN0IHRhcmdldFR5cGUgPSB0aGlzLnJlc29sdmVFRFNBcmd1bWVudFR5cGUoYXJnKTtcblx0XHRcdFx0dGhpcy5hZGRFRFModGFyZ2V0VHlwZSB8fCBzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0XHRraW5kICAgICAgIDogJ2hvb2tBdHRhY2gnLFxuXHRcdFx0XHRcdGNvZGUsXG5cdFx0XHRcdFx0dGFyZ2V0VHlwZSA6IHRhcmdldFR5cGUgfHwgdW5kZWZpbmVkLFxuXHRcdFx0XHRcdHNjb3BlLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0eXBlIGZyb20gRURTIGNhbGwgYXJndW1lbnQgKGJlc3QgZWZmb3J0KVxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRURTQXJndW1lbnRUeXBlIChhcmc6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghYXJnKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIElkZW50aWZpZXI6IHZhcmlhYmxlIG5hbWVcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdGNvbnN0IG1hcHBlZCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGFyZy50ZXh0KTtcblx0XHRcdGlmIChtYXBwZWQpIHtcblx0XHRcdFx0cmV0dXJuIG1hcHBlZDtcblx0XHRcdH1cblx0XHRcdC8vIE1heWJlIGl0J3MgYSB0eXBlIG5hbWUgZGlyZWN0bHlcblx0XHRcdGlmICh0aGlzLmRlZmluaXRpb25zLmhhcyhhcmcudGV4dCkpIHtcblx0XHRcdFx0cmV0dXJuIGFyZy50ZXh0O1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSBhY2Nlc3M6IG9iai5wcm9wXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdHJldHVybiB0aGlzLnJlc29sdmVUeXBlUGF0aChhcmcpO1xuXHRcdH1cblxuXHRcdC8vIFRoaXMgZXhwcmVzc2lvbjogdGhpcy5zb21ldGhpbmdcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXJnKSAmJiB0cy5pc0lkZW50aWZpZXIoYXJnLmV4cHJlc3Npb24pICYmIGFyZy5leHByZXNzaW9uLnRleHQgPT09ICd0aGlzJykge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgdGhlIGVuY2xvc2luZyBtbmVtb25pY2Egc2NvcGUgb2YgYW4gRURTIGNhbGwgc2l0ZSBieSB3YWxraW5nXG5cdCAqIHVwIHRoZSBwYXJlbnQgY2hhaW46IG5lYXJlc3QgZGVmaW5lKCkvbGF6eSgpIGNhbGwgd2hvc2UgaGFuZGxlciBob2xkc1xuXHQgKiB0aGUgbm9kZSwgb3IgbmVhcmVzdCBAZGVjb3JhdGUoKS1lZCBjbGFzcyBkZWNsYXJhdGlvbi4gQmVzdCBlZmZvcnQg4oCUXG5cdCAqIHJldHVybnMgdW5kZWZpbmVkIGZvciBjYWxscyBvdXRzaWRlIGFueSB0eXBlIHNjb3BlIChtb2R1bGUgdG9wIGxldmVsKS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUVEU1Njb3BlIChub2RlOiB0cy5Ob2RlKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IG5vZGUucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRjb25zdCBzY29wZVBhdGggPSB0aGlzLmVkc1Njb3BlQnlOb2RlLmdldChjdXJyZW50KTtcblx0XHRcdGlmIChzY29wZVBhdGgpIHtcblx0XHRcdFx0cmV0dXJuIHNjb3BlUGF0aDtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgd3JhcCBzaXRlJ3MgaW5zdGFuY2UvY29udGV4dCBhcmd1bWVudCB0byBhIG1uZW1vbmljYSB0eXBlXG5cdCAqIHBhdGgg4oCUIHRoZSBmaXJlLWFuZC1mb3JnZXQtd3JhcHBlciBhdHRyaWJ1dGlvbiBmYWxsYmFjayB3aGVuIHRoZSBjYWxsXG5cdCAqIHNpdHMgb3V0c2lkZSBhbnkgZGVmaW5lKCkvbGF6eSgpIGhhbmRsZXI6IGEgdHJhY2tlZCBhc3NpZ25tZW50XG5cdCAqIChgY29uc3QgaG9sZGVyID0gbmV3IEhvbGRlciguLi4pYCksIGVsc2UgdGhlIHJvb3QgaWRlbnRpZmllcidzXG5cdCAqIChwcm9wZXJ0eS1hY2Nlc3Mgcm9vdHMgaW5jbHVkZWQpIHBhcmFtZXRlciBhbm5vdGF0aW9uIHJlc29sdmVkXG5cdCAqIHRocm91Z2ggdGhlIGdyYXBoIGxhdy4gQW1iaWd1aXR5IG9yIGFic2VuY2Ugc3RheXMgc2lsZW50IOKAlCB0aGlzIGlzIGFcblx0ICogbWV0YWRhdGEgaGV1cmlzdGljLCBub3QgdGhlIGlkZW50aXR5LWxhdyBzdXJmYWNlLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlV3JhcEluc3RhbmNlVHlwZVBhdGggKGFyZzogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgZnJvbUJpbmRpbmcgPSAobmFtZTogc3RyaW5nLCBmcm9tOiB0cy5Ob2RlKTogc3RyaW5nIHwgdW5kZWZpbmVkID0+IHtcblx0XHRcdGNvbnN0IG1hcHBlZCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KG5hbWUpO1xuXHRcdFx0aWYgKG1hcHBlZCkge1xuXHRcdFx0XHRyZXR1cm4gbWFwcGVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgYW5ub3RhdGlvblR5cGUgPSB0aGlzLnJlc29sdmVQYXJhbWV0ZXJBbm5vdGF0aW9uVHlwZVBhdGgobmFtZSwgZnJvbSk7XG5cdFx0XHRyZXR1cm4gYW5ub3RhdGlvblR5cGU7XG5cdFx0fTtcblxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0Y29uc3QgcmVzdWx0ID0gZnJvbUJpbmRpbmcoYXJnLnRleHQsIGFyZyk7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0Y29uc3Qgcm9vdCA9IHRoaXMuZ2V0Um9vdElkZW50aWZpZXIoYXJnKTtcblx0XHRcdGlmIChyb290KSB7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdCA9IGZyb21CaW5kaW5nKHJvb3QudGV4dCwgYXJnKTtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgYmFyZS1pZGVudGlmaWVyIHR5cGUgYW5ub3RhdGlvbiBvZiB0aGUgbmVhcmVzdCBlbmNsb3Npbmdcblx0ICogZnVuY3Rpb24ncyBwYXJhbWV0ZXIgdGhyb3VnaCB0aGUgbW5lbW9uaWNhLWdyYXBoIHRpZXJzICh2YWx1ZSBzY29wZSxcblx0ICogaW1wb3J0cywgcm9vdHMsIHByb2dyYW0td2lkZS11bmlxdWUpLiBOb24taWRlbnRpZmllciBhbmQgZ2VuZXJpY1xuXHQgKiBhbm5vdGF0aW9ucyBhcmUgbm90IGdyYXBoIHJlZmVyZW5jZXM7IGFtYmlndWl0eSBhbmQgYWJzZW5jZSB5aWVsZFxuXHQgKiB1bmRlZmluZWQuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVQYXJhbWV0ZXJBbm5vdGF0aW9uVHlwZVBhdGggKG5hbWU6IHN0cmluZywgZnJvbTogdHMuTm9kZSk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBmcm9tLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0aWYgKHRzLmlzRnVuY3Rpb25MaWtlKGN1cnJlbnQpKSB7XG5cdFx0XHRcdGZvciAoY29uc3QgcGFyYW0gb2YgY3VycmVudC5wYXJhbWV0ZXJzID8/IFtdKSB7XG5cdFx0XHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgfHwgcGFyYW0ubmFtZS50ZXh0ICE9PSBuYW1lIHx8ICFwYXJhbS50eXBlIHx8XG5cdFx0XHRcdFx0XHQhdHMuaXNUeXBlUmVmZXJlbmNlTm9kZShwYXJhbS50eXBlKSB8fFxuXHRcdFx0XHRcdFx0IXRzLmlzSWRlbnRpZmllcihwYXJhbS50eXBlLnR5cGVOYW1lKSB8fFxuXHRcdFx0XHRcdFx0KHBhcmFtLnR5cGUudHlwZUFyZ3VtZW50cz8ubGVuZ3RoID8/IDApID4gMCkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdGNvbnN0IGdyYXBoUmVzdWx0ID0gdGhpcy5yZXNvbHZlR3JhcGhUeXBlTmFtZShwYXJhbS50eXBlLnR5cGVOYW1lLnRleHQpO1xuXHRcdFx0XHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRcdFx0XHRjb25zdCByZXN1bHQgPSBncmFwaFJlc3VsdC5ub2RlLmZ1bGxQYXRoO1xuXHRcdFx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgd3JhcCgpIGFyZ3VtZW50IHRvIGl0cyBmdW5jdGlvbiBub2RlIHdpdGhvdXQgdGhlIHR5cGVcblx0ICogY2hlY2tlcjogZGlyZWN0IGZ1bmN0aW9uIGV4cHJlc3Npb25zL2Fycm93cywgb3Igc2FtZS1maWxlIGJpbmRpbmdzXG5cdCAqIChgY29uc3QgZm4gPSAoKSA9PiAuLi5gLCBgZnVuY3Rpb24gZm4oKSAuLi5gKS4gQmVzdCBlZmZvcnQg4oCUIG1ldGhvZFxuXHQgKiByZWZlcmVuY2VzLCAuYmluZCgpIHByb2R1Y3RzIGFuZCBjcm9zcy1maWxlIGlkZW50aWZpZXJzIHN0YXlcblx0ICogdW5yZXNvbHZlZDsgdGhlIGNhbGxzaXRlIGVudHJ5IGl0c2VsZiBpcyBzdGlsbCByZWNvcmRlZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUZ1bmN0aW9uQXJndW1lbnQgKFxuXHRcdGFyZzogdHMuRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlXG5cdCk6IHRzLkZ1bmN0aW9uTGlrZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIWFyZykge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihhcmcpIHx8IHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdHJldHVybiBhcmc7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0Y29uc3Qga2V5ID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX0jJHthcmcudGV4dH1gO1xuXHRcdFx0Y29uc3QgYm91bmQgPSB0aGlzLmZ1bmN0aW9uQmluZGluZ3MuZ2V0KGtleSk7XG5cdFx0XHRpZiAoYm91bmQpIHtcblx0XHRcdFx0cmV0dXJuIGJvdW5kO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEFuYWx5c2UgYSB3cmFwcGVkIGZ1bmN0aW9uJ3MgYm9keSBmb3IgZ3VhcmFudGVlZCBydW50aW1lIHBhdGhzOlxuXHQgKiBkaXZlIHdyYXBzIHJldHVybmVkIGZ1bmN0aW9ucyBhcyB3ZWxsIChyZWN1cnNpdmVseSksIHNvIGVhY2hcblx0ICogZnVuY3Rpb24tdmFsdWVkIHJldHVybiBpcyBhIG5lc3RlZCB3cmFwIHNpdGUsIGFuZCBlYWNoIGBuZXcgVHlwZSgpYFxuXHQgKiBpbnNpZGUgdGhlIGJvZHkgbWVhbnMgdGhlIHBhdGggaGl0cyB0aGF0IHR5cGUncyBjb25zdHJ1Y3RvciAod2hpY2hcblx0ICogYXR0YWNoSG9va3Mgd3JhcHMgdG9vKS4gQm90aCBmYWN0cyBhcmUgMTAwJSBlbnN1cmVkLCBzbyB0aGV5IGFyZVxuXHQgKiByZWNvcmRlZCBBb1QuIE5lc3RlZCBmdW5jdGlvbiBib2RpZXMgYXJlIE5PVCB3YWxrZWQgaGVyZSDigJQgdGhleVxuXHQgKiBiZWxvbmcgdG8gdGhlaXIgb3duIHdyYXAgYW5hbHlzaXMsIHJlYWNoZWQgdmlhIHRoZSByZXR1cm4gY2hhaW4uXG5cdCAqIERlcHRoLWNhcHBlZCBhbmQgY3ljbGUtZ3VhcmRlZC5cblx0ICovXG5cdHByaXZhdGUgYW5hbHl6ZVdyYXBwZWRCb2R5IChcblx0XHRmbjogdHMuRnVuY3Rpb25MaWtlRGVjbGFyYXRpb24sXG5cdFx0dmlhTG9jYXRpb246IHN0cmluZyxcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdGRlcHRoOiBudW1iZXIsXG5cdFx0dmlzaXRlZDogU2V0PHRzLk5vZGU+LFxuXHRcdGNyZWF0ZXNUeXBlczogU2V0PHN0cmluZz4sXG5cdFx0ZmFsbGJhY2tTY29wZT86IHN0cmluZ1xuXHQpOiB2b2lkIHtcblx0XHRpZiAoZGVwdGggPiA1IHx8IHZpc2l0ZWQuaGFzKGZuKSB8fCAhZm4uYm9keSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR2aXNpdGVkLmFkZChmbik7XG5cblx0XHQvLyBBcnJvdyB3aXRoIGV4cHJlc3Npb24gYm9keTogaW1wbGljaXQgcmV0dXJuXG5cdFx0aWYgKHRzLmlzQXJyb3dGdW5jdGlvbihmbikgJiYgIXRzLmlzQmxvY2soZm4uYm9keSkpIHtcblx0XHRcdHRoaXMucmVjb3JkV3JhcHBlZFJldHVybihmbi5ib2R5LCB2aWFMb2NhdGlvbiwgc291cmNlRmlsZSwgZGVwdGgsIHZpc2l0ZWQsIGZhbGxiYWNrU2NvcGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHdhbGsgPSAobm9kZTogdHMuTm9kZSk6IHZvaWQgPT4ge1xuXHRcdFx0aWYgKG5vZGUgIT09IGZuLmJvZHkgJiYgKFxuXHRcdFx0XHR0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihub2RlKSB8fFxuXHRcdFx0XHR0cy5pc0Fycm93RnVuY3Rpb24obm9kZSkgfHxcblx0XHRcdFx0dHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKG5vZGUpIHx8XG5cdFx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24obm9kZSlcblx0XHRcdCkpIHtcblx0XHRcdFx0Ly8gbmVzdGVkIGZ1bmN0aW9uIGJvZGllcyBhcmUgYW5hbHlzZWQgdGhyb3VnaCB0aGUgcmV0dXJuIGNoYWluXG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRXcmFwcGVkUmV0dXJuKG5vZGUuZXhwcmVzc2lvbiwgdmlhTG9jYXRpb24sIHNvdXJjZUZpbGUsIGRlcHRoLCB2aXNpdGVkLCBmYWxsYmFja1Njb3BlKTtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc05ld0V4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdFx0Y29uc3QgY3JlYXRlZCA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbikgfHxcblx0XHRcdFx0XHQodHMuaXNJZGVudGlmaWVyKG5vZGUuZXhwcmVzc2lvbikgJiYgdGhpcy5kZWZpbml0aW9ucy5oYXMobm9kZS5leHByZXNzaW9uLnRleHQpXG5cdFx0XHRcdFx0XHQ/IG5vZGUuZXhwcmVzc2lvbi50ZXh0XG5cdFx0XHRcdFx0XHQ6IHVuZGVmaW5lZCk7XG5cdFx0XHRcdGlmIChjcmVhdGVkKSB7XG5cdFx0XHRcdFx0Y3JlYXRlc1R5cGVzLmFkZChjcmVhdGVkKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdFx0Y29uc3QgbmVzdGVkTmFtZSA9IHRoaXMuZ2V0RnVuY3Rpb25OYW1lKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHRcdGlmIChcblx0XHRcdFx0XHRuZXN0ZWROYW1lID09PSAnd3JhcCcgfHxcblx0XHRcdFx0XHRuZXN0ZWROYW1lID09PSAnd3JhcENvbnN0cnVjdG9yQXJnJyB8fFxuXHRcdFx0XHRcdG5lc3RlZE5hbWUgPT09ICd1cGdyYWRlQ29uc3RydWN0b3JBcmcnIHx8XG5cdFx0XHRcdFx0bmVzdGVkTmFtZSA9PT0gJ3dyYXBJbnN0YW5jZU1ldGhvZHMnXG5cdFx0XHRcdCkge1xuXHRcdFx0XHRcdC8vIHRoZSBuZXN0ZWQgY2FsbCBtYXkgYWxyZWFkeSBiZSBjb2xsZWN0ZWQgKHZpc2l0ZWRcblx0XHRcdFx0XHQvLyBiZWZvcmUgdGhpcyBvdXRlciB3cmFwIHNpdGUpIOKAlCBiYWNrLXBhdGNoIGl0cyBlbnRyeSxcblx0XHRcdFx0XHQvLyBvdGhlcndpc2UgbGVhdmUgdGhlIGxpbmsgKHdpdGggdGhpcyBzaXRlJ3Mgc2NvcGUpIGZvclxuXHRcdFx0XHRcdC8vIGNvbGxlY3RFRFMgdG8gcGljayB1cFxuXHRcdFx0XHRcdGNvbnN0IG5lc3RlZEVudHJ5ID0gdGhpcy53cmFwRW50cnlCeU5vZGUuZ2V0KG5vZGUpO1xuXHRcdFx0XHRcdGlmIChuZXN0ZWRFbnRyeSkge1xuXHRcdFx0XHRcdFx0bmVzdGVkRW50cnkudmlhID0gdmlhTG9jYXRpb247XG5cdFx0XHRcdFx0XHRpZiAobmVzdGVkRW50cnkuc2NvcGUgPT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRcdFx0XHRuZXN0ZWRFbnRyeS5zY29wZSA9IGZhbGxiYWNrU2NvcGU7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHRcdHRoaXMubmVzdGVkV3JhcFZpYS5zZXQobm9kZSwgeyB2aWEgOiB2aWFMb2NhdGlvbiwgc2NvcGUgOiBmYWxsYmFja1Njb3BlIH0pO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIHdhbGspO1xuXHRcdH07XG5cdFx0d2Fsayhmbi5ib2R5KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgb25lIGZ1bmN0aW9uLXZhbHVlZCByZXR1cm4gb2YgYSB3cmFwcGVkIGJvZHkgYXMgYSBuZXN0ZWQgd3JhcFxuXHQgKiBzaXRlIChgdmlhYCA9IHRoZSBzaXRlIHdob3NlIHdyYXBwaW5nIGNhdXNlZCBpdCkgYW5kIHJlY3Vyc2UgaW50b1xuXHQgKiBpdHMgb3duIHJldHVybnMuIFJldHVybnMgdGhyb3VnaCBpZGVudGlmaWVycyByZXNvbHZlIHRocm91Z2ggdGhlXG5cdCAqIHNhbWUtZmlsZSBiaW5kaW5ncyB0YWJsZTsgdW5yZXNvbHZhYmxlIHJldHVybnMgYXJlIHNpbXBseSBza2lwcGVkLlxuXHQgKiBBIHJldHVybiBkZWNsYXJlZCBvdXRzaWRlIGFueSB0eXBlIHNjb3BlIGluaGVyaXRzIHRoZSBjYXVzaW5nIHdyYXBcblx0ICogc2l0ZSdzIHNjb3BlIGF0dHJpYnV0aW9uICh0aGUgZ2VuZXJhdGlvbiBjaGFpbiBpcyB0aGUgb25seSBob2xkZXIpLlxuXHQgKi9cblx0cHJpdmF0ZSByZWNvcmRXcmFwcGVkUmV0dXJuIChcblx0XHRleHByOiB0cy5FeHByZXNzaW9uLFxuXHRcdHZpYUxvY2F0aW9uOiBzdHJpbmcsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRkZXB0aDogbnVtYmVyLFxuXHRcdHZpc2l0ZWQ6IFNldDx0cy5Ob2RlPixcblx0XHRmYWxsYmFja1Njb3BlPzogc3RyaW5nXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IHJldHVybmVkID0gdGhpcy5yZXNvbHZlRnVuY3Rpb25Bcmd1bWVudChleHByLCBzb3VyY2VGaWxlKTtcblx0XHRpZiAoIXJldHVybmVkKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRyZXR1cm5lZC5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gcmV0dXJuZWQuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXHRcdGNvbnN0IHNjb3BlID0gdGhpcy5yZXNvbHZlRURTU2NvcGUocmV0dXJuZWQpID8/IGZhbGxiYWNrU2NvcGU7XG5cdFx0Y29uc3QgZW50cnkgPSB0aGlzLmFkZEVEUyhzY29wZSB8fCAndW5rbm93bicsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCA6ICd3cmFwJyxcblx0XHRcdGNvZGUsXG5cdFx0XHRzY29wZSxcblx0XHRcdHZpYSAgOiB2aWFMb2NhdGlvbixcblx0XHRcdC8vIGRpdmUgd3JhcHMgcmV0dXJuZWQgZnVuY3Rpb25zIHRocm91Z2ggdGhlIHNhbWUgd3JhcCBtYWNoaW5lcnlcblx0XHRcdGZuICAgOiAnd3JhcCcsXG5cdFx0fSk7XG5cdFx0Ly8gdGhlIHJldHVybmVkIGZ1bmN0aW9uJ3Mgb3duIHJldHVybnMgYXJlIHdyYXBwZWQgaW4gdHVybjsgYHZpYWBcblx0XHQvLyBjaGFpbnMgdG8gdGhpcyBuZXN0ZWQgZW50cnkncyBsb2NhdGlvblxuXHRcdGNvbnN0IG5lc3RlZENyZWF0ZXMgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHR0aGlzLmFuYWx5emVXcmFwcGVkQm9keShyZXR1cm5lZCwgbG9jYXRpb24sIHNvdXJjZUZpbGUsIGRlcHRoICsgMSwgdmlzaXRlZCwgbmVzdGVkQ3JlYXRlcywgc2NvcGUpO1xuXHRcdGlmIChuZXN0ZWRDcmVhdGVzLnNpemUgPiAwKSB7XG5cdFx0XHRlbnRyeS5jcmVhdGVzVHlwZXMgPSBBcnJheS5mcm9tKG5lc3RlZENyZWF0ZXMpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBBZGQgYW4gRURTIHVzYWdlIHRvIHRoZSBjb2xsZWN0aW9uXG5cdCAqIFJldHVybnMgdGhlIHN0b3JlZCBlbnRyeSAodGhlIGV4aXN0aW5nIG9uZSB3aGVuIHRoaXMgaXMgYSBkdXBsaWNhdGUpLFxuXHQgKiBzbyBjYWxsZXJzIGNhbiBlbnJpY2ggaXQgYWZ0ZXIgbmVzdGVkIGJvZHkgYW5hbHlzaXMuXG5cdCAqL1xuXHRwcml2YXRlIGFkZEVEUyAodHlwZVBhdGg6IHN0cmluZywgaW5mbzogRURTSW5mbyk6IEVEU0luZm8ge1xuXHRcdGlmICghdGhpcy5lZHNVc2FnZXMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0dGhpcy5lZHNVc2FnZXMuc2V0KHR5cGVQYXRoLCBbXSk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZXhpc3RpbmcgPSB0aGlzLmVkc1VzYWdlcy5nZXQodHlwZVBhdGgpITtcblx0XHRjb25zdCBkdXBsaWNhdGUgPSBleGlzdGluZy5maW5kKGUgPT4ge1xuXHRcdFx0cmV0dXJuIGUubG9jYXRpb24gPT09IGluZm8ubG9jYXRpb24gJiZcblx0XHRcdFx0ZS5raW5kID09PSBpbmZvLmtpbmQgJiZcblx0XHRcdFx0ZS5jb2RlID09PSBpbmZvLmNvZGU7XG5cdFx0fSk7XG5cblx0XHRpZiAoZHVwbGljYXRlKSB7XG5cdFx0XHRyZXR1cm4gZHVwbGljYXRlO1xuXHRcdH1cblx0XHRleGlzdGluZy5wdXNoKGluZm8pO1xuXHRcdHJldHVybiBpbmZvO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgbmF0aXZlIGZsb3cgcGF0dGVybnMgKGluc3RhbmNlIHVzYWdlIGFmdGVyIGNyZWF0aW9uKVxuXHQgKiBQaGFzZSAxOiBwcm9wZXJ0eSBhY2Nlc3MsIG1ldGhvZCBjYWxscywgYXJndW1lbnRzLCByZXR1cm4sIGRlc3RydWN0dXJpbmcsIGV0Yy5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3cgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHQvLyBQcm9wZXJ0eSByZWFkOiB1c2VyLm5hbWUgb3IgdXNlcj8ubmFtZVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd1Byb3BlcnR5QWNjZXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIEVsZW1lbnQgYWNjZXNzOiB1c2VyWyduYW1lJ11cblx0XHRpZiAodHMuaXNFbGVtZW50QWNjZXNzRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0VsZW1lbnRBY2Nlc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgd3JpdGU6IHVzZXIubmFtZSA9IHZhbHVlXG5cdFx0aWYgKHRzLmlzQmluYXJ5RXhwcmVzc2lvbihub2RlKSAmJiBub2RlLm9wZXJhdG9yVG9rZW4ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FcXVhbHNUb2tlbikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0Fzc2lnbm1lbnQobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gTWV0aG9kIGNhbGw6IHVzZXIudmFsaWRhdGUoKSAgQU5EICBhcmd1bWVudCBwYXNzaW5nOiBwcm9jZXNzVXNlcih1c2VyKVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd01ldGhvZENhbGwobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93QXJndW1lbnRQYXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIERlc3RydWN0dXJlIHJlYWQ6IGNvbnN0IHsgbmFtZSB9ID0gdXNlclxuXHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgJiYgbm9kZS5pbml0aWFsaXplcikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0Rlc3RydWN0dXJlKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFJldHVybiBpbnN0YW5jZTogcmV0dXJuIHVzZXJcblx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQobm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93UmV0dXJuKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFNwcmVhZDogeyAuLi51c2VyIH1cblx0XHRpZiAodHMuaXNTcHJlYWRFbGVtZW50KG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RGbG93U3ByZWFkKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IHByb3BlcnR5IGFjY2VzcyBmbG93IChyZWFkIG9yIGNvbmRpdGlvbmFsKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd1Byb3BlcnR5QWNjZXNzIChub2RlOiB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBwcm9wTmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdC8vIFNraXAgaWYgdGhpcyBpcyBhIHR5cGUgY29uc3RydWN0b3IgYWNjZXNzIChlLmcuLCBVc2VyVHlwZS5kZWZpbmUpXG5cdFx0aWYgKHByb3BOYW1lID09PSAnZGVmaW5lJyB8fCBwcm9wTmFtZSA9PT0gJ2xhenknKSB7IHJldHVybjsgfVxuXG5cdFx0dGhpcy5hZGRGbG93KG9iamVjdFR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICAgIDogJ3Byb3BlcnR5UmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0cHJvcGVydHlOYW1lIDogcHJvcE5hbWUsXG5cdFx0XHR0YXJnZXRUeXBlICAgOiBvYmplY3RUeXBlXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBlbGVtZW50IGFjY2VzcyBmbG93OiB1c2VyWyduYW1lJ11cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dFbGVtZW50QWNjZXNzIChub2RlOiB0cy5FbGVtZW50QWNjZXNzRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAnZWxlbWVudEFjY2VzcycsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGFzc2lnbm1lbnQgZmxvdzogdXNlci5uYW1lID0gdmFsdWUgb3IgdXNlciA9IG90aGVyXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93QXNzaWdubWVudCAobm9kZTogdHMuQmluYXJ5RXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIFByb3BlcnR5IHdyaXRlOiB1c2VyLm5hbWUgPSB2YWx1ZVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmxlZnQpKSB7XG5cdFx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5sZWZ0LmV4cHJlc3Npb24pO1xuXHRcdFx0aWYgKCFvYmplY3RUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0XHRjb25zdCBwcm9wTmFtZSA9IG5vZGUubGVmdC5uYW1lLnRleHQ7XG5cdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdCk7XG5cdFx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCAgICAgICAgIDogJ3Byb3BlcnR5V3JpdGUnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRwcm9wZXJ0eU5hbWUgOiBwcm9wTmFtZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSAgIDogb2JqZWN0VHlwZVxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gVmFyaWFibGUgcmVhc3NpZ25tZW50OiB1c2VyID0gb3RoZXJcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG5vZGUubGVmdCkpIHtcblx0XHRcdGNvbnN0IHZhck5hbWUgPSBub2RlLmxlZnQudGV4dDtcblx0XHRcdGNvbnN0IG1hcHBlZFR5cGUgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldCh2YXJOYW1lKTtcblx0XHRcdGlmICghbWFwcGVkVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHQpO1xuXHRcdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdFx0dGhpcy5hZGRGbG93KG1hcHBlZFR5cGUsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgOiAncmVhc3NpZ25tZW50Jyxcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSA6IG1hcHBlZFR5cGVcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IG1ldGhvZCBjYWxsIGZsb3c6IHVzZXIudmFsaWRhdGUoKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd01ldGhvZENhbGwgKG5vZGU6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3Qgb2JqZWN0VHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbi5leHByZXNzaW9uKTtcblx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCBtZXRob2ROYW1lID0gbm9kZS5leHByZXNzaW9uLm5hbWUudGV4dDtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHQvLyBTa2lwIGlmIHRoaXMgaXMgYSB0eXBlIGNvbnN0cnVjdG9yIGNhbGwgKGUuZy4sIG5ldyBVc2VyVHlwZSgpKVxuXHRcdGlmIChtZXRob2ROYW1lID09PSAnZGVmaW5lJyB8fCBtZXRob2ROYW1lID09PSAnbGF6eScpIHsgcmV0dXJuOyB9XG5cblx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgICAgOiAnbWV0aG9kQ2FsbCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0cHJvcGVydHlOYW1lIDogbWV0aG9kTmFtZSxcblx0XHRcdHRhcmdldFR5cGUgICA6IG9iamVjdFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGFyZ3VtZW50IHBhc3NpbmcgZmxvdzogcHJvY2Vzc1VzZXIodXNlcilcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dBcmd1bWVudFBhc3MgKG5vZGU6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuXHRcdFx0Y29uc3QgYXJnID0gbm9kZS5hcmd1bWVudHNbIGkgXTtcblx0XHRcdGNvbnN0IGFyZ1R5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShhcmcpO1xuXHRcdFx0aWYgKCFhcmdUeXBlKSB7IGNvbnRpbnVlOyB9XG5cblx0XHRcdGNvbnN0IGZ1bmNOYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKSB8fCAnYW5vbnltb3VzJztcblx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0KTtcblx0XHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRcdHRoaXMuYWRkRmxvdyhhcmdUeXBlLCB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgIDogJ3Bhc3NBc0FyZycsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHRhcmdldFR5cGUgOiBhcmdUeXBlLFxuXHRcdFx0XHRjb250ZXh0ICAgIDogYGFyZyAke2l9IHRvICR7ZnVuY05hbWV9YFxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgZGVzdHJ1Y3R1cmluZyBmbG93OiBjb25zdCB7IG5hbWUgfSA9IHVzZXJcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dEZXN0cnVjdHVyZSAobm9kZTogdHMuVmFyaWFibGVEZWNsYXJhdGlvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNPYmplY3RCaW5kaW5nUGF0dGVybihub2RlLm5hbWUpKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3Qgc291cmNlVHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuaW5pdGlhbGl6ZXIhKTtcblx0XHRpZiAoIXNvdXJjZVR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHQvLyBFeHRyYWN0IGRlc3RydWN0dXJlZCBwcm9wZXJ0eSBuYW1lc1xuXHRcdGNvbnN0IHByb3BzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBub2RlLm5hbWUuZWxlbWVudHMpIHtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZWxlbWVudC5uYW1lKSkge1xuXHRcdFx0XHRwcm9wcy5wdXNoKGVsZW1lbnQubmFtZS50ZXh0KTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHR0aGlzLmFkZEZsb3coc291cmNlVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ2Rlc3RydWN0dXJlUmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHNvdXJjZVR5cGUsXG5cdFx0XHRjb250ZXh0ICAgIDogcHJvcHMuam9pbignLCAnKVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgcmV0dXJuIGZsb3c6IHJldHVybiB1c2VyXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93UmV0dXJuIChub2RlOiB0cy5SZXR1cm5TdGF0ZW1lbnQsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCByZXR1cm5UeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uISk7XG5cdFx0aWYgKCFyZXR1cm5UeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0dGhpcy5hZGRGbG93KHJldHVyblR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICA6ICdyZXR1cm4nLFxuXHRcdFx0Y29kZSxcblx0XHRcdHRhcmdldFR5cGUgOiByZXR1cm5UeXBlXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBzcHJlYWQgZmxvdzogeyAuLi51c2VyIH1cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dTcHJlYWQgKG5vZGU6IHRzLlNwcmVhZEVsZW1lbnQsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCBzcHJlYWRUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIXNwcmVhZFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHR0aGlzLmFkZEZsb3coc3ByZWFkVHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ3NwcmVhZCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0dGFyZ2V0VHlwZSA6IHNwcmVhZFR5cGVcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHR5cGUgZnJvbSBhbiBleHByZXNzaW9uIChpZGVudGlmaWVyLCBwcm9wZXJ0eSBhY2Nlc3MsIGV0Yy4pXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVFeHByZXNzaW9uVHlwZSAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Ly8gSWRlbnRpZmllcjogdXNlclxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChleHByLnRleHQpO1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IGFjY2VzczogdXNlci5uYW1lIChyZXR1cm4gb2JqZWN0IHR5cGUsIG5vdCBwcm9wZXJ0eSB0eXBlKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKGV4cHIuZXhwcmVzc2lvbik7XG5cdFx0fVxuXG5cdFx0Ly8gRWxlbWVudCBhY2Nlc3M6IHVzZXJbJ25hbWUnXVxuXHRcdGlmICh0cy5pc0VsZW1lbnRBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUoZXhwci5leHByZXNzaW9uKTtcblx0XHR9XG5cblx0XHQvLyBUaGlzIGV4cHJlc3Npb246IHRoaXMgKGlmIGluIGEgbWV0aG9kLCB3ZSBjYW4ndCByZXNvbHZlIHdpdGhvdXQgbW9yZSBjb250ZXh0KVxuXHRcdGlmIChleHByLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVGhpc0tleXdvcmQpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBBZGQgYSBmbG93IHVzYWdlIHRvIHRoZSBjb2xsZWN0aW9uXG5cdCAqL1xuXHRwcml2YXRlIGFkZEZsb3cgKHR5cGVQYXRoOiBzdHJpbmcsIGluZm86IEZsb3dJbmZvKTogdm9pZCB7XG5cdFx0aWYgKCF0aGlzLmZsb3dVc2FnZXMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0dGhpcy5mbG93VXNhZ2VzLnNldCh0eXBlUGF0aCwgW10pO1xuXHRcdH1cblxuXHRcdGNvbnN0IGV4aXN0aW5nID0gdGhpcy5mbG93VXNhZ2VzLmdldCh0eXBlUGF0aCkhO1xuXHRcdGNvbnN0IGlzRHVwbGljYXRlID0gZXhpc3Rpbmcuc29tZShlID0+IHtcblx0XHRcdHJldHVybiBlLmxvY2F0aW9uID09PSBpbmZvLmxvY2F0aW9uICYmXG5cdFx0XHRcdGUua2luZCA9PT0gaW5mby5raW5kICYmXG5cdFx0XHRcdGUuY29kZSA9PT0gaW5mby5jb2RlO1xuXHRcdH0pO1xuXG5cdFx0aWYgKCFpc0R1cGxpY2F0ZSkge1xuXHRcdFx0ZXhpc3RpbmcucHVzaChpbmZvKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHRcdCogR2V0IHR5cGUgbmFtZSBmcm9tIGV4cHJlc3Npb24gKGlkZW50aWZpZXIgb3IgcHJvcGVydHkgYWNjZXNzKVxuXHRcdFx0Ki9cblx0cHJpdmF0ZSBnZXRUeXBlTmFtZUZyb21FeHByZXNzaW9uIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBuYW1lID0gZXhwci50ZXh0O1xuXHRcdFx0Ly8gQ2hlY2sgaWYgdGhpcyBpZGVudGlmaWVyIGlzIGEgdmFyaWFibGUgbWFwcGVkIHRvIGEgdHlwZSAoZS5nLiwgZnJvbSBsb29rdXApXG5cdFx0XHRjb25zdCBtYXBwZWRUeXBlID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0XHRpZiAobWFwcGVkVHlwZSkge1xuXHRcdFx0XHRyZXR1cm4gbWFwcGVkVHlwZTtcblx0XHRcdH1cblx0XHRcdHJldHVybiBuYW1lO1xuXHRcdH1cblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKGV4cHIpO1xuXHRcdFx0cmV0dXJuIGNoYWluLmpvaW4oJy4nKTtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQqIFJlc29sdmUgZnVsbCB0eXBlIHBhdGggZnJvbSBwcm9wZXJ0eSBhY2Nlc3Ncblx0XHRcdCovXG5cdHByaXZhdGUgcmVzb2x2ZVR5cGVQYXRoIChleHByOiB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKGV4cHIpO1xuXHRcdGlmIChjaGFpbi5sZW5ndGggPT09IDApIHJldHVybiB1bmRlZmluZWQ7XG5cdFxuXHRcdC8vIENoZWNrIGlmIHRoaXMgY2hhaW4gbWF0Y2hlcyBhIGtub3duIHR5cGVcblx0XHRjb25zdCBmdWxsUGF0aCA9IGNoYWluLmpvaW4oJy4nKTtcblx0XHRpZiAodGhpcy5kZWZpbml0aW9ucy5oYXMoZnVsbFBhdGgpKSB7XG5cdFx0XHRyZXR1cm4gZnVsbFBhdGg7XG5cdFx0fVxuXHRcblx0XHQvLyBUcnkganVzdCB0aGUgcHJvcGVydHkgbmFtZVxuXHRcdGNvbnN0IHByb3BOYW1lID0gY2hhaW5bIGNoYWluLmxlbmd0aCAtIDEgXTtcblx0XHRmb3IgKGNvbnN0IFsgcGF0aCBdIG9mIHRoaXMuZGVmaW5pdGlvbnMpIHtcblx0XHRcdGlmIChwYXRoLmVuZHNXaXRoKGAuJHtwcm9wTmFtZX1gKSB8fCBwYXRoID09PSBwcm9wTmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdH1cblx0XHR9XG5cdFxuXHRcdHJldHVybiBmdWxsUGF0aDtcblx0fVxuXHRcblx0LyoqXG5cdFx0XHQgKiBDaGVjayBpZiBhIG5hbWUgbG9va3MgbGlrZSBhIHR5cGUgKHN0YXJ0cyB3aXRoIHVwcGVyY2FzZSlcblx0XHRcdCAqL1xuXHRwcml2YXRlIGlzTGlrZWx5VHlwZU5hbWUgKG5hbWU6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRcdHJldHVybiBuYW1lWyAwIF0gPj0gJ0EnICYmIG5hbWVbIDAgXSA8PSAnWic7XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0ICogUmVzb2x2ZSBhIGNvbnN0cnVjdG9yIHBhcmFtZXRlciB0eXBlLCBleHBhbmRpbmcgaW5saW5lIG9iamVjdCBsaXRlcmFsc1xuXHRcdFx0ICogYW5kIHR5cGUgYWxpYXNlcyB3aGVyZSBwb3NzaWJsZS5cblx0XHRcdCAqL1xuXHRwcml2YXRlIHJlc29sdmVDb25zdHJ1Y3RvclBhcmFtVHlwZSAodHlwZU5vZGU6IHRzLlR5cGVOb2RlIHwgdW5kZWZpbmVkKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIXR5cGVOb2RlKSByZXR1cm4gdW5kZWZpbmVkO1xuXG5cdFx0Ly8gRGlyZWN0IGlubGluZSB0eXBlIGxpdGVyYWw6IHsgcHJvcDogdHlwZSB9XG5cdFx0aWYgKHRzLmlzVHlwZUxpdGVyYWxOb2RlKHR5cGVOb2RlKSkge1xuXHRcdFx0Y29uc3QgcHJvcHM6IHN0cmluZ1tdID0gW107XG5cdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiB0eXBlTm9kZS5tZW1iZXJzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRjb25zdCBvcHRpb25hbCA9IG1lbWJlci5xdWVzdGlvblRva2VuID8gJz8nIDogJyc7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRwcm9wcy5wdXNoKGAke3Byb3BOYW1lfSR7b3B0aW9uYWx9OiAke3R5cGV9YCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiBgeyAke3Byb3BzLmpvaW4oJzsgJyl9IH1gO1xuXHRcdH1cblxuXHRcdC8vIFR5cGUgcmVmZXJlbmNlOiB1c2FnZSwgVXNlckRhdGEsIGV0Yy4gLSByZXNvbHZlIGltcG9ydC1hd2FyZSBhbmRcblx0XHQvLyBleHBhbmQgdGhlIHJlZmVyZW5jZWQgZGVjbGFyYXRpb24gd2hlcmUgcG9zc2libGUgKEYxMClcblx0XHRpZiAodHMuaXNUeXBlUmVmZXJlbmNlTm9kZSh0eXBlTm9kZSkgJiYgdHMuaXNJZGVudGlmaWVyKHR5cGVOb2RlLnR5cGVOYW1lKSkge1xuXHRcdFx0Y29uc3QgdHlwZU5hbWUgPSB0eXBlTm9kZS50eXBlTmFtZS50ZXh0O1xuXHRcdFx0Y29uc3QgZGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24odHlwZU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRpZiAoZGVjbCkge1xuXHRcdFx0XHRjb25zdCBleHBhbmRlZCA9IHRoaXMuZXhwYW5kUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihkZWNsKTtcblx0XHRcdFx0aWYgKGV4cGFuZGVkKSByZXR1cm4gZXhwYW5kZWQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBtbmVtb25pY2EgZ3JhcGggdHlwZXMga2VlcCB0aGVpciBzaW1wbGUgbmFtZSDigJQgdGhlIGdlbmVyYXRvclxuXHRcdFx0Ly8gdXBncmFkZXMgdGhlbSB0byBmdWxsLXBhdGggaW5zdGFuY2UgdHlwZSBuYW1lcy4gUmVzb2x1dGlvbiBpc1xuXHRcdFx0Ly8gcGF0aC1hd2FyZSAoaGFyZC1mYWlsIGxhdyk6IGFtYmlndWl0eSBiZXR3ZWVuIHJlYWwgZ3JhcGggdHlwZXNcblx0XHRcdC8vIHJlY29yZHMgYSBmYXRhbCBlcnJvciBpbnN0ZWFkIG9mIHNpbGVudGx5IHBpY2tpbmcgb25lLlxuXHRcdFx0Y29uc3QgZ3JhcGhSZXN1bHQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKHR5cGVOYW1lKTtcblx0XHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRcdGNvbnN0IHNpbXBsZVJlc3VsdCA9IHR5cGVOYW1lO1xuXHRcdFx0XHRyZXR1cm4gc2ltcGxlUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0aWYgKGdyYXBoUmVzdWx0LnN0YXR1cyA9PT0gJ2FtYmlndW91cycpIHtcblx0XHRcdFx0dGhpcy5yZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yKHR5cGVOYW1lLCB0eXBlTm9kZSwgZ3JhcGhSZXN1bHQpO1xuXHRcdFx0XHRjb25zdCB1bmtub3duR3JhcGhSZXN1bHQgPSAndW5rbm93bic7XG5cdFx0XHRcdHJldHVybiB1bmtub3duR3JhcGhSZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBJZiBub3QgYW4gb2JqZWN0IHR5cGUgYWxpYXMsIHJldHVybiB0aGUgdHlwZSBuYW1lIHdpdGggYXJnc1xuXHRcdFx0aWYgKHR5cGVOb2RlLnR5cGVBcmd1bWVudHMgJiYgdHlwZU5vZGUudHlwZUFyZ3VtZW50cy5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdGlmIChLTk9XTl9HTE9CQUxfVFlQRVMuaGFzKHR5cGVOYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IGFyZ3MgPSB0eXBlTm9kZS50eXBlQXJndW1lbnRzLm1hcChhcmcgPT4gdGhpcy5pbmZlclR5cGUoYXJnKSk7XG5cdFx0XHRcdFx0cmV0dXJuIGAke3R5cGVOYW1lICB9PCR7ICBhcmdzLmpvaW4oJywgJykgIH0+YDtcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBnZW5lcmljIHJlZmVyZW5jZSB0byBhIG5vbi1nbG9iYWwsIG5vbi1ncmFwaCB0eXBlIGNhbm5vdCBiZVxuXHRcdFx0XHQvLyBlbWl0dGVkIGJhcmUgaW50byB0aGUgZ2VuZXJhdGVkIGZpbGVcblx0XHRcdFx0dGhpcy5yZWNvcmRQbGFpblR5cGVSZWZlcmVuY2VTaXRlKHR5cGVOYW1lLCB0eXBlTm9kZSk7XG5cdFx0XHRcdGNvbnN0IHVua25vd25HZW5lcmljUmVzdWx0ID0gJ3Vua25vd24nO1xuXHRcdFx0XHRyZXR1cm4gdW5rbm93bkdlbmVyaWNSZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBmYWxsYmFja1Jlc3VsdCA9IHRoaXMudW5yZXNvbHZlZFR5cGVSZWZlcmVuY2VGYWxsYmFjayh0eXBlTmFtZSwgdHlwZU5vZGUpO1xuXHRcdFx0cmV0dXJuIGZhbGxiYWNrUmVzdWx0O1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0XHRcdCAqIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGEgY2xhc3MtbGlrZSBub2RlLlxuXHRcdFx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENsYXNzQ29uc3RydWN0b3JQYXJhbXMgKGNsYXNzTGlrZTogdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHRzLkNsYXNzRXhwcmVzc2lvbik6XG5cdFx0Q29uc3RydWN0b3JQYXJhbUluZm9bXSB7XG5cdFx0Y29uc3QgcGFyYW1zOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdID0gW107XG5cblx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjbGFzc0xpa2UubWVtYmVycykge1xuXHRcdFx0aWYgKCF0cy5pc0NvbnN0cnVjdG9yRGVjbGFyYXRpb24obWVtYmVyKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblxuXHRcdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBtZW1iZXIucGFyYW1ldGVycykge1xuXHRcdFx0XHRpZiAoIXBhcmFtLm5hbWUgfHwgIXRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSkgY29udGludWU7XG5cdFx0XHRcdGlmICghcGFyYW0udHlwZSkgY29udGludWU7XG5cblx0XHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gcGFyYW0ubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBleHBhbmRlZFR5cGUgPSB0aGlzLnJlc29sdmVDb25zdHJ1Y3RvclBhcmFtVHlwZShwYXJhbS50eXBlKSB8fCB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblxuXHRcdFx0XHRwYXJhbXMucHVzaCh7XG5cdFx0XHRcdFx0bmFtZSAgICAgOiBwYXJhbU5hbWUsXG5cdFx0XHRcdFx0dHlwZSAgICAgOiBleHBhbmRlZFR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiAhIXBhcmFtLnF1ZXN0aW9uVG9rZW4gfHwgISFwYXJhbS5pbml0aWFsaXplclxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHRcdC8vIE9ubHkgcHJvY2VzcyBmaXJzdCBjb25zdHJ1Y3RvclxuXHRcdFx0YnJlYWs7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHBhcmFtcztcblx0fVxuXG5cdC8qKlxuXHRcdFx0ICogRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZyb20gZGVmaW5lKCkgY2FsbFxuXHRcdFx0ICogVGhpcyBpcyB1c2VkIGZvciBUeXBlUmVnaXN0cnkgY29uc3RydWN0b3Igc2lnbmF0dXJlc1xuXHRcdFx0ICogUHJlc2VydmVzIHBhcmFtZXRlciBuYW1lcyBhbmQgZXhwYW5kcyBvYmplY3QgdHlwZXMgdG8gdGhlaXIgc3RydWN0dXJlXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0Q29uc3RydWN0b3JQYXJhbXMgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogQ29uc3RydWN0b3JQYXJhbUluZm9bXSB7XG5cdFx0Y29uc3QgY29uc3RydWN0b3JFeHByID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JFeHByZXNzaW9uKGNhbGwpO1xuXHRcdGlmICghY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRyZXR1cm4gW107XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zRnJvbUNvbnN0cnVjdG9yKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHRcdFx0ICogRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZyb20gYSBjb25zdHJ1Y3RvciBleHByZXNzaW9uLlxuXHRcdFx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zRnJvbUNvbnN0cnVjdG9yIChjb25zdHJ1Y3RvckV4cHI6IHRzLkV4cHJlc3Npb24pOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdIHtcblx0XHRjb25zdCBwYXJhbXM6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10gPSBbXTtcblx0XG5cdFx0Ly8gSGFuZGxlIGZ1bmN0aW9uIGV4cHJlc3Npb24gb3IgYXJyb3cgZnVuY3Rpb25cblx0XHRpZiAodHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSB8fCB0cy5pc0Fycm93RnVuY3Rpb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Ly8gTG9vayBmb3IgY29uc3RydWN0b3IgcGFyYW1ldGVycyAoc2Vjb25kIHBhcmFtIGFmdGVyIGB0aGlzYClcblx0XHRcdC8vIFBhdHRlcm5zOiBmdW5jdGlvbih0aGlzOiBUeXBlLCBkYXRhOiB7IC4uLiB9KSBvciAodGhpczogVHlwZSwgZGF0YTogeyAuLi4gfSkgPT5cblx0XHRcdGZvciAobGV0IGkgPSAwOyBpIDwgY29uc3RydWN0b3JFeHByLnBhcmFtZXRlcnMubGVuZ3RoOyBpKyspIHtcblx0XHRcdFx0Y29uc3QgcGFyYW0gPSBjb25zdHJ1Y3RvckV4cHIucGFyYW1ldGVyc1sgaSBdO1xuXHRcdFx0XHRpZiAoIXBhcmFtLnR5cGUpIGNvbnRpbnVlO1xuXHRcblx0XHRcdFx0Ly8gU2tpcCBgdGhpc2AgcGFyYW1ldGVyIChmaXJzdCBwYXJhbSlcblx0XHRcdFx0aWYgKFxuXHRcdFx0XHRcdGkgPT09IDAgJiZcblx0XHRcdFx0XHRwYXJhbS5uYW1lLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuSWRlbnRpZmllciAmJlxuXHRcdFx0XHRcdChwYXJhbS5uYW1lIGFzIHRzLklkZW50aWZpZXIpLnRleHQgPT09ICd0aGlzJ1xuXHRcdFx0XHQpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcblx0XHRcdFx0Ly8gR2V0IHBhcmFtZXRlciBuYW1lIGFuZCBleHBhbmQgaXRzIHR5cGVcblx0XHRcdFx0Y29uc3QgcGFyYW1OYW1lID0gdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpID8gcGFyYW0ubmFtZS50ZXh0IDogJ2FyZyc7XG5cdFx0XHRcdGNvbnN0IGV4cGFuZGVkVHlwZSA9IHRoaXMucmVzb2x2ZUNvbnN0cnVjdG9yUGFyYW1UeXBlKHBhcmFtLnR5cGUpIHx8IHRoaXMuaW5mZXJUeXBlKHBhcmFtLnR5cGUpO1xuXHRcdFx0XHRcdFxuXHRcdFx0XHRwYXJhbXMucHVzaCh7XG5cdFx0XHRcdFx0bmFtZSAgICAgOiBwYXJhbU5hbWUsXG5cdFx0XHRcdFx0dHlwZSAgICAgOiBleHBhbmRlZFR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiAhIXBhcmFtLnF1ZXN0aW9uVG9rZW4gfHwgISFwYXJhbS5pbml0aWFsaXplclxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cdFxuXHRcdC8vIEhhbmRsZSBjbGFzcyBleHByZXNzaW9uIC0gY2hlY2sgY29uc3RydWN0b3IgbWV0aG9kXG5cdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikpIHtcblx0XHRcdGNvbnN0IGNsYXNzUGFyYW1zID0gdGhpcy5leHRyYWN0Q2xhc3NDb25zdHJ1Y3RvclBhcmFtcyhjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBjbGFzc1BhcmFtcykge1xuXHRcdFx0XHRwYXJhbXMucHVzaChwYXJhbSk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHBhcmFtcztcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGZyYW1ld29yayBpbnN0cnVtZW50YXRpb24gcG9pbnRzLiBQdXJlbHkgc3ludGFjdGljOiBoZXJpdGFnZVxuXHQgKiBjbGF1c2VzLCBkZWNvcmF0b3IgYXBwbGljYXRpb24gc2l0ZXMsIHByb3ZpZGVyLXRva2VuIG9iamVjdCBsaXRlcmFsc1xuXHQgKiBhbmQgY29uc3VtZXIuYXBwbHkoKS5mb3JSb3V0ZXMoKSB3aXJpbmcuIFRoZSB2b2NhYnVsYXJ5IGNvbWVzIGZyb21cblx0ICogcGx1Z2luczsgaWRlbnRpZmllciB0ZXh0IGlzIG1hdGNoZWQgYXMtaXMg4oCUIG5vIGltcG9ydCByZXNvbHV0aW9uLFxuXHQgKiB0aGUgdHlwZSBjaGVja2VyIHN0YXlzIHVudXNlZC5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEluc3RydW1lbnRhdGlvbiAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICh0cy5pc0NsYXNzRGVjbGFyYXRpb24obm9kZSkgJiYgbm9kZS5uYW1lKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RJbnN0cnVtZW50YXRpb25DbGFzcyhub2RlLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cdFx0aWYgKHRzLmlzRGVjb3JhdG9yKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RJbnN0cnVtZW50YXRpb25EZWNvcmF0b3Iobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0fVxuXHRcdGlmICh0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RJbnN0cnVtZW50YXRpb25Qcm92aWRlcihub2RlLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbk1pZGRsZXdhcmUobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhIG5hbWVkIGNsYXNzIGRlY2xhcmF0aW9uIGZvciBpbnN0cnVtZW50YXRpb24gc2l0ZSByZXNvbHV0aW9uXG5cdCAqIGFuZCBkZXRlY3QgaGVyaXRhZ2UtYmFzZWQga2luZHMgKGBpbXBsZW1lbnRzIDxwbHVnaW4gaW50ZXJmYWNlPmApXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb25DbGFzcyAobm9kZTogdHMuQ2xhc3NEZWNsYXJhdGlvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghbm9kZS5uYW1lKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGNsYXNzTmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLm5hbWUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Ly8gRmlyc3QgbGluZSBvZiB0aGUgZGVjbGFyYXRpb24sIGxpa2UgRURTIGBjb2RlYCBzbmlwcGV0c1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc3BsaXQoJ1xcbicpWyAwIF0uc2xpY2UoMCwgMTAwKTtcblxuXHRcdGxldCBraW5kOiBJbnN0cnVtZW50YXRpb25LaW5kIHwgdW5kZWZpbmVkO1xuXHRcdGlmIChub2RlLmhlcml0YWdlQ2xhdXNlcykge1xuXHRcdFx0Zm9yIChjb25zdCBjbGF1c2Ugb2Ygbm9kZS5oZXJpdGFnZUNsYXVzZXMpIHtcblx0XHRcdFx0aWYgKGNsYXVzZS50b2tlbiAhPT0gdHMuU3ludGF4S2luZC5JbXBsZW1lbnRzS2V5d29yZCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGZvciAoY29uc3QgdHlwZSBvZiBjbGF1c2UudHlwZXMpIHtcblx0XHRcdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcih0eXBlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Y29uc3QgbWF0Y2hlZCA9IHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS5pbnRlcmZhY2VzWyB0eXBlLmV4cHJlc3Npb24udGV4dCBdO1xuXHRcdFx0XHRcdGlmIChtYXRjaGVkKSB7XG5cdFx0XHRcdFx0XHRraW5kID0gbWF0Y2hlZDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCBkZWNsOiBJbnN0cnVtZW50YXRpb25DbGFzc0RlY2wgPSB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGNvZGUsXG5cdFx0fTtcblx0XHRpZiAoa2luZCkge1xuXHRcdFx0ZGVjbC5raW5kID0ga2luZDtcblx0XHR9XG5cdFx0dGhpcy5pbnN0cnVtZW50YXRpb25DbGFzc0RlY2xzLnNldChjbGFzc05hbWUsIGRlY2wpO1xuXHR9XG5cblx0LyoqXG5cdCAqIERldGVjdCBkZWNvcmF0b3IgYXBwbGljYXRpb24gc2l0ZXM6IHBsdWdpbi1saXN0ZWQgZGVjb3JhdG9ycyBhcHBsaWVkXG5cdCAqIHdpdGggY2xhc3MgYXJndW1lbnRzIG9uIGEgY2xhc3Mgb3Igb25lIG9mIGl0cyBtZXRob2RzLiBPbmUgc2l0ZSBwZXJcblx0ICogcmVmZXJlbmNlZCBjbGFzcyBpZGVudGlmaWVyLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0SW5zdHJ1bWVudGF0aW9uRGVjb3JhdG9yIChub2RlOiB0cy5EZWNvcmF0b3IsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCB7IGV4cHJlc3Npb24gfSA9IG5vZGU7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKGV4cHJlc3Npb24pIHx8ICF0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbi5leHByZXNzaW9uKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBraW5kID0gdGhpcy5pbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5LnVzZURlY29yYXRvcnNbIGV4cHJlc3Npb24uZXhwcmVzc2lvbi50ZXh0IF07XG5cdFx0aWYgKCFraW5kKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gVGhlIGRlY29yYXRvcidzIHBhcmVudCBpcyB0aGUgZGVjb3JhdGVkIG5vZGU6IGEgY29udHJvbGxlciBjbGFzcyxcblx0XHQvLyBvbmUgb2YgaXRzIG1ldGhvZHMsIG9yIG9uZSBvZiBpdHMgbWV0aG9kIHBhcmFtZXRlcnNcblx0XHQvLyAoQEJvZHkobXZwLmZvclR5cGUoRHRvKSkgb24gYSBoYW5kbGVyIGFyZ3VtZW50KVxuXHRcdGNvbnN0IGRlY29yYXRlZCA9IG5vZGUucGFyZW50O1xuXHRcdGxldCBzY29wZTogSW5zdHJ1bWVudGF0aW9uU2NvcGU7XG5cdFx0bGV0IHRhcmdldHM6IHN0cmluZ1tdO1xuXHRcdGlmICh0cy5pc0NsYXNzRGVjbGFyYXRpb24oZGVjb3JhdGVkKSAmJiBkZWNvcmF0ZWQubmFtZSkge1xuXHRcdFx0c2NvcGUgPSBgY29udHJvbGxlcjoke2RlY29yYXRlZC5uYW1lLnRleHR9YDtcblx0XHRcdHRhcmdldHMgPSBbIGRlY29yYXRlZC5uYW1lLnRleHQgXTtcblx0XHR9IGVsc2UgaWYgKFxuXHRcdFx0dHMuaXNNZXRob2REZWNsYXJhdGlvbihkZWNvcmF0ZWQpICYmXG5cdFx0XHR0cy5pc0lkZW50aWZpZXIoZGVjb3JhdGVkLm5hbWUpICYmXG5cdFx0XHR0cy5pc0NsYXNzRGVjbGFyYXRpb24oZGVjb3JhdGVkLnBhcmVudCkgJiZcblx0XHRcdGRlY29yYXRlZC5wYXJlbnQubmFtZVxuXHRcdCkge1xuXHRcdFx0Y29uc3QgY2xhc3NOYW1lID0gZGVjb3JhdGVkLnBhcmVudC5uYW1lLnRleHQ7XG5cdFx0XHRzY29wZSA9IGBtZXRob2Q6JHtjbGFzc05hbWV9LiR7ZGVjb3JhdGVkLm5hbWUudGV4dH1gO1xuXHRcdFx0dGFyZ2V0cyA9IFsgY2xhc3NOYW1lIF07XG5cdFx0fSBlbHNlIGlmICh0cy5pc1BhcmFtZXRlcihkZWNvcmF0ZWQpKSB7XG5cdFx0XHQvLyBQYXJhbWV0ZXIgZGVjb3JhdG9ycyB0YWtlIHRoZSBlbmNsb3NpbmcgbWV0aG9kJ3Mgc2NvcGUg4oCUIHRoZVxuXHRcdFx0Ly8gYXR0YWNobWVudCBwb2ludCBpcyB0aGUgaGFuZGxlciwgbm90IHRoZSBhcmd1bWVudCBuYW1lOyB0aGVcblx0XHRcdC8vIHNhbWUgbWV0aG9kOkNsYXNzLm1ldGhvZCBmb3JtIGFzIG1ldGhvZC1sZXZlbCBzaXRlcy4gUGFyYW1zIG9mXG5cdFx0XHQvLyBjb25zdHJ1Y3RvcnMsIGZ1bmN0aW9ucywgYW5kIHVubmFtZWFibGUgaG9zdHMgc3RheSBzaWxlbnQsIHRoZVxuXHRcdFx0Ly8gc2FtZSBjb252ZW50aW9uIGFzIG90aGVyIHVucmVzb2x2YWJsZSBkZWNvcmF0b3IgcGFyZW50c1xuXHRcdFx0Y29uc3QgaG9zdCA9IGRlY29yYXRlZC5wYXJlbnQ7XG5cdFx0XHRpZiAoXG5cdFx0XHRcdGhvc3QgJiZcblx0XHRcdFx0dHMuaXNNZXRob2REZWNsYXJhdGlvbihob3N0KSAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoaG9zdC5uYW1lKSAmJlxuXHRcdFx0XHR0cy5pc0NsYXNzRGVjbGFyYXRpb24oaG9zdC5wYXJlbnQpICYmXG5cdFx0XHRcdGhvc3QucGFyZW50Lm5hbWVcblx0XHRcdCkge1xuXHRcdFx0XHRjb25zdCBjbGFzc05hbWUgPSBob3N0LnBhcmVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdHNjb3BlID0gYG1ldGhvZDoke2NsYXNzTmFtZX0uJHtob3N0Lm5hbWUudGV4dH1gO1xuXHRcdFx0XHR0YXJnZXRzID0gWyBjbGFzc05hbWUgXTtcblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHR9IGVsc2Uge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdGZvciAoY29uc3QgYXJnIG9mIGV4cHJlc3Npb24uYXJndW1lbnRzKSB7XG5cdFx0XHQvLyBDbGFzcyByZWZlcmVuY2U6IEBSZWdpc3RlcihJbXBsKSBvciBhbiBpbmxpbmUgaW5zdGFuY2U6XG5cdFx0XHQvLyBAUmVnaXN0ZXIobmV3IEltcGwoeyAuLi5vcHRpb25zIH0pKVxuXHRcdFx0bGV0IGNsYXNzTmFtZTogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdFx0Ly8gcGVyLWFyZyBraW5kOiBmYWN0b3J5LWNhbGwgYXJncyBjYXJyeSB0aGVpciBvd24gY29uZmlndXJlZFxuXHRcdFx0Ly8ga2luZCwgZXZlcnl0aGluZyBlbHNlIHRha2VzIHRoZSBkZWNvcmF0b3Inc1xuXHRcdFx0bGV0IGFyZ0tpbmQgPSBraW5kO1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihhcmcpKSB7XG5cdFx0XHRcdGNsYXNzTmFtZSA9IGFyZy50ZXh0O1xuXHRcdFx0fSBlbHNlIGlmICh0cy5pc05ld0V4cHJlc3Npb24oYXJnKSAmJiB0cy5pc0lkZW50aWZpZXIoYXJnLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNsYXNzTmFtZSA9IGFyZy5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHR9IGVsc2UgaWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oYXJnKSAmJiB0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcmcuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Ly8gUGlwZS1mYWN0b3J5IHNoYXBlOiBAVXNlUGlwZXMobXZwLmZvclR5cGUoRHRvKSkg4oCUIHRoZVxuXHRcdFx0XHQvLyBjYWxsJ3MgbWV0aG9kIG5hbWUgaXMgcGx1Z2luLWxpc3RlZCwgdGhlIHRhcmdldCBjbGFzcyBzaXRzXG5cdFx0XHRcdC8vIGluIHRoZSBjb25maWd1cmVkIGFyZ3VtZW50IHBvc2l0aW9uIChkZWZhdWx0IDApXG5cdFx0XHRcdGNvbnN0IGZhY3RvcnkgPSB0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkuZGVjb3JhdG9yQXJnRmFjdG9yaWVzWyBhcmcuZXhwcmVzc2lvbi5uYW1lLnRleHQgXTtcblx0XHRcdFx0aWYgKGZhY3RvcnkpIHtcblx0XHRcdFx0XHRjb25zdCB0YXJnZXRBcmcgPSBhcmcuYXJndW1lbnRzWyBmYWN0b3J5LnRhcmdldEFyZyA/PyAwIF07XG5cdFx0XHRcdFx0aWYgKHRhcmdldEFyZyAmJiB0cy5pc0lkZW50aWZpZXIodGFyZ2V0QXJnKSkge1xuXHRcdFx0XHRcdFx0Y2xhc3NOYW1lID0gdGFyZ2V0QXJnLnRleHQ7XG5cdFx0XHRcdFx0XHRhcmdLaW5kID0gZmFjdG9yeS5raW5kO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKCFjbGFzc05hbWUpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHR0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzLnB1c2goe1xuXHRcdFx0XHRraW5kIDogYXJnS2luZCxcblx0XHRcdFx0Y2xhc3NOYW1lLFxuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0c2NvcGUsXG5cdFx0XHRcdHRhcmdldHMsXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRGV0ZWN0IGdsb2JhbCByZWdpc3RyYXRpb25zOiBvYmplY3QgbGl0ZXJhbHMgc2hhcGVkIGxpa2Vcblx0ICogYHsgcHJvdmlkZTogPHBsdWdpbi1saXN0ZWQgdG9rZW4+LCB1c2VDbGFzczogWCB9YC5cblx0ICogdXNlRXhpc3RpbmcvdXNlRmFjdG9yeSB3aXRob3V0IGEgdXNlQ2xhc3MgaWRlbnRpZmllciBhcmUgbm90XG5cdCAqIHN0YXRpY2FsbHkgb2J2aW91cyDigJQgc2tpcHBlZCByYXRoZXIgdGhhbiBndWVzc2VkLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0SW5zdHJ1bWVudGF0aW9uUHJvdmlkZXIgKG5vZGU6IHRzLk9iamVjdExpdGVyYWxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0bGV0IGtpbmQ6IEluc3RydW1lbnRhdGlvbktpbmQgfCB1bmRlZmluZWQ7XG5cdFx0bGV0IHVzZUNsYXNzTmFtZTogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXG5cdFx0Zm9yIChjb25zdCBwcm9wIG9mIG5vZGUucHJvcGVydGllcykge1xuXHRcdFx0aWYgKFxuXHRcdFx0XHQhdHMuaXNQcm9wZXJ0eUFzc2lnbm1lbnQocHJvcCkgfHxcblx0XHRcdFx0IXRzLmlzSWRlbnRpZmllcihwcm9wLm5hbWUpIHx8XG5cdFx0XHRcdCF0cy5pc0lkZW50aWZpZXIocHJvcC5pbml0aWFsaXplcilcblx0XHRcdCkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGlmIChwcm9wLm5hbWUudGV4dCA9PT0gJ3Byb3ZpZGUnKSB7XG5cdFx0XHRcdGtpbmQgPSB0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkuYXBwVG9rZW5zWyBwcm9wLmluaXRpYWxpemVyLnRleHQgXTtcblx0XHRcdH1cblx0XHRcdGlmIChwcm9wLm5hbWUudGV4dCA9PT0gJ3VzZUNsYXNzJykge1xuXHRcdFx0XHR1c2VDbGFzc05hbWUgPSBwcm9wLmluaXRpYWxpemVyLnRleHQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0aWYgKCFraW5kIHx8ICF1c2VDbGFzc05hbWUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHR0aGlzLmluc3RydW1lbnRhdGlvblNpdGVzLnB1c2goe1xuXHRcdFx0a2luZCxcblx0XHRcdGNsYXNzTmFtZSA6IHVzZUNsYXNzTmFtZSxcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0Y29kZSxcblx0XHRcdHNjb3BlICAgICA6ICdnbG9iYWwnLFxuXHRcdFx0dGFyZ2V0cyAgIDogW10sXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogRGV0ZWN0IG1pZGRsZXdhcmUgd2lyaW5nOiBgY29uc3VtZXIuYXBwbHkoTXcxLCBNdzIpLmZvclJvdXRlcyguLi4pYFxuXHQgKiBpbnNpZGUgYSBjbGFzcydzIGNvbmZpZ3VyZSgpIG1ldGhvZC4gVGFyZ2V0cyBjb21lIGZyb20gZm9yUm91dGVzXG5cdCAqIGFyZ3VtZW50cyB3aGVuIHN0YXRpY2FsbHkgcmVhZGFibGUgKHN0cmluZyByb3V0ZXMgb3IgY29udHJvbGxlclxuXHQgKiBpZGVudGlmaWVycyksIGVsc2UgW10uIFNoYXBlLWJhc2VkLCBzbyBhIHBsdWdpbiBtdXN0IG9wdCBpbiB2aWFcblx0ICogYG1pZGRsZXdhcmVXaXJpbmc6IHRydWVgLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0SW5zdHJ1bWVudGF0aW9uTWlkZGxld2FyZSAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS5taWRkbGV3YXJlV2lyaW5nKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGlmIChcblx0XHRcdCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pIHx8XG5cdFx0XHRub2RlLmV4cHJlc3Npb24ubmFtZS50ZXh0ICE9PSAnZm9yUm91dGVzJ1xuXHRcdCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBhcHBseUNhbGwgPSBub2RlLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRpZiAoXG5cdFx0XHQhdHMuaXNDYWxsRXhwcmVzc2lvbihhcHBseUNhbGwpIHx8XG5cdFx0XHQhdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXBwbHlDYWxsLmV4cHJlc3Npb24pIHx8XG5cdFx0XHRhcHBseUNhbGwuZXhwcmVzc2lvbi5uYW1lLnRleHQgIT09ICdhcHBseSdcblx0XHQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKCF0aGlzLmlzSW5zaWRlQ29uZmlndXJlTWV0aG9kKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgdGFyZ2V0czogc3RyaW5nW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IGFyZyBvZiBub2RlLmFyZ3VtZW50cykge1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihhcmcpIHx8IHRzLmlzU3RyaW5nTGl0ZXJhbChhcmcpKSB7XG5cdFx0XHRcdHRhcmdldHMucHVzaChhcmcudGV4dCk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdGFwcGx5Q2FsbC5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRmb3IgKGNvbnN0IGFyZyBvZiBhcHBseUNhbGwuYXJndW1lbnRzKSB7XG5cdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihhcmcpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0dGhpcy5pbnN0cnVtZW50YXRpb25TaXRlcy5wdXNoKHtcblx0XHRcdFx0a2luZCAgICAgIDogJ21pZGRsZXdhcmUnLFxuXHRcdFx0XHRjbGFzc05hbWUgOiBhcmcudGV4dCxcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHNjb3BlICAgICA6ICdtb2R1bGUnLFxuXHRcdFx0XHR0YXJnZXRzLFxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFdhbGsgdXAgdGhlIHBhcmVudCBjaGFpbiBsb29raW5nIGZvciBhbiBlbmNsb3NpbmcgY29uZmlndXJlKCkgbWV0aG9kXG5cdCAqL1xuXHRwcml2YXRlIGlzSW5zaWRlQ29uZmlndXJlTWV0aG9kIChub2RlOiB0cy5Ob2RlKTogYm9vbGVhbiB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBub2RlLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc01ldGhvZERlY2xhcmF0aW9uKGN1cnJlbnQpICYmXG5cdFx0XHRcdHRzLmlzSWRlbnRpZmllcihjdXJyZW50Lm5hbWUpICYmXG5cdFx0XHRcdGN1cnJlbnQubmFtZS50ZXh0ID09PSAnY29uZmlndXJlJ1xuXHRcdFx0KSB7XG5cdFx0XHRcdHJldHVybiB0cnVlO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cbn1cbiJdfQ==