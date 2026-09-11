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
            let expr = element;
            while (ts.isAsExpression(expr) ||
                ts.isSatisfiesExpression(expr) ||
                ts.isTypeAssertionExpression(expr)) {
                expr = expr.expression;
            }
            if (ts.isStringLiteral(expr) || ts.isNoSubstitutionTemplateLiteral(expr)) {
                literals.push(`'${expr.text}'`);
            }
            else if (ts.isPrefixUnaryExpression(expr) && ts.isNumericLiteral(expr.operand)) {
                // signed numeric literals (`-1 | 1`): unary minus is part
                // of the literal type; unary plus is the bare literal in
                // type space (`+1` is written `1`)
                if (expr.operator === ts.SyntaxKind.MinusToken) {
                    literals.push(`-${expr.operand.text}`);
                }
                else if (expr.operator === ts.SyntaxKind.PlusToken) {
                    literals.push(expr.operand.text);
                }
                else {
                    return undefined;
                }
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
                const graphResult = this.resolveGraphTypeName(declaration.type.typeName.text);
                if (graphResult.status === 'unique') {
                    const result = graphResult.node.fullPath;
                    return result;
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYW5hbHl6ZXIuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvYW5hbHl6ZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFFYiwrQ0FBaUM7QUFDakMsK0NBQWlDO0FBT2pDLG1DQUVpQjtBQUNqQix1Q0FFbUI7QUErRG5COzs7R0FHRztBQUNILE1BQU0sa0JBQWtCLEdBQUcsSUFBSSxHQUFHLENBQUM7SUFDbEMsTUFBTSxFQUFFLFFBQVEsRUFBRSxPQUFPLEVBQUUsV0FBVyxFQUFFLFlBQVksRUFBRSxnQkFBZ0I7SUFDdEUsYUFBYSxFQUFFLFdBQVcsRUFBRSxVQUFVLEVBQUUsZ0JBQWdCO0lBQ3hELEtBQUssRUFBRSxLQUFLLEVBQUUsU0FBUyxFQUFFLFNBQVMsRUFBRSxTQUFTLEVBQUUsc0JBQXNCO0lBQ3JFLFNBQVMsRUFBRSxPQUFPLEVBQUUsZUFBZSxFQUFFLFFBQVEsRUFBRSxTQUFTLEVBQUUsVUFBVTtJQUNwRSxVQUFVLEVBQUUsTUFBTSxFQUFFLE1BQU0sRUFBRSxTQUFTLEVBQUUsU0FBUyxFQUFFLGFBQWE7SUFDL0QsWUFBWSxFQUFFLGNBQWMsRUFBRSxZQUFZLEVBQUUsdUJBQXVCO0lBQ25FLFVBQVUsRUFBRSxtQkFBbUIsRUFBRSxtQkFBbUI7SUFDcEQsV0FBVyxFQUFFLFdBQVcsRUFBRSxZQUFZLEVBQUUsY0FBYztJQUN0RCxRQUFRLEVBQUUsUUFBUSxFQUFFLFNBQVMsRUFBRSxRQUFRLEVBQUUsUUFBUSxFQUFFLFFBQVEsRUFBRSxVQUFVO0lBQ3ZFLFVBQVUsRUFBRSxVQUFVLEVBQUUsV0FBVyxFQUFFLGVBQWUsRUFBRSxlQUFlO0lBQ3JFLGdCQUFnQixFQUFFLGtCQUFrQixFQUFFLHVCQUF1QjtJQUM3RCxhQUFhLEVBQUUsYUFBYSxFQUFFLG1CQUFtQixFQUFFLFVBQVU7SUFDN0QsV0FBVyxFQUFFLFlBQVksRUFBRSxtQkFB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OlsiJ3VzZSBzdHJpY3QnO1xuXG5pbXBvcnQgKiBhcyBub2RlUGF0aCBmcm9tICdwYXRoJztcbmltcG9ydCAqIGFzIHRzIGZyb20gJ3R5cGVzY3JpcHQnO1xuaW1wb3J0IHtcblx0VHlwZU5vZGUsIFByb3BlcnR5SW5mbywgQW5hbHl6ZVJlc3VsdCwgQW5hbHl6ZUVycm9yLFxuXHREZWZpbml0aW9uSW5mbywgVXNhZ2VJbmZvLCBDb25zdHJ1Y3RvclBhcmFtSW5mbyxcblx0RURTSW5mbywgRmxvd0luZm8sIEluc3RydW1lbnRhdGlvbktpbmQsIEluc3RydW1lbnRhdGlvblBvaW50LFxuXHRJbnN0cnVtZW50YXRpb25TY29wZSwgUmVzb2x1dGlvbkVycm9yXG59IGZyb20gJy4vdHlwZXMnO1xuaW1wb3J0IHtcblx0VHlwZUdyYXBoSW1wbCwgcmVzb2x2ZUdyYXBoVHlwZVJlZmVyZW5jZSwgR3JhcGhUeXBlUmVmZXJlbmNlUmVzdWx0IFxufSBmcm9tICcuL2dyYXBoJztcbmltcG9ydCB7XG5cdEluc3RydW1lbnRhdGlvblZvY2FidWxhcnksIFRhY3RpY2FQbHVnaW4sIG1lcmdlVGFjdGljYVBsdWdpbnNcbn0gZnJvbSAnLi9wbHVnaW5zJztcblxuaW50ZXJmYWNlIENvbGxlY3Rpb25JbmZvIHtcblx0dmFyaWFibGVOYW1lOiBzdHJpbmc7XG5cdHNvdXJjZUZpbGU6IHN0cmluZztcblx0cmVnaXN0cnlJbnRlcmZhY2VOYW1lPzogc3RyaW5nO1xufVxuXG4vKipcbiAqIExvY2F0aW9uL2NvZGUgY2FwdHVyZWQgYXQgYSBjbGFzcyBkZWNsYXJhdGlvbiwgdXNlZCB0byByZXNvbHZlXG4gKiBpbnN0cnVtZW50YXRpb24gcmVnaXN0cmF0aW9uIHNpdGVzIHRvIHRoZSBkZWNsYXJlZCBjbGFzc1xuICovXG5pbnRlcmZhY2UgSW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNsIHtcblx0a2luZD86IEluc3RydW1lbnRhdGlvbktpbmQ7XG5cdGxvY2F0aW9uOiBzdHJpbmc7XG5cdGNvZGU6IHN0cmluZztcbn1cblxuLyoqXG4gKiBSYXcgcmVnaXN0cmF0aW9uIHNpdGUgKGRlY29yYXRvciwgQVBQXyogcHJvdmlkZXIsIGNvbnN1bWVyLmFwcGx5KS5cbiAqIExvY2F0aW9uL2NvZGUgYXJlIHRoZSBzaXRlJ3Mgb3duOyBnZXRJbnN0cnVtZW50YXRpb25Qb2ludHMoKSByZXdyaXRlc1xuICogdGhlbSB0byB0aGUgY2xhc3MgZGVjbGFyYXRpb24gd2hlbiB0aGUgY2xhc3MgaXMgZGVjbGFyZWQgaW4tcHJvamVjdC5cbiAqL1xuaW50ZXJmYWNlIEluc3RydW1lbnRhdGlvblNpdGUge1xuXHRraW5kOiBJbnN0cnVtZW50YXRpb25LaW5kO1xuXHRjbGFzc05hbWU6IHN0cmluZztcblx0bG9jYXRpb246IHN0cmluZztcblx0Y29kZTogc3RyaW5nO1xuXHRzY29wZTogSW5zdHJ1bWVudGF0aW9uU2NvcGU7XG5cdHRhcmdldHM6IHN0cmluZ1tdO1xufVxuXG4vKipcbiAqIEEgbmFtZWQgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9uICh0eXBlIGFsaWFzLCBjbGFzcywgb3IgaW50ZXJmYWNlKVxuICogcmVjb3JkZWQgcGVyIGZpbGUsIHNvIHJlZmVyZW5jZXMgY2FuIGJlIHJlc29sdmVkIHRocm91Z2ggdGhlIGltcG9ydGluZ1xuICogZmlsZSdzIG93biBpbXBvcnRzIGluc3RlYWQgb2YgYSBwcm9ncmFtLXdpZGUgbGFzdC13aW5zIG5hbWUgbWFwIChGMTApLlxuICovXG5pbnRlcmZhY2UgUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB7XG5cdGtpbmQ6ICdhbGlhcycgfCAnY2xhc3MnIHwgJ2ludGVyZmFjZSc7XG5cdG5vZGU6IHRzLlR5cGVBbGlhc0RlY2xhcmF0aW9uIHwgdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHRzLkludGVyZmFjZURlY2xhcmF0aW9uO1xuXHQvKiogZmlsZSB0aGF0IGRlY2xhcmVzIHRoZSB0eXBlIOKAlCBuZXN0ZWQgcmVmZXJlbmNlcyByZXNvbHZlIGFnYWluc3QgaXQgKi9cblx0ZmlsZTogc3RyaW5nO1xufVxuXG4vKipcbiAqIE9uZSBpbXBvcnQgYmluZGluZyBvZiBhIHJlZmVyZW5jZWQgdHlwZTogdGhlIGxvY2FsIG5hbWUgdW5kZXIgd2hpY2ggdGhlXG4gKiBmaWxlIGtub3dzIGl0LCB0aGUgb3JpZ2luYWwgZXhwb3J0ZWQgbmFtZSBpbiB0aGUgc291cmNlIG1vZHVsZSwgYW5kIHRoZVxuICogc3BlY2lmaWVyIGl0IGNhbWUgZnJvbS5cbiAqL1xuaW50ZXJmYWNlIFJlZmVyZW5jZWRUeXBlSW1wb3J0IHtcblx0b3JpZ2luYWxOYW1lOiBzdHJpbmc7XG5cdHNwZWNpZmllcjogc3RyaW5nO1xuXHRpc05hbWVzcGFjZTogYm9vbGVhbjtcbn1cblxuLyoqXG4gKiBSZXN1bHQgb2YgcmVzb2x2aW5nIG9uZSBtb2R1bGUgc3BlY2lmaWVyIGZyb20gb25lIGNvbnRhaW5pbmcgZmlsZS5cbiAqL1xuaW50ZXJmYWNlIFJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbiB7XG5cdHJlc29sdmVkUGF0aDogc3RyaW5nO1xuXHRpc0V4dGVybmFsOiBib29sZWFuO1xufVxuXG4vKipcbiAqIEdsb2JhbC9idWlsdGluIHR5cGUgbmFtZXMgdGhhdCBhcmUgc2FmZSB0byBlbWl0IGJhcmUgaW50byBnZW5lcmF0ZWQgZmlsZXNcbiAqIOKAlCB0aGV5IHJlc29sdmUgaW4gYW55IFR5cGVTY3JpcHQgY29tcGlsYXRpb24gd2l0aG91dCBhbiBpbXBvcnQuXG4gKi9cbmNvbnN0IEtOT1dOX0dMT0JBTF9UWVBFUyA9IG5ldyBTZXQoW1xuXHQnRGF0ZScsICdSZWdFeHAnLCAnRXJyb3InLCAnRXZhbEVycm9yJywgJ1JhbmdlRXJyb3InLCAnUmVmZXJlbmNlRXJyb3InLFxuXHQnU3ludGF4RXJyb3InLCAnVHlwZUVycm9yJywgJ1VSSUVycm9yJywgJ0FnZ3JlZ2F0ZUVycm9yJyxcblx0J01hcCcsICdTZXQnLCAnV2Vha01hcCcsICdXZWFrU2V0JywgJ1dlYWtSZWYnLCAnRmluYWxpemF0aW9uUmVnaXN0cnknLFxuXHQnUHJvbWlzZScsICdBcnJheScsICdSZWFkb25seUFycmF5JywgJ1JlY29yZCcsICdQYXJ0aWFsJywgJ1JlcXVpcmVkJyxcblx0J1JlYWRvbmx5JywgJ1BpY2snLCAnT21pdCcsICdFeGNsdWRlJywgJ0V4dHJhY3QnLCAnTm9uTnVsbGFibGUnLFxuXHQnUmV0dXJuVHlwZScsICdJbnN0YW5jZVR5cGUnLCAnUGFyYW1ldGVycycsICdDb25zdHJ1Y3RvclBhcmFtZXRlcnMnLFxuXHQnVGhpc1R5cGUnLCAnVGhpc1BhcmFtZXRlclR5cGUnLCAnT21pdFRoaXNQYXJhbWV0ZXInLFxuXHQnVXBwZXJjYXNlJywgJ0xvd2VyY2FzZScsICdDYXBpdGFsaXplJywgJ1VuY2FwaXRhbGl6ZScsXG5cdCdTdHJpbmcnLCAnTnVtYmVyJywgJ0Jvb2xlYW4nLCAnU3ltYm9sJywgJ0JpZ0ludCcsICdPYmplY3QnLCAnRnVuY3Rpb24nLFxuXHQnSXRlcmFibGUnLCAnSXRlcmF0b3InLCAnR2VuZXJhdG9yJywgJ0FzeW5jSXRlcmFibGUnLCAnQXN5bmNJdGVyYXRvcicsXG5cdCdBc3luY0dlbmVyYXRvcicsICdJdGVyYWJsZUl0ZXJhdG9yJywgJ0FzeW5jSXRlcmFibGVJdGVyYXRvcicsXG5cdCdQcm9wZXJ0eUtleScsICdBcnJheUJ1ZmZlcicsICdTaGFyZWRBcnJheUJ1ZmZlcicsICdEYXRhVmlldycsXG5cdCdJbnQ4QXJyYXknLCAnVWludDhBcnJheScsICdVaW50OENsYW1wZWRBcnJheScsICdJbnQxNkFycmF5Jyxcblx0J1VpbnQxNkFycmF5JywgJ0ludDMyQXJyYXknLCAnVWludDMyQXJyYXknLCAnRmxvYXQzMkFycmF5Jyxcblx0J0Zsb2F0NjRBcnJheScsICdCaWdJbnQ2NEFycmF5JywgJ0JpZ1VpbnQ2NEFycmF5JywgJ0ludGwnXG5dKTtcblxuLy8gQm91bmQgZm9yIGNoYXNpbmcgcmUtZXhwb3J0IGJhcnJlbHMgKGV4cG9ydCB7IFggfSBmcm9tICfigKYnLCBleHBvcnQgKiBmcm9tICfigKYnKVxuY29uc3QgTUFYX1JFRVhQT1JUX0NIQVNFX0RFUFRIID0gNTtcbi8vIEJvdW5kIGZvciB3YWxraW5nIGNsYXNzL2ludGVyZmFjZSBleHRlbmRzIGNoYWlucyBkdXJpbmcgcmVmZXJlbmNlZC10eXBlXG4vLyBleHBhbnNpb24gKGluaGVyaXRlZCBtZW1iZXJzIG1lcmdlIGludG8gdGhlIGV4cGFuZGVkIGZpZWxkcylcbmNvbnN0IE1BWF9IRVJJVEFHRV9ERVBUSCA9IDg7XG5cbi8qKlxuICogQVNUIEFuYWx5emVyIGZvciBmaW5kaW5nIE1uZW1vbmljYSBkZWZpbmUoKSBhbmQgZGVjb3JhdGUoKSBjYWxsc1xuICpcbiAqIEZyYW1ld29yay1ibGluZCBieSBjb25zdHJ1Y3Rpb246IGluc3RydW1lbnRhdGlvbiBkZXRlY3Rpb24gdm9jYWJ1bGFyeVxuICogKGludGVyZmFjZSBuYW1lcywgZGVjb3JhdG9yIG5hbWVzLCBwcm92aWRlciB0b2tlbnMsIG1pZGRsZXdhcmUgd2lyaW5nKVxuICogY29tZXMgZW50aXJlbHkgZnJvbSBwbHVnaW5zIOKAlCB3aXRoIG5vbmUgbG9hZGVkLCB6ZXJvIHBvaW50cyBhcmUgY29sbGVjdGVkLlxuICovXG5leHBvcnQgY2xhc3MgTW5lbW9uaWNhQW5hbHl6ZXIge1xuXHRwcml2YXRlIGVycm9yczogQW5hbHl6ZUVycm9yW10gPSBbXTtcblx0cHJpdmF0ZSBncmFwaCA9IG5ldyBUeXBlR3JhcGhJbXBsKCk7XG5cdHByaXZhdGUgZGVmaW5pdGlvbnMgPSBuZXcgTWFwPHN0cmluZywgRGVmaW5pdGlvbkluZm8+KCk7XG5cdHByaXZhdGUgdXNhZ2VzID0gbmV3IE1hcDxzdHJpbmcsIFVzYWdlSW5mb1tdPigpO1xuXHRwcml2YXRlIGVkc1VzYWdlcyA9IG5ldyBNYXA8c3RyaW5nLCBFRFNJbmZvW10+KCk7XG5cdHByaXZhdGUgZmxvd1VzYWdlcyA9IG5ldyBNYXA8c3RyaW5nLCBGbG93SW5mb1tdPigpO1xuXHQvLyBFbmNsb3NpbmcgbW5lbW9uaWNhIHNjb3BlIGZvciBFRFMga2V5aW5nOiBkZWZpbmUoKS9sYXp5KCkgY2FsbCBub2RlXG5cdC8vIG9yIEBkZWNvcmF0ZSgpLWVkIGNsYXNzIGRlY2xhcmF0aW9uIC0+IGZ1bGxQYXRoIG9mIHRoZSB0eXBlIGl0IG93bnMuXG5cdC8vIFBvcHVsYXRlZCBvbiB0aGUgZGVmaW5pdGlvbnMgcGFzczsgQVNUIG5vZGVzIHBlcnNpc3QgYWNyb3NzIHBhc3Nlcyxcblx0Ly8gc28gZW50cmllcyBzdGF5IHZhbGlkIGFmdGVyIHJlc2V0VXNhZ2VzKCkuXG5cdHByaXZhdGUgZWRzU2NvcGVCeU5vZGUgPSBuZXcgTWFwPHRzLk5vZGUsIHN0cmluZz4oKTtcblx0Ly8gU2FtZS1maWxlIGZ1bmN0aW9uIGJpbmRpbmdzIChgZmlsZU5hbWUjbmFtZWAgLT4gZnVuY3Rpb24gbm9kZSkgZm9yXG5cdC8vIHJlc29sdmluZyB3cmFwKGZuKSBhcmd1bWVudHMgc3ludGFjdGljYWxseSDigJQgdGhlIGNoZWNrZXIgc3RheXMgdW51c2VkXG5cdHByaXZhdGUgZnVuY3Rpb25CaW5kaW5ncyA9IG5ldyBNYXA8c3RyaW5nLCB0cy5GdW5jdGlvbkxpa2VEZWNsYXJhdGlvbj4oKTtcblx0Ly8gd3JhcCBjYWxsIG5vZGUgLT4gbG9jYXRpb24gb2YgdGhlIGVuY2xvc2luZyB3cmFwIHNpdGUgKHBsdXMgdGhhdFxuXHQvLyBzaXRlJ3Mgc2NvcGUgYXR0cmlidXRpb24pLCBzbyBuZXN0ZWQgd3JhcCgpIGNhbGxzIGluc2lkZSBhIHdyYXBwZWRcblx0Ly8gYm9keSBjYXJyeSB0aGUgYHZpYWAgbGluayDigJQgYW5kIGluaGVyaXQgdGhlIHNjb3BlIHdoZW4gdGhleSBoYXZlXG5cdC8vIG5vbmUgb2YgdGhlaXIgb3duXG5cdHByaXZhdGUgbmVzdGVkV3JhcFZpYSA9IG5ldyBNYXA8dHMuTm9kZSwgeyB2aWE6IHN0cmluZzsgc2NvcGU/OiBzdHJpbmcgfT4oKTtcblx0Ly8gd3JhcCBjYWxsIG5vZGUgLT4gaXRzIGNvbGxlY3RlZCBlbnRyeSwgc28gYSBsZXhpY2FsbHkgbmVzdGVkIHdyYXBcblx0Ly8gKHZpc2l0ZWQgQkVGT1JFIHRoZSBvdXRlciB3cmFwIGNhbGwsIHBlciBzb3VyY2Ugb3JkZXIpIGdldHMgaXRzXG5cdC8vIGB2aWFgIGJhY2stcGF0Y2hlZCB3aGVuIHRoZSBvdXRlciBib2R5IGlzIGFuYWx5c2VkXG5cdHByaXZhdGUgd3JhcEVudHJ5QnlOb2RlID0gbmV3IE1hcDx0cy5Ob2RlLCBFRFNJbmZvPigpO1xuXHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50czogdmFyaWFibGVOYW1lIC0+IGZ1bGxQYXRoIG9mIHRoZSB0eXBlIGl0IGhvbGRzXG5cdHByaXZhdGUgdmFyaWFibGVUb1R5cGVNYXAgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHQvLyBUcmFjayBtbmVtb25pY2EgbW9kdWxlLW9iamVjdCB2YXJpYWJsZXMgKGUuZy4sIGltcG9ydCB7IG1uZW1vbmljYSB9IGZyb20gJ21uZW1vbmljYSc7IGNvbnN0IG0gPSBtbmVtb25pY2EpXG5cdHByaXZhdGUgbW9kdWxlT2JqZWN0VmFyaWFibGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdC8vIGZpbGUgLT4gKGxvY2FsIG5hbWUgLT4gaW1wb3J0ZWQgbmFtZSkgZm9yIG5hbWVkIGltcG9ydHMgZnJvbVxuXHQvLyAnbW5lbW9uaWNhJyDigJQgaW1wb3J0LWF3YXJlbmVzcyBmb3IgdGhlIGNvbnN0cnVjdGlvbi1mdW5jdGlvblxuXHQvLyByZWNvZ25pdGlvbiAoY2FsbC9hcHBseS9iaW5kKSBhbmQgdGhlIHV0aWxzIGZvcm1zIChtZXJnZS9mb3JrKTpcblx0Ly8gdXNlcmxhbmQgZnVuY3Rpb25zIHdpdGggdGhvc2UgbmFtZXMgbXVzdCBuZXZlciBtYXRjaFxuXHRwcml2YXRlIG1uZW1vbmljYU5hbWVkSW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBUcmFjayBpbXBvcnRlZCBhbGlhc2VzIG9mIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbiAoZS5nLiwgaW1wb3J0IHsgY3JlYXRlVHlwZXNDb2xsZWN0aW9uIGFzIGN0YyB9KVxuXHRwcml2YXRlIGNyZWF0ZVR5cGVzQ29sbGVjdGlvblZhcmlhYmxlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHQvLyBUcmFjayBjdXN0b20gY29sbGVjdGlvbiB2YXJpYWJsZXM6IHZhcmlhYmxlTmFtZSAtPiBjb2xsZWN0aW9uSWRcblx0cHJpdmF0ZSBjb2xsZWN0aW9uVmFyaWFibGVzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblx0Ly8gVHJhY2sgY3VzdG9tIGNvbGxlY3Rpb24gbWV0YWRhdGEgZm9yIE9wdGlvbiBCIHJlZ2lzdHJ5IGVtaXNzaW9uXG5cdHByaXZhdGUgY29sbGVjdGlvbkluZm8gPSBuZXcgTWFwPHN0cmluZywgQ29sbGVjdGlvbkluZm8+KCk7XG5cdHByaXZhdGUgY29sbGVjdGlvbkNvdW50ZXIgPSAwO1xuXHQvLyBJbnN0cnVtZW50YXRpb24gY29sbGVjdGlvbiAoc3ludGFjdGljIG9ubHkg4oCUIG5vIHR5cGUgY2hlY2tlcik6XG5cdC8vIGV2ZXJ5IG5hbWVkIGNsYXNzIGRlY2xhcmF0aW9uIGJ5IHNpbXBsZSBuYW1lLCBmb3IgcmVzb2x2aW5nXG5cdC8vIHJlZ2lzdHJhdGlvbiBzaXRlcyB0byBkZWNsYXJhdGlvbiBsb2NhdGlvbnMgKGJlc3QgZWZmb3J0LCBsYXN0IHdpbnMpXG5cdHByaXZhdGUgaW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNscyA9IG5ldyBNYXA8c3RyaW5nLCBJbnN0cnVtZW50YXRpb25DbGFzc0RlY2w+KCk7XG5cdC8vIFJlZ2lzdHJhdGlvbiBzaXRlczogZGVjb3JhdG9yIGFwcGxpY2F0aW9ucywgcHJvdmlkZXItdG9rZW4gb2JqZWN0XG5cdC8vIGxpdGVyYWxzLCBjb25zdW1lci5hcHBseSgpIG1pZGRsZXdhcmUgd2lyaW5nXG5cdHByaXZhdGUgaW5zdHJ1bWVudGF0aW9uU2l0ZXM6IEluc3RydW1lbnRhdGlvblNpdGVbXSA9IFtdO1xuXHQvLyBNZXJnZWQgcGx1Z2luIHZvY2FidWxhcnkgZm9yIGluc3RydW1lbnRhdGlvbiBkZXRlY3Rpb24gKGVtcHR5IHdoZW5cblx0Ly8gbm8gcGx1Z2lucyB3ZXJlIHBhc3NlZCDigJQgdGhlIGFuYWx5emVyIHRoZW4gY29sbGVjdHMgbm8gcG9pbnRzKVxuXHRwcml2YXRlIGluc3RydW1lbnRhdGlvblZvY2FidWxhcnk6IEluc3RydW1lbnRhdGlvblZvY2FidWxhcnk7XG5cdC8vIFJlZmVyZW5jZWQtdHlwZSByZXNvbHV0aW9uIChGMTApOiBwZXItZmlsZSBkZWNsYXJhdGlvbnMgYW5kIGltcG9ydHMuXG5cdC8vIEEgdHlwZSBuYW1lIHVzZWQgaW4gZmlsZSBYIHJlc29sdmVzIHRocm91Z2ggWCdzIG93biBpbXBvcnQgc3RhdGVtZW50c1xuXHQvLyBmaXJzdCAocmVsYXRpdmUgKyB0c2NvbmZpZy1wYXRocywgdmlhIHRzLnJlc29sdmVNb2R1bGVOYW1lKSwgdGhlblxuXHQvLyBYJ3MgbG9jYWwgZGVjbGFyYXRpb25zLCB0aGVuIOKAlCBvbmx5IHdoZW4gbm90aGluZyBpbXBvcnRzIG9yIGRlY2xhcmVzXG5cdC8vIHRoZSBuYW1lIOKAlCB0aGUgdW5pcXVlIHNhbWUtbmFtZWQgZGVjbGFyYXRpb24gYWNyb3NzIHNjYW5uZWQgZmlsZXMuXG5cdC8vIEdlbnVpbmUgYW1iaWd1aXR5IG9yIGFuIHVucmVzb2x2YWJsZSByZWZlcmVuY2UgeWllbGRzIGB1bmtub3duYCwgbmV2ZXJcblx0Ly8gYSBiYXJlIGVtaXR0ZWQgbmFtZTogZ2VuZXJhdGVkIHR5cGVzLnRzIGNhcnJpZXMgbm8gaW1wb3J0cyBvZiBpdHMgb3duLlxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlRGVjbHMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbj4+KCk7XG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVJbXBvcnRzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlSW1wb3J0Pj4oKTtcblx0Ly8gZmlsZSAtPiAoZXhwb3J0ZWQgbmFtZSAtPiByZS1leHBvcnQgc3BlY2lmaWVyKSBmb3IgYGV4cG9ydCB7IFggfSBmcm9tICfigKYnYFxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHN0cmluZz4+KCk7XG5cdC8vIGZpbGUgLT4gc3BlY2lmaWVycyBvZiBgZXhwb3J0ICogZnJvbSAn4oCmJ2Bcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZUV4cG9ydFN0YXJzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZ1tdPigpO1xuXHQvLyBmaWxlIC0+IChleHBvcnRlZCBuYW1lIC0+IGxvY2FsIG5hbWUpIGZvciBgZXhwb3J0IHsgWCBhcyBZIH1gXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVFeHBvcnRBbGlhc2VzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIHN0cmluZz4+KCk7XG5cdC8vIGZpbGUgLT4gKG5hbWVzcGFjZSBuYW1lIC0+IG5hbWVzcGFjZSBkZWNsYXJhdGlvbikg4oCUIG1pZGRsZSBzZWdtZW50c1xuXHQvLyBvZiBxdWFsaWZpZWQgcmVmZXJlbmNlcyAobW9kZWxzLklubmVyLkNyYXRlKSBkZXNjZW5kIHRocm91Z2ggdGhlc2Vcblx0cHJpdmF0ZSByZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgdHMuTW9kdWxlRGVjbGFyYXRpb24+PigpO1xuXHQvLyBmaWxlIC0+IChuYW1lc3BhY2UgbmFtZSAtPiBzcGVjaWZpZXIpIGZvciBgZXhwb3J0ICogYXMgbnMgZnJvbSAn4oCmJ2Bcblx0Ly8gYmFycmVscyDigJQgYSBuZXN0ZWQgbW9kdWxlIG5hbWVzcGFjZSBvbmUgc2VnbWVudCBkZWVwXG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VTdGFycyA9IG5ldyBNYXA8c3RyaW5nLCBNYXA8c3RyaW5nLCBzdHJpbmc+PigpO1xuXHQvLyBgJHtjb250YWluaW5nRmlsZX06OiR7c3BlY2lmaWVyfWAgLT4gcmVzb2x1dGlvbiAodW5kZWZpbmVkID0gZmFpbGVkKVxuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbkNhY2hlID0gbmV3IE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbiB8IHVuZGVmaW5lZD4oKTtcblx0Ly8gZmlsZSAtPiAoY29uc3QgbmFtZSAtPiBhcnJheSBsaXRlcmFsKSBmb3IgY29uc3RzIHdpdGggYXJyYXktbGl0ZXJhbFxuXHQvLyBpbml0aWFsaXplcnMgKGBhcyBjb25zdGAgLyBgc2F0aXNmaWVzYCB1bndyYXBwZWQpLCBzbyBhXG5cdC8vIGB0eXBlb2Ygc3RhdHVzTGlzdFtudW1iZXJdYCBmaWVsZCB0eXBlIGV4cGFuZHMgdG8gdGhlIGVsZW1lbnQgbGl0ZXJhbFxuXHQvLyB1bmlvbiBpbnN0ZWFkIG9mIGxlYWtpbmcgYSBiYXJlIHVucmVzb2x2YWJsZSBgdHlwZW9mYCBxdWVyeSBpbnRvIHRoZVxuXHQvLyBnZW5lcmF0ZWQgZmlsZS4gRGVjbGFyYXRpb25zIHBlcnNpc3QgYWNyb3NzIHBhc3NlcyDigJQgZW50cmllcyBzdGF5XG5cdC8vIHZhbGlkIGFmdGVyIHJlc2V0VXNhZ2VzKCksIHNhbWUgYXMgcmVmZXJlbmNlZFR5cGVEZWNsc1xuXHRwcml2YXRlIHJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgdHMuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbj4+KCk7XG5cdHByaXZhdGUgcmVmZXJlbmNlZFR5cGVDb21waWxlck9wdGlvbnM6IHRzLkNvbXBpbGVyT3B0aW9ucztcblx0Ly8gRmlsZSB3aG9zZSBBU1QgaXMgY3VycmVudGx5IGJlaW5nIHZpc2l0ZWQ7IHJlZmVyZW5jZXMgcmVzb2x2ZSBhZ2FpbnN0IGl0XG5cdHByaXZhdGUgY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9ICcnO1xuXHQvLyBBbGlhcyBuYW1lcyBjdXJyZW50bHkgYmVpbmcgZXhwYW5kZWQgKGN5Y2xlIGd1YXJkKVxuXHRwcml2YXRlIGV4cGFuZGluZ1JlZmVyZW5jZWRBbGlhc2VzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdC8vIE1uZW1vbmljYS1ncmFwaCBpZGVudGl0eSBsYXcgKGhhcmQgZmFpbCk6IGV2ZXJ5IGRlZmluZSgpL2xhenkoKS9cblx0Ly8gQGRlY29yYXRlKCkgc2l0ZSBrZXllZCBieSBpdHMgcnVudGltZSBuYW1lc3BhY2UgKGNvbGxlY3Rpb24gcm9vdHM6XG5cdC8vIGA8Y29sbGVjdGlvbj46OjxuYW1lPmA7IHN1YnR5cGVzOiBgPHBhcmVudEZ1bGxQYXRoPi48bmFtZT5gKS4gVHdvXG5cdC8vIHNpdGVzIGluIG9uZSBuYW1lc3BhY2UgYXJlIGEgc2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlIOKAlCB0aGUgcnVudGltZVxuXHQvLyB0aHJvd3MgQUxSRUFEWV9ERUNMQVJFRCDigJQgYW5kIG11c3QgYWJvcnQgZ2VuZXJhdGlvbi5cblx0cHJpdmF0ZSBkZWZpbmVTaXRlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmdbXT4oKTtcblx0Ly8gTW5lbW9uaWNhLWdyYXBoIHJlZmVyZW5jZXMgdGhhdCBzdGF5ZWQgYW1iaWd1b3VzIGFmdGVyIHBhdGgtYXdhcmVcblx0Ly8gcmVzb2x1dGlvbiBvciByZXNvbHZlZCB0byBub3RoaW5nIChoYXJkLWZhaWwgY2xhc3MgMilcblx0cHJpdmF0ZSBncmFwaFJlZmVyZW5jZUVycm9yczogUmVzb2x1dGlvbkVycm9yW10gPSBbXTtcblx0Ly8gR3VhcmRzIGxvb2t1cCgpLXBhdGggdmFsaWRhdGlvbiBzbyBpdCBydW5zIG9uY2UgcGVyIHVzYWdlcyBwYXNzXG5cdC8vIChnZXRSZXNvbHV0aW9uRXJyb3JzIG1heSBiZSBjYWxsZWQgcmVwZWF0ZWRseSk7IHJlc2V0VXNhZ2VzIHJlLWFybXMgaXRcblx0cHJpdmF0ZSBsb29rdXBSZWZlcmVuY2VzVmFsaWRhdGVkID0gZmFsc2U7XG5cdC8vIExpdGVyYWwgbG9va3VwKCkgY2FsbCBzaXRlcyB3aXRoIHRoZWlyIHJlc29sdmVkIHBhdGhzLiBLZXB0IGFwYXJ0IGZyb21cblx0Ly8gdGhlIHVzYWdlcyBtYXAgb24gcHVycG9zZTogYWRkVXNhZ2UgZHJvcHMgcGF0aHMgdGhlIGdyYXBoIGRvZXMgbm90XG5cdC8vIGtub3cgKHVzYWdlcy5qc29uIGluZGV4ZXMgcmVmZXJlbmNlcyB0byBLTk9XTiB0eXBlcyksIGJ1dCBhbiB1bmtub3duXG5cdC8vIGxvb2t1cCBwYXRoIGlzIGV4YWN0bHkgdGhlIGhhcmQtZmFpbCBjYXNlIOKAlCB0aGUgcnVudGltZSByZXR1cm5zXG5cdC8vIHVuZGVmaW5lZCB0aGVyZSBhbmQgdGhlIFR5cGVFcnJvciBhcnJpdmVzIG9uZSBsaW5lIGxhdGVyXG5cdHByaXZhdGUgbG9va3VwUmVmZXJlbmNlczogeyBwYXRoOiBzdHJpbmc7IGxvY2F0aW9uOiBzdHJpbmcgfVtdID0gW107XG5cdC8vIEd1YXJkcyBwbGFpbi1UUyByZWZlcmVuY2UgdmFsaWRhdGlvbiBzbyBpdCBydW5zIG9uY2UgcGVyIHVzYWdlcyBwYXNzXG5cdC8vIChnZXRSZXNvbHV0aW9uRXJyb3JzIG1heSBiZSBjYWxsZWQgcmVwZWF0ZWRseSk7IHJlc2V0VXNhZ2VzIHJlLWFybXMgaXRcblx0cHJpdmF0ZSBwbGFpblR5cGVSZWZlcmVuY2VzVmFsaWRhdGVkID0gZmFsc2U7XG5cdC8vIFBsYWluLVRTIHR5cGUgcmVmZXJlbmNlIHNpdGVzIHdob3NlIHJlc29sdXRpb24gZmVsbCB0aHJvdWdoIGltcG9ydHMsXG5cdC8vIGxvY2FscywgdGhlIHByb2dyYW0td2lkZSBzY2FuLCBhbmQgdGhlIGdyYXBoIHRvIGEgc29mdCBgdW5rbm93bmAuXG5cdC8vIFZhbGlkYXRlZCBsYXppbHkgZnJvbSBnZXRSZXNvbHV0aW9uRXJyb3JzIGFnYWluc3QgdGhlIGNvbXBsZXRlXG5cdC8vIGRlY2xhcmF0aW9uIG1hcDogYSBuYW1lIHNldmVyYWwgcHJvamVjdC1zb3VyY2UgZmlsZXMgZGVjbGFyZSDigJQgd2l0aFxuXHQvLyBubyBpbXBvcnQgaW4gdGhlIHJlZmVyZW5jaW5nIGZpbGUgdG8gYW5jaG9yIGl0IOKAlCBpcyB0aGUgcGxhaW4tVFNcblx0Ly8gYW1iaWd1aXR5IGhhcmQtZmFpbCBjbGFzcyAob25lIHRpZXIgYmVsb3cgdGhlIGdyYXBoIGlkZW50aXR5IGxhdyk7XG5cdC8vIGFic2VuY2UgKGdob3N0IG5hbWVzKSBzdGF5cyBzb2Z0LiBSZWNvcmRpbmcgaGFwcGVucyBvbiBldmVyeSBwYXNzLFxuXHQvLyB0aGUgdmVyZGljdCBvbmx5IGhlcmUg4oCUIHBhc3MgMSBzZWVzIGFuIGluY29tcGxldGUgZGVjbGFyYXRpb24gbWFwLFxuXHQvLyBzbyBvbmx5IHRoZSB1c2FnZXMgcGFzcyBpcyBhdXRob3JpdGF0aXZlIChtaXJyb3JzIGxvb2t1cCByZWZlcmVuY2VzKVxuXHRwcml2YXRlIHBsYWluVHlwZVJlZmVyZW5jZXM6IHsgbmFtZTogc3RyaW5nOyBsb2NhdGlvbjogc3RyaW5nOyBmaWxlOiBzdHJpbmcgfVtdID0gW107XG5cdC8vIFBlci1maWxlIHRvcC1sZXZlbCB2YXJpYWJsZSAtPiBtbmVtb25pY2EgZnVsbFBhdGggYmluZGluZ3MgKHZhbHVlXG5cdC8vIHNjb3BlKTogYGNvbnN0IEFkZHJlc3MgPSBVc2VyLmRlZmluZSgnQWRkcmVzcycsIOKApilgIG1ha2VzIGBBZGRyZXNzYFxuXHQvLyBkZW5vdGUgVXNlci5BZGRyZXNzIHdoZXJldmVyIHRoYXQgZmlsZSdzIHJlZmVyZW5jZXMgYXJlIHJlc29sdmVkXG5cdHByaXZhdGUgZmlsZUdyYXBoQmluZGluZ3MgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgc3RyaW5nPj4oKTtcblx0Ly8gVGhlIGdyYXBoIHR5cGUgd2hvc2UgY29uc3RydWN0b3IgaXMgY3VycmVudGx5IGJlaW5nIGV4dHJhY3RlZDtcblx0Ly8gYW5jaG9ycyByZWxhdGl2ZS1maXJzdCBncmFwaCByZWZlcmVuY2UgcmVzb2x1dGlvblxuXHRwcml2YXRlIGN1cnJlbnRHcmFwaEFuY2hvcjogVHlwZU5vZGUgfCB1bmRlZmluZWQ7XG5cdC8vIGRlZmluZSgpL2xhenkoKSBjYWxscyBhbHJlYWR5IGV4dHJhY3RlZCB0aGlzIHBhc3MuIFRoZSBDTEkgcmUtYW5hbHl6ZXNcblx0Ly8gZXZlcnkgZmlsZSBhZnRlciByZXNldFVzYWdlcygpOyBjbGVhcmluZyB0aGUgc2V0IGxldHMgdGhlIHNlY29uZCBwYXNzXG5cdC8vIHJlLWV4dHJhY3QgZXZlcnkgY29uc3RydWN0b3IgYWdhaW5zdCB0aGUgQ09NUExFVEUgZ3JhcGgg4oCUIHBhc3MgMSBzZWVzXG5cdC8vIGZvcndhcmQgcmVmZXJlbmNlcyBhcyBgbm9uZWAgKHNvZnQgdW5rbm93bikgYmVjYXVzZSBsYXRlciBmaWxlcyBoYXZlXG5cdC8vIG5vdCBiZWVuIHZpc2l0ZWQgeWV0LCBzbyBvbmx5IHBhc3MtMiByZXNvbHV0aW9uIGlzIGF1dGhvcml0YXRpdmUgZm9yXG5cdC8vIHRoZSBoYXJkLWZhaWwgaWRlbnRpdHkgbGF3LiBUaGUgc3RhbXAgbGl2ZXMgaGVyZSByYXRoZXIgdGhhbiBvbiB0aGVcblx0Ly8gQVNUIG5vZGUgc28gaXQgY2FuIGFjdHVhbGx5IGJlIGNsZWFyZWQuIChDaGFpbmVkIGNhbGxzIHZpc2l0IHRoZSBzYW1lXG5cdC8vIG5vZGUgdHdpY2Ugd2l0aGluIG9uZSBwYXNzOyB0aGUgaW4tcGFzcyBkZWR1cCBiZWxvdyBzdGF5cy4pXG5cdHByaXZhdGUgcHJvY2Vzc2VkQ2FsbHMgPSBuZXcgU2V0PHRzLkNhbGxFeHByZXNzaW9uPigpO1xuXG5cdGNvbnN0cnVjdG9yIChwcm9ncmFtPzogdHMuUHJvZ3JhbSwgcGx1Z2luczogVGFjdGljYVBsdWdpbltdID0gW10pIHtcblx0XHQvLyBDb21waWxlciBvcHRpb25zIGRyaXZlIHRzLnJlc29sdmVNb2R1bGVOYW1lIGZvciBpbXBvcnQtYXdhcmVcblx0XHQvLyByZWZlcmVuY2VkLXR5cGUgcmVzb2x1dGlvbiAodHNjb25maWcgYHBhdGhzYCwgZXh0ZW5zaW9ubGVzc1xuXHRcdC8vIGltcG9ydHMpOyB0aGUgdHlwZSBjaGVja2VyIGl0c2VsZiBzdGF5cyB1bnVzZWQuXG5cdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUNvbXBpbGVyT3B0aW9ucyA9IHByb2dyYW0/LmdldENvbXBpbGVyT3B0aW9ucygpID8/IHt9O1xuXHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeSA9IG1lcmdlVGFjdGljYVBsdWdpbnMocGx1Z2lucyk7XG5cdH1cblxuXHQvKipcblx0ICogUmVzZXQgdXNhZ2UtcmVsYXRlZCBzdGF0ZSBmb3IgYSBmcmVzaCBwYXNzLlxuXHQgKiBDYWxsIGJlZm9yZSB0aGUgdXNhZ2UtY29sbGVjdGlvbiBwYXNzIHRvIGF2b2lkIGR1cGxpY2F0ZXMgZnJvbSBkZWZpbml0aW9uIHBhc3MuXG5cdCAqL1xuXHRyZXNldFVzYWdlcyAoKTogdm9pZCB7XG5cdFx0dGhpcy51c2FnZXMuY2xlYXIoKTtcblx0XHR0aGlzLmVkc1VzYWdlcy5jbGVhcigpO1xuXHRcdHRoaXMuZmxvd1VzYWdlcy5jbGVhcigpO1xuXHRcdHRoaXMudmFyaWFibGVUb1R5cGVNYXAuY2xlYXIoKTtcblx0XHQvLyBFRFMgZW50cnkgcmVmZXJlbmNlcyBnbyBzdGFsZSB3aXRoIGVkc1VzYWdlczsgdmlhIGxpbmtzIGFyZVxuXHRcdC8vIHJlLWRlcml2ZWQgb24gdGhlIG5leHQgcGFzc1xuXHRcdHRoaXMud3JhcEVudHJ5QnlOb2RlLmNsZWFyKCk7XG5cdFx0dGhpcy5uZXN0ZWRXcmFwVmlhLmNsZWFyKCk7XG5cdFx0Ly8gTm90ZTogbW9kdWxlT2JqZWN0VmFyaWFibGVzIGFuZCBjb2xsZWN0aW9uVmFyaWFibGVzIGludGVudGlvbmFsbHkgcGVyc2lzdFxuXHRcdC8vIGFjcm9zcyBkZWZpbml0aW9uIGFuZCB1c2FnZSBwYXNzZXMuXG5cdFx0Ly8gUmUtZXh0cmFjdGlvbiBpbiB0aGUgdXNhZ2VzIHBhc3MgaXMgd2hhdCBtYWtlcyBncmFwaCByZWZlcmVuY2Vcblx0XHQvLyByZXNvbHV0aW9uIGF1dGhvcml0YXRpdmU6IHBhc3MgMSByZXNvbHZlcyBhZ2FpbnN0IGFuIGluY29tcGxldGVcblx0XHQvLyBncmFwaCAoZm9yd2FyZCByZWZlcmVuY2VzIHJlYWQgYXMgYG5vbmVgKSwgcGFzcyAyIGFnYWluc3QgYWxsIG9mIGl0LlxuXHRcdHRoaXMucHJvY2Vzc2VkQ2FsbHMuY2xlYXIoKTtcblx0XHQvLyBsb29rdXAoKS1wYXRoIHZhbGlkYXRpb24gcnVucyBhZ2FpbnN0IHRoZSByZWNvcmRlZCBzaXRlczsgYSBmcmVzaFxuXHRcdC8vIHBhc3MgbXVzdCByZS1yZWNvcmQgYW5kIHJlLXZhbGlkYXRlIChwYXNzLTEgcmVzdWx0cyB3b3VsZCBiZVxuXHRcdC8vIHByZW1hdHVyZSDigJQgdGhlIGdyYXBoIGlzIHN0aWxsIGluY29tcGxldGUpXG5cdFx0dGhpcy5sb29rdXBSZWZlcmVuY2VzVmFsaWRhdGVkID0gZmFsc2U7XG5cdFx0dGhpcy5sb29rdXBSZWZlcmVuY2VzID0gW107XG5cdFx0dGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzVmFsaWRhdGVkID0gZmFsc2U7XG5cdFx0dGhpcy5wbGFpblR5cGVSZWZlcmVuY2VzID0gW107XG5cdH1cblxuXHQvKipcblx0ICogQW5hbHl6ZSBhIHNvdXJjZSBmaWxlIGZvciBNbmVtb25pY2EgdHlwZSBkZWZpbml0aW9uc1xuXHQgKi9cblx0YW5hbHl6ZUZpbGUgKHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiBBbmFseXplUmVzdWx0IHtcblx0XHR0aGlzLmVycm9ycyA9IFtdO1xuXHRcdC8vIFJlZmVyZW5jZWQtdHlwZSBuYW1lcyBpbiB0aGlzIGZpbGUgcmVzb2x2ZSBhZ2FpbnN0IGl0cyBvd24gaW1wb3J0c1xuXHRcdHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9IG5vZGVQYXRoLnJlc29sdmUoc291cmNlRmlsZS5maWxlTmFtZSk7XG5cdFx0Ly8gRW5zdXJlIHBhcmVudCBub2RlcyBhcmUgc2V0IGZvciBBU1QgdHJhdmVyc2FsXG5cdFx0dGhpcy5zZXRQYXJlbnROb2Rlc0luU291cmNlRmlsZShzb3VyY2VGaWxlKTtcblx0XHR0aGlzLnZpc2l0Tm9kZShzb3VyY2VGaWxlLCBzb3VyY2VGaWxlKTtcblxuXHRcdHJldHVybiB7XG5cdFx0XHR0eXBlcyAgOiB0aGlzLmdyYXBoLmdldEFsbFR5cGVzKCksXG5cdFx0XHRlcnJvcnMgOiB0aGlzLmVycm9ycyxcblx0XHR9O1xuXHR9XG5cblx0LyoqXG5cdCAqIEFuYWx5emUgc291cmNlIGNvZGUgc3RyaW5nXG5cdCAqL1xuXHRhbmFseXplU291cmNlIChzb3VyY2VDb2RlOiBzdHJpbmcsIGZpbGVOYW1lID0gJ3RlbXAudHMnKTogQW5hbHl6ZVJlc3VsdCB7XG5cdFx0Y29uc3Qgc291cmNlRmlsZSA9IHRzLmNyZWF0ZVNvdXJjZUZpbGUoXG5cdFx0XHRmaWxlTmFtZSxcblx0XHRcdHNvdXJjZUNvZGUsXG5cdFx0XHR0cy5TY3JpcHRUYXJnZXQuTGF0ZXN0LFxuXHRcdFx0dHJ1ZVxuXHRcdCk7XG5cdFx0cmV0dXJuIHRoaXMuYW5hbHl6ZUZpbGUoc291cmNlRmlsZSk7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IHRoZSB0eXBlIGdyYXBoXG5cdCAqL1xuXHRnZXRHcmFwaCAoKTogVHlwZUdyYXBoSW1wbCB7XG5cdFx0cmV0dXJuIHRoaXMuZ3JhcGg7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBkZWZpbml0aW9uc1xuXHQgKi9cblx0Z2V0RGVmaW5pdGlvbnMgKCk6IE1hcDxzdHJpbmcsIERlZmluaXRpb25JbmZvPiB7XG5cdFx0cmV0dXJuIHRoaXMuZGVmaW5pdGlvbnM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCB1c2FnZXNcblx0ICovXG5cdGdldFVzYWdlcyAoKTogTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+IHtcblx0XHRyZXR1cm4gdGhpcy51c2FnZXM7XG5cdH1cblxuXHQvKipcblx0ICogR2V0IGNvbGxlY3RlZCBFRFMgdXNhZ2VzXG5cdCAqL1xuXHRnZXRFRFNVc2FnZXMgKCk6IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4ge1xuXHRcdHJldHVybiB0aGlzLmVkc1VzYWdlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGZsb3cgdXNhZ2VzXG5cdCAqL1xuXHRnZXRGbG93VXNhZ2VzICgpOiBNYXA8c3RyaW5nLCBGbG93SW5mb1tdPiB7XG5cdFx0cmV0dXJuIHRoaXMuZmxvd1VzYWdlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgY29sbGVjdGVkIGluc3RydW1lbnRhdGlvbiBwb2ludHMuXG5cdCAqIFJlZ2lzdHJhdGlvbiBzaXRlcyByZWZlcmVuY2luZyBhIGNsYXNzIGRlY2xhcmVkIGluIHRoZSBzYW1lIHByb2plY3Rcblx0ICogcmVzb2x2ZSB0byB0aGUgY2xhc3MgZGVjbGFyYXRpb24ncyBsb2NhdGlvbi9jb2RlOyBleHRlcm5hbCBjbGFzc2VzXG5cdCAqIChlLmcuLCBhIGZyYW1ld29yay1idWlsdGluIGltcGxlbWVudGF0aW9uIGZyb20gbm9kZV9tb2R1bGVzKSBrZWVwXG5cdCAqIHRoZSByZWdpc3RyYXRpb24gc2l0ZS5cblx0ICogRGVkdXBlZCBieSBraW5kK2NsYXNzTmFtZStsb2NhdGlvbitzY29wZSB3aXRoIHRhcmdldHMgbWVyZ2VkIOKAlCBhXG5cdCAqIGNsYXNzIGRldGVjdGVkIGJ5IGhlcml0YWdlIEFORCBieSBhIGRlY29yYXRvciBzaXRlIHlpZWxkcyBzZXBhcmF0ZVxuXHQgKiBlbnRyaWVzIHdpdGggZGlzdGluY3Qgc2NvcGVzIChzZWUgSW5zdHJ1bWVudGF0aW9uUG9pbnQgaW4gdHlwZXMudHMpLlxuXHQgKi9cblx0Z2V0SW5zdHJ1bWVudGF0aW9uUG9pbnRzICgpOiBJbnN0cnVtZW50YXRpb25Qb2ludFtdIHtcblx0XHRjb25zdCBwb2ludHMgPSBuZXcgTWFwPHN0cmluZywgSW5zdHJ1bWVudGF0aW9uUG9pbnQ+KCk7XG5cblx0XHRjb25zdCBhZGRQb2ludCA9IChwb2ludDogSW5zdHJ1bWVudGF0aW9uUG9pbnQpOiB2b2lkID0+IHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3BvaW50LmtpbmR9fCR7cG9pbnQuY2xhc3NOYW1lfXwke3BvaW50LmxvY2F0aW9ufXwke3BvaW50LnNjb3BlfWA7XG5cdFx0XHRjb25zdCBleGlzdGluZyA9IHBvaW50cy5nZXQoa2V5KTtcblx0XHRcdGlmIChleGlzdGluZykge1xuXHRcdFx0XHRjb25zdCBtZXJnZWQgPSBuZXcgU2V0KFsgLi4uZXhpc3RpbmcudGFyZ2V0cywgLi4ucG9pbnQudGFyZ2V0cyBdKTtcblx0XHRcdFx0ZXhpc3RpbmcudGFyZ2V0cyA9IEFycmF5LmZyb20obWVyZ2VkKTtcblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0cG9pbnRzLnNldChrZXksIHBvaW50KTtcblx0XHR9O1xuXG5cdFx0Zm9yIChjb25zdCBzaXRlIG9mIHRoaXMuaW5zdHJ1bWVudGF0aW9uU2l0ZXMpIHtcblx0XHRcdGNvbnN0IGRlY2wgPSB0aGlzLmluc3RydW1lbnRhdGlvbkNsYXNzRGVjbHMuZ2V0KHNpdGUuY2xhc3NOYW1lKTtcblx0XHRcdGNvbnN0IHBvaW50OiBJbnN0cnVtZW50YXRpb25Qb2ludCA9IHtcblx0XHRcdFx0a2luZCAgICAgIDogc2l0ZS5raW5kLFxuXHRcdFx0XHRjbGFzc05hbWUgOiBzaXRlLmNsYXNzTmFtZSxcblx0XHRcdFx0bG9jYXRpb24gIDogZGVjbCA/IGRlY2wubG9jYXRpb24gOiBzaXRlLmxvY2F0aW9uLFxuXHRcdFx0XHRjb2RlICAgICAgOiBkZWNsID8gZGVjbC5jb2RlIDogc2l0ZS5jb2RlLFxuXHRcdFx0XHRzY29wZSAgICAgOiBzaXRlLnNjb3BlLFxuXHRcdFx0XHR0YXJnZXRzICAgOiBzaXRlLnRhcmdldHMsXG5cdFx0XHR9O1xuXHRcdFx0YWRkUG9pbnQocG9pbnQpO1xuXHRcdH1cblxuXHRcdC8vIEhlcml0YWdlLWRlY2xhcmVkIGNsYXNzZXMgYWx3YXlzIGVtaXQgYSBkZWNsYXJhdGlvbiBwb2ludCB3aXRoXG5cdFx0Ly8gc2NvcGUgJ21vZHVsZScgKGF0dGFjaG1lbnQgc3RhdGljYWxseSB1bmtub3duKTsgcmVnaXN0cmF0aW9uXG5cdFx0Ly8gc2l0ZXMgYWJvdmUgY2FycnkgdGhlIG5hcnJvd2VyIHNjb3BlcyBhcyBzZXBhcmF0ZSBlbnRyaWVzXG5cdFx0Zm9yIChjb25zdCBbIGNsYXNzTmFtZSwgZGVjbCBdIG9mIHRoaXMuaW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNscykge1xuXHRcdFx0aWYgKCFkZWNsLmtpbmQpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBwb2ludDogSW5zdHJ1bWVudGF0aW9uUG9pbnQgPSB7XG5cdFx0XHRcdGtpbmQgICAgICA6IGRlY2wua2luZCxcblx0XHRcdFx0Y2xhc3NOYW1lIDogY2xhc3NOYW1lLFxuXHRcdFx0XHRsb2NhdGlvbiAgOiBkZWNsLmxvY2F0aW9uLFxuXHRcdFx0XHRjb2RlICAgICAgOiBkZWNsLmNvZGUsXG5cdFx0XHRcdHNjb3BlICAgICA6ICdtb2R1bGUnLFxuXHRcdFx0XHR0YXJnZXRzICAgOiBbXSxcblx0XHRcdH07XG5cdFx0XHRhZGRQb2ludChwb2ludCk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVzdWx0ID0gQXJyYXkuZnJvbShwb2ludHMudmFsdWVzKCkpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogQWRkIGEgdG9wb2xvZ2ljYSB0eXBlIHRvIHRoZSBhbmFseXplciBmb3IgdXNhZ2UgdHJhY2tpbmcuXG5cdCAqIFRoaXMgYWxsb3dzIHRoZSBhbmFseXplciB0byByZWNvZ25pemUgdG9wb2xvZ2ljYSB0eXBlcyB3aGVuIGNvbGxlY3RpbmcgdXNhZ2VzLlxuXHQgKi9cblx0YWRkVG9wb2xvZ2ljYVR5cGUgKGZ1bGxQYXRoOiBzdHJpbmcsIG5vZGU6IGltcG9ydCgnLi90eXBlcycpLlR5cGVOb2RlKTogdm9pZCB7XG5cdFx0Ly8gU2tpcCBpZiBhbHJlYWR5IGV4aXN0c1xuXHRcdGlmICh0aGlzLmdyYXBoLmFsbFR5cGVzLmhhcyhmdWxsUGF0aCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGggc28gaXQgY2FuIGJlIGZvdW5kIGR1cmluZyB1c2FnZSBjb2xsZWN0aW9uXG5cdFx0aWYgKG5vZGUucGFyZW50KSB7XG5cdFx0XHQvLyBBZGQgYXMgY2hpbGQgb2YgcGFyZW50XG5cdFx0XHR0aGlzLmdyYXBoLmFkZENoaWxkKG5vZGUucGFyZW50LCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0Ly8gQWRkIGFzIHJvb3Rcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cblx0XHQvLyBBbHNvIGFkZCB0byBkZWZpbml0aW9ucyBzbyBpdCdzIHJlY29nbml6ZWQgYXMgYSBrbm93biB0eXBlXG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IG5vZGUubmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7bm9kZS5zb3VyY2VGaWxlfToke25vZGUubGluZX06JHtub2RlLmNvbHVtbn1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogbm9kZS5wYXJlbnQgPyBub2RlLnBhcmVudC5mdWxsUGF0aCA6IG51bGwsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IHRydWUsXG5cdFx0XHRibG9ja0Vycm9ycyA6IGZhbHNlXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChmdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdH1cblxuXHQvKipcblx0ICogU2V0IHBhcmVudCBub2RlcyBpbiBhIHNvdXJjZSBmaWxlIHRvIGVuYWJsZSBBU1QgdHJhdmVyc2FsIHVwXG5cdCAqL1xuXHRwcml2YXRlIHNldFBhcmVudE5vZGVzSW5Tb3VyY2VGaWxlIChzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3Qgc2V0UGFyZW50ID0gKG5vZGU6IHRzLk5vZGUsIHBhcmVudD86IHRzLk5vZGUpID0+IHtcblx0XHRcdC8vIFR5cGVTY3JpcHQgZG9lc24ndCBleHBvc2UgcGFyZW50IGFzIHdyaXRhYmxlLCBidXQgd2UgbmVlZCBpdFxuXHRcdFx0Ly8gZXNsaW50LWRpc2FibGUtbmV4dC1saW5lIEB0eXBlc2NyaXB0LWVzbGludC9uby1leHBsaWNpdC1hbnlcblx0XHRcdChub2RlIGFzIGFueSkucGFyZW50ID0gcGFyZW50O1xuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHNldFBhcmVudChjaGlsZCwgbm9kZSkpO1xuXHRcdH07XG5cdFx0c2V0UGFyZW50KHNvdXJjZUZpbGUpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFZpc2l0IGEgbm9kZSBpbiB0aGUgQVNUXG5cdCAqL1xuXHRwcml2YXRlIHZpc2l0Tm9kZSAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSwgY3VycmVudENsYXNzPzogdHMuQ2xhc3NEZWNsYXJhdGlvbik6IHZvaWQge1xuXHRcdC8vIFRyYWNrIG1uZW1vbmljYSBtb2R1bGUtb2JqZWN0IGFsaWFzZXMgYW5kIGN1c3RvbSBjb2xsZWN0aW9uIHZhcmlhYmxlc1xuXHRcdC8vIGJlZm9yZSBwcm9jZXNzaW5nIGRlZmluZSgpL2xvb2t1cCgpIGNhbGxzIHNvIHNvdXJjZSByZXNvbHV0aW9uIHdvcmtzLlxuXHRcdHRoaXMudHJhY2tJbXBvcnRzKG5vZGUpO1xuXHRcdHRoaXMudHJhY2tNb2R1bGVPYmplY3RBbGlhc2VzKG5vZGUpO1xuXHRcdHRoaXMudHJhY2tDb2xsZWN0aW9uQWxpYXNlcyhub2RlLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIENoZWNrIGZvciBkZWZpbmUoKSBjYWxsc1xuXHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChub2RlKSkge1xuXHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ2FsbChub2RlIGFzIHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlKTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgbGF6eSgpIGNhbGxzXG5cdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChub2RlKSkge1xuXHRcdFx0dGhpcy5wcm9jZXNzTGF6eUNhbGwobm9kZSBhcyB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIGRlY29yYXRlKCkgZGVjb3JhdG9yXG5cdFx0aWYgKHRoaXMuaXNEZWNvcmF0ZURlY29yYXRvcihub2RlKSkge1xuXHRcdFx0dGhpcy5wcm9jZXNzRGVjb3JhdGVEZWNvcmF0b3Iobm9kZSBhcyB0cy5EZWNvcmF0b3IsIHNvdXJjZUZpbGUsIGN1cnJlbnRDbGFzcyk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIHR5cGUgdXNhZ2VzIChuZXcgVHlwZSgpLCB0eXBlIGFubm90YXRpb25zLCBldGMuKVxuXHRcdHRoaXMuY29sbGVjdFVzYWdlKG5vZGUsIHNvdXJjZUZpbGUpO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIEVEUyBwYXR0ZXJucyAod3JhcCwgY3VycmVudCwgZ2V0RmxvdywgZXRjLilcblx0XHR0aGlzLmNvbGxlY3RFRFMobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgbmF0aXZlIGZsb3cgcGF0dGVybnMgKHByb3BlcnR5IGFjY2VzcywgbWV0aG9kIGNhbGxzLCBldGMuKVxuXHRcdHRoaXMuY29sbGVjdEZsb3cobm9kZSwgc291cmNlRmlsZSk7XG5cblx0XHQvLyBDaGVjayBmb3IgZnJhbWV3b3JrIGluc3RydW1lbnRhdGlvbiBwb2ludHMgKHZvY2FidWxhcnkgc3VwcGxpZWRcblx0XHQvLyBieSBwbHVnaW5zOyBzeW50YWN0aWMgb25seSDigJQgbm8gdHlwZSBjaGVja2VyKVxuXHRcdHRoaXMuY29sbGVjdEluc3RydW1lbnRhdGlvbihub2RlLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIENvbGxlY3QgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9ucyAoYWxpYXNlcywgY2xhc3NlcywgaW50ZXJmYWNlcylcblx0XHQvLyBwZXIgZmlsZSwgYW5kIHRoZSBmaWxlJ3MgaW1wb3J0IHdpcmluZywgZm9yIGltcG9ydC1hd2FyZSByZXNvbHV0aW9uXG5cdFx0dGhpcy50cmFja1JlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24obm9kZSk7XG5cdFx0dGhpcy50cmFja1JlZmVyZW5jZWRUeXBlSW1wb3J0KG5vZGUpO1xuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZVJlRXhwb3J0KG5vZGUpO1xuXHRcdHRoaXMudHJhY2tSZWZlcmVuY2VkVHlwZUNvbnN0QXJyYXkobm9kZSk7XG5cblx0XHQvLyBUcmFjayBzYW1lLWZpbGUgZnVuY3Rpb24gYmluZGluZ3Mgc28gRURTIGNhbiByZXNvbHZlIHdyYXAoZm4pXG5cdFx0Ly8gYXJndW1lbnRzIHdpdGhvdXQgdGhlIHR5cGUgY2hlY2tlciAoYmVzdCBlZmZvcnQsIGxhc3Qgd2lucylcblx0XHRpZiAodHMuaXNGdW5jdGlvbkRlY2xhcmF0aW9uKG5vZGUpICYmIG5vZGUubmFtZSkge1xuXHRcdFx0Y29uc3Qga2V5ID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX0jJHtub2RlLm5hbWUudGV4dH1gO1xuXHRcdFx0dGhpcy5mdW5jdGlvbkJpbmRpbmdzLnNldChrZXksIG5vZGUpO1xuXHRcdH1cblx0XHRpZiAoXG5cdFx0XHR0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpICYmXG5cdFx0XHRub2RlLmluaXRpYWxpemVyICYmXG5cdFx0XHQodHMuaXNBcnJvd0Z1bmN0aW9uKG5vZGUuaW5pdGlhbGl6ZXIpIHx8IHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKG5vZGUuaW5pdGlhbGl6ZXIpKVxuXHRcdCkge1xuXHRcdFx0Y29uc3Qga2V5ID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX0jJHtub2RlLm5hbWUudGV4dH1gO1xuXHRcdFx0dGhpcy5mdW5jdGlvbkJpbmRpbmdzLnNldChrZXksIG5vZGUuaW5pdGlhbGl6ZXIpO1xuXHRcdH1cblxuXHRcdC8vIFRyYWNrIGNsYXNzIGRlY2xhcmF0aW9ucyBmb3IgZGVjb3JhdG9yIHBhcmVudCBsb29rdXBcblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHQvLyBWaXNpdCBjaGlsZHJlbiB3aXRoIHRoaXMgY2xhc3MgYXMgdGhlIGN1cnJlbnQgY29udGV4dFxuXHRcdFx0dHMuZm9yRWFjaENoaWxkKG5vZGUsIGNoaWxkID0+IHRoaXMudmlzaXROb2RlKGNoaWxkLCBzb3VyY2VGaWxlLCBub2RlKSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdC8vIFJlY3Vyc2l2ZWx5IHZpc2l0IGNoaWxkcmVuXG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgY2hpbGQgPT4gdGhpcy52aXNpdE5vZGUoY2hpbGQsIHNvdXJjZUZpbGUsIGN1cnJlbnRDbGFzcykpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBUcmFjayBpbXBvcnRzIGZyb20gJ21uZW1vbmljYScgc28gYWxpYXNlcyBvZiB0aGUgbW9kdWxlIG9iamVjdCBhbmRcblx0ICogY3JlYXRlVHlwZXNDb2xsZWN0aW9uIGFyZSByZWNvZ25pemVkIHdpdGhvdXQgcmVseWluZyBvbiB0aGUgdHlwZSBjaGVja2VyLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja0ltcG9ydHMgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzSW1wb3J0RGVjbGFyYXRpb24obm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IG1vZHVsZVNwZWNpZmllciB9ID0gbm9kZTtcblx0XHRpZiAoIXRzLmlzU3RyaW5nTGl0ZXJhbChtb2R1bGVTcGVjaWZpZXIpIHx8IG1vZHVsZVNwZWNpZmllci50ZXh0ICE9PSAnbW5lbW9uaWNhJykge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IGNsYXVzZSA9IG5vZGUuaW1wb3J0Q2xhdXNlO1xuXHRcdGlmICghY2xhdXNlKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0IHsgbW5lbW9uaWNhLCBjcmVhdGVUeXBlc0NvbGxlY3Rpb24gfSBmcm9tICdtbmVtb25pY2EnXG5cdFx0aWYgKGNsYXVzZS5uYW1lZEJpbmRpbmdzICYmIHRzLmlzTmFtZWRJbXBvcnRzKGNsYXVzZS5uYW1lZEJpbmRpbmdzKSkge1xuXHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGNsYXVzZS5uYW1lZEJpbmRpbmdzLmVsZW1lbnRzKSB7XG5cdFx0XHRcdGNvbnN0IGxvY2FsTmFtZSA9IGVsZW1lbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBpbXBvcnRlZE5hbWUgPSBlbGVtZW50LnByb3BlcnR5TmFtZVxuXHRcdFx0XHRcdD8gZWxlbWVudC5wcm9wZXJ0eU5hbWUudGV4dFxuXHRcdFx0XHRcdDogbG9jYWxOYW1lO1xuXHRcdFx0XHRpZiAoaW1wb3J0ZWROYW1lID09PSAnbW5lbW9uaWNhJykge1xuXHRcdFx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChsb2NhbE5hbWUpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChpbXBvcnRlZE5hbWUgPT09ICdjcmVhdGVUeXBlc0NvbGxlY3Rpb24nKSB7XG5cdFx0XHRcdFx0dGhpcy5jcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMuYWRkKGxvY2FsTmFtZSk7XG5cdFx0XHRcdH1cblx0XHRcdFx0bGV0IGZpbGVJbXBvcnRzID0gdGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRcdGlmICghZmlsZUltcG9ydHMpIHtcblx0XHRcdFx0XHRmaWxlSW1wb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHRcdFx0dGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuc2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSwgZmlsZUltcG9ydHMpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGZpbGVJbXBvcnRzLnNldChsb2NhbE5hbWUsIGltcG9ydGVkTmFtZSk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gaW1wb3J0ICogYXMgbW5lbW9uaWNhIGZyb20gJ21uZW1vbmljYSdcblx0XHRpZiAoY2xhdXNlLm5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lc3BhY2VJbXBvcnQoY2xhdXNlLm5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5hZGQoY2xhdXNlLm5hbWVkQmluZGluZ3MubmFtZS50ZXh0KTtcblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgbW5lbW9uaWNhIGZyb20gJ21uZW1vbmljYScgKGRlZmF1bHQgaW1wb3J0KSDigJQgdHJlYXQgYXMgbW9kdWxlIG9iamVjdCB0b29cblx0XHRpZiAoY2xhdXNlLm5hbWUpIHtcblx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChjbGF1c2UubmFtZS50ZXh0KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGEgbmFtZWQgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9uICh0eXBlIGFsaWFzLCBjbGFzcywgb3Jcblx0ICogaW50ZXJmYWNlKSBmb3IgdGhlIGZpbGUgY3VycmVudGx5IGJlaW5nIHZpc2l0ZWQuXG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdC8vIE5hbWVzcGFjZXMgYXJlIHRoZSBtaWRkbGUgc2VnbWVudHMgb2YgcXVhbGlmaWVkIHJlZmVyZW5jZXNcblx0XHQvLyAobW9kZWxzLklubmVyLkNyYXRlKSDigJQgcmVjb3JkZWQgc2VwYXJhdGVseSBmcm9tIHRoZSBwbGFpbi1uYW1lXG5cdFx0Ly8gZGVjbGFyYXRpb24gdGFibGUgKHN0cmluZy1uYW1lZCBgbW9kdWxlICfigKYnYCBkZWNsYXJhdGlvbnMgYXJlXG5cdFx0Ly8gYW1iaWVudCBleHRlcm5hbHMgYW5kIHN0YXkgb3V0KVxuXHRcdGlmICh0cy5pc01vZHVsZURlY2xhcmF0aW9uKG5vZGUpICYmIHRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpICYmXG5cdFx0XHRub2RlLmJvZHkgJiYgdHMuaXNNb2R1bGVCbG9jayhub2RlLmJvZHkpKSB7XG5cdFx0XHRjb25zdCBuYW1lc3BhY2VGaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRcdGxldCBuYW1lc3BhY2VzID0gdGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMuZ2V0KG5hbWVzcGFjZUZpbGVQYXRoKTtcblx0XHRcdGlmICghbmFtZXNwYWNlcykge1xuXHRcdFx0XHRuYW1lc3BhY2VzID0gbmV3IE1hcDxzdHJpbmcsIHRzLk1vZHVsZURlY2xhcmF0aW9uPigpO1xuXHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlcy5zZXQobmFtZXNwYWNlRmlsZVBhdGgsIG5hbWVzcGFjZXMpO1xuXHRcdFx0fVxuXHRcdFx0bmFtZXNwYWNlcy5zZXQobm9kZS5uYW1lLnRleHQsIG5vZGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGxldCBuYW1lID0gJyc7XG5cdFx0bGV0IGtpbmQ6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25bJ2tpbmQnXSB8IHVuZGVmaW5lZDtcblx0XHRsZXQgZGVjbE5vZGU6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25bJ25vZGUnXSB8IHVuZGVmaW5lZDtcblxuXHRcdGlmICh0cy5pc1R5cGVBbGlhc0RlY2xhcmF0aW9uKG5vZGUpICYmIHRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpKSB7XG5cdFx0XHRuYW1lID0gbm9kZS5uYW1lLnRleHQ7XG5cdFx0XHRraW5kID0gJ2FsaWFzJztcblx0XHRcdGRlY2xOb2RlID0gbm9kZTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihub2RlKSAmJiBub2RlLm5hbWUpIHtcblx0XHRcdG5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRcdGtpbmQgPSAnY2xhc3MnO1xuXHRcdFx0ZGVjbE5vZGUgPSBub2RlO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNJbnRlcmZhY2VEZWNsYXJhdGlvbihub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5uYW1lKSkge1xuXHRcdFx0bmFtZSA9IG5vZGUubmFtZS50ZXh0O1xuXHRcdFx0a2luZCA9ICdpbnRlcmZhY2UnO1xuXHRcdFx0ZGVjbE5vZGUgPSBub2RlO1xuXHRcdH1cblxuXHRcdGlmICgha2luZCB8fCAhZGVjbE5vZGUgfHwgIW5hbWUpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRsZXQgZGVjbHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRGVjbHMuZ2V0KGZpbGVQYXRoKTtcblx0XHRpZiAoIWRlY2xzKSB7XG5cdFx0XHRkZWNscyA9IG5ldyBNYXA8c3RyaW5nLCBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uPigpO1xuXHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLnNldChmaWxlUGF0aCwgZGVjbHMpO1xuXHRcdH1cblx0XHRjb25zdCBlbnRyeTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiA9IHsga2luZCwgbm9kZSA6IGRlY2xOb2RlLCBmaWxlIDogZmlsZVBhdGggfTtcblx0XHRkZWNscy5zZXQobmFtZSwgZW50cnkpO1xuXG5cdFx0Ly8gYGV4cG9ydCBkZWZhdWx0IGNsYXNzIEZvbyB7fWAgaXMgYWxzbyByZWFjaGFibGUgdW5kZXIgdGhlICdkZWZhdWx0J1xuXHRcdC8vIGJpbmRpbmcgZm9yIGRlZmF1bHQgaW1wb3J0ZXJzXG5cdFx0aWYgKGtpbmQgPT09ICdjbGFzcycpIHtcblx0XHRcdGNvbnN0IGNsYXNzTm9kZSA9IGRlY2xOb2RlIGFzIHRzLkNsYXNzRGVjbGFyYXRpb247XG5cdFx0XHRjb25zdCBpc0V4cG9ydGVkID0gY2xhc3NOb2RlLm1vZGlmaWVycz8uc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FeHBvcnRLZXl3b3JkKSA/PyBmYWxzZTtcblx0XHRcdGNvbnN0IGlzRGVmYXVsdCA9IGNsYXNzTm9kZS5tb2RpZmllcnM/LnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRGVmYXVsdEtleXdvcmQpID8/IGZhbHNlO1xuXHRcdFx0aWYgKGlzRXhwb3J0ZWQgJiYgaXNEZWZhdWx0KSB7XG5cdFx0XHRcdGRlY2xzLnNldCgnZGVmYXVsdCcsIGVudHJ5KTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGNvbnN0cyBpbml0aWFsaXplZCB3aXRoIGFuIGFycmF5IGxpdGVyYWwgKG9wdGlvbmFsbHkgd3JhcHBlZCBpblxuXHQgKiBgYXMgY29uc3RgIC8gYHNhdGlzZmllc2ApLCBzbyBhIGB0eXBlb2Ygc3RhdHVzTGlzdFtudW1iZXJdYCBmaWVsZCB0eXBlXG5cdCAqIGV4cGFuZHMgdG8gdGhlIGVsZW1lbnQgbGl0ZXJhbCB1bmlvbiDigJQgdGhlIGdlbmVyYXRlZCBmaWxlIGNhcnJpZXMgbm9cblx0ICogaW1wb3J0cywgc28gZW1pdHRpbmcgdGhlIGJhcmUgYHR5cGVvZiBzdGF0dXNMaXN0YCBxdWVyeSB3b3VsZCBiZSBhblxuXHQgKiB1bnJlc29sdmFibGUgbmFtZSBkb3duc3RyZWFtLiBGaXJzdCBiaW5kaW5nIHdpbnM6IGEgbmVzdGVkIHNoYWRvd1xuXHQgKiBtdXN0IG5vdCByZXBsYWNlIHRoZSBtb2R1bGUtbGV2ZWwgY29uc3QgdGhlIHR5cGVvZiByZWZlcnMgdG8uXG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrUmVmZXJlbmNlZFR5cGVDb25zdEFycmF5IChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgfHwgIXRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpIHx8ICFub2RlLmluaXRpYWxpemVyKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHsgaW5pdGlhbGl6ZXI6IHJhd0luaXRpYWxpemVyIH0gPSBub2RlO1xuXHRcdGxldCBpbml0aWFsaXplcjogdHMuRXhwcmVzc2lvbiA9IHJhd0luaXRpYWxpemVyO1xuXHRcdHdoaWxlIChcblx0XHRcdHRzLmlzQXNFeHByZXNzaW9uKGluaXRpYWxpemVyKSB8fFxuXHRcdFx0dHMuaXNTYXRpc2ZpZXNFeHByZXNzaW9uKGluaXRpYWxpemVyKSB8fFxuXHRcdFx0Ly8gdGhlIGFuZ2xlLWJyYWNrZXQgYXNzZXJ0aW9uIHNwZWxsaW5nIChgPGNvbnN0PlvigKZdYCkgaXMgdGhlXG5cdFx0XHQvLyBzYW1lIGNvbnN0LWFycmF5IG1hcmtlciBhcyB0aGUgYGFzIGNvbnN0YCBmb3JtIChGMTcpXG5cdFx0XHR0cy5pc1R5cGVBc3NlcnRpb25FeHByZXNzaW9uKGluaXRpYWxpemVyKVxuXHRcdCkge1xuXHRcdFx0aW5pdGlhbGl6ZXIgPSBpbml0aWFsaXplci5leHByZXNzaW9uO1xuXHRcdH1cblx0XHRpZiAoIXRzLmlzQXJyYXlMaXRlcmFsRXhwcmVzc2lvbihpbml0aWFsaXplcikpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgZmlsZVBhdGggPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0bGV0IGNvbnN0cyA9IHRoaXMucmVmZXJlbmNlZFR5cGVDb25zdEFycmF5cy5nZXQoZmlsZVBhdGgpO1xuXHRcdGlmICghY29uc3RzKSB7XG5cdFx0XHRjb25zdHMgPSBuZXcgTWFwPHN0cmluZywgdHMuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbj4oKTtcblx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVDb25zdEFycmF5cy5zZXQoZmlsZVBhdGgsIGNvbnN0cyk7XG5cdFx0fVxuXHRcdGlmICghY29uc3RzLmhhcyhub2RlLm5hbWUudGV4dCkpIHtcblx0XHRcdGNvbnN0cy5zZXQobm9kZS5uYW1lLnRleHQsIGluaXRpYWxpemVyKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRmluZCB0aGUgYXJyYXkgbGl0ZXJhbCBiZWhpbmQgYSBtb2R1bGUgY29uc3QgcmVmZXJlbmNlZCB0aHJvdWdoXG5cdCAqIGB0eXBlb2ZgOiB0aGUgZGVjbGFyaW5nIGZpbGUncyBvd24gY29uc3RzIGZpcnN0ICh0aGUgRjEzIGNhc2UgaXMgYVxuXHQgKiBOT04tZXhwb3J0ZWQgY29uc3QgaW4gdGhlIHNhbWUgbW9kdWxlIGFzIHRoZSBleHBhbmRlZCBjbGFzcyksIHRoZW4g4oCUXG5cdCAqIHdoZW4gdGhlIGZpbGUgaW1wb3J0cyB0aGUgbmFtZSDigJQgdGhlIGltcG9ydGVkIG1vZHVsZSdzIGNvbnN0cy5cblx0ICogRXh0ZXJuYWwgbW9kdWxlcyBhcmUgbmV2ZXIgYW5hbHl6ZWQsIHNvIHRob3NlIHlpZWxkIG5vdGhpbmcuXG5cdCAqL1xuXHRwcml2YXRlIGZpbmRSZWZlcmVuY2VkQ29uc3RBcnJheSAoXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdGZyb21GaWxlOiBzdHJpbmdcblx0KTogdHMuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgbG9jYWwgPSB0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuZ2V0KGZyb21GaWxlKT8uZ2V0KG5hbWUpO1xuXHRcdGlmIChsb2NhbCkge1xuXHRcdFx0cmV0dXJuIGxvY2FsO1xuXHRcdH1cblx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldChmcm9tRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAoIWltcG9ydGVkIHx8IGltcG9ydGVkLmlzTmFtZXNwYWNlKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoaW1wb3J0ZWQuc3BlY2lmaWVyLCBmcm9tRmlsZSk7XG5cdFx0aWYgKCFyZXNvbHV0aW9uIHx8IHJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgZm91bmQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlQ29uc3RBcnJheXMuZ2V0KHJlc29sdXRpb24ucmVzb2x2ZWRQYXRoKT8uZ2V0KGltcG9ydGVkLm9yaWdpbmFsTmFtZSk7XG5cdFx0cmV0dXJuIGZvdW5kO1xuXHR9XG5cblx0LyoqXG5cdCAqIEVsZW1lbnQgbGl0ZXJhbCB0eXBlcyBvZiBhIHRyYWNrZWQgY29uc3QgYXJyYXk6IGV2ZXJ5IGVsZW1lbnQgbXVzdCBiZVxuXHQgKiBhIHBsYWluIGxpdGVyYWwgKG9wdGlvbmFsbHkgd3JhcHBlZCBpbiBgYXMgY29uc3RgIC8gYHNhdGlzZmllc2AgL1xuXHQgKiBgPGNvbnN0PmAgYXNzZXJ0aW9ucykg4oCUIHN0cmluZywgbnVtZXJpYyAodW5hcnkgYC1gL2ArYCBwcmVzZXJ2ZWQpLFxuXHQgKiBib29sZWFuLCBvciBudWxsLiBTcHJlYWRzLCBpZGVudGlmaWVycywgYW5kIG5lc3RlZCBhcnJheXMgbWVhbiB0aGVcblx0ICogdW5pb24gaXMgbm90IHN0YXRpY2FsbHkgdmlzaWJsZSBhbmQgeWllbGQgdW5kZWZpbmVkLCBzbyB0aGUgY2FsbGVyXG5cdCAqIGRlZ3JhZGVzIHRoZSBmaWVsZCB0byBgdW5rbm93bmAgcmF0aGVyIHRoYW4gZ3Vlc3NpbmcuXG5cdCAqL1xuXHRwcml2YXRlIGxpdGVyYWxUeXBlc09mQXJyYXkgKGFycmF5TGl0ZXJhbDogdHMuQXJyYXlMaXRlcmFsRXhwcmVzc2lvbik6IHN0cmluZ1tdIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBsaXRlcmFsczogc3RyaW5nW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2YgYXJyYXlMaXRlcmFsLmVsZW1lbnRzKSB7XG5cdFx0XHRpZiAodHMuaXNTcHJlYWRFbGVtZW50KGVsZW1lbnQpKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRsZXQgZXhwcjogdHMuRXhwcmVzc2lvbiA9IGVsZW1lbnQ7XG5cdFx0XHR3aGlsZSAoXG5cdFx0XHRcdHRzLmlzQXNFeHByZXNzaW9uKGV4cHIpIHx8XG5cdFx0XHRcdHRzLmlzU2F0aXNmaWVzRXhwcmVzc2lvbihleHByKSB8fFxuXHRcdFx0XHR0cy5pc1R5cGVBc3NlcnRpb25FeHByZXNzaW9uKGV4cHIpXG5cdFx0XHQpIHtcblx0XHRcdFx0ZXhwciA9IGV4cHIuZXhwcmVzc2lvbjtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoZXhwcikgfHwgdHMuaXNOb1N1YnN0aXR1dGlvblRlbXBsYXRlTGl0ZXJhbChleHByKSkge1xuXHRcdFx0XHRsaXRlcmFscy5wdXNoKGAnJHtleHByLnRleHR9J2ApO1xuXHRcdFx0fSBlbHNlIGlmICh0cy5pc1ByZWZpeFVuYXJ5RXhwcmVzc2lvbihleHByKSAmJiB0cy5pc051bWVyaWNMaXRlcmFsKGV4cHIub3BlcmFuZCkpIHtcblx0XHRcdFx0Ly8gc2lnbmVkIG51bWVyaWMgbGl0ZXJhbHMgKGAtMSB8IDFgKTogdW5hcnkgbWludXMgaXMgcGFydFxuXHRcdFx0XHQvLyBvZiB0aGUgbGl0ZXJhbCB0eXBlOyB1bmFyeSBwbHVzIGlzIHRoZSBiYXJlIGxpdGVyYWwgaW5cblx0XHRcdFx0Ly8gdHlwZSBzcGFjZSAoYCsxYCBpcyB3cml0dGVuIGAxYClcblx0XHRcdFx0aWYgKGV4cHIub3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuTWludXNUb2tlbikge1xuXHRcdFx0XHRcdGxpdGVyYWxzLnB1c2goYC0ke2V4cHIub3BlcmFuZC50ZXh0fWApO1xuXHRcdFx0XHR9IGVsc2UgaWYgKGV4cHIub3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuUGx1c1Rva2VuKSB7XG5cdFx0XHRcdFx0bGl0ZXJhbHMucHVzaChleHByLm9wZXJhbmQudGV4dCk7XG5cdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIGlmICh0cy5pc051bWVyaWNMaXRlcmFsKGV4cHIpKSB7XG5cdFx0XHRcdGxpdGVyYWxzLnB1c2goZXhwci50ZXh0KTtcblx0XHRcdH0gZWxzZSBpZiAoZXhwci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdGxpdGVyYWxzLnB1c2goJ3RydWUnKTtcblx0XHRcdH0gZWxzZSBpZiAoZXhwci5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRsaXRlcmFscy5wdXNoKCdmYWxzZScpO1xuXHRcdFx0fSBlbHNlIGlmIChleHByLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQpIHtcblx0XHRcdFx0bGl0ZXJhbHMucHVzaCgnbnVsbCcpO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHR9XG5cdFx0aWYgKGxpdGVyYWxzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gbGl0ZXJhbHM7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFbWl0LXR5cGUgZm9yIGB0eXBlb2YgbmFtZWAgd2hlbiBgbmFtZWAgaXMgYSB0cmFja2VkIGNvbnN0IGFycmF5OiB0aGVcblx0ICogdW5pb24gb2YgaXRzIGVsZW1lbnQgbGl0ZXJhbCB0eXBlcyAoYCdhY3RpdmUnIHwgJ2Nsb3NlZCdgKS4gRXZlcnlcblx0ICogb3RoZXIgdHlwZW9mIHNvdXJjZSDigJQgbm9uLWFycmF5IGNvbnN0cywgZnVuY3Rpb25zLCBjbGFzc2VzLCBuYW1lcyBub3Rcblx0ICogdHJhY2tlZCBhdCBhbGwg4oCUIHlpZWxkcyB1bmRlZmluZWQsIHNvIHRoZSBjYWxsZXIgZGVncmFkZXMgdGhlIGZpZWxkXG5cdCAqIHRvIGB1bmtub3duYDogYSBiYXJlIGB0eXBlb2YgbmFtZWAgZW1pdHRlZCBpbnRvIHR5cGVzLnRzIGhhcyBub1xuXHQgKiBpbXBvcnQgdG8gcmVzb2x2ZSBhZ2FpbnN0IGRvd25zdHJlYW0uXG5cdCAqL1xuXHRwcml2YXRlIHR5cGVPZkNvbnN0QXJyYXlVbmlvbiAobmFtZTogc3RyaW5nLCBmcm9tRmlsZTogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBhcnJheUxpdGVyYWwgPSB0aGlzLmZpbmRSZWZlcmVuY2VkQ29uc3RBcnJheShuYW1lLCBmcm9tRmlsZSk7XG5cdFx0aWYgKCFhcnJheUxpdGVyYWwpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGxpdGVyYWxzID0gdGhpcy5saXRlcmFsVHlwZXNPZkFycmF5KGFycmF5TGl0ZXJhbCk7XG5cdFx0aWYgKCFsaXRlcmFscykge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgdW5pb24gPSBsaXRlcmFscy5qb2luKCcgfCAnKTtcblx0XHRyZXR1cm4gdW5pb247XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIHRoZSBpbXBvcnRpbmcgZmlsZSdzIG5hbWVkL25hbWVzcGFjZS9kZWZhdWx0IGltcG9ydCBiaW5kaW5ncyBzb1xuXHQgKiByZWZlcmVuY2VkLXR5cGUgbmFtZXMgcmVzb2x2ZSB0aHJvdWdoIHRoZSBmaWxlJ3Mgb3duIGltcG9ydCBzdGF0ZW1lbnRzXG5cdCAqIChGMTApIHJhdGhlciB0aGFuIGEgcHJvZ3JhbS13aWRlIG5hbWUgbWFwLlxuXHQgKi9cblx0cHJpdmF0ZSB0cmFja1JlZmVyZW5jZWRUeXBlSW1wb3J0IChub2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc0ltcG9ydERlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHsgbW9kdWxlU3BlY2lmaWVyIH0gPSBub2RlO1xuXHRcdGlmICghdHMuaXNTdHJpbmdMaXRlcmFsKG1vZHVsZVNwZWNpZmllcikpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgY2xhdXNlID0gbm9kZS5pbXBvcnRDbGF1c2U7XG5cdFx0aWYgKCFjbGF1c2UpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRsZXQgaW1wb3J0cyA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldChmaWxlUGF0aCk7XG5cdFx0aWYgKCFpbXBvcnRzKSB7XG5cdFx0XHRpbXBvcnRzID0gbmV3IE1hcDxzdHJpbmcsIFJlZmVyZW5jZWRUeXBlSW1wb3J0PigpO1xuXHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuc2V0KGZpbGVQYXRoLCBpbXBvcnRzKTtcblx0XHR9XG5cblx0XHQvLyBpbXBvcnQgeyBTaGFyZWRTaGFwZSB9IGZyb20gJ+KApicgLyBpbXBvcnQgeyBTaGFyZWRTaGFwZSBhcyBTIH0gZnJvbSAn4oCmJ1xuXHRcdGlmIChjbGF1c2UubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVkSW1wb3J0cyhjbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBjbGF1c2UubmFtZWRCaW5kaW5ncy5lbGVtZW50cykge1xuXHRcdFx0XHRjb25zdCBsb2NhbE5hbWUgPSBlbGVtZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3Qgb3JpZ2luYWxOYW1lID0gZWxlbWVudC5wcm9wZXJ0eU5hbWUgPyBlbGVtZW50LnByb3BlcnR5TmFtZS50ZXh0IDogbG9jYWxOYW1lO1xuXHRcdFx0XHRpbXBvcnRzLnNldChsb2NhbE5hbWUsIHtcblx0XHRcdFx0XHRvcmlnaW5hbE5hbWUsXG5cdFx0XHRcdFx0c3BlY2lmaWVyICAgOiBtb2R1bGVTcGVjaWZpZXIudGV4dCxcblx0XHRcdFx0XHRpc05hbWVzcGFjZSA6IGZhbHNlXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIGltcG9ydCAqIGFzIG1vZGVscyBmcm9tICfigKYnIOKAlCByZXNvbHZlZCB3aGVuIGEgcXVhbGlmaWVkIG5hbWVcblx0XHQvLyAobW9kZWxzLlNoYXJlZFNoYXBlKSBpcyBlbmNvdW50ZXJlZFxuXHRcdGlmIChjbGF1c2UubmFtZWRCaW5kaW5ncyAmJiB0cy5pc05hbWVzcGFjZUltcG9ydChjbGF1c2UubmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdGltcG9ydHMuc2V0KGNsYXVzZS5uYW1lZEJpbmRpbmdzLm5hbWUudGV4dCwge1xuXHRcdFx0XHRvcmlnaW5hbE5hbWUgOiAnJyxcblx0XHRcdFx0c3BlY2lmaWVyICAgIDogbW9kdWxlU3BlY2lmaWVyLnRleHQsXG5cdFx0XHRcdGlzTmFtZXNwYWNlICA6IHRydWVcblx0XHRcdH0pO1xuXHRcdH1cblxuXHRcdC8vIGltcG9ydCBTaGFyZWRTaGFwZSBmcm9tICfigKYnIChkZWZhdWx0IGltcG9ydClcblx0XHRpZiAoY2xhdXNlLm5hbWUpIHtcblx0XHRcdGltcG9ydHMuc2V0KGNsYXVzZS5uYW1lLnRleHQsIHtcblx0XHRcdFx0b3JpZ2luYWxOYW1lIDogJ2RlZmF1bHQnLFxuXHRcdFx0XHRzcGVjaWZpZXIgICAgOiBtb2R1bGVTcGVjaWZpZXIudGV4dCxcblx0XHRcdFx0aXNOYW1lc3BhY2UgIDogZmFsc2Vcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgcmUtZXhwb3J0IHdpcmluZyAoYGV4cG9ydCB7IFggfSBmcm9tICfigKYnYCwgYGV4cG9ydCAqIGZyb20gJ+KApidgLFxuXHQgKiBgZXhwb3J0IHsgWCBhcyBZIH1gKSBzbyByZXNvbHV0aW9uIGNhbiBjaGFzZSBiYXJyZWxzIHRvIHRoZSBvcmlnaW5cblx0ICogbW9kdWxlLiBNaXJyb3JzIE1vZHVsZUdyYXBoQnVpbGRlci5yZXNvbHZlT3JpZ2luLCBuYW1lLWJhc2VkIG9ubHkuXG5cdCAqL1xuXHRwcml2YXRlIHRyYWNrUmVmZXJlbmNlZFR5cGVSZUV4cG9ydCAobm9kZTogdHMuTm9kZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNFeHBvcnREZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRjb25zdCB7IG1vZHVsZVNwZWNpZmllciB9ID0gbm9kZTtcblx0XHRjb25zdCBzcGVjaWZpZXJUZXh0ID0gbW9kdWxlU3BlY2lmaWVyICYmIHRzLmlzU3RyaW5nTGl0ZXJhbChtb2R1bGVTcGVjaWZpZXIpXG5cdFx0XHQ/IG1vZHVsZVNwZWNpZmllci50ZXh0XG5cdFx0XHQ6IHVuZGVmaW5lZDtcblxuXHRcdGlmIChub2RlLmV4cG9ydENsYXVzZSAmJiB0cy5pc05hbWVkRXhwb3J0cyhub2RlLmV4cG9ydENsYXVzZSkpIHtcblx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBub2RlLmV4cG9ydENsYXVzZS5lbGVtZW50cykge1xuXHRcdFx0XHRjb25zdCBleHBvcnRlZE5hbWUgPSBlbGVtZW50Lm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgbG9jYWxOYW1lID0gZWxlbWVudC5wcm9wZXJ0eU5hbWUgPyBlbGVtZW50LnByb3BlcnR5TmFtZS50ZXh0IDogZXhwb3J0ZWROYW1lO1xuXHRcdFx0XHRpZiAoc3BlY2lmaWVyVGV4dCkge1xuXHRcdFx0XHRcdC8vIGV4cG9ydCB7IFggfSBmcm9tICfigKYnIC8gZXhwb3J0IHsgWCBhcyBZIH0gZnJvbSAn4oCmJ1xuXHRcdFx0XHRcdGxldCByZUV4cG9ydHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLmdldChmaWxlUGF0aCk7XG5cdFx0XHRcdFx0aWYgKCFyZUV4cG9ydHMpIHtcblx0XHRcdFx0XHRcdHJlRXhwb3J0cyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLnNldChmaWxlUGF0aCwgcmVFeHBvcnRzKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0cmVFeHBvcnRzLnNldChleHBvcnRlZE5hbWUsIHNwZWNpZmllclRleHQpO1xuXHRcdFx0XHR9IGVsc2UgaWYgKGxvY2FsTmFtZSAhPT0gZXhwb3J0ZWROYW1lKSB7XG5cdFx0XHRcdFx0Ly8gZXhwb3J0IHsgWCBhcyBZIH0g4oCUIHNhbWUtZmlsZSBhbGlhcyBvZiBhIGxvY2FsIGRlY2xhcmF0aW9uXG5cdFx0XHRcdFx0bGV0IGFsaWFzZXMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0XHRcdGlmICghYWxpYXNlcykge1xuXHRcdFx0XHRcdFx0YWxpYXNlcyA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmc+KCk7XG5cdFx0XHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcy5zZXQoZmlsZVBhdGgsIGFsaWFzZXMpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRhbGlhc2VzLnNldChleHBvcnRlZE5hbWUsIGxvY2FsTmFtZSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAobm9kZS5leHBvcnRDbGF1c2UgJiYgdHMuaXNOYW1lc3BhY2VFeHBvcnQobm9kZS5leHBvcnRDbGF1c2UpKSB7XG5cdFx0XHQvLyBgZXhwb3J0ICogYXMgbnMgZnJvbSAn4oCmJ2Ag4oCUIGEgbmVzdGVkIG1vZHVsZSBuYW1lc3BhY2U7IG1pZGRsZVxuXHRcdFx0Ly8gc2VnbWVudHMgb2YgcXVhbGlmaWVkIHJlZmVyZW5jZXMgKGJhcnJlbC5EZWVwLkdhZGdldCkgY2hhc2UgaXRcblx0XHRcdGlmIChzcGVjaWZpZXJUZXh0KSB7XG5cdFx0XHRcdGxldCBzdGFycyA9IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VTdGFycy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0XHRpZiAoIXN0YXJzKSB7XG5cdFx0XHRcdFx0c3RhcnMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0XHRcdHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VTdGFycy5zZXQoZmlsZVBhdGgsIHN0YXJzKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRzdGFycy5zZXQobm9kZS5leHBvcnRDbGF1c2UubmFtZS50ZXh0LCBzcGVjaWZpZXJUZXh0KTtcblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAoIW5vZGUuZXhwb3J0Q2xhdXNlICYmIHNwZWNpZmllclRleHQpIHtcblx0XHRcdC8vIGV4cG9ydCAqIGZyb20gJ+KApidcblx0XHRcdGxldCBzdGFycyA9IHRoaXMucmVmZXJlbmNlZFR5cGVFeHBvcnRTdGFycy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0aWYgKCFzdGFycykge1xuXHRcdFx0XHRzdGFycyA9IFtdO1xuXHRcdFx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuc2V0KGZpbGVQYXRoLCBzdGFycyk7XG5cdFx0XHR9XG5cdFx0XHRzdGFycy5wdXNoKHNwZWNpZmllclRleHQpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgbW9kdWxlIHNwZWNpZmllciBmcm9tIGEgY29udGFpbmluZyBmaWxlIHdpdGggdGhlIHByb2dyYW0nc1xuXHQgKiBjb21waWxlck9wdGlvbnMgKHRzY29uZmlnIGBwYXRoc2AsIGV4dGVuc2lvbmxlc3MgaW1wb3J0cywgaW5kZXggZmlsZXMpLlxuXHQgKiBNb2R1bGUgcmVzb2x1dGlvbiBvbmx5IOKAlCB0aGUgbm8tZ2V0VHlwZUNoZWNrZXIoKSBwcmVjZWRlbnQgc3RheXMuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZSAoc3BlY2lmaWVyOiBzdHJpbmcsIGNvbnRhaW5pbmdGaWxlOiBzdHJpbmcpOlxuXHRcdFJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbiB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2FjaGVLZXkgPSBgJHtjb250YWluaW5nRmlsZX06OiR7c3BlY2lmaWVyfWA7XG5cdFx0aWYgKHRoaXMucmVmZXJlbmNlZFR5cGVSZXNvbHV0aW9uQ2FjaGUuaGFzKGNhY2hlS2V5KSkge1xuXHRcdFx0Y29uc3QgY2FjaGVkID0gdGhpcy5yZWZlcmVuY2VkVHlwZVJlc29sdXRpb25DYWNoZS5nZXQoY2FjaGVLZXkpO1xuXHRcdFx0cmV0dXJuIGNhY2hlZCA9PT0gdW5kZWZpbmVkID8gdW5kZWZpbmVkIDogY2FjaGVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlc29sdXRpb24gPSB0cy5yZXNvbHZlTW9kdWxlTmFtZShcblx0XHRcdHNwZWNpZmllcixcblx0XHRcdGNvbnRhaW5pbmdGaWxlLFxuXHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZUNvbXBpbGVyT3B0aW9ucyxcblx0XHRcdHRzLnN5c1xuXHRcdCkucmVzb2x2ZWRNb2R1bGU7XG5cblx0XHRjb25zdCByZXN1bHQ6IFJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbiB8IHVuZGVmaW5lZCA9IHJlc29sdXRpb25cblx0XHRcdD8ge1xuXHRcdFx0XHRyZXNvbHZlZFBhdGggOiBub2RlUGF0aC5yZXNvbHZlKHJlc29sdXRpb24ucmVzb2x2ZWRGaWxlTmFtZSksXG5cdFx0XHRcdGlzRXh0ZXJuYWwgICA6ICEhcmVzb2x1dGlvbi5pc0V4dGVybmFsTGlicmFyeUltcG9ydFxuXHRcdFx0fVxuXHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHR0aGlzLnJlZmVyZW5jZWRUeXBlUmVzb2x1dGlvbkNhY2hlLnNldChjYWNoZUtleSwgcmVzdWx0KTtcblx0XHRjb25zdCBmaW5hbFJlc3VsdCA9IHJlc3VsdDtcblx0XHRyZXR1cm4gZmluYWxSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogTG9vayB1cCBhIG5hbWUgaW4gb25lIHJlc29sdmVkIG1vZHVsZSwgY2hhc2luZyByZS1leHBvcnQgYmFycmVscyB3aXRoIGFcblx0ICogYm91bmRlZCBkZXB0aC4gRXh0ZXJuYWwgKG5vZGVfbW9kdWxlcykgbW9kdWxlcyBob2xkIG5vIGluLXByb2plY3Rcblx0ICogZGVjbGFyYXRpb25zIGFuZCBzdG9wIHRoZSBjaGFzZS5cblx0ICovXG5cdHByaXZhdGUgZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUgKFxuXHRcdG1vZHVsZVBhdGg6IHN0cmluZyxcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0ZGVwdGg6IG51bWJlclxuXHQpOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoZGVwdGggPiBNQVhfUkVFWFBPUlRfQ0hBU0VfREVQVEgpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGVjbHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRGVjbHMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGNvbnN0IGRpcmVjdCA9IGRlY2xzPy5nZXQobmFtZSk7XG5cdFx0aWYgKGRpcmVjdCkge1xuXHRcdFx0cmV0dXJuIGRpcmVjdDtcblx0XHR9XG5cdFx0Ly8gZXhwb3J0IHsgWCBhcyBZIH0g4oCUIHJlc29sdmUgdGhyb3VnaCB0aGUgbG9jYWwgbmFtZVxuXHRcdGNvbnN0IGxvY2FsQWxpYXMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0QWxpYXNlcy5nZXQobW9kdWxlUGF0aCk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWxBbGlhcykge1xuXHRcdFx0Y29uc3QgYWxpYXNlZCA9IGRlY2xzPy5nZXQobG9jYWxBbGlhcyk7XG5cdFx0XHRpZiAoYWxpYXNlZCkge1xuXHRcdFx0XHRyZXR1cm4gYWxpYXNlZDtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCByZUV4cG9ydHMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlUmVFeHBvcnRzLmdldChtb2R1bGVQYXRoKTtcblx0XHRjb25zdCByZUV4cG9ydFNwZWNpZmllciA9IHJlRXhwb3J0cz8uZ2V0KG5hbWUpO1xuXHRcdGlmIChyZUV4cG9ydFNwZWNpZmllcikge1xuXHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShyZUV4cG9ydFNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRpZiAobmV4dFJlc29sdXRpb24gJiYgIW5leHRSZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0Y29uc3QgZm91bmQgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgbmFtZSwgZGVwdGggKyAxKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGlmIChzdGFycykge1xuXHRcdFx0Zm9yIChjb25zdCBzdGFyU3BlY2lmaWVyIG9mIHN0YXJzKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoc3RhclNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRcdGlmICghbmV4dFJlc29sdXRpb24gfHwgbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZShuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIG5hbWUsIGRlcHRoICsgMSk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHJlZmVyZW5jZWQgdHlwZSBuYW1lIGFzIHVzZWQgaW4gZnJvbUZpbGUsIGltcG9ydC1hd2FyZTpcblx0ICogICAxLiB0aGUgZmlsZSdzIG93biBpbXBvcnQgc3RhdGVtZW50cyAocmVsYXRpdmUgKyB0c2NvbmZpZyBwYXRocyxcblx0ICogICAgICBjaGFzZWQgdGhyb3VnaCByZS1leHBvcnQgYmFycmVscyksXG5cdCAqICAgMi4gdGhlIGZpbGUncyBsb2NhbCBkZWNsYXJhdGlvbnMsXG5cdCAqICAgMy4gdGhlIHVuaXF1ZSBzYW1lLW5hbWVkIGRlY2xhcmF0aW9uIGFjcm9zcyBzY2FubmVkIGZpbGVzLlxuXHQgKiBSZXR1cm5zIHVuZGVmaW5lZCB3aGVuIG5vdGhpbmcgbWF0Y2hlcyAob3IgdGhlIG1hdGNoIGlzIGFtYmlndW91cyksXG5cdCAqIGluIHdoaWNoIGNhc2UgdGhlIGNhbGxlciBmYWxscyBiYWNrIHRvIGB1bmtub3duYC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRmcm9tRmlsZTogc3RyaW5nXG5cdCk6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdC8vIDEuIHRoZSBmaWxlJ3Mgb3duIGltcG9ydHMgd2luIOKAlCBhbiBpbXBvcnQgaXMgbmV2ZXIgc2hhZG93ZWQgYnkgYVxuXHRcdC8vIHNhbWUtbmFtZWQgbG9jYWwgZGVjbGFyYXRpb24gZWxzZXdoZXJlIGluIHRoZSBwcm9ncmFtIChGMTApXG5cdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLnJlZmVyZW5jZWRUeXBlSW1wb3J0cy5nZXQoZnJvbUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGltcG9ydGVkICYmICFpbXBvcnRlZC5pc05hbWVzcGFjZSkge1xuXHRcdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKGltcG9ydGVkLnNwZWNpZmllciwgZnJvbUZpbGUpO1xuXHRcdFx0aWYgKHJlc29sdXRpb24gJiYgIXJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRjb25zdCBmb3VuZCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5Nb2R1bGUocmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgsIGltcG9ydGVkLm9yaWdpbmFsTmFtZSwgMCk7XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdHJldHVybiBmb3VuZDtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIDIuIGxvY2FsIGRlY2xhcmF0aW9uIGluIHRoZSByZWZlcmVuY2luZyBmaWxlIGl0c2VsZlxuXHRcdGNvbnN0IGxvY2FsID0gdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzLmdldChmcm9tRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWwpIHtcblx0XHRcdHJldHVybiBsb2NhbDtcblx0XHR9XG5cblx0XHQvLyAzLiBwcm9ncmFtLXdpZGUgZmFsbGJhY2ssIHVuaXF1ZSBkZWNsYXJhdGlvbiBvbmx5IOKAlCBhbWJpZ3VpdHkgYW5kXG5cdFx0Ly8gYWJzZW5jZSBib3RoIHlpZWxkIHVuZGVmaW5lZCAodGhlIGNhbGxlciBlbWl0cyBgdW5rbm93bmApLlxuXHRcdC8vIEV4dGVybmFsL2FtYmllbnQgZGVjbGFyYXRpb25zICguZC50cywgbm9kZV9tb2R1bGVzKSBkbyBub3Rcblx0XHQvLyBwYXJ0aWNpcGF0ZTogYSB1c2VyLWxvY2FsIGRlY2xhcmF0aW9uIGFsd2F5cyB3aW5zIG92ZXIgYVxuXHRcdC8vIHBhY2thZ2UtZGVjbGFyZWQgc2FtZS1uYW1lZCB0eXBlICh0aGUgcGxhaW4tVFMgdGllciBvZiB0aGVcblx0XHQvLyBpZGVudGl0eSBsYXc7IGFtYmlndWl0eSBhbW9uZyB0aGUgcmVtYWluaW5nIGRlY2xhcmF0aW9ucyBpc1xuXHRcdC8vIHZhbGlkYXRlZCBzZXBhcmF0ZWx5IGFzIGEgaGFyZCBmYWlsKVxuXHRcdGxldCB1bmlxdWU6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQ7XG5cdFx0bGV0IGNvdW50ID0gMDtcblx0XHRmb3IgKGNvbnN0IFsgZmlsZVBhdGgsIGRlY2xzIF0gb2YgdGhpcy5yZWZlcmVuY2VkVHlwZURlY2xzKSB7XG5cdFx0XHRpZiAodGhpcy5pc0V4dGVybmFsRGVjbEZpbGUoZmlsZVBhdGgpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgY2FuZGlkYXRlID0gZGVjbHMuZ2V0KG5hbWUpO1xuXHRcdFx0aWYgKGNhbmRpZGF0ZSkge1xuXHRcdFx0XHRjb3VudCsrO1xuXHRcdFx0XHR1bmlxdWUgPSBjYW5kaWRhdGU7XG5cdFx0XHRcdGlmIChjb3VudCA+IDEpIHtcblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVzdWx0ID0gY291bnQgPT09IDEgPyB1bmlxdWUgOiB1bmRlZmluZWQ7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRlcm5hbC9hbWJpZW50IGRlY2xhcmF0aW9uIGZpbGVzICguZC50cywgYW55dGhpbmcgdW5kZXJcblx0ICogbm9kZV9tb2R1bGVzKSBuZXZlciBwYXJ0aWNpcGF0ZSBpbiBwbGFpbi1UUyByZWZlcmVuY2VkLXR5cGVcblx0ICogcmVzb2x1dGlvbiBvciB0aGUgYW1iaWd1aXR5IGxhdzogdGhleSBhcmUgbm90IHByb2plY3Qgc291cmNlLCB0aGVcblx0ICogQ0xJIG5ldmVyIGFuYWx5emVzIHRoZW0sIGFuZCBhIHVzZXItbG9jYWwgZGVjbGFyYXRpb24gYWx3YXlzIHdpbnNcblx0ICogb3ZlciBhIHBhY2thZ2UtZGVjbGFyZWQgc2FtZS1uYW1lZCB0eXBlLlxuXHQgKi9cblx0cHJpdmF0ZSBpc0V4dGVybmFsRGVjbEZpbGUgKGZpbGU6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRcdGNvbnN0IGV4dGVybmFsID0gZmlsZS5lbmRzV2l0aCgnLmQudHMnKSB8fFxuXHRcdFx0ZmlsZS5pbmNsdWRlcyhgJHtub2RlUGF0aC5zZXB9bm9kZV9tb2R1bGVzJHtub2RlUGF0aC5zZXB9YCk7XG5cdFx0cmV0dXJuIGV4dGVybmFsO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb3BlcnRpZXMgb2YgYSByZWZlcmVuY2VkIGNsYXNzL2ludGVyZmFjZS9hbGlhcy1vZi1saXRlcmFsIGRlY2xhcmF0aW9uLFxuXHQgKiBzaGFyZWQgYnkgYHRoaXM6YC1wYXJhbWV0ZXIgZXhwYW5zaW9uIGFuZCBpbmxpbmUgdHlwZSBlbWlzc2lvbi5cblx0ICogSW5oZXJpdGVkIG1lbWJlcnMgYXJlIGluY2x1ZGVkOiB0aGUgZXh0ZW5kcyBjaGFpbiBpcyB3YWxrZWRcblx0ICogKGRlcHRoLWNhcHBlZCwgY3ljbGUtZ3VhcmRlZCkgYW5kIHBhcmVudCBmaWVsZHMgbWVyZ2UgZmlyc3QsIHRoZVxuXHQgKiBkZWNsYXJhdGlvbidzIG93biBmaWVsZHMgb3ZlcnJpZGluZyBvbiBuYW1lIGNsYXNoLlxuXHQgKi9cblx0cHJpdmF0ZSByZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzIChkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKTpcblx0XHRNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCB2aXNpdGVkID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IHRoaXMucmVmZXJlbmNlZERlY2xhcmF0aW9uUHJvcGVydGllc0lubmVyKGRlY2wsIHZpc2l0ZWQsIDApO1xuXHRcdHJldHVybiBwcm9wZXJ0aWVzO1xuXHR9XG5cblx0cHJpdmF0ZSByZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzSW5uZXIgKFxuXHRcdGRlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24sXG5cdFx0dmlzaXRlZDogU2V0PHN0cmluZz4sXG5cdFx0ZGVwdGg6IG51bWJlclxuXHQpOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCBvd25Qcm9wZXJ0aWVzID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblx0XHRjb25zdCBkZWNsTm9kZSA9IGRlY2wubm9kZSBhcyB0cy5DbGFzc0RlY2xhcmF0aW9uIHwgdHMuSW50ZXJmYWNlRGVjbGFyYXRpb247XG5cdFx0Y29uc3QgZGVjbE5hbWUgPSBkZWNsTm9kZS5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihkZWNsTm9kZS5uYW1lKSA/IGRlY2xOb2RlLm5hbWUudGV4dCA6ICcnO1xuXHRcdGNvbnN0IHZpc2l0S2V5ID0gYCR7ZGVjbC5raW5kfToke2RlY2wuZmlsZX06JHtkZWNsTmFtZX1gO1xuXHRcdGlmIChkZXB0aCA+IE1BWF9IRVJJVEFHRV9ERVBUSCB8fCB2aXNpdGVkLmhhcyh2aXNpdEtleSkpIHtcblx0XHRcdHJldHVybiBvd25Qcm9wZXJ0aWVzO1xuXHRcdH1cblx0XHR2aXNpdGVkLmFkZCh2aXNpdEtleSk7XG5cblx0XHRpZiAoZGVjbC5raW5kID09PSAnY2xhc3MnKSB7XG5cdFx0XHRjb25zdCBjbGFzc1Byb3BzID0gdGhpcy5leHRyYWN0Q2xhc3NQcm9wZXJ0aWVzKGRlY2wubm9kZSBhcyB0cy5DbGFzc0RlY2xhcmF0aW9uKTtcblx0XHRcdGZvciAoY29uc3QgWyBuYW1lLCBpbmZvIF0gb2YgY2xhc3NQcm9wcykge1xuXHRcdFx0XHRvd25Qcm9wZXJ0aWVzLnNldChuYW1lLCBpbmZvKTtcblx0XHRcdH1cblx0XHR9IGVsc2UgaWYgKGRlY2wua2luZCA9PT0gJ2ludGVyZmFjZScpIHtcblx0XHRcdGNvbnN0IGlmYWNlID0gZGVjbC5ub2RlIGFzIHRzLkludGVyZmFjZURlY2xhcmF0aW9uO1xuXHRcdFx0dGhpcy5jb2xsZWN0VHlwZUVsZW1lbnRQcm9wZXJ0aWVzKFsgLi4uaWZhY2UubWVtYmVycyBdLCBvd25Qcm9wZXJ0aWVzKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0Y29uc3QgYWxpYXNUeXBlID0gKGRlY2wubm9kZSBhcyB0cy5UeXBlQWxpYXNEZWNsYXJhdGlvbikudHlwZTtcblx0XHRcdGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZShhbGlhc1R5cGUpKSB7XG5cdFx0XHRcdHRoaXMuY29sbGVjdFR5cGVFbGVtZW50UHJvcGVydGllcyhbIC4uLmFsaWFzVHlwZS5tZW1iZXJzIF0sIG93blByb3BlcnRpZXMpO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0cmV0dXJuIG93blByb3BlcnRpZXM7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gaGVyaXRhZ2UgbWVyZ2VzIHBhcmVudCBmaWVsZHMgZmlyc3Q7IHRoZSBkZWNsYXJhdGlvbidzIG93biBmaWVsZHNcblx0XHQvLyBvdmVycmlkZSBvbiBuYW1lIGNsYXNoIChsYXRlciBiYXNlcyBvdmVycmlkZSBlYXJsaWVyIG9uZXMpXG5cdFx0Y29uc3QgbWVyZ2VkID0gbmV3IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4oKTtcblx0XHRmb3IgKGNvbnN0IGJhc2VEZWNsIG9mIHRoaXMucmVzb2x2ZUhlcml0YWdlRGVjbGFyYXRpb25zKGRlY2wpKSB7XG5cdFx0XHRjb25zdCBiYXNlUHJvcHMgPSB0aGlzLnJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXNJbm5lcihiYXNlRGVjbCwgdmlzaXRlZCwgZGVwdGggKyAxKTtcblx0XHRcdGZvciAoY29uc3QgWyBuYW1lLCBpbmZvIF0gb2YgYmFzZVByb3BzKSB7XG5cdFx0XHRcdG1lcmdlZC5zZXQobmFtZSwgaW5mbyk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGZvciAoY29uc3QgWyBuYW1lLCBpbmZvIF0gb2Ygb3duUHJvcGVydGllcykge1xuXHRcdFx0bWVyZ2VkLnNldChuYW1lLCBpbmZvKTtcblx0XHR9XG5cdFx0cmV0dXJuIG1lcmdlZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBQcm9wZXJ0eSBzaWduYXR1cmVzIG9mIGludGVyZmFjZS9hbGlhcyB0eXBlLWxpdGVyYWwgbWVtYmVycywgaW50b1xuXHQgKiB0aGUgZ2l2ZW4gbWFwLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0VHlwZUVsZW1lbnRQcm9wZXJ0aWVzIChcblx0XHRtZW1iZXJzOiByZWFkb25seSB0cy5UeXBlRWxlbWVudFtdLFxuXHRcdHByb3BlcnRpZXM6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz5cblx0KTogdm9pZCB7XG5cdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgbWVtYmVycykge1xuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlTaWduYXR1cmUobWVtYmVyKSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0cHJvcGVydGllcy5zZXQocHJvcE5hbWUsIHtcblx0XHRcdFx0XHRuYW1lICAgICA6IHByb3BOYW1lLFxuXHRcdFx0XHRcdHR5cGUsXG5cdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0aGUgaGVyaXRhZ2UgY2xhdXNlIG9mIGEgY2xhc3MgKGBleHRlbmRzIEJhc2VgKSBvciBpbnRlcmZhY2Vcblx0ICogKGBleHRlbmRzIEEsIEJgKSB0byByZWZlcmVuY2VkLXR5cGUgZGVjbGFyYXRpb25zIHRocm91Z2ggdGhlIFNBTUVcblx0ICogaW1wb3J0LWF3YXJlIG1hY2hpbmVyeSBhcyBwbGFpbiByZWZlcmVuY2VzICh0aGUgZGVjbGFyaW5nIGZpbGUncyBvd25cblx0ICogaW1wb3J0cyBmaXJzdCwgdGhlbiBpdHMgbG9jYWxzLCB0aGVuIHRoZSB1bmlxdWUgcHJvZ3JhbS13aWRlXG5cdCAqIGRlY2xhcmF0aW9uKS4gVW5yZXNvbHZhYmxlIG9yIGV4dGVybmFsIGJhc2VzIHlpZWxkIG5vdGhpbmcg4oCUIHRoZWlyXG5cdCAqIGluaGVyaXRlZCBmaWVsZHMgc2ltcGx5IHN0YXkgYWJzZW50LCBzYW1lIGFzIGJlZm9yZSB0aGlzIHdhbGtcblx0ICogZXhpc3RlZC4gTWl4aW4gY2FsbHMgKGBleHRlbmRzIG1peGluKFgpYCkgYW5kIG5hbWVzcGFjZSBhY2Nlc3MgYXJlXG5cdCAqIG5vdCBmb2xsb3dlZC5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUhlcml0YWdlRGVjbGFyYXRpb25zIChkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKTogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbltdIHtcblx0XHRjb25zdCB7IGhlcml0YWdlQ2xhdXNlcyB9ID0gKGRlY2wubm9kZSBhcyB0cy5DbGFzc0RlY2xhcmF0aW9uIHwgdHMuSW50ZXJmYWNlRGVjbGFyYXRpb24pO1xuXHRcdGlmICghaGVyaXRhZ2VDbGF1c2VzKSB7XG5cdFx0XHRyZXR1cm4gW107XG5cdFx0fVxuXHRcdGNvbnN0IGJhc2VzOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IGNsYXVzZSBvZiBoZXJpdGFnZUNsYXVzZXMpIHtcblx0XHRcdGlmIChjbGF1c2UudG9rZW4gIT09IHRzLlN5bnRheEtpbmQuRXh0ZW5kc0tleXdvcmQpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRmb3IgKGNvbnN0IGhlcml0YWdlVHlwZSBvZiBjbGF1c2UudHlwZXMpIHtcblx0XHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoaGVyaXRhZ2VUeXBlLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgYmFzZU5hbWUgPSBoZXJpdGFnZVR5cGUuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHRjb25zdCBiYXNlRGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oYmFzZU5hbWUsIGRlY2wuZmlsZSk7XG5cdFx0XHRcdGlmIChiYXNlRGVjbCkge1xuXHRcdFx0XHRcdGJhc2VzLnB1c2goYmFzZURlY2wpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGJhc2VzO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogRXhwYW5kIGEgcmVmZXJlbmNlZC10eXBlIGRlY2xhcmF0aW9uIHRvIGEgc2VsZi1jb250YWluZWQgdHlwZSBzdHJpbmdcblx0ICogZm9yIGVtaXNzaW9uIGludG8gZ2VuZXJhdGVkIGZpbGVzOiB0eXBlIGFsaWFzZXMgdGhyb3VnaCBpbmZlclR5cGUsXG5cdCAqIGNsYXNzZXMgYW5kIGludGVyZmFjZXMgdGhyb3VnaCB0aGVpciAocHVibGljLCBub24tbWV0aG9kKSBmaWVsZHMuXG5cdCAqIE5lc3RlZCByZWZlcmVuY2VzIHJlc29sdmUgYWdhaW5zdCB0aGUgZGVjbGFyaW5nIGZpbGUgd2hpbGUgZXhwYW5kaW5nLlxuXHQgKi9cblx0cHJpdmF0ZSBleHBhbmRSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uIChkZWNsOiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCByZWZlcmVuY2luZ0ZpbGUgPSB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGU7XG5cdFx0dGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlID0gZGVjbC5maWxlO1xuXHRcdHRyeSB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25Jbm5lcihkZWNsKTtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fSBmaW5hbGx5IHtcblx0XHRcdHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSA9IHJlZmVyZW5jaW5nRmlsZTtcblx0XHR9XG5cdH1cblxuXHRwcml2YXRlIGV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb25Jbm5lciAoZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKGRlY2wua2luZCA9PT0gJ2FsaWFzJykge1xuXHRcdFx0Y29uc3QgYWxpYXNOb2RlID0gZGVjbC5ub2RlIGFzIHRzLlR5cGVBbGlhc0RlY2xhcmF0aW9uO1xuXHRcdFx0Y29uc3QgYWxpYXNOYW1lID0gdHMuaXNJZGVudGlmaWVyKGFsaWFzTm9kZS5uYW1lKSA/IGFsaWFzTm9kZS5uYW1lLnRleHQgOiAnJztcblx0XHRcdGlmIChhbGlhc05hbWUgJiYgdGhpcy5leHBhbmRpbmdSZWZlcmVuY2VkQWxpYXNlcy5oYXMoYWxpYXNOYW1lKSkge1xuXHRcdFx0XHQvLyBTZWxmLXJlZmVyZW50aWFsIGFsaWFzIGNoYWluIOKAlCBiYWlsIG91dFxuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGFsaWFzTmFtZSkge1xuXHRcdFx0XHR0aGlzLmV4cGFuZGluZ1JlZmVyZW5jZWRBbGlhc2VzLmFkZChhbGlhc05hbWUpO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmluZmVyVHlwZShhbGlhc05vZGUudHlwZSk7XG5cdFx0XHRpZiAoYWxpYXNOYW1lKSB7XG5cdFx0XHRcdHRoaXMuZXhwYW5kaW5nUmVmZXJlbmNlZEFsaWFzZXMuZGVsZXRlKGFsaWFzTmFtZSk7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gZXhwYW5kZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGVjbFByb3BlcnRpZXMgPSB0aGlzLnJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXMoZGVjbCk7XG5cdFx0Y29uc3QgcHJvcHMgPSBBcnJheS5mcm9tKGRlY2xQcm9wZXJ0aWVzLmVudHJpZXMoKSkubWFwKChbIHByb3BOYW1lLCBpbmZvIF0pID0+IHtcblx0XHRcdGNvbnN0IG9wdGlvbmFsID0gaW5mby5vcHRpb25hbCA/ICc/JyA6ICcnO1xuXHRcdFx0cmV0dXJuIGAke3Byb3BOYW1lfSR7b3B0aW9uYWx9OiAke2luZm8udHlwZX1gO1xuXHRcdH0pO1xuXG5cdFx0Y29uc3QgcmVzdWx0ID0gYHsgJHtwcm9wcy5qb2luKCc7ICcpfSB9YDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSBzaW1wbGUgKG5vbi1xdWFsaWZpZWQpIHR5cGUgcmVmZXJlbmNlOiBpbXBvcnQtYXdhcmVcblx0ICogZGVjbGFyYXRpb24gZXhwYW5zaW9uIGZpcnN0LCB0aGVuIHRoZSBJbnN0YW5jZVR5cGU8dHlwZW9mIFg+IHBhdHRlcm4sXG5cdCAqIHRoZW4gbW5lbW9uaWNhIGdyYXBoIHR5cGVzOyBrbm93biBnbG9iYWxzIGtlZXAgdGhlaXIgYmFyZSBuYW1lIGFuZFxuXHQgKiBhbnl0aGluZyBlbHNlIGZhbGxzIGJhY2sgdG8gYHVua25vd25gIHNvIGdlbmVyYXRlZCBmaWxlcyBuZXZlciBjYXJyeVxuXHQgKiBhbiB1bnJlc29sdmFibGUgYmFyZSBuYW1lLiBSZXR1cm5zIHVuZGVmaW5lZCB3aGVuIHRoZSBjYWxsZXIgc2hvdWxkXG5cdCAqIGtlZXAgdGhlIGdlbmVyaWMgc3BlbGxpbmcgKGhhbmRsZWQgc2VwYXJhdGVseSkuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVTaW1wbGVUeXBlUmVmZXJlbmNlIChcblx0XHR0eXBlTmFtZTogc3RyaW5nLFxuXHRcdHR5cGVBcmdzPzogdHMuTm9kZUFycmF5PHRzLlR5cGVOb2RlPixcblx0XHRyZWZOb2RlPzogdHMuTm9kZVxuXHQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdC8vIEltcG9ydC1hd2FyZSByZWZlcmVuY2VkLXR5cGUgZGVjbGFyYXRpb24gKEYxMClcblx0XHRjb25zdCBkZWNsID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbih0eXBlTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRpZiAoZGVjbCkge1xuXHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oZGVjbCk7XG5cdFx0XHRpZiAoZXhwYW5kZWQgIT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRyZXR1cm4gZXhwYW5kZWQ7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCB1bmtub3duUmVzdWx0ID0gJ3Vua25vd24nO1xuXHRcdFx0cmV0dXJuIHVua25vd25SZXN1bHQ7XG5cdFx0fVxuXG5cdFx0Ly8gTW5lbW9uaWNhLWdyYXBoIGlkZW50aXR5IGxhdzogcGF0aC1hd2FyZSByZXNvbHV0aW9uICh2YWx1ZSBzY29wZSxcblx0XHQvLyBpbXBvcnRzLCBuZWFyZXN0LWNoYWluLCByb290LCBwcm9ncmFtLXdpZGUpLiBBbWJpZ3VpdHkgYmV0d2VlblxuXHRcdC8vIHJlYWwgZ3JhcGggdHlwZXMgaXMgYSBoYXJkIGZhaWx1cmU7IGEgbmFtZSBubyBncmFwaCB0eXBlIGNhcnJpZXNcblx0XHQvLyBzdGF5cyBpbiB0aGUgcGxhaW4tVFMgc29mdCBzY29wZSBhbmQgZmFsbHMgdG8gYHVua25vd25gLlxuXHRcdGNvbnN0IGdyYXBoUmVzdWx0ID0gdGhpcy5yZXNvbHZlR3JhcGhUeXBlTmFtZSh0eXBlTmFtZSk7XG5cdFx0aWYgKGdyYXBoUmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdC8vIEhhbmRsZSBJbnN0YW5jZVR5cGU8dHlwZW9mIFg+IHBhdHRlcm4gLT4gY29udmVydCB0byBQYXJlbnRfWFxuXHRcdFx0aWYgKHR5cGVOYW1lID09PSAnSW5zdGFuY2VUeXBlJyAmJiB0eXBlQXJncyAmJiB0eXBlQXJncy5sZW5ndGggPT09IDEpIHtcblx0XHRcdFx0Y29uc3QgWyBhcmcgXSA9IHR5cGVBcmdzO1xuXHRcdFx0XHRpZiAoYXJnLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuVHlwZVF1ZXJ5KSB7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZVF1ZXJ5ID0gYXJnIGFzIHRzLlR5cGVRdWVyeU5vZGU7XG5cdFx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcih0eXBlUXVlcnkuZXhwck5hbWUpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBxdWVyeVJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUodHlwZVF1ZXJ5LmV4cHJOYW1lLnRleHQpO1xuXHRcdFx0XHRcdFx0aWYgKHF1ZXJ5UmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdFx0XHRcdFx0Ly8gQ29udmVydCBmdWxsIHBhdGggd2l0aCBkb3RzIHRvIHVuZGVyc2NvcmVzOiBVc2FnZXMuVXNhZ2VFbnRyeSAtPiBVc2FnZXNfVXNhZ2VFbnRyeVxuXHRcdFx0XHRcdFx0XHRyZXR1cm4gcXVlcnlSZXN1bHQubm9kZS5mdWxsUGF0aC5yZXBsYWNlKC9cXC4vZywgJ18nKTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdGlmIChxdWVyeVJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHRcdFx0XHRcdHRoaXMucmVjb3JkR3JhcGhSZWZlcmVuY2VFcnJvcih0eXBlUXVlcnkuZXhwck5hbWUudGV4dCwgdHlwZVF1ZXJ5LCBxdWVyeVJlc3VsdCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHQvLyBOb3QgYSBrbm93biBtbmVtb25pY2EgdHlwZSDigJQgbm8gYmFyZSBlbWlzc2lvblxuXHRcdFx0XHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGlmICghdHlwZUFyZ3MgfHwgdHlwZUFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRcdC8vIENvbnZlcnQgZnVsbCBwYXRoIHdpdGggZG90cyB0byB1bmRlcnNjb3JlczogVXNhZ2VzLlVzYWdlRW50cnkgLT4gVXNhZ2VzX1VzYWdlRW50cnlcblx0XHRcdFx0cmV0dXJuIGdyYXBoUmVzdWx0Lm5vZGUuZnVsbFBhdGgucmVwbGFjZSgvXFwuL2csICdfJyk7XG5cdFx0XHR9XG5cdFx0XHQvLyBHZW5lcmljIHVzZSBvZiBhIGdyYXBoIHR5cGUga2VlcHMgaXRzIHNpbXBsZSBuYW1lOyB0aGVcblx0XHRcdC8vIGdlbmVyYXRvciB1cGdyYWRlcyBpdCB0byB0aGUgZnVsbC1wYXRoIGluc3RhbmNlIHR5cGUgbmFtZVxuXHRcdFx0cmV0dXJuIGAke3R5cGVOYW1lfTwke3R5cGVBcmdzLm1hcChhID0+IHRoaXMuaW5mZXJUeXBlKGEpKS5qb2luKCcsICcpfT5gO1xuXHRcdH1cblx0XHRpZiAoZ3JhcGhSZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0dGhpcy5yZWNvcmRHcmFwaFJlZmVyZW5jZUVycm9yKHR5cGVOYW1lLCByZWZOb2RlID8/IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSwgZ3JhcGhSZXN1bHQpO1xuXHRcdH1cblxuXHRcdGlmICh0eXBlQXJncyAmJiB0eXBlQXJncy5sZW5ndGggPiAwKSB7XG5cdFx0XHRpZiAoS05PV05fR0xPQkFMX1RZUEVTLmhhcyh0eXBlTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgZ2VuZXJpY1Jlc3VsdCA9IGAke3R5cGVOYW1lfTwke3R5cGVBcmdzLm1hcChhID0+IHRoaXMuaW5mZXJUeXBlKGEpKS5qb2luKCcsICcpfT5gO1xuXHRcdFx0XHRyZXR1cm4gZ2VuZXJpY1Jlc3VsdDtcblx0XHRcdH1cblx0XHRcdC8vIEdlbmVyaWMgcmVmZXJlbmNlIHRvIGEgbm9uLWdsb2JhbCwgbm9uLWdyYXBoIHR5cGUgY2Fubm90IGJlXG5cdFx0XHQvLyBlbWl0dGVkIGJhcmUgaW50byB0aGUgZ2VuZXJhdGVkIGZpbGVcblx0XHRcdGlmIChyZWZOb2RlKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSh0eXBlTmFtZSwgcmVmTm9kZSk7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblxuXHRcdGNvbnN0IGZhbGxiYWNrUmVzdWx0ID0gdGhpcy51bnJlc29sdmVkVHlwZVJlZmVyZW5jZUZhbGxiYWNrKHR5cGVOYW1lLCByZWZOb2RlKTtcblx0XHRyZXR1cm4gZmFsbGJhY2tSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHF1YWxpZmllZCB0eXBlIHJlZmVyZW5jZSAobW9kZWxzLklubmVyLkNyYXRlKSB0aHJvdWdoIHRoZVxuXHQgKiBjdXJyZW50IGZpbGUncyBuYW1lc3BhY2UgaW1wb3J0cy4gVGhlIGNoYWluJ3MgaGVhZCBtdXN0IGJlIGEgbmFtZXNwYWNlXG5cdCAqIGltcG9ydDsgbWlkZGxlIHNlZ21lbnRzIGRlc2NlbmQgdGhyb3VnaCBuYW1lc3BhY2UgZGVjbGFyYXRpb25zLCBuYW1lZFxuXHQgKiByZS1leHBvcnRzIG9mIG5hbWVzcGFjZXMsIGFuZCBgZXhwb3J0ICogYXMgbnMgZnJvbSAn4oCmJ2AgYmFycmVscyAoZWFjaFxuXHQgKiBzZWdtZW50IGNvbnN1bWVkIGV4YWN0bHkgb25jZSwgc28gdGhlIHdhbGsgY2Fubm90IGN5Y2xlKTsgdGhlIGZpbmFsXG5cdCAqIHNlZ21lbnQgcmVzb2x2ZXMgdG8gYSBkZWNsYXJhdGlvbiB3aGljaCBpcyBleHBhbmRlZCBpbmxpbmUuIFdoZW4gdGhlXG5cdCAqIHByZWNpc2Ugd2FsayBmaW5kcyBub3RoaW5nLCB0aGUgbGVnYWN5IHJpZ2h0bW9zdC1uYW1lIGxvb2t1cCBpbiB0aGVcblx0ICogaGVhZCBtb2R1bGUga2VlcHMgb25lLWxldmVsIGZvcm1zIChtb2RlbHMuVHlwZSkgd29ya2luZyDigJQgbmVzdGVkXG5cdCAqIGRlY2xhcmF0aW9ucyBhcmUgcmVjb3JkZWQgYnkgcGxhaW4gbmFtZSB0aGVyZSB0b28uIFJldHVybnMgdW5kZWZpbmVkXG5cdCAqIHdoZW4gdGhlIGhlYWQgaXMgbm90IGEgbmFtZXNwYWNlIGltcG9ydCBvciBub3RoaW5nIHJlc29sdmVzLlxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlclF1YWxpZmllZFR5cGVSZWZlcmVuY2UgKHR5cGVSZWY6IHRzLlR5cGVSZWZlcmVuY2VOb2RlKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIXRzLmlzUXVhbGlmaWVkTmFtZSh0eXBlUmVmLnR5cGVOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBmbGF0dGVuIHRoZSBxdWFsaWZpZWQgbmFtZSBjaGFpbjogbW9kZWxzLklubmVyLkNyYXRlIOKGkiBbJ21vZGVscycsICdJbm5lcicsICdDcmF0ZSddXG5cdFx0Y29uc3Qgc2VnbWVudHM6IHN0cmluZ1tdID0gW107XG5cdFx0bGV0IGNoYWluOiB0cy5FbnRpdHlOYW1lID0gdHlwZVJlZi50eXBlTmFtZTtcblx0XHR3aGlsZSAodHMuaXNRdWFsaWZpZWROYW1lKGNoYWluKSkge1xuXHRcdFx0c2VnbWVudHMudW5zaGlmdChjaGFpbi5yaWdodC50ZXh0KTtcblx0XHRcdGNoYWluID0gY2hhaW4ubGVmdDtcblx0XHR9XG5cdFx0c2VnbWVudHMudW5zaGlmdChjaGFpbi50ZXh0KTtcblxuXHRcdGNvbnN0IG5hbWVzcGFjZUltcG9ydCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQoc2VnbWVudHNbIDAgXSk7XG5cdFx0aWYgKCFuYW1lc3BhY2VJbXBvcnQgfHwgIW5hbWVzcGFjZUltcG9ydC5pc05hbWVzcGFjZSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUobmFtZXNwYWNlSW1wb3J0LnNwZWNpZmllciwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRpZiAoIXJlc29sdXRpb24gfHwgcmVzb2x1dGlvbi5pc0V4dGVybmFsKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIGRlc2NlbmQgdGhlIG1pZGRsZSBzZWdtZW50czogYSBtb2R1bGUgY29udGV4dCByZXNvbHZlcyB0aGUgc2VnbWVudFxuXHRcdC8vIGFzIGEgbmFtZXNwYWNlIGRlY2xhcmF0aW9uIC8gbmFtZXNwYWNlIHJlLWV4cG9ydDsgYSBuYW1lc3BhY2UtYmxvY2tcblx0XHQvLyBjb250ZXh0IHJlc29sdmVzIGl0IGFzIGEgbmVzdGVkIG5hbWVzcGFjZSBkZWNsYXJhdGlvblxuXHRcdGxldCBxdWFsaWZpZXI6IHsgbW9kdWxlUGF0aDogc3RyaW5nOyBibG9jaz86IHRzLk1vZHVsZUJsb2NrIH0gfCB1bmRlZmluZWQgPSB7XG5cdFx0XHRtb2R1bGVQYXRoIDogcmVzb2x1dGlvbi5yZXNvbHZlZFBhdGhcblx0XHR9O1xuXHRcdGZvciAobGV0IGkgPSAxOyBpIDwgc2VnbWVudHMubGVuZ3RoIC0gMSAmJiBxdWFsaWZpZXI7IGkrKykge1xuXHRcdFx0Y29uc3Qgc2VnbWVudCA9IHNlZ21lbnRzWyBpIF07XG5cdFx0XHRpZiAocXVhbGlmaWVyLmJsb2NrKSB7XG5cdFx0XHRcdGNvbnN0IG5lc3RlZCA9IHRoaXMuZmluZE5hbWVzcGFjZUluQmxvY2socXVhbGlmaWVyLmJsb2NrLCBzZWdtZW50KTtcblx0XHRcdFx0aWYgKG5lc3RlZD8uYm9keSAmJiB0cy5pc01vZHVsZUJsb2NrKG5lc3RlZC5ib2R5KSkge1xuXHRcdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IHF1YWxpZmllci5tb2R1bGVQYXRoLCBibG9jayA6IG5lc3RlZC5ib2R5IH07XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0cXVhbGlmaWVyID0gdW5kZWZpbmVkO1xuXHRcdFx0XHRicmVhaztcblx0XHRcdH1cblx0XHRcdGNvbnN0IG5hbWVzcGFjZURlY2w6IHRzLk1vZHVsZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkID1cblx0XHRcdFx0dGhpcy5yZWZlcmVuY2VkVHlwZU5hbWVzcGFjZXMuZ2V0KHF1YWxpZmllci5tb2R1bGVQYXRoKT8uZ2V0KHNlZ21lbnQpO1xuXHRcdFx0aWYgKG5hbWVzcGFjZURlY2w/LmJvZHkgJiYgdHMuaXNNb2R1bGVCbG9jayhuYW1lc3BhY2VEZWNsLmJvZHkpKSB7XG5cdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IHF1YWxpZmllci5tb2R1bGVQYXRoLCBibG9jayA6IG5hbWVzcGFjZURlY2wuYm9keSB9O1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHN0YXJTcGVjaWZpZXIgPSB0aGlzLnJlZmVyZW5jZWRUeXBlTmFtZXNwYWNlU3RhcnMuZ2V0KHF1YWxpZmllci5tb2R1bGVQYXRoKT8uZ2V0KHNlZ21lbnQpO1xuXHRcdFx0aWYgKHN0YXJTcGVjaWZpZXIpIHtcblx0XHRcdFx0Y29uc3QgbmV4dFJlc29sdXRpb24gPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZU1vZHVsZShzdGFyU3BlY2lmaWVyLCBxdWFsaWZpZXIubW9kdWxlUGF0aCk7XG5cdFx0XHRcdGlmIChuZXh0UmVzb2x1dGlvbiAmJiAhbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRcdHF1YWxpZmllciA9IHsgbW9kdWxlUGF0aCA6IG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCB9O1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRjb25zdCByZUV4cG9ydFNwZWNpZmllciA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuZ2V0KHF1YWxpZmllci5tb2R1bGVQYXRoKT8uZ2V0KHNlZ21lbnQpO1xuXHRcdFx0aWYgKHJlRXhwb3J0U3BlY2lmaWVyKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUocmVFeHBvcnRTcGVjaWZpZXIsIHF1YWxpZmllci5tb2R1bGVQYXRoKTtcblx0XHRcdFx0Y29uc3QgcmVFeHBvcnRlZDogdHMuTW9kdWxlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQgPVxuXHRcdFx0XHRcdG5leHRSZXNvbHV0aW9uICYmICFuZXh0UmVzb2x1dGlvbi5pc0V4dGVybmFsXG5cdFx0XHRcdFx0XHQ/IHRoaXMucmVmZXJlbmNlZFR5cGVOYW1lc3BhY2VzLmdldChuZXh0UmVzb2x1dGlvbi5yZXNvbHZlZFBhdGgpPy5nZXQoc2VnbWVudClcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0XHRpZiAocmVFeHBvcnRlZD8uYm9keSAmJiB0cy5pc01vZHVsZUJsb2NrKHJlRXhwb3J0ZWQuYm9keSkpIHtcblx0XHRcdFx0XHRxdWFsaWZpZXIgPSB7IG1vZHVsZVBhdGggOiBuZXh0UmVzb2x1dGlvbiEucmVzb2x2ZWRQYXRoLCBibG9jayA6IHJlRXhwb3J0ZWQuYm9keSB9O1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRxdWFsaWZpZXIgPSB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZmluYWxOYW1lID0gc2VnbWVudHNbIHNlZ21lbnRzLmxlbmd0aCAtIDEgXTtcblx0XHRsZXQgZGVjbDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZDtcblx0XHRpZiAocXVhbGlmaWVyPy5ibG9jaykge1xuXHRcdFx0ZGVjbCA9IHRoaXMuZmluZFJlZmVyZW5jZWRUeXBlSW5CbG9jayhxdWFsaWZpZXIuYmxvY2ssIHF1YWxpZmllci5tb2R1bGVQYXRoLCBmaW5hbE5hbWUpO1xuXHRcdH0gZWxzZSBpZiAocXVhbGlmaWVyKSB7XG5cdFx0XHRkZWNsID0gdGhpcy5maW5kUmVmZXJlbmNlZFR5cGVJbk1vZHVsZShxdWFsaWZpZXIubW9kdWxlUGF0aCwgZmluYWxOYW1lLCAwKTtcblx0XHR9XG5cdFx0Ly8gbGVnYWN5IGZhbGxiYWNrOiByaWdodG1vc3QgbmFtZSBhbnl3aGVyZSBpbiB0aGUgaGVhZCBtb2R1bGVcblx0XHQvLyAobmFtZXNwYWNlLW5lc3RlZCBkZWNsYXJhdGlvbnMgYXJlIGFsc28gcmVjb3JkZWQgYnkgcGxhaW4gbmFtZSlcblx0XHRpZiAoIWRlY2wpIHtcblx0XHRcdGRlY2wgPSB0aGlzLmZpbmRSZWZlcmVuY2VkVHlwZUluTW9kdWxlKHJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBmaW5hbE5hbWUsIDApO1xuXHRcdH1cblx0XHRpZiAoIWRlY2wpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oZGVjbCk7XG5cdFx0cmV0dXJuIGV4cGFuZGVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpbmQgYSBuYW1lc3BhY2UgZGVjbGFyYXRpb24gYnkgbmFtZSBkaXJlY3RseSBpbnNpZGUgYSBtb2R1bGUgYmxvY2suXG5cdCAqL1xuXHRwcml2YXRlIGZpbmROYW1lc3BhY2VJbkJsb2NrIChibG9jazogdHMuTW9kdWxlQmxvY2ssIG5hbWU6IHN0cmluZyk6IHRzLk1vZHVsZURlY2xhcmF0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRmb3IgKGNvbnN0IHN0YXRlbWVudCBvZiBibG9jay5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAodHMuaXNNb2R1bGVEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmIHRzLmlzSWRlbnRpZmllcihzdGF0ZW1lbnQubmFtZSkgJiZcblx0XHRcdFx0c3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZSkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQgPSBzdGF0ZW1lbnQ7XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmluZCBhIG5hbWVkIHR5cGUgZGVjbGFyYXRpb24gKGFsaWFzLCBjbGFzcywgaW50ZXJmYWNlKSBkaXJlY3RseSBpbnNpZGVcblx0ICogYSBuYW1lc3BhY2UgYmxvY2sg4oCUIHRoZSBmaW5hbCBzZWdtZW50IG9mIGEgZGVzY2VuZGVkIHF1YWxpZmllZCBjaGFpbi5cblx0ICovXG5cdHByaXZhdGUgZmluZFJlZmVyZW5jZWRUeXBlSW5CbG9jayAoXG5cdFx0YmxvY2s6IHRzLk1vZHVsZUJsb2NrLFxuXHRcdGZpbGVQYXRoOiBzdHJpbmcsXG5cdFx0bmFtZTogc3RyaW5nXG5cdCk6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQge1xuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIGJsb2NrLnN0YXRlbWVudHMpIHtcblx0XHRcdGlmICh0cy5pc1R5cGVBbGlhc0RlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiYgdHMuaXNJZGVudGlmaWVyKHN0YXRlbWVudC5uYW1lKSAmJlxuXHRcdFx0XHRzdGF0ZW1lbnQubmFtZS50ZXh0ID09PSBuYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdDogUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbiA9IHsga2luZCA6ICdhbGlhcycsIG5vZGUgOiBzdGF0ZW1lbnQsIGZpbGUgOiBmaWxlUGF0aCB9O1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0aWYgKHRzLmlzQ2xhc3NEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmIHN0YXRlbWVudC5uYW1lICYmIHN0YXRlbWVudC5uYW1lLnRleHQgPT09IG5hbWUpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0OiBSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uID0geyBraW5kIDogJ2NsYXNzJywgbm9kZSA6IHN0YXRlbWVudCwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNJbnRlcmZhY2VEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmIHRzLmlzSWRlbnRpZmllcihzdGF0ZW1lbnQubmFtZSkgJiZcblx0XHRcdFx0c3RhdGVtZW50Lm5hbWUudGV4dCA9PT0gbmFtZSkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQ6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gPSB7IGtpbmQgOiAnaW50ZXJmYWNlJywgbm9kZSA6IHN0YXRlbWVudCwgZmlsZSA6IGZpbGVQYXRoIH07XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRmFsbGJhY2sgZm9yIGEgdHlwZS1yZWZlcmVuY2UgbmFtZSB0aGF0IHJlc29sdmVzIHRvIG5vIGRlY2xhcmF0aW9uIGFuZFxuXHQgKiBubyBncmFwaCB0eXBlOiBrbm93biBnbG9iYWxzIGtlZXAgdGhlaXIgYmFyZSBuYW1lICh0aGV5IHJlc29sdmUgd2l0aG91dFxuXHQgKiBhbiBpbXBvcnQpOyBldmVyeXRoaW5nIGVsc2UgYmVjb21lcyBgdW5rbm93bmAgc28gZ2VuZXJhdGVkIHR5cGVzLnRzXG5cdCAqIG5ldmVyIGNhcnJpZXMgYW4gdW5yZXNvbHZhYmxlIGJhcmUgbmFtZSAoUkVBRE1FJ3MgZG9jdW1lbnRlZCBiZWhhdmlvcilcblx0ICogYW5kIHRoZSBzaXRlIGlzIHJlY29yZGVkIGZvciB0aGUgcGxhaW4tVFMgYW1iaWd1aXR5IHZhbGlkYXRpb24uXG5cdCAqL1xuXHRwcml2YXRlIHVucmVzb2x2ZWRUeXBlUmVmZXJlbmNlRmFsbGJhY2sgKHR5cGVOYW1lOiBzdHJpbmcsIHJlZk5vZGU/OiB0cy5Ob2RlKTogc3RyaW5nIHtcblx0XHRpZiAoS05PV05fR0xPQkFMX1RZUEVTLmhhcyh0eXBlTmFtZSkpIHtcblx0XHRcdHJldHVybiB0eXBlTmFtZTtcblx0XHR9XG5cdFx0aWYgKHJlZk5vZGUpIHtcblx0XHRcdHRoaXMucmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSh0eXBlTmFtZSwgcmVmTm9kZSk7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9ICd1bmtub3duJztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBvbmUgZGVmaW5lKCkvbGF6eSgpL0BkZWNvcmF0ZSgpIHNpdGUgdW5kZXIgaXRzIHJ1bnRpbWVcblx0ICogbmFtZXNwYWNlIGtleS4gVHdvIHNpdGVzIGluIG9uZSBuYW1lc3BhY2UgYXJlIGEgc2FtZS1uYW1lc3BhY2Vcblx0ICogZHVwbGljYXRlICh0aGUgcnVudGltZSB0aHJvd3MgQUxSRUFEWV9ERUNMQVJFRCk7IGV2ZXJ5IHNpdGUgaXMga2VwdFxuXHQgKiBzbyB0aGUgZmFpbHVyZSBjYW4gcmVwb3J0IGFsbCBsb2NhdGlvbnMuXG5cdCAqL1xuXHRwcml2YXRlIHJlY29yZERlZmluZVNpdGUgKG5hbWVzcGFjZUtleTogc3RyaW5nLCBsb2NhdGlvbjogc3RyaW5nKTogdm9pZCB7XG5cdFx0bGV0IHNpdGVzID0gdGhpcy5kZWZpbmVTaXRlcy5nZXQobmFtZXNwYWNlS2V5KTtcblx0XHRpZiAoIXNpdGVzKSB7XG5cdFx0XHRzaXRlcyA9IFtdO1xuXHRcdFx0dGhpcy5kZWZpbmVTaXRlcy5zZXQobmFtZXNwYWNlS2V5LCBzaXRlcyk7XG5cdFx0fVxuXHRcdGlmICghc2l0ZXMuaW5jbHVkZXMobG9jYXRpb24pKSB7XG5cdFx0XHRzaXRlcy5wdXNoKGxvY2F0aW9uKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogRmF0YWwgcmVzb2x1dGlvbiBmYWlsdXJlcyAoaGFyZC1mYWlsIGxhdyk6IHNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZVxuXHQgKiBtbmVtb25pY2EgZGVmaW5pdGlvbnMgcGx1cyBhbWJpZ3VvdXMvdW5yZXNvbHZlZCBtbmVtb25pY2EtZ3JhcGhcblx0ICogcmVmZXJlbmNlcy4gVGhlIENMSSBwcmludHMgZXZlcnkgbG9jYXRpb24gYW5kIHdyaXRlcyBubyBvdXRwdXQuXG5cdCAqL1xuXHRnZXRSZXNvbHV0aW9uRXJyb3JzICgpOiBSZXNvbHV0aW9uRXJyb3JbXSB7XG5cdFx0dGhpcy52YWxpZGF0ZUxvb2t1cFJlZmVyZW5jZXMoKTtcblx0XHR0aGlzLnZhbGlkYXRlUGxhaW5UeXBlUmVmZXJlbmNlcygpO1xuXHRcdGNvbnN0IGVycm9yczogUmVzb2x1dGlvbkVycm9yW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IFsgbmFtZXNwYWNlS2V5LCBzaXRlcyBdIG9mIHRoaXMuZGVmaW5lU2l0ZXMpIHtcblx0XHRcdGlmIChzaXRlcy5sZW5ndGggPCAyKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZGlzcGxheU5hbWUgPSBuYW1lc3BhY2VLZXkucmVwbGFjZSgvXlteOl0rOjovLCAnJyk7XG5cdFx0XHRjb25zdCBtZXNzYWdlID0gYER1cGxpY2F0ZSBkZWZpbml0aW9uIG9mICcke2Rpc3BsYXlOYW1lfScgaW4gb25lIG5hbWVzcGFjZSDigJQgYCArXG5cdFx0XHRcdCd0aGUgbW5lbW9uaWNhIHJ1bnRpbWUgd291bGQgdGhyb3cgQUxSRUFEWV9ERUNMQVJFRCc7XG5cdFx0XHRlcnJvcnMucHVzaCh7IG1lc3NhZ2UsIGxvY2F0aW9ucyA6IFsgLi4uc2l0ZXMgXSB9KTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBlcnJvciBvZiB0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzKSB7XG5cdFx0XHRlcnJvcnMucHVzaChlcnJvcik7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGVycm9ycztcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYSByZWZlcmVuY2UgdG8gYSBtbmVtb25pY2EgZ3JhcGggdHlwZSBuYW1lLCBpbXBvcnQtYXdhcmUgYW5kXG5cdCAqIHBhdGgtYXdhcmUgKHRoZSBoYXJkLWZhaWwgaWRlbnRpdHkgbGF3LCBtaXJyb3JpbmcgdGhlIHJ1bnRpbWUpOlxuXHQgKiAgIDEuIHZhbHVlIHNjb3BlIOKAlCBhIHRyYWNrZWQgdG9wLWxldmVsIGJpbmRpbmcgaW4gdGhlIHJlZmVyZW5jaW5nIGZpbGVcblx0ICogICAgICAoYGNvbnN0IEFkZHJlc3MgPSBVc2VyLmRlZmluZSgnQWRkcmVzcycsIOKApilgKSxcblx0ICogICAyLiBpbXBvcnQgc2NvcGUg4oCUIGEgYmluZGluZyBleHBvcnRlZCBmcm9tIGEgbW9kdWxlIHRoaXMgZmlsZSBpbXBvcnRzXG5cdCAqICAgICAgKGJhcnJlbHMgY2hhc2VkKSxcblx0ICogICAzLiBuZWFyZXN0LWNoYWluIOKAlCB0aGUgYW5jaG9yIHR5cGUncyBvd24gc3VidHlwZXMgZmlyc3QsIHRoZW4gZWFjaFxuXHQgKiAgICAgIGFuY2VzdG9yIGxldmVsIChyZWxhdGl2ZS1maXJzdCksXG5cdCAqICAgNC4gcm9vdCDigJQgcm9vdHMgb2YgdGhlIGFuY2hvcidzIGNvbGxlY3Rpb24sXG5cdCAqICAgNS4gcHJvZ3JhbS13aWRlIOKAlCBvbmx5IHdoZW4gZXhhY3RseSBvbmUgdHlwZSBjYXJyaWVzIHRoZSBuYW1lLlxuXHQgKiBBbWJpZ3VpdHkgKHNldmVyYWwgY2FuZGlkYXRlcyBhbmQgbm90aGluZyBkaXNhbWJpZ3VhdGVzKSBhbmQgYWJzZW5jZVxuXHQgKiBhcmUgYm90aCByZXR1cm5lZCBhcyBzdWNoIOKAlCB0aGUgY2FsbGVyIHJlY29yZHMgYSBoYXJkIGZhaWx1cmU7IGEgYmFyZVxuXHQgKiBmaXJzdC1tYXRjaCBuYW1lIGlzIG5ldmVyIGVtaXR0ZWQuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVHcmFwaFR5cGVOYW1lIChuYW1lOiBzdHJpbmcpOiBHcmFwaFR5cGVSZWZlcmVuY2VSZXN1bHQge1xuXHRcdC8vIDEuIHZhbHVlIHNjb3BlIGluIHRoZSByZWZlcmVuY2luZyBmaWxlIGl0c2VsZlxuXHRcdGNvbnN0IGxvY2FsQmluZGluZyA9IHRoaXMuZmlsZUdyYXBoQmluZGluZ3MuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChuYW1lKTtcblx0XHRpZiAobG9jYWxCaW5kaW5nKSB7XG5cdFx0XHRjb25zdCBub2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShsb2NhbEJpbmRpbmcpO1xuXHRcdFx0aWYgKG5vZGUpIHtcblx0XHRcdFx0Y29uc3QgdmFsdWVSZXN1bHQ6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCA9IHsgc3RhdHVzIDogJ3VuaXF1ZScsIG5vZGUgfTtcblx0XHRcdFx0cmV0dXJuIHZhbHVlUmVzdWx0O1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIDIuIGltcG9ydCBzY29wZSDigJQgdGhlIGltcG9ydGVkIG1vZHVsZSdzIGV4cG9ydGVkIGJpbmRpbmdcblx0XHRjb25zdCBpbXBvcnRlZCA9IHRoaXMucmVmZXJlbmNlZFR5cGVJbXBvcnRzLmdldCh0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpPy5nZXQobmFtZSk7XG5cdFx0aWYgKGltcG9ydGVkICYmICFpbXBvcnRlZC5pc05hbWVzcGFjZSkge1xuXHRcdFx0Y29uc3QgcmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKGltcG9ydGVkLnNwZWNpZmllciwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdGlmIChyZXNvbHV0aW9uICYmICFyZXNvbHV0aW9uLmlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0Y29uc3QgZnVsbFBhdGggPSB0aGlzLmZpbmRHcmFwaEJpbmRpbmdJbk1vZHVsZShyZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgaW1wb3J0ZWQub3JpZ2luYWxOYW1lLCAwKTtcblx0XHRcdFx0aWYgKGZ1bGxQYXRoKSB7XG5cdFx0XHRcdFx0Y29uc3Qgbm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoZnVsbFBhdGgpO1xuXHRcdFx0XHRcdGlmIChub2RlKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBpbXBvcnRSZXN1bHQ6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCA9IHsgc3RhdHVzIDogJ3VuaXF1ZScsIG5vZGUgfTtcblx0XHRcdFx0XHRcdHJldHVybiBpbXBvcnRSZXN1bHQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gMy01LiBjaGFpbiAvIHJvb3QgLyBwcm9ncmFtLXdpZGUgdGllcnNcblx0XHRjb25zdCByZXN1bHQgPSByZXNvbHZlR3JhcGhUeXBlUmVmZXJlbmNlKHRoaXMuZ3JhcGgsIG5hbWUsIHRoaXMuY3VycmVudEdyYXBoQW5jaG9yKTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEZpbmQgYSBncmFwaCBjb25zdHJ1Y3RvciBiaW5kaW5nIGV4cG9ydGVkIGJ5IGEgcmVzb2x2ZWQgbW9kdWxlLFxuXHQgKiBjaGFzaW5nIHJlLWV4cG9ydCBiYXJyZWxzIHdpdGggYSBib3VuZGVkIGRlcHRoLlxuXHQgKi9cblx0cHJpdmF0ZSBmaW5kR3JhcGhCaW5kaW5nSW5Nb2R1bGUgKG1vZHVsZVBhdGg6IHN0cmluZywgbmFtZTogc3RyaW5nLCBkZXB0aDogbnVtYmVyKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoZGVwdGggPiBNQVhfUkVFWFBPUlRfQ0hBU0VfREVQVEgpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGlyZWN0ID0gdGhpcy5maWxlR3JhcGhCaW5kaW5ncy5nZXQobW9kdWxlUGF0aCk/LmdldChuYW1lKTtcblx0XHRpZiAoZGlyZWN0KSB7XG5cdFx0XHRyZXR1cm4gZGlyZWN0O1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlRXhwb3J0cyA9IHRoaXMucmVmZXJlbmNlZFR5cGVSZUV4cG9ydHMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGNvbnN0IHJlRXhwb3J0U3BlY2lmaWVyID0gcmVFeHBvcnRzPy5nZXQobmFtZSk7XG5cdFx0aWYgKHJlRXhwb3J0U3BlY2lmaWVyKSB7XG5cdFx0XHRjb25zdCBuZXh0UmVzb2x1dGlvbiA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlTW9kdWxlKHJlRXhwb3J0U3BlY2lmaWVyLCBtb2R1bGVQYXRoKTtcblx0XHRcdGlmIChuZXh0UmVzb2x1dGlvbiAmJiAhbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRjb25zdCBmb3VuZCA9IHRoaXMuZmluZEdyYXBoQmluZGluZ0luTW9kdWxlKG5leHRSZXNvbHV0aW9uLnJlc29sdmVkUGF0aCwgbmFtZSwgZGVwdGggKyAxKTtcblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3Qgc3RhcnMgPSB0aGlzLnJlZmVyZW5jZWRUeXBlRXhwb3J0U3RhcnMuZ2V0KG1vZHVsZVBhdGgpO1xuXHRcdGlmIChzdGFycykge1xuXHRcdFx0Zm9yIChjb25zdCBzdGFyU3BlY2lmaWVyIG9mIHN0YXJzKSB7XG5cdFx0XHRcdGNvbnN0IG5leHRSZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVNb2R1bGUoc3RhclNwZWNpZmllciwgbW9kdWxlUGF0aCk7XG5cdFx0XHRcdGlmICghbmV4dFJlc29sdXRpb24gfHwgbmV4dFJlc29sdXRpb24uaXNFeHRlcm5hbCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGZvdW5kID0gdGhpcy5maW5kR3JhcGhCaW5kaW5nSW5Nb2R1bGUobmV4dFJlc29sdXRpb24ucmVzb2x2ZWRQYXRoLCBuYW1lLCBkZXB0aCArIDEpO1xuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIFZhbGlkYXRlIGxpdGVyYWwgbG9va3VwKCkgcGF0aHMgcmVjb3JkZWQgZHVyaW5nIHRoZSB1c2FnZXMgcGFzc1xuXHQgKiBhZ2FpbnN0IHRoZSBjb21wbGV0ZSBncmFwaC4gQSBsb29rdXAgcGF0aCBtYXRjaGluZyBubyB0eXBlIGlzIHdoYXQgdGhlXG5cdCAqIHJ1bnRpbWUgYW5zd2VycyB3aXRoIGB1bmRlZmluZWRgIOKAlCB0aGUgVHlwZUVycm9yIGFycml2ZXMgb25lIGxpbmVcblx0ICogbGF0ZXIgYXQgdGhlIGBuZXdgIOKAlCBzbyBpdCBqb2lucyB0aGUgaGFyZC1mYWlsIGxhdy4gVGhlIHJlbGF0aXZlLWZpcnN0XG5cdCAqIHN0ZXAgYWxyZWFkeSByYW4gaW5zaWRlIHJlc29sdmVMb29rdXBQYXRoOyB3aGF0ZXZlciB3YXMgcmVjb3JkZWQgaXNcblx0ICogdGhlIHJvb3QtcmVzb2x1dGlvbiByZXN1bHQsIHNvIGEgcGxhaW4gZmluZFR5cGUgY2hlY2sgaXMgdGhlIGV4YWN0XG5cdCAqIHJ1bnRpbWUgbGF3LiBTYW1lLW5hbWVkIHR5cGVzIGVsc2V3aGVyZSBpbiB0aGUgZ3JhcGggYXJlIGxpc3RlZCBhc1xuXHQgKiBkaWQteW91LW1lYW4gY2FuZGlkYXRlcy4gUnVucyBvbmNlIHBlciB1c2FnZXMgcGFzcyAocmUtYXJtZWQgYnlcblx0ICogcmVzZXRVc2FnZXMpOyBub24tbGl0ZXJhbCBsb29rdXAgYXJndW1lbnRzIGFyZSBuZXZlciByZWNvcmRlZCBhbmRcblx0ICogc3RheSBiZXN0LWVmZm9ydC5cblx0ICovXG5cdHByaXZhdGUgdmFsaWRhdGVMb29rdXBSZWZlcmVuY2VzICgpOiB2b2lkIHtcblx0XHRpZiAodGhpcy5sb29rdXBSZWZlcmVuY2VzVmFsaWRhdGVkKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHRoaXMubG9va3VwUmVmZXJlbmNlc1ZhbGlkYXRlZCA9IHRydWU7XG5cdFx0Ly8gZ3JvdXAgc2l0ZXMgYnkgcGF0aDogZXZlcnkgZmFpbGluZyBzaXRlIG9mIHRoZSBzYW1lIHBhdGggaXMgbGlzdGVkXG5cdFx0Y29uc3Qgc2l0ZXNCeVBhdGggPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nW10+KCk7XG5cdFx0Zm9yIChjb25zdCByZWYgb2YgdGhpcy5sb29rdXBSZWZlcmVuY2VzKSB7XG5cdFx0XHRjb25zdCBzaXRlcyA9IHNpdGVzQnlQYXRoLmdldChyZWYucGF0aCkgPz8gW107XG5cdFx0XHRzaXRlcy5wdXNoKHJlZi5sb2NhdGlvbik7XG5cdFx0XHRzaXRlc0J5UGF0aC5zZXQocmVmLnBhdGgsIHNpdGVzKTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBbIHR5cGVQYXRoLCBzaXRlcyBdIG9mIHNpdGVzQnlQYXRoKSB7XG5cdFx0XHRpZiAodGhpcy5ncmFwaC5maW5kVHlwZSh0eXBlUGF0aCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHQvLyBkaWQteW91LW1lYW46IHR5cGVzIGNhcnJ5aW5nIHRoZSBzYW1lIG5hbWUgYW55d2hlcmUgaW4gdGhlXG5cdFx0XHQvLyBncmFwaCAobmV2ZXIgYSBmaXJzdC1tYXRjaCBwaWNrIOKAlCB0aGUgZnVsbCBsaXN0IG9ubHkpXG5cdFx0XHRjb25zdCB1bnByZWZpeGVkID0gdHlwZVBhdGgucmVwbGFjZSgvXlteOl0rOjovLCAnJyk7XG5cdFx0XHRjb25zdCBsYXN0U2VnbWVudCA9IHVucHJlZml4ZWQuc3BsaXQoJy4nKS5wb3AoKSA/PyB1bnByZWZpeGVkO1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlcyA9IHRoaXMuZ3JhcGguZ2V0QWxsVHlwZXMoKS5maWx0ZXIodCA9PiB0Lm5hbWUgPT09IGxhc3RTZWdtZW50KTtcblx0XHRcdGlmIChjYW5kaWRhdGVzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHRjb25zdCBub25lRXJyb3I6IFJlc29sdXRpb25FcnJvciA9IHtcblx0XHRcdFx0XHRtZXNzYWdlIDogYFVucmVzb2x2ZWQgbG9va3VwIG9mIG1uZW1vbmljYSB0eXBlICcke3R5cGVQYXRofSc6IG5vIHR5cGUgYXQgdGhhdCBwYXRoIOKAlCBgICtcblx0XHRcdFx0XHRcdCd0aGUgcnVudGltZSB3b3VsZCByZXR1cm4gdW5kZWZpbmVkJyxcblx0XHRcdFx0XHRsb2NhdGlvbnMgOiBzaXRlcyxcblx0XHRcdFx0fTtcblx0XHRcdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKG5vbmVFcnJvcik7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgY2FuZGlkYXRlTG9jYXRpb25zID0gY2FuZGlkYXRlcy5tYXAobiA9PiBgJHtuLnNvdXJjZUZpbGV9OiR7bi5saW5lfToke24uY29sdW1ufWApO1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlUGF0aHMgPSBjYW5kaWRhdGVzLm1hcChuID0+IG4uZnVsbFBhdGgpLmpvaW4oJywgJyk7XG5cdFx0XHRjb25zdCBhbWJpZ3VvdXNFcnJvcjogUmVzb2x1dGlvbkVycm9yID0ge1xuXHRcdFx0XHRtZXNzYWdlIDogYFVucmVzb2x2ZWQgbG9va3VwIG9mIG1uZW1vbmljYSB0eXBlICcke3R5cGVQYXRofSc6IHRoZSBydW50aW1lIHdvdWxkIHJldHVybiBgICtcblx0XHRcdFx0XHRgdW5kZWZpbmVkIOKAlCAke2NhbmRpZGF0ZXMubGVuZ3RofSBncmFwaCB0eXBlKHMpIGNhcnJ5IHRoZSBuYW1lIGAgK1xuXHRcdFx0XHRcdGBvZmYtcm9vdCAoJHtjYW5kaWRhdGVQYXRoc30pOyB1c2UgdGhlIGZ1bGwgZG90dGVkIHBhdGhgLFxuXHRcdFx0XHRsb2NhdGlvbnMgOiBbIC4uLnNpdGVzLCAuLi5jYW5kaWRhdGVMb2NhdGlvbnMgXSxcblx0XHRcdH07XG5cdFx0XHR0aGlzLmdyYXBoUmVmZXJlbmNlRXJyb3JzLnB1c2goYW1iaWd1b3VzRXJyb3IpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgYSBwbGFpbi1UUyB0eXBlIHJlZmVyZW5jZSBzaXRlIHRoYXQgcmVzb2x2ZWQgdG8gbm90aGluZyBhbmRcblx0ICogZmVsbCBiYWNrIHRvIGB1bmtub3duYCwgZm9yIHRoZSBsYXppbHktcnVuIGFtYmlndWl0eSB2YWxpZGF0aW9uLlxuXHQgKiBEZWR1cGVkIGJ5IChuYW1lLCBsb2NhdGlvbik6IGluZmVyVHlwZSBjYW4gdmlzaXQgdGhlIHNhbWUgbm9kZSBtb3JlXG5cdCAqIHRoYW4gb25jZSBwZXIgcGFzcyAoY29uc3RydWN0b3IgcGFyYW1zICsgcHJvcGVydHkgaW5mZXJlbmNlKS5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSAobmFtZTogc3RyaW5nLCByZWZOb2RlOiB0cy5Ob2RlKTogdm9pZCB7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSB0aGlzLm5vZGVMb2NhdGlvbihyZWZOb2RlKTtcblx0XHRjb25zdCBmaWxlID0gdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlO1xuXHRcdGNvbnN0IGFscmVhZHkgPSB0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXMuc29tZSgocmVmKSA9PiByZWYubmFtZSA9PT0gbmFtZSAmJiByZWYubG9jYXRpb24gPT09IGxvY2F0aW9uKTtcblx0XHRpZiAoYWxyZWFkeSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXMucHVzaCh7IG5hbWUsIGxvY2F0aW9uLCBmaWxlIH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb2plY3Qtc291cmNlIGRlY2xhcmF0aW9uIGZpbGVzIGNhcnJ5aW5nIGBuYW1lYCDigJQgb25lIGVudHJ5IHBlclxuXHQgKiBmaWxlLCBzbyBzYW1lLWZpbGUgaW50ZXJmYWNlIG1lcmdpbmcgY291bnRzIG9uY2UgKG5vdCBhbWJpZ3VvdXMpLlxuXHQgKiBFeHRlcm5hbC9hbWJpZW50IGRlY2xhcmF0aW9ucyAoLmQudHMsIGFueXRoaW5nIHVuZGVyIG5vZGVfbW9kdWxlcylcblx0ICogbmV2ZXIgY291bnQ6IGEgdXNlci1sb2NhbCBkZWNsYXJhdGlvbiBhbHdheXMgd2lucyBvdmVyIGEgcGFja2FnZS1cblx0ICogZGVjbGFyZWQgc2FtZS1uYW1lZCB0eXBlLCBzbyBhbiBleHRlcm5hbCBjb2xsaXNpb24gc3RheXMgc29mdC5cblx0ICovXG5cdHByaXZhdGUgcGxhaW5UeXBlRGVjbGFyYXRpb25GaWxlcyAobmFtZTogc3RyaW5nKTogc3RyaW5nW10ge1xuXHRcdGNvbnN0IGZpbGVzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgWyBmaWxlLCBkZWNscyBdIG9mIHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscykge1xuXHRcdFx0aWYgKCF0aGlzLmlzRXh0ZXJuYWxEZWNsRmlsZShmaWxlKSAmJiBkZWNscy5oYXMobmFtZSkpIHtcblx0XHRcdFx0ZmlsZXMucHVzaChmaWxlKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIGZpbGVzO1xuXHR9XG5cblx0LyoqXG5cdCAqIFZhbGlkYXRlIHBsYWluLVRTIHR5cGUgcmVmZXJlbmNlIHNpdGVzIHJlY29yZGVkIGR1cmluZyB0aGUgdXNhZ2VzXG5cdCAqIHBhc3MgYWdhaW5zdCB0aGUgY29tcGxldGUgZGVjbGFyYXRpb24gbWFwLiBBIG5hbWUgZGVjbGFyZWQgaW5cblx0ICogc2V2ZXJhbCBwcm9qZWN0LXNvdXJjZSBmaWxlcyDigJQgd2l0aCBubyBpbXBvcnQgaW4gdGhlIHJlZmVyZW5jaW5nXG5cdCAqIGZpbGUgdG8gYW5jaG9yIGl0IOKAlCBpcyBhbWJpZ3VvdXM6IHNpbGVudGx5IGVtaXR0aW5nIGB1bmtub3duYCB3b3VsZFxuXHQgKiBoaWRlIGEgcmVhbCB0eXBlIHRoZSBhdXRob3IgbWVhbnQsIHNvIGl0IGpvaW5zIHRoZSBoYXJkLWZhaWwgbGF3XG5cdCAqICh0aGUgcGxhaW4tVFMgdGllciBvZiB0aGUgc2FtZSBpZGVudGl0eSBsYXcgYXMgZ3JhcGggcmVmZXJlbmNlcykuXG5cdCAqIEFic2VuY2UgKGdob3N0IG5hbWVzKSBhbmQgZXh0ZXJuYWwgY29sbGlzaW9ucyBzdGF5IHNvZnQgYHVua25vd25gLlxuXHQgKiBSdW5zIG9uY2UgcGVyIHVzYWdlcyBwYXNzIChyZS1hcm1lZCBieSByZXNldFVzYWdlcyksIG1pcnJvcmluZ1xuXHQgKiB2YWxpZGF0ZUxvb2t1cFJlZmVyZW5jZXM6IHJlY29yZGluZyBoYXBwZW5zIG9uIGV2ZXJ5IHBhc3MsIGJ1dCBvbmx5XG5cdCAqIHRoZSB1c2FnZXMgcGFzcyBzZWVzIHRoZSBjb21wbGV0ZSBkZWNsYXJhdGlvbiBtYXAuXG5cdCAqL1xuXHRwcml2YXRlIHZhbGlkYXRlUGxhaW5UeXBlUmVmZXJlbmNlcyAoKTogdm9pZCB7XG5cdFx0aWYgKHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlc1ZhbGlkYXRlZCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR0aGlzLnBsYWluVHlwZVJlZmVyZW5jZXNWYWxpZGF0ZWQgPSB0cnVlO1xuXHRcdGNvbnN0IHNpdGVzQnlOYW1lID0gbmV3IE1hcDxzdHJpbmcsIHsgbmFtZTogc3RyaW5nOyBsb2NhdGlvbjogc3RyaW5nOyBmaWxlOiBzdHJpbmcgfVtdPigpO1xuXHRcdGZvciAoY29uc3QgcmVmIG9mIHRoaXMucGxhaW5UeXBlUmVmZXJlbmNlcykge1xuXHRcdFx0Y29uc3Qgc2l0ZXMgPSBzaXRlc0J5TmFtZS5nZXQocmVmLm5hbWUpID8/IFtdO1xuXHRcdFx0c2l0ZXMucHVzaChyZWYpO1xuXHRcdFx0c2l0ZXNCeU5hbWUuc2V0KHJlZi5uYW1lLCBzaXRlcyk7XG5cdFx0fVxuXHRcdGZvciAoY29uc3QgWyBuYW1lLCBzaXRlcyBdIG9mIHNpdGVzQnlOYW1lKSB7XG5cdFx0XHQvLyBhbiBpbXBvcnQgYmluZGluZyBpbiB0aGUgcmVmZXJlbmNpbmcgZmlsZSBhbmNob3JzIHRoZSBuYW1lIOKAlFxuXHRcdFx0Ly8gdGhlIGF1dGhvciBhbHJlYWR5IGRpc2FtYmlndWF0ZWQgKHRoZSBpbXBvcnQgbWF5IGp1c3QgcG9pbnRcblx0XHRcdC8vIGF0IGFuIHVuYW5hbHl6YWJsZSBleHRlcm5hbCBtb2R1bGUsIHdoaWNoIHN0YXlzIHNvZnQpXG5cdFx0XHRjb25zdCB1bmFuY2hvcmVkID0gc2l0ZXMuZmlsdGVyKChzaXRlKSA9PiAhdGhpcy5yZWZlcmVuY2VkVHlwZUltcG9ydHMuZ2V0KHNpdGUuZmlsZSk/LmhhcyhuYW1lKSk7XG5cdFx0XHRpZiAodW5hbmNob3JlZC5sZW5ndGggPT09IDApIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBkZWNsRmlsZXMgPSB0aGlzLnBsYWluVHlwZURlY2xhcmF0aW9uRmlsZXMobmFtZSk7XG5cdFx0XHRpZiAoZGVjbEZpbGVzLmxlbmd0aCA8IDIpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBtZXNzYWdlID0gYEFtYmlndW91cyByZWZlcmVuY2UgdG8gdHlwZSAnJHtuYW1lfSc6ICR7ZGVjbEZpbGVzLmxlbmd0aH0gZGVjbGFyYXRpb25zIGAgK1xuXHRcdFx0XHQnc2hhcmUgdGhlIG5hbWUgYW5kIG5vIGltcG9ydCBkaXNhbWJpZ3VhdGVzIOKAlCBpbXBvcnQgdGhlIG9uZSB5b3UgbWVhbic7XG5cdFx0XHRjb25zdCBkZWNsTG9jYXRpb25zID0gZGVjbEZpbGVzLm1hcCgoZmlsZSkgPT4gdGhpcy5wbGFpbkRlY2xMb2NhdGlvbihmaWxlLCBuYW1lKSk7XG5cdFx0XHRjb25zdCBlcnJvcjogUmVzb2x1dGlvbkVycm9yID0ge1xuXHRcdFx0XHRtZXNzYWdlLFxuXHRcdFx0XHRsb2NhdGlvbnMgOiBbIC4uLnVuYW5jaG9yZWQubWFwKChzaXRlKSA9PiBzaXRlLmxvY2F0aW9uKSwgLi4uZGVjbExvY2F0aW9ucyBdXG5cdFx0XHR9O1xuXHRcdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKGVycm9yKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogYGZpbGU6bGluZTpjb2x1bW5gIG9mIGEgcmVjb3JkZWQgZGVjbGFyYXRpb24sIGZvciB0aGUgYW1iaWd1aXR5XG5cdCAqIHJlcG9ydC4gTm9kZXMgcmVjb3JkZWQgZHVyaW5nIHRyYXZlcnNhbCBrZWVwIHRoZWlyIHBvc2l0aW9uczsgYVxuXHQgKiBzeW50aGV0aWMvdW5wb3NpdGlvbmVkIG5vZGUgZmFsbHMgYmFjayB0byB0aGUgZmlsZSBpdHNlbGYuXG5cdCAqL1xuXHRwcml2YXRlIHBsYWluRGVjbExvY2F0aW9uIChmaWxlOiBzdHJpbmcsIG5hbWU6IHN0cmluZyk6IHN0cmluZyB7XG5cdFx0Y29uc3QgZGVjbCA9IHRoaXMucmVmZXJlbmNlZFR5cGVEZWNscy5nZXQoZmlsZSk/LmdldChuYW1lKTtcblx0XHRjb25zdCBub2RlID0gZGVjbD8ubm9kZTtcblx0XHRsZXQgbG9jYXRpb24gPSBgJHtmaWxlfToxOjFgO1xuXHRcdGlmIChub2RlICYmIG5vZGUucG9zID49IDApIHtcblx0XHRcdGNvbnN0IHNvdXJjZUZpbGUgPSBub2RlLmdldFNvdXJjZUZpbGUoKTtcblx0XHRcdGNvbnN0IGxpbmUgPSBzb3VyY2VGaWxlLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKG5vZGUuZ2V0U3RhcnQoKSkubGluZSArIDE7XG5cdFx0XHRjb25zdCBjb2x1bW4gPSBzb3VyY2VGaWxlLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKG5vZGUuZ2V0U3RhcnQoKSkuY2hhcmFjdGVyICsgMTtcblx0XHRcdGxvY2F0aW9uID0gYCR7ZmlsZX06JHtsaW5lfToke2NvbHVtbn1gO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSBsb2NhdGlvbjtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhIGhhcmQtZmFpbCBncmFwaCByZWZlcmVuY2UgZXJyb3Igd2l0aCB0aGUgcmVmZXJlbmNlIHNpdGUgYW5kXG5cdCAqIGV2ZXJ5IGNhbmRpZGF0ZSBsb2NhdGlvbi5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkR3JhcGhSZWZlcmVuY2VFcnJvciAoXG5cdFx0bmFtZTogc3RyaW5nLFxuXHRcdHJlZk5vZGU6IHRzLk5vZGUgfCBzdHJpbmcsXG5cdFx0cmVzdWx0OiBFeHRyYWN0PEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCwgeyBzdGF0dXM6ICdhbWJpZ3VvdXMnIHwgJ25vbmUnIH0+XG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gdHlwZW9mIHJlZk5vZGUgPT09ICdzdHJpbmcnID8gcmVmTm9kZSA6IHRoaXMubm9kZUxvY2F0aW9uKHJlZk5vZGUpO1xuXHRcdGlmIChyZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlTG9jYXRpb25zID0gcmVzdWx0LmNhbmRpZGF0ZXMubWFwKG4gPT4gYCR7bi5zb3VyY2VGaWxlfToke24ubGluZX06JHtuLmNvbHVtbn1gKTtcblx0XHRcdGNvbnN0IGFtYmlndW91c01lc3NhZ2UgPSBgQW1iaWd1b3VzIHJlZmVyZW5jZSB0byBtbmVtb25pY2EgdHlwZSAnJHtuYW1lfSc6IGAgK1xuXHRcdFx0XHRgJHtyZXN1bHQuY2FuZGlkYXRlcy5sZW5ndGh9IHR5cGVzIHNoYXJlIHRoZSBuYW1lIGFuZCBuZWl0aGVyIHRoZSBwYXJlbnQgY2hhaW4gYCArXG5cdFx0XHRcdCdub3IgdGhlIGltcG9ydHMgZGlzYW1iaWd1YXRlJztcblx0XHRcdGNvbnN0IGFtYmlndW91c0Vycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7XG5cdFx0XHRcdG1lc3NhZ2UgICA6IGFtYmlndW91c01lc3NhZ2UsXG5cdFx0XHRcdGxvY2F0aW9ucyA6IFsgbG9jYXRpb24sIC4uLmNhbmRpZGF0ZUxvY2F0aW9ucyBdLFxuXHRcdFx0fTtcblx0XHRcdHRoaXMuZ3JhcGhSZWZlcmVuY2VFcnJvcnMucHVzaChhbWJpZ3VvdXNFcnJvcik7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IHVucmVzb2x2ZWRNZXNzYWdlID0gYFVucmVzb2x2ZWQgcmVmZXJlbmNlIHRvIG1uZW1vbmljYSB0eXBlICcke25hbWV9Jzogbm8gdHlwZSBtYXRjaGVzIGAgK1xuXHRcdFx0J2J5IHZhbHVlIHNjb3BlLCBpbXBvcnRzLCBwYXJlbnQgY2hhaW4sIG9yIHJvb3QgcGF0aCc7XG5cdFx0Y29uc3QgdW5yZXNvbHZlZEVycm9yOiBSZXNvbHV0aW9uRXJyb3IgPSB7IG1lc3NhZ2UgOiB1bnJlc29sdmVkTWVzc2FnZSwgbG9jYXRpb25zIDogWyBsb2NhdGlvbiBdIH07XG5cdFx0dGhpcy5ncmFwaFJlZmVyZW5jZUVycm9ycy5wdXNoKHVucmVzb2x2ZWRFcnJvcik7XG5cdH1cblxuXHQvKipcblx0ICogTG9jYXRpb24gKGBmaWxlOmxpbmU6Y29sdW1uYCkgb2YgYW4gQVNUIG5vZGUsIGRlcml2ZWQgd2l0aG91dCBwYXJlbnRcblx0ICogcG9pbnRlcnMgd2hlbiBuZWNlc3NhcnkuXG5cdCAqL1xuXHRwcml2YXRlIG5vZGVMb2NhdGlvbiAobm9kZTogdHMuTm9kZSk6IHN0cmluZyB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBub2RlO1xuXHRcdHdoaWxlIChjdXJyZW50ICYmICF0cy5pc1NvdXJjZUZpbGUoY3VycmVudCkpIHtcblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0aWYgKCFjdXJyZW50KSB7XG5cdFx0XHRjb25zdCBmYWxsYmFjayA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRcdHJldHVybiBmYWxsYmFjaztcblx0XHR9XG5cdFx0Y29uc3Qgc3RhcnQgPSBub2RlLmdldFN0YXJ0KGN1cnJlbnQpO1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihjdXJyZW50LCBzdGFydCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtjdXJyZW50LmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRyZXR1cm4gbG9jYXRpb247XG5cdH1cblxuXHQvKipcblx0ICogVHJhY2sgYWxpYXNlcyBvZiB0aGUgbW5lbW9uaWNhIG1vZHVsZSBvYmplY3QsIGUuZy46XG5cdCAqICAgY29uc3QgbSA9IG1uZW1vbmljYTtcblx0ICogICBjb25zdCBBcHAgPSBtO1xuXHQgKi9cblx0cHJpdmF0ZSB0cmFja01vZHVsZU9iamVjdEFsaWFzZXMgKG5vZGU6IHRzLk5vZGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzVmFyaWFibGVEZWNsYXJhdGlvbihub2RlKSB8fCAhdHMuaXNJZGVudGlmaWVyKG5vZGUubmFtZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGluaXRpYWxpemVyIH0gPSBub2RlO1xuXHRcdGlmICghaW5pdGlhbGl6ZXIpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGluaXRpYWxpemVyKSAmJiB0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoaW5pdGlhbGl6ZXIudGV4dCkpIHtcblx0XHRcdHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmFkZChub2RlLm5hbWUudGV4dCk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFRyYWNrIGN1c3RvbSBjb2xsZWN0aW9uIHZhcmlhYmxlcywgZS5nLjpcblx0ICogICBjb25zdCBNeUNvbGxlY3Rpb24gPSBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKTtcblx0ICogICBjb25zdCBPdGhlciA9IE15Q29sbGVjdGlvbjtcblx0ICpcblx0ICogQWxzbyBkZXRlY3RzIE9wdGlvbiBCIHVzZXItcHJvdmlkZWQgcmVnaXN0cnkgaW50ZXJmYWNlczpcblx0ICogICBleHBvcnQgaW50ZXJmYWNlIE15Q29sbGVjdGlvblJlZ2lzdHJ5IHt9XG5cdCAqICAgY29uc3QgTXlDb2xsZWN0aW9uID0gY3JlYXRlVHlwZXNDb2xsZWN0aW9uPE15Q29sbGVjdGlvblJlZ2lzdHJ5PigpO1xuXHQgKi9cblx0cHJpdmF0ZSB0cmFja0NvbGxlY3Rpb25BbGlhc2VzIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24obm9kZSkgfHwgIXRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBpbml0aWFsaXplciB9ID0gbm9kZTtcblx0XHRpZiAoIWluaXRpYWxpemVyKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gRGlyZWN0IGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIGNhbGxcblx0XHRpZiAodGhpcy5pc0NyZWF0ZVR5cGVzQ29sbGVjdGlvbkNhbGwoaW5pdGlhbGl6ZXIpKSB7XG5cdFx0XHRjb25zdCBjb2xsZWN0aW9uSWQgPSB0aGlzLm5leHRDb2xsZWN0aW9uSWQoKTtcblx0XHRcdHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5zZXQobm9kZS5uYW1lLnRleHQsIGNvbGxlY3Rpb25JZCk7XG5cblx0XHRcdGNvbnN0IHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA9IHRoaXMuZXh0cmFjdFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZShcblx0XHRcdFx0aW5pdGlhbGl6ZXIgYXMgdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0XHRcdHNvdXJjZUZpbGVcblx0XHRcdCk7XG5cdFx0XHR0aGlzLmNvbGxlY3Rpb25JbmZvLnNldChjb2xsZWN0aW9uSWQsIHtcblx0XHRcdFx0dmFyaWFibGVOYW1lICAgICAgICAgIDogbm9kZS5uYW1lLnRleHQsXG5cdFx0XHRcdHNvdXJjZUZpbGUgICAgICAgICAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA6IHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZVxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gQWxpYXMgb2YgYW5vdGhlciBjb2xsZWN0aW9uIHZhcmlhYmxlXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihpbml0aWFsaXplcikpIHtcblx0XHRcdGNvbnN0IGV4aXN0aW5nID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChpbml0aWFsaXplci50ZXh0KTtcblx0XHRcdGlmIChleGlzdGluZykge1xuXHRcdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuc2V0KG5vZGUubmFtZS50ZXh0LCBleGlzdGluZyk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdGhlIHJlZ2lzdHJ5IGludGVyZmFjZSBuYW1lIGZyb20gY3JlYXRlVHlwZXNDb2xsZWN0aW9uPFJlZ2lzdHJ5PigpXG5cdCAqIHdoZW4gdGhlIGludGVyZmFjZSBpcyBkZWNsYXJlZCBpbiB0aGUgc2FtZSBzb3VyY2UgZmlsZS5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSAoXG5cdFx0Y2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZVxuXHQpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IHR5cGVBcmdzID0gY2FsbC50eXBlQXJndW1lbnRzO1xuXHRcdGlmICghdHlwZUFyZ3MgfHwgdHlwZUFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IFsgZmlyc3RUeXBlQXJnIF0gPSB0eXBlQXJncztcblx0XHRpZiAoIXRzLmlzVHlwZVJlZmVyZW5jZU5vZGUoZmlyc3RUeXBlQXJnKSB8fCAhdHMuaXNJZGVudGlmaWVyKGZpcnN0VHlwZUFyZy50eXBlTmFtZSkpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgbmFtZSA9IGZpcnN0VHlwZUFyZy50eXBlTmFtZS50ZXh0O1xuXG5cdFx0Ly8gQ29uZmlybSB0aGUgaW50ZXJmYWNlIGV4aXN0cyBpbiB0aGUgc2FtZSBzb3VyY2UgZmlsZS5cblx0XHRmb3IgKGNvbnN0IHN0YXRlbWVudCBvZiBzb3VyY2VGaWxlLnN0YXRlbWVudHMpIHtcblx0XHRcdGlmIChcblx0XHRcdFx0dHMuaXNJbnRlcmZhY2VEZWNsYXJhdGlvbihzdGF0ZW1lbnQpICYmXG5cdFx0XHRcdHN0YXRlbWVudC5uYW1lLnRleHQgPT09IG5hbWVcblx0XHRcdCkge1xuXHRcdFx0XHRyZXR1cm4gbmFtZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEdldCB0aGUgcmVnaXN0cnkgaW50ZXJmYWNlIG5hbWUgZm9yIGEgY29sbGVjdGlvbiBpZC5cblx0ICovXG5cdHByaXZhdGUgZ2V0UmVnaXN0cnlJbnRlcmZhY2VOYW1lIChjb2xsZWN0aW9uSWQ/OiBzdHJpbmcpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICghY29sbGVjdGlvbklkKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRyZXR1cm4gdGhpcy5jb2xsZWN0aW9uSW5mby5nZXQoY29sbGVjdGlvbklkKT8ucmVnaXN0cnlJbnRlcmZhY2VOYW1lO1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGFuIGV4cHJlc3Npb24gaXMgYSBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSBjYWxsLlxuXHQgKiBIYW5kbGVzOlxuXHQgKiAgIGNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpXG5cdCAqICAgY3RjKCkgLy8gYWxpYXNlZCBpbXBvcnRcblx0ICogICBtbmVtb25pY2EuY3JlYXRlVHlwZXNDb2xsZWN0aW9uKCkgLy8gbW9kdWxlIG9iamVjdCBtZXRob2Rcblx0ICogICBtLmNyZWF0ZVR5cGVzQ29sbGVjdGlvbigpIC8vIGFsaWFzZWQgbW9kdWxlIG9iamVjdFxuXHQgKi9cblx0cHJpdmF0ZSBpc0NyZWF0ZVR5cGVzQ29sbGVjdGlvbkNhbGwgKG5vZGU6IHRzLk5vZGUpOiBub2RlIGlzIHRzLkNhbGxFeHByZXNzaW9uIHtcblx0XHRpZiAoIXRzLmlzQ2FsbEV4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Y29uc3QgZXhwciA9IG5vZGUuZXhwcmVzc2lvbjtcblxuXHRcdC8vIERpcmVjdCBjYWxsIG9yIGFsaWFzZWQgaW1wb3J0OiBjcmVhdGVUeXBlc0NvbGxlY3Rpb24oKSAvIGN0YygpXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0cmV0dXJuIGV4cHIudGV4dCA9PT0gJ2NyZWF0ZVR5cGVzQ29sbGVjdGlvbicgfHxcblx0XHRcdFx0dGhpcy5jcmVhdGVUeXBlc0NvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGV4cHIudGV4dCk7XG5cdFx0fVxuXG5cdFx0Ly8gTW9kdWxlIG9iamVjdCBtZXRob2Q6IG1uZW1vbmljYS5jcmVhdGVUeXBlc0NvbGxlY3Rpb24oKVxuXHRcdGlmIChcblx0XHRcdHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpICYmXG5cdFx0XHRleHByLm5hbWUudGV4dCA9PT0gJ2NyZWF0ZVR5cGVzQ29sbGVjdGlvbicgJiZcblx0XHRcdHRzLmlzSWRlbnRpZmllcihleHByLmV4cHJlc3Npb24pICYmXG5cdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoZXhwci5leHByZXNzaW9uLnRleHQpXG5cdFx0KSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogR2VuZXJhdGUgYSB1bmlxdWUgY29sbGVjdGlvbiBpZGVudGlmaWVyLlxuXHQgKi9cblx0cHJpdmF0ZSBuZXh0Q29sbGVjdGlvbklkICgpOiBzdHJpbmcge1xuXHRcdHRoaXMuY29sbGVjdGlvbkNvdW50ZXIrKztcblx0XHRjb25zdCByZXN1bHQgPSBgY29sbGVjdGlvbl8ke3RoaXMuY29sbGVjdGlvbkNvdW50ZXJ9YDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIENoZWNrIGlmIGEgbm9kZSBpcyBhIGRlZmluZSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgaXNEZWZpbmVDYWxsIChub2RlOiB0cy5Ob2RlKTogbm9kZSBpcyB0cy5DYWxsRXhwcmVzc2lvbiB7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIGRpcmVjdCBjYWxsOiBkZWZpbmUoJ1R5cGVOYW1lJywgLi4uKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIG1ldGhvZCBjYWxsOiBTb21lVHlwZS5kZWZpbmUoJ1N1YlR5cGUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gZXhwcmVzc2lvbi5uYW1lPy50ZXh0ID09PSAnZGVmaW5lJztcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogQ2hlY2sgaWYgYSBub2RlIGlzIGEgbGF6eSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgaXNMYXp5Q2FsbCAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuQ2FsbEV4cHJlc3Npb24ge1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gbm9kZTtcblxuXHRcdC8vIENoZWNrIGZvciBkaXJlY3QgY2FsbDogbGF6eSgnVHlwZU5hbWUnLCBnZXR0ZXIsIC4uLilcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24udGV4dCA9PT0gJ2xhenknKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgbWV0aG9kIGNhbGw6IFNvbWVUeXBlLmxhenkoJ1N1YlR5cGUnLCBnZXR0ZXIsIC4uLilcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcmVzc2lvbikpIHtcblx0XHRcdHJldHVybiBleHByZXNzaW9uLm5hbWU/LnRleHQgPT09ICdsYXp5Jztcblx0XHR9XG5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0XHQqIEV4dHJhY3QgY29uZmlnIG9wdGlvbnMgZnJvbSBhbiBvYmplY3QgbGl0ZXJhbFxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsIChjb25maWdBcmc6IHRzLk9iamVjdExpdGVyYWxFeHByZXNzaW9uKTpcblx0XHR7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0ge1xuXHRcdGNvbnN0IGNvbmZpZzogeyBzdHJpY3RDaGFpbj86IGJvb2xlYW47IGJsb2NrRXJyb3JzPzogYm9vbGVhbiB9ID0ge307XG5cblx0XHRmb3IgKGNvbnN0IHByb3Agb2YgY29uZmlnQXJnLnByb3BlcnRpZXMpIHtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QXNzaWdubWVudChwcm9wKSAmJiB0cy5pc0lkZW50aWZpZXIocHJvcC5uYW1lKSkge1xuXHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IHByb3AubmFtZS50ZXh0O1xuXHRcdFx0XHRpZiAocHJvcE5hbWUgPT09ICdzdHJpY3RDaGFpbicgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLnN0cmljdENoYWluID0gdHJ1ZTtcblx0XHRcdFx0fSBlbHNlIGlmIChwcm9wTmFtZSA9PT0gJ3N0cmljdENoYWluJyAmJiBwcm9wLmluaXRpYWxpemVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLnN0cmljdENoYWluID0gZmFsc2U7XG5cdFx0XHRcdH0gZWxzZSBpZiAocHJvcE5hbWUgPT09ICdibG9ja0Vycm9ycycgJiYgcHJvcC5pbml0aWFsaXplci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLmJsb2NrRXJyb3JzID0gdHJ1ZTtcblx0XHRcdFx0fSBlbHNlIGlmIChwcm9wTmFtZSA9PT0gJ2Jsb2NrRXJyb3JzJyAmJiBwcm9wLmluaXRpYWxpemVyLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uZmlnLmJsb2NrRXJyb3JzID0gZmFsc2U7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gY29uZmlnO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IGNvbmZpZyBvcHRpb25zIGZyb20gZGVmaW5lKCkgY2FsbFxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdENvbmZpZyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7IHN0cmljdENoYWluPzogYm9vbGVhbjsgYmxvY2tFcnJvcnM/OiBib29sZWFuIH0ge1xuXHRcdC8vIENvbmZpZyBpcyB0aGUgdGhpcmQgYXJndW1lbnQ6IGRlZmluZSgnTmFtZScsIGhhbmRsZXIsIGNvbmZpZylcblx0XHRjb25zdCBbICwgLCBjb25maWdBcmcgXSA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGlmICghY29uZmlnQXJnIHx8ICF0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGNvbmZpZ0FyZykpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRjb25zdCBjb25maWdSZXN1bHQgPSB0aGlzLmV4dHJhY3RDb25maWdGcm9tT2JqZWN0TGl0ZXJhbChjb25maWdBcmcpO1xuXHRcdHJldHVybiBjb25maWdSZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHQqIENoZWNrIGlmIGEgbm9kZSBpcyBhIEBkZWNvcmF0ZSgpIGRlY29yYXRvclxuXHRcdCovXG5cdHByaXZhdGUgaXNEZWNvcmF0ZURlY29yYXRvciAobm9kZTogdHMuTm9kZSk6IG5vZGUgaXMgdHMuRGVjb3JhdG9yIHtcblx0XHRpZiAoIXRzLmlzRGVjb3JhdG9yKG5vZGUpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXG5cdFx0Ly8gQ2hlY2sgZm9yIEBkZWNvcmF0ZVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVjb3JhdGUnKSB7XG5cdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBmb3IgQGRlY29yYXRlKCkgb3IgQGRlY29yYXRlKFBhcmVudFR5cGUpXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZXhwcmVzc2lvbikpIHtcblx0XHRcdGNvbnN0IGZuTmFtZSA9IGV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZm5OYW1lKSAmJiBmbk5hbWUudGV4dCA9PT0gJ2RlY29yYXRlJykge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gQ2hlY2sgZm9yIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSB3aGVyZSBNeUNvbGxlY3Rpb24gaXMgYSBjdXN0b20gY29sbGVjdGlvblxuXHRcdFx0aWYgKFxuXHRcdFx0XHR0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihmbk5hbWUpICYmXG5cdFx0XHRcdGZuTmFtZS5uYW1lLnRleHQgPT09ICdkZWNvcmF0ZScgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGZuTmFtZS5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHR0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuaGFzKGZuTmFtZS5leHByZXNzaW9uLnRleHQpXG5cdFx0XHQpIHtcblx0XHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cblx0LyoqXG5cdCAqIE1hcmsgYSBjYWxsIGV4cHJlc3Npb24gYXMgcHJvY2Vzc2VkIGFuZCByZXR1cm4gd2hldGhlciBpdCBhbHJlYWR5IHdhcy5cblx0ICovXG5cdHByaXZhdGUgbWFya1Byb2Nlc3NlZCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBib29sZWFuIHtcblx0XHRpZiAodGhpcy5wcm9jZXNzZWRDYWxscy5oYXMoY2FsbCkpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHR0aGlzLnByb2Nlc3NlZENhbGxzLmFkZChjYWxsKTtcblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogUHJvY2VzcyBhIGRlZmluZSgpIGNhbGxcblx0ICovXG5cdHByaXZhdGUgcHJvY2Vzc0RlZmluZUNhbGwgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBleGFjdCBjYWxsIGhhcyBhbHJlYWR5IGJlZW4gcHJvY2Vzc2VkIChwcmV2ZW50cyBkdXBsaWNhdGVzIGZyb20gY2hhaW5lZCBjYWxscylcblx0XHRpZiAodGhpcy5tYXJrUHJvY2Vzc2VkKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gR2V0IHRoZSB0eXBlIG5hbWUgYW5kIHNvdXJjZSBjb250ZXh0IGZyb20gYXJndW1lbnRzXG5cdFx0Y29uc3QgZGVmaW5lQ29udGV4dCA9IHRoaXMuZXh0cmFjdERlZmluZUNvbnRleHQoY2FsbCk7XG5cblx0XHQvLyBGb3IgY2hhaW5lZCBjYWxscyBsaWtlIGRlZmluZSgnQScpLmRlZmluZSgnQicpLCB3ZSB3YW50IHRoZSBwb3NpdGlvbiBvZiB0aGUgLmRlZmluZSgnQicpIHBhcnRcblx0XHQvLyBub3QgdGhlIHN0YXJ0IG9mIHRoZSBlbnRpcmUgZXhwcmVzc2lvblxuXHRcdGxldCBwb3NpdGlvbk5vZGU6IHRzLk5vZGUgPSBjYWxsO1xuXG5cdFx0Ly8gSWYgdGhpcyBpcyBhIGNoYWluZWQgY2FsbCwgZ2V0IHRoZSBwb3NpdGlvbiBvZiB0aGUgcHJvcGVydHkgYWNjZXNzIGV4cHJlc3Npb25cblx0XHQvLyB3aGljaCBpcyB0aGUgLmRlZmluZSBwYXJ0XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGwuZXhwcmVzc2lvbikpIHtcblx0XHRcdC8vIFRoZSBleHByZXNzaW9uIGlzIHRoZSBwcm9wZXJ0eSBhY2Nlc3M6IChkZWZpbmUoJ1Jvb3RBc3luYycsIC4uLikpLmRlZmluZVxuXHRcdFx0Ly8gV2Ugd2FudCB0aGUgcG9zaXRpb24gb2YganVzdCB0aGUgLmRlZmluZSBwYXJ0XG5cdFx0XHQvLyBUaGlzIGlzIHRoZSAnZGVmaW5lJyBpZGVudGlmaWVyXG5cdFx0XHRwb3NpdGlvbk5vZGUgPSBjYWxsLmV4cHJlc3Npb24ubmFtZTtcblx0XHR9XG5cblx0XHRjb25zdCBzdGFydFBvcyA9IHBvc2l0aW9uTm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKTtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oc291cmNlRmlsZSwgc3RhcnRQb3MpO1xuXG5cdFx0aWYgKCFkZWZpbmVDb250ZXh0LnR5cGVOYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdDb3VsZCBub3QgZXh0cmFjdCB0eXBlIG5hbWUgZnJvbSBkZWZpbmUoKSBjYWxsJyxcblx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdGxpbmUgICAgOiBsaW5lICsgMSxcblx0XHRcdFx0Y29sdW1uICA6IGNoYXJhY3RlciArIDEsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IHR5cGVOYW1lIH0gPSBkZWZpbmVDb250ZXh0O1xuXG5cdFx0Ly8gRGV0ZXJtaW5lIHBhcmVudCB0eXBlIGFuZCBjb2xsZWN0aW9uIGJhc2VkIG9uIHRoZSBjYWxsIHNvdXJjZS5cblx0XHRjb25zdCBwYXJlbnROb2RlID0gZGVmaW5lQ29udGV4dC5wYXJlbnRUeXBlO1xuXHRcdGNvbnN0IHsgY29sbGVjdGlvbklkIH0gPSBkZWZpbmVDb250ZXh0O1xuXG5cdFx0Ly8gRXh0cmFjdCBjb25maWcgb3B0aW9uc1xuXHRcdGNvbnN0IGNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZyhjYWxsKTtcblxuXHRcdC8vIENyZWF0ZSB0eXBlIG5vZGUgZmlyc3Qgc28gaXRzIGludGVybmFsIGZ1bGxQYXRoIChpbmNsdWRpbmcgYW55IGNvbGxlY3Rpb24gcHJlZml4KSBpcyByZXNvbHZlZC5cblx0XHRjb25zdCBub2RlID0gVHlwZUdyYXBoSW1wbC5jcmVhdGVOb2RlKFxuXHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRwYXJlbnROb2RlLFxuXHRcdFx0c291cmNlRmlsZS5maWxlTmFtZSxcblx0XHRcdGxpbmUgKyAxLFxuXHRcdFx0Y2hhcmFjdGVyICsgMSxcblx0XHRcdGNvbGxlY3Rpb25JZFxuXHRcdCk7XG5cdFx0bm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWUgPSB0aGlzLmdldFJlZ2lzdHJ5SW50ZXJmYWNlTmFtZShjb2xsZWN0aW9uSWQpO1xuXG5cdFx0Ly8gU2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlIGRldGVjdGlvbiAoaGFyZC1mYWlsIGxhdyk6IGtleSBieSB0aGVcblx0XHQvLyBydW50aW1lIG5hbWVzcGFjZSDigJQgY29sbGVjdGlvbiByb290cyBgPGNvbGxlY3Rpb24+Ojo8bmFtZT5gLCBvclxuXHRcdC8vIGA8cGFyZW50RnVsbFBhdGg+LjxuYW1lPmAgZm9yIHN1YnR5cGVzXG5cdFx0dGhpcy5yZWNvcmREZWZpbmVTaXRlKFxuXHRcdFx0cGFyZW50Tm9kZSA/IGAke3BhcmVudE5vZGUuZnVsbFBhdGh9LiR7dHlwZU5hbWV9YCA6IGAke2NvbGxlY3Rpb25JZCA/PyAnZGVmYXVsdCd9Ojoke3R5cGVOYW1lfWAsXG5cdFx0XHRgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YFxuXHRcdCk7XG5cblx0XHQvLyBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBjb25zdHJ1Y3RvciBmdW5jdGlvbiDigJQgdGhlIG5ldyBub2RlIGFuY2hvcnNcblx0XHQvLyByZWxhdGl2ZS1maXJzdCBncmFwaCByZWZlcmVuY2UgcmVzb2x1dGlvbiB3aGlsZSBpdHMgb3duIHNpZ25hdHVyZVxuXHRcdC8vIGlzIGJlaW5nIHJlYWRcblx0XHRjb25zdCBwcmV2aW91c0FuY2hvciA9IHRoaXMuY3VycmVudEdyYXBoQW5jaG9yO1xuXHRcdHRoaXMuY3VycmVudEdyYXBoQW5jaG9yID0gbm9kZTtcblx0XHR0cnkge1xuXHRcdFx0bm9kZS5wcm9wZXJ0aWVzID0gdGhpcy5leHRyYWN0UHJvcGVydGllcyhjYWxsKTtcblxuXHRcdFx0Ly8gRXh0cmFjdCBjb25zdHJ1Y3RvciBwYXJhbWV0ZXJzIGZvciBUeXBlUmVnaXN0cnkgc2lnbmF0dXJlXG5cdFx0XHRub2RlLmNvbnN0cnVjdG9yUGFyYW1zID0gdGhpcy5leHRyYWN0Q29uc3RydWN0b3JQYXJhbXMoY2FsbCk7XG5cdFx0fSBmaW5hbGx5IHtcblx0XHRcdHRoaXMuY3VycmVudEdyYXBoQW5jaG9yID0gcHJldmlvdXNBbmNob3I7XG5cdFx0fVxuXG5cdFx0Ly8gQWRkIHRvIGdyYXBoXG5cdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkQ2hpbGQocGFyZW50Tm9kZSwgbm9kZSk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHRoaXMuZ3JhcGguYWRkUm9vdChub2RlKTtcblx0XHR9XG5cblx0XHQvLyBDcmVhdGUgZGVmaW5pdGlvbiBpbmZvIHVzaW5nIHRoZSBub2RlJ3MgcmVzb2x2ZWQgZnVsbFBhdGhcblx0XHRjb25zdCBkZWZpbml0aW9uOiBEZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogcGFyZW50Tm9kZSA/IHBhcmVudE5vZGUuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiBjb25maWcuc3RyaWN0Q2hhaW4gPz8gdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogY29uZmlnLmJsb2NrRXJyb3JzID8/IGZhbHNlLFxuXHRcdH07XG5cdFx0dGhpcy5kZWZpbml0aW9ucy5zZXQobm9kZS5mdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdFx0dGhpcy5lZHNTY29wZUJ5Tm9kZS5zZXQoY2FsbCwgbm9kZS5mdWxsUGF0aCk7XG5cblx0XHQvLyBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50OiBjb25zdCBVc2VyID0gZGVmaW5lKCdVc2VyRW50aXR5JywgLi4uKSAtPiBtYXAgXCJVc2VyXCIgdG8gXCJVc2VyRW50aXR5XCJcblx0XHQvLyBBIG11bHRpLWhvcCBpbml0aWFsaXplciBiaW5kcyB0aGUgTEFTVCBob3A6IGRlZmluZSgpIHJldHVybnMgdGhlXG5cdFx0Ly8gZGVmaW5lZCB0eXBlJ3MgY29uc3RydWN0b3IgKEYxOClcblx0XHR0aGlzLnRyYWNrVmFyaWFibGVBc3NpZ25tZW50KGNhbGwsIHBhcmVudE5vZGUsIG5vZGUuZnVsbFBhdGgpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFByb2Nlc3MgYSBsYXp5KCkgY2FsbFxuXHQgKi9cblx0cHJpdmF0ZSBwcm9jZXNzTGF6eUNhbGwgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gQ2hlY2sgaWYgdGhpcyBleGFjdCBjYWxsIGhhcyBhbHJlYWR5IGJlZW4gcHJvY2Vzc2VkIChwcmV2ZW50cyBkdXBsaWNhdGVzIGZyb20gY2hhaW5lZCBjYWxscylcblx0XHRpZiAodGhpcy5tYXJrUHJvY2Vzc2VkKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gR2V0IHRoZSB0eXBlIG5hbWUgYW5kIHNvdXJjZSBjb250ZXh0IGZyb20gYXJndW1lbnRzXG5cdFx0Y29uc3QgbGF6eUNvbnRleHQgPSB0aGlzLmV4dHJhY3RMYXp5Q29udGV4dChjYWxsLCBzb3VyY2VGaWxlKTtcblxuXHRcdC8vIEZvciBjaGFpbmVkIGNhbGxzIGxpa2UgZGVmaW5lKCdBJykubGF6eSgnQicpLCB3ZSB3YW50IHRoZSBwb3NpdGlvbiBvZiB0aGUgLmxhenkoJ0InKSBwYXJ0XG5cdFx0Ly8gbm90IHRoZSBzdGFydCBvZiB0aGUgZW50aXJlIGV4cHJlc3Npb25cblx0XHRsZXQgcG9zaXRpb25Ob2RlOiB0cy5Ob2RlID0gY2FsbDtcblxuXHRcdC8vIElmIHRoaXMgaXMgYSBjaGFpbmVkIGNhbGwsIGdldCB0aGUgcG9zaXRpb24gb2YgdGhlIHByb3BlcnR5IGFjY2VzcyBleHByZXNzaW9uXG5cdFx0Ly8gd2hpY2ggaXMgdGhlIC5sYXp5IHBhcnRcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0Ly8gVGhlIGV4cHJlc3Npb24gaXMgdGhlIHByb3BlcnR5IGFjY2VzczogKGRlZmluZSgnUm9vdEFzeW5jJywgLi4uKSkubGF6eVxuXHRcdFx0Ly8gV2Ugd2FudCB0aGUgcG9zaXRpb24gb2YganVzdCB0aGUgLmxhenkgcGFydFxuXHRcdFx0Ly8gVGhpcyBpcyB0aGUgJ2xhenknIGlkZW50aWZpZXJcblx0XHRcdHBvc2l0aW9uTm9kZSA9IGNhbGwuZXhwcmVzc2lvbi5uYW1lO1xuXHRcdH1cblxuXHRcdGNvbnN0IHN0YXJ0UG9zID0gcG9zaXRpb25Ob2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpO1xuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihzb3VyY2VGaWxlLCBzdGFydFBvcyk7XG5cblx0XHRpZiAoIWxhenlDb250ZXh0LnR5cGVOYW1lKSB7XG5cdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0bWVzc2FnZSA6ICdDb3VsZCBub3QgZXh0cmFjdCB0eXBlIG5hbWUgZnJvbSBsYXp5KCkgY2FsbCcsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyB0eXBlTmFtZSB9ID0gbGF6eUNvbnRleHQ7XG5cblx0XHQvLyBEZXRlcm1pbmUgcGFyZW50IHR5cGUgYW5kIGNvbGxlY3Rpb24gYmFzZWQgb24gdGhlIGNhbGwgc291cmNlLlxuXHRcdGNvbnN0IHBhcmVudE5vZGUgPSBsYXp5Q29udGV4dC5wYXJlbnRUeXBlO1xuXHRcdGNvbnN0IHsgY29sbGVjdGlvbklkIH0gPSBsYXp5Q29udGV4dDtcblxuXHRcdC8vIEV4dHJhY3QgY29uZmlnIG9wdGlvbnNcblx0XHRjb25zdCBjb25maWcgPSB0aGlzLmV4dHJhY3RMYXp5Q29uZmlnKGNhbGwpO1xuXG5cdFx0Ly8gQ3JlYXRlIHR5cGUgbm9kZSBmaXJzdCBzbyBpdHMgaW50ZXJuYWwgZnVsbFBhdGggKGluY2x1ZGluZyBhbnkgY29sbGVjdGlvbiBwcmVmaXgpIGlzIHJlc29sdmVkLlxuXHRcdGNvbnN0IG5vZGUgPSBUeXBlR3JhcGhJbXBsLmNyZWF0ZU5vZGUoXG5cdFx0XHR0eXBlTmFtZSxcblx0XHRcdHBhcmVudE5vZGUsXG5cdFx0XHRzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0bGluZSArIDEsXG5cdFx0XHRjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0Y29sbGVjdGlvbklkXG5cdFx0KTtcblx0XHRub2RlLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSA9IHRoaXMuZ2V0UmVnaXN0cnlJbnRlcmZhY2VOYW1lKGNvbGxlY3Rpb25JZCk7XG5cblx0XHQvLyBTYW1lLW5hbWVzcGFjZSBkdXBsaWNhdGUgZGV0ZWN0aW9uIChoYXJkLWZhaWwgbGF3KVxuXHRcdHRoaXMucmVjb3JkRGVmaW5lU2l0ZShcblx0XHRcdHBhcmVudE5vZGUgPyBgJHtwYXJlbnROb2RlLmZ1bGxQYXRofS4ke3R5cGVOYW1lfWAgOiBgJHtjb2xsZWN0aW9uSWQgPz8gJ2RlZmF1bHQnfTo6JHt0eXBlTmFtZX1gLFxuXHRcdFx0YCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWBcblx0XHQpO1xuXG5cdFx0Ly8gRXh0cmFjdCBwcm9wZXJ0aWVzIGZyb20gdGhlIGNvbnN0cnVjdG9yIHJldHVybmVkIGJ5IHRoZSBsYXp5IGdldHRlclxuXHRcdC8vIOKAlCB0aGUgbmV3IG5vZGUgYW5jaG9ycyByZWxhdGl2ZS1maXJzdCBncmFwaCByZWZlcmVuY2UgcmVzb2x1dGlvblxuXHRcdGNvbnN0IHByZXZpb3VzQW5jaG9yID0gdGhpcy5jdXJyZW50R3JhcGhBbmNob3I7XG5cdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBub2RlO1xuXHRcdHRyeSB7XG5cdFx0XHRub2RlLnByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzKGNhbGwpO1xuXG5cdFx0XHQvLyBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZm9yIFR5cGVSZWdpc3RyeSBzaWduYXR1cmVcblx0XHRcdG5vZGUuY29uc3RydWN0b3JQYXJhbXMgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtcyhjYWxsKTtcblx0XHR9IGZpbmFsbHkge1xuXHRcdFx0dGhpcy5jdXJyZW50R3JhcGhBbmNob3IgPSBwcmV2aW91c0FuY2hvcjtcblx0XHR9XG5cblx0XHQvLyBBZGQgdG8gZ3JhcGhcblx0XHRpZiAocGFyZW50Tm9kZSkge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRDaGlsZChwYXJlbnROb2RlLCBub2RlKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0dGhpcy5ncmFwaC5hZGRSb290KG5vZGUpO1xuXHRcdH1cblxuXHRcdC8vIENyZWF0ZSBkZWZpbml0aW9uIGluZm8gdXNpbmcgdGhlIG5vZGUncyByZXNvbHZlZCBmdWxsUGF0aFxuXHRcdGNvbnN0IGRlZmluaXRpb246IERlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiBwYXJlbnROb2RlID8gcGFyZW50Tm9kZS5mdWxsUGF0aCA6IG51bGwsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IGNvbmZpZy5zdHJpY3RDaGFpbiA/PyB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBjb25maWcuYmxvY2tFcnJvcnMgPz8gZmFsc2UsXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChub2RlLmZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0XHR0aGlzLmVkc1Njb3BlQnlOb2RlLnNldChjYWxsLCBub2RlLmZ1bGxQYXRoKTtcblxuXHRcdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnQ6IGNvbnN0IExhenlUeXBlID0gbGF6eSgnTGF6eVR5cGUnLCAuLi4pIC0+IG1hcCBcIkxhenlUeXBlXCIgLT4gXCJMYXp5VHlwZVwiXG5cdFx0Ly8gRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBjb25zdCBYID0gbGF6eSgnQScpLmRlZmluZSgnQicpLCB3ZSB3YW50IHRvIG1hcCBYIC0+IEEgKHRoZSByb290KVxuXHRcdHRoaXMudHJhY2tWYXJpYWJsZUFzc2lnbm1lbnQoY2FsbCwgcGFyZW50Tm9kZSwgbm9kZS5mdWxsUGF0aCk7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBsYXp5KCkgY2FsbCBhcmd1bWVudHMgaW50byBhIG5vcm1hbGl6ZWQgc2hhcGUuXG5cdCAqIEhhbmRsZXMgbmFtZWQvdW5uYW1lZCBhbmQgZXhwbGljaXQtc291cmNlIGZvcm1zLCBib3RoIGFzIGZyZWUgY2FsbHNcblx0ICogYW5kIGFzIG1ldGhvZCBjYWxscy5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdExhenlDYWxsQXJncyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB7XG5cdFx0c291cmNlPzogdHMuRXhwcmVzc2lvbjtcblx0XHRuYW1lPzogc3RyaW5nO1xuXHRcdGdldHRlcjogdHMuRXhwcmVzc2lvbjtcblx0XHRjb25maWc/OiB0cy5FeHByZXNzaW9uO1xuXHR9IHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBhcmdzID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0Y29uc3QgaXNNZXRob2RDYWxsID0gdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKTtcblxuXHRcdGlmIChpc01ldGhvZENhbGwpIHtcblx0XHRcdC8vIFNvdXJjZSBpcyB0aGUgb2JqZWN0IG9mIHRoZSBwcm9wZXJ0eSBhY2Nlc3M6IFR5cGUubGF6eSguLi4pXG5cdFx0XHRjb25zdCBzb3VyY2UgPSBjYWxsLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgWyBtZXRob2RGaXJzdEFyZyBdID0gYXJncztcblx0XHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwobWV0aG9kRmlyc3RBcmcpKSB7XG5cdFx0XHRcdC8vIFR5cGUubGF6eSgnTmFtZScsIGdldHRlciwgY29uZmlnPylcblx0XHRcdFx0aWYgKGFyZ3MubGVuZ3RoIDwgMikge1xuXHRcdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHRzb3VyY2UsXG5cdFx0XHRcdFx0bmFtZSAgIDogbWV0aG9kRmlyc3RBcmcudGV4dCxcblx0XHRcdFx0XHRnZXR0ZXIgOiBhcmdzWyAxIF0sXG5cdFx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMiBdLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXHRcdFx0Ly8gVHlwZS5sYXp5KGdldHRlciwgY29uZmlnPylcblx0XHRcdHJldHVybiB7XG5cdFx0XHRcdHNvdXJjZSxcblx0XHRcdFx0Z2V0dGVyIDogbWV0aG9kRmlyc3RBcmcsXG5cdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDEgXSxcblx0XHRcdH07XG5cdFx0fVxuXG5cdFx0Ly8gRnJlZSBjYWxsOiBsYXp5KC4uLilcblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Y29uc3QgWyBmaXJzdEFyZyBdID0gYXJncztcblxuXHRcdC8vIEV4cGxpY2l0LXNvdXJjZSBmb3JtOiBsYXp5KHNvdXJjZSwgJ05hbWUnLCBnZXR0ZXIsIGNvbmZpZz8pXG5cdFx0Ly8gb3IgbGF6eShzb3VyY2UsIGdldHRlciwgY29uZmlnPylcblx0XHRpZiAoYXJncy5sZW5ndGggPj0gMiAmJiB0cy5pc0lkZW50aWZpZXIoZmlyc3RBcmcpKSB7XG5cdFx0XHRjb25zdCBbICwgc2Vjb25kQXJnIF0gPSBhcmdzO1xuXHRcdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChzZWNvbmRBcmcpKSB7XG5cdFx0XHRcdC8vIGxhenkoc291cmNlLCAnTmFtZScsIGdldHRlciwgY29uZmlnPylcblx0XHRcdFx0aWYgKGFyZ3MubGVuZ3RoIDwgMykge1xuXHRcdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHtcblx0XHRcdFx0XHRzb3VyY2UgOiBmaXJzdEFyZyxcblx0XHRcdFx0XHRuYW1lICAgOiBzZWNvbmRBcmcudGV4dCxcblx0XHRcdFx0XHRnZXR0ZXIgOiBhcmdzWyAyIF0sXG5cdFx0XHRcdFx0Y29uZmlnIDogYXJnc1sgMyBdLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXHRcdFx0Ly8gbGF6eShzb3VyY2UsIGdldHRlciwgY29uZmlnPylcblx0XHRcdHJldHVybiB7XG5cdFx0XHRcdHNvdXJjZSA6IGZpcnN0QXJnLFxuXHRcdFx0XHRnZXR0ZXIgOiBzZWNvbmRBcmcsXG5cdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDIgXSxcblx0XHRcdH07XG5cdFx0fVxuXG5cdFx0Ly8gTmFtZWQgcm9vdCBmb3JtOiBsYXp5KCdOYW1lJywgZ2V0dGVyLCBjb25maWc/KVxuXHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoZmlyc3RBcmcpKSB7XG5cdFx0XHRpZiAoYXJncy5sZW5ndGggPCAyKSB7XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRuYW1lICAgOiBmaXJzdEFyZy50ZXh0LFxuXHRcdFx0XHRnZXR0ZXIgOiBhcmdzWyAxIF0sXG5cdFx0XHRcdGNvbmZpZyA6IGFyZ3NbIDIgXSxcblx0XHRcdH07XG5cdFx0fVxuXG5cdFx0Ly8gVW5uYW1lZCByb290IGZvcm06IGxhenkoZ2V0dGVyLCBjb25maWc/KVxuXHRcdHJldHVybiB7XG5cdFx0XHRnZXR0ZXIgOiBmaXJzdEFyZyxcblx0XHRcdGNvbmZpZyA6IGFyZ3NbIDEgXSxcblx0XHR9O1xuXHR9XG5cblx0LyoqXG5cdCAqIFVud3JhcCB0aGUgY29uc3RydWN0b3IgcmV0dXJuZWQgYnkgYSBsYXp5IGdldHRlci5cblx0ICogU3VwcG9ydHM6XG5cdCAqICAgKCkgPT4gY2xhc3MgTmFtZSB7fVxuXHQgKiAgICgpID0+IGZ1bmN0aW9uIE5hbWUoKSB7fVxuXHQgKiAgICgpID0+IHsgcmV0dXJuIGNsYXNzIE5hbWUge307IH1cblx0ICogICBmdW5jdGlvbiAoKSB7IHJldHVybiBmdW5jdGlvbiBOYW1lKCkge307IH1cblx0ICovXG5cdHByaXZhdGUgdW53cmFwTGF6eUdldHRlciAoZ2V0dGVyRXhwcjogdHMuRXhwcmVzc2lvbik6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc0Fycm93RnVuY3Rpb24oZ2V0dGVyRXhwcikpIHtcblx0XHRcdGNvbnN0IHsgYm9keSB9ID0gZ2V0dGVyRXhwcjtcblx0XHRcdGlmICghdHMuaXNCbG9jayhib2R5KSkge1xuXHRcdFx0XHRyZXR1cm4gYm9keTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3Qgc3RtdCBvZiBib2R5LnN0YXRlbWVudHMpIHtcblx0XHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KHN0bXQpICYmIHN0bXQuZXhwcmVzc2lvbikge1xuXHRcdFx0XHRcdHJldHVybiBzdG10LmV4cHJlc3Npb247XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGdldHRlckV4cHIpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGdldHRlckV4cHI7XG5cdFx0XHRmb3IgKGNvbnN0IHN0bXQgb2YgYm9keS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1JldHVyblN0YXRlbWVudChzdG10KSAmJiBzdG10LmV4cHJlc3Npb24pIHtcblx0XHRcdFx0XHRyZXR1cm4gc3RtdC5leHByZXNzaW9uO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIE5vdCBhIHJlY29nbml6ZWQgZ2V0dGVyIHBhdHRlcm5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgYSBjb25zdHJ1Y3RvciBuYW1lIGZyb20gYSBjbGFzcyBleHByZXNzaW9uLCBjbGFzcyBkZWNsYXJhdGlvbixcblx0ICogb3IgbmFtZWQgZnVuY3Rpb24gZXhwcmVzc2lvbi5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENvbnN0cnVjdG9yTmFtZSAoY29uc3RydWN0b3JFeHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSAmJiBjb25zdHJ1Y3RvckV4cHIubmFtZSkge1xuXHRcdFx0cmV0dXJuIGNvbnN0cnVjdG9yRXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0NsYXNzRGVjbGFyYXRpb24oY29uc3RydWN0b3JFeHByKSAmJiBjb25zdHJ1Y3RvckV4cHIubmFtZSkge1xuXHRcdFx0cmV0dXJuIGNvbnN0cnVjdG9yRXhwci5uYW1lLnRleHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpICYmIGNvbnN0cnVjdG9yRXhwci5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gY29uc3RydWN0b3JFeHByLm5hbWUudGV4dDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSB0eXBlIG5hbWUgZnJvbSBlaXRoZXIgYSBkZWZpbmUoKSBvciBsYXp5KCkgY2FsbC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRoaXMuaXNEZWZpbmVDYWxsKGNhbGwpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5leHRyYWN0VHlwZU5hbWUoY2FsbCk7XG5cdFx0fVxuXHRcdGlmICh0aGlzLmlzTGF6eUNhbGwoY2FsbCkpIHtcblx0XHRcdGNvbnN0IGFyZ3MgPSB0aGlzLmV4dHJhY3RMYXp5Q2FsbEFyZ3MoY2FsbCk7XG5cdFx0XHRpZiAoIWFyZ3MpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGlmIChhcmdzLm5hbWUpIHtcblx0XHRcdFx0cmV0dXJuIGFyZ3MubmFtZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMudW53cmFwTGF6eUdldHRlcihhcmdzLmdldHRlcik7XG5cdFx0XHRpZiAoY29uc3RydWN0b3JFeHByKSB7XG5cdFx0XHRcdHJldHVybiB0aGlzLmV4dHJhY3RDb25zdHJ1Y3Rvck5hbWUoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSBmdWxsIGxhenkoKSBjYWxsIGNvbnRleHQ6IHR5cGUgbmFtZSwgcGFyZW50IHR5cGUsIGFuZCBjb2xsZWN0aW9uLlxuXHQgKiBIYW5kbGVzIGRpcmVjdCBjYWxscywgcHJvcGVydHktYWNjZXNzIGNhbGxzLCBjaGFpbmVkIGNhbGxzLCBhbmQgdGhlXG5cdCAqIGV4cGxpY2l0LXNvdXJjZSBmb3JtIGBsYXp5KHNvdXJjZSwgJ1R5cGVOYW1lJywgZ2V0dGVyKWAuXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q29udGV4dCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB7XG5cdFx0dHlwZU5hbWU/OiBzdHJpbmc7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Y29uc3QgYXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRpZiAoIWFyZ3MpIHtcblx0XHRcdHJldHVybiB7fTtcblx0XHR9XG5cblx0XHRsZXQgdHlwZU5hbWU6IHN0cmluZyB8IHVuZGVmaW5lZCA9IGFyZ3MubmFtZTtcblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLnVud3JhcExhenlHZXR0ZXIoYXJncy5nZXR0ZXIpO1xuXHRcdFx0aWYgKGNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0XHR0eXBlTmFtZSA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yTmFtZShjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAoIXR5cGVOYW1lKSB7XG5cdFx0XHRyZXR1cm4ge307XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBjYWxsO1xuXG5cdFx0Ly8gRGlyZWN0IGNhbGw6IGxhenkoJ1R5cGVOYW1lJywgLi4uKSBvciBsYXp5KHNvdXJjZSwgJ1R5cGVOYW1lJywgZ2V0dGVyKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnbGF6eScpIHtcblx0XHRcdGlmIChhcmdzLnNvdXJjZSAmJiB0cy5pc0lkZW50aWZpZXIoYXJncy5zb3VyY2UpKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2UoYXJncy5zb3VyY2UudGV4dCk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXHRcdFx0Ly8gUGxhaW4gcm9vdCBsYXp5IGluIGRlZmF1bHQgY29sbGVjdGlvblxuXHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUgfTtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSBhY2Nlc3M6IFgubGF6eSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnbGF6eScpIHtcblx0XHRcdGNvbnN0IG9iaiA9IGV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblxuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihvYmopKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uob2JqLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4ge1xuXHRcdFx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0XHRcdHBhcmVudFR5cGUgICA6IHNvdXJjZUNvbnRleHQucGFyZW50VHlwZSxcblx0XHRcdFx0XHRjb2xsZWN0aW9uSWQgOiBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCxcblx0XHRcdFx0fTtcblx0XHRcdH1cblxuXHRcdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gTmVzdGVkIGFjY2VzczogaW5zdGFuY2UuVHlwZS5sYXp5IC0gdHJ5IHRvIHJlc29sdmVcblx0XHRcdFx0Y29uc3QgY2hhaW4gPSB0aGlzLmdldFByb3BlcnR5Q2hhaW4ob2JqKTtcblx0XHRcdFx0aWYgKGNoYWluLmxlbmd0aCA+IDApIHtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShjaGFpbi5qb2luKCcuJykpO1xuXHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSB9O1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG9iaikpIHtcblx0XHRcdFx0Ly8gRGV0ZXJtaW5lIHRoZSBjb2xsZWN0aW9uIGNvbnRleHQgZnJvbSB0aGUgcm9vdCBvZiB0aGUgY2hhaW4gc28gdGhhdFxuXHRcdFx0XHQvLyBjdXN0b20tY29sbGVjdGlvbiB0eXBlcyBkbyBub3QgZ2V0IGNvbmZ1c2VkIHdpdGggZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzLlxuXHRcdFx0XHRjb25zdCByb290SWQgPSB0aGlzLmdldFJvb3RJZGVudGlmaWVyKG9iai5leHByZXNzaW9uKTtcblx0XHRcdFx0Y29uc3QgZXhwZWN0ZWRDb2xsZWN0aW9uSWQgPSByb290SWRcblx0XHRcdFx0XHQ/IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShyb290SWQudGV4dCkuY29sbGVjdGlvbklkXG5cdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cblx0XHRcdFx0Ly8gQ2hhaW5lZCBjYWxsOiBkZWZpbmUoJ0EnKS5sYXp5KCdCJykgb3IgbGF6eSgnQScpLmxhenkoJ0InKVxuXHRcdFx0XHRpZiAodGhpcy5pc0RlZmluZUNhbGwob2JqKSkge1xuXHRcdFx0XHRcdHRoaXMucHJvY2Vzc0RlZmluZUNhbGwob2JqLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdE1uZW1vbmljYVR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRpZiAodGhpcy5pc0xhenlDYWxsKG9iaikpIHtcblx0XHRcdFx0XHR0aGlzLnByb2Nlc3NMYXp5Q2FsbChvYmosIHNvdXJjZUZpbGUpO1xuXHRcdFx0XHRcdGNvbnN0IHBhcmVudFR5cGVOYW1lID0gdGhpcy5leHRyYWN0TW5lbW9uaWNhVHlwZU5hbWUob2JqKTtcblx0XHRcdFx0XHRpZiAocGFyZW50VHlwZU5hbWUpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlOYW1lKHBhcmVudFR5cGVOYW1lLCBleHBlY3RlZENvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIEJ1aWxkZXIgbG9va3VwIGNoYWluOiBBcHAubG9va3VwKCdVc2VyJykubGF6eSgnQWRtaW4nKVxuXHRcdFx0XHRpZiAodGhpcy5pc0xvb2t1cENhbGwob2JqKSkge1xuXHRcdFx0XHRcdGNvbnN0IGxvb2tlZFVwUGF0aCA9IHRoaXMucmVzb2x2ZUxvb2t1cFBhdGgob2JqKTtcblx0XHRcdFx0XHRpZiAobG9va2VkVXBQYXRoKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZShsb29rZWRVcFBhdGgpO1xuXHRcdFx0XHRcdFx0aWYgKHBhcmVudE5vZGUpIHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIHsgdHlwZU5hbWUsIHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlLmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBjb25maWcgb3B0aW9ucyBmcm9tIGxhenkoKSBjYWxsXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RMYXp5Q29uZmlnIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSB7XG5cdFx0Y29uc3QgYXJncyA9IHRoaXMuZXh0cmFjdExhenlDYWxsQXJncyhjYWxsKTtcblx0XHRpZiAoIWFyZ3MgfHwgIWFyZ3MuY29uZmlnIHx8ICF0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGFyZ3MuY29uZmlnKSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IGNvbmZpZ1Jlc3VsdCA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGFyZ3MuY29uZmlnKTtcblx0XHRyZXR1cm4gY29uZmlnUmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdFx0KiBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50cyB0aGF0IGNhcHR1cmUgZGVmaW5lKCkgcmVzdWx0c1xuXHRcdCogZS5nLiwgY29uc3QgVXNlciA9IGRlZmluZSgnVXNlckVudGl0eScsIC4uLikgbWFwcyBcIlVzZXJcIiAtPiBcIlVzZXJFbnRpdHlcIlxuXHRcdCogRm9yIGNoYWluZWQgY2FsbHMgbGlrZSBjb25zdCBYID0gZGVmaW5lKCdBJykuZGVmaW5lKCdCJyksIHdlIG1hcCBYIC0+IEEgKHRoZSByb290IHR5cGUpXG5cdFx0Ki9cblx0cHJpdmF0ZSB0cmFja1ZhcmlhYmxlQXNzaWdubWVudCAoXG5cdFx0Y2FsbDogdHMuQ2FsbEV4cHJlc3Npb24sXG5cdFx0cGFyZW50Tm9kZTogVHlwZU5vZGUgfCB1bmRlZmluZWQsXG5cdFx0ZnVsbFBhdGg6IHN0cmluZ1xuXHQpOiB2b2lkIHtcblx0XHQvLyBDaGVjayBpZiB0aGlzIGNhbGwgaXMgdGhlIHJpZ2h0LWhhbmQgc2lkZSBvZiBhIHZhcmlhYmxlIGRlY2xhcmF0aW9uXG5cdFx0Ly8gV2FsayB1cCB0aGUgdHJlZSB0byBmaW5kIFZhcmlhYmxlRGVjbGFyYXRpb25cblx0XHRsZXQgY3VycmVudDogdHMuTm9kZSB8IHVuZGVmaW5lZCA9IGNhbGwucGFyZW50O1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRpZiAodHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKGN1cnJlbnQpKSB7XG5cdFx0XHRcdC8vIEZvdW5kOiBjb25zdCBYID0gZGVmaW5lKC4uLilcblx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50Lm5hbWUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgdmFyTmFtZSA9IGN1cnJlbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRcdC8vIEYxODogZGVmaW5lKCkgcmV0dXJucyB0aGUgREVGSU5FRCB0eXBlJ3MgY29uc3RydWN0b3IsXG5cdFx0XHRcdFx0Ly8gc28gYSBjb25zdCBob2xkaW5nIGEgbXVsdGktaG9wIGluaXRpYWxpemVyXG5cdFx0XHRcdFx0Ly8gKGBjb25zdCBYID0gQS5kZWZpbmUoJ0InKS5kZWZpbmUoJ0MnKWApIGJpbmRzIHRoZSBMQVNUXG5cdFx0XHRcdFx0Ly8gaG9wIOKAlCBhIGRlZXBlciBob3AgbXVzdCBub3QgYmluZCwgYW5kIHRoZSBvdXRlcm1vc3Rcblx0XHRcdFx0XHQvLyBob3AgYmluZHMgdW5jb25kaXRpb25hbGx5ICh2aXNpdC1vcmRlciBpbmRlcGVuZGVudClcblx0XHRcdFx0XHRpZiAodGhpcy5pc0RlZXBlckRlZmluZUhvcChjYWxsKSkge1xuXHRcdFx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHQvLyBGb3IgY2hhaW5lZCBsYXp5IGNhbGxzIGxpa2UgY29uc3QgWCA9IGRlZmluZSgnQScpLmxhenkoJ0InKSxcblx0XHRcdFx0XHQvLyB0aGUgZmlyc3QgY2FsbCBpbiB0aGUgY2hhaW4gc2V0cyB0aGUgbWFwcGluZyAobGF6eSBob3Bcblx0XHRcdFx0XHQvLyBrZWVwcyBpdCDigJQgcGlubmVkIGJlaGF2aW9yKVxuXHRcdFx0XHRcdGlmIChwYXJlbnROb2RlICYmIHRoaXMudmFyaWFibGVUb1R5cGVNYXAuaGFzKHZhck5hbWUpKSB7XG5cdFx0XHRcdFx0XHRyZXR1cm47XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdHRoaXMudmFyaWFibGVUb1R5cGVNYXAuc2V0KHZhck5hbWUsIGZ1bGxQYXRoKTtcblx0XHRcdFx0XHR0aGlzLnRyYWNrRmlsZUdyYXBoQmluZGluZyh2YXJOYW1lLCBmdWxsUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0Y3VycmVudCA9IGN1cnJlbnQucGFyZW50O1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBBIGAuZGVmaW5lKC4uLilgIGhvcCB3cmFwcGVkIGJ5IGFub3RoZXIgYC5kZWZpbmUoLi4uKWAgY2FsbCBpcyBub3Rcblx0ICogdGhlIHZhbHVlIGl0cyBjb25zdCBlbmRzIHVwIGhvbGRpbmcg4oCUIHRoZSBPVVRFUk1PU1QgaG9wIG9mIHRoZVxuXHQgKiBpbml0aWFsaXplciBjaGFpbiBpcyAoZGVmaW5lKCkgcmV0dXJucyB0aGUgZGVmaW5lZCB0eXBlJ3Ncblx0ICogY29uc3RydWN0b3IpLiBPbmx5IHRoZSBvdXRlcm1vc3QgaG9wIG1heSBiaW5kIHRoZSB2YXJpYWJsZS5cblx0ICovXG5cdHByaXZhdGUgaXNEZWVwZXJEZWZpbmVIb3AgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgeyBwYXJlbnQgfSA9IGNhbGw7XG5cdFx0Y29uc3QgZGVlcGVyID0gISFwYXJlbnQgJiZcblx0XHRcdHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKHBhcmVudCkgJiZcblx0XHRcdHBhcmVudC5uYW1lLnRleHQgPT09ICdkZWZpbmUnICYmXG5cdFx0XHR0cy5pc0NhbGxFeHByZXNzaW9uKHBhcmVudC5wYXJlbnQpICYmXG5cdFx0XHRwYXJlbnQucGFyZW50LmV4cHJlc3Npb24gPT09IHBhcmVudDtcblx0XHRyZXR1cm4gZGVlcGVyO1xuXHR9XG5cblx0LyoqXG5cdCAqIE1pcnJvciBhIHZhcmlhYmxlIC0+IG1uZW1vbmljYSBmdWxsUGF0aCBiaW5kaW5nIGludG8gdGhlIHBlci1maWxlXG5cdCAqIHZhbHVlLXNjb3BlIG1hcCAoZ3JhcGggaWRlbnRpdHkgbGF3OiBgdHlwZW9mIFhgIGFuZCBiYXJlIHJlZmVyZW5jZXNcblx0ICogcmVzb2x2ZSB0aHJvdWdoIHRoZSBmaWxlJ3Mgb3duIGJpbmRpbmdzIGZpcnN0KS5cblx0ICovXG5cdHByaXZhdGUgdHJhY2tGaWxlR3JhcGhCaW5kaW5nICh2YXJOYW1lOiBzdHJpbmcsIGZ1bGxQYXRoOiBzdHJpbmcpOiB2b2lkIHtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRsZXQgYmluZGluZ3MgPSB0aGlzLmZpbGVHcmFwaEJpbmRpbmdzLmdldChmaWxlUGF0aCk7XG5cdFx0aWYgKCFiaW5kaW5ncykge1xuXHRcdFx0YmluZGluZ3MgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nPigpO1xuXHRcdFx0dGhpcy5maWxlR3JhcGhCaW5kaW5ncy5zZXQoZmlsZVBhdGgsIGJpbmRpbmdzKTtcblx0XHR9XG5cdFx0YmluZGluZ3Muc2V0KHZhck5hbWUsIGZ1bGxQYXRoKTtcblx0fVxuXHRcblx0LyoqXG5cdFx0KiBUcmFjayB2YXJpYWJsZSBhc3NpZ25tZW50cyBmcm9tIGxvb2t1cCgpIGNhbGxzXG5cdFx0KiBlLmcuLCBjb25zdCBTZW50aWVuY2VDb25zdHJ1Y3RvciA9IGxvb2t1cCgnU2VudGllbmNlJykgbWFwcyBcIlNlbnRpZW5jZUNvbnN0cnVjdG9yXCIgLT4gXCJTZW50aWVuY2VcIlxuXHRcdCovXG5cdHByaXZhdGUgdHJhY2tMb29rdXBBc3NpZ25tZW50IChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbiwgdHlwZVBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdHRoaXMuYmluZFJlc3VsdFZhcmlhYmxlKGNhbGwsIHR5cGVQYXRoKTtcblx0fVxuXG5cdC8qKlxuXHRcdCogVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudHMgZnJvbSBuZXcgVHlwZSgpIGNhbGxzXG5cdFx0KiBlLmcuLCBjb25zdCB1c2VyID0gbmV3IFVzZXJUeXBlKCkgbWFwcyBcInVzZXJcIiAtPiBcIlVzZXJUeXBlXCJcblx0XHQqL1xuXHRwcml2YXRlIHRyYWNrTmV3QXNzaWdubWVudCAobmV3RXhwcjogdHMuTmV3RXhwcmVzc2lvbiwgdHlwZVBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdGxldCBlZmZlY3RpdmVQYXRoID0gdHlwZVBhdGg7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBuZXdFeHByLnBhcmVudDtcblx0XHQvLyBDaGFpbi1mb3JtIGNvbnN0cnVjdGlvbjogbmV3IFIoKS5BKCkuQigpIOKAlCB0aGUgcmVzdWx0IHZhcmlhYmxlXG5cdFx0Ly8gaG9sZHMgdGhlIE9VVEVSTU9TVCB0aXAncyBpbnN0YW5jZSAoYXdhaXQtdHJhbnNwYXJlbnQpLCBub3QgdGhlXG5cdFx0Ly8gaW5uZXIgbmV3J3MgdHlwZS4gV2FsayB0aGUgY2hhaW4sIGtlZXBpbmcgdGhlIGxhc3QgcmVzb2x2YWJsZSB0aXAuXG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdXJyZW50KSAmJlxuXHRcdFx0XHR0cy5pc0NhbGxFeHByZXNzaW9uKGN1cnJlbnQucGFyZW50KSAmJlxuXHRcdFx0XHRjdXJyZW50LnBhcmVudC5leHByZXNzaW9uID09PSBjdXJyZW50KSB7XG5cdFx0XHRcdGNvbnN0IHRpcCA9IHRoaXMucmVzb2x2ZUNoYWluVGlwVHlwZVBhdGgoY3VycmVudC5wYXJlbnQpO1xuXHRcdFx0XHRpZiAodGlwKSB7XG5cdFx0XHRcdFx0ZWZmZWN0aXZlUGF0aCA9IHRpcDtcblx0XHRcdFx0fVxuXHRcdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQucGFyZW50O1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGJyZWFrO1xuXHRcdH1cblx0XHR0aGlzLmJpbmRSZXN1bHRWYXJpYWJsZShuZXdFeHByLCBlZmZlY3RpdmVQYXRoKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBCaW5kIHRoZSBuZWFyZXN0IGVuY2xvc2luZyBgY29uc3QvbGV0L3ZhciBYID0g4oCmYCB0byBhIG1uZW1vbmljYVxuXHQgKiBmdWxsUGF0aCDigJQgdGhlIHNoYXJlZCByZXN1bHQtdmFyaWFibGUgd2Fsa2VyIGJlaGluZCBuZXcvbG9va3VwL1xuXHQgKiBjaGFpbi9mb3JrL21lcmdlL2NhbGwgdHJhY2tpbmcgKHZhbHVlIHNjb3BlOiBkb3duc3RyZWFtIHJlZmVyZW5jZXNcblx0ICogYW5kIGB0aGlzLnggPSB4YCBhc3NpZ25tZW50cyByZXNvbHZlIHRocm91Z2ggdGhlIHNhbWUgYmluZGluZykuXG5cdCAqL1xuXHRwcml2YXRlIGJpbmRSZXN1bHRWYXJpYWJsZSAoZnJvbTogdHMuTm9kZSwgdHlwZVBhdGg6IHN0cmluZyk6IHZvaWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gZnJvbS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc1ZhcmlhYmxlRGVjbGFyYXRpb24oY3VycmVudCkpIHtcblx0XHRcdFx0Ly8gRm91bmQ6IGNvbnN0IFggPSA8Y29uc3RydWN0aW9uPlxuXHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGN1cnJlbnQubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCB2YXJOYW1lID0gY3VycmVudC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0dGhpcy52YXJpYWJsZVRvVHlwZU1hcC5zZXQodmFyTmFtZSwgdHlwZVBhdGgpO1xuXHRcdFx0XHRcdHRoaXMudHJhY2tGaWxlR3JhcGhCaW5kaW5nKHZhck5hbWUsIHR5cGVQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm47XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlY29yZCBhbiBgaW5zdGFudGlhdGlvbmAgdXNhZ2UgZm9yIGEgY29uc3RydWN0aW9uLXNoYXBlIGNhbGxcblx0ICogKGNoYWluIHRpcCAvIGNhbGwgLyBhcHBseSAvIGZvcmsgLyBjbG9uZSAvIG1lcmdlIOKAlFxuXHQgKiBieXRlLWluZGlzdGluZ3Vpc2hhYmxlIGZyb20gYG5ld2AgdW50aWwgdGhlIGRlZmVycmVkXG5cdCAqIG1lY2hhbmlzbS1raW5kIHJldmlzaW9uKS4gYGNvbnN0cnVjdG9yVGV4dGAgZGVmYXVsdHMgdG8gdGhlIGNhbGxlZVxuXHQgKiBleHByZXNzaW9uIHRleHQgc28gdGhlIHNpdGUgc3RheXMgcmVhZGFibGUgd2l0aG91dCBuZXcgZmllbGRzO1xuXHQgKiBjYWxsL2FwcGx5IG92ZXJyaWRlIGl0IHdpdGggdGhlIEN0b3IgYXJndW1lbnQgdGV4dC5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkQ29uc3RydWN0aW9uVXNhZ2UgKFxuXHRcdGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uLFxuXHRcdHR5cGVQYXRoOiBzdHJpbmcsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRjb25zdHJ1Y3RvclRleHQ/OiBzdHJpbmdcblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdGNhbGwuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGN0b3JUZXh0ID0gY29uc3RydWN0b3JUZXh0ID8/IGNhbGwuZXhwcmVzc2lvbi5nZXRUZXh0KHNvdXJjZUZpbGUpO1xuXHRcdHRoaXMuYWRkVXNhZ2UodHlwZVBhdGgsIHtcblx0XHRcdGxvY2F0aW9uICAgICAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0a2luZCAgICAgICAgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0Y29kZSAgICAgICAgICAgIDogY2FsbC5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRjb25zdHJ1Y3RvclRleHQgOiBjdG9yVGV4dC5zbGljZSgwLCAxMDApLFxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgdGhlIHR5cGUgYSBjb25zdHJ1Y3Rpb24tY2hhaW4gdGlwIGNhbGwgY29uc3RydWN0czpcblx0ICogYG5ldyBSKC4uLikuQSguLi4pYCBjb25zdHJ1Y3RzIFIuQTsgYGF3YWl0IG5ldyBSKC4uLikuQSguLi4pLkIoLi4uKWBcblx0ICogY29uc3RydWN0cyBSLkEuQi4gVGhlIHJlY2VpdmVyIGlzIHRoZSBuZXN0ZWQgY2hhaW4gKE5ld0V4cHJlc3Npb25cblx0ICogYmFzZSwgdGhlbiB0aXAgY2FsbHMpOyBleGFjdCBmdWxsUGF0aCBmaXJzdCwgYW5kIG9ubHkgd2hlbiB0aGUgcm9vdFxuXHQgKiBpdHNlbGYgaXMgdW5rbm93biBkb2VzIHRoZSBwcm9wLW5hbWUgZmFsbGJhY2sgbGF3IGFwcGx5IChzbyBwbGFpblxuXHQgKiBtZXRob2QgY2FsbHMgb24gZnJlc2ggaW5zdGFuY2VzIG5ldmVyIHJlY29yZCBhIGNvbnN0cnVjdGlvbikuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVDaGFpblRpcFR5cGVQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZWNlaXZlciA9IGNhbGwuZXhwcmVzc2lvbjtcblx0XHRsZXQgcm9vdFBhdGg6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRpZiAodHMuaXNOZXdFeHByZXNzaW9uKHJlY2VpdmVyLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRjb25zdCBpbm5lciA9IHJlY2VpdmVyLmV4cHJlc3Npb247XG5cdFx0XHRyb290UGF0aCA9IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGlubmVyLmV4cHJlc3Npb24pXG5cdFx0XHRcdD8gdGhpcy5yZXNvbHZlVHlwZVBhdGgoaW5uZXIuZXhwcmVzc2lvbilcblx0XHRcdFx0OiB0aGlzLmdldFR5cGVOYW1lRnJvbUV4cHJlc3Npb24oaW5uZXIuZXhwcmVzc2lvbik7XG5cdFx0fSBlbHNlIGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKHJlY2VpdmVyLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyb290UGF0aCA9IHRoaXMucmVzb2x2ZUNoYWluVGlwVHlwZVBhdGgocmVjZWl2ZXIuZXhwcmVzc2lvbik7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGlmICghcm9vdFBhdGgpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGNhbmRpZGF0ZSA9IGAke3Jvb3RQYXRofS4ke3JlY2VpdmVyLm5hbWUudGV4dH1gO1xuXHRcdGlmICh0aGlzLmRlZmluaXRpb25zLmhhcyhjYW5kaWRhdGUpKSB7XG5cdFx0XHRyZXR1cm4gY2FuZGlkYXRlO1xuXHRcdH1cblx0XHRpZiAoIXRoaXMuZGVmaW5pdGlvbnMuaGFzKHJvb3RQYXRoKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMucmVzb2x2ZVR5cGVQYXRoKHJlY2VpdmVyKTtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBUcnVlIHdoZW4gYGV4cHJgIGRlbm90ZXMgYSBjb25zdHJ1Y3Rpb24gZnVuY3Rpb24gaW1wb3J0ZWQgZnJvbVxuXHQgKiAnbW5lbW9uaWNhJyDigJQgdGhlIG5hbWVkLWltcG9ydCBmb3JtIChgaW1wb3J0IHsgY2FsbCB9IGZyb21cblx0ICogJ21uZW1vbmljYSdgLCBhbGlhc2VzIGluY2x1ZGVkKSBvciBhIG1lbWJlciBvZiBhIHRyYWNrZWRcblx0ICogbW9kdWxlLW9iamVjdCBhbGlhcyAoYG1uZW1vbmljYS5jYWxsYCkuIFVzZXJsYW5kIGNhbGwvYXBwbHkvYmluZFxuXHQgKiBmdW5jdGlvbnMgbmV2ZXIgbWF0Y2guXG5cdCAqL1xuXHRwcml2YXRlIGlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4gKGV4cHI6IHRzLkV4cHJlc3Npb24sIGZuOiAnY2FsbCcgfCAnYXBwbHknIHwgJ2JpbmQnKTogYm9vbGVhbiB7XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLm1uZW1vbmljYU5hbWVkSW1wb3J0cy5nZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKT8uZ2V0KGV4cHIudGV4dCk7XG5cdFx0XHRjb25zdCBtYXRjaGVkID0gaW1wb3J0ZWQgPT09IGZuO1xuXHRcdFx0cmV0dXJuIG1hdGNoZWQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSAmJiBleHByLm5hbWUudGV4dCA9PT0gZm4pIHtcblx0XHRcdGNvbnN0IG1hdGNoZWQgPSB0cy5pc0lkZW50aWZpZXIoZXhwci5leHByZXNzaW9uKSAmJlxuXHRcdFx0XHR0aGlzLm1vZHVsZU9iamVjdFZhcmlhYmxlcy5oYXMoZXhwci5leHByZXNzaW9uLnRleHQpO1xuXHRcdFx0cmV0dXJuIG1hdGNoZWQ7XG5cdFx0fVxuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBtbmVtb25pY2EgY2FsbC9hcHBseShlbnRpdHksIEN0b3IsIC4uLikgLyBiaW5kKGVudGl0eSwgQ3Rvcik6XG5cdCAqIHJlc29sdmUgdGhlIEN0b3IgYXJndW1lbnQgKGFyZyAxKSB0byBhIGdyYXBoIGZ1bGxQYXRoIHRocm91Z2ggdGhlXG5cdCAqIHNhbWUgdGllcnMgYXMgdGhlIGBuZXdgIGJyYW5jaCAodmFsdWUgc2NvcGUgZm9yIGlkZW50aWZpZXJzLFxuXHQgKiBjaGFpbiByZXNvbHV0aW9uIGZvciBwcm9wZXJ0eSBhY2Nlc3NlcykuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVDb25zdHJ1Y3Rpb25GblR5cGVQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2FsbGVlID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGNvbnN0IGlzQ2FsbE9yQXBwbHkgPSB0aGlzLmlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4oY2FsbGVlLCAnY2FsbCcpIHx8XG5cdFx0XHR0aGlzLmlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4oY2FsbGVlLCAnYXBwbHknKTtcblx0XHRjb25zdCBpc0JpbmQgPSB0aGlzLmlzTW5lbW9uaWNhQ29uc3RydWN0aW9uRm4oY2FsbGVlLCAnYmluZCcpO1xuXHRcdGlmICghaXNDYWxsT3JBcHBseSAmJiAhaXNCaW5kKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRpZiAoY2FsbC5hcmd1bWVudHMubGVuZ3RoIDwgMikge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Y29uc3QgWyAsIGN0b3JBcmcgXSA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdGxldCByZXNvbHZlZDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdG9yQXJnKSkge1xuXHRcdFx0cmVzb2x2ZWQgPSB0aGlzLnJlc29sdmVUeXBlUGF0aChjdG9yQXJnKTtcblx0XHR9IGVsc2UgaWYgKHRzLmlzSWRlbnRpZmllcihjdG9yQXJnKSkge1xuXHRcdFx0Y29uc3QgYm91bmQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChjdG9yQXJnLnRleHQpO1xuXHRcdFx0aWYgKGJvdW5kKSB7XG5cdFx0XHRcdHJlc29sdmVkID0gYm91bmQ7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRjb25zdCBncmFwaFJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUoY3RvckFyZy50ZXh0KTtcblx0XHRcdFx0aWYgKGdyYXBoUmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdFx0XHRyZXNvbHZlZCA9IGdyYXBoUmVzdWx0Lm5vZGUuZnVsbFBhdGg7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc3Qga25vd24gPSByZXNvbHZlZCAmJiB0aGlzLmRlZmluaXRpb25zLmhhcyhyZXNvbHZlZCkgPyByZXNvbHZlZCA6IHVuZGVmaW5lZDtcblx0XHRyZXR1cm4ga25vd247XG5cdH1cblxuXHQvKipcblx0ICogaW5zdGFuY2UuZm9yayguLi4pIC8gaW5zdGFuY2UuY2xvbmUoLi4uKSBvbiBhIHRyYWNrZWQgdmFyaWFibGUg4oCUXG5cdCAqIHJ1bnRpbWUgcmV0dXJucyBgdGhpc2AsIHNvIHRoZSByZXN1bHQgY2FycmllcyB0aGUgc291cmNlIHR5cGUuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVGb3JrTGlrZVR5cGVQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCF0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCBtZXRob2QgPSBjYWxsLmV4cHJlc3Npb24ubmFtZS50ZXh0O1xuXHRcdGlmIChtZXRob2QgIT09ICdmb3JrJyAmJiBtZXRob2QgIT09ICdjbG9uZScpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlY2VpdmVyID0gY2FsbC5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIocmVjZWl2ZXIpKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChyZWNlaXZlci50ZXh0KTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEZyZWUgdXRpbHMgZm9ybXM6IHV0aWxzLm1lcmdlKGEsIGIsIC4uLikgKGFsc28gdGhlIGRpcmVjdCBuYW1lZFxuXHQgKiBpbXBvcnQgYG1lcmdlKGEsIGIpYCkgYW5kIHRoZSBjdXJyaWVkIHV0aWxzLmZvcmsoaW5zdGFuY2UpKC4uLikuXG5cdCAqIFRoZSByZXN1bHQgYmluZHMgdG8gYXJnIDAncyB0eXBlIOKAlCBydW50aW1lIHJldHVybnMgYSdzIGxpbmVhZ2Ugb3ZlclxuXHQgKiBiJ3MgY29udGV4dDsgYSdzIGZ1bGxQYXRoIGlzIHRoZSBob25lc3QgYXBwcm94aW1hdGlvbiB3aXRoaW4gdGhlXG5cdCAqIG91dHB1dCBjb250cmFjdCAoZG9jdW1lbnRlZCBpbiBSRUFETUUpLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlVXRpbHNGblR5cGVQYXRoIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2FsbGVlID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGNvbnN0IGlzVXRpbHNPd25lciA9IChvd25lcjogdHMuRXhwcmVzc2lvbik6IGJvb2xlYW4gPT4ge1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihvd25lcikpIHtcblx0XHRcdFx0Y29uc3QgaW1wb3J0ZWQgPSB0aGlzLm1uZW1vbmljYU5hbWVkSW1wb3J0cy5nZXQodGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKT8uZ2V0KG93bmVyLnRleHQpO1xuXHRcdFx0XHRyZXR1cm4gaW1wb3J0ZWQgPT09ICd1dGlscyc7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBtYXRjaGVkID0gdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ob3duZXIpICYmIG93bmVyLm5hbWUudGV4dCA9PT0gJ3V0aWxzJyAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIob3duZXIuZXhwcmVzc2lvbikgJiYgdGhpcy5tb2R1bGVPYmplY3RWYXJpYWJsZXMuaGFzKG93bmVyLmV4cHJlc3Npb24udGV4dCk7XG5cdFx0XHRyZXR1cm4gbWF0Y2hlZDtcblx0XHR9O1xuXHRcdGxldCBzdWJqZWN0QXJnOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkO1xuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsZWUpICYmIGlzVXRpbHNPd25lcihjYWxsZWUuZXhwcmVzc2lvbikgJiZcblx0XHRcdChjYWxsZWUubmFtZS50ZXh0ID09PSAnbWVyZ2UnIHx8IGNhbGxlZS5uYW1lLnRleHQgPT09ICdmb3JrJykpIHtcblx0XHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGNhbGwuYXJndW1lbnRzO1xuXHRcdFx0c3ViamVjdEFyZyA9IGZpcnN0QXJnO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNJZGVudGlmaWVyKGNhbGxlZSkpIHtcblx0XHRcdGNvbnN0IGltcG9ydGVkID0gdGhpcy5tbmVtb25pY2FOYW1lZEltcG9ydHMuZ2V0KHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk/LmdldChjYWxsZWUudGV4dCk7XG5cdFx0XHRpZiAoaW1wb3J0ZWQgPT09ICdtZXJnZScgfHwgaW1wb3J0ZWQgPT09ICdmb3JrJykge1xuXHRcdFx0XHRjb25zdCBbIGZpcnN0QXJnIF0gPSBjYWxsLmFyZ3VtZW50cztcblx0XHRcdFx0c3ViamVjdEFyZyA9IGZpcnN0QXJnO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSBpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihjYWxsZWUpICYmIHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxlZS5leHByZXNzaW9uKSAmJlxuXHRcdFx0Y2FsbGVlLmV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnZm9yaycgJiYgaXNVdGlsc093bmVyKGNhbGxlZS5leHByZXNzaW9uLmV4cHJlc3Npb24pKSB7XG5cdFx0XHQvLyB1dGlscy5mb3JrKGluc3RhbmNlKSguLi5hcmdzKSDigJQgdGhlIGN1cnJpZWQgZm9ybVxuXHRcdFx0Y29uc3QgWyBmaXJzdEFyZyBdID0gY2FsbGVlLmFyZ3VtZW50cztcblx0XHRcdHN1YmplY3RBcmcgPSBmaXJzdEFyZztcblx0XHR9XG5cdFx0aWYgKCFzdWJqZWN0QXJnIHx8ICF0cy5pc0lkZW50aWZpZXIoc3ViamVjdEFyZykpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KHN1YmplY3RBcmcudGV4dCk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cblx0LyoqXG5cdFx0KiBQcm9jZXNzIGEgQGRlY29yYXRlKCkgZGVjb3JhdG9yXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NEZWNvcmF0ZURlY29yYXRvciAoXG5cdFx0ZGVjb3JhdG9yOiB0cy5EZWNvcmF0b3IsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRjbGFzc0RlY2xQYXJhbT86IHRzLkNsYXNzRGVjbGFyYXRpb25cblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdGRlY29yYXRvci5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cblx0XHQvLyBHZXQgdGhlIGNsYXNzIGRlY2xhcmF0aW9uIC0gdXNlIHRoZSBwYXNzZWQgY29udGV4dCBpZiBwYXJlbnQgaXMgbm90IHNldFxuXHRcdGNvbnN0IGNsYXNzRGVjbCA9IGRlY29yYXRvci5wYXJlbnQgYXMgdHMuQ2xhc3NEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCB8fCBjbGFzc0RlY2xQYXJhbTtcblx0XHRpZiAoIWNsYXNzRGVjbCB8fCAhY2xhc3NEZWNsLm5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0RlY29yYXRlZCBjbGFzcyBoYXMgbm8gbmFtZScsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgdHlwZU5hbWUgPSBjbGFzc0RlY2wubmFtZS50ZXh0O1xuXHRcdGlmICghdHlwZU5hbWUpIHtcblx0XHRcdHRoaXMuZXJyb3JzLnB1c2goe1xuXHRcdFx0XHRtZXNzYWdlIDogJ0RlY29yYXRlZCBjbGFzcyBoYXMgbm8gbmFtZScsXG5cdFx0XHRcdGZpbGUgICAgOiBzb3VyY2VGaWxlLmZpbGVOYW1lLFxuXHRcdFx0XHRsaW5lICAgIDogbGluZSArIDEsXG5cdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0fSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUGFyc2UgZGVjb3JhdG9yIGFyZ3VtZW50czogQGRlY29yYXRlKCksIEBkZWNvcmF0ZShQYXJlbnQpLFxuXHRcdC8vIEBkZWNvcmF0ZSh7IC4uLiB9KSwgQGRlY29yYXRlKFBhcmVudCwgeyAuLi4gfSksXG5cdFx0Ly8gQE15Q29sbGVjdGlvbi5kZWNvcmF0ZSgpLCBATXlDb2xsZWN0aW9uLmRlY29yYXRlKHsgLi4uIH0pXG5cdFx0bGV0IHBhcmVudE5vZGU6IFR5cGVOb2RlIHwgdW5kZWZpbmVkO1xuXHRcdGxldCBwYXJlbnRGdWxsUGF0aDogc3RyaW5nIHwgbnVsbCA9IG51bGw7XG5cdFx0bGV0IGNvbGxlY3Rpb25JZDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdGxldCBkZWNvcmF0b3JDb25maWc6IHsgc3RyaWN0Q2hhaW4/OiBib29sZWFuOyBibG9ja0Vycm9ycz86IGJvb2xlYW4gfSA9IHt9O1xuXG5cdFx0aWYgKHRzLmlzQ2FsbEV4cHJlc3Npb24oZGVjb3JhdG9yLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRjb25zdCBjYWxsRXhwciA9IGRlY29yYXRvci5leHByZXNzaW9uO1xuXHRcdFx0Y29uc3QgY2FsbGVlID0gY2FsbEV4cHIuZXhwcmVzc2lvbjtcblxuXHRcdFx0Ly8gQ2hlY2sgZm9yIEBNeUNvbGxlY3Rpb24uZGVjb3JhdGUoKSB3aGVyZSBNeUNvbGxlY3Rpb24gaXMgYSBjdXN0b20gY29sbGVjdGlvbi5cblx0XHRcdC8vIFRoZSBkZWNvcmF0ZWQgY2xhc3MgYmVjb21lcyBhIHJvb3QgdHlwZSBpbiB0aGF0IGNvbGxlY3Rpb24uXG5cdFx0XHRpZiAoXG5cdFx0XHRcdHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGNhbGxlZSkgJiZcblx0XHRcdFx0Y2FsbGVlLm5hbWUudGV4dCA9PT0gJ2RlY29yYXRlJyAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoY2FsbGVlLmV4cHJlc3Npb24pICYmXG5cdFx0XHRcdHRoaXMuY29sbGVjdGlvblZhcmlhYmxlcy5oYXMoY2FsbGVlLmV4cHJlc3Npb24udGV4dClcblx0XHRcdCkge1xuXHRcdFx0XHRjb2xsZWN0aW9uSWQgPSB0aGlzLmNvbGxlY3Rpb25WYXJpYWJsZXMuZ2V0KGNhbGxlZS5leHByZXNzaW9uLnRleHQpO1xuXHRcdFx0XHRpZiAoY2FsbEV4cHIuYXJndW1lbnRzLmxlbmd0aCA9PT0gMSAmJiB0cy5pc09iamVjdExpdGVyYWxFeHByZXNzaW9uKGNhbGxFeHByLmFyZ3VtZW50c1sgMCBdKSkge1xuXHRcdFx0XHRcdGRlY29yYXRvckNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGNhbGxFeHByLmFyZ3VtZW50c1sgMCBdKTtcblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc3QgYXJncyA9IGNhbGxFeHByLmFyZ3VtZW50cztcblx0XHRcdFx0bGV0IHBhcmVudEFyZzogdHMuSWRlbnRpZmllciB8IHVuZGVmaW5lZDtcblx0XHRcdFx0bGV0IGNvbmZpZ0FyZzogdHMuT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24gfCB1bmRlZmluZWQ7XG5cblx0XHRcdFx0Zm9yIChjb25zdCBhcmcgb2YgYXJncykge1xuXHRcdFx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0XHRcdFx0aWYgKHBhcmVudEFyZykge1xuXHRcdFx0XHRcdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0XHRcdFx0XHRtZXNzYWdlIDogJ0BkZWNvcmF0ZSgpIGFjY2VwdHMgb25seSBvbmUgcGFyZW50IHJlZmVyZW5jZScsXG5cdFx0XHRcdFx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRcdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHRcdHBhcmVudEFyZyA9IGFyZztcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9IGVsc2UgaWYgKHRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0XHRcdFx0aWYgKGNvbmZpZ0FyZykge1xuXHRcdFx0XHRcdFx0XHR0aGlzLmVycm9ycy5wdXNoKHtcblx0XHRcdFx0XHRcdFx0XHRtZXNzYWdlIDogJ0BkZWNvcmF0ZSgpIGFjY2VwdHMgb25seSBvbmUgY29uZmlnIG9iamVjdCcsXG5cdFx0XHRcdFx0XHRcdFx0ZmlsZSAgICA6IHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0bGluZSAgICA6IGxpbmUgKyAxLFxuXHRcdFx0XHRcdFx0XHRcdGNvbHVtbiAgOiBjaGFyYWN0ZXIgKyAxLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHRcdGNvbmZpZ0FyZyA9IGFyZztcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRpZiAocGFyZW50QXJnKSB7XG5cdFx0XHRcdFx0cGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeUlkZW50aWZpZXIocGFyZW50QXJnLnRleHQpO1xuXHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHRwYXJlbnRGdWxsUGF0aCA9IHBhcmVudE5vZGUuZnVsbFBhdGg7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0aWYgKGNvbmZpZ0FyZykge1xuXHRcdFx0XHRcdGRlY29yYXRvckNvbmZpZyA9IHRoaXMuZXh0cmFjdENvbmZpZ0Zyb21PYmplY3RMaXRlcmFsKGNvbmZpZ0FyZyk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBCdWlsZCBmdWxsIHBhdGhcblx0XHRjb25zdCBmdWxsUGF0aCA9IHBhcmVudE5vZGUgPyBgJHtwYXJlbnROb2RlLmZ1bGxQYXRofS4ke3R5cGVOYW1lfWAgOiB0eXBlTmFtZTtcblxuXHRcdC8vIENyZWF0ZSBkZWZpbml0aW9uIGluZm8gZm9yIGRlY29yYXRlXG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IHR5cGVOYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlY29yYXRlJyxcblx0XHRcdHBhcmVudCAgICAgIDogcGFyZW50RnVsbFBhdGgsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IGRlY29yYXRvckNvbmZpZy5zdHJpY3RDaGFpbiA/PyB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBkZWNvcmF0b3JDb25maWcuYmxvY2tFcnJvcnMgPz8gZmFsc2UsXG5cdFx0fTtcblx0XHR0aGlzLmRlZmluaXRpb25zLnNldChmdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdFx0dGhpcy5lZHNTY29wZUJ5Tm9kZS5zZXQoY2xhc3NEZWNsLCBmdWxsUGF0aCk7XG5cblx0XHQvLyBDcmVhdGUgdHlwZSBub2RlXG5cdFx0Y29uc3Qgbm9kZSA9IFR5cGVHcmFwaEltcGwuY3JlYXRlTm9kZShcblx0XHRcdHR5cGVOYW1lLFxuXHRcdFx0cGFyZW50Tm9kZSxcblx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUsXG5cdFx0XHRsaW5lICsgMSxcblx0XHRcdGNoYXJhY3RlciArIDEsXG5cdFx0XHRjb2xsZWN0aW9uSWRcblx0XHQpO1xuXHRcdG5vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lID0gdGhpcy5nZXRSZWdpc3RyeUludGVyZmFjZU5hbWUobm9kZS5jb2xsZWN0aW9uSWQpO1xuXG5cdFx0Ly8gU2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlIGRldGVjdGlvbiAoaGFyZC1mYWlsIGxhdylcblx0XHR0aGlzLnJlY29yZERlZmluZVNpdGUoXG5cdFx0XHRwYXJlbnROb2RlID8gYCR7cGFyZW50Tm9kZS5mdWxsUGF0aH0uJHt0eXBlTmFtZX1gIDogYCR7Y29sbGVjdGlvbklkID8/ICdkZWZhdWx0J306OiR7dHlwZU5hbWV9YCxcblx0XHRcdGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gXG5cdFx0KTtcblxuXHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBhbmQgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGNsYXNzIG1lbWJlcnMg4oCUXG5cdFx0Ly8gdGhlIG5ldyBub2RlIGFuY2hvcnMgcmVsYXRpdmUtZmlyc3QgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb25cblx0XHRjb25zdCBwcmV2aW91c0FuY2hvciA9IHRoaXMuY3VycmVudEdyYXBoQW5jaG9yO1xuXHRcdHRoaXMuY3VycmVudEdyYXBoQW5jaG9yID0gbm9kZTtcblx0XHR0cnkge1xuXHRcdFx0bm9kZS5wcm9wZXJ0aWVzID0gdGhpcy5leHRyYWN0Q2xhc3NQcm9wZXJ0aWVzKGNsYXNzRGVjbCk7XG5cdFx0XHRub2RlLmNvbnN0cnVjdG9yUGFyYW1zID0gdGhpcy5leHRyYWN0Q2xhc3NDb25zdHJ1Y3RvclBhcmFtcyhjbGFzc0RlY2wpO1xuXHRcdH0gZmluYWxseSB7XG5cdFx0XHR0aGlzLmN1cnJlbnRHcmFwaEFuY2hvciA9IHByZXZpb3VzQW5jaG9yO1xuXHRcdH1cblxuXHRcdC8vIEFkZCB0byBncmFwaFxuXHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZENoaWxkKHBhcmVudE5vZGUsIG5vZGUpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHR0aGlzLmdyYXBoLmFkZFJvb3Qobm9kZSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgdHlwZSBuYW1lIGZyb20gZGVmaW5lKCkgY2FsbCBhcmd1bWVudHMuXG5cdCAqIEhhbmRsZXM6XG5cdCAqICAgZGVmaW5lKCdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdCAqICAgZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcikgICAvLyBleHBsaWNpdC1zb3VyY2UgZm9ybVxuXHQgKiAgIGRlZmluZShmdW5jdGlvbiBUeXBlTmFtZSgpIHt9KVxuXHQgKiAgIGRlZmluZSgoKSA9PiBjbGFzcyBUeXBlTmFtZSB7fSlcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdFR5cGVOYW1lIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgYXJncyA9IGNhbGwuYXJndW1lbnRzO1xuXG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGFyZ3M7XG5cblx0XHQvLyBFeHBsaWNpdC1zb3VyY2UgZm9ybTogZGVmaW5lKHNvdXJjZSwgJ1R5cGVOYW1lJywgaGFuZGxlcilcblx0XHRpZiAoYXJncy5sZW5ndGggPj0gMiAmJiB0cy5pc0lkZW50aWZpZXIoZmlyc3RBcmcpICYmIHRzLmlzU3RyaW5nTGl0ZXJhbChhcmdzWyAxIF0pKSB7XG5cdFx0XHRyZXR1cm4gYXJnc1sgMSBdLnRleHQ7XG5cdFx0fVxuXG5cdFx0Ly8gU3RyaW5nIGxpdGVyYWw6IGRlZmluZSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzU3RyaW5nTGl0ZXJhbChmaXJzdEFyZykpIHtcblx0XHRcdHJldHVybiBmaXJzdEFyZy50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIEZ1bmN0aW9uIHdpdGggbmFtZTogZGVmaW5lKGZ1bmN0aW9uIFR5cGVOYW1lKCkge30pXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGZpcnN0QXJnKSAmJiBmaXJzdEFyZy5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gZmlyc3RBcmcubmFtZS50ZXh0O1xuXHRcdH1cblxuXHRcdC8vIEFycm93IGZ1bmN0aW9uIHJldHVybmluZyBjbGFzczogZGVmaW5lKCgpID0+IGNsYXNzIFR5cGVOYW1lIHt9KVxuXHRcdGlmICh0cy5pc0Fycm93RnVuY3Rpb24oZmlyc3RBcmcpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGZpcnN0QXJnO1xuXHRcdFx0aWYgKHRzLmlzQ2xhc3NFeHByZXNzaW9uKGJvZHkpICYmIGJvZHkubmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gYm9keS5uYW1lLnRleHQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHRoZSBmdWxsIGRlZmluZSgpIGNhbGwgY29udGV4dDogdHlwZSBuYW1lLCBwYXJlbnQgdHlwZSwgYW5kIGNvbGxlY3Rpb24uXG5cdCAqIEhhbmRsZXMgZGlyZWN0IGNhbGxzLCBwcm9wZXJ0eS1hY2Nlc3MgY2FsbHMsIGNoYWluZWQgY2FsbHMsIGFuZCB0aGVcblx0ICogZXhwbGljaXQtc291cmNlIGZvcm0gYGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpYC5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdERlZmluZUNvbnRleHQgKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKToge1xuXHRcdHR5cGVOYW1lPzogc3RyaW5nO1xuXHRcdHBhcmVudFR5cGU/OiBUeXBlTm9kZTtcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmc7XG5cdH0ge1xuXHRcdGNvbnN0IHR5cGVOYW1lID0gdGhpcy5leHRyYWN0VHlwZU5hbWUoY2FsbCk7XG5cdFx0aWYgKCF0eXBlTmFtZSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gY2FsbDtcblxuXHRcdC8vIERpcmVjdCBjYWxsOiBkZWZpbmUoJ1R5cGVOYW1lJywgLi4uKSBvciBkZWZpbmUoc291cmNlLCAnVHlwZU5hbWUnLCBoYW5kbGVyKVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikgJiYgZXhwcmVzc2lvbi50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0Ly8gRXhwbGljaXQtc291cmNlIGZvcm06IGRlZmluZShzb3VyY2UsICdUeXBlTmFtZScsIGhhbmRsZXIpXG5cdFx0XHRpZiAoY2FsbC5hcmd1bWVudHMubGVuZ3RoID49IDIgJiYgdHMuaXNJZGVudGlmaWVyKGNhbGwuYXJndW1lbnRzWyAwIF0pKSB7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZU5hbWUgPSBjYWxsLmFyZ3VtZW50c1sgMCBdLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHNvdXJjZUNvbnRleHQgPSB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uoc291cmNlTmFtZSk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBQbGFpbiByb290IGRlZmluZSBpbiBkZWZhdWx0IGNvbGxlY3Rpb25cblx0XHRcdHJldHVybiB7IHR5cGVOYW1lIH07XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiBYLmRlZmluZSgnVHlwZU5hbWUnLCAuLi4pXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHJlc3Npb24pICYmIGV4cHJlc3Npb24ubmFtZS50ZXh0ID09PSAnZGVmaW5lJykge1xuXHRcdFx0Y29uc3Qgb2JqID0gZXhwcmVzc2lvbi5leHByZXNzaW9uO1xuXG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKG9iaikpIHtcblx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShvYmoudGV4dCk7XG5cdFx0XHRcdHJldHVybiB7XG5cdFx0XHRcdFx0dHlwZU5hbWUsXG5cdFx0XHRcdFx0cGFyZW50VHlwZSAgIDogc291cmNlQ29udGV4dC5wYXJlbnRUeXBlLFxuXHRcdFx0XHRcdGNvbGxlY3Rpb25JZCA6IHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkLFxuXHRcdFx0XHR9O1xuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24ob2JqKSkge1xuXHRcdFx0XHQvLyBOZXN0ZWQgYWNjZXNzOiBpbnN0YW5jZS5UeXBlLmRlZmluZSAtIHRyeSB0byByZXNvbHZlXG5cdFx0XHRcdGNvbnN0IGNoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUNoYWluKG9iaik7XG5cdFx0XHRcdGlmIChjaGFpbi5sZW5ndGggPiAwKSB7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUoY2hhaW4uam9pbignLicpKTtcblx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUgfTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihvYmopKSB7XG5cdFx0XHRcdC8vIERldGVybWluZSB0aGUgY29sbGVjdGlvbiBjb250ZXh0IGZyb20gdGhlIHJvb3Qgb2YgdGhlIGNoYWluIHNvIHRoYXRcblx0XHRcdFx0Ly8gY3VzdG9tLWNvbGxlY3Rpb24gdHlwZXMgZG8gbm90IGdldCBjb25mdXNlZCB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcy5cblx0XHRcdFx0Y29uc3Qgcm9vdElkID0gdGhpcy5nZXRSb290SWRlbnRpZmllcihvYmouZXhwcmVzc2lvbik7XG5cdFx0XHRcdGNvbnN0IGV4cGVjdGVkQ29sbGVjdGlvbklkID0gcm9vdElkXG5cdFx0XHRcdFx0PyB0aGlzLnJlc29sdmVEZWZpbmVTb3VyY2Uocm9vdElkLnRleHQpLmNvbGxlY3Rpb25JZFxuXHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXG5cdFx0XHRcdC8vIENoYWluZWQgY2FsbDogZGVmaW5lKCdBJykuZGVmaW5lKCdCJykgb3IgbW5lbW9uaWNhLmRlZmluZSgnQScpLmRlZmluZSgnQicpXG5cdFx0XHRcdGlmICh0aGlzLmlzRGVmaW5lQ2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzRGVmaW5lQ2FsbChvYmosIGNhbGwuZ2V0U291cmNlRmlsZSgpKTtcblx0XHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlTmFtZSA9IHRoaXMuZXh0cmFjdFR5cGVOYW1lKG9iaik7XG5cdFx0XHRcdFx0aWYgKHBhcmVudFR5cGVOYW1lKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShwYXJlbnRUeXBlTmFtZSwgZXhwZWN0ZWRDb2xsZWN0aW9uSWQpO1xuXHRcdFx0XHRcdFx0Ly8gSW5oZXJpdCBjb2xsZWN0aW9uIGZyb20gdGhlIHBhcmVudCB0eXBlIChpZiBhbnkpXG5cdFx0XHRcdFx0XHRyZXR1cm4geyB0eXBlTmFtZSwgcGFyZW50VHlwZSA6IHBhcmVudE5vZGUsIGNvbGxlY3Rpb25JZCA6IHBhcmVudE5vZGU/LmNvbGxlY3Rpb25JZCB9O1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIENoYWluZWQgbGF6eSBjYWxsOiBsYXp5KCdBJykuZGVmaW5lKCdCJykgb3IgVHlwZS5sYXp5KCdBJykuZGVmaW5lKCdCJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMYXp5Q2FsbChvYmopKSB7XG5cdFx0XHRcdFx0dGhpcy5wcm9jZXNzTGF6eUNhbGwob2JqLCBjYWxsLmdldFNvdXJjZUZpbGUoKSk7XG5cdFx0XHRcdFx0Y29uc3QgcGFyZW50VHlwZU5hbWUgPSB0aGlzLmV4dHJhY3RNbmVtb25pY2FUeXBlTmFtZShvYmopO1xuXHRcdFx0XHRcdGlmIChwYXJlbnRUeXBlTmFtZSkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZmluZFBhcmVudFR5cGVCeU5hbWUocGFyZW50VHlwZU5hbWUsIGV4cGVjdGVkQ29sbGVjdGlvbklkKTtcblx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZT8uY29sbGVjdGlvbklkIH07XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Ly8gQnVpbGRlciBsb29rdXAgY2hhaW46IEFwcC5sb29rdXAoJ1VzZXInKS5kZWZpbmUoJ0FkbWluJylcblx0XHRcdFx0aWYgKHRoaXMuaXNMb29rdXBDYWxsKG9iaikpIHtcblx0XHRcdFx0XHRjb25zdCBsb29rZWRVcFBhdGggPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKG9iaik7XG5cdFx0XHRcdFx0aWYgKGxvb2tlZFVwUGF0aCkge1xuXHRcdFx0XHRcdFx0Y29uc3QgcGFyZW50Tm9kZSA9IHRoaXMuZ3JhcGguZmluZFR5cGUobG9va2VkVXBQYXRoKTtcblx0XHRcdFx0XHRcdGlmIChwYXJlbnROb2RlKSB7XG5cdFx0XHRcdFx0XHRcdHJldHVybiB7IHR5cGVOYW1lLCBwYXJlbnRUeXBlIDogcGFyZW50Tm9kZSwgY29sbGVjdGlvbklkIDogcGFyZW50Tm9kZS5jb2xsZWN0aW9uSWQgfTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4geyB0eXBlTmFtZSB9O1xuXHR9XG5cblx0LyoqXG5cdCAqIFByZWZpeCBhIGRvdHRlZCB0eXBlIHBhdGggd2l0aCBhIGNvbGxlY3Rpb24gaWRlbnRpZmllciBzbyBjdXN0b20tY29sbGVjdGlvblxuXHQgKiB0eXBlcyBkbyBub3QgY29sbGlkZSB3aXRoIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcyBpbiB0aGUgZ3JhcGguXG5cdCAqL1xuXHRwcml2YXRlIHByZWZpeENvbGxlY3Rpb25QYXRoIChwYXRoOiBzdHJpbmcsIGNvbGxlY3Rpb25JZDogc3RyaW5nKTogc3RyaW5nIHtcblx0XHRyZXR1cm4gYCR7Y29sbGVjdGlvbklkfTo6JHtwYXRofWA7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGRlZmluZSgpIHNvdXJjZSBpZGVudGlmaWVyIHRvIGVpdGhlciBhIHBhcmVudCB0eXBlLCBhIGNvbGxlY3Rpb24sXG5cdCAqIG9yIHRoZSBkZWZhdWx0IChtb2R1bGUgb2JqZWN0KSBjb2xsZWN0aW9uLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRGVmaW5lU291cmNlIChzb3VyY2VOYW1lOiBzdHJpbmcpOiB7XG5cdFx0cGFyZW50VHlwZT86IFR5cGVOb2RlO1xuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZztcblx0fSB7XG5cdFx0Ly8gTW9kdWxlIG9iamVjdCBhbGlhc2VzIC0+IHJvb3QgaW4gZGVmYXVsdCBjb2xsZWN0aW9uXG5cdFx0aWYgKHRoaXMubW9kdWxlT2JqZWN0VmFyaWFibGVzLmhhcyhzb3VyY2VOYW1lKSkge1xuXHRcdFx0cmV0dXJuIHt9O1xuXHRcdH1cblxuXHRcdC8vIENvbGxlY3Rpb24gdmFyaWFibGVzIC0+IHJvb3QgaW4gdGhhdCBjb2xsZWN0aW9uXG5cdFx0Y29uc3QgY29sbGVjdGlvbklkID0gdGhpcy5jb2xsZWN0aW9uVmFyaWFibGVzLmdldChzb3VyY2VOYW1lKTtcblx0XHRpZiAoY29sbGVjdGlvbklkKSB7XG5cdFx0XHRyZXR1cm4geyBjb2xsZWN0aW9uSWQgfTtcblx0XHR9XG5cblx0XHQvLyBPdGhlcndpc2UgdHJlYXQgYXMgYSB0eXBlIHZhcmlhYmxlIHJlZmVyZW5jZVxuXHRcdGNvbnN0IHBhcmVudE5vZGUgPSB0aGlzLmZpbmRQYXJlbnRUeXBlQnlJZGVudGlmaWVyKHNvdXJjZU5hbWUpO1xuXHRcdHJldHVybiB7IHBhcmVudFR5cGUgOiBwYXJlbnROb2RlLCBjb2xsZWN0aW9uSWQgOiBwYXJlbnROb2RlPy5jb2xsZWN0aW9uSWQgfTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGVjayBpZiBhIGNhbGwgZXhwcmVzc2lvbiBpcyBhIGxvb2t1cCgpIGNhbGwuXG5cdCAqL1xuXHRwcml2YXRlIGlzTG9va3VwQ2FsbCAobm9kZTogdHMuQ2FsbEV4cHJlc3Npb24pOiBib29sZWFuIHtcblx0XHRjb25zdCBleHByID0gbm9kZS5leHByZXNzaW9uO1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikgJiYgZXhwci50ZXh0ID09PSAnbG9va3VwJykge1xuXHRcdFx0cmV0dXJuIHRydWU7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSAmJiBleHByLm5hbWUudGV4dCA9PT0gJ2xvb2t1cCcpIHtcblx0XHRcdHJldHVybiB0cnVlO1xuXHRcdH1cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGxvb2t1cCgpIGNhbGwgdG8gYSBkb3R0ZWQgdHlwZSBwYXRoIChiZXN0IGVmZm9ydCkuXG5cdCAqIEhhbmRsZXM6XG5cdCAqICAgbG9va3VwKCdVc2VyJylcblx0ICogICBsb29rdXAoc291cmNlLCAnVXNlcicpXG5cdCAqICAgQXBwLmxvb2t1cCgnVXNlcicpXG5cdCAqICAgY29sbGVjdGlvbi5sb29rdXAoJ1VzZXIuQWRtaW4nKVxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlTG9va3VwUGF0aCAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGFyZ3MgPSBjYWxsLmFyZ3VtZW50cztcblx0XHRpZiAoYXJncy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gU2luZ2xlLWFyZyBsb29rdXA6IGxvb2t1cCgnVXNlcicpIG9yIEFwcC5sb29rdXAoJ1VzZXInKVxuXHRcdGlmIChhcmdzLmxlbmd0aCA9PT0gMSkge1xuXHRcdFx0Y29uc3QgWyBhcmcgXSA9IGFyZ3M7XG5cdFx0XHRpZiAodHMuaXNTdHJpbmdMaXRlcmFsKGFyZykgfHwgdHMuaXNOb1N1YnN0aXR1dGlvblRlbXBsYXRlTGl0ZXJhbChhcmcpKSB7XG5cdFx0XHRcdGNvbnN0IHBhdGggPSBhcmcudGV4dDtcblx0XHRcdFx0Ly8gSWYgdGhpcyBpcyBhIG1ldGhvZCBjYWxsIG9uIGEgc291cmNlLCByZXNvbHZlIHJlbGF0aXZlIHRvIHRoYXQgc291cmNlLlxuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbC5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdGNvbnN0IHNvdXJjZUV4cHIgPSBjYWxsLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKHNvdXJjZUV4cHIpKSB7XG5cdFx0XHRcdFx0XHRjb25zdCBzb3VyY2VOYW1lID0gc291cmNlRXhwci50ZXh0O1xuXHRcdFx0XHRcdFx0Y29uc3Qgc291cmNlQ29udGV4dCA9IHRoaXMucmVzb2x2ZURlZmluZVNvdXJjZShzb3VyY2VOYW1lKTtcblx0XHRcdFx0XHRcdGlmIChzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCkge1xuXHRcdFx0XHRcdFx0XHQvLyBDb2xsZWN0aW9uIGxvb2t1cDogcHJlZml4IHBhdGggd2l0aCB0aGUgY29sbGVjdGlvbiBpZFxuXHRcdFx0XHRcdFx0XHRyZXR1cm4gdGhpcy5wcmVmaXhDb2xsZWN0aW9uUGF0aChwYXRoLCBzb3VyY2VDb250ZXh0LmNvbGxlY3Rpb25JZCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRpZiAoc291cmNlQ29udGV4dC5wYXJlbnRUeXBlKSB7XG5cdFx0XHRcdFx0XHRcdC8vIFR5cGUgbG9va3VwOiByZWxhdGl2ZSBmaXJzdCwgdGhlbiByb290IGZhbGxiYWNrXG5cdFx0XHRcdFx0XHRcdGNvbnN0IHJlbGF0aXZlUGF0aCA9IGAke3NvdXJjZUNvbnRleHQucGFyZW50VHlwZS5mdWxsUGF0aH0uJHtwYXRofWA7XG5cdFx0XHRcdFx0XHRcdGlmICh0aGlzLmdyYXBoLmZpbmRUeXBlKHJlbGF0aXZlUGF0aCkpIHtcblx0XHRcdFx0XHRcdFx0XHRyZXR1cm4gcmVsYXRpdmVQYXRoO1xuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRcdHJldHVybiBwYXRoO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gcGF0aDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gVHdvLWFyZyBsb29rdXA6IGxvb2t1cChzb3VyY2UsICdVc2VyJylcblx0XHRpZiAoYXJncy5sZW5ndGggPj0gMikge1xuXHRcdFx0Y29uc3QgWyBzb3VyY2VBcmcsIHBhdGhBcmcgXSA9IGFyZ3M7XG5cdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihzb3VyY2VBcmcpIHx8ICF0cy5pc1N0cmluZ0xpdGVyYWwocGF0aEFyZykpIHtcblx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHNvdXJjZU5hbWUgPSBzb3VyY2VBcmcudGV4dDtcblx0XHRcdGNvbnN0IHBhdGggPSBwYXRoQXJnLnRleHQ7XG5cdFx0XHRjb25zdCBzb3VyY2VDb250ZXh0ID0gdGhpcy5yZXNvbHZlRGVmaW5lU291cmNlKHNvdXJjZU5hbWUpO1xuXHRcdFx0aWYgKHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKSB7XG5cdFx0XHRcdHJldHVybiB0aGlzLnByZWZpeENvbGxlY3Rpb25QYXRoKHBhdGgsIHNvdXJjZUNvbnRleHQuY29sbGVjdGlvbklkKTtcblx0XHRcdH1cblx0XHRcdGlmIChzb3VyY2VDb250ZXh0LnBhcmVudFR5cGUpIHtcblx0XHRcdFx0Y29uc3QgcmVsYXRpdmVQYXRoID0gYCR7c291cmNlQ29udGV4dC5wYXJlbnRUeXBlLmZ1bGxQYXRofS4ke3BhdGh9YDtcblx0XHRcdFx0aWYgKHRoaXMuZ3JhcGguZmluZFR5cGUocmVsYXRpdmVQYXRoKSkge1xuXHRcdFx0XHRcdHJldHVybiByZWxhdGl2ZVBhdGg7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHBhdGg7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gcGF0aDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdCAqIExvb2t1cC1sYXcgZGVsZWdhdGUgZm9yIHRoZSBsb2NhbC1zY29wZSB3YWxrZXIgKHNjb3Blcy5qc29uIHR5cGVQYXRoXG5cdCAqIG1ldGFkYXRhKTogcmVzb2x2ZSBhIGxvb2t1cCgpIGluaXRpYWxpemVyIGNhbGwgdGhyb3VnaCBleGFjdGx5IHRoZVxuXHQgKiB0aWVycyB0aGUgdXNhZ2VzIHBhc3MgcmVzb2x2ZWQgaXQgYWdhaW5zdCAoc2FtZSBzb3VyY2UgcmVzb2x1dGlvbixcblx0ICogc2FtZSBjb21wbGV0ZSBncmFwaCkuIFRoZSB3YWxrZXIgcnVucyBpdHMgb3duIHNjb3BlLWNoYWluIHZhbHVlLXNjb3BlXG5cdCAqIHRpZXIgYmVmb3JlIGRlbGVnYXRpbmc7IGV2ZXJ5dGhpbmcgYWJvdmUgdmFsdWUgc2NvcGUgbGFuZHMgaGVyZSwgc29cblx0ICogc2NvcGVzLmpzb24gbmV2ZXIgZGlzYWdyZWVzIHdpdGggdGhlIGhhcmQtZmFpbC1sYXcgdmVyZGljdHMuXG5cdCAqL1xuXHRyZXNvbHZlTG9va3VwQ2FsbFBhdGggKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLnJlc29sdmVMb29rdXBQYXRoKGNhbGwpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHQqIEZpbmQgYSBwYXJlbnQgdHlwZSBieSBpdHMgbmFtZSwgc2VhcmNoaW5nIGluIHRoZSBncmFwaC5cblx0XHQqIFdoZW4gY29sbGVjdGlvbklkIGlzIHByb3ZpZGVkLCBvbmx5IHR5cGVzIGZyb20gdGhhdCBjb2xsZWN0aW9uIGFyZSBjb25zaWRlcmVkLlxuXHRcdCovXG5cdHByaXZhdGUgZmluZFBhcmVudFR5cGVCeU5hbWUgKFxuXHRcdG5hbWU6IHN0cmluZyxcblx0XHRjb2xsZWN0aW9uSWQ/OiBzdHJpbmdcblx0KTogVHlwZU5vZGUgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IG1hdGNoZXNDb2xsZWN0aW9uID0gKHR5cGU6IFR5cGVOb2RlKTogYm9vbGVhbiA9PiB7XG5cdFx0XHRpZiAoY29sbGVjdGlvbklkID09PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0cmV0dXJuIHR5cGUuY29sbGVjdGlvbklkID09PSB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdHlwZS5jb2xsZWN0aW9uSWQgPT09IGNvbGxlY3Rpb25JZDtcblx0XHR9O1xuXG5cdFx0Ly8gRmlyc3QgdHJ5IGV4YWN0IG1hdGNoIChkZWZhdWx0LWNvbGxlY3Rpb24gdHlwZXMgdXNlIHRoZSBwbGFpbiBkb3R0ZWQgcGF0aClcblx0XHRjb25zdCBleGFjdCA9IHRoaXMuZ3JhcGguZmluZFR5cGUobmFtZSk7XG5cdFx0aWYgKGV4YWN0ICYmIG1hdGNoZXNDb2xsZWN0aW9uKGV4YWN0KSkge1xuXHRcdFx0cmV0dXJuIGV4YWN0O1xuXHRcdH1cblxuXHRcdC8vIFRoZW4gc2VhcmNoIHRocm91Z2ggYWxsIHR5cGVzIGZvciBvbmUgd2l0aCBtYXRjaGluZyBuYW1lIGFuZCBjb2xsZWN0aW9uXG5cdFx0Zm9yIChjb25zdCB0eXBlIG9mIHRoaXMuZ3JhcGguZ2V0QWxsVHlwZXMoKSkge1xuXHRcdFx0aWYgKHR5cGUubmFtZSA9PT0gbmFtZSAmJiBtYXRjaGVzQ29sbGVjdGlvbih0eXBlKSkge1xuXHRcdFx0XHRyZXR1cm4gdHlwZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBGaW5kIGEgcGFyZW50IHR5cGUgZnJvbSBhbiBpZGVudGlmaWVyIHJlZmVyZW5jZS5cblx0XHQqIEhhbmRsZXMgYm90aCBhbGlhc2VkIHZhcmlhYmxlcyAoY29uc3QgVXNlciA9IGRlZmluZSgnVXNlckVudGl0eScsIC4uLikpXG5cdFx0KiBhbmQgZGlyZWN0IGNsYXNzL3R5cGUgbmFtZXMuXG5cdFx0Ki9cblx0cHJpdmF0ZSBmaW5kUGFyZW50VHlwZUJ5SWRlbnRpZmllciAobmFtZTogc3RyaW5nKTogVHlwZU5vZGUgfCB1bmRlZmluZWQge1xuXHRcdC8vIEZpcnN0IGNoZWNrIHZhcmlhYmxlIG1hcHBpbmc6IGNvbnN0IFVzZXIgPSBkZWZpbmUoJ1VzZXJFbnRpdHknLCAuLi4pXG5cdFx0Y29uc3QgbWFwcGVkRnVsbFBhdGggPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChuYW1lKTtcblx0XHRpZiAobWFwcGVkRnVsbFBhdGgpIHtcblx0XHRcdGNvbnN0IG1hcHBlZE5vZGUgPSB0aGlzLmdyYXBoLmZpbmRUeXBlKG1hcHBlZEZ1bGxQYXRoKTtcblx0XHRcdGlmIChtYXBwZWROb2RlKSByZXR1cm4gbWFwcGVkTm9kZTtcblx0XHR9XG5cblx0XHRjb25zdCBwYXJlbnROb2RlID0gdGhpcy5maW5kUGFyZW50VHlwZUJ5TmFtZShuYW1lKTtcblx0XHRyZXR1cm4gcGFyZW50Tm9kZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgdGhlIGxlZnRtb3N0IGlkZW50aWZpZXIgb2YgYSBwcm9wZXJ0eS1hY2Nlc3MgY2hhaW4uXG5cdCAqIEZvciBgQXBwLmRlZmluZSgnVXNlcicpLmRlZmluZSgnQWRtaW4nKWAgdGhpcyByZXR1cm5zIHRoZSBgQXBwYCBpZGVudGlmaWVyLlxuXHQgKi9cblx0cHJpdmF0ZSBnZXRSb290SWRlbnRpZmllciAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHRzLklkZW50aWZpZXIgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5FeHByZXNzaW9uID0gZXhwcjtcblx0XHR3aGlsZSAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY3VycmVudCkpIHtcblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0fVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY3VycmVudCkpIHtcblx0XHRcdHJldHVybiBjdXJyZW50O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBHZXQgcHJvcGVydHkgY2hhaW4gZnJvbSBuZXN0ZWQgYWNjZXNzXG5cdFx0Ki9cblx0cHJpdmF0ZSBnZXRQcm9wZXJ0eUNoYWluIChleHByOiB0cy5Qcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24gfCB0cy5JZGVudGlmaWVyKTogc3RyaW5nW10ge1xuXHRcdGNvbnN0IGNoYWluOiBzdHJpbmdbXSA9IFtdO1xuXG5cdFx0bGV0IGN1cnJlbnQ6IHRzLkV4cHJlc3Npb24gPSBleHByO1xuXHRcdHdoaWxlICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjdXJyZW50KSkge1xuXHRcdFx0aWYgKGN1cnJlbnQubmFtZSkge1xuXHRcdFx0XHRjaGFpbi51bnNoaWZ0KGN1cnJlbnQubmFtZS50ZXh0KTtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LmV4cHJlc3Npb247XG5cdFx0fVxuXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihjdXJyZW50KSkge1xuXHRcdFx0Y2hhaW4udW5zaGlmdChjdXJyZW50LnRleHQpO1xuXHRcdH1cblxuXHRcdHJldHVybiBjaGFpbjtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlcm1pbmUgdGhlIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24gZm9yIGVpdGhlciBhIGRlZmluZSgpIG9yIGxhenkoKSBjYWxsLlxuXHQgKiBGb3IgZGVmaW5lKCkgdGhpcyBpcyB0aGUgY29uc3RydWN0IGhhbmRsZXI7IGZvciBsYXp5KCkgaXQgaXMgdGhlIHZhbHVlXG5cdCAqIHJldHVybmVkIGJ5IHRoZSBsYXp5IGdldHRlci5cblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENvbnN0cnVjdG9yRXhwcmVzc2lvbiAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBleHByID0gY2FsbC5leHByZXNzaW9uO1xuXHRcdGNvbnN0IG5hbWUgPSB0cy5pc0lkZW50aWZpZXIoZXhwcilcblx0XHRcdD8gZXhwci50ZXh0XG5cdFx0XHQ6IHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpXG5cdFx0XHRcdD8gZXhwci5uYW1lLnRleHRcblx0XHRcdFx0OiAnJztcblxuXHRcdGlmIChuYW1lID09PSAnbGF6eScpIHtcblx0XHRcdGNvbnN0IGxhenlBcmdzID0gdGhpcy5leHRyYWN0TGF6eUNhbGxBcmdzKGNhbGwpO1xuXHRcdFx0aWYgKCFsYXp5QXJncykge1xuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIHRoaXMudW53cmFwTGF6eUdldHRlcihsYXp5QXJncy5nZXR0ZXIpO1xuXHRcdH1cblxuXHRcdC8vIGRlZmluZSgpIGNhbGxcblx0XHRjb25zdCBhcmdzID0gY2FsbC5hcmd1bWVudHM7XG5cdFx0aWYgKGFyZ3MubGVuZ3RoID09PSAwKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdC8vIE1vZGVybiBmb3JtOiBkZWZpbmUoJ05hbWUnLCBoYW5kbGVyLCBjb25maWc/KVxuXHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwoYXJnc1sgMCBdKSkge1xuXHRcdFx0cmV0dXJuIGFyZ3NbIDEgXTtcblx0XHR9XG5cblx0XHQvLyBMZWdhY3kgZm9ybTogZGVmaW5lKGZ1bmN0aW9uIE5hbWUoKSB7fSkgb3IgZGVmaW5lKCgpID0+IGNsYXNzIE5hbWUge30pXG5cdFx0cmV0dXJuIGFyZ3NbIDAgXTtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBjb25zdHJ1Y3RvciBmdW5jdGlvblxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UHJvcGVydGllcyAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+IHtcblx0XHRjb25zdCBjb25zdHJ1Y3RvckV4cHIgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvckV4cHJlc3Npb24oY2FsbCk7XG5cdFx0aWYgKCFjb25zdHJ1Y3RvckV4cHIpIHtcblx0XHRcdHJldHVybiBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLmV4dHJhY3RQcm9wZXJ0aWVzRnJvbUNvbnN0cnVjdG9yKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBhIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24gKGZ1bmN0aW9uLCBhcnJvdywgb3IgY2xhc3MpLlxuXHQgKi9cblx0cHJpdmF0ZSBleHRyYWN0UHJvcGVydGllc0Zyb21Db25zdHJ1Y3RvciAoY29uc3RydWN0b3JFeHByOiB0cy5FeHByZXNzaW9uKTogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPiB7XG5cdFx0Y29uc3QgcHJvcGVydGllcyA9IG5ldyBNYXA8c3RyaW5nLCBQcm9wZXJ0eUluZm8+KCk7XG5cblx0XHQvLyBCdWlsZCB0eXBlIG1hcCBmcm9tIGRhdGEgcGFyYW1ldGVyIChmb3IgdGhpcy54ID0gZGF0YS54IHBhdHRlcm5zKVxuXHRcdGNvbnN0IGRhdGFUeXBlTWFwID0gdGhpcy5idWlsZERhdGFUeXBlTWFwKGNvbnN0cnVjdG9yRXhwcik7XG5cblx0XHQvLyBIYW5kbGUgZnVuY3Rpb24gZXhwcmVzc2lvblxuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpIHx8IHRzLmlzQXJyb3dGdW5jdGlvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHRjb25zdCB7IGJvZHkgfSA9IGNvbnN0cnVjdG9yRXhwcjtcblxuXHRcdFx0Ly8gRmlyc3QsIGV4dHJhY3QgcHJvcGVydGllcyBmcm9tIGB0aGlzYCBwYXJhbWV0ZXIgdHlwZSBhbm5vdGF0aW9uXG5cdFx0XHQvLyBUaGlzIGhhbmRsZXMgcGF0dGVybnMgbGlrZTogZnVuY3Rpb24odGhpczogU29tZVR5cGUsIGRhdGE6IFNvbWVUeXBlKSB7IH1cblx0XHRcdGNvbnN0IHRoaXNQYXJhbVByb3BlcnRpZXMgPSB0aGlzLmV4dHJhY3RUaGlzUGFyYW1Qcm9wZXJ0aWVzKGNvbnN0cnVjdG9yRXhwcik7XG5cdFx0XHRmb3IgKGNvbnN0IFsgbmFtZSwgcHJvcEluZm8gXSBvZiB0aGlzUGFyYW1Qcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHByb3BJbmZvKTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gRnVuY3Rpb24gYm9keSB3aXRoIHN0YXRlbWVudHNcblx0XHRcdGlmICh0cy5pc0Jsb2NrKGJvZHkpKSB7XG5cdFx0XHRcdGZvciAoY29uc3Qgc3RtdCBvZiBib2R5LnN0YXRlbWVudHMpIHtcblx0XHRcdFx0XHRpZiAodHMuaXNFeHByZXNzaW9uU3RhdGVtZW50KHN0bXQpKSB7XG5cdFx0XHRcdFx0XHR0aGlzLmV4dHJhY3RQcm9wZXJ0eUZyb21TdGF0ZW1lbnQoc3RtdC5leHByZXNzaW9uLCBwcm9wZXJ0aWVzLCBkYXRhVHlwZU1hcCk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gSGFuZGxlIGNsYXNzIGV4cHJlc3Npb25cblx0XHRpZiAodHMuaXNDbGFzc0V4cHJlc3Npb24oY29uc3RydWN0b3JFeHByKSkge1xuXHRcdFx0Ly8gRmlyc3QgcGFzczogY29sbGVjdCBhbGwgcHJvcGVydHkgdHlwZXMgZm9yIG1ldGhvZCBpbmZlcmVuY2Vcblx0XHRcdGNvbnN0IGNsYXNzUHJvcGVydHlUeXBlcyA9IHRoaXMuZXh0cmFjdENsYXNzUHJvcGVydHlUeXBlcyhjb25zdHJ1Y3RvckV4cHIpO1xuXG5cdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBjb25zdHJ1Y3RvckV4cHIubWVtYmVycykge1xuXHRcdFx0XHQvLyBIYW5kbGUgcHJvcGVydHkgZGVjbGFyYXRpb25zXG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5RGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSkge1xuXHRcdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIHByb3BlcnRpZXNcblx0XHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4ge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHRcdFx0bS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQ7XG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXG5cdFx0XHRcdFx0Y29uc3QgbmFtZSA9IHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkgPyBtZW1iZXIubmFtZS50ZXh0IDogJyc7XG5cdFx0XHRcdFx0aWYgKG5hbWUpIHtcblx0XHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdFx0dHlwZSAgICAgOiB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSksXG5cdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogISFtZW1iZXIucXVlc3Rpb25Ub2tlbixcblx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdC8vIEhhbmRsZSBtZXRob2QgZGVjbGFyYXRpb25zXG5cdFx0XHRcdGlmICh0cy5pc01ldGhvZERlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIG1ldGhvZHNcblx0XHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4ge1xuXHRcdFx0XHRcdFx0XHRyZXR1cm4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHRcdFx0bS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQ7XG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fVxuXG5cdFx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJNZXRob2RUeXBlKG1lbWJlciwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblxuXHRcdFx0XHQvLyBIYW5kbGUgZ2V0dGVyIGRlY2xhcmF0aW9uc1xuXHRcdFx0XHRpZiAodHMuaXNHZXRBY2Nlc3NvcihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBnZXR0ZXJzXG5cdFx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IHtcblx0XHRcdFx0XHRcdFx0cmV0dXJuIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0XHRcdG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkO1xuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblxuXHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdC8vIEZpcnN0IHRyeSBleHBsaWNpdCB0eXBlIGFubm90YXRpb24sIHRoZW4gaW5mZXIgZnJvbSBnZXR0ZXIgYm9keVxuXHRcdFx0XHRcdGxldCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdGlmICh0eXBlID09PSAndW5rbm93bicgJiYgbWVtYmVyLmJvZHkpIHtcblx0XHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyUmV0dXJuVHlwZUZyb21Cb2R5KG1lbWJlci5ib2R5LCBjbGFzc1Byb3BlcnR5VHlwZXMpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRuYW1lLFxuXHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0XHRyZWFkb25seSA6IHRydWUsXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdC8qKlxuXHQgKiBCdWlsZCBhIHR5cGUgbWFwIGZyb20gYWxsIHBhcmFtZXRlcnMgd2l0aCBpbmxpbmUgb2JqZWN0IHR5cGUgYW5ub3RhdGlvbnNcblx0ICogUmV0dXJucyBhIG1hcCBvZiBcInBhcmFtTmFtZS5wcm9wZXJ0eU5hbWVcIiAtPiB0eXBlXG5cdCAqL1xuXHRwcml2YXRlIGJ1aWxkRGF0YVR5cGVNYXAgKGhhbmRsZXJBcmc6IHRzLkV4cHJlc3Npb24pOiBNYXA8c3RyaW5nLCBzdHJpbmc+IHtcblx0XHRjb25zdCB0eXBlTWFwID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblxuXHRcdGlmICghdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oaGFuZGxlckFyZykgJiYgIXRzLmlzQXJyb3dGdW5jdGlvbihoYW5kbGVyQXJnKSkge1xuXHRcdFx0cmV0dXJuIHR5cGVNYXA7XG5cdFx0fVxuXG5cdFx0Ly8gSXRlcmF0ZSBvdmVyIEFMTCBwYXJhbWV0ZXJzXG5cdFx0Zm9yIChjb25zdCBwYXJhbSBvZiBoYW5kbGVyQXJnLnBhcmFtZXRlcnMpIHtcblx0XHRcdGlmICghcGFyYW0ubmFtZSB8fCAhcGFyYW0udHlwZSkgY29udGludWU7XG5cblx0XHRcdC8vIEdldCBwYXJhbWV0ZXIgbmFtZVxuXHRcdFx0bGV0IHBhcmFtTmFtZSA9ICcnO1xuXHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSkge1xuXHRcdFx0XHRwYXJhbU5hbWUgPSBwYXJhbS5uYW1lLnRleHQ7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHQvLyBTa2lwIGRlc3RydWN0dXJlZCBwYXJhbWV0ZXJzIGZvciBub3dcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cblx0XHRcdC8vIENoZWNrIGlmIGl0J3MgYW4gaW5saW5lIG9iamVjdCB0eXBlIGxpdGVyYWxcblx0XHRcdGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZShwYXJhbS50eXBlKSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IG1lbWJlciBvZiBwYXJhbS50eXBlLm1lbWJlcnMpIHtcblx0XHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0XHR0eXBlTWFwLnNldChgJHtwYXJhbU5hbWV9LiR7cHJvcE5hbWV9YCwgdHlwZSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHQvLyBOYW1lZCB0eXBlIHJlZmVyZW5jZSAoYWxpYXMvaW50ZXJmYWNlL2NsYXNzLCBpbXBvcnRlZCBvclxuXHRcdFx0XHQvLyBsb2NhbCDigJQgRjE0KTogZGVjb21wb3NlIHRoZSByZXNvbHZlZCBkZWNsYXJhdGlvbiBpbnRvXG5cdFx0XHRcdC8vIHBlci1wcm9wZXJ0eSBlbnRyaWVzIHRocm91Z2ggdGhlIHNhbWUgaW1wb3J0LWF3YXJlXG5cdFx0XHRcdC8vIG1hY2hpbmVyeSBhcyBjb25zdHJ1Y3RvciBzaWduYXR1cmVzIChGMTApLCBpbmNsdWRpbmcgdGhlXG5cdFx0XHRcdC8vIGhlcml0YWdlIHdhbGsgKEYxMykuIFdpdGhvdXQgdGhpcywgYHRoaXMueCA9IHBhcmFtLnlgXG5cdFx0XHRcdC8vIHJlYWQgYHVua25vd25gIGZvciBuYW1lZCBwYXJhbXMg4oCUIG9ubHkgaW5saW5lIGxpdGVyYWxzXG5cdFx0XHRcdC8vIHdlcmUgZGVjb21wb3NlZC4gVW5yZXNvbHZhYmxlIOKGkiB3aG9sZS1wYXJhbSBmYWxsYmFja1xuXHRcdFx0XHQvLyBiZWxvdzsgYSBiYXJlIG5hbWUgaXMgbmV2ZXIgZW1pdHRlZCBlaXRoZXIgd2F5XG5cdFx0XHRcdGxldCBuYW1lZERlY2w6IFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24gfCB1bmRlZmluZWQ7XG5cdFx0XHRcdGlmICh0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHBhcmFtLnR5cGUpICYmIHRzLmlzSWRlbnRpZmllcihwYXJhbS50eXBlLnR5cGVOYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHBhcmFtVHlwZU5hbWUgPSBwYXJhbS50eXBlLnR5cGVOYW1lLnRleHQ7XG5cdFx0XHRcdFx0bmFtZWREZWNsID0gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbihwYXJhbVR5cGVOYW1lLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChuYW1lZERlY2wpIHtcblx0XHRcdFx0XHQvLyBtZW1iZXIgdHlwZXMgcmVzb2x2ZSBhZ2FpbnN0IHRoZSBERUNMQVJJTkcgZmlsZVxuXHRcdFx0XHRcdGNvbnN0IHJlZmVyZW5jaW5nRmlsZSA9IHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZTtcblx0XHRcdFx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSBuYW1lZERlY2wuZmlsZTtcblx0XHRcdFx0XHR0cnkge1xuXHRcdFx0XHRcdFx0Y29uc3QgZGVjbFByb3BlcnRpZXMgPSB0aGlzLnJlZmVyZW5jZWREZWNsYXJhdGlvblByb3BlcnRpZXMobmFtZWREZWNsKTtcblx0XHRcdFx0XHRcdGZvciAoY29uc3QgWyBwcm9wTmFtZSwgaW5mbyBdIG9mIGRlY2xQcm9wZXJ0aWVzKSB7XG5cdFx0XHRcdFx0XHRcdHR5cGVNYXAuc2V0KGAke3BhcmFtTmFtZX0uJHtwcm9wTmFtZX1gLCBpbmZvLnR5cGUpO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH0gZmluYWxseSB7XG5cdFx0XHRcdFx0XHR0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUgPSByZWZlcmVuY2luZ0ZpbGU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdC8vIGtlZXAgdGhlIHdob2xlLXBhcmFtIGVudHJ5IHRvbzogYHRoaXMueCA9IGRhdGFgICh0aGVcblx0XHRcdFx0XHQvLyBiYXJlIHBhcmFtZXRlcikgYXNzaWducyB0aGUgZnVsbCBleHBhbmRlZCBzaGFwZSDigJRcblx0XHRcdFx0XHQvLyB0aGUgc2FtZSBzdHJpbmcgY29uc3RydWN0b3Itc2lnbmF0dXJlIGVtaXNzaW9uIHVzZXNcblx0XHRcdFx0XHRjb25zdCB3aG9sZVR5cGUgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24obmFtZWREZWNsKTtcblx0XHRcdFx0XHRpZiAod2hvbGVUeXBlICYmIHdob2xlVHlwZSAhPT0gJ3Vua25vd24nKSB7XG5cdFx0XHRcdFx0XHR0eXBlTWFwLnNldChwYXJhbU5hbWUsIHdob2xlVHlwZSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdC8vIFN0b3JlIHNpbXBsZSBwYXJhbWV0ZXIgdHlwZXMgbGlrZSBgZGVjb3JhdGVWYWx1ZTogc3RyaW5nYFxuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblx0XHRcdFx0XHRpZiAodHlwZSAhPT0gJ3Vua25vd24nKSB7XG5cdFx0XHRcdFx0XHR0eXBlTWFwLnNldChwYXJhbU5hbWUsIHR5cGUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB0eXBlTWFwO1xuXHR9XG5cblx0LyoqXG5cdCAqIEV4dHJhY3QgcHJvcGVydHkgYWNjZXNzIGNoYWluIChlLmcuLCBcImRhdGFSZW5hbWVkLmlkXCIgZnJvbSBkYXRhUmVuYW1lZC5pZClcblx0ICogSGFuZGxlcyBmYWxsYmFja3MgbGlrZTogZGF0YS5wZXJtaXNzaW9ucyB8fCBbXVxuXHQgKi9cblx0cHJpdmF0ZSBnZXRQcm9wZXJ0eUFjY2Vzc0NoYWluIChleHByOiB0cy5FeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHQvLyBIYW5kbGUgaWRlbnRpZmllcjogZGF0YVxuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLnRleHQ7XG5cdFx0fVxuXHRcdC8vIEhhbmRsZSBwcm9wZXJ0eSBhY2Nlc3M6IGRhdGEucGVybWlzc2lvbnNcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdGNvbnN0IGJhc2UgPSB0aGlzLmdldFByb3BlcnR5QWNjZXNzQ2hhaW4oZXhwci5leHByZXNzaW9uKTtcblx0XHRcdGlmIChiYXNlKSB7XG5cdFx0XHRcdHJldHVybiBgJHtiYXNlfS4ke2V4cHIubmFtZS50ZXh0fWA7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdC8vIEhhbmRsZSBmYWxsYmFjayBwYXR0ZXJuOiBkYXRhLnBlcm1pc3Npb25zIHx8IFtdXG5cdFx0aWYgKHRzLmlzQmluYXJ5RXhwcmVzc2lvbihleHByKSAmJlxuXHRcdFx0ZXhwci5vcGVyYXRvclRva2VuLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuQmFyQmFyVG9rZW4pIHtcblx0XHRcdC8vIFJldHVybiB0aGUgbGVmdCBzaWRlIG9mIHx8IG9wZXJhdG9yXG5cdFx0XHRyZXR1cm4gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGV4cHIubGVmdCk7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBwcm9wZXJ0eSBhc3NpZ25tZW50IGZyb20gc3RhdGVtZW50XG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RQcm9wZXJ0eUZyb21TdGF0ZW1lbnQgKFxuXHRcdGV4cHI6IHRzLkV4cHJlc3Npb24sXG5cdFx0cHJvcGVydGllczogTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPixcblx0XHRkYXRhVHlwZU1hcDogTWFwPHN0cmluZywgc3RyaW5nPiA9IG5ldyBNYXAoKVxuXHQpOiB2b2lkIHtcblx0XHQvLyBIYW5kbGU6IHRoaXMucHJvcGVydHkgPSB2YWx1ZVxuXHRcdGlmICh0cy5pc0JpbmFyeUV4cHJlc3Npb24oZXhwcikgJiZcblx0XHRcdGV4cHIub3BlcmF0b3JUb2tlbi5raW5kID09PSB0cy5TeW50YXhLaW5kLkVxdWFsc1Rva2VuKSB7XG5cdFx0XHRjb25zdCB7IGxlZnQgfSA9IGV4cHI7XG5cblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihsZWZ0KSkge1xuXHRcdFx0XHQvLyBDaGVjayBpZiBhY2Nlc3NpbmcgJ3RoaXMnIChUaGlzS2V5d29yZClcblx0XHRcdFx0aWYgKGxlZnQuZXhwcmVzc2lvbi5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRcdFx0Y29uc3QgbmFtZSA9IGxlZnQubmFtZT8udGV4dDtcblx0XHRcdFx0XHRpZiAobmFtZSkge1xuXHRcdFx0XHRcdFx0Ly8gVHJ5IHRvIGdldCB0eXBlIGZyb20gZGF0YVR5cGVNYXAgdXNpbmcgZnVsbCBhY2Nlc3MgY2hhaW4gKGUuZy4sIFwiZGF0YVJlbmFtZWQuaWRcIilcblx0XHRcdFx0XHRcdGNvbnN0IGFjY2Vzc0NoYWluID0gdGhpcy5nZXRQcm9wZXJ0eUFjY2Vzc0NoYWluKGV4cHIucmlnaHQpO1xuXHRcdFx0XHRcdFx0bGV0IHR5cGUgPSBhY2Nlc3NDaGFpbiA/IGRhdGFUeXBlTWFwLmdldChhY2Nlc3NDaGFpbikgOiB1bmRlZmluZWQ7XG5cdFx0XHRcdFx0XHQvLyBJZiBub3QgZm91bmQgYW5kIFJIUyBpcyBhIHNpbXBsZSBpZGVudGlmaWVyLCB0cnkgbG9va2luZyBpdCB1cCBkaXJlY3RseVxuXHRcdFx0XHRcdFx0aWYgKCF0eXBlICYmIHRzLmlzSWRlbnRpZmllcihleHByLnJpZ2h0KSkge1xuXHRcdFx0XHRcdFx0XHR0eXBlID0gZGF0YVR5cGVNYXAuZ2V0KGV4cHIucmlnaHQudGV4dCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHQvLyBhIGJvdW5kIGNvbnN0cnVjdGlvbiByZXN1bHQgKG5ldy9sb29rdXAvY2hhaW4vZm9yay9cblx0XHRcdFx0XHRcdC8vIG1lcmdlL2NhbGwpOiB0aGUgdmFsdWUgc2NvcGUgYmluZGluZyBzdXBwbGllcyB0aGVcblx0XHRcdFx0XHRcdC8vIGdyYXBoIHR5cGUg4oCUIGVtaXR0ZWQgYnkgaXRzIGluc3RhbmNlLXR5cGUgbmFtZVxuXHRcdFx0XHRcdFx0aWYgKCF0eXBlICYmIHRzLmlzSWRlbnRpZmllcihleHByLnJpZ2h0KSkge1xuXHRcdFx0XHRcdFx0XHRjb25zdCBib3VuZCA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KGV4cHIucmlnaHQudGV4dCk7XG5cdFx0XHRcdFx0XHRcdGlmIChib3VuZCkge1xuXHRcdFx0XHRcdFx0XHRcdHR5cGUgPSBib3VuZC5yZXBsYWNlKC9cXC4vZywgJ18nKTtcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKCF0eXBlKSB7XG5cdFx0XHRcdFx0XHRcdHR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihleHByLnJpZ2h0LCBkYXRhVHlwZU1hcCk7XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHQvLyBEb24ndCBvdmVyd3JpdGUgYSBrbm93biB0eXBlIGZyb20gYSBgdGhpc2AgYW5ub3RhdGlvblxuXHRcdFx0XHRcdFx0Ly8gd2l0aCBhbiB1bmtub3duLWJlYXJpbmcgaW5mZXJlbmNlOiBhbiBlbXB0eS1hcnJheVxuXHRcdFx0XHRcdFx0Ly8gaW5pdGlhbGl6ZXIgaW5mZXJzICdBcnJheTx1bmtub3duPicsIHdoaWNoIG11c3Qgbm90XG5cdFx0XHRcdFx0XHQvLyBjbG9iYmVyIGFuIGFubm90YXRlZCAnQXJyYXk8eyBpZDogbnVtYmVyIH0+JyBlaXRoZXIuXG5cdFx0XHRcdFx0XHQvLyBcIktub3duXCIgb24gdGhlIEVYSVNUSU5HIHNpZGUgbWVhbnMgdGhlIHdob2xlIHR5cGUgSVNcblx0XHRcdFx0XHRcdC8vIGB1bmtub3duYCAoZXhhY3QgbWF0Y2gpIOKAlCBhIHN1YnN0cmluZyBtYXRjaCB0cmVhdHNcblx0XHRcdFx0XHRcdC8vIGBSZWNvcmQ8c3RyaW5nLCB1bmtub3duPmAgYXMgdW5rbm93bi1iZWFyaW5nIGFuZCBsZXRcblx0XHRcdFx0XHRcdC8vIGluZmVyZW5jZSBjbG9iYmVyIGEgZ29vZCBhbm5vdGF0aW9uIChGMTQpXG5cdFx0XHRcdFx0XHRjb25zdCBleGlzdGluZyA9IHByb3BlcnRpZXMuZ2V0KG5hbWUpO1xuXHRcdFx0XHRcdFx0Y29uc3QgdHlwZUhhc1Vua25vd24gPSAhdHlwZSB8fCB0eXBlLmluY2x1ZGVzKCd1bmtub3duJyk7XG5cdFx0XHRcdFx0XHRjb25zdCBleGlzdGluZ0lzS25vd24gPSBleGlzdGluZyA/IGV4aXN0aW5nLnR5cGUudHJpbSgpICE9PSAndW5rbm93bicgOiBmYWxzZTtcblx0XHRcdFx0XHRcdGlmIChleGlzdGluZ0lzS25vd24gJiYgdHlwZUhhc1Vua25vd24pIHtcblx0XHRcdFx0XHRcdFx0Ly8gS2VlcCB0aGUgYmV0dGVyIHR5cGUgZnJvbSBleHBsaWNpdCBhbm5vdGF0aW9uXG5cdFx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZXhpc3RpbmcgPyBleGlzdGluZy5vcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBIYW5kbGU6IE9iamVjdC5hc3NpZ24odGhpcywgeyBwcm9wOiB2YWx1ZSB9KVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBmbiA9IGV4cHIuZXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihmbikgJiZcblx0XHRcdFx0Zm4ubmFtZT8udGV4dCA9PT0gJ2Fzc2lnbicgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGZuLmV4cHJlc3Npb24pICYmXG5cdFx0XHRcdGZuLmV4cHJlc3Npb24udGV4dCA9PT0gJ09iamVjdCcpIHtcblx0XHRcdFx0Y29uc3QgYXJncyA9IGV4cHIuYXJndW1lbnRzO1xuXHRcdFx0XHRpZiAoYXJncy5sZW5ndGggPj0gMiAmJiBhcmdzWyAwIF0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdC8vIEV4dHJhY3QgcHJvcGVydGllcyBmcm9tIHRoZSBzZWNvbmQgYXJndW1lbnRcblx0XHRcdFx0XHRjb25zdCBbICwgcHJvcHNBcmcgXSA9IGFyZ3M7XG5cdFx0XHRcdFx0aWYgKHRzLmlzT2JqZWN0TGl0ZXJhbEV4cHJlc3Npb24ocHJvcHNBcmcpKSB7XG5cdFx0XHRcdFx0XHRmb3IgKGNvbnN0IHByb3Agb2YgcHJvcHNBcmcucHJvcGVydGllcykge1xuXHRcdFx0XHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFzc2lnbm1lbnQocHJvcCkgJiYgdHMuaXNJZGVudGlmaWVyKHByb3AubmFtZSkpIHtcblx0XHRcdFx0XHRcdFx0XHRjb25zdCBuYW1lID0gcHJvcC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdFx0XHRcdHR5cGUgICAgIDogdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIocHJvcC5pbml0aWFsaXplciksXG5cdFx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc0lkZW50aWZpZXIocHJvcHNBcmcpKSB7XG5cdFx0XHRcdFx0XHQvLyBPYmplY3QuYXNzaWduKHRoaXMsIGRhdGEpIOKAlCB0aGUgaWRlbnRpZmllciBmb3JtOiBldmVyeVxuXHRcdFx0XHRcdFx0Ly8gcGVyLXByb3BlcnR5IGVudHJ5IHRoZSBkYXRhIHBhcmFtZXRlciBjb250cmlidXRlZCB0b1xuXHRcdFx0XHRcdFx0Ly8gdGhlIHR5cGUgbWFwIGJlY29tZXMgYW4gb3duIHByb3BlcnR5LiBUaGlzIGlzIHdoYXRcblx0XHRcdFx0XHRcdC8vIGNhcnJpZXMgdGhlIGZpZWxkcyBmb3IgdGhlIHNlbGYtcmVmZXJlbmNpbmdcblx0XHRcdFx0XHRcdC8vIGludGVyc2VjdGlvbi1hbGlhcyByb290IHBhdHRlcm4gKEYyMSk6IHRoZSB0aGlzLWFsaWFzXG5cdFx0XHRcdFx0XHQvLyBpcyBlcmdvbm9taWMtb25seSBhbmQgaXRzIGludGVyc2VjdGlvbiBtZW1iZXJzIGFyZVxuXHRcdFx0XHRcdFx0Ly8gbmV2ZXIgZXhwYW5kZWQsIHNvIHRoZSBhc3NpZ24gaXMgd2hlcmUgdGhlIHJvb3Qnc1xuXHRcdFx0XHRcdFx0Ly8gZmllbGRzIG11c3QgY29tZSBmcm9tXG5cdFx0XHRcdFx0XHRjb25zdCBwYXJhbU5hbWUgPSBwcm9wc0FyZy50ZXh0O1xuXHRcdFx0XHRcdFx0Zm9yIChjb25zdCBbIGtleSwgdHlwZSBdIG9mIGRhdGFUeXBlTWFwKSB7XG5cdFx0XHRcdFx0XHRcdGlmICgha2V5LnN0YXJ0c1dpdGgoYCR7cGFyYW1OYW1lfS5gKSkge1xuXHRcdFx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRcdGNvbnN0IG5hbWUgPSBrZXkuc2xpY2UocGFyYW1OYW1lLmxlbmd0aCArIDEpO1xuXHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBjbGFzcyBkZWNsYXJhdGlvbiAoaW5jbHVkaW5nIG1ldGhvZHMgYW5kIGdldHRlcnMpXG5cdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDbGFzc1Byb3BlcnRpZXMgKGNsYXNzRGVjbDogdHMuQ2xhc3NEZWNsYXJhdGlvbik6IE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgY2xhc3NEZWNsLm1lbWJlcnMpIHtcblx0XHRcdC8vIEhhbmRsZSBwcm9wZXJ0eSBkZWNsYXJhdGlvbnNcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5RGVjbGFyYXRpb24obWVtYmVyKSAmJiBtZW1iZXIubmFtZSkge1xuXHRcdFx0XHQvLyBTa2lwIHByaXZhdGUgYW5kIHByb3RlY3RlZCBwcm9wZXJ0aWVzXG5cdFx0XHRcdGlmIChtZW1iZXIubW9kaWZpZXJzKSB7XG5cdFx0XHRcdFx0Y29uc3QgaGFzUHJpdmF0ZU9yUHJvdGVjdGVkID0gbWVtYmVyLm1vZGlmaWVycy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByaXZhdGVLZXl3b3JkIHx8XG5cdFx0XHRcdFx0XHQgICAgIG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcm90ZWN0ZWRLZXl3b3JkKTtcblx0XHRcdFx0XHRpZiAoaGFzUHJpdmF0ZU9yUHJvdGVjdGVkKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblxuXHRcdFx0XHRjb25zdCBuYW1lID0gdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSA/IG1lbWJlci5uYW1lLnRleHQgOiAnJztcblx0XHRcdFx0aWYgKG5hbWUpIHtcblx0XHRcdFx0XHQvLyBJZiBubyBleHBsaWNpdCB0eXBlIGJ1dCBoYXMgaW5pdGlhbGl6ZXIsIGluZmVyIGZyb20gaW5pdGlhbGl6ZXJcblx0XHRcdFx0XHRsZXQgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRpZiAodHlwZSA9PT0gJ3Vua25vd24nICYmIG1lbWJlci5pbml0aWFsaXplcikge1xuXHRcdFx0XHRcdFx0dHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKG1lbWJlci5pbml0aWFsaXplcik7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdHByb3BlcnRpZXMuc2V0KG5hbWUsIHtcblx0XHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdFx0b3B0aW9uYWwgOiAhIW1lbWJlci5xdWVzdGlvblRva2VuLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cblx0XHRcdC8vIEhhbmRsZSBtZXRob2QgZGVjbGFyYXRpb25zXG5cdFx0XHRpZiAodHMuaXNNZXRob2REZWNsYXJhdGlvbihtZW1iZXIpICYmIG1lbWJlci5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0Ly8gU2tpcCBwcml2YXRlIGFuZCBwcm90ZWN0ZWQgbWV0aG9kc1xuXHRcdFx0XHRpZiAobWVtYmVyLm1vZGlmaWVycykge1xuXHRcdFx0XHRcdGNvbnN0IGhhc1ByaXZhdGVPclByb3RlY3RlZCA9IG1lbWJlci5tb2RpZmllcnMuc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5Qcml2YXRlS2V5d29yZCB8fFxuXHRcdFx0XHRcdFx0ICAgICBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJvdGVjdGVkS2V5d29yZCk7XG5cdFx0XHRcdFx0aWYgKGhhc1ByaXZhdGVPclByb3RlY3RlZCkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cblx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyTWV0aG9kVHlwZShtZW1iZXIpO1xuXHRcdFx0XHRwcm9wZXJ0aWVzLnNldChuYW1lLCB7XG5cdFx0XHRcdFx0bmFtZSxcblx0XHRcdFx0XHR0eXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogZmFsc2UsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBIYW5kbGUgZ2V0dGVyIGRlY2xhcmF0aW9uc1xuXHRcdFx0aWYgKHRzLmlzR2V0QWNjZXNzb3IobWVtYmVyKSAmJiBtZW1iZXIubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIobWVtYmVyLm5hbWUpKSB7XG5cdFx0XHRcdC8vIFNraXAgcHJpdmF0ZSBhbmQgcHJvdGVjdGVkIGdldHRlcnNcblx0XHRcdFx0aWYgKG1lbWJlci5tb2RpZmllcnMpIHtcblx0XHRcdFx0XHRjb25zdCBoYXNQcml2YXRlT3JQcm90ZWN0ZWQgPSBtZW1iZXIubW9kaWZpZXJzLnNvbWUobSA9PiBtLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuUHJpdmF0ZUtleXdvcmQgfHxcblx0XHRcdFx0XHRcdCAgICAgbS5raW5kID09PSB0cy5TeW50YXhLaW5kLlByb3RlY3RlZEtleXdvcmQpO1xuXHRcdFx0XHRcdGlmIChoYXNQcml2YXRlT3JQcm90ZWN0ZWQpIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXG5cdFx0XHRcdGNvbnN0IG5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHQvLyBGaXJzdCB0cnkgZXhwbGljaXQgdHlwZSBhbm5vdGF0aW9uLCB0aGVuIGluZmVyIGZyb20gZ2V0dGVyIGJvZHlcblx0XHRcdFx0bGV0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdGlmICh0eXBlID09PSAndW5rbm93bicgJiYgbWVtYmVyLmJvZHkpIHtcblx0XHRcdFx0XHR0eXBlID0gdGhpcy5pbmZlclJldHVyblR5cGVGcm9tQm9keShtZW1iZXIuYm9keSk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cHJvcGVydGllcy5zZXQobmFtZSwge1xuXHRcdFx0XHRcdG5hbWUsXG5cdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRvcHRpb25hbCA6IGZhbHNlLFxuXHRcdFx0XHRcdHJlYWRvbmx5IDogdHJ1ZSxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHByb3BlcnRpZXM7XG5cdH1cblxuXHQvKipcblx0ICogRXh0cmFjdCBjbGFzcyBwcm9wZXJ0eSB0eXBlcyBmb3IgbWV0aG9kIHJldHVybiB0eXBlIGluZmVyZW5jZVxuXHQgKiBNYXBzIHByb3BlcnR5IG5hbWVzIHRvIHRoZWlyIFR5cGVTY3JpcHQgdHlwZSBzdHJpbmdzXG5cdCAqIE5vdGU6IEluY2x1ZGVzIHByaXZhdGUvcHJvdGVjdGVkIHByb3BlcnRpZXMgZm9yIG1ldGhvZCBpbmZlcmVuY2Vcblx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENsYXNzUHJvcGVydHlUeXBlcyAoY2xhc3NEZWNsOiB0cy5DbGFzc0V4cHJlc3Npb24pOiBNYXA8c3RyaW5nLCBzdHJpbmc+IHtcblx0XHRjb25zdCBwcm9wZXJ0eVR5cGVzID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZz4oKTtcblxuXHRcdGZvciAoY29uc3QgbWVtYmVyIG9mIGNsYXNzRGVjbC5tZW1iZXJzKSB7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eURlY2xhcmF0aW9uKG1lbWJlcikgJiYgbWVtYmVyLm5hbWUgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHQvLyBJbmNsdWRlIEFMTCBwcm9wZXJ0aWVzIChldmVuIHByaXZhdGUpIGZvciBtZXRob2QgcmV0dXJuIHR5cGUgaW5mZXJlbmNlXG5cdFx0XHRcdC8vIFRoZSB2aXNpYmlsaXR5IGNoZWNrIGlzIGRvbmUgd2hlbiBhZGRpbmcgdG8gb3V0cHV0IHByb3BlcnRpZXNcblx0XHRcdFx0Y29uc3QgbmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdGlmIChtZW1iZXIudHlwZSkge1xuXHRcdFx0XHRcdHByb3BlcnR5VHlwZXMuc2V0KG5hbWUsIHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydHlUeXBlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBJbmZlciBtZXRob2QgdHlwZSBmcm9tIG1ldGhvZCBkZWNsYXJhdGlvblxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlck1ldGhvZFR5cGUgKG1ldGhvZDogdHMuTWV0aG9kRGVjbGFyYXRpb24sIGNsYXNzUHJvcGVydHlUeXBlcz86IE1hcDxzdHJpbmcsIHN0cmluZz4pOiBzdHJpbmcge1xuXHRcdGNvbnN0IHBhcmFtcyA9IG1ldGhvZC5wYXJhbWV0ZXJzLm1hcChwYXJhbSA9PiB7XG5cdFx0XHRjb25zdCBwYXJhbU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgPyBwYXJhbS5uYW1lLnRleHQgOiAnYXJnJztcblx0XHRcdGNvbnN0IHBhcmFtVHlwZSA9IHRoaXMuaW5mZXJUeXBlKHBhcmFtLnR5cGUpO1xuXHRcdFx0cmV0dXJuIGAke3BhcmFtTmFtZX06ICR7cGFyYW1UeXBlfWA7XG5cdFx0fSkuam9pbignLCAnKTtcblxuXHRcdGNvbnN0IHJldHVyblR5cGUgPSB0aGlzLmluZmVyUmV0dXJuVHlwZShtZXRob2QsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cblx0XHRpZiAocGFyYW1zKSB7XG5cdFx0XHRyZXR1cm4gYCgke3BhcmFtc30pID0+ICR7cmV0dXJuVHlwZX1gO1xuXHRcdH1cblx0XHRyZXR1cm4gYCgpID0+ICR7cmV0dXJuVHlwZX1gO1xuXHR9XG5cblx0LyoqXG5cdFx0KiBFeHRyYWN0IHByb3BlcnRpZXMgZnJvbSBgdGhpc2AgcGFyYW1ldGVyIHR5cGUgYW5ub3RhdGlvblxuXHRcdCogSGFuZGxlcyBwYXR0ZXJucyBsaWtlOiBmdW5jdGlvbih0aGlzOiBTb21lVHlwZSwgZGF0YTogU29tZVR5cGUpIHsgfVxuXHRcdCovXG5cdHByaXZhdGUgZXh0cmFjdFRoaXNQYXJhbVByb3BlcnRpZXMgKGhhbmRsZXJBcmc6IHRzLkZ1bmN0aW9uRXhwcmVzc2lvbiB8IHRzLkFycm93RnVuY3Rpb24pOlxuXHRcdE1hcDxzdHJpbmcsIFByb3BlcnR5SW5mbz4ge1xuXHRcdGNvbnN0IHByb3BlcnRpZXMgPSBuZXcgTWFwPHN0cmluZywgUHJvcGVydHlJbmZvPigpO1xuXG5cdFx0Ly8gRmluZCB0aGUgYHRoaXNgIHBhcmFtZXRlciAoaWYgYW55KVxuXHRcdGZvciAoY29uc3QgcGFyYW0gb2YgaGFuZGxlckFyZy5wYXJhbWV0ZXJzKSB7XG5cdFx0XHRpZiAocGFyYW0ubmFtZSAmJiB0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkgJiYgcGFyYW0ubmFtZS50ZXh0ID09PSAndGhpcycgJiYgcGFyYW0udHlwZSkge1xuXHRcdFx0XHQvLyBDaGVjayBpZiBpdCdzIGEgdHlwZSByZWZlcmVuY2UgKGUuZy4sIGB0aGlzOiB1c2FnZWApXG5cdFx0XHRcdGlmICh0cy5pc1R5cGVSZWZlcmVuY2VOb2RlKHBhcmFtLnR5cGUpKSB7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZU5hbWUgPSB0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSlcblx0XHRcdFx0XHRcdD8gcGFyYW0udHlwZS50eXBlTmFtZS50ZXh0XG5cdFx0XHRcdFx0XHQ6ICcnO1xuXG5cdFx0XHRcdFx0Ly8gUmVzb2x2ZSB0aHJvdWdoIHRoZSByZWZlcmVuY2luZyBmaWxlJ3Mgb3duIGltcG9ydHMgZmlyc3QgKEYxMClcblx0XHRcdFx0XHRjb25zdCBkZWNsID0gdHlwZU5hbWVcblx0XHRcdFx0XHRcdD8gdGhpcy5yZXNvbHZlUmVmZXJlbmNlZFR5cGVEZWNsYXJhdGlvbih0eXBlTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKVxuXHRcdFx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cdFx0XHRcdFx0aWYgKGRlY2wpIHtcblx0XHRcdFx0XHRcdGNvbnN0IGRlY2xQcm9wZXJ0aWVzID0gdGhpcy5yZWZlcmVuY2VkRGVjbGFyYXRpb25Qcm9wZXJ0aWVzKGRlY2wpO1xuXHRcdFx0XHRcdFx0Zm9yIChjb25zdCBbIHByb3BOYW1lLCBpbmZvIF0gb2YgZGVjbFByb3BlcnRpZXMpIHtcblx0XHRcdFx0XHRcdFx0cHJvcGVydGllcy5zZXQocHJvcE5hbWUsIGluZm8pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBDaGVjayBpZiBpdCdzIGRpcmVjdGx5IGFuIGlubGluZSB0eXBlIGxpdGVyYWwgKGUuZy4sIGB0aGlzOiB7IGlkOiBzdHJpbmcgfWApXG5cdFx0XHRcdGVsc2UgaWYgKHRzLmlzVHlwZUxpdGVyYWxOb2RlKHBhcmFtLnR5cGUpKSB7XG5cdFx0XHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgcGFyYW0udHlwZS5tZW1iZXJzKSB7XG5cdFx0XHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBtZW1iZXIubmFtZS50ZXh0O1xuXHRcdFx0XHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGUobWVtYmVyLnR5cGUpO1xuXHRcdFx0XHRcdFx0XHRwcm9wZXJ0aWVzLnNldChwcm9wTmFtZSwge1xuXHRcdFx0XHRcdFx0XHRcdG5hbWUgICAgIDogcHJvcE5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0dHlwZSxcblx0XHRcdFx0XHRcdFx0XHRvcHRpb25hbCA6ICEhbWVtYmVyLnF1ZXN0aW9uVG9rZW4sXG5cdFx0XHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBGb3VuZCB0aGUgYHRoaXNgIHBhcmFtZXRlciwgbm8gbmVlZCB0byBjb250aW51ZVxuXHRcdFx0XHRicmVhaztcblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gcHJvcGVydGllcztcblx0fVxuXG5cdC8qKlxuXHRcdCogSW5mZXIgVHlwZVNjcmlwdCB0eXBlIGZyb20gdHlwZSBub2RlXG5cdFx0Ki9cblx0LyoqXG5cdCAqIEluZmVyIFR5cGVTY3JpcHQgdHlwZSBmcm9tIHR5cGUgbm9kZVxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlclR5cGUgKHR5cGVOb2RlPzogdHMuVHlwZU5vZGUpOiBzdHJpbmcge1xuXHRcdGlmICghdHlwZU5vZGUpIHtcblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXG5cdFx0c3dpdGNoICh0eXBlTm9kZS5raW5kKSB7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlN0cmluZ0tleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bWJlcktleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLkJvb2xlYW5LZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5kZWZpbmVkS2V5d29yZDpcblx0XHRcdHJldHVybiAndW5kZWZpbmVkJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bGwnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5BbnlLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdhbnknO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5Vbmtub3duS2V5d29yZDpcblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlZvaWRLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICd2b2lkJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuQXJyYXlUeXBlOlxuXHRcdFx0cmV0dXJuIGBBcnJheTwkeyAgdGhpcy5pbmZlclR5cGUoKHR5cGVOb2RlIGFzIHRzLkFycmF5VHlwZU5vZGUpLmVsZW1lbnRUeXBlKSAgfT5gO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlTGl0ZXJhbDoge1xuXHRcdFx0Ly8gSW5saW5lLWV4cGFuZCB0eXBlIGxpdGVyYWxzIGluc3RlYWQgb2YgY29sbGFwc2luZyB0byAnb2JqZWN0J1xuXHRcdFx0Y29uc3QgdHlwZUxpdCA9IHR5cGVOb2RlIGFzIHRzLlR5cGVMaXRlcmFsTm9kZTtcblx0XHRcdGNvbnN0IHByb3BzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgdHlwZUxpdC5tZW1iZXJzKSB7XG5cdFx0XHRcdGlmICh0cy5pc1Byb3BlcnR5U2lnbmF0dXJlKG1lbWJlcikgJiYgdHMuaXNJZGVudGlmaWVyKG1lbWJlci5uYW1lKSkge1xuXHRcdFx0XHRcdGNvbnN0IHByb3BOYW1lID0gbWVtYmVyLm5hbWUudGV4dDtcblx0XHRcdFx0XHRjb25zdCBvcHRpb25hbCA9IG1lbWJlci5xdWVzdGlvblRva2VuID8gJz8nIDogJyc7XG5cdFx0XHRcdFx0Y29uc3QgdHlwZSA9IHRoaXMuaW5mZXJUeXBlKG1lbWJlci50eXBlKTtcblx0XHRcdFx0XHRwcm9wcy5wdXNoKGAke3Byb3BOYW1lfSR7b3B0aW9uYWx9OiAke3R5cGV9YCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiBgeyAke3Byb3BzLmpvaW4oJzsgJyl9IH1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTGl0ZXJhbFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBzdHJpbmcgbGl0ZXJhbCB0eXBlcyBsaWtlICd1c2VyJywgJ2FkbWluJywgZXRjLlxuXHRcdFx0Y29uc3QgeyBsaXRlcmFsIH0gPSAodHlwZU5vZGUgYXMgdHMuTGl0ZXJhbFR5cGVOb2RlKTtcblx0XHRcdGlmICh0cy5pc1N0cmluZ0xpdGVyYWwobGl0ZXJhbCkpIHtcblx0XHRcdFx0Ly8gUmV0dXJuIHRoZSBhY3R1YWwgbGl0ZXJhbCB2YWx1ZSAoZS5nLiwgJ3VzZXInIGluc3RlYWQgb2Ygc3RyaW5nKVxuXHRcdFx0XHRyZXR1cm4gYCcke2xpdGVyYWwudGV4dH0nYDtcblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc051bWVyaWNMaXRlcmFsKGxpdGVyYWwpKSB7XG5cdFx0XHRcdHJldHVybiBsaXRlcmFsLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAobGl0ZXJhbC5raW5kID09PSB0cy5TeW50YXhLaW5kLlRydWVLZXl3b3JkKSB7XG5cdFx0XHRcdHJldHVybiAndHJ1ZSc7XG5cdFx0XHR9XG5cdFx0XHRpZiAobGl0ZXJhbC5raW5kID09PSB0cy5TeW50YXhLaW5kLkZhbHNlS2V5d29yZCkge1xuXHRcdFx0XHRyZXR1cm4gJ2ZhbHNlJztcblx0XHRcdH1cblx0XHRcdGlmIChsaXRlcmFsLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQpIHtcblx0XHRcdFx0cmV0dXJuICdudWxsJztcblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UeXBlUmVmZXJlbmNlOiB7XG5cdFx0XHQvLyBIYW5kbGUgdHlwZSByZWZlcmVuY2VzIGxpa2UgTWFwPHN0cmluZywgbnVtYmVyPiwgUHJvcGVydHlJbmZvLCBldGMuXG5cdFx0XHRjb25zdCB0eXBlUmVmID0gdHlwZU5vZGUgYXMgdHMuVHlwZVJlZmVyZW5jZU5vZGU7XG5cblx0XHRcdC8vIFF1YWxpZmllZCBuYW1lcyAoTmFtZXNwYWNlLlR5cGUpOiByZXNvbHZlIHRocm91Z2ggbmFtZXNwYWNlIGltcG9ydHNcblx0XHRcdGlmICh0cy5pc1F1YWxpZmllZE5hbWUodHlwZVJlZi50eXBlTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgcmVzb2x2ZWRRdWFsaWZpZWQgPSB0aGlzLmluZmVyUXVhbGlmaWVkVHlwZVJlZmVyZW5jZSh0eXBlUmVmKTtcblx0XHRcdFx0aWYgKHJlc29sdmVkUXVhbGlmaWVkICE9PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0XHRyZXR1cm4gcmVzb2x2ZWRRdWFsaWZpZWQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gdW5yZXNvbHZlZCBxdWFsaWZpZWQgcmVmZXJlbmNlcyBtdXN0IG5vdCBsZWFrIGEgYmFyZSBuYW1lXG5cdFx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0XHR9XG5cblx0XHRcdGNvbnN0IHR5cGVOYW1lID0gdHMuaXNJZGVudGlmaWVyKHR5cGVSZWYudHlwZU5hbWUpID8gdHlwZVJlZi50eXBlTmFtZS50ZXh0IDogJ3Vua25vd24nO1xuXG5cdFx0XHQvLyBJbXBvcnQtYXdhcmUgcmVmZXJlbmNlZC10eXBlIHJlc29sdXRpb24gKEYxMCk6IGEgZGVjbGFyYXRpb25cblx0XHRcdC8vIHJlYWNoZWQgdGhyb3VnaCB0aGUgY3VycmVudCBmaWxlJ3Mgb3duIGltcG9ydHMgKG9yIGl0cyBsb2NhbHMsXG5cdFx0XHQvLyBvciBhIHVuaXF1ZSBwcm9ncmFtLXdpZGUgZGVjbGFyYXRpb24pIGV4cGFuZHMgaW5saW5lXG5cdFx0XHRjb25zdCBzaW1wbGVSZWYgPSB0aGlzLnJlc29sdmVTaW1wbGVUeXBlUmVmZXJlbmNlKHR5cGVOYW1lLCB0eXBlUmVmLnR5cGVBcmd1bWVudHMsIHR5cGVSZWYpO1xuXHRcdFx0aWYgKHNpbXBsZVJlZiAhPT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdHJldHVybiBzaW1wbGVSZWY7XG5cdFx0XHR9XG5cblx0XHRcdC8vIEJ1aWxkIGdlbmVyaWMgdHlwZSBhcmd1bWVudHNcblx0XHRcdGNvbnN0IHR5cGVBcmdzID0gKHR5cGVSZWYudHlwZUFyZ3VtZW50cyA/PyBbXSkubWFwKGFyZyA9PiB0aGlzLmluZmVyVHlwZShhcmcpKTtcblx0XHRcdHJldHVybiBgJHt0eXBlTmFtZX08JHt0eXBlQXJncy5qb2luKCcsICcpfT5gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVW5pb25UeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgdW5pb24gdHlwZXMgbGlrZSAnYScgfCAnYicgfCAnYydcblx0XHRcdGNvbnN0IHVuaW9uVHlwZSA9IHR5cGVOb2RlIGFzIHRzLlVuaW9uVHlwZU5vZGU7XG5cdFx0XHRjb25zdCB0eXBlcyA9IHVuaW9uVHlwZS50eXBlcy5tYXAodCA9PiB0aGlzLmluZmVyVHlwZSh0KSk7XG5cdFx0XHRyZXR1cm4gdHlwZXMuam9pbignIHwgJyk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5JbnRlcnNlY3Rpb25UeXBlOiB7XG5cdFx0XHQvLyBIYW5kbGUgaW50ZXJzZWN0aW9uIHR5cGVzIGxpa2UgVHlwZUEgJiBUeXBlQlxuXHRcdFx0Y29uc3QgaW50ZXJzZWN0aW9uVHlwZSA9IHR5cGVOb2RlIGFzIHRzLkludGVyc2VjdGlvblR5cGVOb2RlO1xuXHRcdFx0Y29uc3QgdHlwZXMgPSBpbnRlcnNlY3Rpb25UeXBlLnR5cGVzLm1hcCh0ID0+IHRoaXMuaW5mZXJUeXBlKHQpKTtcblx0XHRcdHJldHVybiB0eXBlcy5qb2luKCcgJiAnKTtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR1cGxlVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHR1cGxlIHR5cGVzIGxpa2UgW3N0cmluZywgbnVtYmVyXVxuXHRcdFx0Y29uc3QgdHVwbGVUeXBlID0gdHlwZU5vZGUgYXMgdHMuVHVwbGVUeXBlTm9kZTtcblx0XHRcdGNvbnN0IGVsZW1lbnRzID0gdHVwbGVUeXBlLmVsZW1lbnRzLm1hcChlbGVtID0+IHRoaXMuaW5mZXJUeXBlKGVsZW0gYXMgdHMuVHlwZU5vZGUpKTtcblx0XHRcdHJldHVybiBgWyR7ZWxlbWVudHMuam9pbignLCAnKX1dYDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk9wdGlvbmFsVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIG9wdGlvbmFsIGVsZW1lbnQgaW4gdHVwbGU6IHN0cmluZz9cblx0XHRcdGNvbnN0IG9wdGlvbmFsVHlwZSA9IHR5cGVOb2RlIGFzIHRzLk9wdGlvbmFsVHlwZU5vZGU7XG5cdFx0XHRyZXR1cm4gYCR7dGhpcy5pbmZlclR5cGUob3B0aW9uYWxUeXBlLnR5cGUpICB9P2A7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5SZXN0VHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIHJlc3QgZWxlbWVudDogLi4uVFxuXHRcdFx0Y29uc3QgcmVzdFR5cGUgPSB0eXBlTm9kZSBhcyB0cy5SZXN0VHlwZU5vZGU7XG5cdFx0XHRyZXR1cm4gYC4uLiR7ICB0aGlzLmluZmVyVHlwZShyZXN0VHlwZS50eXBlKX1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuUGFyZW50aGVzaXplZFR5cGU6IHtcblx0XHRcdC8vIEhhbmRsZSBwYXJlbnRoZXNpemVkIHR5cGVzOiAoQSB8IEIpXG5cdFx0XHRyZXR1cm4gdGhpcy5pbmZlclR5cGUoKHR5cGVOb2RlIGFzIHRzLlBhcmVudGhlc2l6ZWRUeXBlTm9kZSkudHlwZSk7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5JbmRleGVkQWNjZXNzVHlwZToge1xuXHRcdFx0Ly8gSGFuZGxlIGluZGV4ZWQgYWNjZXNzOiBUW0tdXG5cdFx0XHRjb25zdCBpbmRleGVkID0gdHlwZU5vZGUgYXMgdHMuSW5kZXhlZEFjY2Vzc1R5cGVOb2RlO1xuXHRcdFx0Ly8gYHR5cGVvZiBjb25zdEFycmF5W0tdYCDigJQgZWxlbWVudCB0eXBlIG9mIGEgdHJhY2tlZCBjb25zdCBhcnJheTpcblx0XHRcdC8vIGVtaXQgdGhlIGVsZW1lbnQgbGl0ZXJhbCB1bmlvbiBkaXJlY3RseSAoYXNzZW1ibGluZ1xuXHRcdFx0Ly8gYHVuaW9uW0tdYCB0ZXh0IHdvdWxkIG1pc3JlYWQgcHJlY2VkZW5jZSwgYW5kIHdoZW4gdGhlIGNvbnN0XG5cdFx0XHQvLyBpcyBub3Qgc3RhdGljYWxseSB2aXNpYmxlIHRoZSBob25lc3QgYW5zd2VyIGlzIGB1bmtub3duYCxcblx0XHRcdC8vIG5ldmVyIGEgYmFyZSBgdHlwZW9mIG5hbWVgIHF1ZXJ5KVxuXHRcdFx0aWYgKHRzLmlzVHlwZVF1ZXJ5Tm9kZShpbmRleGVkLm9iamVjdFR5cGUpICYmIHRzLmlzSWRlbnRpZmllcihpbmRleGVkLm9iamVjdFR5cGUuZXhwck5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHF1ZXJ5TmFtZSA9IGluZGV4ZWQub2JqZWN0VHlwZS5leHByTmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBhcnJheUxpdGVyYWwgPSB0aGlzLmZpbmRSZWZlcmVuY2VkQ29uc3RBcnJheShxdWVyeU5hbWUsIHRoaXMuY3VycmVudFJlZmVyZW5jZWRUeXBlRmlsZSk7XG5cdFx0XHRcdGNvbnN0IGxpdGVyYWxzID0gYXJyYXlMaXRlcmFsID8gdGhpcy5saXRlcmFsVHlwZXNPZkFycmF5KGFycmF5TGl0ZXJhbCkgOiB1bmRlZmluZWQ7XG5cdFx0XHRcdGlmICghbGl0ZXJhbHMpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmICh0cy5pc0xpdGVyYWxUeXBlTm9kZShpbmRleGVkLmluZGV4VHlwZSkgJiYgdHMuaXNOdW1lcmljTGl0ZXJhbChpbmRleGVkLmluZGV4VHlwZS5saXRlcmFsKSkge1xuXHRcdFx0XHRcdGNvbnN0IGVsZW1lbnRJbmRleCA9IHBhcnNlSW50KGluZGV4ZWQuaW5kZXhUeXBlLmxpdGVyYWwudGV4dCwgMTApO1xuXHRcdFx0XHRcdGNvbnN0IGVsZW1lbnQgPSBsaXRlcmFsc1sgZWxlbWVudEluZGV4IF07XG5cdFx0XHRcdFx0Y29uc3QgZWxlbWVudFJlc3VsdCA9IGVsZW1lbnQgPT09IHVuZGVmaW5lZCA/ICd1bmtub3duJyA6IGVsZW1lbnQ7XG5cdFx0XHRcdFx0cmV0dXJuIGVsZW1lbnRSZXN1bHQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgdW5pb25SZXN1bHQgPSBsaXRlcmFscy5qb2luKCcgfCAnKTtcblx0XHRcdFx0cmV0dXJuIHVuaW9uUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0bGV0IG9iamVjdFR5cGUgPSB0aGlzLmluZmVyVHlwZShpbmRleGVkLm9iamVjdFR5cGUpO1xuXHRcdFx0Y29uc3QgaW5kZXhUeXBlID0gdGhpcy5pbmZlclR5cGUoaW5kZXhlZC5pbmRleFR5cGUpO1xuXHRcdFx0Ly8gSWYgb2JqZWN0VHlwZSBpcyAnb2JqZWN0JywgdHJ5IHRvIHJlc29sdmUgdGhlIHVuZGVybHlpbmcgcmVmZXJlbmNlZCB0eXBlXG5cdFx0XHRpZiAob2JqZWN0VHlwZSA9PT0gJ29iamVjdCcgJiYgdHMuaXNUeXBlUmVmZXJlbmNlTm9kZShpbmRleGVkLm9iamVjdFR5cGUpKSB7XG5cdFx0XHRcdGNvbnN0IHJlZk5hbWUgPSB0cy5pc0lkZW50aWZpZXIoaW5kZXhlZC5vYmplY3RUeXBlLnR5cGVOYW1lKSA/IGluZGV4ZWQub2JqZWN0VHlwZS50eXBlTmFtZS50ZXh0IDogJyc7XG5cdFx0XHRcdGlmIChyZWZOYW1lKSB7XG5cdFx0XHRcdFx0Y29uc3QgZGVjbCA9IHRoaXMucmVzb2x2ZVJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24ocmVmTmFtZSwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdFx0XHRpZiAoZGVjbCkge1xuXHRcdFx0XHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oZGVjbCk7XG5cdFx0XHRcdFx0XHRpZiAoZXhwYW5kZWQpIHtcblx0XHRcdFx0XHRcdFx0b2JqZWN0VHlwZSA9IGV4cGFuZGVkO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gSW52YXJpYW50OiBhbiBpbmRleCBzdWZmaXggbXVzdCBORVZFUiBiZSBnbHVlZCBvbnRvIGFuXG5cdFx0XHQvLyB1bnJlc29sdmVkL2ZhbGxiYWNrIHRhcmdldCDigJQgYHVua25vd25bbnVtYmVyXWAgLyBgb2JqZWN0W0tdYFxuXHRcdFx0Ly8gYXJlIGludmFsaWQgVHlwZVNjcmlwdCBpbiB0aGUgZ2VuZXJhdGVkIGZpbGUgKGhhcmQgY29tcGlsZVxuXHRcdFx0Ly8gYnJlYWssIEYxNykuIFdoZW4gZWl0aGVyIHNpZGUgZGlkIG5vdCByZXNvbHZlLCB0aGUgV0hPTEVcblx0XHRcdC8vIGluZGV4ZWQgYWNjZXNzIGRlZ3JhZGVzIHRvIGB1bmtub3duYC5cblx0XHRcdGNvbnN0IHRhcmdldFVucmVzb2x2ZWQgPSBvYmplY3RUeXBlID09PSAndW5rbm93bicgfHwgb2JqZWN0VHlwZSA9PT0gJ29iamVjdCc7XG5cdFx0XHRjb25zdCBpbmRleFVucmVzb2x2ZWQgPSBpbmRleFR5cGUgPT09ICd1bmtub3duJztcblx0XHRcdGlmICh0YXJnZXRVbnJlc29sdmVkIHx8IGluZGV4VW5yZXNvbHZlZCkge1xuXHRcdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGAke29iamVjdFR5cGV9WyR7aW5kZXhUeXBlfV1gO1xuXHRcdH1cblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuVHlwZU9wZXJhdG9yOiB7XG5cdFx0XHQvLyBIYW5kbGUga2V5b2YsIHJlYWRvbmx5LCB1bmlxdWUgb3BlcmF0b3JzXG5cdFx0XHRjb25zdCB0eXBlT3AgPSB0eXBlTm9kZSBhcyB0cy5UeXBlT3BlcmF0b3JOb2RlO1xuXHRcdFx0Y29uc3Qgb3BlcmF0b3IgPSB0cy5TeW50YXhLaW5kWyB0eXBlT3Aub3BlcmF0b3IgXTtcblx0XHRcdHJldHVybiBgJHtvcGVyYXRvcn0gJHt0aGlzLmluZmVyVHlwZSh0eXBlT3AudHlwZSl9YDtcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlR5cGVRdWVyeToge1xuXHRcdFx0Ly8gYHR5cGVvZiB4YCBhcyBhIEZJRUxEIFRZUEU6IHRoZSBnZW5lcmF0ZWQgZmlsZSBoYXMgbm8gaW1wb3J0cyxcblx0XHRcdC8vIHNvIGEgYmFyZSBgdHlwZW9mIHhgIHdvdWxkIGJlIGFuIHVucmVzb2x2YWJsZSBuYW1lIGRvd25zdHJlYW0uXG5cdFx0XHQvLyBXaGVuIHggaXMgYSB0cmFja2VkIGNvbnN0IGFycmF5LCBlbWl0IGl0cyBlbGVtZW50IGxpdGVyYWxcblx0XHRcdC8vIHVuaW9uOyBvdGhlcndpc2UgZGVncmFkZSB0byBgdW5rbm93bmAuIChJbnN0YW5jZVR5cGU8dHlwZW9mIFg+XG5cdFx0XHQvLyBncmFwaCB0eXBlcyBhcmUgaGFuZGxlZCBpbiByZXNvbHZlU2ltcGxlVHlwZVJlZmVyZW5jZSBiZWZvcmVcblx0XHRcdC8vIGluZmVyVHlwZSBydW5zLilcblx0XHRcdGNvbnN0IHR5cGVRdWVyeSA9IHR5cGVOb2RlIGFzIHRzLlR5cGVRdWVyeU5vZGU7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKHR5cGVRdWVyeS5leHByTmFtZSkpIHtcblx0XHRcdFx0Y29uc3QgdW5pb24gPSB0aGlzLnR5cGVPZkNvbnN0QXJyYXlVbmlvbih0eXBlUXVlcnkuZXhwck5hbWUudGV4dCwgdGhpcy5jdXJyZW50UmVmZXJlbmNlZFR5cGVGaWxlKTtcblx0XHRcdFx0aWYgKHVuaW9uKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHVuaW9uO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ3Vua25vd24nO1xuXHRcdH1cblx0XHRkZWZhdWx0OlxuXHRcdFx0Ly8gRm9yIGNvbXBsZXggdHlwZXMsIHJldHVybiB0aGUgdGV4dCByZXByZXNlbnRhdGlvblxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdH1cblxuXHQvKipcblx0XHQqIEluZmVyIHJldHVybiB0eXBlIGZyb20gYSBtZXRob2QgZGVjbGFyYXRpb25cblx0XHQqIFVzZXMgZXhwbGljaXQgcmV0dXJuIHR5cGUgYW5ub3RhdGlvbiBvciBpbmZlcnMgZnJvbSByZXR1cm4gc3RhdGVtZW50c1xuXHRcdCovXG5cdHByaXZhdGUgaW5mZXJSZXR1cm5UeXBlIChtZXRob2Q6IHRzLk1ldGhvZERlY2xhcmF0aW9uLCBjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+KTogc3RyaW5nIHtcblx0XHQvLyBJZiBtZXRob2QgaGFzIGV4cGxpY2l0IHJldHVybiB0eXBlIGFubm90YXRpb24sIHVzZSBpdFxuXHRcdGlmIChtZXRob2QudHlwZSkge1xuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJUeXBlKG1ldGhvZC50eXBlKTtcblx0XHR9XG5cblx0XHQvLyBPdGhlcndpc2UsIHRyeSB0byBpbmZlciBmcm9tIHJldHVybiBzdGF0ZW1lbnRzIGluIHRoZSBtZXRob2QgYm9keVxuXHRcdGlmIChtZXRob2QuYm9keSkge1xuXHRcdFx0cmV0dXJuIHRoaXMuaW5mZXJSZXR1cm5UeXBlRnJvbUJvZHkobWV0aG9kLmJvZHksIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0fVxuXG5cdFx0cmV0dXJuICd1bmtub3duJztcblx0fVxuXG5cdC8qKlxuXHRcdCogSW5mZXIgcmV0dXJuIHR5cGUgYnkgYW5hbHl6aW5nIHJldHVybiBzdGF0ZW1lbnRzIGluIHRoZSBtZXRob2QgYm9keVxuXHRcdCovXG5cdHByaXZhdGUgaW5mZXJSZXR1cm5UeXBlRnJvbUJvZHkgKGJvZHk6IHRzLkJsb2NrLCBjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+KTogc3RyaW5nIHtcblx0XHRjb25zdCByZXR1cm5UeXBlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXG5cdFx0Y29uc3QgdmlzaXQgPSAobm9kZTogdHMuTm9kZSk6IHZvaWQgPT4ge1xuXHRcdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0XHRjb25zdCB0eXBlID0gdGhpcy5pbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIobm9kZS5leHByZXNzaW9uLCB1bmRlZmluZWQsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRcdGlmICh0eXBlICE9PSAndW5rbm93bicpIHtcblx0XHRcdFx0XHRyZXR1cm5UeXBlcy5hZGQodHlwZSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCB2aXNpdCk7XG5cdFx0fTtcblxuXHRcdHZpc2l0KGJvZHkpO1xuXG5cdFx0aWYgKHJldHVyblR5cGVzLnNpemUgPT09IDApIHtcblx0XHRcdHJldHVybiAndm9pZCc7XG5cdFx0fVxuXHRcdGlmIChyZXR1cm5UeXBlcy5zaXplID09PSAxKSB7XG5cdFx0XHRyZXR1cm4gQXJyYXkuZnJvbShyZXR1cm5UeXBlcylbIDAgXTtcblx0XHR9XG5cdFx0cmV0dXJuIEFycmF5LmZyb20ocmV0dXJuVHlwZXMpLmpvaW4oJyB8ICcpO1xuXHR9XG5cblx0LyoqXG5cdCAqIEluZmVyIHR5cGUgZnJvbSBpbml0aWFsaXplclxuXHQgKi9cblx0cHJpdmF0ZSBpbmZlclR5cGVGcm9tSW5pdGlhbGl6ZXIgKFxuXHRcdGluaXRpYWxpemVyOiB0cy5FeHByZXNzaW9uLFxuXHRcdGRhdGFUeXBlTWFwPzogTWFwPHN0cmluZywgc3RyaW5nPixcblx0XHRjbGFzc1Byb3BlcnR5VHlwZXM/OiBNYXA8c3RyaW5nLCBzdHJpbmc+XG5cdCk6IHN0cmluZyB7XG5cdFx0c3dpdGNoIChpbml0aWFsaXplci5raW5kKSB7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlN0cmluZ0xpdGVyYWw6XG5cdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk51bWVyaWNMaXRlcmFsOlxuXHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UcnVlS2V5d29yZDpcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuRmFsc2VLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICdib29sZWFuJztcblx0XHRjYXNlIHRzLlN5bnRheEtpbmQuTnVsbEtleXdvcmQ6XG5cdFx0XHRyZXR1cm4gJ251bGwnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5VbmRlZmluZWRLZXl3b3JkOlxuXHRcdFx0cmV0dXJuICd1bmRlZmluZWQnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5BcnJheUxpdGVyYWxFeHByZXNzaW9uOlxuXHRcdFx0cmV0dXJuICdBcnJheTx1bmtub3duPic7XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk9iamVjdExpdGVyYWxFeHByZXNzaW9uOlxuXHRcdFx0cmV0dXJuICdvYmplY3QnO1xuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5OZXdFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgbmV3IERhdGUoKSwgbmV3IE1hcCgpLCBldGMuXG5cdFx0XHRjb25zdCBuZXdFeHByID0gaW5pdGlhbGl6ZXIgYXMgdHMuTmV3RXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIobmV3RXhwci5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRyZXR1cm4gbmV3RXhwci5leHByZXNzaW9uLnRleHQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gJ29iamVjdCc7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5CaW5hcnlFeHByZXNzaW9uOiB7XG5cdFx0XHQvLyBIYW5kbGUgYXJpdGhtZXRpYyBvcGVyYXRpb25zOiBhICogYiwgYSArIGIsIGEgLSBiLCBhIC8gYlxuXHRcdFx0Y29uc3QgYmluYXJ5RXhwciA9IGluaXRpYWxpemVyIGFzIHRzLkJpbmFyeUV4cHJlc3Npb247XG5cdFx0XHRjb25zdCBsZWZ0VHlwZSA9IHRoaXMuaW5mZXJUeXBlRnJvbUluaXRpYWxpemVyKGJpbmFyeUV4cHIubGVmdCwgZGF0YVR5cGVNYXAsIGNsYXNzUHJvcGVydHlUeXBlcyk7XG5cdFx0XHRjb25zdCByaWdodFR5cGUgPSB0aGlzLmluZmVyVHlwZUZyb21Jbml0aWFsaXplcihiaW5hcnlFeHByLnJpZ2h0LCBkYXRhVHlwZU1hcCwgY2xhc3NQcm9wZXJ0eVR5cGVzKTtcblx0XHRcdFx0XG5cdFx0XHQvLyBDaGVjayBpZiBpdCdzIGFuIGFyaXRobWV0aWMgb3BlcmF0b3Jcblx0XHRcdGNvbnN0IG9wZXJhdG9yID0gYmluYXJ5RXhwci5vcGVyYXRvclRva2VuLmtpbmQ7XG5cdFx0XHRpZiAob3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuQXN0ZXJpc2tUb2tlbiB8fFxuXHRcdFx0XHQgICAgb3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuU2xhc2hUb2tlbiB8fFxuXHRcdFx0XHQgICAgb3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuTWludXNUb2tlbiB8fFxuXHRcdFx0XHQgICAgb3BlcmF0b3IgPT09IHRzLlN5bnRheEtpbmQuUGVyY2VudFRva2VuKSB7XG5cdFx0XHRcdC8vIEFyaXRobWV0aWMgb3BlcmF0aW9ucyBvbiBudW1iZXJzIHByb2R1Y2UgbnVtYmVyc1xuXHRcdFx0XHRpZiAoKGxlZnRUeXBlID09PSAnbnVtYmVyJyB8fCBsZWZ0VHlwZSA9PT0gJ3Vua25vd24nKSAmJlxuXHRcdFx0XHRcdCAgICAocmlnaHRUeXBlID09PSAnbnVtYmVyJyB8fCByaWdodFR5cGUgPT09ICd1bmtub3duJykpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ251bWJlcic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGlmIChvcGVyYXRvciA9PT0gdHMuU3ludGF4S2luZC5QbHVzVG9rZW4pIHtcblx0XHRcdFx0Ly8gUGx1cyBjYW4gYmUgYWRkaXRpb24gb3Igc3RyaW5nIGNvbmNhdGVuYXRpb25cblx0XHRcdFx0aWYgKGxlZnRUeXBlID09PSAnc3RyaW5nJyB8fCByaWdodFR5cGUgPT09ICdzdHJpbmcnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChsZWZ0VHlwZSA9PT0gJ251bWJlcicgJiYgcmlnaHRUeXBlID09PSAnbnVtYmVyJykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gSGFuZGxlIHByb3BlcnR5IGFjY2VzcyBsaWtlIGRhdGEudmFsdWUsIGRhdGEuaWRcblx0XHRcdGlmIChkYXRhVHlwZU1hcCkge1xuXHRcdFx0XHRjb25zdCBhY2Nlc3NDaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlBY2Nlc3NDaGFpbihpbml0aWFsaXplcik7XG5cdFx0XHRcdGlmIChhY2Nlc3NDaGFpbikge1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSBkYXRhVHlwZU1hcC5nZXQoYWNjZXNzQ2hhaW4pO1xuXHRcdFx0XHRcdGlmICh0eXBlKSB7XG5cdFx0XHRcdFx0XHRyZXR1cm4gdHlwZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIEhhbmRsZSB0aGlzLm1hcC5zaXplIHBhdHRlcm4gKE1hcC5zaXplIHJldHVybnMgbnVtYmVyKVxuXHRcdFx0Y29uc3QgcHJvcEFjY2VzcyA9IGluaXRpYWxpemVyIGFzIHRzLlByb3BlcnR5QWNjZXNzRXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihwcm9wQWNjZXNzLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdGNvbnN0IG91dGVyUHJvcCA9IHByb3BBY2Nlc3MuZXhwcmVzc2lvbjtcblx0XHRcdFx0Ly8gQ2hlY2sgZm9yIHRoaXMubWFwIHBhdHRlcm5cblx0XHRcdFx0bGV0IGlubmVyTmFtZSA9ICcnO1xuXHRcdFx0XHRpZiAob3V0ZXJQcm9wLmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdGlubmVyTmFtZSA9ICd0aGlzJztcblx0XHRcdFx0fSBlbHNlIGlmICh0cy5pc0lkZW50aWZpZXIob3V0ZXJQcm9wLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdFx0aW5uZXJOYW1lID0gb3V0ZXJQcm9wLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBtYXBQcm9wID0gb3V0ZXJQcm9wLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgZmluYWxQcm9wID0gcHJvcEFjY2Vzcy5uYW1lLnRleHQ7XG5cdFx0XHRcdC8vIHRoaXMubWFwLnNpemUgLT4gbnVtYmVyXG5cdFx0XHRcdGlmIChpbm5lck5hbWUgPT09ICd0aGlzJyAmJiBtYXBQcm9wID09PSAnbWFwJyAmJiBmaW5hbFByb3AgPT09ICdzaXplJykge1xuXHRcdFx0XHRcdHJldHVybiAnbnVtYmVyJztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0cmV0dXJuICd1bmtub3duJztcblx0XHR9XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLklkZW50aWZpZXI6IHtcblx0XHRcdC8vIEhhbmRsZSBpZGVudGlmaWVyIHJlZmVyZW5jZXMgaWYgaW4gZGF0YVR5cGVNYXBcblx0XHRcdGlmIChkYXRhVHlwZU1hcCkge1xuXHRcdFx0XHRjb25zdCBuYW1lID0gKGluaXRpYWxpemVyIGFzIHRzLklkZW50aWZpZXIpLnRleHQ7XG5cdFx0XHRcdGNvbnN0IHR5cGUgPSBkYXRhVHlwZU1hcC5nZXQobmFtZSk7XG5cdFx0XHRcdGlmICh0eXBlKSB7XG5cdFx0XHRcdFx0cmV0dXJuIHR5cGU7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5DYWxsRXhwcmVzc2lvbjoge1xuXHRcdFx0Ly8gSGFuZGxlIGZ1bmN0aW9uIGNhbGxzIGxpa2UgRGF0ZS5ub3coKSwgcGFyc2VJbnQoKSwgZXRjLlxuXHRcdFx0Y29uc3QgY2FsbEV4cHIgPSBpbml0aWFsaXplciBhcyB0cy5DYWxsRXhwcmVzc2lvbjtcblx0XHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihjYWxsRXhwci5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBtZXRob2ROYW1lID0gY2FsbEV4cHIuZXhwcmVzc2lvbi5uYW1lLnRleHQ7XG5cdFx0XHRcdGNvbnN0IG9iak5hbWUgPSB0cy5pc0lkZW50aWZpZXIoY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uKVxuXHRcdFx0XHRcdD8gY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uLnRleHRcblx0XHRcdFx0XHQ6ICcnO1xuXHRcdFx0XHRcdFxuXHRcdFx0XHQvLyBEYXRlLm5vdygpIC0+IG51bWJlclxuXHRcdFx0XHRpZiAob2JqTmFtZSA9PT0gJ0RhdGUnICYmIG1ldGhvZE5hbWUgPT09ICdub3cnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIFN0cmluZyBtZXRob2RzIHRoYXQgcmV0dXJuIHN0cmluZ1xuXHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3RvU3RyaW5nJyB8fCBtZXRob2ROYW1lID09PSAndmFsdWVPZicpIHtcblx0XHRcdFx0XHRyZXR1cm4gJ3N0cmluZyc7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gSGFuZGxlIE1hcCBwcm9wZXJ0eSBhY2Nlc3Mgb24gY2xhc3MgaW5zdGFuY2VzICh0aGlzLm1hcC4qKVxuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oY2FsbEV4cHIuZXhwcmVzc2lvbi5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdGNvbnN0IG91dGVyUHJvcCA9IGNhbGxFeHByLmV4cHJlc3Npb24uZXhwcmVzc2lvbjtcblx0XHRcdFx0XHQvLyBIYW5kbGUgYm90aCAndGhpcycga2V5d29yZCBhbmQgaWRlbnRpZmllciBwYXR0ZXJuc1xuXHRcdFx0XHRcdGxldCBpbm5lck5hbWUgPSAnJztcblx0XHRcdFx0XHRpZiAob3V0ZXJQcm9wLmV4cHJlc3Npb24ua2luZCA9PT0gdHMuU3ludGF4S2luZC5UaGlzS2V5d29yZCkge1xuXHRcdFx0XHRcdFx0aW5uZXJOYW1lID0gJ3RoaXMnO1xuXHRcdFx0XHRcdH0gZWxzZSBpZiAodHMuaXNJZGVudGlmaWVyKG91dGVyUHJvcC5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdFx0aW5uZXJOYW1lID0gb3V0ZXJQcm9wLmV4cHJlc3Npb24udGV4dDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Y29uc3QgbWFwUHJvcCA9IG91dGVyUHJvcC5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Ly8gdGhpcy5tYXAuWCgpIHBhdHRlcm5zXG5cdFx0XHRcdFx0aWYgKGlubmVyTmFtZSA9PT0gJ3RoaXMnICYmIG1hcFByb3AgPT09ICdtYXAnKSB7XG5cdFx0XHRcdFx0XHQvLyBUcnkgdG8gZ2V0IHRoZSBNYXAncyB2YWx1ZSB0eXBlIGZyb20gY2xhc3MgcHJvcGVydGllc1xuXHRcdFx0XHRcdFx0bGV0IG1hcFZhbHVlVHlwZSA9ICd1bmtub3duJztcblx0XHRcdFx0XHRcdGlmIChjbGFzc1Byb3BlcnR5VHlwZXMpIHtcblx0XHRcdFx0XHRcdFx0Y29uc3QgbWFwVHlwZSA9IGNsYXNzUHJvcGVydHlUeXBlcy5nZXQoJ21hcCcpO1xuXHRcdFx0XHRcdFx0XHRpZiAobWFwVHlwZSAmJiBtYXBUeXBlLnN0YXJ0c1dpdGgoJ01hcDwnKSkge1xuXHRcdFx0XHRcdFx0XHRcdC8vIFBhcnNlIE1hcDxLLCBWPiB0byBnZXQgVlxuXHRcdFx0XHRcdFx0XHRcdGNvbnN0IG1hdGNoID0gbWFwVHlwZS5tYXRjaCgvTWFwPFteLF0rLFxccyooLispPiQvKTtcblx0XHRcdFx0XHRcdFx0XHRpZiAobWF0Y2gpIHtcblx0XHRcdFx0XHRcdFx0XHRcdFsgLCBtYXBWYWx1ZVR5cGUgXSA9IG1hdGNoO1xuXHRcdFx0XHRcdFx0XHRcdH1cblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdoYXMnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdzZXQnKSByZXR1cm4gJ3RoaXMnO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdnZXQnKSByZXR1cm4gbWFwVmFsdWVUeXBlO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdkZWxldGUnKSByZXR1cm4gJ2Jvb2xlYW4nO1xuXHRcdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdjbGVhcicpIHJldHVybiAndm9pZCc7XG5cdFx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3ZhbHVlcycpIHJldHVybiBgSXRlcmFibGVJdGVyYXRvcjwke21hcFZhbHVlVHlwZX0+YDtcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAna2V5cycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjxzdHJpbmc+Jztcblx0XHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZW50cmllcycpIHJldHVybiBgSXRlcmFibGVJdGVyYXRvcjxbc3RyaW5nLCAke21hcFZhbHVlVHlwZX1dPmA7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHRcdC8vIERpcmVjdCBtYXAuWCgpIGNhbGxzXG5cdFx0XHRcdGlmIChvYmpOYW1lID09PSAnbWFwJyB8fCBvYmpOYW1lID09PSAnb2JqJykge1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnaGFzJykgcmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3NldCcpIHJldHVybiAndGhpcyc7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdnZXQnKSByZXR1cm4gJ3Vua25vd24nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZGVsZXRlJykgcmV0dXJuICdib29sZWFuJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2NsZWFyJykgcmV0dXJuICd2b2lkJztcblx0XHRcdFx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ3ZhbHVlcycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjx1bmtub3duPic7XG5cdFx0XHRcdFx0aWYgKG1ldGhvZE5hbWUgPT09ICdrZXlzJykgcmV0dXJuICdJdGVyYWJsZUl0ZXJhdG9yPHN0cmluZz4nO1xuXHRcdFx0XHRcdGlmIChtZXRob2ROYW1lID09PSAnZW50cmllcycpIHJldHVybiAnSXRlcmFibGVJdGVyYXRvcjxbc3RyaW5nLCB1bmtub3duXT4nO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBwYXJzZUludCwgcGFyc2VGbG9hdCAtPiBudW1iZXJcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoY2FsbEV4cHIuZXhwcmVzc2lvbikpIHtcblx0XHRcdFx0Y29uc3QgZm5OYW1lID0gY2FsbEV4cHIuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0XHRpZiAoZm5OYW1lID09PSAncGFyc2VJbnQnIHx8IGZuTmFtZSA9PT0gJ3BhcnNlRmxvYXQnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdTdHJpbmcnKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdzdHJpbmcnO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdOdW1iZXInKSB7XG5cdFx0XHRcdFx0cmV0dXJuICdudW1iZXInO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmbk5hbWUgPT09ICdCb29sZWFuJykge1xuXHRcdFx0XHRcdHJldHVybiAnYm9vbGVhbic7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHRcdGNhc2UgdHMuU3ludGF4S2luZC5UZW1wbGF0ZUV4cHJlc3Npb246XG5cdFx0Y2FzZSB0cy5TeW50YXhLaW5kLk5vU3Vic3RpdHV0aW9uVGVtcGxhdGVMaXRlcmFsOiB7XG5cdFx0XHQvLyBUZW1wbGF0ZSBsaXRlcmFscyBsaWtlIGAke2Jhc2VWYWx1ZX0tJHtleHRyYX1gIGFsd2F5cyBwcm9kdWNlIHN0cmluZ3Ncblx0XHRcdHJldHVybiAnc3RyaW5nJztcblx0XHR9XG5cdFx0ZGVmYXVsdDpcblx0XHRcdHJldHVybiAndW5rbm93bic7XG5cdFx0fVxuXHR9XG5cdFxuXHQvKipcblx0XHRcdCogQ29sbGVjdCB1c2FnZSBpbmZvcm1hdGlvbiBmb3IgdHlwZSByZWZlcmVuY2VzXG5cdFx0XHQqL1xuXHRwcml2YXRlIGNvbGxlY3RVc2FnZSAobm9kZTogdHMuTm9kZSwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdC8vIENoZWNrIGZvciBuZXcgVHlwZSgpIGluc3RhbnRpYXRpb25cblx0XHRpZiAodHMuaXNOZXdFeHByZXNzaW9uKG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0bGV0IHR5cGVOYW1lOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdFx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obm9kZS5leHByZXNzaW9uKSkge1xuXHRcdFx0XHR0eXBlTmFtZSA9IHRoaXMucmVzb2x2ZVR5cGVQYXRoKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHR0eXBlTmFtZSA9IHRoaXMuZ2V0VHlwZU5hbWVGcm9tRXhwcmVzc2lvbihub2RlLmV4cHJlc3Npb24pO1xuXHRcdFx0fVxuXHRcdFx0aWYgKHR5cGVOYW1lKSB7XG5cdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0dGhpcy5hZGRVc2FnZSh0eXBlTmFtZSwge1xuXHRcdFx0XHRcdGxvY2F0aW9uICAgICAgICA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdGtpbmQgICAgICAgICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRjb2RlICAgICAgICAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHQvLyBDb25zdHJ1Y3RvciBleHByZXNzaW9uIHRleHQgKCdUaGluZycsICd1c2VyLkFkbWluRW50aXR5Jyxcblx0XHRcdFx0XHQvLyBhIGxvb2t1cCBhbGlhcykg4oCUIENyZWF0aW9uQW5jaG9yLmNvbnN0cnVjdG9yVGV4dCAoUGhhc2UgMylcblx0XHRcdFx0XHRjb25zdHJ1Y3RvclRleHQgOiBub2RlLmV4cHJlc3Npb24uZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHR9KTtcblx0XHRcdFx0Ly8gVHJhY2sgdmFyaWFibGUgYXNzaWdubWVudCBmcm9tIG5ldyBUeXBlKCkgZm9yIGZsb3cgYW5hbHlzaXNcblx0XHRcdFx0dGhpcy50cmFja05ld0Fzc2lnbm1lbnQobm9kZSwgdHlwZU5hbWUpO1xuXHRcdFx0XHQvLyBBbHNvIHJlY29yZCBhcyBmbG93IGV2ZW50XG5cdFx0XHRcdHRoaXMuYWRkRmxvdyh0eXBlTmFtZSwge1xuXHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0a2luZCAgICAgOiAnaW5zdGFudGlhdGlvbicsXG5cdFx0XHRcdFx0Y29kZSAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRjb250ZXh0ICA6ICduZXcgZXhwcmVzc2lvbicsXG5cdFx0XHRcdH0pO1xuXHRcdFx0fVxuXHRcdH1cblx0XG5cdFx0Ly8gQ2hlY2sgZm9yIHByb3BlcnR5IGFjY2VzcyBvbiBpbnN0YW5jZXMgKHVzZXIuQWRtaW5UeXBlKVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRcdC8vIGluc3RhbmNlLmNsb25lIOKAlCB0aGUgUFJPUEVSVFkgZm9ybSAoY29yZSB0eXBlcyBpdFxuXHRcdFx0Ly8gYHJlYWRvbmx5IGNsb25lOiB0aGlzYCk6IHRoZSByZXN1bHQgdmFyaWFibGUgYmluZHMgdG8gdGhlXG5cdFx0XHQvLyBzb3VyY2UgaW5zdGFuY2UncyB0eXBlLCBzYW1lIGFzIHRoZSBmb3JrKCkvY2xvbmUoKSBjYWxsXG5cdFx0XHQvLyBmb3JtcyAoYXdhaXQtdHJhbnNwYXJlbnQpLiBUaGUgY2FsbCBmb3JtJ3MgcmVjb3JkaW5nIGhhcHBlbnNcblx0XHRcdC8vIGluIHRoZSBDYWxsRXhwcmVzc2lvbiBicmFuY2g7IHRoZSBwcm9wZXJ0eSBicmFuY2ggc2tpcHMgaXRcblx0XHRcdC8vIHRvIGF2b2lkIGEgZHVwbGljYXRlIGVudHJ5IGF0IHRoZSBzYW1lIHNpdGVcblx0XHRcdGlmIChwcm9wTmFtZSA9PT0gJ2Nsb25lJyAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjb25zdCBjbG9uZWRQYXRoID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQobm9kZS5leHByZXNzaW9uLnRleHQpO1xuXHRcdFx0XHRjb25zdCBpc0NhbGxGb3JtID0gdHMuaXNDYWxsRXhwcmVzc2lvbihub2RlLnBhcmVudCkgJiYgbm9kZS5wYXJlbnQuZXhwcmVzc2lvbiA9PT0gbm9kZTtcblx0XHRcdFx0aWYgKGNsb25lZFBhdGgpIHtcblx0XHRcdFx0XHRpZiAoIWlzQ2FsbEZvcm0pIHtcblx0XHRcdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHRcdFx0KTtcblx0XHRcdFx0XHRcdHRoaXMuYWRkVXNhZ2UoY2xvbmVkUGF0aCwge1xuXHRcdFx0XHRcdFx0XHRsb2NhdGlvbiAgICAgICAgOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRcdFx0a2luZCAgICAgICAgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0XHRcdFx0XHRjb2RlICAgICAgICAgICAgOiBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKSxcblx0XHRcdFx0XHRcdFx0Y29uc3RydWN0b3JUZXh0IDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0dGhpcy5iaW5kUmVzdWx0VmFyaWFibGUobm9kZSwgY2xvbmVkUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdC8vIENoZWNrIGlmIHRoaXMgbG9va3MgbGlrZSBhIHR5cGUgYWNjZXNzIHBhdHRlcm5cblx0XHRcdGlmIChwcm9wTmFtZSAmJiB0aGlzLmlzTGlrZWx5VHlwZU5hbWUocHJvcE5hbWUpKSB7XG5cdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdFx0KTtcblx0XHRcdFx0XHQvLyBUcnkgdG8gcmVzb2x2ZSBmdWxsIHBhdGhcblx0XHRcdFx0Y29uc3QgZnVsbFBhdGggPSB0aGlzLnJlc29sdmVUeXBlUGF0aChub2RlKTtcblx0XHRcdFx0aWYgKGZ1bGxQYXRoKSB7XG5cdFx0XHRcdFx0dGhpcy5hZGRVc2FnZShmdWxsUGF0aCwge1xuXHRcdFx0XHRcdFx0bG9jYXRpb24gOiBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCxcblx0XHRcdFx0XHRcdGtpbmQgICAgIDogJ3Byb3BlcnR5QWNjZXNzJyxcblx0XHRcdFx0XHRcdGNvZGUgICAgIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdFxuXHRcdC8vIENoZWNrIGZvciBsb29rdXAoJ1R5cGVOYW1lJykgb3IgbG9va3VwKHNvdXJjZSwgJ1R5cGVOYW1lJykgY2FsbHNcblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdGNvbnN0IGZ1bmNOYW1lID0gdGhpcy5nZXRGdW5jdGlvbk5hbWUobm9kZS5leHByZXNzaW9uKTtcblx0XHRcdGlmIChmdW5jTmFtZSA9PT0gJ2xvb2t1cCcgJiYgbm9kZS5hcmd1bWVudHMubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRjb25zdCB0eXBlUGF0aCA9IHRoaXMucmVzb2x2ZUxvb2t1cFBhdGgobm9kZSk7XG5cdFx0XHRcdGlmICh0eXBlUGF0aCkge1xuXHRcdFx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHRcdFx0KTtcblx0XHRcdFx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0XHRcdHRoaXMuYWRkVXNhZ2UodHlwZVBhdGgsIHtcblx0XHRcdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRcdFx0a2luZCA6ICdsb29rdXAnLFxuXHRcdFx0XHRcdFx0Y29kZSA6IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHRcdC8vIFRyYWNrIHZhcmlhYmxlIGFzc2lnbm1lbnQgZnJvbSBsb29rdXAgZm9yIGluc3RhbnRpYXRpb24gdHJhY2tpbmdcblx0XHRcdFx0XHR0aGlzLnRyYWNrTG9va3VwQXNzaWdubWVudChub2RlLCB0eXBlUGF0aCk7XG5cdFx0XHRcdFx0Ly8gUmVjb3JkIGZvciB0aGUgaGFyZC1mYWlsIGxhdyBldmVuIHdoZW4gYWRkVXNhZ2UgZHJvcHBlZFxuXHRcdFx0XHRcdC8vIHRoZSBwYXRoICh1bmtub3duIHBhdGhzIGFyZSBleGFjdGx5IHRoZSBmYWlsdXJlIGNsYXNzKVxuXHRcdFx0XHRcdHRoaXMubG9va3VwUmVmZXJlbmNlcy5wdXNoKHsgcGF0aCA6IHR5cGVQYXRoLCBsb2NhdGlvbiB9KTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHQvLyBDaGFpbi1mb3JtIGNvbnN0cnVjdGlvbjogYG5ldyBSKC4uLikuQSguLi4pYCAvIHRoZSBhd2FpdGVkXG5cdFx0XHQvLyBzaW5nbGUtY2hhaW4gYGF3YWl0IG5ldyBSKC4uLikuQSguLi4pLkIoLi4uKWAg4oCUIHRoZSBjYWxsIG9uXG5cdFx0XHQvLyB0aGUgZnJlc2ggaW5zdGFuY2UgY29uc3RydWN0cyB0aGUgY2hhaW4gVElQIChhd2FpdCBpc1xuXHRcdFx0Ly8gdHJhbnNwYXJlbnQ7IHRoZSBOZXdFeHByZXNzaW9uIGJyYW5jaCBhbHJlYWR5IHJlY29yZGVkIHRoZVxuXHRcdFx0Ly8gaW5uZXIgcm9vdCkuIFRoZSByZXN1bHQgdmFyaWFibGUgYmluZHMgdG8gdGhlIHRpcCwgbm90IHRoZVxuXHRcdFx0Ly8gcm9vdCAodHJhY2tOZXdBc3NpZ25tZW50IHJlc29sdmVzIHRoZSBzYW1lIHRpcClcblx0XHRcdGNvbnN0IGNoYWluVGlwID0gdGhpcy5yZXNvbHZlQ2hhaW5UaXBUeXBlUGF0aChub2RlKTtcblx0XHRcdGlmIChjaGFpblRpcCkge1xuXHRcdFx0XHR0aGlzLnJlY29yZENvbnN0cnVjdGlvblVzYWdlKG5vZGUsIGNoYWluVGlwLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHQpO1xuXHRcdFx0XHR0aGlzLmFkZEZsb3coY2hhaW5UaXAsIHtcblx0XHRcdFx0XHRsb2NhdGlvbiA6IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gLFxuXHRcdFx0XHRcdGtpbmQgICAgIDogJ2luc3RhbnRpYXRpb24nLFxuXHRcdFx0XHRcdGNvZGUgICAgIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0Y29udGV4dCAgOiAnY2hhaW5lZCBjb25zdHJ1Y3Rpb24nLFxuXHRcdFx0XHR9KTtcblx0XHRcdH1cblxuXHRcdFx0Ly8gbW5lbW9uaWNhIGNhbGwvYXBwbHkoZW50aXR5LCBDdG9yLCAuLi4pIC8gYmluZChlbnRpdHksIEN0b3IpIOKAlFxuXHRcdFx0Ly8gdHlwZWQgY29uc3RydWN0aW9uIHdpdGhvdXQgYG5ld2A6IHRoZSBDdG9yIGFyZ3VtZW50IChhcmcgMSkgaXNcblx0XHRcdC8vIHRoZSBjb25zdHJ1Y3RlZCB0eXBlLiBJbXBvcnQtYXdhcmU6IG9ubHkgaWRlbnRpZmllcnMgYWN0dWFsbHlcblx0XHRcdC8vIGltcG9ydGVkIGZyb20gJ21uZW1vbmljYScgKG9yIG1lbWJlcnMgb2YgYSB0cmFja2VkXG5cdFx0XHQvLyBtb2R1bGUtb2JqZWN0IGFsaWFzKSBtYXRjaCDigJQgdXNlcmxhbmQgY2FsbC9hcHBseS9iaW5kIG5ldmVyXG5cdFx0XHQvLyBkby4gY2FsbC9hcHBseSByZWNvcmQgdGhlIGNvbnN0cnVjdGlvbjsgYmluZCgpIGNvbnN0cnVjdHNcblx0XHRcdC8vIG5vdGhpbmcg4oCUIGl0IG9ubHkgYmluZHMgdGhlIHJlc3VsdCB2YXJpYWJsZSB0byB0aGUgQ3RvcidzXG5cdFx0XHQvLyB0eXBlIChydW50aW1lIEluc3RhbmNlUmVzdWx0PE1lcmdlPEUsVD4+IGFwcHJveGltYXRlZCBieSBUXG5cdFx0XHQvLyB3aXRoaW4gdGhlIG91dHB1dCBjb250cmFjdClcblx0XHRcdGNvbnN0IGNvbnN0cnVjdGlvblBhdGggPSB0aGlzLnJlc29sdmVDb25zdHJ1Y3Rpb25GblR5cGVQYXRoKG5vZGUpO1xuXHRcdFx0aWYgKGNvbnN0cnVjdGlvblBhdGgpIHtcblx0XHRcdFx0Y29uc3QgaXNCaW5kRm9ybSA9IHRoaXMuaXNNbmVtb25pY2FDb25zdHJ1Y3Rpb25Gbihub2RlLmV4cHJlc3Npb24sICdiaW5kJyk7XG5cdFx0XHRcdGlmICghaXNCaW5kRm9ybSkge1xuXHRcdFx0XHRcdGNvbnN0IGN0b3JBcmdUZXh0ID0gbm9kZS5hcmd1bWVudHNbIDEgXT8uZ2V0VGV4dChzb3VyY2VGaWxlKTtcblx0XHRcdFx0XHR0aGlzLnJlY29yZENvbnN0cnVjdGlvblVzYWdlKG5vZGUsIGNvbnN0cnVjdGlvblBhdGgsIHNvdXJjZUZpbGUsIGN0b3JBcmdUZXh0KTtcblx0XHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHRcdCk7XG5cdFx0XHRcdFx0dGhpcy5hZGRGbG93KGNvbnN0cnVjdGlvblBhdGgsIHtcblx0XHRcdFx0XHRcdGxvY2F0aW9uIDogYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWAsXG5cdFx0XHRcdFx0XHRraW5kICAgICA6ICdpbnN0YW50aWF0aW9uJyxcblx0XHRcdFx0XHRcdGNvZGUgICAgIDogbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCksXG5cdFx0XHRcdFx0XHRjb250ZXh0ICA6ICdjYWxsL2FwcGx5IGNvbnN0cnVjdGlvbicsXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdFx0dGhpcy5iaW5kUmVzdWx0VmFyaWFibGUobm9kZSwgY29uc3RydWN0aW9uUGF0aCk7XG5cdFx0XHR9XG5cblx0XHRcdC8vIGluc3RhbmNlLmZvcmsoKS9jbG9uZSgpIOKAlCBydW50aW1lIHJlLXJ1bnMgY29uc3RydWN0aW9uIChob29rc1xuXHRcdFx0Ly8gZmlyZSwgYSBkaXN0aW5jdCBpbnN0YW5jZSBvbiBhIGRpc3RpbmN0IGxpbmUpLCBzbyBhblxuXHRcdFx0Ly8gYGluc3RhbnRpYXRpb25gIHVzYWdlIHJlY29yZHMgdGhlIHNpdGUgSU4gQURESVRJT04gdG8gdGhlXG5cdFx0XHQvLyByZXN1bHQtdmFyIGJpbmRpbmcgYW5kIHRoZSBnZW5lcmljIG1ldGhvZENhbGwgZmxvdyAodGhlIGVudHJ5XG5cdFx0XHQvLyBpcyBieXRlLWluZGlzdGluZ3Vpc2hhYmxlIGZyb20gYG5ld2AgdW50aWwgdGhlIGRlZmVycmVkXG5cdFx0XHQvLyBtZWNoYW5pc20ta2luZCByZXZpc2lvbiDigJQgdGhlIG93bmVyJ3MgZXhwbGljaXQgY2FsbCkuIEZyZWVcblx0XHRcdC8vIHV0aWxzLm1lcmdlKGEsIGIsIC4uLikgLyB1dGlscy5mb3JrKGluc3RhbmNlKSguLi4pIGFyZVxuXHRcdFx0Ly8gY29uc3RydWN0aW9uIG9mIGEncyB0eXBlIHRvbyAobWVyZ2UgPSBmb3JrKGEpIG92ZXIgYidzXG5cdFx0XHQvLyBjb250ZXh0KTsgdGhlIHJlc3VsdCBiaW5kaW5nIGtlZXBzIHRoZSBkb2N1bWVudGVkIGFyZy0wXG5cdFx0XHQvLyBhcHByb3hpbWF0aW9uXG5cdFx0XHRjb25zdCBmb3JrTGlrZVBhdGggPSB0aGlzLnJlc29sdmVGb3JrTGlrZVR5cGVQYXRoKG5vZGUpO1xuXHRcdFx0aWYgKGZvcmtMaWtlUGF0aCkge1xuXHRcdFx0XHR0aGlzLnJlY29yZENvbnN0cnVjdGlvblVzYWdlKG5vZGUsIGZvcmtMaWtlUGF0aCwgc291cmNlRmlsZSk7XG5cdFx0XHRcdHRoaXMuYmluZFJlc3VsdFZhcmlhYmxlKG5vZGUsIGZvcmtMaWtlUGF0aCk7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCB1dGlsc1BhdGggPSB0aGlzLnJlc29sdmVVdGlsc0ZuVHlwZVBhdGgobm9kZSk7XG5cdFx0XHRpZiAodXRpbHNQYXRoKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkQ29uc3RydWN0aW9uVXNhZ2Uobm9kZSwgdXRpbHNQYXRoLCBzb3VyY2VGaWxlKTtcblx0XHRcdFx0dGhpcy5iaW5kUmVzdWx0VmFyaWFibGUobm9kZSwgdXRpbHNQYXRoKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0KiBHZXQgZnVuY3Rpb24gbmFtZSBmcm9tIGV4cHJlc3Npb24gKGlkZW50aWZpZXIgb3IgcHJvcGVydHkgYWNjZXNzKVxuXHRcdFx0Ki9cblx0cHJpdmF0ZSBnZXRGdW5jdGlvbk5hbWUgKGV4cHI6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcikpIHtcblx0XHRcdHJldHVybiBleHByLnRleHQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0cmV0dXJuIGV4cHIubmFtZS50ZXh0O1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cdFxuXHQvKipcblx0XHRcdCogQWRkIGEgdXNhZ2UgdG8gdGhlIGNvbGxlY3Rpb25cblx0XHRcdCovXG5cdHByaXZhdGUgYWRkVXNhZ2UgKHR5cGVQYXRoOiBzdHJpbmcsIHVzYWdlOiBVc2FnZUluZm8pOiB2b2lkIHtcblx0XHQvLyBPbmx5IHRyYWNrIHVzYWdlcyBvZiBtbmVtb25pY2EtZGVmaW5lZCB0eXBlc1xuXHRcdGlmICghdGhpcy5kZWZpbml0aW9ucy5oYXModHlwZVBhdGgpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGlmICghdGhpcy51c2FnZXMuaGFzKHR5cGVQYXRoKSkge1xuXHRcdFx0dGhpcy51c2FnZXMuc2V0KHR5cGVQYXRoLCBbXSk7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZm9yIGR1cGxpY2F0ZXMgYmFzZWQgb24gbG9jYXRpb24sIGNvZGUsIGFuZCBraW5kXG5cdFx0Y29uc3QgZXhpc3RpbmdVc2FnZXMgPSB0aGlzLnVzYWdlcy5nZXQodHlwZVBhdGgpITtcblx0XHRjb25zdCBpc0R1cGxpY2F0ZSA9IGV4aXN0aW5nVXNhZ2VzLnNvbWUoZXhpc3RpbmcgPT5cblx0XHRcdGV4aXN0aW5nLmxvY2F0aW9uID09PSB1c2FnZS5sb2NhdGlvbiAmJlxuXHRcdFx0XHRleGlzdGluZy5jb2RlID09PSB1c2FnZS5jb2RlICYmXG5cdFx0XHRcdGV4aXN0aW5nLmtpbmQgPT09IHVzYWdlLmtpbmQpO1xuXG5cdFx0aWYgKCFpc0R1cGxpY2F0ZSkge1xuXHRcdFx0ZXhpc3RpbmdVc2FnZXMucHVzaCh1c2FnZSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgRURTIChFeGVjdXRpb24gRGF0YSBTdG9yYWdlKSB1c2FnZSBpbmZvcm1hdGlvblxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0RURTIChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpIHx8ICFub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCBmdW5jTmFtZSA9IHRoaXMuZ2V0RnVuY3Rpb25OYW1lKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0aWYgKCFmdW5jTmFtZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblx0XHQvLyBFbmNsb3NpbmcgbW5lbW9uaWNhIHR5cGUgcGF0aCDigJQgd3JhcCBhcmdzIGFyZSB1c3VhbGx5IGxvY2FsXG5cdFx0Ly8gZnVuY3Rpb25zLCBzbyB0aGUgb3duaW5nIGRlZmluZSgpL2xhenkoKSBoYW5kbGVyIG9yIGRlY29yYXRlZFxuXHRcdC8vIGNsYXNzIGlzIHdoYXQgZWRzLmpzb24gY29uc3VtZXJzIChHcmFwaEJ1aWxkZXIpIGNhbiBqb2luIG9uLlxuXHRcdGNvbnN0IHNjb3BlID0gdGhpcy5yZXNvbHZlRURTU2NvcGUobm9kZSk7XG5cblx0XHQvLyB3cmFwKGZuKSwgd3JhcENvbnN0cnVjdG9yQXJnKGZuLCBwYXJlbnQpLCB1cGdyYWRlQ29uc3RydWN0b3JBcmcoYXJnLCBpbnN0KSwgd3JhcEluc3RhbmNlTWV0aG9kcyhvYmopXG5cdFx0aWYgKFxuXHRcdFx0ZnVuY05hbWUgPT09ICd3cmFwJyB8fFxuXHRcdFx0ZnVuY05hbWUgPT09ICd3cmFwQ29uc3RydWN0b3JBcmcnIHx8XG5cdFx0XHRmdW5jTmFtZSA9PT0gJ3VwZ3JhZGVDb25zdHJ1Y3RvckFyZycgfHxcblx0XHRcdGZ1bmNOYW1lID09PSAnd3JhcEluc3RhbmNlTWV0aG9kcydcblx0XHQpIHtcblx0XHRcdGNvbnN0IHRhcmdldFR5cGUgPSB0aGlzLnJlc29sdmVFRFNBcmd1bWVudFR5cGUobm9kZS5hcmd1bWVudHNbIDAgXSk7XG5cdFx0XHQvLyBkaXZlJ3Mgd3JhcC1mYW1pbHkgc2lnbmF0dXJlcyAoZGl2ZS9zcmMvaW5kZXgudHMpOlxuXHRcdFx0Ly8gICB3cmFwKGZuLCBsYWJlbD8pIHwgd3JhcChmbiwgY29udGV4dD8sIGxhYmVsPylcblx0XHRcdC8vICAgd3JhcENvbnN0cnVjdG9yQXJnKGZuLCBjb250ZXh0KVxuXHRcdFx0Ly8gICB1cGdyYWRlQ29uc3RydWN0b3JBcmcoYXJnLCBpbnN0YW5jZSlcblx0XHRcdC8vICAgd3JhcEluc3RhbmNlTWV0aG9kcyhpbnN0YW5jZSlcblx0XHRcdC8vIOKApnNvIHRoZSBpbnN0YW5jZS9jb250ZXh0IGFyZyBzaXRzIGF0IGFyZ3NbMV0gKGFyZ3NbMF0gZm9yXG5cdFx0XHQvLyB3cmFwSW5zdGFuY2VNZXRob2RzKSBhbmQgYSBzdHJpbmcgbGl0ZXJhbCBpbiBhcmdzWzEuLjJdIGlzIHRoZSBsYWJlbFxuXHRcdFx0Y29uc3QgaW5zdGFuY2VBcmdOb2RlID0gZnVuY05hbWUgPT09ICd3cmFwSW5zdGFuY2VNZXRob2RzJ1xuXHRcdFx0XHQ/IG5vZGUuYXJndW1lbnRzWyAwIF1cblx0XHRcdFx0OiBub2RlLmFyZ3VtZW50c1sgMSBdO1xuXHRcdFx0Ly8gRmlyZS1hbmQtZm9yZ2V0IHdyYXBwZXJzICh3aXJlLXVwIGhlbHBlcnMsIHJlZ2lzdHJhdGlvblxuXHRcdFx0Ly8gZnVuY3Rpb25zKSBzaXQgb3V0c2lkZSBhbnkgZGVmaW5lKCkvbGF6eSgpIGhhbmRsZXIsIHNvIHRoZVxuXHRcdFx0Ly8gbGV4aWNhbCBzY29wZSBpcyBhYnNlbnQg4oCUIGF0dHJpYnV0ZSB0aHJvdWdoIHRoZSBpbnN0YW5jZS9jb250ZXh0XG5cdFx0XHQvLyBhcmd1bWVudCBpbnN0ZWFkOiBhIHRyYWNrZWQgYXNzaWdubWVudCwgZWxzZSB0aGUgZW5jbG9zaW5nXG5cdFx0XHQvLyBmdW5jdGlvbidzIHBhcmFtZXRlciBhbm5vdGF0aW9uIHJlc29sdmVkIHRocm91Z2ggdGhlIGdyYXBoIGxhd1xuXHRcdFx0Y29uc3QgaW5zdGFuY2VUeXBlUGF0aCA9IGluc3RhbmNlQXJnTm9kZVxuXHRcdFx0XHQ/IHRoaXMucmVzb2x2ZVdyYXBJbnN0YW5jZVR5cGVQYXRoKGluc3RhbmNlQXJnTm9kZSlcblx0XHRcdFx0OiB1bmRlZmluZWQ7XG5cdFx0XHRjb25zdCBlZmZlY3RpdmVTY29wZSA9IHNjb3BlID8/IGluc3RhbmNlVHlwZVBhdGg7XG5cdFx0XHRjb25zdCBpbmZvOiBFRFNJbmZvID0ge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCAgICAgICA6ICd3cmFwJyxcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0dGFyZ2V0VHlwZSA6IHRhcmdldFR5cGUgfHwgdW5kZWZpbmVkLFxuXHRcdFx0XHRzY29wZSAgICAgIDogZWZmZWN0aXZlU2NvcGUsXG5cdFx0XHRcdGZuICAgICAgICAgOiBmdW5jTmFtZSxcblx0XHRcdH07XG5cdFx0XHRpZiAoaW5zdGFuY2VBcmdOb2RlICYmIHRzLmlzSWRlbnRpZmllcihpbnN0YW5jZUFyZ05vZGUpKSB7XG5cdFx0XHRcdGluZm8uaW5zdGFuY2VBcmcgPSBpbnN0YW5jZUFyZ05vZGUudGV4dDtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3QgZXh0cmFBcmcgb2YgWyBub2RlLmFyZ3VtZW50c1sgMSBdLCBub2RlLmFyZ3VtZW50c1sgMiBdIF0pIHtcblx0XHRcdFx0aWYgKGV4dHJhQXJnICYmIHRzLmlzU3RyaW5nTGl0ZXJhbChleHRyYUFyZykpIHtcblx0XHRcdFx0XHRpbmZvLmxhYmVsID0gZXh0cmFBcmcudGV4dDtcblx0XHRcdFx0XHRicmVhaztcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0Ly8gQSB3cmFwKCkgY2FsbCBuZXN0ZWQgaW5zaWRlIGFub3RoZXIgd3JhcHBlZCBib2R5IGNhcnJpZXMgdGhlXG5cdFx0XHQvLyBsaW5rIHRvIHRoZSBzaXRlIHdob3NlIHJ1bnRpbWUgd3JhcHBpbmcgY2F1c2VkIGl0IOKAlCBhbmQsIHdoZW5cblx0XHRcdC8vIHRoZSBuZXN0ZWQgc2l0ZSBoYXMgbm8gc2NvcGUgb2YgaXRzIG93biwgdGhlIGNhdXNpbmcgc2l0ZSdzXG5cdFx0XHQvLyBzY29wZSBhdHRyaWJ1dGlvbiB0cmF2ZWxzIHdpdGggdGhlIGxpbmtcblx0XHRcdGNvbnN0IHZpYUxpbmsgPSB0aGlzLm5lc3RlZFdyYXBWaWEuZ2V0KG5vZGUpO1xuXHRcdFx0aWYgKHZpYUxpbmspIHtcblx0XHRcdFx0aW5mby52aWEgPSB2aWFMaW5rLnZpYTtcblx0XHRcdFx0aWYgKGluZm8uc2NvcGUgPT09IHVuZGVmaW5lZCkge1xuXHRcdFx0XHRcdGluZm8uc2NvcGUgPSB2aWFMaW5rLnNjb3BlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHQvLyBkaXZlIHdyYXBzIHJldHVybmVkIGZ1bmN0aW9ucyB0b28sIGFuZCBhbnkgbW5lbW9uaWNhIGluc3RhbmNlXG5cdFx0XHQvLyBjcmVhdGVkIGluc2lkZSB0aGUgd3JhcHBlZCBib2R5IGlzIGEgZ3VhcmFudGVlZCBwYXRoIGhpdCDigJRcblx0XHRcdC8vIGJvdGggYXJlIGNhbGN1bGFibGUgQW9ULCBzbyByZWNvcmQgdGhlbVxuXHRcdFx0Y29uc3Qgd3JhcHBlZCA9IHRoaXMucmVzb2x2ZUZ1bmN0aW9uQXJndW1lbnQobm9kZS5hcmd1bWVudHNbIDAgXSwgc291cmNlRmlsZSk7XG5cdFx0XHRpZiAod3JhcHBlZCkge1xuXHRcdFx0XHQvLyBUaGUgd3JhcHBlZCBjYWxsYmFjayBnZXRzIGl0cyBvd24gc2NvcGUgaW4gc2NvcGVzLmpzb24ga2V5ZWQgYnlcblx0XHRcdFx0Ly8gaXRzIHN0YXJ0IHBvc2l0aW9uIOKAlCByZWNvcmQgdGhhdCBzY29wZUlkIHNvIGdyYXBoIGNvbnN1bWVycyBjYW5cblx0XHRcdFx0Ly8gam9pbiBhIHdyYXAgZW50cnkgdG8gdGhlIGNhbGxiYWNrJ3MgY3JlYXRpb24gbm9kZVxuXHRcdFx0XHRjb25zdCBjYWxsYmFja1BvcyA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdFx0d3JhcHBlZC5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0XHQpO1xuXHRcdFx0XHRjb25zdCBjYWxsYmFja0ZpbGUgPSBub2RlUGF0aC5yZXNvbHZlKHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXHRcdFx0XHRpbmZvLmNhbGxiYWNrU2NvcGVJZCA9IGAke2NhbGxiYWNrRmlsZX06JHtjYWxsYmFja1Bvcy5saW5lICsgMX06JHtjYWxsYmFja1Bvcy5jaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRcdGNvbnN0IGNyZWF0ZXNUeXBlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdFx0XHR0aGlzLmFuYWx5emVXcmFwcGVkQm9keSh3cmFwcGVkLCBsb2NhdGlvbiwgc291cmNlRmlsZSwgMCwgbmV3IFNldCgpLCBjcmVhdGVzVHlwZXMsIGVmZmVjdGl2ZVNjb3BlKTtcblx0XHRcdFx0aWYgKGNyZWF0ZXNUeXBlcy5zaXplID4gMCkge1xuXHRcdFx0XHRcdGluZm8uY3JlYXRlc1R5cGVzID0gQXJyYXkuZnJvbShjcmVhdGVzVHlwZXMpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBzdG9yZWQgPSB0aGlzLmFkZEVEUyh0YXJnZXRUeXBlIHx8IGVmZmVjdGl2ZVNjb3BlIHx8ICd1bmtub3duJywgaW5mbyk7XG5cdFx0XHR0aGlzLndyYXBFbnRyeUJ5Tm9kZS5zZXQobm9kZSwgc3RvcmVkKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBjdXJyZW50KCksIGdldEVycm9ySW5zdGFuY2UoZXJyKSwgZ2V0Rmxvdyh0YXJnZXQ/KVxuXHRcdGlmIChmdW5jTmFtZSA9PT0gJ2N1cnJlbnQnIHx8IGZ1bmNOYW1lID09PSAnZ2V0RXJyb3JJbnN0YW5jZScgfHwgZnVuY05hbWUgPT09ICdnZXRGbG93Jykge1xuXHRcdFx0dGhpcy5hZGRFRFMoc2NvcGUgfHwgJ3Vua25vd24nLCB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kIDogJ2NvbnRleHRDb25zdW1lJyxcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0c2NvcGUsXG5cdFx0XHR9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBhdHRhY2hIb29rcyhjb2xsZWN0aW9uKSDigJQgZnJvbSBAbW5lbW9uaWNhL290ZWwsIHdpcmVzIGFcblx0XHQvLyBUeXBlc0NvbGxlY3Rpb24gdG8gZGl2ZSdzIGxpZmVjeWNsZSB0cmFjaW5nXG5cdFx0aWYgKGZ1bmNOYW1lID09PSAnYXR0YWNoSG9va3MnICYmIG5vZGUuYXJndW1lbnRzLmxlbmd0aCA+IDApIHtcblx0XHRcdGNvbnN0IFsgYXJnIF0gPSBub2RlLmFyZ3VtZW50cztcblx0XHRcdGlmICh0cy5pc0FycmF5TGl0ZXJhbEV4cHJlc3Npb24oYXJnKSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2YgYXJnLmVsZW1lbnRzKSB7XG5cdFx0XHRcdFx0Y29uc3QgdGFyZ2V0VHlwZSA9IHRoaXMucmVzb2x2ZUVEU0FyZ3VtZW50VHlwZShlbGVtZW50KTtcblx0XHRcdFx0XHR0aGlzLmFkZEVEUyh0YXJnZXRUeXBlIHx8IHNjb3BlIHx8ICd1bmtub3duJywge1xuXHRcdFx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdFx0XHRraW5kICAgICAgIDogJ2hvb2tBdHRhY2gnLFxuXHRcdFx0XHRcdFx0Y29kZSxcblx0XHRcdFx0XHRcdHRhcmdldFR5cGUgOiB0YXJnZXRUeXBlIHx8IHVuZGVmaW5lZCxcblx0XHRcdFx0XHRcdHNjb3BlLFxuXHRcdFx0XHRcdH0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRjb25zdCB0YXJnZXRUeXBlID0gdGhpcy5yZXNvbHZlRURTQXJndW1lbnRUeXBlKGFyZyk7XG5cdFx0XHRcdHRoaXMuYWRkRURTKHRhcmdldFR5cGUgfHwgc2NvcGUgfHwgJ3Vua25vd24nLCB7XG5cdFx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdFx0a2luZCAgICAgICA6ICdob29rQXR0YWNoJyxcblx0XHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRcdHRhcmdldFR5cGUgOiB0YXJnZXRUeXBlIHx8IHVuZGVmaW5lZCxcblx0XHRcdFx0XHRzY29wZSxcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgdHlwZSBmcm9tIEVEUyBjYWxsIGFyZ3VtZW50IChiZXN0IGVmZm9ydClcblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZUVEU0FyZ3VtZW50VHlwZSAoYXJnOiB0cy5FeHByZXNzaW9uIHwgdW5kZWZpbmVkKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoIWFyZykge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cblx0XHQvLyBJZGVudGlmaWVyOiB2YXJpYWJsZSBuYW1lXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihhcmcpKSB7XG5cdFx0XHRjb25zdCBtYXBwZWQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChhcmcudGV4dCk7XG5cdFx0XHRpZiAobWFwcGVkKSB7XG5cdFx0XHRcdHJldHVybiBtYXBwZWQ7XG5cdFx0XHR9XG5cdFx0XHQvLyBNYXliZSBpdCdzIGEgdHlwZSBuYW1lIGRpcmVjdGx5XG5cdFx0XHRpZiAodGhpcy5kZWZpbml0aW9ucy5oYXMoYXJnLnRleHQpKSB7XG5cdFx0XHRcdHJldHVybiBhcmcudGV4dDtcblx0XHRcdH1cblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gUHJvcGVydHkgYWNjZXNzOiBvYmoucHJvcFxuXHRcdGlmICh0cy5pc1Byb3BlcnR5QWNjZXNzRXhwcmVzc2lvbihhcmcpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5yZXNvbHZlVHlwZVBhdGgoYXJnKTtcblx0XHR9XG5cblx0XHQvLyBUaGlzIGV4cHJlc3Npb246IHRoaXMuc29tZXRoaW5nXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFyZykgJiYgdHMuaXNJZGVudGlmaWVyKGFyZy5leHByZXNzaW9uKSAmJiBhcmcuZXhwcmVzc2lvbi50ZXh0ID09PSAndGhpcycpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIHRoZSBlbmNsb3NpbmcgbW5lbW9uaWNhIHNjb3BlIG9mIGFuIEVEUyBjYWxsIHNpdGUgYnkgd2Fsa2luZ1xuXHQgKiB1cCB0aGUgcGFyZW50IGNoYWluOiBuZWFyZXN0IGRlZmluZSgpL2xhenkoKSBjYWxsIHdob3NlIGhhbmRsZXIgaG9sZHNcblx0ICogdGhlIG5vZGUsIG9yIG5lYXJlc3QgQGRlY29yYXRlKCktZWQgY2xhc3MgZGVjbGFyYXRpb24uIEJlc3QgZWZmb3J0IOKAlFxuXHQgKiByZXR1cm5zIHVuZGVmaW5lZCBmb3IgY2FsbHMgb3V0c2lkZSBhbnkgdHlwZSBzY29wZSAobW9kdWxlIHRvcCBsZXZlbCkuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVFRFNTY29wZSAobm9kZTogdHMuTm9kZSk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBub2RlLnBhcmVudDtcblx0XHR3aGlsZSAoY3VycmVudCkge1xuXHRcdFx0Y29uc3Qgc2NvcGVQYXRoID0gdGhpcy5lZHNTY29wZUJ5Tm9kZS5nZXQoY3VycmVudCk7XG5cdFx0XHRpZiAoc2NvcGVQYXRoKSB7XG5cdFx0XHRcdHJldHVybiBzY29wZVBhdGg7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHdyYXAgc2l0ZSdzIGluc3RhbmNlL2NvbnRleHQgYXJndW1lbnQgdG8gYSBtbmVtb25pY2EgdHlwZVxuXHQgKiBwYXRoIOKAlCB0aGUgZmlyZS1hbmQtZm9yZ2V0LXdyYXBwZXIgYXR0cmlidXRpb24gZmFsbGJhY2sgd2hlbiB0aGUgY2FsbFxuXHQgKiBzaXRzIG91dHNpZGUgYW55IGRlZmluZSgpL2xhenkoKSBoYW5kbGVyOiBhIHRyYWNrZWQgYXNzaWdubWVudFxuXHQgKiAoYGNvbnN0IGhvbGRlciA9IG5ldyBIb2xkZXIoLi4uKWApLCBlbHNlIHRoZSByb290IGlkZW50aWZpZXInc1xuXHQgKiAocHJvcGVydHktYWNjZXNzIHJvb3RzIGluY2x1ZGVkKSBwYXJhbWV0ZXIgYW5ub3RhdGlvbiByZXNvbHZlZFxuXHQgKiB0aHJvdWdoIHRoZSBncmFwaCBsYXcuIEFtYmlndWl0eSBvciBhYnNlbmNlIHN0YXlzIHNpbGVudCDigJQgdGhpcyBpcyBhXG5cdCAqIG1ldGFkYXRhIGhldXJpc3RpYywgbm90IHRoZSBpZGVudGl0eS1sYXcgc3VyZmFjZS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVdyYXBJbnN0YW5jZVR5cGVQYXRoIChhcmc6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IGZyb21CaW5kaW5nID0gKG5hbWU6IHN0cmluZywgZnJvbTogdHMuTm9kZSk6IHN0cmluZyB8IHVuZGVmaW5lZCA9PiB7XG5cdFx0XHRjb25zdCBtYXBwZWQgPSB0aGlzLnZhcmlhYmxlVG9UeXBlTWFwLmdldChuYW1lKTtcblx0XHRcdGlmIChtYXBwZWQpIHtcblx0XHRcdFx0cmV0dXJuIG1hcHBlZDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGFubm90YXRpb25UeXBlID0gdGhpcy5yZXNvbHZlUGFyYW1ldGVyQW5ub3RhdGlvblR5cGVQYXRoKG5hbWUsIGZyb20pID8/XG5cdFx0XHRcdC8vIEYyMCBjaGVhcCB0aWVyOiB0aGUgaWRlbnRpZmllciBpcyBib3VuZCB0byBhIGxldC92YXIvY29uc3Rcblx0XHRcdFx0Ly8gd2l0aCBhbiBFWFBMSUNJVCB0eXBlIGFubm90YXRpb24g4oCUIHJlc29sdmUgdGhlIGFubm90YXRpb25cblx0XHRcdFx0Ly8gdGhyb3VnaCB0aGUgZ3JhcGggbGF3LiBObyBmbG93LXNlbnNpdGl2ZSBhc3NpZ25tZW50XG5cdFx0XHRcdC8vIHRyYWNraW5nOiBhbiBVTkFOTk9UQVRFRCBsZXQgc3RpbGwgYnVja2V0cyB1bmtub3duXG5cdFx0XHRcdHRoaXMucmVzb2x2ZVZhcmlhYmxlQW5ub3RhdGlvblR5cGVQYXRoKG5hbWUsIGZyb20pO1xuXHRcdFx0cmV0dXJuIGFubm90YXRpb25UeXBlO1xuXHRcdH07XG5cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGZyb21CaW5kaW5nKGFyZy50ZXh0LCBhcmcpO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFyZykpIHtcblx0XHRcdGNvbnN0IHJvb3QgPSB0aGlzLmdldFJvb3RJZGVudGlmaWVyKGFyZyk7XG5cdFx0XHRpZiAocm9vdCkge1xuXHRcdFx0XHRjb25zdCByZXN1bHQgPSBmcm9tQmluZGluZyhyb290LnRleHQsIGFyZyk7XG5cdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIGJhcmUtaWRlbnRpZmllciB0eXBlIGFubm90YXRpb24gb2YgdGhlIG5lYXJlc3QgZW5jbG9zaW5nXG5cdCAqIGZ1bmN0aW9uJ3MgcGFyYW1ldGVyIHRocm91Z2ggdGhlIG1uZW1vbmljYS1ncmFwaCB0aWVycyAodmFsdWUgc2NvcGUsXG5cdCAqIGltcG9ydHMsIHJvb3RzLCBwcm9ncmFtLXdpZGUtdW5pcXVlKS4gTm9uLWlkZW50aWZpZXIgYW5kIGdlbmVyaWNcblx0ICogYW5ub3RhdGlvbnMgYXJlIG5vdCBncmFwaCByZWZlcmVuY2VzOyBhbWJpZ3VpdHkgYW5kIGFic2VuY2UgeWllbGRcblx0ICogdW5kZWZpbmVkLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlUGFyYW1ldGVyQW5ub3RhdGlvblR5cGVQYXRoIChuYW1lOiBzdHJpbmcsIGZyb206IHRzLk5vZGUpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gZnJvbS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmICh0cy5pc0Z1bmN0aW9uTGlrZShjdXJyZW50KSkge1xuXHRcdFx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIGN1cnJlbnQucGFyYW1ldGVycyA/PyBbXSkge1xuXHRcdFx0XHRcdGlmICghdHMuaXNJZGVudGlmaWVyKHBhcmFtLm5hbWUpIHx8IHBhcmFtLm5hbWUudGV4dCAhPT0gbmFtZSB8fCAhcGFyYW0udHlwZSB8fFxuXHRcdFx0XHRcdFx0IXRzLmlzVHlwZVJlZmVyZW5jZU5vZGUocGFyYW0udHlwZSkgfHxcblx0XHRcdFx0XHRcdCF0cy5pc0lkZW50aWZpZXIocGFyYW0udHlwZS50eXBlTmFtZSkgfHxcblx0XHRcdFx0XHRcdChwYXJhbS50eXBlLnR5cGVBcmd1bWVudHM/Lmxlbmd0aCA/PyAwKSA+IDApIHtcblx0XHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRjb25zdCBncmFwaFJlc3VsdCA9IHRoaXMucmVzb2x2ZUdyYXBoVHlwZU5hbWUocGFyYW0udHlwZS50eXBlTmFtZS50ZXh0KTtcblx0XHRcdFx0XHRpZiAoZ3JhcGhSZXN1bHQuc3RhdHVzID09PSAndW5pcXVlJykge1xuXHRcdFx0XHRcdFx0Y29uc3QgcmVzdWx0ID0gZ3JhcGhSZXN1bHQubm9kZS5mdWxsUGF0aDtcblx0XHRcdFx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHR9XG5cdFx0XHRjdXJyZW50ID0gY3VycmVudC5wYXJlbnQ7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogRjIwIGNoZWFwIHRpZXI6IHRoZSB3cmFwIGFyZ3VtZW50IGlzIGFuIGlkZW50aWZpZXIgZGVjbGFyZWQgd2l0aCBhblxuXHQgKiBFWFBMSUNJVCB0eXBlIGFubm90YXRpb24gKGBsZXQgdXBkYXRlQ29tbWl0dGVkOiBMZWRnZXJVcGRhdGU7YFxuXHQgKiBhc3NpZ25lZCBsYXRlciBpbiBhIGZsb3cgdGhlIGFuYWx5emVyIGRvZXMgbm90IHRyYWNrKS4gVGhlXG5cdCAqIGFubm90YXRpb24gcmVzb2x2ZXMgdGhyb3VnaCB0aGUgc2FtZSBncmFwaCB0aWVycyBhcyBwYXJhbWV0ZXJcblx0ICogYW5ub3RhdGlvbnMuIERlbGliZXJhdGVseSBOT1QgZmxvdy1zZW5zaXRpdmU6IGFuIFVOQU5OT1RBVEVEXG5cdCAqIGxldC92YXIgc3RpbGwgYnVja2V0cyB1bmtub3duLCBhbmQgYSBjb25zdCB3aXRoIGFuIGFuYWx5emFibGVcblx0ICogaW5pdGlhbGl6ZXIgc3RheXMgdGhlIHJlY29tbWVuZGVkIGRpc2NpcGxpbmUuIFRoZSBsb29rdXAgd2Fsa3MgdGhlXG5cdCAqIGVuY2xvc2luZyBzdGF0ZW1lbnQgY29udGFpbmVycyBpbm5lcm1vc3Qtb3V0LCBzbyBhIHNoYWRvd2luZyBpbm5lclxuXHQgKiBkZWNsYXJhdGlvbiB3aW5zLlxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlVmFyaWFibGVBbm5vdGF0aW9uVHlwZVBhdGggKG5hbWU6IHN0cmluZywgZnJvbTogdHMuTm9kZSk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0bGV0IGN1cnJlbnQ6IHRzLk5vZGUgfCB1bmRlZmluZWQgPSBmcm9tO1xuXHRcdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0XHRjb25zdCBzdGF0ZW1lbnRzOiB0cy5Ob2RlQXJyYXk8dHMuU3RhdGVtZW50PiB8IHVuZGVmaW5lZCA9XG5cdFx0XHRcdHRzLmlzQmxvY2soY3VycmVudCkgfHwgdHMuaXNNb2R1bGVCbG9jayhjdXJyZW50KSB8fCB0cy5pc1NvdXJjZUZpbGUoY3VycmVudClcblx0XHRcdFx0XHQ/IGN1cnJlbnQuc3RhdGVtZW50c1xuXHRcdFx0XHRcdDogdHMuaXNDYXNlQ2xhdXNlKGN1cnJlbnQpIHx8IHRzLmlzRGVmYXVsdENsYXVzZShjdXJyZW50KVxuXHRcdFx0XHRcdFx0PyBjdXJyZW50LnN0YXRlbWVudHNcblx0XHRcdFx0XHRcdDogdW5kZWZpbmVkO1xuXHRcdFx0aWYgKHN0YXRlbWVudHMpIHtcblx0XHRcdFx0Y29uc3QgcmVzb2x2ZWQgPSB0aGlzLmZpbmRBbm5vdGF0ZWRWYXJpYWJsZVR5cGVQYXRoKHN0YXRlbWVudHMsIG5hbWUpO1xuXHRcdFx0XHRpZiAocmVzb2x2ZWQpIHtcblx0XHRcdFx0XHRyZXR1cm4gcmVzb2x2ZWQ7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBGaXJzdCB2YXJpYWJsZSBkZWNsYXJhdGlvbiBjYXJyeWluZyBhbiBleHBsaWNpdCBiYXJlLWlkZW50aWZpZXIgdHlwZVxuXHQgKiBhbm5vdGF0aW9uIGZvciBgbmFtZWAgaW4gdGhlIGdpdmVuIHN0YXRlbWVudCBsaXN0LCByZXNvbHZlZCB0aHJvdWdoXG5cdCAqIHRoZSBncmFwaCBsYXcuXG5cdCAqL1xuXHRwcml2YXRlIGZpbmRBbm5vdGF0ZWRWYXJpYWJsZVR5cGVQYXRoIChcblx0XHRzdGF0ZW1lbnRzOiByZWFkb25seSB0cy5TdGF0ZW1lbnRbXSxcblx0XHRuYW1lOiBzdHJpbmdcblx0KTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRmb3IgKGNvbnN0IHN0YXRlbWVudCBvZiBzdGF0ZW1lbnRzKSB7XG5cdFx0XHRpZiAoIXRzLmlzVmFyaWFibGVTdGF0ZW1lbnQoc3RhdGVtZW50KSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3QgZGVjbGFyYXRpb24gb2Ygc3RhdGVtZW50LmRlY2xhcmF0aW9uTGlzdC5kZWNsYXJhdGlvbnMpIHtcblx0XHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoZGVjbGFyYXRpb24ubmFtZSkgfHwgZGVjbGFyYXRpb24ubmFtZS50ZXh0ICE9PSBuYW1lIHx8XG5cdFx0XHRcdFx0IWRlY2xhcmF0aW9uLnR5cGUgfHxcblx0XHRcdFx0XHQhdHMuaXNUeXBlUmVmZXJlbmNlTm9kZShkZWNsYXJhdGlvbi50eXBlKSB8fFxuXHRcdFx0XHRcdCF0cy5pc0lkZW50aWZpZXIoZGVjbGFyYXRpb24udHlwZS50eXBlTmFtZSkgfHxcblx0XHRcdFx0XHQoZGVjbGFyYXRpb24udHlwZS50eXBlQXJndW1lbnRzPy5sZW5ndGggPz8gMCkgPiAwKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgZ3JhcGhSZXN1bHQgPSB0aGlzLnJlc29sdmVHcmFwaFR5cGVOYW1lKGRlY2xhcmF0aW9uLnR5cGUudHlwZU5hbWUudGV4dCk7XG5cdFx0XHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRcdFx0Y29uc3QgcmVzdWx0ID0gZ3JhcGhSZXN1bHQubm9kZS5mdWxsUGF0aDtcblx0XHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHdyYXAoKSBhcmd1bWVudCB0byBpdHMgZnVuY3Rpb24gbm9kZSB3aXRob3V0IHRoZSB0eXBlXG5cdCAqIGNoZWNrZXI6IGRpcmVjdCBmdW5jdGlvbiBleHByZXNzaW9ucy9hcnJvd3MsIG9yIHNhbWUtZmlsZSBiaW5kaW5nc1xuXHQgKiAoYGNvbnN0IGZuID0gKCkgPT4gLi4uYCwgYGZ1bmN0aW9uIGZuKCkgLi4uYCkuIEJlc3QgZWZmb3J0IOKAlCBtZXRob2Rcblx0ICogcmVmZXJlbmNlcywgLmJpbmQoKSBwcm9kdWN0cyBhbmQgY3Jvc3MtZmlsZSBpZGVudGlmaWVycyBzdGF5XG5cdCAqIHVucmVzb2x2ZWQ7IHRoZSBjYWxsc2l0ZSBlbnRyeSBpdHNlbGYgaXMgc3RpbGwgcmVjb3JkZWQuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVGdW5jdGlvbkFyZ3VtZW50IChcblx0XHRhcmc6IHRzLkV4cHJlc3Npb24gfCB1bmRlZmluZWQsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZVxuXHQpOiB0cy5GdW5jdGlvbkxpa2VEZWNsYXJhdGlvbiB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCFhcmcpIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0Fycm93RnVuY3Rpb24oYXJnKSB8fCB0cy5pc0Z1bmN0aW9uRXhwcmVzc2lvbihhcmcpKSB7XG5cdFx0XHRyZXR1cm4gYXJnO1xuXHRcdH1cblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGFyZykpIHtcblx0XHRcdGNvbnN0IGtleSA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9IyR7YXJnLnRleHR9YDtcblx0XHRcdGNvbnN0IGJvdW5kID0gdGhpcy5mdW5jdGlvbkJpbmRpbmdzLmdldChrZXkpO1xuXHRcdFx0aWYgKGJvdW5kKSB7XG5cdFx0XHRcdHJldHVybiBib3VuZDtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBBbmFseXNlIGEgd3JhcHBlZCBmdW5jdGlvbidzIGJvZHkgZm9yIGd1YXJhbnRlZWQgcnVudGltZSBwYXRoczpcblx0ICogZGl2ZSB3cmFwcyByZXR1cm5lZCBmdW5jdGlvbnMgYXMgd2VsbCAocmVjdXJzaXZlbHkpLCBzbyBlYWNoXG5cdCAqIGZ1bmN0aW9uLXZhbHVlZCByZXR1cm4gaXMgYSBuZXN0ZWQgd3JhcCBzaXRlLCBhbmQgZWFjaCBgbmV3IFR5cGUoKWBcblx0ICogaW5zaWRlIHRoZSBib2R5IG1lYW5zIHRoZSBwYXRoIGhpdHMgdGhhdCB0eXBlJ3MgY29uc3RydWN0b3IgKHdoaWNoXG5cdCAqIGF0dGFjaEhvb2tzIHdyYXBzIHRvbykuIEJvdGggZmFjdHMgYXJlIDEwMCUgZW5zdXJlZCwgc28gdGhleSBhcmVcblx0ICogcmVjb3JkZWQgQW9ULiBOZXN0ZWQgZnVuY3Rpb24gYm9kaWVzIGFyZSBOT1Qgd2Fsa2VkIGhlcmUg4oCUIHRoZXlcblx0ICogYmVsb25nIHRvIHRoZWlyIG93biB3cmFwIGFuYWx5c2lzLCByZWFjaGVkIHZpYSB0aGUgcmV0dXJuIGNoYWluLlxuXHQgKiBEZXB0aC1jYXBwZWQgYW5kIGN5Y2xlLWd1YXJkZWQuXG5cdCAqL1xuXHRwcml2YXRlIGFuYWx5emVXcmFwcGVkQm9keSAoXG5cdFx0Zm46IHRzLkZ1bmN0aW9uTGlrZURlY2xhcmF0aW9uLFxuXHRcdHZpYUxvY2F0aW9uOiBzdHJpbmcsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRkZXB0aDogbnVtYmVyLFxuXHRcdHZpc2l0ZWQ6IFNldDx0cy5Ob2RlPixcblx0XHRjcmVhdGVzVHlwZXM6IFNldDxzdHJpbmc+LFxuXHRcdGZhbGxiYWNrU2NvcGU/OiBzdHJpbmdcblx0KTogdm9pZCB7XG5cdFx0aWYgKGRlcHRoID4gNSB8fCB2aXNpdGVkLmhhcyhmbikgfHwgIWZuLmJvZHkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0dmlzaXRlZC5hZGQoZm4pO1xuXG5cdFx0Ly8gQXJyb3cgd2l0aCBleHByZXNzaW9uIGJvZHk6IGltcGxpY2l0IHJldHVyblxuXHRcdGlmICh0cy5pc0Fycm93RnVuY3Rpb24oZm4pICYmICF0cy5pc0Jsb2NrKGZuLmJvZHkpKSB7XG5cdFx0XHR0aGlzLnJlY29yZFdyYXBwZWRSZXR1cm4oZm4uYm9keSwgdmlhTG9jYXRpb24sIHNvdXJjZUZpbGUsIGRlcHRoLCB2aXNpdGVkLCBmYWxsYmFja1Njb3BlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB3YWxrID0gKG5vZGU6IHRzLk5vZGUpOiB2b2lkID0+IHtcblx0XHRcdGlmIChub2RlICE9PSBmbi5ib2R5ICYmIChcblx0XHRcdFx0dHMuaXNGdW5jdGlvbkV4cHJlc3Npb24obm9kZSkgfHxcblx0XHRcdFx0dHMuaXNBcnJvd0Z1bmN0aW9uKG5vZGUpIHx8XG5cdFx0XHRcdHRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihub2RlKSB8fFxuXHRcdFx0XHR0cy5pc01ldGhvZERlY2xhcmF0aW9uKG5vZGUpXG5cdFx0XHQpKSB7XG5cdFx0XHRcdC8vIG5lc3RlZCBmdW5jdGlvbiBib2RpZXMgYXJlIGFuYWx5c2VkIHRocm91Z2ggdGhlIHJldHVybiBjaGFpblxuXHRcdFx0XHRyZXR1cm47XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNSZXR1cm5TdGF0ZW1lbnQobm9kZSkgJiYgbm9kZS5leHByZXNzaW9uKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkV3JhcHBlZFJldHVybihub2RlLmV4cHJlc3Npb24sIHZpYUxvY2F0aW9uLCBzb3VyY2VGaWxlLCBkZXB0aCwgdmlzaXRlZCwgZmFsbGJhY2tTY29wZSk7XG5cdFx0XHR9XG5cdFx0XHRpZiAodHMuaXNOZXdFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRcdGNvbnN0IGNyZWF0ZWQgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24pIHx8XG5cdFx0XHRcdFx0KHRzLmlzSWRlbnRpZmllcihub2RlLmV4cHJlc3Npb24pICYmIHRoaXMuZGVmaW5pdGlvbnMuaGFzKG5vZGUuZXhwcmVzc2lvbi50ZXh0KVxuXHRcdFx0XHRcdFx0PyBub2RlLmV4cHJlc3Npb24udGV4dFxuXHRcdFx0XHRcdFx0OiB1bmRlZmluZWQpO1xuXHRcdFx0XHRpZiAoY3JlYXRlZCkge1xuXHRcdFx0XHRcdGNyZWF0ZXNUeXBlcy5hZGQoY3JlYXRlZCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHRcdGNvbnN0IG5lc3RlZE5hbWUgPSB0aGlzLmdldEZ1bmN0aW9uTmFtZShub2RlLmV4cHJlc3Npb24pO1xuXHRcdFx0XHRpZiAoXG5cdFx0XHRcdFx0bmVzdGVkTmFtZSA9PT0gJ3dyYXAnIHx8XG5cdFx0XHRcdFx0bmVzdGVkTmFtZSA9PT0gJ3dyYXBDb25zdHJ1Y3RvckFyZycgfHxcblx0XHRcdFx0XHRuZXN0ZWROYW1lID09PSAndXBncmFkZUNvbnN0cnVjdG9yQXJnJyB8fFxuXHRcdFx0XHRcdG5lc3RlZE5hbWUgPT09ICd3cmFwSW5zdGFuY2VNZXRob2RzJ1xuXHRcdFx0XHQpIHtcblx0XHRcdFx0XHQvLyB0aGUgbmVzdGVkIGNhbGwgbWF5IGFscmVhZHkgYmUgY29sbGVjdGVkICh2aXNpdGVkXG5cdFx0XHRcdFx0Ly8gYmVmb3JlIHRoaXMgb3V0ZXIgd3JhcCBzaXRlKSDigJQgYmFjay1wYXRjaCBpdHMgZW50cnksXG5cdFx0XHRcdFx0Ly8gb3RoZXJ3aXNlIGxlYXZlIHRoZSBsaW5rICh3aXRoIHRoaXMgc2l0ZSdzIHNjb3BlKSBmb3Jcblx0XHRcdFx0XHQvLyBjb2xsZWN0RURTIHRvIHBpY2sgdXBcblx0XHRcdFx0XHRjb25zdCBuZXN0ZWRFbnRyeSA9IHRoaXMud3JhcEVudHJ5QnlOb2RlLmdldChub2RlKTtcblx0XHRcdFx0XHRpZiAobmVzdGVkRW50cnkpIHtcblx0XHRcdFx0XHRcdG5lc3RlZEVudHJ5LnZpYSA9IHZpYUxvY2F0aW9uO1xuXHRcdFx0XHRcdFx0aWYgKG5lc3RlZEVudHJ5LnNjb3BlID09PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0XHRcdFx0bmVzdGVkRW50cnkuc2NvcGUgPSBmYWxsYmFja1Njb3BlO1xuXHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdFx0XHR0aGlzLm5lc3RlZFdyYXBWaWEuc2V0KG5vZGUsIHsgdmlhIDogdmlhTG9jYXRpb24sIHNjb3BlIDogZmFsbGJhY2tTY29wZSB9KTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdHRzLmZvckVhY2hDaGlsZChub2RlLCB3YWxrKTtcblx0XHR9O1xuXHRcdHdhbGsoZm4uYm9keSk7XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIG9uZSBmdW5jdGlvbi12YWx1ZWQgcmV0dXJuIG9mIGEgd3JhcHBlZCBib2R5IGFzIGEgbmVzdGVkIHdyYXBcblx0ICogc2l0ZSAoYHZpYWAgPSB0aGUgc2l0ZSB3aG9zZSB3cmFwcGluZyBjYXVzZWQgaXQpIGFuZCByZWN1cnNlIGludG9cblx0ICogaXRzIG93biByZXR1cm5zLiBSZXR1cm5zIHRocm91Z2ggaWRlbnRpZmllcnMgcmVzb2x2ZSB0aHJvdWdoIHRoZVxuXHQgKiBzYW1lLWZpbGUgYmluZGluZ3MgdGFibGU7IHVucmVzb2x2YWJsZSByZXR1cm5zIGFyZSBzaW1wbHkgc2tpcHBlZC5cblx0ICogQSByZXR1cm4gZGVjbGFyZWQgb3V0c2lkZSBhbnkgdHlwZSBzY29wZSBpbmhlcml0cyB0aGUgY2F1c2luZyB3cmFwXG5cdCAqIHNpdGUncyBzY29wZSBhdHRyaWJ1dGlvbiAodGhlIGdlbmVyYXRpb24gY2hhaW4gaXMgdGhlIG9ubHkgaG9sZGVyKS5cblx0ICovXG5cdHByaXZhdGUgcmVjb3JkV3JhcHBlZFJldHVybiAoXG5cdFx0ZXhwcjogdHMuRXhwcmVzc2lvbixcblx0XHR2aWFMb2NhdGlvbjogc3RyaW5nLFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0ZGVwdGg6IG51bWJlcixcblx0XHR2aXNpdGVkOiBTZXQ8dHMuTm9kZT4sXG5cdFx0ZmFsbGJhY2tTY29wZT86IHN0cmluZ1xuXHQpOiB2b2lkIHtcblx0XHRjb25zdCByZXR1cm5lZCA9IHRoaXMucmVzb2x2ZUZ1bmN0aW9uQXJndW1lbnQoZXhwciwgc291cmNlRmlsZSk7XG5cdFx0aWYgKCFyZXR1cm5lZCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0cmV0dXJuZWQuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IHJldHVybmVkLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblx0XHRjb25zdCBzY29wZSA9IHRoaXMucmVzb2x2ZUVEU1Njb3BlKHJldHVybmVkKSA/PyBmYWxsYmFja1Njb3BlO1xuXHRcdGNvbnN0IGVudHJ5ID0gdGhpcy5hZGRFRFMoc2NvcGUgfHwgJ3Vua25vd24nLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgOiAnd3JhcCcsXG5cdFx0XHRjb2RlLFxuXHRcdFx0c2NvcGUsXG5cdFx0XHR2aWEgIDogdmlhTG9jYXRpb24sXG5cdFx0XHQvLyBkaXZlIHdyYXBzIHJldHVybmVkIGZ1bmN0aW9ucyB0aHJvdWdoIHRoZSBzYW1lIHdyYXAgbWFjaGluZXJ5XG5cdFx0XHRmbiAgIDogJ3dyYXAnLFxuXHRcdH0pO1xuXHRcdC8vIHRoZSByZXR1cm5lZCBmdW5jdGlvbidzIG93biByZXR1cm5zIGFyZSB3cmFwcGVkIGluIHR1cm47IGB2aWFgXG5cdFx0Ly8gY2hhaW5zIHRvIHRoaXMgbmVzdGVkIGVudHJ5J3MgbG9jYXRpb25cblx0XHRjb25zdCBuZXN0ZWRDcmVhdGVzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0dGhpcy5hbmFseXplV3JhcHBlZEJvZHkocmV0dXJuZWQsIGxvY2F0aW9uLCBzb3VyY2VGaWxlLCBkZXB0aCArIDEsIHZpc2l0ZWQsIG5lc3RlZENyZWF0ZXMsIHNjb3BlKTtcblx0XHRpZiAobmVzdGVkQ3JlYXRlcy5zaXplID4gMCkge1xuXHRcdFx0ZW50cnkuY3JlYXRlc1R5cGVzID0gQXJyYXkuZnJvbShuZXN0ZWRDcmVhdGVzKTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQWRkIGFuIEVEUyB1c2FnZSB0byB0aGUgY29sbGVjdGlvblxuXHQgKiBSZXR1cm5zIHRoZSBzdG9yZWQgZW50cnkgKHRoZSBleGlzdGluZyBvbmUgd2hlbiB0aGlzIGlzIGEgZHVwbGljYXRlKSxcblx0ICogc28gY2FsbGVycyBjYW4gZW5yaWNoIGl0IGFmdGVyIG5lc3RlZCBib2R5IGFuYWx5c2lzLlxuXHQgKi9cblx0cHJpdmF0ZSBhZGRFRFMgKHR5cGVQYXRoOiBzdHJpbmcsIGluZm86IEVEU0luZm8pOiBFRFNJbmZvIHtcblx0XHRpZiAoIXRoaXMuZWRzVXNhZ2VzLmhhcyh0eXBlUGF0aCkpIHtcblx0XHRcdHRoaXMuZWRzVXNhZ2VzLnNldCh0eXBlUGF0aCwgW10pO1xuXHRcdH1cblxuXHRcdGNvbnN0IGV4aXN0aW5nID0gdGhpcy5lZHNVc2FnZXMuZ2V0KHR5cGVQYXRoKSE7XG5cdFx0Y29uc3QgZHVwbGljYXRlID0gZXhpc3RpbmcuZmluZChlID0+IHtcblx0XHRcdHJldHVybiBlLmxvY2F0aW9uID09PSBpbmZvLmxvY2F0aW9uICYmXG5cdFx0XHRcdGUua2luZCA9PT0gaW5mby5raW5kICYmXG5cdFx0XHRcdGUuY29kZSA9PT0gaW5mby5jb2RlO1xuXHRcdH0pO1xuXG5cdFx0aWYgKGR1cGxpY2F0ZSkge1xuXHRcdFx0cmV0dXJuIGR1cGxpY2F0ZTtcblx0XHR9XG5cdFx0ZXhpc3RpbmcucHVzaChpbmZvKTtcblx0XHRyZXR1cm4gaW5mbztcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IG5hdGl2ZSBmbG93IHBhdHRlcm5zIChpbnN0YW5jZSB1c2FnZSBhZnRlciBjcmVhdGlvbilcblx0ICogUGhhc2UgMTogcHJvcGVydHkgYWNjZXNzLCBtZXRob2QgY2FsbHMsIGFyZ3VtZW50cywgcmV0dXJuLCBkZXN0cnVjdHVyaW5nLCBldGMuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93IChub2RlOiB0cy5Ob2RlLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Ly8gUHJvcGVydHkgcmVhZDogdXNlci5uYW1lIG9yIHVzZXI/Lm5hbWVcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dQcm9wZXJ0eUFjY2Vzcyhub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBFbGVtZW50IGFjY2VzczogdXNlclsnbmFtZSddXG5cdFx0aWYgKHRzLmlzRWxlbWVudEFjY2Vzc0V4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dFbGVtZW50QWNjZXNzKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFByb3BlcnR5IHdyaXRlOiB1c2VyLm5hbWUgPSB2YWx1ZVxuXHRcdGlmICh0cy5pc0JpbmFyeUV4cHJlc3Npb24obm9kZSkgJiYgbm9kZS5vcGVyYXRvclRva2VuLmtpbmQgPT09IHRzLlN5bnRheEtpbmQuRXF1YWxzVG9rZW4pIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dBc3NpZ25tZW50KG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIE1ldGhvZCBjYWxsOiB1c2VyLnZhbGlkYXRlKCkgIEFORCAgYXJndW1lbnQgcGFzc2luZzogcHJvY2Vzc1VzZXIodXNlcilcblx0XHRpZiAodHMuaXNDYWxsRXhwcmVzc2lvbihub2RlKSAmJiBub2RlLmV4cHJlc3Npb24pIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dNZXRob2RDYWxsKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd0FyZ3VtZW50UGFzcyhub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBEZXN0cnVjdHVyZSByZWFkOiBjb25zdCB7IG5hbWUgfSA9IHVzZXJcblx0XHRpZiAodHMuaXNWYXJpYWJsZURlY2xhcmF0aW9uKG5vZGUpICYmIG5vZGUuaW5pdGlhbGl6ZXIpIHtcblx0XHRcdHRoaXMuY29sbGVjdEZsb3dEZXN0cnVjdHVyZShub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBSZXR1cm4gaW5zdGFuY2U6IHJldHVybiB1c2VyXG5cdFx0aWYgKHRzLmlzUmV0dXJuU3RhdGVtZW50KG5vZGUpICYmIG5vZGUuZXhwcmVzc2lvbikge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd1JldHVybihub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHQvLyBTcHJlYWQ6IHsgLi4udXNlciB9XG5cdFx0aWYgKHRzLmlzU3ByZWFkRWxlbWVudChub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0Rmxvd1NwcmVhZChub2RlLCBzb3VyY2VGaWxlKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBwcm9wZXJ0eSBhY2Nlc3MgZmxvdyAocmVhZCBvciBjb25kaXRpb25hbClcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dQcm9wZXJ0eUFjY2VzcyAobm9kZTogdHMuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3Qgb2JqZWN0VHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0aWYgKCFvYmplY3RUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3QgcHJvcE5hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHQvLyBTa2lwIGlmIHRoaXMgaXMgYSB0eXBlIGNvbnN0cnVjdG9yIGFjY2VzcyAoZS5nLiwgVXNlclR5cGUuZGVmaW5lKVxuXHRcdGlmIChwcm9wTmFtZSA9PT0gJ2RlZmluZScgfHwgcHJvcE5hbWUgPT09ICdsYXp5JykgeyByZXR1cm47IH1cblxuXHRcdHRoaXMuYWRkRmxvdyhvYmplY3RUeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgICA6ICdwcm9wZXJ0eVJlYWQnLFxuXHRcdFx0Y29kZSxcblx0XHRcdHByb3BlcnR5TmFtZSA6IHByb3BOYW1lLFxuXHRcdFx0dGFyZ2V0VHlwZSAgIDogb2JqZWN0VHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3QgZWxlbWVudCBhY2Nlc3MgZmxvdzogdXNlclsnbmFtZSddXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93RWxlbWVudEFjY2VzcyAobm9kZTogdHMuRWxlbWVudEFjY2Vzc0V4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRjb25zdCBvYmplY3RUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUobm9kZS5leHByZXNzaW9uKTtcblx0XHRpZiAoIW9iamVjdFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHR0aGlzLmFkZEZsb3cob2JqZWN0VHlwZSwge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRraW5kICAgICAgIDogJ2VsZW1lbnRBY2Nlc3MnLFxuXHRcdFx0Y29kZSxcblx0XHRcdHRhcmdldFR5cGUgOiBvYmplY3RUeXBlXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBhc3NpZ25tZW50IGZsb3c6IHVzZXIubmFtZSA9IHZhbHVlIG9yIHVzZXIgPSBvdGhlclxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd0Fzc2lnbm1lbnQgKG5vZGU6IHRzLkJpbmFyeUV4cHJlc3Npb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHQvLyBQcm9wZXJ0eSB3cml0ZTogdXNlci5uYW1lID0gdmFsdWVcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obm9kZS5sZWZ0KSkge1xuXHRcdFx0Y29uc3Qgb2JqZWN0VHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUubGVmdC5leHByZXNzaW9uKTtcblx0XHRcdGlmICghb2JqZWN0VHlwZSkgeyByZXR1cm47IH1cblxuXHRcdFx0Y29uc3QgcHJvcE5hbWUgPSBub2RlLmxlZnQubmFtZS50ZXh0O1xuXHRcdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0XHQpO1xuXHRcdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdFx0dGhpcy5hZGRGbG93KG9iamVjdFR5cGUsIHtcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGtpbmQgICAgICAgICA6ICdwcm9wZXJ0eVdyaXRlJyxcblx0XHRcdFx0Y29kZSxcblx0XHRcdFx0cHJvcGVydHlOYW1lIDogcHJvcE5hbWUsXG5cdFx0XHRcdHRhcmdldFR5cGUgICA6IG9iamVjdFR5cGVcblx0XHRcdH0pO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFZhcmlhYmxlIHJlYXNzaWdubWVudDogdXNlciA9IG90aGVyXG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihub2RlLmxlZnQpKSB7XG5cdFx0XHRjb25zdCB2YXJOYW1lID0gbm9kZS5sZWZ0LnRleHQ7XG5cdFx0XHRjb25zdCBtYXBwZWRUeXBlID0gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQodmFyTmFtZSk7XG5cdFx0XHRpZiAoIW1hcHBlZFR5cGUpIHsgcmV0dXJuOyB9XG5cblx0XHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdFx0c291cmNlRmlsZSxcblx0XHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdFx0KTtcblx0XHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRcdHRoaXMuYWRkRmxvdyhtYXBwZWRUeXBlLCB7XG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRraW5kICAgICAgIDogJ3JlYXNzaWdubWVudCcsXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHRhcmdldFR5cGUgOiBtYXBwZWRUeXBlXG5cdFx0XHR9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBtZXRob2QgY2FsbCBmbG93OiB1c2VyLnZhbGlkYXRlKClcblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEZsb3dNZXRob2RDYWxsIChub2RlOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGlmICghdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obm9kZS5leHByZXNzaW9uKSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IG9iamVjdFR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmV4cHJlc3Npb24uZXhwcmVzc2lvbik7XG5cdFx0aWYgKCFvYmplY3RUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3QgbWV0aG9kTmFtZSA9IG5vZGUuZXhwcmVzc2lvbi5uYW1lLnRleHQ7XG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0Ly8gU2tpcCBpZiB0aGlzIGlzIGEgdHlwZSBjb25zdHJ1Y3RvciBjYWxsIChlLmcuLCBuZXcgVXNlclR5cGUoKSlcblx0XHRpZiAobWV0aG9kTmFtZSA9PT0gJ2RlZmluZScgfHwgbWV0aG9kTmFtZSA9PT0gJ2xhenknKSB7IHJldHVybjsgfVxuXG5cdFx0dGhpcy5hZGRGbG93KG9iamVjdFR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICAgIDogJ21ldGhvZENhbGwnLFxuXHRcdFx0Y29kZSxcblx0XHRcdHByb3BlcnR5TmFtZSA6IG1ldGhvZE5hbWUsXG5cdFx0XHR0YXJnZXRUeXBlICAgOiBvYmplY3RUeXBlXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBhcmd1bWVudCBwYXNzaW5nIGZsb3c6IHByb2Nlc3NVc2VyKHVzZXIpXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93QXJndW1lbnRQYXNzIChub2RlOiB0cy5DYWxsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5hcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcblx0XHRcdGNvbnN0IGFyZyA9IG5vZGUuYXJndW1lbnRzWyBpIF07XG5cdFx0XHRjb25zdCBhcmdUeXBlID0gdGhpcy5yZXNvbHZlRXhwcmVzc2lvblR5cGUoYXJnKTtcblx0XHRcdGlmICghYXJnVHlwZSkgeyBjb250aW51ZTsgfVxuXG5cdFx0XHRjb25zdCBmdW5jTmFtZSA9IHRoaXMuZ2V0RnVuY3Rpb25OYW1lKG5vZGUuZXhwcmVzc2lvbikgfHwgJ2Fub255bW91cyc7XG5cdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHRcdCk7XG5cdFx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0XHR0aGlzLmFkZEZsb3coYXJnVHlwZSwge1xuXHRcdFx0XHRsb2NhdGlvbixcblx0XHRcdFx0a2luZCAgICAgICA6ICdwYXNzQXNBcmcnLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHR0YXJnZXRUeXBlIDogYXJnVHlwZSxcblx0XHRcdFx0Y29udGV4dCAgICA6IGBhcmcgJHtpfSB0byAke2Z1bmNOYW1lfWBcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IGRlc3RydWN0dXJpbmcgZmxvdzogY29uc3QgeyBuYW1lIH0gPSB1c2VyXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93RGVzdHJ1Y3R1cmUgKG5vZGU6IHRzLlZhcmlhYmxlRGVjbGFyYXRpb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIXRzLmlzT2JqZWN0QmluZGluZ1BhdHRlcm4obm9kZS5uYW1lKSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHNvdXJjZVR5cGUgPSB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShub2RlLmluaXRpYWxpemVyISk7XG5cdFx0aWYgKCFzb3VyY2VUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0Ly8gRXh0cmFjdCBkZXN0cnVjdHVyZWQgcHJvcGVydHkgbmFtZXNcblx0XHRjb25zdCBwcm9wczogc3RyaW5nW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2Ygbm9kZS5uYW1lLmVsZW1lbnRzKSB7XG5cdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGVsZW1lbnQubmFtZSkpIHtcblx0XHRcdFx0cHJvcHMucHVzaChlbGVtZW50Lm5hbWUudGV4dCk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0dGhpcy5hZGRGbG93KHNvdXJjZVR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICA6ICdkZXN0cnVjdHVyZVJlYWQnLFxuXHRcdFx0Y29kZSxcblx0XHRcdHRhcmdldFR5cGUgOiBzb3VyY2VUeXBlLFxuXHRcdFx0Y29udGV4dCAgICA6IHByb3BzLmpvaW4oJywgJylcblx0XHR9KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDb2xsZWN0IHJldHVybiBmbG93OiByZXR1cm4gdXNlclxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0Rmxvd1JldHVybiAobm9kZTogdHMuUmV0dXJuU3RhdGVtZW50LCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3QgcmV0dXJuVHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbiEpO1xuXHRcdGlmICghcmV0dXJuVHlwZSkgeyByZXR1cm47IH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdGNvbnN0IGNvZGUgPSBub2RlLmdldFRleHQoc291cmNlRmlsZSkuc2xpY2UoMCwgMTAwKTtcblxuXHRcdHRoaXMuYWRkRmxvdyhyZXR1cm5UeXBlLCB7XG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGtpbmQgICAgICAgOiAncmV0dXJuJyxcblx0XHRcdGNvZGUsXG5cdFx0XHR0YXJnZXRUeXBlIDogcmV0dXJuVHlwZVxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIENvbGxlY3Qgc3ByZWFkIGZsb3c6IHsgLi4udXNlciB9XG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RGbG93U3ByZWFkIChub2RlOiB0cy5TcHJlYWRFbGVtZW50LCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3Qgc3ByZWFkVHlwZSA9IHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKG5vZGUuZXhwcmVzc2lvbik7XG5cdFx0aWYgKCFzcHJlYWRUeXBlKSB7IHJldHVybjsgfVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0dGhpcy5hZGRGbG93KHNwcmVhZFR5cGUsIHtcblx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0a2luZCAgICAgICA6ICdzcHJlYWQnLFxuXHRcdFx0Y29kZSxcblx0XHRcdHRhcmdldFR5cGUgOiBzcHJlYWRUeXBlXG5cdFx0fSk7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSB0eXBlIGZyb20gYW4gZXhwcmVzc2lvbiAoaWRlbnRpZmllciwgcHJvcGVydHkgYWNjZXNzLCBldGMuKVxuXHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlRXhwcmVzc2lvblR5cGUgKGV4cHI6IHRzLkV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdC8vIElkZW50aWZpZXI6IHVzZXJcblx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGV4cHIpKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy52YXJpYWJsZVRvVHlwZU1hcC5nZXQoZXhwci50ZXh0KTtcblx0XHR9XG5cblx0XHQvLyBQcm9wZXJ0eSBhY2Nlc3M6IHVzZXIubmFtZSAocmV0dXJuIG9iamVjdCB0eXBlLCBub3QgcHJvcGVydHkgdHlwZSlcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oZXhwcikpIHtcblx0XHRcdHJldHVybiB0aGlzLnJlc29sdmVFeHByZXNzaW9uVHlwZShleHByLmV4cHJlc3Npb24pO1xuXHRcdH1cblxuXHRcdC8vIEVsZW1lbnQgYWNjZXNzOiB1c2VyWyduYW1lJ11cblx0XHRpZiAodHMuaXNFbGVtZW50QWNjZXNzRXhwcmVzc2lvbihleHByKSkge1xuXHRcdFx0cmV0dXJuIHRoaXMucmVzb2x2ZUV4cHJlc3Npb25UeXBlKGV4cHIuZXhwcmVzc2lvbik7XG5cdFx0fVxuXG5cdFx0Ly8gVGhpcyBleHByZXNzaW9uOiB0aGlzIChpZiBpbiBhIG1ldGhvZCwgd2UgY2FuJ3QgcmVzb2x2ZSB3aXRob3V0IG1vcmUgY29udGV4dClcblx0XHRpZiAoZXhwci5raW5kID09PSB0cy5TeW50YXhLaW5kLlRoaXNLZXl3b3JkKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogQWRkIGEgZmxvdyB1c2FnZSB0byB0aGUgY29sbGVjdGlvblxuXHQgKi9cblx0cHJpdmF0ZSBhZGRGbG93ICh0eXBlUGF0aDogc3RyaW5nLCBpbmZvOiBGbG93SW5mbyk6IHZvaWQge1xuXHRcdGlmICghdGhpcy5mbG93VXNhZ2VzLmhhcyh0eXBlUGF0aCkpIHtcblx0XHRcdHRoaXMuZmxvd1VzYWdlcy5zZXQodHlwZVBhdGgsIFtdKTtcblx0XHR9XG5cblx0XHRjb25zdCBleGlzdGluZyA9IHRoaXMuZmxvd1VzYWdlcy5nZXQodHlwZVBhdGgpITtcblx0XHRjb25zdCBpc0R1cGxpY2F0ZSA9IGV4aXN0aW5nLnNvbWUoZSA9PiB7XG5cdFx0XHRyZXR1cm4gZS5sb2NhdGlvbiA9PT0gaW5mby5sb2NhdGlvbiAmJlxuXHRcdFx0XHRlLmtpbmQgPT09IGluZm8ua2luZCAmJlxuXHRcdFx0XHRlLmNvZGUgPT09IGluZm8uY29kZTtcblx0XHR9KTtcblxuXHRcdGlmICghaXNEdXBsaWNhdGUpIHtcblx0XHRcdGV4aXN0aW5nLnB1c2goaW5mbyk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdFx0XHQqIEdldCB0eXBlIG5hbWUgZnJvbSBleHByZXNzaW9uIChpZGVudGlmaWVyIG9yIHByb3BlcnR5IGFjY2Vzcylcblx0XHRcdCovXG5cdHByaXZhdGUgZ2V0VHlwZU5hbWVGcm9tRXhwcmVzc2lvbiAoZXhwcjogdHMuRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKHRzLmlzSWRlbnRpZmllcihleHByKSkge1xuXHRcdFx0Y29uc3QgbmFtZSA9IGV4cHIudGV4dDtcblx0XHRcdC8vIENoZWNrIGlmIHRoaXMgaWRlbnRpZmllciBpcyBhIHZhcmlhYmxlIG1hcHBlZCB0byBhIHR5cGUgKGUuZy4sIGZyb20gbG9va3VwKVxuXHRcdFx0Y29uc3QgbWFwcGVkVHlwZSA9IHRoaXMudmFyaWFibGVUb1R5cGVNYXAuZ2V0KG5hbWUpO1xuXHRcdFx0aWYgKG1hcHBlZFR5cGUpIHtcblx0XHRcdFx0cmV0dXJuIG1hcHBlZFR5cGU7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gbmFtZTtcblx0XHR9XG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGV4cHIpKSB7XG5cdFx0XHRjb25zdCBjaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlDaGFpbihleHByKTtcblx0XHRcdHJldHVybiBjaGFpbi5qb2luKCcuJyk7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0KiBSZXNvbHZlIGZ1bGwgdHlwZSBwYXRoIGZyb20gcHJvcGVydHkgYWNjZXNzXG5cdFx0XHQqL1xuXHRwcml2YXRlIHJlc29sdmVUeXBlUGF0aCAoZXhwcjogdHMuUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBjaGFpbiA9IHRoaXMuZ2V0UHJvcGVydHlDaGFpbihleHByKTtcblx0XHRpZiAoY2hhaW4ubGVuZ3RoID09PSAwKSByZXR1cm4gdW5kZWZpbmVkO1xuXHRcblx0XHQvLyBDaGVjayBpZiB0aGlzIGNoYWluIG1hdGNoZXMgYSBrbm93biB0eXBlXG5cdFx0Y29uc3QgZnVsbFBhdGggPSBjaGFpbi5qb2luKCcuJyk7XG5cdFx0aWYgKHRoaXMuZGVmaW5pdGlvbnMuaGFzKGZ1bGxQYXRoKSkge1xuXHRcdFx0cmV0dXJuIGZ1bGxQYXRoO1xuXHRcdH1cblx0XG5cdFx0Ly8gVHJ5IGp1c3QgdGhlIHByb3BlcnR5IG5hbWVcblx0XHRjb25zdCBwcm9wTmFtZSA9IGNoYWluWyBjaGFpbi5sZW5ndGggLSAxIF07XG5cdFx0Zm9yIChjb25zdCBbIHBhdGggXSBvZiB0aGlzLmRlZmluaXRpb25zKSB7XG5cdFx0XHRpZiAocGF0aC5lbmRzV2l0aChgLiR7cHJvcE5hbWV9YCkgfHwgcGF0aCA9PT0gcHJvcE5hbWUpIHtcblx0XHRcdFx0cmV0dXJuIHBhdGg7XG5cdFx0XHR9XG5cdFx0fVxuXHRcblx0XHRyZXR1cm4gZnVsbFBhdGg7XG5cdH1cblx0XG5cdC8qKlxuXHRcdFx0ICogQ2hlY2sgaWYgYSBuYW1lIGxvb2tzIGxpa2UgYSB0eXBlIChzdGFydHMgd2l0aCB1cHBlcmNhc2UpXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSBpc0xpa2VseVR5cGVOYW1lIChuYW1lOiBzdHJpbmcpOiBib29sZWFuIHtcblx0XHRyZXR1cm4gbmFtZVsgMCBdID49ICdBJyAmJiBuYW1lWyAwIF0gPD0gJ1onO1xuXHR9XG5cdFxuXHQvKipcblx0XHRcdCAqIFJlc29sdmUgYSBjb25zdHJ1Y3RvciBwYXJhbWV0ZXIgdHlwZSwgZXhwYW5kaW5nIGlubGluZSBvYmplY3QgbGl0ZXJhbHNcblx0XHRcdCAqIGFuZCB0eXBlIGFsaWFzZXMgd2hlcmUgcG9zc2libGUuXG5cdFx0XHQgKi9cblx0cHJpdmF0ZSByZXNvbHZlQ29uc3RydWN0b3JQYXJhbVR5cGUgKHR5cGVOb2RlOiB0cy5UeXBlTm9kZSB8IHVuZGVmaW5lZCk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0aWYgKCF0eXBlTm9kZSkgcmV0dXJuIHVuZGVmaW5lZDtcblxuXHRcdC8vIERpcmVjdCBpbmxpbmUgdHlwZSBsaXRlcmFsOiB7IHByb3A6IHR5cGUgfVxuXHRcdGlmICh0cy5pc1R5cGVMaXRlcmFsTm9kZSh0eXBlTm9kZSkpIHtcblx0XHRcdGNvbnN0IHByb3BzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgdHlwZU5vZGUubWVtYmVycykge1xuXHRcdFx0XHRpZiAodHMuaXNQcm9wZXJ0eVNpZ25hdHVyZShtZW1iZXIpICYmIHRzLmlzSWRlbnRpZmllcihtZW1iZXIubmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBwcm9wTmFtZSA9IG1lbWJlci5uYW1lLnRleHQ7XG5cdFx0XHRcdFx0Y29uc3Qgb3B0aW9uYWwgPSBtZW1iZXIucXVlc3Rpb25Ub2tlbiA/ICc/JyA6ICcnO1xuXHRcdFx0XHRcdGNvbnN0IHR5cGUgPSB0aGlzLmluZmVyVHlwZShtZW1iZXIudHlwZSk7XG5cdFx0XHRcdFx0cHJvcHMucHVzaChgJHtwcm9wTmFtZX0ke29wdGlvbmFsfTogJHt0eXBlfWApO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gYHsgJHtwcm9wcy5qb2luKCc7ICcpfSB9YDtcblx0XHR9XG5cblx0XHQvLyBUeXBlIHJlZmVyZW5jZTogdXNhZ2UsIFVzZXJEYXRhLCBldGMuIC0gcmVzb2x2ZSBpbXBvcnQtYXdhcmUgYW5kXG5cdFx0Ly8gZXhwYW5kIHRoZSByZWZlcmVuY2VkIGRlY2xhcmF0aW9uIHdoZXJlIHBvc3NpYmxlIChGMTApXG5cdFx0aWYgKHRzLmlzVHlwZVJlZmVyZW5jZU5vZGUodHlwZU5vZGUpICYmIHRzLmlzSWRlbnRpZmllcih0eXBlTm9kZS50eXBlTmFtZSkpIHtcblx0XHRcdGNvbnN0IHR5cGVOYW1lID0gdHlwZU5vZGUudHlwZU5hbWUudGV4dDtcblx0XHRcdGNvbnN0IGRlY2wgPSB0aGlzLnJlc29sdmVSZWZlcmVuY2VkVHlwZURlY2xhcmF0aW9uKHR5cGVOYW1lLCB0aGlzLmN1cnJlbnRSZWZlcmVuY2VkVHlwZUZpbGUpO1xuXHRcdFx0aWYgKGRlY2wpIHtcblx0XHRcdFx0Y29uc3QgZXhwYW5kZWQgPSB0aGlzLmV4cGFuZFJlZmVyZW5jZWRUeXBlRGVjbGFyYXRpb24oZGVjbCk7XG5cdFx0XHRcdGlmIChleHBhbmRlZCkgcmV0dXJuIGV4cGFuZGVkO1xuXHRcdFx0fVxuXHRcdFx0Ly8gbW5lbW9uaWNhIGdyYXBoIHR5cGVzIGtlZXAgdGhlaXIgc2ltcGxlIG5hbWUg4oCUIHRoZSBnZW5lcmF0b3Jcblx0XHRcdC8vIHVwZ3JhZGVzIHRoZW0gdG8gZnVsbC1wYXRoIGluc3RhbmNlIHR5cGUgbmFtZXMuIFJlc29sdXRpb24gaXNcblx0XHRcdC8vIHBhdGgtYXdhcmUgKGhhcmQtZmFpbCBsYXcpOiBhbWJpZ3VpdHkgYmV0d2VlbiByZWFsIGdyYXBoIHR5cGVzXG5cdFx0XHQvLyByZWNvcmRzIGEgZmF0YWwgZXJyb3IgaW5zdGVhZCBvZiBzaWxlbnRseSBwaWNraW5nIG9uZS5cblx0XHRcdGNvbnN0IGdyYXBoUmVzdWx0ID0gdGhpcy5yZXNvbHZlR3JhcGhUeXBlTmFtZSh0eXBlTmFtZSk7XG5cdFx0XHRpZiAoZ3JhcGhSZXN1bHQuc3RhdHVzID09PSAndW5pcXVlJykge1xuXHRcdFx0XHRjb25zdCBzaW1wbGVSZXN1bHQgPSB0eXBlTmFtZTtcblx0XHRcdFx0cmV0dXJuIHNpbXBsZVJlc3VsdDtcblx0XHRcdH1cblx0XHRcdGlmIChncmFwaFJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHRcdHRoaXMucmVjb3JkR3JhcGhSZWZlcmVuY2VFcnJvcih0eXBlTmFtZSwgdHlwZU5vZGUsIGdyYXBoUmVzdWx0KTtcblx0XHRcdFx0Y29uc3QgdW5rbm93bkdyYXBoUmVzdWx0ID0gJ3Vua25vd24nO1xuXHRcdFx0XHRyZXR1cm4gdW5rbm93bkdyYXBoUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0Ly8gSWYgbm90IGFuIG9iamVjdCB0eXBlIGFsaWFzLCByZXR1cm4gdGhlIHR5cGUgbmFtZSB3aXRoIGFyZ3Ncblx0XHRcdGlmICh0eXBlTm9kZS50eXBlQXJndW1lbnRzICYmIHR5cGVOb2RlLnR5cGVBcmd1bWVudHMubGVuZ3RoID4gMCkge1xuXHRcdFx0XHRpZiAoS05PV05fR0xPQkFMX1RZUEVTLmhhcyh0eXBlTmFtZSkpIHtcblx0XHRcdFx0XHRjb25zdCBhcmdzID0gdHlwZU5vZGUudHlwZUFyZ3VtZW50cy5tYXAoYXJnID0+IHRoaXMuaW5mZXJUeXBlKGFyZykpO1xuXHRcdFx0XHRcdHJldHVybiBgJHt0eXBlTmFtZSAgfTwkeyAgYXJncy5qb2luKCcsICcpICB9PmA7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gZ2VuZXJpYyByZWZlcmVuY2UgdG8gYSBub24tZ2xvYmFsLCBub24tZ3JhcGggdHlwZSBjYW5ub3QgYmVcblx0XHRcdFx0Ly8gZW1pdHRlZCBiYXJlIGludG8gdGhlIGdlbmVyYXRlZCBmaWxlXG5cdFx0XHRcdHRoaXMucmVjb3JkUGxhaW5UeXBlUmVmZXJlbmNlU2l0ZSh0eXBlTmFtZSwgdHlwZU5vZGUpO1xuXHRcdFx0XHRjb25zdCB1bmtub3duR2VuZXJpY1Jlc3VsdCA9ICd1bmtub3duJztcblx0XHRcdFx0cmV0dXJuIHVua25vd25HZW5lcmljUmVzdWx0O1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZmFsbGJhY2tSZXN1bHQgPSB0aGlzLnVucmVzb2x2ZWRUeXBlUmVmZXJlbmNlRmFsbGJhY2sodHlwZU5hbWUsIHR5cGVOb2RlKTtcblx0XHRcdHJldHVybiBmYWxsYmFja1Jlc3VsdDtcblx0XHR9XG5cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9XG5cblx0LyoqXG5cdFx0XHQgKiBFeHRyYWN0IGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgZnJvbSBhIGNsYXNzLWxpa2Ugbm9kZS5cblx0XHRcdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDbGFzc0NvbnN0cnVjdG9yUGFyYW1zIChjbGFzc0xpa2U6IHRzLkNsYXNzRGVjbGFyYXRpb24gfCB0cy5DbGFzc0V4cHJlc3Npb24pOlxuXHRcdENvbnN0cnVjdG9yUGFyYW1JbmZvW10ge1xuXHRcdGNvbnN0IHBhcmFtczogQ29uc3RydWN0b3JQYXJhbUluZm9bXSA9IFtdO1xuXG5cdFx0Zm9yIChjb25zdCBtZW1iZXIgb2YgY2xhc3NMaWtlLm1lbWJlcnMpIHtcblx0XHRcdGlmICghdHMuaXNDb25zdHJ1Y3RvckRlY2xhcmF0aW9uKG1lbWJlcikpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cblx0XHRcdGZvciAoY29uc3QgcGFyYW0gb2YgbWVtYmVyLnBhcmFtZXRlcnMpIHtcblx0XHRcdFx0aWYgKCFwYXJhbS5uYW1lIHx8ICF0cy5pc0lkZW50aWZpZXIocGFyYW0ubmFtZSkpIGNvbnRpbnVlO1xuXHRcdFx0XHRpZiAoIXBhcmFtLnR5cGUpIGNvbnRpbnVlO1xuXG5cdFx0XHRcdGNvbnN0IHBhcmFtTmFtZSA9IHBhcmFtLm5hbWUudGV4dDtcblx0XHRcdFx0Y29uc3QgZXhwYW5kZWRUeXBlID0gdGhpcy5yZXNvbHZlQ29uc3RydWN0b3JQYXJhbVR5cGUocGFyYW0udHlwZSkgfHwgdGhpcy5pbmZlclR5cGUocGFyYW0udHlwZSk7XG5cblx0XHRcdFx0cGFyYW1zLnB1c2goe1xuXHRcdFx0XHRcdG5hbWUgICAgIDogcGFyYW1OYW1lLFxuXHRcdFx0XHRcdHR5cGUgICAgIDogZXhwYW5kZWRUeXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogISFwYXJhbS5xdWVzdGlvblRva2VuIHx8ICEhcGFyYW0uaW5pdGlhbGl6ZXJcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0XHQvLyBPbmx5IHByb2Nlc3MgZmlyc3QgY29uc3RydWN0b3Jcblx0XHRcdGJyZWFrO1xuXHRcdH1cblxuXHRcdHJldHVybiBwYXJhbXM7XG5cdH1cblxuXHQvKipcblx0XHRcdCAqIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGRlZmluZSgpIGNhbGxcblx0XHRcdCAqIFRoaXMgaXMgdXNlZCBmb3IgVHlwZVJlZ2lzdHJ5IGNvbnN0cnVjdG9yIHNpZ25hdHVyZXNcblx0XHRcdCAqIFByZXNlcnZlcyBwYXJhbWV0ZXIgbmFtZXMgYW5kIGV4cGFuZHMgb2JqZWN0IHR5cGVzIHRvIHRoZWlyIHN0cnVjdHVyZVxuXHRcdFx0ICovXG5cdHByaXZhdGUgZXh0cmFjdENvbnN0cnVjdG9yUGFyYW1zIChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IENvbnN0cnVjdG9yUGFyYW1JbmZvW10ge1xuXHRcdGNvbnN0IGNvbnN0cnVjdG9yRXhwciA9IHRoaXMuZXh0cmFjdENvbnN0cnVjdG9yRXhwcmVzc2lvbihjYWxsKTtcblx0XHRpZiAoIWNvbnN0cnVjdG9yRXhwcikge1xuXHRcdFx0cmV0dXJuIFtdO1xuXHRcdH1cblx0XHRjb25zdCByZXN1bHQgPSB0aGlzLmV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtc0Zyb21Db25zdHJ1Y3Rvcihjb25zdHJ1Y3RvckV4cHIpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHRcdCAqIEV4dHJhY3QgY29uc3RydWN0b3IgcGFyYW1ldGVycyBmcm9tIGEgY29uc3RydWN0b3IgZXhwcmVzc2lvbi5cblx0XHRcdCAqL1xuXHRwcml2YXRlIGV4dHJhY3RDb25zdHJ1Y3RvclBhcmFtc0Zyb21Db25zdHJ1Y3RvciAoY29uc3RydWN0b3JFeHByOiB0cy5FeHByZXNzaW9uKTogQ29uc3RydWN0b3JQYXJhbUluZm9bXSB7XG5cdFx0Y29uc3QgcGFyYW1zOiBDb25zdHJ1Y3RvclBhcmFtSW5mb1tdID0gW107XG5cdFxuXHRcdC8vIEhhbmRsZSBmdW5jdGlvbiBleHByZXNzaW9uIG9yIGFycm93IGZ1bmN0aW9uXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25FeHByZXNzaW9uKGNvbnN0cnVjdG9yRXhwcikgfHwgdHMuaXNBcnJvd0Z1bmN0aW9uKGNvbnN0cnVjdG9yRXhwcikpIHtcblx0XHRcdC8vIExvb2sgZm9yIGNvbnN0cnVjdG9yIHBhcmFtZXRlcnMgKHNlY29uZCBwYXJhbSBhZnRlciBgdGhpc2ApXG5cdFx0XHQvLyBQYXR0ZXJuczogZnVuY3Rpb24odGhpczogVHlwZSwgZGF0YTogeyAuLi4gfSkgb3IgKHRoaXM6IFR5cGUsIGRhdGE6IHsgLi4uIH0pID0+XG5cdFx0XHRmb3IgKGxldCBpID0gMDsgaSA8IGNvbnN0cnVjdG9yRXhwci5wYXJhbWV0ZXJzLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRcdGNvbnN0IHBhcmFtID0gY29uc3RydWN0b3JFeHByLnBhcmFtZXRlcnNbIGkgXTtcblx0XHRcdFx0aWYgKCFwYXJhbS50eXBlKSBjb250aW51ZTtcblx0XG5cdFx0XHRcdC8vIFNraXAgYHRoaXNgIHBhcmFtZXRlciAoZmlyc3QgcGFyYW0pXG5cdFx0XHRcdGlmIChcblx0XHRcdFx0XHRpID09PSAwICYmXG5cdFx0XHRcdFx0cGFyYW0ubmFtZS5raW5kID09PSB0cy5TeW50YXhLaW5kLklkZW50aWZpZXIgJiZcblx0XHRcdFx0XHQocGFyYW0ubmFtZSBhcyB0cy5JZGVudGlmaWVyKS50ZXh0ID09PSAndGhpcydcblx0XHRcdFx0KSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XG5cdFx0XHRcdC8vIEdldCBwYXJhbWV0ZXIgbmFtZSBhbmQgZXhwYW5kIGl0cyB0eXBlXG5cdFx0XHRcdGNvbnN0IHBhcmFtTmFtZSA9IHRzLmlzSWRlbnRpZmllcihwYXJhbS5uYW1lKSA/IHBhcmFtLm5hbWUudGV4dCA6ICdhcmcnO1xuXHRcdFx0XHRjb25zdCBleHBhbmRlZFR5cGUgPSB0aGlzLnJlc29sdmVDb25zdHJ1Y3RvclBhcmFtVHlwZShwYXJhbS50eXBlKSB8fCB0aGlzLmluZmVyVHlwZShwYXJhbS50eXBlKTtcblx0XHRcdFx0XHRcblx0XHRcdFx0cGFyYW1zLnB1c2goe1xuXHRcdFx0XHRcdG5hbWUgICAgIDogcGFyYW1OYW1lLFxuXHRcdFx0XHRcdHR5cGUgICAgIDogZXhwYW5kZWRUeXBlLFxuXHRcdFx0XHRcdG9wdGlvbmFsIDogISFwYXJhbS5xdWVzdGlvblRva2VuIHx8ICEhcGFyYW0uaW5pdGlhbGl6ZXJcblx0XHRcdFx0fSk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcblx0XHQvLyBIYW5kbGUgY2xhc3MgZXhwcmVzc2lvbiAtIGNoZWNrIGNvbnN0cnVjdG9yIG1ldGhvZFxuXHRcdGlmICh0cy5pc0NsYXNzRXhwcmVzc2lvbihjb25zdHJ1Y3RvckV4cHIpKSB7XG5cdFx0XHRjb25zdCBjbGFzc1BhcmFtcyA9IHRoaXMuZXh0cmFjdENsYXNzQ29uc3RydWN0b3JQYXJhbXMoY29uc3RydWN0b3JFeHByKTtcblx0XHRcdGZvciAoY29uc3QgcGFyYW0gb2YgY2xhc3NQYXJhbXMpIHtcblx0XHRcdFx0cGFyYW1zLnB1c2gocGFyYW0pO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBwYXJhbXM7XG5cdH1cblxuXHQvKipcblx0ICogQ29sbGVjdCBmcmFtZXdvcmsgaW5zdHJ1bWVudGF0aW9uIHBvaW50cy4gUHVyZWx5IHN5bnRhY3RpYzogaGVyaXRhZ2Vcblx0ICogY2xhdXNlcywgZGVjb3JhdG9yIGFwcGxpY2F0aW9uIHNpdGVzLCBwcm92aWRlci10b2tlbiBvYmplY3QgbGl0ZXJhbHNcblx0ICogYW5kIGNvbnN1bWVyLmFwcGx5KCkuZm9yUm91dGVzKCkgd2lyaW5nLiBUaGUgdm9jYWJ1bGFyeSBjb21lcyBmcm9tXG5cdCAqIHBsdWdpbnM7IGlkZW50aWZpZXIgdGV4dCBpcyBtYXRjaGVkIGFzLWlzIOKAlCBubyBpbXBvcnQgcmVzb2x1dGlvbixcblx0ICogdGhlIHR5cGUgY2hlY2tlciBzdGF5cyB1bnVzZWQuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RJbnN0cnVtZW50YXRpb24gKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKG5vZGUpICYmIG5vZGUubmFtZSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uQ2xhc3Mobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0RlY29yYXRvcihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uRGVjb3JhdG9yKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0XHRpZiAodHMuaXNPYmplY3RMaXRlcmFsRXhwcmVzc2lvbihub2RlKSkge1xuXHRcdFx0dGhpcy5jb2xsZWN0SW5zdHJ1bWVudGF0aW9uUHJvdmlkZXIobm9kZSwgc291cmNlRmlsZSk7XG5cdFx0fVxuXHRcdGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKG5vZGUpKSB7XG5cdFx0XHR0aGlzLmNvbGxlY3RJbnN0cnVtZW50YXRpb25NaWRkbGV3YXJlKG5vZGUsIHNvdXJjZUZpbGUpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBSZWNvcmQgYSBuYW1lZCBjbGFzcyBkZWNsYXJhdGlvbiBmb3IgaW5zdHJ1bWVudGF0aW9uIHNpdGUgcmVzb2x1dGlvblxuXHQgKiBhbmQgZGV0ZWN0IGhlcml0YWdlLWJhc2VkIGtpbmRzIChgaW1wbGVtZW50cyA8cGx1Z2luIGludGVyZmFjZT5gKVxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0SW5zdHJ1bWVudGF0aW9uQ2xhc3MgKG5vZGU6IHRzLkNsYXNzRGVjbGFyYXRpb24sIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiB2b2lkIHtcblx0XHRpZiAoIW5vZGUubmFtZSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRjb25zdCBjbGFzc05hbWUgPSBub2RlLm5hbWUudGV4dDtcblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5uYW1lLmdldFN0YXJ0KHNvdXJjZUZpbGUpXG5cdFx0KTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OiR7bGluZSArIDF9OiR7Y2hhcmFjdGVyICsgMX1gO1xuXHRcdC8vIEZpcnN0IGxpbmUgb2YgdGhlIGRlY2xhcmF0aW9uLCBsaWtlIEVEUyBgY29kZWAgc25pcHBldHNcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNwbGl0KCdcXG4nKVsgMCBdLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRsZXQga2luZDogSW5zdHJ1bWVudGF0aW9uS2luZCB8IHVuZGVmaW5lZDtcblx0XHRpZiAobm9kZS5oZXJpdGFnZUNsYXVzZXMpIHtcblx0XHRcdGZvciAoY29uc3QgY2xhdXNlIG9mIG5vZGUuaGVyaXRhZ2VDbGF1c2VzKSB7XG5cdFx0XHRcdGlmIChjbGF1c2UudG9rZW4gIT09IHRzLlN5bnRheEtpbmQuSW1wbGVtZW50c0tleXdvcmQpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRmb3IgKGNvbnN0IHR5cGUgb2YgY2xhdXNlLnR5cGVzKSB7XG5cdFx0XHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIodHlwZS5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdGNvbnN0IG1hdGNoZWQgPSB0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkuaW50ZXJmYWNlc1sgdHlwZS5leHByZXNzaW9uLnRleHQgXTtcblx0XHRcdFx0XHRpZiAobWF0Y2hlZCkge1xuXHRcdFx0XHRcdFx0a2luZCA9IG1hdGNoZWQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgZGVjbDogSW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNsID0ge1xuXHRcdFx0bG9jYXRpb24sXG5cdFx0XHRjb2RlLFxuXHRcdH07XG5cdFx0aWYgKGtpbmQpIHtcblx0XHRcdGRlY2wua2luZCA9IGtpbmQ7XG5cdFx0fVxuXHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uQ2xhc3NEZWNscy5zZXQoY2xhc3NOYW1lLCBkZWNsKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBEZXRlY3QgZGVjb3JhdG9yIGFwcGxpY2F0aW9uIHNpdGVzOiBwbHVnaW4tbGlzdGVkIGRlY29yYXRvcnMgYXBwbGllZFxuXHQgKiB3aXRoIGNsYXNzIGFyZ3VtZW50cyBvbiBhIGNsYXNzIG9yIG9uZSBvZiBpdHMgbWV0aG9kcy4gT25lIHNpdGUgcGVyXG5cdCAqIHJlZmVyZW5jZWQgY2xhc3MgaWRlbnRpZmllci5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEluc3RydW1lbnRhdGlvbkRlY29yYXRvciAobm9kZTogdHMuRGVjb3JhdG9yLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBub2RlO1xuXHRcdGlmICghdHMuaXNDYWxsRXhwcmVzc2lvbihleHByZXNzaW9uKSB8fCAhdHMuaXNJZGVudGlmaWVyKGV4cHJlc3Npb24uZXhwcmVzc2lvbikpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3Qga2luZCA9IHRoaXMuaW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeS51c2VEZWNvcmF0b3JzWyBleHByZXNzaW9uLmV4cHJlc3Npb24udGV4dCBdO1xuXHRcdGlmICgha2luZCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIFRoZSBkZWNvcmF0b3IncyBwYXJlbnQgaXMgdGhlIGRlY29yYXRlZCBub2RlOiBhIGNvbnRyb2xsZXIgY2xhc3MsXG5cdFx0Ly8gb25lIG9mIGl0cyBtZXRob2RzLCBvciBvbmUgb2YgaXRzIG1ldGhvZCBwYXJhbWV0ZXJzXG5cdFx0Ly8gKEBCb2R5KG12cC5mb3JUeXBlKER0bykpIG9uIGEgaGFuZGxlciBhcmd1bWVudClcblx0XHRjb25zdCBkZWNvcmF0ZWQgPSBub2RlLnBhcmVudDtcblx0XHRsZXQgc2NvcGU6IEluc3RydW1lbnRhdGlvblNjb3BlO1xuXHRcdGxldCB0YXJnZXRzOiBzdHJpbmdbXTtcblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKGRlY29yYXRlZCkgJiYgZGVjb3JhdGVkLm5hbWUpIHtcblx0XHRcdHNjb3BlID0gYGNvbnRyb2xsZXI6JHtkZWNvcmF0ZWQubmFtZS50ZXh0fWA7XG5cdFx0XHR0YXJnZXRzID0gWyBkZWNvcmF0ZWQubmFtZS50ZXh0IF07XG5cdFx0fSBlbHNlIGlmIChcblx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24oZGVjb3JhdGVkKSAmJlxuXHRcdFx0dHMuaXNJZGVudGlmaWVyKGRlY29yYXRlZC5uYW1lKSAmJlxuXHRcdFx0dHMuaXNDbGFzc0RlY2xhcmF0aW9uKGRlY29yYXRlZC5wYXJlbnQpICYmXG5cdFx0XHRkZWNvcmF0ZWQucGFyZW50Lm5hbWVcblx0XHQpIHtcblx0XHRcdGNvbnN0IGNsYXNzTmFtZSA9IGRlY29yYXRlZC5wYXJlbnQubmFtZS50ZXh0O1xuXHRcdFx0c2NvcGUgPSBgbWV0aG9kOiR7Y2xhc3NOYW1lfS4ke2RlY29yYXRlZC5uYW1lLnRleHR9YDtcblx0XHRcdHRhcmdldHMgPSBbIGNsYXNzTmFtZSBdO1xuXHRcdH0gZWxzZSBpZiAodHMuaXNQYXJhbWV0ZXIoZGVjb3JhdGVkKSkge1xuXHRcdFx0Ly8gUGFyYW1ldGVyIGRlY29yYXRvcnMgdGFrZSB0aGUgZW5jbG9zaW5nIG1ldGhvZCdzIHNjb3BlIOKAlCB0aGVcblx0XHRcdC8vIGF0dGFjaG1lbnQgcG9pbnQgaXMgdGhlIGhhbmRsZXIsIG5vdCB0aGUgYXJndW1lbnQgbmFtZTsgdGhlXG5cdFx0XHQvLyBzYW1lIG1ldGhvZDpDbGFzcy5tZXRob2QgZm9ybSBhcyBtZXRob2QtbGV2ZWwgc2l0ZXMuIFBhcmFtcyBvZlxuXHRcdFx0Ly8gY29uc3RydWN0b3JzLCBmdW5jdGlvbnMsIGFuZCB1bm5hbWVhYmxlIGhvc3RzIHN0YXkgc2lsZW50LCB0aGVcblx0XHRcdC8vIHNhbWUgY29udmVudGlvbiBhcyBvdGhlciB1bnJlc29sdmFibGUgZGVjb3JhdG9yIHBhcmVudHNcblx0XHRcdGNvbnN0IGhvc3QgPSBkZWNvcmF0ZWQucGFyZW50O1xuXHRcdFx0aWYgKFxuXHRcdFx0XHRob3N0ICYmXG5cdFx0XHRcdHRzLmlzTWV0aG9kRGVjbGFyYXRpb24oaG9zdCkgJiZcblx0XHRcdFx0dHMuaXNJZGVudGlmaWVyKGhvc3QubmFtZSkgJiZcblx0XHRcdFx0dHMuaXNDbGFzc0RlY2xhcmF0aW9uKGhvc3QucGFyZW50KSAmJlxuXHRcdFx0XHRob3N0LnBhcmVudC5uYW1lXG5cdFx0XHQpIHtcblx0XHRcdFx0Y29uc3QgY2xhc3NOYW1lID0gaG9zdC5wYXJlbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRzY29wZSA9IGBtZXRob2Q6JHtjbGFzc05hbWV9LiR7aG9zdC5uYW1lLnRleHR9YDtcblx0XHRcdFx0dGFyZ2V0cyA9IFsgY2xhc3NOYW1lIF07XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRyZXR1cm47XG5cdFx0XHR9XG5cdFx0fSBlbHNlIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gdHMuZ2V0TGluZUFuZENoYXJhY3Rlck9mUG9zaXRpb24oXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bm9kZS5nZXRTdGFydChzb3VyY2VGaWxlKVxuXHRcdCk7XG5cdFx0Y29uc3QgbG9jYXRpb24gPSBgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YDtcblx0XHRjb25zdCBjb2RlID0gbm9kZS5nZXRUZXh0KHNvdXJjZUZpbGUpLnNsaWNlKDAsIDEwMCk7XG5cblx0XHRmb3IgKGNvbnN0IGFyZyBvZiBleHByZXNzaW9uLmFyZ3VtZW50cykge1xuXHRcdFx0Ly8gQ2xhc3MgcmVmZXJlbmNlOiBAUmVnaXN0ZXIoSW1wbCkgb3IgYW4gaW5saW5lIGluc3RhbmNlOlxuXHRcdFx0Ly8gQFJlZ2lzdGVyKG5ldyBJbXBsKHsgLi4ub3B0aW9ucyB9KSlcblx0XHRcdGxldCBjbGFzc05hbWU6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRcdC8vIHBlci1hcmcga2luZDogZmFjdG9yeS1jYWxsIGFyZ3MgY2FycnkgdGhlaXIgb3duIGNvbmZpZ3VyZWRcblx0XHRcdC8vIGtpbmQsIGV2ZXJ5dGhpbmcgZWxzZSB0YWtlcyB0aGUgZGVjb3JhdG9yJ3Ncblx0XHRcdGxldCBhcmdLaW5kID0ga2luZDtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0XHRjbGFzc05hbWUgPSBhcmcudGV4dDtcblx0XHRcdH0gZWxzZSBpZiAodHMuaXNOZXdFeHByZXNzaW9uKGFyZykgJiYgdHMuaXNJZGVudGlmaWVyKGFyZy5leHByZXNzaW9uKSkge1xuXHRcdFx0XHRjbGFzc05hbWUgPSBhcmcuZXhwcmVzc2lvbi50ZXh0O1xuXHRcdFx0fSBlbHNlIGlmICh0cy5pc0NhbGxFeHByZXNzaW9uKGFyZykgJiYgdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24oYXJnLmV4cHJlc3Npb24pKSB7XG5cdFx0XHRcdC8vIFBpcGUtZmFjdG9yeSBzaGFwZTogQFVzZVBpcGVzKG12cC5mb3JUeXBlKER0bykpIOKAlCB0aGVcblx0XHRcdFx0Ly8gY2FsbCdzIG1ldGhvZCBuYW1lIGlzIHBsdWdpbi1saXN0ZWQsIHRoZSB0YXJnZXQgY2xhc3Mgc2l0c1xuXHRcdFx0XHQvLyBpbiB0aGUgY29uZmlndXJlZCBhcmd1bWVudCBwb3NpdGlvbiAoZGVmYXVsdCAwKVxuXHRcdFx0XHRjb25zdCBmYWN0b3J5ID0gdGhpcy5pbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5LmRlY29yYXRvckFyZ0ZhY3Rvcmllc1sgYXJnLmV4cHJlc3Npb24ubmFtZS50ZXh0IF07XG5cdFx0XHRcdGlmIChmYWN0b3J5KSB7XG5cdFx0XHRcdFx0Y29uc3QgdGFyZ2V0QXJnID0gYXJnLmFyZ3VtZW50c1sgZmFjdG9yeS50YXJnZXRBcmcgPz8gMCBdO1xuXHRcdFx0XHRcdGlmICh0YXJnZXRBcmcgJiYgdHMuaXNJZGVudGlmaWVyKHRhcmdldEFyZykpIHtcblx0XHRcdFx0XHRcdGNsYXNzTmFtZSA9IHRhcmdldEFyZy50ZXh0O1xuXHRcdFx0XHRcdFx0YXJnS2luZCA9IGZhY3Rvcnkua2luZDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHRcdGlmICghY2xhc3NOYW1lKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0dGhpcy5pbnN0cnVtZW50YXRpb25TaXRlcy5wdXNoKHtcblx0XHRcdFx0a2luZCA6IGFyZ0tpbmQsXG5cdFx0XHRcdGNsYXNzTmFtZSxcblx0XHRcdFx0bG9jYXRpb24sXG5cdFx0XHRcdGNvZGUsXG5cdFx0XHRcdHNjb3BlLFxuXHRcdFx0XHR0YXJnZXRzLFxuXHRcdFx0fSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIERldGVjdCBnbG9iYWwgcmVnaXN0cmF0aW9uczogb2JqZWN0IGxpdGVyYWxzIHNoYXBlZCBsaWtlXG5cdCAqIGB7IHByb3ZpZGU6IDxwbHVnaW4tbGlzdGVkIHRva2VuPiwgdXNlQ2xhc3M6IFggfWAuXG5cdCAqIHVzZUV4aXN0aW5nL3VzZUZhY3Rvcnkgd2l0aG91dCBhIHVzZUNsYXNzIGlkZW50aWZpZXIgYXJlIG5vdFxuXHQgKiBzdGF0aWNhbGx5IG9idmlvdXMg4oCUIHNraXBwZWQgcmF0aGVyIHRoYW4gZ3Vlc3NlZC5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEluc3RydW1lbnRhdGlvblByb3ZpZGVyIChub2RlOiB0cy5PYmplY3RMaXRlcmFsRXhwcmVzc2lvbiwgc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IHZvaWQge1xuXHRcdGxldCBraW5kOiBJbnN0cnVtZW50YXRpb25LaW5kIHwgdW5kZWZpbmVkO1xuXHRcdGxldCB1c2VDbGFzc05hbWU6IHN0cmluZyB8IHVuZGVmaW5lZDtcblxuXHRcdGZvciAoY29uc3QgcHJvcCBvZiBub2RlLnByb3BlcnRpZXMpIHtcblx0XHRcdGlmIChcblx0XHRcdFx0IXRzLmlzUHJvcGVydHlBc3NpZ25tZW50KHByb3ApIHx8XG5cdFx0XHRcdCF0cy5pc0lkZW50aWZpZXIocHJvcC5uYW1lKSB8fFxuXHRcdFx0XHQhdHMuaXNJZGVudGlmaWVyKHByb3AuaW5pdGlhbGl6ZXIpXG5cdFx0XHQpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRpZiAocHJvcC5uYW1lLnRleHQgPT09ICdwcm92aWRlJykge1xuXHRcdFx0XHRraW5kID0gdGhpcy5pbnN0cnVtZW50YXRpb25Wb2NhYnVsYXJ5LmFwcFRva2Vuc1sgcHJvcC5pbml0aWFsaXplci50ZXh0IF07XG5cdFx0XHR9XG5cdFx0XHRpZiAocHJvcC5uYW1lLnRleHQgPT09ICd1c2VDbGFzcycpIHtcblx0XHRcdFx0dXNlQ2xhc3NOYW1lID0gcHJvcC5pbml0aWFsaXplci50ZXh0O1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGlmICgha2luZCB8fCAhdXNlQ2xhc3NOYW1lKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBsaW5lLCBjaGFyYWN0ZXIgfSA9IHRzLmdldExpbmVBbmRDaGFyYWN0ZXJPZlBvc2l0aW9uKFxuXHRcdFx0c291cmNlRmlsZSxcblx0XHRcdG5vZGUuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0dGhpcy5pbnN0cnVtZW50YXRpb25TaXRlcy5wdXNoKHtcblx0XHRcdGtpbmQsXG5cdFx0XHRjbGFzc05hbWUgOiB1c2VDbGFzc05hbWUsXG5cdFx0XHRsb2NhdGlvbixcblx0XHRcdGNvZGUsXG5cdFx0XHRzY29wZSAgICAgOiAnZ2xvYmFsJyxcblx0XHRcdHRhcmdldHMgICA6IFtdLFxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIERldGVjdCBtaWRkbGV3YXJlIHdpcmluZzogYGNvbnN1bWVyLmFwcGx5KE13MSwgTXcyKS5mb3JSb3V0ZXMoLi4uKWBcblx0ICogaW5zaWRlIGEgY2xhc3MncyBjb25maWd1cmUoKSBtZXRob2QuIFRhcmdldHMgY29tZSBmcm9tIGZvclJvdXRlc1xuXHQgKiBhcmd1bWVudHMgd2hlbiBzdGF0aWNhbGx5IHJlYWRhYmxlIChzdHJpbmcgcm91dGVzIG9yIGNvbnRyb2xsZXJcblx0ICogaWRlbnRpZmllcnMpLCBlbHNlIFtdLiBTaGFwZS1iYXNlZCwgc28gYSBwbHVnaW4gbXVzdCBvcHQgaW4gdmlhXG5cdCAqIGBtaWRkbGV3YXJlV2lyaW5nOiB0cnVlYC5cblx0ICovXG5cdHByaXZhdGUgY29sbGVjdEluc3RydW1lbnRhdGlvbk1pZGRsZXdhcmUgKG5vZGU6IHRzLkNhbGxFeHByZXNzaW9uLCBzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlKTogdm9pZCB7XG5cdFx0aWYgKCF0aGlzLmluc3RydW1lbnRhdGlvblZvY2FidWxhcnkubWlkZGxld2FyZVdpcmluZykge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAoXG5cdFx0XHQhdHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obm9kZS5leHByZXNzaW9uKSB8fFxuXHRcdFx0bm9kZS5leHByZXNzaW9uLm5hbWUudGV4dCAhPT0gJ2ZvclJvdXRlcydcblx0XHQpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgYXBwbHlDYWxsID0gbm9kZS5leHByZXNzaW9uLmV4cHJlc3Npb247XG5cdFx0aWYgKFxuXHRcdFx0IXRzLmlzQ2FsbEV4cHJlc3Npb24oYXBwbHlDYWxsKSB8fFxuXHRcdFx0IXRzLmlzUHJvcGVydHlBY2Nlc3NFeHByZXNzaW9uKGFwcGx5Q2FsbC5leHByZXNzaW9uKSB8fFxuXHRcdFx0YXBwbHlDYWxsLmV4cHJlc3Npb24ubmFtZS50ZXh0ICE9PSAnYXBwbHknXG5cdFx0KSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGlmICghdGhpcy5pc0luc2lkZUNvbmZpZ3VyZU1ldGhvZChub2RlKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHRhcmdldHM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBhcmcgb2Ygbm9kZS5hcmd1bWVudHMpIHtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIoYXJnKSB8fCB0cy5pc1N0cmluZ0xpdGVyYWwoYXJnKSkge1xuXHRcdFx0XHR0YXJnZXRzLnB1c2goYXJnLnRleHQpO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGNvbnN0IHsgbGluZSwgY2hhcmFjdGVyIH0gPSB0cy5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihcblx0XHRcdHNvdXJjZUZpbGUsXG5cdFx0XHRhcHBseUNhbGwuZ2V0U3RhcnQoc291cmNlRmlsZSlcblx0XHQpO1xuXHRcdGNvbnN0IGxvY2F0aW9uID0gYCR7c291cmNlRmlsZS5maWxlTmFtZX06JHtsaW5lICsgMX06JHtjaGFyYWN0ZXIgKyAxfWA7XG5cdFx0Y29uc3QgY29kZSA9IG5vZGUuZ2V0VGV4dChzb3VyY2VGaWxlKS5zbGljZSgwLCAxMDApO1xuXG5cdFx0Zm9yIChjb25zdCBhcmcgb2YgYXBwbHlDYWxsLmFyZ3VtZW50cykge1xuXHRcdFx0aWYgKCF0cy5pc0lkZW50aWZpZXIoYXJnKSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdHRoaXMuaW5zdHJ1bWVudGF0aW9uU2l0ZXMucHVzaCh7XG5cdFx0XHRcdGtpbmQgICAgICA6ICdtaWRkbGV3YXJlJyxcblx0XHRcdFx0Y2xhc3NOYW1lIDogYXJnLnRleHQsXG5cdFx0XHRcdGxvY2F0aW9uLFxuXHRcdFx0XHRjb2RlLFxuXHRcdFx0XHRzY29wZSAgICAgOiAnbW9kdWxlJyxcblx0XHRcdFx0dGFyZ2V0cyxcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBXYWxrIHVwIHRoZSBwYXJlbnQgY2hhaW4gbG9va2luZyBmb3IgYW4gZW5jbG9zaW5nIGNvbmZpZ3VyZSgpIG1ldGhvZFxuXHQgKi9cblx0cHJpdmF0ZSBpc0luc2lkZUNvbmZpZ3VyZU1ldGhvZCAobm9kZTogdHMuTm9kZSk6IGJvb2xlYW4ge1xuXHRcdGxldCBjdXJyZW50OiB0cy5Ob2RlIHwgdW5kZWZpbmVkID0gbm9kZS5wYXJlbnQ7XG5cdFx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRcdGlmIChcblx0XHRcdFx0dHMuaXNNZXRob2REZWNsYXJhdGlvbihjdXJyZW50KSAmJlxuXHRcdFx0XHR0cy5pc0lkZW50aWZpZXIoY3VycmVudC5uYW1lKSAmJlxuXHRcdFx0XHRjdXJyZW50Lm5hbWUudGV4dCA9PT0gJ2NvbmZpZ3VyZSdcblx0XHRcdCkge1xuXHRcdFx0XHRyZXR1cm4gdHJ1ZTtcblx0XHRcdH1cblx0XHRcdGN1cnJlbnQgPSBjdXJyZW50LnBhcmVudDtcblx0XHR9XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG59XG4iXX0=