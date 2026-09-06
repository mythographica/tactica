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
exports.CreationGraphBuilder = void 0;
const path = __importStar(require("path"));
const ts = __importStar(require("typescript"));
/**
 * Inside-out creation walker (instrumentation walker plan, Phase 3).
 *
 * Starts at the certain points — instantiation usages carrying a
 * holderScopeId — then walks OUTWARD: who invokes or references the holder,
 * crossing files through the module graph (barrels chased the same way
 * ModuleGraphBuilder.resolveOrigin does), until no callers remain. Terminals
 * are the starters (application entry points). The walk never assumes a
 * linear Trie (decision 1: strictChain:false permits cycles/out-of-order
 * construction), so traversal is cycle-guarded DFS, and every anchor records
 * which constructor expression was actually used.
 *
 * Deliberate approximations (no getTypeChecker(), name-based only):
 * - Namespace imports (`import * as ns`): when the namespace's source module
 *   exposes the holder's export, ANY reference to the alias counts as a
 *   caller reference.
 * - Method scopes bind to their CLASS name (callers reference the class);
 *   instance-method call sites (`obj.method()`) are not distinguishable
 *   without the checker.
 * - Any non-declaration identifier counts as a reference (invocations,
 *   pass-as-arg, rebinding); type-position references are not filtered.
 * - Module scopes end the invocation walk, but a terminal module still
 *   gains its IMPORTERS as callers: entry modules hand classes to the
 *   framework as values (a bootstrap call receiving the root module),
 *   which no call-walk can see — the import relation bridges them to
 *   the center.
 */
class CreationGraphBuilder {
    constructor(moduleGraph, scopeAnalysis, scopeWalker, sourceFiles) {
        /** filePath -> (identifier text -> reference locations), built lazily per file */
        this.referencesByFile = new Map();
        this.moduleGraph = moduleGraph;
        this.scopeAnalysis = scopeAnalysis;
        this.scopeWalker = scopeWalker;
        this.sourceFiles = sourceFiles;
    }
    /**
     * Build the creation graph from the analyzer's usages (holderScopeId
     * already attached). Always returns a graph, empty arrays when nothing
     * creates mnemonica instances.
     */
    build(usages) {
        const anchors = this.collectAnchors(usages);
        const nodes = new Map();
        const edges = [];
        const seenEdges = new Set();
        // scopeIds with at least one caller — everyone else is a starter
        const called = new Set();
        const visited = new Set();
        const work = anchors.map(anchor => anchor.holderScopeId);
        const addEdge = (caller, callee) => {
            const key = `${caller}\n${callee}`;
            if (seenEdges.has(key)) {
                return;
            }
            seenEdges.add(key);
            edges.push({ caller, callee });
            called.add(callee);
        };
        while (work.length > 0) {
            const scopeId = work.pop();
            if (!scopeId || visited.has(scopeId)) {
                continue;
            }
            visited.add(scopeId);
            const scope = this.scopeAnalysis.scopes.get(scopeId);
            if (!scope) {
                continue;
            }
            nodes.set(scopeId, CreationGraphBuilder.nodeOf(scope));
            if (scope.kind === 'module') {
                // Module scopes END the invocation walk — nobody invokes a
                // module (a module-scope creation is labeled rooted on the
                // anchor instead). But entry modules hand their classes to
                // the framework as VALUES (a bootstrap call receiving the
                // root module, or framework metadata listing controllers),
                // invisible to
                // call-walking — so a terminal module still gains its
                // IMPORTERS as callers: main.ts importing AppModule yields
                // the main.ts → app.module edge the pure call graph misses.
                for (const importer of this.importersOf(scope.filePath)) {
                    addEdge(importer, scopeId);
                    if (!visited.has(importer)) {
                        work.push(importer);
                    }
                }
                continue;
            }
            const bindingName = CreationGraphBuilder.bindingNameOf(scope);
            if (!bindingName) {
                // Anonymous holder (file:line label): never referenced by name
                continue;
            }
            // Plan-sketch refinement: same-file references are followed for
            // EVERY holder, exported or not — an exported function can also be
            // called from its own module, and both paths lead outward.
            const sameFileCallers = this.callersOf(scope.filePath, bindingName);
            const crossFileCallers = this.findCrossFileCallers(scope, bindingName);
            for (const caller of [...sameFileCallers, ...crossFileCallers]) {
                // Direct recursion (f calls f) adds no outward information
                if (caller === scopeId) {
                    continue;
                }
                addEdge(caller, scopeId);
                if (!visited.has(caller)) {
                    work.push(caller);
                }
            }
        }
        for (const node of nodes.values()) {
            node.starter = !called.has(node.scopeId);
        }
        const result = {
            nodes: Array.from(nodes.values()),
            edges,
            anchors,
        };
        return result;
    }
    /**
     * One anchor per instantiation usage with a known holder scope.
     */
    collectAnchors(usages) {
        const anchors = [];
        for (const [typePath, usageList] of usages) {
            for (const usage of usageList) {
                if (usage.kind !== 'instantiation' || !usage.holderScopeId) {
                    continue;
                }
                const holderScope = this.scopeAnalysis.scopes.get(usage.holderScopeId);
                if (!holderScope) {
                    continue;
                }
                const anchor = {
                    location: usage.location,
                    holderScopeId: usage.holderScopeId,
                    typePath,
                };
                if (usage.constructorText) {
                    anchor.constructorText = usage.constructorText;
                }
                if (holderScope.kind === 'module') {
                    // Plan: module-scope creation is a rooted instance —
                    // legitimate root or developer error; labeled, not policed
                    anchor.rooted = true;
                }
                const variable = this.matchAnchorVariable(usage, typePath, holderScope);
                if (variable) {
                    anchor.variable = variable.name;
                    const [terminatedAt] = variable.reassignments;
                    if (terminatedAt) {
                        anchor.terminatedAt = terminatedAt;
                    }
                }
                anchors.push(anchor);
            }
        }
        return anchors;
    }
    /**
     * Same-line heuristic for the anchor's variable: the variable declared in
     * the holder scope on the same line as the creation, whose typePath (when
     * known) matches the created type.
     */
    matchAnchorVariable(usage, typePath, holderScope) {
        const usageLine = CreationGraphBuilder.lineOf(usage.location);
        if (usageLine === undefined) {
            return undefined;
        }
        for (const variable of this.scopeAnalysis.variables.values()) {
            if (variable.scopeId !== holderScope.scopeId) {
                continue;
            }
            if (CreationGraphBuilder.lineOf(variable.declaration) !== usageLine) {
                continue;
            }
            if (variable.typePath && variable.typePath !== typePath) {
                continue;
            }
            return variable;
        }
        return undefined;
    }
    /**
     * Parse the 1-based line out of a file.ts:Line:Col location string.
     */
    static lineOf(location) {
        const lastColon = location.lastIndexOf(':');
        const prevColon = location.lastIndexOf(':', lastColon - 1);
        if (lastColon < 0 || prevColon < 0) {
            return undefined;
        }
        const line = Number(location.slice(prevColon + 1, lastColon));
        const result = Number.isFinite(line) ? line : undefined;
        return result;
    }
    static nodeOf(scope) {
        const node = {
            scopeId: scope.scopeId,
            name: scope.name,
            kind: scope.kind,
            filePath: scope.filePath,
            location: scope.location,
            starter: false,
        };
        return node;
    }
    /**
     * The name a scope is reachable by: functions/arrows take their scope
     * name; methods take their class (the part before '.') — that is what
     * callers reference. Anonymous holders (file:line labels) and module
     * scopes have no binding name.
     */
    static bindingNameOf(scope) {
        if (scope.kind === 'module') {
            return undefined;
        }
        // Anonymous label is `${filePath}:${line}` — a name can never contain '/'
        if (scope.name.startsWith(`${scope.filePath}:`)) {
            return undefined;
        }
        if (scope.kind === 'method') {
            const dotIndex = scope.name.indexOf('.');
            if (dotIndex < 0) {
                // Method of an anonymous class — no binding name
                return undefined;
            }
            const result = scope.name.slice(0, dotIndex);
            return result;
        }
        return scope.name;
    }
    /**
     * Scope ids referencing `bindingName` inside one file (invocations,
     * pass-as-arg, rebindings — any non-declaration identifier).
     */
    callersOf(filePath, bindingName) {
        const references = this.referencesIn(filePath, bindingName);
        const callers = [];
        for (const location of references) {
            const callerScopeId = this.scopeWalker.findHolderScopeId(location);
            if (callerScopeId) {
                callers.push(callerScopeId);
            }
        }
        return callers;
    }
    /**
     * Callers in OTHER modules, followed through the module graph when the
     * holder's binding is exported (the plan's "if f is exported" branch,
     * including the barrel chase).
     */
    findCrossFileCallers(scope, bindingName) {
        const holderModule = this.moduleGraph.modules.get(scope.filePath);
        if (!holderModule) {
            return [];
        }
        // The exported binding whose LOCAL name is the scope's binding name.
        // Plain exports present under their own name; `export { X as Y }` and
        // `export default X` carry the local name in importAlias.
        const exported = holderModule.exportedBindings.find(binding => !binding.isReExport && (binding.importAlias ?? binding.name) === bindingName);
        if (!exported) {
            return [];
        }
        const callers = [];
        for (const importer of this.moduleGraph.modules.values()) {
            if (importer.filePath === scope.filePath) {
                continue;
            }
            for (const imported of importer.importedBindings) {
                // Re-exports create no local identifier to reference; external
                // packages (node_modules) are never walked
                if (imported.isReExport || imported.external) {
                    continue;
                }
                const localName = this.importReferencesHolder(imported, exported, scope.filePath);
                if (!localName) {
                    continue;
                }
                const importerCallers = this.callersOf(importer.filePath, localName);
                callers.push(...importerCallers);
            }
        }
        return callers;
    }
    /**
     * Modules importing bindings whose ORIGIN is `filePath` — the
     * exports-and-usage bridge for terminal module scopes. Any binding kind
     * counts (named, default, re-export): resolveImportOrigin chases barrels
     * to the declaring module; namespace imports and external packages never
     * resolve, so neither connects. Returned as module-scope scopeIds — a
     * module's scopeId IS its resolved filePath.
     */
    importersOf(filePath) {
        const importers = [];
        for (const importer of this.moduleGraph.modules.values()) {
            if (importer.filePath === filePath) {
                continue;
            }
            const depends = importer.importedBindings.some(imported => {
                const origin = this.resolveImportOrigin(imported);
                const result = origin !== undefined && origin.module.filePath === filePath;
                return result;
            });
            if (depends) {
                importers.push(importer.filePath);
            }
        }
        return importers;
    }
    /**
     * The local identifier an import binding presents for reference search,
     * when the binding resolves to the holder's export — undefined otherwise.
     */
    importReferencesHolder(imported, holderExport, holderFilePath) {
        if (imported.importKind === 'namespace') {
            // Namespace approximation: when the alias's source module exposes
            // the holder's export, any reference to the alias counts
            const exposes = this.namespaceExposes(imported.sourceModule, holderExport.name, holderFilePath);
            const result = exposes ? imported.name : undefined;
            return result;
        }
        const origin = this.resolveImportOrigin(imported);
        if (!origin) {
            return undefined;
        }
        if (origin.module.filePath !== holderFilePath || origin.binding.name !== holderExport.name) {
            return undefined;
        }
        return imported.name;
    }
    /**
     * True when a namespace import's source module exposes `exportedName`
     * whose origin is the holder's module. Expressed as resolving a synthetic
     * named binding, so star barrels and named re-exports are chased by the
     * same machinery as plain imports.
     */
    namespaceExposes(sourceModule, exportedName, holderFilePath) {
        const synthetic = {
            name: exportedName,
            kind: 'unknown',
            sourceModule,
            isReExport: true,
        };
        const origin = this.resolveImportOrigin(synthetic);
        if (!origin) {
            return false;
        }
        const result = origin.module.filePath === holderFilePath && origin.binding.name === exportedName;
        return result;
    }
    /**
     * Chase an import binding to the module that actually declares it,
     * following re-export chains (barrels). Same shape as
     * ModuleGraphBuilder.resolveOrigin, run here over the BUILT graph
     * (sourceModule values are already resolved absolute paths).
     * Cycle-guarded; undefined when the origin is external or the chain loops.
     */
    resolveImportOrigin(binding, visited = new Set()) {
        const sourcePath = path.resolve(binding.sourceModule);
        if (visited.has(sourcePath)) {
            return undefined;
        }
        visited.add(sourcePath);
        const sourceModuleInfo = this.moduleGraph.modules.get(sourcePath);
        if (!sourceModuleInfo) {
            return undefined;
        }
        // The name to look up in the source module's export list
        const lookupKey = binding.importKind === 'default'
            ? 'default'
            : binding.importAlias ?? binding.name;
        for (const exported of sourceModuleInfo.exportedBindings) {
            if (exported.name !== lookupKey) {
                continue;
            }
            if (!exported.isReExport) {
                const result = { module: sourceModuleInfo, binding: exported };
                return result;
            }
            const chased = this.resolveImportOrigin(exported, visited);
            return chased;
        }
        // `export * from './y'` barrels: the name may live behind a star
        for (const exported of sourceModuleInfo.exportedBindings) {
            if (!exported.isReExport || exported.importKind !== 'namespace' || exported.name !== '*') {
                continue;
            }
            const chased = this.resolveImportOrigin({
                name: lookupKey,
                kind: 'unknown',
                sourceModule: exported.sourceModule,
                isReExport: true,
            }, visited);
            if (chased) {
                return chased;
            }
        }
        return undefined;
    }
    /**
     * All references to `name` in a file as location strings. The per-file
     * index is built lazily in ONE pass (every identifier bucketed by text)
     * and cached.
     */
    referencesIn(filePath, name) {
        let byName = this.referencesByFile.get(filePath);
        if (!byName) {
            byName = new Map();
            const sourceFile = this.sourceFiles.get(filePath);
            if (sourceFile) {
                CreationGraphBuilder.collectReferences(sourceFile, byName);
            }
            this.referencesByFile.set(filePath, byName);
        }
        const result = byName.get(name) ?? [];
        return result;
    }
    /**
     * Bucket every identifier reference by name. Declaration and wiring
     * positions are NOT references: import/export specifiers, declaration
     * names, property-access `.name`, and property-assignment keys go into a
     * skip set of NODES — program files can be unbound, so parent-pointer
     * checks are impossible (the scopes walker precedent, Phase 2).
     * ShorthandPropertyAssignment names DO count: `{ foo }` is a genuine
     * reference to foo.
     */
    static collectReferences(sourceFile, byName) {
        const skip = new Set();
        const filePath = path.resolve(sourceFile.fileName);
        const visit = (node) => {
            CreationGraphBuilder.registerSkips(node, skip);
            if (ts.isIdentifier(node) && !skip.has(node)) {
                const list = byName.get(node.text) ?? [];
                if (list.length === 0) {
                    byName.set(node.text, list);
                }
                const { line, character } = sourceFile.getLineAndCharacterOfPosition(node.getStart(sourceFile));
                list.push(`${filePath}:${line + 1}:${character + 1}`);
            }
            ts.forEachChild(node, visit);
        };
        visit(sourceFile);
    }
    /**
     * Register the identifier nodes that must NOT count as references when
     * `node` is a wiring/declaration construct. Runs on the parent before
     * descending, so the skip set is populated before the identifier nodes
     * themselves are visited.
     */
    static registerSkips(node, skip) {
        // import … from './x'
        if (ts.isImportDeclaration(node)) {
            const { importClause } = node;
            if (!importClause) {
                return;
            }
            if (importClause.name) {
                skip.add(importClause.name);
            }
            const { namedBindings } = importClause;
            if (namedBindings && ts.isNamedImports(namedBindings)) {
                for (const element of namedBindings.elements) {
                    if (element.propertyName) {
                        skip.add(element.propertyName);
                    }
                    skip.add(element.name);
                }
            }
            if (namedBindings && ts.isNamespaceImport(namedBindings)) {
                skip.add(namedBindings.name);
            }
            return;
        }
        // import x = require('./y')
        if (ts.isImportEqualsDeclaration(node)) {
            skip.add(node.name);
            return;
        }
        // export { X } [from './y'] / export * as ns from './y' — export wiring
        // alone is not a caller; an importer's usage creates the edge instead
        if (ts.isExportDeclaration(node)) {
            const { exportClause } = node;
            if (exportClause && ts.isNamedExports(exportClause)) {
                for (const element of exportClause.elements) {
                    if (element.propertyName) {
                        skip.add(element.propertyName);
                    }
                    skip.add(element.name);
                }
            }
            if (exportClause && ts.isNamespaceExport(exportClause)) {
                skip.add(exportClause.name);
            }
            return;
        }
        // export default foo — same export-wiring rule
        if (ts.isExportAssignment(node) && ts.isIdentifier(node.expression)) {
            skip.add(node.expression);
            return;
        }
        // obj.name — the `.name` part is property wiring, not a reference
        if (ts.isPropertyAccessExpression(node)) {
            skip.add(node.name);
            return;
        }
        // { name: value } — the key is not a reference. Shorthand `{ name }`
        // IS a reference: ShorthandPropertyAssignment never matches here.
        if (ts.isPropertyAssignment(node) && ts.isIdentifier(node.name)) {
            skip.add(node.name);
            return;
        }
        if (ts.isShorthandPropertyAssignment(node)) {
            return;
        }
        // { x: a } destructuring — `x` is property wiring (`a` is the declared
        // name, skipped by the generic declaration branch below)
        if (ts.isBindingElement(node) && node.propertyName && ts.isIdentifier(node.propertyName)) {
            skip.add(node.propertyName);
        }
        // Declaration names: `function f`, `class C`, `const x`, parameters,
        // methods, enum members… — being declared is not being referenced
        const named = node;
        if ('name' in node && named.name && ts.isIdentifier(named.name)) {
            skip.add(named.name);
        }
    }
}
exports.CreationGraphBuilder = CreationGraphBuilder;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiY3JlYXRpb24tZ3JhcGguanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvY3JlYXRpb24tZ3JhcGgudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFFYiwyQ0FBNkI7QUFDN0IsK0NBQWlDO0FBT2pDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztHQTBCRztBQUNILE1BQWEsb0JBQW9CO0lBU2hDLFlBQ0MsV0FBd0IsRUFDeEIsYUFBNEIsRUFDNUIsV0FBNkIsRUFDN0IsV0FBdUM7UUFQeEMsa0ZBQWtGO1FBQzFFLHFCQUFnQixHQUFHLElBQUksR0FBRyxFQUFpQyxDQUFDO1FBUW5FLElBQUksQ0FBQyxXQUFXLEdBQUcsV0FBVyxDQUFDO1FBQy9CLElBQUksQ0FBQyxhQUFhLEdBQUcsYUFBYSxDQUFDO1FBQ25DLElBQUksQ0FBQyxXQUFXLEdBQUcsV0FBVyxDQUFDO1FBQy9CLElBQUksQ0FBQyxXQUFXLEdBQUcsV0FBVyxDQUFDO0lBQ2hDLENBQUM7SUFFRDs7OztPQUlHO0lBQ0gsS0FBSyxDQUFFLE1BQWdDO1FBQ3RDLE1BQU0sT0FBTyxHQUFHLElBQUksQ0FBQyxjQUFjLENBQUMsTUFBTSxDQUFDLENBQUM7UUFFNUMsTUFBTSxLQUFLLEdBQUcsSUFBSSxHQUFHLEVBQTZCLENBQUM7UUFDbkQsTUFBTSxLQUFLLEdBQXdCLEVBQUUsQ0FBQztRQUN0QyxNQUFNLFNBQVMsR0FBRyxJQUFJLEdBQUcsRUFBVSxDQUFDO1FBQ3BDLGlFQUFpRTtRQUNqRSxNQUFNLE1BQU0sR0FBRyxJQUFJLEdBQUcsRUFBVSxDQUFDO1FBQ2pDLE1BQU0sT0FBTyxHQUFHLElBQUksR0FBRyxFQUFVLENBQUM7UUFDbEMsTUFBTSxJQUFJLEdBQWEsT0FBTyxDQUFDLEdBQUcsQ0FBQyxNQUFNLENBQUMsRUFBRSxDQUFDLE1BQU0sQ0FBQyxhQUFhLENBQUMsQ0FBQztRQUVuRSxN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QXlpQkMiLCJzb3VyY2VzQ29udGVudCI6WyIndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIHBhdGggZnJvbSAncGF0aCc7XG5pbXBvcnQgKiBhcyB0cyBmcm9tICd0eXBlc2NyaXB0JztcbmltcG9ydCB7IExvY2FsU2NvcGVXYWxrZXIgfSBmcm9tICcuL3Njb3Blcyc7XG5pbXBvcnQge1xuXHRDcmVhdGlvbkFuY2hvciwgQ3JlYXRpb25HcmFwaCwgQ3JlYXRpb25HcmFwaEVkZ2UsIENyZWF0aW9uR3JhcGhOb2RlLCBNb2R1bGVCaW5kaW5nLCBNb2R1bGVHcmFwaCwgTW9kdWxlSW5mbyxcblx0U2NvcGVBbmFseXNpcywgU2NvcGVJbmZvLCBTY29wZVZhcmlhYmxlLCBVc2FnZUluZm9cbn0gZnJvbSAnLi90eXBlcyc7XG5cbi8qKlxuICogSW5zaWRlLW91dCBjcmVhdGlvbiB3YWxrZXIgKGluc3RydW1lbnRhdGlvbiB3YWxrZXIgcGxhbiwgUGhhc2UgMykuXG4gKlxuICogU3RhcnRzIGF0IHRoZSBjZXJ0YWluIHBvaW50cyDigJQgaW5zdGFudGlhdGlvbiB1c2FnZXMgY2FycnlpbmcgYVxuICogaG9sZGVyU2NvcGVJZCDigJQgdGhlbiB3YWxrcyBPVVRXQVJEOiB3aG8gaW52b2tlcyBvciByZWZlcmVuY2VzIHRoZSBob2xkZXIsXG4gKiBjcm9zc2luZyBmaWxlcyB0aHJvdWdoIHRoZSBtb2R1bGUgZ3JhcGggKGJhcnJlbHMgY2hhc2VkIHRoZSBzYW1lIHdheVxuICogTW9kdWxlR3JhcGhCdWlsZGVyLnJlc29sdmVPcmlnaW4gZG9lcyksIHVudGlsIG5vIGNhbGxlcnMgcmVtYWluLiBUZXJtaW5hbHNcbiAqIGFyZSB0aGUgc3RhcnRlcnMgKGFwcGxpY2F0aW9uIGVudHJ5IHBvaW50cykuIFRoZSB3YWxrIG5ldmVyIGFzc3VtZXMgYVxuICogbGluZWFyIFRyaWUgKGRlY2lzaW9uIDE6IHN0cmljdENoYWluOmZhbHNlIHBlcm1pdHMgY3ljbGVzL291dC1vZi1vcmRlclxuICogY29uc3RydWN0aW9uKSwgc28gdHJhdmVyc2FsIGlzIGN5Y2xlLWd1YXJkZWQgREZTLCBhbmQgZXZlcnkgYW5jaG9yIHJlY29yZHNcbiAqIHdoaWNoIGNvbnN0cnVjdG9yIGV4cHJlc3Npb24gd2FzIGFjdHVhbGx5IHVzZWQuXG4gKlxuICogRGVsaWJlcmF0ZSBhcHByb3hpbWF0aW9ucyAobm8gZ2V0VHlwZUNoZWNrZXIoKSwgbmFtZS1iYXNlZCBvbmx5KTpcbiAqIC0gTmFtZXNwYWNlIGltcG9ydHMgKGBpbXBvcnQgKiBhcyBuc2ApOiB3aGVuIHRoZSBuYW1lc3BhY2UncyBzb3VyY2UgbW9kdWxlXG4gKiAgIGV4cG9zZXMgdGhlIGhvbGRlcidzIGV4cG9ydCwgQU5ZIHJlZmVyZW5jZSB0byB0aGUgYWxpYXMgY291bnRzIGFzIGFcbiAqICAgY2FsbGVyIHJlZmVyZW5jZS5cbiAqIC0gTWV0aG9kIHNjb3BlcyBiaW5kIHRvIHRoZWlyIENMQVNTIG5hbWUgKGNhbGxlcnMgcmVmZXJlbmNlIHRoZSBjbGFzcyk7XG4gKiAgIGluc3RhbmNlLW1ldGhvZCBjYWxsIHNpdGVzIChgb2JqLm1ldGhvZCgpYCkgYXJlIG5vdCBkaXN0aW5ndWlzaGFibGVcbiAqICAgd2l0aG91dCB0aGUgY2hlY2tlci5cbiAqIC0gQW55IG5vbi1kZWNsYXJhdGlvbiBpZGVudGlmaWVyIGNvdW50cyBhcyBhIHJlZmVyZW5jZSAoaW52b2NhdGlvbnMsXG4gKiAgIHBhc3MtYXMtYXJnLCByZWJpbmRpbmcpOyB0eXBlLXBvc2l0aW9uIHJlZmVyZW5jZXMgYXJlIG5vdCBmaWx0ZXJlZC5cbiAqIC0gTW9kdWxlIHNjb3BlcyBlbmQgdGhlIGludm9jYXRpb24gd2FsaywgYnV0IGEgdGVybWluYWwgbW9kdWxlIHN0aWxsXG4gKiAgIGdhaW5zIGl0cyBJTVBPUlRFUlMgYXMgY2FsbGVyczogZW50cnkgbW9kdWxlcyBoYW5kIGNsYXNzZXMgdG8gdGhlXG4gKiAgIGZyYW1ld29yayBhcyB2YWx1ZXMgKGEgYm9vdHN0cmFwIGNhbGwgcmVjZWl2aW5nIHRoZSByb290IG1vZHVsZSksXG4gKiAgIHdoaWNoIG5vIGNhbGwtd2FsayBjYW4gc2VlIOKAlCB0aGUgaW1wb3J0IHJlbGF0aW9uIGJyaWRnZXMgdGhlbSB0b1xuICogICB0aGUgY2VudGVyLlxuICovXG5leHBvcnQgY2xhc3MgQ3JlYXRpb25HcmFwaEJ1aWxkZXIge1xuXHRwcml2YXRlIG1vZHVsZUdyYXBoOiBNb2R1bGVHcmFwaDtcblx0cHJpdmF0ZSBzY29wZUFuYWx5c2lzOiBTY29wZUFuYWx5c2lzO1xuXHRwcml2YXRlIHNjb3BlV2Fsa2VyOiBMb2NhbFNjb3BlV2Fsa2VyO1xuXHQvKiogS2V5ZWQgYnkgcGF0aC5yZXNvbHZlKHNvdXJjZUZpbGUuZmlsZU5hbWUpLCBtYXRjaGluZyBzY29wZUlkcyAqL1xuXHRwcml2YXRlIHNvdXJjZUZpbGVzOiBNYXA8c3RyaW5nLCB0cy5Tb3VyY2VGaWxlPjtcblx0LyoqIGZpbGVQYXRoIC0+IChpZGVudGlmaWVyIHRleHQgLT4gcmVmZXJlbmNlIGxvY2F0aW9ucyksIGJ1aWx0IGxhemlseSBwZXIgZmlsZSAqL1xuXHRwcml2YXRlIHJlZmVyZW5jZXNCeUZpbGUgPSBuZXcgTWFwPHN0cmluZywgTWFwPHN0cmluZywgc3RyaW5nW10+PigpO1xuXG5cdGNvbnN0cnVjdG9yIChcblx0XHRtb2R1bGVHcmFwaDogTW9kdWxlR3JhcGgsXG5cdFx0c2NvcGVBbmFseXNpczogU2NvcGVBbmFseXNpcyxcblx0XHRzY29wZVdhbGtlcjogTG9jYWxTY29wZVdhbGtlcixcblx0XHRzb3VyY2VGaWxlczogTWFwPHN0cmluZywgdHMuU291cmNlRmlsZT5cblx0KSB7XG5cdFx0dGhpcy5tb2R1bGVHcmFwaCA9IG1vZHVsZUdyYXBoO1xuXHRcdHRoaXMuc2NvcGVBbmFseXNpcyA9IHNjb3BlQW5hbHlzaXM7XG5cdFx0dGhpcy5zY29wZVdhbGtlciA9IHNjb3BlV2Fsa2VyO1xuXHRcdHRoaXMuc291cmNlRmlsZXMgPSBzb3VyY2VGaWxlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBCdWlsZCB0aGUgY3JlYXRpb24gZ3JhcGggZnJvbSB0aGUgYW5hbHl6ZXIncyB1c2FnZXMgKGhvbGRlclNjb3BlSWRcblx0ICogYWxyZWFkeSBhdHRhY2hlZCkuIEFsd2F5cyByZXR1cm5zIGEgZ3JhcGgsIGVtcHR5IGFycmF5cyB3aGVuIG5vdGhpbmdcblx0ICogY3JlYXRlcyBtbmVtb25pY2EgaW5zdGFuY2VzLlxuXHQgKi9cblx0YnVpbGQgKHVzYWdlczogTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+KTogQ3JlYXRpb25HcmFwaCB7XG5cdFx0Y29uc3QgYW5jaG9ycyA9IHRoaXMuY29sbGVjdEFuY2hvcnModXNhZ2VzKTtcblxuXHRcdGNvbnN0IG5vZGVzID0gbmV3IE1hcDxzdHJpbmcsIENyZWF0aW9uR3JhcGhOb2RlPigpO1xuXHRcdGNvbnN0IGVkZ2VzOiBDcmVhdGlvbkdyYXBoRWRnZVtdID0gW107XG5cdFx0Y29uc3Qgc2VlbkVkZ2VzID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0Ly8gc2NvcGVJZHMgd2l0aCBhdCBsZWFzdCBvbmUgY2FsbGVyIOKAlCBldmVyeW9uZSBlbHNlIGlzIGEgc3RhcnRlclxuXHRcdGNvbnN0IGNhbGxlZCA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdGNvbnN0IHZpc2l0ZWQgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHRjb25zdCB3b3JrOiBzdHJpbmdbXSA9IGFuY2hvcnMubWFwKGFuY2hvciA9PiBhbmNob3IuaG9sZGVyU2NvcGVJZCk7XG5cblx0XHRjb25zdCBhZGRFZGdlID0gKGNhbGxlcjogc3RyaW5nLCBjYWxsZWU6IHN0cmluZyk6IHZvaWQgPT4ge1xuXHRcdFx0Y29uc3Qga2V5ID0gYCR7Y2FsbGVyfVxcbiR7Y2FsbGVlfWA7XG5cdFx0XHRpZiAoc2VlbkVkZ2VzLmhhcyhrZXkpKSB7XG5cdFx0XHRcdHJldHVybjtcblx0XHRcdH1cblx0XHRcdHNlZW5FZGdlcy5hZGQoa2V5KTtcblx0XHRcdGVkZ2VzLnB1c2goeyBjYWxsZXIsIGNhbGxlZSB9KTtcblx0XHRcdGNhbGxlZC5hZGQoY2FsbGVlKTtcblx0XHR9O1xuXG5cdFx0d2hpbGUgKHdvcmsubGVuZ3RoID4gMCkge1xuXHRcdFx0Y29uc3Qgc2NvcGVJZCA9IHdvcmsucG9wKCk7XG5cdFx0XHRpZiAoIXNjb3BlSWQgfHwgdmlzaXRlZC5oYXMoc2NvcGVJZCkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHR2aXNpdGVkLmFkZChzY29wZUlkKTtcblx0XHRcdGNvbnN0IHNjb3BlID0gdGhpcy5zY29wZUFuYWx5c2lzLnNjb3Blcy5nZXQoc2NvcGVJZCk7XG5cdFx0XHRpZiAoIXNjb3BlKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0bm9kZXMuc2V0KHNjb3BlSWQsIENyZWF0aW9uR3JhcGhCdWlsZGVyLm5vZGVPZihzY29wZSkpO1xuXG5cdFx0XHRpZiAoc2NvcGUua2luZCA9PT0gJ21vZHVsZScpIHtcblx0XHRcdFx0Ly8gTW9kdWxlIHNjb3BlcyBFTkQgdGhlIGludm9jYXRpb24gd2FsayDigJQgbm9ib2R5IGludm9rZXMgYVxuXHRcdFx0XHQvLyBtb2R1bGUgKGEgbW9kdWxlLXNjb3BlIGNyZWF0aW9uIGlzIGxhYmVsZWQgcm9vdGVkIG9uIHRoZVxuXHRcdFx0XHQvLyBhbmNob3IgaW5zdGVhZCkuIEJ1dCBlbnRyeSBtb2R1bGVzIGhhbmQgdGhlaXIgY2xhc3NlcyB0b1xuXHRcdFx0XHQvLyB0aGUgZnJhbWV3b3JrIGFzIFZBTFVFUyAoYSBib290c3RyYXAgY2FsbCByZWNlaXZpbmcgdGhlXG5cdFx0XHRcdC8vIHJvb3QgbW9kdWxlLCBvciBmcmFtZXdvcmsgbWV0YWRhdGEgbGlzdGluZyBjb250cm9sbGVycyksXG5cdFx0XHRcdC8vIGludmlzaWJsZSB0b1xuXHRcdFx0XHQvLyBjYWxsLXdhbGtpbmcg4oCUIHNvIGEgdGVybWluYWwgbW9kdWxlIHN0aWxsIGdhaW5zIGl0c1xuXHRcdFx0XHQvLyBJTVBPUlRFUlMgYXMgY2FsbGVyczogbWFpbi50cyBpbXBvcnRpbmcgQXBwTW9kdWxlIHlpZWxkc1xuXHRcdFx0XHQvLyB0aGUgbWFpbi50cyDihpIgYXBwLm1vZHVsZSBlZGdlIHRoZSBwdXJlIGNhbGwgZ3JhcGggbWlzc2VzLlxuXHRcdFx0XHRmb3IgKGNvbnN0IGltcG9ydGVyIG9mIHRoaXMuaW1wb3J0ZXJzT2Yoc2NvcGUuZmlsZVBhdGgpKSB7XG5cdFx0XHRcdFx0YWRkRWRnZShpbXBvcnRlciwgc2NvcGVJZCk7XG5cdFx0XHRcdFx0aWYgKCF2aXNpdGVkLmhhcyhpbXBvcnRlcikpIHtcblx0XHRcdFx0XHRcdHdvcmsucHVzaChpbXBvcnRlcik7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXG5cdFx0XHRjb25zdCBiaW5kaW5nTmFtZSA9IENyZWF0aW9uR3JhcGhCdWlsZGVyLmJpbmRpbmdOYW1lT2Yoc2NvcGUpO1xuXHRcdFx0aWYgKCFiaW5kaW5nTmFtZSkge1xuXHRcdFx0XHQvLyBBbm9ueW1vdXMgaG9sZGVyIChmaWxlOmxpbmUgbGFiZWwpOiBuZXZlciByZWZlcmVuY2VkIGJ5IG5hbWVcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cblx0XHRcdC8vIFBsYW4tc2tldGNoIHJlZmluZW1lbnQ6IHNhbWUtZmlsZSByZWZlcmVuY2VzIGFyZSBmb2xsb3dlZCBmb3Jcblx0XHRcdC8vIEVWRVJZIGhvbGRlciwgZXhwb3J0ZWQgb3Igbm90IOKAlCBhbiBleHBvcnRlZCBmdW5jdGlvbiBjYW4gYWxzbyBiZVxuXHRcdFx0Ly8gY2FsbGVkIGZyb20gaXRzIG93biBtb2R1bGUsIGFuZCBib3RoIHBhdGhzIGxlYWQgb3V0d2FyZC5cblx0XHRcdGNvbnN0IHNhbWVGaWxlQ2FsbGVycyA9IHRoaXMuY2FsbGVyc09mKHNjb3BlLmZpbGVQYXRoLCBiaW5kaW5nTmFtZSk7XG5cdFx0XHRjb25zdCBjcm9zc0ZpbGVDYWxsZXJzID0gdGhpcy5maW5kQ3Jvc3NGaWxlQ2FsbGVycyhzY29wZSwgYmluZGluZ05hbWUpO1xuXHRcdFx0Zm9yIChjb25zdCBjYWxsZXIgb2YgWyAuLi5zYW1lRmlsZUNhbGxlcnMsIC4uLmNyb3NzRmlsZUNhbGxlcnMgXSkge1xuXHRcdFx0XHQvLyBEaXJlY3QgcmVjdXJzaW9uIChmIGNhbGxzIGYpIGFkZHMgbm8gb3V0d2FyZCBpbmZvcm1hdGlvblxuXHRcdFx0XHRpZiAoY2FsbGVyID09PSBzY29wZUlkKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0YWRkRWRnZShjYWxsZXIsIHNjb3BlSWQpO1xuXHRcdFx0XHRpZiAoIXZpc2l0ZWQuaGFzKGNhbGxlcikpIHtcblx0XHRcdFx0XHR3b3JrLnB1c2goY2FsbGVyKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdGZvciAoY29uc3Qgbm9kZSBvZiBub2Rlcy52YWx1ZXMoKSkge1xuXHRcdFx0bm9kZS5zdGFydGVyID0gIWNhbGxlZC5oYXMobm9kZS5zY29wZUlkKTtcblx0XHR9XG5cblx0XHRjb25zdCByZXN1bHQ6IENyZWF0aW9uR3JhcGggPSB7XG5cdFx0XHRub2RlcyA6IEFycmF5LmZyb20obm9kZXMudmFsdWVzKCkpLFxuXHRcdFx0ZWRnZXMsXG5cdFx0XHRhbmNob3JzLFxuXHRcdH07XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBPbmUgYW5jaG9yIHBlciBpbnN0YW50aWF0aW9uIHVzYWdlIHdpdGggYSBrbm93biBob2xkZXIgc2NvcGUuXG5cdCAqL1xuXHRwcml2YXRlIGNvbGxlY3RBbmNob3JzICh1c2FnZXM6IE1hcDxzdHJpbmcsIFVzYWdlSW5mb1tdPik6IENyZWF0aW9uQW5jaG9yW10ge1xuXHRcdGNvbnN0IGFuY2hvcnM6IENyZWF0aW9uQW5jaG9yW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IFsgdHlwZVBhdGgsIHVzYWdlTGlzdCBdIG9mIHVzYWdlcykge1xuXHRcdFx0Zm9yIChjb25zdCB1c2FnZSBvZiB1c2FnZUxpc3QpIHtcblx0XHRcdFx0aWYgKHVzYWdlLmtpbmQgIT09ICdpbnN0YW50aWF0aW9uJyB8fCAhdXNhZ2UuaG9sZGVyU2NvcGVJZCkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGhvbGRlclNjb3BlID0gdGhpcy5zY29wZUFuYWx5c2lzLnNjb3Blcy5nZXQodXNhZ2UuaG9sZGVyU2NvcGVJZCk7XG5cdFx0XHRcdGlmICghaG9sZGVyU2NvcGUpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBhbmNob3I6IENyZWF0aW9uQW5jaG9yID0ge1xuXHRcdFx0XHRcdGxvY2F0aW9uICAgICAgOiB1c2FnZS5sb2NhdGlvbixcblx0XHRcdFx0XHRob2xkZXJTY29wZUlkIDogdXNhZ2UuaG9sZGVyU2NvcGVJZCxcblx0XHRcdFx0XHR0eXBlUGF0aCxcblx0XHRcdFx0fTtcblx0XHRcdFx0aWYgKHVzYWdlLmNvbnN0cnVjdG9yVGV4dCkge1xuXHRcdFx0XHRcdGFuY2hvci5jb25zdHJ1Y3RvclRleHQgPSB1c2FnZS5jb25zdHJ1Y3RvclRleHQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGhvbGRlclNjb3BlLmtpbmQgPT09ICdtb2R1bGUnKSB7XG5cdFx0XHRcdFx0Ly8gUGxhbjogbW9kdWxlLXNjb3BlIGNyZWF0aW9uIGlzIGEgcm9vdGVkIGluc3RhbmNlIOKAlFxuXHRcdFx0XHRcdC8vIGxlZ2l0aW1hdGUgcm9vdCBvciBkZXZlbG9wZXIgZXJyb3I7IGxhYmVsZWQsIG5vdCBwb2xpY2VkXG5cdFx0XHRcdFx0YW5jaG9yLnJvb3RlZCA9IHRydWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgdmFyaWFibGUgPSB0aGlzLm1hdGNoQW5jaG9yVmFyaWFibGUodXNhZ2UsIHR5cGVQYXRoLCBob2xkZXJTY29wZSk7XG5cdFx0XHRcdGlmICh2YXJpYWJsZSkge1xuXHRcdFx0XHRcdGFuY2hvci52YXJpYWJsZSA9IHZhcmlhYmxlLm5hbWU7XG5cdFx0XHRcdFx0Y29uc3QgWyB0ZXJtaW5hdGVkQXQgXSA9IHZhcmlhYmxlLnJlYXNzaWdubWVudHM7XG5cdFx0XHRcdFx0aWYgKHRlcm1pbmF0ZWRBdCkge1xuXHRcdFx0XHRcdFx0YW5jaG9yLnRlcm1pbmF0ZWRBdCA9IHRlcm1pbmF0ZWRBdDtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0YW5jaG9ycy5wdXNoKGFuY2hvcik7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiBhbmNob3JzO1xuXHR9XG5cblx0LyoqXG5cdCAqIFNhbWUtbGluZSBoZXVyaXN0aWMgZm9yIHRoZSBhbmNob3IncyB2YXJpYWJsZTogdGhlIHZhcmlhYmxlIGRlY2xhcmVkIGluXG5cdCAqIHRoZSBob2xkZXIgc2NvcGUgb24gdGhlIHNhbWUgbGluZSBhcyB0aGUgY3JlYXRpb24sIHdob3NlIHR5cGVQYXRoICh3aGVuXG5cdCAqIGtub3duKSBtYXRjaGVzIHRoZSBjcmVhdGVkIHR5cGUuXG5cdCAqL1xuXHRwcml2YXRlIG1hdGNoQW5jaG9yVmFyaWFibGUgKFxuXHRcdHVzYWdlOiBVc2FnZUluZm8sXG5cdFx0dHlwZVBhdGg6IHN0cmluZyxcblx0XHRob2xkZXJTY29wZTogU2NvcGVJbmZvXG5cdCk6IFNjb3BlVmFyaWFibGUgfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IHVzYWdlTGluZSA9IENyZWF0aW9uR3JhcGhCdWlsZGVyLmxpbmVPZih1c2FnZS5sb2NhdGlvbik7XG5cdFx0aWYgKHVzYWdlTGluZSA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRmb3IgKGNvbnN0IHZhcmlhYmxlIG9mIHRoaXMuc2NvcGVBbmFseXNpcy52YXJpYWJsZXMudmFsdWVzKCkpIHtcblx0XHRcdGlmICh2YXJpYWJsZS5zY29wZUlkICE9PSBob2xkZXJTY29wZS5zY29wZUlkKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0aWYgKENyZWF0aW9uR3JhcGhCdWlsZGVyLmxpbmVPZih2YXJpYWJsZS5kZWNsYXJhdGlvbikgIT09IHVzYWdlTGluZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGlmICh2YXJpYWJsZS50eXBlUGF0aCAmJiB2YXJpYWJsZS50eXBlUGF0aCAhPT0gdHlwZVBhdGgpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gdmFyaWFibGU7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogUGFyc2UgdGhlIDEtYmFzZWQgbGluZSBvdXQgb2YgYSBmaWxlLnRzOkxpbmU6Q29sIGxvY2F0aW9uIHN0cmluZy5cblx0ICovXG5cdHByaXZhdGUgc3RhdGljIGxpbmVPZiAobG9jYXRpb246IHN0cmluZyk6IG51bWJlciB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgbGFzdENvbG9uID0gbG9jYXRpb24ubGFzdEluZGV4T2YoJzonKTtcblx0XHRjb25zdCBwcmV2Q29sb24gPSBsb2NhdGlvbi5sYXN0SW5kZXhPZignOicsIGxhc3RDb2xvbiAtIDEpO1xuXHRcdGlmIChsYXN0Q29sb24gPCAwIHx8IHByZXZDb2xvbiA8IDApIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXHRcdGNvbnN0IGxpbmUgPSBOdW1iZXIobG9jYXRpb24uc2xpY2UocHJldkNvbG9uICsgMSwgbGFzdENvbG9uKSk7XG5cdFx0Y29uc3QgcmVzdWx0ID0gTnVtYmVyLmlzRmluaXRlKGxpbmUpID8gbGluZSA6IHVuZGVmaW5lZDtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0cHJpdmF0ZSBzdGF0aWMgbm9kZU9mIChzY29wZTogU2NvcGVJbmZvKTogQ3JlYXRpb25HcmFwaE5vZGUge1xuXHRcdGNvbnN0IG5vZGU6IENyZWF0aW9uR3JhcGhOb2RlID0ge1xuXHRcdFx0c2NvcGVJZCAgOiBzY29wZS5zY29wZUlkLFxuXHRcdFx0bmFtZSAgICAgOiBzY29wZS5uYW1lLFxuXHRcdFx0a2luZCAgICAgOiBzY29wZS5raW5kLFxuXHRcdFx0ZmlsZVBhdGggOiBzY29wZS5maWxlUGF0aCxcblx0XHRcdGxvY2F0aW9uIDogc2NvcGUubG9jYXRpb24sXG5cdFx0XHRzdGFydGVyICA6IGZhbHNlLFxuXHRcdH07XG5cdFx0cmV0dXJuIG5vZGU7XG5cdH1cblxuXHQvKipcblx0ICogVGhlIG5hbWUgYSBzY29wZSBpcyByZWFjaGFibGUgYnk6IGZ1bmN0aW9ucy9hcnJvd3MgdGFrZSB0aGVpciBzY29wZVxuXHQgKiBuYW1lOyBtZXRob2RzIHRha2UgdGhlaXIgY2xhc3MgKHRoZSBwYXJ0IGJlZm9yZSAnLicpIOKAlCB0aGF0IGlzIHdoYXRcblx0ICogY2FsbGVycyByZWZlcmVuY2UuIEFub255bW91cyBob2xkZXJzIChmaWxlOmxpbmUgbGFiZWxzKSBhbmQgbW9kdWxlXG5cdCAqIHNjb3BlcyBoYXZlIG5vIGJpbmRpbmcgbmFtZS5cblx0ICovXG5cdHByaXZhdGUgc3RhdGljIGJpbmRpbmdOYW1lT2YgKHNjb3BlOiBTY29wZUluZm8pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRcdGlmIChzY29wZS5raW5kID09PSAnbW9kdWxlJykge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0Ly8gQW5vbnltb3VzIGxhYmVsIGlzIGAke2ZpbGVQYXRofToke2xpbmV9YCDigJQgYSBuYW1lIGNhbiBuZXZlciBjb250YWluICcvJ1xuXHRcdGlmIChzY29wZS5uYW1lLnN0YXJ0c1dpdGgoYCR7c2NvcGUuZmlsZVBhdGh9OmApKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRpZiAoc2NvcGUua2luZCA9PT0gJ21ldGhvZCcpIHtcblx0XHRcdGNvbnN0IGRvdEluZGV4ID0gc2NvcGUubmFtZS5pbmRleE9mKCcuJyk7XG5cdFx0XHRpZiAoZG90SW5kZXggPCAwKSB7XG5cdFx0XHRcdC8vIE1ldGhvZCBvZiBhbiBhbm9ueW1vdXMgY2xhc3Mg4oCUIG5vIGJpbmRpbmcgbmFtZVxuXHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgcmVzdWx0ID0gc2NvcGUubmFtZS5zbGljZSgwLCBkb3RJbmRleCk7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH1cblx0XHRyZXR1cm4gc2NvcGUubmFtZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBTY29wZSBpZHMgcmVmZXJlbmNpbmcgYGJpbmRpbmdOYW1lYCBpbnNpZGUgb25lIGZpbGUgKGludm9jYXRpb25zLFxuXHQgKiBwYXNzLWFzLWFyZywgcmViaW5kaW5ncyDigJQgYW55IG5vbi1kZWNsYXJhdGlvbiBpZGVudGlmaWVyKS5cblx0ICovXG5cdHByaXZhdGUgY2FsbGVyc09mIChmaWxlUGF0aDogc3RyaW5nLCBiaW5kaW5nTmFtZTogc3RyaW5nKTogc3RyaW5nW10ge1xuXHRcdGNvbnN0IHJlZmVyZW5jZXMgPSB0aGlzLnJlZmVyZW5jZXNJbihmaWxlUGF0aCwgYmluZGluZ05hbWUpO1xuXHRcdGNvbnN0IGNhbGxlcnM6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCBsb2NhdGlvbiBvZiByZWZlcmVuY2VzKSB7XG5cdFx0XHRjb25zdCBjYWxsZXJTY29wZUlkID0gdGhpcy5zY29wZVdhbGtlci5maW5kSG9sZGVyU2NvcGVJZChsb2NhdGlvbik7XG5cdFx0XHRpZiAoY2FsbGVyU2NvcGVJZCkge1xuXHRcdFx0XHRjYWxsZXJzLnB1c2goY2FsbGVyU2NvcGVJZCk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiBjYWxsZXJzO1xuXHR9XG5cblx0LyoqXG5cdCAqIENhbGxlcnMgaW4gT1RIRVIgbW9kdWxlcywgZm9sbG93ZWQgdGhyb3VnaCB0aGUgbW9kdWxlIGdyYXBoIHdoZW4gdGhlXG5cdCAqIGhvbGRlcidzIGJpbmRpbmcgaXMgZXhwb3J0ZWQgKHRoZSBwbGFuJ3MgXCJpZiBmIGlzIGV4cG9ydGVkXCIgYnJhbmNoLFxuXHQgKiBpbmNsdWRpbmcgdGhlIGJhcnJlbCBjaGFzZSkuXG5cdCAqL1xuXHRwcml2YXRlIGZpbmRDcm9zc0ZpbGVDYWxsZXJzIChzY29wZTogU2NvcGVJbmZvLCBiaW5kaW5nTmFtZTogc3RyaW5nKTogc3RyaW5nW10ge1xuXHRcdGNvbnN0IGhvbGRlck1vZHVsZSA9IHRoaXMubW9kdWxlR3JhcGgubW9kdWxlcy5nZXQoc2NvcGUuZmlsZVBhdGgpO1xuXHRcdGlmICghaG9sZGVyTW9kdWxlKSB7XG5cdFx0XHRyZXR1cm4gW107XG5cdFx0fVxuXHRcdC8vIFRoZSBleHBvcnRlZCBiaW5kaW5nIHdob3NlIExPQ0FMIG5hbWUgaXMgdGhlIHNjb3BlJ3MgYmluZGluZyBuYW1lLlxuXHRcdC8vIFBsYWluIGV4cG9ydHMgcHJlc2VudCB1bmRlciB0aGVpciBvd24gbmFtZTsgYGV4cG9ydCB7IFggYXMgWSB9YCBhbmRcblx0XHQvLyBgZXhwb3J0IGRlZmF1bHQgWGAgY2FycnkgdGhlIGxvY2FsIG5hbWUgaW4gaW1wb3J0QWxpYXMuXG5cdFx0Y29uc3QgZXhwb3J0ZWQgPSBob2xkZXJNb2R1bGUuZXhwb3J0ZWRCaW5kaW5ncy5maW5kKGJpbmRpbmcgPT5cblx0XHRcdCFiaW5kaW5nLmlzUmVFeHBvcnQgJiYgKGJpbmRpbmcuaW1wb3J0QWxpYXMgPz8gYmluZGluZy5uYW1lKSA9PT0gYmluZGluZ05hbWUpO1xuXHRcdGlmICghZXhwb3J0ZWQpIHtcblx0XHRcdHJldHVybiBbXTtcblx0XHR9XG5cblx0XHRjb25zdCBjYWxsZXJzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgaW1wb3J0ZXIgb2YgdGhpcy5tb2R1bGVHcmFwaC5tb2R1bGVzLnZhbHVlcygpKSB7XG5cdFx0XHRpZiAoaW1wb3J0ZXIuZmlsZVBhdGggPT09IHNjb3BlLmZpbGVQYXRoKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBpbXBvcnRlZCBvZiBpbXBvcnRlci5pbXBvcnRlZEJpbmRpbmdzKSB7XG5cdFx0XHRcdC8vIFJlLWV4cG9ydHMgY3JlYXRlIG5vIGxvY2FsIGlkZW50aWZpZXIgdG8gcmVmZXJlbmNlOyBleHRlcm5hbFxuXHRcdFx0XHQvLyBwYWNrYWdlcyAobm9kZV9tb2R1bGVzKSBhcmUgbmV2ZXIgd2Fsa2VkXG5cdFx0XHRcdGlmIChpbXBvcnRlZC5pc1JlRXhwb3J0IHx8IGltcG9ydGVkLmV4dGVybmFsKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgbG9jYWxOYW1lID0gdGhpcy5pbXBvcnRSZWZlcmVuY2VzSG9sZGVyKGltcG9ydGVkLCBleHBvcnRlZCwgc2NvcGUuZmlsZVBhdGgpO1xuXHRcdFx0XHRpZiAoIWxvY2FsTmFtZSkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGltcG9ydGVyQ2FsbGVycyA9IHRoaXMuY2FsbGVyc09mKGltcG9ydGVyLmZpbGVQYXRoLCBsb2NhbE5hbWUpO1xuXHRcdFx0XHRjYWxsZXJzLnB1c2goLi4uaW1wb3J0ZXJDYWxsZXJzKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0cmV0dXJuIGNhbGxlcnM7XG5cdH1cblxuXHQvKipcblx0ICogTW9kdWxlcyBpbXBvcnRpbmcgYmluZGluZ3Mgd2hvc2UgT1JJR0lOIGlzIGBmaWxlUGF0aGAg4oCUIHRoZVxuXHQgKiBleHBvcnRzLWFuZC11c2FnZSBicmlkZ2UgZm9yIHRlcm1pbmFsIG1vZHVsZSBzY29wZXMuIEFueSBiaW5kaW5nIGtpbmRcblx0ICogY291bnRzIChuYW1lZCwgZGVmYXVsdCwgcmUtZXhwb3J0KTogcmVzb2x2ZUltcG9ydE9yaWdpbiBjaGFzZXMgYmFycmVsc1xuXHQgKiB0byB0aGUgZGVjbGFyaW5nIG1vZHVsZTsgbmFtZXNwYWNlIGltcG9ydHMgYW5kIGV4dGVybmFsIHBhY2thZ2VzIG5ldmVyXG5cdCAqIHJlc29sdmUsIHNvIG5laXRoZXIgY29ubmVjdHMuIFJldHVybmVkIGFzIG1vZHVsZS1zY29wZSBzY29wZUlkcyDigJQgYVxuXHQgKiBtb2R1bGUncyBzY29wZUlkIElTIGl0cyByZXNvbHZlZCBmaWxlUGF0aC5cblx0ICovXG5cdHByaXZhdGUgaW1wb3J0ZXJzT2YgKGZpbGVQYXRoOiBzdHJpbmcpOiBzdHJpbmdbXSB7XG5cdFx0Y29uc3QgaW1wb3J0ZXJzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGZvciAoY29uc3QgaW1wb3J0ZXIgb2YgdGhpcy5tb2R1bGVHcmFwaC5tb2R1bGVzLnZhbHVlcygpKSB7XG5cdFx0XHRpZiAoaW1wb3J0ZXIuZmlsZVBhdGggPT09IGZpbGVQYXRoKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgZGVwZW5kcyA9IGltcG9ydGVyLmltcG9ydGVkQmluZGluZ3Muc29tZShpbXBvcnRlZCA9PiB7XG5cdFx0XHRcdGNvbnN0IG9yaWdpbiA9IHRoaXMucmVzb2x2ZUltcG9ydE9yaWdpbihpbXBvcnRlZCk7XG5cdFx0XHRcdGNvbnN0IHJlc3VsdCA9IG9yaWdpbiAhPT0gdW5kZWZpbmVkICYmIG9yaWdpbi5tb2R1bGUuZmlsZVBhdGggPT09IGZpbGVQYXRoO1xuXHRcdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdFx0fSk7XG5cdFx0XHRpZiAoZGVwZW5kcykge1xuXHRcdFx0XHRpbXBvcnRlcnMucHVzaChpbXBvcnRlci5maWxlUGF0aCk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiBpbXBvcnRlcnM7XG5cdH1cblxuXHQvKipcblx0ICogVGhlIGxvY2FsIGlkZW50aWZpZXIgYW4gaW1wb3J0IGJpbmRpbmcgcHJlc2VudHMgZm9yIHJlZmVyZW5jZSBzZWFyY2gsXG5cdCAqIHdoZW4gdGhlIGJpbmRpbmcgcmVzb2x2ZXMgdG8gdGhlIGhvbGRlcidzIGV4cG9ydCDigJQgdW5kZWZpbmVkIG90aGVyd2lzZS5cblx0ICovXG5cdHByaXZhdGUgaW1wb3J0UmVmZXJlbmNlc0hvbGRlciAoXG5cdFx0aW1wb3J0ZWQ6IE1vZHVsZUJpbmRpbmcsXG5cdFx0aG9sZGVyRXhwb3J0OiBNb2R1bGVCaW5kaW5nLFxuXHRcdGhvbGRlckZpbGVQYXRoOiBzdHJpbmdcblx0KTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0XHRpZiAoaW1wb3J0ZWQuaW1wb3J0S2luZCA9PT0gJ25hbWVzcGFjZScpIHtcblx0XHRcdC8vIE5hbWVzcGFjZSBhcHByb3hpbWF0aW9uOiB3aGVuIHRoZSBhbGlhcydzIHNvdXJjZSBtb2R1bGUgZXhwb3Nlc1xuXHRcdFx0Ly8gdGhlIGhvbGRlcidzIGV4cG9ydCwgYW55IHJlZmVyZW5jZSB0byB0aGUgYWxpYXMgY291bnRzXG5cdFx0XHRjb25zdCBleHBvc2VzID0gdGhpcy5uYW1lc3BhY2VFeHBvc2VzKGltcG9ydGVkLnNvdXJjZU1vZHVsZSwgaG9sZGVyRXhwb3J0Lm5hbWUsIGhvbGRlckZpbGVQYXRoKTtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGV4cG9zZXMgPyBpbXBvcnRlZC5uYW1lIDogdW5kZWZpbmVkO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9XG5cdFx0Y29uc3Qgb3JpZ2luID0gdGhpcy5yZXNvbHZlSW1wb3J0T3JpZ2luKGltcG9ydGVkKTtcblx0XHRpZiAoIW9yaWdpbikge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0aWYgKG9yaWdpbi5tb2R1bGUuZmlsZVBhdGggIT09IGhvbGRlckZpbGVQYXRoIHx8IG9yaWdpbi5iaW5kaW5nLm5hbWUgIT09IGhvbGRlckV4cG9ydC5uYW1lKSB7XG5cdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdH1cblx0XHRyZXR1cm4gaW1wb3J0ZWQubmFtZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBUcnVlIHdoZW4gYSBuYW1lc3BhY2UgaW1wb3J0J3Mgc291cmNlIG1vZHVsZSBleHBvc2VzIGBleHBvcnRlZE5hbWVgXG5cdCAqIHdob3NlIG9yaWdpbiBpcyB0aGUgaG9sZGVyJ3MgbW9kdWxlLiBFeHByZXNzZWQgYXMgcmVzb2x2aW5nIGEgc3ludGhldGljXG5cdCAqIG5hbWVkIGJpbmRpbmcsIHNvIHN0YXIgYmFycmVscyBhbmQgbmFtZWQgcmUtZXhwb3J0cyBhcmUgY2hhc2VkIGJ5IHRoZVxuXHQgKiBzYW1lIG1hY2hpbmVyeSBhcyBwbGFpbiBpbXBvcnRzLlxuXHQgKi9cblx0cHJpdmF0ZSBuYW1lc3BhY2VFeHBvc2VzIChzb3VyY2VNb2R1bGU6IHN0cmluZywgZXhwb3J0ZWROYW1lOiBzdHJpbmcsIGhvbGRlckZpbGVQYXRoOiBzdHJpbmcpOiBib29sZWFuIHtcblx0XHRjb25zdCBzeW50aGV0aWM6IE1vZHVsZUJpbmRpbmcgPSB7XG5cdFx0XHRuYW1lICAgICAgIDogZXhwb3J0ZWROYW1lLFxuXHRcdFx0a2luZCAgICAgICA6ICd1bmtub3duJyxcblx0XHRcdHNvdXJjZU1vZHVsZSxcblx0XHRcdGlzUmVFeHBvcnQgOiB0cnVlLFxuXHRcdH07XG5cdFx0Y29uc3Qgb3JpZ2luID0gdGhpcy5yZXNvbHZlSW1wb3J0T3JpZ2luKHN5bnRoZXRpYyk7XG5cdFx0aWYgKCFvcmlnaW4pIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0Y29uc3QgcmVzdWx0ID0gb3JpZ2luLm1vZHVsZS5maWxlUGF0aCA9PT0gaG9sZGVyRmlsZVBhdGggJiYgb3JpZ2luLmJpbmRpbmcubmFtZSA9PT0gZXhwb3J0ZWROYW1lO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogQ2hhc2UgYW4gaW1wb3J0IGJpbmRpbmcgdG8gdGhlIG1vZHVsZSB0aGF0IGFjdHVhbGx5IGRlY2xhcmVzIGl0LFxuXHQgKiBmb2xsb3dpbmcgcmUtZXhwb3J0IGNoYWlucyAoYmFycmVscykuIFNhbWUgc2hhcGUgYXNcblx0ICogTW9kdWxlR3JhcGhCdWlsZGVyLnJlc29sdmVPcmlnaW4sIHJ1biBoZXJlIG92ZXIgdGhlIEJVSUxUIGdyYXBoXG5cdCAqIChzb3VyY2VNb2R1bGUgdmFsdWVzIGFyZSBhbHJlYWR5IHJlc29sdmVkIGFic29sdXRlIHBhdGhzKS5cblx0ICogQ3ljbGUtZ3VhcmRlZDsgdW5kZWZpbmVkIHdoZW4gdGhlIG9yaWdpbiBpcyBleHRlcm5hbCBvciB0aGUgY2hhaW4gbG9vcHMuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVJbXBvcnRPcmlnaW4gKFxuXHRcdGJpbmRpbmc6IE1vZHVsZUJpbmRpbmcsXG5cdFx0dmlzaXRlZCA9IG5ldyBTZXQ8c3RyaW5nPigpXG5cdCk6IHsgbW9kdWxlOiBNb2R1bGVJbmZvOyBiaW5kaW5nOiBNb2R1bGVCaW5kaW5nIH0gfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IHNvdXJjZVBhdGggPSBwYXRoLnJlc29sdmUoYmluZGluZy5zb3VyY2VNb2R1bGUpO1xuXHRcdGlmICh2aXNpdGVkLmhhcyhzb3VyY2VQYXRoKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0dmlzaXRlZC5hZGQoc291cmNlUGF0aCk7XG5cblx0XHRjb25zdCBzb3VyY2VNb2R1bGVJbmZvID0gdGhpcy5tb2R1bGVHcmFwaC5tb2R1bGVzLmdldChzb3VyY2VQYXRoKTtcblx0XHRpZiAoIXNvdXJjZU1vZHVsZUluZm8pIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gVGhlIG5hbWUgdG8gbG9vayB1cCBpbiB0aGUgc291cmNlIG1vZHVsZSdzIGV4cG9ydCBsaXN0XG5cdFx0Y29uc3QgbG9va3VwS2V5ID0gYmluZGluZy5pbXBvcnRLaW5kID09PSAnZGVmYXVsdCdcblx0XHRcdD8gJ2RlZmF1bHQnXG5cdFx0XHQ6IGJpbmRpbmcuaW1wb3J0QWxpYXMgPz8gYmluZGluZy5uYW1lO1xuXG5cdFx0Zm9yIChjb25zdCBleHBvcnRlZCBvZiBzb3VyY2VNb2R1bGVJbmZvLmV4cG9ydGVkQmluZGluZ3MpIHtcblx0XHRcdGlmIChleHBvcnRlZC5uYW1lICE9PSBsb29rdXBLZXkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRpZiAoIWV4cG9ydGVkLmlzUmVFeHBvcnQpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0ID0geyBtb2R1bGUgOiBzb3VyY2VNb2R1bGVJbmZvLCBiaW5kaW5nIDogZXhwb3J0ZWQgfTtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGNoYXNlZCA9IHRoaXMucmVzb2x2ZUltcG9ydE9yaWdpbihleHBvcnRlZCwgdmlzaXRlZCk7XG5cdFx0XHRyZXR1cm4gY2hhc2VkO1xuXHRcdH1cblxuXHRcdC8vIGBleHBvcnQgKiBmcm9tICcuL3knYCBiYXJyZWxzOiB0aGUgbmFtZSBtYXkgbGl2ZSBiZWhpbmQgYSBzdGFyXG5cdFx0Zm9yIChjb25zdCBleHBvcnRlZCBvZiBzb3VyY2VNb2R1bGVJbmZvLmV4cG9ydGVkQmluZGluZ3MpIHtcblx0XHRcdGlmICghZXhwb3J0ZWQuaXNSZUV4cG9ydCB8fCBleHBvcnRlZC5pbXBvcnRLaW5kICE9PSAnbmFtZXNwYWNlJyB8fCBleHBvcnRlZC5uYW1lICE9PSAnKicpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBjaGFzZWQgPSB0aGlzLnJlc29sdmVJbXBvcnRPcmlnaW4oe1xuXHRcdFx0XHRuYW1lICAgICAgICAgOiBsb29rdXBLZXksXG5cdFx0XHRcdGtpbmQgICAgICAgICA6ICd1bmtub3duJyxcblx0XHRcdFx0c291cmNlTW9kdWxlIDogZXhwb3J0ZWQuc291cmNlTW9kdWxlLFxuXHRcdFx0XHRpc1JlRXhwb3J0ICAgOiB0cnVlLFxuXHRcdFx0fSwgdmlzaXRlZCk7XG5cdFx0XHRpZiAoY2hhc2VkKSB7XG5cdFx0XHRcdHJldHVybiBjaGFzZWQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBBbGwgcmVmZXJlbmNlcyB0byBgbmFtZWAgaW4gYSBmaWxlIGFzIGxvY2F0aW9uIHN0cmluZ3MuIFRoZSBwZXItZmlsZVxuXHQgKiBpbmRleCBpcyBidWlsdCBsYXppbHkgaW4gT05FIHBhc3MgKGV2ZXJ5IGlkZW50aWZpZXIgYnVja2V0ZWQgYnkgdGV4dClcblx0ICogYW5kIGNhY2hlZC5cblx0ICovXG5cdHByaXZhdGUgcmVmZXJlbmNlc0luIChmaWxlUGF0aDogc3RyaW5nLCBuYW1lOiBzdHJpbmcpOiBzdHJpbmdbXSB7XG5cdFx0bGV0IGJ5TmFtZSA9IHRoaXMucmVmZXJlbmNlc0J5RmlsZS5nZXQoZmlsZVBhdGgpO1xuXHRcdGlmICghYnlOYW1lKSB7XG5cdFx0XHRieU5hbWUgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nW10+KCk7XG5cdFx0XHRjb25zdCBzb3VyY2VGaWxlID0gdGhpcy5zb3VyY2VGaWxlcy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0aWYgKHNvdXJjZUZpbGUpIHtcblx0XHRcdFx0Q3JlYXRpb25HcmFwaEJ1aWxkZXIuY29sbGVjdFJlZmVyZW5jZXMoc291cmNlRmlsZSwgYnlOYW1lKTtcblx0XHRcdH1cblx0XHRcdHRoaXMucmVmZXJlbmNlc0J5RmlsZS5zZXQoZmlsZVBhdGgsIGJ5TmFtZSk7XG5cdFx0fVxuXHRcdGNvbnN0IHJlc3VsdCA9IGJ5TmFtZS5nZXQobmFtZSkgPz8gW107XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBCdWNrZXQgZXZlcnkgaWRlbnRpZmllciByZWZlcmVuY2UgYnkgbmFtZS4gRGVjbGFyYXRpb24gYW5kIHdpcmluZ1xuXHQgKiBwb3NpdGlvbnMgYXJlIE5PVCByZWZlcmVuY2VzOiBpbXBvcnQvZXhwb3J0IHNwZWNpZmllcnMsIGRlY2xhcmF0aW9uXG5cdCAqIG5hbWVzLCBwcm9wZXJ0eS1hY2Nlc3MgYC5uYW1lYCwgYW5kIHByb3BlcnR5LWFzc2lnbm1lbnQga2V5cyBnbyBpbnRvIGFcblx0ICogc2tpcCBzZXQgb2YgTk9ERVMg4oCUIHByb2dyYW0gZmlsZXMgY2FuIGJlIHVuYm91bmQsIHNvIHBhcmVudC1wb2ludGVyXG5cdCAqIGNoZWNrcyBhcmUgaW1wb3NzaWJsZSAodGhlIHNjb3BlcyB3YWxrZXIgcHJlY2VkZW50LCBQaGFzZSAyKS5cblx0ICogU2hvcnRoYW5kUHJvcGVydHlBc3NpZ25tZW50IG5hbWVzIERPIGNvdW50OiBgeyBmb28gfWAgaXMgYSBnZW51aW5lXG5cdCAqIHJlZmVyZW5jZSB0byBmb28uXG5cdCAqL1xuXHRwcml2YXRlIHN0YXRpYyBjb2xsZWN0UmVmZXJlbmNlcyAoc291cmNlRmlsZTogdHMuU291cmNlRmlsZSwgYnlOYW1lOiBNYXA8c3RyaW5nLCBzdHJpbmdbXT4pOiB2b2lkIHtcblx0XHRjb25zdCBza2lwID0gbmV3IFNldDx0cy5Ob2RlPigpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5yZXNvbHZlKHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXG5cdFx0Y29uc3QgdmlzaXQgPSAobm9kZTogdHMuTm9kZSk6IHZvaWQgPT4ge1xuXHRcdFx0Q3JlYXRpb25HcmFwaEJ1aWxkZXIucmVnaXN0ZXJTa2lwcyhub2RlLCBza2lwKTtcblx0XHRcdGlmICh0cy5pc0lkZW50aWZpZXIobm9kZSkgJiYgIXNraXAuaGFzKG5vZGUpKSB7XG5cdFx0XHRcdGNvbnN0IGxpc3QgPSBieU5hbWUuZ2V0KG5vZGUudGV4dCkgPz8gW107XG5cdFx0XHRcdGlmIChsaXN0Lmxlbmd0aCA9PT0gMCkge1xuXHRcdFx0XHRcdGJ5TmFtZS5zZXQobm9kZS50ZXh0LCBsaXN0KTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCB7IGxpbmUsIGNoYXJhY3RlciB9ID0gc291cmNlRmlsZS5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpKTtcblx0XHRcdFx0bGlzdC5wdXNoKGAke2ZpbGVQYXRofToke2xpbmUgKyAxfToke2NoYXJhY3RlciArIDF9YCk7XG5cdFx0XHR9XG5cdFx0XHR0cy5mb3JFYWNoQ2hpbGQobm9kZSwgdmlzaXQpO1xuXHRcdH07XG5cdFx0dmlzaXQoc291cmNlRmlsZSk7XG5cdH1cblxuXHQvKipcblx0ICogUmVnaXN0ZXIgdGhlIGlkZW50aWZpZXIgbm9kZXMgdGhhdCBtdXN0IE5PVCBjb3VudCBhcyByZWZlcmVuY2VzIHdoZW5cblx0ICogYG5vZGVgIGlzIGEgd2lyaW5nL2RlY2xhcmF0aW9uIGNvbnN0cnVjdC4gUnVucyBvbiB0aGUgcGFyZW50IGJlZm9yZVxuXHQgKiBkZXNjZW5kaW5nLCBzbyB0aGUgc2tpcCBzZXQgaXMgcG9wdWxhdGVkIGJlZm9yZSB0aGUgaWRlbnRpZmllciBub2Rlc1xuXHQgKiB0aGVtc2VsdmVzIGFyZSB2aXNpdGVkLlxuXHQgKi9cblx0cHJpdmF0ZSBzdGF0aWMgcmVnaXN0ZXJTa2lwcyAobm9kZTogdHMuTm9kZSwgc2tpcDogU2V0PHRzLk5vZGU+KTogdm9pZCB7XG5cdFx0Ly8gaW1wb3J0IOKApiBmcm9tICcuL3gnXG5cdFx0aWYgKHRzLmlzSW1wb3J0RGVjbGFyYXRpb24obm9kZSkpIHtcblx0XHRcdGNvbnN0IHsgaW1wb3J0Q2xhdXNlIH0gPSBub2RlO1xuXHRcdFx0aWYgKCFpbXBvcnRDbGF1c2UpIHtcblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGltcG9ydENsYXVzZS5uYW1lKSB7XG5cdFx0XHRcdHNraXAuYWRkKGltcG9ydENsYXVzZS5uYW1lKTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHsgbmFtZWRCaW5kaW5ncyB9ID0gaW1wb3J0Q2xhdXNlO1xuXHRcdFx0aWYgKG5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lZEltcG9ydHMobmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIG5hbWVkQmluZGluZ3MuZWxlbWVudHMpIHtcblx0XHRcdFx0XHRpZiAoZWxlbWVudC5wcm9wZXJ0eU5hbWUpIHtcblx0XHRcdFx0XHRcdHNraXAuYWRkKGVsZW1lbnQucHJvcGVydHlOYW1lKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0c2tpcC5hZGQoZWxlbWVudC5uYW1lKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdFx0aWYgKG5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lc3BhY2VJbXBvcnQobmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdFx0c2tpcC5hZGQobmFtZWRCaW5kaW5ncy5uYW1lKTtcblx0XHRcdH1cblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Ly8gaW1wb3J0IHggPSByZXF1aXJlKCcuL3knKVxuXHRcdGlmICh0cy5pc0ltcG9ydEVxdWFsc0RlY2xhcmF0aW9uKG5vZGUpKSB7XG5cdFx0XHRza2lwLmFkZChub2RlLm5hbWUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHQvLyBleHBvcnQgeyBYIH0gW2Zyb20gJy4veSddIC8gZXhwb3J0ICogYXMgbnMgZnJvbSAnLi95JyDigJQgZXhwb3J0IHdpcmluZ1xuXHRcdC8vIGFsb25lIGlzIG5vdCBhIGNhbGxlcjsgYW4gaW1wb3J0ZXIncyB1c2FnZSBjcmVhdGVzIHRoZSBlZGdlIGluc3RlYWRcblx0XHRpZiAodHMuaXNFeHBvcnREZWNsYXJhdGlvbihub2RlKSkge1xuXHRcdFx0Y29uc3QgeyBleHBvcnRDbGF1c2UgfSA9IG5vZGU7XG5cdFx0XHRpZiAoZXhwb3J0Q2xhdXNlICYmIHRzLmlzTmFtZWRFeHBvcnRzKGV4cG9ydENsYXVzZSkpIHtcblx0XHRcdFx0Zm9yIChjb25zdCBlbGVtZW50IG9mIGV4cG9ydENsYXVzZS5lbGVtZW50cykge1xuXHRcdFx0XHRcdGlmIChlbGVtZW50LnByb3BlcnR5TmFtZSkge1xuXHRcdFx0XHRcdFx0c2tpcC5hZGQoZWxlbWVudC5wcm9wZXJ0eU5hbWUpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0XHRza2lwLmFkZChlbGVtZW50Lm5hbWUpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRpZiAoZXhwb3J0Q2xhdXNlICYmIHRzLmlzTmFtZXNwYWNlRXhwb3J0KGV4cG9ydENsYXVzZSkpIHtcblx0XHRcdFx0c2tpcC5hZGQoZXhwb3J0Q2xhdXNlLm5hbWUpO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHQvLyBleHBvcnQgZGVmYXVsdCBmb28g4oCUIHNhbWUgZXhwb3J0LXdpcmluZyBydWxlXG5cdFx0aWYgKHRzLmlzRXhwb3J0QXNzaWdubWVudChub2RlKSAmJiB0cy5pc0lkZW50aWZpZXIobm9kZS5leHByZXNzaW9uKSkge1xuXHRcdFx0c2tpcC5hZGQobm9kZS5leHByZXNzaW9uKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Ly8gb2JqLm5hbWUg4oCUIHRoZSBgLm5hbWVgIHBhcnQgaXMgcHJvcGVydHkgd2lyaW5nLCBub3QgYSByZWZlcmVuY2Vcblx0XHRpZiAodHMuaXNQcm9wZXJ0eUFjY2Vzc0V4cHJlc3Npb24obm9kZSkpIHtcblx0XHRcdHNraXAuYWRkKG5vZGUubmFtZSk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdC8vIHsgbmFtZTogdmFsdWUgfSDigJQgdGhlIGtleSBpcyBub3QgYSByZWZlcmVuY2UuIFNob3J0aGFuZCBgeyBuYW1lIH1gXG5cdFx0Ly8gSVMgYSByZWZlcmVuY2U6IFNob3J0aGFuZFByb3BlcnR5QXNzaWdubWVudCBuZXZlciBtYXRjaGVzIGhlcmUuXG5cdFx0aWYgKHRzLmlzUHJvcGVydHlBc3NpZ25tZW50KG5vZGUpICYmIHRzLmlzSWRlbnRpZmllcihub2RlLm5hbWUpKSB7XG5cdFx0XHRza2lwLmFkZChub2RlLm5hbWUpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAodHMuaXNTaG9ydGhhbmRQcm9wZXJ0eUFzc2lnbm1lbnQobm9kZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Ly8geyB4OiBhIH0gZGVzdHJ1Y3R1cmluZyDigJQgYHhgIGlzIHByb3BlcnR5IHdpcmluZyAoYGFgIGlzIHRoZSBkZWNsYXJlZFxuXHRcdC8vIG5hbWUsIHNraXBwZWQgYnkgdGhlIGdlbmVyaWMgZGVjbGFyYXRpb24gYnJhbmNoIGJlbG93KVxuXHRcdGlmICh0cy5pc0JpbmRpbmdFbGVtZW50KG5vZGUpICYmIG5vZGUucHJvcGVydHlOYW1lICYmIHRzLmlzSWRlbnRpZmllcihub2RlLnByb3BlcnR5TmFtZSkpIHtcblx0XHRcdHNraXAuYWRkKG5vZGUucHJvcGVydHlOYW1lKTtcblx0XHR9XG5cdFx0Ly8gRGVjbGFyYXRpb24gbmFtZXM6IGBmdW5jdGlvbiBmYCwgYGNsYXNzIENgLCBgY29uc3QgeGAsIHBhcmFtZXRlcnMsXG5cdFx0Ly8gbWV0aG9kcywgZW51bSBtZW1iZXJz4oCmIOKAlCBiZWluZyBkZWNsYXJlZCBpcyBub3QgYmVpbmcgcmVmZXJlbmNlZFxuXHRcdGNvbnN0IG5hbWVkID0gbm9kZSBhcyB0cy5OYW1lZERlY2xhcmF0aW9uO1xuXHRcdGlmICgnbmFtZScgaW4gbm9kZSAmJiBuYW1lZC5uYW1lICYmIHRzLmlzSWRlbnRpZmllcihuYW1lZC5uYW1lKSkge1xuXHRcdFx0c2tpcC5hZGQobmFtZWQubmFtZSk7XG5cdFx0fVxuXHR9XG59XG4iXX0=