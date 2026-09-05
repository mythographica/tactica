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
exports.ModuleGraphBuilder = void 0;
const module_1 = require("module");
const path = __importStar(require("path"));
const ts = __importStar(require("typescript"));
// Bare builtin names from node:module; both 'path' and 'node:path' accepted
const BUILTIN_MODULES = new Set(module_1.builtinModules);
/**
 * Module-scope walker (instrumentation walker plan, Phase 1).
 *
 * Builds the cross-file module graph: every export/import binding (functions,
 * classes, consts, types — not only mnemonica types), resolved with
 * `ts.resolveModuleName` driven by the program's compilerOptions (tsconfig
 * `paths`, extensionless imports, index files). This is module resolution,
 * NOT the type checker — the no-`getTypeChecker()` precedent stays intact.
 *
 * Usage: addFile() per source file during the definitions pass, then
 * build(definedTypesByFile) once definitions are known.
 */
class ModuleGraphBuilder {
    constructor(program, compilerOptions) {
        this.modules = new Map();
        // filePath -> (local name -> kind) for every named top-level declaration
        this.localDecls = new Map();
        // filePath -> import/export specifier sites, for build()-time resolution
        this.importSites = new Map();
        // `${filePath}\n${specifier}` -> resolution (undefined = failed)
        this.resolutionCache = new Map();
        const options = compilerOptions ?? program?.getCompilerOptions() ?? {};
        this.compilerOptions = options;
    }
    /**
     * Track one source file. Re-adding the same file replaces its record,
     * so a builder may safely be reused across passes.
     */
    addFile(sourceFile) {
        const filePath = path.resolve(sourceFile.fileName);
        const moduleInfo = {
            filePath,
            definedTypes: [],
            exportedBindings: [],
            importedBindings: [],
            dependencies: [],
            unresolvedSpecifiers: [],
            builtinSpecifiers: [],
        };
        const decls = new Map();
        const sites = [];
        this.modules.set(filePath, moduleInfo);
        this.localDecls.set(filePath, decls);
        this.importSites.set(filePath, sites);
        // Pass 1: collect every named top-level declaration, so later
        // `export { X }` statements can be classified regardless of order
        for (const statement of sourceFile.statements) {
            this.collectLocalDecl(statement, decls);
        }
        // Pass 2: process imports, exports, and exported declarations
        for (const statement of sourceFile.statements) {
            this.processStatement(statement, sourceFile, moduleInfo, decls, sites);
        }
        return moduleInfo;
    }
    /**
     * Resolve all specifiers, backfill binding kinds from origin modules,
     * derive dependencies, cross-module mnemonica-type edges, and cycles.
     * `definedTypesByFile` maps absolute file path -> mnemonica type fullPaths
     * defined there (from the analyzer's definitions).
     */
    build(definedTypesByFile) {
        if (definedTypesByFile) {
            for (const [file, types] of definedTypesByFile) {
                const moduleInfo = this.modules.get(path.resolve(file));
                if (moduleInfo) {
                    moduleInfo.definedTypes = types;
                }
            }
        }
        // Resolution pass: rewrite sourceModule to the resolved absolute path
        for (const [filePath, sites] of this.importSites) {
            const moduleInfo = this.modules.get(filePath);
            if (!moduleInfo) {
                continue;
            }
            for (const site of sites) {
                const resolution = this.resolveModule(site.specifier, filePath);
                if (!resolution?.resolvedPath) {
                    if (!moduleInfo.unresolvedSpecifiers.includes(site.specifier)) {
                        moduleInfo.unresolvedSpecifiers.push(site.specifier);
                    }
                    continue;
                }
                const { resolvedPath, isExternal } = resolution;
                for (const binding of site.bindings) {
                    binding.sourceModule = resolvedPath;
                    if (isExternal) {
                        binding.external = true;
                    }
                }
                // Dependencies stay project-internal: external (node_modules)
                // modules are never addFile()'d, so modules.has() gates them out
                if (this.modules.has(resolvedPath) && !moduleInfo.dependencies.includes(resolvedPath)) {
                    moduleInfo.dependencies.push(resolvedPath);
                }
            }
        }
        // Kind backfill + edge collection
        const edges = [];
        for (const [filePath, sites] of this.importSites) {
            const moduleInfo = this.modules.get(filePath);
            if (!moduleInfo) {
                continue;
            }
            for (const site of sites) {
                for (const binding of site.bindings) {
                    const origin = this.resolveOrigin(binding);
                    if (origin && binding.kind === 'unknown') {
                        binding.kind = origin.binding.kind;
                    }
                    if (!origin || origin.module.filePath === filePath) {
                        continue;
                    }
                    const typePath = this.matchDefinedType(origin.module, binding);
                    if (typePath) {
                        edges.push({
                            typePath,
                            definitionModule: origin.module.filePath,
                            usageModule: filePath,
                            usageLocation: site.location,
                        });
                    }
                }
            }
        }
        const cycles = this.detectCycles();
        const graph = {
            modules: this.modules,
            edges,
            cycles,
        };
        return graph;
    }
    /**
     * Resolve a specifier to an absolute file path via ts.resolveModuleName
     * with the program's compilerOptions. Returns undefined on failure.
     */
    resolveModule(specifier, fromFile) {
        const cacheKey = `${fromFile}\n${specifier}`;
        if (this.resolutionCache.has(cacheKey)) {
            const cached = this.resolutionCache.get(cacheKey);
            return cached;
        }
        const result = ts.resolveModuleName(specifier, fromFile, this.compilerOptions, ts.sys);
        const resolution = result.resolvedModule
            ? {
                resolvedPath: path.resolve(result.resolvedModule.resolvedFileName),
                isExternal: result.resolvedModule.isExternalLibraryImport === true,
            }
            : undefined;
        this.resolutionCache.set(cacheKey, resolution);
        return resolution;
    }
    /**
     * True for Node.js builtins in both bare and `node:`-prefixed forms
     * ('path', 'node:path', 'fs/promises', 'node:fs/promises', …).
     */
    static isBuiltinSpecifier(specifier) {
        const bare = specifier.startsWith('node:') ? specifier.slice('node:'.length) : specifier;
        const result = BUILTIN_MODULES.has(bare);
        return result;
    }
    /**
     * Record a builtin import on the module (honesty marker) and skip it
     * entirely: no bindings, no site, no dependency, no edge.
     * Returns true when the specifier was a builtin (caller must return early).
     */
    static skipBuiltin(moduleInfo, specifier) {
        if (!ModuleGraphBuilder.isBuiltinSpecifier(specifier)) {
            return false;
        }
        if (!moduleInfo.builtinSpecifiers.includes(specifier)) {
            moduleInfo.builtinSpecifiers.push(specifier);
        }
        return true;
    }
    /**
     * Chase a binding to the module that actually declares it, following
     * re-export chains (barrels). Cycle-guarded. Returns undefined when the
     * origin is external or the chain loops.
     */
    resolveOrigin(binding, visited = new Set()) {
        const sourcePath = path.resolve(binding.sourceModule);
        if (visited.has(sourcePath)) {
            return undefined;
        }
        visited.add(sourcePath);
        const sourceModuleInfo = this.modules.get(sourcePath);
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
            const chased = this.resolveOrigin(exported, visited);
            return chased;
        }
        // `export * from './y'` barrels: the name may live behind a star
        for (const exported of sourceModuleInfo.exportedBindings) {
            if (!exported.isReExport || exported.importKind !== 'namespace' || exported.name !== '*') {
                continue;
            }
            const chased = this.resolveOrigin({
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
     * Match a binding against a module's defined mnemonica types.
     * Returns the matched fullPath, or undefined when the binding is not a
     * mnemonica type of that module.
     */
    matchDefinedType(moduleInfo, binding) {
        const candidate = binding.importAlias ?? binding.name;
        for (const definedType of moduleInfo.definedTypes) {
            // Custom-collection types are keyed `collectionId::Path`
            const bare = definedType.includes('::')
                ? definedType.slice(definedType.indexOf('::') + 2)
                : definedType;
            if (bare === candidate || bare.startsWith(`${candidate}.`)) {
                return definedType;
            }
        }
        return undefined;
    }
    /**
     * Three-color DFS over project-internal dependencies. Cycles are recorded
     * (mnemonica strictChain:false permits non-linear construction), never
     * treated as errors.
     */
    detectCycles() {
        const cycles = [];
        const seenCycles = new Set();
        // 1 = on the current stack, 2 = fully explored
        const state = new Map();
        const visit = (filePath, stack) => {
            state.set(filePath, 1);
            stack.push(filePath);
            const moduleInfo = this.modules.get(filePath);
            for (const dep of moduleInfo?.dependencies ?? []) {
                if (state.get(dep) === 1) {
                    const cycle = stack.slice(stack.indexOf(dep));
                    const key = ModuleGraphBuilder.cycleKey(cycle);
                    if (!seenCycles.has(key)) {
                        seenCycles.add(key);
                        cycles.push(cycle);
                    }
                    continue;
                }
                if (!state.get(dep)) {
                    visit(dep, stack);
                }
            }
            stack.pop();
            state.set(filePath, 2);
        };
        for (const filePath of this.modules.keys()) {
            if (!state.get(filePath)) {
                visit(filePath, []);
            }
        }
        return cycles;
    }
    /**
     * Rotation-independent cycle key: smallest path first.
     */
    static cycleKey(cycle) {
        let minIndex = 0;
        for (let i = 1; i < cycle.length; i++) {
            if (cycle[i] < cycle[minIndex]) {
                minIndex = i;
            }
        }
        const rotated = cycle.slice(minIndex).concat(cycle.slice(0, minIndex));
        const key = rotated.join('\n');
        return key;
    }
    /**
     * Pass 1: record every named top-level declaration's kind.
     */
    collectLocalDecl(statement, decls) {
        if (ts.isFunctionDeclaration(statement) && statement.name) {
            decls.set(statement.name.text, 'function');
            return;
        }
        if (ts.isClassDeclaration(statement) && statement.name) {
            decls.set(statement.name.text, 'class');
            return;
        }
        if (ts.isInterfaceDeclaration(statement) || ts.isTypeAliasDeclaration(statement)) {
            decls.set(statement.name.text, 'type');
            return;
        }
        if (ts.isEnumDeclaration(statement)) {
            decls.set(statement.name.text, 'type');
            return;
        }
        if (ts.isVariableStatement(statement)) {
            for (const decl of statement.declarationList.declarations) {
                if (ts.isIdentifier(decl.name)) {
                    decls.set(decl.name.text, ModuleGraphBuilder.variableKind(decl));
                }
            }
        }
    }
    /**
     * Classify a variable declaration: arrow/function initializers are
     * 'function' (holder functions the walker follows), class expressions
     * are 'class', everything else is 'const'.
     */
    static variableKind(decl) {
        const { initializer } = decl;
        if (initializer && (ts.isArrowFunction(initializer) || ts.isFunctionExpression(initializer))) {
            return 'function';
        }
        if (initializer && ts.isClassExpression(initializer)) {
            return 'class';
        }
        return 'const';
    }
    /**
     * Pass 2: imports, exports, requires, exported declarations.
     */
    processStatement(statement, sourceFile, moduleInfo, decls, sites) {
        if (ts.isImportDeclaration(statement)) {
            this.processImport(statement, sourceFile, moduleInfo, sites);
            return;
        }
        if (ts.isExportDeclaration(statement)) {
            this.processExportDeclaration(statement, sourceFile, moduleInfo, decls, sites);
            return;
        }
        if (ts.isImportEqualsDeclaration(statement)) {
            this.processImportEquals(statement, sourceFile, moduleInfo, sites);
            return;
        }
        if (ts.isExportAssignment(statement)) {
            this.processExportAssignment(statement, moduleInfo, decls);
            return;
        }
        this.processMaybeExportedDecl(statement, moduleInfo, decls);
        this.processRequireCall(statement, sourceFile, moduleInfo, sites);
    }
    processImport(importDecl, sourceFile, moduleInfo, sites) {
        const { moduleSpecifier } = importDecl;
        if (!ts.isStringLiteral(moduleSpecifier)) {
            return;
        }
        if (ModuleGraphBuilder.skipBuiltin(moduleInfo, moduleSpecifier.text)) {
            return;
        }
        const site = {
            specifier: moduleSpecifier.text,
            location: this.locationOf(moduleSpecifier, sourceFile),
            bindings: [],
        };
        sites.push(site);
        const { importClause } = importDecl;
        if (!importClause) {
            // Side-effect import: dependency only, no bindings
            return;
        }
        // Default import: import Type from './module'
        if (importClause.name) {
            const binding = {
                name: importClause.name.text,
                kind: 'unknown',
                sourceModule: site.specifier,
                importKind: 'default',
                isReExport: false,
            };
            moduleInfo.importedBindings.push(binding);
            site.bindings.push(binding);
        }
        const { namedBindings } = importClause;
        if (namedBindings && ts.isNamedImports(namedBindings)) {
            for (const element of namedBindings.elements) {
                const originalName = element.propertyName?.text;
                const binding = {
                    name: element.name.text,
                    kind: 'unknown',
                    sourceModule: site.specifier,
                    importKind: 'named',
                    isReExport: false,
                };
                if (originalName) {
                    binding.importAlias = originalName;
                }
                moduleInfo.importedBindings.push(binding);
                site.bindings.push(binding);
            }
            return;
        }
        // Namespace import: import * as Types from './module'
        if (namedBindings && ts.isNamespaceImport(namedBindings)) {
            const binding = {
                name: namedBindings.name.text,
                kind: 'unknown',
                sourceModule: site.specifier,
                importKind: 'namespace',
                isReExport: false,
            };
            moduleInfo.importedBindings.push(binding);
            site.bindings.push(binding);
        }
    }
    processExportDeclaration(exportDecl, sourceFile, moduleInfo, decls, sites) {
        const { moduleSpecifier } = exportDecl;
        const { exportClause } = exportDecl;
        // Re-export forms carry a module specifier: `export … from './y'`
        if (moduleSpecifier && ts.isStringLiteral(moduleSpecifier)) {
            if (ModuleGraphBuilder.skipBuiltin(moduleInfo, moduleSpecifier.text)) {
                return;
            }
            const site = {
                specifier: moduleSpecifier.text,
                location: this.locationOf(moduleSpecifier, sourceFile),
                bindings: [],
            };
            sites.push(site);
            if (!exportClause) {
                // `export * from './y'`
                const binding = {
                    name: '*',
                    kind: 'unknown',
                    sourceModule: site.specifier,
                    importKind: 'namespace',
                    isReExport: true,
                };
                moduleInfo.exportedBindings.push(binding);
                moduleInfo.importedBindings.push(binding);
                site.bindings.push(binding);
                return;
            }
            if (ts.isNamespaceExport(exportClause)) {
                // `export * as ns from './y'`
                const binding = {
                    name: exportClause.name.text,
                    kind: 'unknown',
                    sourceModule: site.specifier,
                    importKind: 'namespace',
                    isReExport: true,
                };
                moduleInfo.exportedBindings.push(binding);
                moduleInfo.importedBindings.push(binding);
                site.bindings.push(binding);
                return;
            }
            // `export { X, Y as Z } from './y'`
            for (const element of exportClause.elements) {
                const originalName = element.propertyName?.text;
                const binding = {
                    name: element.name.text,
                    kind: 'unknown',
                    sourceModule: site.specifier,
                    importKind: 'named',
                    isReExport: true,
                };
                if (originalName) {
                    binding.importAlias = originalName;
                }
                moduleInfo.exportedBindings.push(binding);
                moduleInfo.importedBindings.push(binding);
                site.bindings.push(binding);
            }
            return;
        }
        // Plain `export { X, Y as Z }` — local declarations
        if (exportClause && ts.isNamedExports(exportClause)) {
            for (const element of exportClause.elements) {
                const originalName = element.propertyName?.text ?? element.name.text;
                const binding = {
                    name: element.name.text,
                    kind: decls.get(originalName) ?? 'unknown',
                    sourceModule: moduleInfo.filePath,
                    isReExport: false,
                };
                if (element.propertyName) {
                    binding.importAlias = element.propertyName.text;
                }
                moduleInfo.exportedBindings.push(binding);
            }
        }
    }
    /**
     * `import foo = require('./y')`
     */
    processImportEquals(importDecl, sourceFile, moduleInfo, sites) {
        const { moduleReference } = importDecl;
        if (!ts.isExternalModuleReference(moduleReference)) {
            return;
        }
        const { expression } = moduleReference;
        if (!ts.isStringLiteral(expression)) {
            return;
        }
        if (ModuleGraphBuilder.skipBuiltin(moduleInfo, expression.text)) {
            return;
        }
        const binding = {
            name: importDecl.name.text,
            kind: 'unknown',
            sourceModule: expression.text,
            importKind: 'require',
            isReExport: false,
        };
        moduleInfo.importedBindings.push(binding);
        sites.push({
            specifier: expression.text,
            location: this.locationOf(expression, sourceFile),
            bindings: [binding],
        });
    }
    /**
     * `export default <expression>`
     */
    processExportAssignment(statement, moduleInfo, decls) {
        const { expression } = statement;
        const kind = ts.isIdentifier(expression)
            ? decls.get(expression.text) ?? 'unknown'
            : 'unknown';
        const binding = {
            name: 'default',
            kind,
            sourceModule: moduleInfo.filePath,
            importKind: 'default',
            isReExport: false,
        };
        if (ts.isIdentifier(expression)) {
            binding.importAlias = expression.text;
        }
        moduleInfo.exportedBindings.push(binding);
    }
    /**
     * `export function/class/const/interface/type …` declarations.
     */
    processMaybeExportedDecl(statement, moduleInfo, decls) {
        const modifiers = ts.canHaveModifiers(statement) ? ts.getModifiers(statement) : undefined;
        const hasExport = modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword) ?? false;
        const hasDefault = modifiers?.some(m => m.kind === ts.SyntaxKind.DefaultKeyword) ?? false;
        if (!hasExport) {
            return;
        }
        const addExport = (localName, kind) => {
            const binding = {
                name: hasDefault ? 'default' : localName ?? 'default',
                kind,
                sourceModule: moduleInfo.filePath,
                isReExport: false,
            };
            if (hasDefault) {
                binding.importKind = 'default';
                if (localName) {
                    binding.importAlias = localName;
                }
            }
            moduleInfo.exportedBindings.push(binding);
        };
        if (ts.isFunctionDeclaration(statement)) {
            addExport(statement.name?.text, 'function');
            return;
        }
        if (ts.isClassDeclaration(statement)) {
            addExport(statement.name?.text, 'class');
            return;
        }
        if (ts.isInterfaceDeclaration(statement) || ts.isTypeAliasDeclaration(statement)) {
            addExport(statement.name.text, 'type');
            return;
        }
        if (ts.isEnumDeclaration(statement)) {
            addExport(statement.name.text, 'type');
            return;
        }
        if (ts.isVariableStatement(statement)) {
            for (const decl of statement.declarationList.declarations) {
                if (ts.isIdentifier(decl.name)) {
                    addExport(decl.name.text, decls.get(decl.name.text) ?? 'const');
                }
            }
        }
    }
    /**
     * CommonJS `const x = require('./y')` (JS sources with allowJs).
     */
    processRequireCall(statement, sourceFile, moduleInfo, sites) {
        if (!ts.isVariableStatement(statement)) {
            return;
        }
        for (const decl of statement.declarationList.declarations) {
            const { initializer } = decl;
            if (!initializer || !ts.isCallExpression(initializer)) {
                continue;
            }
            if (!ts.isIdentifier(initializer.expression) || initializer.expression.text !== 'require') {
                continue;
            }
            const [firstArg] = initializer.arguments;
            if (!firstArg || !ts.isStringLiteral(firstArg)) {
                continue;
            }
            if (ModuleGraphBuilder.skipBuiltin(moduleInfo, firstArg.text)) {
                continue;
            }
            const localName = ts.isIdentifier(decl.name) ? decl.name.text : decl.name.getText();
            const binding = {
                name: localName,
                kind: 'unknown',
                sourceModule: firstArg.text,
                importKind: 'require',
                isReExport: false,
            };
            moduleInfo.importedBindings.push(binding);
            sites.push({
                specifier: firstArg.text,
                location: this.locationOf(firstArg, sourceFile),
                bindings: [binding],
            });
        }
    }
    /**
     * Format a node's position as file.ts:Line:Col (1-based), matching the
     * location format of the other .tactica outputs.
     */
    locationOf(node, sourceFile) {
        const position = sourceFile.getLineAndCharacterOfPosition(node.getStart(sourceFile));
        const location = `${path.resolve(sourceFile.fileName)}:${position.line + 1}:${position.character + 1}`;
        return location;
    }
}
exports.ModuleGraphBuilder = ModuleGraphBuilder;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoibW9kdWxlLWdyYXBoLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL21vZHVsZS1ncmFwaC50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQSxZQUFZLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQUViLG1DQUF3QztBQUN4QywyQ0FBNkI7QUFDN0IsK0NBQWlDO0FBeUJqQyw0RUFBNEU7QUFDNUUsTUFBTSxlQUFlLEdBQUcsSUFBSSxHQUFHLENBQUMsdUJBQWMsQ0FBQyxDQUFDO0FBRWhEOzs7Ozs7Ozs7OztHQVdHO0FBQ0gsTUFBYSxrQkFBa0I7SUFVOUIsWUFBYSxPQUFvQixFQUFFLGVBQW9DO1FBUi9ELFlBQU8sR0FBRyxJQUFJLEdBQUcsRUFBc0IsQ0FBQztRQUNoRCx5RUFBeUU7UUFDakUsZUFBVSxHQUFHLElBQUksR0FBRyxFQUEwQyxDQUFDO1FBQ3ZFLHlFQUF5RTtRQUNqRSxnQkFBVyxHQUFHLElBQUksR0FBRyxFQUF3QixDQUFDO1FBQ3RELGlFQUFpRTtRQUN6RCxvQkFBZSxHQUFHLElBQUksR0FBRyxFQUF3QyxDQUFDO1FBR3pFLE1BQU0sT0FBTyxHQUFHLGVBQWUsSUFBSSxPQUFPLEVBQUUsa0JBQWtCLEVBQUUsSUFBSSxFQUFFLENBQUM7UUFDdkUsSUFBSSxDQUFDLGVBQWUsR0FBRyxPQUFPLENBQUM7SUFDaEMsQ0FBQztJQUVEOzs7T0FHRztJQUNILE9BQU8sQ0FBRSxVQUF5QjtRQUNqQyxNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxRQUFRLENBQUMsQ0FBQztRQUVuRCxNQUFNLFVBQVUsR0FBZTtZQUM5QixRQUFRO1lBQ1IsWUFBWSxFQUFXLEVBQUU7WUFDekIsZ0JBQWdCLEVBQU8sRUFBRTtZQUN6QixnQkFBZ0IsRUFBTyxFQUFFO1lBQ3pCLFlBQVksRUFBVyxFQUFFO1lBQ3pCLG9CQUFvQixFQUFHLEVBQUU7WUFDekIsaUJBQWlCLEVBQU0sRUFB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QkQsZ0RBdXRCQyIsInNvdXJjZXNDb250ZW50IjpbIid1c2Ugc3RyaWN0JztcblxuaW1wb3J0IHsgYnVpbHRpbk1vZHVsZXMgfSBmcm9tICdtb2R1bGUnO1xuaW1wb3J0ICogYXMgcGF0aCBmcm9tICdwYXRoJztcbmltcG9ydCAqIGFzIHRzIGZyb20gJ3R5cGVzY3JpcHQnO1xuaW1wb3J0IHtcblx0TW9kdWxlQmluZGluZywgTW9kdWxlQmluZGluZ0tpbmQsIE1vZHVsZUdyYXBoLCBNb2R1bGVJbmZvLCBDcm9zc01vZHVsZVVzYWdlXG59IGZyb20gJy4vdHlwZXMnO1xuXG4vKipcbiAqIEludGVybmFsIHJlY29yZCBvZiBvbmUgaW1wb3J0L2V4cG9ydCBzaXRlOiB0aGUgc3BlY2lmaWVyIGFzIHdyaXR0ZW4sIGl0c1xuICogbG9jYXRpb24sIGFuZCB0aGUgYmluZGluZyBvYmplY3RzIGl0IHByb2R1Y2VkIChzaGFyZWQgYnkgcmVmZXJlbmNlIHdpdGhcbiAqIE1vZHVsZUluZm8sIHNvIGJ1aWxkKCktdGltZSByZXNvbHV0aW9uIHJld3JpdGVzIHRoZW0gaW4gcGxhY2UpLlxuICovXG5pbnRlcmZhY2UgSW1wb3J0U2l0ZSB7XG5cdHNwZWNpZmllcjogc3RyaW5nO1xuXHRsb2NhdGlvbjogc3RyaW5nO1xuXHRiaW5kaW5nczogTW9kdWxlQmluZGluZ1tdO1xufVxuXG4vKipcbiAqIFJlc3VsdCBvZiByZXNvbHZpbmcgb25lIHNwZWNpZmllcjogdGhlIGFic29sdXRlIHBhdGggKHVuZGVmaW5lZCB3aGVuXG4gKiB1bnJlc29sdmFibGUpIGFuZCB3aGV0aGVyIGl0IGxhbmRlZCBpbiBub2RlX21vZHVsZXMuXG4gKi9cbmludGVyZmFjZSBNb2R1bGVSZXNvbHV0aW9uIHtcblx0cmVzb2x2ZWRQYXRoPzogc3RyaW5nO1xuXHRpc0V4dGVybmFsOiBib29sZWFuO1xufVxuXG4vLyBCYXJlIGJ1aWx0aW4gbmFtZXMgZnJvbSBub2RlOm1vZHVsZTsgYm90aCAncGF0aCcgYW5kICdub2RlOnBhdGgnIGFjY2VwdGVkXG5jb25zdCBCVUlMVElOX01PRFVMRVMgPSBuZXcgU2V0KGJ1aWx0aW5Nb2R1bGVzKTtcblxuLyoqXG4gKiBNb2R1bGUtc2NvcGUgd2Fsa2VyIChpbnN0cnVtZW50YXRpb24gd2Fsa2VyIHBsYW4sIFBoYXNlIDEpLlxuICpcbiAqIEJ1aWxkcyB0aGUgY3Jvc3MtZmlsZSBtb2R1bGUgZ3JhcGg6IGV2ZXJ5IGV4cG9ydC9pbXBvcnQgYmluZGluZyAoZnVuY3Rpb25zLFxuICogY2xhc3NlcywgY29uc3RzLCB0eXBlcyDigJQgbm90IG9ubHkgbW5lbW9uaWNhIHR5cGVzKSwgcmVzb2x2ZWQgd2l0aFxuICogYHRzLnJlc29sdmVNb2R1bGVOYW1lYCBkcml2ZW4gYnkgdGhlIHByb2dyYW0ncyBjb21waWxlck9wdGlvbnMgKHRzY29uZmlnXG4gKiBgcGF0aHNgLCBleHRlbnNpb25sZXNzIGltcG9ydHMsIGluZGV4IGZpbGVzKS4gVGhpcyBpcyBtb2R1bGUgcmVzb2x1dGlvbixcbiAqIE5PVCB0aGUgdHlwZSBjaGVja2VyIOKAlCB0aGUgbm8tYGdldFR5cGVDaGVja2VyKClgIHByZWNlZGVudCBzdGF5cyBpbnRhY3QuXG4gKlxuICogVXNhZ2U6IGFkZEZpbGUoKSBwZXIgc291cmNlIGZpbGUgZHVyaW5nIHRoZSBkZWZpbml0aW9ucyBwYXNzLCB0aGVuXG4gKiBidWlsZChkZWZpbmVkVHlwZXNCeUZpbGUpIG9uY2UgZGVmaW5pdGlvbnMgYXJlIGtub3duLlxuICovXG5leHBvcnQgY2xhc3MgTW9kdWxlR3JhcGhCdWlsZGVyIHtcblx0cHJpdmF0ZSBjb21waWxlck9wdGlvbnM6IHRzLkNvbXBpbGVyT3B0aW9ucztcblx0cHJpdmF0ZSBtb2R1bGVzID0gbmV3IE1hcDxzdHJpbmcsIE1vZHVsZUluZm8+KCk7XG5cdC8vIGZpbGVQYXRoIC0+IChsb2NhbCBuYW1lIC0+IGtpbmQpIGZvciBldmVyeSBuYW1lZCB0b3AtbGV2ZWwgZGVjbGFyYXRpb25cblx0cHJpdmF0ZSBsb2NhbERlY2xzID0gbmV3IE1hcDxzdHJpbmcsIE1hcDxzdHJpbmcsIE1vZHVsZUJpbmRpbmdLaW5kPj4oKTtcblx0Ly8gZmlsZVBhdGggLT4gaW1wb3J0L2V4cG9ydCBzcGVjaWZpZXIgc2l0ZXMsIGZvciBidWlsZCgpLXRpbWUgcmVzb2x1dGlvblxuXHRwcml2YXRlIGltcG9ydFNpdGVzID0gbmV3IE1hcDxzdHJpbmcsIEltcG9ydFNpdGVbXT4oKTtcblx0Ly8gYCR7ZmlsZVBhdGh9XFxuJHtzcGVjaWZpZXJ9YCAtPiByZXNvbHV0aW9uICh1bmRlZmluZWQgPSBmYWlsZWQpXG5cdHByaXZhdGUgcmVzb2x1dGlvbkNhY2hlID0gbmV3IE1hcDxzdHJpbmcsIE1vZHVsZVJlc29sdXRpb24gfCB1bmRlZmluZWQ+KCk7XG5cblx0Y29uc3RydWN0b3IgKHByb2dyYW0/OiB0cy5Qcm9ncmFtLCBjb21waWxlck9wdGlvbnM/OiB0cy5Db21waWxlck9wdGlvbnMpIHtcblx0XHRjb25zdCBvcHRpb25zID0gY29tcGlsZXJPcHRpb25zID8/IHByb2dyYW0/LmdldENvbXBpbGVyT3B0aW9ucygpID8/IHt9O1xuXHRcdHRoaXMuY29tcGlsZXJPcHRpb25zID0gb3B0aW9ucztcblx0fVxuXG5cdC8qKlxuXHQgKiBUcmFjayBvbmUgc291cmNlIGZpbGUuIFJlLWFkZGluZyB0aGUgc2FtZSBmaWxlIHJlcGxhY2VzIGl0cyByZWNvcmQsXG5cdCAqIHNvIGEgYnVpbGRlciBtYXkgc2FmZWx5IGJlIHJldXNlZCBhY3Jvc3MgcGFzc2VzLlxuXHQgKi9cblx0YWRkRmlsZSAoc291cmNlRmlsZTogdHMuU291cmNlRmlsZSk6IE1vZHVsZUluZm8ge1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5yZXNvbHZlKHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXG5cdFx0Y29uc3QgbW9kdWxlSW5mbzogTW9kdWxlSW5mbyA9IHtcblx0XHRcdGZpbGVQYXRoLFxuXHRcdFx0ZGVmaW5lZFR5cGVzICAgICAgICAgOiBbXSxcblx0XHRcdGV4cG9ydGVkQmluZGluZ3MgICAgIDogW10sXG5cdFx0XHRpbXBvcnRlZEJpbmRpbmdzICAgICA6IFtdLFxuXHRcdFx0ZGVwZW5kZW5jaWVzICAgICAgICAgOiBbXSxcblx0XHRcdHVucmVzb2x2ZWRTcGVjaWZpZXJzIDogW10sXG5cdFx0XHRidWlsdGluU3BlY2lmaWVycyAgICA6IFtdLFxuXHRcdH07XG5cdFx0Y29uc3QgZGVjbHMgPSBuZXcgTWFwPHN0cmluZywgTW9kdWxlQmluZGluZ0tpbmQ+KCk7XG5cdFx0Y29uc3Qgc2l0ZXM6IEltcG9ydFNpdGVbXSA9IFtdO1xuXG5cdFx0dGhpcy5tb2R1bGVzLnNldChmaWxlUGF0aCwgbW9kdWxlSW5mbyk7XG5cdFx0dGhpcy5sb2NhbERlY2xzLnNldChmaWxlUGF0aCwgZGVjbHMpO1xuXHRcdHRoaXMuaW1wb3J0U2l0ZXMuc2V0KGZpbGVQYXRoLCBzaXRlcyk7XG5cblx0XHQvLyBQYXNzIDE6IGNvbGxlY3QgZXZlcnkgbmFtZWQgdG9wLWxldmVsIGRlY2xhcmF0aW9uLCBzbyBsYXRlclxuXHRcdC8vIGBleHBvcnQgeyBYIH1gIHN0YXRlbWVudHMgY2FuIGJlIGNsYXNzaWZpZWQgcmVnYXJkbGVzcyBvZiBvcmRlclxuXHRcdGZvciAoY29uc3Qgc3RhdGVtZW50IG9mIHNvdXJjZUZpbGUuc3RhdGVtZW50cykge1xuXHRcdFx0dGhpcy5jb2xsZWN0TG9jYWxEZWNsKHN0YXRlbWVudCwgZGVjbHMpO1xuXHRcdH1cblxuXHRcdC8vIFBhc3MgMjogcHJvY2VzcyBpbXBvcnRzLCBleHBvcnRzLCBhbmQgZXhwb3J0ZWQgZGVjbGFyYXRpb25zXG5cdFx0Zm9yIChjb25zdCBzdGF0ZW1lbnQgb2Ygc291cmNlRmlsZS5zdGF0ZW1lbnRzKSB7XG5cdFx0XHR0aGlzLnByb2Nlc3NTdGF0ZW1lbnQoc3RhdGVtZW50LCBzb3VyY2VGaWxlLCBtb2R1bGVJbmZvLCBkZWNscywgc2l0ZXMpO1xuXHRcdH1cblxuXHRcdHJldHVybiBtb2R1bGVJbmZvO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJlc29sdmUgYWxsIHNwZWNpZmllcnMsIGJhY2tmaWxsIGJpbmRpbmcga2luZHMgZnJvbSBvcmlnaW4gbW9kdWxlcyxcblx0ICogZGVyaXZlIGRlcGVuZGVuY2llcywgY3Jvc3MtbW9kdWxlIG1uZW1vbmljYS10eXBlIGVkZ2VzLCBhbmQgY3ljbGVzLlxuXHQgKiBgZGVmaW5lZFR5cGVzQnlGaWxlYCBtYXBzIGFic29sdXRlIGZpbGUgcGF0aCAtPiBtbmVtb25pY2EgdHlwZSBmdWxsUGF0aHNcblx0ICogZGVmaW5lZCB0aGVyZSAoZnJvbSB0aGUgYW5hbHl6ZXIncyBkZWZpbml0aW9ucykuXG5cdCAqL1xuXHRidWlsZCAoZGVmaW5lZFR5cGVzQnlGaWxlPzogTWFwPHN0cmluZywgc3RyaW5nW10+KTogTW9kdWxlR3JhcGgge1xuXHRcdGlmIChkZWZpbmVkVHlwZXNCeUZpbGUpIHtcblx0XHRcdGZvciAoY29uc3QgWyBmaWxlLCB0eXBlcyBdIG9mIGRlZmluZWRUeXBlc0J5RmlsZSkge1xuXHRcdFx0XHRjb25zdCBtb2R1bGVJbmZvID0gdGhpcy5tb2R1bGVzLmdldChwYXRoLnJlc29sdmUoZmlsZSkpO1xuXHRcdFx0XHRpZiAobW9kdWxlSW5mbykge1xuXHRcdFx0XHRcdG1vZHVsZUluZm8uZGVmaW5lZFR5cGVzID0gdHlwZXM7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBSZXNvbHV0aW9uIHBhc3M6IHJld3JpdGUgc291cmNlTW9kdWxlIHRvIHRoZSByZXNvbHZlZCBhYnNvbHV0ZSBwYXRoXG5cdFx0Zm9yIChjb25zdCBbIGZpbGVQYXRoLCBzaXRlcyBdIG9mIHRoaXMuaW1wb3J0U2l0ZXMpIHtcblx0XHRcdGNvbnN0IG1vZHVsZUluZm8gPSB0aGlzLm1vZHVsZXMuZ2V0KGZpbGVQYXRoKTtcblx0XHRcdGlmICghbW9kdWxlSW5mbykge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGZvciAoY29uc3Qgc2l0ZSBvZiBzaXRlcykge1xuXHRcdFx0XHRjb25zdCByZXNvbHV0aW9uID0gdGhpcy5yZXNvbHZlTW9kdWxlKHNpdGUuc3BlY2lmaWVyLCBmaWxlUGF0aCk7XG5cdFx0XHRcdGlmICghcmVzb2x1dGlvbj8ucmVzb2x2ZWRQYXRoKSB7XG5cdFx0XHRcdFx0aWYgKCFtb2R1bGVJbmZvLnVucmVzb2x2ZWRTcGVjaWZpZXJzLmluY2x1ZGVzKHNpdGUuc3BlY2lmaWVyKSkge1xuXHRcdFx0XHRcdFx0bW9kdWxlSW5mby51bnJlc29sdmVkU3BlY2lmaWVycy5wdXNoKHNpdGUuc3BlY2lmaWVyKTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgeyByZXNvbHZlZFBhdGgsIGlzRXh0ZXJuYWwgfSA9IHJlc29sdXRpb247XG5cdFx0XHRcdGZvciAoY29uc3QgYmluZGluZyBvZiBzaXRlLmJpbmRpbmdzKSB7XG5cdFx0XHRcdFx0YmluZGluZy5zb3VyY2VNb2R1bGUgPSByZXNvbHZlZFBhdGg7XG5cdFx0XHRcdFx0aWYgKGlzRXh0ZXJuYWwpIHtcblx0XHRcdFx0XHRcdGJpbmRpbmcuZXh0ZXJuYWwgPSB0cnVlO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBEZXBlbmRlbmNpZXMgc3RheSBwcm9qZWN0LWludGVybmFsOiBleHRlcm5hbCAobm9kZV9tb2R1bGVzKVxuXHRcdFx0XHQvLyBtb2R1bGVzIGFyZSBuZXZlciBhZGRGaWxlKCknZCwgc28gbW9kdWxlcy5oYXMoKSBnYXRlcyB0aGVtIG91dFxuXHRcdFx0XHRpZiAodGhpcy5tb2R1bGVzLmhhcyhyZXNvbHZlZFBhdGgpICYmICFtb2R1bGVJbmZvLmRlcGVuZGVuY2llcy5pbmNsdWRlcyhyZXNvbHZlZFBhdGgpKSB7XG5cdFx0XHRcdFx0bW9kdWxlSW5mby5kZXBlbmRlbmNpZXMucHVzaChyZXNvbHZlZFBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gS2luZCBiYWNrZmlsbCArIGVkZ2UgY29sbGVjdGlvblxuXHRcdGNvbnN0IGVkZ2VzOiBDcm9zc01vZHVsZVVzYWdlW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IFsgZmlsZVBhdGgsIHNpdGVzIF0gb2YgdGhpcy5pbXBvcnRTaXRlcykge1xuXHRcdFx0Y29uc3QgbW9kdWxlSW5mbyA9IHRoaXMubW9kdWxlcy5nZXQoZmlsZVBhdGgpO1xuXHRcdFx0aWYgKCFtb2R1bGVJbmZvKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Zm9yIChjb25zdCBzaXRlIG9mIHNpdGVzKSB7XG5cdFx0XHRcdGZvciAoY29uc3QgYmluZGluZyBvZiBzaXRlLmJpbmRpbmdzKSB7XG5cdFx0XHRcdFx0Y29uc3Qgb3JpZ2luID0gdGhpcy5yZXNvbHZlT3JpZ2luKGJpbmRpbmcpO1xuXHRcdFx0XHRcdGlmIChvcmlnaW4gJiYgYmluZGluZy5raW5kID09PSAndW5rbm93bicpIHtcblx0XHRcdFx0XHRcdGJpbmRpbmcua2luZCA9IG9yaWdpbi5iaW5kaW5nLmtpbmQ7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdGlmICghb3JpZ2luIHx8IG9yaWdpbi5tb2R1bGUuZmlsZVBhdGggPT09IGZpbGVQYXRoKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0Y29uc3QgdHlwZVBhdGggPSB0aGlzLm1hdGNoRGVmaW5lZFR5cGUob3JpZ2luLm1vZHVsZSwgYmluZGluZyk7XG5cdFx0XHRcdFx0aWYgKHR5cGVQYXRoKSB7XG5cdFx0XHRcdFx0XHRlZGdlcy5wdXNoKHtcblx0XHRcdFx0XHRcdFx0dHlwZVBhdGgsXG5cdFx0XHRcdFx0XHRcdGRlZmluaXRpb25Nb2R1bGUgOiBvcmlnaW4ubW9kdWxlLmZpbGVQYXRoLFxuXHRcdFx0XHRcdFx0XHR1c2FnZU1vZHVsZSAgICAgIDogZmlsZVBhdGgsXG5cdFx0XHRcdFx0XHRcdHVzYWdlTG9jYXRpb24gICAgOiBzaXRlLmxvY2F0aW9uLFxuXHRcdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QgY3ljbGVzID0gdGhpcy5kZXRlY3RDeWNsZXMoKTtcblxuXHRcdGNvbnN0IGdyYXBoOiBNb2R1bGVHcmFwaCA9IHtcblx0XHRcdG1vZHVsZXMgOiB0aGlzLm1vZHVsZXMsXG5cdFx0XHRlZGdlcyxcblx0XHRcdGN5Y2xlcyxcblx0XHR9O1xuXHRcdHJldHVybiBncmFwaDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgc3BlY2lmaWVyIHRvIGFuIGFic29sdXRlIGZpbGUgcGF0aCB2aWEgdHMucmVzb2x2ZU1vZHVsZU5hbWVcblx0ICogd2l0aCB0aGUgcHJvZ3JhbSdzIGNvbXBpbGVyT3B0aW9ucy4gUmV0dXJucyB1bmRlZmluZWQgb24gZmFpbHVyZS5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZU1vZHVsZSAoc3BlY2lmaWVyOiBzdHJpbmcsIGZyb21GaWxlOiBzdHJpbmcpOiBNb2R1bGVSZXNvbHV0aW9uIHwgdW5kZWZpbmVkIHtcblx0XHRjb25zdCBjYWNoZUtleSA9IGAke2Zyb21GaWxlfVxcbiR7c3BlY2lmaWVyfWA7XG5cdFx0aWYgKHRoaXMucmVzb2x1dGlvbkNhY2hlLmhhcyhjYWNoZUtleSkpIHtcblx0XHRcdGNvbnN0IGNhY2hlZCA9IHRoaXMucmVzb2x1dGlvbkNhY2hlLmdldChjYWNoZUtleSk7XG5cdFx0XHRyZXR1cm4gY2FjaGVkO1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlc3VsdCA9IHRzLnJlc29sdmVNb2R1bGVOYW1lKHNwZWNpZmllciwgZnJvbUZpbGUsIHRoaXMuY29tcGlsZXJPcHRpb25zLCB0cy5zeXMpO1xuXHRcdGNvbnN0IHJlc29sdXRpb246IE1vZHVsZVJlc29sdXRpb24gfCB1bmRlZmluZWQgPSByZXN1bHQucmVzb2x2ZWRNb2R1bGVcblx0XHRcdD8ge1xuXHRcdFx0XHRyZXNvbHZlZFBhdGggOiBwYXRoLnJlc29sdmUocmVzdWx0LnJlc29sdmVkTW9kdWxlLnJlc29sdmVkRmlsZU5hbWUpLFxuXHRcdFx0XHRpc0V4dGVybmFsICAgOiByZXN1bHQucmVzb2x2ZWRNb2R1bGUuaXNFeHRlcm5hbExpYnJhcnlJbXBvcnQgPT09IHRydWUsXG5cdFx0XHR9XG5cdFx0XHQ6IHVuZGVmaW5lZDtcblx0XHR0aGlzLnJlc29sdXRpb25DYWNoZS5zZXQoY2FjaGVLZXksIHJlc29sdXRpb24pO1xuXHRcdHJldHVybiByZXNvbHV0aW9uO1xuXHR9XG5cblx0LyoqXG5cdCAqIFRydWUgZm9yIE5vZGUuanMgYnVpbHRpbnMgaW4gYm90aCBiYXJlIGFuZCBgbm9kZTpgLXByZWZpeGVkIGZvcm1zXG5cdCAqICgncGF0aCcsICdub2RlOnBhdGgnLCAnZnMvcHJvbWlzZXMnLCAnbm9kZTpmcy9wcm9taXNlcycsIOKApikuXG5cdCAqL1xuXHRwcml2YXRlIHN0YXRpYyBpc0J1aWx0aW5TcGVjaWZpZXIgKHNwZWNpZmllcjogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0Y29uc3QgYmFyZSA9IHNwZWNpZmllci5zdGFydHNXaXRoKCdub2RlOicpID8gc3BlY2lmaWVyLnNsaWNlKCdub2RlOicubGVuZ3RoKSA6IHNwZWNpZmllcjtcblx0XHRjb25zdCByZXN1bHQgPSBCVUlMVElOX01PRFVMRVMuaGFzKGJhcmUpO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVjb3JkIGEgYnVpbHRpbiBpbXBvcnQgb24gdGhlIG1vZHVsZSAoaG9uZXN0eSBtYXJrZXIpIGFuZCBza2lwIGl0XG5cdCAqIGVudGlyZWx5OiBubyBiaW5kaW5ncywgbm8gc2l0ZSwgbm8gZGVwZW5kZW5jeSwgbm8gZWRnZS5cblx0ICogUmV0dXJucyB0cnVlIHdoZW4gdGhlIHNwZWNpZmllciB3YXMgYSBidWlsdGluIChjYWxsZXIgbXVzdCByZXR1cm4gZWFybHkpLlxuXHQgKi9cblx0cHJpdmF0ZSBzdGF0aWMgc2tpcEJ1aWx0aW4gKG1vZHVsZUluZm86IE1vZHVsZUluZm8sIHNwZWNpZmllcjogc3RyaW5nKTogYm9vbGVhbiB7XG5cdFx0aWYgKCFNb2R1bGVHcmFwaEJ1aWxkZXIuaXNCdWlsdGluU3BlY2lmaWVyKHNwZWNpZmllcikpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cdFx0aWYgKCFtb2R1bGVJbmZvLmJ1aWx0aW5TcGVjaWZpZXJzLmluY2x1ZGVzKHNwZWNpZmllcikpIHtcblx0XHRcdG1vZHVsZUluZm8uYnVpbHRpblNwZWNpZmllcnMucHVzaChzcGVjaWZpZXIpO1xuXHRcdH1cblx0XHRyZXR1cm4gdHJ1ZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDaGFzZSBhIGJpbmRpbmcgdG8gdGhlIG1vZHVsZSB0aGF0IGFjdHVhbGx5IGRlY2xhcmVzIGl0LCBmb2xsb3dpbmdcblx0ICogcmUtZXhwb3J0IGNoYWlucyAoYmFycmVscykuIEN5Y2xlLWd1YXJkZWQuIFJldHVybnMgdW5kZWZpbmVkIHdoZW4gdGhlXG5cdCAqIG9yaWdpbiBpcyBleHRlcm5hbCBvciB0aGUgY2hhaW4gbG9vcHMuXG5cdCAqL1xuXHRwcml2YXRlIHJlc29sdmVPcmlnaW4gKFxuXHRcdGJpbmRpbmc6IE1vZHVsZUJpbmRpbmcsXG5cdFx0dmlzaXRlZCA9IG5ldyBTZXQ8c3RyaW5nPigpXG5cdCk6IHsgbW9kdWxlOiBNb2R1bGVJbmZvOyBiaW5kaW5nOiBNb2R1bGVCaW5kaW5nIH0gfCB1bmRlZmluZWQge1xuXHRcdGNvbnN0IHNvdXJjZVBhdGggPSBwYXRoLnJlc29sdmUoYmluZGluZy5zb3VyY2VNb2R1bGUpO1xuXHRcdGlmICh2aXNpdGVkLmhhcyhzb3VyY2VQYXRoKSkge1xuXHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHR9XG5cdFx0dmlzaXRlZC5hZGQoc291cmNlUGF0aCk7XG5cblx0XHRjb25zdCBzb3VyY2VNb2R1bGVJbmZvID0gdGhpcy5tb2R1bGVzLmdldChzb3VyY2VQYXRoKTtcblx0XHRpZiAoIXNvdXJjZU1vZHVsZUluZm8pIHtcblx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0fVxuXG5cdFx0Ly8gVGhlIG5hbWUgdG8gbG9vayB1cCBpbiB0aGUgc291cmNlIG1vZHVsZSdzIGV4cG9ydCBsaXN0XG5cdFx0Y29uc3QgbG9va3VwS2V5ID0gYmluZGluZy5pbXBvcnRLaW5kID09PSAnZGVmYXVsdCdcblx0XHRcdD8gJ2RlZmF1bHQnXG5cdFx0XHQ6IGJpbmRpbmcuaW1wb3J0QWxpYXMgPz8gYmluZGluZy5uYW1lO1xuXG5cdFx0Zm9yIChjb25zdCBleHBvcnRlZCBvZiBzb3VyY2VNb2R1bGVJbmZvLmV4cG9ydGVkQmluZGluZ3MpIHtcblx0XHRcdGlmIChleHBvcnRlZC5uYW1lICE9PSBsb29rdXBLZXkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRpZiAoIWV4cG9ydGVkLmlzUmVFeHBvcnQpIHtcblx0XHRcdFx0Y29uc3QgcmVzdWx0ID0geyBtb2R1bGUgOiBzb3VyY2VNb2R1bGVJbmZvLCBiaW5kaW5nIDogZXhwb3J0ZWQgfTtcblx0XHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGNoYXNlZCA9IHRoaXMucmVzb2x2ZU9yaWdpbihleHBvcnRlZCwgdmlzaXRlZCk7XG5cdFx0XHRyZXR1cm4gY2hhc2VkO1xuXHRcdH1cblxuXHRcdC8vIGBleHBvcnQgKiBmcm9tICcuL3knYCBiYXJyZWxzOiB0aGUgbmFtZSBtYXkgbGl2ZSBiZWhpbmQgYSBzdGFyXG5cdFx0Zm9yIChjb25zdCBleHBvcnRlZCBvZiBzb3VyY2VNb2R1bGVJbmZvLmV4cG9ydGVkQmluZGluZ3MpIHtcblx0XHRcdGlmICghZXhwb3J0ZWQuaXNSZUV4cG9ydCB8fCBleHBvcnRlZC5pbXBvcnRLaW5kICE9PSAnbmFtZXNwYWNlJyB8fCBleHBvcnRlZC5uYW1lICE9PSAnKicpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBjaGFzZWQgPSB0aGlzLnJlc29sdmVPcmlnaW4oe1xuXHRcdFx0XHRuYW1lICAgICAgICAgOiBsb29rdXBLZXksXG5cdFx0XHRcdGtpbmQgICAgICAgICA6ICd1bmtub3duJyxcblx0XHRcdFx0c291cmNlTW9kdWxlIDogZXhwb3J0ZWQuc291cmNlTW9kdWxlLFxuXHRcdFx0XHRpc1JlRXhwb3J0ICAgOiB0cnVlLFxuXHRcdFx0fSwgdmlzaXRlZCk7XG5cdFx0XHRpZiAoY2hhc2VkKSB7XG5cdFx0XHRcdHJldHVybiBjaGFzZWQ7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fVxuXG5cdC8qKlxuXHQgKiBNYXRjaCBhIGJpbmRpbmcgYWdhaW5zdCBhIG1vZHVsZSdzIGRlZmluZWQgbW5lbW9uaWNhIHR5cGVzLlxuXHQgKiBSZXR1cm5zIHRoZSBtYXRjaGVkIGZ1bGxQYXRoLCBvciB1bmRlZmluZWQgd2hlbiB0aGUgYmluZGluZyBpcyBub3QgYVxuXHQgKiBtbmVtb25pY2EgdHlwZSBvZiB0aGF0IG1vZHVsZS5cblx0ICovXG5cdHByaXZhdGUgbWF0Y2hEZWZpbmVkVHlwZSAobW9kdWxlSW5mbzogTW9kdWxlSW5mbywgYmluZGluZzogTW9kdWxlQmluZGluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdFx0Y29uc3QgY2FuZGlkYXRlID0gYmluZGluZy5pbXBvcnRBbGlhcyA/PyBiaW5kaW5nLm5hbWU7XG5cdFx0Zm9yIChjb25zdCBkZWZpbmVkVHlwZSBvZiBtb2R1bGVJbmZvLmRlZmluZWRUeXBlcykge1xuXHRcdFx0Ly8gQ3VzdG9tLWNvbGxlY3Rpb24gdHlwZXMgYXJlIGtleWVkIGBjb2xsZWN0aW9uSWQ6OlBhdGhgXG5cdFx0XHRjb25zdCBiYXJlID0gZGVmaW5lZFR5cGUuaW5jbHVkZXMoJzo6Jylcblx0XHRcdFx0PyBkZWZpbmVkVHlwZS5zbGljZShkZWZpbmVkVHlwZS5pbmRleE9mKCc6OicpICsgMilcblx0XHRcdFx0OiBkZWZpbmVkVHlwZTtcblx0XHRcdGlmIChiYXJlID09PSBjYW5kaWRhdGUgfHwgYmFyZS5zdGFydHNXaXRoKGAke2NhbmRpZGF0ZSAgfS5gKSkge1xuXHRcdFx0XHRyZXR1cm4gZGVmaW5lZFR5cGU7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHQvKipcblx0ICogVGhyZWUtY29sb3IgREZTIG92ZXIgcHJvamVjdC1pbnRlcm5hbCBkZXBlbmRlbmNpZXMuIEN5Y2xlcyBhcmUgcmVjb3JkZWRcblx0ICogKG1uZW1vbmljYSBzdHJpY3RDaGFpbjpmYWxzZSBwZXJtaXRzIG5vbi1saW5lYXIgY29uc3RydWN0aW9uKSwgbmV2ZXJcblx0ICogdHJlYXRlZCBhcyBlcnJvcnMuXG5cdCAqL1xuXHRwcml2YXRlIGRldGVjdEN5Y2xlcyAoKTogc3RyaW5nW11bXSB7XG5cdFx0Y29uc3QgY3ljbGVzOiBzdHJpbmdbXVtdID0gW107XG5cdFx0Y29uc3Qgc2VlbkN5Y2xlcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdC8vIDEgPSBvbiB0aGUgY3VycmVudCBzdGFjaywgMiA9IGZ1bGx5IGV4cGxvcmVkXG5cdFx0Y29uc3Qgc3RhdGUgPSBuZXcgTWFwPHN0cmluZywgbnVtYmVyPigpO1xuXG5cdFx0Y29uc3QgdmlzaXQgPSAoZmlsZVBhdGg6IHN0cmluZywgc3RhY2s6IHN0cmluZ1tdKTogdm9pZCA9PiB7XG5cdFx0XHRzdGF0ZS5zZXQoZmlsZVBhdGgsIDEpO1xuXHRcdFx0c3RhY2sucHVzaChmaWxlUGF0aCk7XG5cblx0XHRcdGNvbnN0IG1vZHVsZUluZm8gPSB0aGlzLm1vZHVsZXMuZ2V0KGZpbGVQYXRoKTtcblx0XHRcdGZvciAoY29uc3QgZGVwIG9mIG1vZHVsZUluZm8/LmRlcGVuZGVuY2llcyA/PyBbXSkge1xuXHRcdFx0XHRpZiAoc3RhdGUuZ2V0KGRlcCkgPT09IDEpIHtcblx0XHRcdFx0XHRjb25zdCBjeWNsZSA9IHN0YWNrLnNsaWNlKHN0YWNrLmluZGV4T2YoZGVwKSk7XG5cdFx0XHRcdFx0Y29uc3Qga2V5ID0gTW9kdWxlR3JhcGhCdWlsZGVyLmN5Y2xlS2V5KGN5Y2xlKTtcblx0XHRcdFx0XHRpZiAoIXNlZW5DeWNsZXMuaGFzKGtleSkpIHtcblx0XHRcdFx0XHRcdHNlZW5DeWNsZXMuYWRkKGtleSk7XG5cdFx0XHRcdFx0XHRjeWNsZXMucHVzaChjeWNsZSk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmICghc3RhdGUuZ2V0KGRlcCkpIHtcblx0XHRcdFx0XHR2aXNpdChkZXAsIHN0YWNrKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXG5cdFx0XHRzdGFjay5wb3AoKTtcblx0XHRcdHN0YXRlLnNldChmaWxlUGF0aCwgMik7XG5cdFx0fTtcblxuXHRcdGZvciAoY29uc3QgZmlsZVBhdGggb2YgdGhpcy5tb2R1bGVzLmtleXMoKSkge1xuXHRcdFx0aWYgKCFzdGF0ZS5nZXQoZmlsZVBhdGgpKSB7XG5cdFx0XHRcdHZpc2l0KGZpbGVQYXRoLCBbXSk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0cmV0dXJuIGN5Y2xlcztcblx0fVxuXG5cdC8qKlxuXHQgKiBSb3RhdGlvbi1pbmRlcGVuZGVudCBjeWNsZSBrZXk6IHNtYWxsZXN0IHBhdGggZmlyc3QuXG5cdCAqL1xuXHRwcml2YXRlIHN0YXRpYyBjeWNsZUtleSAoY3ljbGU6IHN0cmluZ1tdKTogc3RyaW5nIHtcblx0XHRsZXQgbWluSW5kZXggPSAwO1xuXHRcdGZvciAobGV0IGkgPSAxOyBpIDwgY3ljbGUubGVuZ3RoOyBpKyspIHtcblx0XHRcdGlmIChjeWNsZVsgaSBdIDwgY3ljbGVbIG1pbkluZGV4IF0pIHtcblx0XHRcdFx0bWluSW5kZXggPSBpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zdCByb3RhdGVkID0gY3ljbGUuc2xpY2UobWluSW5kZXgpLmNvbmNhdChjeWNsZS5zbGljZSgwLCBtaW5JbmRleCkpO1xuXHRcdGNvbnN0IGtleSA9IHJvdGF0ZWQuam9pbignXFxuJyk7XG5cdFx0cmV0dXJuIGtleTtcblx0fVxuXG5cdC8qKlxuXHQgKiBQYXNzIDE6IHJlY29yZCBldmVyeSBuYW1lZCB0b3AtbGV2ZWwgZGVjbGFyYXRpb24ncyBraW5kLlxuXHQgKi9cblx0cHJpdmF0ZSBjb2xsZWN0TG9jYWxEZWNsIChzdGF0ZW1lbnQ6IHRzLlN0YXRlbWVudCwgZGVjbHM6IE1hcDxzdHJpbmcsIE1vZHVsZUJpbmRpbmdLaW5kPik6IHZvaWQge1xuXHRcdGlmICh0cy5pc0Z1bmN0aW9uRGVjbGFyYXRpb24oc3RhdGVtZW50KSAmJiBzdGF0ZW1lbnQubmFtZSkge1xuXHRcdFx0ZGVjbHMuc2V0KHN0YXRlbWVudC5uYW1lLnRleHQsICdmdW5jdGlvbicpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKHN0YXRlbWVudCkgJiYgc3RhdGVtZW50Lm5hbWUpIHtcblx0XHRcdGRlY2xzLnNldChzdGF0ZW1lbnQubmFtZS50ZXh0LCAnY2xhc3MnKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKHRzLmlzSW50ZXJmYWNlRGVjbGFyYXRpb24oc3RhdGVtZW50KSB8fCB0cy5pc1R5cGVBbGlhc0RlY2xhcmF0aW9uKHN0YXRlbWVudCkpIHtcblx0XHRcdGRlY2xzLnNldChzdGF0ZW1lbnQubmFtZS50ZXh0LCAndHlwZScpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAodHMuaXNFbnVtRGVjbGFyYXRpb24oc3RhdGVtZW50KSkge1xuXHRcdFx0ZGVjbHMuc2V0KHN0YXRlbWVudC5uYW1lLnRleHQsICd0eXBlJyk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGlmICh0cy5pc1ZhcmlhYmxlU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdGZvciAoY29uc3QgZGVjbCBvZiBzdGF0ZW1lbnQuZGVjbGFyYXRpb25MaXN0LmRlY2xhcmF0aW9ucykge1xuXHRcdFx0XHRpZiAodHMuaXNJZGVudGlmaWVyKGRlY2wubmFtZSkpIHtcblx0XHRcdFx0XHRkZWNscy5zZXQoZGVjbC5uYW1lLnRleHQsIE1vZHVsZUdyYXBoQnVpbGRlci52YXJpYWJsZUtpbmQoZGVjbCkpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENsYXNzaWZ5IGEgdmFyaWFibGUgZGVjbGFyYXRpb246IGFycm93L2Z1bmN0aW9uIGluaXRpYWxpemVycyBhcmVcblx0ICogJ2Z1bmN0aW9uJyAoaG9sZGVyIGZ1bmN0aW9ucyB0aGUgd2Fsa2VyIGZvbGxvd3MpLCBjbGFzcyBleHByZXNzaW9uc1xuXHQgKiBhcmUgJ2NsYXNzJywgZXZlcnl0aGluZyBlbHNlIGlzICdjb25zdCcuXG5cdCAqL1xuXHRwcml2YXRlIHN0YXRpYyB2YXJpYWJsZUtpbmQgKGRlY2w6IHRzLlZhcmlhYmxlRGVjbGFyYXRpb24pOiBNb2R1bGVCaW5kaW5nS2luZCB7XG5cdFx0Y29uc3QgeyBpbml0aWFsaXplciB9ID0gZGVjbDtcblx0XHRpZiAoaW5pdGlhbGl6ZXIgJiYgKHRzLmlzQXJyb3dGdW5jdGlvbihpbml0aWFsaXplcikgfHwgdHMuaXNGdW5jdGlvbkV4cHJlc3Npb24oaW5pdGlhbGl6ZXIpKSkge1xuXHRcdFx0cmV0dXJuICdmdW5jdGlvbic7XG5cdFx0fVxuXHRcdGlmIChpbml0aWFsaXplciAmJiB0cy5pc0NsYXNzRXhwcmVzc2lvbihpbml0aWFsaXplcikpIHtcblx0XHRcdHJldHVybiAnY2xhc3MnO1xuXHRcdH1cblx0XHRyZXR1cm4gJ2NvbnN0Jztcblx0fVxuXG5cdC8qKlxuXHQgKiBQYXNzIDI6IGltcG9ydHMsIGV4cG9ydHMsIHJlcXVpcmVzLCBleHBvcnRlZCBkZWNsYXJhdGlvbnMuXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NTdGF0ZW1lbnQgKFxuXHRcdHN0YXRlbWVudDogdHMuU3RhdGVtZW50LFxuXHRcdHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUsXG5cdFx0bW9kdWxlSW5mbzogTW9kdWxlSW5mbyxcblx0XHRkZWNsczogTWFwPHN0cmluZywgTW9kdWxlQmluZGluZ0tpbmQ+LFxuXHRcdHNpdGVzOiBJbXBvcnRTaXRlW11cblx0KTogdm9pZCB7XG5cdFx0aWYgKHRzLmlzSW1wb3J0RGVjbGFyYXRpb24oc3RhdGVtZW50KSkge1xuXHRcdFx0dGhpcy5wcm9jZXNzSW1wb3J0KHN0YXRlbWVudCwgc291cmNlRmlsZSwgbW9kdWxlSW5mbywgc2l0ZXMpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAodHMuaXNFeHBvcnREZWNsYXJhdGlvbihzdGF0ZW1lbnQpKSB7XG5cdFx0XHR0aGlzLnByb2Nlc3NFeHBvcnREZWNsYXJhdGlvbihzdGF0ZW1lbnQsIHNvdXJjZUZpbGUsIG1vZHVsZUluZm8sIGRlY2xzLCBzaXRlcyk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGlmICh0cy5pc0ltcG9ydEVxdWFsc0RlY2xhcmF0aW9uKHN0YXRlbWVudCkpIHtcblx0XHRcdHRoaXMucHJvY2Vzc0ltcG9ydEVxdWFscyhzdGF0ZW1lbnQsIHNvdXJjZUZpbGUsIG1vZHVsZUluZm8sIHNpdGVzKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKHRzLmlzRXhwb3J0QXNzaWdubWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHR0aGlzLnByb2Nlc3NFeHBvcnRBc3NpZ25tZW50KHN0YXRlbWVudCwgbW9kdWxlSW5mbywgZGVjbHMpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR0aGlzLnByb2Nlc3NNYXliZUV4cG9ydGVkRGVjbChzdGF0ZW1lbnQsIG1vZHVsZUluZm8sIGRlY2xzKTtcblx0XHR0aGlzLnByb2Nlc3NSZXF1aXJlQ2FsbChzdGF0ZW1lbnQsIHNvdXJjZUZpbGUsIG1vZHVsZUluZm8sIHNpdGVzKTtcblx0fVxuXG5cdHByaXZhdGUgcHJvY2Vzc0ltcG9ydCAoXG5cdFx0aW1wb3J0RGVjbDogdHMuSW1wb3J0RGVjbGFyYXRpb24sXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRtb2R1bGVJbmZvOiBNb2R1bGVJbmZvLFxuXHRcdHNpdGVzOiBJbXBvcnRTaXRlW11cblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgeyBtb2R1bGVTcGVjaWZpZXIgfSA9IGltcG9ydERlY2w7XG5cdFx0aWYgKCF0cy5pc1N0cmluZ0xpdGVyYWwobW9kdWxlU3BlY2lmaWVyKSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAoTW9kdWxlR3JhcGhCdWlsZGVyLnNraXBCdWlsdGluKG1vZHVsZUluZm8sIG1vZHVsZVNwZWNpZmllci50ZXh0KSkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IHNpdGU6IEltcG9ydFNpdGUgPSB7XG5cdFx0XHRzcGVjaWZpZXIgOiBtb2R1bGVTcGVjaWZpZXIudGV4dCxcblx0XHRcdGxvY2F0aW9uICA6IHRoaXMubG9jYXRpb25PZihtb2R1bGVTcGVjaWZpZXIsIHNvdXJjZUZpbGUpLFxuXHRcdFx0YmluZGluZ3MgIDogW10sXG5cdFx0fTtcblx0XHRzaXRlcy5wdXNoKHNpdGUpO1xuXG5cdFx0Y29uc3QgeyBpbXBvcnRDbGF1c2UgfSA9IGltcG9ydERlY2w7XG5cdFx0aWYgKCFpbXBvcnRDbGF1c2UpIHtcblx0XHRcdC8vIFNpZGUtZWZmZWN0IGltcG9ydDogZGVwZW5kZW5jeSBvbmx5LCBubyBiaW5kaW5nc1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIERlZmF1bHQgaW1wb3J0OiBpbXBvcnQgVHlwZSBmcm9tICcuL21vZHVsZSdcblx0XHRpZiAoaW1wb3J0Q2xhdXNlLm5hbWUpIHtcblx0XHRcdGNvbnN0IGJpbmRpbmc6IE1vZHVsZUJpbmRpbmcgPSB7XG5cdFx0XHRcdG5hbWUgICAgICAgICA6IGltcG9ydENsYXVzZS5uYW1lLnRleHQsXG5cdFx0XHRcdGtpbmQgICAgICAgICA6ICd1bmtub3duJyxcblx0XHRcdFx0c291cmNlTW9kdWxlIDogc2l0ZS5zcGVjaWZpZXIsXG5cdFx0XHRcdGltcG9ydEtpbmQgICA6ICdkZWZhdWx0Jyxcblx0XHRcdFx0aXNSZUV4cG9ydCAgIDogZmFsc2UsXG5cdFx0XHR9O1xuXHRcdFx0bW9kdWxlSW5mby5pbXBvcnRlZEJpbmRpbmdzLnB1c2goYmluZGluZyk7XG5cdFx0XHRzaXRlLmJpbmRpbmdzLnB1c2goYmluZGluZyk7XG5cdFx0fVxuXG5cdFx0Y29uc3QgeyBuYW1lZEJpbmRpbmdzIH0gPSBpbXBvcnRDbGF1c2U7XG5cdFx0aWYgKG5hbWVkQmluZGluZ3MgJiYgdHMuaXNOYW1lZEltcG9ydHMobmFtZWRCaW5kaW5ncykpIHtcblx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBuYW1lZEJpbmRpbmdzLmVsZW1lbnRzKSB7XG5cdFx0XHRcdGNvbnN0IG9yaWdpbmFsTmFtZSA9IGVsZW1lbnQucHJvcGVydHlOYW1lPy50ZXh0O1xuXHRcdFx0XHRjb25zdCBiaW5kaW5nOiBNb2R1bGVCaW5kaW5nID0ge1xuXHRcdFx0XHRcdG5hbWUgICAgICAgICA6IGVsZW1lbnQubmFtZS50ZXh0LFxuXHRcdFx0XHRcdGtpbmQgICAgICAgICA6ICd1bmtub3duJyxcblx0XHRcdFx0XHRzb3VyY2VNb2R1bGUgOiBzaXRlLnNwZWNpZmllcixcblx0XHRcdFx0XHRpbXBvcnRLaW5kICAgOiAnbmFtZWQnLFxuXHRcdFx0XHRcdGlzUmVFeHBvcnQgICA6IGZhbHNlLFxuXHRcdFx0XHR9O1xuXHRcdFx0XHRpZiAob3JpZ2luYWxOYW1lKSB7XG5cdFx0XHRcdFx0YmluZGluZy5pbXBvcnRBbGlhcyA9IG9yaWdpbmFsTmFtZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRtb2R1bGVJbmZvLmltcG9ydGVkQmluZGluZ3MucHVzaChiaW5kaW5nKTtcblx0XHRcdFx0c2l0ZS5iaW5kaW5ncy5wdXNoKGJpbmRpbmcpO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdC8vIE5hbWVzcGFjZSBpbXBvcnQ6IGltcG9ydCAqIGFzIFR5cGVzIGZyb20gJy4vbW9kdWxlJ1xuXHRcdGlmIChuYW1lZEJpbmRpbmdzICYmIHRzLmlzTmFtZXNwYWNlSW1wb3J0KG5hbWVkQmluZGluZ3MpKSB7XG5cdFx0XHRjb25zdCBiaW5kaW5nOiBNb2R1bGVCaW5kaW5nID0ge1xuXHRcdFx0XHRuYW1lICAgICAgICAgOiBuYW1lZEJpbmRpbmdzLm5hbWUudGV4dCxcblx0XHRcdFx0a2luZCAgICAgICAgIDogJ3Vua25vd24nLFxuXHRcdFx0XHRzb3VyY2VNb2R1bGUgOiBzaXRlLnNwZWNpZmllcixcblx0XHRcdFx0aW1wb3J0S2luZCAgIDogJ25hbWVzcGFjZScsXG5cdFx0XHRcdGlzUmVFeHBvcnQgICA6IGZhbHNlLFxuXHRcdFx0fTtcblx0XHRcdG1vZHVsZUluZm8uaW1wb3J0ZWRCaW5kaW5ncy5wdXNoKGJpbmRpbmcpO1xuXHRcdFx0c2l0ZS5iaW5kaW5ncy5wdXNoKGJpbmRpbmcpO1xuXHRcdH1cblx0fVxuXG5cdHByaXZhdGUgcHJvY2Vzc0V4cG9ydERlY2xhcmF0aW9uIChcblx0XHRleHBvcnREZWNsOiB0cy5FeHBvcnREZWNsYXJhdGlvbixcblx0XHRzb3VyY2VGaWxlOiB0cy5Tb3VyY2VGaWxlLFxuXHRcdG1vZHVsZUluZm86IE1vZHVsZUluZm8sXG5cdFx0ZGVjbHM6IE1hcDxzdHJpbmcsIE1vZHVsZUJpbmRpbmdLaW5kPixcblx0XHRzaXRlczogSW1wb3J0U2l0ZVtdXG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IHsgbW9kdWxlU3BlY2lmaWVyIH0gPSBleHBvcnREZWNsO1xuXHRcdGNvbnN0IHsgZXhwb3J0Q2xhdXNlIH0gPSBleHBvcnREZWNsO1xuXG5cdFx0Ly8gUmUtZXhwb3J0IGZvcm1zIGNhcnJ5IGEgbW9kdWxlIHNwZWNpZmllcjogYGV4cG9ydCDigKYgZnJvbSAnLi95J2Bcblx0XHRpZiAobW9kdWxlU3BlY2lmaWVyICYmIHRzLmlzU3RyaW5nTGl0ZXJhbChtb2R1bGVTcGVjaWZpZXIpKSB7XG5cdFx0XHRpZiAoTW9kdWxlR3JhcGhCdWlsZGVyLnNraXBCdWlsdGluKG1vZHVsZUluZm8sIG1vZHVsZVNwZWNpZmllci50ZXh0KSkge1xuXHRcdFx0XHRyZXR1cm47XG5cdFx0XHR9XG5cblx0XHRcdGNvbnN0IHNpdGU6IEltcG9ydFNpdGUgPSB7XG5cdFx0XHRcdHNwZWNpZmllciA6IG1vZHVsZVNwZWNpZmllci50ZXh0LFxuXHRcdFx0XHRsb2NhdGlvbiAgOiB0aGlzLmxvY2F0aW9uT2YobW9kdWxlU3BlY2lmaWVyLCBzb3VyY2VGaWxlKSxcblx0XHRcdFx0YmluZGluZ3MgIDogW10sXG5cdFx0XHR9O1xuXHRcdFx0c2l0ZXMucHVzaChzaXRlKTtcblxuXHRcdFx0aWYgKCFleHBvcnRDbGF1c2UpIHtcblx0XHRcdFx0Ly8gYGV4cG9ydCAqIGZyb20gJy4veSdgXG5cdFx0XHRcdGNvbnN0IGJpbmRpbmc6IE1vZHVsZUJpbmRpbmcgPSB7XG5cdFx0XHRcdFx0bmFtZSAgICAgICAgIDogJyonLFxuXHRcdFx0XHRcdGtpbmQgICAgICAgICA6ICd1bmtub3duJyxcblx0XHRcdFx0XHRzb3VyY2VNb2R1bGUgOiBzaXRlLnNwZWNpZmllcixcblx0XHRcdFx0XHRpbXBvcnRLaW5kICAgOiAnbmFtZXNwYWNlJyxcblx0XHRcdFx0XHRpc1JlRXhwb3J0ICAgOiB0cnVlLFxuXHRcdFx0XHR9O1xuXHRcdFx0XHRtb2R1bGVJbmZvLmV4cG9ydGVkQmluZGluZ3MucHVzaChiaW5kaW5nKTtcblx0XHRcdFx0bW9kdWxlSW5mby5pbXBvcnRlZEJpbmRpbmdzLnB1c2goYmluZGluZyk7XG5cdFx0XHRcdHNpdGUuYmluZGluZ3MucHVzaChiaW5kaW5nKTtcblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXG5cdFx0XHRpZiAodHMuaXNOYW1lc3BhY2VFeHBvcnQoZXhwb3J0Q2xhdXNlKSkge1xuXHRcdFx0XHQvLyBgZXhwb3J0ICogYXMgbnMgZnJvbSAnLi95J2Bcblx0XHRcdFx0Y29uc3QgYmluZGluZzogTW9kdWxlQmluZGluZyA9IHtcblx0XHRcdFx0XHRuYW1lICAgICAgICAgOiBleHBvcnRDbGF1c2UubmFtZS50ZXh0LFxuXHRcdFx0XHRcdGtpbmQgICAgICAgICA6ICd1bmtub3duJyxcblx0XHRcdFx0XHRzb3VyY2VNb2R1bGUgOiBzaXRlLnNwZWNpZmllcixcblx0XHRcdFx0XHRpbXBvcnRLaW5kICAgOiAnbmFtZXNwYWNlJyxcblx0XHRcdFx0XHRpc1JlRXhwb3J0ICAgOiB0cnVlLFxuXHRcdFx0XHR9O1xuXHRcdFx0XHRtb2R1bGVJbmZvLmV4cG9ydGVkQmluZGluZ3MucHVzaChiaW5kaW5nKTtcblx0XHRcdFx0bW9kdWxlSW5mby5pbXBvcnRlZEJpbmRpbmdzLnB1c2goYmluZGluZyk7XG5cdFx0XHRcdHNpdGUuYmluZGluZ3MucHVzaChiaW5kaW5nKTtcblx0XHRcdFx0cmV0dXJuO1xuXHRcdFx0fVxuXG5cdFx0XHQvLyBgZXhwb3J0IHsgWCwgWSBhcyBaIH0gZnJvbSAnLi95J2Bcblx0XHRcdGZvciAoY29uc3QgZWxlbWVudCBvZiBleHBvcnRDbGF1c2UuZWxlbWVudHMpIHtcblx0XHRcdFx0Y29uc3Qgb3JpZ2luYWxOYW1lID0gZWxlbWVudC5wcm9wZXJ0eU5hbWU/LnRleHQ7XG5cdFx0XHRcdGNvbnN0IGJpbmRpbmc6IE1vZHVsZUJpbmRpbmcgPSB7XG5cdFx0XHRcdFx0bmFtZSAgICAgICAgIDogZWxlbWVudC5uYW1lLnRleHQsXG5cdFx0XHRcdFx0a2luZCAgICAgICAgIDogJ3Vua25vd24nLFxuXHRcdFx0XHRcdHNvdXJjZU1vZHVsZSA6IHNpdGUuc3BlY2lmaWVyLFxuXHRcdFx0XHRcdGltcG9ydEtpbmQgICA6ICduYW1lZCcsXG5cdFx0XHRcdFx0aXNSZUV4cG9ydCAgIDogdHJ1ZSxcblx0XHRcdFx0fTtcblx0XHRcdFx0aWYgKG9yaWdpbmFsTmFtZSkge1xuXHRcdFx0XHRcdGJpbmRpbmcuaW1wb3J0QWxpYXMgPSBvcmlnaW5hbE5hbWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0bW9kdWxlSW5mby5leHBvcnRlZEJpbmRpbmdzLnB1c2goYmluZGluZyk7XG5cdFx0XHRcdG1vZHVsZUluZm8uaW1wb3J0ZWRCaW5kaW5ncy5wdXNoKGJpbmRpbmcpO1xuXHRcdFx0XHRzaXRlLmJpbmRpbmdzLnB1c2goYmluZGluZyk7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Ly8gUGxhaW4gYGV4cG9ydCB7IFgsIFkgYXMgWiB9YCDigJQgbG9jYWwgZGVjbGFyYXRpb25zXG5cdFx0aWYgKGV4cG9ydENsYXVzZSAmJiB0cy5pc05hbWVkRXhwb3J0cyhleHBvcnRDbGF1c2UpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGVsZW1lbnQgb2YgZXhwb3J0Q2xhdXNlLmVsZW1lbnRzKSB7XG5cdFx0XHRcdGNvbnN0IG9yaWdpbmFsTmFtZSA9IGVsZW1lbnQucHJvcGVydHlOYW1lPy50ZXh0ID8/IGVsZW1lbnQubmFtZS50ZXh0O1xuXHRcdFx0XHRjb25zdCBiaW5kaW5nOiBNb2R1bGVCaW5kaW5nID0ge1xuXHRcdFx0XHRcdG5hbWUgICAgICAgICA6IGVsZW1lbnQubmFtZS50ZXh0LFxuXHRcdFx0XHRcdGtpbmQgICAgICAgICA6IGRlY2xzLmdldChvcmlnaW5hbE5hbWUpID8/ICd1bmtub3duJyxcblx0XHRcdFx0XHRzb3VyY2VNb2R1bGUgOiBtb2R1bGVJbmZvLmZpbGVQYXRoLFxuXHRcdFx0XHRcdGlzUmVFeHBvcnQgICA6IGZhbHNlLFxuXHRcdFx0XHR9O1xuXHRcdFx0XHRpZiAoZWxlbWVudC5wcm9wZXJ0eU5hbWUpIHtcblx0XHRcdFx0XHRiaW5kaW5nLmltcG9ydEFsaWFzID0gZWxlbWVudC5wcm9wZXJ0eU5hbWUudGV4dDtcblx0XHRcdFx0fVxuXHRcdFx0XHRtb2R1bGVJbmZvLmV4cG9ydGVkQmluZGluZ3MucHVzaChiaW5kaW5nKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogYGltcG9ydCBmb28gPSByZXF1aXJlKCcuL3knKWBcblx0ICovXG5cdHByaXZhdGUgcHJvY2Vzc0ltcG9ydEVxdWFscyAoXG5cdFx0aW1wb3J0RGVjbDogdHMuSW1wb3J0RXF1YWxzRGVjbGFyYXRpb24sXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRtb2R1bGVJbmZvOiBNb2R1bGVJbmZvLFxuXHRcdHNpdGVzOiBJbXBvcnRTaXRlW11cblx0KTogdm9pZCB7XG5cdFx0Y29uc3QgeyBtb2R1bGVSZWZlcmVuY2UgfSA9IGltcG9ydERlY2w7XG5cdFx0aWYgKCF0cy5pc0V4dGVybmFsTW9kdWxlUmVmZXJlbmNlKG1vZHVsZVJlZmVyZW5jZSkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Y29uc3QgeyBleHByZXNzaW9uIH0gPSBtb2R1bGVSZWZlcmVuY2U7XG5cdFx0aWYgKCF0cy5pc1N0cmluZ0xpdGVyYWwoZXhwcmVzc2lvbikpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKE1vZHVsZUdyYXBoQnVpbGRlci5za2lwQnVpbHRpbihtb2R1bGVJbmZvLCBleHByZXNzaW9uLnRleHQpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXG5cdFx0Y29uc3QgYmluZGluZzogTW9kdWxlQmluZGluZyA9IHtcblx0XHRcdG5hbWUgICAgICAgICA6IGltcG9ydERlY2wubmFtZS50ZXh0LFxuXHRcdFx0a2luZCAgICAgICAgIDogJ3Vua25vd24nLFxuXHRcdFx0c291cmNlTW9kdWxlIDogZXhwcmVzc2lvbi50ZXh0LFxuXHRcdFx0aW1wb3J0S2luZCAgIDogJ3JlcXVpcmUnLFxuXHRcdFx0aXNSZUV4cG9ydCAgIDogZmFsc2UsXG5cdFx0fTtcblx0XHRtb2R1bGVJbmZvLmltcG9ydGVkQmluZGluZ3MucHVzaChiaW5kaW5nKTtcblx0XHRzaXRlcy5wdXNoKHtcblx0XHRcdHNwZWNpZmllciA6IGV4cHJlc3Npb24udGV4dCxcblx0XHRcdGxvY2F0aW9uICA6IHRoaXMubG9jYXRpb25PZihleHByZXNzaW9uLCBzb3VyY2VGaWxlKSxcblx0XHRcdGJpbmRpbmdzICA6IFsgYmluZGluZyBdLFxuXHRcdH0pO1xuXHR9XG5cblx0LyoqXG5cdCAqIGBleHBvcnQgZGVmYXVsdCA8ZXhwcmVzc2lvbj5gXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NFeHBvcnRBc3NpZ25tZW50IChcblx0XHRzdGF0ZW1lbnQ6IHRzLkV4cG9ydEFzc2lnbm1lbnQsXG5cdFx0bW9kdWxlSW5mbzogTW9kdWxlSW5mbyxcblx0XHRkZWNsczogTWFwPHN0cmluZywgTW9kdWxlQmluZGluZ0tpbmQ+XG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IHsgZXhwcmVzc2lvbiB9ID0gc3RhdGVtZW50O1xuXHRcdGNvbnN0IGtpbmQgPSB0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbilcblx0XHRcdD8gZGVjbHMuZ2V0KGV4cHJlc3Npb24udGV4dCkgPz8gJ3Vua25vd24nXG5cdFx0XHQ6ICd1bmtub3duJztcblx0XHRjb25zdCBiaW5kaW5nOiBNb2R1bGVCaW5kaW5nID0ge1xuXHRcdFx0bmFtZSAgICAgICAgIDogJ2RlZmF1bHQnLFxuXHRcdFx0a2luZCxcblx0XHRcdHNvdXJjZU1vZHVsZSA6IG1vZHVsZUluZm8uZmlsZVBhdGgsXG5cdFx0XHRpbXBvcnRLaW5kICAgOiAnZGVmYXVsdCcsXG5cdFx0XHRpc1JlRXhwb3J0ICAgOiBmYWxzZSxcblx0XHR9O1xuXHRcdGlmICh0cy5pc0lkZW50aWZpZXIoZXhwcmVzc2lvbikpIHtcblx0XHRcdGJpbmRpbmcuaW1wb3J0QWxpYXMgPSBleHByZXNzaW9uLnRleHQ7XG5cdFx0fVxuXHRcdG1vZHVsZUluZm8uZXhwb3J0ZWRCaW5kaW5ncy5wdXNoKGJpbmRpbmcpO1xuXHR9XG5cblx0LyoqXG5cdCAqIGBleHBvcnQgZnVuY3Rpb24vY2xhc3MvY29uc3QvaW50ZXJmYWNlL3R5cGUg4oCmYCBkZWNsYXJhdGlvbnMuXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NNYXliZUV4cG9ydGVkRGVjbCAoXG5cdFx0c3RhdGVtZW50OiB0cy5TdGF0ZW1lbnQsXG5cdFx0bW9kdWxlSW5mbzogTW9kdWxlSW5mbyxcblx0XHRkZWNsczogTWFwPHN0cmluZywgTW9kdWxlQmluZGluZ0tpbmQ+XG5cdCk6IHZvaWQge1xuXHRcdGNvbnN0IG1vZGlmaWVycyA9IHRzLmNhbkhhdmVNb2RpZmllcnMoc3RhdGVtZW50KSA/IHRzLmdldE1vZGlmaWVycyhzdGF0ZW1lbnQpIDogdW5kZWZpbmVkO1xuXHRcdGNvbnN0IGhhc0V4cG9ydCA9IG1vZGlmaWVycz8uc29tZShtID0+IG0ua2luZCA9PT0gdHMuU3ludGF4S2luZC5FeHBvcnRLZXl3b3JkKSA/PyBmYWxzZTtcblx0XHRjb25zdCBoYXNEZWZhdWx0ID0gbW9kaWZpZXJzPy5zb21lKG0gPT4gbS5raW5kID09PSB0cy5TeW50YXhLaW5kLkRlZmF1bHRLZXl3b3JkKSA/PyBmYWxzZTtcblx0XHRpZiAoIWhhc0V4cG9ydCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblxuXHRcdGNvbnN0IGFkZEV4cG9ydCA9IChsb2NhbE5hbWU6IHN0cmluZyB8IHVuZGVmaW5lZCwga2luZDogTW9kdWxlQmluZGluZ0tpbmQpOiB2b2lkID0+IHtcblx0XHRcdGNvbnN0IGJpbmRpbmc6IE1vZHVsZUJpbmRpbmcgPSB7XG5cdFx0XHRcdG5hbWUgICAgICAgICA6IGhhc0RlZmF1bHQgPyAnZGVmYXVsdCcgOiBsb2NhbE5hbWUgPz8gJ2RlZmF1bHQnLFxuXHRcdFx0XHRraW5kLFxuXHRcdFx0XHRzb3VyY2VNb2R1bGUgOiBtb2R1bGVJbmZvLmZpbGVQYXRoLFxuXHRcdFx0XHRpc1JlRXhwb3J0ICAgOiBmYWxzZSxcblx0XHRcdH07XG5cdFx0XHRpZiAoaGFzRGVmYXVsdCkge1xuXHRcdFx0XHRiaW5kaW5nLmltcG9ydEtpbmQgPSAnZGVmYXVsdCc7XG5cdFx0XHRcdGlmIChsb2NhbE5hbWUpIHtcblx0XHRcdFx0XHRiaW5kaW5nLmltcG9ydEFsaWFzID0gbG9jYWxOYW1lO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0XHRtb2R1bGVJbmZvLmV4cG9ydGVkQmluZGluZ3MucHVzaChiaW5kaW5nKTtcblx0XHR9O1xuXG5cdFx0aWYgKHRzLmlzRnVuY3Rpb25EZWNsYXJhdGlvbihzdGF0ZW1lbnQpKSB7XG5cdFx0XHRhZGRFeHBvcnQoc3RhdGVtZW50Lm5hbWU/LnRleHQsICdmdW5jdGlvbicpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAodHMuaXNDbGFzc0RlY2xhcmF0aW9uKHN0YXRlbWVudCkpIHtcblx0XHRcdGFkZEV4cG9ydChzdGF0ZW1lbnQubmFtZT8udGV4dCwgJ2NsYXNzJyk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGlmICh0cy5pc0ludGVyZmFjZURlY2xhcmF0aW9uKHN0YXRlbWVudCkgfHwgdHMuaXNUeXBlQWxpYXNEZWNsYXJhdGlvbihzdGF0ZW1lbnQpKSB7XG5cdFx0XHRhZGRFeHBvcnQoc3RhdGVtZW50Lm5hbWUudGV4dCwgJ3R5cGUnKTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKHRzLmlzRW51bURlY2xhcmF0aW9uKHN0YXRlbWVudCkpIHtcblx0XHRcdGFkZEV4cG9ydChzdGF0ZW1lbnQubmFtZS50ZXh0LCAndHlwZScpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAodHMuaXNWYXJpYWJsZVN0YXRlbWVudChzdGF0ZW1lbnQpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGRlY2wgb2Ygc3RhdGVtZW50LmRlY2xhcmF0aW9uTGlzdC5kZWNsYXJhdGlvbnMpIHtcblx0XHRcdFx0aWYgKHRzLmlzSWRlbnRpZmllcihkZWNsLm5hbWUpKSB7XG5cdFx0XHRcdFx0YWRkRXhwb3J0KGRlY2wubmFtZS50ZXh0LCBkZWNscy5nZXQoZGVjbC5uYW1lLnRleHQpID8/ICdjb25zdCcpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENvbW1vbkpTIGBjb25zdCB4ID0gcmVxdWlyZSgnLi95JylgIChKUyBzb3VyY2VzIHdpdGggYWxsb3dKcykuXG5cdCAqL1xuXHRwcml2YXRlIHByb2Nlc3NSZXF1aXJlQ2FsbCAoXG5cdFx0c3RhdGVtZW50OiB0cy5TdGF0ZW1lbnQsXG5cdFx0c291cmNlRmlsZTogdHMuU291cmNlRmlsZSxcblx0XHRtb2R1bGVJbmZvOiBNb2R1bGVJbmZvLFxuXHRcdHNpdGVzOiBJbXBvcnRTaXRlW11cblx0KTogdm9pZCB7XG5cdFx0aWYgKCF0cy5pc1ZhcmlhYmxlU3RhdGVtZW50KHN0YXRlbWVudCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBkZWNsIG9mIHN0YXRlbWVudC5kZWNsYXJhdGlvbkxpc3QuZGVjbGFyYXRpb25zKSB7XG5cdFx0XHRjb25zdCB7IGluaXRpYWxpemVyIH0gPSBkZWNsO1xuXHRcdFx0aWYgKCFpbml0aWFsaXplciB8fCAhdHMuaXNDYWxsRXhwcmVzc2lvbihpbml0aWFsaXplcikpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRpZiAoIXRzLmlzSWRlbnRpZmllcihpbml0aWFsaXplci5leHByZXNzaW9uKSB8fCBpbml0aWFsaXplci5leHByZXNzaW9uLnRleHQgIT09ICdyZXF1aXJlJykge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IFsgZmlyc3RBcmcgXSA9IGluaXRpYWxpemVyLmFyZ3VtZW50cztcblx0XHRcdGlmICghZmlyc3RBcmcgfHwgIXRzLmlzU3RyaW5nTGl0ZXJhbChmaXJzdEFyZykpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRpZiAoTW9kdWxlR3JhcGhCdWlsZGVyLnNraXBCdWlsdGluKG1vZHVsZUluZm8sIGZpcnN0QXJnLnRleHQpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgbG9jYWxOYW1lID0gdHMuaXNJZGVudGlmaWVyKGRlY2wubmFtZSkgPyBkZWNsLm5hbWUudGV4dCA6IGRlY2wubmFtZS5nZXRUZXh0KCk7XG5cdFx0XHRjb25zdCBiaW5kaW5nOiBNb2R1bGVCaW5kaW5nID0ge1xuXHRcdFx0XHRuYW1lICAgICAgICAgOiBsb2NhbE5hbWUsXG5cdFx0XHRcdGtpbmQgICAgICAgICA6ICd1bmtub3duJyxcblx0XHRcdFx0c291cmNlTW9kdWxlIDogZmlyc3RBcmcudGV4dCxcblx0XHRcdFx0aW1wb3J0S2luZCAgIDogJ3JlcXVpcmUnLFxuXHRcdFx0XHRpc1JlRXhwb3J0ICAgOiBmYWxzZSxcblx0XHRcdH07XG5cdFx0XHRtb2R1bGVJbmZvLmltcG9ydGVkQmluZGluZ3MucHVzaChiaW5kaW5nKTtcblx0XHRcdHNpdGVzLnB1c2goe1xuXHRcdFx0XHRzcGVjaWZpZXIgOiBmaXJzdEFyZy50ZXh0LFxuXHRcdFx0XHRsb2NhdGlvbiAgOiB0aGlzLmxvY2F0aW9uT2YoZmlyc3RBcmcsIHNvdXJjZUZpbGUpLFxuXHRcdFx0XHRiaW5kaW5ncyAgOiBbIGJpbmRpbmcgXSxcblx0XHRcdH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBGb3JtYXQgYSBub2RlJ3MgcG9zaXRpb24gYXMgZmlsZS50czpMaW5lOkNvbCAoMS1iYXNlZCksIG1hdGNoaW5nIHRoZVxuXHQgKiBsb2NhdGlvbiBmb3JtYXQgb2YgdGhlIG90aGVyIC50YWN0aWNhIG91dHB1dHMuXG5cdCAqL1xuXHRwcml2YXRlIGxvY2F0aW9uT2YgKG5vZGU6IHRzLk5vZGUsIHNvdXJjZUZpbGU6IHRzLlNvdXJjZUZpbGUpOiBzdHJpbmcge1xuXHRcdGNvbnN0IHBvc2l0aW9uID0gc291cmNlRmlsZS5nZXRMaW5lQW5kQ2hhcmFjdGVyT2ZQb3NpdGlvbihub2RlLmdldFN0YXJ0KHNvdXJjZUZpbGUpKTtcblx0XHRjb25zdCBsb2NhdGlvbiA9IGAke3BhdGgucmVzb2x2ZShzb3VyY2VGaWxlLmZpbGVOYW1lKX06JHtwb3NpdGlvbi5saW5lICsgMX06JHtwb3NpdGlvbi5jaGFyYWN0ZXIgKyAxfWA7XG5cdFx0cmV0dXJuIGxvY2F0aW9uO1xuXHR9XG59XG4iXX0=