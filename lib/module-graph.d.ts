import * as ts from 'typescript';
import { ModuleGraph, ModuleInfo } from './types';
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
export declare class ModuleGraphBuilder {
    private compilerOptions;
    private modules;
    private localDecls;
    private importSites;
    private resolutionCache;
    constructor(program?: ts.Program, compilerOptions?: ts.CompilerOptions);
    /**
     * Track one source file. Re-adding the same file replaces its record,
     * so a builder may safely be reused across passes.
     */
    addFile(sourceFile: ts.SourceFile): ModuleInfo;
    /**
     * Resolve all specifiers, backfill binding kinds from origin modules,
     * derive dependencies, cross-module mnemonica-type edges, and cycles.
     * `definedTypesByFile` maps absolute file path -> mnemonica type fullPaths
     * defined there (from the analyzer's definitions).
     */
    build(definedTypesByFile?: Map<string, string[]>): ModuleGraph;
    /**
     * Resolve a specifier to an absolute file path via ts.resolveModuleName
     * with the program's compilerOptions. Returns undefined on failure.
     */
    private resolveModule;
    /**
     * True for Node.js builtins in both bare and `node:`-prefixed forms
     * ('path', 'node:path', 'fs/promises', 'node:fs/promises', …).
     */
    private static isBuiltinSpecifier;
    /**
     * Record a builtin import on the module (honesty marker) and skip it
     * entirely: no bindings, no site, no dependency, no edge.
     * Returns true when the specifier was a builtin (caller must return early).
     */
    private static skipBuiltin;
    /**
     * Chase a binding to the module that actually declares it, following
     * re-export chains (barrels). Cycle-guarded. Returns undefined when the
     * origin is external or the chain loops.
     */
    private resolveOrigin;
    /**
     * Match a binding against a module's defined mnemonica types.
     * Returns the matched fullPath, or undefined when the binding is not a
     * mnemonica type of that module.
     */
    private matchDefinedType;
    /**
     * Three-color DFS over project-internal dependencies. Cycles are recorded
     * (mnemonica strictChain:false permits non-linear construction), never
     * treated as errors.
     */
    private detectCycles;
    /**
     * Rotation-independent cycle key: smallest path first.
     */
    private static cycleKey;
    /**
     * Pass 1: record every named top-level declaration's kind.
     */
    private collectLocalDecl;
    /**
     * Classify a variable declaration: arrow/function initializers are
     * 'function' (holder functions the walker follows), class expressions
     * are 'class', everything else is 'const'.
     */
    private static variableKind;
    /**
     * Pass 2: imports, exports, requires, exported declarations.
     */
    private processStatement;
    private processImport;
    private processExportDeclaration;
    /**
     * `import foo = require('./y')`
     */
    private processImportEquals;
    /**
     * `export default <expression>`
     */
    private processExportAssignment;
    /**
     * `export function/class/const/interface/type …` declarations.
     */
    private processMaybeExportedDecl;
    /**
     * CommonJS `const x = require('./y')` (JS sources with allowJs).
     */
    private processRequireCall;
    /**
     * Format a node's position as file.ts:Line:Col (1-based), matching the
     * location format of the other .tactica outputs.
     */
    private locationOf;
}
