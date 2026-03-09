/**
 * Type definitions for Tactica
 */
export interface TacticaConfig {
    /** Output directory for generated types (default: .tactica) */
    outputDir?: string;
    /** Files to include (glob patterns) */
    include?: string[];
    /** Files to exclude (glob patterns) */
    exclude?: string[];
    /** Enable verbose logging */
    verbose?: boolean;
    /** Generate global augmentation instead of module augmentation (default: true) */
    globalAugmentation?: boolean;
}
export interface PropertyInfo {
    name: string;
    type: string;
    optional: boolean;
}
export interface TypeNode {
    /** Type name (e.g., "SecondType") */
    name: string;
    /** Full path (e.g., "FirstType.SecondType") */
    fullPath: string;
    /** Properties defined in this type's constructor */
    properties: Map<string, PropertyInfo>;
    /** Parent type node */
    parent?: TypeNode;
    /** Child types */
    children: Map<string, TypeNode>;
    /** Source file path */
    sourceFile: string;
    /** Line number in source */
    line: number;
    /** Column number in source */
    column: number;
    /** Constructor function name or class name */
    constructorName?: string;
}
export interface TypeGraph {
    /** Root types (defined at module level) */
    roots: Map<string, TypeNode>;
    /** All types by full path */
    allTypes: Map<string, TypeNode>;
    /** Add a root type */
    addRoot(node: TypeNode): void;
    /** Find a type by full path */
    findType(fullPath: string): TypeNode | undefined;
    /** Get all types as array */
    getAllTypes(): TypeNode[];
    /** Clear the graph */
    clear(): void;
}
export interface AnalyzeResult {
    /** Types found in the analysis */
    types: TypeNode[];
    /** Errors encountered */
    errors: AnalyzeError[];
}
export interface AnalyzeError {
    message: string;
    file: string;
    line: number;
    column: number;
}
export interface GeneratedTypes {
    /** Content of the .d.ts file */
    content: string;
    /** Types that were generated */
    types: string[];
}
/**
 * Definition info for code navigation
 */
export interface DefinitionInfo {
    /** Type name (e.g., "AdminType") */
    name: string;
    /** Location in source: file.ts:Line:Col */
    location: string;
    /** How type was created: 'define' or 'decorate' */
    kind: 'define' | 'decorate';
    /** Parent type full path, null if root */
    parent: string | null;
    /** strictChain config option */
    strictChain: boolean;
    /** blockErrors config option */
    blockErrors: boolean;
}
/**
 * Usage info for code navigation
 */
export interface UsageInfo {
    /** Location in source: file.ts:Line:Col */
    location: string;
    /** Kind of usage: instantiation, typeAnnotation, propertyAccess */
    kind: 'instantiation' | 'typeAnnotation' | 'propertyAccess' | 'reference';
    /** Code snippet */
    code: string;
}
/**
 * JSON output for definitions.json
 */
export interface DefinitionsJson {
    version: string;
    generatedAt: string;
    definitions: Record<string, DefinitionInfo>;
}
/**
 * JSON output for usages.json
 */
export interface UsagesJson {
    version: string;
    generatedAt: string;
    usages: Record<string, UsageInfo[]>;
}
