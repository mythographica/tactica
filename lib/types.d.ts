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
    /** True if this is a getter property (readonly) */
    readonly?: boolean;
}
/** Constructor parameter info for TypeRegistry signatures */
export interface ConstructorParamInfo {
    /** Parameter name (e.g., "usages", "data", "config") */
    name: string;
    /** The type string - can be a simple type or expanded object literal */
    type: string;
    optional: boolean;
}
/**
 * Where a TypeNode's property/parameter shape was sourced from.
 * Higher-priority sources win when multiple are available.
 *
 * Priority: 'generic' > 'thisAnnotation' > 'inference'.
 */
export type ShapeSource = 'generic' | 'thisAnnotation' | 'inference';
export interface TypeNode {
    /** Type name (e.g., "SecondType") */
    name: string;
    /** Full path (e.g., "FirstType.SecondType") */
    fullPath: string;
    /** Properties defined in this type's constructor */
    properties: Map<string, PropertyInfo>;
    /** Constructor parameters (for TypeRegistry constructor signature) */
    constructorParams?: ConstructorParamInfo[];
    /**
     * Properties declared by the user via define<TInstance, …>(…) generic
     * argument or `this:` parameter annotation. Resolved through the
     * TypeChecker when ts.Program is available. Authoritative when set.
     */
    declaredProperties?: Map<string, PropertyInfo>;
    /**
     * Constructor parameters declared by the user via define<…, TArgs>(…)
     * generic argument. Authoritative when set.
     */
    declaredConstructorParams?: ConstructorParamInfo[];
    /** Where the canonical shape came from (highest-priority source). */
    propertiesSource?: ShapeSource;
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
    /** Kind of usage: instantiation, typeAnnotation, propertyAccess, lookup, reference */
    kind: 'instantiation' | 'typeAnnotation' | 'propertyAccess' | 'lookup' | 'reference';
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
/**
 * Drift detector report — emitted when a TypeNode's declared shape
 * disagrees with what the constructor body actually does.
 */
export type DriftKind = 'typeMismatch' | 'declaredOnly' | 'inferredOnly';
export interface DriftReport {
    /** Full path of the type that drifted (e.g., "Parent.Child") */
    typeName: string;
    /** Source file where the define() call lives */
    fileName: string;
    /** 1-based line number of the define() call */
    line: number;
    /** Property or parameter name that drifted */
    key: string;
    /** Type as declared (interface / generic / this: annotation) */
    declaredType: string | undefined;
    /** Type as inferred from constructor body */
    inferredType: string | undefined;
    /** What kind of drift this is */
    kind: DriftKind;
    /** Human-readable, single-line message */
    message: string;
}
