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
export interface TypeNode {
    /** Type name (e.g., "SecondType") */
    name: string;
    /** Full path (e.g., "FirstType.SecondType") */
    fullPath: string;
    /** Properties defined in this type's constructor */
    properties: Map<string, PropertyInfo>;
    /** Constructor parameters (for TypeRegistry constructor signature) */
    constructorParams?: ConstructorParamInfo[];
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
    /** Collection identifier if the type belongs to a custom collection (undefined = default/global registry) */
    collectionId?: string;
    /** Registry interface name for custom collections using Option B (user-provided registry interface) */
    registryInterfaceName?: string;
}
export interface TypeGraph {
    /** Root types, keyed by full path (custom-collection roots carry the `collectionId::` prefix) */
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
 * EDS (Execution Data Storage) kind for tracking execution flow patterns
 */
export type EDSKind = 'wrap' | 'link' | 'contextConsume' | 'errorEnrich' | 'hookAttach' | 'adapterUse';
/**
 * EDS info for execution data flow tracking
 */
export interface EDSInfo {
    /** Location in source: file.ts:Line:Col */
    location: string;
    /** Kind of EDS usage */
    kind: EDSKind;
    /** Code snippet */
    code: string;
    /** Resolved target type if detectable */
    targetType?: string;
}
/**
 * JSON output for eds.json
 */
export interface EDSJson {
    version: string;
    generatedAt: string;
    eds: Record<string, EDSInfo[]>;
}
/**
 * Flow kind for tracking native instance usage patterns
 */
export type FlowKind = 'propertyRead' | 'propertyWrite' | 'methodCall' | 'destructureRead' | 'passAsArg' | 'return' | 'spread' | 'arrayElement' | 'conditionalAccess' | 'elementAccess' | 'reassignment' | 'instantiation';
/**
 * Flow info for native instance usage tracking
 */
export interface FlowInfo {
    /** Location in source: file.ts:Line:Col */
    location: string;
    /** Kind of flow */
    kind: FlowKind;
    /** Code snippet */
    code: string;
    /** Property name if applicable */
    propertyName?: string;
    /** Resolved target type if known */
    targetType?: string;
    /** Context (function name, param position, etc.) */
    context?: string;
}
/**
 * JSON output for flow.json
 */
export interface FlowJson {
    version: string;
    generatedAt: string;
    flow: Record<string, FlowInfo[]>;
}
/**
 * JSON output for hierarchy.json
 */
export interface HierarchyJson {
    version: string;
    generatedAt: string;
    roots: HierarchyNode[];
}
/**
 * Structured hierarchy node for machine consumption.
 */
export interface HierarchyNode {
    /** Type name (e.g., "AdminType") */
    name: string;
    /** Full dotted path (e.g., "UserType.AdminType") */
    fullPath: string;
    /** Location in source: file.ts:Line:Col */
    location: string;
    /** Child types in the Trie */
    children: HierarchyNode[];
}
