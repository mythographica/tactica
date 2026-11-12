import { TypeNode, GeneratedTypes, ResolutionError, BuilderValue } from './types';
import { TypeGraphImpl } from './graph';
/**
 * Path-aware resolver for mnemonica graph type names referenced inside type
 * strings while generating output. Returns the unique type, 'ambiguous', or
 * undefined (resolves to nothing) — see resolveGraphTypeReference.
 */
export type GraphReferenceResolver = (simpleName: string, currentNode: TypeNode) => TypeNode | 'ambiguous' | undefined;
/**
 * TypeScript declaration file generator
 */
export declare class TypesGenerator {
    private graph;
    private referenceResolver?;
    private builderValues;
    private esm;
    private outputDir;
    private resolutionErrors;
    constructor(graph: TypeGraphImpl, esm?: boolean, outputDir?: string, referenceResolver?: GraphReferenceResolver | undefined, builderValues?: BuilderValue[]);
    /**
     * Get import path with optional .js extension for ESM NodeNext
     */
    private importPath;
    private derivedTypePaths;
    private builderImportName;
    private pushBuilderImports;
    /**
        * Generate a types.ts file with complete instance interfaces
        * This includes all properties extracted from the constructors
        */
    generateTypesFile(): GeneratedTypes;
    /**
         * Generate a complete instance type alias with all properties
         * This is for the types.ts file that users import from
         */
    private generateCompleteInstanceInterface;
    /**
         * Emit one nested-ctor field. Default-collection children use core's
         * complete constructor surface. Option B uses dual signatures:
         * construct + the chain-tip CALL form, both resolving through
         * getConstructorResultType.
         */
    private pushChildConstructorField;
    /**
     * The type a constructor invocation resolves to: the instance type, or
     * Promise<InstanceType> for async handlers (isAsync). The instance type
     * itself is never wrapped — only the constructor RESULT positions
     * (subtype property twins + registry entries).
     */
    private getConstructorResultType;
    /**
         * Generate a simple type declaration for a single type
         */
    generateSingleType(node: TypeNode): string;
    /**
         * Generate TypeRegistry interface for type-safe lookup() function
         * Augment mnemonica's TypeRegistry so lookup('TypeName') returns the typed constructor
         */
    generateTypeRegistry(): GeneratedTypes;
    /**
         * Generate constructor parameter list for a type node (the "(…)" part)
         */
    private generateConstructorParams;
    private generateConstructorArgs;
    /**
         * Generate constructor signature for a type node
         * Uses constructorParams for TypeRegistry signature (not instance properties)
         */
    private generateConstructorSignature;
    /**
         * Get the full dotted path for a type node
         */
    private getFullPath;
    /**
     * Get the instance type name for a node
     * Uses full path with underscores: Usages.UsageEntry -> Usages_UsageEntry
     * For Option B custom collections, prefixes with the registry interface name.
     */
    private getInstanceTypeName;
    /**
     * Resolve a simple type name to its full path name
     * e.g., "DefinitionEntry" -> "Definitions_DefinitionEntry"
     *
     * With a referenceResolver installed (the CLI path), resolution is
     * path-aware per the graph identity law: the resolver returns the unique
     * type, 'ambiguous', or undefined — the latter two record a hard-fail
     * ResolutionError and emit `unknown` instead of silently picking a
     * first match. Without a resolver the legacy first-match scan stays.
     */
    private resolveTypeName;
    /**
     * Hard-fail graph reference errors recorded while generating (see
     * referenceResolver). The CLI prints every location and writes no output.
     */
    getResolutionErrors(): ResolutionError[];
    /**
     * Resolve simple type names to full path names within a type string
     * Handles complex types like Array<UsageEntry>, Map<string, TypeEntry>, etc.
     */
    private resolveTypeInString;
    /**
     * Group collection type nodes by their registry interface name and the
     * collection's home file (the module declaring the interface — the
     * augmentation target), NOT each type's own define file: multi-file
     * collections define types across many modules.
     * Returns a map keyed by `${registryInterfaceName}::${sourceFile}`.
     */
    private groupCollectionRegistryNodes;
    /**
     * Resolve a source file path to a module specifier relative to the output directory,
     * suitable for use in a `declare module '...'` block.
     */
    private resolveModulePath;
}
