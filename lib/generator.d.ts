import { TypeNode, GeneratedTypes } from './types';
import { TypeGraphImpl } from './graph';
/**
 * TypeScript declaration file generator
 */
export declare class TypesGenerator {
    private graph;
    private esm;
    private outputDir;
    constructor(graph: TypeGraphImpl, esm?: boolean, outputDir?: string);
    /**
     * Get import path with optional .js extension for ESM NodeNext
     */
    private importPath;
    /**
        * Generate global augmentation file that augments user classes directly
        * This allows using decorated classes without manual type casting
        *
        * All types are placed in the global scope via declare global, which allows
        * them to be accessed from any module without imports. Interfaces declared
        * in the global scope will merge with classes of the same name in user modules.
        */
    generateGlobalAugmentation(): GeneratedTypes;
    /**
         * Generate instance type alias (describes what the instance IS)
         * Uses ProtoFlat for proper inheritance (excludes overridden parent props)
         */
    private generateInstanceType;
    /**
         * Generate class interface for TypeScript declaration merging
         * This merges with the actual class to provide proper typing
         */
    private generateClassInterface;
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
         * Generate a simple type declaration for a single type
         */
    generateSingleType(node: TypeNode): string;
    /**
         * Generate TypeRegistry interface for type-safe lookup() function
         * Augment mnemonica's TypeRegistry so lookup('TypeName') returns the typed constructor
         */
    generateTypeRegistry(): GeneratedTypes;
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
     */
    private resolveTypeName;
    /**
     * Resolve simple type names to full path names within a type string
     * Handles complex types like Array<UsageEntry>, Map<string, TypeEntry>, etc.
     */
    private resolveTypeInString;
    /**
     * Group collection type nodes by their registry interface name and source file.
     * Returns a map keyed by `${registryInterfaceName}::${sourceFile}`.
     */
    private groupCollectionRegistryNodes;
    /**
     * Resolve a source file path to a module specifier relative to the output directory,
     * suitable for use in a `declare module '...'` block.
     */
    private resolveModulePath;
}
