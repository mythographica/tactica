import { TypeNode, GeneratedTypes } from './types';
import { TypeGraphImpl } from './graph';
/**
 * TypeScript declaration file generator
 */
export declare class TypesGenerator {
    private graph;
    constructor(graph: TypeGraphImpl);
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
         * Generate TypeRegistry interface for type-safe lookupTyped() function
         * Import this interface and pass it to lookupTyped<TypeRegistry>() from mnemonica
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
     */
    private getInstanceTypeName;
}
