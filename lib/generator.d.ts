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
         * Uses intersection types for inheritance (types can't extend)
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
}
