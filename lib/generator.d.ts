import { TypeNode, GeneratedTypes } from './types';
import { TypeGraphImpl } from './graph';
/**
 * TypeScript declaration file generator
 */
export declare class TypesGenerator {
    private graph;
    constructor(graph: TypeGraphImpl);
    /**
     * Generate the complete .d.ts file content for module augmentation
     * This adds nested constructors to mnemonica's instance types
     */
    generate(): GeneratedTypes;
    /**
        * Generate global augmentation file that augments user classes directly
        * This allows using decorated classes without manual type casting
        */
    generateGlobalAugmentation(): GeneratedTypes;
    /**
         * Generate instance type alias (describes what the instance IS)
         * Uses intersection types for inheritance (types can't extend)
         */
    private generateInstanceType;
    /**
     * Generate class interface (describes constructor behavior)
     * Class extends parent class, contains instance properties and constructors
     */
    private generateClassInterface;
    /**
* Generate a types.ts file with complete instance interfaces
* This includes all properties extracted from the constructors
*/
    generateTypesFile(): GeneratedTypes;
    /**
     * Generate an instance interface for a type node
     */
    private generateInstanceInterface;
    /**
     * Generate a complete instance interface with all properties
     * This is for the types.ts file that users import from
     */
    private generateCompleteInstanceInterface;
    /**
     * Generate a simple type declaration for a single type
     */
    generateSingleType(node: TypeNode): string;
}
