import { TypeNode, GeneratedTypes } from './types';
import { TypeGraphImpl } from './graph';
/**
 * TypeScript declaration file generator
 */
export declare class TypesGenerator {
    private graph;
    constructor(graph: TypeGraphImpl);
    /**
     * Generate the complete .d.ts file content
     */
    generate(): GeneratedTypes;
    /**
     * Generate a registry entry for a type node
     */
    private generateRegistryEntry;
    /**
     * Generate an instance interface for a type node
     */
    private generateInstanceInterface;
    /**
     * Generate constructor augmentation
     */
    private generateConstructorAugmentation;
    /**
     * Generate a simple type declaration for a single type
     */
    generateSingleType(node: TypeNode): string;
}
