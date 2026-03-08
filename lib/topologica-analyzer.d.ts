import { TypeNode } from './types';
import { TypeGraphImpl } from './graph';
/**
 * Analyzer for Topologica directory-based type definitions
 * Scans directory structures to create type hierarchies like:
 * ai-types/Sentience/Consciousness/Empathy/Gratitude/
 */
export declare class TopologicaAnalyzer {
    private errors;
    private graph;
    /**
     * Analyze a directory structure for topologica type definitions
     */
    analyzeDirectory(directoryPath: string): {
        types: Map<string, TypeNode>;
        errors: string[];
    };
    /**
     * Recursively scan directory structure to build type hierarchy
     */
    private scanDirectory;
    /**
     * Get the type graph
     */
    getGraph(): TypeGraphImpl;
    /**
     * Get collected errors
     */
    getErrors(): string[];
}
