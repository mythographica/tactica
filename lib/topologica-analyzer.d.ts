import { TypeNode } from './types';
import { TypeGraphImpl } from './graph';
/**
 * Analyzer for Topologica directory-based type definitions
 * Scans directory structures to create type hierarchies like:
 * ai-types/Sentience/Consciousness/Empathy/Gratitude/
 *
 * Now with AST-based property extraction from TypeScript/JavaScript files
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
     * Extract properties from a directory's index file
     * Supports both .ts and .js files
     */
    private extractPropertiesFromDir;
    /**
     * Collect type aliases from source file
     * e.g., export type SentienceData = { awareness?: string; }
     */
    private collectTypeAliases;
    /**
     * Extract property assignments from a source file
     * Returns constructor parameters and handler location if found
     */
    private extractPropertiesFromSourceFile;
    /**
     * Extract `this.property = value` assignments from a function body
     */
    private extractThisProperties;
    /**
     * Check if a call expression is Object.assign(this, ...)
     */
    private isObjectAssignCall;
    /**
     * Extract properties from Object.assign(this, data) pattern
     */
    private extractFromObjectAssign;
    /**
     * Extract constructor parameters from a function
     * Similar to main analyzer - skips `this` parameter and expands data types
     */
    private extractConstructorParams;
    /**
     * Expand a type node to its object literal representation
     * Similar to main analyzer's resolveTypeAndExtract
     */
    private expandTypeToObject;
    /**
     * Convert a TypeScript type node to a simple string representation
     */
    private typeNodeToSimpleString;
    /**
     * Infer TypeScript type from an expression
     */
    private inferType;
    /**
     * Infer type from new expressions like new Date(), new Array(), etc.
     */
    private inferNewExpressionType;
    /**
     * Infer type from call expressions like Date.now(), parseInt(), etc.
     */
    private inferCallExpressionType;
    /**
     * Get the type graph
     */
    getGraph(): TypeGraphImpl;
    /**
     * Get collected errors
     */
    getErrors(): string[];
}
