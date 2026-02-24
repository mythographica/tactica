import * as ts from 'typescript';
import { AnalyzeResult } from './types';
import { TypeGraphImpl } from './graph';
/**
 * AST Analyzer for finding Mnemonica define() and decorate() calls
 */
export declare class MnemonicaAnalyzer {
    private errors;
    private graph;
    constructor(program?: ts.Program);
    /**
     * Analyze a source file for Mnemonica type definitions
     */
    analyzeFile(sourceFile: ts.SourceFile): AnalyzeResult;
    /**
     * Analyze source code string
     */
    analyzeSource(sourceCode: string, fileName?: string): AnalyzeResult;
    /**
     * Get the type graph
     */
    getGraph(): TypeGraphImpl;
    /**
     * Visit a node in the AST
     */
    private visitNode;
    /**
     * Check if a node is a define() call
     */
    private isDefineCall;
    /**
     * Check if a node is a @decorate() decorator
     */
    private isDecorateDecorator;
    /**
     * Process a define() call
     */
    private processDefineCall;
    /**
     * Process a @decorate() decorator
     */
    private processDecorateDecorator;
    /**
     * Extract type name from define() call arguments
     */
    private extractTypeName;
    /**
     * Find parent type node for nested define calls
     */
    private findParentType;
    /**
     * Get property chain from nested access
     */
    private getPropertyChain;
    /**
     * Extract properties from constructor function
     */
    private extractProperties;
    /**
     * Extract property assignment from statement
     */
    private extractPropertyFromStatement;
    /**
     * Extract properties from class declaration
     */
    private extractClassProperties;
    /**
     * Infer TypeScript type from type node
     */
    private inferType;
    /**
     * Infer type from initializer
     */
    private inferTypeFromInitializer;
}
