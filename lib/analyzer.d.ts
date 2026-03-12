import * as ts from 'typescript';
import { AnalyzeResult, DefinitionInfo, UsageInfo } from './types';
import { TypeGraphImpl } from './graph';
/**
 * AST Analyzer for finding Mnemonica define() and decorate() calls
 */
export declare class MnemonicaAnalyzer {
    private errors;
    private graph;
    private definitions;
    private usages;
    private typeAliases;
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
     * Get collected definitions
     */
    getDefinitions(): Map<string, DefinitionInfo>;
    /**
     * Get collected usages
     */
    getUsages(): Map<string, UsageInfo[]>;
    /**
     * Visit a node in the AST
     */
    private visitNode;
    /**
     * Check if a node is a define() call
     */
    private isDefineCall;
    /**
        * Extract config options from define() call
        */
    private extractConfig;
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
     * Build a type map from all parameters with inline object type annotations
     * Returns a map of "paramName.propertyName" -> type
     */
    private buildDataTypeMap;
    /**
     * Extract property access chain (e.g., "dataRenamed.id" from dataRenamed.id)
     * Handles fallbacks like: data.permissions || []
     */
    private getPropertyAccessChain;
    /**
     * Extract property assignment from statement
     */
    private extractPropertyFromStatement;
    /**
     * Extract properties from class declaration (including methods and getters)
     */
    private extractClassProperties;
    /**
     * Infer method type from method declaration
     */
    private inferMethodType;
    /**
        * Extract properties from `this` parameter type annotation
        * Handles patterns like: function(this: SomeType, data: SomeType) { }
        */
    private extractThisParamProperties;
    /**
        * Infer TypeScript type from type node
        */
    /**
     * Infer TypeScript type from type node
     */
    private inferType;
    /**
        * Infer return type from a method declaration
        * Uses explicit return type annotation or infers from return statements
        */
    private inferReturnType;
    /**
        * Infer return type by analyzing return statements in the method body
        */
    private inferReturnTypeFromBody;
    /**
        * Get full text from a qualified name (e.g., Namespace.Type)
        */
    private getQualifiedNameText;
    /**
     * Infer type from initializer
     */
    private inferTypeFromInitializer;
    /**
        * Collect usage information for type references
        */
    private collectUsage;
    /**
        * Add a usage to the collection
        */
    private addUsage;
    /**
        * Get type name from expression (identifier or property access)
        */
    private getTypeNameFromExpression;
    /**
        * Resolve full type path from property access
        */
    private resolveTypePath;
    /**
        * Check if a name looks like a type (starts with uppercase)
        */
    private isLikelyTypeName;
}
