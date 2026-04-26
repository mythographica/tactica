import * as ts from 'typescript';
import { AnalyzeResult, DefinitionInfo, UsageInfo, DriftReport } from './types';
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
    private variableToTypeMap;
    private program?;
    private _typeChecker?;
    constructor(program?: ts.Program);
    /**
     * Lazily-resolved TypeChecker. Returns undefined when the analyzer was
     * created without a ts.Program (e.g. in unit tests using
     * analyzeSource(string)). All callers must be null-safe.
     */
    private getTypeChecker;
    /**
     * Resolve a TS TypeNode (e.g. a generic argument or `this:` annotation)
     * into a property map using the TypeChecker. Returns undefined if no
     * checker is available, the type is not an object, or it has no
     * accessible properties.
     *
     * This is the bridge that lets declared interfaces in another file
     * become tactica's source of truth.
     */
    private resolvePropertiesFromTypeNode;
    /**
     * Resolve a TypeNode that represents the constructor-args generic
     * (TArgs in `define<TInstance, TArgs>`) into a ConstructorParamInfo
     * array. We treat the args type as the shape of a single positional
     * argument named `data`, mirroring the conventional
     * `function(this, data) { … }` signature. When the args type is a
     * tuple, each tuple element becomes a positional parameter.
     */
    private resolveConstructorParamsFromTypeNode;
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
     * Compare each TypeNode's declared shape (from generic args or `this:`
     * annotation) against its inferred shape (from constructor body) and
     * return a list of drift reports.
     *
     * Heuristics:
     *  - Suppress reports when there is no declared shape, since inference
     *    is the only source of truth in that case.
     *  - Suppress reports when the body uses `Object.assign(this, data)`
     *    style — i.e. inferred set is empty — because the assignments
     *    aren't visible textually. Only contradictory inferred entries
     *    raise drift.
     *  - Compare type strings as-is (the TypeChecker normalizes them).
     */
    detectDrift(): DriftReport[];
    /**
     * Add a topologica type to the analyzer for usage tracking.
     * This allows the analyzer to recognize topologica types when collecting usages.
     */
    addTopologicaType(fullPath: string, node: import('./types').TypeNode): void;
    /**
     * Set parent nodes in a source file to enable AST traversal up
     */
    private setParentNodesInSourceFile;
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
        * Track variable assignments that capture define() results
        * e.g., const User = define('UserEntity', ...) maps "User" -> "UserEntity"
        * For chained calls like const X = define('A').define('B'), we map X -> A (the root type)
        */
    private trackVariableAssignment;
    /**
        * Track variable assignments from lookupTyped() calls
        * e.g., const SentienceConstructor = lookupTyped('Sentience') maps "SentienceConstructor" -> "Sentience"
        */
    private trackLookupTypedAssignment;
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
        * Find a parent type by its name, searching in the graph
        */
    private findParentTypeByName;
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
     * Extract class property types for method return type inference
     * Maps property names to their TypeScript type strings
     * Note: Includes private/protected properties for method inference
     */
    private extractClassPropertyTypes;
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
        * Get function name from expression (identifier or property access)
        */
    private getFunctionName;
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
    /**
     * Extract the user-declared instance / args shapes from explicit
     * generic arguments on `define<TInstance, TArgs>(…)`.
     *
     * Returns whatever subset can be resolved — both, one, or neither.
     * Requires a TypeChecker (CLI path); silently no-ops without one.
     */
    private extractDeclaredFromGenerics;
    /**
     * Extract user-declared instance shape from the constructor's
     * `this:` annotation, resolved via the TypeChecker so imported
     * type aliases work across files. Returns undefined when no checker
     * is available or the annotation is missing.
     */
    private extractDeclaredFromThisAnnotation;
    /**
         * Extract constructor parameters from define() call
         * This is used for TypeRegistry constructor signatures
         * Preserves parameter names and expands object types to their structure
         */
    private extractConstructorParams;
}
