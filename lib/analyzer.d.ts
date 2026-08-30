import * as ts from 'typescript';
import { AnalyzeResult, DefinitionInfo, UsageInfo, EDSInfo, FlowInfo } from './types';
import { TypeGraphImpl } from './graph';
/**
 * AST Analyzer for finding Mnemonica define() and decorate() calls
 */
export declare class MnemonicaAnalyzer {
    private errors;
    private graph;
    private definitions;
    private usages;
    private edsUsages;
    private flowUsages;
    private edsScopeByNode;
    private typeAliases;
    private variableToTypeMap;
    private moduleObjectVariables;
    private createTypesCollectionVariables;
    private collectionVariables;
    private collectionInfo;
    private collectionCounter;
    constructor(program?: ts.Program);
    /**
     * Reset usage-related state for a fresh pass.
     * Call before the usage-collection pass to avoid duplicates from definition pass.
     */
    resetUsages(): void;
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
     * Get collected EDS usages
     */
    getEDSUsages(): Map<string, EDSInfo[]>;
    /**
     * Get collected flow usages
     */
    getFlowUsages(): Map<string, FlowInfo[]>;
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
     * Track imports from 'mnemonica' so aliases of the module object and
     * createTypesCollection are recognized without relying on the type checker.
     */
    private trackImports;
    /**
     * Track aliases of the mnemonica module object, e.g.:
     *   const m = mnemonica;
     *   const App = m;
     */
    private trackModuleObjectAliases;
    /**
     * Track custom collection variables, e.g.:
     *   const MyCollection = createTypesCollection();
     *   const Other = MyCollection;
     *
     * Also detects Option B user-provided registry interfaces:
     *   export interface MyCollectionRegistry {}
     *   const MyCollection = createTypesCollection<MyCollectionRegistry>();
     */
    private trackCollectionAliases;
    /**
     * Extract the registry interface name from createTypesCollection<Registry>()
     * when the interface is declared in the same source file.
     */
    private extractRegistryInterfaceName;
    /**
     * Get the registry interface name for a collection id.
     */
    private getRegistryInterfaceName;
    /**
     * Check if an expression is a createTypesCollection() call.
     * Handles:
     *   createTypesCollection()
     *   ctc() // aliased import
     *   mnemonica.createTypesCollection() // module object method
     *   m.createTypesCollection() // aliased module object
     */
    private isCreateTypesCollectionCall;
    /**
     * Generate a unique collection identifier.
     */
    private nextCollectionId;
    /**
     * Check if a node is a define() call
     */
    private isDefineCall;
    /**
     * Check if a node is a lazy() call
     */
    private isLazyCall;
    /**
        * Extract config options from an object literal
        */
    private extractConfigFromObjectLiteral;
    /**
        * Extract config options from define() call
        */
    private extractConfig;
    /**
        * Check if a node is a @decorate() decorator
        */
    private isDecorateDecorator;
    /**
     * Mark a call expression as processed and return whether it already was.
     */
    private markProcessed;
    /**
     * Process a define() call
     */
    private processDefineCall;
    /**
     * Process a lazy() call
     */
    private processLazyCall;
    /**
     * Extract lazy() call arguments into a normalized shape.
     * Handles named/unnamed and explicit-source forms, both as free calls
     * and as method calls.
     */
    private extractLazyCallArgs;
    /**
     * Unwrap the constructor returned by a lazy getter.
     * Supports:
     *   () => class Name {}
     *   () => function Name() {}
     *   () => { return class Name {}; }
     *   function () { return function Name() {}; }
     */
    private unwrapLazyGetter;
    /**
     * Extract a constructor name from a class expression, class declaration,
     * or named function expression.
     */
    private extractConstructorName;
    /**
     * Extract the type name from either a define() or lazy() call.
     */
    private extractMnemonicaTypeName;
    /**
     * Extract the full lazy() call context: type name, parent type, and collection.
     * Handles direct calls, property-access calls, chained calls, and the
     * explicit-source form `lazy(source, 'TypeName', getter)`.
     */
    private extractLazyContext;
    /**
     * Extract config options from lazy() call
     */
    private extractLazyConfig;
    /**
        * Track variable assignments that capture define() results
        * e.g., const User = define('UserEntity', ...) maps "User" -> "UserEntity"
        * For chained calls like const X = define('A').define('B'), we map X -> A (the root type)
        */
    private trackVariableAssignment;
    /**
        * Track variable assignments from lookup() calls
        * e.g., const SentienceConstructor = lookup('Sentience') maps "SentienceConstructor" -> "Sentience"
        */
    private trackLookupAssignment;
    /**
        * Track variable assignments from new Type() calls
        * e.g., const user = new UserType() maps "user" -> "UserType"
        */
    private trackNewAssignment;
    /**
        * Process a @decorate() decorator
     */
    private processDecorateDecorator;
    /**
     * Extract type name from define() call arguments.
     * Handles:
     *   define('TypeName', handler)
     *   define(source, 'TypeName', handler)   // explicit-source form
     *   define(function TypeName() {})
     *   define(() => class TypeName {})
     */
    private extractTypeName;
    /**
     * Extract the full define() call context: type name, parent type, and collection.
     * Handles direct calls, property-access calls, chained calls, and the
     * explicit-source form `define(source, 'TypeName', handler)`.
     */
    private extractDefineContext;
    /**
     * Prefix a dotted type path with a collection identifier so custom-collection
     * types do not collide with default-collection types in the graph.
     */
    private prefixCollectionPath;
    /**
     * Resolve a define() source identifier to either a parent type, a collection,
     * or the default (module object) collection.
     */
    private resolveDefineSource;
    /**
     * Check if a call expression is a lookup() call.
     */
    private isLookupCall;
    /**
     * Resolve a lookup() call to a dotted type path (best effort).
     * Handles:
     *   lookup('User')
     *   lookup(source, 'User')
     *   App.lookup('User')
     *   collection.lookup('User.Admin')
     */
    private resolveLookupPath;
    /**
        * Find a parent type by its name, searching in the graph.
        * When collectionId is provided, only types from that collection are considered.
        */
    private findParentTypeByName;
    /**
        * Find a parent type from an identifier reference.
        * Handles both aliased variables (const User = define('UserEntity', ...))
        * and direct class/type names.
        */
    private findParentTypeByIdentifier;
    /**
     * Get the leftmost identifier of a property-access chain.
     * For `App.define('User').define('Admin')` this returns the `App` identifier.
     */
    private getRootIdentifier;
    /**
        * Get property chain from nested access
        */
    private getPropertyChain;
    /**
     * Determine the constructor expression for either a define() or lazy() call.
     * For define() this is the construct handler; for lazy() it is the value
     * returned by the lazy getter.
     */
    private extractConstructorExpression;
    /**
     * Extract properties from constructor function
     */
    private extractProperties;
    /**
     * Extract properties from a constructor expression (function, arrow, or class).
     */
    private extractPropertiesFromConstructor;
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
     * Collect EDS (Execution Data Storage) usage information
     */
    private collectEDS;
    /**
     * Resolve type from EDS call argument (best effort)
     */
    private resolveEDSArgumentType;
    /**
     * Resolve the enclosing mnemonica scope of an EDS call site by walking
     * up the parent chain: nearest define()/lazy() call whose handler holds
     * the node, or nearest @decorate()-ed class declaration. Best effort —
     * returns undefined for calls outside any type scope (module top level).
     */
    private resolveEDSScope;
    /**
     * Add an EDS usage to the collection
     */
    private addEDS;
    /**
     * Collect native flow patterns (instance usage after creation)
     * Phase 1: property access, method calls, arguments, return, destructuring, etc.
     */
    private collectFlow;
    /**
     * Collect property access flow (read or conditional)
     */
    private collectFlowPropertyAccess;
    /**
     * Collect element access flow: user['name']
     */
    private collectFlowElementAccess;
    /**
     * Collect assignment flow: user.name = value or user = other
     */
    private collectFlowAssignment;
    /**
     * Collect method call flow: user.validate()
     */
    private collectFlowMethodCall;
    /**
     * Collect argument passing flow: processUser(user)
     */
    private collectFlowArgumentPass;
    /**
     * Collect destructuring flow: const { name } = user
     */
    private collectFlowDestructure;
    /**
     * Collect return flow: return user
     */
    private collectFlowReturn;
    /**
     * Collect spread flow: { ...user }
     */
    private collectFlowSpread;
    /**
     * Resolve type from an expression (identifier, property access, etc.)
     */
    private resolveExpressionType;
    /**
     * Add a flow usage to the collection
     */
    private addFlow;
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
             * Resolve a constructor parameter type, expanding inline object literals
             * and type aliases where possible.
             */
    private resolveConstructorParamType;
    /**
             * Extract constructor parameters from a class-like node.
             */
    private extractClassConstructorParams;
    /**
             * Extract constructor parameters from define() call
             * This is used for TypeRegistry constructor signatures
             * Preserves parameter names and expands object types to their structure
             */
    private extractConstructorParams;
    /**
             * Extract constructor parameters from a constructor expression.
             */
    private extractConstructorParamsFromConstructor;
}
