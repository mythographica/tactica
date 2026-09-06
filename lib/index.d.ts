/**
 * Tactica - Type definition generator for Mnemonica
 *
 * Generates type definitions for Mnemonica's dynamic nested constructors,
 * enabling TypeScript to understand runtime type hierarchies created through
 * define() and decorate() calls.
 */
export { MnemonicaAnalyzer } from './analyzer';
export { TopologicaAnalyzer } from './topologica-analyzer';
export { TypeGraphImpl } from './graph';
export { TypesGenerator } from './generator';
export { TypesWriter } from './writer';
export { ModuleGraphBuilder } from './module-graph';
export { LocalScopeWalker } from './scopes';
export type { ScopeTypeResolver } from './scopes';
export { CreationGraphBuilder } from './creation-graph';
export { mergeTacticaPlugins } from './plugins';
export type { TacticaPlugin, InstrumentationVocabulary } from './plugins';
export type { TacticaConfig, TypeNode, TypeGraph, PropertyInfo, AnalyzeResult, AnalyzeError, GeneratedTypes, DefinitionInfo, UsageInfo, DefinitionsJson, UsagesJson, InstrumentationKind, InstrumentationScope, InstrumentationPoint, InstrumentationJson, ModuleBindingKind, ModuleImportKind, ModuleBinding, ModuleInfo, CrossModuleUsage, ModuleGraph, ModulesJson, ScopeKind, ScopeInfo, ScopeVariable, ScopeAnalysis, ScopesJson, CreationGraphNode, CreationGraphEdge, CreationAnchor, CreationGraph, } from './types';
export { main, run, watch, parseArgs } from './cli';
export declare const VERSION: string;
