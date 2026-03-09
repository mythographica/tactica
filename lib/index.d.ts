/**
 * Tactica - TypeScript Language Service Plugin for Mnemonica
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
export type { TacticaConfig, TypeNode, TypeGraph, PropertyInfo, AnalyzeResult, AnalyzeError, GeneratedTypes, DefinitionInfo, UsageInfo, DefinitionsJson, UsagesJson, } from './types';
export { main, run, watch, parseArgs } from './cli';
export { default } from './plugin';
export declare const VERSION: string;
