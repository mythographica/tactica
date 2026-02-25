'use strict';

/**
 * Tactica - TypeScript Language Service Plugin for Mnemonica
 *
 * Generates type definitions for Mnemonica's dynamic nested constructors,
 * enabling TypeScript to understand runtime type hierarchies created through
 * define() and decorate() calls.
 */

export { MnemonicaAnalyzer } from './analyzer';
export { TypeGraphImpl } from './graph';
export { TypesGenerator } from './generator';
export { TypesWriter } from './writer';

// Tactica's enhanced define function
export { define, decorate, create, InstanceType } from './define';

export type {
	TacticaConfig,
	TypeNode,
	TypeGraph,
	PropertyInfo,
	AnalyzeResult,
	AnalyzeError,
	GeneratedTypes,
} from './types';

// CLI entry point
export { main, run, watch, parseArgs } from './cli';

// Plugin entry point (for TypeScript Language Service)
export { default } from './plugin';

// Version
export const VERSION = '0.1.0';
