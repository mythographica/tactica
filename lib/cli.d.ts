#!/usr/bin/env node
import { TacticaConfig } from './types';
import { TacticaPlugin } from './plugins';
/**
 * CLI entry point for Tactica
 *
 * Runs the analyzer over a tsconfig project and writes .tactica/ output
 */
interface CLIOptions extends TacticaConfig {
    watch?: boolean;
    project?: string;
    help?: boolean;
    /** Custom topologica directories to scan */
    topologicaDirs?: string[];
    /** Add .js extensions to relative imports for ESM NodeNext resolution */
    esm?: boolean;
    /** Enable EDS (Execution Data Storage) tracking */
    eds?: boolean;
    /** Programmatic plugins; config-file plugins are appended after these */
    plugins?: TacticaPlugin[];
}
/**
 * Parse command line arguments
 */
declare function parseArgs(args: string[]): CLIOptions;
/**
 * Run type generation
 */
declare function run(options: CLIOptions): void;
/**
 * Watch mode
 */
declare function watch(options: CLIOptions): void;
/**
 * Main entry point
 */
declare function main(): void;
export { main, run, watch, parseArgs };
