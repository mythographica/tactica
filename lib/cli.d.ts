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
 * Run type generation. Returns 0 on success; 1 when the graph identity law
 * aborted the run (failures printed, no .tactica output written).
 */
declare function run(options: CLIOptions): number;
/**
 * chokidar options for watch mode. The initial run has already happened,
 * so existing files are not reported as added (ignoreInitial: one full
 * run per existing file otherwise). The directories tactica writes are
 * always ignored, whatever the include/exclude globs say: a written file
 * would trigger another run.
 */
declare function watchOptions(options: CLIOptions, tsconfigPath: string): {
    cwd: string;
    ignored: (string | ((filePath: string) => boolean))[];
    ignoreInitial: boolean;
    persistent: boolean;
};
/**
 * Watch mode
 */
declare function watch(options: CLIOptions): void;
/**
 * Main entry point
 */
declare function main(): void;
export { main, run, watch, parseArgs, watchOptions };
