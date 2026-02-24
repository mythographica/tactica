import { TacticaConfig } from './types';
/**
 * CLI entry point for Tactica
 *
 * Can be used standalone without the Language Service Plugin
 */
interface CLIOptions extends TacticaConfig {
    watch?: boolean;
    project?: string;
    help?: boolean;
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
