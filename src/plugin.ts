'use strict';

import * as ts from 'typescript';
import { TacticaConfig } from './types';
import { MnemonicaAnalyzer } from './analyzer';
import { TypeGraphImpl } from './graph';
import { TypesGenerator } from './generator';
import { TypesWriter } from './writer';

/**
 * TypeScript Language Service Plugin for Mnemonica
 *
 * This plugin integrates with TypeScript's language service to provide
 * type information for Mnemonica's dynamic nested constructors.
 */

interface PluginInfo {
	config: TacticaConfig;
	project: ts.server.Project;
	serverHost: ts.server.ServerHost;
	moduleResolver: ts.ModuleResolutionHost;
}

let pluginInfo: PluginInfo | undefined;
let typeGraph = new TypeGraphImpl();

/**
 * Initialize the plugin
 */
function init(modules: { typescript: typeof ts }): ts.server.PluginModule {
	const tsModule = modules.typescript;

	function create(info: ts.server.PluginCreateInfo): ts.LanguageService {
		const config: TacticaConfig = info.config || {};
		config.outputDir = config.outputDir || '.tactica';

		// Store plugin info
		pluginInfo = {
			config,
			project: info.project,
			serverHost: info.serverHost,
			moduleResolver: info.project,
		};

		// Set up file watching
		setupFileWatcher(info, tsModule);

		// Initial type generation
		generateTypes(info, tsModule);

		// Wrap the language service to intercept requests if needed
		const proxy: ts.LanguageService = Object.create(null);
		const oldService = info.languageService;

		for (const key of Object.keys(oldService) as Array<keyof ts.LanguageService>) {
			const fn = oldService[key];
			(proxy as any)[key] = (...args: any[]) => {
				return (fn as any).apply(oldService, args);
			};
		}

		return proxy;
	}

	function onConfigurationChanged(config: TacticaConfig): void {
		if (pluginInfo) {
			pluginInfo.config = { ...pluginInfo.config, ...config };
		}
	}

	return {
		create,
		onConfigurationChanged,
	};
}

/**
 * Set up file watching for incremental updates
 */
function setupFileWatcher(info: ts.server.PluginCreateInfo, _tsModule: typeof ts): void {
	const serverHost = info.serverHost;

	// Hook into file change notifications
	const originalFileChanged = (serverHost as any).fileChanged;
	if (originalFileChanged) {
		(serverHost as any).fileChanged = function(...args: any[]) {
			const result = originalFileChanged.apply(this, args);
			// Regenerate types when files change
			generateTypes(info, _tsModule);
			return result;
		};
	}
}

/**
 * Generate types from the project
 */
function generateTypes(info: ts.server.PluginCreateInfo, _tsModule: typeof ts): void {
	try {
		const program = info.languageService.getProgram();
		if (!program) {
			return;
		}

		const config = pluginInfo?.config || { outputDir: '.tactica' };
		const include = config.include || ['**/*.ts'];
		const exclude = config.exclude || ['**/*.d.ts', 'node_modules/**'];

		// Create analyzer
		const analyzer = new MnemonicaAnalyzer(program);

		// Clear existing graph
		typeGraph.clear();

		// Analyze all source files
		for (const sourceFile of program.getSourceFiles()) {
			// Skip declaration files and files outside the project
			if (sourceFile.isDeclarationFile) {
				continue;
			}

			const fileName = sourceFile.fileName;

			// Check exclude patterns
			if (exclude.some(pattern => matchesGlob(fileName, pattern))) {
				continue;
			}

			// Check include patterns (if specified)
			if (include.length > 0 && !include.some(pattern => matchesGlob(fileName, pattern))) {
				continue;
			}

			// Analyze the file
			analyzer.analyzeFile(sourceFile);
		}

		// Get the graph and generate types
		typeGraph = analyzer.getGraph();
		const generator = new TypesGenerator(typeGraph);
		const generated = generator.generate();

		// Write types to file
		const writer = new TypesWriter(config.outputDir);
		const outputPath = writer.write(generated);

		// Log success
		if (config.verbose) {
			info.project.projectService.logger.info(
				`[Tactica] Generated types at ${outputPath} (${generated.types.length} types)`
			);
		}
	} catch (error) {
		info.project.projectService.logger.info(
			`[Tactica] Error generating types: ${error}`
		);
	}
}

/**
 * Simple glob matching function
 */
function matchesGlob(filePath: string, pattern: string): boolean {
	// Convert glob pattern to regex
	const regexPattern = pattern
		.replace(/\*\*/g, '<<<DOUBLESTAR>>>')
		.replace(/\*/g, '[^/]*')
		.replace(/<<<DOUBLESTAR>>>/g, '.*')
		.replace(/\?/g, '.');

	const regex = new RegExp(regexPattern);
	return regex.test(filePath);
}

// Export for TypeScript Language Service
export = init;
