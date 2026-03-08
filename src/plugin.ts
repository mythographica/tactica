'use strict';

import * as fs from 'fs';
import * as path from 'path';
import * as ts from 'typescript';
import { TacticaConfig, TypeNode } from './types';
import { MnemonicaAnalyzer } from './analyzer';
import { TopologicaAnalyzer } from './topologica-analyzer';
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
 * Merge topologica types into mnemonica graph
 */
function mergeTopologicaTypes(graph: TypeGraphImpl, topologicaTypes: Map<string, TypeNode>): void {
	for (const [fullPath, typeNode] of topologicaTypes) {
		// Skip if already exists in graph (prefer mnemonica's TypeScript analysis)
		if (graph.allTypes.has(fullPath)) {
			continue;
		}

		// Add to graph - parent relationship is already set in typeNode
		if (typeNode.parent) {
			// Add as child of parent
			graph.addChild(typeNode.parent, typeNode);
		} else {
			// Add as root
			graph.addRoot(typeNode);
		}
	}
}

/**
 * Scan for topologica directory structures
 */
function scanTopologicaDirectories(projectDir: string): string[] {
	const dirs: string[] = [];
	const possibleDirs = ['ai-types', 'types', 'topologica-types'];

	for (const dirName of possibleDirs) {
		const dirPath = path.join(projectDir, dirName);
		if (fs.existsSync(dirPath) && fs.statSync(dirPath).isDirectory()) {
			dirs.push(dirPath);
		}
	}

	// Also scan src/ subdirectory
	const srcPath = path.join(projectDir, 'src');
	if (fs.existsSync(srcPath) && fs.statSync(srcPath).isDirectory()) {
		for (const dirName of possibleDirs) {
			const dirPath = path.join(srcPath, dirName);
			if (fs.existsSync(dirPath) && fs.statSync(dirPath).isDirectory()) {
				dirs.push(dirPath);
			}
		}
	}

	return dirs;
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

		// Get the graph from mnemonica analysis
		typeGraph = analyzer.getGraph();

		// Scan for topologica directory structures
		const projectDir = info.project.getCurrentDirectory();
		const topologicaDirs = scanTopologicaDirectories(projectDir);

		// Analyze topologica directories and merge into graph
		const topologicaAnalyzer = new TopologicaAnalyzer();
		for (const dir of topologicaDirs) {
			const result = topologicaAnalyzer.analyzeDirectory(dir);
			if (result.types.size > 0) {
				mergeTopologicaTypes(typeGraph, result.types);
				if (config.verbose) {
					info.project.projectService.logger.info(
						`[Tactica] Added ${result.types.size} types from topologica directory: ${dir}`
					);
				}
			}
		}
		const generator = new TypesGenerator(typeGraph);
		const generated = generator.generateTypesFile();

		// Write types to file
		const writer = new TypesWriter(config.outputDir);
		const outputPath = writer.writeTypesFile(generated);

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
