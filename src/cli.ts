#!/usr/bin/env node
'use strict';

import * as fs from 'fs';
import * as path from 'path';
import * as ts from 'typescript';
import { MnemonicaAnalyzer } from './analyzer';
import { TopologicaAnalyzer } from './topologica-analyzer';
import { TypesGenerator } from './generator';
import { TypesWriter } from './writer';
import { TacticaConfig, TypeNode } from './types';
import { TypeGraphImpl } from './graph';

/**
 * CLI entry point for Tactica
 *
 * Can be used standalone without the Language Service Plugin
 */

interface CLIOptions extends TacticaConfig {
	watch?: boolean;
	project?: string;
	help?: boolean;
	/** Custom topologica directories to scan */
	topologicaDirs?: string[];
}

/**
 * Parse command line arguments
 */
function parseArgs(args: string[]): CLIOptions {
	const options: CLIOptions = {};

	for (let i = 0; i < args.length; i++) {
		const arg = args[i];

		switch (arg) {
			case '-w':
			case '--watch':
				options.watch = true;
				break;
			case '-p':
			case '--project':
				options.project = args[++i];
				break;
			case '-o':
			case '--output':
				options.outputDir = args[++i];
				break;
			case '-i':
			case '--include':
				options.include = (options.include || []).concat(args[++i].split(','));
				break;
			case '-e':
			case '--exclude':
				options.exclude = (options.exclude || []).concat(args[++i].split(','));
				break;
			case '-m':
			case '--module-augmentation':
				options.globalAugmentation = false;
				break;
			case '-v':
			case '--verbose':
				options.verbose = true;
				break;
			case '-t':
			case '--topologica':
				options.topologicaDirs = (options.topologicaDirs || []).concat(args[++i].split(','));
				break;
			case '-h':
			case '--help':
				options.help = true;
				break;
		}
	}

	return options;
}

/**
 * Print help message
 */
function printHelp(): void {
	console.log(`
Tactica - TypeScript Language Service Plugin for Mnemonica

Usage: tactica [options]

Options:
  -w, --watch               Watch for file changes and regenerate types
  -p, --project             Path to tsconfig.json (default: ./tsconfig.json)
  -o, --output              Output directory for generated types (default: .tactica)
  -i, --include             Comma-separated list of file patterns to include
  -e, --exclude             Comma-separated list of file patterns to exclude
  -t, --topologica          Comma-separated list of topologica directories to scan
  -m, --module-augmentation Use module augmentation instead of global (legacy mode)
  -v, --verbose             Enable verbose logging
  -h, --help                Show this help message

Examples:
  tactica                              # Generate types with global augmentation (default)
  tactica --watch                      # Watch mode
  tactica --module-augmentation        # Use legacy module augmentation mode
  tactica --project ./src/tsconfig.json # Custom tsconfig path
  tactica --output ./types/mnemonica   # Custom output directory
  tactica --topologica ./src/ai-types  # Scan specific topologica directory
`);
}

/**
 * Find tsconfig.json
 */
function findTsConfig(projectPath?: string): string | undefined {
	if (projectPath) {
		if (fs.existsSync(projectPath)) {
			return projectPath;
		}
		throw new Error(`Project file not found: ${projectPath}`);
	}

	// Look for tsconfig.json in current directory and parent directories
	let currentDir = process.cwd();
	while (currentDir !== path.dirname(currentDir)) {
		const tsconfigPath = path.join(currentDir, 'tsconfig.json');
		if (fs.existsSync(tsconfigPath)) {
			return tsconfigPath;
		}
		currentDir = path.dirname(currentDir);
	}

	return undefined;
}

/**
 * Load TypeScript program from tsconfig
 */
function loadProgram(tsconfigPath: string): ts.Program {
	const configFile = ts.readConfigFile(tsconfigPath, ts.sys.readFile);

	if (configFile.error) {
		throw new Error(`Error reading tsconfig: ${ts.flattenDiagnosticMessageText(configFile.error.messageText, '\n')}`);
	}

	const parsedConfig = ts.parseJsonConfigFileContent(
		configFile.config,
		ts.sys,
		path.dirname(tsconfigPath)
	);

	if (parsedConfig.errors.length > 0) {
		const errorMessages = parsedConfig.errors.map(e =>
			ts.flattenDiagnosticMessageText(e.messageText, '\n')
		);
		throw new Error(`Error parsing tsconfig: ${errorMessages.join('\n')}`);
	}

	const program = ts.createProgram({
		rootNames: parsedConfig.fileNames,
		options: parsedConfig.options,
	});

	return program;
}

/**
 * Print type hierarchy as a tree
 */
function printTypeHierarchy(graph: TypeGraphImpl): void {
	console.log('\nType Hierarchy (Trie):');
	
	function printNode(node: TypeNode, prefix = '', isLast = true): void {
		const connector = isLast ? '└── ' : '├── ';
		// Use node.fullPath directly and convert dots to underscores
		const instanceName = node.fullPath.replace(/\./g, '_');
		console.log(`${prefix}${connector}${instanceName}`);
		
		const children = Array.from(node.children.values());
		const newPrefix = prefix + (isLast ? '    ' : '│   ');
		
		for (let i = 0; i < children.length; i++) {
			printNode(children[i], newPrefix, i === children.length - 1);
		}
	}
	
	const roots = Array.from(graph.roots.values());
	for (let i = 0; i < roots.length; i++) {
		printNode(roots[i], '', i === roots.length - 1);
	}
	console.log(); // Empty line at end
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
function scanTopologicaDirectories(projectDir: string, customDirs?: string[]): string[] {
	const dirs: string[] = [];

	// First, add custom directories if specified
	if (customDirs) {
		for (const dir of customDirs) {
			const dirPath = path.isAbsolute(dir) ? dir : path.join(projectDir, dir);
			if (fs.existsSync(dirPath) && fs.statSync(dirPath).isDirectory()) {
				dirs.push(dirPath);
			} else {
				console.warn(`Warning: Topologica directory not found: ${dirPath}`);
			}
		}
	}

	// Then auto-discover standard topologica directories
	const possibleDirs = ['ai-types', 'types', 'topologica-types'];

	for (const dirName of possibleDirs) {
		const dirPath = path.join(projectDir, dirName);
		if (fs.existsSync(dirPath) && fs.statSync(dirPath).isDirectory()) {
			// Avoid duplicates
			if (!dirs.includes(dirPath)) {
				dirs.push(dirPath);
			}
		}
	}

	// Also scan src/ subdirectory
	const srcPath = path.join(projectDir, 'src');
	if (fs.existsSync(srcPath) && fs.statSync(srcPath).isDirectory()) {
		for (const dirName of possibleDirs) {
			const dirPath = path.join(srcPath, dirName);
			if (fs.existsSync(dirPath) && fs.statSync(dirPath).isDirectory()) {
				// Avoid duplicates
				if (!dirs.includes(dirPath)) {
					dirs.push(dirPath);
				}
			}
		}
	}

	return dirs;
}

/**
 * Run type generation
 */
function run(options: CLIOptions): void {
	const tsconfigPath = findTsConfig(options.project);

	if (!tsconfigPath) {
		console.error('Error: Could not find tsconfig.json');
		process.exit(1);
	}

	if (options.verbose) {
		console.log(`Using tsconfig: ${tsconfigPath}`);
	}

	// Load TypeScript program
	const program = loadProgram(tsconfigPath);

	// Create analyzer
	const analyzer = new MnemonicaAnalyzer(program);

	// Determine output directory for exclusion
	const outputDir = options.outputDir || '.tactica';
	const outputDirPath = path.resolve(process.cwd(), outputDir);

	// Collect source files to analyze
	const sourceFiles: ts.SourceFile[] = [];
	for (const sourceFile of program.getSourceFiles()) {
		if (sourceFile.isDeclarationFile) {
			continue;
		}

		// Always exclude the output directory to avoid analyzing generated files
		if (sourceFile.fileName.startsWith(outputDirPath + path.sep)) {
			continue;
		}

		// Check exclude patterns
		if (options.exclude) {
			const shouldExclude = options.exclude.some(pattern =>
				sourceFile.fileName.includes(pattern.replace(/\*/g, ''))
			);
			if (shouldExclude) {
				continue;
			}
		}

		// Check include patterns
		if (options.include && options.include.length > 0) {
			const shouldInclude = options.include.some(pattern =>
				sourceFile.fileName.includes(pattern.replace(/\*/g, ''))
			);
			if (!shouldInclude) {
				continue;
			}
		}

		sourceFiles.push(sourceFile);
	}

	// First pass: collect all definitions
	for (const sourceFile of sourceFiles) {
		if (options.verbose) {
			console.log(`Analyzing (definitions): ${sourceFile.fileName}`);
		}

		try {
			analyzer.analyzeFile(sourceFile);
		} catch (err) {
			console.error(`Error analyzing ${sourceFile.fileName}:`, err);
			throw err;
		}
	}

	// Second pass: collect usages (now all definitions are known)
	for (const sourceFile of sourceFiles) {
		if (options.verbose) {
			console.log(`Analyzing (usages): ${sourceFile.fileName}`);
		}

		try {
			analyzer.analyzeFile(sourceFile);
		} catch (err) {
			console.error(`Error analyzing ${sourceFile.fileName}:`, err);
			throw err;
		}
	}

	// Generate types from mnemonica analysis
	const graph = analyzer.getGraph();

	// Scan for topologica directory structures
	const projectDir = path.dirname(tsconfigPath);
	const topologicaDirs = scanTopologicaDirectories(projectDir, options.topologicaDirs);

	if (topologicaDirs.length > 0 && options.verbose) {
		console.log(`Found topologica directories: ${topologicaDirs.join(', ')}`);
	}

	// Analyze topologica directories and merge into graph
	const topologicaAnalyzer = new TopologicaAnalyzer();
	const topologicaTypes = new Map<string, import('./types').TypeNode>();
	for (const dir of topologicaDirs) {
		const result = topologicaAnalyzer.analyzeDirectory(dir);
		if (result.types.size > 0) {
			mergeTopologicaTypes(graph, result.types);
			// Collect topologica types for definitions
			for (const [path, node] of result.types) {
				topologicaTypes.set(path, node);
			}
			if (options.verbose) {
				console.log(`Added ${result.types.size} types from ${dir}`);
			}
		}
		if (result.errors.length > 0 && options.verbose) {
			result.errors.forEach(err => console.warn(`[Topologica] ${err}`));
		}
	}
	const generator = new TypesGenerator(graph);

	// Check if module augmentation mode is requested (legacy)
	const useModuleAugmentation = options.globalAugmentation === false;

	// Generate types based on mode
	let generatedTypes: { content: string; types: string[] };
	let outputPath: string;

	const writer = new TypesWriter(options.outputDir);

	if (useModuleAugmentation) {
		// Legacy mode: generate global augmentation file (index.d.ts)
		generatedTypes = generator.generateGlobalAugmentation();
		outputPath = writer.writeGlobalAugmentation(generatedTypes);
	} else {
		// Default mode: generate types.ts for manual imports
		generatedTypes = generator.generateTypesFile();
		outputPath = writer.writeTypesFile(generatedTypes);

		// Generate registry.ts for type-safe lookupTyped<TypeRegistry>() function
		const registryTypes = generator.generateTypeRegistry();
		const registryPath = writer.writeTo('registry.ts', registryTypes.content);

		// Generate index.ts to export everything
		const indexContent = `// Generated by @mnemonica/tactica - DO NOT EDIT
// Export all generated types

export * from './types';
export * from './registry';
`;
		writer.writeTo('index.ts', indexContent);

		if (options.verbose) {
			console.log(`Generated registry.ts at: ${registryPath}`);
		}
	}

	// Generate definitions.json and usages.json for code navigation
	// Include both mnemonica and topologica definitions
	const definitions = new Map(analyzer.getDefinitions());
	const usages = new Map(analyzer.getUsages());
	
	// Add topologica types to definitions
	for (const [fullPath, typeNode] of topologicaTypes) {
		// Skip if already exists (prefer mnemonica's analysis)
		if (definitions.has(fullPath)) {
			continue;
		}
		
		const definition: import('./types').DefinitionInfo = {
			name: typeNode.name,
			location: `${typeNode.sourceFile}/index.ts:1:1`,
			kind: 'define',
			parent: typeNode.parent ? typeNode.parent.fullPath : null,
			strictChain: true,
			blockErrors: false
		};
		definitions.set(fullPath, definition);
	}
	
	const definitionsPath = writer.writeDefinitionsFile(definitions);
	const usagesPath = writer.writeUsagesFile(usages);

	if (options.verbose) {
		console.log(`Generated definitions.json at: ${definitionsPath}`);
		console.log(`Generated usages.json at: ${usagesPath}`);
	}

	if (options.verbose) {
		console.log(`Generated types at: ${outputPath}`);
		console.log(`Mode: ${useModuleAugmentation ? 'global augmentation (legacy)' : 'types file (default)'}`);
		console.log(`Found ${generatedTypes.types.length} types:`);
		printTypeHierarchy(graph);
	} else {
		console.log(`Generated ${generatedTypes.types.length} types at ${options.outputDir || '.tactica'}`);
		if (useModuleAugmentation) {
			console.log('Using global augmentation mode (legacy, use default mode for types.ts only)');
		}
	}
}

/**
 * Watch mode
 */
function watch(options: CLIOptions): void {
	console.log('Starting watch mode...');

	// Initial run
	run(options);

	// Set up file watching
	const chokidar = require('chokidar');
	const tsconfigPath = findTsConfig(options.project);

	if (!tsconfigPath) {
		console.error('Error: Could not find tsconfig.json');
		process.exit(1);
	}

	const projectDir = path.dirname(tsconfigPath);
	const watchPaths = options.include || ['**/*.ts'];
	const ignorePaths = options.exclude || ['**/*.d.ts', 'node_modules/**', '.tactica/**'];

	const watcher = chokidar.watch(watchPaths, {
		cwd: projectDir,
		ignored: ignorePaths,
		persistent: true,
	});

	watcher.on('change', (filePath: string) => {
		if (options.verbose) {
			console.log(`File changed: ${filePath}`);
		}
		run(options);
	});

	watcher.on('add', (filePath: string) => {
		if (options.verbose) {
			console.log(`File added: ${filePath}`);
		}
		run(options);
	});

	console.log('Watching for changes... (Press Ctrl+C to stop)');
}

/**
 * Main entry point
 */
function main(): void {
	const args = process.argv.slice(2);
	const options = parseArgs(args);

	if (options.help) {
		printHelp();
		process.exit(0);
	}

	try {
		if (options.watch) {
			watch(options);
		} else {
			run(options);
		}
	} catch (error) {
		console.error('Error:', error instanceof Error ? error.message : error);
		process.exit(1);
	}
}

// Run if executed directly
if (require.main === module) {
	main();
}

export { main, run, watch, parseArgs };
