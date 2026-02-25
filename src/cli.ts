#!/usr/bin/env node
'use strict';

import * as fs from 'fs';
import * as path from 'path';
import * as ts from 'typescript';
import { MnemonicaAnalyzer } from './analyzer';
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
			case '-v':
			case '--verbose':
				options.verbose = true;
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
  -w, --watch          Watch for file changes and regenerate types
  -p, --project        Path to tsconfig.json (default: ./tsconfig.json)
  -o, --output         Output directory for generated types (default: .mnemonica)
  -i, --include        Comma-separated list of file patterns to include
  -e, --exclude        Comma-separated list of file patterns to exclude
  -v, --verbose        Enable verbose logging
  -h, --help           Show this help message

Examples:
  tactica                              # Generate types once
  tactica --watch                      # Watch mode
  tactica --project ./src/tsconfig.json # Custom tsconfig path
  tactica --output ./types/mnemonica   # Custom output directory
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
		const instanceName = `${node.name}Instance`;
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
	const outputDir = options.outputDir || '.mnemonica';
	const outputDirPath = path.resolve(process.cwd(), outputDir);

	// Analyze all source files
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

		if (options.verbose) {
			console.log(`Analyzing: ${sourceFile.fileName}`);
		}

		try {
			analyzer.analyzeFile(sourceFile);
		} catch (err) {
			console.error(`Error analyzing ${sourceFile.fileName}:`, err);
			throw err;
		}
	}

	// Generate types
	const graph = analyzer.getGraph();
	const generator = new TypesGenerator(graph);

	// Generate both module augmentation (.d.ts) and complete interfaces (types.ts)
	const generatedDts = generator.generate();
	const generatedTs = generator.generateTypesFile();

	// Write types
	const writer = new TypesWriter(options.outputDir);
	const dtsPath = writer.write(generatedDts);
	const tsPath = writer.writeTypesFile(generatedTs);

	if (options.verbose) {
		console.log(`Generated types at: ${dtsPath}`);
		console.log(`Generated complete interfaces at: ${tsPath}`);
		console.log(`Found ${generatedDts.types.length} types:`);
		printTypeHierarchy(graph);
	} else {
		console.log(`Generated ${generatedDts.types.length} types at ${options.outputDir || '.mnemonica'}`);
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
	const ignorePaths = options.exclude || ['**/*.d.ts', 'node_modules/**', '.mnemonica/**'];

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
