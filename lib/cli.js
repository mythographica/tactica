#!/usr/bin/env node
'use strict';
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.main = main;
exports.run = run;
exports.watch = watch;
exports.parseArgs = parseArgs;
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const ts = __importStar(require("typescript"));
const analyzer_1 = require("./analyzer");
const topologica_analyzer_1 = require("./topologica-analyzer");
const generator_1 = require("./generator");
const writer_1 = require("./writer");
/**
 * Parse command line arguments
 */
function parseArgs(args) {
    const options = {};
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
            case '--esm':
                options.esm = true;
                break;
            case '--eds':
                options.eds = true;
                break;
            case '--no-eds':
                options.eds = false;
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
function printHelp() {
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
  --esm                     Add .js extensions to relative imports (NodeNext ESM)
  --eds                     Enable EDS (Execution Data Storage) tracking
  --no-eds                  Disable EDS tracking
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
function findTsConfig(projectPath) {
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
function loadProgram(tsconfigPath) {
    const configFile = ts.readConfigFile(tsconfigPath, ts.sys.readFile);
    if (configFile.error) {
        const errorText = ts.flattenDiagnosticMessageText(configFile.error.messageText, '\n');
        throw new Error(`Error reading tsconfig: ${errorText}`);
    }
    const parsedConfig = ts.parseJsonConfigFileContent(configFile.config, ts.sys, path.dirname(tsconfigPath));
    if (parsedConfig.errors.length > 0) {
        const errorMessages = parsedConfig.errors.map(e => ts.flattenDiagnosticMessageText(e.messageText, '\n'));
        throw new Error(`Error parsing tsconfig: ${errorMessages.join('\n')}`);
    }
    const program = ts.createProgram({
        rootNames: parsedConfig.fileNames,
        options: parsedConfig.options,
    });
    return program;
}
/**
 * Render type hierarchy as an ASCII tree string.
 */
function renderTypeHierarchy(graph) {
    const lines = ['Type Hierarchy (Trie):'];
    function renderNode(node, prefix = '', isLast = true) {
        const connector = isLast ? '└── ' : '├── ';
        // Use node.fullPath directly and convert dots to underscores
        const instanceName = node.fullPath.replace(/\./g, '_');
        lines.push(`${prefix}${connector}${instanceName}`);
        const children = Array.from(node.children.values());
        const newPrefix = prefix + (isLast ? '    ' : '│   ');
        for (let i = 0; i < children.length; i++) {
            renderNode(children[i], newPrefix, i === children.length - 1);
        }
    }
    const roots = Array.from(graph.roots.values());
    for (let i = 0; i < roots.length; i++) {
        renderNode(roots[i], '', i === roots.length - 1);
    }
    lines.push(''); // Empty line at end
    const result = lines.join('\n');
    return result;
}
/**
 * Print type hierarchy to the console.
 */
function printTypeHierarchy(graph) {
    const output = renderTypeHierarchy(graph);
    console.log(output);
}
/**
 * Check if @mnemonica/dive is present in package.json dependencies
 */
function hasDiveDependency(projectDir) {
    const packageJsonPath = path.join(projectDir, 'package.json');
    if (!fs.existsSync(packageJsonPath)) {
        return false;
    }
    try {
        const content = fs.readFileSync(packageJsonPath, 'utf-8');
        const pkg = JSON.parse(content);
        const deps = pkg.dependencies || {};
        const devDeps = pkg.devDependencies || {};
        const peerDeps = pkg.peerDependencies || {};
        return '@mnemonica/dive' in deps || '@mnemonica/dive' in devDeps || '@mnemonica/dive' in peerDeps;
    }
    catch {
        return false;
    }
}
/**
 * Scan for topologica directory structures
 */
function scanTopologicaDirectories(projectDir, customDirs) {
    const dirs = [];
    // First, add custom directories if specified
    if (customDirs) {
        for (const dir of customDirs) {
            const dirPath = path.isAbsolute(dir) ? dir : path.join(projectDir, dir);
            if (fs.existsSync(dirPath) && fs.statSync(dirPath).isDirectory()) {
                dirs.push(dirPath);
            }
            else {
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
function run(options) {
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
    const analyzer = new analyzer_1.MnemonicaAnalyzer(program);
    // Determine output directory for exclusion
    const outputDir = options.outputDir || '.tactica';
    const outputDirPath = path.resolve(process.cwd(), outputDir);
    // Collect source files to analyze
    const sourceFiles = [];
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
            const shouldExclude = options.exclude.some(pattern => sourceFile.fileName.includes(pattern.replace(/\*/g, '')));
            if (shouldExclude) {
                continue;
            }
        }
        // Check include patterns
        if (options.include && options.include.length > 0) {
            const shouldInclude = options.include.some(pattern => sourceFile.fileName.includes(pattern.replace(/\*/g, '')));
            if (!shouldInclude) {
                continue;
            }
        }
        sourceFiles.push(sourceFile);
    }
    // Scan for topologica directory structures FIRST
    const projectDir = path.dirname(tsconfigPath);
    const topologicaDirs = scanTopologicaDirectories(projectDir, options.topologicaDirs);
    if (topologicaDirs.length > 0 && options.verbose) {
        console.log(`Found topologica directories: ${topologicaDirs.join(', ')}`);
    }
    // Analyze topologica directories BEFORE usage collection
    const topologicaAnalyzer = new topologica_analyzer_1.TopologicaAnalyzer();
    const topologicaTypes = new Map();
    for (const dir of topologicaDirs) {
        const result = topologicaAnalyzer.analyzeDirectory(dir);
        if (result.types.size > 0) {
            // Collect topologica types for definitions and usage tracking
            for (const [typePath, node] of result.types) {
                topologicaTypes.set(typePath, node);
            }
            if (options.verbose) {
                console.log(`Added ${result.types.size} types from ${dir}`);
            }
        }
        if (result.errors.length > 0 && options.verbose) {
            result.errors.forEach(err => console.warn(`[Topologica] ${err}`));
        }
    }
    // Add topologica types to analyzer so they're available for usage detection
    // Process in order of path depth (parents first) to ensure proper hierarchy
    const sortedTypes = Array.from(topologicaTypes.entries()).sort((a, b) => {
        const depthA = (a[0].match(/\./g) || []).length;
        const depthB = (b[0].match(/\./g) || []).length;
        return depthA - depthB;
    });
    for (const [typePath, node] of sortedTypes) {
        analyzer.addTopologicaType(typePath, node);
    }
    // First pass: collect all definitions
    for (const sourceFile of sourceFiles) {
        if (options.verbose) {
            console.log(`Analyzing (definitions): ${sourceFile.fileName}`);
        }
        try {
            analyzer.analyzeFile(sourceFile);
        }
        catch (err) {
            console.error(`Error analyzing ${sourceFile.fileName}:`, err);
            throw err;
        }
    }
    // Second pass: collect usages (now all definitions are known, including topologica)
    analyzer.resetUsages();
    for (const sourceFile of sourceFiles) {
        if (options.verbose) {
            console.log(`Analyzing (usages): ${sourceFile.fileName}`);
        }
        try {
            analyzer.analyzeFile(sourceFile);
        }
        catch (err) {
            console.error(`Error analyzing ${sourceFile.fileName}:`, err);
            throw err;
        }
    }
    // Generate types from mnemonica analysis
    // Note: topologica types are already added to the analyzer's graph via addTopologicaType()
    const graph = analyzer.getGraph();
    const generator = new generator_1.TypesGenerator(graph, options.esm, options.outputDir);
    // Check if module augmentation mode is requested (legacy)
    const useModuleAugmentation = options.globalAugmentation === false;
    // Generate types based on mode
    let generatedTypes;
    let outputPath;
    const writer = new writer_1.TypesWriter(options.outputDir);
    if (useModuleAugmentation) {
        // Legacy mode: generate global augmentation file (index.d.ts)
        generatedTypes = generator.generateGlobalAugmentation();
        outputPath = writer.writeGlobalAugmentation(generatedTypes);
    }
    else {
        // Default mode: generate types.ts for manual imports
        generatedTypes = generator.generateTypesFile();
        outputPath = writer.writeTypesFile(generatedTypes);
        // Generate registry.ts for type-safe lookup() function
        const registryTypes = generator.generateTypeRegistry();
        const registryPath = writer.writeTo('registry.ts', registryTypes.content);
        // Generate index.ts to export everything
        const indexContent = `// Generated by @mnemonica/tactica - DO NOT EDIT
// Export all generated types

export * from './types${options.esm ? '.js' : ''}';
export * from './registry${options.esm ? '.js' : ''}';
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
        const definition = {
            name: typeNode.name,
            location: `${typeNode.sourceFile}:${typeNode.line}:${typeNode.column}`,
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
    // Determine EDS setting: explicit flag > auto-detect dive > default off
    let enableEDS = options.eds;
    if (enableEDS === undefined) {
        enableEDS = hasDiveDependency(projectDir);
    }
    if (enableEDS) {
        const eds = analyzer.getEDSUsages();
        const edsPath = writer.writeEDSFile(eds);
        if (options.verbose) {
            console.log(`Generated eds.json at: ${edsPath}`);
        }
    }
    // Always generate flow.json (native instance usage tracking)
    const flow = analyzer.getFlowUsages();
    const flowPath = writer.writeFlowFile(flow);
    if (options.verbose) {
        const flowCount = Array.from(flow.values()).reduce((sum, arr) => sum + arr.length, 0);
        console.log(`Generated flow.json at: ${flowPath} (${flowCount} flow entries)`);
    }
    // Generate hierarchy.json (structured) and hierarchy.txt (ASCII tree) for the Trie
    const hierarchyRoots = graph.toHierarchy();
    const hierarchyJsonPath = writer.writeHierarchyFile(hierarchyRoots);
    const hierarchyText = renderTypeHierarchy(graph);
    const hierarchyTxtPath = writer.writeTo('hierarchy.txt', hierarchyText);
    if (options.verbose) {
        console.log(`Generated hierarchy.json at: ${hierarchyJsonPath}`);
        console.log(`Generated hierarchy.txt at: ${hierarchyTxtPath}`);
    }
    if (options.verbose) {
        console.log(`Generated types at: ${outputPath}`);
        console.log(`Mode: ${useModuleAugmentation ? 'global augmentation (legacy)' : 'types file (default)'}`);
        console.log(`Found ${generatedTypes.types.length} types:`);
        printTypeHierarchy(graph);
    }
    else {
        console.log(`Generated ${generatedTypes.types.length} types at ${options.outputDir || '.tactica'}`);
        if (useModuleAugmentation) {
            console.log('Using global augmentation mode (legacy, use default mode for types.ts only)');
        }
    }
}
/**
 * Watch mode
 */
function watch(options) {
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
    watcher.on('change', (filePath) => {
        if (options.verbose) {
            console.log(`File changed: ${filePath}`);
        }
        run(options);
    });
    watcher.on('add', (filePath) => {
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
function main() {
    const args = process.argv.slice(2);
    const options = parseArgs(args);
    if (options.help) {
        printHelp();
        process.exit(0);
    }
    try {
        if (options.watch) {
            watch(options);
        }
        else {
            run(options);
        }
    }
    catch (error) {
        console.error('Error:', error instanceof Error ? error.message : error);
        process.exit(1);
    }
}
// Run if executed directly
if (require.main === module) {
    main();
}
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiY2xpLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL2NsaS50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiO0FBQ0EsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQStsQlosb0JBQUk7QUFBRSxrQkFBRztBQUFFLHNCQUFLO0FBQUUsOEJBQVM7QUE3bEI1Qix1Q0FBeUI7QUFDekIsMkNBQTZCO0FBQzdCLCtDQUFpQztBQUNqQyx5Q0FBK0M7QUFDL0MsK0RBQTJEO0FBQzNELDJDQUE2QztBQUM3QyxxQ0FBdUM7QUF3QnZDOztHQUVHO0FBQ0gsU0FBUyxTQUFTLENBQUUsSUFBYztJQUNqQyxNQUFNLE9BQU8sR0FBZSxFQUFFLENBQUM7SUFFL0IsS0FBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxNQUFNLEVBQUUsQ0FBQyxFQUFFLEVBQUUsQ0FBQztRQUN0QyxNQUFNLEdBQUcsR0FBRyxJQUFJLENBQUUsQ0FBQyxDQUFFLENBQUM7UUFFdEIsUUFBUSxHQUFHLEVBQUUsQ0FBQztZQUNkLEtBQUssSUFBSSxDQUFDO1lBQ1YsS0FBSyxTQUFTO2dCQUNiLE9BQU8sQ0FBQyxLQUFLLEdBQUcsSUFBSSxDQUFDO2dCQUNyQixNQUFNO1lBQ1AsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFdBQVc7Z0JBQ2YsT0FBTyxDQUFDLE9BQU8sR0FBRyxJQUFJLENBQUUsRUFBRSxDQUFDLENBQUUsQ0FBQztnQkFDOUIsTUFBTTtZQUNQLEtBQUssSUFBSSxDQUFDO1lBQ1YsS0FBSyxVQUFVO2dCQUNkLE9BQU8sQ0FBQyxTQUFTLEdBQUcsSUFBSSxDQUFFLEVBQUUsQ0FBQyxDQUFFLENBQUM7Z0JBQ2hDLE1BQU07WUFDUCxLQUFLLElBQUksQ0FBQztZQUNWLEtBQUssV0FBVztnQkFDZixPQUFPLENBQUMsT0FBTyxHQUFHLENBQUMsT0FBTyxDQUFDLE9BQU8sSUFBSSxFQUFFLENBQUMsQ0FB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c3IvYmluL2VudiBub2RlXG4ndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIGZzIGZyb20gJ2ZzJztcbmltcG9ydCAqIGFzIHBhdGggZnJvbSAncGF0aCc7XG5pbXBvcnQgKiBhcyB0cyBmcm9tICd0eXBlc2NyaXB0JztcbmltcG9ydCB7IE1uZW1vbmljYUFuYWx5emVyIH0gZnJvbSAnLi9hbmFseXplcic7XG5pbXBvcnQgeyBUb3BvbG9naWNhQW5hbHl6ZXIgfSBmcm9tICcuL3RvcG9sb2dpY2EtYW5hbHl6ZXInO1xuaW1wb3J0IHsgVHlwZXNHZW5lcmF0b3IgfSBmcm9tICcuL2dlbmVyYXRvcic7XG5pbXBvcnQgeyBUeXBlc1dyaXRlciB9IGZyb20gJy4vd3JpdGVyJztcbmltcG9ydCB7XG5cdFRhY3RpY2FDb25maWcsIFR5cGVOb2RlIFxufSBmcm9tICcuL3R5cGVzJztcbmltcG9ydCB7IFR5cGVHcmFwaEltcGwgfSBmcm9tICcuL2dyYXBoJztcblxuLyoqXG4gKiBDTEkgZW50cnkgcG9pbnQgZm9yIFRhY3RpY2FcbiAqXG4gKiBDYW4gYmUgdXNlZCBzdGFuZGFsb25lIHdpdGhvdXQgdGhlIExhbmd1YWdlIFNlcnZpY2UgUGx1Z2luXG4gKi9cblxuaW50ZXJmYWNlIENMSU9wdGlvbnMgZXh0ZW5kcyBUYWN0aWNhQ29uZmlnIHtcblx0d2F0Y2g/OiBib29sZWFuO1xuXHRwcm9qZWN0Pzogc3RyaW5nO1xuXHRoZWxwPzogYm9vbGVhbjtcblx0LyoqIEN1c3RvbSB0b3BvbG9naWNhIGRpcmVjdG9yaWVzIHRvIHNjYW4gKi9cblx0dG9wb2xvZ2ljYURpcnM/OiBzdHJpbmdbXTtcblx0LyoqIEFkZCAuanMgZXh0ZW5zaW9ucyB0byByZWxhdGl2ZSBpbXBvcnRzIGZvciBFU00gTm9kZU5leHQgcmVzb2x1dGlvbiAqL1xuXHRlc20/OiBib29sZWFuO1xuXHQvKiogRW5hYmxlIEVEUyAoRXhlY3V0aW9uIERhdGEgU3RvcmFnZSkgdHJhY2tpbmcgKi9cblx0ZWRzPzogYm9vbGVhbjtcbn1cblxuLyoqXG4gKiBQYXJzZSBjb21tYW5kIGxpbmUgYXJndW1lbnRzXG4gKi9cbmZ1bmN0aW9uIHBhcnNlQXJncyAoYXJnczogc3RyaW5nW10pOiBDTElPcHRpb25zIHtcblx0Y29uc3Qgb3B0aW9uczogQ0xJT3B0aW9ucyA9IHt9O1xuXG5cdGZvciAobGV0IGkgPSAwOyBpIDwgYXJncy5sZW5ndGg7IGkrKykge1xuXHRcdGNvbnN0IGFyZyA9IGFyZ3NbIGkgXTtcblxuXHRcdHN3aXRjaCAoYXJnKSB7XG5cdFx0Y2FzZSAnLXcnOlxuXHRcdGNhc2UgJy0td2F0Y2gnOlxuXHRcdFx0b3B0aW9ucy53YXRjaCA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctcCc6XG5cdFx0Y2FzZSAnLS1wcm9qZWN0Jzpcblx0XHRcdG9wdGlvbnMucHJvamVjdCA9IGFyZ3NbICsraSBdO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLW8nOlxuXHRcdGNhc2UgJy0tb3V0cHV0Jzpcblx0XHRcdG9wdGlvbnMub3V0cHV0RGlyID0gYXJnc1sgKytpIF07XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctaSc6XG5cdFx0Y2FzZSAnLS1pbmNsdWRlJzpcblx0XHRcdG9wdGlvbnMuaW5jbHVkZSA9IChvcHRpb25zLmluY2x1ZGUgfHwgW10pLmNvbmNhdChhcmdzWyArK2kgXS5zcGxpdCgnLCcpKTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1lJzpcblx0XHRjYXNlICctLWV4Y2x1ZGUnOlxuXHRcdFx0b3B0aW9ucy5leGNsdWRlID0gKG9wdGlvbnMuZXhjbHVkZSB8fCBbXSkuY29uY2F0KGFyZ3NbICsraSBdLnNwbGl0KCcsJykpO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLW0nOlxuXHRcdGNhc2UgJy0tbW9kdWxlLWF1Z21lbnRhdGlvbic6XG5cdFx0XHRvcHRpb25zLmdsb2JhbEF1Z21lbnRhdGlvbiA9IGZhbHNlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLXYnOlxuXHRcdGNhc2UgJy0tdmVyYm9zZSc6XG5cdFx0XHRvcHRpb25zLnZlcmJvc2UgPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLXQnOlxuXHRcdGNhc2UgJy0tdG9wb2xvZ2ljYSc6XG5cdFx0XHRvcHRpb25zLnRvcG9sb2dpY2FEaXJzID0gKG9wdGlvbnMudG9wb2xvZ2ljYURpcnMgfHwgW10pLmNvbmNhdChhcmdzWyArK2kgXS5zcGxpdCgnLCcpKTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tZXNtJzpcblx0XHRcdG9wdGlvbnMuZXNtID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tZWRzJzpcblx0XHRcdG9wdGlvbnMuZWRzID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tbm8tZWRzJzpcblx0XHRcdG9wdGlvbnMuZWRzID0gZmFsc2U7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctaCc6XG5cdFx0Y2FzZSAnLS1oZWxwJzpcblx0XHRcdG9wdGlvbnMuaGVscCA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHR9XG5cdH1cblxuXHRyZXR1cm4gb3B0aW9ucztcbn1cblxuLyoqXG4gKiBQcmludCBoZWxwIG1lc3NhZ2VcbiAqL1xuZnVuY3Rpb24gcHJpbnRIZWxwICgpOiB2b2lkIHtcblx0Y29uc29sZS5sb2coYFxuVGFjdGljYSAtIFR5cGVTY3JpcHQgTGFuZ3VhZ2UgU2VydmljZSBQbHVnaW4gZm9yIE1uZW1vbmljYVxuXG5Vc2FnZTogdGFjdGljYSBbb3B0aW9uc11cblxuT3B0aW9uczpcbiAgLXcsIC0td2F0Y2ggICAgICAgICAgICAgICBXYXRjaCBmb3IgZmlsZSBjaGFuZ2VzIGFuZCByZWdlbmVyYXRlIHR5cGVzXG4gIC1wLCAtLXByb2plY3QgICAgICAgICAgICAgUGF0aCB0byB0c2NvbmZpZy5qc29uIChkZWZhdWx0OiAuL3RzY29uZmlnLmpzb24pXG4gIC1vLCAtLW91dHB1dCAgICAgICAgICAgICAgT3V0cHV0IGRpcmVjdG9yeSBmb3IgZ2VuZXJhdGVkIHR5cGVzIChkZWZhdWx0OiAudGFjdGljYSlcbiAgLWksIC0taW5jbHVkZSAgICAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBmaWxlIHBhdHRlcm5zIHRvIGluY2x1ZGVcbiAgLWUsIC0tZXhjbHVkZSAgICAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBmaWxlIHBhdHRlcm5zIHRvIGV4Y2x1ZGVcbiAgLXQsIC0tdG9wb2xvZ2ljYSAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiB0b3BvbG9naWNhIGRpcmVjdG9yaWVzIHRvIHNjYW5cbiAgLW0sIC0tbW9kdWxlLWF1Z21lbnRhdGlvbiBVc2UgbW9kdWxlIGF1Z21lbnRhdGlvbiBpbnN0ZWFkIG9mIGdsb2JhbCAobGVnYWN5IG1vZGUpXG4gIC0tZXNtICAgICAgICAgICAgICAgICAgICAgQWRkIC5qcyBleHRlbnNpb25zIHRvIHJlbGF0aXZlIGltcG9ydHMgKE5vZGVOZXh0IEVTTSlcbiAgLS1lZHMgICAgICAgICAgICAgICAgICAgICBFbmFibGUgRURTIChFeGVjdXRpb24gRGF0YSBTdG9yYWdlKSB0cmFja2luZ1xuICAtLW5vLWVkcyAgICAgICAgICAgICAgICAgIERpc2FibGUgRURTIHRyYWNraW5nXG4gIC12LCAtLXZlcmJvc2UgICAgICAgICAgICAgRW5hYmxlIHZlcmJvc2UgbG9nZ2luZ1xuICAtaCwgLS1oZWxwICAgICAgICAgICAgICAgIFNob3cgdGhpcyBoZWxwIG1lc3NhZ2VcblxuRXhhbXBsZXM6XG4gIHRhY3RpY2EgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAjIEdlbmVyYXRlIHR5cGVzIHdpdGggZ2xvYmFsIGF1Z21lbnRhdGlvbiAoZGVmYXVsdClcbiAgdGFjdGljYSAtLXdhdGNoICAgICAgICAgICAgICAgICAgICAgICMgV2F0Y2ggbW9kZVxuICB0YWN0aWNhIC0tbW9kdWxlLWF1Z21lbnRhdGlvbiAgICAgICAgIyBVc2UgbGVnYWN5IG1vZHVsZSBhdWdtZW50YXRpb24gbW9kZVxuICB0YWN0aWNhIC0tcHJvamVjdCAuL3NyYy90c2NvbmZpZy5qc29uICMgQ3VzdG9tIHRzY29uZmlnIHBhdGhcbiAgdGFjdGljYSAtLW91dHB1dCAuL3R5cGVzL21uZW1vbmljYSAgICMgQ3VzdG9tIG91dHB1dCBkaXJlY3RvcnlcbiAgdGFjdGljYSAtLXRvcG9sb2dpY2EgLi9zcmMvYWktdHlwZXMgICMgU2NhbiBzcGVjaWZpYyB0b3BvbG9naWNhIGRpcmVjdG9yeVxuYCk7XG59XG5cbi8qKlxuICogRmluZCB0c2NvbmZpZy5qc29uXG4gKi9cbmZ1bmN0aW9uIGZpbmRUc0NvbmZpZyAocHJvamVjdFBhdGg/OiBzdHJpbmcpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRpZiAocHJvamVjdFBhdGgpIHtcblx0XHRpZiAoZnMuZXhpc3RzU3luYyhwcm9qZWN0UGF0aCkpIHtcblx0XHRcdHJldHVybiBwcm9qZWN0UGF0aDtcblx0XHR9XG5cdFx0dGhyb3cgbmV3IEVycm9yKGBQcm9qZWN0IGZpbGUgbm90IGZvdW5kOiAke3Byb2plY3RQYXRofWApO1xuXHR9XG5cblx0Ly8gTG9vayBmb3IgdHNjb25maWcuanNvbiBpbiBjdXJyZW50IGRpcmVjdG9yeSBhbmQgcGFyZW50IGRpcmVjdG9yaWVzXG5cdGxldCBjdXJyZW50RGlyID0gcHJvY2Vzcy5jd2QoKTtcblx0d2hpbGUgKGN1cnJlbnREaXIgIT09IHBhdGguZGlybmFtZShjdXJyZW50RGlyKSkge1xuXHRcdGNvbnN0IHRzY29uZmlnUGF0aCA9IHBhdGguam9pbihjdXJyZW50RGlyLCAndHNjb25maWcuanNvbicpO1xuXHRcdGlmIChmcy5leGlzdHNTeW5jKHRzY29uZmlnUGF0aCkpIHtcblx0XHRcdHJldHVybiB0c2NvbmZpZ1BhdGg7XG5cdFx0fVxuXHRcdGN1cnJlbnREaXIgPSBwYXRoLmRpcm5hbWUoY3VycmVudERpcik7XG5cdH1cblxuXHRyZXR1cm4gdW5kZWZpbmVkO1xufVxuXG4vKipcbiAqIExvYWQgVHlwZVNjcmlwdCBwcm9ncmFtIGZyb20gdHNjb25maWdcbiAqL1xuZnVuY3Rpb24gbG9hZFByb2dyYW0gKHRzY29uZmlnUGF0aDogc3RyaW5nKTogdHMuUHJvZ3JhbSB7XG5cdGNvbnN0IGNvbmZpZ0ZpbGUgPSB0cy5yZWFkQ29uZmlnRmlsZSh0c2NvbmZpZ1BhdGgsIHRzLnN5cy5yZWFkRmlsZSk7XG5cblx0aWYgKGNvbmZpZ0ZpbGUuZXJyb3IpIHtcblx0XHRjb25zdCBlcnJvclRleHQgPSB0cy5mbGF0dGVuRGlhZ25vc3RpY01lc3NhZ2VUZXh0KFxuXHRcdFx0Y29uZmlnRmlsZS5lcnJvci5tZXNzYWdlVGV4dCxcblx0XHRcdCdcXG4nXG5cdFx0KTtcblx0XHR0aHJvdyBuZXcgRXJyb3IoYEVycm9yIHJlYWRpbmcgdHNjb25maWc6ICR7ZXJyb3JUZXh0fWApO1xuXHR9XG5cblx0Y29uc3QgcGFyc2VkQ29uZmlnID0gdHMucGFyc2VKc29uQ29uZmlnRmlsZUNvbnRlbnQoXG5cdFx0Y29uZmlnRmlsZS5jb25maWcsXG5cdFx0dHMuc3lzLFxuXHRcdHBhdGguZGlybmFtZSh0c2NvbmZpZ1BhdGgpXG5cdCk7XG5cblx0aWYgKHBhcnNlZENvbmZpZy5lcnJvcnMubGVuZ3RoID4gMCkge1xuXHRcdGNvbnN0IGVycm9yTWVzc2FnZXMgPSBwYXJzZWRDb25maWcuZXJyb3JzLm1hcChlID0+XG5cdFx0XHR0cy5mbGF0dGVuRGlhZ25vc3RpY01lc3NhZ2VUZXh0KGUubWVzc2FnZVRleHQsICdcXG4nKSk7XG5cdFx0dGhyb3cgbmV3IEVycm9yKGBFcnJvciBwYXJzaW5nIHRzY29uZmlnOiAke2Vycm9yTWVzc2FnZXMuam9pbignXFxuJyl9YCk7XG5cdH1cblxuXHRjb25zdCBwcm9ncmFtID0gdHMuY3JlYXRlUHJvZ3JhbSh7XG5cdFx0cm9vdE5hbWVzIDogcGFyc2VkQ29uZmlnLmZpbGVOYW1lcyxcblx0XHRvcHRpb25zICAgOiBwYXJzZWRDb25maWcub3B0aW9ucyxcblx0fSk7XG5cblx0cmV0dXJuIHByb2dyYW07XG59XG5cbi8qKlxuICogUmVuZGVyIHR5cGUgaGllcmFyY2h5IGFzIGFuIEFTQ0lJIHRyZWUgc3RyaW5nLlxuICovXG5mdW5jdGlvbiByZW5kZXJUeXBlSGllcmFyY2h5IChncmFwaDogVHlwZUdyYXBoSW1wbCk6IHN0cmluZyB7XG5cdGNvbnN0IGxpbmVzOiBzdHJpbmdbXSA9IFsgJ1R5cGUgSGllcmFyY2h5IChUcmllKTonIF07XG5cblx0ZnVuY3Rpb24gcmVuZGVyTm9kZSAobm9kZTogVHlwZU5vZGUsIHByZWZpeCA9ICcnLCBpc0xhc3QgPSB0cnVlKTogdm9pZCB7XG5cdFx0Y29uc3QgY29ubmVjdG9yID0gaXNMYXN0ID8gJ+KUlOKUgOKUgCAnIDogJ+KUnOKUgOKUgCAnO1xuXHRcdC8vIFVzZSBub2RlLmZ1bGxQYXRoIGRpcmVjdGx5IGFuZCBjb252ZXJ0IGRvdHMgdG8gdW5kZXJzY29yZXNcblx0XHRjb25zdCBpbnN0YW5jZU5hbWUgPSBub2RlLmZ1bGxQYXRoLnJlcGxhY2UoL1xcLi9nLCAnXycpO1xuXHRcdGxpbmVzLnB1c2goYCR7cHJlZml4fSR7Y29ubmVjdG9yfSR7aW5zdGFuY2VOYW1lfWApO1xuXG5cdFx0Y29uc3QgY2hpbGRyZW4gPSBBcnJheS5mcm9tKG5vZGUuY2hpbGRyZW4udmFsdWVzKCkpO1xuXHRcdGNvbnN0IG5ld1ByZWZpeCA9IHByZWZpeCArIChpc0xhc3QgPyAnICAgICcgOiAn4pSCICAgJyk7XG5cblx0XHRmb3IgKGxldCBpID0gMDsgaSA8IGNoaWxkcmVuLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRyZW5kZXJOb2RlKGNoaWxkcmVuWyBpIF0sIG5ld1ByZWZpeCwgaSA9PT0gY2hpbGRyZW4ubGVuZ3RoIC0gMSk7XG5cdFx0fVxuXHR9XG5cblx0Y29uc3Qgcm9vdHMgPSBBcnJheS5mcm9tKGdyYXBoLnJvb3RzLnZhbHVlcygpKTtcblx0Zm9yIChsZXQgaSA9IDA7IGkgPCByb290cy5sZW5ndGg7IGkrKykge1xuXHRcdHJlbmRlck5vZGUocm9vdHNbIGkgXSwgJycsIGkgPT09IHJvb3RzLmxlbmd0aCAtIDEpO1xuXHR9XG5cdGxpbmVzLnB1c2goJycpOyAvLyBFbXB0eSBsaW5lIGF0IGVuZFxuXG5cdGNvbnN0IHJlc3VsdCA9IGxpbmVzLmpvaW4oJ1xcbicpO1xuXHRyZXR1cm4gcmVzdWx0O1xufVxuXG4vKipcbiAqIFByaW50IHR5cGUgaGllcmFyY2h5IHRvIHRoZSBjb25zb2xlLlxuICovXG5mdW5jdGlvbiBwcmludFR5cGVIaWVyYXJjaHkgKGdyYXBoOiBUeXBlR3JhcGhJbXBsKTogdm9pZCB7XG5cdGNvbnN0IG91dHB1dCA9IHJlbmRlclR5cGVIaWVyYXJjaHkoZ3JhcGgpO1xuXHRjb25zb2xlLmxvZyhvdXRwdXQpO1xufVxuXG4vKipcbiAqIENoZWNrIGlmIEBtbmVtb25pY2EvZGl2ZSBpcyBwcmVzZW50IGluIHBhY2thZ2UuanNvbiBkZXBlbmRlbmNpZXNcbiAqL1xuZnVuY3Rpb24gaGFzRGl2ZURlcGVuZGVuY3kgKHByb2plY3REaXI6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRjb25zdCBwYWNrYWdlSnNvblBhdGggPSBwYXRoLmpvaW4ocHJvamVjdERpciwgJ3BhY2thZ2UuanNvbicpO1xuXHRpZiAoIWZzLmV4aXN0c1N5bmMocGFja2FnZUpzb25QYXRoKSkge1xuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXHR0cnkge1xuXHRcdGNvbnN0IGNvbnRlbnQgPSBmcy5yZWFkRmlsZVN5bmMocGFja2FnZUpzb25QYXRoLCAndXRmLTgnKTtcblx0XHRjb25zdCBwa2cgPSBKU09OLnBhcnNlKGNvbnRlbnQpO1xuXHRcdGNvbnN0IGRlcHMgPSBwa2cuZGVwZW5kZW5jaWVzIHx8IHt9O1xuXHRcdGNvbnN0IGRldkRlcHMgPSBwa2cuZGV2RGVwZW5kZW5jaWVzIHx8IHt9O1xuXHRcdGNvbnN0IHBlZXJEZXBzID0gcGtnLnBlZXJEZXBlbmRlbmNpZXMgfHwge307XG5cdFx0cmV0dXJuICdAbW5lbW9uaWNhL2RpdmUnIGluIGRlcHMgfHwgJ0BtbmVtb25pY2EvZGl2ZScgaW4gZGV2RGVwcyB8fCAnQG1uZW1vbmljYS9kaXZlJyBpbiBwZWVyRGVwcztcblx0fSBjYXRjaCB7XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG59XG5cbi8qKlxuICogU2NhbiBmb3IgdG9wb2xvZ2ljYSBkaXJlY3Rvcnkgc3RydWN0dXJlc1xuICovXG5mdW5jdGlvbiBzY2FuVG9wb2xvZ2ljYURpcmVjdG9yaWVzIChwcm9qZWN0RGlyOiBzdHJpbmcsIGN1c3RvbURpcnM/OiBzdHJpbmdbXSk6IHN0cmluZ1tdIHtcblx0Y29uc3QgZGlyczogc3RyaW5nW10gPSBbXTtcblxuXHQvLyBGaXJzdCwgYWRkIGN1c3RvbSBkaXJlY3RvcmllcyBpZiBzcGVjaWZpZWRcblx0aWYgKGN1c3RvbURpcnMpIHtcblx0XHRmb3IgKGNvbnN0IGRpciBvZiBjdXN0b21EaXJzKSB7XG5cdFx0XHRjb25zdCBkaXJQYXRoID0gcGF0aC5pc0Fic29sdXRlKGRpcikgPyBkaXIgOiBwYXRoLmpvaW4ocHJvamVjdERpciwgZGlyKTtcblx0XHRcdGlmIChmcy5leGlzdHNTeW5jKGRpclBhdGgpICYmIGZzLnN0YXRTeW5jKGRpclBhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRcdFx0ZGlycy5wdXNoKGRpclBhdGgpO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc29sZS53YXJuKGBXYXJuaW5nOiBUb3BvbG9naWNhIGRpcmVjdG9yeSBub3QgZm91bmQ6ICR7ZGlyUGF0aH1gKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvLyBUaGVuIGF1dG8tZGlzY292ZXIgc3RhbmRhcmQgdG9wb2xvZ2ljYSBkaXJlY3Rvcmllc1xuXHRjb25zdCBwb3NzaWJsZURpcnMgPSBbICdhaS10eXBlcycsICd0eXBlcycsICd0b3BvbG9naWNhLXR5cGVzJyBdO1xuXG5cdGZvciAoY29uc3QgZGlyTmFtZSBvZiBwb3NzaWJsZURpcnMpIHtcblx0XHRjb25zdCBkaXJQYXRoID0gcGF0aC5qb2luKHByb2plY3REaXIsIGRpck5hbWUpO1xuXHRcdGlmIChmcy5leGlzdHNTeW5jKGRpclBhdGgpICYmIGZzLnN0YXRTeW5jKGRpclBhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRcdC8vIEF2b2lkIGR1cGxpY2F0ZXNcblx0XHRcdGlmICghZGlycy5pbmNsdWRlcyhkaXJQYXRoKSkge1xuXHRcdFx0XHRkaXJzLnB1c2goZGlyUGF0aCk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0Ly8gQWxzbyBzY2FuIHNyYy8gc3ViZGlyZWN0b3J5XG5cdGNvbnN0IHNyY1BhdGggPSBwYXRoLmpvaW4ocHJvamVjdERpciwgJ3NyYycpO1xuXHRpZiAoZnMuZXhpc3RzU3luYyhzcmNQYXRoKSAmJiBmcy5zdGF0U3luYyhzcmNQYXRoKS5pc0RpcmVjdG9yeSgpKSB7XG5cdFx0Zm9yIChjb25zdCBkaXJOYW1lIG9mIHBvc3NpYmxlRGlycykge1xuXHRcdFx0Y29uc3QgZGlyUGF0aCA9IHBhdGguam9pbihzcmNQYXRoLCBkaXJOYW1lKTtcblx0XHRcdGlmIChmcy5leGlzdHNTeW5jKGRpclBhdGgpICYmIGZzLnN0YXRTeW5jKGRpclBhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRcdFx0Ly8gQXZvaWQgZHVwbGljYXRlc1xuXHRcdFx0XHRpZiAoIWRpcnMuaW5jbHVkZXMoZGlyUGF0aCkpIHtcblx0XHRcdFx0XHRkaXJzLnB1c2goZGlyUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHRyZXR1cm4gZGlycztcbn1cblxuLyoqXG4gKiBSdW4gdHlwZSBnZW5lcmF0aW9uXG4gKi9cbmZ1bmN0aW9uIHJ1biAob3B0aW9uczogQ0xJT3B0aW9ucyk6IHZvaWQge1xuXHRjb25zdCB0c2NvbmZpZ1BhdGggPSBmaW5kVHNDb25maWcob3B0aW9ucy5wcm9qZWN0KTtcblxuXHRpZiAoIXRzY29uZmlnUGF0aCkge1xuXHRcdGNvbnNvbGUuZXJyb3IoJ0Vycm9yOiBDb3VsZCBub3QgZmluZCB0c2NvbmZpZy5qc29uJyk7XG5cdFx0cHJvY2Vzcy5leGl0KDEpO1xuXHR9XG5cblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBVc2luZyB0c2NvbmZpZzogJHt0c2NvbmZpZ1BhdGh9YCk7XG5cdH1cblxuXHQvLyBMb2FkIFR5cGVTY3JpcHQgcHJvZ3JhbVxuXHRjb25zdCBwcm9ncmFtID0gbG9hZFByb2dyYW0odHNjb25maWdQYXRoKTtcblxuXHQvLyBDcmVhdGUgYW5hbHl6ZXJcblx0Y29uc3QgYW5hbHl6ZXIgPSBuZXcgTW5lbW9uaWNhQW5hbHl6ZXIocHJvZ3JhbSk7XG5cblx0Ly8gRGV0ZXJtaW5lIG91dHB1dCBkaXJlY3RvcnkgZm9yIGV4Y2x1c2lvblxuXHRjb25zdCBvdXRwdXREaXIgPSBvcHRpb25zLm91dHB1dERpciB8fCAnLnRhY3RpY2EnO1xuXHRjb25zdCBvdXRwdXREaXJQYXRoID0gcGF0aC5yZXNvbHZlKHByb2Nlc3MuY3dkKCksIG91dHB1dERpcik7XG5cblx0Ly8gQ29sbGVjdCBzb3VyY2UgZmlsZXMgdG8gYW5hbHl6ZVxuXHRjb25zdCBzb3VyY2VGaWxlczogdHMuU291cmNlRmlsZVtdID0gW107XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBwcm9ncmFtLmdldFNvdXJjZUZpbGVzKCkpIHtcblx0XHRpZiAoc291cmNlRmlsZS5pc0RlY2xhcmF0aW9uRmlsZSkge1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXG5cdFx0Ly8gQWx3YXlzIGV4Y2x1ZGUgdGhlIG91dHB1dCBkaXJlY3RvcnkgdG8gYXZvaWQgYW5hbHl6aW5nIGdlbmVyYXRlZCBmaWxlc1xuXHRcdGlmIChzb3VyY2VGaWxlLmZpbGVOYW1lLnN0YXJ0c1dpdGgob3V0cHV0RGlyUGF0aCArIHBhdGguc2VwKSkge1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZXhjbHVkZSBwYXR0ZXJuc1xuXHRcdGlmIChvcHRpb25zLmV4Y2x1ZGUpIHtcblx0XHRcdGNvbnN0IHNob3VsZEV4Y2x1ZGUgPSBvcHRpb25zLmV4Y2x1ZGUuc29tZShwYXR0ZXJuID0+XG5cdFx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUuaW5jbHVkZXMocGF0dGVybi5yZXBsYWNlKC9cXCovZywgJycpKSk7XG5cdFx0XHRpZiAoc2hvdWxkRXhjbHVkZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBDaGVjayBpbmNsdWRlIHBhdHRlcm5zXG5cdFx0aWYgKG9wdGlvbnMuaW5jbHVkZSAmJiBvcHRpb25zLmluY2x1ZGUubGVuZ3RoID4gMCkge1xuXHRcdFx0Y29uc3Qgc2hvdWxkSW5jbHVkZSA9IG9wdGlvbnMuaW5jbHVkZS5zb21lKHBhdHRlcm4gPT5cblx0XHRcdFx0c291cmNlRmlsZS5maWxlTmFtZS5pbmNsdWRlcyhwYXR0ZXJuLnJlcGxhY2UoL1xcKi9nLCAnJykpKTtcblx0XHRcdGlmICghc2hvdWxkSW5jbHVkZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRzb3VyY2VGaWxlcy5wdXNoKHNvdXJjZUZpbGUpO1xuXHR9XG5cblx0Ly8gU2NhbiBmb3IgdG9wb2xvZ2ljYSBkaXJlY3Rvcnkgc3RydWN0dXJlcyBGSVJTVFxuXHRjb25zdCBwcm9qZWN0RGlyID0gcGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aCk7XG5cdGNvbnN0IHRvcG9sb2dpY2FEaXJzID0gc2NhblRvcG9sb2dpY2FEaXJlY3Rvcmllcyhwcm9qZWN0RGlyLCBvcHRpb25zLnRvcG9sb2dpY2FEaXJzKTtcblxuXHRpZiAodG9wb2xvZ2ljYURpcnMubGVuZ3RoID4gMCAmJiBvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgRm91bmQgdG9wb2xvZ2ljYSBkaXJlY3RvcmllczogJHt0b3BvbG9naWNhRGlycy5qb2luKCcsICcpfWApO1xuXHR9XG5cblx0Ly8gQW5hbHl6ZSB0b3BvbG9naWNhIGRpcmVjdG9yaWVzIEJFRk9SRSB1c2FnZSBjb2xsZWN0aW9uXG5cdGNvbnN0IHRvcG9sb2dpY2FBbmFseXplciA9IG5ldyBUb3BvbG9naWNhQW5hbHl6ZXIoKTtcblx0Y29uc3QgdG9wb2xvZ2ljYVR5cGVzID0gbmV3IE1hcDxzdHJpbmcsIGltcG9ydCgnLi90eXBlcycpLlR5cGVOb2RlPigpO1xuXHRmb3IgKGNvbnN0IGRpciBvZiB0b3BvbG9naWNhRGlycykge1xuXHRcdGNvbnN0IHJlc3VsdCA9IHRvcG9sb2dpY2FBbmFseXplci5hbmFseXplRGlyZWN0b3J5KGRpcik7XG5cdFx0aWYgKHJlc3VsdC50eXBlcy5zaXplID4gMCkge1xuXHRcdFx0Ly8gQ29sbGVjdCB0b3BvbG9naWNhIHR5cGVzIGZvciBkZWZpbml0aW9ucyBhbmQgdXNhZ2UgdHJhY2tpbmdcblx0XHRcdGZvciAoY29uc3QgWyB0eXBlUGF0aCwgbm9kZSBdIG9mIHJlc3VsdC50eXBlcykge1xuXHRcdFx0XHR0b3BvbG9naWNhVHlwZXMuc2V0KHR5cGVQYXRoLCBub2RlKTtcblx0XHRcdH1cblx0XHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdFx0Y29uc29sZS5sb2coYEFkZGVkICR7cmVzdWx0LnR5cGVzLnNpemV9IHR5cGVzIGZyb20gJHtkaXJ9YCk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGlmIChyZXN1bHQuZXJyb3JzLmxlbmd0aCA+IDAgJiYgb3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRyZXN1bHQuZXJyb3JzLmZvckVhY2goZXJyID0+IGNvbnNvbGUud2FybihgW1RvcG9sb2dpY2FdICR7ZXJyfWApKTtcblx0XHR9XG5cdH1cblxuXHQvLyBBZGQgdG9wb2xvZ2ljYSB0eXBlcyB0byBhbmFseXplciBzbyB0aGV5J3JlIGF2YWlsYWJsZSBmb3IgdXNhZ2UgZGV0ZWN0aW9uXG5cdC8vIFByb2Nlc3MgaW4gb3JkZXIgb2YgcGF0aCBkZXB0aCAocGFyZW50cyBmaXJzdCkgdG8gZW5zdXJlIHByb3BlciBoaWVyYXJjaHlcblx0Y29uc3Qgc29ydGVkVHlwZXMgPSBBcnJheS5mcm9tKHRvcG9sb2dpY2FUeXBlcy5lbnRyaWVzKCkpLnNvcnQoKGEsIGIpID0+IHtcblx0XHRjb25zdCBkZXB0aEEgPSAoYVsgMCBdLm1hdGNoKC9cXC4vZykgfHwgW10pLmxlbmd0aDtcblx0XHRjb25zdCBkZXB0aEIgPSAoYlsgMCBdLm1hdGNoKC9cXC4vZykgfHwgW10pLmxlbmd0aDtcblx0XHRyZXR1cm4gZGVwdGhBIC0gZGVwdGhCO1xuXHR9KTtcblx0Zm9yIChjb25zdCBbIHR5cGVQYXRoLCBub2RlIF0gb2Ygc29ydGVkVHlwZXMpIHtcblx0XHRhbmFseXplci5hZGRUb3BvbG9naWNhVHlwZSh0eXBlUGF0aCwgbm9kZSk7XG5cdH1cblxuXHQvLyBGaXJzdCBwYXNzOiBjb2xsZWN0IGFsbCBkZWZpbml0aW9uc1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2Ygc291cmNlRmlsZXMpIHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgQW5hbHl6aW5nIChkZWZpbml0aW9ucyk6ICR7c291cmNlRmlsZS5maWxlTmFtZX1gKTtcblx0XHR9XG5cblx0XHR0cnkge1xuXHRcdFx0YW5hbHl6ZXIuYW5hbHl6ZUZpbGUoc291cmNlRmlsZSk7XG5cdFx0fSBjYXRjaCAoZXJyKSB7XG5cdFx0XHRjb25zb2xlLmVycm9yKGBFcnJvciBhbmFseXppbmcgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfTpgLCBlcnIpO1xuXHRcdFx0dGhyb3cgZXJyO1xuXHRcdH1cblx0fVxuXG5cdC8vIFNlY29uZCBwYXNzOiBjb2xsZWN0IHVzYWdlcyAobm93IGFsbCBkZWZpbml0aW9ucyBhcmUga25vd24sIGluY2x1ZGluZyB0b3BvbG9naWNhKVxuXHRhbmFseXplci5yZXNldFVzYWdlcygpO1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2Ygc291cmNlRmlsZXMpIHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgQW5hbHl6aW5nICh1c2FnZXMpOiAke3NvdXJjZUZpbGUuZmlsZU5hbWV9YCk7XG5cdFx0fVxuXG5cdFx0dHJ5IHtcblx0XHRcdGFuYWx5emVyLmFuYWx5emVGaWxlKHNvdXJjZUZpbGUpO1xuXHRcdH0gY2F0Y2ggKGVycikge1xuXHRcdFx0Y29uc29sZS5lcnJvcihgRXJyb3IgYW5hbHl6aW5nICR7c291cmNlRmlsZS5maWxlTmFtZX06YCwgZXJyKTtcblx0XHRcdHRocm93IGVycjtcblx0XHR9XG5cdH1cblxuXHQvLyBHZW5lcmF0ZSB0eXBlcyBmcm9tIG1uZW1vbmljYSBhbmFseXNpc1xuXHQvLyBOb3RlOiB0b3BvbG9naWNhIHR5cGVzIGFyZSBhbHJlYWR5IGFkZGVkIHRvIHRoZSBhbmFseXplcidzIGdyYXBoIHZpYSBhZGRUb3BvbG9naWNhVHlwZSgpXG5cdGNvbnN0IGdyYXBoID0gYW5hbHl6ZXIuZ2V0R3JhcGgoKTtcblx0Y29uc3QgZ2VuZXJhdG9yID0gbmV3IFR5cGVzR2VuZXJhdG9yKGdyYXBoLCBvcHRpb25zLmVzbSwgb3B0aW9ucy5vdXRwdXREaXIpO1xuXG5cdC8vIENoZWNrIGlmIG1vZHVsZSBhdWdtZW50YXRpb24gbW9kZSBpcyByZXF1ZXN0ZWQgKGxlZ2FjeSlcblx0Y29uc3QgdXNlTW9kdWxlQXVnbWVudGF0aW9uID0gb3B0aW9ucy5nbG9iYWxBdWdtZW50YXRpb24gPT09IGZhbHNlO1xuXG5cdC8vIEdlbmVyYXRlIHR5cGVzIGJhc2VkIG9uIG1vZGVcblx0bGV0IGdlbmVyYXRlZFR5cGVzOiB7IGNvbnRlbnQ6IHN0cmluZzsgdHlwZXM6IHN0cmluZ1tdIH07XG5cdGxldCBvdXRwdXRQYXRoOiBzdHJpbmc7XG5cblx0Y29uc3Qgd3JpdGVyID0gbmV3IFR5cGVzV3JpdGVyKG9wdGlvbnMub3V0cHV0RGlyKTtcblxuXHRpZiAodXNlTW9kdWxlQXVnbWVudGF0aW9uKSB7XG5cdFx0Ly8gTGVnYWN5IG1vZGU6IGdlbmVyYXRlIGdsb2JhbCBhdWdtZW50YXRpb24gZmlsZSAoaW5kZXguZC50cylcblx0XHRnZW5lcmF0ZWRUeXBlcyA9IGdlbmVyYXRvci5nZW5lcmF0ZUdsb2JhbEF1Z21lbnRhdGlvbigpO1xuXHRcdG91dHB1dFBhdGggPSB3cml0ZXIud3JpdGVHbG9iYWxBdWdtZW50YXRpb24oZ2VuZXJhdGVkVHlwZXMpO1xuXHR9IGVsc2Uge1xuXHRcdC8vIERlZmF1bHQgbW9kZTogZ2VuZXJhdGUgdHlwZXMudHMgZm9yIG1hbnVhbCBpbXBvcnRzXG5cdFx0Z2VuZXJhdGVkVHlwZXMgPSBnZW5lcmF0b3IuZ2VuZXJhdGVUeXBlc0ZpbGUoKTtcblx0XHRvdXRwdXRQYXRoID0gd3JpdGVyLndyaXRlVHlwZXNGaWxlKGdlbmVyYXRlZFR5cGVzKTtcblxuXHRcdC8vIEdlbmVyYXRlIHJlZ2lzdHJ5LnRzIGZvciB0eXBlLXNhZmUgbG9va3VwKCkgZnVuY3Rpb25cblx0XHRjb25zdCByZWdpc3RyeVR5cGVzID0gZ2VuZXJhdG9yLmdlbmVyYXRlVHlwZVJlZ2lzdHJ5KCk7XG5cdFx0Y29uc3QgcmVnaXN0cnlQYXRoID0gd3JpdGVyLndyaXRlVG8oJ3JlZ2lzdHJ5LnRzJywgcmVnaXN0cnlUeXBlcy5jb250ZW50KTtcblxuXHRcdC8vIEdlbmVyYXRlIGluZGV4LnRzIHRvIGV4cG9ydCBldmVyeXRoaW5nXG5cdFx0Y29uc3QgaW5kZXhDb250ZW50ID0gYC8vIEdlbmVyYXRlZCBieSBAbW5lbW9uaWNhL3RhY3RpY2EgLSBETyBOT1QgRURJVFxuLy8gRXhwb3J0IGFsbCBnZW5lcmF0ZWQgdHlwZXNcblxuZXhwb3J0ICogZnJvbSAnLi90eXBlcyR7b3B0aW9ucy5lc20gPyAnLmpzJyA6ICcnfSc7XG5leHBvcnQgKiBmcm9tICcuL3JlZ2lzdHJ5JHtvcHRpb25zLmVzbSA/ICcuanMnIDogJyd9JztcbmA7XG5cdFx0d3JpdGVyLndyaXRlVG8oJ2luZGV4LnRzJywgaW5kZXhDb250ZW50KTtcblxuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgcmVnaXN0cnkudHMgYXQ6ICR7cmVnaXN0cnlQYXRofWApO1xuXHRcdH1cblx0fVxuXG5cdC8vIEdlbmVyYXRlIGRlZmluaXRpb25zLmpzb24gYW5kIHVzYWdlcy5qc29uIGZvciBjb2RlIG5hdmlnYXRpb25cblx0Ly8gSW5jbHVkZSBib3RoIG1uZW1vbmljYSBhbmQgdG9wb2xvZ2ljYSBkZWZpbml0aW9uc1xuXHRjb25zdCBkZWZpbml0aW9ucyA9IG5ldyBNYXAoYW5hbHl6ZXIuZ2V0RGVmaW5pdGlvbnMoKSk7XG5cdGNvbnN0IHVzYWdlcyA9IG5ldyBNYXAoYW5hbHl6ZXIuZ2V0VXNhZ2VzKCkpO1xuXHRcblx0Ly8gQWRkIHRvcG9sb2dpY2EgdHlwZXMgdG8gZGVmaW5pdGlvbnNcblx0Zm9yIChjb25zdCBbIGZ1bGxQYXRoLCB0eXBlTm9kZSBdIG9mIHRvcG9sb2dpY2FUeXBlcykge1xuXHRcdC8vIFNraXAgaWYgYWxyZWFkeSBleGlzdHMgKHByZWZlciBtbmVtb25pY2EncyBhbmFseXNpcylcblx0XHRpZiAoZGVmaW5pdGlvbnMuaGFzKGZ1bGxQYXRoKSkge1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXHRcdFxuXHRcdGNvbnN0IGRlZmluaXRpb246IGltcG9ydCgnLi90eXBlcycpLkRlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTm9kZS5uYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHt0eXBlTm9kZS5zb3VyY2VGaWxlfToke3R5cGVOb2RlLmxpbmV9OiR7dHlwZU5vZGUuY29sdW1ufWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiB0eXBlTm9kZS5wYXJlbnQgPyB0eXBlTm9kZS5wYXJlbnQuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBmYWxzZVxuXHRcdH07XG5cdFx0ZGVmaW5pdGlvbnMuc2V0KGZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0fVxuXHRcblx0Y29uc3QgZGVmaW5pdGlvbnNQYXRoID0gd3JpdGVyLndyaXRlRGVmaW5pdGlvbnNGaWxlKGRlZmluaXRpb25zKTtcblx0Y29uc3QgdXNhZ2VzUGF0aCA9IHdyaXRlci53cml0ZVVzYWdlc0ZpbGUodXNhZ2VzKTtcblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBkZWZpbml0aW9ucy5qc29uIGF0OiAke2RlZmluaXRpb25zUGF0aH1gKTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIHVzYWdlcy5qc29uIGF0OiAke3VzYWdlc1BhdGh9YCk7XG5cdH1cblxuXHQvLyBEZXRlcm1pbmUgRURTIHNldHRpbmc6IGV4cGxpY2l0IGZsYWcgPiBhdXRvLWRldGVjdCBkaXZlID4gZGVmYXVsdCBvZmZcblx0bGV0IGVuYWJsZUVEUyA9IG9wdGlvbnMuZWRzO1xuXHRpZiAoZW5hYmxlRURTID09PSB1bmRlZmluZWQpIHtcblx0XHRlbmFibGVFRFMgPSBoYXNEaXZlRGVwZW5kZW5jeShwcm9qZWN0RGlyKTtcblx0fVxuXG5cdGlmIChlbmFibGVFRFMpIHtcblx0XHRjb25zdCBlZHMgPSBhbmFseXplci5nZXRFRFNVc2FnZXMoKTtcblx0XHRjb25zdCBlZHNQYXRoID0gd3JpdGVyLndyaXRlRURTRmlsZShlZHMpO1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgZWRzLmpzb24gYXQ6ICR7ZWRzUGF0aH1gKTtcblx0XHR9XG5cdH1cblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgZmxvdy5qc29uIChuYXRpdmUgaW5zdGFuY2UgdXNhZ2UgdHJhY2tpbmcpXG5cdGNvbnN0IGZsb3cgPSBhbmFseXplci5nZXRGbG93VXNhZ2VzKCk7XG5cdGNvbnN0IGZsb3dQYXRoID0gd3JpdGVyLndyaXRlRmxvd0ZpbGUoZmxvdyk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zdCBmbG93Q291bnQgPSBBcnJheS5mcm9tKGZsb3cudmFsdWVzKCkpLnJlZHVjZSgoc3VtLCBhcnIpID0+IHN1bSArIGFyci5sZW5ndGgsIDApO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgZmxvdy5qc29uIGF0OiAke2Zsb3dQYXRofSAoJHtmbG93Q291bnR9IGZsb3cgZW50cmllcylgKTtcblx0fVxuXG5cdC8vIEdlbmVyYXRlIGhpZXJhcmNoeS5qc29uIChzdHJ1Y3R1cmVkKSBhbmQgaGllcmFyY2h5LnR4dCAoQVNDSUkgdHJlZSkgZm9yIHRoZSBUcmllXG5cdGNvbnN0IGhpZXJhcmNoeVJvb3RzID0gZ3JhcGgudG9IaWVyYXJjaHkoKTtcblx0Y29uc3QgaGllcmFyY2h5SnNvblBhdGggPSB3cml0ZXIud3JpdGVIaWVyYXJjaHlGaWxlKGhpZXJhcmNoeVJvb3RzKTtcblx0Y29uc3QgaGllcmFyY2h5VGV4dCA9IHJlbmRlclR5cGVIaWVyYXJjaHkoZ3JhcGgpO1xuXHRjb25zdCBoaWVyYXJjaHlUeHRQYXRoID0gd3JpdGVyLndyaXRlVG8oJ2hpZXJhcmNoeS50eHQnLCBoaWVyYXJjaHlUZXh0KTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgaGllcmFyY2h5Lmpzb24gYXQ6ICR7aGllcmFyY2h5SnNvblBhdGh9YCk7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBoaWVyYXJjaHkudHh0IGF0OiAke2hpZXJhcmNoeVR4dFBhdGh9YCk7XG5cdH1cblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCB0eXBlcyBhdDogJHtvdXRwdXRQYXRofWApO1xuXHRcdGNvbnNvbGUubG9nKGBNb2RlOiAke3VzZU1vZHVsZUF1Z21lbnRhdGlvbiA/ICdnbG9iYWwgYXVnbWVudGF0aW9uIChsZWdhY3kpJyA6ICd0eXBlcyBmaWxlIChkZWZhdWx0KSd9YCk7XG5cdFx0Y29uc29sZS5sb2coYEZvdW5kICR7Z2VuZXJhdGVkVHlwZXMudHlwZXMubGVuZ3RofSB0eXBlczpgKTtcblx0XHRwcmludFR5cGVIaWVyYXJjaHkoZ3JhcGgpO1xuXHR9IGVsc2Uge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgJHtnZW5lcmF0ZWRUeXBlcy50eXBlcy5sZW5ndGh9IHR5cGVzIGF0ICR7b3B0aW9ucy5vdXRwdXREaXIgfHwgJy50YWN0aWNhJ31gKTtcblx0XHRpZiAodXNlTW9kdWxlQXVnbWVudGF0aW9uKSB7XG5cdFx0XHRjb25zb2xlLmxvZygnVXNpbmcgZ2xvYmFsIGF1Z21lbnRhdGlvbiBtb2RlIChsZWdhY3ksIHVzZSBkZWZhdWx0IG1vZGUgZm9yIHR5cGVzLnRzIG9ubHkpJyk7XG5cdFx0fVxuXHR9XG59XG5cbi8qKlxuICogV2F0Y2ggbW9kZVxuICovXG5mdW5jdGlvbiB3YXRjaCAob3B0aW9uczogQ0xJT3B0aW9ucyk6IHZvaWQge1xuXHRjb25zb2xlLmxvZygnU3RhcnRpbmcgd2F0Y2ggbW9kZS4uLicpO1xuXG5cdC8vIEluaXRpYWwgcnVuXG5cdHJ1bihvcHRpb25zKTtcblxuXHQvLyBTZXQgdXAgZmlsZSB3YXRjaGluZ1xuXHRjb25zdCBjaG9raWRhciA9IHJlcXVpcmUoJ2Nob2tpZGFyJyk7XG5cdGNvbnN0IHRzY29uZmlnUGF0aCA9IGZpbmRUc0NvbmZpZyhvcHRpb25zLnByb2plY3QpO1xuXG5cdGlmICghdHNjb25maWdQYXRoKSB7XG5cdFx0Y29uc29sZS5lcnJvcignRXJyb3I6IENvdWxkIG5vdCBmaW5kIHRzY29uZmlnLmpzb24nKTtcblx0XHRwcm9jZXNzLmV4aXQoMSk7XG5cdH1cblxuXHRjb25zdCBwcm9qZWN0RGlyID0gcGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aCk7XG5cdGNvbnN0IHdhdGNoUGF0aHMgPSBvcHRpb25zLmluY2x1ZGUgfHwgWyAnKiovKi50cycgXTtcblx0Y29uc3QgaWdub3JlUGF0aHMgPSBvcHRpb25zLmV4Y2x1ZGUgfHwgWyAnKiovKi5kLnRzJywgJ25vZGVfbW9kdWxlcy8qKicsICcudGFjdGljYS8qKicgXTtcblxuXHRjb25zdCB3YXRjaGVyID0gY2hva2lkYXIud2F0Y2god2F0Y2hQYXRocywge1xuXHRcdGN3ZCAgICAgICAgOiBwcm9qZWN0RGlyLFxuXHRcdGlnbm9yZWQgICAgOiBpZ25vcmVQYXRocyxcblx0XHRwZXJzaXN0ZW50IDogdHJ1ZSxcblx0fSk7XG5cblx0d2F0Y2hlci5vbignY2hhbmdlJywgKGZpbGVQYXRoOiBzdHJpbmcpID0+IHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgRmlsZSBjaGFuZ2VkOiAke2ZpbGVQYXRofWApO1xuXHRcdH1cblx0XHRydW4ob3B0aW9ucyk7XG5cdH0pO1xuXG5cdHdhdGNoZXIub24oJ2FkZCcsIChmaWxlUGF0aDogc3RyaW5nKSA9PiB7XG5cdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0Y29uc29sZS5sb2coYEZpbGUgYWRkZWQ6ICR7ZmlsZVBhdGh9YCk7XG5cdFx0fVxuXHRcdHJ1bihvcHRpb25zKTtcblx0fSk7XG5cblx0Y29uc29sZS5sb2coJ1dhdGNoaW5nIGZvciBjaGFuZ2VzLi4uIChQcmVzcyBDdHJsK0MgdG8gc3RvcCknKTtcbn1cblxuLyoqXG4gKiBNYWluIGVudHJ5IHBvaW50XG4gKi9cbmZ1bmN0aW9uIG1haW4gKCk6IHZvaWQge1xuXHRjb25zdCBhcmdzID0gcHJvY2Vzcy5hcmd2LnNsaWNlKDIpO1xuXHRjb25zdCBvcHRpb25zID0gcGFyc2VBcmdzKGFyZ3MpO1xuXG5cdGlmIChvcHRpb25zLmhlbHApIHtcblx0XHRwcmludEhlbHAoKTtcblx0XHRwcm9jZXNzLmV4aXQoMCk7XG5cdH1cblxuXHR0cnkge1xuXHRcdGlmIChvcHRpb25zLndhdGNoKSB7XG5cdFx0XHR3YXRjaChvcHRpb25zKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0cnVuKG9wdGlvbnMpO1xuXHRcdH1cblx0fSBjYXRjaCAoZXJyb3IpIHtcblx0XHRjb25zb2xlLmVycm9yKCdFcnJvcjonLCBlcnJvciBpbnN0YW5jZW9mIEVycm9yID8gZXJyb3IubWVzc2FnZSA6IGVycm9yKTtcblx0XHRwcm9jZXNzLmV4aXQoMSk7XG5cdH1cbn1cblxuLy8gUnVuIGlmIGV4ZWN1dGVkIGRpcmVjdGx5XG5pZiAocmVxdWlyZS5tYWluID09PSBtb2R1bGUpIHtcblx0bWFpbigpO1xufVxuXG5leHBvcnQge1xuXHRtYWluLCBydW4sIHdhdGNoLCBwYXJzZUFyZ3MgXG59O1xuIl19