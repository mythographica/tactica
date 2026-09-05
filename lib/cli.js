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
const module_graph_1 = require("./module-graph");
const creation_graph_1 = require("./creation-graph");
const scopes_1 = require("./scopes");
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
 * Look up a variable by name starting from a scope, walking outward through
 * parentScopeId. The innermost binding wins even when it carries no typePath
 * (shadowing honesty — an untyped local shadows a typed outer one).
 */
function resolveScopedVariableTypePath(name, scopeId, scopeAnalysis) {
    let current = scopeId;
    while (current) {
        const variable = scopeAnalysis.variables.get(`${current}#${name}`);
        if (variable) {
            const { typePath } = variable;
            return typePath;
        }
        current = scopeAnalysis.scopes.get(current)?.parentScopeId;
    }
    return undefined;
}
/**
 * Join data for mnemographica's wrappers layer: pin each wrap entry to the
 * scope holding its call site, and resolve the wrapped instance argument's
 * mnemonica type through the scope-variable chain.
 */
function attachWrapJoinData(eds, scopeWalker, scopeAnalysis) {
    for (const entries of eds.values()) {
        for (const entry of entries) {
            if (entry.kind !== 'wrap') {
                continue;
            }
            const holderScopeId = scopeWalker.findHolderScopeId(entry.location);
            if (!holderScopeId) {
                continue;
            }
            entry.scopeId = holderScopeId;
            if (!entry.instanceArg) {
                continue;
            }
            const wrapsTypePath = resolveScopedVariableTypePath(entry.instanceArg, holderScopeId, scopeAnalysis);
            if (wrapsTypePath) {
                entry.wrapsTypePath = wrapsTypePath;
            }
        }
    }
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
    // Empty line at end
    lines.push('');
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
    // The project-conventional .tactica dir (next to tsconfig) is ALWAYS
    // excluded, even when --output points elsewhere: generated files are
    // never project source. resolve() both sides — tsconfigPath may be
    // relative ('./tsconfig.json') while sourceFile.fileName is absolute
    const conventionalOutputDir = path.resolve(process.cwd(), path.dirname(tsconfigPath), '.tactica');
    // Collect source files to analyze
    const sourceFiles = [];
    for (const sourceFile of program.getSourceFiles()) {
        if (sourceFile.isDeclarationFile) {
            continue;
        }
        const absoluteFileName = path.resolve(process.cwd(), sourceFile.fileName);
        if (absoluteFileName.startsWith(outputDirPath + path.sep) ||
            absoluteFileName.startsWith(conventionalOutputDir + path.sep)) {
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
    // First pass: collect all definitions.
    // Module-scope tracking (imports/exports for modules.json) happens in the
    // same pass — it needs only the AST, not the collected definitions.
    const moduleGraphBuilder = new module_graph_1.ModuleGraphBuilder(program);
    for (const sourceFile of sourceFiles) {
        if (options.verbose) {
            console.log(`Analyzing (definitions): ${sourceFile.fileName}`);
        }
        try {
            analyzer.analyzeFile(sourceFile);
            moduleGraphBuilder.addFile(sourceFile);
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
    // Local-scope walk (instrumentation walker Phase 2): function/method/arrow
    // scopes only (no block scopes — decision 5), variables with isMutable and
    // reassignment sites (decision 6). Runs after definitions are known so
    // variable typePaths can resolve; holderScopeId is attached to usages
    // before they are written.
    const scopeWalker = new scopes_1.LocalScopeWalker();
    for (const sourceFile of sourceFiles) {
        scopeWalker.addFile(sourceFile);
    }
    const scopeResolver = {
        resolveByName: (name) => {
            if (definitions.has(name)) {
                return name;
            }
            let found;
            for (const [fullPath, definition] of definitions) {
                if (definition.name !== name) {
                    continue;
                }
                if (found) {
                    // Ambiguous name — no type checker, so refuse to guess
                    return undefined;
                }
                found = fullPath;
            }
            return found;
        },
        hasPath: (fullPath) => {
            const result = definitions.has(fullPath);
            return result;
        },
    };
    const scopeAnalysis = scopeWalker.build(scopeResolver);
    scopes_1.LocalScopeWalker.attachHolderScopeIds(usages, scopeWalker);
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
        attachWrapJoinData(eds, scopeWalker, scopeAnalysis);
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
    // Always generate modules.json (module-scope graph: imports/exports,
    // dependencies, cycles, cross-module mnemonica-type edges)
    const definedTypesByFile = new Map();
    for (const [fullPath, definition] of definitions) {
        const { location } = definition;
        const lastColon = location.lastIndexOf(':');
        const prevColon = location.lastIndexOf(':', lastColon - 1);
        const file = location.slice(0, prevColon);
        const list = definedTypesByFile.get(file) ?? [];
        list.push(fullPath);
        definedTypesByFile.set(file, list);
    }
    const moduleGraph = moduleGraphBuilder.build(definedTypesByFile);
    const modulesPath = writer.writeModulesFile(moduleGraph);
    if (options.verbose) {
        const moduleCount = moduleGraph.modules.size;
        const edgeCount = moduleGraph.edges.length;
        console.log(`Generated modules.json at: ${modulesPath} (${moduleCount} modules, ${edgeCount} edges)`);
    }
    // Always generate scopes.json (local-scope walker: scopes, variables,
    // reassignment flow-termination points)
    const scopesPath = writer.writeScopesFile(scopeAnalysis);
    if (options.verbose) {
        const scopeCount = scopeAnalysis.scopes.size;
        const variableCount = scopeAnalysis.variables.size;
        console.log(`Generated scopes.json at: ${scopesPath} (${scopeCount} scopes, ${variableCount} variables)`);
    }
    // The inside-out creation walk (instrumentation walker Phase 3): anchors
    // are the instantiation usages; callers are followed same-file and
    // cross-file (module graph, barrels chased) until only starters remain.
    const sourceFilesByPath = new Map();
    for (const sourceFile of sourceFiles) {
        sourceFilesByPath.set(path.resolve(sourceFile.fileName), sourceFile);
    }
    const creationGraphBuilder = new creation_graph_1.CreationGraphBuilder(moduleGraph, scopeAnalysis, scopeWalker, sourceFilesByPath);
    const creationGraph = creationGraphBuilder.build(usages);
    // Always generate instrumentation.json (NestJS lifecycle crossroads —
    // syntactic detection needs no dive dependency, unlike eds.json). v2
    // carries the creation graph alongside the points.
    const instrumentation = analyzer.getInstrumentationPoints();
    const instrumentationPath = writer.writeInstrumentationFile(instrumentation, creationGraph);
    if (options.verbose) {
        const nodeCount = creationGraph.nodes.length;
        const edgeCount = creationGraph.edges.length;
        const anchorCount = creationGraph.anchors.length;
        console.log(`Generated instrumentation.json at: ${instrumentationPath} (${instrumentation.length} points)`);
        console.log(`  creation graph: ${nodeCount} nodes, ${edgeCount} edges, ${anchorCount} anchors`);
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiY2xpLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL2NsaS50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiO0FBQ0EsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQWd3Qlosb0JBQUk7QUFBRSxrQkFBRztBQUFFLHNCQUFLO0FBQUUsOEJBQVM7QUE5dkI1Qix1Q0FBeUI7QUFDekIsMkNBQTZCO0FBQzdCLCtDQUFpQztBQUNqQyx5Q0FBK0M7QUFDL0MsK0RBQTJEO0FBQzNELDJDQUE2QztBQUM3QyxxQ0FBdUM7QUFDdkMsaURBQW9EO0FBQ3BELHFEQUF3RDtBQUN4RCxxQ0FFa0I7QUF3QmxCOztHQUVHO0FBQ0gsU0FBUyxTQUFTLENBQUUsSUFBYztJQUNqQyxNQUFNLE9BQU8sR0FBZSxFQUFFLENBQUM7SUFFL0IsS0FBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxNQUFNLEVBQUUsQ0FBQyxFQUFFLEVBQUUsQ0FBQztRQUN0QyxNQUFNLEdBQUcsR0FBRyxJQUFJLENBQUUsQ0FBQyxDQUFFLENBQUM7UUFFdEIsUUFBUSxHQUFHLEVBQUUsQ0FBQztZQUNkLEtBQUssSUFBSSxDQUFDO1lBQ1YsS0FBSyxTQUFTO2dCQUNiLE9BQU8sQ0FBQyxLQUFLLEdBQUcsSUFBSSxDQUFDO2dCQUNyQixNQUFNO1lBQ1AsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFdBQVc7Z0JBQ2YsT0FBTyxDQUFDLE9BQU8sR0FBRyxJQUFJLENBQUUsRUFBRSxDQUFDLENBQUUsQ0FBQztnQkFDOUIsTUFBTTtZQUNQLEtBQUssSUFBSSxDQUFDO1lBQ1YsS0FBSyxVQUFVO2dCQUNkLE9BQU8sQ0FBQyxTQUFTLEdBQUcsSUFBSSxDQUFFLEVBQUUsQ0FBQyxDQUFFLENBQUM7Z0JBQ2hDLE1BQU07WUFDUCxLQUFLLElBQUksQ0FBQztZQUNWLEtBQUssV0FBVztnQkFDZixPQUFPLENBQUMsT0FBTyxHQUFH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YmluL2VudiBub2RlXG4ndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIGZzIGZyb20gJ2ZzJztcbmltcG9ydCAqIGFzIHBhdGggZnJvbSAncGF0aCc7XG5pbXBvcnQgKiBhcyB0cyBmcm9tICd0eXBlc2NyaXB0JztcbmltcG9ydCB7IE1uZW1vbmljYUFuYWx5emVyIH0gZnJvbSAnLi9hbmFseXplcic7XG5pbXBvcnQgeyBUb3BvbG9naWNhQW5hbHl6ZXIgfSBmcm9tICcuL3RvcG9sb2dpY2EtYW5hbHl6ZXInO1xuaW1wb3J0IHsgVHlwZXNHZW5lcmF0b3IgfSBmcm9tICcuL2dlbmVyYXRvcic7XG5pbXBvcnQgeyBUeXBlc1dyaXRlciB9IGZyb20gJy4vd3JpdGVyJztcbmltcG9ydCB7IE1vZHVsZUdyYXBoQnVpbGRlciB9IGZyb20gJy4vbW9kdWxlLWdyYXBoJztcbmltcG9ydCB7IENyZWF0aW9uR3JhcGhCdWlsZGVyIH0gZnJvbSAnLi9jcmVhdGlvbi1ncmFwaCc7XG5pbXBvcnQge1xuXHRMb2NhbFNjb3BlV2Fsa2VyLCBTY29wZVR5cGVSZXNvbHZlclxufSBmcm9tICcuL3Njb3Blcyc7XG5pbXBvcnQge1xuXHRUYWN0aWNhQ29uZmlnLCBUeXBlTm9kZSwgRURTSW5mbywgU2NvcGVBbmFseXNpc1xufSBmcm9tICcuL3R5cGVzJztcbmltcG9ydCB7IFR5cGVHcmFwaEltcGwgfSBmcm9tICcuL2dyYXBoJztcblxuLyoqXG4gKiBDTEkgZW50cnkgcG9pbnQgZm9yIFRhY3RpY2FcbiAqXG4gKiBDYW4gYmUgdXNlZCBzdGFuZGFsb25lIHdpdGhvdXQgdGhlIExhbmd1YWdlIFNlcnZpY2UgUGx1Z2luXG4gKi9cblxuaW50ZXJmYWNlIENMSU9wdGlvbnMgZXh0ZW5kcyBUYWN0aWNhQ29uZmlnIHtcblx0d2F0Y2g/OiBib29sZWFuO1xuXHRwcm9qZWN0Pzogc3RyaW5nO1xuXHRoZWxwPzogYm9vbGVhbjtcblx0LyoqIEN1c3RvbSB0b3BvbG9naWNhIGRpcmVjdG9yaWVzIHRvIHNjYW4gKi9cblx0dG9wb2xvZ2ljYURpcnM/OiBzdHJpbmdbXTtcblx0LyoqIEFkZCAuanMgZXh0ZW5zaW9ucyB0byByZWxhdGl2ZSBpbXBvcnRzIGZvciBFU00gTm9kZU5leHQgcmVzb2x1dGlvbiAqL1xuXHRlc20/OiBib29sZWFuO1xuXHQvKiogRW5hYmxlIEVEUyAoRXhlY3V0aW9uIERhdGEgU3RvcmFnZSkgdHJhY2tpbmcgKi9cblx0ZWRzPzogYm9vbGVhbjtcbn1cblxuLyoqXG4gKiBQYXJzZSBjb21tYW5kIGxpbmUgYXJndW1lbnRzXG4gKi9cbmZ1bmN0aW9uIHBhcnNlQXJncyAoYXJnczogc3RyaW5nW10pOiBDTElPcHRpb25zIHtcblx0Y29uc3Qgb3B0aW9uczogQ0xJT3B0aW9ucyA9IHt9O1xuXG5cdGZvciAobGV0IGkgPSAwOyBpIDwgYXJncy5sZW5ndGg7IGkrKykge1xuXHRcdGNvbnN0IGFyZyA9IGFyZ3NbIGkgXTtcblxuXHRcdHN3aXRjaCAoYXJnKSB7XG5cdFx0Y2FzZSAnLXcnOlxuXHRcdGNhc2UgJy0td2F0Y2gnOlxuXHRcdFx0b3B0aW9ucy53YXRjaCA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctcCc6XG5cdFx0Y2FzZSAnLS1wcm9qZWN0Jzpcblx0XHRcdG9wdGlvbnMucHJvamVjdCA9IGFyZ3NbICsraSBdO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLW8nOlxuXHRcdGNhc2UgJy0tb3V0cHV0Jzpcblx0XHRcdG9wdGlvbnMub3V0cHV0RGlyID0gYXJnc1sgKytpIF07XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctaSc6XG5cdFx0Y2FzZSAnLS1pbmNsdWRlJzpcblx0XHRcdG9wdGlvbnMuaW5jbHVkZSA9IChvcHRpb25zLmluY2x1ZGUgfHwgW10pLmNvbmNhdChhcmdzWyArK2kgXS5zcGxpdCgnLCcpKTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1lJzpcblx0XHRjYXNlICctLWV4Y2x1ZGUnOlxuXHRcdFx0b3B0aW9ucy5leGNsdWRlID0gKG9wdGlvbnMuZXhjbHVkZSB8fCBbXSkuY29uY2F0KGFyZ3NbICsraSBdLnNwbGl0KCcsJykpO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLW0nOlxuXHRcdGNhc2UgJy0tbW9kdWxlLWF1Z21lbnRhdGlvbic6XG5cdFx0XHRvcHRpb25zLmdsb2JhbEF1Z21lbnRhdGlvbiA9IGZhbHNlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLXYnOlxuXHRcdGNhc2UgJy0tdmVyYm9zZSc6XG5cdFx0XHRvcHRpb25zLnZlcmJvc2UgPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLXQnOlxuXHRcdGNhc2UgJy0tdG9wb2xvZ2ljYSc6XG5cdFx0XHRvcHRpb25zLnRvcG9sb2dpY2FEaXJzID0gKG9wdGlvbnMudG9wb2xvZ2ljYURpcnMgfHwgW10pLmNvbmNhdChhcmdzWyArK2kgXS5zcGxpdCgnLCcpKTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tZXNtJzpcblx0XHRcdG9wdGlvbnMuZXNtID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tZWRzJzpcblx0XHRcdG9wdGlvbnMuZWRzID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tbm8tZWRzJzpcblx0XHRcdG9wdGlvbnMuZWRzID0gZmFsc2U7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctaCc6XG5cdFx0Y2FzZSAnLS1oZWxwJzpcblx0XHRcdG9wdGlvbnMuaGVscCA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHR9XG5cdH1cblxuXHRyZXR1cm4gb3B0aW9ucztcbn1cblxuLyoqXG4gKiBQcmludCBoZWxwIG1lc3NhZ2VcbiAqL1xuZnVuY3Rpb24gcHJpbnRIZWxwICgpOiB2b2lkIHtcblx0Y29uc29sZS5sb2coYFxuVGFjdGljYSAtIFR5cGVTY3JpcHQgTGFuZ3VhZ2UgU2VydmljZSBQbHVnaW4gZm9yIE1uZW1vbmljYVxuXG5Vc2FnZTogdGFjdGljYSBbb3B0aW9uc11cblxuT3B0aW9uczpcbiAgLXcsIC0td2F0Y2ggICAgICAgICAgICAgICBXYXRjaCBmb3IgZmlsZSBjaGFuZ2VzIGFuZCByZWdlbmVyYXRlIHR5cGVzXG4gIC1wLCAtLXByb2plY3QgICAgICAgICAgICAgUGF0aCB0byB0c2NvbmZpZy5qc29uIChkZWZhdWx0OiAuL3RzY29uZmlnLmpzb24pXG4gIC1vLCAtLW91dHB1dCAgICAgICAgICAgICAgT3V0cHV0IGRpcmVjdG9yeSBmb3IgZ2VuZXJhdGVkIHR5cGVzIChkZWZhdWx0OiAudGFjdGljYSlcbiAgLWksIC0taW5jbHVkZSAgICAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBmaWxlIHBhdHRlcm5zIHRvIGluY2x1ZGVcbiAgLWUsIC0tZXhjbHVkZSAgICAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBmaWxlIHBhdHRlcm5zIHRvIGV4Y2x1ZGVcbiAgLXQsIC0tdG9wb2xvZ2ljYSAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiB0b3BvbG9naWNhIGRpcmVjdG9yaWVzIHRvIHNjYW5cbiAgLW0sIC0tbW9kdWxlLWF1Z21lbnRhdGlvbiBVc2UgbW9kdWxlIGF1Z21lbnRhdGlvbiBpbnN0ZWFkIG9mIGdsb2JhbCAobGVnYWN5IG1vZGUpXG4gIC0tZXNtICAgICAgICAgICAgICAgICAgICAgQWRkIC5qcyBleHRlbnNpb25zIHRvIHJlbGF0aXZlIGltcG9ydHMgKE5vZGVOZXh0IEVTTSlcbiAgLS1lZHMgICAgICAgICAgICAgICAgICAgICBFbmFibGUgRURTIChFeGVjdXRpb24gRGF0YSBTdG9yYWdlKSB0cmFja2luZ1xuICAtLW5vLWVkcyAgICAgICAgICAgICAgICAgIERpc2FibGUgRURTIHRyYWNraW5nXG4gIC12LCAtLXZlcmJvc2UgICAgICAgICAgICAgRW5hYmxlIHZlcmJvc2UgbG9nZ2luZ1xuICAtaCwgLS1oZWxwICAgICAgICAgICAgICAgIFNob3cgdGhpcyBoZWxwIG1lc3NhZ2VcblxuRXhhbXBsZXM6XG4gIHRhY3RpY2EgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAjIEdlbmVyYXRlIHR5cGVzIHdpdGggZ2xvYmFsIGF1Z21lbnRhdGlvbiAoZGVmYXVsdClcbiAgdGFjdGljYSAtLXdhdGNoICAgICAgICAgICAgICAgICAgICAgICMgV2F0Y2ggbW9kZVxuICB0YWN0aWNhIC0tbW9kdWxlLWF1Z21lbnRhdGlvbiAgICAgICAgIyBVc2UgbGVnYWN5IG1vZHVsZSBhdWdtZW50YXRpb24gbW9kZVxuICB0YWN0aWNhIC0tcHJvamVjdCAuL3NyYy90c2NvbmZpZy5qc29uICMgQ3VzdG9tIHRzY29uZmlnIHBhdGhcbiAgdGFjdGljYSAtLW91dHB1dCAuL3R5cGVzL21uZW1vbmljYSAgICMgQ3VzdG9tIG91dHB1dCBkaXJlY3RvcnlcbiAgdGFjdGljYSAtLXRvcG9sb2dpY2EgLi9zcmMvYWktdHlwZXMgICMgU2NhbiBzcGVjaWZpYyB0b3BvbG9naWNhIGRpcmVjdG9yeVxuYCk7XG59XG5cbi8qKlxuICogRmluZCB0c2NvbmZpZy5qc29uXG4gKi9cbmZ1bmN0aW9uIGZpbmRUc0NvbmZpZyAocHJvamVjdFBhdGg/OiBzdHJpbmcpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRpZiAocHJvamVjdFBhdGgpIHtcblx0XHRpZiAoZnMuZXhpc3RzU3luYyhwcm9qZWN0UGF0aCkpIHtcblx0XHRcdHJldHVybiBwcm9qZWN0UGF0aDtcblx0XHR9XG5cdFx0dGhyb3cgbmV3IEVycm9yKGBQcm9qZWN0IGZpbGUgbm90IGZvdW5kOiAke3Byb2plY3RQYXRofWApO1xuXHR9XG5cblx0Ly8gTG9vayBmb3IgdHNjb25maWcuanNvbiBpbiBjdXJyZW50IGRpcmVjdG9yeSBhbmQgcGFyZW50IGRpcmVjdG9yaWVzXG5cdGxldCBjdXJyZW50RGlyID0gcHJvY2Vzcy5jd2QoKTtcblx0d2hpbGUgKGN1cnJlbnREaXIgIT09IHBhdGguZGlybmFtZShjdXJyZW50RGlyKSkge1xuXHRcdGNvbnN0IHRzY29uZmlnUGF0aCA9IHBhdGguam9pbihjdXJyZW50RGlyLCAndHNjb25maWcuanNvbicpO1xuXHRcdGlmIChmcy5leGlzdHNTeW5jKHRzY29uZmlnUGF0aCkpIHtcblx0XHRcdHJldHVybiB0c2NvbmZpZ1BhdGg7XG5cdFx0fVxuXHRcdGN1cnJlbnREaXIgPSBwYXRoLmRpcm5hbWUoY3VycmVudERpcik7XG5cdH1cblxuXHRyZXR1cm4gdW5kZWZpbmVkO1xufVxuXG4vKipcbiAqIExvYWQgVHlwZVNjcmlwdCBwcm9ncmFtIGZyb20gdHNjb25maWdcbiAqL1xuZnVuY3Rpb24gbG9hZFByb2dyYW0gKHRzY29uZmlnUGF0aDogc3RyaW5nKTogdHMuUHJvZ3JhbSB7XG5cdGNvbnN0IGNvbmZpZ0ZpbGUgPSB0cy5yZWFkQ29uZmlnRmlsZSh0c2NvbmZpZ1BhdGgsIHRzLnN5cy5yZWFkRmlsZSk7XG5cblx0aWYgKGNvbmZpZ0ZpbGUuZXJyb3IpIHtcblx0XHRjb25zdCBlcnJvclRleHQgPSB0cy5mbGF0dGVuRGlhZ25vc3RpY01lc3NhZ2VUZXh0KFxuXHRcdFx0Y29uZmlnRmlsZS5lcnJvci5tZXNzYWdlVGV4dCxcblx0XHRcdCdcXG4nXG5cdFx0KTtcblx0XHR0aHJvdyBuZXcgRXJyb3IoYEVycm9yIHJlYWRpbmcgdHNjb25maWc6ICR7ZXJyb3JUZXh0fWApO1xuXHR9XG5cblx0Y29uc3QgcGFyc2VkQ29uZmlnID0gdHMucGFyc2VKc29uQ29uZmlnRmlsZUNvbnRlbnQoXG5cdFx0Y29uZmlnRmlsZS5jb25maWcsXG5cdFx0dHMuc3lzLFxuXHRcdHBhdGguZGlybmFtZSh0c2NvbmZpZ1BhdGgpXG5cdCk7XG5cblx0aWYgKHBhcnNlZENvbmZpZy5lcnJvcnMubGVuZ3RoID4gMCkge1xuXHRcdGNvbnN0IGVycm9yTWVzc2FnZXMgPSBwYXJzZWRDb25maWcuZXJyb3JzLm1hcChlID0+XG5cdFx0XHR0cy5mbGF0dGVuRGlhZ25vc3RpY01lc3NhZ2VUZXh0KGUubWVzc2FnZVRleHQsICdcXG4nKSk7XG5cdFx0dGhyb3cgbmV3IEVycm9yKGBFcnJvciBwYXJzaW5nIHRzY29uZmlnOiAke2Vycm9yTWVzc2FnZXMuam9pbignXFxuJyl9YCk7XG5cdH1cblxuXHRjb25zdCBwcm9ncmFtID0gdHMuY3JlYXRlUHJvZ3JhbSh7XG5cdFx0cm9vdE5hbWVzIDogcGFyc2VkQ29uZmlnLmZpbGVOYW1lcyxcblx0XHRvcHRpb25zICAgOiBwYXJzZWRDb25maWcub3B0aW9ucyxcblx0fSk7XG5cblx0cmV0dXJuIHByb2dyYW07XG59XG5cbi8qKlxuICogTG9vayB1cCBhIHZhcmlhYmxlIGJ5IG5hbWUgc3RhcnRpbmcgZnJvbSBhIHNjb3BlLCB3YWxraW5nIG91dHdhcmQgdGhyb3VnaFxuICogcGFyZW50U2NvcGVJZC4gVGhlIGlubmVybW9zdCBiaW5kaW5nIHdpbnMgZXZlbiB3aGVuIGl0IGNhcnJpZXMgbm8gdHlwZVBhdGhcbiAqIChzaGFkb3dpbmcgaG9uZXN0eSDigJQgYW4gdW50eXBlZCBsb2NhbCBzaGFkb3dzIGEgdHlwZWQgb3V0ZXIgb25lKS5cbiAqL1xuZnVuY3Rpb24gcmVzb2x2ZVNjb3BlZFZhcmlhYmxlVHlwZVBhdGggKFxuXHRuYW1lOiBzdHJpbmcsXG5cdHNjb3BlSWQ6IHN0cmluZyxcblx0c2NvcGVBbmFseXNpczogU2NvcGVBbmFseXNpc1xuKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0bGV0IGN1cnJlbnQ6IHN0cmluZyB8IHVuZGVmaW5lZCA9IHNjb3BlSWQ7XG5cdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0Y29uc3QgdmFyaWFibGUgPSBzY29wZUFuYWx5c2lzLnZhcmlhYmxlcy5nZXQoYCR7Y3VycmVudH0jJHtuYW1lfWApO1xuXHRcdGlmICh2YXJpYWJsZSkge1xuXHRcdFx0Y29uc3QgeyB0eXBlUGF0aCB9ID0gdmFyaWFibGU7XG5cdFx0XHRyZXR1cm4gdHlwZVBhdGg7XG5cdFx0fVxuXHRcdGN1cnJlbnQgPSBzY29wZUFuYWx5c2lzLnNjb3Blcy5nZXQoY3VycmVudCk/LnBhcmVudFNjb3BlSWQ7XG5cdH1cblx0cmV0dXJuIHVuZGVmaW5lZDtcbn1cblxuLyoqXG4gKiBKb2luIGRhdGEgZm9yIG1uZW1vZ3JhcGhpY2EncyB3cmFwcGVycyBsYXllcjogcGluIGVhY2ggd3JhcCBlbnRyeSB0byB0aGVcbiAqIHNjb3BlIGhvbGRpbmcgaXRzIGNhbGwgc2l0ZSwgYW5kIHJlc29sdmUgdGhlIHdyYXBwZWQgaW5zdGFuY2UgYXJndW1lbnQnc1xuICogbW5lbW9uaWNhIHR5cGUgdGhyb3VnaCB0aGUgc2NvcGUtdmFyaWFibGUgY2hhaW4uXG4gKi9cbmZ1bmN0aW9uIGF0dGFjaFdyYXBKb2luRGF0YSAoXG5cdGVkczogTWFwPHN0cmluZywgRURTSW5mb1tdPixcblx0c2NvcGVXYWxrZXI6IExvY2FsU2NvcGVXYWxrZXIsXG5cdHNjb3BlQW5hbHlzaXM6IFNjb3BlQW5hbHlzaXNcbik6IHZvaWQge1xuXHRmb3IgKGNvbnN0IGVudHJpZXMgb2YgZWRzLnZhbHVlcygpKSB7XG5cdFx0Zm9yIChjb25zdCBlbnRyeSBvZiBlbnRyaWVzKSB7XG5cdFx0XHRpZiAoZW50cnkua2luZCAhPT0gJ3dyYXAnKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgaG9sZGVyU2NvcGVJZCA9IHNjb3BlV2Fsa2VyLmZpbmRIb2xkZXJTY29wZUlkKGVudHJ5LmxvY2F0aW9uKTtcblx0XHRcdGlmICghaG9sZGVyU2NvcGVJZCkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGVudHJ5LnNjb3BlSWQgPSBob2xkZXJTY29wZUlkO1xuXHRcdFx0aWYgKCFlbnRyeS5pbnN0YW5jZUFyZykge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHdyYXBzVHlwZVBhdGggPSByZXNvbHZlU2NvcGVkVmFyaWFibGVUeXBlUGF0aChcblx0XHRcdFx0ZW50cnkuaW5zdGFuY2VBcmcsXG5cdFx0XHRcdGhvbGRlclNjb3BlSWQsXG5cdFx0XHRcdHNjb3BlQW5hbHlzaXNcblx0XHRcdCk7XG5cdFx0XHRpZiAod3JhcHNUeXBlUGF0aCkge1xuXHRcdFx0XHRlbnRyeS53cmFwc1R5cGVQYXRoID0gd3JhcHNUeXBlUGF0aDtcblx0XHRcdH1cblx0XHR9XG5cdH1cbn1cblxuLyoqXG4gKiBSZW5kZXIgdHlwZSBoaWVyYXJjaHkgYXMgYW4gQVNDSUkgdHJlZSBzdHJpbmcuXG4gKi9cbmZ1bmN0aW9uIHJlbmRlclR5cGVIaWVyYXJjaHkgKGdyYXBoOiBUeXBlR3JhcGhJbXBsKTogc3RyaW5nIHtcblx0Y29uc3QgbGluZXM6IHN0cmluZ1tdID0gWyAnVHlwZSBIaWVyYXJjaHkgKFRyaWUpOicgXTtcblxuXHRmdW5jdGlvbiByZW5kZXJOb2RlIChub2RlOiBUeXBlTm9kZSwgcHJlZml4ID0gJycsIGlzTGFzdCA9IHRydWUpOiB2b2lkIHtcblx0XHRjb25zdCBjb25uZWN0b3IgPSBpc0xhc3QgPyAn4pSU4pSA4pSAICcgOiAn4pSc4pSA4pSAICc7XG5cdFx0Ly8gVXNlIG5vZGUuZnVsbFBhdGggZGlyZWN0bHkgYW5kIGNvbnZlcnQgZG90cyB0byB1bmRlcnNjb3Jlc1xuXHRcdGNvbnN0IGluc3RhbmNlTmFtZSA9IG5vZGUuZnVsbFBhdGgucmVwbGFjZSgvXFwuL2csICdfJyk7XG5cdFx0bGluZXMucHVzaChgJHtwcmVmaXh9JHtjb25uZWN0b3J9JHtpbnN0YW5jZU5hbWV9YCk7XG5cblx0XHRjb25zdCBjaGlsZHJlbiA9IEFycmF5LmZyb20obm9kZS5jaGlsZHJlbi52YWx1ZXMoKSk7XG5cdFx0Y29uc3QgbmV3UHJlZml4ID0gcHJlZml4ICsgKGlzTGFzdCA/ICcgICAgJyA6ICfilIIgICAnKTtcblxuXHRcdGZvciAobGV0IGkgPSAwOyBpIDwgY2hpbGRyZW4ubGVuZ3RoOyBpKyspIHtcblx0XHRcdHJlbmRlck5vZGUoY2hpbGRyZW5bIGkgXSwgbmV3UHJlZml4LCBpID09PSBjaGlsZHJlbi5sZW5ndGggLSAxKTtcblx0XHR9XG5cdH1cblxuXHRjb25zdCByb290cyA9IEFycmF5LmZyb20oZ3JhcGgucm9vdHMudmFsdWVzKCkpO1xuXHRmb3IgKGxldCBpID0gMDsgaSA8IHJvb3RzLmxlbmd0aDsgaSsrKSB7XG5cdFx0cmVuZGVyTm9kZShyb290c1sgaSBdLCAnJywgaSA9PT0gcm9vdHMubGVuZ3RoIC0gMSk7XG5cdH1cblx0Ly8gRW1wdHkgbGluZSBhdCBlbmRcblx0bGluZXMucHVzaCgnJyk7XG5cblx0Y29uc3QgcmVzdWx0ID0gbGluZXMuam9pbignXFxuJyk7XG5cdHJldHVybiByZXN1bHQ7XG59XG5cbi8qKlxuICogUHJpbnQgdHlwZSBoaWVyYXJjaHkgdG8gdGhlIGNvbnNvbGUuXG4gKi9cbmZ1bmN0aW9uIHByaW50VHlwZUhpZXJhcmNoeSAoZ3JhcGg6IFR5cGVHcmFwaEltcGwpOiB2b2lkIHtcblx0Y29uc3Qgb3V0cHV0ID0gcmVuZGVyVHlwZUhpZXJhcmNoeShncmFwaCk7XG5cdGNvbnNvbGUubG9nKG91dHB1dCk7XG59XG5cbi8qKlxuICogQ2hlY2sgaWYgQG1uZW1vbmljYS9kaXZlIGlzIHByZXNlbnQgaW4gcGFja2FnZS5qc29uIGRlcGVuZGVuY2llc1xuICovXG5mdW5jdGlvbiBoYXNEaXZlRGVwZW5kZW5jeSAocHJvamVjdERpcjogc3RyaW5nKTogYm9vbGVhbiB7XG5cdGNvbnN0IHBhY2thZ2VKc29uUGF0aCA9IHBhdGguam9pbihwcm9qZWN0RGlyLCAncGFja2FnZS5qc29uJyk7XG5cdGlmICghZnMuZXhpc3RzU3luYyhwYWNrYWdlSnNvblBhdGgpKSB7XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cdHRyeSB7XG5cdFx0Y29uc3QgY29udGVudCA9IGZzLnJlYWRGaWxlU3luYyhwYWNrYWdlSnNvblBhdGgsICd1dGYtOCcpO1xuXHRcdGNvbnN0IHBrZyA9IEpTT04ucGFyc2UoY29udGVudCk7XG5cdFx0Y29uc3QgZGVwcyA9IHBrZy5kZXBlbmRlbmNpZXMgfHwge307XG5cdFx0Y29uc3QgZGV2RGVwcyA9IHBrZy5kZXZEZXBlbmRlbmNpZXMgfHwge307XG5cdFx0Y29uc3QgcGVlckRlcHMgPSBwa2cucGVlckRlcGVuZGVuY2llcyB8fCB7fTtcblx0XHRyZXR1cm4gJ0BtbmVtb25pY2EvZGl2ZScgaW4gZGVwcyB8fCAnQG1uZW1vbmljYS9kaXZlJyBpbiBkZXZEZXBzIHx8ICdAbW5lbW9uaWNhL2RpdmUnIGluIHBlZXJEZXBzO1xuXHR9IGNhdGNoIHtcblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cbn1cblxuLyoqXG4gKiBTY2FuIGZvciB0b3BvbG9naWNhIGRpcmVjdG9yeSBzdHJ1Y3R1cmVzXG4gKi9cbmZ1bmN0aW9uIHNjYW5Ub3BvbG9naWNhRGlyZWN0b3JpZXMgKHByb2plY3REaXI6IHN0cmluZywgY3VzdG9tRGlycz86IHN0cmluZ1tdKTogc3RyaW5nW10ge1xuXHRjb25zdCBkaXJzOiBzdHJpbmdbXSA9IFtdO1xuXG5cdC8vIEZpcnN0LCBhZGQgY3VzdG9tIGRpcmVjdG9yaWVzIGlmIHNwZWNpZmllZFxuXHRpZiAoY3VzdG9tRGlycykge1xuXHRcdGZvciAoY29uc3QgZGlyIG9mIGN1c3RvbURpcnMpIHtcblx0XHRcdGNvbnN0IGRpclBhdGggPSBwYXRoLmlzQWJzb2x1dGUoZGlyKSA/IGRpciA6IHBhdGguam9pbihwcm9qZWN0RGlyLCBkaXIpO1xuXHRcdFx0aWYgKGZzLmV4aXN0c1N5bmMoZGlyUGF0aCkgJiYgZnMuc3RhdFN5bmMoZGlyUGF0aCkuaXNEaXJlY3RvcnkoKSkge1xuXHRcdFx0XHRkaXJzLnB1c2goZGlyUGF0aCk7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRjb25zb2xlLndhcm4oYFdhcm5pbmc6IFRvcG9sb2dpY2EgZGlyZWN0b3J5IG5vdCBmb3VuZDogJHtkaXJQYXRofWApO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8vIFRoZW4gYXV0by1kaXNjb3ZlciBzdGFuZGFyZCB0b3BvbG9naWNhIGRpcmVjdG9yaWVzXG5cdGNvbnN0IHBvc3NpYmxlRGlycyA9IFsgJ2FpLXR5cGVzJywgJ3R5cGVzJywgJ3RvcG9sb2dpY2EtdHlwZXMnIF07XG5cblx0Zm9yIChjb25zdCBkaXJOYW1lIG9mIHBvc3NpYmxlRGlycykge1xuXHRcdGNvbnN0IGRpclBhdGggPSBwYXRoLmpvaW4ocHJvamVjdERpciwgZGlyTmFtZSk7XG5cdFx0aWYgKGZzLmV4aXN0c1N5bmMoZGlyUGF0aCkgJiYgZnMuc3RhdFN5bmMoZGlyUGF0aCkuaXNEaXJlY3RvcnkoKSkge1xuXHRcdFx0Ly8gQXZvaWQgZHVwbGljYXRlc1xuXHRcdFx0aWYgKCFkaXJzLmluY2x1ZGVzKGRpclBhdGgpKSB7XG5cdFx0XHRcdGRpcnMucHVzaChkaXJQYXRoKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvLyBBbHNvIHNjYW4gc3JjLyBzdWJkaXJlY3Rvcnlcblx0Y29uc3Qgc3JjUGF0aCA9IHBhdGguam9pbihwcm9qZWN0RGlyLCAnc3JjJyk7XG5cdGlmIChmcy5leGlzdHNTeW5jKHNyY1BhdGgpICYmIGZzLnN0YXRTeW5jKHNyY1BhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRmb3IgKGNvbnN0IGRpck5hbWUgb2YgcG9zc2libGVEaXJzKSB7XG5cdFx0XHRjb25zdCBkaXJQYXRoID0gcGF0aC5qb2luKHNyY1BhdGgsIGRpck5hbWUpO1xuXHRcdFx0aWYgKGZzLmV4aXN0c1N5bmMoZGlyUGF0aCkgJiYgZnMuc3RhdFN5bmMoZGlyUGF0aCkuaXNEaXJlY3RvcnkoKSkge1xuXHRcdFx0XHQvLyBBdm9pZCBkdXBsaWNhdGVzXG5cdFx0XHRcdGlmICghZGlycy5pbmNsdWRlcyhkaXJQYXRoKSkge1xuXHRcdFx0XHRcdGRpcnMucHVzaChkaXJQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdHJldHVybiBkaXJzO1xufVxuXG4vKipcbiAqIFJ1biB0eXBlIGdlbmVyYXRpb25cbiAqL1xuZnVuY3Rpb24gcnVuIChvcHRpb25zOiBDTElPcHRpb25zKTogdm9pZCB7XG5cdGNvbnN0IHRzY29uZmlnUGF0aCA9IGZpbmRUc0NvbmZpZyhvcHRpb25zLnByb2plY3QpO1xuXG5cdGlmICghdHNjb25maWdQYXRoKSB7XG5cdFx0Y29uc29sZS5lcnJvcignRXJyb3I6IENvdWxkIG5vdCBmaW5kIHRzY29uZmlnLmpzb24nKTtcblx0XHRwcm9jZXNzLmV4aXQoMSk7XG5cdH1cblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYFVzaW5nIHRzY29uZmlnOiAke3RzY29uZmlnUGF0aH1gKTtcblx0fVxuXG5cdC8vIExvYWQgVHlwZVNjcmlwdCBwcm9ncmFtXG5cdGNvbnN0IHByb2dyYW0gPSBsb2FkUHJvZ3JhbSh0c2NvbmZpZ1BhdGgpO1xuXG5cdC8vIENyZWF0ZSBhbmFseXplclxuXHRjb25zdCBhbmFseXplciA9IG5ldyBNbmVtb25pY2FBbmFseXplcihwcm9ncmFtKTtcblxuXHQvLyBEZXRlcm1pbmUgb3V0cHV0IGRpcmVjdG9yeSBmb3IgZXhjbHVzaW9uXG5cdGNvbnN0IG91dHB1dERpciA9IG9wdGlvbnMub3V0cHV0RGlyIHx8ICcudGFjdGljYSc7XG5cdGNvbnN0IG91dHB1dERpclBhdGggPSBwYXRoLnJlc29sdmUocHJvY2Vzcy5jd2QoKSwgb3V0cHV0RGlyKTtcblx0Ly8gVGhlIHByb2plY3QtY29udmVudGlvbmFsIC50YWN0aWNhIGRpciAobmV4dCB0byB0c2NvbmZpZykgaXMgQUxXQVlTXG5cdC8vIGV4Y2x1ZGVkLCBldmVuIHdoZW4gLS1vdXRwdXQgcG9pbnRzIGVsc2V3aGVyZTogZ2VuZXJhdGVkIGZpbGVzIGFyZVxuXHQvLyBuZXZlciBwcm9qZWN0IHNvdXJjZS4gcmVzb2x2ZSgpIGJvdGggc2lkZXMg4oCUIHRzY29uZmlnUGF0aCBtYXkgYmVcblx0Ly8gcmVsYXRpdmUgKCcuL3RzY29uZmlnLmpzb24nKSB3aGlsZSBzb3VyY2VGaWxlLmZpbGVOYW1lIGlzIGFic29sdXRlXG5cdGNvbnN0IGNvbnZlbnRpb25hbE91dHB1dERpciA9IHBhdGgucmVzb2x2ZShwcm9jZXNzLmN3ZCgpLCBwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKSwgJy50YWN0aWNhJyk7XG5cblx0Ly8gQ29sbGVjdCBzb3VyY2UgZmlsZXMgdG8gYW5hbHl6ZVxuXHRjb25zdCBzb3VyY2VGaWxlczogdHMuU291cmNlRmlsZVtdID0gW107XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBwcm9ncmFtLmdldFNvdXJjZUZpbGVzKCkpIHtcblx0XHRpZiAoc291cmNlRmlsZS5pc0RlY2xhcmF0aW9uRmlsZSkge1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QgYWJzb2x1dGVGaWxlTmFtZSA9IHBhdGgucmVzb2x2ZShwcm9jZXNzLmN3ZCgpLCBzb3VyY2VGaWxlLmZpbGVOYW1lKTtcblx0XHRpZiAoYWJzb2x1dGVGaWxlTmFtZS5zdGFydHNXaXRoKG91dHB1dERpclBhdGggKyBwYXRoLnNlcCkgfHxcblx0XHRcdGFic29sdXRlRmlsZU5hbWUuc3RhcnRzV2l0aChjb252ZW50aW9uYWxPdXRwdXREaXIgKyBwYXRoLnNlcCkpIHtcblx0XHRcdGNvbnRpbnVlO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGV4Y2x1ZGUgcGF0dGVybnNcblx0XHRpZiAob3B0aW9ucy5leGNsdWRlKSB7XG5cdFx0XHRjb25zdCBzaG91bGRFeGNsdWRlID0gb3B0aW9ucy5leGNsdWRlLnNvbWUocGF0dGVybiA9PlxuXHRcdFx0XHRzb3VyY2VGaWxlLmZpbGVOYW1lLmluY2x1ZGVzKHBhdHRlcm4ucmVwbGFjZSgvXFwqL2csICcnKSkpO1xuXHRcdFx0aWYgKHNob3VsZEV4Y2x1ZGUpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgaW5jbHVkZSBwYXR0ZXJuc1xuXHRcdGlmIChvcHRpb25zLmluY2x1ZGUgJiYgb3B0aW9ucy5pbmNsdWRlLmxlbmd0aCA+IDApIHtcblx0XHRcdGNvbnN0IHNob3VsZEluY2x1ZGUgPSBvcHRpb25zLmluY2x1ZGUuc29tZShwYXR0ZXJuID0+XG5cdFx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUuaW5jbHVkZXMocGF0dGVybi5yZXBsYWNlKC9cXCovZywgJycpKSk7XG5cdFx0XHRpZiAoIXNob3VsZEluY2x1ZGUpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0c291cmNlRmlsZXMucHVzaChzb3VyY2VGaWxlKTtcblx0fVxuXG5cdC8vIFNjYW4gZm9yIHRvcG9sb2dpY2EgZGlyZWN0b3J5IHN0cnVjdHVyZXMgRklSU1Rcblx0Y29uc3QgcHJvamVjdERpciA9IHBhdGguZGlybmFtZSh0c2NvbmZpZ1BhdGgpO1xuXHRjb25zdCB0b3BvbG9naWNhRGlycyA9IHNjYW5Ub3BvbG9naWNhRGlyZWN0b3JpZXMocHJvamVjdERpciwgb3B0aW9ucy50b3BvbG9naWNhRGlycyk7XG5cblx0aWYgKHRvcG9sb2dpY2FEaXJzLmxlbmd0aCA+IDAgJiYgb3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEZvdW5kIHRvcG9sb2dpY2EgZGlyZWN0b3JpZXM6ICR7dG9wb2xvZ2ljYURpcnMuam9pbignLCAnKX1gKTtcblx0fVxuXG5cdC8vIEFuYWx5emUgdG9wb2xvZ2ljYSBkaXJlY3RvcmllcyBCRUZPUkUgdXNhZ2UgY29sbGVjdGlvblxuXHRjb25zdCB0b3BvbG9naWNhQW5hbHl6ZXIgPSBuZXcgVG9wb2xvZ2ljYUFuYWx5emVyKCk7XG5cdGNvbnN0IHRvcG9sb2dpY2FUeXBlcyA9IG5ldyBNYXA8c3RyaW5nLCBpbXBvcnQoJy4vdHlwZXMnKS5UeXBlTm9kZT4oKTtcblx0Zm9yIChjb25zdCBkaXIgb2YgdG9wb2xvZ2ljYURpcnMpIHtcblx0XHRjb25zdCByZXN1bHQgPSB0b3BvbG9naWNhQW5hbHl6ZXIuYW5hbHl6ZURpcmVjdG9yeShkaXIpO1xuXHRcdGlmIChyZXN1bHQudHlwZXMuc2l6ZSA+IDApIHtcblx0XHRcdC8vIENvbGxlY3QgdG9wb2xvZ2ljYSB0eXBlcyBmb3IgZGVmaW5pdGlvbnMgYW5kIHVzYWdlIHRyYWNraW5nXG5cdFx0XHRmb3IgKGNvbnN0IFsgdHlwZVBhdGgsIG5vZGUgXSBvZiByZXN1bHQudHlwZXMpIHtcblx0XHRcdFx0dG9wb2xvZ2ljYVR5cGVzLnNldCh0eXBlUGF0aCwgbm9kZSk7XG5cdFx0XHR9XG5cdFx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRcdGNvbnNvbGUubG9nKGBBZGRlZCAke3Jlc3VsdC50eXBlcy5zaXplfSB0eXBlcyBmcm9tICR7ZGlyfWApO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAocmVzdWx0LmVycm9ycy5sZW5ndGggPiAwICYmIG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0cmVzdWx0LmVycm9ycy5mb3JFYWNoKGVyciA9PiBjb25zb2xlLndhcm4oYFtUb3BvbG9naWNhXSAke2Vycn1gKSk7XG5cdFx0fVxuXHR9XG5cblx0Ly8gQWRkIHRvcG9sb2dpY2EgdHlwZXMgdG8gYW5hbHl6ZXIgc28gdGhleSdyZSBhdmFpbGFibGUgZm9yIHVzYWdlIGRldGVjdGlvblxuXHQvLyBQcm9jZXNzIGluIG9yZGVyIG9mIHBhdGggZGVwdGggKHBhcmVudHMgZmlyc3QpIHRvIGVuc3VyZSBwcm9wZXIgaGllcmFyY2h5XG5cdGNvbnN0IHNvcnRlZFR5cGVzID0gQXJyYXkuZnJvbSh0b3BvbG9naWNhVHlwZXMuZW50cmllcygpKS5zb3J0KChhLCBiKSA9PiB7XG5cdFx0Y29uc3QgZGVwdGhBID0gKGFbIDAgXS5tYXRjaCgvXFwuL2cpIHx8IFtdKS5sZW5ndGg7XG5cdFx0Y29uc3QgZGVwdGhCID0gKGJbIDAgXS5tYXRjaCgvXFwuL2cpIHx8IFtdKS5sZW5ndGg7XG5cdFx0cmV0dXJuIGRlcHRoQSAtIGRlcHRoQjtcblx0fSk7XG5cdGZvciAoY29uc3QgWyB0eXBlUGF0aCwgbm9kZSBdIG9mIHNvcnRlZFR5cGVzKSB7XG5cdFx0YW5hbHl6ZXIuYWRkVG9wb2xvZ2ljYVR5cGUodHlwZVBhdGgsIG5vZGUpO1xuXHR9XG5cblx0Ly8gRmlyc3QgcGFzczogY29sbGVjdCBhbGwgZGVmaW5pdGlvbnMuXG5cdC8vIE1vZHVsZS1zY29wZSB0cmFja2luZyAoaW1wb3J0cy9leHBvcnRzIGZvciBtb2R1bGVzLmpzb24pIGhhcHBlbnMgaW4gdGhlXG5cdC8vIHNhbWUgcGFzcyDigJQgaXQgbmVlZHMgb25seSB0aGUgQVNULCBub3QgdGhlIGNvbGxlY3RlZCBkZWZpbml0aW9ucy5cblx0Y29uc3QgbW9kdWxlR3JhcGhCdWlsZGVyID0gbmV3IE1vZHVsZUdyYXBoQnVpbGRlcihwcm9ncmFtKTtcblx0Zm9yIChjb25zdCBzb3VyY2VGaWxlIG9mIHNvdXJjZUZpbGVzKSB7XG5cdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0Y29uc29sZS5sb2coYEFuYWx5emluZyAoZGVmaW5pdGlvbnMpOiAke3NvdXJjZUZpbGUuZmlsZU5hbWV9YCk7XG5cdFx0fVxuXG5cdFx0dHJ5IHtcblx0XHRcdGFuYWx5emVyLmFuYWx5emVGaWxlKHNvdXJjZUZpbGUpO1xuXHRcdFx0bW9kdWxlR3JhcGhCdWlsZGVyLmFkZEZpbGUoc291cmNlRmlsZSk7XG5cdFx0fSBjYXRjaCAoZXJyKSB7XG5cdFx0XHRjb25zb2xlLmVycm9yKGBFcnJvciBhbmFseXppbmcgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfTpgLCBlcnIpO1xuXHRcdFx0dGhyb3cgZXJyO1xuXHRcdH1cblx0fVxuXG5cdC8vIFNlY29uZCBwYXNzOiBjb2xsZWN0IHVzYWdlcyAobm93IGFsbCBkZWZpbml0aW9ucyBhcmUga25vd24sIGluY2x1ZGluZyB0b3BvbG9naWNhKVxuXHRhbmFseXplci5yZXNldFVzYWdlcygpO1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2Ygc291cmNlRmlsZXMpIHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgQW5hbHl6aW5nICh1c2FnZXMpOiAke3NvdXJjZUZpbGUuZmlsZU5hbWV9YCk7XG5cdFx0fVxuXG5cdFx0dHJ5IHtcblx0XHRcdGFuYWx5emVyLmFuYWx5emVGaWxlKHNvdXJjZUZpbGUpO1xuXHRcdH0gY2F0Y2ggKGVycikge1xuXHRcdFx0Y29uc29sZS5lcnJvcihgRXJyb3IgYW5hbHl6aW5nICR7c291cmNlRmlsZS5maWxlTmFtZX06YCwgZXJyKTtcblx0XHRcdHRocm93IGVycjtcblx0XHR9XG5cdH1cblxuXHQvLyBHZW5lcmF0ZSB0eXBlcyBmcm9tIG1uZW1vbmljYSBhbmFseXNpc1xuXHQvLyBOb3RlOiB0b3BvbG9naWNhIHR5cGVzIGFyZSBhbHJlYWR5IGFkZGVkIHRvIHRoZSBhbmFseXplcidzIGdyYXBoIHZpYSBhZGRUb3BvbG9naWNhVHlwZSgpXG5cdGNvbnN0IGdyYXBoID0gYW5hbHl6ZXIuZ2V0R3JhcGgoKTtcblx0Y29uc3QgZ2VuZXJhdG9yID0gbmV3IFR5cGVzR2VuZXJhdG9yKGdyYXBoLCBvcHRpb25zLmVzbSwgb3B0aW9ucy5vdXRwdXREaXIpO1xuXG5cdC8vIENoZWNrIGlmIG1vZHVsZSBhdWdtZW50YXRpb24gbW9kZSBpcyByZXF1ZXN0ZWQgKGxlZ2FjeSlcblx0Y29uc3QgdXNlTW9kdWxlQXVnbWVudGF0aW9uID0gb3B0aW9ucy5nbG9iYWxBdWdtZW50YXRpb24gPT09IGZhbHNlO1xuXG5cdC8vIEdlbmVyYXRlIHR5cGVzIGJhc2VkIG9uIG1vZGVcblx0bGV0IGdlbmVyYXRlZFR5cGVzOiB7IGNvbnRlbnQ6IHN0cmluZzsgdHlwZXM6IHN0cmluZ1tdIH07XG5cdGxldCBvdXRwdXRQYXRoOiBzdHJpbmc7XG5cblx0Y29uc3Qgd3JpdGVyID0gbmV3IFR5cGVzV3JpdGVyKG9wdGlvbnMub3V0cHV0RGlyKTtcblxuXHRpZiAodXNlTW9kdWxlQXVnbWVudGF0aW9uKSB7XG5cdFx0Ly8gTGVnYWN5IG1vZGU6IGdlbmVyYXRlIGdsb2JhbCBhdWdtZW50YXRpb24gZmlsZSAoaW5kZXguZC50cylcblx0XHRnZW5lcmF0ZWRUeXBlcyA9IGdlbmVyYXRvci5nZW5lcmF0ZUdsb2JhbEF1Z21lbnRhdGlvbigpO1xuXHRcdG91dHB1dFBhdGggPSB3cml0ZXIud3JpdGVHbG9iYWxBdWdtZW50YXRpb24oZ2VuZXJhdGVkVHlwZXMpO1xuXHR9IGVsc2Uge1xuXHRcdC8vIERlZmF1bHQgbW9kZTogZ2VuZXJhdGUgdHlwZXMudHMgZm9yIG1hbnVhbCBpbXBvcnRzXG5cdFx0Z2VuZXJhdGVkVHlwZXMgPSBnZW5lcmF0b3IuZ2VuZXJhdGVUeXBlc0ZpbGUoKTtcblx0XHRvdXRwdXRQYXRoID0gd3JpdGVyLndyaXRlVHlwZXNGaWxlKGdlbmVyYXRlZFR5cGVzKTtcblxuXHRcdC8vIEdlbmVyYXRlIHJlZ2lzdHJ5LnRzIGZvciB0eXBlLXNhZmUgbG9va3VwKCkgZnVuY3Rpb25cblx0XHRjb25zdCByZWdpc3RyeVR5cGVzID0gZ2VuZXJhdG9yLmdlbmVyYXRlVHlwZVJlZ2lzdHJ5KCk7XG5cdFx0Y29uc3QgcmVnaXN0cnlQYXRoID0gd3JpdGVyLndyaXRlVG8oJ3JlZ2lzdHJ5LnRzJywgcmVnaXN0cnlUeXBlcy5jb250ZW50KTtcblxuXHRcdC8vIEdlbmVyYXRlIGluZGV4LnRzIHRvIGV4cG9ydCBldmVyeXRoaW5nXG5cdFx0Y29uc3QgaW5kZXhDb250ZW50ID0gYC8vIEdlbmVyYXRlZCBieSBAbW5lbW9uaWNhL3RhY3RpY2EgLSBETyBOT1QgRURJVFxuLy8gRXhwb3J0IGFsbCBnZW5lcmF0ZWQgdHlwZXNcblxuZXhwb3J0ICogZnJvbSAnLi90eXBlcyR7b3B0aW9ucy5lc20gPyAnLmpzJyA6ICcnfSc7XG5leHBvcnQgKiBmcm9tICcuL3JlZ2lzdHJ5JHtvcHRpb25zLmVzbSA/ICcuanMnIDogJyd9JztcbmA7XG5cdFx0d3JpdGVyLndyaXRlVG8oJ2luZGV4LnRzJywgaW5kZXhDb250ZW50KTtcblxuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgcmVnaXN0cnkudHMgYXQ6ICR7cmVnaXN0cnlQYXRofWApO1xuXHRcdH1cblx0fVxuXG5cdC8vIEdlbmVyYXRlIGRlZmluaXRpb25zLmpzb24gYW5kIHVzYWdlcy5qc29uIGZvciBjb2RlIG5hdmlnYXRpb25cblx0Ly8gSW5jbHVkZSBib3RoIG1uZW1vbmljYSBhbmQgdG9wb2xvZ2ljYSBkZWZpbml0aW9uc1xuXHRjb25zdCBkZWZpbml0aW9ucyA9IG5ldyBNYXAoYW5hbHl6ZXIuZ2V0RGVmaW5pdGlvbnMoKSk7XG5cdGNvbnN0IHVzYWdlcyA9IG5ldyBNYXAoYW5hbHl6ZXIuZ2V0VXNhZ2VzKCkpO1xuXHRcblx0Ly8gQWRkIHRvcG9sb2dpY2EgdHlwZXMgdG8gZGVmaW5pdGlvbnNcblx0Zm9yIChjb25zdCBbIGZ1bGxQYXRoLCB0eXBlTm9kZSBdIG9mIHRvcG9sb2dpY2FUeXBlcykge1xuXHRcdC8vIFNraXAgaWYgYWxyZWFkeSBleGlzdHMgKHByZWZlciBtbmVtb25pY2EncyBhbmFseXNpcylcblx0XHRpZiAoZGVmaW5pdGlvbnMuaGFzKGZ1bGxQYXRoKSkge1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXHRcdFxuXHRcdGNvbnN0IGRlZmluaXRpb246IGltcG9ydCgnLi90eXBlcycpLkRlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTm9kZS5uYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHt0eXBlTm9kZS5zb3VyY2VGaWxlfToke3R5cGVOb2RlLmxpbmV9OiR7dHlwZU5vZGUuY29sdW1ufWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiB0eXBlTm9kZS5wYXJlbnQgPyB0eXBlTm9kZS5wYXJlbnQuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBmYWxzZVxuXHRcdH07XG5cdFx0ZGVmaW5pdGlvbnMuc2V0KGZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0fVxuXG5cdC8vIExvY2FsLXNjb3BlIHdhbGsgKGluc3RydW1lbnRhdGlvbiB3YWxrZXIgUGhhc2UgMik6IGZ1bmN0aW9uL21ldGhvZC9hcnJvd1xuXHQvLyBzY29wZXMgb25seSAobm8gYmxvY2sgc2NvcGVzIOKAlCBkZWNpc2lvbiA1KSwgdmFyaWFibGVzIHdpdGggaXNNdXRhYmxlIGFuZFxuXHQvLyByZWFzc2lnbm1lbnQgc2l0ZXMgKGRlY2lzaW9uIDYpLiBSdW5zIGFmdGVyIGRlZmluaXRpb25zIGFyZSBrbm93biBzb1xuXHQvLyB2YXJpYWJsZSB0eXBlUGF0aHMgY2FuIHJlc29sdmU7IGhvbGRlclNjb3BlSWQgaXMgYXR0YWNoZWQgdG8gdXNhZ2VzXG5cdC8vIGJlZm9yZSB0aGV5IGFyZSB3cml0dGVuLlxuXHRjb25zdCBzY29wZVdhbGtlciA9IG5ldyBMb2NhbFNjb3BlV2Fsa2VyKCk7XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdHNjb3BlV2Fsa2VyLmFkZEZpbGUoc291cmNlRmlsZSk7XG5cdH1cblx0Y29uc3Qgc2NvcGVSZXNvbHZlcjogU2NvcGVUeXBlUmVzb2x2ZXIgPSB7XG5cdFx0cmVzb2x2ZUJ5TmFtZSA6IChuYW1lOiBzdHJpbmcpOiBzdHJpbmcgfCB1bmRlZmluZWQgPT4ge1xuXHRcdFx0aWYgKGRlZmluaXRpb25zLmhhcyhuYW1lKSkge1xuXHRcdFx0XHRyZXR1cm4gbmFtZTtcblx0XHRcdH1cblx0XHRcdGxldCBmb3VuZDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdFx0Zm9yIChjb25zdCBbIGZ1bGxQYXRoLCBkZWZpbml0aW9uIF0gb2YgZGVmaW5pdGlvbnMpIHtcblx0XHRcdFx0aWYgKGRlZmluaXRpb24ubmFtZSAhPT0gbmFtZSkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdC8vIEFtYmlndW91cyBuYW1lIOKAlCBubyB0eXBlIGNoZWNrZXIsIHNvIHJlZnVzZSB0byBndWVzc1xuXHRcdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Zm91bmQgPSBmdWxsUGF0aDtcblx0XHRcdH1cblx0XHRcdHJldHVybiBmb3VuZDtcblx0XHR9LFxuXHRcdGhhc1BhdGggOiAoZnVsbFBhdGg6IHN0cmluZyk6IGJvb2xlYW4gPT4ge1xuXHRcdFx0Y29uc3QgcmVzdWx0ID0gZGVmaW5pdGlvbnMuaGFzKGZ1bGxQYXRoKTtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fSxcblx0fTtcblx0Y29uc3Qgc2NvcGVBbmFseXNpcyA9IHNjb3BlV2Fsa2VyLmJ1aWxkKHNjb3BlUmVzb2x2ZXIpO1xuXHRMb2NhbFNjb3BlV2Fsa2VyLmF0dGFjaEhvbGRlclNjb3BlSWRzKHVzYWdlcywgc2NvcGVXYWxrZXIpO1xuXG5cdGNvbnN0IGRlZmluaXRpb25zUGF0aCA9IHdyaXRlci53cml0ZURlZmluaXRpb25zRmlsZShkZWZpbml0aW9ucyk7XG5cdGNvbnN0IHVzYWdlc1BhdGggPSB3cml0ZXIud3JpdGVVc2FnZXNGaWxlKHVzYWdlcyk7XG5cblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgZGVmaW5pdGlvbnMuanNvbiBhdDogJHtkZWZpbml0aW9uc1BhdGh9YCk7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCB1c2FnZXMuanNvbiBhdDogJHt1c2FnZXNQYXRofWApO1xuXHR9XG5cblx0Ly8gRGV0ZXJtaW5lIEVEUyBzZXR0aW5nOiBleHBsaWNpdCBmbGFnID4gYXV0by1kZXRlY3QgZGl2ZSA+IGRlZmF1bHQgb2ZmXG5cdGxldCBlbmFibGVFRFMgPSBvcHRpb25zLmVkcztcblx0aWYgKGVuYWJsZUVEUyA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0ZW5hYmxlRURTID0gaGFzRGl2ZURlcGVuZGVuY3kocHJvamVjdERpcik7XG5cdH1cblxuXHRpZiAoZW5hYmxlRURTKSB7XG5cdFx0Y29uc3QgZWRzID0gYW5hbHl6ZXIuZ2V0RURTVXNhZ2VzKCk7XG5cdFx0YXR0YWNoV3JhcEpvaW5EYXRhKGVkcywgc2NvcGVXYWxrZXIsIHNjb3BlQW5hbHlzaXMpO1xuXHRcdGNvbnN0IGVkc1BhdGggPSB3cml0ZXIud3JpdGVFRFNGaWxlKGVkcyk7XG5cdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBlZHMuanNvbiBhdDogJHtlZHNQYXRofWApO1xuXHRcdH1cblx0fVxuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBmbG93Lmpzb24gKG5hdGl2ZSBpbnN0YW5jZSB1c2FnZSB0cmFja2luZylcblx0Y29uc3QgZmxvdyA9IGFuYWx5emVyLmdldEZsb3dVc2FnZXMoKTtcblx0Y29uc3QgZmxvd1BhdGggPSB3cml0ZXIud3JpdGVGbG93RmlsZShmbG93KTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IGZsb3dDb3VudCA9IEFycmF5LmZyb20oZmxvdy52YWx1ZXMoKSkucmVkdWNlKChzdW0sIGFycikgPT4gc3VtICsgYXJyLmxlbmd0aCwgMCk7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBmbG93Lmpzb24gYXQ6ICR7Zmxvd1BhdGh9ICgke2Zsb3dDb3VudH0gZmxvdyBlbnRyaWVzKWApO1xuXHR9XG5cblx0Ly8gQWx3YXlzIGdlbmVyYXRlIG1vZHVsZXMuanNvbiAobW9kdWxlLXNjb3BlIGdyYXBoOiBpbXBvcnRzL2V4cG9ydHMsXG5cdC8vIGRlcGVuZGVuY2llcywgY3ljbGVzLCBjcm9zcy1tb2R1bGUgbW5lbW9uaWNhLXR5cGUgZWRnZXMpXG5cdGNvbnN0IGRlZmluZWRUeXBlc0J5RmlsZSA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmdbXT4oKTtcblx0Zm9yIChjb25zdCBbIGZ1bGxQYXRoLCBkZWZpbml0aW9uIF0gb2YgZGVmaW5pdGlvbnMpIHtcblx0XHRjb25zdCB7IGxvY2F0aW9uIH0gPSBkZWZpbml0aW9uO1xuXHRcdGNvbnN0IGxhc3RDb2xvbiA9IGxvY2F0aW9uLmxhc3RJbmRleE9mKCc6Jyk7XG5cdFx0Y29uc3QgcHJldkNvbG9uID0gbG9jYXRpb24ubGFzdEluZGV4T2YoJzonLCBsYXN0Q29sb24gLSAxKTtcblx0XHRjb25zdCBmaWxlID0gbG9jYXRpb24uc2xpY2UoMCwgcHJldkNvbG9uKTtcblx0XHRjb25zdCBsaXN0ID0gZGVmaW5lZFR5cGVzQnlGaWxlLmdldChmaWxlKSA/PyBbXTtcblx0XHRsaXN0LnB1c2goZnVsbFBhdGgpO1xuXHRcdGRlZmluZWRUeXBlc0J5RmlsZS5zZXQoZmlsZSwgbGlzdCk7XG5cdH1cblx0Y29uc3QgbW9kdWxlR3JhcGggPSBtb2R1bGVHcmFwaEJ1aWxkZXIuYnVpbGQoZGVmaW5lZFR5cGVzQnlGaWxlKTtcblx0Y29uc3QgbW9kdWxlc1BhdGggPSB3cml0ZXIud3JpdGVNb2R1bGVzRmlsZShtb2R1bGVHcmFwaCk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zdCBtb2R1bGVDb3VudCA9IG1vZHVsZUdyYXBoLm1vZHVsZXMuc2l6ZTtcblx0XHRjb25zdCBlZGdlQ291bnQgPSBtb2R1bGVHcmFwaC5lZGdlcy5sZW5ndGg7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBtb2R1bGVzLmpzb24gYXQ6ICR7bW9kdWxlc1BhdGh9ICgke21vZHVsZUNvdW50fSBtb2R1bGVzLCAke2VkZ2VDb3VudH0gZWRnZXMpYCk7XG5cdH1cblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgc2NvcGVzLmpzb24gKGxvY2FsLXNjb3BlIHdhbGtlcjogc2NvcGVzLCB2YXJpYWJsZXMsXG5cdC8vIHJlYXNzaWdubWVudCBmbG93LXRlcm1pbmF0aW9uIHBvaW50cylcblx0Y29uc3Qgc2NvcGVzUGF0aCA9IHdyaXRlci53cml0ZVNjb3Blc0ZpbGUoc2NvcGVBbmFseXNpcyk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zdCBzY29wZUNvdW50ID0gc2NvcGVBbmFseXNpcy5zY29wZXMuc2l6ZTtcblx0XHRjb25zdCB2YXJpYWJsZUNvdW50ID0gc2NvcGVBbmFseXNpcy52YXJpYWJsZXMuc2l6ZTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIHNjb3Blcy5qc29uIGF0OiAke3Njb3Blc1BhdGh9ICgke3Njb3BlQ291bnR9IHNjb3BlcywgJHt2YXJpYWJsZUNvdW50fSB2YXJpYWJsZXMpYCk7XG5cdH1cblxuXHQvLyBUaGUgaW5zaWRlLW91dCBjcmVhdGlvbiB3YWxrIChpbnN0cnVtZW50YXRpb24gd2Fsa2VyIFBoYXNlIDMpOiBhbmNob3JzXG5cdC8vIGFyZSB0aGUgaW5zdGFudGlhdGlvbiB1c2FnZXM7IGNhbGxlcnMgYXJlIGZvbGxvd2VkIHNhbWUtZmlsZSBhbmRcblx0Ly8gY3Jvc3MtZmlsZSAobW9kdWxlIGdyYXBoLCBiYXJyZWxzIGNoYXNlZCkgdW50aWwgb25seSBzdGFydGVycyByZW1haW4uXG5cdGNvbnN0IHNvdXJjZUZpbGVzQnlQYXRoID0gbmV3IE1hcDxzdHJpbmcsIHRzLlNvdXJjZUZpbGU+KCk7XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdHNvdXJjZUZpbGVzQnlQYXRoLnNldChwYXRoLnJlc29sdmUoc291cmNlRmlsZS5maWxlTmFtZSksIHNvdXJjZUZpbGUpO1xuXHR9XG5cdGNvbnN0IGNyZWF0aW9uR3JhcGhCdWlsZGVyID0gbmV3IENyZWF0aW9uR3JhcGhCdWlsZGVyKG1vZHVsZUdyYXBoLCBzY29wZUFuYWx5c2lzLCBzY29wZVdhbGtlciwgc291cmNlRmlsZXNCeVBhdGgpO1xuXHRjb25zdCBjcmVhdGlvbkdyYXBoID0gY3JlYXRpb25HcmFwaEJ1aWxkZXIuYnVpbGQodXNhZ2VzKTtcblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgaW5zdHJ1bWVudGF0aW9uLmpzb24gKE5lc3RKUyBsaWZlY3ljbGUgY3Jvc3Nyb2FkcyDigJRcblx0Ly8gc3ludGFjdGljIGRldGVjdGlvbiBuZWVkcyBubyBkaXZlIGRlcGVuZGVuY3ksIHVubGlrZSBlZHMuanNvbikuIHYyXG5cdC8vIGNhcnJpZXMgdGhlIGNyZWF0aW9uIGdyYXBoIGFsb25nc2lkZSB0aGUgcG9pbnRzLlxuXHRjb25zdCBpbnN0cnVtZW50YXRpb24gPSBhbmFseXplci5nZXRJbnN0cnVtZW50YXRpb25Qb2ludHMoKTtcblx0Y29uc3QgaW5zdHJ1bWVudGF0aW9uUGF0aCA9IHdyaXRlci53cml0ZUluc3RydW1lbnRhdGlvbkZpbGUoaW5zdHJ1bWVudGF0aW9uLCBjcmVhdGlvbkdyYXBoKTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IG5vZGVDb3VudCA9IGNyZWF0aW9uR3JhcGgubm9kZXMubGVuZ3RoO1xuXHRcdGNvbnN0IGVkZ2VDb3VudCA9IGNyZWF0aW9uR3JhcGguZWRnZXMubGVuZ3RoO1xuXHRcdGNvbnN0IGFuY2hvckNvdW50ID0gY3JlYXRpb25HcmFwaC5hbmNob3JzLmxlbmd0aDtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGluc3RydW1lbnRhdGlvbi5qc29uIGF0OiAke2luc3RydW1lbnRhdGlvblBhdGh9ICgke2luc3RydW1lbnRhdGlvbi5sZW5ndGh9IHBvaW50cylgKTtcblx0XHRjb25zb2xlLmxvZyhgICBjcmVhdGlvbiBncmFwaDogJHtub2RlQ291bnR9IG5vZGVzLCAke2VkZ2VDb3VudH0gZWRnZXMsICR7YW5jaG9yQ291bnR9IGFuY2hvcnNgKTtcblx0fVxuXG5cdC8vIEdlbmVyYXRlIGhpZXJhcmNoeS5qc29uIChzdHJ1Y3R1cmVkKSBhbmQgaGllcmFyY2h5LnR4dCAoQVNDSUkgdHJlZSkgZm9yIHRoZSBUcmllXG5cdGNvbnN0IGhpZXJhcmNoeVJvb3RzID0gZ3JhcGgudG9IaWVyYXJjaHkoKTtcblx0Y29uc3QgaGllcmFyY2h5SnNvblBhdGggPSB3cml0ZXIud3JpdGVIaWVyYXJjaHlGaWxlKGhpZXJhcmNoeVJvb3RzKTtcblx0Y29uc3QgaGllcmFyY2h5VGV4dCA9IHJlbmRlclR5cGVIaWVyYXJjaHkoZ3JhcGgpO1xuXHRjb25zdCBoaWVyYXJjaHlUeHRQYXRoID0gd3JpdGVyLndyaXRlVG8oJ2hpZXJhcmNoeS50eHQnLCBoaWVyYXJjaHlUZXh0KTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgaGllcmFyY2h5Lmpzb24gYXQ6ICR7aGllcmFyY2h5SnNvblBhdGh9YCk7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBoaWVyYXJjaHkudHh0IGF0OiAke2hpZXJhcmNoeVR4dFBhdGh9YCk7XG5cdH1cblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCB0eXBlcyBhdDogJHtvdXRwdXRQYXRofWApO1xuXHRcdGNvbnNvbGUubG9nKGBNb2RlOiAke3VzZU1vZHVsZUF1Z21lbnRhdGlvbiA/ICdnbG9iYWwgYXVnbWVudGF0aW9uIChsZWdhY3kpJyA6ICd0eXBlcyBmaWxlIChkZWZhdWx0KSd9YCk7XG5cdFx0Y29uc29sZS5sb2coYEZvdW5kICR7Z2VuZXJhdGVkVHlwZXMudHlwZXMubGVuZ3RofSB0eXBlczpgKTtcblx0XHRwcmludFR5cGVIaWVyYXJjaHkoZ3JhcGgpO1xuXHR9IGVsc2Uge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgJHtnZW5lcmF0ZWRUeXBlcy50eXBlcy5sZW5ndGh9IHR5cGVzIGF0ICR7b3B0aW9ucy5vdXRwdXREaXIgfHwgJy50YWN0aWNhJ31gKTtcblx0XHRpZiAodXNlTW9kdWxlQXVnbWVudGF0aW9uKSB7XG5cdFx0XHRjb25zb2xlLmxvZygnVXNpbmcgZ2xvYmFsIGF1Z21lbnRhdGlvbiBtb2RlIChsZWdhY3ksIHVzZSBkZWZhdWx0IG1vZGUgZm9yIHR5cGVzLnRzIG9ubHkpJyk7XG5cdFx0fVxuXHR9XG59XG5cbi8qKlxuICogV2F0Y2ggbW9kZVxuICovXG5mdW5jdGlvbiB3YXRjaCAob3B0aW9uczogQ0xJT3B0aW9ucyk6IHZvaWQge1xuXHRjb25zb2xlLmxvZygnU3RhcnRpbmcgd2F0Y2ggbW9kZS4uLicpO1xuXG5cdC8vIEluaXRpYWwgcnVuXG5cdHJ1bihvcHRpb25zKTtcblxuXHQvLyBTZXQgdXAgZmlsZSB3YXRjaGluZ1xuXHRjb25zdCBjaG9raWRhciA9IHJlcXVpcmUoJ2Nob2tpZGFyJyk7XG5cdGNvbnN0IHRzY29uZmlnUGF0aCA9IGZpbmRUc0NvbmZpZyhvcHRpb25zLnByb2plY3QpO1xuXG5cdGlmICghdHNjb25maWdQYXRoKSB7XG5cdFx0Y29uc29sZS5lcnJvcignRXJyb3I6IENvdWxkIG5vdCBmaW5kIHRzY29uZmlnLmpzb24nKTtcblx0XHRwcm9jZXNzLmV4aXQoMSk7XG5cdH1cblxuXHRjb25zdCBwcm9qZWN0RGlyID0gcGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aCk7XG5cdGNvbnN0IHdhdGNoUGF0aHMgPSBvcHRpb25zLmluY2x1ZGUgfHwgWyAnKiovKi50cycgXTtcblx0Y29uc3QgaWdub3JlUGF0aHMgPSBvcHRpb25zLmV4Y2x1ZGUgfHwgWyAnKiovKi5kLnRzJywgJ25vZGVfbW9kdWxlcy8qKicsICcudGFjdGljYS8qKicgXTtcblxuXHRjb25zdCB3YXRjaGVyID0gY2hva2lkYXIud2F0Y2god2F0Y2hQYXRocywge1xuXHRcdGN3ZCAgICAgICAgOiBwcm9qZWN0RGlyLFxuXHRcdGlnbm9yZWQgICAgOiBpZ25vcmVQYXRocyxcblx0XHRwZXJzaXN0ZW50IDogdHJ1ZSxcblx0fSk7XG5cblx0d2F0Y2hlci5vbignY2hhbmdlJywgKGZpbGVQYXRoOiBzdHJpbmcpID0+IHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgRmlsZSBjaGFuZ2VkOiAke2ZpbGVQYXRofWApO1xuXHRcdH1cblx0XHRydW4ob3B0aW9ucyk7XG5cdH0pO1xuXG5cdHdhdGNoZXIub24oJ2FkZCcsIChmaWxlUGF0aDogc3RyaW5nKSA9PiB7XG5cdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0Y29uc29sZS5sb2coYEZpbGUgYWRkZWQ6ICR7ZmlsZVBhdGh9YCk7XG5cdFx0fVxuXHRcdHJ1bihvcHRpb25zKTtcblx0fSk7XG5cblx0Y29uc29sZS5sb2coJ1dhdGNoaW5nIGZvciBjaGFuZ2VzLi4uIChQcmVzcyBDdHJsK0MgdG8gc3RvcCknKTtcbn1cblxuLyoqXG4gKiBNYWluIGVudHJ5IHBvaW50XG4gKi9cbmZ1bmN0aW9uIG1haW4gKCk6IHZvaWQge1xuXHRjb25zdCBhcmdzID0gcHJvY2Vzcy5hcmd2LnNsaWNlKDIpO1xuXHRjb25zdCBvcHRpb25zID0gcGFyc2VBcmdzKGFyZ3MpO1xuXG5cdGlmIChvcHRpb25zLmhlbHApIHtcblx0XHRwcmludEhlbHAoKTtcblx0XHRwcm9jZXNzLmV4aXQoMCk7XG5cdH1cblxuXHR0cnkge1xuXHRcdGlmIChvcHRpb25zLndhdGNoKSB7XG5cdFx0XHR3YXRjaChvcHRpb25zKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0cnVuKG9wdGlvbnMpO1xuXHRcdH1cblx0fSBjYXRjaCAoZXJyb3IpIHtcblx0XHRjb25zb2xlLmVycm9yKCdFcnJvcjonLCBlcnJvciBpbnN0YW5jZW9mIEVycm9yID8gZXJyb3IubWVzc2FnZSA6IGVycm9yKTtcblx0XHRwcm9jZXNzLmV4aXQoMSk7XG5cdH1cbn1cblxuLy8gUnVuIGlmIGV4ZWN1dGVkIGRpcmVjdGx5XG5pZiAocmVxdWlyZS5tYWluID09PSBtb2R1bGUpIHtcblx0bWFpbigpO1xufVxuXG5leHBvcnQge1xuXHRtYWluLCBydW4sIHdhdGNoLCBwYXJzZUFyZ3MgXG59O1xuIl19