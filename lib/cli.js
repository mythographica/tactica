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
const module_1 = require("module");
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
Tactica - Type definition generator for Mnemonica

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

Configuration:
  Framework instrumentation vocabulary is supplied by plugins. Place a
  .tactica.js (or tactica.config.js) next to your tsconfig.json:

      module.exports = { plugins: [ 'your-framework-adapter/tactica' ] };

  Entries are module specifiers (required relative to the config file) or
  inline plugin objects. Without plugins, instrumentation.json points = [].

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
 * Config file candidates (eslint-style project config), searched next to
 * the resolved tsconfig first, then in the current working directory.
 */
const CONFIG_FILE_NAMES = ['.tactica.js', 'tactica.config.js'];
/**
 * Load framework-vocabulary plugins: programmatic options first, then the
 * project config file. String entries are module specifiers required
 * relative to the config file (e.g. an adapter package's plugin subpath).
 * Without a config file and without programmatic plugins the analyzer
 * stays framework-blind and instrumentation.json carries empty points.
 */
function loadTacticaPlugins(projectDir, options) {
    const plugins = [...(options.plugins || [])];
    const searchDirs = [projectDir];
    const cwd = process.cwd();
    if (cwd !== projectDir) {
        searchDirs.push(cwd);
    }
    let configPath;
    for (const dir of searchDirs) {
        for (const name of CONFIG_FILE_NAMES) {
            const candidate = path.join(dir, name);
            if (fs.existsSync(candidate)) {
                configPath = candidate;
                break;
            }
        }
        if (configPath) {
            break;
        }
    }
    if (!configPath) {
        return plugins;
    }
    // createRequire anchored at the config file: the config's own imports
    // and string plugin specifiers resolve against the project's modules
    const configRequire = (0, module_1.createRequire)(configPath);
    const loaded = configRequire(configPath);
    const config = loaded && typeof loaded === 'object' && 'default' in loaded
        ? loaded.default
        : loaded;
    const entries = config && Array.isArray(config.plugins) ? config.plugins : [];
    for (const entry of entries) {
        if (typeof entry !== 'string') {
            plugins.push(entry);
            continue;
        }
        const mod = configRequire(entry);
        const plugin = mod && typeof mod === 'object' && 'default' in mod
            ? mod.default
            : mod;
        plugins.push(plugin);
    }
    if (options.verbose) {
        const names = plugins.map(plugin => plugin.name || '(unnamed)').join(', ');
        console.log(`Loaded tactica config: ${configPath} (plugins: ${names || 'none'})`);
    }
    return plugins;
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
    // Framework vocabulary arrives via plugins — a config file next to the
    // tsconfig (or in cwd) and/or programmatic options. None loaded means
    // the analyzer detects zero instrumentation points.
    const plugins = loadTacticaPlugins(path.dirname(path.resolve(tsconfigPath)), options);
    // Load TypeScript program
    const program = loadProgram(tsconfigPath);
    // Create analyzer
    const analyzer = new analyzer_1.MnemonicaAnalyzer(program, plugins);
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
    // Always generate instrumentation.json (framework lifecycle crossroads
    // from the loaded plugins — syntactic detection needs no dive
    // dependency, unlike eds.json). v2 carries the creation graph
    // alongside the points.
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiY2xpLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL2NsaS50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiO0FBQ0EsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQTQxQlosb0JBQUk7QUFBRSxrQkFBRztBQUFFLHNCQUFLO0FBQUUsOEJBQVM7QUExMUI1Qix1Q0FBeUI7QUFDekIsMkNBQTZCO0FBQzdCLG1DQUF1QztBQUN2QywrQ0FBaUM7QUFDakMseUNBQStDO0FBQy9DLCtEQUEyRDtBQUMzRCwyQ0FBNkM7QUFDN0MscUNBQXVDO0FBQ3ZDLGlEQUFvRDtBQUNwRCxxREFBd0Q7QUFDeEQscUNBRWtCO0FBMkJsQjs7R0FFRztBQUNILFNBQVMsU0FBUyxDQUFFLElBQWM7SUFDakMsTUFBTSxPQUFPLEdBQWUsRUFBRSxDQUFDO0lBRS9CLEtBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxJQUFJLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFLENBQUM7UUFDdEMsTUFBTSxHQUFHLEdBQUcsSUFBSSxDQUFFLENBQUMsQ0FBRSxDQUFDO1FBRXRCLFFBQVEsR0FBRyxFQUFFLENBQUM7WUFDZCxLQUFLLElBQUksQ0FBQztZQUNWLEtBQUssU0FBUztnQkFDYixPQUFPLENBQUMsS0FBSyxHQUFHLElBQUksQ0FBQztnQkFDckIsTUFBTTtZQUNQLEtBQUssSUFBSSxDQUFDO1lBQ1YsS0FBSyxXQUFXO2dCQUNmLE9BQU8sQ0FBQyxPQUFPLEdBQUcsSUFBSSxDQUFFLEVBQUUsQ0FBQyxDQUFFLENBQUM7Z0JBQzlCLE1BQU07WUFDUCxLQUFLLElBQUksQ0FBQztZQUNWLEtBQUssVUFBVTtnQkFDZCxPQUFPLENBQUMsU0FBUyxHQUFHLElBQUksQ0FBRSxFQUFFLENBQUMsQ0FBRSxDQUFDO2dCQUNoQyxNQUFNO1lBQ1AsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFdBQVc7Z0JBQ2YsT0FBTyxD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QztRQUN4RSxPQUFPLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDO0lBQ2pCLENBQUM7QUFDRixDQUFDO0FBRUQsMkJBQTJCO0FBQzNCLElBQUksT0FBTyxDQUFDLElBQUksS0FBSyxNQUFNLEVBQUUsQ0FBQztJQUM3QixJQUFJLEVBQUUsQ0FBQztBQUNSLENBQUMiLCJzb3VyY2VzQ29udGVudCI6WyIjIS91c3IvYmluL2VudiBub2RlXG4ndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIGZzIGZyb20gJ2ZzJztcbmltcG9ydCAqIGFzIHBhdGggZnJvbSAncGF0aCc7XG5pbXBvcnQgeyBjcmVhdGVSZXF1aXJlIH0gZnJvbSAnbW9kdWxlJztcbmltcG9ydCAqIGFzIHRzIGZyb20gJ3R5cGVzY3JpcHQnO1xuaW1wb3J0IHsgTW5lbW9uaWNhQW5hbHl6ZXIgfSBmcm9tICcuL2FuYWx5emVyJztcbmltcG9ydCB7IFRvcG9sb2dpY2FBbmFseXplciB9IGZyb20gJy4vdG9wb2xvZ2ljYS1hbmFseXplcic7XG5pbXBvcnQgeyBUeXBlc0dlbmVyYXRvciB9IGZyb20gJy4vZ2VuZXJhdG9yJztcbmltcG9ydCB7IFR5cGVzV3JpdGVyIH0gZnJvbSAnLi93cml0ZXInO1xuaW1wb3J0IHsgTW9kdWxlR3JhcGhCdWlsZGVyIH0gZnJvbSAnLi9tb2R1bGUtZ3JhcGgnO1xuaW1wb3J0IHsgQ3JlYXRpb25HcmFwaEJ1aWxkZXIgfSBmcm9tICcuL2NyZWF0aW9uLWdyYXBoJztcbmltcG9ydCB7XG5cdExvY2FsU2NvcGVXYWxrZXIsIFNjb3BlVHlwZVJlc29sdmVyXG59IGZyb20gJy4vc2NvcGVzJztcbmltcG9ydCB7XG5cdFRhY3RpY2FDb25maWcsIFR5cGVOb2RlLCBFRFNJbmZvLCBTY29wZUFuYWx5c2lzXG59IGZyb20gJy4vdHlwZXMnO1xuaW1wb3J0IHsgVGFjdGljYVBsdWdpbiB9IGZyb20gJy4vcGx1Z2lucyc7XG5pbXBvcnQgeyBUeXBlR3JhcGhJbXBsIH0gZnJvbSAnLi9ncmFwaCc7XG5cbi8qKlxuICogQ0xJIGVudHJ5IHBvaW50IGZvciBUYWN0aWNhXG4gKlxuICogUnVucyB0aGUgYW5hbHl6ZXIgb3ZlciBhIHRzY29uZmlnIHByb2plY3QgYW5kIHdyaXRlcyAudGFjdGljYS8gb3V0cHV0XG4gKi9cblxuaW50ZXJmYWNlIENMSU9wdGlvbnMgZXh0ZW5kcyBUYWN0aWNhQ29uZmlnIHtcblx0d2F0Y2g/OiBib29sZWFuO1xuXHRwcm9qZWN0Pzogc3RyaW5nO1xuXHRoZWxwPzogYm9vbGVhbjtcblx0LyoqIEN1c3RvbSB0b3BvbG9naWNhIGRpcmVjdG9yaWVzIHRvIHNjYW4gKi9cblx0dG9wb2xvZ2ljYURpcnM/OiBzdHJpbmdbXTtcblx0LyoqIEFkZCAuanMgZXh0ZW5zaW9ucyB0byByZWxhdGl2ZSBpbXBvcnRzIGZvciBFU00gTm9kZU5leHQgcmVzb2x1dGlvbiAqL1xuXHRlc20/OiBib29sZWFuO1xuXHQvKiogRW5hYmxlIEVEUyAoRXhlY3V0aW9uIERhdGEgU3RvcmFnZSkgdHJhY2tpbmcgKi9cblx0ZWRzPzogYm9vbGVhbjtcblx0LyoqIFByb2dyYW1tYXRpYyBwbHVnaW5zOyBjb25maWctZmlsZSBwbHVnaW5zIGFyZSBhcHBlbmRlZCBhZnRlciB0aGVzZSAqL1xuXHRwbHVnaW5zPzogVGFjdGljYVBsdWdpbltdO1xufVxuXG4vKipcbiAqIFBhcnNlIGNvbW1hbmQgbGluZSBhcmd1bWVudHNcbiAqL1xuZnVuY3Rpb24gcGFyc2VBcmdzIChhcmdzOiBzdHJpbmdbXSk6IENMSU9wdGlvbnMge1xuXHRjb25zdCBvcHRpb25zOiBDTElPcHRpb25zID0ge307XG5cblx0Zm9yIChsZXQgaSA9IDA7IGkgPCBhcmdzLmxlbmd0aDsgaSsrKSB7XG5cdFx0Y29uc3QgYXJnID0gYXJnc1sgaSBdO1xuXG5cdFx0c3dpdGNoIChhcmcpIHtcblx0XHRjYXNlICctdyc6XG5cdFx0Y2FzZSAnLS13YXRjaCc6XG5cdFx0XHRvcHRpb25zLndhdGNoID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1wJzpcblx0XHRjYXNlICctLXByb2plY3QnOlxuXHRcdFx0b3B0aW9ucy5wcm9qZWN0ID0gYXJnc1sgKytpIF07XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctbyc6XG5cdFx0Y2FzZSAnLS1vdXRwdXQnOlxuXHRcdFx0b3B0aW9ucy5vdXRwdXREaXIgPSBhcmdzWyArK2kgXTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1pJzpcblx0XHRjYXNlICctLWluY2x1ZGUnOlxuXHRcdFx0b3B0aW9ucy5pbmNsdWRlID0gKG9wdGlvbnMuaW5jbHVkZSB8fCBbXSkuY29uY2F0KGFyZ3NbICsraSBdLnNwbGl0KCcsJykpO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLWUnOlxuXHRcdGNhc2UgJy0tZXhjbHVkZSc6XG5cdFx0XHRvcHRpb25zLmV4Y2x1ZGUgPSAob3B0aW9ucy5leGNsdWRlIHx8IFtdKS5jb25jYXQoYXJnc1sgKytpIF0uc3BsaXQoJywnKSk7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctbSc6XG5cdFx0Y2FzZSAnLS1tb2R1bGUtYXVnbWVudGF0aW9uJzpcblx0XHRcdG9wdGlvbnMuZ2xvYmFsQXVnbWVudGF0aW9uID0gZmFsc2U7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctdic6XG5cdFx0Y2FzZSAnLS12ZXJib3NlJzpcblx0XHRcdG9wdGlvbnMudmVyYm9zZSA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctdCc6XG5cdFx0Y2FzZSAnLS10b3BvbG9naWNhJzpcblx0XHRcdG9wdGlvbnMudG9wb2xvZ2ljYURpcnMgPSAob3B0aW9ucy50b3BvbG9naWNhRGlycyB8fCBbXSkuY29uY2F0KGFyZ3NbICsraSBdLnNwbGl0KCcsJykpO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLS1lc20nOlxuXHRcdFx0b3B0aW9ucy5lc20gPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLS1lZHMnOlxuXHRcdFx0b3B0aW9ucy5lZHMgPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLS1uby1lZHMnOlxuXHRcdFx0b3B0aW9ucy5lZHMgPSBmYWxzZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1oJzpcblx0XHRjYXNlICctLWhlbHAnOlxuXHRcdFx0b3B0aW9ucy5oZWxwID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdH1cblx0fVxuXG5cdHJldHVybiBvcHRpb25zO1xufVxuXG4vKipcbiAqIFByaW50IGhlbHAgbWVzc2FnZVxuICovXG5mdW5jdGlvbiBwcmludEhlbHAgKCk6IHZvaWQge1xuXHRjb25zb2xlLmxvZyhgXG5UYWN0aWNhIC0gVHlwZSBkZWZpbml0aW9uIGdlbmVyYXRvciBmb3IgTW5lbW9uaWNhXG5cblVzYWdlOiB0YWN0aWNhIFtvcHRpb25zXVxuXG5PcHRpb25zOlxuICAtdywgLS13YXRjaCAgICAgICAgICAgICAgIFdhdGNoIGZvciBmaWxlIGNoYW5nZXMgYW5kIHJlZ2VuZXJhdGUgdHlwZXNcbiAgLXAsIC0tcHJvamVjdCAgICAgICAgICAgICBQYXRoIHRvIHRzY29uZmlnLmpzb24gKGRlZmF1bHQ6IC4vdHNjb25maWcuanNvbilcbiAgLW8sIC0tb3V0cHV0ICAgICAgICAgICAgICBPdXRwdXQgZGlyZWN0b3J5IGZvciBnZW5lcmF0ZWQgdHlwZXMgKGRlZmF1bHQ6IC50YWN0aWNhKVxuICAtaSwgLS1pbmNsdWRlICAgICAgICAgICAgIENvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIGZpbGUgcGF0dGVybnMgdG8gaW5jbHVkZVxuICAtZSwgLS1leGNsdWRlICAgICAgICAgICAgIENvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIGZpbGUgcGF0dGVybnMgdG8gZXhjbHVkZVxuICAtdCwgLS10b3BvbG9naWNhICAgICAgICAgIENvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIHRvcG9sb2dpY2EgZGlyZWN0b3JpZXMgdG8gc2NhblxuICAtbSwgLS1tb2R1bGUtYXVnbWVudGF0aW9uIFVzZSBtb2R1bGUgYXVnbWVudGF0aW9uIGluc3RlYWQgb2YgZ2xvYmFsIChsZWdhY3kgbW9kZSlcbiAgLS1lc20gICAgICAgICAgICAgICAgICAgICBBZGQgLmpzIGV4dGVuc2lvbnMgdG8gcmVsYXRpdmUgaW1wb3J0cyAoTm9kZU5leHQgRVNNKVxuICAtLWVkcyAgICAgICAgICAgICAgICAgICAgIEVuYWJsZSBFRFMgKEV4ZWN1dGlvbiBEYXRhIFN0b3JhZ2UpIHRyYWNraW5nXG4gIC0tbm8tZWRzICAgICAgICAgICAgICAgICAgRGlzYWJsZSBFRFMgdHJhY2tpbmdcbiAgLXYsIC0tdmVyYm9zZSAgICAgICAgICAgICBFbmFibGUgdmVyYm9zZSBsb2dnaW5nXG4gIC1oLCAtLWhlbHAgICAgICAgICAgICAgICAgU2hvdyB0aGlzIGhlbHAgbWVzc2FnZVxuXG5Db25maWd1cmF0aW9uOlxuICBGcmFtZXdvcmsgaW5zdHJ1bWVudGF0aW9uIHZvY2FidWxhcnkgaXMgc3VwcGxpZWQgYnkgcGx1Z2lucy4gUGxhY2UgYVxuICAudGFjdGljYS5qcyAob3IgdGFjdGljYS5jb25maWcuanMpIG5leHQgdG8geW91ciB0c2NvbmZpZy5qc29uOlxuXG4gICAgICBtb2R1bGUuZXhwb3J0cyA9IHsgcGx1Z2luczogWyAneW91ci1mcmFtZXdvcmstYWRhcHRlci90YWN0aWNhJyBdIH07XG5cbiAgRW50cmllcyBhcmUgbW9kdWxlIHNwZWNpZmllcnMgKHJlcXVpcmVkIHJlbGF0aXZlIHRvIHRoZSBjb25maWcgZmlsZSkgb3JcbiAgaW5saW5lIHBsdWdpbiBvYmplY3RzLiBXaXRob3V0IHBsdWdpbnMsIGluc3RydW1lbnRhdGlvbi5qc29uIHBvaW50cyA9IFtdLlxuXG5FeGFtcGxlczpcbiAgdGFjdGljYSAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICMgR2VuZXJhdGUgdHlwZXMgd2l0aCBnbG9iYWwgYXVnbWVudGF0aW9uIChkZWZhdWx0KVxuICB0YWN0aWNhIC0td2F0Y2ggICAgICAgICAgICAgICAgICAgICAgIyBXYXRjaCBtb2RlXG4gIHRhY3RpY2EgLS1tb2R1bGUtYXVnbWVudGF0aW9uICAgICAgICAjIFVzZSBsZWdhY3kgbW9kdWxlIGF1Z21lbnRhdGlvbiBtb2RlXG4gIHRhY3RpY2EgLS1wcm9qZWN0IC4vc3JjL3RzY29uZmlnLmpzb24gIyBDdXN0b20gdHNjb25maWcgcGF0aFxuICB0YWN0aWNhIC0tb3V0cHV0IC4vdHlwZXMvbW5lbW9uaWNhICAgIyBDdXN0b20gb3V0cHV0IGRpcmVjdG9yeVxuICB0YWN0aWNhIC0tdG9wb2xvZ2ljYSAuL3NyYy9haS10eXBlcyAgIyBTY2FuIHNwZWNpZmljIHRvcG9sb2dpY2EgZGlyZWN0b3J5XG5gKTtcbn1cblxuLyoqXG4gKiBGaW5kIHRzY29uZmlnLmpzb25cbiAqL1xuZnVuY3Rpb24gZmluZFRzQ29uZmlnIChwcm9qZWN0UGF0aD86IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdGlmIChwcm9qZWN0UGF0aCkge1xuXHRcdGlmIChmcy5leGlzdHNTeW5jKHByb2plY3RQYXRoKSkge1xuXHRcdFx0cmV0dXJuIHByb2plY3RQYXRoO1xuXHRcdH1cblx0XHR0aHJvdyBuZXcgRXJyb3IoYFByb2plY3QgZmlsZSBub3QgZm91bmQ6ICR7cHJvamVjdFBhdGh9YCk7XG5cdH1cblxuXHQvLyBMb29rIGZvciB0c2NvbmZpZy5qc29uIGluIGN1cnJlbnQgZGlyZWN0b3J5IGFuZCBwYXJlbnQgZGlyZWN0b3JpZXNcblx0bGV0IGN1cnJlbnREaXIgPSBwcm9jZXNzLmN3ZCgpO1xuXHR3aGlsZSAoY3VycmVudERpciAhPT0gcGF0aC5kaXJuYW1lKGN1cnJlbnREaXIpKSB7XG5cdFx0Y29uc3QgdHNjb25maWdQYXRoID0gcGF0aC5qb2luKGN1cnJlbnREaXIsICd0c2NvbmZpZy5qc29uJyk7XG5cdFx0aWYgKGZzLmV4aXN0c1N5bmModHNjb25maWdQYXRoKSkge1xuXHRcdFx0cmV0dXJuIHRzY29uZmlnUGF0aDtcblx0XHR9XG5cdFx0Y3VycmVudERpciA9IHBhdGguZGlybmFtZShjdXJyZW50RGlyKTtcblx0fVxuXG5cdHJldHVybiB1bmRlZmluZWQ7XG59XG5cbi8qKlxuICogTG9hZCBUeXBlU2NyaXB0IHByb2dyYW0gZnJvbSB0c2NvbmZpZ1xuICovXG5mdW5jdGlvbiBsb2FkUHJvZ3JhbSAodHNjb25maWdQYXRoOiBzdHJpbmcpOiB0cy5Qcm9ncmFtIHtcblx0Y29uc3QgY29uZmlnRmlsZSA9IHRzLnJlYWRDb25maWdGaWxlKHRzY29uZmlnUGF0aCwgdHMuc3lzLnJlYWRGaWxlKTtcblxuXHRpZiAoY29uZmlnRmlsZS5lcnJvcikge1xuXHRcdGNvbnN0IGVycm9yVGV4dCA9IHRzLmZsYXR0ZW5EaWFnbm9zdGljTWVzc2FnZVRleHQoXG5cdFx0XHRjb25maWdGaWxlLmVycm9yLm1lc3NhZ2VUZXh0LFxuXHRcdFx0J1xcbidcblx0XHQpO1xuXHRcdHRocm93IG5ldyBFcnJvcihgRXJyb3IgcmVhZGluZyB0c2NvbmZpZzogJHtlcnJvclRleHR9YCk7XG5cdH1cblxuXHRjb25zdCBwYXJzZWRDb25maWcgPSB0cy5wYXJzZUpzb25Db25maWdGaWxlQ29udGVudChcblx0XHRjb25maWdGaWxlLmNvbmZpZyxcblx0XHR0cy5zeXMsXG5cdFx0cGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aClcblx0KTtcblxuXHRpZiAocGFyc2VkQ29uZmlnLmVycm9ycy5sZW5ndGggPiAwKSB7XG5cdFx0Y29uc3QgZXJyb3JNZXNzYWdlcyA9IHBhcnNlZENvbmZpZy5lcnJvcnMubWFwKGUgPT5cblx0XHRcdHRzLmZsYXR0ZW5EaWFnbm9zdGljTWVzc2FnZVRleHQoZS5tZXNzYWdlVGV4dCwgJ1xcbicpKTtcblx0XHR0aHJvdyBuZXcgRXJyb3IoYEVycm9yIHBhcnNpbmcgdHNjb25maWc6ICR7ZXJyb3JNZXNzYWdlcy5qb2luKCdcXG4nKX1gKTtcblx0fVxuXG5cdGNvbnN0IHByb2dyYW0gPSB0cy5jcmVhdGVQcm9ncmFtKHtcblx0XHRyb290TmFtZXMgOiBwYXJzZWRDb25maWcuZmlsZU5hbWVzLFxuXHRcdG9wdGlvbnMgICA6IHBhcnNlZENvbmZpZy5vcHRpb25zLFxuXHR9KTtcblxuXHRyZXR1cm4gcHJvZ3JhbTtcbn1cblxuLyoqXG4gKiBMb29rIHVwIGEgdmFyaWFibGUgYnkgbmFtZSBzdGFydGluZyBmcm9tIGEgc2NvcGUsIHdhbGtpbmcgb3V0d2FyZCB0aHJvdWdoXG4gKiBwYXJlbnRTY29wZUlkLiBUaGUgaW5uZXJtb3N0IGJpbmRpbmcgd2lucyBldmVuIHdoZW4gaXQgY2FycmllcyBubyB0eXBlUGF0aFxuICogKHNoYWRvd2luZyBob25lc3R5IOKAlCBhbiB1bnR5cGVkIGxvY2FsIHNoYWRvd3MgYSB0eXBlZCBvdXRlciBvbmUpLlxuICovXG5mdW5jdGlvbiByZXNvbHZlU2NvcGVkVmFyaWFibGVUeXBlUGF0aCAoXG5cdG5hbWU6IHN0cmluZyxcblx0c2NvcGVJZDogc3RyaW5nLFxuXHRzY29wZUFuYWx5c2lzOiBTY29wZUFuYWx5c2lzXG4pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRsZXQgY3VycmVudDogc3RyaW5nIHwgdW5kZWZpbmVkID0gc2NvcGVJZDtcblx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRjb25zdCB2YXJpYWJsZSA9IHNjb3BlQW5hbHlzaXMudmFyaWFibGVzLmdldChgJHtjdXJyZW50fSMke25hbWV9YCk7XG5cdFx0aWYgKHZhcmlhYmxlKSB7XG5cdFx0XHRjb25zdCB7IHR5cGVQYXRoIH0gPSB2YXJpYWJsZTtcblx0XHRcdHJldHVybiB0eXBlUGF0aDtcblx0XHR9XG5cdFx0Y3VycmVudCA9IHNjb3BlQW5hbHlzaXMuc2NvcGVzLmdldChjdXJyZW50KT8ucGFyZW50U2NvcGVJZDtcblx0fVxuXHRyZXR1cm4gdW5kZWZpbmVkO1xufVxuXG4vKipcbiAqIEpvaW4gZGF0YSBmb3IgbW5lbW9ncmFwaGljYSdzIHdyYXBwZXJzIGxheWVyOiBwaW4gZWFjaCB3cmFwIGVudHJ5IHRvIHRoZVxuICogc2NvcGUgaG9sZGluZyBpdHMgY2FsbCBzaXRlLCBhbmQgcmVzb2x2ZSB0aGUgd3JhcHBlZCBpbnN0YW5jZSBhcmd1bWVudCdzXG4gKiBtbmVtb25pY2EgdHlwZSB0aHJvdWdoIHRoZSBzY29wZS12YXJpYWJsZSBjaGFpbi5cbiAqL1xuZnVuY3Rpb24gYXR0YWNoV3JhcEpvaW5EYXRhIChcblx0ZWRzOiBNYXA8c3RyaW5nLCBFRFNJbmZvW10+LFxuXHRzY29wZVdhbGtlcjogTG9jYWxTY29wZVdhbGtlcixcblx0c2NvcGVBbmFseXNpczogU2NvcGVBbmFseXNpc1xuKTogdm9pZCB7XG5cdGZvciAoY29uc3QgZW50cmllcyBvZiBlZHMudmFsdWVzKCkpIHtcblx0XHRmb3IgKGNvbnN0IGVudHJ5IG9mIGVudHJpZXMpIHtcblx0XHRcdGlmIChlbnRyeS5raW5kICE9PSAnd3JhcCcpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBob2xkZXJTY29wZUlkID0gc2NvcGVXYWxrZXIuZmluZEhvbGRlclNjb3BlSWQoZW50cnkubG9jYXRpb24pO1xuXHRcdFx0aWYgKCFob2xkZXJTY29wZUlkKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0ZW50cnkuc2NvcGVJZCA9IGhvbGRlclNjb3BlSWQ7XG5cdFx0XHRpZiAoIWVudHJ5Lmluc3RhbmNlQXJnKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgd3JhcHNUeXBlUGF0aCA9IHJlc29sdmVTY29wZWRWYXJpYWJsZVR5cGVQYXRoKFxuXHRcdFx0XHRlbnRyeS5pbnN0YW5jZUFyZyxcblx0XHRcdFx0aG9sZGVyU2NvcGVJZCxcblx0XHRcdFx0c2NvcGVBbmFseXNpc1xuXHRcdFx0KTtcblx0XHRcdGlmICh3cmFwc1R5cGVQYXRoKSB7XG5cdFx0XHRcdGVudHJ5LndyYXBzVHlwZVBhdGggPSB3cmFwc1R5cGVQYXRoO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxufVxuXG4vKipcbiAqIFJlbmRlciB0eXBlIGhpZXJhcmNoeSBhcyBhbiBBU0NJSSB0cmVlIHN0cmluZy5cbiAqL1xuZnVuY3Rpb24gcmVuZGVyVHlwZUhpZXJhcmNoeSAoZ3JhcGg6IFR5cGVHcmFwaEltcGwpOiBzdHJpbmcge1xuXHRjb25zdCBsaW5lczogc3RyaW5nW10gPSBbICdUeXBlIEhpZXJhcmNoeSAoVHJpZSk6JyBdO1xuXG5cdGZ1bmN0aW9uIHJlbmRlck5vZGUgKG5vZGU6IFR5cGVOb2RlLCBwcmVmaXggPSAnJywgaXNMYXN0ID0gdHJ1ZSk6IHZvaWQge1xuXHRcdGNvbnN0IGNvbm5lY3RvciA9IGlzTGFzdCA/ICfilJTilIDilIAgJyA6ICfilJzilIDilIAgJztcblx0XHQvLyBVc2Ugbm9kZS5mdWxsUGF0aCBkaXJlY3RseSBhbmQgY29udmVydCBkb3RzIHRvIHVuZGVyc2NvcmVzXG5cdFx0Y29uc3QgaW5zdGFuY2VOYW1lID0gbm9kZS5mdWxsUGF0aC5yZXBsYWNlKC9cXC4vZywgJ18nKTtcblx0XHRsaW5lcy5wdXNoKGAke3ByZWZpeH0ke2Nvbm5lY3Rvcn0ke2luc3RhbmNlTmFtZX1gKTtcblxuXHRcdGNvbnN0IGNoaWxkcmVuID0gQXJyYXkuZnJvbShub2RlLmNoaWxkcmVuLnZhbHVlcygpKTtcblx0XHRjb25zdCBuZXdQcmVmaXggPSBwcmVmaXggKyAoaXNMYXN0ID8gJyAgICAnIDogJ+KUgiAgICcpO1xuXG5cdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBjaGlsZHJlbi5sZW5ndGg7IGkrKykge1xuXHRcdFx0cmVuZGVyTm9kZShjaGlsZHJlblsgaSBdLCBuZXdQcmVmaXgsIGkgPT09IGNoaWxkcmVuLmxlbmd0aCAtIDEpO1xuXHRcdH1cblx0fVxuXG5cdGNvbnN0IHJvb3RzID0gQXJyYXkuZnJvbShncmFwaC5yb290cy52YWx1ZXMoKSk7XG5cdGZvciAobGV0IGkgPSAwOyBpIDwgcm9vdHMubGVuZ3RoOyBpKyspIHtcblx0XHRyZW5kZXJOb2RlKHJvb3RzWyBpIF0sICcnLCBpID09PSByb290cy5sZW5ndGggLSAxKTtcblx0fVxuXHQvLyBFbXB0eSBsaW5lIGF0IGVuZFxuXHRsaW5lcy5wdXNoKCcnKTtcblxuXHRjb25zdCByZXN1bHQgPSBsaW5lcy5qb2luKCdcXG4nKTtcblx0cmV0dXJuIHJlc3VsdDtcbn1cblxuLyoqXG4gKiBQcmludCB0eXBlIGhpZXJhcmNoeSB0byB0aGUgY29uc29sZS5cbiAqL1xuZnVuY3Rpb24gcHJpbnRUeXBlSGllcmFyY2h5IChncmFwaDogVHlwZUdyYXBoSW1wbCk6IHZvaWQge1xuXHRjb25zdCBvdXRwdXQgPSByZW5kZXJUeXBlSGllcmFyY2h5KGdyYXBoKTtcblx0Y29uc29sZS5sb2cob3V0cHV0KTtcbn1cblxuLyoqXG4gKiBDaGVjayBpZiBAbW5lbW9uaWNhL2RpdmUgaXMgcHJlc2VudCBpbiBwYWNrYWdlLmpzb24gZGVwZW5kZW5jaWVzXG4gKi9cbmZ1bmN0aW9uIGhhc0RpdmVEZXBlbmRlbmN5IChwcm9qZWN0RGlyOiBzdHJpbmcpOiBib29sZWFuIHtcblx0Y29uc3QgcGFja2FnZUpzb25QYXRoID0gcGF0aC5qb2luKHByb2plY3REaXIsICdwYWNrYWdlLmpzb24nKTtcblx0aWYgKCFmcy5leGlzdHNTeW5jKHBhY2thZ2VKc29uUGF0aCkpIHtcblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblx0dHJ5IHtcblx0XHRjb25zdCBjb250ZW50ID0gZnMucmVhZEZpbGVTeW5jKHBhY2thZ2VKc29uUGF0aCwgJ3V0Zi04Jyk7XG5cdFx0Y29uc3QgcGtnID0gSlNPTi5wYXJzZShjb250ZW50KTtcblx0XHRjb25zdCBkZXBzID0gcGtnLmRlcGVuZGVuY2llcyB8fCB7fTtcblx0XHRjb25zdCBkZXZEZXBzID0gcGtnLmRldkRlcGVuZGVuY2llcyB8fCB7fTtcblx0XHRjb25zdCBwZWVyRGVwcyA9IHBrZy5wZWVyRGVwZW5kZW5jaWVzIHx8IHt9O1xuXHRcdHJldHVybiAnQG1uZW1vbmljYS9kaXZlJyBpbiBkZXBzIHx8ICdAbW5lbW9uaWNhL2RpdmUnIGluIGRldkRlcHMgfHwgJ0BtbmVtb25pY2EvZGl2ZScgaW4gcGVlckRlcHM7XG5cdH0gY2F0Y2gge1xuXHRcdHJldHVybiBmYWxzZTtcblx0fVxufVxuXG4vKipcbiAqIFNjYW4gZm9yIHRvcG9sb2dpY2EgZGlyZWN0b3J5IHN0cnVjdHVyZXNcbiAqL1xuZnVuY3Rpb24gc2NhblRvcG9sb2dpY2FEaXJlY3RvcmllcyAocHJvamVjdERpcjogc3RyaW5nLCBjdXN0b21EaXJzPzogc3RyaW5nW10pOiBzdHJpbmdbXSB7XG5cdGNvbnN0IGRpcnM6IHN0cmluZ1tdID0gW107XG5cblx0Ly8gRmlyc3QsIGFkZCBjdXN0b20gZGlyZWN0b3JpZXMgaWYgc3BlY2lmaWVkXG5cdGlmIChjdXN0b21EaXJzKSB7XG5cdFx0Zm9yIChjb25zdCBkaXIgb2YgY3VzdG9tRGlycykge1xuXHRcdFx0Y29uc3QgZGlyUGF0aCA9IHBhdGguaXNBYnNvbHV0ZShkaXIpID8gZGlyIDogcGF0aC5qb2luKHByb2plY3REaXIsIGRpcik7XG5cdFx0XHRpZiAoZnMuZXhpc3RzU3luYyhkaXJQYXRoKSAmJiBmcy5zdGF0U3luYyhkaXJQYXRoKS5pc0RpcmVjdG9yeSgpKSB7XG5cdFx0XHRcdGRpcnMucHVzaChkaXJQYXRoKTtcblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGNvbnNvbGUud2FybihgV2FybmluZzogVG9wb2xvZ2ljYSBkaXJlY3Rvcnkgbm90IGZvdW5kOiAke2RpclBhdGh9YCk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0Ly8gVGhlbiBhdXRvLWRpc2NvdmVyIHN0YW5kYXJkIHRvcG9sb2dpY2EgZGlyZWN0b3JpZXNcblx0Y29uc3QgcG9zc2libGVEaXJzID0gWyAnYWktdHlwZXMnLCAndHlwZXMnLCAndG9wb2xvZ2ljYS10eXBlcycgXTtcblxuXHRmb3IgKGNvbnN0IGRpck5hbWUgb2YgcG9zc2libGVEaXJzKSB7XG5cdFx0Y29uc3QgZGlyUGF0aCA9IHBhdGguam9pbihwcm9qZWN0RGlyLCBkaXJOYW1lKTtcblx0XHRpZiAoZnMuZXhpc3RzU3luYyhkaXJQYXRoKSAmJiBmcy5zdGF0U3luYyhkaXJQYXRoKS5pc0RpcmVjdG9yeSgpKSB7XG5cdFx0XHQvLyBBdm9pZCBkdXBsaWNhdGVzXG5cdFx0XHRpZiAoIWRpcnMuaW5jbHVkZXMoZGlyUGF0aCkpIHtcblx0XHRcdFx0ZGlycy5wdXNoKGRpclBhdGgpO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8vIEFsc28gc2NhbiBzcmMvIHN1YmRpcmVjdG9yeVxuXHRjb25zdCBzcmNQYXRoID0gcGF0aC5qb2luKHByb2plY3REaXIsICdzcmMnKTtcblx0aWYgKGZzLmV4aXN0c1N5bmMoc3JjUGF0aCkgJiYgZnMuc3RhdFN5bmMoc3JjUGF0aCkuaXNEaXJlY3RvcnkoKSkge1xuXHRcdGZvciAoY29uc3QgZGlyTmFtZSBvZiBwb3NzaWJsZURpcnMpIHtcblx0XHRcdGNvbnN0IGRpclBhdGggPSBwYXRoLmpvaW4oc3JjUGF0aCwgZGlyTmFtZSk7XG5cdFx0XHRpZiAoZnMuZXhpc3RzU3luYyhkaXJQYXRoKSAmJiBmcy5zdGF0U3luYyhkaXJQYXRoKS5pc0RpcmVjdG9yeSgpKSB7XG5cdFx0XHRcdC8vIEF2b2lkIGR1cGxpY2F0ZXNcblx0XHRcdFx0aWYgKCFkaXJzLmluY2x1ZGVzKGRpclBhdGgpKSB7XG5cdFx0XHRcdFx0ZGlycy5wdXNoKGRpclBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0cmV0dXJuIGRpcnM7XG59XG5cbi8qKlxuICogQ29uZmlnIGZpbGUgY2FuZGlkYXRlcyAoZXNsaW50LXN0eWxlIHByb2plY3QgY29uZmlnKSwgc2VhcmNoZWQgbmV4dCB0b1xuICogdGhlIHJlc29sdmVkIHRzY29uZmlnIGZpcnN0LCB0aGVuIGluIHRoZSBjdXJyZW50IHdvcmtpbmcgZGlyZWN0b3J5LlxuICovXG5jb25zdCBDT05GSUdfRklMRV9OQU1FUyA9IFsgJy50YWN0aWNhLmpzJywgJ3RhY3RpY2EuY29uZmlnLmpzJyBdO1xuXG5pbnRlcmZhY2UgVGFjdGljYUNvbmZpZ0ZpbGUge1xuXHRwbHVnaW5zPzogQXJyYXk8VGFjdGljYVBsdWdpbiB8IHN0cmluZz47XG59XG5cbi8qKlxuICogTG9hZCBmcmFtZXdvcmstdm9jYWJ1bGFyeSBwbHVnaW5zOiBwcm9ncmFtbWF0aWMgb3B0aW9ucyBmaXJzdCwgdGhlbiB0aGVcbiAqIHByb2plY3QgY29uZmlnIGZpbGUuIFN0cmluZyBlbnRyaWVzIGFyZSBtb2R1bGUgc3BlY2lmaWVycyByZXF1aXJlZFxuICogcmVsYXRpdmUgdG8gdGhlIGNvbmZpZyBmaWxlIChlLmcuIGFuIGFkYXB0ZXIgcGFja2FnZSdzIHBsdWdpbiBzdWJwYXRoKS5cbiAqIFdpdGhvdXQgYSBjb25maWcgZmlsZSBhbmQgd2l0aG91dCBwcm9ncmFtbWF0aWMgcGx1Z2lucyB0aGUgYW5hbHl6ZXJcbiAqIHN0YXlzIGZyYW1ld29yay1ibGluZCBhbmQgaW5zdHJ1bWVudGF0aW9uLmpzb24gY2FycmllcyBlbXB0eSBwb2ludHMuXG4gKi9cbmZ1bmN0aW9uIGxvYWRUYWN0aWNhUGx1Z2lucyAocHJvamVjdERpcjogc3RyaW5nLCBvcHRpb25zOiBDTElPcHRpb25zKTogVGFjdGljYVBsdWdpbltdIHtcblx0Y29uc3QgcGx1Z2luczogVGFjdGljYVBsdWdpbltdID0gWyAuLi4ob3B0aW9ucy5wbHVnaW5zIHx8IFtdKSBdO1xuXG5cdGNvbnN0IHNlYXJjaERpcnMgPSBbIHByb2plY3REaXIgXTtcblx0Y29uc3QgY3dkID0gcHJvY2Vzcy5jd2QoKTtcblx0aWYgKGN3ZCAhPT0gcHJvamVjdERpcikge1xuXHRcdHNlYXJjaERpcnMucHVzaChjd2QpO1xuXHR9XG5cblx0bGV0IGNvbmZpZ1BhdGg6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0Zm9yIChjb25zdCBkaXIgb2Ygc2VhcmNoRGlycykge1xuXHRcdGZvciAoY29uc3QgbmFtZSBvZiBDT05GSUdfRklMRV9OQU1FUykge1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlID0gcGF0aC5qb2luKGRpciwgbmFtZSk7XG5cdFx0XHRpZiAoZnMuZXhpc3RzU3luYyhjYW5kaWRhdGUpKSB7XG5cdFx0XHRcdGNvbmZpZ1BhdGggPSBjYW5kaWRhdGU7XG5cdFx0XHRcdGJyZWFrO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAoY29uZmlnUGF0aCkge1xuXHRcdFx0YnJlYWs7XG5cdFx0fVxuXHR9XG5cblx0aWYgKCFjb25maWdQYXRoKSB7XG5cdFx0cmV0dXJuIHBsdWdpbnM7XG5cdH1cblxuXHQvLyBjcmVhdGVSZXF1aXJlIGFuY2hvcmVkIGF0IHRoZSBjb25maWcgZmlsZTogdGhlIGNvbmZpZydzIG93biBpbXBvcnRzXG5cdC8vIGFuZCBzdHJpbmcgcGx1Z2luIHNwZWNpZmllcnMgcmVzb2x2ZSBhZ2FpbnN0IHRoZSBwcm9qZWN0J3MgbW9kdWxlc1xuXHRjb25zdCBjb25maWdSZXF1aXJlID0gY3JlYXRlUmVxdWlyZShjb25maWdQYXRoKTtcblx0Y29uc3QgbG9hZGVkID0gY29uZmlnUmVxdWlyZShjb25maWdQYXRoKTtcblx0Y29uc3QgY29uZmlnOiBUYWN0aWNhQ29uZmlnRmlsZSA9IGxvYWRlZCAmJiB0eXBlb2YgbG9hZGVkID09PSAnb2JqZWN0JyAmJiAnZGVmYXVsdCcgaW4gbG9hZGVkXG5cdFx0PyBsb2FkZWQuZGVmYXVsdFxuXHRcdDogbG9hZGVkO1xuXHRjb25zdCBlbnRyaWVzID0gY29uZmlnICYmIEFycmF5LmlzQXJyYXkoY29uZmlnLnBsdWdpbnMpID8gY29uZmlnLnBsdWdpbnMgOiBbXTtcblxuXHRmb3IgKGNvbnN0IGVudHJ5IG9mIGVudHJpZXMpIHtcblx0XHRpZiAodHlwZW9mIGVudHJ5ICE9PSAnc3RyaW5nJykge1xuXHRcdFx0cGx1Z2lucy5wdXNoKGVudHJ5KTtcblx0XHRcdGNvbnRpbnVlO1xuXHRcdH1cblx0XHRjb25zdCBtb2QgPSBjb25maWdSZXF1aXJlKGVudHJ5KTtcblx0XHRjb25zdCBwbHVnaW46IFRhY3RpY2FQbHVnaW4gPSBtb2QgJiYgdHlwZW9mIG1vZCA9PT0gJ29iamVjdCcgJiYgJ2RlZmF1bHQnIGluIG1vZFxuXHRcdFx0PyBtb2QuZGVmYXVsdFxuXHRcdFx0OiBtb2Q7XG5cdFx0cGx1Z2lucy5wdXNoKHBsdWdpbik7XG5cdH1cblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3QgbmFtZXMgPSBwbHVnaW5zLm1hcChwbHVnaW4gPT4gcGx1Z2luLm5hbWUgfHwgJyh1bm5hbWVkKScpLmpvaW4oJywgJyk7XG5cdFx0Y29uc29sZS5sb2coYExvYWRlZCB0YWN0aWNhIGNvbmZpZzogJHtjb25maWdQYXRofSAocGx1Z2luczogJHtuYW1lcyB8fCAnbm9uZSd9KWApO1xuXHR9XG5cblx0cmV0dXJuIHBsdWdpbnM7XG59XG5cbi8qKlxuICogUnVuIHR5cGUgZ2VuZXJhdGlvblxuICovXG5mdW5jdGlvbiBydW4gKG9wdGlvbnM6IENMSU9wdGlvbnMpOiB2b2lkIHtcblx0Y29uc3QgdHNjb25maWdQYXRoID0gZmluZFRzQ29uZmlnKG9wdGlvbnMucHJvamVjdCk7XG5cblx0aWYgKCF0c2NvbmZpZ1BhdGgpIHtcblx0XHRjb25zb2xlLmVycm9yKCdFcnJvcjogQ291bGQgbm90IGZpbmQgdHNjb25maWcuanNvbicpO1xuXHRcdHByb2Nlc3MuZXhpdCgxKTtcblx0fVxuXG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgVXNpbmcgdHNjb25maWc6ICR7dHNjb25maWdQYXRofWApO1xuXHR9XG5cblx0Ly8gRnJhbWV3b3JrIHZvY2FidWxhcnkgYXJyaXZlcyB2aWEgcGx1Z2lucyDigJQgYSBjb25maWcgZmlsZSBuZXh0IHRvIHRoZVxuXHQvLyB0c2NvbmZpZyAob3IgaW4gY3dkKSBhbmQvb3IgcHJvZ3JhbW1hdGljIG9wdGlvbnMuIE5vbmUgbG9hZGVkIG1lYW5zXG5cdC8vIHRoZSBhbmFseXplciBkZXRlY3RzIHplcm8gaW5zdHJ1bWVudGF0aW9uIHBvaW50cy5cblx0Y29uc3QgcGx1Z2lucyA9IGxvYWRUYWN0aWNhUGx1Z2lucyhwYXRoLmRpcm5hbWUocGF0aC5yZXNvbHZlKHRzY29uZmlnUGF0aCkpLCBvcHRpb25zKTtcblxuXHQvLyBMb2FkIFR5cGVTY3JpcHQgcHJvZ3JhbVxuXHRjb25zdCBwcm9ncmFtID0gbG9hZFByb2dyYW0odHNjb25maWdQYXRoKTtcblxuXHQvLyBDcmVhdGUgYW5hbHl6ZXJcblx0Y29uc3QgYW5hbHl6ZXIgPSBuZXcgTW5lbW9uaWNhQW5hbHl6ZXIocHJvZ3JhbSwgcGx1Z2lucyk7XG5cblx0Ly8gRGV0ZXJtaW5lIG91dHB1dCBkaXJlY3RvcnkgZm9yIGV4Y2x1c2lvblxuXHRjb25zdCBvdXRwdXREaXIgPSBvcHRpb25zLm91dHB1dERpciB8fCAnLnRhY3RpY2EnO1xuXHRjb25zdCBvdXRwdXREaXJQYXRoID0gcGF0aC5yZXNvbHZlKHByb2Nlc3MuY3dkKCksIG91dHB1dERpcik7XG5cdC8vIFRoZSBwcm9qZWN0LWNvbnZlbnRpb25hbCAudGFjdGljYSBkaXIgKG5leHQgdG8gdHNjb25maWcpIGlzIEFMV0FZU1xuXHQvLyBleGNsdWRlZCwgZXZlbiB3aGVuIC0tb3V0cHV0IHBvaW50cyBlbHNld2hlcmU6IGdlbmVyYXRlZCBmaWxlcyBhcmVcblx0Ly8gbmV2ZXIgcHJvamVjdCBzb3VyY2UuIHJlc29sdmUoKSBib3RoIHNpZGVzIOKAlCB0c2NvbmZpZ1BhdGggbWF5IGJlXG5cdC8vIHJlbGF0aXZlICgnLi90c2NvbmZpZy5qc29uJykgd2hpbGUgc291cmNlRmlsZS5maWxlTmFtZSBpcyBhYnNvbHV0ZVxuXHRjb25zdCBjb252ZW50aW9uYWxPdXRwdXREaXIgPSBwYXRoLnJlc29sdmUocHJvY2Vzcy5jd2QoKSwgcGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aCksICcudGFjdGljYScpO1xuXG5cdC8vIENvbGxlY3Qgc291cmNlIGZpbGVzIHRvIGFuYWx5emVcblx0Y29uc3Qgc291cmNlRmlsZXM6IHRzLlNvdXJjZUZpbGVbXSA9IFtdO1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2YgcHJvZ3JhbS5nZXRTb3VyY2VGaWxlcygpKSB7XG5cdFx0aWYgKHNvdXJjZUZpbGUuaXNEZWNsYXJhdGlvbkZpbGUpIHtcblx0XHRcdGNvbnRpbnVlO1xuXHRcdH1cblxuXHRcdGNvbnN0IGFic29sdXRlRmlsZU5hbWUgPSBwYXRoLnJlc29sdmUocHJvY2Vzcy5jd2QoKSwgc291cmNlRmlsZS5maWxlTmFtZSk7XG5cdFx0aWYgKGFic29sdXRlRmlsZU5hbWUuc3RhcnRzV2l0aChvdXRwdXREaXJQYXRoICsgcGF0aC5zZXApIHx8XG5cdFx0XHRhYnNvbHV0ZUZpbGVOYW1lLnN0YXJ0c1dpdGgoY29udmVudGlvbmFsT3V0cHV0RGlyICsgcGF0aC5zZXApKSB7XG5cdFx0XHRjb250aW51ZTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBleGNsdWRlIHBhdHRlcm5zXG5cdFx0aWYgKG9wdGlvbnMuZXhjbHVkZSkge1xuXHRcdFx0Y29uc3Qgc2hvdWxkRXhjbHVkZSA9IG9wdGlvbnMuZXhjbHVkZS5zb21lKHBhdHRlcm4gPT5cblx0XHRcdFx0c291cmNlRmlsZS5maWxlTmFtZS5pbmNsdWRlcyhwYXR0ZXJuLnJlcGxhY2UoL1xcKi9nLCAnJykpKTtcblx0XHRcdGlmIChzaG91bGRFeGNsdWRlKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIENoZWNrIGluY2x1ZGUgcGF0dGVybnNcblx0XHRpZiAob3B0aW9ucy5pbmNsdWRlICYmIG9wdGlvbnMuaW5jbHVkZS5sZW5ndGggPiAwKSB7XG5cdFx0XHRjb25zdCBzaG91bGRJbmNsdWRlID0gb3B0aW9ucy5pbmNsdWRlLnNvbWUocGF0dGVybiA9PlxuXHRcdFx0XHRzb3VyY2VGaWxlLmZpbGVOYW1lLmluY2x1ZGVzKHBhdHRlcm4ucmVwbGFjZSgvXFwqL2csICcnKSkpO1xuXHRcdFx0aWYgKCFzaG91bGRJbmNsdWRlKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHNvdXJjZUZpbGVzLnB1c2goc291cmNlRmlsZSk7XG5cdH1cblxuXHQvLyBTY2FuIGZvciB0b3BvbG9naWNhIGRpcmVjdG9yeSBzdHJ1Y3R1cmVzIEZJUlNUXG5cdGNvbnN0IHByb2plY3REaXIgPSBwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKTtcblx0Y29uc3QgdG9wb2xvZ2ljYURpcnMgPSBzY2FuVG9wb2xvZ2ljYURpcmVjdG9yaWVzKHByb2plY3REaXIsIG9wdGlvbnMudG9wb2xvZ2ljYURpcnMpO1xuXG5cdGlmICh0b3BvbG9naWNhRGlycy5sZW5ndGggPiAwICYmIG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBGb3VuZCB0b3BvbG9naWNhIGRpcmVjdG9yaWVzOiAke3RvcG9sb2dpY2FEaXJzLmpvaW4oJywgJyl9YCk7XG5cdH1cblxuXHQvLyBBbmFseXplIHRvcG9sb2dpY2EgZGlyZWN0b3JpZXMgQkVGT1JFIHVzYWdlIGNvbGxlY3Rpb25cblx0Y29uc3QgdG9wb2xvZ2ljYUFuYWx5emVyID0gbmV3IFRvcG9sb2dpY2FBbmFseXplcigpO1xuXHRjb25zdCB0b3BvbG9naWNhVHlwZXMgPSBuZXcgTWFwPHN0cmluZywgaW1wb3J0KCcuL3R5cGVzJykuVHlwZU5vZGU+KCk7XG5cdGZvciAoY29uc3QgZGlyIG9mIHRvcG9sb2dpY2FEaXJzKSB7XG5cdFx0Y29uc3QgcmVzdWx0ID0gdG9wb2xvZ2ljYUFuYWx5emVyLmFuYWx5emVEaXJlY3RvcnkoZGlyKTtcblx0XHRpZiAocmVzdWx0LnR5cGVzLnNpemUgPiAwKSB7XG5cdFx0XHQvLyBDb2xsZWN0IHRvcG9sb2dpY2EgdHlwZXMgZm9yIGRlZmluaXRpb25zIGFuZCB1c2FnZSB0cmFja2luZ1xuXHRcdFx0Zm9yIChjb25zdCBbIHR5cGVQYXRoLCBub2RlIF0gb2YgcmVzdWx0LnR5cGVzKSB7XG5cdFx0XHRcdHRvcG9sb2dpY2FUeXBlcy5zZXQodHlwZVBhdGgsIG5vZGUpO1xuXHRcdFx0fVxuXHRcdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0XHRjb25zb2xlLmxvZyhgQWRkZWQgJHtyZXN1bHQudHlwZXMuc2l6ZX0gdHlwZXMgZnJvbSAke2Rpcn1gKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0aWYgKHJlc3VsdC5lcnJvcnMubGVuZ3RoID4gMCAmJiBvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdHJlc3VsdC5lcnJvcnMuZm9yRWFjaChlcnIgPT4gY29uc29sZS53YXJuKGBbVG9wb2xvZ2ljYV0gJHtlcnJ9YCkpO1xuXHRcdH1cblx0fVxuXG5cdC8vIEFkZCB0b3BvbG9naWNhIHR5cGVzIHRvIGFuYWx5emVyIHNvIHRoZXkncmUgYXZhaWxhYmxlIGZvciB1c2FnZSBkZXRlY3Rpb25cblx0Ly8gUHJvY2VzcyBpbiBvcmRlciBvZiBwYXRoIGRlcHRoIChwYXJlbnRzIGZpcnN0KSB0byBlbnN1cmUgcHJvcGVyIGhpZXJhcmNoeVxuXHRjb25zdCBzb3J0ZWRUeXBlcyA9IEFycmF5LmZyb20odG9wb2xvZ2ljYVR5cGVzLmVudHJpZXMoKSkuc29ydCgoYSwgYikgPT4ge1xuXHRcdGNvbnN0IGRlcHRoQSA9IChhWyAwIF0ubWF0Y2goL1xcLi9nKSB8fCBbXSkubGVuZ3RoO1xuXHRcdGNvbnN0IGRlcHRoQiA9IChiWyAwIF0ubWF0Y2goL1xcLi9nKSB8fCBbXSkubGVuZ3RoO1xuXHRcdHJldHVybiBkZXB0aEEgLSBkZXB0aEI7XG5cdH0pO1xuXHRmb3IgKGNvbnN0IFsgdHlwZVBhdGgsIG5vZGUgXSBvZiBzb3J0ZWRUeXBlcykge1xuXHRcdGFuYWx5emVyLmFkZFRvcG9sb2dpY2FUeXBlKHR5cGVQYXRoLCBub2RlKTtcblx0fVxuXG5cdC8vIEZpcnN0IHBhc3M6IGNvbGxlY3QgYWxsIGRlZmluaXRpb25zLlxuXHQvLyBNb2R1bGUtc2NvcGUgdHJhY2tpbmcgKGltcG9ydHMvZXhwb3J0cyBmb3IgbW9kdWxlcy5qc29uKSBoYXBwZW5zIGluIHRoZVxuXHQvLyBzYW1lIHBhc3Mg4oCUIGl0IG5lZWRzIG9ubHkgdGhlIEFTVCwgbm90IHRoZSBjb2xsZWN0ZWQgZGVmaW5pdGlvbnMuXG5cdGNvbnN0IG1vZHVsZUdyYXBoQnVpbGRlciA9IG5ldyBNb2R1bGVHcmFwaEJ1aWxkZXIocHJvZ3JhbSk7XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBBbmFseXppbmcgKGRlZmluaXRpb25zKTogJHtzb3VyY2VGaWxlLmZpbGVOYW1lfWApO1xuXHRcdH1cblxuXHRcdHRyeSB7XG5cdFx0XHRhbmFseXplci5hbmFseXplRmlsZShzb3VyY2VGaWxlKTtcblx0XHRcdG1vZHVsZUdyYXBoQnVpbGRlci5hZGRGaWxlKHNvdXJjZUZpbGUpO1xuXHRcdH0gY2F0Y2ggKGVycikge1xuXHRcdFx0Y29uc29sZS5lcnJvcihgRXJyb3IgYW5hbHl6aW5nICR7c291cmNlRmlsZS5maWxlTmFtZX06YCwgZXJyKTtcblx0XHRcdHRocm93IGVycjtcblx0XHR9XG5cdH1cblxuXHQvLyBTZWNvbmQgcGFzczogY29sbGVjdCB1c2FnZXMgKG5vdyBhbGwgZGVmaW5pdGlvbnMgYXJlIGtub3duLCBpbmNsdWRpbmcgdG9wb2xvZ2ljYSlcblx0YW5hbHl6ZXIucmVzZXRVc2FnZXMoKTtcblx0Zm9yIChjb25zdCBzb3VyY2VGaWxlIG9mIHNvdXJjZUZpbGVzKSB7XG5cdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0Y29uc29sZS5sb2coYEFuYWx5emluZyAodXNhZ2VzKTogJHtzb3VyY2VGaWxlLmZpbGVOYW1lfWApO1xuXHRcdH1cblxuXHRcdHRyeSB7XG5cdFx0XHRhbmFseXplci5hbmFseXplRmlsZShzb3VyY2VGaWxlKTtcblx0XHR9IGNhdGNoIChlcnIpIHtcblx0XHRcdGNvbnNvbGUuZXJyb3IoYEVycm9yIGFuYWx5emluZyAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OmAsIGVycik7XG5cdFx0XHR0aHJvdyBlcnI7XG5cdFx0fVxuXHR9XG5cblx0Ly8gR2VuZXJhdGUgdHlwZXMgZnJvbSBtbmVtb25pY2EgYW5hbHlzaXNcblx0Ly8gTm90ZTogdG9wb2xvZ2ljYSB0eXBlcyBhcmUgYWxyZWFkeSBhZGRlZCB0byB0aGUgYW5hbHl6ZXIncyBncmFwaCB2aWEgYWRkVG9wb2xvZ2ljYVR5cGUoKVxuXHRjb25zdCBncmFwaCA9IGFuYWx5emVyLmdldEdyYXBoKCk7XG5cdGNvbnN0IGdlbmVyYXRvciA9IG5ldyBUeXBlc0dlbmVyYXRvcihncmFwaCwgb3B0aW9ucy5lc20sIG9wdGlvbnMub3V0cHV0RGlyKTtcblxuXHQvLyBDaGVjayBpZiBtb2R1bGUgYXVnbWVudGF0aW9uIG1vZGUgaXMgcmVxdWVzdGVkIChsZWdhY3kpXG5cdGNvbnN0IHVzZU1vZHVsZUF1Z21lbnRhdGlvbiA9IG9wdGlvbnMuZ2xvYmFsQXVnbWVudGF0aW9uID09PSBmYWxzZTtcblxuXHQvLyBHZW5lcmF0ZSB0eXBlcyBiYXNlZCBvbiBtb2RlXG5cdGxldCBnZW5lcmF0ZWRUeXBlczogeyBjb250ZW50OiBzdHJpbmc7IHR5cGVzOiBzdHJpbmdbXSB9O1xuXHRsZXQgb3V0cHV0UGF0aDogc3RyaW5nO1xuXG5cdGNvbnN0IHdyaXRlciA9IG5ldyBUeXBlc1dyaXRlcihvcHRpb25zLm91dHB1dERpcik7XG5cblx0aWYgKHVzZU1vZHVsZUF1Z21lbnRhdGlvbikge1xuXHRcdC8vIExlZ2FjeSBtb2RlOiBnZW5lcmF0ZSBnbG9iYWwgYXVnbWVudGF0aW9uIGZpbGUgKGluZGV4LmQudHMpXG5cdFx0Z2VuZXJhdGVkVHlwZXMgPSBnZW5lcmF0b3IuZ2VuZXJhdGVHbG9iYWxBdWdtZW50YXRpb24oKTtcblx0XHRvdXRwdXRQYXRoID0gd3JpdGVyLndyaXRlR2xvYmFsQXVnbWVudGF0aW9uKGdlbmVyYXRlZFR5cGVzKTtcblx0fSBlbHNlIHtcblx0XHQvLyBEZWZhdWx0IG1vZGU6IGdlbmVyYXRlIHR5cGVzLnRzIGZvciBtYW51YWwgaW1wb3J0c1xuXHRcdGdlbmVyYXRlZFR5cGVzID0gZ2VuZXJhdG9yLmdlbmVyYXRlVHlwZXNGaWxlKCk7XG5cdFx0b3V0cHV0UGF0aCA9IHdyaXRlci53cml0ZVR5cGVzRmlsZShnZW5lcmF0ZWRUeXBlcyk7XG5cblx0XHQvLyBHZW5lcmF0ZSByZWdpc3RyeS50cyBmb3IgdHlwZS1zYWZlIGxvb2t1cCgpIGZ1bmN0aW9uXG5cdFx0Y29uc3QgcmVnaXN0cnlUeXBlcyA9IGdlbmVyYXRvci5nZW5lcmF0ZVR5cGVSZWdpc3RyeSgpO1xuXHRcdGNvbnN0IHJlZ2lzdHJ5UGF0aCA9IHdyaXRlci53cml0ZVRvKCdyZWdpc3RyeS50cycsIHJlZ2lzdHJ5VHlwZXMuY29udGVudCk7XG5cblx0XHQvLyBHZW5lcmF0ZSBpbmRleC50cyB0byBleHBvcnQgZXZlcnl0aGluZ1xuXHRcdGNvbnN0IGluZGV4Q29udGVudCA9IGAvLyBHZW5lcmF0ZWQgYnkgQG1uZW1vbmljYS90YWN0aWNhIC0gRE8gTk9UIEVESVRcbi8vIEV4cG9ydCBhbGwgZ2VuZXJhdGVkIHR5cGVzXG5cbmV4cG9ydCAqIGZyb20gJy4vdHlwZXMke29wdGlvbnMuZXNtID8gJy5qcycgOiAnJ30nO1xuZXhwb3J0ICogZnJvbSAnLi9yZWdpc3RyeSR7b3B0aW9ucy5lc20gPyAnLmpzJyA6ICcnfSc7XG5gO1xuXHRcdHdyaXRlci53cml0ZVRvKCdpbmRleC50cycsIGluZGV4Q29udGVudCk7XG5cblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIHJlZ2lzdHJ5LnRzIGF0OiAke3JlZ2lzdHJ5UGF0aH1gKTtcblx0XHR9XG5cdH1cblxuXHQvLyBHZW5lcmF0ZSBkZWZpbml0aW9ucy5qc29uIGFuZCB1c2FnZXMuanNvbiBmb3IgY29kZSBuYXZpZ2F0aW9uXG5cdC8vIEluY2x1ZGUgYm90aCBtbmVtb25pY2EgYW5kIHRvcG9sb2dpY2EgZGVmaW5pdGlvbnNcblx0Y29uc3QgZGVmaW5pdGlvbnMgPSBuZXcgTWFwKGFuYWx5emVyLmdldERlZmluaXRpb25zKCkpO1xuXHRjb25zdCB1c2FnZXMgPSBuZXcgTWFwKGFuYWx5emVyLmdldFVzYWdlcygpKTtcblx0XG5cdC8vIEFkZCB0b3BvbG9naWNhIHR5cGVzIHRvIGRlZmluaXRpb25zXG5cdGZvciAoY29uc3QgWyBmdWxsUGF0aCwgdHlwZU5vZGUgXSBvZiB0b3BvbG9naWNhVHlwZXMpIHtcblx0XHQvLyBTa2lwIGlmIGFscmVhZHkgZXhpc3RzIChwcmVmZXIgbW5lbW9uaWNhJ3MgYW5hbHlzaXMpXG5cdFx0aWYgKGRlZmluaXRpb25zLmhhcyhmdWxsUGF0aCkpIHtcblx0XHRcdGNvbnRpbnVlO1xuXHRcdH1cblx0XHRcblx0XHRjb25zdCBkZWZpbml0aW9uOiBpbXBvcnQoJy4vdHlwZXMnKS5EZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5vZGUubmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7dHlwZU5vZGUuc291cmNlRmlsZX06JHt0eXBlTm9kZS5saW5lfToke3R5cGVOb2RlLmNvbHVtbn1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogdHlwZU5vZGUucGFyZW50ID8gdHlwZU5vZGUucGFyZW50LmZ1bGxQYXRoIDogbnVsbCxcblx0XHRcdHN0cmljdENoYWluIDogdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogZmFsc2Vcblx0XHR9O1xuXHRcdGRlZmluaXRpb25zLnNldChmdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdH1cblxuXHQvLyBMb2NhbC1zY29wZSB3YWxrIChpbnN0cnVtZW50YXRpb24gd2Fsa2VyIFBoYXNlIDIpOiBmdW5jdGlvbi9tZXRob2QvYXJyb3dcblx0Ly8gc2NvcGVzIG9ubHkgKG5vIGJsb2NrIHNjb3BlcyDigJQgZGVjaXNpb24gNSksIHZhcmlhYmxlcyB3aXRoIGlzTXV0YWJsZSBhbmRcblx0Ly8gcmVhc3NpZ25tZW50IHNpdGVzIChkZWNpc2lvbiA2KS4gUnVucyBhZnRlciBkZWZpbml0aW9ucyBhcmUga25vd24gc29cblx0Ly8gdmFyaWFibGUgdHlwZVBhdGhzIGNhbiByZXNvbHZlOyBob2xkZXJTY29wZUlkIGlzIGF0dGFjaGVkIHRvIHVzYWdlc1xuXHQvLyBiZWZvcmUgdGhleSBhcmUgd3JpdHRlbi5cblx0Y29uc3Qgc2NvcGVXYWxrZXIgPSBuZXcgTG9jYWxTY29wZVdhbGtlcigpO1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2Ygc291cmNlRmlsZXMpIHtcblx0XHRzY29wZVdhbGtlci5hZGRGaWxlKHNvdXJjZUZpbGUpO1xuXHR9XG5cdGNvbnN0IHNjb3BlUmVzb2x2ZXI6IFNjb3BlVHlwZVJlc29sdmVyID0ge1xuXHRcdHJlc29sdmVCeU5hbWUgOiAobmFtZTogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkID0+IHtcblx0XHRcdGlmIChkZWZpbml0aW9ucy5oYXMobmFtZSkpIHtcblx0XHRcdFx0cmV0dXJuIG5hbWU7XG5cdFx0XHR9XG5cdFx0XHRsZXQgZm91bmQ6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRcdGZvciAoY29uc3QgWyBmdWxsUGF0aCwgZGVmaW5pdGlvbiBdIG9mIGRlZmluaXRpb25zKSB7XG5cdFx0XHRcdGlmIChkZWZpbml0aW9uLm5hbWUgIT09IG5hbWUpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHQvLyBBbWJpZ3VvdXMgbmFtZSDigJQgbm8gdHlwZSBjaGVja2VyLCBzbyByZWZ1c2UgdG8gZ3Vlc3Ncblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGZvdW5kID0gZnVsbFBhdGg7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0fSxcblx0XHRoYXNQYXRoIDogKGZ1bGxQYXRoOiBzdHJpbmcpOiBib29sZWFuID0+IHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGRlZmluaXRpb25zLmhhcyhmdWxsUGF0aCk7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH0sXG5cdH07XG5cdGNvbnN0IHNjb3BlQW5hbHlzaXMgPSBzY29wZVdhbGtlci5idWlsZChzY29wZVJlc29sdmVyKTtcblx0TG9jYWxTY29wZVdhbGtlci5hdHRhY2hIb2xkZXJTY29wZUlkcyh1c2FnZXMsIHNjb3BlV2Fsa2VyKTtcblxuXHRjb25zdCBkZWZpbml0aW9uc1BhdGggPSB3cml0ZXIud3JpdGVEZWZpbml0aW9uc0ZpbGUoZGVmaW5pdGlvbnMpO1xuXHRjb25zdCB1c2FnZXNQYXRoID0gd3JpdGVyLndyaXRlVXNhZ2VzRmlsZSh1c2FnZXMpO1xuXG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGRlZmluaXRpb25zLmpzb24gYXQ6ICR7ZGVmaW5pdGlvbnNQYXRofWApO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgdXNhZ2VzLmpzb24gYXQ6ICR7dXNhZ2VzUGF0aH1gKTtcblx0fVxuXG5cdC8vIERldGVybWluZSBFRFMgc2V0dGluZzogZXhwbGljaXQgZmxhZyA+IGF1dG8tZGV0ZWN0IGRpdmUgPiBkZWZhdWx0IG9mZlxuXHRsZXQgZW5hYmxlRURTID0gb3B0aW9ucy5lZHM7XG5cdGlmIChlbmFibGVFRFMgPT09IHVuZGVmaW5lZCkge1xuXHRcdGVuYWJsZUVEUyA9IGhhc0RpdmVEZXBlbmRlbmN5KHByb2plY3REaXIpO1xuXHR9XG5cblx0aWYgKGVuYWJsZUVEUykge1xuXHRcdGNvbnN0IGVkcyA9IGFuYWx5emVyLmdldEVEU1VzYWdlcygpO1xuXHRcdGF0dGFjaFdyYXBKb2luRGF0YShlZHMsIHNjb3BlV2Fsa2VyLCBzY29wZUFuYWx5c2lzKTtcblx0XHRjb25zdCBlZHNQYXRoID0gd3JpdGVyLndyaXRlRURTRmlsZShlZHMpO1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgZWRzLmpzb24gYXQ6ICR7ZWRzUGF0aH1gKTtcblx0XHR9XG5cdH1cblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgZmxvdy5qc29uIChuYXRpdmUgaW5zdGFuY2UgdXNhZ2UgdHJhY2tpbmcpXG5cdGNvbnN0IGZsb3cgPSBhbmFseXplci5nZXRGbG93VXNhZ2VzKCk7XG5cdGNvbnN0IGZsb3dQYXRoID0gd3JpdGVyLndyaXRlRmxvd0ZpbGUoZmxvdyk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zdCBmbG93Q291bnQgPSBBcnJheS5mcm9tKGZsb3cudmFsdWVzKCkpLnJlZHVjZSgoc3VtLCBhcnIpID0+IHN1bSArIGFyci5sZW5ndGgsIDApO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgZmxvdy5qc29uIGF0OiAke2Zsb3dQYXRofSAoJHtmbG93Q291bnR9IGZsb3cgZW50cmllcylgKTtcblx0fVxuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBtb2R1bGVzLmpzb24gKG1vZHVsZS1zY29wZSBncmFwaDogaW1wb3J0cy9leHBvcnRzLFxuXHQvLyBkZXBlbmRlbmNpZXMsIGN5Y2xlcywgY3Jvc3MtbW9kdWxlIG1uZW1vbmljYS10eXBlIGVkZ2VzKVxuXHRjb25zdCBkZWZpbmVkVHlwZXNCeUZpbGUgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nW10+KCk7XG5cdGZvciAoY29uc3QgWyBmdWxsUGF0aCwgZGVmaW5pdGlvbiBdIG9mIGRlZmluaXRpb25zKSB7XG5cdFx0Y29uc3QgeyBsb2NhdGlvbiB9ID0gZGVmaW5pdGlvbjtcblx0XHRjb25zdCBsYXN0Q29sb24gPSBsb2NhdGlvbi5sYXN0SW5kZXhPZignOicpO1xuXHRcdGNvbnN0IHByZXZDb2xvbiA9IGxvY2F0aW9uLmxhc3RJbmRleE9mKCc6JywgbGFzdENvbG9uIC0gMSk7XG5cdFx0Y29uc3QgZmlsZSA9IGxvY2F0aW9uLnNsaWNlKDAsIHByZXZDb2xvbik7XG5cdFx0Y29uc3QgbGlzdCA9IGRlZmluZWRUeXBlc0J5RmlsZS5nZXQoZmlsZSkgPz8gW107XG5cdFx0bGlzdC5wdXNoKGZ1bGxQYXRoKTtcblx0XHRkZWZpbmVkVHlwZXNCeUZpbGUuc2V0KGZpbGUsIGxpc3QpO1xuXHR9XG5cdGNvbnN0IG1vZHVsZUdyYXBoID0gbW9kdWxlR3JhcGhCdWlsZGVyLmJ1aWxkKGRlZmluZWRUeXBlc0J5RmlsZSk7XG5cdGNvbnN0IG1vZHVsZXNQYXRoID0gd3JpdGVyLndyaXRlTW9kdWxlc0ZpbGUobW9kdWxlR3JhcGgpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3QgbW9kdWxlQ291bnQgPSBtb2R1bGVHcmFwaC5tb2R1bGVzLnNpemU7XG5cdFx0Y29uc3QgZWRnZUNvdW50ID0gbW9kdWxlR3JhcGguZWRnZXMubGVuZ3RoO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgbW9kdWxlcy5qc29uIGF0OiAke21vZHVsZXNQYXRofSAoJHttb2R1bGVDb3VudH0gbW9kdWxlcywgJHtlZGdlQ291bnR9IGVkZ2VzKWApO1xuXHR9XG5cblx0Ly8gQWx3YXlzIGdlbmVyYXRlIHNjb3Blcy5qc29uIChsb2NhbC1zY29wZSB3YWxrZXI6IHNjb3BlcywgdmFyaWFibGVzLFxuXHQvLyByZWFzc2lnbm1lbnQgZmxvdy10ZXJtaW5hdGlvbiBwb2ludHMpXG5cdGNvbnN0IHNjb3Blc1BhdGggPSB3cml0ZXIud3JpdGVTY29wZXNGaWxlKHNjb3BlQW5hbHlzaXMpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3Qgc2NvcGVDb3VudCA9IHNjb3BlQW5hbHlzaXMuc2NvcGVzLnNpemU7XG5cdFx0Y29uc3QgdmFyaWFibGVDb3VudCA9IHNjb3BlQW5hbHlzaXMudmFyaWFibGVzLnNpemU7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBzY29wZXMuanNvbiBhdDogJHtzY29wZXNQYXRofSAoJHtzY29wZUNvdW50fSBzY29wZXMsICR7dmFyaWFibGVDb3VudH0gdmFyaWFibGVzKWApO1xuXHR9XG5cblx0Ly8gVGhlIGluc2lkZS1vdXQgY3JlYXRpb24gd2FsayAoaW5zdHJ1bWVudGF0aW9uIHdhbGtlciBQaGFzZSAzKTogYW5jaG9yc1xuXHQvLyBhcmUgdGhlIGluc3RhbnRpYXRpb24gdXNhZ2VzOyBjYWxsZXJzIGFyZSBmb2xsb3dlZCBzYW1lLWZpbGUgYW5kXG5cdC8vIGNyb3NzLWZpbGUgKG1vZHVsZSBncmFwaCwgYmFycmVscyBjaGFzZWQpIHVudGlsIG9ubHkgc3RhcnRlcnMgcmVtYWluLlxuXHRjb25zdCBzb3VyY2VGaWxlc0J5UGF0aCA9IG5ldyBNYXA8c3RyaW5nLCB0cy5Tb3VyY2VGaWxlPigpO1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2Ygc291cmNlRmlsZXMpIHtcblx0XHRzb3VyY2VGaWxlc0J5UGF0aC5zZXQocGF0aC5yZXNvbHZlKHNvdXJjZUZpbGUuZmlsZU5hbWUpLCBzb3VyY2VGaWxlKTtcblx0fVxuXHRjb25zdCBjcmVhdGlvbkdyYXBoQnVpbGRlciA9IG5ldyBDcmVhdGlvbkdyYXBoQnVpbGRlcihtb2R1bGVHcmFwaCwgc2NvcGVBbmFseXNpcywgc2NvcGVXYWxrZXIsIHNvdXJjZUZpbGVzQnlQYXRoKTtcblx0Y29uc3QgY3JlYXRpb25HcmFwaCA9IGNyZWF0aW9uR3JhcGhCdWlsZGVyLmJ1aWxkKHVzYWdlcyk7XG5cblx0Ly8gQWx3YXlzIGdlbmVyYXRlIGluc3RydW1lbnRhdGlvbi5qc29uIChmcmFtZXdvcmsgbGlmZWN5Y2xlIGNyb3Nzcm9hZHNcblx0Ly8gZnJvbSB0aGUgbG9hZGVkIHBsdWdpbnMg4oCUIHN5bnRhY3RpYyBkZXRlY3Rpb24gbmVlZHMgbm8gZGl2ZVxuXHQvLyBkZXBlbmRlbmN5LCB1bmxpa2UgZWRzLmpzb24pLiB2MiBjYXJyaWVzIHRoZSBjcmVhdGlvbiBncmFwaFxuXHQvLyBhbG9uZ3NpZGUgdGhlIHBvaW50cy5cblx0Y29uc3QgaW5zdHJ1bWVudGF0aW9uID0gYW5hbHl6ZXIuZ2V0SW5zdHJ1bWVudGF0aW9uUG9pbnRzKCk7XG5cdGNvbnN0IGluc3RydW1lbnRhdGlvblBhdGggPSB3cml0ZXIud3JpdGVJbnN0cnVtZW50YXRpb25GaWxlKGluc3RydW1lbnRhdGlvbiwgY3JlYXRpb25HcmFwaCk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zdCBub2RlQ291bnQgPSBjcmVhdGlvbkdyYXBoLm5vZGVzLmxlbmd0aDtcblx0XHRjb25zdCBlZGdlQ291bnQgPSBjcmVhdGlvbkdyYXBoLmVkZ2VzLmxlbmd0aDtcblx0XHRjb25zdCBhbmNob3JDb3VudCA9IGNyZWF0aW9uR3JhcGguYW5jaG9ycy5sZW5ndGg7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBpbnN0cnVtZW50YXRpb24uanNvbiBhdDogJHtpbnN0cnVtZW50YXRpb25QYXRofSAoJHtpbnN0cnVtZW50YXRpb24ubGVuZ3RofSBwb2ludHMpYCk7XG5cdFx0Y29uc29sZS5sb2coYCAgY3JlYXRpb24gZ3JhcGg6ICR7bm9kZUNvdW50fSBub2RlcywgJHtlZGdlQ291bnR9IGVkZ2VzLCAke2FuY2hvckNvdW50fSBhbmNob3JzYCk7XG5cdH1cblxuXHQvLyBHZW5lcmF0ZSBoaWVyYXJjaHkuanNvbiAoc3RydWN0dXJlZCkgYW5kIGhpZXJhcmNoeS50eHQgKEFTQ0lJIHRyZWUpIGZvciB0aGUgVHJpZVxuXHRjb25zdCBoaWVyYXJjaHlSb290cyA9IGdyYXBoLnRvSGllcmFyY2h5KCk7XG5cdGNvbnN0IGhpZXJhcmNoeUpzb25QYXRoID0gd3JpdGVyLndyaXRlSGllcmFyY2h5RmlsZShoaWVyYXJjaHlSb290cyk7XG5cdGNvbnN0IGhpZXJhcmNoeVRleHQgPSByZW5kZXJUeXBlSGllcmFyY2h5KGdyYXBoKTtcblx0Y29uc3QgaGllcmFyY2h5VHh0UGF0aCA9IHdyaXRlci53cml0ZVRvKCdoaWVyYXJjaHkudHh0JywgaGllcmFyY2h5VGV4dCk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGhpZXJhcmNoeS5qc29uIGF0OiAke2hpZXJhcmNoeUpzb25QYXRofWApO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgaGllcmFyY2h5LnR4dCBhdDogJHtoaWVyYXJjaHlUeHRQYXRofWApO1xuXHR9XG5cblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgdHlwZXMgYXQ6ICR7b3V0cHV0UGF0aH1gKTtcblx0XHRjb25zb2xlLmxvZyhgTW9kZTogJHt1c2VNb2R1bGVBdWdtZW50YXRpb24gPyAnZ2xvYmFsIGF1Z21lbnRhdGlvbiAobGVnYWN5KScgOiAndHlwZXMgZmlsZSAoZGVmYXVsdCknfWApO1xuXHRcdGNvbnNvbGUubG9nKGBGb3VuZCAke2dlbmVyYXRlZFR5cGVzLnR5cGVzLmxlbmd0aH0gdHlwZXM6YCk7XG5cdFx0cHJpbnRUeXBlSGllcmFyY2h5KGdyYXBoKTtcblx0fSBlbHNlIHtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkICR7Z2VuZXJhdGVkVHlwZXMudHlwZXMubGVuZ3RofSB0eXBlcyBhdCAke29wdGlvbnMub3V0cHV0RGlyIHx8ICcudGFjdGljYSd9YCk7XG5cdFx0aWYgKHVzZU1vZHVsZUF1Z21lbnRhdGlvbikge1xuXHRcdFx0Y29uc29sZS5sb2coJ1VzaW5nIGdsb2JhbCBhdWdtZW50YXRpb24gbW9kZSAobGVnYWN5LCB1c2UgZGVmYXVsdCBtb2RlIGZvciB0eXBlcy50cyBvbmx5KScpO1xuXHRcdH1cblx0fVxufVxuXG4vKipcbiAqIFdhdGNoIG1vZGVcbiAqL1xuZnVuY3Rpb24gd2F0Y2ggKG9wdGlvbnM6IENMSU9wdGlvbnMpOiB2b2lkIHtcblx0Y29uc29sZS5sb2coJ1N0YXJ0aW5nIHdhdGNoIG1vZGUuLi4nKTtcblxuXHQvLyBJbml0aWFsIHJ1blxuXHRydW4ob3B0aW9ucyk7XG5cblx0Ly8gU2V0IHVwIGZpbGUgd2F0Y2hpbmdcblx0Y29uc3QgY2hva2lkYXIgPSByZXF1aXJlKCdjaG9raWRhcicpO1xuXHRjb25zdCB0c2NvbmZpZ1BhdGggPSBmaW5kVHNDb25maWcob3B0aW9ucy5wcm9qZWN0KTtcblxuXHRpZiAoIXRzY29uZmlnUGF0aCkge1xuXHRcdGNvbnNvbGUuZXJyb3IoJ0Vycm9yOiBDb3VsZCBub3QgZmluZCB0c2NvbmZpZy5qc29uJyk7XG5cdFx0cHJvY2Vzcy5leGl0KDEpO1xuXHR9XG5cblx0Y29uc3QgcHJvamVjdERpciA9IHBhdGguZGlybmFtZSh0c2NvbmZpZ1BhdGgpO1xuXHRjb25zdCB3YXRjaFBhdGhzID0gb3B0aW9ucy5pbmNsdWRlIHx8IFsgJyoqLyoudHMnIF07XG5cdGNvbnN0IGlnbm9yZVBhdGhzID0gb3B0aW9ucy5leGNsdWRlIHx8IFsgJyoqLyouZC50cycsICdub2RlX21vZHVsZXMvKionLCAnLnRhY3RpY2EvKionIF07XG5cblx0Y29uc3Qgd2F0Y2hlciA9IGNob2tpZGFyLndhdGNoKHdhdGNoUGF0aHMsIHtcblx0XHRjd2QgICAgICAgIDogcHJvamVjdERpcixcblx0XHRpZ25vcmVkICAgIDogaWdub3JlUGF0aHMsXG5cdFx0cGVyc2lzdGVudCA6IHRydWUsXG5cdH0pO1xuXG5cdHdhdGNoZXIub24oJ2NoYW5nZScsIChmaWxlUGF0aDogc3RyaW5nKSA9PiB7XG5cdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0Y29uc29sZS5sb2coYEZpbGUgY2hhbmdlZDogJHtmaWxlUGF0aH1gKTtcblx0XHR9XG5cdFx0cnVuKG9wdGlvbnMpO1xuXHR9KTtcblxuXHR3YXRjaGVyLm9uKCdhZGQnLCAoZmlsZVBhdGg6IHN0cmluZykgPT4ge1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBGaWxlIGFkZGVkOiAke2ZpbGVQYXRofWApO1xuXHRcdH1cblx0XHRydW4ob3B0aW9ucyk7XG5cdH0pO1xuXG5cdGNvbnNvbGUubG9nKCdXYXRjaGluZyBmb3IgY2hhbmdlcy4uLiAoUHJlc3MgQ3RybCtDIHRvIHN0b3ApJyk7XG59XG5cbi8qKlxuICogTWFpbiBlbnRyeSBwb2ludFxuICovXG5mdW5jdGlvbiBtYWluICgpOiB2b2lkIHtcblx0Y29uc3QgYXJncyA9IHByb2Nlc3MuYXJndi5zbGljZSgyKTtcblx0Y29uc3Qgb3B0aW9ucyA9IHBhcnNlQXJncyhhcmdzKTtcblxuXHRpZiAob3B0aW9ucy5oZWxwKSB7XG5cdFx0cHJpbnRIZWxwKCk7XG5cdFx0cHJvY2Vzcy5leGl0KDApO1xuXHR9XG5cblx0dHJ5IHtcblx0XHRpZiAob3B0aW9ucy53YXRjaCkge1xuXHRcdFx0d2F0Y2gob3B0aW9ucyk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdHJ1bihvcHRpb25zKTtcblx0XHR9XG5cdH0gY2F0Y2ggKGVycm9yKSB7XG5cdFx0Y29uc29sZS5lcnJvcignRXJyb3I6JywgZXJyb3IgaW5zdGFuY2VvZiBFcnJvciA/IGVycm9yLm1lc3NhZ2UgOiBlcnJvcik7XG5cdFx0cHJvY2Vzcy5leGl0KDEpO1xuXHR9XG59XG5cbi8vIFJ1biBpZiBleGVjdXRlZCBkaXJlY3RseVxuaWYgKHJlcXVpcmUubWFpbiA9PT0gbW9kdWxlKSB7XG5cdG1haW4oKTtcbn1cblxuZXhwb3J0IHtcblx0bWFpbiwgcnVuLCB3YXRjaCwgcGFyc2VBcmdzIFxufTtcbiJdfQ==